//! Stable identities for formal machine profiles.
//!
//! A profile is not a trusted extern boundary: its Lean semantics is checked
//! by the kernel. The content hash is nevertheless part of every generated
//! artifact that uses it, so cached proofs cannot silently survive a semantic
//! profile change (ADR 0057).

use std::collections::BTreeMap;
use std::io::ErrorKind;
use std::path::{Path, PathBuf};

pub const UART_POLL_V1_ID: &str = "uart-poll-v1";

/// Hash the complete repository-local Lean import closure of the UART profile,
/// plus the toolchain and Lake pins. The supplied root is the checkout whose
/// prelude the kernel will use; labels remain relative so the resulting identity
/// is independent of that checkout's absolute path.
pub fn uart_poll_v1_hash(repo_root: &Path) -> Result<String, String> {
    // Do not memoize this in-process. Long-lived compiler clients must observe
    // profile edits on their next check rather than retain a stale identity.
    let canonical_repo_root = repo_root.canonicalize().map_err(|error| {
        format!(
            "cannot resolve repository root {} for formal profile hashing: {error}",
            repo_root.display()
        )
    })?;
    let requested_lean_root = canonical_repo_root.join("lean");
    let lean_root = requested_lean_root.canonicalize().map_err(|error| {
        format!(
            "cannot resolve formal profile root {}: {error}",
            requested_lean_root.display()
        )
    })?;
    if !lean_root.starts_with(&canonical_repo_root) {
        return Err(format!(
            "formal profile root {} resolves outside repository root {}",
            lean_root.display(),
            canonical_repo_root.display()
        ));
    }
    if !lean_root.is_dir() {
        return Err(format!(
            "formal profile root {} is not a directory",
            lean_root.display()
        ));
    }

    let mut files = BTreeMap::new();
    insert_file(&mut files, &lean_root, "lean-toolchain")?;
    insert_file(&mut files, &lean_root, "lakefile.toml")?;
    collect_local_imports(&mut files, &lean_root, "Sable/MMIO.lean")?;
    collect_local_imports(&mut files, &lean_root, "Sable/SVMUart.lean")?;
    Ok(format!("fnv64:{:016x}", hash_files(&files)))
}

fn contained_file(lean_root: &Path, relative: &str) -> Result<PathBuf, String> {
    let requested = lean_root.join(relative);
    let canonical = requested.canonicalize().map_err(|error| {
        format!(
            "cannot resolve formal profile source {} ({}): {error}",
            relative,
            requested.display()
        )
    })?;
    if !canonical.starts_with(lean_root) {
        return Err(format!(
            "formal profile source {relative} resolves outside {}: {}",
            lean_root.display(),
            canonical.display()
        ));
    }
    if !canonical.is_file() {
        return Err(format!(
            "formal profile source {relative} is not a file ({})",
            canonical.display()
        ));
    }
    Ok(canonical)
}

fn insert_file(
    files: &mut BTreeMap<String, Vec<u8>>,
    lean_root: &Path,
    relative: &str,
) -> Result<(), String> {
    if files.contains_key(relative) {
        return Ok(());
    }
    let path = contained_file(lean_root, relative)?;
    let bytes = std::fs::read(&path).map_err(|error| {
        format!(
            "cannot hash formal profile source {} ({}): {error}",
            relative,
            path.display()
        )
    })?;
    files.insert(relative.into(), bytes);
    Ok(())
}

fn collect_local_imports(
    files: &mut BTreeMap<String, Vec<u8>>,
    lean_root: &Path,
    relative: &str,
) -> Result<(), String> {
    if files.contains_key(relative) {
        return Ok(());
    }
    insert_file(files, lean_root, relative)?;
    let text = std::str::from_utf8(&files[relative])
        .map_err(|error| format!("formal profile source {relative} is not UTF-8: {error}"))?;
    let modules = parse_header_imports(text, relative)?;
    for module in modules {
        if let Some(import) = resolve_local_module(lean_root, &module)? {
            collect_local_imports(files, lean_root, &import)?;
        }
    }
    Ok(())
}

/// Resolve an imported Lean module only when its source is part of this
/// repository's `lean/` tree. Toolchain and package imports deliberately do not
/// enter this closure; `lean-toolchain` and `lakefile.toml` identify those pins.
/// A module whose first namespace component exists locally must resolve to a
/// source file: silently classifying a miss as external would under-hash a typo
/// or a renamed local dependency.
fn resolve_local_module(lean_root: &Path, module: &str) -> Result<Option<String>, String> {
    let relative = module_relative_path(module)?;
    let requested = lean_root.join(&relative);
    let canonical = match requested.canonicalize() {
        Ok(path) => path,
        Err(error) if error.kind() == ErrorKind::NotFound => {
            let namespace = relative.split('/').next().unwrap_or(relative.as_str());
            if lean_root.join(namespace).is_dir() {
                return Err(format!(
                    "repository-local imported module {module} has no source at {}",
                    requested.display()
                ));
            }
            return Ok(None);
        }
        Err(error) => {
            return Err(format!(
                "cannot resolve imported module {module} ({}): {error}",
                requested.display()
            ));
        }
    };
    if !canonical.starts_with(lean_root) {
        return Err(format!(
            "imported module {module} resolves outside {}: {}",
            lean_root.display(),
            canonical.display()
        ));
    }
    if !canonical.is_file() {
        return Err(format!(
            "imported module {module} is not a file ({})",
            canonical.display()
        ));
    }
    Ok(Some(relative))
}

/// Convert a Lean module identifier to its repository-relative source path.
/// Lean maps ordinary and guillemet-escaped name components directly to path
/// components. Separators and parent components are rejected before the
/// canonical containment check.
fn module_relative_path(module: &str) -> Result<String, String> {
    let mut components = Vec::new();
    let mut chars = module.chars().peekable();

    while chars.peek().is_some() {
        let component = if chars.peek() == Some(&'«') {
            chars.next();
            let mut component = String::new();
            loop {
                match chars.next() {
                    Some('»') => break,
                    Some(ch) => component.push(ch),
                    None => {
                        return Err(format!(
                            "unterminated escaped identifier in Lean import `{module}`"
                        ));
                    }
                }
            }
            component
        } else {
            let mut component = String::new();
            while let Some(&ch) = chars.peek() {
                if ch == '.' {
                    break;
                }
                if ch.is_whitespace() || ch == '«' || ch == '»' {
                    return Err(format!("invalid Lean module identifier `{module}`"));
                }
                component.push(ch);
                chars.next();
            }
            component
        };

        if component.is_empty()
            || component == "."
            || component == ".."
            || component.chars().any(|ch| matches!(ch, '/' | '\\' | '\0'))
        {
            return Err(format!("unsafe Lean module identifier `{module}`"));
        }
        components.push(component);

        match chars.next() {
            Some('.') if chars.peek().is_some() => {}
            Some(_) => return Err(format!("invalid Lean module identifier `{module}`")),
            None => break,
        }
    }

    if components.is_empty() {
        return Err("empty Lean module identifier".into());
    }
    Ok(format!("{}.lean", components.join("/")))
}

/// Parse Lean header imports for the pinned toolchain. Command whitespace and
/// comments may cross lines between `[public] [meta] import [all]` tokens;
/// module names remain confined to the command's terminating line.
fn parse_header_imports(text: &str, relative: &str) -> Result<Vec<String>, String> {
    let uncommented = strip_lean_comments(text)
        .map_err(|error| format!("cannot parse imports in {relative}: {error}"))?;
    let mut imports = Vec::new();

    let lines: Vec<&str> = uncommented.lines().collect();
    let mut line_index = 0;
    while line_index < lines.len() {
        let line = lines[line_index].trim_start_matches('\u{feff}').trim();
        if line.is_empty() || line == "module" || line == "prelude" {
            line_index += 1;
            continue;
        }

        let start_line = line_index + 1;
        let mut command = line.to_string();
        while import_prefix_needs_more(&command) {
            line_index += 1;
            if line_index >= lines.len() {
                return Err(format!(
                    "{relative}:{start_line}: Lean import modifier has no command"
                ));
            }
            let next = lines[line_index].trim();
            if next.is_empty() {
                continue;
            }
            command.push(' ');
            command.push_str(next);
        }
        match parse_import_line(&command) {
            Ok(Some(module)) => imports.push(module),
            Ok(None) => break,
            Err(error) => return Err(format!("{relative}:{start_line}: {error}")),
        }
        line_index += 1;
    }
    Ok(imports)
}

fn import_prefix_needs_more(command: &str) -> bool {
    let mut rest = command;
    let mut saw_modifier = false;
    for keyword in ["public", "meta"] {
        if let Some(after) = strip_keyword(rest, keyword) {
            rest = after;
            saw_modifier = true;
        }
    }
    if rest.is_empty() {
        return saw_modifier;
    }
    let Some(after_import) = strip_keyword(rest, "import") else {
        return false;
    };
    if after_import.is_empty() {
        return true;
    }
    strip_keyword(after_import, "all").is_some_and(str::is_empty)
}

fn parse_import_line(line: &str) -> Result<Option<String>, String> {
    let mut rest = line;
    if let Some(after) = strip_keyword(rest, "public") {
        rest = after;
    }
    if let Some(after) = strip_keyword(rest, "meta") {
        rest = after;
    }
    let Some(after_import) = strip_keyword(rest, "import") else {
        return Ok(None);
    };
    rest = after_import;
    if let Some(after) = strip_keyword(rest, "all") {
        rest = after;
    }
    let module = rest.trim();
    if module.is_empty() {
        return Err("Lean import has no module name".into());
    }
    // Validate the complete remainder. In particular, this rejects a second
    // whitespace-separated module instead of silently treating it as another
    // import; the pinned Lean grammar permits one module per command.
    module_relative_path(module)?;
    Ok(Some(module.to_string()))
}

fn strip_keyword<'a>(text: &'a str, keyword: &str) -> Option<&'a str> {
    let text = text.trim_start();
    let rest = text.strip_prefix(keyword)?;
    if rest.is_empty() {
        return Some(rest);
    }
    rest.chars()
        .next()
        .filter(|ch| ch.is_whitespace())
        .map(|_| rest.trim_start())
}

/// Remove nested block comments and line comments while retaining line breaks.
fn strip_lean_comments(text: &str) -> Result<String, String> {
    let mut out = String::with_capacity(text.len());
    let mut chars = text.chars().peekable();
    let mut block_depth = 0usize;
    let mut line_comment = false;
    let mut in_string = false;
    let mut string_escape = false;
    let mut in_escaped_ident = false;

    while let Some(ch) = chars.next() {
        if line_comment {
            if ch == '\n' {
                line_comment = false;
                out.push(ch);
            } else {
                out.push(' ');
            }
            continue;
        }

        if block_depth != 0 {
            if ch == '/' && chars.peek() == Some(&'-') {
                chars.next();
                block_depth += 1;
                out.push_str("  ");
            } else if ch == '-' && chars.peek() == Some(&'/') {
                chars.next();
                block_depth -= 1;
                out.push_str("  ");
            } else if ch == '\n' {
                out.push(ch);
            } else {
                out.push(' ');
            }
            continue;
        }

        if in_string {
            out.push(ch);
            if string_escape {
                string_escape = false;
            } else if ch == '\\' {
                string_escape = true;
            } else if ch == '"' {
                in_string = false;
            }
            continue;
        }

        if in_escaped_ident {
            out.push(ch);
            if ch == '»' {
                in_escaped_ident = false;
            }
            continue;
        }

        if ch == '-' && chars.peek() == Some(&'-') {
            chars.next();
            line_comment = true;
            out.push_str("  ");
        } else if ch == '/' && chars.peek() == Some(&'-') {
            chars.next();
            block_depth = 1;
            out.push_str("  ");
        } else {
            if ch == '"' {
                in_string = true;
            } else if ch == '«' {
                in_escaped_ident = true;
            }
            out.push(ch);
        }
    }

    if block_depth != 0 {
        return Err("unterminated block comment".into());
    }
    Ok(out)
}

fn hash_files(files: &BTreeMap<String, Vec<u8>>) -> u64 {
    let mut hash = 0xcbf29ce484222325u64;
    for (label, bytes) in files {
        // Stable relative labels make the identity clone-location independent;
        // the NUL separators keep adjacent label/content pairs unambiguous.
        hash = fnv64(hash, label.as_bytes());
        hash = fnv64(hash, &[0]);
        hash = fnv64(hash, bytes);
        hash = fnv64(hash, &[0]);
    }
    hash
}

fn fnv64(mut hash: u64, bytes: &[u8]) -> u64 {
    for &byte in bytes {
        hash ^= u64::from(byte);
        hash = hash.wrapping_mul(0x100000001b3);
    }
    hash
}

#[cfg(test)]
mod tests {
    use super::{module_relative_path, parse_header_imports};

    #[test]
    fn parses_pinned_import_modifiers_and_comments() {
        let source = r#"
module
public import Sable.One -- Sable.NotAnImport
meta /- nested /- block -/ comment -/ import all Local.Two
public meta import /- between tokens -/ Sable.Three
import Lean

public section
"#;
        assert_eq!(
            parse_header_imports(source, "Fixture.lean").unwrap(),
            vec![
                "Sable.One".to_string(),
                "Local.Two".to_string(),
                "Sable.Three".to_string(),
                "Lean".to_string(),
            ]
        );
    }

    #[test]
    fn one_import_command_cannot_name_two_modules() {
        let error =
            parse_header_imports("import Sable.One Sable.Two\n", "Fixture.lean").unwrap_err();
        assert!(error.contains("invalid Lean module identifier"));
    }

    #[test]
    fn parses_multiline_import_command_whitespace() {
        assert_eq!(
            parse_header_imports(
                "public /- whitespace may continue on the next line -/\nmeta\nimport\nSable.One\npublic meta\nimport all\nSable.Two\n",
                "Fixture.lean",
            )
            .unwrap(),
            vec!["Sable.One".to_string(), "Sable.Two".to_string()]
        );
        assert!(parse_header_imports("public\n", "Fixture.lean").is_err());
        assert!(
            parse_header_imports("public section\n", "Fixture.lean")
                .unwrap()
                .is_empty()
        );
    }

    #[test]
    fn comment_shapes_inside_strings_do_not_hide_an_unterminated_comment() {
        let source = "import Sable.One\ndef s := \"/- not a comment\"\n/- open";
        assert!(parse_header_imports(source, "Fixture.lean").is_err());
    }

    #[test]
    fn maps_root_and_escaped_modules_and_rejects_unsafe_components() {
        assert_eq!(module_relative_path("Sable").unwrap(), "Sable.lean");
        assert_eq!(
            module_relative_path("Sable.«Odd Name»").unwrap(),
            "Sable/Odd Name.lean"
        );
        assert!(module_relative_path("Sable.«..»").is_err());
        assert!(module_relative_path("Sable.«outside/path»").is_err());
    }
}
