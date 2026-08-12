//! Handwritten recursive-descent parser, plus positional attachment of
//! proof blocks (design §1): a block attaches to the item starting on the
//! line right after its last `///` line; a blank line detaches it.
//! Attachment targets: functions (`pre`/`post`/`variant`), `while`
//! loops (`invariant`/`variant`), the post-signature position
//! (`variant`, design §8 style), and free-floating `discharge` blocks.

use crate::ast::*;
use crate::diag::Diagnostic;
use crate::lexer::{Tok, Token};
use crate::scan::{Clause, ClauseKind, ProofBlock};
use crate::span::{LineMap, Span};

const MAX_GENERIC_TYPE_DEPTH: usize = 64;
const MAX_GENERIC_TYPE_ARGS: usize = 256;
const MAX_GENERIC_TYPE_NODES: usize = 4096;
/// Recovery only needs to see far enough past a hard limit to distinguish a
/// real generic call from a comparison. This accepts the one-step-over-limit
/// diagnostics while bounding its own token and frame storage.
const MAX_GENERIC_RECOVERY_TOKENS: usize = MAX_GENERIC_TYPE_NODES * 4;

/// A nominal class visible while parsing recursive generic arguments.
///
/// This is intentionally separate from `class_names`: that list is an index
/// table for the checked `Ty` model and therefore excludes local generic
/// templates. Recursive use-site types need to recognize those templates
/// without assigning them a premature checked-class index.
#[derive(Debug, Clone)]
struct GenericClassName {
    name: String,
    arity: usize,
}

#[derive(Debug, Clone)]
struct GenericTypeSyntax {
    kind: GenericTypeSyntaxKind,
    span: Span,
}

#[derive(Debug, Clone)]
enum GenericTypeSyntaxKind {
    Named {
        name: String,
        name_span: Span,
        args: Option<Vec<GenericTypeSyntax>>,
    },
    Array(Box<GenericTypeSyntax>),
}

#[derive(Debug)]
struct ParsedTypeArgList {
    args: Vec<GenericTypeSyntax>,
    /// Token index immediately after the closing `>`.
    end: usize,
}

#[derive(Debug, Default)]
struct GenericTypeBudget {
    nodes: usize,
}

#[derive(Debug, Clone, Copy)]
enum GenericRecoveryFrame {
    ListNeedType,
    ListNeedSeparator,
    ArrayNeedType,
    ArrayNeedClose,
}

pub struct Parser<'a> {
    tokens: &'a [Token],
    pos: usize,
    /// Statements synthesized while parsing the current statement (the
    /// hidden byte-array temp behind a bare string literal); the block
    /// splices them in just before the statement that produced them.
    pending: Vec<Stmt>,
    /// A `mut` marker was just parsed; the next declaration consumes it.
    pending_mut: bool,
    str_temps: usize,
    blocks: &'a [ProofBlock],
    consumed: Vec<bool>,
    lines: &'a LineMap,
    text: &'a str,
    /// Type parameters of the generic declaration being parsed.
    tparams: Vec<String>,
    /// Names of classes declared anywhere in the file (pre-scanned so
    /// `&Nat` parameters and `-> Nat` returns resolve — ADR 0010).
    class_names: Vec<String>,
    /// Classes usable as recursive generic arguments, including local
    /// generic templates together with their declaration arity. Keeping this
    /// separate preserves the checked-class indices in `class_names`.
    generic_class_names: Vec<GenericClassName>,
    /// Names of POD records declared anywhere in the file. As with classes,
    /// a pre-scan permits self-referential `raw<R>` fields and forward uses.
    record_names: Vec<String>,
}

type PResult<T> = Result<T, Diagnostic>;

/// Pre-scan class declarations so recursive generic arguments may refer
/// forward to templates. The full declaration parser remains authoritative;
/// malformed parameter lists simply receive a placeholder arity here and are
/// diagnosed when their declaration is reached.
fn pre_scan_generic_class_names(
    tokens: &[Token],
    extern_classes: &[String],
    extern_generic_classes: &[(String, usize)],
) -> Vec<GenericClassName> {
    let mut classes: Vec<GenericClassName> = extern_classes
        .iter()
        .map(|name| GenericClassName {
            name: name.clone(),
            arity: 0,
        })
        .collect();
    classes.extend(
        extern_generic_classes
            .iter()
            .map(|(name, arity)| GenericClassName {
                name: name.clone(),
                arity: *arity,
            }),
    );

    for index in 0..tokens.len().saturating_sub(1) {
        if !matches!(tokens[index].tok, Tok::KwClass) {
            continue;
        }
        let Tok::Ident(name) = &tokens[index + 1].tok else {
            continue;
        };
        let arity = if tokens.get(index + 2).map(|token| &token.tok) == Some(&Tok::Lt) {
            pre_scan_type_parameter_arity(tokens, index + 2).unwrap_or(0)
        } else {
            0
        };
        if let Some(existing) = classes.iter_mut().find(|class| class.name == *name) {
            existing.arity = arity;
        } else {
            classes.push(GenericClassName {
                name: name.clone(),
                arity,
            });
        }
    }
    classes
}

fn pre_scan_type_parameter_arity(tokens: &[Token], lt: usize) -> Option<usize> {
    if tokens.get(lt).map(|token| &token.tok) != Some(&Tok::Lt) {
        return None;
    }
    let mut index = lt + 1;
    let mut arity = 0usize;
    loop {
        if !matches!(
            tokens.get(index).map(|token| &token.tok),
            Some(Tok::Ident(_))
        ) {
            return None;
        }
        arity = arity.checked_add(1)?;
        index += 1;
        if tokens.get(index).map(|token| &token.tok) == Some(&Tok::Colon) {
            index += 1;
            if !matches!(
                tokens.get(index).map(|token| &token.tok),
                Some(Tok::Ident(_))
            ) {
                return None;
            }
            index += 1;
        }
        match tokens.get(index).map(|token| &token.tok) {
            Some(Tok::Comma) => index += 1,
            Some(Tok::Gt) => return Some(arity),
            _ => return None,
        }
    }
}

pub fn parse(
    tokens: &[Token],
    blocks: &[ProofBlock],
    lines: &LineMap,
    text: &str,
) -> PResult<Program> {
    parse_module(tokens, blocks, lines, text, &[], &[], &[])
}

/// Parse one module. `extern_classes` are non-generic classes from
/// already-loaded imports (ADR 0013), in merged-index order: this module's own
/// classes get indices after them, matching the loader's merge.
/// `extern_generic_classes` is deliberately separate: templates need a name
/// and arity for recursive generic arguments, but must not acquire a checked
/// class index before monomorphization.
pub fn parse_module(
    tokens: &[Token],
    blocks: &[ProofBlock],
    lines: &LineMap,
    text: &str,
    extern_classes: &[String],
    extern_generic_classes: &[(String, usize)],
    extern_records: &[String],
) -> PResult<Program> {
    // Non-generic classes only, in declaration order — this matches
    // their indices in `program.classes` after monomorphization
    // (instances are appended after). Borrows of generic instances are
    // an ADR 0010 deferral.
    let mut class_names: Vec<String> = extern_classes.to_vec();
    for w in tokens.windows(3) {
        if matches!(w[0].tok, Tok::KwClass) && !matches!(w[2].tok, Tok::Lt) {
            if let Tok::Ident(n) = &w[1].tok {
                class_names.push(n.clone());
            }
        }
    }
    let generic_class_names =
        pre_scan_generic_class_names(tokens, extern_classes, extern_generic_classes);
    let mut record_names: Vec<String> = extern_records.to_vec();
    for w in tokens.windows(2) {
        if matches!(w[0].tok, Tok::KwRecord) {
            if let Tok::Ident(n) = &w[1].tok {
                record_names.push(n.clone());
            }
        }
    }
    let mut parser = Parser {
        tokens,
        pos: 0,
        pending: Vec::new(),
        pending_mut: false,
        str_temps: 0,
        blocks,
        consumed: vec![false; blocks.len()],
        lines,
        text,
        tparams: Vec::new(),
        class_names,
        generic_class_names,
        record_names,
    };
    let mut fns = Vec::new();
    let mut classes = Vec::new();
    let mut records = Vec::new();
    let mut traits = Vec::new();
    let mut impls = Vec::new();
    let mut operators = Vec::new();
    let mut uses = Vec::new();
    let mut consts = Vec::new();
    while !parser.at(&Tok::Eof) {
        if matches!(parser.peek(), Tok::Ident(n) if n == "use") {
            uses.push(parser.parse_use()?);
            continue;
        }
        // `pub` exports an item to importers (ADR 0019); everything
        // else is private to its module.
        let is_pub = matches!(parser.peek(), Tok::Ident(n) if n == "pub");
        if is_pub {
            let span = parser.peek_span();
            parser.bump();
            if !(parser.at(&Tok::KwClass)
                || parser.at(&Tok::KwRecord)
                || matches!(parser.peek(), Tok::Ident(n) if n == "trait" || n == "const" || n == "fn")
                || parser.at(&Tok::KwFn)
                || parser.at(&Tok::KwExtern))
            {
                return Err(Diagnostic {
                    name: "module.bad_pub".into(),
                    title: "`pub` does not apply here".into(),
                    span,
                    label: "only `fn`, `class`, `record`, `trait`, and `const` take `pub`".into(),
                    notes: vec![(
                        "note".into(),
                        "impls and operator bindings export with their trait/class; \
                         the proof layer (ghost defs, theorems) is always visible \
                         (ADR 0019)"
                            .into(),
                    )],
                });
            }
        }
        if parser.at(&Tok::KwClass) {
            let mut c = parser.parse_class()?;
            c.is_pub = is_pub;
            classes.push(c);
        } else if parser.at(&Tok::KwRecord) {
            let mut r = parser.parse_record()?;
            r.is_pub = is_pub;
            records.push(r);
        } else if matches!(parser.peek(), Tok::Ident(n) if n == "trait") {
            let mut t = parser.parse_trait()?;
            t.is_pub = is_pub;
            traits.push(t);
        } else if matches!(parser.peek(), Tok::Ident(n) if n == "impl") {
            impls.push(parser.parse_impl()?);
        } else if matches!(parser.peek(), Tok::Ident(n) if n == "operator") {
            operators.push(parser.parse_operator()?);
        } else if matches!(parser.peek(), Tok::Ident(n) if n == "const") {
            let mut c = parser.parse_const()?;
            c.is_pub = is_pub;
            consts.push(c);
        } else if parser.at(&Tok::KwExtern) {
            let mut f = parser.parse_extern()?;
            f.is_pub = is_pub;
            fns.push(f);
        } else {
            let mut f = parser.parse_fn()?;
            f.is_pub = is_pub;
            fns.push(f);
        }
    }

    // Remaining blocks are module-level: ghost defs, theorems,
    // discharges, defers, assumes.
    let mut discharges = Vec::new();
    let mut ghosts = Vec::new();
    let mut defers = Vec::new();
    let mut assumes = Vec::new();
    for (bi, block) in parser.blocks.iter().enumerate() {
        if parser.consumed[bi] {
            continue;
        }
        for clause in &block.clauses {
            validate_clause_label(clause)?;
            match clause.kind {
                ClauseKind::Discharge => discharges.push(parse_discharge(clause)?),
                ClauseKind::Defer => defers.push(parse_defer(clause)?),
                ClauseKind::Assume => assumes.push(parse_assume(clause)?),
                ClauseKind::GhostDef => ghosts.push(GhostItem {
                    keyword: "def",
                    unfold: clause.unfold,
                    text: clause.text.clone(),
                    span: clause.span,
                }),
                ClauseKind::Theorem => ghosts.push(GhostItem {
                    keyword: "theorem",
                    unfold: clause.unfold,
                    text: clause.text.clone(),
                    span: clause.span,
                }),
                other => {
                    return Err(Diagnostic {
                        name: "proof.unattached_block".into(),
                        title: format!(
                            "`{}` clause in a free-floating proof block",
                            kind_word(other)
                        ),
                        span: clause.line_span,
                        label: "module-level blocks hold `def`, `theorem`, and `discharge`".into(),
                        notes: vec![(
                            "note".into(),
                            "a blank line detaches a proof block from the item below — \
                             contracts must touch their function"
                                .into(),
                        )],
                    });
                }
            }
        }
    }

    Ok(Program {
        fns,
        classes,
        records,
        fn_templates: Vec::new(),
        class_templates: Vec::new(),
        traits,
        impls,
        discharges,
        ghosts,
        defers,
        assumes,
        operators,
        uses,
        consts,
    })
}

fn obligation_name(text: &str) -> (String, &str) {
    let text = text.trim_start();
    let name: String = text
        .chars()
        .take_while(|c| c.is_ascii_alphanumeric() || *c == '.' || *c == '_' || *c == ':')
        .collect();
    let rest = text[name.len()..].trim();
    (name, rest)
}

/// A contract clause whose text still starts with `#[` carried a
/// malformed label (well-formed ones are stripped by the scanner).
pub fn validate_clause_label(clause: &Clause) -> PResult<()> {
    if matches!(
        clause.kind,
        ClauseKind::Pre
            | ClauseKind::Post
            | ClauseKind::Invariant
            | ClauseKind::Variant
            | ClauseKind::Assert
    ) && clause.text.starts_with("#[")
    {
        return Err(Diagnostic {
            name: "proof.malformed_label".into(),
            title: "malformed `#[label(...)]`".into(),
            span: clause.span,
            label: "expected `#[label(name)]` with an identifier name".into(),
            notes: vec![],
        });
    }
    Ok(())
}

fn parse_defer(clause: &Clause) -> PResult<Defer> {
    let (name, rest) = obligation_name(&clause.text);
    if name.is_empty() || !rest.is_empty() {
        return Err(Diagnostic {
            name: "proof.malformed_defer".into(),
            title: "malformed `defer` clause".into(),
            span: clause.span,
            label: "expected `defer <obligation-name>`".into(),
            notes: vec![],
        });
    }
    Ok(Defer {
        name,
        span: clause.span,
    })
}

fn parse_assume(clause: &Clause) -> PResult<Assume> {
    // `#[audit(reason := "...")] NAME` — the audit payload is mandatory:
    // an assume is a permanent, reviewed trust statement (design §9).
    let text = clause.text.trim_start();
    let missing_audit = || Diagnostic {
        name: "proof.assume_needs_audit".into(),
        title: "`assume` without an `#[audit]` payload".into(),
        span: clause.span,
        label: "an axiom must carry its justification".into(),
        notes: vec![(
            "note".into(),
            "write `assume #[audit(reason := \"...\")] <obligation-name>` (design §9)".into(),
        )],
    };
    let Some(rest) = text.strip_prefix("#[audit(reason") else {
        return Err(missing_audit());
    };
    let rest = rest.trim_start();
    let Some(rest) = rest.strip_prefix(":=") else {
        return Err(missing_audit());
    };
    let rest = rest.trim_start();
    let Some(rest) = rest.strip_prefix('"') else {
        return Err(missing_audit());
    };
    let Some(quote_end) = rest.find('"') else {
        return Err(missing_audit());
    };
    let reason = rest[..quote_end].to_string();
    let rest = rest[quote_end + 1..].trim_start();
    let Some(rest) = rest.strip_prefix(")]") else {
        return Err(missing_audit());
    };
    let (name, tail) = obligation_name(rest);
    if name.is_empty() || !tail.is_empty() || reason.trim().is_empty() {
        return Err(Diagnostic {
            name: "proof.malformed_assume".into(),
            title: "malformed `assume` clause".into(),
            span: clause.span,
            label: "expected `assume #[audit(reason := \"...\")] <obligation-name>`".into(),
            notes: vec![],
        });
    }
    Ok(Assume {
        name,
        reason,
        span: clause.span,
    })
}

/// `spec NAME : <lean-type>` inside a trait (ADR 0007).
fn parse_trait_spec(clause: &Clause) -> PResult<TraitSpecFn> {
    let text = clause.text.trim_start();
    let name: String = text
        .chars()
        .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
        .collect();
    let rest = text[name.len()..].trim_start();
    if name.is_empty() || !rest.starts_with(':') || rest[1..].trim().is_empty() {
        return Err(Diagnostic {
            name: "proof.malformed_spec".into(),
            title: "malformed `spec` clause".into(),
            span: clause.span,
            label: "expected `spec <name> : <lean-type>`".into(),
            notes: vec![],
        });
    }
    Ok(TraitSpecFn {
        name,
        sig: rest[1..].trim().to_string(),
        span: clause.span,
    })
}

fn parse_discharge(clause: &Clause) -> PResult<Discharge> {
    // Clause text: `NAME by\n  <script>` (the keyword `discharge` is
    // already stripped by the scanner).
    let text = clause.text.trim_start();
    let name: String = text
        .chars()
        .take_while(|c| c.is_ascii_alphanumeric() || *c == '.' || *c == '_' || *c == ':')
        .collect();
    let rest = text[name.len()..].trim_start();
    let malformed = || Diagnostic {
        name: "proof.malformed_discharge".into(),
        title: "malformed `discharge` clause".into(),
        span: clause.span,
        label: "expected `discharge <obligation-name> by <tactics>`".into(),
        notes: vec![],
    };
    if name.is_empty() || !rest.starts_with("by") {
        return Err(malformed());
    }
    // Dedent by the common leading indent so the emitter's uniform
    // re-indent preserves nesting.
    let raw = &rest["by".len()..];
    let lines: Vec<&str> = raw.lines().skip_while(|l| l.trim().is_empty()).collect();
    let min_indent = lines
        .iter()
        .filter(|l| !l.trim().is_empty())
        .map(|l| l.len() - l.trim_start().len())
        .min()
        .unwrap_or(0);
    let script = lines
        .iter()
        .map(|l| {
            if l.len() >= min_indent {
                &l[min_indent..]
            } else {
                l.trim_end()
            }
        })
        .collect::<Vec<_>>()
        .join(
            "
",
        )
        .trim_end()
        .to_string();
    if script.is_empty() {
        return Err(malformed());
    }
    Ok(Discharge {
        name,
        script,
        span: clause.span,
    })
}

fn kind_word(k: ClauseKind) -> &'static str {
    match k {
        ClauseKind::Pre => "pre",
        ClauseKind::Post => "post",
        ClauseKind::Invariant => "invariant",
        ClauseKind::Variant => "variant",
        ClauseKind::Assert => "assert",
        ClauseKind::Defer => "defer",
        ClauseKind::Assume => "assume",
        ClauseKind::GhostDef => "def",
        ClauseKind::Spec => "spec",
        ClauseKind::Requires => "requires",
        ClauseKind::Theorem => "theorem",
        ClauseKind::Discharge => "discharge",
        ClauseKind::Other => "<continuation>",
    }
}

impl<'a> Parser<'a> {
    fn peek(&self) -> &Tok {
        &self.tokens[self.pos].tok
    }
    fn peek2(&self) -> &Tok {
        &self.tokens[(self.pos + 1).min(self.tokens.len() - 1)].tok
    }
    fn peek_span(&self) -> Span {
        self.tokens[self.pos].span
    }
    fn peek_line(&self) -> usize {
        self.lines.line_col(self.peek_span().start).0
    }
    fn at(&self, t: &Tok) -> bool {
        self.peek() == t
    }
    fn bump(&mut self) -> Token {
        let t = self.tokens[self.pos].clone();
        if self.pos < self.tokens.len() - 1 {
            self.pos += 1;
        }
        t
    }
    fn expect(&mut self, t: Tok) -> PResult<Token> {
        if self.peek() == &t {
            Ok(self.bump())
        } else {
            Err(self.error_expected(&t.describe()))
        }
    }
    fn error_expected(&self, what: &str) -> Diagnostic {
        Diagnostic {
            name: "parse.expected".into(),
            title: format!("expected {what}, found {}", self.peek().describe()),
            span: self.peek_span(),
            label: format!("expected {what}"),
            notes: vec![],
        }
    }

    /// The proof block whose last line immediately precedes `line`, if any.
    fn take_block_ending_before(&mut self, line: usize) -> Option<&'a ProofBlock> {
        for (bi, block) in self.blocks.iter().enumerate() {
            if !self.consumed[bi] && block.last_line + 1 == line {
                self.consumed[bi] = true;
                return Some(block);
            }
        }
        None
    }

    fn token_at(&self, index: usize) -> &Token {
        self.tokens
            .get(index)
            .unwrap_or_else(|| self.tokens.last().expect("the lexer emits EOF"))
    }

    fn expected_generic_type(&self, index: usize) -> Diagnostic {
        let token = self.token_at(index);
        Diagnostic {
            name: "parse.expected_generic_type".into(),
            title: format!(
                "expected a generic type, found {}",
                token.tok.describe()
            ),
            span: token.span,
            label: "expected an integer, `bool`, a type parameter, a visible nominal type, `[T]`, or `option<T>`"
                .into(),
            notes: vec![],
        }
    }

    fn generic_type_separator_error(&self, index: usize) -> Diagnostic {
        let token = self.token_at(index);
        Diagnostic {
            name: "parse.generic_type_separator".into(),
            title: format!(
                "expected `,` or `>` in generic arguments, found {}",
                token.tok.describe()
            ),
            span: token.span,
            label: "separate type arguments with `,` and close the list with `>`".into(),
            notes: vec![],
        }
    }

    fn generic_type_depth_error(&self, index: usize) -> Diagnostic {
        Diagnostic {
            name: "parse.generic_type_too_deep".into(),
            title: "generic type is nested too deeply".into(),
            span: self.token_at(index).span,
            label: format!(
                "at most {MAX_GENERIC_TYPE_DEPTH} recursive type nodes may occur on one path"
            ),
            notes: vec![],
        }
    }

    fn generic_type_size_error(&self, index: usize) -> Diagnostic {
        Diagnostic {
            name: "parse.generic_type_too_large".into(),
            title: "generic type is too large".into(),
            span: self.token_at(index).span,
            label: format!(
                "at most {MAX_GENERIC_TYPE_NODES} nodes are allowed in one outer type argument"
            ),
            notes: vec![],
        }
    }

    fn too_many_generic_type_args(&self, index: usize) -> Diagnostic {
        Diagnostic {
            name: "parse.too_many_type_args".into(),
            title: "too many generic type arguments".into(),
            span: self.token_at(index).span,
            label: format!("at most {MAX_GENERIC_TYPE_ARGS} arguments are allowed in one list"),
            notes: vec![],
        }
    }

    /// Parse one bounded recursive type from `index`. This syntax routine is
    /// shared by lookahead and AST construction, so nested closing `>` tokens
    /// cannot be interpreted differently by the two paths.
    fn parse_generic_type_syntax_at(
        &self,
        index: &mut usize,
        depth: usize,
        budget: &mut GenericTypeBudget,
    ) -> PResult<GenericTypeSyntax> {
        if depth > MAX_GENERIC_TYPE_DEPTH {
            return Err(self.generic_type_depth_error(*index));
        }
        if budget.nodes == MAX_GENERIC_TYPE_NODES {
            return Err(self.generic_type_size_error(*index));
        }
        budget.nodes += 1;

        let token = self.token_at(*index).clone();
        match token.tok {
            Tok::Ident(name) => {
                *index += 1;
                let mut span = token.span;
                let args = if self.token_at(*index).tok == Tok::Lt {
                    let (args, close) =
                        self.parse_nested_generic_type_list(index, depth + 1, budget)?;
                    span = span.join(close);
                    Some(args)
                } else {
                    None
                };
                Ok(GenericTypeSyntax {
                    kind: GenericTypeSyntaxKind::Named {
                        name,
                        name_span: token.span,
                        args,
                    },
                    span,
                })
            }
            Tok::LBracket => {
                *index += 1;
                let element = self.parse_generic_type_syntax_at(index, depth + 1, budget)?;
                if self.token_at(*index).tok != Tok::RBracket {
                    let found = self.token_at(*index);
                    return Err(Diagnostic {
                        name: "parse.generic_array_close".into(),
                        title: format!(
                            "expected `]` after generic array element, found {}",
                            found.tok.describe()
                        ),
                        span: found.span,
                        label: "close the generic array type with `]`".into(),
                        notes: vec![],
                    });
                }
                let close = self.token_at(*index).span;
                *index += 1;
                Ok(GenericTypeSyntax {
                    kind: GenericTypeSyntaxKind::Array(Box::new(element)),
                    span: token.span.join(close),
                })
            }
            _ => Err(self.expected_generic_type(*index)),
        }
    }

    /// Parse a nested `<...>` list. Every nested list has its own arity cap,
    /// while all of its nodes charge the enclosing outer-argument budget.
    fn parse_nested_generic_type_list(
        &self,
        index: &mut usize,
        child_depth: usize,
        budget: &mut GenericTypeBudget,
    ) -> PResult<(Vec<GenericTypeSyntax>, Span)> {
        debug_assert_eq!(self.token_at(*index).tok, Tok::Lt);
        *index += 1;
        if self.token_at(*index).tok == Tok::Gt {
            return Err(self.expected_generic_type(*index));
        }

        let mut args = Vec::new();
        loop {
            if args.len() == MAX_GENERIC_TYPE_ARGS {
                return Err(self.too_many_generic_type_args(*index));
            }
            args.push(self.parse_generic_type_syntax_at(index, child_depth, budget)?);
            match &self.token_at(*index).tok {
                Tok::Comma => *index += 1,
                Tok::Gt => {
                    let close = self.token_at(*index).span;
                    *index += 1;
                    return Ok((args, close));
                }
                _ => return Err(self.generic_type_separator_error(*index)),
            }
        }
    }

    /// Parse the outer use-site `<...>` list. The node budget resets for each
    /// argument, as promised by the public limit.
    fn parse_type_arg_syntax_list_at(&self, start: usize) -> PResult<ParsedTypeArgList> {
        debug_assert_eq!(self.token_at(start).tok, Tok::Lt);
        let mut index = start + 1;
        if self.token_at(index).tok == Tok::Gt {
            return Err(self.expected_generic_type(index));
        }

        let mut args = Vec::new();
        loop {
            if args.len() == MAX_GENERIC_TYPE_ARGS {
                return Err(self.too_many_generic_type_args(index));
            }
            let mut budget = GenericTypeBudget::default();
            args.push(self.parse_generic_type_syntax_at(&mut index, 1, &mut budget)?);
            match &self.token_at(index).tok {
                Tok::Comma => index += 1,
                Tok::Gt => {
                    index += 1;
                    return Ok(ParsedTypeArgList { args, end: index });
                }
                _ => return Err(self.generic_type_separator_error(index)),
            }
        }
    }

    fn generic_class_arity(&self, name: &str) -> Option<usize> {
        self.generic_class_names
            .iter()
            .find(|class| class.name == name)
            .map(|class| class.arity)
    }

    fn generic_type_arity_error(
        &self,
        name: &str,
        expected: usize,
        actual: usize,
        span: Span,
        diagnostic_name: &str,
    ) -> Diagnostic {
        Diagnostic {
            name: diagnostic_name.into(),
            title: format!("wrong number of type arguments for `{name}`"),
            span,
            label: format!("expected {expected}, found {actual}"),
            notes: vec![],
        }
    }

    fn lower_generic_type(&self, syntax: &GenericTypeSyntax) -> PResult<GenericTy> {
        let GenericTypeSyntaxKind::Named {
            name,
            name_span,
            args,
        } = &syntax.kind
        else {
            let GenericTypeSyntaxKind::Array(element) = &syntax.kind else {
                unreachable!()
            };
            return Ok(GenericTy::Array(Box::new(
                self.lower_generic_type(element)?,
            )));
        };

        let actual = args.as_ref().map_or(0, Vec::len);
        if let Some(integer) = IntTy::from_name(name) {
            if args.is_some() {
                return Err(self.generic_type_arity_error(
                    name,
                    0,
                    actual,
                    syntax.span,
                    "parse.primitive_type_args",
                ));
            }
            return Ok(GenericTy::Int(integer));
        }
        if name == "bool" {
            if args.is_some() {
                return Err(self.generic_type_arity_error(
                    name,
                    0,
                    actual,
                    syntax.span,
                    "parse.primitive_type_args",
                ));
            }
            return Ok(GenericTy::Bool);
        }
        if let Some(parameter) = self.tparams.iter().position(|candidate| candidate == name) {
            if args.is_some() {
                return Err(self.generic_type_arity_error(
                    name,
                    0,
                    actual,
                    syntax.span,
                    "parse.type_parameter_args",
                ));
            }
            return Ok(GenericTy::Param(
                TypeParamId::new(parameter)
                    .expect("type_param_list enforces the type-parameter ceiling"),
            ));
        }
        if name == "option" {
            if actual != 1 {
                return Err(self.generic_type_arity_error(
                    name,
                    1,
                    actual,
                    syntax.span,
                    "parse.option_type_arity",
                ));
            }
            let element = self.lower_generic_type(&args.as_ref().expect("one argument")[0])?;
            return Ok(GenericTy::Option(Box::new(element)));
        }
        if let Some(expected) = self.generic_class_arity(name) {
            if actual != expected {
                let diagnostic_name = if args.is_none() && expected != 0 {
                    "parse.unsaturated_generic_class"
                } else if args.is_some() && expected == 0 {
                    "parse.nongeneric_class_type_args"
                } else {
                    "parse.generic_class_arity"
                };
                return Err(self.generic_type_arity_error(
                    name,
                    expected,
                    actual,
                    syntax.span,
                    diagnostic_name,
                ));
            }
            let lowered = match args {
                Some(args) => args
                    .iter()
                    .map(|argument| self.lower_generic_type(argument))
                    .collect::<PResult<Vec<_>>>()?,
                None => Vec::new(),
            };
            return Ok(GenericTy::Class {
                name: name.clone(),
                args: lowered.into_boxed_slice(),
            });
        }
        if self.record_names.iter().any(|record| record == name) {
            if args.is_some() {
                return Err(self.generic_type_arity_error(
                    name,
                    0,
                    actual,
                    syntax.span,
                    "parse.record_type_args",
                ));
            }
            return Ok(GenericTy::Record(name.clone()));
        }
        Err(Diagnostic {
            name: "parse.unknown_generic_type".into(),
            title: format!("unknown generic type `{name}`"),
            span: *name_span,
            label: "not an integer, `bool`, an in-scope type parameter, or a visible nominal type"
                .into(),
            notes: vec![],
        })
    }

    /// Independently bounded, non-recursive syntax probe used only after the
    /// main bounded parser reports an error. It carries limit diagnostics out
    /// when the candidate is otherwise a complete generic call. Expression
    /// operators and misplaced brackets terminate the probe, so a later
    /// comparison cannot be mistaken for this candidate's close.
    fn malformed_generic_list_has_call_follower(&self, start: usize) -> bool {
        debug_assert_eq!(self.token_at(start).tok, Tok::Lt);
        let mut index = start + 1;
        let recovery_end = start.saturating_add(MAX_GENERIC_RECOVERY_TOKENS);
        let mut frames = vec![GenericRecoveryFrame::ListNeedType];
        loop {
            if index > recovery_end || frames.len() > MAX_GENERIC_TYPE_DEPTH + 1 {
                return false;
            }
            let Some(frame) = frames.last().copied() else {
                return matches!(&self.token_at(index).tok, Tok::LParen | Tok::ColonColon);
            };
            match frame {
                GenericRecoveryFrame::ListNeedType | GenericRecoveryFrame::ArrayNeedType => {
                    match &self.token_at(index).tok {
                        Tok::Ident(_) => {
                            index += 1;
                            if self.token_at(index).tok == Tok::Lt {
                                index += 1;
                                frames.push(GenericRecoveryFrame::ListNeedType);
                            } else {
                                *frames.last_mut().expect("frame exists") = match frame {
                                    GenericRecoveryFrame::ListNeedType => {
                                        GenericRecoveryFrame::ListNeedSeparator
                                    }
                                    GenericRecoveryFrame::ArrayNeedType => {
                                        GenericRecoveryFrame::ArrayNeedClose
                                    }
                                    _ => unreachable!(),
                                };
                            }
                        }
                        Tok::LBracket => {
                            index += 1;
                            frames.push(GenericRecoveryFrame::ArrayNeedType);
                        }
                        _ => return false,
                    }
                }
                GenericRecoveryFrame::ListNeedSeparator => match &self.token_at(index).tok {
                    Tok::Comma => {
                        index += 1;
                        *frames.last_mut().expect("frame exists") =
                            GenericRecoveryFrame::ListNeedType;
                    }
                    Tok::Gt => {
                        index += 1;
                        frames.pop();
                        if let Some(parent) = frames.last_mut() {
                            *parent = match parent {
                                GenericRecoveryFrame::ListNeedType => {
                                    GenericRecoveryFrame::ListNeedSeparator
                                }
                                GenericRecoveryFrame::ArrayNeedType => {
                                    GenericRecoveryFrame::ArrayNeedClose
                                }
                                _ => return false,
                            };
                        }
                    }
                    _ => return false,
                },
                GenericRecoveryFrame::ArrayNeedClose => {
                    if self.token_at(index).tok != Tok::RBracket {
                        return false;
                    }
                    index += 1;
                    frames.pop();
                    let Some(parent) = frames.last_mut() else {
                        return false;
                    };
                    *parent = match parent {
                        GenericRecoveryFrame::ListNeedType => {
                            GenericRecoveryFrame::ListNeedSeparator
                        }
                        GenericRecoveryFrame::ArrayNeedType => GenericRecoveryFrame::ArrayNeedClose,
                        _ => return false,
                    };
                }
            }
        }
    }

    /// Disambiguate `f<T>(...)` / `C<T>::...` from comparisons. The same
    /// bounded recursive grammar used by `type_arg_list` performs lookahead;
    /// only a complete list followed by `(` or `::` is a generic use.
    fn at_generic_args(&self) -> PResult<bool> {
        // Builtin angle-bracket forms have dedicated arms.
        if matches!(self.peek(), Tok::Ident(n) if n == "widen" || n == "narrow" || n == "alloc_array")
        {
            return Ok(false);
        }
        let start = self.pos + 1;
        if self.tokens.get(start).map(|token| &token.tok) != Some(&Tok::Lt) {
            return Ok(false);
        }
        let parsed = match self.parse_type_arg_syntax_list_at(start) {
            Ok(parsed) => parsed,
            Err(error) if self.malformed_generic_list_has_call_follower(start) => {
                return Err(error);
            }
            Err(_) => return Ok(false),
        };
        let follower = &self.token_at(parsed.end).tok;
        if !matches!(follower, Tok::LParen | Tok::ColonColon) {
            return Ok(false);
        }
        for argument in &parsed.args {
            if let Err(error) = self.lower_generic_type(argument) {
                // Preserve the historical comparison disambiguation for an
                // arbitrary identifier: `x < y > (z)` is not a generic call
                // merely because its punctuation happens to fit. `::`, on
                // the other hand, cannot continue a comparison.
                if error.name == "parse.unknown_generic_type" && follower == &Tok::LParen {
                    return Ok(false);
                }
                return Err(error);
            }
        }
        Ok(true)
    }

    fn ident(&mut self) -> PResult<(String, Span)> {
        match self.peek().clone() {
            Tok::Ident(name) => {
                let span = self.peek_span();
                self.bump();
                Ok((name, span))
            }
            _ => Err(self.error_expected("an identifier")),
        }
    }

    fn int_ty(&mut self) -> PResult<(IntTy, Span)> {
        let (name, span) = self.ident()?;
        if let Some(i) = self.tparams.iter().position(|p| *p == name) {
            let index = u8::try_from(i)
                .expect("type_param_list enforces the legacy type-parameter ceiling");
            return Ok((IntTy::TParam(index), span));
        }
        IntTy::from_name(&name)
            .map(|t| (t, span))
            .ok_or_else(|| Diagnostic {
                name: "parse.unknown_type".into(),
                title: format!("unknown integer type `{name}`"),
                span,
                label: "expected `u8`..`u64`, `i8`..`i64`, or an in-scope type parameter".into(),
                notes: vec![],
            })
    }

    /// The currently admitted array payload grammar: concrete integer types
    /// plus an in-scope declaration parameter. Unlike `int_ty`, this preserves
    /// a parameter as `ValueTy::Param`, so later stages cannot infer integer
    /// semantics from its representation. Boolean and record arrays remain a
    /// later G1 semantic slice.
    fn value_ty(&mut self) -> PResult<(ValueTy, Span)> {
        let (name, span) = self.ident()?;
        if let Some(index) = self.tparams.iter().position(|parameter| *parameter == name) {
            let parameter = TypeParamId::new(index)
                .expect("type_param_list enforces the type-parameter ceiling");
            return Ok((ValueTy::Param(parameter), span));
        }
        IntTy::from_name(&name)
            .map(|ty| (ValueTy::Int(ty), span))
            .ok_or_else(|| Diagnostic {
                name: "parse.unknown_type".into(),
                title: format!("unknown integer type `{name}`"),
                span,
                label: "expected `u8`..`u64`, `i8`..`i64`, or an in-scope type parameter".into(),
                notes: vec![],
            })
    }

    /// The first non-integer aggregate slice is deliberately option-specific:
    /// integers and declaration parameters retain their existing behavior,
    /// while `bool` gains a payload identity without also admitting `[bool]`
    /// or `alloc_array<bool>`. Visible POD records are represented honestly so
    /// the checker can reject them at its semantic boundary with a stable
    /// diagnostic; classes and nested aggregates are not value payloads here.
    fn option_value_ty(&mut self) -> PResult<(ValueTy, Span)> {
        let (name, span) = self.ident()?;
        if name == "bool" {
            return Ok((ValueTy::Bool, span));
        }
        if let Some(index) = self.tparams.iter().position(|parameter| *parameter == name) {
            let parameter = TypeParamId::new(index)
                .expect("type_param_list enforces the type-parameter ceiling");
            return Ok((ValueTy::Param(parameter), span));
        }
        if let Some(ty) = IntTy::from_name(&name) {
            return Ok((ValueTy::Int(ty), span));
        }
        if let Some(record) = self
            .record_names
            .iter()
            .position(|candidate| *candidate == name)
        {
            return Ok((ValueTy::Record(record), span));
        }
        Err(Diagnostic {
            name: "parse.unknown_type".into(),
            title: format!("unknown option payload type `{name}`"),
            span,
            label: "expected `bool`, `u8`..`u64`, `i8`..`i64`, or an in-scope type parameter"
                .into(),
            notes: vec![],
        })
    }

    /// `<T, U>` / `<K: Hashable, V>` after a declaration name.
    fn type_param_list(&mut self) -> PResult<(Vec<String>, Vec<Option<String>>)> {
        if !self.at(&Tok::Lt) {
            return Ok((Vec::new(), Vec::new()));
        }
        self.bump();
        let mut out = Vec::new();
        let mut bounds = Vec::new();
        loop {
            let (name, span) = self.ident()?;
            if IntTy::from_name(&name).is_some() || is_reserved_name(&name) {
                return Err(Diagnostic {
                    name: "parse.bad_type_param".into(),
                    title: format!("`{name}` cannot be a type parameter"),
                    span,
                    label: "shadows a concrete type or reserved name".into(),
                    notes: vec![],
                });
            }
            if out.iter().any(|parameter| parameter == &name) {
                return Err(Diagnostic {
                    name: "parse.duplicate_type_param".into(),
                    title: format!("duplicate type parameter `{name}`"),
                    span,
                    label: "type parameter names must be unique".into(),
                    notes: vec![],
                });
            }
            if out.len() == MAX_TYPE_PARAMS {
                return Err(Diagnostic {
                    name: "parse.too_many_type_params".into(),
                    title: "too many type parameters".into(),
                    span,
                    label: format!("at most {MAX_TYPE_PARAMS} type parameters are supported"),
                    notes: vec![],
                });
            }
            out.push(name);
            if self.at(&Tok::Colon) {
                self.bump();
                let (bound, _) = self.ident()?;
                bounds.push(Some(bound));
            } else {
                bounds.push(None);
            }
            if self.at(&Tok::Comma) {
                self.bump();
            } else {
                break;
            }
        }
        self.expect(Tok::Gt)?;
        Ok((out, bounds))
    }

    /// A bounded recursive `<...>` list at a generic use site. Checked `Ty`
    /// contexts deliberately do not call this routine: G0 only records the
    /// richer use-site shape, and monomorphization remains the hard semantic
    /// gate for the currently enabled integer-only domain.
    fn type_arg_list(&mut self) -> PResult<Vec<TypeArg>> {
        let parsed = self.parse_type_arg_syntax_list_at(self.pos)?;
        let out = parsed
            .args
            .iter()
            .map(|argument| {
                Ok(TypeArg {
                    ty: self.lower_generic_type(argument)?,
                    span: argument.span,
                })
            })
            .collect::<PResult<Vec<_>>>()?;
        self.pos = parsed.end;
        Ok(out)
    }

    /// A parameter type: scalar, `&C`, `&mut C`, `&[T]`, `&mut [T]`, or a
    /// resource — `resource R`, `resource &R`, `resource &mut R`.
    fn param_ty(&mut self) -> PResult<(Ty, Span)> {
        if self.at(&Tok::KwResource) {
            return self.resource_ty();
        }
        if self.at(&Tok::KwRaw) {
            return self.raw_ty();
        }
        if matches!(self.peek(), Tok::Ident(n) if n == "option") {
            return self.option_ty();
        }
        if self.at(&Tok::Amp) {
            let start = self.bump().span;
            let mutability = if matches!(self.peek(), Tok::Ident(m) if m == "mut") {
                self.bump();
                Mutability::Mut
            } else {
                Mutability::Shared
            };
            // `&Nat` (ADR 0010) or `&mut Nat` (ADR 0023) — a class borrow.
            if let Tok::Ident(n) = self.peek() {
                if let Some(ci) = self.class_names.iter().position(|c| c == n) {
                    let end = self.bump().span;
                    return Ok((Ty::ClassRef(ci, mutability), start.join(end)));
                }
            }
            self.expect(Tok::LBracket)?;
            let (elem, _) = self.value_ty()?;
            let end = self.expect(Tok::RBracket)?.span;
            return Ok((Ty::Array(elem, mutability), start.join(end)));
        }
        // `Nat m` — a class taken by value: the argument is moved into
        // the callee (classes are affine).
        if let Tok::Ident(n) = self.peek() {
            if let Some(ci) = self.class_names.iter().position(|c| c == n) {
                let span = self.bump().span;
                return Ok((Ty::Class(ci), span));
            }
            if let Some(ri) = self.record_names.iter().position(|r| r == n) {
                let span = self.bump().span;
                return Ok((Ty::Record(ri), span));
            }
        }
        self.scalar_ty()
    }

    /// `raw<u8>` — a raw pointer type.
    fn raw_ty(&mut self) -> PResult<(Ty, Span)> {
        let start = self.expect(Tok::KwRaw)?.span;
        self.expect(Tok::Lt)?;
        if let Tok::Ident(name) = self.peek() {
            if let Some(ri) = self.record_names.iter().position(|r| r == name) {
                let elem_span = self.bump().span;
                let end = self.expect(Tok::Gt)?.span;
                return Ok((Ty::RawRecord(ri), start.join(elem_span).join(end)));
            }
        }
        let (elem, elem_span) = self.int_ty()?;
        let end = self.expect(Tok::Gt)?.span;
        if elem != IntTy::U8 {
            return Err(Diagnostic {
                name: "raw.element_type".into(),
                title: format!("`raw<{}>` is not supported yet", elem.name()),
                span: elem_span,
                label: "only `raw<u8>` for now".into(),
                notes: vec![(
                    "note".into(),
                    "wider raw access needs typed storage, which is a scheduled \
                     deliverable; byte-at-a-time comes first so no layout question \
                     is answered by accident"
                        .into(),
                )],
            });
        }
        Ok((Ty::Raw(elem), start.join(end)))
    }

    /// The option families currently admitted by the parser: integer/Boolean
    /// value options (plus retained declaration parameters), and nullable
    /// pointers to explicit records. POD record values reach the checker only
    /// to receive the G1 semantic-boundary diagnostic.
    fn option_ty(&mut self) -> PResult<(Ty, Span)> {
        let (name, start) = self.ident()?;
        debug_assert_eq!(name, "option");
        self.expect(Tok::Lt)?;
        if self.at(&Tok::KwRaw) {
            let (raw, _) = self.raw_ty()?;
            let end = self.expect(Tok::Gt)?.span;
            return match raw {
                Ty::RawRecord(ri) => Ok((Ty::OptionRaw(ri), start.join(end))),
                _ => Err(Diagnostic {
                    name: "record.option_pointer_type".into(),
                    title: "nullable raw pointers require a record pointee".into(),
                    span: start.join(end),
                    label: "expected `option<raw<Record>>`".into(),
                    notes: vec![(
                        "note".into(),
                        "integer options remain `option<u8>` through `option<u64>`; raw byte \
                         pointers do not yet have a nullable storage role"
                            .into(),
                    )],
                }),
            };
        }
        let (elem, _) = self.option_value_ty()?;
        let end = self.expect(Tok::Gt)?.span;
        Ok((Ty::Option(elem), start.join(end)))
    }

    fn signed_int_literal(&mut self) -> PResult<(i128, Span)> {
        let neg = if self.at(&Tok::Minus) {
            Some(self.bump().span)
        } else {
            None
        };
        match self.bump() {
            Token {
                tok: Tok::Int(n),
                span,
            } => Ok((
                if neg.is_some() { -n } else { n },
                neg.map_or(span, |s| s.join(span)),
            )),
            t => Err(Diagnostic {
                name: "parse.expected".into(),
                title: "expected an integer literal".into(),
                span: t.span,
                label: "layout geometry must be a literal".into(),
                notes: vec![],
            }),
        }
    }

    fn record_field_ty(&mut self) -> PResult<(Ty, Span)> {
        if self.at(&Tok::KwRaw) {
            return self.raw_ty();
        }
        if matches!(self.peek(), Tok::Ident(n) if n == "option") {
            return self.option_ty();
        }
        self.scalar_ty()
    }

    /// `resource R` (owned, moved), `resource &R`, or `resource &mut R`.
    /// The category is written before the borrow marker so that a reader
    /// sees "this is authority" before anything else about the type.
    fn resource_ty(&mut self) -> PResult<(Ty, Span)> {
        let start = self.expect(Tok::KwResource)?.span;
        let mutability = if self.at(&Tok::Amp) {
            self.bump();
            if matches!(self.peek(), Tok::Ident(m) if m == "mut") {
                self.bump();
                Some(Mutability::Mut)
            } else {
                Some(Mutability::Shared)
            }
        } else {
            None
        };
        let (name, name_span) = self.ident()?;
        let (kind, end_span) = if name == "ResourceMap" {
            self.expect(Tok::Lt)?;
            let (key, key_span) = self.int_ty()?;
            self.expect(Tok::Comma)?;
            let (value_name, value_span) = self.ident()?;
            if value_name != "PointsTo" {
                return Err(Diagnostic {
                    name: "resource.map_type".into(),
                    title: "this `ResourceMap` value type is not supported yet".into(),
                    span: value_span,
                    label: "the first aggregate slice requires `PointsTo<u64>`".into(),
                    notes: vec![(
                        "note".into(),
                        "the surface is parameterized so later resource kinds reuse the same \
                         aggregate abstraction; for now only \
                         `ResourceMap<u64, PointsTo<u64>>` has sealed operations"
                            .into(),
                    )],
                });
            }
            self.expect(Tok::Lt)?;
            let (record_elem, value_elem_span) = if let Tok::Ident(elem) = self.peek() {
                if let Some(ri) = self.record_names.iter().position(|r| r == elem) {
                    let span = self.bump().span;
                    (Some(ri), span)
                } else {
                    let (elem, span) = self.int_ty()?;
                    if elem != IntTy::U64 {
                        return Err(Diagnostic {
                            name: "resource.map_type".into(),
                            title: "this `ResourceMap` value type is not supported yet".into(),
                            span,
                            label: "expected `PointsTo<u64>` or `PointsTo<Record>`".into(),
                            notes: vec![],
                        });
                    }
                    (None, span)
                }
            } else {
                let (elem, span) = self.int_ty()?;
                if elem != IntTy::U64 {
                    return Err(Diagnostic {
                        name: "resource.map_type".into(),
                        title: "this `ResourceMap` value type is not supported yet".into(),
                        span,
                        label: "expected `PointsTo<u64>` or `PointsTo<Record>`".into(),
                        notes: vec![],
                    });
                }
                (None, span)
            };
            self.expect(Tok::Gt)?;
            let end = self.expect(Tok::Gt)?.span;
            if key != IntTy::U64 {
                return Err(Diagnostic {
                    name: "resource.map_type".into(),
                    title: "this `ResourceMap` instantiation is not supported yet".into(),
                    span: key_span,
                    label: "resource-map keys are `u64` arena offsets in v1".into(),
                    notes: vec![(
                        "note".into(),
                        "the one-arena intrusive-list profile deliberately avoids \
                         cross-allocation pointer keys"
                            .into(),
                    )],
                });
            }
            let _ = value_elem_span;
            (
                record_elem.map_or(
                    ResKind::ResourceMapPointsToU64,
                    ResKind::ResourceMapPointsToRecord,
                ),
                end,
            )
        } else if name == "PointsTo" || name == "LeasedPointsTo" {
            self.expect(Tok::Lt)?;
            if let Tok::Ident(elem) = self.peek() {
                if let Some(ri) = self.record_names.iter().position(|r| r == elem) {
                    let elem_span = self.bump().span;
                    let end = self.expect(Tok::Gt)?.span;
                    if name == "LeasedPointsTo" {
                        return Err(Diagnostic {
                            name: "resource.points_to_type".into(),
                            title: "allocator leases support only `u64` typed cells".into(),
                            span: elem_span,
                            label: "use ordinary `PointsTo<Record>` authority".into(),
                            notes: vec![],
                        });
                    }
                    (ResKind::PointsToRecord(ri), end)
                } else {
                    let (elem, elem_span) = self.int_ty()?;
                    let end = self.expect(Tok::Gt)?.span;
                    if elem != IntTy::U64 {
                        return Err(Diagnostic {
                            name: "resource.points_to_type".into(),
                            title: format!("`PointsTo<{}>` is not supported yet", elem.name()),
                            span: elem_span,
                            label: "expected `PointsTo<u64>` or `PointsTo<Record>`".into(),
                            notes: vec![],
                        });
                    }
                    (
                        if name == "PointsTo" {
                            ResKind::PointsToU64
                        } else {
                            ResKind::LeasedPointsToU64
                        },
                        end,
                    )
                }
            } else {
                let (elem, elem_span) = self.int_ty()?;
                let end = self.expect(Tok::Gt)?.span;
                if elem != IntTy::U64 {
                    return Err(Diagnostic {
                        name: "resource.points_to_type".into(),
                        title: format!("`PointsTo<{}>` is not supported yet", elem.name()),
                        span: elem_span,
                        label: "expected `PointsTo<u64>` or `PointsTo<Record>`".into(),
                        notes: vec![],
                    });
                }
                (
                    if name == "PointsTo" {
                        ResKind::PointsToU64
                    } else {
                        ResKind::LeasedPointsToU64
                    },
                    end,
                )
            }
        } else {
            let Some(kind) = ResKind::from_name(&name) else {
                return Err(Diagnostic {
                    name: "resource.unknown_type".into(),
                    title: format!("unknown resource type `{name}`"),
                    span: name_span,
                    label: "expected `RawSpan`, `PointsTo<u64>`, or a built-in resource".into(),
                    notes: vec![(
                        "note".into(),
                        "resource types are compiler-defined; a program may not declare \
                         one, because it must not be able to fabricate authority by \
                         constructing a view-shaped value"
                            .into(),
                    )],
                });
            };
            (kind, name_span)
        };
        let ty = match mutability {
            Some(m) => Ty::ResRef(kind, m),
            None => Ty::Res(kind),
        };
        Ok((ty, start.join(end_span)))
    }

    fn scalar_ty(&mut self) -> PResult<(Ty, Span)> {
        let (name, span) = self.ident()?;
        if name == "bool" {
            return Ok((Ty::Bool, span));
        }
        if let Some(i) = self.tparams.iter().position(|p| *p == name) {
            let parameter =
                TypeParamId::new(i).expect("type_param_list enforces the type-parameter ceiling");
            return Ok((Ty::Param(parameter), span));
        }
        IntTy::from_name(&name)
            .map(|t| (Ty::Int(t), span))
            .ok_or_else(|| Diagnostic {
                name: "parse.unknown_type".into(),
                title: format!("unknown type `{name}`"),
                span,
                label: "expected `u8`..`u64`, `i8`..`i64`, or `bool`".into(),
                notes: vec![],
            })
    }

    /// A return type: scalar, `option<T>`, a class (ADR 0010), or an
    /// owned resource (ADR 0024).
    fn ret_ty(&mut self) -> PResult<Ty> {
        if self.at(&Tok::KwResource) {
            return Ok(self.resource_ty()?.0);
        }
        if self.at(&Tok::KwRaw) {
            return Ok(self.raw_ty()?.0);
        }
        if let Tok::Ident(name) = self.peek() {
            if let Some(ci) = self.class_names.iter().position(|c| c == name) {
                self.bump();
                return Ok(Ty::Class(ci));
            }
            if let Some(ri) = self.record_names.iter().position(|r| r == name) {
                self.bump();
                return Ok(Ty::Record(ri));
            }
            if name == "option" {
                return Ok(self.option_ty()?.0);
            }
        }
        Ok(self.scalar_ty()?.0)
    }

    /// `class Name { fields... /// invariant ... init ... fn ... deinit }`
    /// (design §7). Blocks immediately preceding an init/method are its
    /// contract; remaining blocks inside the body are the class invariant.
    fn parse_class(&mut self) -> PResult<ClassDecl> {
        let start = self.expect(Tok::KwClass)?.span;
        let (name, name_span) = self.ident()?;
        let (tp, type_bounds) = self.type_param_list()?;
        self.tparams = tp;
        let type_params = self.tparams.clone();
        self.expect(Tok::LBrace)?;
        let mut fields = Vec::new();
        let mut inits = Vec::new();
        let mut methods = Vec::new();
        let mut deinit = None;
        let body_first_line = self.peek_line();

        while !self.at(&Tok::RBrace) {
            if self.at(&Tok::Eof) {
                return Err(self.error_expected("`}`"));
            }
            let item_line = self.peek_line();
            match self.peek().clone() {
                Tok::KwInit => {
                    let mut f = self.parse_init()?;
                    self.attach_member_contract(item_line, &mut f, "an `init`")?;
                    inits.push(f);
                }
                Tok::KwFn => {
                    let mut m = self.parse_method()?;
                    self.attach_member_contract(item_line, &mut m.f, "a method")?;
                    methods.push(m);
                }
                Tok::KwDeinit => {
                    self.bump();
                    if deinit.replace(self.block()?).is_some() {
                        return Err(Diagnostic {
                            name: "parse.duplicate_deinit".into(),
                            title: "a class has at most one `deinit`".into(),
                            span: self.peek_span(),
                            label: "second `deinit`".into(),
                            notes: vec![],
                        });
                    }
                }
                Tok::Hash => {
                    // `#[must_consume] resource R f;` — the attribute goes
                    // before the field, and only a resource may carry it.
                    self.bump();
                    self.expect(Tok::LBracket)?;
                    let (attr, aspan) = self.ident()?;
                    if attr != "must_consume" {
                        return Err(Diagnostic {
                            name: "parse.unknown_field_attr".into(),
                            title: format!("unknown field attribute `{attr}`"),
                            span: aspan,
                            label: "expected `must_consume`".into(),
                            notes: vec![],
                        });
                    }
                    self.expect(Tok::RBracket)?;
                    if !self.at(&Tok::KwResource) {
                        return Err(Diagnostic {
                            name: "resource.must_consume_non_resource".into(),
                            title: "`#[must_consume]` applies to a resource field".into(),
                            span: aspan,
                            label: "an ordinary value has nothing to hand on".into(),
                            notes: vec![(
                                "note".into(),
                                "the marker says this field's *authority* must be handed \
                                 on by `deinit`; a number or an array has none"
                                    .into(),
                            )],
                        });
                    }
                    let (ty, _) = self.resource_ty()?;
                    let (fname, fspan) = self.ident()?;
                    self.expect(Tok::Semi)?;
                    fields.push(Field {
                        name: fname,
                        ty,
                        span: fspan,
                        must_consume: true,
                    });
                }
                Tok::KwResource => {
                    let (ty, _) = self.resource_ty()?;
                    let (fname, fspan) = self.ident()?;
                    self.expect(Tok::Semi)?;
                    fields.push(Field {
                        name: fname,
                        ty,
                        span: fspan,
                        must_consume: false,
                    });
                }
                Tok::LBracket => {
                    self.bump();
                    let (elem, _) = self.value_ty()?;
                    self.expect(Tok::RBracket)?;
                    let (fname, fspan) = self.ident()?;
                    self.expect(Tok::Semi)?;
                    fields.push(Field {
                        name: fname,
                        ty: Ty::Array(elem, Mutability::Owned),
                        span: fspan,
                        must_consume: false,
                    });
                }
                Tok::Ident(n) => {
                    // Parse value-option fields honestly so the checker can
                    // keep their storage boundary closed with a dedicated
                    // diagnostic. A class-typed field owns its value (and is
                    // dropped with it, in reverse declaration order).
                    let ty = if n == "option" && self.peek2() == &Tok::Lt {
                        self.option_ty()?.0
                    } else {
                        match self.class_names.iter().position(|c| *c == n) {
                            Some(ci) => {
                                self.bump();
                                Ty::Class(ci)
                            }
                            None => self.scalar_ty()?.0,
                        }
                    };
                    let (fname, fspan) = self.ident()?;
                    self.expect(Tok::Semi)?;
                    fields.push(Field {
                        name: fname,
                        ty,
                        span: fspan,
                        must_consume: false,
                    });
                }
                _ => return Err(self.error_expected("a field, `init`, `fn`, or `deinit`")),
            }
        }
        let end = self.expect(Tok::RBrace)?.span;
        let body_last_line = self.lines.line_col(end.start).0;

        // Remaining blocks inside the body are the class invariant.
        let mut invariants = Vec::new();
        for (bi, block) in self.blocks.iter().enumerate() {
            if self.consumed[bi]
                || block.first_line < body_first_line
                || block.last_line > body_last_line
            {
                continue;
            }
            self.consumed[bi] = true;
            for clause in &block.clauses {
                validate_clause_label(clause)?;
                if clause.kind == ClauseKind::Invariant {
                    invariants.push(clause.clone());
                } else {
                    return Err(bad_clause(
                        clause.kind,
                        clause,
                        "a class body",
                        "free blocks inside a class hold only `invariant` clauses",
                    ));
                }
            }
        }

        self.tparams.clear();
        Ok(ClassDecl {
            is_pub: false,
            name,
            name_span,
            type_params,
            type_bounds,
            proof_reuse: ProofReuse::None,
            fields,
            invariants,
            inits,
            methods,
            deinit,
            span: start.join(end),
        })
    }

    /// A POD record has no members or proof blocks. Its complete target
    /// geometry is stated explicitly and checked later against the field
    /// layouts (ADR 0054):
    ///
    /// `record R #[layout(size := N, align := A)] {`
    /// `  #[offset(K)] T field;`
    /// `}`
    fn parse_record(&mut self) -> PResult<RecordDecl> {
        let start = self.expect(Tok::KwRecord)?.span;
        let (name, name_span) = self.ident()?;

        self.expect(Tok::Hash)?;
        self.expect(Tok::LBracket)?;
        let (attr, attr_span) = self.ident()?;
        if attr != "layout" {
            return Err(Diagnostic {
                name: "record.missing_layout".into(),
                title: format!("record `{name}` needs an explicit layout"),
                span: attr_span,
                label: "expected `layout(size := ..., align := ...)`".into(),
                notes: vec![(
                    "note".into(),
                    "raw-storable records do not inherit class layout or an implicit ABI".into(),
                )],
            });
        }
        self.expect(Tok::LParen)?;
        let (size_key, size_key_span) = self.ident()?;
        if size_key != "size" {
            return Err(Diagnostic {
                name: "record.layout_syntax".into(),
                title: "record layout starts with `size`".into(),
                span: size_key_span,
                label: "expected `size := <literal>`".into(),
                notes: vec![],
            });
        }
        self.expect(Tok::Colon)?;
        self.expect(Tok::Assign)?;
        let (size, size_span) = self.signed_int_literal()?;
        self.expect(Tok::Comma)?;
        let (align_key, align_key_span) = self.ident()?;
        if align_key != "align" {
            return Err(Diagnostic {
                name: "record.layout_syntax".into(),
                title: "record layout needs `align` after `size`".into(),
                span: align_key_span,
                label: "expected `align := <literal>`".into(),
                notes: vec![],
            });
        }
        self.expect(Tok::Colon)?;
        self.expect(Tok::Assign)?;
        let (align, align_span) = self.signed_int_literal()?;
        self.expect(Tok::RParen)?;
        let attr_end = self.expect(Tok::RBracket)?.span;
        let layout_span = attr_span.join(size_span).join(align_span).join(attr_end);

        self.expect(Tok::LBrace)?;
        let mut fields = Vec::new();
        while !self.at(&Tok::RBrace) {
            if self.at(&Tok::Eof) {
                return Err(self.error_expected("`}`"));
            }
            self.expect(Tok::Hash)?;
            self.expect(Tok::LBracket)?;
            let (offset_attr, offset_attr_span) = self.ident()?;
            if offset_attr != "offset" {
                return Err(Diagnostic {
                    name: "record.missing_offset".into(),
                    title: "record fields need an explicit offset".into(),
                    span: offset_attr_span,
                    label: "expected `#[offset(<literal>)]`".into(),
                    notes: vec![],
                });
            }
            self.expect(Tok::LParen)?;
            let (offset, offset_span) = self.signed_int_literal()?;
            self.expect(Tok::RParen)?;
            self.expect(Tok::RBracket)?;
            let (ty, _) = self.record_field_ty()?;
            let (field, field_span) = self.ident()?;
            self.expect(Tok::Semi)?;
            fields.push(RecordField {
                name: field,
                ty,
                offset,
                span: field_span,
                offset_span,
            });
        }
        let end = self.expect(Tok::RBrace)?.span;
        Ok(RecordDecl {
            is_pub: false,
            name,
            name_span,
            layout: StorageLayout { size, align },
            layout_span,
            fields,
            span: start.join(end),
        })
    }

    fn attach_member_contract(&mut self, item_line: usize, f: &mut Fn, what: &str) -> PResult<()> {
        if let Some(block) = self.take_block_ending_before(item_line) {
            for clause in &block.clauses {
                validate_clause_label(clause)?;
                match clause.kind {
                    ClauseKind::Pre => f.pres.push(clause.clone()),
                    ClauseKind::Post => f.posts.push(clause.clone()),
                    other => {
                        return Err(bad_clause(
                            other,
                            clause,
                            "a class-member contract block",
                            "only `pre` and `post` may precede an init or method",
                        ));
                    }
                }
            }
        }
        let _ = what;
        Ok(())
    }

    /// `init name(params) { ... }` — a named constructor (Unit-"returning").
    /// `use m;` / `use m::{a, b};` (ADR 0013).
    fn parse_use(&mut self) -> PResult<crate::ast::UseDecl> {
        let start = self.peek_span();
        self.pos += 1; // `use`
        let (module, _) = self.ident()?;
        let names = if self.at(&Tok::ColonColon) {
            self.pos += 1;
            self.expect(Tok::LBrace)?;
            let mut names = Vec::new();
            loop {
                let (n, _) = self.ident()?;
                names.push(n);
                if self.at(&Tok::Comma) {
                    self.pos += 1;
                    continue;
                }
                break;
            }
            self.expect(Tok::RBrace)?;
            Some(names)
        } else {
            None
        };
        let end = self.expect(Tok::Semi)?.span;
        Ok(crate::ast::UseDecl {
            module,
            names,
            span: start.join(end),
        })
    }

    /// `operator + = add;` (ADR 0012).
    /// `const u64 NAME = 123;` — a named compile-time value
    /// (ADR 0016). The value is an integer literal (optionally
    /// negated); the const pass checks the range and substitutes uses.
    fn parse_const(&mut self) -> PResult<crate::ast::ConstDecl> {
        let kw = self.bump().span; // `const`
        let (ty, _) = self.int_ty()?;
        let (name, name_span) = self.ident()?;
        if is_reserved_name(&name) {
            return Err(reserved_name_error(&name, name_span, "constant"));
        }
        self.expect(Tok::Assign)?;
        let neg = if self.at(&Tok::Minus) {
            self.bump();
            true
        } else {
            false
        };
        let Tok::Int(v) = self.peek().clone() else {
            return Err(self.error_expected("an integer literal"));
        };
        self.bump();
        let end = self.expect(Tok::Semi)?.span;
        Ok(crate::ast::ConstDecl {
            is_pub: false,
            name,
            name_span,
            ty,
            value: if neg { -v } else { v },
            span: kw.join(end),
        })
    }

    fn parse_operator(&mut self) -> PResult<crate::ast::OpBind> {
        let start = self.peek_span();
        self.pos += 1; // `operator`
        let op = match self.peek().clone() {
            Tok::Plus => crate::ast::OpSym::Add,
            Tok::Minus => crate::ast::OpSym::Sub,
            Tok::Star => crate::ast::OpSym::Mul,
            Tok::Slash => crate::ast::OpSym::Div,
            Tok::Percent => crate::ast::OpSym::Rem,
            Tok::Ident(n) if n == "cmp" => crate::ast::OpSym::Cmp,
            _ => return Err(self.error_expected("an operator symbol (`+ - * / %` or `cmp`)")),
        };
        self.pos += 1;
        self.expect(Tok::Assign)?;
        let (fn_name, _) = self.ident()?;
        let end = self.expect(Tok::Semi)?.span;
        Ok(crate::ast::OpBind {
            op,
            fn_name,
            span: start.join(end),
        })
    }

    fn parse_init(&mut self) -> PResult<Fn> {
        let start = self.expect(Tok::KwInit)?.span;
        let (name, name_span) = self.ident()?;
        self.expect(Tok::LParen)?;
        let params = self.param_list()?;
        self.expect(Tok::RParen)?;
        let body = self.block()?;
        let end = self.tokens[self.pos.saturating_sub(1)].span;
        Ok(Fn {
            is_pub: false,
            extern_info: None,
            name,
            name_span,
            type_params: Vec::new(),
            type_bounds: Vec::new(),
            requires: Vec::new(),
            proof_reuse: ProofReuse::None,
            params,
            ret: Ty::Unit,
            pres: Vec::new(),
            posts: Vec::new(),
            variant: None,
            body,
            span: start.join(end),
        })
    }

    /// `fn name(&mut self, params) -> ty { ... }`
    fn parse_method(&mut self) -> PResult<Method> {
        let start = self.expect(Tok::KwFn)?.span;
        let (name, name_span) = self.ident()?;
        self.expect(Tok::LParen)?;
        self.expect(Tok::Amp)?;
        let self_kind = if matches!(self.peek(), Tok::Ident(m) if m == "mut") {
            self.bump();
            SelfKind::Mut
        } else {
            SelfKind::Shared
        };
        match self.bump().tok {
            Tok::Ident(w) if w == "self" => {}
            _ => return Err(self.error_expected("`self`")),
        }
        let params = if self.at(&Tok::Comma) {
            self.bump();
            self.param_list()?
        } else {
            Vec::new()
        };
        self.expect(Tok::RParen)?;
        let ret = if self.at(&Tok::Arrow) {
            self.bump();
            self.ret_ty()?
        } else {
            Ty::Unit
        };
        let body = self.block()?;
        let end = self.tokens[self.pos.saturating_sub(1)].span;
        Ok(Method {
            self_kind,
            f: Fn {
                is_pub: false,
                extern_info: None,
                name,
                name_span,
                type_params: Vec::new(),
                type_bounds: Vec::new(),
                requires: Vec::new(),
                proof_reuse: ProofReuse::None,
                params,
                ret,
                pres: Vec::new(),
                posts: Vec::new(),
                variant: None,
                body,
                span: start.join(end),
            },
        })
    }

    fn param_list(&mut self) -> PResult<Vec<Param>> {
        let mut params = Vec::new();
        if matches!(self.peek(), Tok::RParen) {
            return Ok(params);
        }
        loop {
            let (ty, tspan) = self.param_ty()?;
            let (pname, pspan) = self.ident()?;
            if is_reserved_name(&pname) {
                return Err(reserved_name_error(&pname, pspan, "parameter"));
            }
            params.push(Param {
                name: pname,
                ty,
                span: tspan.join(pspan),
                consumes: false,
            });
            if self.at(&Tok::Comma) {
                self.bump();
            } else {
                break;
            }
        }
        Ok(params)
    }

    /// `extern "C" #[audit(id := "...", reason := "...")] fn f(params);`
    ///
    /// The audit metadata is mandatory. A trusted contract with no
    /// recorded reason is an unsourced axiom, and the manifest exists so a
    /// reader can find every one of them (ADR 0027).
    fn parse_extern(&mut self) -> PResult<Fn> {
        let decl_line = self.peek_line();
        let start = self.expect(Tok::KwExtern)?.span;
        let abi = match self.peek().clone() {
            Tok::Str(bytes) => {
                self.bump();
                String::from_utf8(bytes).map_err(|_| Diagnostic {
                    name: "extern.abi".into(),
                    title: "ABI string is not UTF-8".into(),
                    span: start,
                    label: "expected `\"C\"`".into(),
                    notes: vec![],
                })?
            }
            _ => return Err(self.error_expected("an ABI string, e.g. `\"C\"`")),
        };
        if abi != "C" {
            return Err(Diagnostic {
                name: "extern.abi".into(),
                title: format!("unsupported ABI `{abi}`"),
                span: start,
                label: "only `\"C\"` for now".into(),
                notes: vec![],
            });
        }
        // `#[audit(id := "...", reason := "...")]`
        self.expect(Tok::Hash)?;
        self.expect(Tok::LBracket)?;
        let (attr, attr_span) = self.ident()?;
        if attr != "audit" {
            return Err(Diagnostic {
                name: "extern.missing_audit".into(),
                title: format!("expected `audit`, found `{attr}`"),
                span: attr_span,
                label: "an extern declaration needs audit metadata".into(),
                notes: vec![],
            });
        }
        self.expect(Tok::LParen)?;
        let mut audit_id = None;
        let mut reason = None;
        loop {
            let (key, key_span) = self.ident()?;
            self.expect(Tok::Colon)?;
            self.expect(Tok::Assign)?;
            let value = match self.peek().clone() {
                Tok::Str(bytes) => {
                    self.bump();
                    String::from_utf8_lossy(&bytes).into_owned()
                }
                _ => return Err(self.error_expected("a string")),
            };
            match key.as_str() {
                "id" => audit_id = Some(value),
                "reason" => reason = Some(value),
                _ => {
                    return Err(Diagnostic {
                        name: "extern.missing_audit".into(),
                        title: format!("unknown audit key `{key}`"),
                        span: key_span,
                        label: "expected `id` or `reason`".into(),
                        notes: vec![],
                    });
                }
            }
            if self.at(&Tok::Comma) {
                self.bump();
            } else {
                break;
            }
        }
        self.expect(Tok::RParen)?;
        self.expect(Tok::RBracket)?;
        let (Some(audit_id), Some(reason)) = (audit_id, reason) else {
            return Err(Diagnostic {
                name: "extern.missing_audit".into(),
                title: "`audit` needs both `id` and `reason`".into(),
                span: attr_span,
                label: "an unsourced trusted contract is an unsourced axiom".into(),
                notes: vec![(
                    "note".into(),
                    "the id is what invalidates artifacts when the contract changes; \
                     the reason is what a reader of the manifest gets"
                        .into(),
                )],
            });
        };
        let mut f = self.parse_fn_inner(Some(decl_line))?;
        // Rejected here rather than in the checker: monomorphization drops
        // an uninstantiated template before the checker sees it, and
        // substitutes the parameters away on an instantiated one — so by
        // then there is no generic extern left to reject.
        if !f.type_params.is_empty() {
            return Err(Diagnostic {
                name: "extern.generic".into(),
                title: format!("`{}` may not be generic", f.name),
                span: f.name_span,
                label: "an extern has one ABI, not a family of them".into(),
                notes: vec![],
            });
        }
        f.extern_info = Some(ExternInfo {
            abi,
            audit_id,
            reason,
            span: start,
        });
        Ok(f)
    }

    fn parse_fn(&mut self) -> PResult<Fn> {
        self.parse_fn_inner(None)
    }

    /// `decl_line` is `Some(line)` for a declaration whose contract block
    /// sits above something other than `fn` — an `extern` header — and
    /// which therefore has no body (ADR 0027).
    fn parse_fn_inner(&mut self, decl_line: Option<usize>) -> PResult<Fn> {
        let fn_line = decl_line.unwrap_or_else(|| self.peek_line());
        let is_extern = decl_line.is_some();
        let start = self.expect(Tok::KwFn)?.span;
        let (name, name_span) = self.ident()?;
        if is_reserved_name(&name) {
            return Err(reserved_name_error(&name, name_span, "function"));
        }
        let (tp, type_bounds) = self.type_param_list()?;
        self.tparams = tp;
        let type_params = self.tparams.clone();
        self.expect(Tok::LParen)?;
        let mut params = Vec::new();
        if !self.at(&Tok::RParen) {
            loop {
                let consumes_span = if self.at(&Tok::Hash) {
                    let start = self.bump().span;
                    self.expect(Tok::LBracket)?;
                    let (attr, attr_span) = self.ident()?;
                    if attr != "consumes" {
                        return Err(Diagnostic {
                            name: "resource.unknown_param_attribute".into(),
                            title: format!("unknown parameter attribute `{attr}`"),
                            span: attr_span,
                            label: "expected `consumes`".into(),
                            notes: vec![],
                        });
                    }
                    let end = self.expect(Tok::RBracket)?.span;
                    Some(start.join(end))
                } else {
                    None
                };
                if consumes_span.is_some() && !is_extern {
                    return Err(Diagnostic {
                        name: "resource.consumes_verified".into(),
                        title: "a verified function may not declare a consuming parameter".into(),
                        span: consumes_span.unwrap(),
                        label: "its body must hand mandatory authority to an audited sink".into(),
                        notes: vec![(
                            "note".into(),
                            "`#[consumes]` is an audited promise on an extern parameter; an \
                             ordinary Sable parameter inherits the resource-type obligation"
                                .into(),
                        )],
                    });
                }
                let (ty, tspan) = self.param_ty()?;
                let (pname, pspan) = self.ident()?;
                if is_reserved_name(&pname) {
                    return Err(reserved_name_error(&pname, pspan, "parameter"));
                }
                params.push(Param {
                    name: pname,
                    ty,
                    span: consumes_span.unwrap_or(tspan).join(pspan),
                    consumes: consumes_span.is_some(),
                });
                if self.at(&Tok::Comma) {
                    self.bump();
                } else {
                    break;
                }
            }
        }
        self.expect(Tok::RParen)?;
        let ret = if self.at(&Tok::Arrow) {
            self.bump();
            self.ret_ty()?
        } else {
            Ty::Unit
        };

        let mut f = Fn {
            is_pub: false,
            extern_info: None,
            name,
            name_span,
            type_params,
            type_bounds,
            requires: Vec::new(),
            proof_reuse: ProofReuse::None,
            params,
            ret,
            pres: Vec::new(),
            posts: Vec::new(),
            variant: None,
            body: Vec::new(),
            span: start,
        };

        // Contract block above `fn`.
        if let Some(block) = self.take_block_ending_before(fn_line) {
            for clause in &block.clauses {
                validate_clause_label(clause)?;
                match clause.kind {
                    ClauseKind::Pre => f.pres.push(clause.clone()),
                    ClauseKind::Post => f.posts.push(clause.clone()),
                    ClauseKind::Variant => set_fn_variant(&mut f, clause)?,
                    ClauseKind::Requires => {
                        if f.type_params.is_empty() {
                            return Err(Diagnostic {
                                name: "concepts.requires_non_generic".into(),
                                title: "`requires` on a non-generic function".into(),
                                span: clause.span,
                                label: "concept preconditions constrain type \
                                        parameters (ADR 0009)"
                                    .into(),
                                notes: vec![],
                            });
                        }
                        f.requires.push(clause.clone());
                    }
                    other => {
                        return Err(bad_clause(
                            other,
                            clause,
                            "a function contract block",
                            "only `pre`, `post`, `variant`, and `requires` may precede a function",
                        ));
                    }
                }
            }
        }
        // An extern has no body: its contract is the whole of what is
        // known about it, and there is nothing to check it against.
        if is_extern {
            if f.variant.is_some() {
                return Err(Diagnostic {
                    name: "extern.variant".into(),
                    title: "an extern declaration has no `variant`".into(),
                    span: f.span,
                    label: "there is no recursion here to measure".into(),
                    notes: vec![],
                });
            }
            let end = self.expect(Tok::Semi)?.span;
            self.tparams.clear();
            f.span = start.join(end);
            return Ok(f);
        }
        // Post-signature block (design §8: `fn gcd(...) -> u64` / `/// variant b` / `{`).
        let brace_line = self.peek_line();
        if !self.at(&Tok::LBrace) {
            return Err(self.error_expected("`{`"));
        }
        if let Some(block) = self.take_block_ending_before(brace_line) {
            for clause in &block.clauses {
                validate_clause_label(clause)?;
                match clause.kind {
                    ClauseKind::Variant => set_fn_variant(&mut f, clause)?,
                    other => {
                        return Err(bad_clause(
                            other,
                            clause,
                            "the post-signature position",
                            "only `variant` may sit between a signature and its body",
                        ));
                    }
                }
            }
        }

        f.body = self.block()?;
        self.tparams.clear();
        let end = self.tokens[self.pos.saturating_sub(1)].span;
        f.span = start.join(end);
        Ok(f)
    }

    /// `trait Name { /// spec ... /// post ... fn m(Self x) -> T; ... }`
    /// — `Self` is in scope as a type parameter (ADR 0007).
    fn parse_trait(&mut self) -> PResult<TraitDecl> {
        let start = self.bump().span; // `trait`
        let (name, name_span) = self.ident()?;
        if is_reserved_name(&name) {
            return Err(reserved_name_error(&name, name_span, "trait"));
        }
        self.expect(Tok::LBrace)?;
        self.tparams = vec!["Self".to_string()];
        let mut specs = Vec::new();
        let mut methods = Vec::new();
        while !self.at(&Tok::RBrace) {
            if self.at(&Tok::Eof) {
                return Err(self.error_expected("`}`"));
            }
            let item_line = self.peek_line();
            let fstart = self.expect(Tok::KwFn)?.span;
            let (mname, mspan) = self.ident()?;
            if is_reserved_name(&mname) {
                return Err(reserved_name_error(&mname, mspan, "trait method"));
            }
            self.expect(Tok::LParen)?;
            let params = self.param_list()?;
            self.expect(Tok::RParen)?;
            let ret = if self.at(&Tok::Arrow) {
                self.bump();
                self.ret_ty()?
            } else {
                Ty::Unit
            };
            let end = self.expect(Tok::Semi)?.span;
            let mut f = Fn {
                is_pub: false,
                extern_info: None,
                name: mname,
                name_span: mspan,
                type_params: Vec::new(),
                type_bounds: Vec::new(),
                requires: Vec::new(),
                proof_reuse: ProofReuse::None,
                params,
                ret,
                pres: Vec::new(),
                posts: Vec::new(),
                variant: None,
                body: Vec::new(),
                span: fstart.join(end),
            };
            if let Some(block) = self.take_block_ending_before(item_line) {
                for clause in &block.clauses {
                    validate_clause_label(clause)?;
                    match clause.kind {
                        ClauseKind::Pre => f.pres.push(clause.clone()),
                        ClauseKind::Post => f.posts.push(clause.clone()),
                        ClauseKind::Spec => specs.push(parse_trait_spec(clause)?),
                        other => {
                            return Err(bad_clause(
                                other,
                                clause,
                                "a trait method block",
                                "only `spec`, `pre`, and `post` may precede a trait method",
                            ));
                        }
                    }
                }
            }
            methods.push(f);
        }
        let end = self.expect(Tok::RBrace)?.span;
        self.tparams.clear();
        Ok(TraitDecl {
            is_pub: false,
            name,
            name_span,
            specs,
            methods,
            span: start.join(end),
        })
    }

    /// `impl Trait for i32 { /// def spec... fn m(...) { ... } }` —
    /// bodies plus spec-function ghost defs; contracts come from the
    /// trait (ADR 0007).
    fn parse_impl(&mut self) -> PResult<ImplDecl> {
        let start = self.bump().span; // `impl`
        let (trait_name, trait_span) = self.ident()?;
        self.expect(Tok::KwFor)?;
        let (for_ty, for_span) = self.int_ty()?;
        self.expect(Tok::LBrace)?;
        let body_first_line = self.peek_line();
        let mut ghosts = Vec::new();
        let mut fns = Vec::new();
        while !self.at(&Tok::RBrace) {
            if self.at(&Tok::Eof) {
                return Err(self.error_expected("`}`"));
            }
            let item_line = self.peek_line();
            let fstart = self.expect(Tok::KwFn)?.span;
            let (mname, mspan) = self.ident()?;
            self.expect(Tok::LParen)?;
            let params = self.param_list()?;
            self.expect(Tok::RParen)?;
            let ret = if self.at(&Tok::Arrow) {
                self.bump();
                self.ret_ty()?
            } else {
                Ty::Unit
            };
            if let Some(block) = self.take_block_ending_before(item_line) {
                for clause in &block.clauses {
                    validate_clause_label(clause)?;
                    match clause.kind {
                        ClauseKind::GhostDef => ghosts.push(GhostItem {
                            keyword: "def",
                            unfold: clause.unfold,
                            text: clause.text.clone(),
                            span: clause.span,
                        }),
                        other => {
                            return Err(bad_clause(
                                other,
                                clause,
                                "an impl body",
                                "impl bodies carry no contracts — the trait\'s contract \
                                 applies (ADR 0007); only `def` may appear here",
                            ));
                        }
                    }
                }
            }
            let body = self.block()?;
            let end = self.tokens[self.pos.saturating_sub(1)].span;
            fns.push(Fn {
                is_pub: false,
                extern_info: None,
                name: mname,
                name_span: mspan,
                type_params: Vec::new(),
                type_bounds: Vec::new(),
                requires: Vec::new(),
                proof_reuse: ProofReuse::None,
                params,
                ret,
                pres: Vec::new(),
                posts: Vec::new(),
                variant: None,
                body,
                span: fstart.join(end),
            });
        }
        let end = self.expect(Tok::RBrace)?.span;
        let body_last_line = self.lines.line_col(end.start).0;
        // Free-floating blocks inside the impl body are spec functions.
        for (bi, block) in self.blocks.iter().enumerate() {
            if self.consumed[bi]
                || block.first_line < body_first_line
                || block.last_line > body_last_line
            {
                continue;
            }
            self.consumed[bi] = true;
            for clause in &block.clauses {
                validate_clause_label(clause)?;
                if clause.kind == ClauseKind::GhostDef {
                    ghosts.push(GhostItem {
                        keyword: "def",
                        unfold: clause.unfold,
                        text: clause.text.clone(),
                        span: clause.span,
                    });
                } else {
                    return Err(bad_clause(
                        clause.kind,
                        clause,
                        "an impl body",
                        "free blocks inside an impl hold only `def` (spec functions)",
                    ));
                }
            }
        }
        Ok(ImplDecl {
            trait_name,
            trait_span,
            for_ty,
            for_span,
            ghosts,
            fns,
            span: start.join(end),
        })
    }

    fn block(&mut self) -> PResult<Vec<Stmt>> {
        self.expect(Tok::LBrace)?;
        let mut stmts = Vec::new();
        while !self.at(&Tok::RBrace) {
            if self.at(&Tok::Eof) {
                return Err(self.error_expected("`}`"));
            }
            // A proof block ending just above a non-loop statement holds
            // inline `assert` clauses (loops consume their own preceding
            // block for `invariant`/`variant`/`assert`).
            if !self.at(&Tok::KwFor) && !self.at(&Tok::KwWhile) {
                self.take_asserts(&mut stmts)?;
            }
            if self.at(&Tok::RBrace) {
                break;
            }
            if self.at(&Tok::KwFor) {
                stmts.extend(self.for_stmt()?);
            } else if self.at(&Tok::KwWhile) {
                stmts.extend(self.while_stmt()?);
            } else {
                let stmt = self.stmt()?;
                stmts.append(&mut self.pending);
                stmts.push(stmt);
            }
        }
        // Trailing asserts just before the closing brace.
        self.take_asserts(&mut stmts)?;
        self.expect(Tok::RBrace)?;
        Ok(stmts)
    }

    /// Consume a proof block ending immediately above the current token
    /// as inline `assert` statements.
    fn take_asserts(&mut self, stmts: &mut Vec<Stmt>) -> PResult<()> {
        let line = self.peek_line();
        if let Some(block) = self.take_block_ending_before(line) {
            for clause in &block.clauses {
                validate_clause_label(clause)?;
                match clause.kind {
                    ClauseKind::Assert => stmts.push(Stmt::Assert(clause.clone())),
                    other => {
                        return Err(bad_clause(
                            other,
                            clause,
                            "a statement position",
                            "only `assert` clauses may precede a statement",
                        ));
                    }
                }
            }
        }
        Ok(())
    }

    /// `for (T i : range(hi))` / `for (T i : range(lo, hi))` — pure sugar,
    /// desugared here to a declaration plus a `while` whose bounds
    /// invariant, variant, and increment are synthesized from the bounds'
    /// source text. Extra user `invariant`s above the `for` are kept; a
    /// user `variant` is rejected (the sugar provides it).
    fn for_stmt(&mut self) -> PResult<Vec<Stmt>> {
        let for_line = self.peek_line();
        let kw_span = self.expect(Tok::KwFor)?.span;

        let mut user_invariants = Vec::new();
        if let Some(block) = self.take_block_ending_before(for_line) {
            for clause in &block.clauses {
                validate_clause_label(clause)?;
                match clause.kind {
                    ClauseKind::Invariant => user_invariants.push(clause.clone()),
                    ClauseKind::Variant => {
                        return Err(Diagnostic {
                            name: "proof.for_variant".into(),
                            title: "`for` loops provide their own `variant`".into(),
                            span: clause.line_span,
                            label: "remove this clause (the range bound is the measure)".into(),
                            notes: vec![],
                        });
                    }
                    other => {
                        return Err(bad_clause(
                            other,
                            clause,
                            "a loop annotation block",
                            "only `invariant` may precede a `for` loop",
                        ));
                    }
                }
            }
        }

        self.expect(Tok::LParen)?;
        let (value_ty, _) = self.value_ty()?;
        let loop_ty = match value_ty {
            ValueTy::Int(integer) => Ty::Int(integer),
            ValueTy::Param(parameter) => Ty::Param(parameter),
            ValueTy::Bool | ValueTy::Record(_) => {
                unreachable!("value_ty currently admits only integers and parameters")
            }
        };
        let (index, index_span) = self.ident()?;
        if is_reserved_name(&index) {
            return Err(reserved_name_error(&index, index_span, "loop index"));
        }
        self.expect(Tok::Colon)?;
        let (range_word, range_span) = self.ident()?;
        if range_word != "range" {
            return Err(Diagnostic {
                name: "parse.expected_range".into(),
                title: format!("expected `range`, found `{range_word}`"),
                span: range_span,
                label: "`for` iterates over `range(hi)` or `range(lo, hi)`".into(),
                notes: vec![],
            });
        }
        self.expect(Tok::LParen)?;
        let first_bound = self.expr()?;
        let (lo_expr, hi_expr) = if self.at(&Tok::Comma) {
            self.bump();
            let hi = self.expr()?;
            (Some(first_bound), hi)
        } else {
            (None, first_bound)
        };
        self.expect(Tok::RParen)?;
        self.expect(Tok::RParen)?;
        let body = self.block()?;

        // The synthesized invariant refers to the bounds by their source
        // text, so neither the index nor the bounds' variables may be
        // assigned by the body.
        let mut assigned = std::collections::HashSet::new();
        crate::vcgen::collect_assigned(&body, &mut assigned, crate::vcgen::ANY_RECV_MUTATES);
        if assigned.contains(&index) {
            return Err(Diagnostic {
                name: "parse.for_assigns_index".into(),
                title: format!("`for` body assigns the loop index `{index}`"),
                span: index_span,
                label: "the index is advanced by the loop itself".into(),
                notes: vec![],
            });
        }
        let mut bound_vars = std::collections::HashSet::new();
        expr_vars(&hi_expr, &mut bound_vars);
        if let Some(lo) = &lo_expr {
            expr_vars(lo, &mut bound_vars);
        }
        if let Some(clash) = bound_vars.iter().find(|v| assigned.contains(v.as_str())) {
            return Err(Diagnostic {
                name: "parse.for_mutates_bound".into(),
                title: format!("`for` body assigns `{clash}`, which the range bound mentions"),
                span: kw_span,
                label: "range bounds must be loop-invariant".into(),
                notes: vec![],
            });
        }

        let lo_src = lo_expr
            .as_ref()
            .map(|e| self.text[e.span.start..e.span.end].to_string())
            .unwrap_or_else(|| "0".to_string());
        let hi_src = self.text[hi_expr.span.start..hi_expr.span.end].to_string();
        let hi_span = hi_expr.span;

        let synth_clause = |text: String, kind: ClauseKind| Clause {
            kind,
            label: None,
            unfold: false,
            text,
            span: hi_span,
            line_span: kw_span.join(hi_span),
        };
        let mut invariants = vec![synth_clause(
            format!("({lo_src}) ≤ {index} ∧ {index} ≤ ({hi_src})"),
            ClauseKind::Invariant,
        )];
        invariants.extend(user_invariants);
        let variant = synth_clause(format!("({hi_src}) - {index}"), ClauseKind::Variant);

        let var = |name: &str| Expr {
            kind: ExprKind::Var(name.to_string()),
            span: index_span,
            ty: None,
        };
        let init = lo_expr.unwrap_or(Expr {
            kind: ExprKind::IntLit(0),
            span: kw_span,
            ty: None,
        });
        let cond = Expr {
            kind: ExprKind::Binary {
                op: BinOp::Lt,
                op_span: kw_span,
                lhs: Box::new(var(&index)),
                rhs: Box::new(hi_expr),
            },
            span: kw_span.join(hi_span),
            ty: None,
        };
        let increment = Stmt::Assign {
            name: index.clone(),
            name_span: index_span,
            value: Expr {
                kind: ExprKind::Binary {
                    op: BinOp::Add,
                    op_span: kw_span,
                    lhs: Box::new(var(&index)),
                    rhs: Box::new(Expr {
                        kind: ExprKind::IntLit(1),
                        span: kw_span,
                        ty: None,
                    }),
                },
                span: kw_span,
                ty: None,
            },
        };
        let mut while_body = body;
        while_body.push(increment);

        Ok(vec![
            Stmt::Decl {
                ty: loop_ty,
                name: index,
                name_span: index_span,
                init: Some(init),
                mutable: true,
            },
            Stmt::While {
                cond,
                invariants,
                variant: Some(variant),
                kw_span,
                body: while_body,
            },
        ])
    }

    /// `expose &a as (p, resource m) { ... }` / `expose &mut a as ...`,
    /// after the `unsafe` keyword has been consumed.
    fn expose_stmt(&mut self, kw_span: Span) -> PResult<Stmt> {
        self.expect(Tok::KwExpose)?;
        self.expect(Tok::Amp)?;
        let mutable = if matches!(self.peek(), Tok::Ident(m) if m == "mut") {
            self.bump();
            true
        } else {
            false
        };
        let (array, array_span) = self.ident()?;
        match self.peek() {
            Tok::Ident(kw) if kw == "as" => {
                self.bump();
            }
            _ => return Err(self.error_expected("`as`")),
        }
        self.expect(Tok::LParen)?;
        let (ptr, ptr_span) = self.ident()?;
        if is_reserved_name(&ptr) {
            return Err(reserved_name_error(&ptr, ptr_span, "variable"));
        }
        self.expect(Tok::Comma)?;
        self.expect(Tok::KwResource)?;
        let (res, res_span) = self.ident()?;
        if is_reserved_name(&res) {
            return Err(reserved_name_error(&res, res_span, "variable"));
        }
        self.expect(Tok::RParen)?;
        let body = self.block()?;
        Ok(Stmt::Expose {
            kw_span,
            array,
            array_span,
            mutable,
            ptr,
            ptr_span,
            res,
            res_span,
            body,
        })
    }

    /// `static_alloc(N) as (p, resource m);`, after `unsafe`.
    fn static_alloc_stmt(&mut self, kw_span: Span) -> PResult<Stmt> {
        let (op, _) = self.ident()?;
        debug_assert_eq!(op, "static_alloc");
        self.expect(Tok::LParen)?;
        let size = self.expr()?;
        self.expect(Tok::RParen)?;
        match self.peek() {
            Tok::Ident(kw) if kw == "as" => {
                self.bump();
            }
            _ => return Err(self.error_expected("`as`")),
        }
        self.expect(Tok::LParen)?;
        let (ptr, ptr_span) = self.ident()?;
        if is_reserved_name(&ptr) {
            return Err(reserved_name_error(&ptr, ptr_span, "variable"));
        }
        self.expect(Tok::Comma)?;
        self.expect(Tok::KwResource)?;
        let (res, res_span) = self.ident()?;
        if is_reserved_name(&res) {
            return Err(reserved_name_error(&res, res_span, "variable"));
        }
        self.expect(Tok::RParen)?;
        self.expect(Tok::Semi)?;
        Ok(Stmt::StaticAlloc {
            kw_span,
            size,
            ptr,
            ptr_span,
            res,
            res_span,
        })
    }

    /// `system_alloc(N) as (p, resource m, resource release);`, after
    /// `unsafe`. Unlike the static root, this returns mandatory release
    /// authority (ADR 0036).
    fn system_alloc_stmt(&mut self, kw_span: Span) -> PResult<Stmt> {
        let (op, _) = self.ident()?;
        debug_assert_eq!(op, "system_alloc");
        self.expect(Tok::LParen)?;
        let size = self.expr()?;
        self.expect(Tok::RParen)?;
        match self.peek() {
            Tok::Ident(kw) if kw == "as" => {
                self.bump();
            }
            _ => return Err(self.error_expected("`as`")),
        }
        self.expect(Tok::LParen)?;
        let (ptr, ptr_span) = self.ident()?;
        self.expect(Tok::Comma)?;
        self.expect(Tok::KwResource)?;
        let (res, res_span) = self.ident()?;
        self.expect(Tok::Comma)?;
        self.expect(Tok::KwResource)?;
        let (release, release_span) = self.ident()?;
        for (name, span) in [(&ptr, ptr_span), (&res, res_span), (&release, release_span)] {
            if is_reserved_name(name) {
                return Err(reserved_name_error(name, span, "variable"));
            }
        }
        self.expect(Tok::RParen)?;
        self.expect(Tok::Semi)?;
        Ok(Stmt::SystemAlloc {
            kw_span,
            size,
            ptr,
            ptr_span,
            res,
            res_span,
            release,
            release_span,
        })
    }

    /// `system_dealloc(p, mem, release);`, after `unsafe`.
    fn system_dealloc_stmt(&mut self, kw_span: Span) -> PResult<Stmt> {
        let (op, _) = self.ident()?;
        debug_assert_eq!(op, "system_dealloc");
        self.expect(Tok::LParen)?;
        let ptr = self.expr()?;
        self.expect(Tok::Comma)?;
        let res = self.expr()?;
        self.expect(Tok::Comma)?;
        let release = self.expr()?;
        self.expect(Tok::RParen)?;
        self.expect(Tok::Semi)?;
        Ok(Stmt::SystemDealloc {
            kw_span,
            ptr,
            res,
            release,
        })
    }

    fn stmt(&mut self) -> PResult<Stmt> {
        match self.peek().clone() {
            // `mut <decl>` — the declared local is mutable (ADR 0016).
            Tok::Ident(m) if m == "mut" && !self.pending_mut => {
                let mut_span = self.bump().span;
                self.pending_mut = true;
                let s = self.stmt()?;
                if self.pending_mut {
                    self.pending_mut = false;
                    return Err(Diagnostic {
                        name: "mut.not_a_declaration".into(),
                        title: "`mut` must prefix a declaration".into(),
                        span: mut_span,
                        label: "only local declarations take a mutability marker".into(),
                        notes: vec![],
                    });
                }
                Ok(s)
            }
            Tok::KwReturn => {
                let kw = self.bump().span;
                let value = if self.at(&Tok::Semi) {
                    None
                } else {
                    Some(self.expr()?)
                };
                let end = self.expect(Tok::Semi)?.span;
                Ok(Stmt::Return {
                    value,
                    span: kw.join(end),
                })
            }
            Tok::KwIf => self.if_stmt(),
            Tok::KwVar => {
                self.bump();
                // `var mut s = ...;` — the marker sits between `var`
                // and the name (ADR 0016).
                if matches!(self.peek(), Tok::Ident(m) if m == "mut") {
                    self.bump();
                    self.pending_mut = true;
                }
                let (name, name_span) = self.ident()?;
                if is_reserved_name(&name) {
                    return Err(reserved_name_error(&name, name_span, "variable"));
                }
                self.expect(Tok::Assign)?;
                // `var s = "Hi!";` — sugar for a hidden [u8] temp holding
                // the literal's UTF-8 bytes plus `String::from_bytes(&temp)`
                // (ADR 0014). The library class carries the semantics; the
                // parser only names it.
                if let Tok::Str(bs) = self.peek().clone() {
                    let lit_span = self.bump().span;
                    self.expect(Tok::Semi)?;
                    let temp = format!("_str{}", self.str_temps);
                    self.str_temps += 1;
                    let elems = bs
                        .iter()
                        .map(|b| Expr {
                            kind: ExprKind::IntLit(i128::from(*b)),
                            span: lit_span,
                            ty: None,
                        })
                        .collect();
                    self.pending.push(Stmt::Decl {
                        ty: Ty::Array(ValueTy::Int(IntTy::U8), Mutability::Owned),
                        name: temp.clone(),
                        name_span: lit_span,
                        init: Some(Expr {
                            kind: ExprKind::ArrayLit(elems),
                            span: lit_span,
                            ty: None,
                        }),
                        mutable: false,
                    });
                    return Ok(Stmt::VarDecl {
                        name,
                        name_span,
                        mutable: std::mem::take(&mut self.pending_mut),
                        init: Expr {
                            kind: ExprKind::CtorCall {
                                class: "String".into(),
                                class_span: lit_span,
                                type_args: Vec::new(),
                                init: "from_bytes".into(),
                                args: vec![Expr {
                                    kind: ExprKind::Borrow {
                                        field: None,
                                        array: temp,
                                        mutable: false,
                                    },
                                    span: lit_span,
                                    ty: None,
                                }],
                            },
                            span: lit_span,
                            ty: None,
                        },
                        ty: None,
                    });
                }
                let init = self.expr()?;
                self.expect(Tok::Semi)?;
                Ok(Stmt::VarDecl {
                    name,
                    name_span,
                    init,
                    mutable: std::mem::take(&mut self.pending_mut),
                    ty: None,
                })
            }
            Tok::KwUnsafe => {
                let kw_span = self.bump().span;
                // `unsafe expose &a as (p, resource m) { ... }` — the
                // bridge to raw bytes; or a plain `unsafe { ... }` block,
                // which is where raw operations may be called.
                if self.at(&Tok::KwExpose) {
                    return self.expose_stmt(kw_span);
                }
                if matches!(self.peek(), Tok::Ident(op) if op == "static_alloc") {
                    return self.static_alloc_stmt(kw_span);
                }
                if matches!(self.peek(), Tok::Ident(op) if op == "system_alloc") {
                    return self.system_alloc_stmt(kw_span);
                }
                if matches!(self.peek(), Tok::Ident(op) if op == "system_dealloc") {
                    return self.system_dealloc_stmt(kw_span);
                }
                let body = self.block()?;
                Ok(Stmt::Unsafe { kw_span, body })
            }
            Tok::KwResource => {
                // `resource RawSpan tail = split_off(...);` — an owned
                // resource local. The category is spelled out at every
                // binding site: authority is erased at runtime, so a
                // reader must not have to infer it from a callee's
                // signature (ADR 0024).
                let (ty, _) = self.resource_ty()?;
                if let Ty::ResRef(..) = ty {
                    return Err(Diagnostic {
                        name: "resource.borrow_local".into(),
                        title: "a resource borrow cannot be a local".into(),
                        span: self.peek_span(),
                        label: "declare `resource RawSpan` and borrow it at the call".into(),
                        notes: vec![(
                            "note".into(),
                            "borrows are arguments, not values: they live for one call, \
                             which is what keeps borrow state out of the checker's \
                             per-statement bookkeeping"
                                .into(),
                        )],
                    });
                }
                let (name, name_span) = self.ident()?;
                if is_reserved_name(&name) {
                    return Err(reserved_name_error(&name, name_span, "variable"));
                }
                self.expect(Tok::Assign)?;
                let init = self.expr()?;
                self.expect(Tok::Semi)?;
                Ok(Stmt::Decl {
                    ty,
                    name,
                    name_span,
                    init: Some(init),
                    mutable: std::mem::take(&mut self.pending_mut),
                })
            }
            Tok::KwRaw => {
                // `raw<u8> p = raw_offset(q, 1);` — a pointer local. It
                // may also be declared without an initializer, which is
                // the only way to have one before an exposure exists to
                // produce a value; definite initialization is what keeps
                // it from being read early.
                let (ty, _) = self.raw_ty()?;
                let (name, name_span) = self.ident()?;
                if is_reserved_name(&name) {
                    return Err(reserved_name_error(&name, name_span, "variable"));
                }
                let init = if self.at(&Tok::Assign) {
                    self.bump();
                    Some(self.expr()?)
                } else {
                    None
                };
                self.expect(Tok::Semi)?;
                Ok(Stmt::Decl {
                    ty,
                    name,
                    name_span,
                    init,
                    mutable: std::mem::take(&mut self.pending_mut),
                })
            }
            Tok::LBracket => {
                // `[i32] a = [1, 2, 3];` — owned array local (tests only;
                // the checker enforces the context).
                self.bump();
                let (elem, _) = self.value_ty()?;
                self.expect(Tok::RBracket)?;
                let (name, name_span) = self.ident()?;
                if is_reserved_name(&name) {
                    return Err(reserved_name_error(&name, name_span, "variable"));
                }
                self.expect(Tok::Assign)?;
                let init = self.expr()?;
                self.expect(Tok::Semi)?;
                Ok(Stmt::Decl {
                    ty: Ty::Array(elem, Mutability::Owned),
                    name,
                    name_span,
                    init: Some(init),
                    mutable: std::mem::take(&mut self.pending_mut),
                })
            }
            Tok::Ident(first) if first == "option" && self.peek2() == &Tok::Lt => {
                // Integer options and nullable record pointers are both
                // initialized values; neither has an implicit default.
                let (ty, _) = self.option_ty()?;
                let (name, name_span) = self.ident()?;
                if is_reserved_name(&name) {
                    return Err(reserved_name_error(&name, name_span, "variable"));
                }
                self.expect(Tok::Assign)?;
                let init = self.expr()?;
                self.expect(Tok::Semi)?;
                Ok(Stmt::Decl {
                    ty,
                    name,
                    name_span,
                    init: Some(init),
                    mutable: std::mem::take(&mut self.pending_mut),
                })
            }
            Tok::Ident(first) if first == "self" && self.peek2() == &Tok::Dot => {
                // self.f = e;   self.f[i] = e;
                self.bump();
                self.bump();
                let (field, field_span) = self.ident()?;
                if self.at(&Tok::LBracket) {
                    self.bump();
                    let index = self.expr()?;
                    self.expect(Tok::RBracket)?;
                    self.expect(Tok::Assign)?;
                    let value = self.expr()?;
                    self.expect(Tok::Semi)?;
                    return Ok(Stmt::FieldStore {
                        field,
                        field_span,
                        index,
                        value,
                    });
                }
                self.expect(Tok::Assign)?;
                let value = self.expr()?;
                self.expect(Tok::Semi)?;
                Ok(Stmt::FieldAssign {
                    field,
                    field_span,
                    value,
                })
            }
            Tok::Ident(_) if self.peek2() == &Tok::Dot => {
                // Method-call statement: `s.push(7);`
                let e = self.expr()?;
                if !matches!(e.kind, ExprKind::MethodCall { .. }) {
                    return Err(Diagnostic {
                        name: "parse.expr_stmt".into(),
                        title: "only calls can be used as statements".into(),
                        span: e.span,
                        label: "this expression has no effect".into(),
                        notes: vec![],
                    });
                }
                self.expect(Tok::Semi)?;
                Ok(Stmt::ExprStmt(e))
            }
            Tok::Ident(first) => {
                if let Tok::Ident(_) = self.peek2() {
                    let ty = if let Some(ri) = self.record_names.iter().position(|r| r == &first) {
                        self.bump();
                        Ty::Record(ri)
                    } else {
                        self.scalar_ty()?.0
                    };
                    let (name, name_span) = self.ident()?;
                    if is_reserved_name(&name) {
                        return Err(reserved_name_error(&name, name_span, "variable"));
                    }
                    let init = if self.at(&Tok::Assign) {
                        self.bump();
                        Some(self.expr()?)
                    } else {
                        None
                    };
                    self.expect(Tok::Semi)?;
                    Ok(Stmt::Decl {
                        ty,
                        name,
                        name_span,
                        init,
                        mutable: std::mem::take(&mut self.pending_mut),
                    })
                } else if self.peek2() == &Tok::LParen {
                    let e = self.expr()?;
                    self.expect(Tok::Semi)?;
                    Ok(Stmt::ExprStmt(e))
                } else if self.at_generic_args()? {
                    // `clamp<i32>(...);` — a generic call for effect.
                    let e = self.expr()?;
                    self.expect(Tok::Semi)?;
                    Ok(Stmt::ExprStmt(e))
                } else if self.peek2() == &Tok::LBracket {
                    let array_span = self.peek_span();
                    self.bump();
                    self.bump();
                    let index = self.expr()?;
                    self.expect(Tok::RBracket)?;
                    self.expect(Tok::Assign)?;
                    let value = self.expr()?;
                    self.expect(Tok::Semi)?;
                    Ok(Stmt::Store {
                        array: first,
                        array_span,
                        index,
                        value,
                    })
                } else {
                    let name_span = self.peek_span();
                    self.bump();
                    self.expect(Tok::Assign)?;
                    let value = self.expr()?;
                    self.expect(Tok::Semi)?;
                    Ok(Stmt::Assign {
                        name: first,
                        name_span,
                        value,
                    })
                }
            }
            _ => Err(self.error_expected("a statement")),
        }
    }

    fn if_stmt(&mut self) -> PResult<Stmt> {
        self.expect(Tok::KwIf)?;
        self.expect(Tok::LParen)?;
        let cond = self.expr()?;
        self.expect(Tok::RParen)?;
        let then_block = self.block()?;
        let else_block = if self.at(&Tok::KwElse) {
            self.bump();
            if self.at(&Tok::KwIf) {
                Some(vec![self.if_stmt()?])
            } else {
                Some(self.block()?)
            }
        } else {
            None
        };
        Ok(Stmt::If {
            cond,
            then_block,
            else_block,
        })
    }

    fn while_stmt(&mut self) -> PResult<Vec<Stmt>> {
        let while_line = self.peek_line();
        let kw_span = self.expect(Tok::KwWhile)?.span;
        let mut invariants = Vec::new();
        let mut asserts = Vec::new();
        let mut variant = None;
        if let Some(block) = self.take_block_ending_before(while_line) {
            for clause in &block.clauses {
                validate_clause_label(clause)?;
                match clause.kind {
                    ClauseKind::Invariant => invariants.push(clause.clone()),
                    ClauseKind::Assert => asserts.push(Stmt::Assert(clause.clone())),
                    ClauseKind::Variant => {
                        if variant.replace(clause.clone()).is_some() {
                            return Err(Diagnostic {
                                name: "proof.duplicate_variant".into(),
                                title: "a loop has exactly one `variant`".into(),
                                span: clause.line_span,
                                label: "second `variant` clause".into(),
                                notes: vec![],
                            });
                        }
                    }
                    other => {
                        return Err(bad_clause(
                            other,
                            clause,
                            "a loop annotation block",
                            "only `invariant`, `variant`, and `assert` may precede a loop",
                        ));
                    }
                }
            }
        }
        self.expect(Tok::LParen)?;
        let cond = self.expr()?;
        self.expect(Tok::RParen)?;
        let body = self.block()?;
        asserts.push(Stmt::While {
            cond,
            invariants,
            variant,
            kw_span,
            body,
        });
        Ok(asserts)
    }

    // Precedence climbing. Comparisons are non-associative by design.
    fn expr(&mut self) -> PResult<Expr> {
        self.or_expr()
    }

    fn or_expr(&mut self) -> PResult<Expr> {
        let mut lhs = self.and_expr()?;
        while self.at(&Tok::OrOr) {
            let op_span = self.bump().span;
            let rhs = self.and_expr()?;
            lhs = mk_bin(BinOp::Or, op_span, lhs, rhs);
        }
        Ok(lhs)
    }

    fn and_expr(&mut self) -> PResult<Expr> {
        let mut lhs = self.cmp_expr()?;
        while self.at(&Tok::AndAnd) {
            let op_span = self.bump().span;
            let rhs = self.cmp_expr()?;
            lhs = mk_bin(BinOp::And, op_span, lhs, rhs);
        }
        Ok(lhs)
    }

    fn cmp_expr(&mut self) -> PResult<Expr> {
        let lhs = self.add_expr()?;
        let op = match self.peek() {
            Tok::Lt => BinOp::Lt,
            Tok::Le => BinOp::Le,
            Tok::Gt => BinOp::Gt,
            Tok::Ge => BinOp::Ge,
            Tok::EqEq => BinOp::Eq,
            Tok::Ne => BinOp::Ne,
            _ => return Ok(lhs),
        };
        let op_span = self.bump().span;
        let rhs = self.add_expr()?;
        let e = mk_bin(op, op_span, lhs, rhs);
        if matches!(
            self.peek(),
            Tok::Lt | Tok::Le | Tok::Gt | Tok::Ge | Tok::EqEq | Tok::Ne
        ) {
            return Err(Diagnostic {
                name: "parse.chained_comparison".into(),
                title: "comparison operators cannot be chained".into(),
                span: self.peek_span(),
                label: "use `&&` to combine comparisons".into(),
                notes: vec![],
            });
        }
        Ok(e)
    }

    fn add_expr(&mut self) -> PResult<Expr> {
        let mut lhs = self.mul_expr()?;
        loop {
            let op = match self.peek() {
                Tok::Plus => BinOp::Add,
                Tok::Minus => BinOp::Sub,
                _ => break,
            };
            let op_span = self.bump().span;
            let rhs = self.mul_expr()?;
            lhs = mk_bin(op, op_span, lhs, rhs);
        }
        Ok(lhs)
    }

    fn mul_expr(&mut self) -> PResult<Expr> {
        let mut lhs = self.unary_expr()?;
        loop {
            let op = match self.peek() {
                Tok::Star => BinOp::Mul,
                Tok::Slash => BinOp::Div,
                Tok::Percent => BinOp::Rem,
                _ => break,
            };
            let op_span = self.bump().span;
            let rhs = self.unary_expr()?;
            lhs = mk_bin(op, op_span, lhs, rhs);
        }
        Ok(lhs)
    }

    fn unary_expr(&mut self) -> PResult<Expr> {
        match self.peek() {
            Tok::Minus => {
                let span = self.bump().span;
                let operand = self.unary_expr()?;
                let full = span.join(operand.span);
                if let ExprKind::IntLit(n) = operand.kind {
                    return Ok(Expr {
                        kind: ExprKind::IntLit(-n),
                        span: full,
                        ty: None,
                    });
                }
                Ok(Expr {
                    kind: ExprKind::Unary {
                        op: UnOp::Neg,
                        operand: Box::new(operand),
                    },
                    span: full,
                    ty: None,
                })
            }
            Tok::Bang => {
                let span = self.bump().span;
                let operand = self.unary_expr()?;
                let full = span.join(operand.span);
                Ok(Expr {
                    kind: ExprKind::Unary {
                        op: UnOp::Not,
                        operand: Box::new(operand),
                    },
                    span: full,
                    ty: None,
                })
            }
            _ => self.postfix_expr(),
        }
    }

    fn postfix_expr(&mut self) -> PResult<Expr> {
        let mut e = self.primary_expr()?;
        loop {
            match self.peek() {
                Tok::LParen => {
                    let ExprKind::Var(name) = &e.kind else {
                        return Err(Diagnostic {
                            name: "parse.bad_call".into(),
                            title: "only named functions can be called".into(),
                            span: self.peek_span(),
                            label: "call target must be a function name".into(),
                            notes: vec![],
                        });
                    };
                    let callee = name.clone();
                    let callee_span = e.span;
                    self.bump();
                    let mut args = Vec::new();
                    if !self.at(&Tok::RParen) {
                        loop {
                            args.push(self.expr()?);
                            if self.at(&Tok::Comma) {
                                self.bump();
                            } else {
                                break;
                            }
                        }
                    }
                    let close = self.expect(Tok::RParen)?.span;
                    e = Expr {
                        kind: ExprKind::Call {
                            callee,
                            callee_span,
                            type_args: Vec::new(),
                            args,
                        },
                        span: callee_span.join(close),
                        ty: None,
                    };
                }
                Tok::LBracket => {
                    let ExprKind::Var(name) = &e.kind else {
                        return Err(Diagnostic {
                            name: "parse.bad_index".into(),
                            title: "only named arrays can be indexed".into(),
                            span: self.peek_span(),
                            label: "indexing applies to array values".into(),
                            notes: vec![],
                        });
                    };
                    let array = name.clone();
                    let array_span = e.span;
                    self.bump();
                    let index = self.expr()?;
                    let close = self.expect(Tok::RBracket)?.span;
                    e = Expr {
                        kind: ExprKind::Index {
                            array,
                            array_span,
                            index: Box::new(index),
                        },
                        span: array_span.join(close),
                        ty: None,
                    };
                }
                Tok::Dot => {
                    // Option accessors postfix any expression (ADR 0008).
                    if matches!(self.peek2(), Tok::Ident(f) if f == "is_some" || f == "value") {
                        self.bump();
                        let (field, fspan) = self.ident()?;
                        let espan = e.span;
                        e = Expr {
                            kind: if field == "is_some" {
                                ExprKind::IsSome {
                                    operand: Box::new(e),
                                }
                            } else {
                                ExprKind::OptValue {
                                    operand: Box::new(e),
                                }
                            },
                            span: espan.join(fspan),
                            ty: None,
                        };
                        continue;
                    }
                    let ExprKind::Var(name) = &e.kind else {
                        return Err(self.error_expected("nothing (`.` applies to names)"));
                    };
                    let recv = name.clone();
                    let recv_span = e.span;
                    self.bump();
                    let (field, fspan) = self.ident()?;
                    if self.at(&Tok::LParen) {
                        // recv.method(args)
                        self.bump();
                        let mut args = Vec::new();
                        if !self.at(&Tok::RParen) {
                            loop {
                                args.push(self.expr()?);
                                if self.at(&Tok::Comma) {
                                    self.bump();
                                } else {
                                    break;
                                }
                            }
                        }
                        let close = self.expect(Tok::RParen)?.span;
                        e = Expr {
                            kind: ExprKind::MethodCall {
                                recv,
                                recv_span,
                                method: field,
                                method_span: fspan,
                                args,
                            },
                            span: recv_span.join(close),
                            ty: None,
                        };
                        continue;
                    }
                    if field == "len" {
                        // Array length — or a class field named `len`;
                        // the checker disambiguates by receiver type.
                        e = Expr {
                            kind: ExprKind::Len { array: recv },
                            span: recv_span.join(fspan),
                            ty: None,
                        };
                        continue;
                    }
                    // `o.f` — class field read (ADR 0010); may continue
                    // postfix as `o.f.len` or `o.f[i]`.
                    if self.at(&Tok::Dot) && matches!(self.peek2(), Tok::Ident(n) if n == "len") {
                        self.bump();
                        let (_, lspan) = self.ident()?;
                        e = Expr {
                            kind: ExprKind::ClassFieldLen { obj: recv, field },
                            span: recv_span.join(lspan),
                            ty: None,
                        };
                        continue;
                    }
                    if self.at(&Tok::LBracket) {
                        self.bump();
                        let index = self.expr()?;
                        let close = self.expect(Tok::RBracket)?.span;
                        e = Expr {
                            kind: ExprKind::ClassFieldIndex {
                                obj: recv,
                                obj_span: recv_span,
                                field,
                                index: Box::new(index),
                            },
                            span: recv_span.join(close),
                            ty: None,
                        };
                        continue;
                    }
                    e = Expr {
                        kind: ExprKind::ClassField {
                            obj: recv,
                            obj_span: recv_span,
                            field,
                        },
                        span: recv_span.join(fspan),
                        ty: None,
                    };
                }
                _ => break,
            }
        }
        Ok(e)
    }

    fn primary_expr(&mut self) -> PResult<Expr> {
        let span = self.peek_span();
        match self.peek().clone() {
            Tok::Int(n) => {
                self.bump();
                Ok(Expr {
                    kind: ExprKind::IntLit(n),
                    span,
                    ty: None,
                })
            }
            Tok::Str(_) => Err(Diagnostic {
                name: "string.literal_position".into(),
                title: "string literal outside a `var` initializer".into(),
                span,
                label: "a bare literal builds a `String`; bind it first: `var s = \"...\";`".into(),
                notes: vec![],
            }),
            // b"..." is sugar for the array literal of its bytes.
            Tok::Bytes(bs) => {
                self.bump();
                Ok(Expr {
                    kind: ExprKind::ArrayLit(
                        bs.iter()
                            .map(|b| Expr {
                                kind: ExprKind::IntLit(i128::from(*b)),
                                span,
                                ty: None,
                            })
                            .collect(),
                    ),
                    span,
                    ty: None,
                })
            }
            Tok::KwTrue => {
                self.bump();
                Ok(Expr {
                    kind: ExprKind::BoolLit(true),
                    span,
                    ty: None,
                })
            }
            Tok::KwFalse => {
                self.bump();
                Ok(Expr {
                    kind: ExprKind::BoolLit(false),
                    span,
                    ty: None,
                })
            }
            Tok::Ident(record)
                if self.record_names.iter().any(|r| r == &record)
                    && self.peek2() == &Tok::LParen =>
            {
                let record_span = self.bump().span;
                self.expect(Tok::LParen)?;
                let mut args = Vec::new();
                if !self.at(&Tok::RParen) {
                    loop {
                        args.push(self.expr()?);
                        if self.at(&Tok::Comma) {
                            self.bump();
                        } else {
                            break;
                        }
                    }
                }
                let close = self.expect(Tok::RParen)?.span;
                Ok(Expr {
                    kind: ExprKind::RecordLit {
                        record,
                        record_span,
                        args,
                    },
                    span: record_span.join(close),
                    ty: None,
                })
            }
            Tok::Ident(name)
                if matches!(
                    name.as_str(),
                    "raw_into_cell"
                        | "raw_from_cell"
                        | "raw_cell_init"
                        | "raw_cell_read"
                        | "raw_cell_take"
                        | "raw_cell_drop"
                        | "raw_cast"
                        | "raw_pointer_offset"
                ) && self.peek2() == &Tok::Lt =>
            {
                let op_name = name;
                let op_span = self.bump().span;
                self.expect(Tok::Lt)?;
                let (record, record_span) = self.ident()?;
                let Some(ri) = self.record_names.iter().position(|r| r == &record) else {
                    return Err(Diagnostic {
                        name: "record.unknown_type".into(),
                        title: format!("unknown record `{record}`"),
                        span: record_span,
                        label: "typed record operations require a declared `record`".into(),
                        notes: vec![],
                    });
                };
                self.expect(Tok::Gt)?;
                self.expect(Tok::LParen)?;
                let mut args = Vec::new();
                if !self.at(&Tok::RParen) {
                    loop {
                        args.push(self.expr()?);
                        if self.at(&Tok::Comma) {
                            self.bump();
                        } else {
                            break;
                        }
                    }
                }
                let close = self.expect(Tok::RParen)?.span;
                let op = match op_name.as_str() {
                    "raw_into_cell" => RawOp::IntoCellRecord(ri),
                    "raw_from_cell" => RawOp::FromCellRecord(ri),
                    "raw_cell_init" => RawOp::CellInitRecord(ri),
                    "raw_cell_read" => RawOp::CellReadRecord(ri),
                    "raw_cell_take" => RawOp::CellTakeRecord(ri),
                    "raw_cell_drop" => RawOp::CellDropRecord(ri),
                    "raw_cast" => RawOp::CastRecord(ri),
                    "raw_pointer_offset" => RawOp::PointerOffsetRecord(ri),
                    _ => unreachable!(),
                };
                Ok(Expr {
                    kind: ExprKind::RawOp { op, op_span, args },
                    span: op_span.join(close),
                    ty: None,
                })
            }
            Tok::Ident(name) if RawOp::from_name(&name).is_some() => {
                let op = RawOp::from_name(&name).expect("checked");
                self.bump();
                self.expect(Tok::LParen)?;
                let mut args = Vec::new();
                while !self.at(&Tok::RParen) {
                    args.push(self.expr()?);
                    if self.at(&Tok::Comma) {
                        self.bump();
                    } else {
                        break;
                    }
                }
                let close = self.expect(Tok::RParen)?.span;
                Ok(Expr {
                    kind: ExprKind::RawOp {
                        op,
                        op_span: span,
                        args,
                    },
                    span: span.join(close),
                    ty: None,
                })
            }
            Tok::Ident(name) if DeviceOp::from_name(&name).is_some() => {
                let op = DeviceOp::from_name(&name).expect("checked");
                self.bump();
                self.expect(Tok::LParen)?;
                let mut args = Vec::new();
                while !self.at(&Tok::RParen) {
                    args.push(self.expr()?);
                    if self.at(&Tok::Comma) {
                        self.bump();
                    } else {
                        break;
                    }
                }
                let close = self.expect(Tok::RParen)?.span;
                Ok(Expr {
                    kind: ExprKind::DeviceOp {
                        op,
                        op_span: span,
                        args,
                    },
                    span: span.join(close),
                    ty: None,
                })
            }
            Tok::Ident(name) if ResOp::from_name(&name).is_some() => {
                let op = ResOp::from_name(&name).expect("checked");
                self.bump();
                self.expect(Tok::LParen)?;
                let mut args = Vec::new();
                while !self.at(&Tok::RParen) {
                    args.push(self.expr()?);
                    if self.at(&Tok::Comma) {
                        self.bump();
                    } else {
                        break;
                    }
                }
                let close = self.expect(Tok::RParen)?.span;
                Ok(Expr {
                    kind: ExprKind::ResOp {
                        op,
                        op_span: span,
                        args,
                    },
                    span: span.join(close),
                    ty: None,
                })
            }
            Tok::Ident(name) if name == "alloc_array" => {
                self.bump();
                self.expect(Tok::Lt)?;
                let (elem, _) = self.value_ty()?;
                self.expect(Tok::Gt)?;
                self.expect(Tok::LParen)?;
                let len = self.expr()?;
                self.expect(Tok::Comma)?;
                let init = self.expr()?;
                let close = self.expect(Tok::RParen)?.span;
                Ok(Expr {
                    kind: ExprKind::AllocArray {
                        elem,
                        len: Box::new(len),
                        init: Box::new(init),
                    },
                    span: span.join(close),
                    ty: None,
                })
            }
            Tok::Ident(name) if name == "self" && self.peek2() == &Tok::Dot => {
                self.bump();
                self.bump();
                let (field, fspan) = self.ident()?;
                if self.at(&Tok::LBracket) {
                    self.bump();
                    let index = self.expr()?;
                    let close = self.expect(Tok::RBracket)?.span;
                    return Ok(Expr {
                        kind: ExprKind::SelfFieldIndex {
                            field,
                            index: Box::new(index),
                        },
                        span: span.join(close),
                        ty: None,
                    });
                }
                if self.at(&Tok::Dot) {
                    self.bump();
                    let (sub, sspan) = self.ident()?;
                    if sub != "len" {
                        return Err(Diagnostic {
                            name: "parse.unknown_field".into(),
                            title: format!("unknown field `.{sub}`"),
                            span: sspan,
                            label: "`.len` is the only array-field accessor".into(),
                            notes: vec![],
                        });
                    }
                    return Ok(Expr {
                        kind: ExprKind::SelfFieldLen { field },
                        span: span.join(sspan),
                        ty: None,
                    });
                }
                Ok(Expr {
                    kind: ExprKind::SelfField { field },
                    span: span.join(fspan),
                    ty: None,
                })
            }
            Tok::Ident(head) if self.at_generic_args()? => {
                let head_span = self.peek_span();
                self.bump();
                let type_args = self.type_arg_list()?;
                if self.at(&Tok::ColonColon) {
                    self.bump();
                    let (init, _) = self.ident()?;
                    self.expect(Tok::LParen)?;
                    let mut args = Vec::new();
                    if !self.at(&Tok::RParen) {
                        loop {
                            args.push(self.expr()?);
                            if self.at(&Tok::Comma) {
                                self.bump();
                            } else {
                                break;
                            }
                        }
                    }
                    let close = self.expect(Tok::RParen)?.span;
                    return Ok(Expr {
                        kind: ExprKind::CtorCall {
                            class: head,
                            class_span: head_span,
                            type_args,
                            init,
                            args,
                        },
                        span: span.join(close),
                        ty: None,
                    });
                }
                self.expect(Tok::LParen)?;
                let mut args = Vec::new();
                if !self.at(&Tok::RParen) {
                    loop {
                        args.push(self.expr()?);
                        if self.at(&Tok::Comma) {
                            self.bump();
                        } else {
                            break;
                        }
                    }
                }
                let close = self.expect(Tok::RParen)?.span;
                Ok(Expr {
                    kind: ExprKind::Call {
                        callee: head,
                        callee_span: head_span,
                        type_args,
                        args,
                    },
                    span: span.join(close),
                    ty: None,
                })
            }
            Tok::Ident(class) if self.peek2() == &Tok::ColonColon => {
                let class_span = self.peek_span();
                self.bump();
                self.bump();
                let (init, _) = self.ident()?;
                self.expect(Tok::LParen)?;
                let mut args = Vec::new();
                if !self.at(&Tok::RParen) {
                    loop {
                        args.push(self.expr()?);
                        if self.at(&Tok::Comma) {
                            self.bump();
                        } else {
                            break;
                        }
                    }
                }
                let close = self.expect(Tok::RParen)?.span;
                Ok(Expr {
                    kind: ExprKind::CtorCall {
                        class,
                        class_span,
                        type_args: Vec::new(),
                        init,
                        args,
                    },
                    span: span.join(close),
                    ty: None,
                })
            }
            Tok::Ident(name) if name == "widen" || name == "narrow" => {
                let is_widen = name == "widen";
                self.bump();
                self.expect(Tok::Lt)?;
                let (target, _) = self.int_ty()?;
                self.expect(Tok::Gt)?;
                self.expect(Tok::LParen)?;
                let arg = self.expr()?;
                let close = self.expect(Tok::RParen)?.span;
                Ok(Expr {
                    kind: if is_widen {
                        ExprKind::Widen {
                            target,
                            arg: Box::new(arg),
                        }
                    } else {
                        ExprKind::Narrow {
                            target,
                            arg: Box::new(arg),
                        }
                    },
                    span: span.join(close),
                    ty: None,
                })
            }
            Tok::Ident(name) if name == "some" => {
                self.bump();
                self.expect(Tok::LParen)?;
                let arg = self.expr()?;
                let close = self.expect(Tok::RParen)?.span;
                Ok(Expr {
                    kind: ExprKind::SomeE(Box::new(arg)),
                    span: span.join(close),
                    ty: None,
                })
            }
            Tok::Ident(name) if name == "none" => {
                self.bump();
                Ok(Expr {
                    kind: ExprKind::NoneE,
                    span,
                    ty: None,
                })
            }
            Tok::Ident(name) => {
                self.bump();
                Ok(Expr {
                    kind: ExprKind::Var(name),
                    span,
                    ty: None,
                })
            }
            Tok::LParen => {
                self.bump();
                let mut e = self.expr()?;
                let close = self.expect(Tok::RParen)?.span;
                e.span = span.join(close);
                Ok(e)
            }
            Tok::LBracket => {
                self.bump();
                let mut elems = Vec::new();
                if !self.at(&Tok::RBracket) {
                    loop {
                        elems.push(self.expr()?);
                        if self.at(&Tok::Comma) {
                            self.bump();
                        } else {
                            break;
                        }
                    }
                }
                let close = self.expect(Tok::RBracket)?.span;
                Ok(Expr {
                    kind: ExprKind::ArrayLit(elems),
                    span: span.join(close),
                    ty: None,
                })
            }
            Tok::Amp => {
                self.bump();
                let mutable = if matches!(self.peek(), Tok::Ident(m) if m == "mut") {
                    self.bump();
                    true
                } else {
                    false
                };
                let (array, aspan) = self.ident()?;
                // `&x.f` — borrow a class-valued field.
                let (field, aspan) = if self.at(&Tok::Dot) {
                    self.bump();
                    let (f, fspan) = self.ident()?;
                    (Some(f), fspan)
                } else {
                    (None, aspan)
                };
                Ok(Expr {
                    kind: ExprKind::Borrow {
                        array,
                        field,
                        mutable,
                    },
                    span: span.join(aspan),
                    ty: None,
                })
            }
            _ => Err(self.error_expected("an expression")),
        }
    }
}

fn set_fn_variant(f: &mut Fn, clause: &Clause) -> PResult<()> {
    if f.variant.replace(clause.clone()).is_some() {
        return Err(Diagnostic {
            name: "proof.duplicate_variant".into(),
            title: "a function has at most one `variant`".into(),
            span: clause.line_span,
            label: "second `variant` clause".into(),
            notes: vec![],
        });
    }
    Ok(())
}

fn bad_clause(kind: ClauseKind, clause: &Clause, where_: &str, rule: &str) -> Diagnostic {
    Diagnostic {
        name: "proof.bad_clause".into(),
        title: format!("`{}` clause in {where_}", kind_word(kind)),
        span: clause.line_span,
        label: rule.to_string(),
        notes: vec![(
            "note".into(),
            "statement-level `assert` is not supported; a continuation \
             line must follow a clause"
                .into(),
        )],
    }
}

fn mk_bin(op: BinOp, op_span: Span, lhs: Expr, rhs: Expr) -> Expr {
    let span = lhs.span.join(rhs.span);
    Expr {
        kind: ExprKind::Binary {
            op,
            op_span,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        },
        span,
        ty: None,
    }
}

/// Names that would collide with the proof language or generated Lean.
fn is_reserved_name(name: &str) -> bool {
    const RESERVED: &[&str] = &[
        "result",
        "old",
        "mut",
        "some",
        "none",
        "option",
        "widen",
        "narrow",
        "theorem",
        "def",
        "by",
        "fun",
        "match",
        "with",
        "do",
        "let",
        "have",
        "show",
        "from",
        "open",
        "import",
        "namespace",
        "end",
        "in",
        "at",
        "forall",
        "exists",
        "Prop",
        "Type",
        "Int",
        "Nat",
        "Bool",
        "True",
        "False",
        "len",
        "alloc_array",
        "split_off",
        "join",
        "open_file",
        "posix_world",
        "test_uart",
        "uart_status",
        "uart_write",
        "raw_offset",
        "raw_load8",
        "raw_store8",
        "raw_copy_nonoverlapping",
        "raw_into_cell_u64",
        "raw_from_cell_u64",
        "raw_cell_init_u64",
        "raw_cell_read_u64",
        "raw_cell_take_u64",
        "raw_cell_drop_u64",
        "raw_into_free_header",
        "raw_from_free_header",
        "raw_header_init",
        "raw_header_size",
        "raw_header_next",
        "raw_header_clear",
        "allocator_take_header",
        "allocator_put_header",
        "allocator_step_header",
        "resource_map_empty",
        "resource_map_take",
        "resource_map_put",
        "static_alloc",
        "system_alloc",
        "system_dealloc",
        "expose",
        "as",
    ];
    RESERVED.contains(&name) || IntTy::from_name(name).is_some() || name == "bool"
}

fn reserved_name_error(name: &str, span: Span, what: &str) -> Diagnostic {
    Diagnostic {
        name: "parse.reserved_name".into(),
        title: format!("`{name}` cannot be used as a {what} name"),
        span,
        label: "reserved by the proof language".into(),
        notes: vec![(
            "note".into(),
            "program identifiers appear verbatim in proofs, so names that collide \
             with Lean keywords or Sable builtins are rejected"
                .into(),
        )],
    }
}

/// Free program identifiers of an expression (over-approximate: includes
/// array names and callees; used for `for`-bound stability checks).
fn expr_vars(e: &Expr, out: &mut std::collections::HashSet<String>) {
    match &e.kind {
        ExprKind::Var(n) => {
            out.insert(n.clone());
        }
        ExprKind::ResOp { args, .. }
        | ExprKind::RawOp { args, .. }
        | ExprKind::DeviceOp { args, .. } => {
            for a in args {
                expr_vars(a, out);
            }
        }
        ExprKind::Index { array, index, .. } => {
            out.insert(array.clone());
            expr_vars(index, out);
        }
        ExprKind::Len { array } => {
            out.insert(array.clone());
        }
        ExprKind::Unary { operand, .. } => expr_vars(operand, out),
        ExprKind::Widen { arg, .. } | ExprKind::Narrow { arg, .. } => expr_vars(arg, out),
        ExprKind::IsSome { operand } | ExprKind::OptValue { operand } => expr_vars(operand, out),
        ExprKind::TraitCall { args, .. } => {
            for a in args {
                expr_vars(a, out);
            }
        }
        ExprKind::ClassField { obj, .. }
        | ExprKind::RecordField { obj, .. }
        | ExprKind::ClassFieldLen { obj, .. } => {
            out.insert(obj.clone());
        }
        ExprKind::ClassFieldIndex { obj, index, .. } => {
            out.insert(obj.clone());
            expr_vars(index, out);
        }
        ExprKind::SomeE(inner) => expr_vars(inner, out),
        ExprKind::Binary { lhs, rhs, .. } => {
            expr_vars(lhs, out);
            expr_vars(rhs, out);
        }
        ExprKind::Call { args, .. } => {
            for a in args {
                expr_vars(a, out);
            }
        }
        ExprKind::ArrayLit(elems) => {
            for el in elems {
                expr_vars(el, out);
            }
        }
        ExprKind::AllocArray { len, init, .. } => {
            expr_vars(len, out);
            expr_vars(init, out);
        }
        ExprKind::SelfField { .. } | ExprKind::SelfFieldLen { .. } => {
            out.insert("self".to_string());
        }
        ExprKind::SelfFieldIndex { index, .. } => {
            out.insert("self".to_string());
            expr_vars(index, out);
        }
        ExprKind::CtorCall { args, .. } => {
            for a in args {
                expr_vars(a, out);
            }
        }
        ExprKind::RecordLit { args, .. } => {
            for a in args {
                expr_vars(a, out);
            }
        }
        ExprKind::MethodCall { recv, args, .. } => {
            out.insert(recv.clone());
            for a in args {
                expr_vars(a, out);
            }
        }
        ExprKind::Borrow { array, .. } => {
            out.insert(array.clone());
        }
        ExprKind::IntLit(_) | ExprKind::BoolLit(_) | ExprKind::NoneE => {}
    }
}

#[cfg(test)]
mod generic_type_arg_tests {
    use super::*;

    fn parse_source(source: &str) -> PResult<Program> {
        let scanned = crate::scan::scan(source);
        let tokens = crate::lexer::lex(&scanned.program_text).unwrap();
        let lines = LineMap::new(source);
        parse(&tokens, &scanned.blocks, &lines, &scanned.program_text)
    }

    fn parse_source_with_extern_generic_classes(
        source: &str,
        classes: &[(String, usize)],
    ) -> PResult<Program> {
        let scanned = crate::scan::scan(source);
        let tokens = crate::lexer::lex(&scanned.program_text).unwrap();
        let lines = LineMap::new(source);
        parse_module(
            &tokens,
            &scanned.blocks,
            &lines,
            &scanned.program_text,
            &[],
            classes,
            &[],
        )
    }

    fn type_parameter_names(count: usize) -> String {
        (0..count)
            .map(|index| format!("T{index}"))
            .collect::<Vec<_>>()
            .join(", ")
    }

    fn return_type_args(function: &Fn) -> &[TypeArg] {
        let Stmt::Return {
            value: Some(expression),
            ..
        } = &function.body[0]
        else {
            panic!("expected one return statement");
        };
        let ExprKind::Call { type_args, .. } = &expression.kind else {
            panic!("expected a generic call");
        };
        type_args
    }

    #[test]
    fn recursive_type_argument_parser_preserves_full_outer_spans() {
        let source = "record R #[layout(size := 1, align := 1)] {\n\
                          #[offset(0)] u8 value;\n\
                      }\n\
                      class Pair<A, B> {}\n\
                      fn concrete() -> i32 { return id<Pair<bool, option<[R]>>>(1); }\n\
                      fn generic<T>(T x) -> T { return id<T>(x); }\n";
        let program = parse_source(source).unwrap();

        let concrete = &return_type_args(&program.fns[0])[0];
        let concrete_text = "Pair<bool, option<[R]>>";
        let concrete_start = source.find(concrete_text).unwrap();
        assert_eq!(
            concrete.ty,
            GenericTy::Class {
                name: "Pair".into(),
                args: vec![
                    GenericTy::Bool,
                    GenericTy::Option(Box::new(GenericTy::Array(Box::new(GenericTy::Record(
                        "R".into()
                    ))))),
                ]
                .into_boxed_slice(),
            }
        );
        assert_eq!(
            concrete.span,
            Span::new(concrete_start, concrete_start + concrete_text.len())
        );

        let generic = &return_type_args(&program.fns[1])[0];
        let generic_start = source.rfind("T>(x)").unwrap();
        assert_eq!(generic.ty, GenericTy::Param(TypeParamId::from_legacy(0)));
        assert_eq!(generic.span, Span::new(generic_start, generic_start + 1));
    }

    #[test]
    fn recursive_arguments_support_multiple_outer_shapes_and_nested_closing_angles() {
        let source = "fn shapes() -> i32 {\n\
                          return id<[i32], option<option<bool>>>(0);\n\
                      }\n";
        let program = parse_source(source).unwrap();
        let arguments = return_type_args(&program.fns[0]);

        assert_eq!(
            arguments[0].ty,
            GenericTy::Array(Box::new(GenericTy::Int(IntTy::I32)))
        );
        assert_eq!(
            arguments[1].ty,
            GenericTy::Option(Box::new(GenericTy::Option(Box::new(GenericTy::Bool))))
        );
        for (argument, text) in arguments.iter().zip(["[i32]", "option<option<bool>>"]) {
            assert_eq!(&source[argument.span.start..argument.span.end], text);
        }
    }

    #[test]
    fn forward_generic_classes_and_nested_parameters_work_in_constructor_uses() {
        let source = "fn build<T>(T value) {\n\
                          Pair<option<T>, [bool]>::new();\n\
                      }\n\
                      class Pair<A: AnyTrait, B> {}\n";
        let program = parse_source(source).unwrap();
        let Stmt::ExprStmt(expression) = &program.fns[0].body[0] else {
            panic!("expected a constructor expression statement");
        };
        let ExprKind::CtorCall { type_args, .. } = &expression.kind else {
            panic!("expected a generic constructor call");
        };

        assert_eq!(
            type_args[0].ty,
            GenericTy::Option(Box::new(GenericTy::Param(TypeParamId::from_legacy(0))))
        );
        assert_eq!(type_args[1].ty, GenericTy::Array(Box::new(GenericTy::Bool)));
        assert_eq!(
            &source[type_args[0].span.start..type_args[0].span.end],
            "option<T>"
        );
        assert_eq!(
            &source[type_args[1].span.start..type_args[1].span.end],
            "[bool]"
        );
    }

    #[test]
    fn imported_generic_class_arities_are_visible_without_checked_class_indices() {
        let source = "fn use_box() -> i32 { return id<Box<i32>>(0); }\n";
        let program =
            parse_source_with_extern_generic_classes(source, &[("Box".into(), 1)]).unwrap();
        let argument = &return_type_args(&program.fns[0])[0];

        assert_eq!(
            argument.ty,
            GenericTy::Class {
                name: "Box".into(),
                args: vec![GenericTy::Int(IntTy::I32)].into_boxed_slice(),
            }
        );
        assert_eq!(&source[argument.span.start..argument.span.end], "Box<i32>");
    }

    #[test]
    fn unknown_comparison_operand_does_not_become_a_generic_type() {
        let source = "fn compare(i32 x, i32 y, i32 z) -> bool {\n\
                          return x < y > (z);\n\
                      }\n";
        let diagnostic = parse_source(source).unwrap_err();
        let greater = source.find("> (z)").unwrap();

        assert_eq!(diagnostic.name, "parse.chained_comparison");
        assert_eq!(diagnostic.span, Span::new(greater, greater + 1));
    }

    #[test]
    fn generic_recovery_does_not_scan_past_boolean_comparison_operators() {
        let source = "fn compare(i32 x, i32 y, i32 z) -> bool {\n\
                          return x < y && y > (z);\n\
                      }\n";
        let program = parse_source(source).unwrap();
        let Stmt::Return {
            value: Some(expression),
            ..
        } = &program.fns[0].body[0]
        else {
            panic!("expected a return expression");
        };
        let ExprKind::Binary { op: BinOp::And, .. } = &expression.kind else {
            panic!("expected two comparisons joined by &&");
        };
    }

    #[test]
    fn generic_recovery_probe_has_its_own_token_budget() {
        let arguments = vec!["i32"; MAX_GENERIC_RECOVERY_TOKENS].join(", ");
        let source = format!("id<{arguments}>(0)");
        let scanned = crate::scan::scan(&source);
        let tokens = crate::lexer::lex(&scanned.program_text).unwrap();
        let lines = LineMap::new(&source);
        let parser = Parser {
            tokens: &tokens,
            pos: 0,
            pending: Vec::new(),
            pending_mut: false,
            str_temps: 0,
            blocks: &scanned.blocks,
            consumed: vec![false; scanned.blocks.len()],
            lines: &lines,
            text: &scanned.program_text,
            tparams: Vec::new(),
            class_names: Vec::new(),
            generic_class_names: Vec::new(),
            record_names: Vec::new(),
        };

        assert!(!parser.malformed_generic_list_has_call_follower(1));
    }

    #[test]
    fn constructor_syntax_reports_an_unknown_recursive_type() {
        let source = "class Box<T> {}\n\
                      fn bad() { Box<Missing>::new(); }\n";
        let diagnostic = parse_source(source).unwrap_err();
        let missing = source.find("Missing").unwrap();

        assert_eq!(diagnostic.name, "parse.unknown_generic_type");
        assert_eq!(diagnostic.title, "unknown generic type `Missing`");
        assert_eq!(
            diagnostic.span,
            Span::new(missing, missing + "Missing".len())
        );
    }

    #[test]
    fn nominal_generic_argument_arity_errors_are_precise() {
        let cases = [
            (
                "record R #[layout(size := 1, align := 1)] { #[offset(0)] u8 x; }\n\
                 fn bad() -> i32 { return id<R<i32>>(0); }\n",
                "parse.record_type_args",
                "R<i32>",
                "expected 0, found 1",
            ),
            (
                "class Plain {}\n\
                 fn bad() -> i32 { return id<Plain<i32>>(0); }\n",
                "parse.nongeneric_class_type_args",
                "Plain<i32>",
                "expected 0, found 1",
            ),
            (
                "class Box<T> {}\n\
                 fn bad() -> i32 { return id<Box>(0); }\n",
                "parse.unsaturated_generic_class",
                "Box",
                "expected 1, found 0",
            ),
            (
                "class Pair<A, B> {}\n\
                 fn bad() -> i32 { return id<Pair<i32>>(0); }\n",
                "parse.generic_class_arity",
                "Pair<i32>",
                "expected 2, found 1",
            ),
            (
                "fn bad() -> i32 { return id<option<i32, bool>>(0); }\n",
                "parse.option_type_arity",
                "option<i32, bool>",
                "expected 1, found 2",
            ),
        ];

        for (source, name, marked, label) in cases {
            let diagnostic = parse_source(source).unwrap_err();
            let start = source.rfind(marked).unwrap();
            assert_eq!(diagnostic.name, name);
            assert_eq!(diagnostic.label, label);
            assert_eq!(diagnostic.span, Span::new(start, start + marked.len()));
        }
    }

    #[test]
    fn outer_and_nested_type_argument_lists_are_capped_at_256() {
        let at_limit = vec!["i32"; MAX_GENERIC_TYPE_ARGS].join(", ");
        let source = format!("fn limit() -> i32 {{ return id<{at_limit}>(0); }}\n");
        let program = parse_source(&source).unwrap();
        assert_eq!(
            return_type_args(&program.fns[0]).len(),
            MAX_GENERIC_TYPE_ARGS
        );

        let mut outer = vec!["i32"; MAX_GENERIC_TYPE_ARGS];
        outer.push("u8");
        let source = format!(
            "fn too_many() -> i32 {{ return id<{}>(0); }}\n",
            outer.join(", ")
        );
        let diagnostic = parse_source(&source).unwrap_err();
        let overflow = source.rfind("u8").unwrap();
        assert_eq!(diagnostic.name, "parse.too_many_type_args");
        assert_eq!(
            diagnostic.label,
            "at most 256 arguments are allowed in one list"
        );
        assert_eq!(diagnostic.span, Span::new(overflow, overflow + 2));

        let mut nested = vec!["i32"; MAX_GENERIC_TYPE_ARGS];
        nested.push("u8");
        let source = format!(
            "fn too_many() -> i32 {{ return id<option<{}>>(0); }}\n",
            nested.join(", ")
        );
        let diagnostic = parse_source(&source).unwrap_err();
        let overflow = source.rfind("u8").unwrap();
        assert_eq!(diagnostic.name, "parse.too_many_type_args");
        assert_eq!(diagnostic.span, Span::new(overflow, overflow + 2));
    }

    #[test]
    fn recursive_type_depth_is_capped_at_64_nodes() {
        let argument = format!(
            "{}i32{}",
            "option<".repeat(MAX_GENERIC_TYPE_DEPTH),
            ">".repeat(MAX_GENERIC_TYPE_DEPTH)
        );
        let source = format!("fn deep() -> i32 {{ return id<{argument}>(0); }}\n");
        let diagnostic = parse_source(&source).unwrap_err();
        let leaf = source.rfind("i32").unwrap();

        assert_eq!(diagnostic.name, "parse.generic_type_too_deep");
        assert_eq!(
            diagnostic.label,
            "at most 64 recursive type nodes may occur on one path"
        );
        assert_eq!(diagnostic.span, Span::new(leaf, leaf + 3));
    }

    #[test]
    fn each_outer_type_argument_has_a_4096_node_budget() {
        let parameters = type_parameter_names(MAX_GENERIC_TYPE_ARGS);
        let branch = format!("{}i32{}", "option<".repeat(16), ">".repeat(16));
        let argument = format!("Many<{}>", vec![branch; MAX_GENERIC_TYPE_ARGS].join(", "));
        let source = format!(
            "class Many<{parameters}> {{}}\n\
             fn large() -> i32 {{ return id<{argument}>(0); }}\n"
        );
        let diagnostic = parse_source(&source).unwrap_err();

        assert_eq!(diagnostic.name, "parse.generic_type_too_large");
        assert_eq!(
            diagnostic.label,
            "at most 4096 nodes are allowed in one outer type argument"
        );
        assert!(matches!(
            &source[diagnostic.span.start..diagnostic.span.end],
            "option" | "i32"
        ));
    }

    #[test]
    fn monomorphization_still_rejects_new_recursive_shapes_at_their_outer_span() {
        let source = "fn id<T>(T value) -> T { return value; }\n\
                      fn use_bool() -> bool { return id<bool>(true); }\n";
        let mut program = parse_source(source).unwrap();
        let expected_span = return_type_args(&program.fns[1])[0].span;
        let diagnostic = crate::mono::monomorphize(&mut program).unwrap_err();

        assert_eq!(diagnostic.name, "mono.type_arg_unsupported");
        assert_eq!(diagnostic.span, expected_span);
        assert_eq!(&source[diagnostic.span.start..diagnostic.span.end], "bool");
    }

    #[test]
    fn declaration_type_parameters_keep_non_integer_representations() {
        let source = r#"
fn plumbing<T>(&[T] input, T value) -> option<T> {
    [T] copy = alloc_array<T>(input.len, value);
    return some(copy[0]);
}
"#;
        let program = parse_source(source).unwrap();
        let function = &program.fns[0];
        let parameter = TypeParamId::from_legacy(0);

        assert_eq!(
            function.params[0].ty,
            Ty::Array(ValueTy::Param(parameter), Mutability::Shared)
        );
        assert_eq!(function.params[1].ty, Ty::Param(parameter));
        assert_eq!(function.ret, Ty::Option(ValueTy::Param(parameter)));

        let Stmt::Decl {
            ty,
            init: Some(initializer),
            ..
        } = &function.body[0]
        else {
            panic!("expected the owned array declaration");
        };
        assert_eq!(*ty, Ty::Array(ValueTy::Param(parameter), Mutability::Owned));
        let ExprKind::AllocArray { elem, .. } = &initializer.kind else {
            panic!("expected alloc_array initializer");
        };
        assert_eq!(*elem, ValueTy::Param(parameter));
    }

    #[test]
    fn bool_options_parse_without_widening_array_payload_syntax() {
        let source = r#"
fn choose(i32 value) -> option<bool> {
    mut option<bool> r = none;
    r = some(value > 0);
    return r;
}
"#;
        let program = parse_source(source).unwrap();
        let function = &program.fns[0];
        assert_eq!(function.ret, Ty::Option(ValueTy::Bool));

        let Stmt::Decl {
            ty,
            init: Some(initializer),
            mutable,
            ..
        } = &function.body[0]
        else {
            panic!("expected the explicit option local");
        };
        assert_eq!(*ty, Ty::Option(ValueTy::Bool));
        assert!(*mutable);
        assert!(matches!(&initializer.kind, ExprKind::NoneE));

        let Stmt::Assign { value, .. } = &function.body[1] else {
            panic!("expected the contextual option assignment");
        };
        let ExprKind::SomeE(payload) = &value.kind else {
            panic!("expected some(Boolean expression)");
        };
        assert!(matches!(
            &payload.kind,
            ExprKind::Binary { op: BinOp::Gt, .. }
        ));

        let array_error = parse_source("fn bad(&[bool] values) {}\n").unwrap_err();
        assert_eq!(array_error.name, "parse.unknown_type");
        assert!(array_error.title.contains("bool"));

        let allocation_error =
            parse_source("fn bad() { var values = alloc_array<bool>(1, false); }\n").unwrap_err();
        assert_eq!(allocation_error.name, "parse.unknown_type");
        assert!(allocation_error.title.contains("bool"));
    }

    #[test]
    fn visible_record_option_payload_reaches_the_checker_boundary() {
        let source = r#"
record Pair #[layout(size := 1, align := 1)] {
    #[offset(0)] u8 value;
}

fn unsupported() -> option<Pair> {
    return none;
}
"#;
        let program = parse_source(source).unwrap();
        assert_eq!(program.fns[0].ret, Ty::Option(ValueTy::Record(0)));
    }

    #[test]
    fn type_parameter_ceiling_accepts_256_and_rejects_the_257th_name() {
        let names = type_parameter_names(MAX_TYPE_PARAMS);
        let last = format!("T{}", MAX_TYPE_PARAMS - 1);
        let source = format!("fn wide<{names}>({last} x) -> {last} {{ return x; }}\n");
        let program = parse_source(&source).unwrap();

        assert_eq!(program.fns[0].type_params.len(), MAX_TYPE_PARAMS);
        let last_parameter = TypeParamId::from_legacy(u8::MAX);
        assert_eq!(program.fns[0].params[0].ty, Ty::Param(last_parameter));
        assert_eq!(program.fns[0].ret, Ty::Param(last_parameter));

        let names = type_parameter_names(MAX_TYPE_PARAMS + 1);
        let source = format!("fn too_wide<{names}>() {{}}\n");
        let overflow_name = format!("T{MAX_TYPE_PARAMS}");
        let overflow_start = source.rfind(&overflow_name).unwrap();
        let diagnostic = parse_source(&source).unwrap_err();

        assert_eq!(diagnostic.name, "parse.too_many_type_params");
        assert_eq!(diagnostic.title, "too many type parameters");
        assert_eq!(
            diagnostic.label,
            format!("at most {MAX_TYPE_PARAMS} type parameters are supported")
        );
        assert_eq!(
            diagnostic.span,
            Span::new(overflow_start, overflow_start + overflow_name.len())
        );
    }

    #[test]
    fn duplicate_type_parameter_points_at_the_repeated_name() {
        let source = "fn duplicate<T, U, T>() {}\n";
        let duplicate_start = source.rfind("T>").unwrap();
        let diagnostic = parse_source(source).unwrap_err();

        assert_eq!(diagnostic.name, "parse.duplicate_type_param");
        assert_eq!(diagnostic.title, "duplicate type parameter `T`");
        assert_eq!(diagnostic.label, "type parameter names must be unique");
        assert_eq!(
            diagnostic.span,
            Span::new(duplicate_start, duplicate_start + 1)
        );
    }
}
