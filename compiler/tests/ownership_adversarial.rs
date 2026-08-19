//! Generated adversarial coverage for ownership interactions at user-call boundaries.
//!
//! This is intentionally a constrained pairwise generator, not a random source
//! fuzzer.  Every selected case has a typed semantic oracle: either the checker
//! must refuse one exact alias/move family by name, or the whole generated bundle
//! must verify with Lean and return the same value dynamically.  The constraints
//! are part of the test.  In particular, a permanent move is not put on a loop
//! backedge, and receiver-only calls are not described as argument reorderings.

use sable::interp::RtVal;
use sable::{Options, load_checked, verify_file_structured};
use std::collections::BTreeSet;
use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Site {
    Free,
    Constructor,
    Method,
}

impl Site {
    const ALL: [Self; 3] = [Self::Free, Self::Constructor, Self::Method];

    const fn label(self) -> &'static str {
        match self {
            Self::Free => "free",
            Self::Constructor => "constructor",
            Self::Method => "method",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Interaction {
    Arguments,
    ReceiverAndArguments,
}

impl Interaction {
    const fn label(self) -> &'static str {
        match self {
            Self::Arguments => "arguments",
            Self::ReceiverAndArguments => "receiver+arguments",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
/// Effect carried by the explicit `affected` argument. Method receivers in
/// the receiver+arguments interaction are always shared and evaluate first.
enum Effect {
    Shared,
    Unique,
    Move,
}

impl Effect {
    const ALL: [Self; 3] = [Self::Shared, Self::Unique, Self::Move];

    const fn label(self) -> &'static str {
        match self {
            Self::Shared => "shared",
            Self::Unique => "unique",
            Self::Move => "move",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Relation {
    RootRoot,
    RootDirectField,
}

impl Relation {
    const ALL: [Self; 2] = [Self::RootRoot, Self::RootDirectField];

    const fn label(self) -> &'static str {
        match self {
            Self::RootRoot => "root/root",
            Self::RootDirectField => "root/direct-field",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Evaluation {
    LoanThenEffect,
    EffectThenLoan,
    NestedEffect,
}

impl Evaluation {
    const ALL: [Self; 3] = [
        Self::LoanThenEffect,
        Self::EffectThenLoan,
        Self::NestedEffect,
    ];

    const fn label(self) -> &'static str {
        match self {
            Self::LoanThenEffect => "loan-then-effect",
            Self::EffectThenLoan => "effect-then-loan",
            Self::NestedEffect => "nested-effect",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Context {
    Straight,
    Branch,
    EarlyReturn,
    OneLoop,
}

impl Context {
    const ALL: [Self; 4] = [
        Self::Straight,
        Self::Branch,
        Self::EarlyReturn,
        Self::OneLoop,
    ];

    const fn label(self) -> &'static str {
        match self {
            Self::Straight => "straight",
            Self::Branch => "branch",
            Self::EarlyReturn => "early-return",
            Self::OneLoop => "one-loop",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Case {
    site: Site,
    interaction: Interaction,
    effect: Effect,
    relation: Relation,
    evaluation: Evaluation,
    context: Context,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Oracle {
    VerifyAndRun(i128),
    Refuse(&'static str),
}

impl Case {
    fn factors(self) -> [&'static str; 6] {
        [
            self.site.label(),
            self.interaction.label(),
            self.effect.label(),
            self.relation.label(),
            self.evaluation.label(),
            self.context.label(),
        ]
    }

    const fn oracle(self) -> Oracle {
        match (self.effect, self.evaluation) {
            (Effect::Shared, _) => Oracle::VerifyAndRun(42),
            (
                Effect::Unique,
                Evaluation::LoanThenEffect | Evaluation::EffectThenLoan | Evaluation::NestedEffect,
            ) => Oracle::Refuse("borrow.conflict"),
            (Effect::Move, Evaluation::EffectThenLoan) => Oracle::Refuse("class.use_after_move"),
            (Effect::Move, Evaluation::LoanThenEffect | Evaluation::NestedEffect) => {
                Oracle::Refuse("borrow.moved_in_call")
            }
        }
    }
}

fn candidate_cases() -> Vec<Case> {
    let mut cases = Vec::new();
    for site in Site::ALL {
        for interaction in [Interaction::Arguments, Interaction::ReceiverAndArguments] {
            if interaction == Interaction::ReceiverAndArguments && site != Site::Method {
                continue;
            }
            for effect in Effect::ALL {
                for relation in Relation::ALL {
                    for evaluation in Evaluation::ALL {
                        // An implicit receiver is necessarily evaluated before
                        // every explicit argument. There is no honest
                        // effect-then-loan ordering for this interaction: the
                        // receiver's shared reservation is always first.
                        if interaction == Interaction::ReceiverAndArguments
                            && evaluation == Evaluation::EffectThenLoan
                        {
                            continue;
                        }
                        for context in Context::ALL {
                            // A move cannot be repeated on a backedge.  Loop
                            // coverage therefore uses shared or temporary unique
                            // loans only; early-return cases cover permanent moves.
                            if effect == Effect::Move && context == Context::OneLoop {
                                continue;
                            }
                            cases.push(Case {
                                site,
                                interaction,
                                effect,
                                relation,
                                evaluation,
                                context,
                            });
                        }
                    }
                }
            }
        }
    }
    cases
}

fn pair_tokens(case: Case) -> BTreeSet<String> {
    let factors = case.factors();
    let mut pairs = BTreeSet::new();
    for left in 0..factors.len() {
        for right in (left + 1)..factors.len() {
            pairs.insert(format!(
                "{left}:{}|{right}:{}",
                factors[left], factors[right]
            ));
        }
    }
    pairs
}

fn pairwise_cases() -> Vec<Case> {
    let candidates = candidate_cases();
    let mut uncovered: BTreeSet<String> = candidates
        .iter()
        .flat_map(|case| pair_tokens(*case))
        .collect();
    let mut selected = Vec::new();

    while !uncovered.is_empty() {
        let (best, score) = candidates
            .iter()
            .copied()
            .filter(|case| !selected.contains(case))
            .map(|case| {
                let score = pair_tokens(case).intersection(&uncovered).count();
                (case, score)
            })
            .max_by(|(left_case, left_score), (right_case, right_score)| {
                left_score
                    .cmp(right_score)
                    .then_with(|| right_case.cmp(left_case))
            })
            .expect("an uncovered feasible pair has a candidate");
        assert!(score > 0, "pairwise selection made no progress");
        for pair in pair_tokens(best) {
            uncovered.remove(&pair);
        }
        selected.push(best);
    }

    // These anchors make the intended high-risk seams readable even if a
    // future factor changes the greedy covering-array tie break.
    let anchors = [
        Case {
            site: Site::Free,
            interaction: Interaction::Arguments,
            effect: Effect::Shared,
            relation: Relation::RootRoot,
            evaluation: Evaluation::LoanThenEffect,
            context: Context::Straight,
        },
        Case {
            site: Site::Constructor,
            interaction: Interaction::Arguments,
            effect: Effect::Unique,
            relation: Relation::RootDirectField,
            evaluation: Evaluation::NestedEffect,
            context: Context::Branch,
        },
        Case {
            site: Site::Method,
            interaction: Interaction::ReceiverAndArguments,
            effect: Effect::Unique,
            relation: Relation::RootDirectField,
            evaluation: Evaluation::LoanThenEffect,
            context: Context::Straight,
        },
        Case {
            site: Site::Method,
            interaction: Interaction::ReceiverAndArguments,
            effect: Effect::Move,
            relation: Relation::RootRoot,
            evaluation: Evaluation::NestedEffect,
            context: Context::EarlyReturn,
        },
        Case {
            site: Site::Method,
            interaction: Interaction::Arguments,
            effect: Effect::Shared,
            relation: Relation::RootDirectField,
            evaluation: Evaluation::NestedEffect,
            context: Context::OneLoop,
        },
    ];
    for anchor in anchors {
        if !selected.contains(&anchor) {
            selected.push(anchor);
        }
    }
    selected
}

struct TestTempDir {
    path: PathBuf,
}

impl std::ops::Deref for TestTempDir {
    type Target = Path;

    fn deref(&self) -> &Self::Target {
        &self.path
    }
}

impl Drop for TestTempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

fn temp_dir() -> TestTempDir {
    static NEXT: AtomicU64 = AtomicU64::new(0);
    let path = std::env::temp_dir().join(format!(
        "sable-ownership-adversarial-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&path).expect("create adversarial test directory");
    TestTempDir { path }
}

fn write_source(dir: &Path, name: &str, source: &str) -> PathBuf {
    let path = dir.join(format!("{name}.sable"));
    fs::write(&path, source).expect("write generated adversarial source");
    path
}

fn render_context(context: Context, statement: &str) -> String {
    match context {
        Context::Straight => format!("    {statement}\n    return 42;\n"),
        Context::Branch => {
            // Sable deliberately forbids reusing one local name even in
            // disjoint lexical arms, so constructor-result binders are
            // distinct here. This is not an alpha-equivalence claim about
            // the call itself; it only keeps both generated sites well formed.
            let then_statement = statement.replace("var produced =", "var produced_then =");
            let else_statement = statement.replace("var produced =", "var produced_else =");
            format!(
                "    if (true) {{\n        {then_statement}\n    }} else {{\n        {else_statement}\n    }}\n    return 42;\n"
            )
        }
        Context::EarlyReturn => format!(
            "    if (true) {{\n        {statement}\n        return 42;\n    }}\n    return 42;\n"
        ),
        Context::OneLoop => format!(
            "    mut u64 turn = 0;\n    /// invariant turn <= 1\n    /// variant 1 - turn\n    while (turn < 1) {{\n        {statement}\n        turn = turn + 1;\n    }}\n    return 42;\n"
        ),
    }
}

fn render_case(case: Case, index: usize) -> (String, String) {
    let suffix = format!("{index:03}");
    let item = format!("AdvItem{suffix}");
    let holder = format!("AdvHolder{suffix}");
    let target = format!("AdvTarget{suffix}");
    let driver = format!("AdvDriver{suffix}");
    let helper = format!("adv_helper_{suffix}");
    let entry = format!("adv_case_{suffix}");
    let root_ty = match case.relation {
        Relation::RootRoot => item.as_str(),
        Relation::RootDirectField => holder.as_str(),
    };
    let loan_expr = match case.relation {
        Relation::RootRoot => "&root".to_string(),
        Relation::RootDirectField => "&root.item".to_string(),
    };
    let effect_expr = match case.effect {
        Effect::Shared => "&root".to_string(),
        Effect::Unique => "&mut root".to_string(),
        Effect::Move => "root".to_string(),
    };
    let effect_ty = match case.effect {
        Effect::Shared => format!("&{root_ty}"),
        Effect::Unique => format!("&mut {root_ty}"),
        Effect::Move => root_ty.to_string(),
    };

    let mut helper_decl = String::new();
    let (params, args) = if case.evaluation == Evaluation::NestedEffect {
        match case.effect {
            Effect::Shared | Effect::Unique => {
                writeln!(
                    helper_decl,
                    "fn {helper}({effect_ty} affected) -> u64 {{\n    return 0;\n}}\n"
                )
                .unwrap();
                (
                    format!("&{item} loan, u64 marker"),
                    format!("{loan_expr}, {helper}({effect_expr})"),
                )
            }
            Effect::Move => {
                writeln!(
                    helper_decl,
                    "fn {helper}({root_ty} affected) -> {root_ty} {{\n    return affected;\n}}\n"
                )
                .unwrap();
                (
                    format!("&{item} loan, {root_ty} affected"),
                    format!("{loan_expr}, {helper}({effect_expr})"),
                )
            }
        }
    } else if case.evaluation == Evaluation::LoanThenEffect {
        (
            format!("&{item} loan, {effect_ty} affected"),
            format!("{loan_expr}, {effect_expr}"),
        )
    } else {
        (
            format!("{effect_ty} affected, &{item} loan"),
            format!("{effect_expr}, {loan_expr}"),
        )
    };

    let mut receiver_method = String::new();
    let mut target_decl = String::new();
    let mut extra_setup = String::new();
    let statement = match (case.site, case.interaction) {
        (Site::Free, Interaction::Arguments) => {
            writeln!(target_decl, "fn {target}({params}) {{\n}}\n").unwrap();
            format!("{target}({args});")
        }
        (Site::Constructor, Interaction::Arguments) => {
            writeln!(
                target_decl,
                "class {target} {{\n    u64 marker;\n\n    init call({params}) {{\n        self.marker = 0;\n    }}\n}}\n"
            )
            .unwrap();
            format!("var produced = {target}::call({args});")
        }
        (Site::Method, Interaction::Arguments) => {
            writeln!(
                target_decl,
                "class {driver} {{\n    u64 marker;\n\n    init new() {{\n        self.marker = 0;\n    }}\n\n    fn call(&self, {params}) {{\n    }}\n}}\n"
            )
            .unwrap();
            writeln!(extra_setup, "    var driver = {driver}::new();").unwrap();
            format!("driver.call({args});")
        }
        (Site::Method, Interaction::ReceiverAndArguments) => {
            // `Effect` is consistently the explicit argument effect. Mutable
            // receiver behavior has focused checker tests rather than a
            // factor label that changes meaning for one generated case.
            writeln!(receiver_method, "\n    fn call(&self, {params}) {{\n    }}").unwrap();
            format!("root.call({args});")
        }
        (Site::Free | Site::Constructor, Interaction::ReceiverAndArguments) => {
            unreachable!("receiver interactions are method-only")
        }
    };

    let item_method = if case.interaction == Interaction::ReceiverAndArguments
        && case.relation == Relation::RootRoot
    {
        receiver_method.as_str()
    } else {
        ""
    };
    let holder_method = if case.interaction == Interaction::ReceiverAndArguments
        && case.relation == Relation::RootDirectField
    {
        receiver_method.as_str()
    } else {
        ""
    };

    let setup = match case.relation {
        Relation::RootRoot => format!("    var mut root = {item}::new(1);\n{extra_setup}"),
        Relation::RootDirectField => format!(
            "    var inner = {item}::new(1);\n    var mut root = {holder}::wrap(inner);\n{extra_setup}"
        ),
    };
    let body = render_context(case.context, &statement);
    let source = format!(
        "// generated ownership case: {} / {} / {} / {} / {} / {}\n\
         class {item} {{\n    u64 value;\n\n    init new(u64 initial) {{\n        self.value = initial;\n    }}{item_method}\n}}\n\n\
         class {holder} {{\n    {item} item;\n\n    init wrap({item} initial) {{\n        self.item = initial;\n    }}{holder_method}\n}}\n\n\
         {helper_decl}{target_decl}\
         /// post result = 42\n\
         fn {entry}() -> u64 {{\n{setup}{body}}}\n\n",
        case.site.label(),
        case.interaction.label(),
        case.effect.label(),
        case.relation.label(),
        case.evaluation.label(),
        case.context.label(),
    );
    (entry, source)
}

fn render_metamorphic_source() -> (&'static [&'static str], String) {
    const ENTRIES: &[&str] = &[
        "meta_base",
        "meta_alpha_renamed",
        "meta_dead_disjoint",
        "meta_independent_reorder",
    ];
    let source = r#"
class MetaItem {
    u64 value;

    /// invariant value <= 100

    /// pre initial <= 100
    /// post self.value = initial
    init new(u64 initial) {
        self.value = initial;
    }

    /// pre next <= 100
    /// post self.value = next
    fn set(&mut self, u64 next) {
        self.value = next;
    }

    /// post result = self.value
    fn get(&self) -> u64 {
        return self.value;
    }
}

/// post result = 42
fn meta_base() -> u64 {
    var mut left = MetaItem::new(0);
    var mut right = MetaItem::new(0);
    left.set(10);
    right.set(32);
    return left.get() + right.get();
}

// Alpha-renaming changes only local binders, never fields or call targets.
/// post result = 42
fn meta_alpha_renamed() -> u64 {
    var mut first_owner = MetaItem::new(0);
    var mut second_owner = MetaItem::new(0);
    first_owner.set(10);
    second_owner.set(32);
    return first_owner.get() + second_owner.get();
}

// The extra owner is dead and disjoint from both observed owners.
/// post result = 42
fn meta_dead_disjoint() -> u64 {
    var mut left = MetaItem::new(0);
    var mut right = MetaItem::new(0);
    var dead_disjoint = MetaItem::new(7);
    left.set(10);
    right.set(32);
    return left.get() + right.get();
}

// These calls touch distinct roots; that side condition is why reordering is safe.
/// post result = 42
fn meta_independent_reorder() -> u64 {
    var mut left = MetaItem::new(0);
    var mut right = MetaItem::new(0);
    right.set(32);
    left.set(10);
    return left.get() + right.get();
}
"#;
    (ENTRIES, source.to_string())
}

fn false_post_twins_source() -> (&'static [(&'static str, &'static str)], &'static str) {
    const TWINS: &[(&str, &str)] = &[
        ("counter_twin_free", "free_stale"),
        ("counter_twin_constructor", "constructor_stale"),
        ("counter_twin_method", "method_stale"),
        ("counter_twin_nested", "nested_stale"),
    ];
    let source = r#"
class CounterItem {
    u64 value;

    /// invariant value <= 100

    /// pre initial <= 100
    /// post self.value = initial
    init new(u64 initial) {
        self.value = initial;
    }

    /// post self.value = 9
    fn set_nine(&mut self) {
        self.value = 9;
    }

    /// post result = self.value
    fn get(&self) -> u64 {
        return self.value;
    }
}

/// post item.value = 9
fn counter_free_set(&mut CounterItem item) {
    item.set_nine();
}

class CounterTouch {
    u64 marker;

    /// post item.value = 9
    init run(&mut CounterItem item) {
        item.set_nine();
        self.marker = 0;
    }
}

/// post item.value = 9
/// post result = 0
fn counter_nested_set(&mut CounterItem item) -> u64 {
    item.set_nine();
    return 0;
}

/// post result = item.value
fn counter_observe(&CounterItem item, u64 marker) -> u64 {
    return item.get();
}

/// post #[label(free_stale)] result = 1
fn counter_twin_free() -> u64 {
    var mut item = CounterItem::new(1);
    counter_free_set(&mut item);
    return item.get();
}

/// post #[label(constructor_stale)] result = 1
fn counter_twin_constructor() -> u64 {
    var mut item = CounterItem::new(1);
    var touched = CounterTouch::run(&mut item);
    return item.get();
}

/// post #[label(method_stale)] result = 1
fn counter_twin_method() -> u64 {
    var mut item = CounterItem::new(1);
    item.set_nine();
    return item.get();
}

/// post #[label(nested_stale)] result = 1
fn counter_twin_nested() -> u64 {
    var mut item = CounterItem::new(1);
    return counter_observe(&item, counter_nested_set(&mut item));
}
"#;
    (TWINS, source)
}

fn nested_timing_regression_source() -> &'static str {
    r#"
class NestedTimingItem {
    u64 value;

    /// post self.value = initial
    init new(u64 initial) {
        self.value = initial;
    }

    /// post self.value = 9
    fn set_nine(&mut self) {
        self.value = 9;
    }

    /// post result = self.value
    fn get(&self) -> u64 {
        return self.value;
    }
}

/// post item.value = 9
/// post result = 0
fn nested_timing_set(&mut NestedTimingItem item) -> u64 {
    item.set_nine();
    return 0;
}

/// post result = item.value
fn nested_timing_observe(&NestedTimingItem item, u64 marker) -> u64 {
    return item.get();
}

/// post #[label(stale)] result = 1
fn nested_timing_false_post() -> u64 {
    var mut item = NestedTimingItem::new(1);
    return nested_timing_observe(&item, nested_timing_set(&mut item));
}

fn nested_timing_actual() -> u64 {
    var mut item = NestedTimingItem::new(1);
    return nested_timing_observe(&item, nested_timing_set(&mut item));
}
"#
}

fn verify(path: &Path) -> (sable::modules::ModuleSet, sable::VerifiedProgram) {
    let (mods, verified) = verify_file_structured(path, &Options::default());
    let verified = verified.unwrap_or_else(|diagnostics| {
        panic!(
            "{} failed verification:\n{}",
            path.display(),
            diagnostics
                .iter()
                .map(|diagnostic| mods.render(diagnostic))
                .collect::<Vec<_>>()
                .join("\n")
        )
    });
    (mods, verified)
}

#[test]
fn generated_selection_covers_every_feasible_pair() {
    let candidates = candidate_cases();
    let selected = pairwise_cases();
    assert!(candidates.iter().all(|case| {
        case.interaction != Interaction::ReceiverAndArguments
            || case.evaluation != Evaluation::EffectThenLoan
    }));
    assert!(
        selected.len() <= 40,
        "the bounded covering array unexpectedly grew to {} cases",
        selected.len()
    );
    let feasible: BTreeSet<String> = candidates
        .iter()
        .flat_map(|case| pair_tokens(*case))
        .collect();
    let covered: BTreeSet<String> = selected
        .iter()
        .flat_map(|case| pair_tokens(*case))
        .collect();
    assert_eq!(covered, feasible);
    assert!(
        selected
            .iter()
            .any(|case| matches!(case.oracle(), Oracle::VerifyAndRun(_)))
    );
    assert!(
        selected
            .iter()
            .any(|case| matches!(case.oracle(), Oracle::Refuse("borrow.conflict")))
    );
    assert!(
        selected
            .iter()
            .any(|case| matches!(case.oracle(), Oracle::Refuse("borrow.moved_in_call")))
    );
    assert!(selected.iter().any(|case| {
        case.interaction == Interaction::ReceiverAndArguments
            && case.relation == Relation::RootDirectField
    }));
}

#[test]
fn generated_adversarial_ownership_oracles_and_metamorphs() {
    let dir = temp_dir();
    let cases = pairwise_cases();
    let mut accepted_source =
        String::from("// Accepted half of the generated adversarial ownership matrix.\n\n");
    let mut accepted_entries = Vec::new();

    for (index, case) in cases.iter().copied().enumerate() {
        let (entry, source) = render_case(case, index);
        match case.oracle() {
            Oracle::VerifyAndRun(expected) => {
                accepted_source.push_str(&source);
                accepted_entries.push((entry, expected));
            }
            Oracle::Refuse(expected) => {
                let path = write_source(&dir, &format!("refused_{index:03}"), &source);
                let failures = match load_checked(&path, &Options::default()) {
                    Ok(_) => panic!("an aliased generated case must be refused: {case:?}"),
                    Err(failures) => failures,
                };
                assert!(
                    failures.iter().any(|failure| failure.name == expected),
                    "wrong refusal for {case:?}; expected `{expected}`, got:\n{}",
                    failures
                        .iter()
                        .map(|failure| failure.rendered.as_str())
                        .collect::<Vec<_>>()
                        .join("\n")
                );
            }
        }
    }

    let accepted_path = write_source(&dir, "accepted_matrix", &accepted_source);
    let (accepted_mods, accepted) = verify(&accepted_path);
    for (entry, expected) in accepted_entries {
        let value = sable::interp::run_verified_fn(&accepted, &accepted_mods, &entry)
            .unwrap_or_else(|trap| panic!("verified adversarial case `{entry}` trapped: {trap}"));
        let RtVal::Int(actual) = value else {
            panic!("verified adversarial case `{entry}` returned a non-integer")
        };
        assert_eq!(actual, expected, "dynamic oracle for `{entry}`");
    }

    let (meta_entries, meta_source) = render_metamorphic_source();
    let meta_path = write_source(&dir, "safe_metamorphs", &meta_source);
    let (meta_mods, meta) = verify(&meta_path);
    for entry in meta_entries {
        let value = sable::interp::run_verified_fn(&meta, &meta_mods, entry)
            .unwrap_or_else(|trap| panic!("safe metamorphic variant `{entry}` trapped: {trap}"));
        let RtVal::Int(actual) = value else {
            panic!("safe metamorphic variant `{entry}` returned a non-integer")
        };
        assert_eq!(actual, 42, "metamorphic result for `{entry}`");
    }
}

#[test]
fn direct_false_post_twins_fail_proof_and_runtime() {
    let dir = temp_dir();
    let (twins, twin_source) = false_post_twins_source();
    for (entry, label) in &twins[..3] {
        // Isolate each false post. Lean is allowed to stop elaborating later
        // declarations after earlier theorem errors, so one multi-error file
        // would not prove that every formerly stale family was independently
        // rejected.
        let mut isolated = twin_source.to_string();
        for (other_entry, other_label) in twins {
            if other_entry == entry {
                continue;
            }
            isolated = isolated.replace(
                &format!("/// post #[label({other_label})] result = 1"),
                "/// post result = 9",
            );
        }
        // The fourth historical twin is now a front-end temporal-loan
        // refusal. Keep it out of these three proof/runtime isolates by
        // applying its sound ordering rewrite; its own test below retains
        // the minimized invalid source and requires `borrow.conflict`.
        isolated = isolated.replace(
            "return counter_observe(&item, counter_nested_set(&mut item));",
            "counter_nested_set(&mut item);\n    return counter_observe(&item, 0);",
        );
        let twin_path = write_source(&dir, &format!("false_post_{label}"), &isolated);
        let (checked_twin, twin_mods) = match load_checked(&twin_path, &Options::default()) {
            Ok(loaded) => loaded,
            Err(failures) => panic!(
                "false post `{label}` must pass typing so both oracles can inspect it:\n{}",
                failures
                    .iter()
                    .map(|failure| failure.rendered.as_str())
                    .collect::<Vec<_>>()
                    .join("\n")
            ),
        };
        let failure = sable::interp::run_checked_fn(&checked_twin, &twin_mods, entry)
            .expect_err("the dynamic twin must exhibit the false post");
        assert!(
            failure.contains(&format!("post of `{entry}` violated")),
            "wrong dynamic counterexample for `{entry}`: {failure}"
        );

        let (proof_mods, proof_result) = verify_file_structured(&twin_path, &Options::default());
        let diagnostics = match proof_result {
            Err(diagnostics) => diagnostics,
            Ok(_) => panic!("Lean verified the isolated false post `{label}`"),
        };
        let expected = format!("{entry}.post.{label}");
        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.name == expected),
            "missing proof refusal `{expected}`; got:\n{}",
            diagnostics
                .iter()
                .map(|diagnostic| proof_mods.render(diagnostic))
                .collect::<Vec<_>>()
                .join("\n")
        );
    }
}

#[test]
fn nested_unique_argument_mutation_conflicts_with_pending_outer_state() {
    let dir = temp_dir();
    let path = write_source(
        &dir,
        "nested_unique_argument_timing",
        nested_timing_regression_source(),
    );
    let diagnostics = match load_checked(&path, &Options::default()) {
        Err(diagnostics) => diagnostics,
        Ok(_) => panic!("the nested timing witness must be rejected before VC generation"),
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.name == "borrow.conflict"),
        "missing temporal borrow refusal for the stale nested-call witness:\n{}",
        diagnostics
            .iter()
            .map(|diagnostic| diagnostic.rendered.as_str())
            .collect::<Vec<_>>()
            .join("\n")
    );
}
