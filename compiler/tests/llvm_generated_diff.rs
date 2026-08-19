//! Generated differential coverage for the admitted native subset.
//!
//! The generator works over a small typed case IR rather than arbitrary source
//! text. It exhausts the cross-product of admitted scalar widths and arithmetic
//! operations over bounded operands, then crosses the ownership-bearing shapes
//! the LLVM gate actually admits: fixed-owner class moves/rebinding, shared and
//! unique Boolean/`u32` array borrows, nested lexical exits, and loop-carried
//! class replacement, Boolean-array affine-option cleanup, and the admitted
//! mutable class receiver. Deliberately unsupported owner compositions are
//! generated separately to pin their fail-closed diagnostics. Scalar cases
//! retain compact bit-vector batches. Every admitted ownership case instead
//! gets its own process observation and an ordered allocator/free trace, so a
//! leak, double free, wrong cleanup route, or value disagreement cannot cancel
//! against another case.
//!
//! Verified calls are always interpreted from the exact `VerifiedProgram` and
//! compared with Clang `-O0` and `-O2`. Bounds-trap probes are necessarily
//! outside a verified caller's contract. Like the curated trap-ABI test, their
//! native dispatcher deliberately violates a proved guard; the interpreter
//! side renders a separate source with the same concrete bad index, passes it
//! through the full Lean-free front end, and executes its `CheckedProgram`.
//! Those probes compare operational trap classification and observe native
//! no-unwind through the live-allocation hook. They are not evidence about an
//! admitted verified call.

use sable::interp::RtVal;
use sable::llvm::{EmitOptions, emit_verified};
use sable::{Options, load_checked, verify_file_structured};
use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

/// Seven payload bits leave exit status 255 reserved for a non-Boolean native
/// return. The interpreter can never produce that status because every case's
/// checked contract restricts it to zero or one.
const BATCH_SIZE: usize = 7;
const INVALID_CASE_STATUS: u16 = 255;
const UNEXPECTED_DISPATCH_STATUS: i32 = 254;
const OWNERSHIP_ANCHOR: &str = "generated_ownership_anchor";

#[derive(Clone, Copy)]
enum ScalarTy {
    I8,
    U8,
    I16,
    U16,
    I32,
    U32,
    I64,
    U64,
}

impl ScalarTy {
    const ALL: [Self; 8] = [
        Self::I8,
        Self::U8,
        Self::I16,
        Self::U16,
        Self::I32,
        Self::U32,
        Self::I64,
        Self::U64,
    ];

    fn source(self) -> &'static str {
        match self {
            Self::I8 => "i8",
            Self::U8 => "u8",
            Self::I16 => "i16",
            Self::U16 => "u16",
            Self::I32 => "i32",
            Self::U32 => "u32",
            Self::I64 => "i64",
            Self::U64 => "u64",
        }
    }

    fn wide(self) -> Option<&'static str> {
        match self {
            Self::I8 | Self::I16 => Some("i32"),
            Self::U8 | Self::U16 => Some("u32"),
            Self::I32 => Some("i64"),
            Self::U32 => Some("u64"),
            Self::I64 | Self::U64 => None,
        }
    }

    fn signed(self) -> bool {
        matches!(self, Self::I8 | Self::I16 | Self::I32 | Self::I64)
    }
}

#[derive(Clone, Copy)]
enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
}

impl BinOp {
    const ALL: [Self; 5] = [Self::Add, Self::Sub, Self::Mul, Self::Div, Self::Rem];

    fn source(self) -> &'static str {
        match self {
            Self::Add => "+",
            Self::Sub => "-",
            Self::Mul => "*",
            Self::Div => "/",
            Self::Rem => "%",
        }
    }
}

#[derive(Clone, Copy)]
enum Compare {
    Lt,
    Le,
    Eq,
    Ne,
    Ge,
    Gt,
}

impl Compare {
    const ALL: [Self; 6] = [Self::Lt, Self::Le, Self::Eq, Self::Ne, Self::Ge, Self::Gt];

    fn source(self) -> &'static str {
        match self {
            Self::Lt => "<",
            Self::Le => "<=",
            Self::Eq => "==",
            Self::Ne => "!=",
            Self::Ge => ">=",
            Self::Gt => ">",
        }
    }
}

struct ArithmeticCase {
    ty: ScalarTy,
    op: BinOp,
    lhs: i32,
    rhs: i32,
    compare: Compare,
    threshold: i32,
}

struct LoopCase {
    start: i32,
    delta: i32,
    steps: u32,
    compare: Compare,
    threshold: i32,
}

enum Case {
    Arithmetic(ArithmeticCase),
    Loop(LoopCase),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum NativeArray {
    Bool,
    U32,
}

impl NativeArray {
    const ALL: [Self; 2] = [Self::Bool, Self::U32];

    fn source(self) -> &'static str {
        match self {
            Self::Bool => "bool",
            Self::U32 => "u32",
        }
    }

    fn bytes(self, len: u64) -> u64 {
        match self {
            Self::Bool => len,
            Self::U32 => len * 4,
        }
    }

    fn value(self, truth: bool) -> &'static str {
        match (self, truth) {
            (Self::Bool, true) => "true",
            (Self::Bool, false) => "false",
            (Self::U32, true) => "17",
            (Self::U32, false) => "0",
        }
    }

    fn render_condition(self, local: &str) -> String {
        match self {
            Self::Bool => local.to_owned(),
            Self::U32 => format!("{local} > 0"),
        }
    }

    fn render_read(self, array: &str, index: impl std::fmt::Display) -> String {
        format!("{array}[{index}]")
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum BorrowMode {
    Shared,
    Unique,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum NestedExit {
    Fallthrough,
    EarlyReturn,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum MoveForm {
    Declaration,
    ReplaceAndRevive,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum AffineOptionForm {
    Present,
    Taken,
    None,
}

#[derive(Clone, Debug)]
enum OwnershipShape {
    ClassMove {
        form: MoveForm,
        expected_true: bool,
    },
    ArrayBorrow {
        array: NativeArray,
        mode: BorrowMode,
        len: u64,
        initial_truth: bool,
        written_truth: bool,
    },
    NestedScopes {
        array: NativeArray,
        lengths: Vec<u64>,
        exit: NestedExit,
        truth: bool,
    },
    LoopReassign {
        iterations: u64,
        expected_true: bool,
    },
    AffineBoolOption {
        form: AffineOptionForm,
        len: u64,
        truth: bool,
    },
    MutableClassReceiver {
        initial_sign: u64,
    },
}

#[derive(Clone, Debug)]
struct OwnershipCase {
    index: usize,
    shape: OwnershipShape,
}

impl OwnershipCase {
    fn name(&self) -> String {
        format!("generated_owner_case_{:02}", self.index)
    }

    fn expected_result(&self) -> i32 {
        let truth = match &self.shape {
            OwnershipShape::ClassMove { expected_true, .. }
            | OwnershipShape::LoopReassign { expected_true, .. } => *expected_true,
            OwnershipShape::ArrayBorrow {
                mode,
                initial_truth,
                written_truth,
                ..
            } => match mode {
                BorrowMode::Shared => *initial_truth,
                BorrowMode::Unique => *written_truth,
            },
            OwnershipShape::NestedScopes { truth, .. } => *truth,
            OwnershipShape::AffineBoolOption { form, truth, .. } => match form {
                AffineOptionForm::Present | AffineOptionForm::None => true,
                AffineOptionForm::Taken => *truth,
            },
            OwnershipShape::MutableClassReceiver { initial_sign } => *initial_sign == 0,
        };
        i32::from(truth)
    }

    fn expected_runtime_events(&self) -> Vec<RuntimeEvent> {
        if matches!(
            &self.shape,
            OwnershipShape::AffineBoolOption {
                form: AffineOptionForm::None,
                ..
            }
        ) {
            // No allocation means the replacement runtime hook never needs
            // to register its process-exit summary. The empty trace is the
            // observable none-owner cleanup result.
            return Vec::new();
        }
        let mut model = LifetimeModel::default();
        match &self.shape {
            OwnershipShape::ClassMove {
                form: MoveForm::Declaration,
                ..
            } => {
                let owner = model.allocate(4);
                model.free(owner);
            }
            OwnershipShape::ClassMove {
                form: MoveForm::ReplaceAndRevive,
                ..
            } => {
                let original_destination = model.allocate(4);
                let transferred = model.allocate(4);
                model.free(original_destination);
                let revived = model.allocate(4);
                // Reverse declaration cleanup: `moved` owns the transferred
                // value and is declared after the revived destination.
                model.free(transferred);
                model.free(revived);
            }
            OwnershipShape::ArrayBorrow { array, len, .. } => {
                let owner = model.allocate(array.bytes(*len));
                model.free(owner);
            }
            OwnershipShape::NestedScopes { array, lengths, .. } => {
                let owners = lengths
                    .iter()
                    .map(|len| model.allocate(array.bytes(*len)))
                    .collect::<Vec<_>>();
                for owner in owners.into_iter().rev() {
                    model.free(owner);
                }
            }
            OwnershipShape::LoopReassign { iterations, .. } => {
                let mut carried = model.allocate(4);
                for _ in 0..*iterations {
                    let replacement = model.allocate(4);
                    model.free(carried);
                    carried = replacement;
                }
                model.free(carried);
            }
            OwnershipShape::AffineBoolOption { len, .. } => {
                let payload = model.allocate(*len);
                model.free(payload);
            }
            OwnershipShape::MutableClassReceiver { .. } => {
                let magnitude = model.allocate(4);
                model.free(magnitude);
            }
        }
        model.finish()
    }

    fn render(&self, out: &mut String) {
        writeln!(out, "/// post result = 0 ∨ result = 1").unwrap();
        writeln!(out, "fn {}() -> i32 {{", self.name()).unwrap();
        match &self.shape {
            OwnershipShape::ClassMove {
                form: MoveForm::Declaration,
                expected_true,
            } => {
                writeln!(out, "    var source = Nat::filled(11);").unwrap();
                writeln!(out, "    var moved = source;").unwrap();
                writeln!(out, "    u32 observed = generated_nat_first(&moved);").unwrap();
                let comparison = if *expected_true { 11 } else { 12 };
                writeln!(out, "    if (observed == {comparison}) {{ return 1; }}").unwrap();
                writeln!(out, "    return 0;").unwrap();
            }
            OwnershipShape::ClassMove {
                form: MoveForm::ReplaceAndRevive,
                expected_true,
            } => {
                writeln!(out, "    var mut destination = Nat::filled(3);").unwrap();
                writeln!(out, "    var source = Nat::filled(7);").unwrap();
                writeln!(out, "    destination = source;").unwrap();
                writeln!(out, "    var moved = destination;").unwrap();
                writeln!(out, "    destination = Nat::filled(19);").unwrap();
                writeln!(out, "    u32 transferred = generated_nat_first(&moved);").unwrap();
                writeln!(out, "    u32 revived = generated_nat_first(&destination);").unwrap();
                let transferred = if *expected_true { 7 } else { 8 };
                writeln!(
                    out,
                    "    if (transferred == {transferred} && revived == 19) {{ return 1; }}"
                )
                .unwrap();
                writeln!(out, "    return 0;").unwrap();
            }
            OwnershipShape::ArrayBorrow {
                array,
                mode,
                len,
                initial_truth,
                written_truth,
            } => {
                let mutable = if matches!(mode, BorrowMode::Unique) {
                    "mut "
                } else {
                    ""
                };
                writeln!(
                    out,
                    "    {mutable}[{}] values = alloc_array<{}>({len}, {});",
                    array.source(),
                    array.source(),
                    array.value(*initial_truth)
                )
                .unwrap();
                if matches!(mode, BorrowMode::Unique) {
                    writeln!(
                        out,
                        "    generated_{}_write(&mut values, {});",
                        array.source(),
                        array.value(*written_truth)
                    )
                    .unwrap();
                }
                writeln!(
                    out,
                    "    {} observed = generated_{}_read(&values);",
                    array.source(),
                    array.source()
                )
                .unwrap();
                writeln!(
                    out,
                    "    if ({}) {{ return 1; }}",
                    array.render_condition("observed")
                )
                .unwrap();
                writeln!(out, "    return 0;").unwrap();
            }
            OwnershipShape::NestedScopes {
                array,
                lengths,
                exit,
                truth,
            } => {
                if matches!(exit, NestedExit::Fallthrough) {
                    writeln!(out, "    mut i32 observed = 0;").unwrap();
                }
                for (depth, len) in lengths.iter().enumerate() {
                    let indent = "    ".repeat(depth + 1);
                    writeln!(out, "{indent}if (true) {{").unwrap();
                    writeln!(
                        out,
                        "{indent}    [{}] nested_{depth} = alloc_array<{}>({len}, {});",
                        array.source(),
                        array.source(),
                        array.value(*truth)
                    )
                    .unwrap();
                }
                let inner_indent = "    ".repeat(lengths.len() + 1);
                let inner_name = format!("nested_{}", lengths.len() - 1);
                let read = array.render_read(&inner_name, lengths[lengths.len() - 1] - 1);
                let condition = array.render_condition(&read);
                match exit {
                    NestedExit::EarlyReturn => {
                        writeln!(out, "{inner_indent}if ({condition}) {{ return 1; }}").unwrap();
                        writeln!(out, "{inner_indent}return 0;").unwrap();
                    }
                    NestedExit::Fallthrough => {
                        writeln!(out, "{inner_indent}if ({condition}) {{ observed = 1; }}")
                            .unwrap();
                    }
                }
                for depth in (0..lengths.len()).rev() {
                    let indent = "    ".repeat(depth + 1);
                    writeln!(out, "{indent}}}").unwrap();
                }
                match exit {
                    NestedExit::Fallthrough => {
                        writeln!(out, "    return observed;").unwrap();
                    }
                    NestedExit::EarlyReturn => {
                        // Structurally total even though the generated true
                        // guards make the nested return the executed route.
                        writeln!(out, "    return 0;").unwrap();
                    }
                }
            }
            OwnershipShape::LoopReassign {
                iterations,
                expected_true,
            } => {
                writeln!(out, "    var mut carried = Nat::filled(23);").unwrap();
                writeln!(out, "    mut u64 remaining = {iterations};").unwrap();
                writeln!(out, "    /// invariant remaining <= {iterations}").unwrap();
                writeln!(out, "    /// variant remaining").unwrap();
                writeln!(out, "    while (remaining > 0) {{").unwrap();
                writeln!(out, "        var replacement = Nat::filled(23);").unwrap();
                writeln!(out, "        carried = replacement;").unwrap();
                writeln!(out, "        remaining = remaining - 1;").unwrap();
                writeln!(out, "    }}").unwrap();
                writeln!(out, "    u32 observed = generated_nat_first(&carried);").unwrap();
                let comparison = if *expected_true { 23 } else { 24 };
                writeln!(out, "    if (observed == {comparison}) {{ return 1; }}").unwrap();
                writeln!(out, "    return 0;").unwrap();
            }
            OwnershipShape::AffineBoolOption { form, len, truth } => match form {
                AffineOptionForm::Present => {
                    writeln!(
                        out,
                        "    mut option<[bool]> pending = some(alloc_array<bool>({len}, {}));",
                        NativeArray::Bool.value(*truth)
                    )
                    .unwrap();
                    writeln!(out, "    if (pending.is_some) {{ return 1; }}").unwrap();
                    writeln!(out, "    return 0;").unwrap();
                }
                AffineOptionForm::Taken => {
                    writeln!(
                        out,
                        "    mut option<[bool]> pending = some(alloc_array<bool>({len}, {}));",
                        NativeArray::Bool.value(*truth)
                    )
                    .unwrap();
                    writeln!(out, "    mut [bool] values = pending.take;").unwrap();
                    writeln!(out, "    if (pending.is_some) {{ return 0; }}").unwrap();
                    writeln!(out, "    if (values[{}]) {{ return 1; }}", len - 1).unwrap();
                    writeln!(out, "    return 0;").unwrap();
                }
                AffineOptionForm::None => {
                    writeln!(out, "    mut option<[bool]> pending = none;").unwrap();
                    writeln!(out, "    if (pending.is_some) {{ return 0; }}").unwrap();
                    writeln!(out, "    return 1;").unwrap();
                }
            },
            OwnershipShape::MutableClassReceiver { initial_sign } => {
                writeln!(out, "    var magnitude = Nat::filled(29);").unwrap();
                writeln!(
                    out,
                    "    var mut value = Integer::make(magnitude, {initial_sign});"
                )
                .unwrap();
                writeln!(out, "    value.flip_sign();").unwrap();
                writeln!(out, "    u64 observed = generated_integer_sign(&value);").unwrap();
                writeln!(out, "    if (observed == 1) {{ return 1; }}").unwrap();
                writeln!(out, "    return 0;").unwrap();
            }
        }
        writeln!(out, "}}\n").unwrap();
    }
}

#[derive(Clone, Debug)]
struct TrapCase {
    index: usize,
    array: NativeArray,
    len: u64,
    bad_index: u64,
    truth: bool,
}

impl TrapCase {
    fn name(&self) -> String {
        format!("generated_oob_guard_{:02}", self.index)
    }

    fn render(&self, out: &mut String) {
        writeln!(out, "/// pre index = 0").unwrap();
        writeln!(out, "/// post result = 0 ∨ result = 1").unwrap();
        writeln!(out, "fn {}(u64 index) -> i32 {{", self.name()).unwrap();
        writeln!(
            out,
            "    [{}] values = alloc_array<{}>({}, {});",
            self.array.source(),
            self.array.source(),
            self.len,
            self.array.value(self.truth)
        )
        .unwrap();
        let read = self.array.render_read("values", "index");
        writeln!(
            out,
            "    if ({}) {{ return 1; }}",
            self.array.render_condition(&read)
        )
        .unwrap();
        writeln!(out, "    return 0;\n}}\n").unwrap();
    }

    fn render_operational_probe(&self, out: &mut String) {
        writeln!(out, "fn {}() -> i32 {{", self.name()).unwrap();
        writeln!(
            out,
            "    [{}] values = alloc_array<{}>({}, {});",
            self.array.source(),
            self.array.source(),
            self.len,
            self.array.value(self.truth)
        )
        .unwrap();
        let read = self.array.render_read("values", self.bad_index);
        writeln!(
            out,
            "    if ({}) {{ return 1; }}",
            self.array.render_condition(&read)
        )
        .unwrap();
        writeln!(out, "    return 0;\n}}\n").unwrap();
    }

    fn expected_interpreter_trap(&self) -> String {
        format!(
            "index out of bounds: index {}, length {}",
            self.bad_index, self.len
        )
    }

    fn expected_native_trap(&self) -> RuntimeEvent {
        RuntimeEvent::Trap {
            kind: 10,
            type_info: 0,
            lhs: self.bad_index,
            rhs: self.len,
            live: 1,
            allocations: 1,
            frees: 0,
        }
    }
}

#[derive(Clone, Copy, Debug)]
enum RefusedOwnershipShape {
    AffineClassOption,
    DiscardedClassResult,
}

#[derive(Clone, Debug)]
struct RefusedOwnershipCase {
    shape: RefusedOwnershipShape,
}

impl RefusedOwnershipCase {
    fn name(&self) -> &'static str {
        match self.shape {
            RefusedOwnershipShape::AffineClassOption => "generated_refused_affine_class_option",
            RefusedOwnershipShape::DiscardedClassResult => {
                "generated_refused_discarded_class_result"
            }
        }
    }

    fn expected_diagnostic(&self) -> (&'static str, &'static str) {
        match self.shape {
            RefusedOwnershipShape::AffineClassOption => {
                ("backend.affine_option_unsupported", "option<class>")
            }
            RefusedOwnershipShape::DiscardedClassResult => {
                ("backend.class_unsupported", "bind or return")
            }
        }
    }

    fn render(&self, out: &mut String) {
        match self.shape {
            RefusedOwnershipShape::AffineClassOption => {
                writeln!(out, "fn {}() -> i32 {{", self.name()).unwrap();
                writeln!(out, "    mut option<Nat> pending = none;").unwrap();
                writeln!(out, "    if (pending.is_some) {{ return 0; }}").unwrap();
                writeln!(out, "    return 1;\n}}\n").unwrap();
            }
            RefusedOwnershipShape::DiscardedClassResult => {
                writeln!(out, "fn generated_owner_factory() -> Nat {{").unwrap();
                writeln!(out, "    return Nat::filled(37);\n}}\n").unwrap();
                writeln!(out, "fn {}() -> i32 {{", self.name()).unwrap();
                writeln!(out, "    generated_owner_factory();").unwrap();
                writeln!(out, "    return 0;\n}}\n").unwrap();
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum RuntimeEvent {
    Alloc {
        id: u64,
        bytes: u64,
    },
    Free {
        id: u64,
        bytes: u64,
    },
    Summary {
        live: usize,
        allocations: u64,
        frees: u64,
    },
    Trap {
        kind: u32,
        type_info: u32,
        lhs: u64,
        rhs: u64,
        live: usize,
        allocations: u64,
        frees: u64,
    },
}

#[derive(Default)]
struct LifetimeModel {
    next_id: u64,
    live: Vec<(u64, u64)>,
    events: Vec<RuntimeEvent>,
    allocations: u64,
    frees: u64,
}

impl LifetimeModel {
    fn allocate(&mut self, bytes: u64) -> u64 {
        self.next_id += 1;
        let id = self.next_id;
        self.live.push((id, bytes));
        self.allocations += 1;
        self.events.push(RuntimeEvent::Alloc { id, bytes });
        id
    }

    fn free(&mut self, id: u64) {
        let position = self
            .live
            .iter()
            .position(|(candidate, _)| *candidate == id)
            .expect("typed lifetime model frees only live owners");
        let (_, bytes) = self.live.remove(position);
        self.frees += 1;
        self.events.push(RuntimeEvent::Free { id, bytes });
    }

    fn finish(mut self) -> Vec<RuntimeEvent> {
        self.events.push(RuntimeEvent::Summary {
            live: self.live.len(),
            allocations: self.allocations,
            frees: self.frees,
        });
        self.events
    }
}

impl Case {
    fn render(&self, index: usize, out: &mut String) {
        match self {
            Self::Arithmetic(case) => case.render(index, out),
            Self::Loop(case) => case.render(index, out),
        }
    }
}

impl ArithmeticCase {
    fn render(&self, index: usize, out: &mut String) {
        let ty = self.ty.source();
        writeln!(out, "/// post result = 0 ∨ result = 1").unwrap();
        writeln!(out, "fn generated_case_{index:03}() -> i32 {{").unwrap();
        writeln!(out, "    {ty} lhs = {};", self.lhs).unwrap();
        writeln!(out, "    {ty} rhs = {};", self.rhs).unwrap();
        writeln!(out, "    {ty} computed = lhs {} rhs;", self.op.source()).unwrap();
        if let Some(wide) = self.ty.wide() {
            writeln!(out, "    {wide} wide = widen<{wide}>(computed);").unwrap();
            writeln!(out, "    {ty} value = narrow<{ty}>(wide);").unwrap();
        } else {
            writeln!(out, "    {ty} value = computed;").unwrap();
        }
        writeln!(
            out,
            "    if (value {} {}) {{ return 1; }}",
            self.compare.source(),
            self.threshold
        )
        .unwrap();
        writeln!(out, "    return 0;\n}}\n").unwrap();
    }
}

impl LoopCase {
    fn render(&self, index: usize, out: &mut String) {
        writeln!(out, "/// post result = 0 ∨ result = 1").unwrap();
        writeln!(out, "fn generated_case_{index:03}() -> i32 {{").unwrap();
        writeln!(out, "    mut i32 value = {};", self.start).unwrap();
        writeln!(out, "    mut u32 remaining = {};", self.steps).unwrap();
        writeln!(out, "    /// invariant remaining <= {}", self.steps).unwrap();
        writeln!(
            out,
            "    /// invariant value = {} + {} * ({} - remaining)",
            self.start, self.delta, self.steps
        )
        .unwrap();
        writeln!(out, "    /// variant remaining").unwrap();
        writeln!(out, "    while (remaining > 0) {{").unwrap();
        writeln!(out, "        value = value + {};", self.delta).unwrap();
        writeln!(out, "        remaining = remaining - 1;").unwrap();
        writeln!(out, "    }}").unwrap();
        writeln!(out, "    if (remaining == 0) {{").unwrap();
        writeln!(
            out,
            "        if (value {} {}) {{ return 1; }}",
            self.compare.source(),
            self.threshold
        )
        .unwrap();
        writeln!(out, "    }}").unwrap();
        writeln!(out, "    return 0;\n}}\n").unwrap();
    }
}

fn cases() -> Vec<Case> {
    let mut cases = Vec::new();
    for (ty_index, ty) in ScalarTy::ALL.into_iter().enumerate() {
        for (op_index, op) in BinOp::ALL.into_iter().enumerate() {
            for sample in 0..2 {
                let signed = ty.signed();
                let mut lhs = 2 + ((ty_index * 3 + op_index * 5 + sample) % 9) as i32;
                let mut rhs = 1 + ((ty_index * 7 + op_index * 2 + sample * 3) % 5) as i32;
                if signed && (ty_index + op_index + sample) % 2 == 0 {
                    lhs = -lhs;
                }
                if signed && (ty_index + op_index + sample) % 3 == 0 {
                    rhs = -rhs;
                }
                if matches!(op, BinOp::Sub) && !signed && lhs < rhs {
                    std::mem::swap(&mut lhs, &mut rhs);
                }
                let compare = Compare::ALL[(ty_index + op_index + sample) % Compare::ALL.len()];
                let threshold = if signed {
                    ((ty_index + op_index + sample) % 7) as i32 - 3
                } else {
                    ((ty_index + op_index + sample) % 7) as i32
                };
                cases.push(Case::Arithmetic(ArithmeticCase {
                    ty,
                    op,
                    lhs,
                    rhs,
                    compare,
                    threshold,
                }));
            }
        }
    }

    for index in 0..6 {
        cases.push(Case::Loop(LoopCase {
            start: index as i32 - 4,
            delta: 1 + (index % 3) as i32,
            steps: 1 + (index % 4) as u32,
            compare: Compare::ALL[index],
            threshold: index as i32 - 1,
        }));
    }
    cases
}

fn ownership_cases() -> Vec<OwnershipCase> {
    let mut shapes = Vec::new();

    for form in [MoveForm::Declaration, MoveForm::ReplaceAndRevive] {
        for expected_true in [false, true] {
            shapes.push(OwnershipShape::ClassMove {
                form,
                expected_true,
            });
        }
    }

    for array in NativeArray::ALL {
        for mode in [BorrowMode::Shared, BorrowMode::Unique] {
            for truth in [false, true] {
                shapes.push(OwnershipShape::ArrayBorrow {
                    array,
                    mode,
                    len: 2 + shapes.len() as u64 % 4,
                    initial_truth: truth,
                    written_truth: !truth,
                });
            }
        }
    }

    for array in NativeArray::ALL {
        for exit in [NestedExit::Fallthrough, NestedExit::EarlyReturn] {
            for truth in [false, true] {
                let base = 2 + shapes.len() as u64 % 3;
                shapes.push(OwnershipShape::NestedScopes {
                    array,
                    lengths: vec![base, base + 1, base + 2],
                    exit,
                    truth,
                });
            }
        }
    }

    for iterations in [1, 2, 4] {
        for expected_true in [false, true] {
            shapes.push(OwnershipShape::LoopReassign {
                iterations,
                expected_true,
            });
        }
    }

    shapes.push(OwnershipShape::AffineBoolOption {
        form: AffineOptionForm::Present,
        len: 5,
        truth: true,
    });
    for truth in [false, true] {
        shapes.push(OwnershipShape::AffineBoolOption {
            form: AffineOptionForm::Taken,
            len: if truth { 7 } else { 6 },
            truth,
        });
    }
    shapes.push(OwnershipShape::AffineBoolOption {
        form: AffineOptionForm::None,
        len: 0,
        truth: false,
    });

    for initial_sign in [0, 1] {
        shapes.push(OwnershipShape::MutableClassReceiver { initial_sign });
    }

    shapes
        .into_iter()
        .enumerate()
        .map(|(index, shape)| OwnershipCase { index, shape })
        .collect()
}

fn trap_cases() -> Vec<TrapCase> {
    NativeArray::ALL
        .into_iter()
        .enumerate()
        .map(|(index, array)| TrapCase {
            index,
            array,
            len: 2 + index as u64,
            bad_index: 7 + index as u64 * 2,
            truth: index % 2 == 0,
        })
        .collect()
}

fn refused_ownership_cases() -> Vec<RefusedOwnershipCase> {
    vec![
        RefusedOwnershipCase {
            shape: RefusedOwnershipShape::AffineClassOption,
        },
        RefusedOwnershipCase {
            shape: RefusedOwnershipShape::DiscardedClassResult,
        },
    ]
}

fn render_ownership_prelude(out: &mut String) {
    out.push_str(
        "class Nat {\n\
             [u32] limbs;\n\n\
             init filled(u32 value) {\n\
                 self.limbs = alloc_array<u32>(1, value);\n\
             }\n\n\
             deinit {\n\
             }\n\
         }\n\n\
         fn generated_nat_first(&Nat value) -> u32 {\n\
             if (value.limbs.len > 0) {\n\
                 return value.limbs[0];\n\
             }\n\
             return 0;\n\
         }\n\n\
         fn generated_bool_read(&[bool] values) -> bool {\n\
             if (values.len > 0) {\n\
                 return values[0];\n\
             }\n\
             return false;\n\
         }\n\n\
         fn generated_bool_write(&mut [bool] values, bool value) {\n\
             if (values.len > 0) {\n\
                 values[0] = value;\n\
             }\n\
         }\n\n\
         fn generated_u32_read(&[u32] values) -> u32 {\n\
             if (values.len > 0) {\n\
                 return values[0];\n\
             }\n\
             return 0;\n\
         }\n\n\
         fn generated_u32_write(&mut [u32] values, u32 value) {\n\
             if (values.len > 0) {\n\
                 values[0] = value;\n\
             }\n\
         }\n\n",
    );
    out.push_str(
        "class Integer {\n\
             Nat mag;\n\
             u64 neg;\n\n\
             init make(Nat magnitude, u64 sign) {\n\
                 self.mag = magnitude;\n\
                 self.neg = sign;\n\
             }\n\n\
             fn flip_sign(&mut self) {\n\
                 if (self.neg == 1) {\n\
                     self.neg = 0;\n\
                     return;\n\
                 }\n\
                 self.neg = 1;\n\
             }\n\n\
             deinit {\n\
             }\n\
         }\n\n\
         fn generated_integer_sign(&Integer value) -> u64 {\n\
             return value.neg;\n\
         }\n\n",
    );
}

fn render_ownership_anchor(ownership: &[OwnershipCase], traps: &[TrapCase], out: &mut String) {
    writeln!(out, "fn {OWNERSHIP_ANCHOR}() -> i32 {{").unwrap();
    for case in ownership {
        writeln!(out, "    {}();", case.name()).unwrap();
    }
    for case in traps {
        writeln!(out, "    {}(0);", case.name()).unwrap();
    }
    writeln!(out, "    return 0;\n}}\n").unwrap();
}

fn generated_source() -> String {
    let cases = cases();

    let mut source = String::from("// Deterministic generated native-differential subject.\n\n");
    for (index, case) in cases.iter().enumerate() {
        case.render(index, &mut source);
    }

    for (batch_index, chunk) in cases.chunks(BATCH_SIZE).enumerate() {
        let max_status = (1_u16 << chunk.len()) - 1;
        writeln!(
            source,
            "/// post (0 <= result ∧ result <= {max_status}) ∨ result = {INVALID_CASE_STATUS}"
        )
        .unwrap();
        writeln!(source, "fn generated_batch_{batch_index:02}() -> i32 {{").unwrap();
        for offset in 0..chunk.len() {
            let case_index = batch_index * BATCH_SIZE + offset;
            writeln!(
                source,
                "    i32 observed_{case_index:03} = generated_case_{case_index:03}();"
            )
            .unwrap();
        }
        let valid_results = (0..chunk.len())
            .map(|offset| {
                let case_index = batch_index * BATCH_SIZE + offset;
                format!("(observed_{case_index:03} == 0 || observed_{case_index:03} == 1)")
            })
            .collect::<Vec<_>>()
            .join(" && ");
        writeln!(source, "    if ({valid_results}) {{").unwrap();
        writeln!(source, "        mut i32 total = 0;").unwrap();
        for offset in 0..chunk.len() {
            let case_index = batch_index * BATCH_SIZE + offset;
            let weight = 1_u16 << offset;
            writeln!(
                source,
                "        total = total + observed_{case_index:03} * {weight};"
            )
            .unwrap();
        }
        writeln!(source, "        return total;").unwrap();
        writeln!(source, "    }}").unwrap();
        writeln!(source, "    return {INVALID_CASE_STATUS};\n}}\n").unwrap();
    }

    let ownership = ownership_cases();
    let traps = trap_cases();
    let refused = refused_ownership_cases();
    render_ownership_prelude(&mut source);
    for case in &ownership {
        case.render(&mut source);
    }
    for case in &traps {
        case.render(&mut source);
    }
    for case in &refused {
        case.render(&mut source);
    }
    render_ownership_anchor(&ownership, &traps, &mut source);
    source
}

fn generated_operational_trap_source(traps: &[TrapCase]) -> String {
    let mut source = String::from(concat!(
        "// Operational trap oracle: checked for type/ownership/control safety,\n",
        "// but intentionally not submitted for proof because each access is OOB.\n\n",
    ));
    for case in traps {
        case.render_operational_probe(&mut source);
    }
    source
}

fn run_checked_operational_traps(temp: &Path, traps: &[TrapCase]) {
    let source_path = temp.join("generated_operational_traps.sable");
    fs::write(&source_path, generated_operational_trap_source(traps))
        .expect("write generated operational trap oracle");
    let (checked, mods) =
        load_checked(&source_path, &Options::default()).unwrap_or_else(|failures| {
            panic!(
                "generated operational trap oracle failed checking (retained at {}):\n{}",
                source_path.display(),
                failures
                    .iter()
                    .map(|failure| failure.rendered.as_str())
                    .collect::<Vec<_>>()
                    .join("\n")
            )
        });
    for case in traps {
        let name = case.name();
        let trapped = match sable::interp::run_checked_fn(&checked, &mods, &name) {
            Ok(value) => panic!("checked operational trap probe `{name}` returned {value:?}"),
            Err(trapped) => trapped,
        };
        assert!(
            trapped.contains(&case.expected_interpreter_trap()),
            "wrong checked operational trap for `{name}`: {trapped}"
        );
    }
}

#[test]
fn generated_batches_range_check_every_case_before_bit_packing() {
    let source = generated_source();
    let case_count = cases().len();
    let batch_count = case_count.div_ceil(BATCH_SIZE);

    assert_eq!(
        source.matches("    i32 observed_").count(),
        case_count,
        "every generated call result needs its own named observation"
    );
    assert_eq!(
        source.matches(" == 0 || observed_").count(),
        case_count,
        "every generated call result needs an exact zero-or-one guard"
    );
    assert_eq!(
        source.matches("    return 255;").count(),
        batch_count,
        "every batch needs the reserved invalid-value exit"
    );
    assert!(
        (1_u16 << BATCH_SIZE) - 1 < INVALID_CASE_STATUS,
        "the invalid-value exit must not collide with a valid bit vector"
    );

    for case_index in 0..case_count {
        assert!(
            source.contains(&format!(
                "i32 observed_{case_index:03} = generated_case_{case_index:03}();"
            )),
            "case {case_index} is not observed"
        );
        assert!(
            source.contains(&format!(
                "observed_{case_index:03} == 0 || observed_{case_index:03} == 1"
            )),
            "case {case_index} is not range-checked before bit-packing"
        );
        let weight = 1_u16 << (case_index % BATCH_SIZE);
        assert!(
            source.contains(&format!(
                "total = total + observed_{case_index:03} * {weight};"
            )),
            "case {case_index} has no distinct valid-result bit"
        );
    }
}

#[test]
fn generated_ownership_matrix_is_typed_and_individually_observable() {
    let source = generated_source();
    let ownership = ownership_cases();
    let traps = trap_cases();
    let refused = refused_ownership_cases();

    assert_eq!(ownership.len(), 32);
    assert_eq!(traps.len(), 2);
    assert_eq!(refused.len(), 2);

    assert!(ownership.iter().any(|case| matches!(
        &case.shape,
        OwnershipShape::ClassMove {
            form: MoveForm::Declaration,
            ..
        }
    )));
    assert!(ownership.iter().any(|case| matches!(
        &case.shape,
        OwnershipShape::ClassMove {
            form: MoveForm::ReplaceAndRevive,
            ..
        }
    )));
    for array in NativeArray::ALL {
        for mode in [BorrowMode::Shared, BorrowMode::Unique] {
            assert!(ownership.iter().any(|case| matches!(
                &case.shape,
                OwnershipShape::ArrayBorrow {
                    array: candidate,
                    mode: candidate_mode,
                    ..
                } if *candidate == array && *candidate_mode == mode
            )));
        }
        for exit in [NestedExit::Fallthrough, NestedExit::EarlyReturn] {
            assert!(ownership.iter().any(|case| matches!(
                &case.shape,
                OwnershipShape::NestedScopes {
                    array: candidate,
                    exit: candidate_exit,
                    ..
                } if *candidate == array && *candidate_exit == exit
            )));
        }
    }
    assert!(ownership.iter().any(|case| matches!(
        &case.shape,
        OwnershipShape::LoopReassign { iterations: 4, .. }
    )));
    for form in [
        AffineOptionForm::Present,
        AffineOptionForm::Taken,
        AffineOptionForm::None,
    ] {
        assert!(ownership.iter().any(|case| matches!(
            &case.shape,
            OwnershipShape::AffineBoolOption {
                form: candidate, ..
            } if *candidate == form
        )));
    }
    assert!(ownership.iter().any(|case| matches!(
        &case.shape,
        OwnershipShape::MutableClassReceiver { initial_sign: 0 }
    )));
    assert!(ownership.iter().any(|case| matches!(
        &case.shape,
        OwnershipShape::MutableClassReceiver { initial_sign: 1 }
    )));
    assert!(ownership.iter().any(|case| case.expected_result() == 0));
    assert!(ownership.iter().any(|case| case.expected_result() == 1));

    for case in &ownership {
        assert!(source.contains(&format!("fn {}() -> i32", case.name())));
        let events = case.expected_runtime_events();
        assert!(
            events.is_empty()
                || matches!(
                    events.last(),
                    Some(RuntimeEvent::Summary {
                        live: 0,
                        allocations,
                        frees,
                    }) if allocations == frees
                )
        );
    }
    for case in &traps {
        assert!(source.contains(&format!("fn {}(u64 index) -> i32", case.name())));
    }
    for case in &refused {
        assert!(source.contains(&format!("fn {}() -> i32", case.name())));
    }
    assert!(source.contains(&format!("fn {OWNERSHIP_ANCHOR}() -> i32")));
}

#[test]
fn generated_operational_traps_consume_checked_control_carrier() {
    let temp = temp_dir();
    run_checked_operational_traps(&temp, &trap_cases());
    fs::remove_dir_all(&temp).expect("remove generated operational trap directory");
}

#[test]
fn generated_native_programs_match_the_interpreter_at_o0_and_o2() {
    let clang = find_clang().unwrap_or_else(|| {
        panic!(
            "generated LLVM differential requires Clang; set SABLE_CLANG to a working executable"
        )
    });

    let temp = temp_dir();
    let source_path = temp.join("generated_native.sable");
    fs::write(&source_path, generated_source()).expect("write generated Sable subject");

    let (mods, verified) = verify_file_structured(&source_path, &Options::default());
    let verified = verified.unwrap_or_else(|diagnostics| {
        panic!(
            "generated subject failed verification (retained at {}):\n{}",
            source_path.display(),
            diagnostics
                .iter()
                .map(|diagnostic| mods.render(diagnostic))
                .collect::<Vec<_>>()
                .join("\n")
        )
    });

    assert_refused_ownership_lowering(&verified, &mods);

    let case_count = cases().len();
    for batch_index in 0..case_count.div_ceil(BATCH_SIZE) {
        let entry = format!("generated_batch_{batch_index:02}");
        let interpreted = sable::interp::run_verified_fn(&verified, &mods, &entry)
            .unwrap_or_else(|trap| panic!("generated interpreter trapped in `{entry}`: {trap}"));
        let RtVal::Int(expected) = interpreted else {
            panic!("generated batch `{entry}` returned a non-integer value");
        };
        let expected = i32::try_from(expected).expect("generated result fits the process ABI");
        let max_valid_status = (1_i32 << BATCH_SIZE) - 1;
        assert!((0..=max_valid_status).contains(&expected));

        let ir = emit_verified(
            &verified,
            &EmitOptions {
                entry: Some(entry.clone()),
            },
        )
        .unwrap_or_else(|diagnostics| {
            panic!(
                "generated batch `{entry}` failed LLVM lowering:\n{}",
                diagnostics
                    .iter()
                    .map(|diagnostic| mods.render(diagnostic))
                    .collect::<Vec<_>>()
                    .join("\n")
            )
        });
        let ir_path = temp.join(format!("generated_native_batch_{batch_index:02}.ll"));
        fs::write(&ir_path, ir).expect("write generated LLVM IR");

        for optimization in ["-O0", "-O2"] {
            let executable = temp.join(format!(
                "generated-native-batch-{batch_index:02}-{}",
                &optimization[1..]
            ));
            let compile = Command::new(&clang)
                .args([optimization, "-x", "ir"])
                .arg(&ir_path)
                .arg("-o")
                .arg(&executable)
                .output()
                .expect("run clang over generated LLVM IR");
            assert!(
                compile.status.success(),
                "clang {optimization} rejected generated batch `{entry}` (retained at {}):\n{}",
                ir_path.display(),
                String::from_utf8_lossy(&compile.stderr)
            );
            let native = Command::new(&executable)
                .output()
                .expect("run generated native executable");
            assert_eq!(
                native.status.code(),
                Some(expected),
                "generated differential diverged for `{entry}` at {optimization}: interpreter={expected:#010b}, native={}\n{}",
                native.status,
                String::from_utf8_lossy(&native.stderr)
            );
        }
    }

    run_ownership_differential(&clang, &temp, &mods, &verified);

    fs::remove_dir_all(&temp).expect("remove generated differential directory");
}

fn assert_refused_ownership_lowering(
    verified: &sable::VerifiedProgram,
    mods: &sable::modules::ModuleSet,
) {
    for case in refused_ownership_cases() {
        let diagnostics = match emit_verified(
            verified,
            &EmitOptions {
                entry: Some(case.name().to_owned()),
            },
        ) {
            Ok(_) => panic!(
                "generated refused ownership case `{}` unexpectedly entered the native subset",
                case.name()
            ),
            Err(diagnostics) => diagnostics,
        };
        let (expected_name, expected_label) = case.expected_diagnostic();
        assert!(
            diagnostics.iter().any(|diagnostic| {
                diagnostic.name == expected_name && diagnostic.label.contains(expected_label)
            }),
            "wrong fail-closed diagnostic for `{}`:\n{}",
            case.name(),
            diagnostics
                .iter()
                .map(|diagnostic| mods.render(diagnostic))
                .collect::<Vec<_>>()
                .join("\n")
        );
    }
}

fn run_ownership_differential(
    clang: &Path,
    temp: &Path,
    mods: &sable::modules::ModuleSet,
    verified: &sable::VerifiedProgram,
) {
    let ownership = ownership_cases();
    let traps = trap_cases();

    for case in &ownership {
        let name = case.name();
        let interpreted =
            sable::interp::run_verified_fn(verified, mods, &name).unwrap_or_else(|trap| {
                panic!("generated ownership interpreter trapped in `{name}`: {trap}")
            });
        let RtVal::Int(interpreted) = interpreted else {
            panic!("generated ownership case `{name}` returned a non-integer value");
        };
        assert_eq!(
            i32::try_from(interpreted).expect("generated ownership result fits i32"),
            case.expected_result(),
            "typed semantic oracle disagrees with the exact-VerifiedProgram interpreter for `{name}`"
        );
    }

    // A verified caller cannot reach a bounds guard with an invalid index.
    // Build a separate operational oracle through the normal Lean-free front
    // end, so even this deliberately unprovable probe consumes the exact
    // checker-sealed control plan rather than rebuilding one from a raw AST.
    run_checked_operational_traps(temp, &traps);

    let ir = emit_verified(
        verified,
        &EmitOptions {
            entry: Some(OWNERSHIP_ANCHOR.to_owned()),
        },
    )
    .unwrap_or_else(|diagnostics| {
        panic!(
            "generated ownership module failed LLVM lowering:\n{}",
            diagnostics
                .iter()
                .map(|diagnostic| mods.render(diagnostic))
                .collect::<Vec<_>>()
                .join("\n")
        )
    });
    let ir = append_native_dispatcher(strip_emitted_main(ir), &ownership, &traps);
    let ir_path = temp.join("generated_ownership.ll");
    let hooks_path = temp.join("generated_ownership_hooks.c");
    fs::write(&ir_path, ir).expect("write generated ownership LLVM IR");
    fs::write(&hooks_path, OWNERSHIP_RUNTIME_HOOKS)
        .expect("write generated ownership runtime hooks");

    for optimization in ["-O0", "-O2"] {
        let executable = temp.join(format!("generated-ownership-{}", &optimization[1..]));
        let compile = Command::new(clang)
            .args([optimization, "-x", "ir"])
            .arg(&ir_path)
            .args(["-x", "c"])
            .arg(&hooks_path)
            .arg("-o")
            .arg(&executable)
            .output()
            .expect("run clang over generated ownership IR and hooks");
        assert!(
            compile.status.success(),
            "clang {optimization} rejected generated ownership module (retained at {}):\n{}",
            ir_path.display(),
            String::from_utf8_lossy(&compile.stderr)
        );

        for (dispatch, case) in ownership.iter().enumerate() {
            let output = run_dispatch(&executable, dispatch);
            assert_eq!(
                output.status.code(),
                Some(case.expected_result()),
                "generated ownership differential diverged for `{}` at {optimization}: expected {}, native={}\nstdout:\n{}\nstderr:\n{}",
                case.name(),
                case.expected_result(),
                output.status,
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            );
            assert_eq!(
                parse_runtime_events(&output.stderr),
                case.expected_runtime_events(),
                "wrong ownership/cleanup trace for `{}` at {optimization}:\n{}",
                case.name(),
                String::from_utf8_lossy(&output.stderr)
            );
        }

        for (offset, case) in traps.iter().enumerate() {
            let dispatch = ownership.len() + offset;
            let output = run_dispatch(&executable, dispatch);
            assert!(
                !output.status.success(),
                "generated trap hook returned from `{}` at {optimization}; llvm.trap must terminate",
                case.name()
            );
            assert_eq!(
                parse_runtime_events(&output.stderr),
                vec![
                    RuntimeEvent::Alloc {
                        id: 1,
                        bytes: case.array.bytes(case.len),
                    },
                    case.expected_native_trap(),
                ],
                "wrong trap/no-unwind trace for `{}` at {optimization}: status {}\n{}",
                case.name(),
                output.status,
                String::from_utf8_lossy(&output.stderr)
            );
        }
    }
}

fn run_dispatch(executable: &Path, dispatch: usize) -> Output {
    Command::new(executable)
        .args(std::iter::repeat_n("case", dispatch))
        .output()
        .expect("run generated ownership dispatch")
}

fn strip_emitted_main(mut ir: String) -> String {
    let marker = "\ndefine i32 @main() {\n";
    let main = ir
        .rfind(marker)
        .expect("entry-mode LLVM contains the generated C main bridge");
    ir.truncate(main + 1);
    ir
}

fn append_native_dispatcher(
    mut ir: String,
    ownership: &[OwnershipCase],
    traps: &[TrapCase],
) -> String {
    assert!(!ir.contains("define i32 @main("));
    ir.push_str("\ndefine i32 @main(i32 %argc, ptr %argv) {\nentry:\n");
    ir.push_str("  switch i32 %argc, label %unexpected [\n");
    for dispatch in 0..ownership.len() + traps.len() {
        writeln!(ir, "    i32 {}, label %dispatch_{dispatch}", dispatch + 1).unwrap();
    }
    ir.push_str("  ]\n");

    for (dispatch, case) in ownership.iter().enumerate() {
        let symbol = internal_function_symbol(&ir, &case.name());
        writeln!(
            ir,
            "dispatch_{dispatch}:\n  %result_{dispatch} = call i32 @{symbol}()\n  ret i32 %result_{dispatch}"
        )
        .unwrap();
    }
    for (offset, case) in traps.iter().enumerate() {
        let dispatch = ownership.len() + offset;
        let symbol = internal_function_symbol(&ir, &case.name());
        writeln!(
            ir,
            "dispatch_{dispatch}:\n  %result_{dispatch} = call i32 @{symbol}(i64 {})\n  ret i32 %result_{dispatch}",
            case.bad_index
        )
        .unwrap();
    }
    writeln!(
        ir,
        "unexpected:\n  ret i32 {UNEXPECTED_DISPATCH_STATUS}\n}}"
    )
    .unwrap();
    ir
}

fn internal_function_symbol(ir: &str, source_name: &str) -> String {
    let marker = format!("_{}_{}__p_", source_name.len(), source_name);
    let definition = ir
        .lines()
        .find(|line| {
            line.starts_with("define internal ")
                && line.contains("@__sable_v0_f_")
                && line.contains(&marker)
        })
        .unwrap_or_else(|| panic!("missing emitted definition for `{source_name}`"));
    definition
        .split_once('@')
        .and_then(|(_, rest)| rest.split_once('(').map(|(symbol, _)| symbol.to_owned()))
        .expect("internal function definition carries a symbol")
}

fn parse_runtime_events(stderr: &[u8]) -> Vec<RuntimeEvent> {
    String::from_utf8_lossy(stderr)
        .lines()
        .filter_map(|line| {
            let fields = line.split_whitespace().collect::<Vec<_>>();
            match fields.first().copied() {
                Some("SABLE_GEN_ALLOC") => Some(RuntimeEvent::Alloc {
                    id: runtime_field(&fields, "id"),
                    bytes: runtime_field(&fields, "bytes"),
                }),
                Some("SABLE_GEN_FREE") => Some(RuntimeEvent::Free {
                    id: runtime_field(&fields, "id"),
                    bytes: runtime_field(&fields, "bytes"),
                }),
                Some("SABLE_GEN_SUMMARY") => Some(RuntimeEvent::Summary {
                    live: runtime_field::<usize>(&fields, "live"),
                    allocations: runtime_field(&fields, "allocations"),
                    frees: runtime_field(&fields, "frees"),
                }),
                Some("SABLE_GEN_TRAP") => Some(RuntimeEvent::Trap {
                    kind: runtime_field(&fields, "kind"),
                    type_info: runtime_field(&fields, "type_info"),
                    lhs: runtime_field(&fields, "lhs"),
                    rhs: runtime_field(&fields, "rhs"),
                    live: runtime_field::<usize>(&fields, "live"),
                    allocations: runtime_field(&fields, "allocations"),
                    frees: runtime_field(&fields, "frees"),
                }),
                _ => None,
            }
        })
        .collect()
}

fn runtime_field<T>(fields: &[&str], name: &str) -> T
where
    T: std::str::FromStr,
    T::Err: std::fmt::Debug,
{
    fields
        .iter()
        .find_map(|field| field.strip_prefix(&format!("{name}=")))
        .unwrap_or_else(|| panic!("runtime event has no `{name}` field: {fields:?}"))
        .parse()
        .unwrap_or_else(|error| panic!("runtime event `{name}` field is invalid: {error:?}"))
}

const OWNERSHIP_RUNTIME_HOOKS: &str = r#"#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

typedef struct {
    void *storage;
    uint64_t id;
    uint64_t bytes;
} SableGeneratedAllocation;

static SableGeneratedAllocation live_allocations[256];
static size_t live_count = 0;
static uint64_t next_id = 0;
static uint64_t allocation_count = 0;
static uint64_t free_count = 0;
static int summary_registered = 0;

static void generated_summary(void) {
    fprintf(
        stderr,
        "SABLE_GEN_SUMMARY live=%zu allocations=%" PRIu64 " frees=%" PRIu64 "\n",
        live_count,
        allocation_count,
        free_count
    );
    fflush(stderr);
    if (live_count != 0 || allocation_count != free_count) {
        abort();
    }
}

void *__sable_rt_array_alloc_v1(uint64_t bytes) {
    if (!summary_registered) {
        if (atexit(generated_summary) != 0) {
            abort();
        }
        summary_registered = 1;
    }
    if (bytes == 0 || bytes > SIZE_MAX || live_count == 256) {
        abort();
    }
    void *storage = malloc((size_t)bytes);
    if (storage == NULL) {
        abort();
    }
    next_id += 1;
    allocation_count += 1;
    live_allocations[live_count].storage = storage;
    live_allocations[live_count].id = next_id;
    live_allocations[live_count].bytes = bytes;
    live_count += 1;
    fprintf(
        stderr,
        "SABLE_GEN_ALLOC id=%" PRIu64 " bytes=%" PRIu64 "\n",
        next_id,
        bytes
    );
    fflush(stderr);
    return storage;
}

void __sable_rt_array_free_v1(void *storage) {
    for (size_t i = 0; i < live_count; i += 1) {
        if (live_allocations[i].storage == storage) {
            uint64_t id = live_allocations[i].id;
            uint64_t bytes = live_allocations[i].bytes;
            live_count -= 1;
            live_allocations[i] = live_allocations[live_count];
            free_count += 1;
            fprintf(
                stderr,
                "SABLE_GEN_FREE id=%" PRIu64 " bytes=%" PRIu64 "\n",
                id,
                bytes
            );
            fflush(stderr);
            free(storage);
            return;
        }
    }
    fprintf(stderr, "SABLE_GEN_UNKNOWN_FREE\n");
    fflush(stderr);
    abort();
}

void __sable_rt_trap_v1(
    int32_t kind,
    int32_t type_info,
    uint64_t lhs,
    uint64_t rhs
) {
    fprintf(
        stderr,
        "SABLE_GEN_TRAP kind=%" PRId32 " type_info=%" PRIu32
        " lhs=%" PRIu64 " rhs=%" PRIu64 " live=%zu allocations=%" PRIu64
        " frees=%" PRIu64 "\n",
        kind,
        (uint32_t)type_info,
        lhs,
        rhs,
        live_count,
        allocation_count,
        free_count
    );
    fflush(stderr);
}
"#;

fn temp_dir() -> PathBuf {
    static NEXT: AtomicU64 = AtomicU64::new(0);
    let path = std::env::temp_dir().join(format!(
        "sable-llvm-generated-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&path).expect("create generated differential directory");
    path
}

fn find_clang() -> Option<PathBuf> {
    if let Some(path) = std::env::var_os("SABLE_CLANG") {
        let path = PathBuf::from(path);
        return command_works(&path).then_some(path);
    }
    let homebrew = Path::new("/opt/homebrew/opt/llvm/bin/clang");
    if command_works(homebrew) {
        return Some(homebrew.to_path_buf());
    }
    let path = PathBuf::from("clang");
    command_works(&path).then_some(path)
}

fn command_works(path: &Path) -> bool {
    Command::new(path)
        .arg("--version")
        .output()
        .is_ok_and(|output| output.status.success())
}
