//! AST for the program language (see docs/PLAN.md for scope).
//! Types are filled in by the checker (`ty` fields start as None).

use crate::scan::Clause;
use crate::span::Span;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IntTy {
    U8,
    U16,
    U32,
    U64,
    I8,
    I16,
    I32,
    I64,
    /// A type parameter of the enclosing generic declaration (index into
    /// its parameter list). Exists only between parse and
    /// monomorphization; every later stage may assert its absence.
    TParam(u8),
}

/// Compiler-established storage geometry. This carries no byte
/// representation; it is the executable counterpart of `Sable.Layout`
/// (ADR 0032).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StorageLayout {
    pub size: i128,
    pub align: i128,
}

impl IntTy {
    pub fn name(self) -> &'static str {
        match self {
            IntTy::U8 => "u8",
            IntTy::U16 => "u16",
            IntTy::U32 => "u32",
            IntTy::U64 => "u64",
            IntTy::I8 => "i8",
            IntTy::I16 => "i16",
            IntTy::I32 => "i32",
            IntTy::I64 => "i64",
            IntTy::TParam(_) => "<T>",
        }
    }
    pub fn signed(self) -> bool {
        matches!(self, IntTy::I8 | IntTy::I16 | IntTy::I32 | IntTy::I64)
    }
    pub fn bits(self) -> u32 {
        match self {
            IntTy::U8 | IntTy::I8 => 8,
            IntTy::U16 | IntTy::I16 => 16,
            IntTy::U32 | IntTy::I32 => 32,
            IntTy::U64 | IntTy::I64 => 64,
            IntTy::TParam(_) => unreachable!("type parameter after monomorphization"),
        }
    }
    pub fn layout(self) -> StorageLayout {
        let bytes = i128::from(self.bits() / 8);
        StorageLayout {
            size: bytes,
            align: bytes,
        }
    }
    pub fn lean_layout(self) -> String {
        format!("{}.layout", self.name())
    }
    pub fn min(self) -> i128 {
        if self.signed() {
            -(1i128 << (self.bits() - 1))
        } else {
            0
        }
    }
    pub fn max(self) -> i128 {
        if self.signed() {
            (1i128 << (self.bits() - 1)) - 1
        } else {
            (1i128 << self.bits()) - 1
        }
    }
    /// Lean expression for the lower bound (literal 0 for unsigned so
    /// goals read naturally; named constant for signed).
    pub fn lean_min(self) -> String {
        if self.signed() {
            format!("{}.min", self.name())
        } else {
            "0".to_string()
        }
    }
    pub fn lean_max(self) -> String {
        format!("{}.max", self.name())
    }
    pub fn from_name(s: &str) -> Option<IntTy> {
        Some(match s {
            "u8" => IntTy::U8,
            "u16" => IntTy::U16,
            "u32" => IntTy::U32,
            "u64" => IntTy::U64,
            "i8" => IntTy::I8,
            "i16" => IntTy::I16,
            "i32" => IntTy::I32,
            "i64" => IntTy::I64,
            _ => return None,
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Ty {
    Int(IntTy),
    Bool,
    /// A class value (owned local); index into `Program::classes`.
    Class(usize),
    /// A borrow of a class: `&Nat` (shared — ADR 0010) or `&mut Nat`
    /// (unique, mutable through the class's own `&mut self` methods —
    /// ADR 0023). Parameters only.
    ClassRef(usize, Mutability),
    /// Borrowed array of integers: `&[i32]` (shared) or `&mut [i32]`
    /// (unique, mutable). Parameters only.
    Array(IntTy, Mutability),
    /// `option<u64>` etc. Return types only.
    Option(IntTy),
    /// An owned resource: affine authority, erased at runtime, with a
    /// pure view the proof language reads (ADR 0024).
    Res(ResKind),
    /// `raw<u8>` — a raw pointer: provenance plus a byte offset, never an
    /// address. Carries no authority at all; a load or a store needs a
    /// resource borrow alongside it (ADR 0026).
    Raw(IntTy),
    /// `resource &R` / `resource &mut R` — a borrow of that authority.
    ResRef(ResKind, Mutability),
    /// No return value (procedures like in-place sorts).
    Unit,
}

/// The resource types. Compiler-defined for now: a program may not
/// declare one, because it must not be able to fabricate authority by
/// constructing a view-shaped value.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ResKind {
    RawSpan,
    /// One abstract `u64` typed extent. The source spelling is
    /// `PointsTo<u64>`; layout is general proof vocabulary, while the
    /// typed operation surface remains deliberately u64-only (ADRs
    /// 0031–0032).
    PointsToU64,
    /// One open file description: the authority to use a descriptor, and
    /// the position that description is at (ADR 0028).
    OpenFile,
    /// The external world. A foreign operation that touches global state
    /// must receive this explicitly, which is what replaces a free-form
    /// `modifies` clause over the outside.
    PosixWorld,
    /// The unique authority to release one system allocation. Mandatory:
    /// it must reach the compiler-sealed deallocation operation (ADR 0036).
    SystemDealloc,
    /// One allocator-owned aggregate of free byte extents. Its sealed
    /// take/put operations are the only source and sink of `BlockLease`.
    AllocatorState,
    /// Client authority for one allocator block. This refines byte
    /// authority with allocator/key identity (ADR 0037).
    BlockLease,
    /// A leased block in its typed-u64 role. Allocator and key identity
    /// survive beside the ordinary typed-cell view.
    LeasedPointsToU64,
    /// Allocator-internal byte authority. Unlike a client lease, this
    /// role may split/join while maintaining offset-derived keys.
    FreeBlock,
}

/// The sealed transformations of resource authority. These are not
/// library functions: a program may not define one, because each is a
/// rule about who owns what, and the rules are the compiler's to state
/// (ADR 0024).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ResOp {
    /// `split_off(&mut whole, n)` — leaves the first `n` bytes in the
    /// borrowed token and returns authority over the rest.
    SplitOff,
    /// `join(a, b)` — consumes two adjacent spans of one allocation and
    /// returns authority over their concatenation.
    Join,
    /// `open_file(&mut w, fd) -> resource OpenFile` — carve the authority
    /// to use a descriptor out of the world that handed it out. Authority
    /// for a descriptor has to come from *somewhere*, and the world is the
    /// thing that has descriptors (ADR 0028).
    OpenFileOf,
    /// `posix_world(script) -> resource PosixWorld` — a scripted world, for
    /// tests only. This is the one place authority appears from nothing,
    /// and the checker confines it to `test_` functions.
    TestWorld,
    /// Fold one complete raw extent into a fresh allocator aggregate.
    AllocatorCreate,
    /// Unfold a complete allocator aggregate back to its raw root.
    AllocatorDestroy,
    /// Remove one keyed free extent and return it as a client lease.
    AllocatorTake,
    /// Consume a matching client lease and restore its free-map entry.
    AllocatorPut,
    AllocatorTakeFree,
    AllocatorPutFree,
    FreeBlockSplit,
    FreeBlockJoin,
    FreeBlockLease,
    BlockLeaseFree,
}

impl ResOp {
    pub fn from_name(name: &str) -> Option<ResOp> {
        match name {
            "split_off" => Some(ResOp::SplitOff),
            "join" => Some(ResOp::Join),
            "open_file" => Some(ResOp::OpenFileOf),
            "posix_world" => Some(ResOp::TestWorld),
            "allocator_create" => Some(ResOp::AllocatorCreate),
            "allocator_destroy" => Some(ResOp::AllocatorDestroy),
            "allocator_take" => Some(ResOp::AllocatorTake),
            "allocator_put" => Some(ResOp::AllocatorPut),
            "allocator_take_free" => Some(ResOp::AllocatorTakeFree),
            "allocator_put_free" => Some(ResOp::AllocatorPutFree),
            "free_block_split" => Some(ResOp::FreeBlockSplit),
            "free_block_join" => Some(ResOp::FreeBlockJoin),
            "free_block_lease" => Some(ResOp::FreeBlockLease),
            "block_lease_free" => Some(ResOp::BlockLeaseFree),
            _ => None,
        }
    }

    pub fn name(self) -> &'static str {
        match self {
            ResOp::SplitOff => "split_off",
            ResOp::Join => "join",
            ResOp::OpenFileOf => "open_file",
            ResOp::TestWorld => "posix_world",
            ResOp::AllocatorCreate => "allocator_create",
            ResOp::AllocatorDestroy => "allocator_destroy",
            ResOp::AllocatorTake => "allocator_take",
            ResOp::AllocatorPut => "allocator_put",
            ResOp::AllocatorTakeFree => "allocator_take_free",
            ResOp::AllocatorPutFree => "allocator_put_free",
            ResOp::FreeBlockSplit => "free_block_split",
            ResOp::FreeBlockJoin => "free_block_join",
            ResOp::FreeBlockLease => "free_block_lease",
            ResOp::BlockLeaseFree => "block_lease_free",
        }
    }
}

/// The raw machine operations. Each needs a resource borrow alongside its
/// pointer — the pointer says *which* byte, the resource says the caller
/// is allowed to touch it — and each may only be called inside `unsafe`
/// (ADR 0026).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RawOp {
    /// `raw_offset(p, d) -> raw<u8>` — pure pointer arithmetic.
    Offset,
    /// `raw_load8(p, resource &RawSpan m) -> u8`
    Load8,
    /// `raw_store8(p, v, resource &mut RawSpan m)`
    Store8,
    /// `raw_copy_nonoverlapping(sp, dp, n, resource &RawSpan s,
    /// resource &mut RawSpan d)` — the affine tokens are what supply
    /// separation, so there is no nonoverlap premise to discharge.
    Copy,
    /// Convert exactly eight aligned raw bytes into an uninitialized typed
    /// `u64` extent, discarding their former contents.
    IntoCellU64,
    /// Return an uninitialized typed `u64` extent to raw byte authority.
    FromCellU64,
    /// Initialize, copy-read, take, or drop a typed `u64` extent.
    CellInitU64,
    CellReadU64,
    CellTakeU64,
    CellDropU64,
}

impl RawOp {
    pub fn from_name(name: &str) -> Option<RawOp> {
        match name {
            "raw_offset" => Some(RawOp::Offset),
            "raw_load8" => Some(RawOp::Load8),
            "raw_store8" => Some(RawOp::Store8),
            "raw_copy_nonoverlapping" => Some(RawOp::Copy),
            "raw_into_cell_u64" => Some(RawOp::IntoCellU64),
            "raw_from_cell_u64" => Some(RawOp::FromCellU64),
            "raw_cell_init_u64" => Some(RawOp::CellInitU64),
            "raw_cell_read_u64" => Some(RawOp::CellReadU64),
            "raw_cell_take_u64" => Some(RawOp::CellTakeU64),
            "raw_cell_drop_u64" => Some(RawOp::CellDropU64),
            _ => None,
        }
    }

    pub fn name(self) -> &'static str {
        match self {
            RawOp::Offset => "raw_offset",
            RawOp::Load8 => "raw_load8",
            RawOp::Store8 => "raw_store8",
            RawOp::Copy => "raw_copy_nonoverlapping",
            RawOp::IntoCellU64 => "raw_into_cell_u64",
            RawOp::FromCellU64 => "raw_from_cell_u64",
            RawOp::CellInitU64 => "raw_cell_init_u64",
            RawOp::CellReadU64 => "raw_cell_read_u64",
            RawOp::CellTakeU64 => "raw_cell_take_u64",
            RawOp::CellDropU64 => "raw_cell_drop_u64",
        }
    }

    /// Only `raw_offset` is pure; the rest touch memory and are the
    /// reason `unsafe` exists.
    pub fn touches_memory(self) -> bool {
        !matches!(self, RawOp::Offset)
    }

    pub fn arity(self) -> usize {
        match self {
            RawOp::Offset => 2,
            RawOp::Load8 => 2,
            RawOp::Store8 => 3,
            RawOp::Copy => 5,
            RawOp::IntoCellU64 | RawOp::FromCellU64 | RawOp::CellReadU64
            | RawOp::CellTakeU64 | RawOp::CellDropU64 => 2,
            RawOp::CellInitU64 => 3,
        }
    }
}

impl ResKind {
    pub fn from_name(name: &str) -> Option<ResKind> {
        match name {
            "RawSpan" => Some(ResKind::RawSpan),
            "OpenFile" => Some(ResKind::OpenFile),
            "PosixWorld" => Some(ResKind::PosixWorld),
            "SystemDealloc" => Some(ResKind::SystemDealloc),
            "AllocatorState" => Some(ResKind::AllocatorState),
            "BlockLease" => Some(ResKind::BlockLease),
            "FreeBlock" => Some(ResKind::FreeBlock),
            _ => None,
        }
    }

    pub fn name(self) -> &'static str {
        match self {
            ResKind::RawSpan => "RawSpan",
            ResKind::PointsToU64 => "PointsTo<u64>",
            ResKind::OpenFile => "OpenFile",
            ResKind::PosixWorld => "PosixWorld",
            ResKind::SystemDealloc => "SystemDealloc",
            ResKind::AllocatorState => "AllocatorState",
            ResKind::BlockLease => "BlockLease",
            ResKind::LeasedPointsToU64 => "LeasedPointsTo<u64>",
            ResKind::FreeBlock => "FreeBlock",
        }
    }

    /// Authority of this kind may not be abandoned.  Every owned place
    /// carrying it has a travelling obligation until an audited primitive
    /// consumes it. `OpenFile` is the first proving instance and
    /// `SystemDealloc` is the first compiler-sealed instance (ADRs
    /// 0035–0036).
    pub fn must_consume(self) -> bool {
        matches!(
            self,
            ResKind::OpenFile
                | ResKind::SystemDealloc
                | ResKind::AllocatorState
                | ResKind::BlockLease
                | ResKind::LeasedPointsToU64
                | ResKind::FreeBlock
        )
    }

    /// The Lean type of this resource's view.
    pub fn view_ty(self) -> &'static str {
        match self {
            ResKind::RawSpan => "Sable.SpanView",
            ResKind::PointsToU64 => "Sable.PointsToView Int",
            ResKind::OpenFile => "Sable.OpenFileView",
            ResKind::PosixWorld => "Sable.PosixWorldView",
            ResKind::SystemDealloc => "Sable.SystemDeallocView",
            ResKind::AllocatorState => "Sable.AllocatorView",
            ResKind::BlockLease => "Sable.BlockLeaseView",
            ResKind::LeasedPointsToU64 => "Sable.LeasedPointsToU64View",
            ResKind::FreeBlock => "Sable.FreeBlockView",
        }
    }

    /// This mandatory authority may terminate only in a compiler-sealed
    /// operation; an erased extern parameter cannot honestly consume it.
    pub fn sealed_terminal(self) -> bool {
        matches!(
            self,
            ResKind::SystemDealloc
                | ResKind::AllocatorState
                | ResKind::BlockLease
                | ResKind::LeasedPointsToU64
                | ResKind::FreeBlock
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mutability {
    Shared,
    Mut,
    /// A test-function local created by an array literal.
    Owned,
}

impl Ty {
    /// Resources are erased from runtime signatures and layout: authority
    /// is a static notion with no value to pass (ADR 0024).
    pub fn is_resource(self) -> bool {
        matches!(self, Ty::Res(_) | Ty::ResRef(..))
    }

    pub fn name(self) -> String {
        match self {
            Ty::Int(t) => t.name().to_string(),
            Ty::Bool => "bool".to_string(),
            Ty::Array(t, Mutability::Shared) => format!("&[{}]", t.name()),
            Ty::Array(t, Mutability::Mut) => format!("&mut [{}]", t.name()),
            Ty::Array(t, Mutability::Owned) => format!("[{}]", t.name()),
            Ty::Class(_) => "class".to_string(),
            Ty::ClassRef(_, Mutability::Mut) => "&mut class".to_string(),
            Ty::ClassRef(..) => "&class".to_string(),
            Ty::Raw(t) => format!("raw<{}>", t.name()),
            Ty::Res(k) => format!("resource {}", k.name()),
            Ty::ResRef(k, Mutability::Mut) => format!("resource &mut {}", k.name()),
            Ty::ResRef(k, _) => format!("resource &{}", k.name()),
            Ty::Option(t) => format!("option<{}>", t.name()),
            Ty::Unit => "()".to_string(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
    Ne,
    And,
    Or,
}

impl BinOp {
    pub fn symbol(self) -> &'static str {
        match self {
            BinOp::Add => "+",
            BinOp::Sub => "-",
            BinOp::Mul => "*",
            BinOp::Div => "/",
            BinOp::Rem => "%",
            BinOp::Lt => "<",
            BinOp::Le => "<=",
            BinOp::Gt => ">",
            BinOp::Ge => ">=",
            BinOp::Eq => "==",
            BinOp::Ne => "!=",
            BinOp::And => "&&",
            BinOp::Or => "||",
        }
    }
    pub fn is_arith(self) -> bool {
        matches!(
            self,
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem
        )
    }
    pub fn is_comparison(self) -> bool {
        matches!(
            self,
            BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::Eq | BinOp::Ne
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnOp {
    Neg,
    Not,
}

#[derive(Debug, Clone)]
pub enum ExprKind {
    IntLit(i128),
    BoolLit(bool),
    Var(String),
    Unary {
        op: UnOp,
        operand: Box<Expr>,
    },
    Binary {
        op: BinOp,
        op_span: Span,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    Call {
        callee: String,
        callee_span: Span,
        /// Explicit type arguments (`swap<i32>(...)`); consumed by mono.
        type_args: Vec<IntTy>,
        args: Vec<Expr>,
    },
    /// `a[i]` where `a` names an array parameter.
    Index {
        array: String,
        array_span: Span,
        index: Box<Expr>,
    },
    /// `a.len` where `a` names an array parameter.
    Len {
        array: String,
    },
    /// A raw machine operation. Its contract is generated (ADR 0026).
    RawOp {
        op: RawOp,
        op_span: Span,
        args: Vec<Expr>,
    },
    /// A sealed resource transformation: `split_off(&mut s, n)`,
    /// `join(a, b)`. Its contract is generated, not written (ADR 0024).
    ResOp {
        op: ResOp,
        op_span: Span,
        args: Vec<Expr>,
    },
    /// `widen<T>(e)` — value-preserving widening; no VC, identity in Lean.
    Widen {
        target: IntTy,
        arg: Box<Expr>,
    },
    /// `narrow<T>(e)` — conversion to any integer type under a range VC
    /// (`narrow.range`); identity in Lean, trap in `sable test` (ADR 0007).
    Narrow {
        target: IntTy,
        arg: Box<Expr>,
    },
    /// `e.is_some` — option holds a value (ADR 0008; no pattern matching
    /// in the program language, ever).
    IsSome {
        operand: Box<Expr>,
    },
    /// `e.value` — the option's payload, under an `option.some` VC;
    /// junk-on-none in the model (like `Seq.get` off-range), trap in
    /// `sable test`.
    OptValue {
        operand: Box<Expr>,
    },
    /// `some(e)` / `none` — return position only for now.
    SomeE(Box<Expr>),
    NoneE,
    /// `[e1, e2, ...]` — test functions only.
    ArrayLit(Vec<Expr>),
    /// `alloc_array<T>(len, init)` — a fresh owned array (design §7/§10:
    /// allocation failure is a named OOM trap, not a VC).
    AllocArray {
        elem: IntTy,
        len: Box<Expr>,
        init: Box<Expr>,
    },
    /// `self.f` — int/bool field read (methods only).
    SelfField {
        field: String,
    },
    /// `self.f.len` — array-field length (methods only).
    SelfFieldLen {
        field: String,
    },
    /// `self.f[i]` — array-field element read (methods only).
    SelfFieldIndex {
        field: String,
        index: Box<Expr>,
    },
    /// `Class::init_name(args)` / `Class<T>::init_name(args)`.
    CtorCall {
        class: String,
        class_span: Span,
        /// Explicit type arguments (`Vec<i32>::new()`); consumed by mono.
        type_args: Vec<IntTy>,
        init: String,
        args: Vec<Expr>,
    },
    /// `o.f` — int field read on a class-typed name (ADR 0010).
    ClassField {
        obj: String,
        obj_span: Span,
        field: String,
    },
    /// `o.f.len` — array-field length on a class-typed name.
    ClassFieldLen {
        obj: String,
        field: String,
    },
    /// `o.f[i]` — array-field element read on a class-typed name.
    ClassFieldIndex {
        obj: String,
        obj_span: Span,
        field: String,
        index: Box<Expr>,
    },
    /// `K::m(args)` through a trait bound, inside a TEMPLATE body
    /// (ADR 0009): modeled as an opaque call whose posts are the
    /// trait's contracts over the abstract spec functions. Instances
    /// never contain this (mono resolves them to concrete calls).
    TraitCall {
        param: String,
        param_span: Span,
        method: String,
        args: Vec<Expr>,
    },
    /// `recv.method(args)` where recv is a class-typed local.
    MethodCall {
        recv: String,
        recv_span: Span,
        method: String,
        method_span: Span,
        args: Vec<Expr>,
    },
    /// `&a` / `&mut a` call argument, or `&x.f` / `&self.f` — a borrow
    /// of a class-valued field (ADR 0020: borrowing a *place*, not
    /// only a local).
    Borrow {
        array: String,
        /// Some for a field borrow; the base is then a class-typed
        /// name (or `self`).
        field: Option<String>,
        mutable: bool,
    },
}

#[derive(Debug, Clone)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
    /// Filled in by the checker.
    pub ty: Option<Ty>,
}

#[derive(Debug, Clone)]
pub enum Stmt {
    Decl {
        ty: Ty,
        name: String,
        name_span: Span,
        init: Option<Expr>,
        /// Declared `mut` — assignment, stores, and `&mut` borrows are
        /// only legal on mutable locals (ADR 0016).
        mutable: bool,
    },
    Assign {
        name: String,
        name_span: Span,
        value: Expr,
    },
    If {
        cond: Expr,
        then_block: Vec<Stmt>,
        else_block: Option<Vec<Stmt>>,
    },
    Return {
        /// None for `return;` in a procedure.
        value: Option<Expr>,
        span: Span,
    },
    /// A call evaluated for effect: `f(x);` (procedures, test calls).
    ExprStmt(Expr),
    /// `/// assert P` at a statement position: a named obligation at this
    /// program point, then a hypothesis downstream; monitored dynamically
    /// like any other clause.
    Assert(crate::scan::Clause),
    /// `var x = expr;` — type inferred by the checker (class construction).
    VarDecl {
        name: String,
        name_span: Span,
        init: Expr,
        /// Declared `var mut` (ADR 0016).
        mutable: bool,
        /// Filled by the checker.
        ty: Option<Ty>,
    },
    /// `self.f = e;` (methods/inits only).
    FieldAssign {
        field: String,
        field_span: Span,
        value: Expr,
    },
    /// `self.f[i] = e;` on an array field.
    FieldStore {
        field: String,
        field_span: Span,
        index: Expr,
        value: Expr,
    },
    /// `a[i] = v;` on a `&mut [T]` parameter.
    Store {
        array: String,
        array_span: Span,
        index: Expr,
        value: Expr,
    },
    While {
        cond: Expr,
        invariants: Vec<Clause>,
        variant: Option<Clause>,
        /// Span of the `while` keyword (for "missing variant" errors).
        kw_span: Span,
        body: Vec<Stmt>,
    },
    /// `unsafe { ... }` — the block raw operations may be called in. It
    /// is a marker, not a scope: locals declared inside still belong to
    /// the enclosing function (ADR 0026).
    Unsafe {
        kw_span: Span,
        body: Vec<Stmt>,
    },
    /// `unsafe static_alloc(N) as (p, resource m);` — acquire one fresh,
    /// program-lifetime raw root. There is deliberately no deallocation
    /// authority on this rung (ADR 0033).
    StaticAlloc {
        kw_span: Span,
        size: Expr,
        ptr: String,
        ptr_span: Span,
        res: String,
        res_span: Span,
    },
    /// A releasable system root: fresh pointer, full raw authority, and
    /// one mandatory release token (ADR 0036).
    SystemAlloc {
        kw_span: Span,
        size: Expr,
        ptr: String,
        ptr_span: Span,
        res: String,
        res_span: Span,
        release: String,
        release_span: Span,
    },
    /// Release a full system root. Both resources are consumed; the
    /// `SystemDealloc` argument is a compiler-sealed terminal sink.
    SystemDealloc {
        kw_span: Span,
        ptr: Expr,
        res: Expr,
        release: Expr,
    },
    /// `unsafe expose &a as (p, resource m) { ... }` — the bridge from a
    /// safe `[u8]` to raw bytes. The body sees a pointer and a resource
    /// naming the array's storage; at scope exit the array is what the
    /// bytes say (mutable form) or provably unchanged (shared form).
    Expose {
        kw_span: Span,
        /// The exposed array's local name.
        array: String,
        array_span: Span,
        /// `&mut a` exposes for writing; `&a` read-only.
        mutable: bool,
        /// The body's pointer binding.
        ptr: String,
        ptr_span: Span,
        /// The body's resource binding.
        res: String,
        res_span: Span,
        body: Vec<Stmt>,
    },
}

#[derive(Debug, Clone)]
pub struct Param {
    pub name: String,
    pub ty: Ty,
    pub span: Span,
    /// An audited extern promises that this parameter is the terminal sink
    /// for a mandatory resource. Verified Sable functions may not assert
    /// this: their owned parameters inherit the obligation and their bodies
    /// must prove that it reaches such a sink (ADR 0035).
    pub consumes: bool,
}

#[derive(Debug, Clone)]
pub struct Fn {
    /// Exported to importers (`pub fn`, ADR 0019). Methods, inits,
    /// and trait signatures ignore this (class visibility governs).
    pub is_pub: bool,
    /// `extern "C"`: a foreign function with no body. Its contract is
    /// *audited*, not proved — the boundary the build status has to be
    /// honest about (ADR 0027).
    pub extern_info: Option<ExternInfo>,
    pub name: String,
    pub name_span: Span,
    /// Generic type parameters (`fn swap<T>(...)`). Non-empty only
    /// before monomorphization.
    pub type_params: Vec<String>,
    /// Per-parameter trait bound (`<K: Hashable>`), parallel to
    /// `type_params` (ADR 0007).
    pub type_bounds: Vec<Option<String>>,
    /// Concept preconditions on the type parameters (ADR 0009).
    pub requires: Vec<Clause>,
    /// Set by mono on instances of a template-verified generic: the
    /// instance skips its own obligations (the template's theorems
    /// cover them) and owes only the substituted `requires`.
    pub from_template: Option<String>,
    pub params: Vec<Param>,
    pub ret: Ty,
    pub pres: Vec<Clause>,
    pub posts: Vec<Clause>,
    /// Termination measure for self-recursive functions.
    pub variant: Option<Clause>,
    pub body: Vec<Stmt>,
    pub span: Span,
}

/// An audited foreign declaration. The metadata is mandatory: a trusted
/// contract with no recorded reason is an unsourced axiom, and the whole
/// point of the manifest is that a reader can find every one of them
/// (ADR 0027).
#[derive(Debug, Clone)]
pub struct ExternInfo {
    /// The ABI string; `"C"` for now.
    pub abi: String,
    /// A stable identifier for *this version* of the contract. Changing
    /// it invalidates every artifact that trusted the old one.
    pub audit_id: String,
    /// Why this boundary is trusted, in the author's words.
    pub reason: String,
    pub span: Span,
}

/// `/// discharge NAME by <tactic script>` — replaces `sable_auto` as the
/// proof of the named obligation.
#[derive(Debug, Clone)]
pub struct Discharge {
    pub name: String,
    pub script: String,
    pub span: Span,
}

/// A free-floating ghost item: `/// def ...` or `/// theorem ...`,
/// emitted verbatim into the generated Lean (design §6).
#[derive(Debug, Clone)]
pub struct GhostItem {
    /// "def" or "theorem".
    pub keyword: &'static str,
    /// `#[unfold]`: emit `@[simp]` even though the def recurses.
    pub unfold: bool,
    pub text: String,
    pub span: Span,
}

/// `/// defer NAME` — the named obligation becomes a runtime trap
/// instead of a proof (sound: downstream still assumes it, execution
/// halts if it fails). Design §9.
#[derive(Debug, Clone)]
pub struct Defer {
    pub name: String,
    pub span: Span,
}

/// `/// assume #[audit(reason := "...")] NAME` — the named obligation
/// becomes an axiom (UNSOUND; the audit payload is mandatory). Design §9.
#[derive(Debug, Clone)]
pub struct Assume {
    pub name: String,
    pub reason: String,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SelfKind {
    Shared,
    Mut,
}

#[derive(Debug, Clone)]
pub struct Field {
    pub name: String,
    pub ty: Ty,
    pub span: Span,
    /// `#[must_consume]` — this field's authority has to be handed on by
    /// the class's `deinit`, or abandoning it is a diagnostic rather than
    /// a permitted leak (ADR 0029). Only resource fields may carry it: an
    /// ordinary value has nothing to hand on.
    pub must_consume: bool,
}

/// A class method: an ordinary `Fn` whose first parameter is `&self` /
/// `&mut self` (recorded here, not in `params`).
#[derive(Debug, Clone)]
pub struct Method {
    pub self_kind: SelfKind,
    pub f: Fn,
}

/// `/// spec name : sig` inside a trait — a spec-level (Lean) function
/// symbol each impl must provide as a ghost def (ADR 0007).
#[derive(Debug, Clone)]
pub struct TraitSpecFn {
    pub name: String,
    /// The Lean type after the `:` (e.g. `int → int`) — the binder type
    /// for the abstract spec function in template verification.
    pub sig: String,
    pub span: Span,
}

/// `trait Name { /// spec ... /// post ... fn m(Self x) -> T; ... }` —
/// within the trait, `Self` is `IntTy::TParam(0)`.
#[derive(Debug, Clone)]
pub struct TraitDecl {
    /// Exported to importers (`pub trait`, ADR 0019).
    pub is_pub: bool,
    pub name: String,
    pub name_span: Span,
    pub specs: Vec<TraitSpecFn>,
    /// Method signatures (empty bodies) carrying the trait's contracts.
    pub methods: Vec<Fn>,
    pub span: Span,
}

/// `impl Trait for i32 { /// def spec... fn m(...) { ... } }` — bodies
/// only; contracts come from the trait (ADR 0007).
#[derive(Debug, Clone)]
pub struct ImplDecl {
    pub trait_name: String,
    pub trait_span: Span,
    pub for_ty: IntTy,
    pub for_span: Span,
    /// The impl's ghost defs — must map 1:1 onto the trait's spec fns.
    pub ghosts: Vec<GhostItem>,
    pub fns: Vec<Fn>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct ClassDecl {
    /// Exported to importers (`pub class`, ADR 0019).
    pub is_pub: bool,
    pub name: String,
    pub name_span: Span,
    /// Generic type parameters (`class Vec<T>`). Non-empty only before
    /// monomorphization.
    pub type_params: Vec<String>,
    /// Per-parameter trait bound, parallel to `type_params` (ADR 0007).
    pub type_bounds: Vec<Option<String>>,
    /// Set by mono on instances of a template-verified generic class
    /// (ADR 0009): members skip their own obligations.
    pub from_template: Option<String>,
    pub fields: Vec<Field>,
    /// Class invariant clauses — interface blocks (design §7).
    pub invariants: Vec<Clause>,
    /// Named constructors (`init with_capacity(...) { ... }`).
    pub inits: Vec<Fn>,
    pub methods: Vec<Method>,
    pub deinit: Option<Vec<Stmt>>,
    pub span: Span,
}

/// `const u64 NAME = <literal>;` — a named compile-time value
/// (ADR 0016), substituted into program expressions and clause text
/// before any later stage runs.
#[derive(Debug, Clone)]
pub struct ConstDecl {
    /// Exported to importers (`pub const`, ADR 0019).
    pub is_pub: bool,
    pub name: String,
    pub name_span: Span,
    pub ty: IntTy,
    pub value: i128,
    pub span: Span,
}

/// The symbol slot of an `operator` binding declaration (ADR 0012).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OpSym {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    /// `operator cmp = f;` — unlocks all six comparisons via the
    /// −1/0/1 convention (`a < b` ⇒ `f(&a,&b) < 0`, …).
    Cmp,
}

impl OpSym {
    pub fn symbol(self) -> &'static str {
        match self {
            OpSym::Add => "+",
            OpSym::Sub => "-",
            OpSym::Mul => "*",
            OpSym::Div => "/",
            OpSym::Rem => "%",
            OpSym::Cmp => "cmp",
        }
    }
}

/// `use bignum;` / `use bignum::{gcd, Nat};` — imports a module
/// (ADR 0013). v1: everything a module declares is exported; a listed
/// import additionally validates the names exist.
#[derive(Debug, Clone)]
pub struct UseDecl {
    pub module: String,
    /// None = glob (`use m;`); Some = the listed names.
    pub names: Option<Vec<String>>,
    pub span: Span,
}

/// `operator + = add;` — binds an operator to a contracted function for
/// the class its signature names. Pure front-end sugar: after the
/// checker's rewrite, every downstream stage sees the ordinary call.
#[derive(Debug, Clone)]
pub struct OpBind {
    pub op: OpSym,
    pub fn_name: String,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Program {
    pub fns: Vec<Fn>,
    /// Generic templates, preserved by mono for template-level
    /// verification (ADR 0009).
    pub fn_templates: Vec<Fn>,
    pub class_templates: Vec<ClassDecl>,
    pub classes: Vec<ClassDecl>,
    /// Consumed entirely by monomorphization (ADR 0007).
    pub traits: Vec<TraitDecl>,
    pub impls: Vec<ImplDecl>,
    pub discharges: Vec<Discharge>,
    pub ghosts: Vec<GhostItem>,
    pub defers: Vec<Defer>,
    pub assumes: Vec<Assume>,
    /// Operator bindings (ADR 0012), resolved by the checker.
    pub operators: Vec<OpBind>,
    /// Imports (ADR 0013), consumed by the module loader.
    pub uses: Vec<UseDecl>,
    /// Named constants (ADR 0016), consumed by the const pass.
    pub consts: Vec<ConstDecl>,
}
