//! AST for the M0 program-language subset (see docs/PLAN.md for scope).
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
        }
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
    /// Borrowed array of integers: `&[i32]` (shared) or `&mut [i32]`
    /// (unique, mutable). Parameters only.
    Array(IntTy, Mutability),
    /// `option<u64>` etc. Return types only.
    Option(IntTy),
    /// No return value (procedures like in-place sorts).
    Unit,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mutability {
    Shared,
    Mut,
    /// A test-function local created by an array literal.
    Owned,
}

impl Ty {
    pub fn name(self) -> String {
        match self {
            Ty::Int(t) => t.name().to_string(),
            Ty::Bool => "bool".to_string(),
            Ty::Array(t, Mutability::Shared) => format!("&[{}]", t.name()),
            Ty::Array(t, Mutability::Mut) => format!("&mut [{}]", t.name()),
            Ty::Array(t, Mutability::Owned) => format!("[{}]", t.name()),
            Ty::Class(_) => "class".to_string(),
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
        args: Vec<Expr>,
    },
    /// `a[i]` where `a` names an array parameter.
    Index {
        array: String,
        array_span: Span,
        index: Box<Expr>,
    },
    /// `a.len` where `a` names an array parameter.
    Len { array: String },
    /// `widen<T>(e)` — value-preserving widening; no VC, identity in Lean.
    Widen { target: IntTy, arg: Box<Expr> },
    /// `some(e)` / `none` — return position only in M1.
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
    SelfField { field: String },
    /// `self.f.len` — array-field length (methods only).
    SelfFieldLen { field: String },
    /// `self.f[i]` — array-field element read (methods only).
    SelfFieldIndex {
        field: String,
        index: Box<Expr>,
    },
    /// `Class::init_name(args)` — construction.
    CtorCall {
        class: String,
        class_span: Span,
        init: String,
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
    /// `&a` / `&mut a` call argument — test functions only.
    Borrow {
        array: String,
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
    /// `var x = expr;` — type inferred by the checker (class construction).
    VarDecl {
        name: String,
        name_span: Span,
        init: Expr,
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
}

#[derive(Debug, Clone)]
pub struct Param {
    pub name: String,
    pub ty: Ty,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Fn {
    pub name: String,
    pub name_span: Span,
    pub params: Vec<Param>,
    pub ret: Ty,
    pub pres: Vec<Clause>,
    pub posts: Vec<Clause>,
    /// Termination measure for self-recursive functions.
    pub variant: Option<Clause>,
    pub body: Vec<Stmt>,
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
}

/// A class method: an ordinary `Fn` whose first parameter is `&self` /
/// `&mut self` (recorded here, not in `params`).
#[derive(Debug, Clone)]
pub struct Method {
    pub self_kind: SelfKind,
    pub f: Fn,
}

#[derive(Debug, Clone)]
pub struct ClassDecl {
    pub name: String,
    pub name_span: Span,
    pub fields: Vec<Field>,
    /// Class invariant clauses — interface blocks (design §7).
    pub invariants: Vec<Clause>,
    /// Named constructors (`init with_capacity(...) { ... }`).
    pub inits: Vec<Fn>,
    pub methods: Vec<Method>,
    pub deinit: Option<Vec<Stmt>>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Program {
    pub fns: Vec<Fn>,
    pub classes: Vec<ClassDecl>,
    pub discharges: Vec<Discharge>,
    pub ghosts: Vec<GhostItem>,
    pub defers: Vec<Defer>,
    pub assumes: Vec<Assume>,
}
