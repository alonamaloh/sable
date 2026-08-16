//! AST for the program language (see docs/PLAN.md for scope).
//! Types are filled in by the checker (`ty` fields start as None).

use crate::scan::Clause;
use crate::span::Span;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IntTy {
    U8,
    U16,
    U32,
    U64,
    I8,
    I16,
    I32,
    I64,
    /// Legacy integer-expression representation of a type parameter in
    /// `widen<T>` / `narrow<T>` and generic compatibility helpers. Declaration
    /// positions use `Ty::Param` / `Ty::Param`, so a parameter is not
    /// accidentally treated as an integer merely because v1 instances are
    /// currently integer-only.
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

/// A declaration may bind at most this many type parameters. The ceiling is
/// explicit because `IntTy::TParam(u8)` still carries a parameter in the
/// integer-expression positions, and a parser index must never be truncated
/// into it with `as u8`.
pub const MAX_TYPE_PARAMS: usize = u8::MAX as usize + 1;

/// Stable index of a parameter in its enclosing generic declaration.
///
/// This is deliberately distinct from `IntTy::TParam`: neither the recursive
/// generic type tree nor a declaration-position type parameter is
/// intrinsically integer-typed. Construction is checked against the same
/// ceiling as `IntTy::TParam`, which the remaining integer-expression
/// positions still use.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TypeParamId(u32);

impl TypeParamId {
    pub fn new(index: usize) -> Option<TypeParamId> {
        (index < MAX_TYPE_PARAMS).then_some(TypeParamId(index as u32))
    }

    pub const fn from_legacy(index: u8) -> TypeParamId {
        TypeParamId(index as u32)
    }

    pub const fn index(self) -> usize {
        self.0 as usize
    }

    fn legacy_index(self) -> u8 {
        u8::try_from(self.0).expect("TypeParamId construction enforces the u8 parameter ceiling")
    }
}

/// A nominal value type referenced by a recursive generic type.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum NominalKind {
    Record,
    Class,
}

/// A source-level value-type shape carried through generic parsing and
/// monomorphization.
///
/// Call and constructor type-argument sites store this. It is an owned
/// structural representation, wider than the integer arguments instantiation
/// currently accepts. Nominal types are name-based
/// because module-local class indices are not stable until merging and
/// monomorphization have finished.
///
/// `GenericTy::Int(IntTy::TParam(_))` is non-canonical. Use
/// `GenericTy::from_legacy_int`, which normalizes it to `GenericTy::Param`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum GenericTy {
    Int(IntTy),
    Param(TypeParamId),
    Bool,
    Record(String),
    Array(Box<GenericTy>),
    Option(Box<GenericTy>),
    Class {
        name: String,
        args: Box<[GenericTy]>,
    },
}

/// A recursive generic type together with the source range that named it.
/// Spans deliberately do not participate in structural instance identity.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeArg {
    pub ty: GenericTy,
    pub span: Span,
}

impl TypeArg {
    pub fn from_legacy_int(ty: IntTy, span: Span) -> TypeArg {
        TypeArg {
            ty: GenericTy::from_legacy_int(ty),
            span,
        }
    }
}

/// Failures from checked generic-type conversion, substitution, and keying.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GenericTyError {
    /// The shape cannot be represented by the integer-only v1 AST surface.
    NotV1Integer,
    /// A parameter survived where a concrete monomorphization key or integer
    /// was required.
    UnsubstitutedTypeParameter(TypeParamId),
    /// A substitution referred outside the declaration's argument list.
    TypeParameterOutOfBounds {
        parameter: TypeParamId,
        arity: usize,
    },
    /// A caller constructed `Int(TParam(_))` instead of the normalized
    /// `Param(_)` form.
    NonCanonicalLegacyParameter(TypeParamId),
}

/// Opaque, injective encoding of one concrete recursive generic type.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CanonicalTypeKey(String);

impl CanonicalTypeKey {
    pub fn as_str(&self) -> &str {
        &self.0
    }

    pub fn into_string(self) -> String {
        self.0
    }
}

impl std::fmt::Display for CanonicalTypeKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

impl AsRef<str> for CanonicalTypeKey {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl GenericTy {
    /// Lift an existing integer type into the recursive representation,
    /// normalizing the legacy embedded parameter variant.
    pub fn from_legacy_int(ty: IntTy) -> GenericTy {
        match ty {
            IntTy::TParam(index) => GenericTy::Param(TypeParamId::from_legacy(index)),
            concrete => GenericTy::Int(concrete),
        }
    }

    /// Convert back to the current integer-only AST representation. This
    /// admits a parameter because templates still encode one as
    /// `IntTy::TParam`; aggregate and nominal shapes are rejected.
    pub fn try_to_v1_int(&self) -> Result<IntTy, GenericTyError> {
        match self {
            GenericTy::Int(IntTy::TParam(index)) => Err(
                GenericTyError::NonCanonicalLegacyParameter(TypeParamId::from_legacy(*index)),
            ),
            GenericTy::Int(concrete) => Ok(*concrete),
            GenericTy::Param(parameter) => Ok(IntTy::TParam(parameter.legacy_index())),
            _ => Err(GenericTyError::NotV1Integer),
        }
    }

    /// Convert a fully instantiated type argument to an integer type.
    pub fn try_to_concrete_v1_int(&self) -> Result<IntTy, GenericTyError> {
        match self {
            GenericTy::Param(parameter) => {
                Err(GenericTyError::UnsubstitutedTypeParameter(*parameter))
            }
            _ => self.try_to_v1_int(),
        }
    }

    /// Substitute type parameters recursively. The returned tree is owned so
    /// callers cannot accidentally share and mutate an instance key.
    pub fn substitute(&self, args: &[GenericTy]) -> Result<GenericTy, GenericTyError> {
        match self {
            GenericTy::Int(IntTy::TParam(index)) => {
                let parameter = TypeParamId::from_legacy(*index);
                args.get(parameter.index()).cloned().ok_or(
                    GenericTyError::TypeParameterOutOfBounds {
                        parameter,
                        arity: args.len(),
                    },
                )
            }
            GenericTy::Param(parameter) => args.get(parameter.index()).cloned().ok_or(
                GenericTyError::TypeParameterOutOfBounds {
                    parameter: *parameter,
                    arity: args.len(),
                },
            ),
            GenericTy::Int(concrete) => Ok(GenericTy::Int(*concrete)),
            GenericTy::Bool => Ok(GenericTy::Bool),
            GenericTy::Record(name) => Ok(GenericTy::Record(name.clone())),
            GenericTy::Array(element) => Ok(GenericTy::Array(Box::new(element.substitute(args)?))),
            GenericTy::Option(element) => {
                Ok(GenericTy::Option(Box::new(element.substitute(args)?)))
            }
            GenericTy::Class {
                name,
                args: type_args,
            } => Ok(GenericTy::Class {
                name: name.clone(),
                args: type_args
                    .iter()
                    .map(|arg| arg.substitute(args))
                    .collect::<Result<Vec<_>, _>>()?
                    .into_boxed_slice(),
            }),
        }
    }

    /// Whether this tree contains no type parameter, including the legacy
    /// non-canonical `Int(TParam(_))` spelling.
    pub fn is_concrete(&self) -> bool {
        match self {
            GenericTy::Int(IntTy::TParam(_)) | GenericTy::Param(_) => false,
            GenericTy::Int(_) | GenericTy::Bool | GenericTy::Record(_) => true,
            GenericTy::Array(element) | GenericTy::Option(element) => element.is_concrete(),
            GenericTy::Class { args, .. } => args.iter().all(GenericTy::is_concrete),
        }
    }

    /// Structural tree depth, counting an atom as one node. A zero-argument
    /// class also has depth one.
    pub fn structural_depth(&self) -> usize {
        match self {
            GenericTy::Int(_) | GenericTy::Param(_) | GenericTy::Bool | GenericTy::Record(_) => 1,
            GenericTy::Array(element) | GenericTy::Option(element) => {
                1 + element.structural_depth()
            }
            GenericTy::Class { args, .. } => {
                1 + args
                    .iter()
                    .map(GenericTy::structural_depth)
                    .max()
                    .unwrap_or(0)
            }
        }
    }

    /// Visit every nominal reference in deterministic preorder.
    pub fn visit_nominals(&self, mut visit: impl FnMut(NominalKind, &str)) {
        self.visit_nominals_with(&mut visit);
    }

    fn visit_nominals_with(&self, visit: &mut impl FnMut(NominalKind, &str)) {
        match self {
            GenericTy::Record(name) => visit(NominalKind::Record, name),
            GenericTy::Array(element) | GenericTy::Option(element) => {
                element.visit_nominals_with(visit)
            }
            GenericTy::Class { name, args } => {
                visit(NominalKind::Class, name);
                for arg in args.iter() {
                    arg.visit_nominals_with(visit);
                }
            }
            GenericTy::Int(_) | GenericTy::Param(_) | GenericTy::Bool => {}
        }
    }

    /// Produce an injective, length-prefixed key for a concrete type. Source
    /// identifiers are ASCII today, but lengths are byte lengths so the
    /// encoding remains unambiguous for any UTF-8 string.
    pub fn concrete_key(&self) -> Result<CanonicalTypeKey, GenericTyError> {
        let mut encoded = String::new();
        self.encode_concrete_key(&mut encoded)?;
        Ok(CanonicalTypeKey(encoded))
    }

    fn encode_concrete_key(&self, out: &mut String) -> Result<(), GenericTyError> {
        match self {
            GenericTy::Int(IntTy::TParam(index)) => {
                return Err(GenericTyError::NonCanonicalLegacyParameter(
                    TypeParamId::from_legacy(*index),
                ));
            }
            GenericTy::Int(concrete) => {
                out.push('I');
                push_length_prefixed(out, concrete.name());
            }
            GenericTy::Param(parameter) => {
                return Err(GenericTyError::UnsubstitutedTypeParameter(*parameter));
            }
            GenericTy::Bool => out.push('B'),
            GenericTy::Record(name) => {
                out.push('R');
                push_length_prefixed(out, name);
            }
            GenericTy::Array(element) => {
                let child = element.concrete_key()?;
                out.push('A');
                push_length_prefixed(out, child.as_str());
            }
            GenericTy::Option(element) => {
                let child = element.concrete_key()?;
                out.push('O');
                push_length_prefixed(out, child.as_str());
            }
            GenericTy::Class { name, args } => {
                out.push('C');
                push_length_prefixed(out, name);
                out.push_str(&args.len().to_string());
                out.push('_');
                for arg in args.iter() {
                    let key = arg.concrete_key()?;
                    push_length_prefixed(out, key.as_str());
                }
            }
        }
        Ok(())
    }
}

fn push_length_prefixed(out: &mut String, value: &str) {
    out.push_str(&value.len().to_string());
    out.push('_');
    out.push_str(value);
}

/// The language's one type grammar.
///
/// Every checked type is a value of this type: there is no narrower payload
/// representation anywhere in the compiler, so what a container can hold is
/// not a property of the representation. Which shapes a position accepts is
/// stated by `Parser::admits` (ADR 0063) and by one named gate per consuming
/// stage (ADR 0064) — never by what the representation happens to be able to
/// express.
///
/// The container payloads are boxed, so a payload is matched through an
/// accessor (`as_array`, `as_option`) rather than as a nested pattern.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Ty {
    Int(IntTy),
    Bool,
    /// A declaration-position type parameter. This exists only in retained
    /// generic templates; every ordinary declaration is concrete after mono.
    Param(TypeParamId),
    /// A class value (owned local); index into `Program::classes`.
    Class(usize),
    /// A plain, copyable record value with compiler-checked explicit
    /// layout. Records are deliberately distinct from affine classes:
    /// they have no invariant, methods, resources, or destructor (ADR 0054).
    Record(usize),
    /// `[T]` — an owned array. The element is a full type: which elements a
    /// stage will actually execute, prove, or lower is each stage's own named
    /// gate to state, not this constructor's.
    ///
    /// A bare type owns. `&[T]` and `&mut [T]` are `Ty::Borrow` over this.
    Array(Box<Ty>),
    /// `option<T>`. The payload is a full type for the same reason an array
    /// element is, so whether the option owns its present case is read off
    /// the payload (`is_affine`) rather than encoded by the constructor. The
    /// one payload shape that owns and is admitted anywhere is an owned
    /// array; `as_affine_option_payload` is the question every rule that must
    /// route the owning case away from a copy rule asks.
    Option(Box<Ty>),
    /// `option<raw<R>>` for an explicitly laid-out record. This is an
    /// abstract nullable pointer value, not a byte representation.
    OptionRaw(usize),
    /// An owned resource: affine authority, erased at runtime, with a
    /// pure view the proof language reads (ADR 0024).
    Res(ResKind),
    /// `raw<u8>` — a raw pointer: provenance plus a byte offset, never an
    /// address. Carries no authority at all; a load or a store needs a
    /// resource borrow alongside it (ADR 0026).
    ///
    /// This stays split from `RawRecord` rather than becoming
    /// `Raw(Box<Ty>)`: the pointee of a `raw<...>` is a width or a nominal
    /// record and nothing else, and one merged constructor would give
    /// `raw<u8>` the record-field layout that only a record pointer has.
    Raw(IntTy),
    /// A statically tagged pointer to an explicitly laid-out record.
    /// Runtime representation remains provenance plus byte offset.
    RawRecord(usize),
    /// `&T` (shared — ADR 0010) or `&mut T` (unique — ADR 0023): a second
    /// name for storage the caller keeps.
    ///
    /// Binding mode lives here and nowhere else, so a shape and a mode are
    /// never the same constructor and "does this own" is answerable
    /// structurally: `is_affine` is `false` for every borrow whatever its
    /// referent. Which referents may actually be borrowed, and where, is
    /// stated by `Parser::admits` at `TyPos::BorrowParam` and by each stage's
    /// own named gate — not by which referents this constructor can hold.
    ///
    /// `resource &K` is a borrow of `Ty::Res(K)`. It keeps its own syntactic
    /// shape (`TypeShape::Resource`), because the spelling puts the borrow
    /// marker after the keyword; `Ty::name` renders that spelling from the
    /// referent.
    Borrow(Mutability, Box<Ty>),
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
    /// One abstract typed extent containing an explicitly laid-out record.
    PointsToRecord(usize),
    /// One open file description: the authority to use a descriptor, and
    /// the position that description is at (ADR 0028).
    OpenFile,
    /// The external world. A foreign operation that touches global state
    /// must receive this explicitly, which is what replaces a free-form
    /// `modifies` clause over the outside.
    PosixWorld,
    /// Authority for one UART device profile. Device operations mutate its
    /// logical view; the interpreter separately records concrete MMIO events.
    Uart,
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
    /// An internal free block while its two-word size/link header is typed.
    FreeHeader,
    /// An affine aggregate of independently owned typed cells, indexed by a
    /// stable integer key. The parameterized source surface initially admits
    /// only `ResourceMap<u64, PointsTo<u64>>` (ADR 0053).
    ResourceMapPointsToU64,
    /// The record-typed instance needed by the intrusive-list acceptance
    /// test. Keys remain arena-relative `u64` offsets in v1.
    ResourceMapPointsToRecord(usize),
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
    /// `test_uart(script) -> resource Uart` — a scripted device profile,
    /// confined to dynamic tests just like `posix_world`.
    TestUart,
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
    /// Move one initialized in-band header between the allocator aggregate
    /// and a temporary affine handle used by a traversal step.
    AllocatorTakeHeader,
    AllocatorPutHeader,
    /// Policy-bearing header extraction for one sorted traversal step.
    AllocatorStepHeader,
    FreeBlockSplit,
    FreeBlockJoin,
    FreeBlockLease,
    BlockLeaseFree,
    ResourceMapEmpty,
    ResourceMapTake,
    ResourceMapPut,
}

impl ResOp {
    pub fn from_name(name: &str) -> Option<ResOp> {
        match name {
            "split_off" => Some(ResOp::SplitOff),
            "join" => Some(ResOp::Join),
            "open_file" => Some(ResOp::OpenFileOf),
            "posix_world" => Some(ResOp::TestWorld),
            "test_uart" => Some(ResOp::TestUart),
            "allocator_create" => Some(ResOp::AllocatorCreate),
            "allocator_destroy" => Some(ResOp::AllocatorDestroy),
            "allocator_take" => Some(ResOp::AllocatorTake),
            "allocator_put" => Some(ResOp::AllocatorPut),
            "allocator_take_free" => Some(ResOp::AllocatorTakeFree),
            "allocator_put_free" => Some(ResOp::AllocatorPutFree),
            "allocator_take_header" => Some(ResOp::AllocatorTakeHeader),
            "allocator_put_header" => Some(ResOp::AllocatorPutHeader),
            "allocator_step_header" => Some(ResOp::AllocatorStepHeader),
            "free_block_split" => Some(ResOp::FreeBlockSplit),
            "free_block_join" => Some(ResOp::FreeBlockJoin),
            "free_block_lease" => Some(ResOp::FreeBlockLease),
            "block_lease_free" => Some(ResOp::BlockLeaseFree),
            "resource_map_empty" => Some(ResOp::ResourceMapEmpty),
            "resource_map_take" => Some(ResOp::ResourceMapTake),
            "resource_map_put" => Some(ResOp::ResourceMapPut),
            _ => None,
        }
    }

    pub fn name(self) -> &'static str {
        match self {
            ResOp::SplitOff => "split_off",
            ResOp::Join => "join",
            ResOp::OpenFileOf => "open_file",
            ResOp::TestWorld => "posix_world",
            ResOp::TestUart => "test_uart",
            ResOp::AllocatorCreate => "allocator_create",
            ResOp::AllocatorDestroy => "allocator_destroy",
            ResOp::AllocatorTake => "allocator_take",
            ResOp::AllocatorPut => "allocator_put",
            ResOp::AllocatorTakeFree => "allocator_take_free",
            ResOp::AllocatorPutFree => "allocator_put_free",
            ResOp::AllocatorTakeHeader => "allocator_take_header",
            ResOp::AllocatorPutHeader => "allocator_put_header",
            ResOp::AllocatorStepHeader => "allocator_step_header",
            ResOp::FreeBlockSplit => "free_block_split",
            ResOp::FreeBlockJoin => "free_block_join",
            ResOp::FreeBlockLease => "free_block_lease",
            ResOp::BlockLeaseFree => "block_lease_free",
            ResOp::ResourceMapEmpty => "resource_map_empty",
            ResOp::ResourceMapTake => "resource_map_take",
            ResOp::ResourceMapPut => "resource_map_put",
        }
    }
}

/// Profile-mediated device operations. These are neither authority
/// transformations nor ordinary raw-memory operations: they produce ordered
/// MMIO observations against a concrete platform profile.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DeviceOp {
    UartStatus,
    UartWrite,
}

impl DeviceOp {
    pub fn from_name(name: &str) -> Option<DeviceOp> {
        match name {
            "uart_status" => Some(DeviceOp::UartStatus),
            "uart_write" => Some(DeviceOp::UartWrite),
            _ => None,
        }
    }

    pub fn name(self) -> &'static str {
        match self {
            DeviceOp::UartStatus => "uart_status",
            DeviceOp::UartWrite => "uart_write",
        }
    }

    pub fn arity(self) -> usize {
        match self {
            DeviceOp::UartStatus => 1,
            DeviceOp::UartWrite => 2,
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
    /// Record-typed counterparts. The record index is the static type tag;
    /// none of these operations grants a byte representation (ADR 0054).
    IntoCellRecord(usize),
    FromCellRecord(usize),
    CellInitRecord(usize),
    CellReadRecord(usize),
    CellTakeRecord(usize),
    CellDropRecord(usize),
    /// Pure retagging from `raw<u8>` to `raw<R>` and pure observation of
    /// the arena-relative offset. Neither operation carries authority.
    CastRecord(usize),
    PointerOffsetRecord(usize),
    /// Convert the first two words of a FreeBlock to/from an in-band header.
    IntoFreeHeader,
    FromFreeHeader,
    /// Initialize, inspect, or clear both typed header fields.
    HeaderInit,
    HeaderSize,
    HeaderNext,
    HeaderClear,
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
            "raw_into_free_header" => Some(RawOp::IntoFreeHeader),
            "raw_from_free_header" => Some(RawOp::FromFreeHeader),
            "raw_header_init" => Some(RawOp::HeaderInit),
            "raw_header_size" => Some(RawOp::HeaderSize),
            "raw_header_next" => Some(RawOp::HeaderNext),
            "raw_header_clear" => Some(RawOp::HeaderClear),
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
            RawOp::IntoCellRecord(_) => "raw_into_cell",
            RawOp::FromCellRecord(_) => "raw_from_cell",
            RawOp::CellInitRecord(_) => "raw_cell_init",
            RawOp::CellReadRecord(_) => "raw_cell_read",
            RawOp::CellTakeRecord(_) => "raw_cell_take",
            RawOp::CellDropRecord(_) => "raw_cell_drop",
            RawOp::CastRecord(_) => "raw_cast",
            RawOp::PointerOffsetRecord(_) => "raw_pointer_offset",
            RawOp::IntoFreeHeader => "raw_into_free_header",
            RawOp::FromFreeHeader => "raw_from_free_header",
            RawOp::HeaderInit => "raw_header_init",
            RawOp::HeaderSize => "raw_header_size",
            RawOp::HeaderNext => "raw_header_next",
            RawOp::HeaderClear => "raw_header_clear",
        }
    }

    /// Only `raw_offset` is pure; the rest touch memory and are the
    /// reason `unsafe` exists.
    pub fn touches_memory(self) -> bool {
        !matches!(
            self,
            RawOp::Offset | RawOp::CastRecord(_) | RawOp::PointerOffsetRecord(_)
        )
    }

    pub fn arity(self) -> usize {
        match self {
            RawOp::Offset => 2,
            RawOp::Load8 => 2,
            RawOp::Store8 => 3,
            RawOp::Copy => 5,
            RawOp::IntoCellU64
            | RawOp::FromCellU64
            | RawOp::CellReadU64
            | RawOp::CellTakeU64
            | RawOp::CellDropU64
            | RawOp::IntoCellRecord(_)
            | RawOp::FromCellRecord(_)
            | RawOp::CellReadRecord(_)
            | RawOp::CellTakeRecord(_)
            | RawOp::CellDropRecord(_)
            | RawOp::IntoFreeHeader
            | RawOp::FromFreeHeader
            | RawOp::HeaderSize
            | RawOp::HeaderNext
            | RawOp::HeaderClear => 2,
            RawOp::CellInitU64 | RawOp::CellInitRecord(_) => 3,
            RawOp::CastRecord(_) | RawOp::PointerOffsetRecord(_) => 1,
            RawOp::HeaderInit => 4,
        }
    }
}

impl ResKind {
    pub fn from_name(name: &str) -> Option<ResKind> {
        match name {
            "RawSpan" => Some(ResKind::RawSpan),
            "OpenFile" => Some(ResKind::OpenFile),
            "PosixWorld" => Some(ResKind::PosixWorld),
            "Uart" => Some(ResKind::Uart),
            "SystemDealloc" => Some(ResKind::SystemDealloc),
            "AllocatorState" => Some(ResKind::AllocatorState),
            "BlockLease" => Some(ResKind::BlockLease),
            "FreeBlock" => Some(ResKind::FreeBlock),
            "FreeHeader" => Some(ResKind::FreeHeader),
            _ => None,
        }
    }

    pub fn name(self) -> &'static str {
        match self {
            ResKind::RawSpan => "RawSpan",
            ResKind::PointsToU64 => "PointsTo<u64>",
            ResKind::PointsToRecord(_) => "PointsTo<record>",
            ResKind::OpenFile => "OpenFile",
            ResKind::PosixWorld => "PosixWorld",
            ResKind::Uart => "Uart",
            ResKind::SystemDealloc => "SystemDealloc",
            ResKind::AllocatorState => "AllocatorState",
            ResKind::BlockLease => "BlockLease",
            ResKind::LeasedPointsToU64 => "LeasedPointsTo<u64>",
            ResKind::FreeBlock => "FreeBlock",
            ResKind::FreeHeader => "FreeHeader",
            ResKind::ResourceMapPointsToU64 => "ResourceMap<u64, PointsTo<u64>>",
            ResKind::ResourceMapPointsToRecord(_) => "ResourceMap<u64, PointsTo<record>>",
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
                | ResKind::FreeHeader
        )
    }

    /// The Lean type of this resource's view.
    pub fn view_ty(self) -> &'static str {
        match self {
            ResKind::RawSpan => "Sable.SpanView",
            ResKind::PointsToU64 => "Sable.PointsToView Int",
            ResKind::PointsToRecord(_) => {
                unreachable!("record resource views need the program record table")
            }
            ResKind::OpenFile => "Sable.OpenFileView",
            ResKind::PosixWorld => "Sable.PosixWorldView",
            ResKind::Uart => "Sable.UartView",
            ResKind::SystemDealloc => "Sable.SystemDeallocView",
            ResKind::AllocatorState => "Sable.AllocatorView",
            ResKind::BlockLease => "Sable.BlockLeaseView",
            ResKind::LeasedPointsToU64 => "Sable.LeasedPointsToU64View",
            ResKind::FreeBlock => "Sable.FreeBlockView",
            ResKind::FreeHeader => "Sable.FreeHeaderView",
            ResKind::ResourceMapPointsToU64 => "Sable.ResourceMapView Int (Sable.PointsToView Int)",
            ResKind::ResourceMapPointsToRecord(_) => {
                unreachable!("record resource-map views need the program record table")
            }
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
                | ResKind::FreeHeader
        )
    }

    /// Resource views whose erased authority may cross the audited extern
    /// boundary. This is deliberately a whitelist: adding a resource kind
    /// does not silently grant it foreign-call semantics.
    pub fn extern_abi_allowed(self) -> bool {
        matches!(
            self,
            ResKind::RawSpan | ResKind::OpenFile | ResKind::PosixWorld
        )
    }
}

/// How much a borrow may do through the storage it names.
///
/// This is a property of a borrow and of nothing else: there is no "owned"
/// mutability, because owning is the absence of a borrow. Ask
/// [`Ty::binding_mode`] for the three-way question.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Mutability {
    Shared,
    Mut,
}

/// How a type binds the storage it names: outright, or through a borrow.
///
/// Derived from the shape — `Ty::Borrow` carries the two borrowed cases and
/// every other constructor owns — so it is a *question* about a type, never a
/// field of one. A rule that must give owned, shared, and unique three
/// different answers matches on this; a rule that only asks "does this own"
/// asks [`Ty::is_affine`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BindingMode {
    Owned,
    Shared,
    Mut,
}

impl BindingMode {
    /// The type `referent` has when it is bound this way.
    pub fn bind(self, referent: Ty) -> Ty {
        match self {
            BindingMode::Owned => referent,
            BindingMode::Shared => Ty::borrow(Mutability::Shared, referent),
            BindingMode::Mut => Ty::borrow(Mutability::Mut, referent),
        }
    }

    /// The three modes, for a battery that must cover all of them.
    pub fn all() -> [BindingMode; 3] {
        [BindingMode::Owned, BindingMode::Shared, BindingMode::Mut]
    }
}

impl Ty {
    /// `[element]` — an owned array.
    pub fn array(element: Ty) -> Ty {
        Ty::Array(Box::new(element))
    }

    /// `&referent` / `&mut referent`.
    pub fn borrow(mutability: Mutability, referent: Ty) -> Ty {
        Ty::Borrow(mutability, Box::new(referent))
    }

    /// `&[element]` / `&mut [element]`.
    pub fn array_ref(element: Ty, mutability: Mutability) -> Ty {
        Ty::borrow(mutability, Ty::array(element))
    }

    /// A copyable `option<payload>`.
    pub fn option(payload: Ty) -> Ty {
        Ty::Option(Box::new(payload))
    }

    /// An owning `option<[element]>`: an option over an owned array.
    pub fn affine_array_option(element: Ty) -> Ty {
        Ty::option(Ty::array(element))
    }

    /// What a borrow names, or the type itself when it owns.
    ///
    /// One level only: `&&[T]` is a borrow whose referent is a borrow, and
    /// this returns the inner borrow rather than the array.
    ///
    /// Use it where the binding mode is asked *separately* — a rule that
    /// looks through a borrow without also asking [`Ty::binding_mode`] is a
    /// rule that treats a borrow as its referent, which is how an owner is
    /// duplicated.
    pub fn referent(&self) -> &Ty {
        match self {
            Ty::Borrow(_, referent) => referent,
            owned => owned,
        }
    }

    /// How this type binds its storage.
    pub fn binding_mode(&self) -> BindingMode {
        match self {
            Ty::Borrow(Mutability::Shared, _) => BindingMode::Shared,
            Ty::Borrow(Mutability::Mut, _) => BindingMode::Mut,
            _ => BindingMode::Owned,
        }
    }

    /// What a borrow names, and how much it may do through it.
    pub fn as_borrow(&self) -> Option<(Mutability, &Ty)> {
        match self {
            Ty::Borrow(mutability, referent) => Some((*mutability, referent)),
            _ => None,
        }
    }

    /// What a *unique* borrow `&mut T` names.
    ///
    /// This is the one question the `old` snapshots, the loop havoc, and the
    /// call-site havoc all ask: a unique borrow is the only type through which
    /// a callee can change storage its caller still names.
    pub fn as_unique_borrow(&self) -> Option<&Ty> {
        match self {
            Ty::Borrow(Mutability::Mut, referent) => Some(referent),
            _ => None,
        }
    }

    /// Whether this is a unique borrow `&mut T`.
    pub fn is_unique_borrow(&self) -> bool {
        self.as_unique_borrow().is_some()
    }

    /// The element type and binding mode of an array, owned or borrowed.
    ///
    /// Container payloads are read through accessors rather than nested
    /// patterns because they are boxed. A caller that wants an exact payload
    /// compares the result: `ty.as_array() == Some((&Ty::Bool, ...))`.
    pub fn as_array(&self) -> Option<(&Ty, BindingMode)> {
        match self.referent() {
            Ty::Array(element) => Some((element, self.binding_mode())),
            _ => None,
        }
    }

    /// The element type of an owned array, ignoring borrowed ones.
    ///
    /// Strict: `&[T]` is not an owned array, and this is what keeps the
    /// owning-option family (`as_affine_option_payload`) and the runtime's
    /// owned-storage cleanup from ever naming a borrow.
    pub fn as_owned_array(&self) -> Option<&Ty> {
        match self {
            Ty::Array(element) => Some(element),
            _ => None,
        }
    }

    /// The element type and mutability of a *borrowed* array `&[T]`/`&mut [T]`.
    pub fn as_array_borrow(&self) -> Option<(&Ty, Mutability)> {
        match self {
            Ty::Borrow(mutability, referent) => referent
                .as_owned_array()
                .map(|element| (element, *mutability)),
            _ => None,
        }
    }

    /// The class a class value or a borrow of one names.
    pub fn class_index(&self) -> Option<usize> {
        match self.referent() {
            Ty::Class(class) => Some(*class),
            _ => None,
        }
    }

    /// The class a class borrow `&C`/`&mut C` names, and its mutability.
    pub fn as_class_borrow(&self) -> Option<(usize, Mutability)> {
        match self {
            Ty::Borrow(mutability, referent) => match **referent {
                Ty::Class(class) => Some((class, *mutability)),
                _ => None,
            },
            _ => None,
        }
    }

    /// The resource kind an owned resource or a borrow of one names.
    pub fn res_kind(&self) -> Option<ResKind> {
        match self.referent() {
            Ty::Res(kind) => Some(*kind),
            _ => None,
        }
    }

    /// The resource kind a resource borrow names, and its mutability.
    pub fn as_res_borrow(&self) -> Option<(ResKind, Mutability)> {
        match self {
            Ty::Borrow(mutability, referent) => match **referent {
                Ty::Res(kind) => Some((kind, *mutability)),
                _ => None,
            },
            _ => None,
        }
    }

    /// The payload of an option, whether or not that payload owns.
    pub fn as_option(&self) -> Option<&Ty> {
        match self {
            Ty::Option(payload) => Some(payload),
            _ => None,
        }
    }

    /// The payload of an option whose present case owns storage — the whole
    /// payload type, not its element.
    ///
    /// This is the single question every rule asks when it has to route the
    /// owning case away from a rule that would copy it. It is deliberately
    /// narrower than `self.as_option().is_some_and(Ty::is_affine)`:
    /// `option<class>` has an owning payload too, and it belongs to the
    /// copyable family's gates, which refuse it by their own name
    /// (`type.option_payload_unsupported`). The owning family is the shapes
    /// the ownership rules — move, take, join, destruction — are written for,
    /// and that is an option over an owned array.
    ///
    /// A gate, not a traversal: one level, no recursion.
    pub fn as_affine_option_payload(&self) -> Option<&Ty> {
        match self {
            Ty::Option(payload) if payload.as_owned_array().is_some() => Some(payload),
            _ => None,
        }
    }

    /// Whether this option's present case owns storage.
    pub fn is_affine_option(&self) -> bool {
        self.as_affine_option_payload().is_some()
    }

    /// Whether this is an array of exactly `element`, in any binding mode.
    ///
    /// A payload is compared rather than pattern-matched because it is boxed,
    /// and an exact comparison is what a stage allow-list wants: `[bool]` is
    /// admitted somewhere `[u64]` is not.
    pub fn is_array_of(&self, element: &Ty) -> bool {
        matches!(self.as_array(), Some((found, _)) if found == element)
    }

    /// Whether this is an owned array of exactly `element`.
    pub fn is_owned_array_of(&self, element: &Ty) -> bool {
        matches!(self.as_owned_array(), Some(found) if found == element)
    }

    /// A Boolean array in any binding mode.
    ///
    /// Borrow-transparent, because it answers representation questions: the
    /// descriptor an owner and a borrow both carry, and the element bytes
    /// both address.
    pub fn is_bool_array(&self) -> bool {
        self.is_array_of(&Ty::Bool)
    }

    /// A Boolean array whose storage this scope owns and must free.
    ///
    /// Strict about the binding mode, because it answers ownership questions:
    /// which declarations allocate, which enter the cleanup registry, and
    /// which call the free hook. `&[bool]` and `&mut [bool]` are deliberately
    /// not owned Boolean arrays: they name a sequence their caller owns and
    /// transport exactly as `&[T]` does.
    pub fn is_owned_bool_array(&self) -> bool {
        self.is_owned_array_of(&Ty::Bool)
    }

    /// Values that can be transferred but not duplicated.
    ///
    /// Ownership is a property of the shape, read off the shape rather than
    /// off a constructor kept for the purpose: an option owns exactly when
    /// its payload does, and a borrow never owns its referent (ADRs 0010,
    /// 0023).
    ///
    /// `Param` is copyable because the type-argument domain is concrete
    /// integers (ADR 0009). `type_arguments_are_copyable` pins that coupling,
    /// so widening the domain fails a test rather than silently classifying
    /// an owner as copyable.
    pub fn is_affine(&self) -> bool {
        match self {
            Ty::Class(_) | Ty::Res(_) | Ty::Array(_) => true,
            // An option owns exactly when its present case does.
            Ty::Option(payload) => payload.is_affine(),
            // Terminal, and deliberately *not* `referent.is_affine()`. A
            // borrow is a second name for storage someone else owns, so it
            // owns nothing however affine its referent is. Recursing here
            // would make `&mut [T]` affine, which would move the borrow's
            // place into the moved set and hand the runtime's owned-storage
            // cleanup the caller's buffer.
            Ty::Borrow(..) => false,
            Ty::Int(_)
            | Ty::Bool
            | Ty::Param(_)
            | Ty::Record(_)
            | Ty::OptionRaw(_)
            | Ty::Raw(_)
            | Ty::RawRecord(_)
            | Ty::Unit => false,
        }
    }

    /// May a value of this type occupy a record field, and with what
    /// geometry.
    ///
    /// A gate: an allow-list, never recursive. A record field states raw-cell
    /// geometry, so a type has a field form only if it has a chosen width and
    /// a copy rule. `option<raw<R>>` is a nullable pointer with both;
    /// `option<u64>` is a tag plus a payload, which is a representation
    /// decision the language has not made. `raw<u8>` is deliberately absent:
    /// a pointee is a width or a nominal record, and only the record pointer
    /// has a field form.
    pub fn storage_layout(&self) -> Option<StorageLayout> {
        match self {
            Ty::Int(width) if !matches!(width, IntTy::TParam(_)) => Some(width.layout()),
            Ty::RawRecord(_) | Ty::OptionRaw(_) => Some(StorageLayout { size: 8, align: 8 }),
            _ => None,
        }
    }

    /// Resources are erased from runtime signatures and layout: authority
    /// is a static notion with no value to pass (ADR 0024).
    pub fn is_resource(&self) -> bool {
        matches!(self.referent(), Ty::Res(_))
    }

    /// Whether this type contains no type parameter, including the
    /// non-canonical `Int(TParam(_))` spelling.
    ///
    /// A traversal: it recurses into every payload, and the match is
    /// exhaustive with no wildcard so a new constructor is a compile error
    /// rather than a shape silently reported concrete.
    pub fn is_concrete(&self) -> bool {
        match self {
            Ty::Int(IntTy::TParam(_)) | Ty::Param(_) => false,
            Ty::Raw(IntTy::TParam(_)) => false,
            Ty::Array(element) => element.is_concrete(),
            Ty::Option(payload) => payload.is_concrete(),
            Ty::Borrow(_, referent) => referent.is_concrete(),
            Ty::Int(_)
            | Ty::Bool
            | Ty::Class(_)
            | Ty::Record(_)
            | Ty::OptionRaw(_)
            | Ty::Res(_)
            | Ty::Raw(_)
            | Ty::RawRecord(_)
            | Ty::Unit => true,
        }
    }

    /// How many constructors deep this type is.
    ///
    /// The parser bounds a *spelled* type, but substitution can multiply
    /// depth: a template parameter under two containers becomes the argument
    /// under two containers. Since `name`, `is_concrete`, and every traversal
    /// recurse over this tree, the bound has to hold on the substituted type
    /// too, not only on the written one.
    pub fn structural_depth(&self) -> usize {
        1 + match self {
            Ty::Array(element) => element.structural_depth(),
            Ty::Option(payload) => payload.structural_depth(),
            Ty::Borrow(_, referent) => referent.structural_depth(),
            Ty::Int(_)
            | Ty::Bool
            | Ty::Param(_)
            | Ty::Class(_)
            | Ty::Record(_)
            | Ty::OptionRaw(_)
            | Ty::Res(_)
            | Ty::Raw(_)
            | Ty::RawRecord(_)
            | Ty::Unit => 0,
        }
    }

    /// Return the integer model for concrete integer values and retained
    /// ADR 0009 template parameters. Ordinary post-mono declarations never
    /// contain `Ty::Param`; this helper keeps template checking explicit.
    pub fn int_model(&self) -> Option<IntTy> {
        match self {
            Ty::Int(integer) if !matches!(integer, IntTy::TParam(_)) => Some(*integer),
            Ty::Param(parameter) => Some(IntTy::TParam(parameter.legacy_index())),
            _ => None,
        }
    }

    pub fn name(&self) -> String {
        match self {
            Ty::Int(t) => t.name().to_string(),
            Ty::Bool => "bool".to_string(),
            Ty::Param(parameter) => format!("<T{}>", parameter.index()),
            Ty::Array(t) => format!("[{}]", t.name()),
            Ty::Class(_) => "class".to_string(),
            Ty::Record(_) => "record".to_string(),
            Ty::Raw(t) => format!("raw<{}>", t.name()),
            Ty::RawRecord(_) => "raw<record>".to_string(),
            Ty::Res(k) => format!("resource {}", k.name()),
            Ty::Borrow(mutability, referent) => borrow_name(*mutability, referent),
            Ty::Option(t) => format!("option<{}>", t.name()),
            Ty::OptionRaw(_) => "option<raw<record>>".to_string(),
            Ty::Unit => "()".to_string(),
        }
    }
}

/// How a borrow of `referent` is spelled.
///
/// The marker is a prefix on the referent's own name, so the printing stays
/// compositional and every new referent shape prints without an edit here.
/// The one exception is the spelling the language actually uses for a
/// resource borrow: `resource &K` puts the marker *after* the keyword.
fn borrow_name(mutability: Mutability, referent: &Ty) -> String {
    let marker = match mutability {
        Mutability::Shared => "&",
        Mutability::Mut => "&mut ",
    };
    match referent {
        Ty::Res(kind) => format!("resource {marker}{}", kind.name()),
        other => format!("{marker}{}", other.name()),
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
        type_args: Vec<TypeArg>,
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
    /// A profile-mediated device access. It requires explicit affine
    /// authority and an `unsafe` audit boundary, but never exposes a raw
    /// address to source code.
    DeviceOp {
        op: DeviceOp,
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
    /// `name.take` — atomically extract an owned payload from a named
    /// mutable affine-option local and leave `none` behind. The checker only
    /// admits this as the direct initializer of an explicit owned local; a
    /// name-shaped node keeps that ownership transfer visible to every later
    /// stage instead of disguising it as an ordinary option projection.
    OptTake {
        option: String,
        option_span: Span,
    },
    /// `some(e)` / `none` — contextual option construction. Affine-option
    /// checking admits only `none` and a freshly allocated Boolean array.
    SomeE(Box<Expr>),
    NoneE,
    /// `[e1, e2, ...]` — test functions only.
    ArrayLit(Vec<Expr>),
    /// `alloc_array<T>(len, init)` — a fresh owned array (design §7/§10:
    /// allocation failure is a named OOM trap, not a VC).
    AllocArray {
        elem: Ty,
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
        type_args: Vec<TypeArg>,
        init: String,
        args: Vec<Expr>,
    },
    /// `o.f` — int field read on a class-typed name (ADR 0010).
    ClassField {
        obj: String,
        obj_span: Span,
        field: String,
    },
    /// `r.f` after the checker resolves `r` as a POD record rather than
    /// a class. The parser initially produces `ClassField`; keeping a
    /// distinct checked node prevents later stages from conflating their
    /// runtime and ownership semantics (ADR 0054).
    RecordField {
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
    /// Direct positional construction of a POD record in field declaration
    /// order. Unlike `CtorCall`, this invokes no initializer body.
    RecordLit {
        record: String,
        record_span: Span,
        args: Vec<Expr>,
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
    Unsafe { kw_span: Span, body: Vec<Stmt> },
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

/// Why a concrete monomorphized declaration may reuse a retained template's
/// proof instead of generating its own obligations.
///
/// Naming the ADR 0009 integer model in the variant makes the proof domain
/// explicit: future bool/record instances cannot silently inherit a theorem
/// proved only for integer-valued templates.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProofReuse {
    None,
    /// Opaque authorization issued only by monomorphization after validating
    /// a concrete all-integer instantiation. External AST callers may inspect
    /// this marker but cannot forge its private payload.
    Adr0009IntModel(Adr0009IntModelReuse),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Adr0009IntModelReuse {
    template: String,
    _mono_authority: (),
}

impl Adr0009IntModelReuse {
    pub fn template(&self) -> &str {
        &self.template
    }
}

impl ProofReuse {
    pub fn template(&self) -> Option<&str> {
        match self {
            ProofReuse::None => None,
            ProofReuse::Adr0009IntModel(reuse) => Some(reuse.template()),
        }
    }

    pub fn is_none(&self) -> bool {
        matches!(self, ProofReuse::None)
    }

    pub(crate) fn adr0009_int_model(template: String) -> ProofReuse {
        ProofReuse::Adr0009IntModel(Adr0009IntModelReuse {
            template,
            _mono_authority: (),
        })
    }
}

impl Default for ProofReuse {
    fn default() -> ProofReuse {
        ProofReuse::None
    }
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
    pub proof_reuse: ProofReuse,
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
    pub proof_reuse: ProofReuse,
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
pub struct RecordField {
    pub name: String,
    pub ty: Ty,
    pub offset: i128,
    pub span: Span,
    pub offset_span: Span,
}

/// An explicitly laid-out, plain runtime value (ADR 0054). A record is not a
/// restricted class: its declaration has no member or ownership surface at
/// all, and the checker validates its complete storage geometry separately.
#[derive(Debug, Clone)]
pub struct RecordDecl {
    pub is_pub: bool,
    pub name: String,
    pub name_span: Span,
    pub layout: StorageLayout,
    pub layout_span: Span,
    pub fields: Vec<RecordField>,
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
    pub records: Vec<RecordDecl>,
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

#[cfg(test)]
mod generic_ty_tests {
    use super::*;

    fn parameter(index: usize) -> GenericTy {
        GenericTy::Param(TypeParamId::new(index).expect("test parameter is in range"))
    }

    #[test]
    fn type_parameter_ids_enforce_the_legacy_g0_ceiling() {
        assert_eq!(MAX_TYPE_PARAMS, 256);
        assert_eq!(TypeParamId::new(0).unwrap().index(), 0);
        assert_eq!(
            TypeParamId::new(MAX_TYPE_PARAMS - 1).unwrap().index(),
            MAX_TYPE_PARAMS - 1
        );
        assert_eq!(TypeParamId::new(MAX_TYPE_PARAMS), None);
    }

    /// Affinity is computed from the shape, so it has to agree with the
    /// ownership rule stated on its own — for every shape, not for the ones
    /// someone remembered. The right-hand side is that rule, written out
    /// where a reader can compare it against the language's ownership
    /// documentation without reading `is_affine`.
    ///
    /// It is derived from the *spelling* rather than from the constructor
    /// list `is_affine` matches on. A second copy is only worth having if it
    /// can be wrong differently: two copies that both enumerate constructors
    /// can be edited identically-wrong in one sitting, and this test would
    /// still pass.
    #[test]
    fn affinity_agrees_with_the_ownership_rule() {
        fn owns(ty: &Ty) -> bool {
            let spelled = ty.name();
            // A borrow is written with a `&` — at the head of a value
            // borrow, and after the keyword in `resource &K`. Either way it
            // names storage someone else owns (ADRs 0010, 0023, 0024).
            if spelled.starts_with('&') || spelled.starts_with("resource &") {
                return false;
            }
            // An option owns exactly when its present case does.
            if let Some(payload) = ty.as_option() {
                return owns(payload);
            }
            // What is left owns when it names a class, a resource, or an
            // array: `class`, `resource K`, `[T]`.
            spelled == "class" || spelled.starts_with("resource ") || spelled.starts_with('[')
        }
        for (_, ty) in crate::shape_admission::samples() {
            assert_eq!(
                ty.is_affine(),
                owns(&ty),
                "affinity of `{}` disagrees with the ownership rule",
                ty.name()
            );
        }
    }

    /// The copyable family and the owning family may not overlap.
    ///
    /// An option's payload is a full type, so an option can own. Every rule
    /// that would duplicate an option reaches its payload through
    /// `check::option_payload_ty`; every rule that moves, takes, joins, or
    /// destroys one routes on `Ty::as_affine_option_payload`. If a single
    /// shape were admitted by the first while owning, a copy rule would
    /// duplicate an owner with no diagnostic — which is the failure this
    /// whole partition exists to prevent.
    ///
    /// The two are not complements: `option<class>` owns and is in neither
    /// family, because the copyable gate refuses it. That is why the owning
    /// family is read as "the payload is an owned array" rather than as "the
    /// payload is affine".
    #[test]
    fn no_owning_option_is_admitted_by_the_copyable_option_gate() {
        let mut owning = 0;
        for (_, ty) in crate::shape_admission::samples() {
            let Ty::Option(payload) = &ty else { continue };
            if !payload.is_affine() {
                continue;
            }
            owning += 1;
            assert!(
                crate::check::option_payload_ty((**payload).clone(), crate::span::Span::new(0, 0))
                    .is_err(),
                "`{}` owns its payload, so the copyable-option gate must refuse it",
                ty.name()
            );
        }
        assert!(owning > 0, "the samples must contain an owning option");
    }

    /// The record-field allow-list, checked against the match it replaced.
    /// Getting this wrong moves matrix cells in either direction: an extra
    /// admission opens a cell silently, a missing one closes a shape two
    /// corpus subjects rely on.
    #[test]
    fn storage_layout_agrees_with_the_record_field_rule_it_replaces() {
        for (_, ty) in crate::shape_admission::samples() {
            let by_constructor = match &ty {
                Ty::Int(width) if !matches!(width, IntTy::TParam(_)) => Some(width.layout()),
                Ty::RawRecord(_) | Ty::OptionRaw(_) => Some(StorageLayout { size: 8, align: 8 }),
                _ => None,
            };
            assert_eq!(
                ty.storage_layout(),
                by_constructor,
                "the field geometry of `{}` disagrees with the rule it is read from",
                ty.name()
            );
        }
        // `raw<u8>` is a byte cursor whose pointee has no record identity, so
        // it stays without a field form even though `raw<Record>` has one.
        assert_eq!(Ty::Raw(IntTy::U8).storage_layout(), None);
        assert!(Ty::RawRecord(0).storage_layout().is_some());
    }

    /// The argument domain is concrete integers, which is what makes a
    /// retained template parameter provably copyable. Widening the domain
    /// fails here rather than silently classifying an owner as copyable.
    #[test]
    fn type_arguments_are_copyable() {
        for width in [
            IntTy::U8,
            IntTy::U16,
            IntTy::U32,
            IntTy::U64,
            IntTy::I8,
            IntTy::I16,
            IntTy::I32,
            IntTy::I64,
        ] {
            assert!(!Ty::Int(width).is_affine());
        }
        let parameter = TypeParamId::from_legacy(0);
        assert!(!Ty::Param(parameter).is_affine());
    }

    #[test]
    fn container_payloads_are_ordinary_types() {
        let parameter = TypeParamId::from_legacy(7);
        assert!(!Ty::Param(parameter).is_concrete());
        assert!(!Ty::Int(IntTy::TParam(7)).is_concrete());
        assert!(Ty::Bool.is_concrete());
        assert_eq!(Ty::Param(parameter).name(), "<T7>");
        assert_eq!(Ty::option(Ty::Param(parameter)).name(), "option<<T7>>");
        let affine = Ty::affine_array_option(Ty::Param(parameter));
        assert!(!affine.is_concrete());
        assert_eq!(affine.name(), "option<[<T7>]>");
        assert!(Ty::affine_array_option(Ty::Bool).is_concrete());

        // An owning option is one constructor over an owned array, and the
        // owning family is read back off that payload.
        let owning = Ty::affine_array_option(Ty::Bool);
        assert_eq!(owning, Ty::option(Ty::array(Ty::Bool)));
        assert!(owning.is_affine());
        assert!(owning.is_affine_option());
        assert_eq!(
            owning.as_affine_option_payload(),
            Some(&Ty::array(Ty::Bool))
        );
        assert_eq!(
            owning.as_affine_option_payload().and_then(Ty::as_owned_array),
            Some(&Ty::Bool)
        );
        // A borrowed array payload is representable and does not join the
        // owning family: a borrow owns nothing.
        assert!(!Ty::option(Ty::array_ref(Ty::Bool, Mutability::Shared)).is_affine_option());
        // Neither does an option over another owner the ownership rules are
        // not written for; the copyable-option gate refuses it by name.
        assert!(!Ty::option(Ty::Class(0)).is_affine_option());
        assert!(Ty::option(Ty::Class(0)).is_affine());

        // Nesting is representable, and prints exactly as it is spelled. What
        // refuses these shapes is a stage gate with a name, not the grammar.
        assert_eq!(Ty::array(Ty::array(Ty::Int(IntTy::U64))).name(), "[[u64]]");
        assert_eq!(
            Ty::option(Ty::option(Ty::Int(IntTy::U64))).name(),
            "option<option<u64>>"
        );
        assert_eq!(Ty::array(Ty::Class(0)).name(), "[class]");
        assert!(!Ty::array(Ty::array(Ty::Param(parameter))).is_concrete());
        assert_eq!(
            Ty::array(Ty::array(Ty::Int(IntTy::U64))).structural_depth(),
            3
        );
    }

    #[test]
    fn proof_reuse_names_its_integer_model_domain() {
        let none = ProofReuse::None;
        assert!(none.is_none());
        assert_eq!(none.template(), None);

        let reuse = ProofReuse::adr0009_int_model("identity".into());
        assert!(!reuse.is_none());
        assert_eq!(reuse.template(), Some("identity"));
    }

    #[test]
    fn legacy_integer_parameters_normalize_and_round_trip() {
        let concrete = [
            IntTy::U8,
            IntTy::U16,
            IntTy::U32,
            IntTy::U64,
            IntTy::I8,
            IntTy::I16,
            IntTy::I32,
            IntTy::I64,
        ];
        for integer in concrete {
            let ty = GenericTy::from_legacy_int(integer);
            assert_eq!(ty, GenericTy::Int(integer));
            assert_eq!(ty.try_to_v1_int(), Ok(integer));
            assert_eq!(ty.try_to_concrete_v1_int(), Ok(integer));
        }

        let parameter = GenericTy::from_legacy_int(IntTy::TParam(7));
        assert_eq!(parameter, GenericTy::Param(TypeParamId::from_legacy(7)));
        assert_eq!(parameter.try_to_v1_int(), Ok(IntTy::TParam(7)));
        assert_eq!(
            parameter.try_to_concrete_v1_int(),
            Err(GenericTyError::UnsubstitutedTypeParameter(
                TypeParamId::from_legacy(7)
            ))
        );

        let malformed = GenericTy::Int(IntTy::TParam(7));
        assert_eq!(
            malformed.try_to_v1_int(),
            Err(GenericTyError::NonCanonicalLegacyParameter(
                TypeParamId::from_legacy(7)
            ))
        );
        assert!(!malformed.is_concrete());
    }

    #[test]
    fn v1_integer_conversion_rejects_new_shapes() {
        for ty in [
            GenericTy::Bool,
            GenericTy::Record("Node".into()),
            GenericTy::Array(Box::new(GenericTy::Int(IntTy::I32))),
            GenericTy::Option(Box::new(GenericTy::Int(IntTy::I32))),
            GenericTy::Class {
                name: "Box".into(),
                args: vec![GenericTy::Int(IntTy::I32)].into_boxed_slice(),
            },
        ] {
            assert_eq!(ty.try_to_v1_int(), Err(GenericTyError::NotV1Integer));
            assert_eq!(
                ty.try_to_concrete_v1_int(),
                Err(GenericTyError::NotV1Integer)
            );
        }
    }

    #[test]
    fn substitution_recurses_through_every_container_shape() {
        let template = GenericTy::Class {
            name: "Pair".into(),
            args: vec![
                GenericTy::Option(Box::new(parameter(0))),
                GenericTy::Array(Box::new(GenericTy::Class {
                    name: "Box".into(),
                    args: vec![parameter(1)].into_boxed_slice(),
                })),
            ]
            .into_boxed_slice(),
        };
        let got = template
            .substitute(&[GenericTy::Bool, GenericTy::Record("Node".into())])
            .unwrap();
        let expected = GenericTy::Class {
            name: "Pair".into(),
            args: vec![
                GenericTy::Option(Box::new(GenericTy::Bool)),
                GenericTy::Array(Box::new(GenericTy::Class {
                    name: "Box".into(),
                    args: vec![GenericTy::Record("Node".into())].into_boxed_slice(),
                })),
            ]
            .into_boxed_slice(),
        };
        assert_eq!(got, expected);
        assert!(got.is_concrete());

        assert_eq!(
            GenericTy::Int(IntTy::TParam(0))
                .substitute(&[GenericTy::Bool])
                .unwrap(),
            GenericTy::Bool
        );
    }

    #[test]
    fn substitution_reports_an_out_of_bounds_parameter() {
        let parameter = TypeParamId::new(2).unwrap();
        assert_eq!(
            GenericTy::Param(parameter).substitute(&[GenericTy::Bool]),
            Err(GenericTyError::TypeParameterOutOfBounds {
                parameter,
                arity: 1,
            })
        );
    }

    #[test]
    fn concreteness_and_depth_are_recursive() {
        let concrete = GenericTy::Class {
            name: "Outer".into(),
            args: vec![GenericTy::Option(Box::new(GenericTy::Array(Box::new(
                GenericTy::Int(IntTy::I32),
            ))))]
            .into_boxed_slice(),
        };
        assert!(concrete.is_concrete());
        assert_eq!(concrete.structural_depth(), 4);

        let abstract_ty = GenericTy::Option(Box::new(GenericTy::Class {
            name: "Box".into(),
            args: vec![parameter(0)].into_boxed_slice(),
        }));
        assert!(!abstract_ty.is_concrete());
        assert_eq!(abstract_ty.structural_depth(), 3);
        assert_eq!(
            GenericTy::Class {
                name: "UnitLike".into(),
                args: Box::new([]),
            }
            .structural_depth(),
            1
        );
    }

    #[test]
    fn nominal_visitation_is_deterministic_preorder() {
        let ty = GenericTy::Class {
            name: "Outer".into(),
            args: vec![
                GenericTy::Record("Header".into()),
                GenericTy::Option(Box::new(GenericTy::Class {
                    name: "Inner".into(),
                    args: vec![GenericTy::Record("Payload".into())].into_boxed_slice(),
                })),
            ]
            .into_boxed_slice(),
        };
        let mut seen = Vec::new();
        ty.visit_nominals(|kind, name| seen.push((kind, name.to_string())));
        assert_eq!(
            seen,
            vec![
                (NominalKind::Class, "Outer".into()),
                (NominalKind::Record, "Header".into()),
                (NominalKind::Class, "Inner".into()),
                (NominalKind::Record, "Payload".into()),
            ]
        );
    }

    #[test]
    fn canonical_keys_are_length_prefixed_and_injective() {
        let integer = GenericTy::Int(IntTy::I32);
        let array = GenericTy::Array(Box::new(integer.clone()));
        let record = GenericTy::Record("Node".into());
        let option_record = GenericTy::Option(Box::new(record.clone()));
        let class = GenericTy::Class {
            name: "Vec".into(),
            args: vec![option_record.clone()].into_boxed_slice(),
        };

        assert_eq!(integer.concrete_key().unwrap().as_str(), "I3_i32");
        assert_eq!(array.concrete_key().unwrap().as_str(), "A6_I3_i32");
        assert_eq!(record.concrete_key().unwrap().as_str(), "R4_Node");
        assert_eq!(option_record.concrete_key().unwrap().as_str(), "O7_R4_Node");
        assert_eq!(
            class.concrete_key().unwrap().as_str(),
            "C3_Vec1_10_O7_R4_Node"
        );

        let array_of_option =
            GenericTy::Array(Box::new(GenericTy::Option(Box::new(integer.clone()))));
        let option_of_array = GenericTy::Option(Box::new(array));
        assert_ne!(
            array_of_option.concrete_key().unwrap(),
            option_of_array.concrete_key().unwrap()
        );
        assert_ne!(
            GenericTy::Record("X".into()).concrete_key().unwrap(),
            GenericTy::Class {
                name: "X".into(),
                args: Box::new([]),
            }
            .concrete_key()
            .unwrap()
        );

        let left = GenericTy::Class {
            name: "A_i32".into(),
            args: vec![GenericTy::Int(IntTy::U8)].into_boxed_slice(),
        };
        let right = GenericTy::Class {
            name: "A".into(),
            args: vec![GenericTy::Int(IntTy::I32), GenericTy::Int(IntTy::U8)].into_boxed_slice(),
        };
        assert_ne!(left.concrete_key().unwrap(), right.concrete_key().unwrap());
    }

    #[test]
    fn concrete_keys_reject_parameters_and_noncanonical_legacy_parameters() {
        let parameter = TypeParamId::new(3).unwrap();
        assert_eq!(
            GenericTy::Param(parameter).concrete_key(),
            Err(GenericTyError::UnsubstitutedTypeParameter(parameter))
        );
        assert_eq!(
            GenericTy::Int(IntTy::TParam(3)).concrete_key(),
            Err(GenericTyError::NonCanonicalLegacyParameter(parameter))
        );
    }

    #[test]
    fn type_arg_preserves_span_while_normalizing_legacy_parameters() {
        let span = Span::new(10, 14);
        assert_eq!(
            TypeArg::from_legacy_int(IntTy::TParam(2), span),
            TypeArg {
                ty: parameter(2),
                span,
            }
        );
    }
}
