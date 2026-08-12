//! `sable test`: the tree-walking interpreter with trap semantics
//! (design §9). Every partial operation is checked exactly where the
//! verifier would emit a VC — overflow, bounds, division — and every
//! monitorable contract (pre, post, invariant, variant) is evaluated
//! dynamically via `speceval`. Unmonitorable clauses are reported as
//! skipped, never guessed.
//!
//! This is a dev tool in the sanitizer category: its results are not a
//! verification claim, and test functions are never verified.

use crate::ast::*;
use crate::speceval::{self, GhostDefs, SpecEnv, SpecVal};
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

#[derive(Debug, Clone)]
pub enum RtVal {
    Int(i128),
    Bool(bool),
    Arr(Rc<RefCell<Vec<i128>>>),
    Opt(Option<i128>),
    Obj {
        class: usize,
        fields: Rc<RefCell<HashMap<String, RtVal>>>,
    },
    /// A raw pointer: allocation id plus byte offset (ADR 0025/0026).
    Ptr(i128, i128),
    Unit,
}

pub struct TestReport {
    pub name: String,
    /// Err carries a rendered failure message.
    pub outcome: Result<(), String>,
    /// Clauses that could not be checked dynamically (text, reason).
    pub skipped: Vec<(String, String)>,
}

struct Trap {
    message: String,
    span: crate::span::Span,
    /// This failure is the machine's `undef`, not a trap. The interpreter
    /// is allowed to be *more precise* than the machine — it says which
    /// rule was broken — as long as it agrees on the classification, which
    /// is what the differential harness compares (ADR 0025).
    undef: bool,
}

type IResult<T> = Result<T, Trap>;

const FUEL: u64 = 50_000_000;

pub fn run_tests(program: &Program, mods: &crate::modules::ModuleSet) -> Vec<TestReport> {
    let source = mods.combined_source.as_str();
    let ghosts = GhostDefs::from_items(&program.ghosts);
    let fns: HashMap<&str, &Fn> = program.fns.iter().map(|f| (f.name.as_str(), f)).collect();
    let classes = &program.classes;

    program
        .fns
        .iter()
        .filter(|f| f.name.starts_with("test_"))
        .map(|test| {
            let mut interp = Interp {
                fns: &fns,
                classes,
                ghosts: &ghosts,
                source,
                fuel: FUEL,
                skipped: Vec::new(),
                raw: RawHeap::default(),
                world: None,
            };
            let outcome = interp.call(test, Vec::new()).map(|_| ()).map_err(|trap| {
                let (file, line, col) = mods.locate(trap.span.start);
                format!("{} ({file}:{line}:{col})", trap.message)
            });
            TestReport {
                name: test.name.clone(),
                outcome,
                skipped: interp.skipped,
            }
        })
        .collect()
}

/// Run one zero-argument function, returning its value or the raw trap
/// message (no source location) — the interpreter side of the SVM
/// differential harness.
pub fn run_fn(
    program: &Program,
    mods: &crate::modules::ModuleSet,
    name: &str,
) -> Result<RtVal, String> {
    let ghosts = GhostDefs::from_items(&program.ghosts);
    let fns: HashMap<&str, &Fn> = program.fns.iter().map(|f| (f.name.as_str(), f)).collect();
    let f = fns[name];
    let mut interp = Interp {
        fns: &fns,
        classes: &program.classes,
        ghosts: &ghosts,
        source: mods.combined_source.as_str(),
        fuel: FUEL,
        skipped: Vec::new(),
        raw: RawHeap::default(),
        world: None,
    };
    interp.call(f, Vec::new()).map_err(|trap| {
        if trap.undef {
            format!("undef: {}", trap.message)
        } else {
            trap.message
        }
    })
}

enum Flow {
    Normal,
    Return(RtVal),
}

struct Interp<'a> {
    fns: &'a HashMap<&'a str, &'a Fn>,
    classes: &'a [ClassDecl],
    ghosts: &'a GhostDefs,
    source: &'a str,
    fuel: u64,
    skipped: Vec<(String, String)>,
    raw: RawHeap,
    /// `None` until a test asks for one. A program cannot conjure the
    /// world; only `posix_world` can, and only in a test.
    world: Option<PosixWorld>,
}

/// The interpreter's raw heap. It mirrors the SVM's: a fresh-provenance
/// counter and allocations that are marked dead rather than removed, so a
/// stale pointer stays distinguishable from a fresh one (ADR 0025).
///
/// Exposure is modelled the way the SVM models it — copy the array's
/// bytes into a fresh loan allocation, run the body, copy the final bytes
/// back — because that is what makes the escape rules observable: a
/// pointer that outlived its exposure would name a dead allocation.
#[derive(Default)]
struct RawHeap {
    next: i128,
    allocs: HashMap<i128, RawAlloc>,
}

struct RawAlloc {
    live: bool,
    /// `None` is uninitialized: distinct from any byte value.
    bytes: Vec<Option<i128>>,
    /// Starts of abstract typed `u64` extents. `None` is a typed but
    /// uninitialized cell; `Some(v)` is initialized. Bytes covered by a
    /// cell are inaccessible until the uninitialized cell is converted
    /// back (ADR 0031).
    cells_u64: HashMap<i128, Option<i128>>,
}

impl RawHeap {
    fn fresh(&mut self, bytes: Vec<Option<i128>>) -> i128 {
        let id = self.next;
        self.next += 1;
        self.allocs.insert(
            id,
            RawAlloc {
                live: true,
                bytes,
                cells_u64: HashMap::new(),
            },
        );
        id
    }

    fn live_at(&self, alloc: i128, off: i128) -> Option<&RawAlloc> {
        let al = self.allocs.get(&alloc)?;
        let covered = al
            .cells_u64
            .keys()
            .any(|start| *start <= off && off < *start + IntTy::U64.layout().size);
        if al.live && off >= 0 && (off as usize) < al.bytes.len() && !covered {
            Some(al)
        } else {
            None
        }
    }
}

/// The scripted external world `sable test` plays against.
///
/// A contract cannot predict a short read or an I/O error, so those live
/// here and never in the view (ADR 0028). The `script` argument to
/// `posix_world` selects the schedule, which is what makes external
/// behaviour something a test *author* controls rather than something that
/// happens to them.
struct PosixWorld {
    /// The byte stream descriptors read from, indexed by absolute position.
    data: Vec<i128>,
    /// How many descriptors the world has handed out.
    fds: i128,
    /// Descriptors whose *authority* has been adopted. The world can
    /// supply each one once: affinity governs a token that exists, and
    /// this is what stops a second one being minted beside it.
    claimed: HashSet<i128>,
    /// Which read attempts misbehave, by 0-based call index: `Short(k)`
    /// transfers `k` bytes, `Fail(e)` returns `-e`.
    schedule: Vec<ReadOutcome>,
    /// How many reads have happened.
    reads: usize,
    /// Positions, by descriptor.
    pos: Vec<i128>,
}

#[derive(Clone, Copy)]
enum ReadOutcome {
    Full,
    Short(i128),
    Fail(i128),
}

impl PosixWorld {
    /// Scripts are numbered so a test can name one. Each is deliberately
    /// small and deliberately nasty: the interesting cases are the ones a
    /// caller is tempted to assume away.
    fn scripted(script: i128) -> PosixWorld {
        let data: Vec<i128> = (0..16).map(|i| (i * 7 + 3) % 256).collect();
        let schedule = match script {
            // Everything succeeds.
            0 => vec![],
            // The second read is short by half.
            1 => vec![ReadOutcome::Full, ReadOutcome::Short(2)],
            // The first read fails outright (EIO).
            2 => vec![ReadOutcome::Fail(5)],
            // Short, then a failure, then fine again.
            _ => vec![
                ReadOutcome::Short(1),
                ReadOutcome::Fail(5),
                ReadOutcome::Full,
            ],
        };
        PosixWorld {
            data,
            fds: 3,
            claimed: HashSet::new(),
            schedule,
            reads: 0,
            pos: vec![0; 3],
        }
    }

    fn next_outcome(&mut self) -> ReadOutcome {
        let out = self
            .schedule
            .get(self.reads)
            .copied()
            .unwrap_or(ReadOutcome::Full);
        self.reads += 1;
        out
    }
}

/// A place a value can be moved out of or dropped: a local, or a field of
/// the enclosing `self`. These are the roots of the checker's `Place`, at
/// the depth the program language can name.
enum RtPlace {
    Local(String),
    SelfField(String),
}

impl RtPlace {
    /// How the place is spelled in a diagnostic.
    fn name(&self) -> String {
        match self {
            RtPlace::Local(n) => n.clone(),
            RtPlace::SelfField(f) => format!("self.{f}"),
        }
    }
}

struct Frame {
    vars: HashMap<String, RtVal>,
    /// Entry-state scalar params (post clauses mean entry values for
    /// by-value params) and entry snapshots of &mut state (`old a`,
    /// `old self`).
    entry_scalars: HashMap<String, RtVal>,
    olds: HashMap<String, SpecVal>,
    /// Member context: the class index and its field storage.
    self_ctx: Option<(usize, Rc<RefCell<HashMap<String, RtVal>>>)>,
}

impl<'a> Interp<'a> {
    /// The deterministic test shims. An extern has no Sable body, so
    /// `sable test` has to supply one — and it is keyed on the *audit id*,
    /// not the name, because the id is what names the contract version the
    /// program was verified against (ADR 0027).
    ///
    /// An unknown id traps. Running the body as a no-op would let a
    /// contract appear to hold because nothing happened, which is the one
    /// outcome a monitor must never produce.
    fn call_extern(&mut self, f: &'a Fn, args: Vec<RtVal>, span: crate::span::Span)
        -> IResult<RtVal> {
        let info = f.extern_info.as_ref().expect("checked: extern");
        match info.audit_id.as_str() {
            "test.fill.v1" => {
                let (RtVal::Ptr(a, off), RtVal::Int(n), RtVal::Int(v)) =
                    (args[0].clone(), args[1].clone(), args[2].clone())
                else {
                    unreachable!("checked: (raw<u8>, u64, u8)")
                };
                for i in 0..n {
                    if self.raw.live_at(a, off + i).is_none() {
                        return Err(Trap {
                            undef: true,
                            message: format!(
                                "`{}` writes out of bounds: {a}+{}",
                                f.name,
                                off + i
                            ),
                            span,
                        });
                    }
                    self.raw
                        .allocs
                        .get_mut(&a)
                        .expect("live_at checked")
                        .bytes[(off + i) as usize] = Some(v);
                }
                Ok(RtVal::Unit)
            }
            "test.checksum.v1" => {
                let (RtVal::Ptr(a, off), RtVal::Int(n)) = (args[0].clone(), args[1].clone())
                else {
                    unreachable!("checked: (raw<u8>, u64)")
                };
                let mut sum: i128 = 0;
                for i in 0..n {
                    match self.raw.live_at(a, off + i).map(|al| al.bytes[(off + i) as usize]) {
                        Some(Some(b)) => sum += b,
                        _ => {
                            return Err(Trap {
                                undef: true,
                                message: format!(
                                    "`{}` reads out of bounds or uninitialized: {a}+{}",
                                    f.name,
                                    off + i
                                ),
                                span,
                            });
                        }
                    }
                }
                Ok(RtVal::Int(sum))
            }
            // POSIX-shaped shims against the scripted world. Short reads
            // and failures come from the script, not from the contract:
            // no contract can predict them, which is why a caller has to
            // handle every outcome its post admits (ADR 0028).
            "posix.read.v1" => {
                let (RtVal::Int(fd), RtVal::Ptr(a, off), RtVal::Int(n)) =
                    (args[0].clone(), args[1].clone(), args[2].clone())
                else {
                    unreachable!("checked: (i32, raw<u8>, u64)")
                };
                let Some(w) = self.world.as_mut() else {
                    return Err(Trap {
                        undef: false,
                        message: format!("`{}` called with no world in play", f.name),
                        span,
                    });
                };
                if fd < 0 || fd >= w.fds {
                    return Err(Trap {
                        undef: true,
                        message: format!("`{}`: descriptor {fd} was never handed out", f.name),
                        span,
                    });
                }
                let want = match w.next_outcome() {
                    ReadOutcome::Full => n,
                    ReadOutcome::Short(k) => k.min(n),
                    ReadOutcome::Fail(e) => return Ok(RtVal::Int(-e)),
                };
                let pos = w.pos[fd as usize];
                let avail = (w.data.len() as i128 - pos).max(0);
                let got = want.min(avail);
                let bytes: Vec<i128> = (0..got)
                    .map(|i| w.data[(pos + i) as usize])
                    .collect();
                w.pos[fd as usize] = pos + got;
                for (i, b) in bytes.iter().enumerate() {
                    let at = off + i as i128;
                    if self.raw.live_at(a, at).is_none() {
                        return Err(Trap {
                            undef: true,
                            message: format!("`{}` writes out of bounds: {a}+{at}", f.name),
                            span,
                        });
                    }
                    self.raw
                        .allocs
                        .get_mut(&a)
                        .expect("live_at checked")
                        .bytes[at as usize] = Some(*b);
                }
                Ok(RtVal::Int(got))
            }
            "posix.close.v2" => {
                let RtVal::Int(fd) = args[0].clone() else {
                    unreachable!("checked: i32")
                };
                let Some(w) = self.world.as_mut() else {
                    return Err(Trap {
                        undef: false,
                        message: format!("`{}` called with no world in play", f.name),
                        span,
                    });
                };
                if fd < 0 || fd >= w.fds {
                    return Err(Trap {
                        undef: true,
                        message: format!("`{}`: descriptor {fd} was never handed out", f.name),
                        span,
                    });
                }
                // Closing twice is a *checker* error — the `OpenFile` is
                // affine — so the shim need not police it, and the fact
                // that it cannot is the point: the discipline is static.
                Ok(RtVal::Int(0))
            }
            other => Err(Trap {
                undef: false,
                message: format!(
                    "no test shim for audited extern `{}` (audit id `{other}`)",
                    f.name
                ),
                span,
            }),
        }
    }

    fn call(&mut self, f: &'a Fn, args: Vec<RtVal>) -> IResult<RtVal> {
        let mut frame = Frame {
            vars: HashMap::new(),
            entry_scalars: HashMap::new(),
            olds: HashMap::new(),
            self_ctx: None,
        };
        for (p, v) in f.params.iter().filter(|p| !p.ty.is_resource()).zip(args) {
            match (&v, p.ty) {
                (RtVal::Arr(a), Ty::Array(_, Mutability::Mut)) => {
                    frame
                        .olds
                        .insert(p.name.clone(), SpecVal::Arr(a.borrow().clone()));
                }
                // `&mut C`: the borrow shares storage with the caller, so
                // the bare name reads the current state and `old p` needs
                // the value it had at entry. `spec_of` copies.
                (obj @ RtVal::Obj { .. }, Ty::ClassRef(_, Mutability::Mut)) => {
                    if let Some(sv) = spec_of(obj) {
                        frame.olds.insert(p.name.clone(), sv);
                    }
                }
                (RtVal::Arr(_), _) => {}
                _ => {
                    frame.entry_scalars.insert(p.name.clone(), v.clone());
                }
            }
            frame.vars.insert(p.name.clone(), v);
        }

        for pre in &f.pres {
            self.check_clause(&frame, pre, None, &format!("pre of `{}`", f.name))?;
        }

        let flow = self.exec_block(&f.body, &mut frame)?;
        let result = match flow {
            Flow::Return(v) => v,
            Flow::Normal => RtVal::Unit,
        };

        for post in &f.posts {
            self.check_clause(
                &frame,
                post,
                Some(&result),
                &format!("post of `{}`", f.name),
            )?;
        }
        self.drop_owned_params(&f.params, &mut frame)?;
        Ok(result)
    }

    /// Owned parameters die with the frame, after the contract has been
    /// checked against them. A by-value class argument was handed over, so
    /// the callee is who destroys it — unless the body moved it on, in
    /// which case its place is already empty.
    fn drop_owned_params(&mut self, params: &[Param], frame: &mut Frame) -> IResult<()> {
        for p in params.iter().rev() {
            if matches!(p.ty, Ty::Class(_)) {
                self.drop_place(&RtPlace::Local(p.name.clone()), frame)?;
            }
        }
        Ok(())
    }

    /// Contract-clause check with the right environment: entry values for
    /// by-value params, current contents for arrays, snapshots for `old`.
    fn check_clause(
        &mut self,
        frame: &Frame,
        clause: &crate::scan::Clause,
        result: Option<&RtVal>,
        what: &str,
    ) -> IResult<()> {
        let mut vars: HashMap<String, SpecVal> = HashMap::new();
        for (name, v) in &frame.vars {
            let val = if let Some(entry) = frame.entry_scalars.get(name) {
                entry
            } else {
                v
            };
            if let Some(sv) = spec_of(val) {
                vars.insert(name.clone(), sv);
            }
        }
        // A by-value parameter the body handed on is gone from its place,
        // but a contract speaks about the *value* it was given, and a value
        // outlives the transfer of authority (ADR 0024): the post of an
        // `init` that stores its argument in a field still says what the
        // field got.
        for (name, v) in &frame.entry_scalars {
            if !frame.vars.contains_key(name) {
                if let Some(sv) = spec_of(v) {
                    vars.insert(name.clone(), sv);
                }
            }
        }
        if let Some((class, fields)) = &frame.self_ctx {
            let obj = RtVal::Obj {
                class: *class,
                fields: fields.clone(),
            };
            if let Some(sv) = spec_of(&obj) {
                vars.insert("self".into(), sv);
            }
            for (k, v) in fields.borrow().iter() {
                if let Some(sv) = spec_of(v) {
                    vars.insert(k.clone(), sv);
                }
            }
        }
        if let Some(r) = result {
            if let Some(sv) = spec_of(r) {
                vars.insert("result".into(), sv);
            }
        }
        let env = SpecEnv {
            vars,
            olds: frame.olds.clone(),
            ghosts: self.ghosts,
        };
        match speceval::eval_clause(&clause.text, &env) {
            Ok(true) => Ok(()),
            Ok(false) => Err(Trap {
                undef: false,
                message: format!("{what} violated: {}", clause.text.replace('\n', " ")),
                span: clause.span,
            }),
            Err(um) => {
                self.skipped.push((clause.text.replace('\n', " "), um.0));
                Ok(())
            }
        }
    }

    /// Loop-clause check in the *current* frame (invariants speak about
    /// current values, including mutated by-value params).
    fn check_loop_clause(
        &mut self,
        frame: &Frame,
        clause: &crate::scan::Clause,
        what: &str,
    ) -> IResult<()> {
        let mut vars: HashMap<String, SpecVal> = HashMap::new();
        for (name, v) in &frame.vars {
            if let Some(sv) = spec_of(v) {
                vars.insert(name.clone(), sv);
            }
        }
        if let Some((class, fields)) = &frame.self_ctx {
            let obj = RtVal::Obj {
                class: *class,
                fields: fields.clone(),
            };
            if let Some(sv) = spec_of(&obj) {
                vars.insert("self".into(), sv);
            }
            for (k, v) in fields.borrow().iter() {
                if let Some(sv) = spec_of(v) {
                    vars.insert(k.clone(), sv);
                }
            }
        }
        let env = SpecEnv {
            vars,
            olds: frame.olds.clone(),
            ghosts: self.ghosts,
        };
        match speceval::eval_clause(&clause.text, &env) {
            Ok(true) => Ok(()),
            Ok(false) => Err(Trap {
                undef: false,
                message: format!("{what} violated: {}", clause.text.replace('\n', " ")),
                span: clause.span,
            }),
            Err(um) => {
                self.skipped.push((clause.text.replace('\n', " "), um.0));
                Ok(())
            }
        }
    }

    /// Run a block that owns its declarations: whatever it declares is
    /// destroyed at the closing brace, in reverse declaration order.
    fn exec_block(&mut self, stmts: &[Stmt], frame: &mut Frame) -> IResult<Flow> {
        let mut locals: Vec<String> = Vec::new();
        let out = self.exec_stmts(stmts, frame, &mut locals);
        // RAII: drop block-local values in reverse declaration order.
        // A local the block moved away is no longer in its place, which is
        // the whole reason a move removes it: the value belongs to whoever
        // took it, and this scope has nothing left to destroy.
        //
        // The drops run whether the block fell off its end or returned,
        // but not after a trap: a trapped program has stopped, and running
        // destructors past the failure would report the *second* thing that
        // went wrong.
        let out = out?;
        for name in locals.iter().rev() {
            self.drop_place(&RtPlace::Local(name.clone()), frame)?;
        }
        Ok(out)
    }

    /// Run a block whose declarations belong to the *enclosing* scope.
    ///
    /// `unsafe { ... }` and an exposure body are markers, not scopes: the
    /// checker keeps their locals in the function (ADR 0026), so a value
    /// declared inside one is still live at the closing brace and must not
    /// be destroyed there. The two sides have to agree about this, and the
    /// checker's answer is the language's.
    fn exec_open_block(
        &mut self,
        stmts: &[Stmt],
        frame: &mut Frame,
        locals: &mut Vec<String>,
    ) -> IResult<Flow> {
        self.exec_stmts(stmts, frame, locals)
    }

    fn exec_stmts(
        &mut self,
        stmts: &[Stmt],
        frame: &mut Frame,
        locals: &mut Vec<String>,
    ) -> IResult<Flow> {
        let mut out = Flow::Normal;
        for stmt in stmts {
            if let Stmt::VarDecl { name, .. } | Stmt::Decl { name, .. } = stmt {
                locals.push(name.clone());
            }
            match self.exec_stmt(stmt, frame, locals)? {
                Flow::Normal => {}
                ret => {
                    out = ret;
                    break;
                }
            }
        }
        Ok(out)
    }

    /// Remove a value from its source place, returning it.
    ///
    /// This is what makes a move a move at runtime: the source stops
    /// holding the value, so no later drop — of the scope, of the object,
    /// of the field — can reach it a second time. Every ownership transfer
    /// goes through here.
    fn take_place(&mut self, place: &RtPlace, frame: &mut Frame) -> Option<RtVal> {
        match place {
            RtPlace::Local(name) => frame.vars.remove(name.as_str()),
            RtPlace::SelfField(field) => {
                let (_, fields) = frame.self_ctx.clone()?;
                let v = fields.borrow_mut().remove(field.as_str());
                v
            }
        }
    }

    /// Take a value out of a place and destroy it: at scope exit, and
    /// wherever a place is overwritten. A place holding no value — moved
    /// away, or never initialized — has nothing to drop.
    fn drop_place(&mut self, place: &RtPlace, frame: &mut Frame) -> IResult<()> {
        let held = match place {
            RtPlace::Local(name) => frame.vars.get(name.as_str()).cloned(),
            RtPlace::SelfField(field) => frame
                .self_ctx
                .as_ref()
                .and_then(|(_, fields)| fields.borrow().get(field.as_str()).cloned()),
        };
        let Some(RtVal::Obj { class, fields }) = held else {
            return Ok(());
        };
        // Out of its place *before* the destructor runs: a `deinit` that
        // reached the dying value through its own name would see a value
        // that no longer belongs to anyone.
        self.take_place(place, frame);
        self.drop_value(class, &fields, &place.name())
    }

    /// The source place of an expression, if it names one. A call or a
    /// constructor is already a temporary: it has no source to clear.
    ///
    /// The two roots here are the two the program language can name as an
    /// ownership source, and they are the roots of the checker's `Place`.
    fn source_place(e: &Expr) -> Option<RtPlace> {
        match &e.kind {
            ExprKind::Var(n) => Some(RtPlace::Local(n.clone())),
            ExprKind::SelfField { field } => Some(RtPlace::SelfField(field.clone())),
            _ => None,
        }
    }

    /// Evaluate an expression in a position that *takes* the value, and
    /// clear its source place if it named one. Declarations, assignments,
    /// field assignments, arguments, and returns all transfer ownership,
    /// and they all transfer it the same way.
    ///
    /// Only class values have runtime identity to transfer: resources are
    /// erased (ADR 0024), and integers are copied.
    fn eval_moved(&mut self, e: &Expr, frame: &mut Frame) -> IResult<RtVal> {
        let v = self.eval(e, frame)?;
        if matches!(v, RtVal::Obj { .. }) {
            if let Some(place) = Self::source_place(e) {
                self.take_place(&place, frame);
            }
        }
        Ok(v)
    }

    /// Drop one class value: invariant, body, then the remaining fields in
    /// reverse declaration order. A field the body moved out is *not*
    /// dropped again — a moved field is somebody else's now, and dropping
    /// it twice is the failure the affine discipline exists to prevent.
    fn drop_value(
        &mut self,
        class: usize,
        fields: &Rc<RefCell<HashMap<String, RtVal>>>,
        what: &str,
    ) -> IResult<()> {
        let cd = self.classes[class].clone();
        self.check_invariants_at(&cd, fields, what)?;
        if let Some(body) = cd.deinit.clone() {
            let mut frame = Frame {
                vars: HashMap::new(),
                entry_scalars: HashMap::new(),
                olds: HashMap::new(),
                self_ctx: Some((class, fields.clone())),
            };
            self.exec_block(&body, &mut frame)?;
        }
        // The remaining fields, in reverse declaration order. A field the
        // body handed on is gone from the map, which is exactly the record
        // of "already somebody else's".
        for f in cd.fields.iter().rev() {
            let held = fields.borrow().get(f.name.as_str()).cloned();
            if let Some(RtVal::Obj {
                class: fc,
                fields: ff,
            }) = held
            {
                self.drop_value(fc, &ff, &format!("{what}.{}", f.name))?;
            }
        }
        Ok(())
    }

    fn check_invariants_at(
        &mut self,
        class: &ClassDecl,
        fields: &Rc<RefCell<HashMap<String, RtVal>>>,
        what: &str,
    ) -> IResult<()> {
        let mut vars: HashMap<String, SpecVal> = HashMap::new();
        let obj = RtVal::Obj {
            class: 0,
            fields: fields.clone(),
        };
        if let Some(sv) = spec_of(&obj) {
            vars.insert("self".into(), sv);
        }
        for (k, v) in fields.borrow().iter() {
            if let Some(sv) = spec_of(v) {
                vars.insert(k.clone(), sv);
            }
        }
        let env = SpecEnv {
            vars,
            olds: HashMap::new(),
            ghosts: self.ghosts,
        };
        for inv in &class.invariants {
            match speceval::eval_clause(&inv.text, &env) {
                Ok(true) => {}
                Ok(false) => {
                    return Err(Trap {
                        undef: false,
                        message: format!(
                            "class invariant of `{}` violated at `{what}`: {}",
                            class.name,
                            inv.text.replace('\n', " ")
                        ),
                        span: inv.span,
                    });
                }
                Err(um) => {
                    self.skipped.push((inv.text.replace('\n', " "), um.0));
                }
            }
        }
        Ok(())
    }

    fn exec_stmt(
        &mut self,
        stmt: &Stmt,
        frame: &mut Frame,
        locals: &mut Vec<String>,
    ) -> IResult<Flow> {
        self.burn(stmt_span(stmt))?;
        match stmt {
            Stmt::Decl { name, init, .. } => {
                if let Some(e) = init {
                    let v = self.eval_moved(e, frame)?;
                    frame.vars.insert(name.clone(), v);
                }
                Ok(Flow::Normal)
            }
            Stmt::Assign { name, value, .. } => {
                let v = self.eval_moved(value, frame)?;
                // Overwriting a place destroys what it held: the same drop
                // as at scope exit, destructor and fields included. The
                // new value goes in afterwards, so a self-assignment
                // cannot destroy what it is about to store.
                self.drop_place(&RtPlace::Local(name.clone()), frame)?;
                frame.vars.insert(name.clone(), v);
                Ok(Flow::Normal)
            }
            // `unsafe { ... }` is a marker: the block runs like any other.
            Stmt::Unsafe { body, .. } => self.exec_open_block(body, frame, locals),
            Stmt::StaticAlloc { size, ptr, res, .. } => {
                let RtVal::Int(n) = self.eval(size, frame)? else {
                    unreachable!("checked: u64 literal")
                };
                let alloc = self.raw.fresh(vec![None; n as usize]);
                frame.vars.insert(ptr.clone(), RtVal::Ptr(alloc, 0));
                frame.vars.insert(res.clone(), RtVal::Unit);
                Ok(Flow::Normal)
            }
            Stmt::SystemAlloc {
                size,
                ptr,
                res,
                release,
                ..
            } => {
                let RtVal::Int(n) = self.eval(size, frame)? else {
                    unreachable!("checked: u64 literal")
                };
                let alloc = self.raw.fresh(vec![None; n as usize]);
                frame.vars.insert(ptr.clone(), RtVal::Ptr(alloc, 0));
                frame.vars.insert(res.clone(), RtVal::Unit);
                frame.vars.insert(release.clone(), RtVal::Unit);
                Ok(Flow::Normal)
            }
            Stmt::SystemDealloc {
                ptr,
                res,
                release,
                kw_span,
            } => {
                let RtVal::Ptr(alloc, off) = self.eval(ptr, frame)? else {
                    unreachable!("checked: raw pointer")
                };
                self.eval_moved(res, frame)?;
                self.eval_moved(release, frame)?;
                let Some(al) = self.raw.allocs.get_mut(&alloc) else {
                    return Err(Trap {
                        undef: true,
                        message: format!("system_dealloc names absent allocation {alloc}"),
                        span: *kw_span,
                    });
                };
                if off != 0 || !al.live {
                    return Err(Trap {
                        undef: true,
                        message: format!("system_dealloc needs a live base pointer: {alloc}+{off}"),
                        span: *kw_span,
                    });
                }
                al.live = false;
                Ok(Flow::Normal)
            }
            // Exposure: copy the array's bytes into a fresh loan
            // allocation, run the body, copy the final bytes back, and
            // kill the allocation. Modelling it as a real copy is what
            // makes a leaked pointer observable at runtime rather than
            // silently fine (ADR 0026).
            Stmt::Expose {
                kw_span,
                array,
                mutable,
                ptr,
                res,
                body,
                ..
            } => {
                let RtVal::Arr(a) = frame.vars[array.as_str()].clone() else {
                    unreachable!("checked: u8 array")
                };
                let bytes: Vec<Option<i128>> = a.borrow().iter().map(|v| Some(*v)).collect();
                let n = bytes.len();
                let alloc = self.raw.fresh(bytes);
                frame.vars.insert(ptr.clone(), RtVal::Ptr(alloc, 0));
                // The resource has no runtime representation (ADR 0024);
                // the binding exists so the body's names resolve.
                frame.vars.insert(res.clone(), RtVal::Unit);
                // An exposure body is a scope on both sides: the loan ends
                // at the closing brace, so anything the body declared ends
                // with it (ADR 0030). `unsafe { ... }` is the other case —
                // vocabulary, no lifetime, no scope.
                let flow = self.exec_block(body, frame)?;
                let final_bytes = self
                    .raw
                    .allocs
                    .get(&alloc)
                    .map(|al| al.bytes.clone())
                    .expect("the loan allocation is ours");
                if *mutable {
                    for (i, b) in final_bytes.iter().enumerate().take(n) {
                        match b {
                            Some(v) => a.borrow_mut()[i] = *v,
                            None => {
                                return Err(Trap {
                                    undef: false,
                                    message: format!(
                                        "exposure of `{array}` ends with byte {i} \
                                         uninitialized"
                                    ),
                                    span: *kw_span,
                                });
                            }
                        }
                    }
                }
                if let Some(al) = self.raw.allocs.get_mut(&alloc) {
                    al.live = false;
                }
                frame.vars.remove(ptr.as_str());
                frame.vars.remove(res.as_str());
                Ok(flow)
            }
            Stmt::ExprStmt(e) => {
                // A discarded class value is a temporary that nothing
                // names, and it dies at the end of the statement that made
                // it. It is the one owned value with no place, so it is
                // also the one drop that cannot go through `drop_place`.
                let v = self.eval(e, frame)?;
                if let RtVal::Obj { class, fields } = v {
                    self.drop_value(class, &fields, "temporary")?;
                }
                Ok(Flow::Normal)
            }
            Stmt::Assert(clause) => {
                self.check_clause(frame, clause, None, "inline assert")?;
                Ok(Flow::Normal)
            }
            Stmt::VarDecl { name, init, .. } => {
                let v = self.eval_moved(init, frame)?;
                frame.vars.insert(name.clone(), v);
                Ok(Flow::Normal)
            }
            Stmt::FieldAssign { field, value, .. } => {
                let v = self.eval_moved(value, frame)?;
                // A field is a place like any other: overwriting it
                // destroys what it held. An `init` is the exception —
                // there is nothing there yet — and `drop_place` on an
                // uninitialized field finds nothing to do.
                self.drop_place(&RtPlace::SelfField(field.clone()), frame)?;
                let (_, fields) = frame.self_ctx.clone().expect("checked: member ctx");
                fields.borrow_mut().insert(field.clone(), v);
                Ok(Flow::Normal)
            }
            Stmt::FieldStore {
                field,
                field_span,
                index,
                value,
            } => {
                let idx = self.eval_int(index, frame)?;
                let val = self.eval_int(value, frame)?;
                let (_, fields) = frame.self_ctx.clone().expect("checked: member ctx");
                let arr = match fields.borrow().get(field.as_str()) {
                    Some(RtVal::Arr(a)) => a.clone(),
                    _ => unreachable!("checked: array field initialized"),
                };
                let len = arr.borrow().len() as i128;
                if idx < 0 || idx >= len {
                    return Err(Trap {
                        undef: false,
                        message: format!("store index out of bounds: index {idx}, length {len}"),
                        span: *field_span,
                    });
                }
                arr.borrow_mut()[idx as usize] = val;
                Ok(Flow::Normal)
            }
            Stmt::Store {
                array,
                array_span,
                index,
                value,
            } => {
                let idx = self.eval_int(index, frame)?;
                let val = self.eval_int(value, frame)?;
                let RtVal::Arr(a) = frame.vars[array.as_str()].clone() else {
                    unreachable!()
                };
                let len = a.borrow().len() as i128;
                if idx < 0 || idx >= len {
                    return Err(Trap {
                        undef: false,
                        message: format!("store index out of bounds: index {idx}, length {len}"),
                        span: *array_span,
                    });
                }
                a.borrow_mut()[idx as usize] = val;
                Ok(Flow::Normal)
            }
            Stmt::Return { value, .. } => {
                // Returning a place is a move: the value leaves with the
                // caller, so the scopes unwinding behind it must not find
                // it still sitting in its source and destroy it.
                let v = match value {
                    Some(e) => self.eval_moved(e, frame)?,
                    None => RtVal::Unit,
                };
                Ok(Flow::Return(v))
            }
            Stmt::If {
                cond,
                then_block,
                else_block,
            } => {
                if self.eval_bool(cond, frame)? {
                    self.exec_block(then_block, frame)
                } else if let Some(eb) = else_block {
                    self.exec_block(eb, frame)
                } else {
                    Ok(Flow::Normal)
                }
            }
            Stmt::While {
                cond,
                invariants,
                variant,
                kw_span,
                body,
            } => {
                let mut prev_variant: Option<i128> = None;
                loop {
                    self.burn(*kw_span)?;
                    for inv in invariants {
                        self.check_loop_clause(frame, inv, "loop invariant")?;
                    }
                    if !self.eval_bool(cond, frame)? {
                        break;
                    }
                    if let Some(v) = variant {
                        if let Some(val) = self.variant_value(frame, v) {
                            if val < 0 {
                                return Err(Trap {
                                    undef: false,
                                    message: format!(
                                        "loop variant is negative ({val}): {}",
                                        v.text
                                    ),
                                    span: v.span,
                                });
                            }
                            if let Some(prev) = prev_variant {
                                if val >= prev {
                                    return Err(Trap {
                                        undef: false,
                                        message: format!(
                                            "loop variant did not decrease ({prev} → {val}): {}",
                                            v.text
                                        ),
                                        span: v.span,
                                    });
                                }
                            }
                            prev_variant = Some(val);
                        }
                    }
                    match self.exec_block(body, frame)? {
                        Flow::Normal => {}
                        ret => return Ok(ret),
                    }
                }
                Ok(Flow::Normal)
            }
        }
    }

    /// Evaluate a variant measure numerically by evaluating the program
    /// expression through the spec evaluator (variants are Int-valued).
    fn variant_value(&mut self, frame: &Frame, clause: &crate::scan::Clause) -> Option<i128> {
        let mut vars: HashMap<String, SpecVal> = HashMap::new();
        for (name, v) in &frame.vars {
            if let Some(sv) = spec_of(v) {
                vars.insert(name.clone(), sv);
            }
        }
        let env = SpecEnv {
            vars,
            olds: frame.olds.clone(),
            ghosts: self.ghosts,
        };
        match speceval::eval_int_expr(&clause.text, &env) {
            Ok(n) => Some(n),
            Err(um) => {
                self.skipped.push((clause.text.replace('\n', " "), um.0));
                None
            }
        }
    }

    fn construct(
        &mut self,
        ci: usize,
        init_name: &str,
        args: Vec<RtVal>,
        span: crate::span::Span,
    ) -> IResult<RtVal> {
        self.burn(span)?;
        let class = self.classes[ci].clone();
        let ifn = class
            .inits
            .iter()
            .find(|i| i.name == init_name)
            .expect("checked: init exists")
            .clone();
        let fields = Rc::new(RefCell::new(HashMap::new()));
        let mut frame = Frame {
            vars: HashMap::new(),
            entry_scalars: HashMap::new(),
            olds: HashMap::new(),
            self_ctx: Some((ci, fields.clone())),
        };
        for (p, v) in ifn.params.iter().zip(args) {
            match (&v, p.ty) {
                (obj @ RtVal::Obj { .. }, Ty::ClassRef(_, Mutability::Mut)) => {
                    if let Some(sv) = spec_of(obj) {
                        frame.olds.insert(p.name.clone(), sv);
                    }
                }
                _ => {
                    frame.entry_scalars.insert(p.name.clone(), v.clone());
                }
            }
            frame.vars.insert(p.name.clone(), v);
        }
        for pre in &ifn.pres {
            self.check_clause(
                &frame,
                pre,
                None,
                &format!("pre of `{}::{}`", class.name, ifn.name),
            )?;
        }
        self.exec_block(&ifn.body, &mut frame)?;
        for post in &ifn.posts {
            self.check_clause(
                &frame,
                post,
                None,
                &format!("post of `{}::{}`", class.name, ifn.name),
            )?;
        }
        self.check_invariants_at(
            &class,
            &fields,
            &format!("{}::{} exit", class.name, ifn.name),
        )?;
        self.drop_owned_params(&ifn.params, &mut frame)?;
        Ok(RtVal::Obj { class: ci, fields })
    }

    fn invoke(
        &mut self,
        ci: usize,
        method: &str,
        fields: Rc<RefCell<HashMap<String, RtVal>>>,
        args: Vec<RtVal>,
    ) -> IResult<RtVal> {
        let class = self.classes[ci].clone();
        let m = class
            .methods
            .iter()
            .find(|m| m.f.name == method)
            .expect("checked: method exists")
            .clone();
        let mut frame = Frame {
            vars: HashMap::new(),
            entry_scalars: HashMap::new(),
            olds: HashMap::new(),
            self_ctx: Some((ci, fields.clone())),
        };
        // Entry snapshot for `old self` (and post-checking of by-value
        // params).
        let entry_obj = RtVal::Obj {
            class: ci,
            fields: Rc::new(RefCell::new(
                fields
                    .borrow()
                    .iter()
                    .map(|(k, v)| (k.clone(), deep_copy(v)))
                    .collect(),
            )),
        };
        if let Some(sv) = spec_of(&entry_obj) {
            frame.olds.insert("self".into(), sv);
        }
        for (p, v) in m.f.params.iter().zip(args) {
            match (&v, p.ty) {
                // `&mut C`: the borrow shares storage with the caller, so
                // `old p` needs the value it had at entry. `spec_of` copies.
                (obj @ RtVal::Obj { .. }, Ty::ClassRef(_, Mutability::Mut)) => {
                    if let Some(sv) = spec_of(obj) {
                        frame.olds.insert(p.name.clone(), sv);
                    }
                }
                _ => {
                    frame.entry_scalars.insert(p.name.clone(), v.clone());
                }
            }
            frame.vars.insert(p.name.clone(), v);
        }
        for pre in &m.f.pres {
            self.check_clause(
                &frame,
                pre,
                None,
                &format!("pre of `{}::{method}`", class.name),
            )?;
        }
        let flow = self.exec_block(&m.f.body, &mut frame)?;
        let result = match flow {
            Flow::Return(v) => v,
            Flow::Normal => RtVal::Unit,
        };
        if m.self_kind == SelfKind::Mut {
            self.check_invariants_at(&class, &fields, &format!("{}::{method} exit", class.name))?;
        }
        for post in &m.f.posts {
            self.check_clause(
                &frame,
                post,
                Some(&result),
                &format!("post of `{}::{method}`", class.name),
            )?;
        }
        self.drop_owned_params(&m.f.params, &mut frame)?;
        Ok(result)
    }

    fn eval_int(&mut self, e: &Expr, frame: &mut Frame) -> IResult<i128> {
        match self.eval(e, frame)? {
            RtVal::Int(n) => Ok(n),
            _ => unreachable!("checked: int expression"),
        }
    }

    fn eval_bool(&mut self, e: &Expr, frame: &mut Frame) -> IResult<bool> {
        match self.eval(e, frame)? {
            RtVal::Bool(b) => Ok(b),
            _ => unreachable!("checked: bool expression"),
        }
    }

    fn eval(&mut self, e: &Expr, frame: &mut Frame) -> IResult<RtVal> {
        self.burn(e.span)?;
        match &e.kind {
            ExprKind::IntLit(n) => Ok(RtVal::Int(*n)),
            ExprKind::BoolLit(b) => Ok(RtVal::Bool(*b)),
            ExprKind::Var(name) => Ok(frame.vars[name.as_str()].clone()),
            // Resource transformations redistribute authority, which is
            // a static notion: at runtime there is nothing to move and
            // nothing to return (ADR 0024). `posix_world` is the
            // exception: the *script* it selects is real runtime state,
            // and a test controlling it is what "scripted world" means.
            ExprKind::ResOp { op, args, .. } => {
                match op {
                    ResOp::TestWorld => {
                        let script = self.eval_int(&args[0], frame)?;
                        self.world = Some(PosixWorld::scripted(script));
                    }
                    // Adoption spends the world's claim on a descriptor.
                    // The VC is what makes a second adoption unreachable;
                    // this is the monitor saying so independently, the
                    // same two layers the raw operations have.
                    ResOp::OpenFileOf => {
                        let fd = self.eval_int(&args[1], frame)?;
                        if let Some(w) = &mut self.world {
                            if fd < 0 || fd >= w.fds {
                                return Err(Trap {
                                    undef: false,
                                    message: format!(
                                        "open_file: descriptor {fd} is not open in this world"
                                    ),
                                    span: e.span,
                                });
                            }
                            if !w.claimed.insert(fd) {
                                return Err(Trap {
                                    undef: false,
                                    message: format!(
                                        "open_file: descriptor {fd}'s authority has already \
                                         been handed out"
                                    ),
                                    span: e.span,
                                });
                            }
                        }
                    }
                    _ => {}
                }
                Ok(RtVal::Unit)
            }
            // The raw operations. Each classification here must match the
            // machine's: a trap is a trap, and everything the SVM calls
            // `undef` is a trap with a precise message — the reference
            // interpreter may say *which* rule was broken while agreeing
            // on the outcome class (ADR 0025).
            ExprKind::RawOp { op, args, .. } => {
                let vals: Vec<RtVal> = {
                    let mut vs = Vec::with_capacity(args.len());
                    for a in args {
                        vs.push(self.eval(a, frame)?);
                    }
                    vs
                };
                let ptr_at = |i: usize| match vals[i] {
                    RtVal::Ptr(a, o) => (a, o),
                    _ => unreachable!("checked: raw<u8> argument"),
                };
                let int_at = |i: usize| match vals[i] {
                    RtVal::Int(n) => n,
                    _ => unreachable!("checked: integer argument"),
                };
                // Every way a raw operation can fail is the machine's
                // `undef`: the static semantics is what makes these
                // unreachable, so there is no defined runtime behavior to
                // trap into (ADR 0025).
                let bad = |msg: String| Trap {
                    undef: true,
                    message: msg,
                    span: e.span,
                };
                match op {
                    RawOp::Offset => {
                        let (a, o) = ptr_at(0);
                        Ok(RtVal::Ptr(a, o + int_at(1)))
                    }
                    RawOp::Load8 => {
                        let (a, o) = ptr_at(0);
                        match self.raw.live_at(a, o).map(|al| al.bytes[o as usize]) {
                            Some(Some(b)) => Ok(RtVal::Int(b)),
                            Some(None) => Err(bad(format!(
                                "raw_load8 reads uninitialized byte {o} of allocation {a}"
                            ))),
                            None => Err(bad(format!(
                                "raw_load8 out of bounds or after free: {a}+{o}"
                            ))),
                        }
                    }
                    RawOp::Store8 => {
                        let (a, o) = ptr_at(0);
                        let w = int_at(1);
                        if self.raw.live_at(a, o).is_none() {
                            return Err(bad(format!(
                                "raw_store8 out of bounds or after free: {a}+{o}"
                            )));
                        }
                        self.raw
                            .allocs
                            .get_mut(&a)
                            .expect("live_at checked")
                            .bytes[o as usize] = Some(w);
                        Ok(RtVal::Unit)
                    }
                    RawOp::Copy => {
                        let (sa, so) = ptr_at(0);
                        let (da, do_) = ptr_at(1);
                        let n = int_at(2);
                        for i in 0..n {
                            let b = match self
                                .raw
                                .live_at(sa, so + i)
                                .map(|al| al.bytes[(so + i) as usize])
                            {
                                Some(Some(b)) => b,
                                Some(None) => {
                                    return Err(bad(format!(
                                        "raw_copy_nonoverlapping reads uninitialized byte \
                                         {} of allocation {sa}",
                                        so + i
                                    )));
                                }
                                None => {
                                    return Err(bad(format!(
                                        "raw_copy_nonoverlapping source out of bounds: \
                                         {sa}+{}",
                                        so + i
                                    )));
                                }
                            };
                            if self.raw.live_at(da, do_ + i).is_none() {
                                return Err(bad(format!(
                                    "raw_copy_nonoverlapping destination out of bounds: \
                                     {da}+{}",
                                    do_ + i
                                )));
                            }
                            self.raw
                                .allocs
                                .get_mut(&da)
                                .expect("live_at checked")
                                .bytes[(do_ + i) as usize] = Some(b);
                        }
                        Ok(RtVal::Unit)
                    }
                    RawOp::IntoCellU64 => {
                        let (a, o) = ptr_at(0);
                        let layout = IntTy::U64.layout();
                        if o % layout.align != 0 {
                            return Err(bad(format!(
                                "raw_into_cell_u64 needs 8-byte alignment: {a}+{o}"
                            )));
                        }
                        for i in 0..layout.size {
                            if self.raw.live_at(a, o + i).is_none() {
                                return Err(bad(format!(
                                    "raw_into_cell_u64 needs eight raw bytes at {a}+{o}"
                                )));
                            }
                        }
                        self.raw
                            .allocs
                            .get_mut(&a)
                            .expect("live_at checked")
                            .cells_u64
                            .insert(o, None);
                        Ok(RtVal::Unit)
                    }
                    RawOp::FromCellU64 => {
                        let (a, o) = ptr_at(0);
                        let layout = IntTy::U64.layout();
                        let al = self.raw.allocs.get_mut(&a).ok_or_else(|| {
                            bad(format!("raw_from_cell_u64 names absent allocation {a}"))
                        })?;
                        if !al.live {
                            return Err(bad(format!(
                                "raw_from_cell_u64 names dead allocation {a}"
                            )));
                        }
                        match al.cells_u64.get(&o) {
                            Some(None) => {
                                al.cells_u64.remove(&o);
                                for i in 0..layout.size {
                                    al.bytes[(o + i) as usize] = Some(0);
                                }
                                Ok(RtVal::Unit)
                            }
                            _ => Err(bad(format!(
                                "raw_from_cell_u64 needs an uninitialized cell at {a}+{o}"
                            ))),
                        }
                    }
                    RawOp::CellInitU64 => {
                        let (a, o) = ptr_at(0);
                        let w = int_at(1);
                        let al = self.raw.allocs.get_mut(&a).ok_or_else(|| {
                            bad(format!("raw_cell_init_u64 names absent allocation {a}"))
                        })?;
                        if !al.live {
                            return Err(bad(format!(
                                "raw_cell_init_u64 names dead allocation {a}"
                            )));
                        }
                        match al.cells_u64.get_mut(&o) {
                            Some(state @ None) => {
                                *state = Some(w);
                                Ok(RtVal::Unit)
                            }
                            _ => Err(bad(format!(
                                "raw_cell_init_u64 needs an uninitialized cell at {a}+{o}"
                            ))),
                        }
                    }
                    RawOp::CellReadU64 => {
                        let (a, o) = ptr_at(0);
                        match self
                            .raw
                            .allocs
                            .get(&a)
                            .filter(|al| al.live)
                            .and_then(|al| al.cells_u64.get(&o))
                        {
                            Some(Some(w)) => Ok(RtVal::Int(*w)),
                            _ => Err(bad(format!(
                                "raw_cell_read_u64 needs an initialized cell at {a}+{o}"
                            ))),
                        }
                    }
                    RawOp::CellTakeU64 => {
                        let (a, o) = ptr_at(0);
                        let al = self.raw.allocs.get_mut(&a).ok_or_else(|| {
                            bad(format!("raw_cell_take_u64 names absent allocation {a}"))
                        })?;
                        if !al.live {
                            return Err(bad(format!(
                                "raw_cell_take_u64 names dead allocation {a}"
                            )));
                        }
                        match al.cells_u64.get_mut(&o) {
                            Some(state @ Some(_)) => {
                                let w = state.take().expect("matched initialized cell");
                                Ok(RtVal::Int(w))
                            }
                            _ => Err(bad(format!(
                                "raw_cell_take_u64 needs an initialized cell at {a}+{o}"
                            ))),
                        }
                    }
                    RawOp::CellDropU64 => {
                        let (a, o) = ptr_at(0);
                        let al = self.raw.allocs.get_mut(&a).ok_or_else(|| {
                            bad(format!("raw_cell_drop_u64 names absent allocation {a}"))
                        })?;
                        if !al.live {
                            return Err(bad(format!(
                                "raw_cell_drop_u64 names dead allocation {a}"
                            )));
                        }
                        match al.cells_u64.get_mut(&o) {
                            Some(state @ Some(_)) => {
                                *state = None;
                                Ok(RtVal::Unit)
                            }
                            _ => Err(bad(format!(
                                "raw_cell_drop_u64 needs an initialized cell at {a}+{o}"
                            ))),
                        }
                    }
                }
            }

            ExprKind::Len { array } => {
                let RtVal::Arr(a) = &frame.vars[array.as_str()] else {
                    unreachable!()
                };
                Ok(RtVal::Int(a.borrow().len() as i128))
            }
            ExprKind::Index { array, index, .. } => {
                let idx = self.eval_int(index, frame)?;
                let RtVal::Arr(a) = &frame.vars[array.as_str()] else {
                    unreachable!()
                };
                let arr = a.borrow();
                if idx < 0 || idx >= arr.len() as i128 {
                    return Err(Trap {
                        undef: false,
                        message: format!("index out of bounds: index {idx}, length {}", arr.len()),
                        span: e.span,
                    });
                }
                Ok(RtVal::Int(arr[idx as usize]))
            }
            ExprKind::IsSome { operand } => {
                let RtVal::Opt(o) = self.eval(operand, frame)? else {
                    unreachable!("checked: option operand")
                };
                Ok(RtVal::Bool(o.is_some()))
            }
            ExprKind::OptValue { operand } => {
                let RtVal::Opt(o) = self.eval(operand, frame)? else {
                    unreachable!("checked: option operand")
                };
                match o {
                    Some(v) => Ok(RtVal::Int(v)),
                    None => Err(Trap {
                        undef: false,
                        message: "`.value` of an empty option".into(),
                        span: e.span,
                    }),
                }
            }
            ExprKind::TraitCall { .. } => {
                unreachable!("trait calls exist only in templates, never executed")
            }
            ExprKind::ClassField { obj, field, .. } => {
                let RtVal::Obj { fields, .. } = frame.vars[obj.as_str()].clone() else {
                    unreachable!("checked: class receiver")
                };
                let v = fields.borrow()[field.as_str()].clone();
                Ok(v)
            }
            ExprKind::ClassFieldLen { obj, field } => {
                let RtVal::Obj { fields, .. } = frame.vars[obj.as_str()].clone() else {
                    unreachable!("checked: class receiver")
                };
                let RtVal::Arr(a) = fields.borrow()[field.as_str()].clone() else {
                    unreachable!("checked: array field")
                };
                let n = a.borrow().len() as i128;
                Ok(RtVal::Int(n))
            }
            ExprKind::ClassFieldIndex {
                obj, field, index, ..
            } => {
                let RtVal::Obj { fields, .. } = frame.vars[obj.as_str()].clone() else {
                    unreachable!("checked: class receiver")
                };
                let RtVal::Arr(a) = fields.borrow()[field.as_str()].clone() else {
                    unreachable!("checked: array field")
                };
                let idx = self.eval_int(index, frame)?;
                let arr = a.borrow();
                if idx < 0 || idx as usize >= arr.len() {
                    return Err(Trap {
                        undef: false,
                        message: format!("index out of bounds: index {idx}, length {}", arr.len()),
                        span: e.span,
                    });
                }
                Ok(RtVal::Int(arr[idx as usize]))
            }
            ExprKind::Widen { arg, .. } => self.eval(arg, frame),
            ExprKind::Narrow { target, arg } => {
                let v = self.eval_int(arg, frame)?;
                if v < target.min() || v > target.max() {
                    return Err(Trap {
                        undef: false,
                        message: format!(
                            "narrow out of range: {v} does not fit in `{}`",
                            target.name()
                        ),
                        span: e.span,
                    });
                }
                Ok(RtVal::Int(v))
            }
            ExprKind::SomeE(inner) => {
                let v = self.eval_int(inner, frame)?;
                Ok(RtVal::Opt(Some(v)))
            }
            ExprKind::NoneE => Ok(RtVal::Opt(None)),
            ExprKind::ArrayLit(elems) => {
                let mut v = Vec::with_capacity(elems.len());
                for el in elems {
                    v.push(self.eval_int(el, frame)?);
                }
                Ok(RtVal::Arr(Rc::new(RefCell::new(v))))
            }
            ExprKind::Borrow { array, field, .. } => {
                let base = if array == "self" {
                    let (class, fields) = frame.self_ctx.clone().expect("checked: member ctx");
                    RtVal::Obj { class, fields }
                } else {
                    frame.vars[array.as_str()].clone()
                };
                match field {
                    // `&x.f` — borrow the field's value, not the base
                    // (ADR 0020). Sharing the Rc is the borrow.
                    Some(f) => {
                        let RtVal::Obj { fields, .. } = base else {
                            unreachable!("checked: class base")
                        };
                        let v = fields.borrow()[f.as_str()].clone();
                        Ok(v)
                    }
                    None => Ok(base),
                }
            }
            ExprKind::AllocArray { len, init, .. } => {
                let n = self.eval_int(len, frame)?;
                let v0 = self.eval_int(init, frame)?;
                // Defined allocation-failure behavior: the named OOM trap.
                if n < 0 || n > 50_000_000 {
                    return Err(Trap {
                        undef: false,
                        message: format!("OOM trap: alloc_array of length {n}"),
                        span: e.span,
                    });
                }
                Ok(RtVal::Arr(Rc::new(RefCell::new(vec![v0; n as usize]))))
            }
            ExprKind::SelfField { field } => {
                let (_, fields) = frame.self_ctx.clone().expect("checked: member ctx");
                let v = fields
                    .borrow()
                    .get(field.as_str())
                    .cloned()
                    .expect("checked: field initialized");
                Ok(v)
            }
            ExprKind::SelfFieldLen { field } => {
                let (_, fields) = frame.self_ctx.clone().expect("checked: member ctx");
                let arr = match fields.borrow().get(field.as_str()) {
                    Some(RtVal::Arr(a)) => a.clone(),
                    _ => unreachable!("checked: array field"),
                };
                let n = arr.borrow().len() as i128;
                Ok(RtVal::Int(n))
            }
            ExprKind::SelfFieldIndex { field, index } => {
                let idx = self.eval_int(index, frame)?;
                let (_, fields) = frame.self_ctx.clone().expect("checked: member ctx");
                let arr = match fields.borrow().get(field.as_str()) {
                    Some(RtVal::Arr(a)) => a.clone(),
                    _ => unreachable!("checked: array field"),
                };
                let len = arr.borrow().len() as i128;
                if idx < 0 || idx >= len {
                    return Err(Trap {
                        undef: false,
                        message: format!("index out of bounds: index {idx}, length {len}"),
                        span: e.span,
                    });
                }
                let v = arr.borrow()[idx as usize];
                Ok(RtVal::Int(v))
            }
            ExprKind::CtorCall {
                class, init, args, ..
            } => {
                let ci = self
                    .classes
                    .iter()
                    .position(|c| c.name == *class)
                    .expect("checked: class exists");
                let mut vals = Vec::with_capacity(args.len());
                for a in args {
                    vals.push(self.eval_moved(a, frame)?);
                }
                self.construct(ci, init, vals, e.span)
            }
            ExprKind::MethodCall {
                recv, method, args, ..
            } => {
                let RtVal::Obj { class, fields } = frame.vars[recv.as_str()].clone() else {
                    unreachable!("checked: class receiver")
                };
                let mut vals = Vec::with_capacity(args.len());
                for a in args {
                    vals.push(self.eval_moved(a, frame)?);
                }
                self.invoke(class, method, fields, vals)
            }
            ExprKind::Unary { op, operand } => match op {
                UnOp::Not => {
                    let b = self.eval_bool(operand, frame)?;
                    Ok(RtVal::Bool(!b))
                }
                UnOp::Neg => {
                    let v = self.eval_int(operand, frame)?;
                    let Ty::Int(it) = e.ty.unwrap() else {
                        unreachable!()
                    };
                    self.check_range(-v, it, e, "negation")?;
                    Ok(RtVal::Int(-v))
                }
            },
            ExprKind::Binary { op, lhs, rhs, .. } => {
                if matches!(op, BinOp::And | BinOp::Or) {
                    let l = self.eval_bool(lhs, frame)?;
                    // Short-circuit, matching the VC semantics.
                    return Ok(RtVal::Bool(match op {
                        BinOp::And => l && self.eval_bool(rhs, frame)?,
                        BinOp::Or => l || self.eval_bool(rhs, frame)?,
                        _ => unreachable!(),
                    }));
                }
                let a = self.eval_int(lhs, frame)?;
                let b = self.eval_int(rhs, frame)?;
                if op.is_comparison() {
                    return Ok(RtVal::Bool(match op {
                        BinOp::Lt => a < b,
                        BinOp::Le => a <= b,
                        BinOp::Gt => a > b,
                        BinOp::Ge => a >= b,
                        BinOp::Eq => a == b,
                        BinOp::Ne => a != b,
                        _ => unreachable!(),
                    }));
                }
                let Ty::Int(it) = e.ty.unwrap() else {
                    unreachable!()
                };
                let val = match op {
                    BinOp::Add => a + b,
                    BinOp::Sub => a - b,
                    BinOp::Mul => a.checked_mul(b).ok_or_else(|| Trap {
                        undef: false,
                        message: "multiplication exceeds i128 (ghost width)".into(),
                        span: e.span,
                    })?,
                    BinOp::Div | BinOp::Rem => {
                        if b == 0 {
                            return Err(Trap {
                                undef: false,
                                message: "division by zero".into(),
                                span: rhs.span,
                            });
                        }
                        if *op == BinOp::Div && it.signed() && a == it.min() && b == -1 {
                            return Err(Trap {
                                undef: false,
                                message: format!(
                                    "Euclidean quotient overflows: {}.min / -1",
                                    it.name()
                                ),
                                span: e.span,
                            });
                        }
                        if *op == BinOp::Div {
                            a.div_euclid(b)
                        } else {
                            a.rem_euclid(b)
                        }
                    }
                    _ => unreachable!(),
                };
                if matches!(op, BinOp::Add | BinOp::Sub | BinOp::Mul) {
                    self.check_range(val, it, e, op.symbol())?;
                }
                Ok(RtVal::Int(val))
            }
            ExprKind::Call { callee, args, .. } => {
                let f = self.fns[callee.as_str()];
                // Resource arguments are erased: authority is a static
                // notion, so it has no runtime representation to pass and
                // the callee's runtime signature does not have the
                // parameter at all (ADR 0024). Both sides drop the same
                // positions, so the remaining ones still line up.
                // A by-value class argument is a *move*, and moves clear
                // their source place — `eval_moved` is the same operation
                // the other transfers use.
                let mut vals = Vec::with_capacity(args.len());
                for (a, p) in args.iter().zip(&f.params) {
                    if p.ty.is_resource() {
                        continue;
                    }
                    vals.push(self.eval_moved(a, frame)?);
                }
                if f.extern_info.is_some() {
                    // The foreign implementation receives only ABI values:
                    // resources were already dropped above.
                    return self.call_extern(f, vals, e.span);
                }
                self.call(f, vals)
            }
        }
    }

    fn check_range(&self, val: i128, it: IntTy, e: &Expr, what: &str) -> IResult<()> {
        if val < it.min() || val > it.max() {
            let src = &self.source[e.span.start..e.span.end.min(self.source.len())];
            return Err(Trap {
                undef: false,
                message: format!(
                    "overflow: `{src}` = {val} does not fit in `{}` ({what})",
                    it.name()
                ),
                span: e.span,
            });
        }
        Ok(())
    }

    fn burn(&mut self, span: crate::span::Span) -> IResult<()> {
        if self.fuel == 0 {
            return Err(Trap {
                undef: false,
                message: "fuel exhausted (runaway loop or recursion?)".into(),
                span,
            });
        }
        self.fuel -= 1;
        Ok(())
    }
}

fn deep_copy(v: &RtVal) -> RtVal {
    match v {
        RtVal::Arr(a) => RtVal::Arr(Rc::new(RefCell::new(a.borrow().clone()))),
        RtVal::Obj { class, fields } => RtVal::Obj {
            class: *class,
            fields: Rc::new(RefCell::new(
                fields
                    .borrow()
                    .iter()
                    .map(|(k, v)| (k.clone(), deep_copy(v)))
                    .collect(),
            )),
        },
        other => other.clone(),
    }
}

fn spec_of(v: &RtVal) -> Option<SpecVal> {
    Some(match v {
        RtVal::Int(n) => SpecVal::Int(*n),
        RtVal::Bool(b) => SpecVal::Bool(*b),
        RtVal::Arr(a) => SpecVal::Arr(a.borrow().clone()),
        RtVal::Opt(o) => SpecVal::Opt(*o),
        RtVal::Obj { fields, .. } => SpecVal::Obj(
            fields
                .borrow()
                .iter()
                .filter_map(|(k, v)| spec_of(v).map(|sv| (k.clone(), sv)))
                .collect(),
        ),
        // A pointer has no specification value: contracts speak about
        // views, and a view is not something the monitor can see.
        RtVal::Ptr(..) => return None,
        RtVal::Unit => return None,
    })
}

fn stmt_span(stmt: &Stmt) -> crate::span::Span {
    match stmt {
        Stmt::Unsafe { kw_span, .. }
        | Stmt::StaticAlloc { kw_span, .. }
        | Stmt::SystemAlloc { kw_span, .. }
        | Stmt::SystemDealloc { kw_span, .. }
        | Stmt::Expose { kw_span, .. } => *kw_span,
        Stmt::Decl { name_span, .. } | Stmt::Assign { name_span, .. } => *name_span,
        Stmt::Assert(c) => c.line_span,
        Stmt::If { cond, .. } => cond.span,
        Stmt::While { kw_span, .. } => *kw_span,
        Stmt::Return { span, .. } => *span,
        Stmt::Store { array_span, .. } => *array_span,
        Stmt::ExprStmt(e) => e.span,
        Stmt::VarDecl { name_span, .. } => *name_span,
        Stmt::FieldAssign { field_span, .. } => *field_span,
        Stmt::FieldStore { field_span, .. } => *field_span,
    }
}
