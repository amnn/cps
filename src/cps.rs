//! # CPS
//!
//! Continuation-passing style conversion on a direct-style de-Bruijn indexed input AST.  The
//! resulting representation of the program is simplified w.r.t. its input in the following ways:
//!
//! - Complex expressions are replaced by a sequence of simple expressions (with no nesting) that
//!   bind intermediate results.  Simple expressions are easier to lower into machine operations,
//!   and the sequencing makes evaluation order explicit.
//!
//! - Lambdas can no longer appear as expressions, they must first be bound (given a "name"), and
//!   referred to by that name.
//!
//! - References to local variables are no longer expressions in their own right -- they can only
//!   appear as inputs to other simple expressions.
//!
//!
//! ## Bindings
//!
//! A `Var` in the output AST can refer to either a binding in the input AST, or a newly introduced
//! binding for a continuation parameter, or an intermediate result.  These references are still in
//! terms of de-Bruijn indices but they will be renumbered relative to the input AST to account for
//! the new bindings that the pass introduces.
//!
//! `Command`s implicitly introduce bindings for following commands, and lambdas nested within those
//! commands.  Most commands introduce only one binding -- for their result -- but `Fix` can
//! introduce multiple (one for each expression being bound).
//!
//!
//! ## Administrative Redexes
//!
//! To avoid a representation that includes many administrative redexes, a program is represented by
//! a sequence of `Command`s followed by a continuation call where commands are simple operations
//! that bind new values (references to globals, introducing lambdas, constructing and destructing
//! tuples) without introducing control flow.
//!
//! The continuation call at the end of a program can either be from an existing application in the
//! input AST, or the application of a newly introduced continuation parameter (corresponding to a
//! return of a value introduced by a command in the input AST).
//!
//! This also means that the pass avoids introducing a redundant continuation (and another
//! administrative redex) to return the result of another function application.  Instead, it
//! preserves the function call in question as the tail call, and updates its continuation
//! parameter.
//!
//!
//! ## HALT
//!
//! The pass introduces a special global variable: "HALT" to represent the continuation to exit the
//! program with its return value (Like the return value of `main`).

use std::{fmt, iter};

use crate::naming as N;

/// An AST contains a sequence of commands which bind temporaries, followed by a function
/// application (the last two fields), either from a function call in the input AST, or a
/// continuation call.
#[derive(PartialEq, Eq, Debug)]
pub(crate) struct Ast(Vec<Cmd>, Var, Vec<Var>);

/// Variables are represented by de-Bruijn indices.  They are used to refer to both function
/// parameters and locals/temporaries.
#[derive(Copy, Clone, PartialEq, Eq)]
pub(crate) struct Var(usize);

/// Commands are the "right-hand side" of binders, they produce values that get bound to variables
/// in the [Ast].
#[derive(PartialEq, Eq)]
pub(crate) enum Cmd {
    /// Load a free/global variable.
    Free(String),

    /// Bind co-recursive functions.  This command binds multiple values (as many as the lambdas it
    /// binds) and they are bound within each lambda, and for the continuation of the [Ast].
    Fix(Vec<Lam>),

    /// Construct a tuple.
    Record(Vec<Var>),

    /// Select an element from a tuple.
    Select(Var, usize),
}

/// A lambda is defined by the number of parameters it has, and its body.
#[derive(PartialEq, Eq)]
pub(crate) struct Lam(usize, Ast);

/// Bound variables are represented by an index counting down from the first binding (as opposed to
/// Vars which is a de-Bruijn index and counts up from the last binding).  These are used to refer
/// to a binding before it is known from where in the Ast it will be referred (and how many other
/// bindings exist between this variable's binding and its reference).
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
struct BVar(usize);

#[derive(Debug)]
pub(crate) struct Cps {
    /// Partially built functions, nested in successive lexical scopes in the contified AST.  New
    /// commands are appended to the top-most frame, and frames are popped off the stack and
    /// converted into `Lam`s when they have been completed.
    frames: Vec<Frame>,

    /// A mapping from local variables in the input AST to bound variables in the contified AST
    /// (used when contifying local variables in the input AST).
    frm_vars: Vec<BVar>,
}

/// Frames correspond to a function in the contified AST that has been partially built.
#[derive(Debug)]
struct Frame {
    /// If this frame is a continuation function, its caller is included here.
    caller: Option<(BVar, Vec<BVar>)>,

    /// Number of local variables in the input AST before entering this frame.
    frm_bp: usize,

    /// Number of local variables in the contified AST before entering this frame.
    cps_bp: usize,

    /// Top of the local variable stack in the contified AST, so far.
    cps_sp: usize,

    /// Number of parameters in the contified AST (i.e. includes continuation parameters).
    params: usize,

    /// Local commands being accumulated for the body of this function, so far.
    locals: Vec<Cmd>,
}

impl Cps {
    /// Entrypoint: convert an input AST into a contified AST.
    pub(crate) fn convert(from: N::Ast) -> Ast {
        let mut cps = Cps {
            frames: vec![],
            frm_vars: vec![],
        };

        // Introduce a special frame to hold a distinguished `HALT` free variable -- the "final"
        // continuation.
        cps.enter(0, 0, None);
        let halt = cps.push(Cmd::Free("HALT".to_owned()))[0];

        cps.body(from, halt).1
    }

    /// Create a contified lambda with body translated from AST `from`. `k` is the parameter
    /// containing the continuation that the lambda should return to.  Assumes that the lambda's
    /// frame has already been set-up, before `body` is called.
    fn body(&mut self, from: N::Ast, k: BVar) -> Lam {
        // If the body is already a function application, then avoid creating a redundant
        // continuation just to call `k` with the result of application: Use the function being
        // called in `from` as the continuation.
        let (mut k, mut xs) = if let N::Ast::App(f, xs) = from {
            (
                self.bind(*f),
                xs.into_iter()
                    .map(|x| self.bind(x))
                    .chain(iter::once(k))
                    .collect(),
            )
        } else {
            (k, vec![self.bind(from)])
        };

        // Translating `from` may have pushed multiple frames, keep exiting out of them as long as
        // they have a caller, which means they are a continuation frame.
        loop {
            let frame = self.exit();

            // End the frame with the current continuation
            let kv = frame.refer(k);
            let vs: Vec<_> = xs.into_iter().map(|x| frame.refer(x)).collect();

            let Frame {
                caller,
                params,
                locals,
                ..
            } = frame;

            let mut prog = Lam(params, Ast(locals, kv, vs));
            if let Some((f, mut ys)) = caller {
                // This frame has a caller, so it is the continuation of some other function
                // application.  Bind the lambda to use as that continuation, and keep popping.
                // Its param count also needs decrementing so that the slot reserved for the
                // self-reference (introduced by the `Fix` command), is not double-counted.
                debug_assert_eq!(prog.0, 2);
                prog.0 = 1;

                ys.push(self.push(Cmd::Fix(vec![prog]))[0]);
                (k, xs) = (f, ys);
            } else {
                return prog;
            }
        }
    }

    /// Translate `from`, accumulating the intermediate results in `self`.  Returns the bound
    /// variable used to refer to the result corresponding to `from`.
    fn bind(&mut self, from: N::Ast) -> BVar {
        use Cmd as C;
        match from {
            N::Ast::Free(x) => self.push(C::Free(x.to_string()))[0],
            N::Ast::Var(ix) => self.frm_var(ix),

            N::Ast::Let(binds, body) => {
                // self-bindings
                self.enter(binds.len(), 0, None);

                let functions: Vec<_> = binds.into_iter().map(|l| self.lambda(l)).collect();

                self.exit();

                // Re-establish self-bindings so `body` can reference them.
                let locals = self.push(C::Fix(functions));
                self.frm_vars.extend(locals);

                self.bind(*body)
            }

            N::Ast::Lam(l) => {
                // Dummy scope, for the lambda's self-reference.
                self.enter(0, 1, None);
                let function = self.lambda(*l);
                self.exit();

                self.push(C::Fix(vec![function]))[0]
            }

            N::Ast::App(f, xs) => {
                let f = self.bind(*f);
                let vs: Vec<_> = xs.into_iter().map(|x| self.bind(x)).collect();

                // Enter continuation, reserving two extra variables: The first is an implicit
                // binding for the continuation itself (because we will bind it using `Fix`), and
                // the second is for the continuation parameter.
                self.enter(0, 2, Some((f, vs)));
                self.cps_var(1)
            }

            N::Ast::Record(xs) => {
                let vs: Vec<_> = xs.into_iter().map(|x| self.bind(x)).collect();
                let vs = vs.into_iter().map(|v| self.refer(v));
                self.push(C::Record(vs.collect()))[0]
            }

            N::Ast::Select(ix, xs) => {
                let tuple = self.bind(*xs);
                self.push(C::Select(self.refer(tuple), ix))[0]
            }
        }
    }

    /// Translate a lambda in the input AST into a contified lambda.
    fn lambda(&mut self, l: N::Lam) -> Lam {
        let N::Lam(formals, body) = l;
        self.enter(formals, 1, None);
        let k = self.cps_var(formals);
        self.body(body, k)
    }

    /// Translate a local variable in the input AST (given by its `de_bruijn` index) to the
    /// corresponding bound variable in the contified AST.
    fn frm_var(&self, de_bruijn: usize) -> BVar {
        *self
            .frm_vars
            .get(self.frm_vars.len() - de_bruijn - 1)
            .expect("ICE: de-bruijn out-of-bounds.")
    }

    /// Get the bound variable corresponding to the `ix`-th local in the top frame.
    fn cps_var(&self, ix: usize) -> BVar {
        self.frames.last().expect("ICE: No frame.").cps_var(ix)
    }

    // Translate a bound variable into a de-Bruijn index for the contified AST at the current
    // position.  This variable is only valid as long as no more results are pushed.
    fn refer(&self, bvar: BVar) -> Var {
        self.frames.last().expect("ICE: No frame.").refer(bvar)
    }

    /// The number of bindings in the contified AST.
    fn bindings(&self) -> usize {
        self.frames.last().map_or(0, |f| f.cps_sp)
    }

    /// Push the command to the top-most frame.  This adds the command and also registers its
    /// results as locals on the stack.
    fn push(&mut self, cmd: Cmd) -> Vec<BVar> {
        self.frames
            .last_mut()
            .expect("ICE: no frame to push to.")
            .push(cmd)
    }

    /// Enter a new frame. `args` is the number of parameters in the input AST, `extras` are the
    /// additional parameters introduced in the contified `AST` (e.g. for the continuation
    /// parameter).  If the frame being entered is for a continuation, `caller` is the function
    /// application that it is a continuation for.
    fn enter(&mut self, args: usize, extras: usize, caller: Option<(BVar, Vec<BVar>)>) {
        let frm_bp = self.frm_vars.len();
        let cps_bp = self.bindings();

        for ix in cps_bp..cps_bp + args {
            self.frm_vars.push(BVar(ix))
        }

        self.frames.push(Frame {
            caller,
            frm_bp,
            cps_bp,
            cps_sp: args + extras + cps_bp,
            params: args + extras,
            locals: vec![],
        });
    }

    fn exit(&mut self) -> Frame {
        let frame = self.frames.pop().expect("ICE: no frame to pop.");
        self.frm_vars.truncate(frame.frm_bp);
        frame
    }
}

impl Frame {
    fn cps_var(&self, mut ix: usize) -> BVar {
        ix += self.cps_bp;
        debug_assert!(ix < self.cps_sp);
        BVar(ix)
    }

    fn refer(&self, BVar(ix): BVar) -> Var {
        Var(self.cps_sp - ix - 1)
    }

    fn push(&mut self, cmd: Cmd) -> Vec<BVar> {
        use Cmd as C;
        let results = match &cmd {
            C::Free(_) | C::Record(_) | C::Select(_, _) => 1,
            C::Fix(binds) => binds.len(),
        };

        self.locals.push(cmd);
        let bp = self.cps_sp;
        self.cps_sp += results;
        (bp..bp + results).map(BVar).collect()
    }
}

impl fmt::Debug for Var {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "Var({})", self.0)
    }
}

impl fmt::Debug for Cmd {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        use Cmd as C;
        match self {
            C::Free(v) => write!(fmt, "Free({v:?})"),

            C::Fix(binds) if fmt.alternate() => write!(fmt, "Fix({binds:#?})"),
            C::Fix(binds) => write!(fmt, "Fix({binds:?})"),

            C::Record(elems) if fmt.alternate() => write!(fmt, "Record({elems:#?})"),
            C::Record(elems) => write!(fmt, "Record({elems:?})"),

            C::Select(tuple, ix) => write!(fmt, "Select({tuple:?}, {ix:?})"),
        }
    }
}

impl fmt::Debug for Lam {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        let Lam(params, ast) = self;
        if fmt.alternate() {
            write!(fmt, "Lam({params}, {ast:#?})")
        } else {
            write!(fmt, "Lam({params}, {ast:?})")
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::fixtures::*;
    use crate::{lex::Lexer, naming, parse::Parser};

    use super::*;
    use expect_test::expect;

    fn cps<'b>(buf: &'b str) -> String {
        let tokens = Lexer::new(buf);
        let pexpr = Parser::parse(tokens).expect("parsing should succeed");
        let nexpr = naming::pass(pexpr);
        let cexpr = Cps::convert(nexpr);
        format!("{cexpr:#?}\n")
    }

    #[test]
    fn variable() {
        expect![[r#"
            Ast(
                [
                    Free("HALT"),
                    Free("a"),
                ],
                Var(1),
                [
                    Var(0),
                ],
            )
        "#]]
        .assert_eq(&cps(VARIABLE));
    }

    #[test]
    fn comment() {
        expect![[r#"
            Ast(
                [
                    Free("HALT"),
                    Free("a"),
                ],
                Var(1),
                [
                    Var(0),
                ],
            )
        "#]]
        .assert_eq(&cps(COMMENT));
    }

    #[test]
    fn multi_comment() {
        expect![[r#"
            Ast(
                [
                    Free("HALT"),
                    Free("b"),
                ],
                Var(1),
                [
                    Var(0),
                ],
            )
        "#]]
        .assert_eq(&cps(MULTI_COMMENT));
    }

    #[test]
    fn binding() {
        expect![[r#"
            Ast(
                [
                    Free("HALT"),
                    Fix([
                        Lam(2, Ast(
                            [],
                            Var(0),
                            [
                                Var(1),
                            ],
                        )),
                    ]),
                    Fix([
                        Lam(2, Ast(
                            [],
                            Var(0),
                            [
                                Var(1),
                            ],
                        )),
                    ]),
                    Free("a"),
                ],
                Var(3),
                [
                    Var(0),
                ],
            )
        "#]]
        .assert_eq(&cps(BINDING));
    }

    #[test]
    fn shadow() {
        expect![[r#"
            Ast(
                [
                    Free("HALT"),
                    Free("f"),
                    Free("x"),
                    Fix([
                        Lam(1, Ast(
                            [
                                Fix([
                                    Lam(2, Ast(
                                        [],
                                        Var(1),
                                        [
                                            Var(3),
                                            Var(0),
                                        ],
                                    )),
                                    Lam(2, Ast(
                                        [
                                            Free("x"),
                                        ],
                                        Var(2),
                                        [
                                            Var(0),
                                            Var(1),
                                        ],
                                    )),
                                ]),
                                Fix([
                                    Lam(1, Ast(
                                        [
                                            Free("f"),
                                            Free("x"),
                                            Fix([
                                                Lam(1, Ast(
                                                    [
                                                        Record([
                                                            Var(8),
                                                            Var(4),
                                                            Var(0),
                                                        ]),
                                                    ],
                                                    Var(13),
                                                    [
                                                        Var(0),
                                                    ],
                                                )),
                                            ]),
                                        ],
                                        Var(2),
                                        [
                                            Var(1),
                                            Var(0),
                                        ],
                                    )),
                                ]),
                            ],
                            Var(2),
                            [
                                Var(1),
                                Var(0),
                            ],
                        )),
                    ]),
                ],
                Var(2),
                [
                    Var(1),
                    Var(0),
                ],
            )
        "#]]
        .assert_eq(&cps(SHADOW));
    }

    #[test]
    fn let_shadow() {
        expect![[r#"
            Ast(
                [
                    Free("HALT"),
                    Fix([
                        Lam(2, Ast(
                            [],
                            Var(2),
                            [
                                Var(1),
                                Var(0),
                            ],
                        )),
                        Lam(2, Ast(
                            [
                                Free("x"),
                            ],
                            Var(2),
                            [
                                Var(0),
                                Var(1),
                            ],
                        )),
                    ]),
                ],
                Var(2),
                [
                    Var(0),
                ],
            )
        "#]]
        .assert_eq(&cps(LET_SHADOW));
    }

    #[test]
    fn apply() {
        expect![[r#"
            Ast(
                [
                    Free("HALT"),
                    Free("a"),
                    Free("b"),
                    Free("c"),
                ],
                Var(2),
                [
                    Var(1),
                    Var(0),
                    Var(3),
                ],
            )
        "#]]
        .assert_eq(&cps(APPLY));
    }

    #[test]
    fn select() {
        expect![[r#"
            Ast(
                [
                    Free("HALT"),
                    Free("a"),
                    Select(Var(0), 2),
                ],
                Var(2),
                [
                    Var(0),
                ],
            )
        "#]]
        .assert_eq(&cps(SELECT));
    }

    #[test]
    fn record() {
        expect![[r#"
            Ast(
                [
                    Free("HALT"),
                    Free("a"),
                    Free("b"),
                    Free("c"),
                    Record([
                        Var(2),
                        Var(1),
                        Var(0),
                    ]),
                ],
                Var(4),
                [
                    Var(0),
                ],
            )
        "#]]
        .assert_eq(&cps(RECORD));
    }

    #[test]
    fn apply_nested() {
        expect![[r#"
            Ast(
                [
                    Free("HALT"),
                    Free("a"),
                    Free("b"),
                    Fix([
                        Lam(1, Ast(
                            [
                                Free("c"),
                                Free("d"),
                                Fix([
                                    Lam(1, Ast(
                                        [],
                                        Var(4),
                                        [
                                            Var(0),
                                            Var(8),
                                        ],
                                    )),
                                ]),
                            ],
                            Var(2),
                            [
                                Var(1),
                                Var(0),
                            ],
                        )),
                    ]),
                ],
                Var(2),
                [
                    Var(1),
                    Var(0),
                ],
            )
        "#]]
        .assert_eq(&cps(APPLY_NESTED));
    }

    #[test]
    fn apply_select() {
        expect![[r#"
            Ast(
                [
                    Free("HALT"),
                    Free("a"),
                    Free("b"),
                    Select(Var(0), 2),
                    Free("c"),
                    Select(Var(0), 3),
                ],
                Var(4),
                [
                    Var(2),
                    Var(0),
                    Var(5),
                ],
            )
        "#]]
        .assert_eq(&cps(APPLY_SELECT));
    }

    #[test]
    fn record_select() {
        expect![[r#"
            Ast(
                [
                    Free("HALT"),
                    Free("a"),
                    Select(Var(0), 2),
                    Free("b"),
                    Select(Var(0), 3),
                    Free("c"),
                    Select(Var(0), 4),
                    Record([
                        Var(4),
                        Var(2),
                        Var(0),
                    ]),
                ],
                Var(7),
                [
                    Var(0),
                ],
            )
        "#]]
        .assert_eq(&cps(RECORD_SELECT));
    }

    #[test]
    fn lambda() {
        expect![[r#"
            Ast(
                [
                    Free("HALT"),
                    Fix([
                        Lam(4, Ast(
                            [],
                            Var(1),
                            [
                                Var(2),
                                Var(3),
                                Var(0),
                            ],
                        )),
                    ]),
                ],
                Var(1),
                [
                    Var(0),
                ],
            )
        "#]]
        .assert_eq(&cps(LAMBDA));
    }

    #[test]
    fn complicated() {
        expect![[r#"
            Ast(
                [
                    Free("HALT"),
                    Fix([
                        Lam(3, Ast(
                            [
                                Select(Var(2), 2),
                            ],
                            Var(1),
                            [
                                Var(0),
                            ],
                        )),
                    ]),
                    Fix([
                        Lam(3, Ast(
                            [
                                Select(Var(1), 3),
                            ],
                            Var(1),
                            [
                                Var(0),
                            ],
                        )),
                    ]),
                    Free("x"),
                    Free("y"),
                    Free("z"),
                    Select(Var(0), 4),
                    Fix([
                        Lam(1, Ast(
                            [
                                Record([
                                    Var(5),
                                    Var(0),
                                ]),
                            ],
                            Var(9),
                            [
                                Var(0),
                            ],
                        )),
                    ]),
                ],
                Var(6),
                [
                    Var(3),
                    Var(1),
                    Var(0),
                ],
            )
        "#]]
        .assert_eq(&cps(COMPLICATED));
    }

    #[test]
    fn loop_() {
        expect![[r#"
            Ast(
                [
                    Free("HALT"),
                    Fix([
                        Lam(2, Ast(
                            [
                                Select(Var(1), 0),
                            ],
                            Var(3),
                            [
                                Var(0),
                                Var(1),
                            ],
                        )),
                    ]),
                ],
                Var(1),
                [
                    Var(0),
                ],
            )
        "#]]
        .assert_eq(&cps(LOOP));
    }

    #[test]
    fn co_recursive() {
        expect![[r#"
            Ast(
                [
                    Free("HALT"),
                    Fix([
                        Lam(2, Ast(
                            [],
                            Var(2),
                            [
                                Var(1),
                                Var(0),
                            ],
                        )),
                        Lam(2, Ast(
                            [],
                            Var(3),
                            [
                                Var(1),
                                Var(0),
                            ],
                        )),
                    ]),
                ],
                Var(2),
                [
                    Var(1),
                ],
            )
        "#]]
        .assert_eq(&cps(CO_RECURSIVE));
    }

    #[test]
    fn already_cps() {
        expect![[r#"
            Ast(
                [
                    Free("HALT"),
                    Fix([
                        Lam(3, Ast(
                            [],
                            Var(1),
                            [
                                Var(2),
                                Var(0),
                            ],
                        )),
                    ]),
                ],
                Var(1),
                [
                    Var(0),
                ],
            )
        "#]]
        .assert_eq(&cps(ALREADY_CPS));
    }
}
