use std::{fmt, iter};

use crate::parse as P;

#[derive(Copy, Clone, PartialEq, Eq)]
pub(crate) struct Var(usize);

#[derive(PartialEq, Eq)]
pub(crate) enum Cmd {
    Free(String),
    Fix(Vec<Lam>),
    Record(Vec<Var>),
    Select(Var, usize),
}

#[derive(PartialEq, Eq)]
pub(crate) struct Lam(usize, Ast);

#[derive(PartialEq, Eq, Debug)]
pub(crate) struct Ast(Vec<Cmd>, Var, Vec<Var>);

/// Bound variables are represented by an index counting down from the first binding (as opposed to
/// Vars which is a de-Bruijn index and counts up from the last binding).
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
struct BVar(usize);

#[derive(Debug)]
pub(crate) struct Cps {
    frames: Vec<Frame>,
    frm_vars: Vec<BVar>,
}

#[derive(Debug)]
struct Frame {
    callee: Option<(BVar, Vec<BVar>)>,
    frm_bp: usize,
    cps_bp: usize,
    cps_sp: usize,
    params: usize,
    locals: Vec<Cmd>,
}

impl Cps {
    pub(crate) fn convert(from: P::Ast) -> Ast {
        let mut cps = Cps {
            frames: vec![],
            frm_vars: vec![],
        };

        cps.enter(0, 0, None);
        let halt = cps.push(Cmd::Free("HALT".to_owned()))[0];
        cps.body(from, halt).1
    }

    fn body(&mut self, from: P::Ast, k: BVar) -> Lam {
        let (mut k, mut xs) = if let P::Ast::App(f, xs) = from {
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

        loop {
            let frame = self.exit();

            // End the frame with the current continuation
            let kv = frame.refer(k);
            let vs: Vec<_> = xs.into_iter().map(|x| frame.refer(x)).collect();

            let Frame {
                callee,
                params,
                locals,
                ..
            } = frame;

            let mut prog = Lam(params, Ast(locals, kv, vs));
            if let Some((f, mut ys)) = callee {
                // This frame has a callee, so it is the continuation of some other function
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

    fn bind(&mut self, from: P::Ast) -> BVar {
        use Cmd as C;
        match from {
            P::Ast::Free(x) => self.push(C::Free(x))[0],
            P::Ast::Var(ix) => self.frm_var(ix),

            P::Ast::Let(binds, body) => {
                // self-bindings
                self.enter(binds.len(), 0, None);

                let functions: Vec<_> = binds
                    .into_iter()
                    .map(|(formals, body)| self.lambda(formals, body))
                    .collect();

                self.exit();

                // Re-establish self-bindings so `body` can reference them.
                let locals = self.push(C::Fix(functions));
                self.frm_vars.extend(locals);

                self.bind(*body)
            }

            P::Ast::Lam(formals, body) => {
                // Dummy scope, for the lambda's self-reference.
                self.enter(0, 1, None);
                let function = self.lambda(formals, *body);
                self.exit();

                self.push(C::Fix(vec![function]))[0]
            }

            P::Ast::App(f, xs) => {
                let f = self.bind(*f);
                let vs: Vec<_> = xs.into_iter().map(|x| self.bind(x)).collect();

                // Enter continuation, reserving two extra variables: The first is an implicit
                // binding for the continuation itself (because we will bind it using `Fix`), and
                // the second is for the continuation parameter.
                self.enter(0, 2, Some((f, vs)));
                self.cps_var(1)
            }

            P::Ast::Record(xs) => {
                let vs: Vec<_> = xs.into_iter().map(|x| self.bind(x)).collect();
                let vs = vs.into_iter().map(|v| self.refer(v));
                self.push(C::Record(vs.collect()))[0]
            }

            P::Ast::Select(xs, ix) => {
                let tuple = self.bind(*xs);
                self.push(C::Select(self.refer(tuple), ix))[0]
            }
        }
    }

    fn lambda(&mut self, formals: usize, body: P::Ast) -> Lam {

        self.enter(formals, 1, None);
        let k = self.cps_var(formals);
        self.body(body, k)
    }

    fn frm_var(&self, de_bruijn: usize) -> BVar {
        *self
            .frm_vars
            .get(self.frm_vars.len() - de_bruijn - 1)
            .expect("ICE: de-bruijn out-of-bounds.")
    }

    fn cps_var(&self, ix: usize) -> BVar {
        self.frames.last().expect("ICE: No frame.").cps_var(ix)
    }

    fn refer(&self, bvar: BVar) -> Var {
        self.frames.last().expect("ICE: No frame.").refer(bvar)
    }

    fn bindings(&self) -> usize {
        self.frames.last().map_or(0, |f| f.cps_sp)
    }

    fn push(&mut self, cmd: Cmd) -> Vec<BVar> {
        self.frames
            .last_mut()
            .expect("ICE: no frame to push to.")
            .push(cmd)
    }

    fn enter(&mut self, args: usize, extras: usize, callee: Option<(BVar, Vec<BVar>)>) {
        let frm_bp = self.frm_vars.len();
        let cps_bp = self.bindings();

        for ix in cps_bp..cps_bp + args {
            self.frm_vars.push(BVar(ix))
        }

        self.frames.push(Frame {
            callee,
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
    use crate::{lex::Lexer, parse::Parser};

    use super::*;
    use expect_test::expect;

    fn cps<'b>(buf: &'b str) -> String {
        let tokens = Lexer::new(buf);
        let lterm = Parser::parse(tokens).expect("parsing should succeed");
        let cterm = Cps::convert(lterm);
        format!("{cterm:#?}\n")
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

    // TODO Debug: x = Var(4) seems incorrect.
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
