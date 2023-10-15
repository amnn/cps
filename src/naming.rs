//! # Naming
//!
//! Replaces named bindings with de-Bruijn indices.  This simplifies the work of following passes
//! that may need to generate fresh bindings.  Such passes now no longer need to worry about
//! generating fresh symbols to avoid shadowing etc.
//!
//! This pass does not fail, but will leave references to variables that aren't under a binder as
//! `Free` variables.
//!
//! The resulting `Ast<'b>` differs from its input (`P::Ast<'b>`) in the following ways:
//!
//! - `P::Ast::Var(&'b str)` is split into `Ast::Var(usize)` and `Ast::Free(&'b str)`.  The former
//!   represents a local variable `v` whose binder is nested `v.0` many binders away.  The latter
//!   represents a free/global variable that wasn't introduced by a binder in this program.
//!
//! - `P::Ast::Let` loses all references to the names of the bindings it introduces.  They are
//!   simply represented as a list of the bindings' values (Order is preserved from the input AST).
//!
//! - `P::Lam`'s list of parameters is reduced to a parameter count, again preserving the order of
//!   parameters.

use std::{collections::HashMap, fmt};

use crate::parse as P;

#[derive(Eq, PartialEq, Clone)]
pub(crate) enum Ast<'b> {
    Free(&'b str),
    Var(usize),
    Let(Vec<Lam<'b>>, Box<Ast<'b>>),
    Lam(Box<Lam<'b>>),
    App(Box<Ast<'b>>, Vec<Ast<'b>>),
    Record(Vec<Ast<'b>>),
    Select(usize, Box<Ast<'b>>),
}

#[derive(Eq, PartialEq, Clone)]
pub(crate) struct Lam<'b>(pub usize, pub Ast<'b>);

/// Represents the state of the environment: The current bindings in scope, and any that have been
/// shadowed.
#[derive(Default, Debug)]
pub(crate) struct ScopeChain<'b> {
    /// Mapping in-scope variables to the index of their binder.  This index is absolute (i.e. not a
    /// de-Bruijn index), so that existing entries do not need to be updated when a new binder is
    /// introduced.
    local_to_ix: HashMap<&'b str, usize>,

    /// Metadata about a particular binder: Its name (a reverse mapping for `local_to_ix`) and the
    /// index of a previous binding for the same name that this binding shadows.  If this binding
    /// does not shadow any other, then this index points to itself.
    ix_to_local: Vec<Node<'b>>,
}

#[derive(Debug)]
struct Node<'b> {
    name: &'b str,
    prev: usize,
}

/// Entrypoint
pub(crate) fn pass(from: P::Ast) -> Ast {
    let mut env = ScopeChain::default();
    expr(&mut env, from)
}

impl<'b> ScopeChain<'b> {
    fn len(&self) -> usize {
        self.ix_to_local.len()
    }

    /// Return the de-Bruijn index of the variable, `name`, if it has been bound or `None`
    /// otherwise.
    fn var(&self, name: &str) -> Option<usize> {
        let bvar = *self.local_to_ix.get(name)?;
        Some(self.ix_to_local.len() - bvar - 1)
    }

    /// Add a new binding for `name`, potentially shadowing other bindings.
    fn push(&mut self, name: &'b str) {
        let next = self.ix_to_local.len();
        let curr = self.local_to_ix.entry(name).or_insert_with(|| next);
        let prev = *curr;
        *curr = next;

        self.ix_to_local.push(Node { name, prev })
    }

    /// Pop bindings until there are at most `target` bindings left (including shadowed bindings).
    fn pop_to(&mut self, target: usize) {
        let mut len = self.ix_to_local.len();
        while len > target {
            // SAFETY: self.ix_to_local.len() == len > target >= 0
            let Node { name, prev } = self.ix_to_local.pop().unwrap();

            len -= 1;
            if prev == len {
                self.local_to_ix.remove(name);
            } else {
                self.local_to_ix.insert(name, prev);
            }
        }
    }
}

impl<'b> fmt::Debug for Ast<'b> {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Ast::Free(v) => write!(fmt, "Free({v:?})"),
            Ast::Var(v) => write!(fmt, "Var({v:?})"),
            Ast::Let(binds, body) => fmt.debug_tuple("Let").field(binds).field(body).finish(),

            Ast::Lam(l) if fmt.alternate() => write!(fmt, "{l:#?}"),
            Ast::Lam(l) => write!(fmt, "{l:?}"),

            Ast::App(f, xs) => fmt.debug_tuple("App").field(f).field(xs).finish(),

            Ast::Record(xs) if fmt.alternate() => write!(fmt, "Record({xs:#?})"),
            Ast::Record(xs) => write!(fmt, "Record({xs:?})"),

            Ast::Select(ix, tuple) if fmt.alternate() => write!(fmt, "Select({ix}, {tuple:#?})"),
            Ast::Select(ix, tuple) => write!(fmt, "Select({ix}, {tuple:?})"),
        }
    }
}

impl<'b> fmt::Debug for Lam<'b> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        let Lam(formals, body) = self;
        write!(fmt, "Lam({formals:?}, ")?;

        if fmt.alternate() {
            write!(fmt, "{body:#?}")?;
        } else {
            write!(fmt, "{body:?}")?;
        }

        write!(fmt, ")")
    }
}

fn expr<'b>(env: &mut ScopeChain<'b>, from: P::Ast<'b>) -> Ast<'b> {
    match from {
        P::Ast::Var(name) => env.var(name).map_or(Ast::Free(name), Ast::Var),

        P::Ast::Let(binds, body) => {
            let before = env.len();
            for (name, _) in &binds {
                env.push(name);
            }

            let binds = binds.into_iter().map(|(_, l)| lambda(env, l)).collect();

            let body = expr(env, *body);
            env.pop_to(before);
            Ast::Let(binds, Box::new(body))
        }

        P::Ast::Lam(lam) => Ast::Lam(Box::new(lambda(env, *lam))),

        // Simple recursive cases
        P::Ast::App(f, xs) => Ast::App(Box::new(expr(env, *f)), exprs(env, xs)),
        P::Ast::Record(xs) => Ast::Record(exprs(env, xs)),
        P::Ast::Select(ix, x) => Ast::Select(ix, Box::new(expr(env, *x))),
    }
}

fn exprs<'b>(env: &mut ScopeChain<'b>, from: Vec<P::Ast<'b>>) -> Vec<Ast<'b>> {
    from.into_iter().map(|e| expr(env, e)).collect()
}

fn lambda<'b>(env: &mut ScopeChain<'b>, from: P::Lam<'b>) -> Lam<'b> {
    let before = env.len();
    let params = from.0.len();
    for param in from.0 {
        env.push(param);
    }

    let body = expr(env, from.1);
    env.pop_to(before);
    Lam(params, body)
}

#[cfg(test)]
mod tests {
    use crate::{fixtures::*, lex, parse};
    use expect_test::expect;

    fn naming<'b>(buf: &'b str) -> String {
        let toks = lex::pass(buf);
        let astp = parse::pass(toks).expect("parsing should succeed");
        let astn = super::pass(astp);
        format!("{astn:#?}\n")
    }

    #[test]
    fn variable() {
        expect![[r#"
            Free("a")
        "#]]
        .assert_eq(&naming(VARIABLE));
    }

    #[test]
    fn comment() {
        expect![[r#"
            Free("a")
        "#]]
        .assert_eq(&naming(COMMENT));
    }

    #[test]
    fn multi_comment() {
        expect![[r#"
            Free("b")
        "#]]
        .assert_eq(&naming(MULTI_COMMENT));
    }

    #[test]
    fn binding() {
        expect![[r#"
            Let(
                [
                    Lam(1, Var(0)),
                ],
                Let(
                    [
                        Lam(1, Var(0)),
                    ],
                    Free("a"),
                ),
            )
        "#]]
        .assert_eq(&naming(BINDING))
    }

    #[test]
    fn shadow() {
        expect![[r#"
            Record([
                App(
                    Free("f"),
                    [
                        Free("x"),
                    ],
                ),
                Let(
                    [
                        Lam(1, App(
                            Var(0),
                            [
                                Var(2),
                            ],
                        )),
                        Lam(1, App(
                            Var(0),
                            [
                                Free("x"),
                            ],
                        )),
                    ],
                    App(
                        Var(1),
                        [
                            Var(0),
                        ],
                    ),
                ),
                App(
                    Free("f"),
                    [
                        Free("x"),
                    ],
                ),
            ])
        "#]]
        .assert_eq(&naming(SHADOW));
    }

    #[test]
    fn let_shadow() {
        expect![[r#"
            Let(
                [
                    Lam(1, App(
                        Var(1),
                        [
                            Var(0),
                        ],
                    )),
                    Lam(1, App(
                        Var(0),
                        [
                            Free("x"),
                        ],
                    )),
                ],
                Var(0),
            )
        "#]]
        .assert_eq(&naming(LET_SHADOW));
    }

    #[test]
    fn apply() {
        expect![[r#"
            App(
                Free("a"),
                [
                    Free("b"),
                    Free("c"),
                ],
            )
        "#]]
        .assert_eq(&naming(APPLY));
    }

    #[test]
    fn select() {
        expect![[r#"
            Select(2, Free("a"))
        "#]]
        .assert_eq(&naming(SELECT));
    }

    #[test]
    fn record() {
        expect![[r#"
            Record([
                Free("a"),
                Free("b"),
                Free("c"),
            ])
        "#]]
        .assert_eq(&naming(RECORD));
    }

    #[test]
    fn apply_nested() {
        expect![[r#"
            App(
                App(
                    Free("a"),
                    [
                        Free("b"),
                    ],
                ),
                [
                    App(
                        Free("c"),
                        [
                            Free("d"),
                        ],
                    ),
                ],
            )
        "#]]
        .assert_eq(&naming(APPLY_NESTED));
    }

    #[test]
    fn apply_select() {
        expect![[r#"
            App(
                Free("a"),
                [
                    Select(2, Free("b")),
                    Select(3, Free("c")),
                ],
            )
        "#]]
        .assert_eq(&naming(APPLY_SELECT));
    }

    #[test]
    fn record_select() {
        expect![[r#"
            Record([
                Select(2, Free("a")),
                Select(3, Free("b")),
                Select(4, Free("c")),
            ])
        "#]]
        .assert_eq(&naming(RECORD_SELECT));
    }

    #[test]
    fn lambda() {
        expect![[r#"
            Lam(3, App(
                Var(0),
                [
                    Var(1),
                    Var(2),
                ],
            ))
        "#]]
        .assert_eq(&naming(LAMBDA));
    }

    #[test]
    fn complicated() {
        expect![[r#"
            Let(
                [
                    Lam(2, Select(2, Var(1))),
                ],
                Let(
                    [
                        Lam(2, Select(3, Var(0))),
                    ],
                    Record([
                        Free("x"),
                        App(
                            Var(1),
                            [
                                Free("y"),
                                Select(4, Free("z")),
                            ],
                        ),
                    ]),
                ),
            )
        "#]]
        .assert_eq(&naming(COMPLICATED));
    }

    #[test]
    fn loop_() {
        expect![[r#"
            Let(
                [
                    Lam(1, App(
                        Var(1),
                        [
                            Select(0, Var(0)),
                        ],
                    )),
                ],
                Var(0),
            )
        "#]]
        .assert_eq(&naming(LOOP));
    }

    #[test]
    fn co_recursive() {
        expect![[r#"
            Let(
                [
                    Lam(1, App(
                        Var(1),
                        [
                            Var(0),
                        ],
                    )),
                    Lam(1, App(
                        Var(2),
                        [
                            Var(0),
                        ],
                    )),
                ],
                Var(1),
            )
        "#]]
        .assert_eq(&naming(CO_RECURSIVE));
    }

    #[test]
    fn already_cps() {
        expect![[r#"
            Let(
                [
                    Lam(2, App(
                        Var(0),
                        [
                            Var(1),
                        ],
                    )),
                ],
                Var(0),
            )
        "#]]
        .assert_eq(&naming(ALREADY_CPS));
    }
}
