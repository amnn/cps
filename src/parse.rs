use std::{fmt, iter::Peekable};

use crate::lex::{Lexer, Token};

#[derive(Eq, PartialEq, Clone)]
pub(crate) enum Ast {
    Free(String),
    Var(usize),
    Let(Vec<(usize, Ast)>, Box<Ast>),
    Lam(usize, Box<Ast>),
    App(Box<Ast>, Vec<Ast>),
    Record(Vec<Ast>),
    Select(usize, Box<Ast>),
}

#[derive(Debug)]
pub(crate) enum Error<'b> {
    Unexpected(Token<'b>),
    Eof,
}

#[derive(Debug)]
pub(crate) struct Parser<'b>(Peekable<Lexer<'b>>);

/// Parses the following grammar
///
/// expr    ::= "(" "let" "(" binds ")" expr ")"
///           | lambda
///           | "(" "record" expr* ")"
///           | "(" "select" <Int> expr ")"
///           | "(" expr+ ")" ;; function application
///           | <Int>         ;; local variables
///           | <Word>        ;; free variables
///
/// binds  ::= binds bind | ε
/// bind   ::= <Int> expr
///
/// lambda ::= "(" "fn" "(" <Int> ")" expr ")"
impl<'b> Parser<'b> {
    /// Entrypoint: Convert a token stream into an AST.
    pub(crate) fn parse(tokens: Lexer<'b>) -> Result<Ast, Error<'b>> {
        let mut parser = Self(tokens.peekable());

        let ast = parser.expr()?;
        if let Ok(t) = parser.peek() {
            Err(Error::Unexpected(*t))
        } else {
            Ok(ast)
        }
    }

    fn expr(&mut self) -> Result<Ast, Error<'b>> {
        use Token as T;

        match self.next()? {
            T::Word(free) => Ok(Ast::Free(free.to_string())),
            T::Int(local) => Ok(Ast::Var(local)),
            T::LPar => self.compound(),
            t => Err(Error::Unexpected(t))
        }
    }

    fn compound(&mut self) -> Result<Ast, Error<'b>> {
        use Token as T;
        match self.peek()? {
            T::Word("let") => {
                self.bump();
                self.lexeme(T::LPar)?;
                let binds = self.tail(|p| {
                    let ix = p.int()?;
                    let expr = p.expr()?;
                    Ok((ix, expr))
                })?;

                let body  = self.expr()?;
                self.lexeme(T::RPar)?;
                Ok(Ast::Let(binds, Box::new(body)))
            },

            T::Word("record") => {
                self.bump();
                Ok(Ast::Record(self.tail(|p| p.expr())?))
            },

            T::Word("select") => {
                self.bump();
                let ix = self.int()?;
                let expr = self.expr()?;
                self.lexeme(T::RPar)?;
                Ok(Ast::Select(ix, Box::new(expr)))
            },

            T::Word("fn") => {
                self.bump();
                self.lexeme(T::LPar)?;
                let params = self.int()?;
                self.lexeme(T::RPar)?;
                let body = self.expr()?;
                self.lexeme(T::RPar)?;
                Ok(Ast::Lam(params, Box::new(body)))
            }

            _ => {
                let fun = self.expr()?;
                Ok(Ast::App(Box::new(fun), self.tail(|p| p.expr())?))
            },
        }
    }

    fn tail<T, E>(&mut self, mut elem: E) -> Result<Vec<T>, Error<'b>>
    where
        E: FnMut(&mut Self) -> Result<T, Error<'b>>
    {
        use Token as T;
        let mut elems = vec![];
        while self.peek()? != &T::RPar {
            elems.push(elem(self)?);
        }

        self.bump();
        Ok(elems)
    }

    fn peek(&mut self) -> Result<&Token<'b>, Error<'b>> {
        self.0.peek().ok_or(Error::Eof)
    }

    fn next(&mut self) -> Result<Token<'b>, Error<'b>> {
        self.0.next().ok_or(Error::Eof)
    }

    fn bump(&mut self) {
        self.0.next();
    }

    fn lexeme(&mut self, tok_: Token) -> Result<(), Error<'b>> {
        let tok = self.peek()?;
        if tok != &tok_ {
            return Err(Error::Unexpected(*tok));
        }

        self.bump();
        Ok(())
    }

    fn int(&mut self) -> Result<usize, Error<'b>> {
        match self.peek()? {
            &Token::Int(i) => {
                self.bump();
                Ok(i)
            }

            tok => Err(Error::Unexpected(*tok)),
        }
    }
}

impl fmt::Debug for Ast {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Ast::Free(v) => write!(fmt, "Free({v:?})"),
            Ast::Var(v) => write!(fmt, "Var({v:?})"),
            Ast::App(f, x) => fmt.debug_tuple("App").field(f).field(x).finish(),
            Ast::Select(ix, tuple) => fmt.debug_tuple("Select").field(ix).field(tuple).finish(),

            Ast::Let(binds, body) => {
                let lams: Vec<_> = binds
                    .iter()
                    .map(|(f, b)| Ast::Lam(*f, Box::new(b.clone())))
                    .collect();

                fmt.debug_tuple("Let").field(&lams).field(body).finish()
            }

            Ast::Lam(f, b) if fmt.alternate() => write!(fmt, "Lam({f}, {b:#?})"),
            Ast::Lam(f, b) => write!(fmt, "Lam({f}, {b:?})"),

            Ast::Record(es) if fmt.alternate() => write!(fmt, "Record({es:#?})"),
            Ast::Record(es) => write!(fmt, "Record({es:?})"),
        }
    }
}

impl<'b> fmt::Display for Error<'b> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::Unexpected(t) => write!(f, "Unexpected token: {t:?}"),
            Error::Eof => write!(f, "Unexpected end-of-file."),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fixtures::*;
    use expect_test::expect;

    fn parse<'b>(buf: &'b str) -> String {
        let tokens = Lexer::new(buf);
        format!("{:#?}\n", Parser::parse(tokens))
    }

    #[test]
    fn empty() {
        expect![[r#"
            Err(
                Eof,
            )
        "#]]
        .assert_eq(&parse(EMPTY));
    }

    #[test]
    fn variable() {
        expect![[r#"
            Ok(
                Free("a"),
            )
        "#]]
        .assert_eq(&parse(VARIABLE));
    }

    #[test]
    fn comment() {
        expect![[r#"
            Ok(
                Free("a"),
            )
        "#]]
        .assert_eq(&parse(COMMENT));
    }

    #[test]
    fn multi_comment() {
        expect![[r#"
            Ok(
                Free("b"),
            )
        "#]]
        .assert_eq(&parse(MULTI_COMMENT));
    }

    #[test]
    fn binding() {
        expect![[r#"
            Ok(
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
                ),
            )
        "#]]
        .assert_eq(&parse(BINDING))
    }

    #[test]
    fn apply() {
        expect![[r#"
            Ok(
                App(
                    Free("a"),
                    [
                        Free("b"),
                        Free("c"),
                    ],
                ),
            )
        "#]]
        .assert_eq(&parse(APPLY));
    }

    #[test]
    fn select() {
        expect![[r#"
            Ok(
                Select(
                    2,
                    Free("a"),
                ),
            )
        "#]]
        .assert_eq(&parse(SELECT));
    }

    #[test]
    fn record() {
        expect![[r#"
            Ok(
                Record([
                    Free("a"),
                    Free("b"),
                    Free("c"),
                ]),
            )
        "#]]
        .assert_eq(&parse(RECORD));
    }

    #[test]
    fn apply_nested() {
        expect![[r#"
            Ok(
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
                ),
            )
        "#]]
        .assert_eq(&parse(APPLY_NESTED));
    }

    #[test]
    fn apply_select() {
        expect![[r#"
            Ok(
                App(
                    Free("a"),
                    [
                        Select(
                            2,
                            Free("b"),
                        ),
                        Select(
                            3,
                            Free("c"),
                        ),
                    ],
                ),
            )
        "#]]
        .assert_eq(&parse(APPLY_SELECT));
    }

    #[test]
    fn record_select() {
        expect![[r#"
            Ok(
                Record([
                    Select(
                        2,
                        Free("a"),
                    ),
                    Select(
                        3,
                        Free("b"),
                    ),
                    Select(
                        4,
                        Free("c"),
                    ),
                ]),
            )
        "#]]
        .assert_eq(&parse(RECORD_SELECT));
    }

    #[test]
    fn lambda() {
        expect![[r#"
            Ok(
                Lam(3, App(
                    Var(0),
                    [
                        Var(1),
                        Var(2),
                    ],
                )),
            )
        "#]]
        .assert_eq(&parse(LAMBDA));
    }

    #[test]
    fn complicated() {
        expect![[r#"
            Ok(
                Let(
                    [
                        Lam(2, Select(
                            2,
                            Var(1),
                        )),
                    ],
                    Let(
                        [
                            Lam(2, Select(
                                3,
                                Var(0),
                            )),
                        ],
                        Record([
                            Free("x"),
                            App(
                                Var(1),
                                [
                                    Free("y"),
                                    Select(
                                        4,
                                        Free("z"),
                                    ),
                                ],
                            ),
                        ]),
                    ),
                ),
            )
        "#]]
        .assert_eq(&parse(COMPLICATED));
    }

    #[test]
    fn loop_() {
        expect![[r#"
            Ok(
                Let(
                    [
                        Lam(1, App(
                            Var(1),
                            [
                                Select(
                                    0,
                                    Var(0),
                                ),
                            ],
                        )),
                    ],
                    Var(0),
                ),
            )
        "#]]
        .assert_eq(&parse(LOOP));
    }

    #[test]
    fn co_recursive() {
        expect![[r#"
            Ok(
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
                ),
            )
        "#]]
        .assert_eq(&parse(CO_RECURSIVE));
    }

    #[test]
    fn already_cps() {
        expect![[r#"
            Ok(
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
                ),
            )
        "#]]
        .assert_eq(&parse(ALREADY_CPS));
    }
}
