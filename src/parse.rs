use std::{fmt, iter::Peekable};

use crate::lex::{Lexer, Token};

#[derive(Eq, PartialEq, Clone)]
pub(crate) enum Ast {
    Free(String),
    Var(u32),
    Let(Vec<(u32, Ast)>, Box<Ast>),
    Lam(u32, Box<Ast>),
    App(Box<Ast>, Vec<Ast>),
    Record(Vec<Ast>),
    Select(Box<Ast>, u32),
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
/// decl        := "let" binds "in" decl
///              | lambda
///              | application
///
/// binds       := lambda
///              | lambda "and" binds
///
/// lambda      := "\"+ decl
///
/// application := application select
///              | select
///
/// select      := select "." <Int>
///              | atom
///
/// atom        := "[" record "]"
///              | "(" decl ")"
///              | <Word>
///
/// record      := ε
///              | decl
///              | decl "," record
///
impl<'b> Parser<'b> {
    pub(crate) fn parse(tokens: Lexer<'b>) -> Result<Ast, Error<'b>> {
        let mut parser = Self(tokens.peekable());

        let term = parser.decl()?;
        if let Ok(t) = parser.peek() {
            Err(Error::Unexpected(*t))
        } else {
            Ok(term)
        }
    }

    fn decl(&mut self) -> Result<Ast, Error<'b>> {
        use Token as T;

        match self.peek()? {
            T::BSlash => {
                let (formals, body) = self.lambda()?;
                Ok(Ast::Lam(formals, Box::new(body)))
            }

            T::Word("let") => {
                self.bump();
                let binds = self.binds()?;
                self.lexeme(T::Word("in"))?;
                let body = self.decl()?;
                Ok(Ast::Let(binds, Box::new(body)))
            }

            _ => self.application(),
        }
    }

    fn binds(&mut self) -> Result<Vec<(u32, Ast)>, Error<'b>> {
        let mut binds = vec![];
        loop {
            binds.push(self.lambda()?);
            if self.lexeme(Token::Word("and")).is_err() {
                break Ok(binds);
            }
        }
    }

    fn lambda(&mut self) -> Result<(u32, Ast), Error<'b>> {
        use Token as T;
        self.lexeme(T::BSlash)?;

        let mut args = 1;
        while self.lexeme(T::BSlash).is_ok() {
            args += 1;
        }

        let body = self.decl()?;
        Ok((args, body))
    }

    fn application(&mut self) -> Result<Ast, Error<'b>> {
        let fun = self.select()?;

        let mut actuals = vec![];
        while let Ok(select) = self.select() {
            actuals.push(select);
        }

        Ok(if !actuals.is_empty() {
            Ast::App(Box::new(fun), actuals)
        } else {
            fun
        })
    }

    fn select(&mut self) -> Result<Ast, Error<'b>> {
        use Token as T;

        let mut select = self.atom()?;
        while self.lexeme(T::Dot).is_ok() {
            select = Ast::Select(Box::new(select), self.int()?);
        }

        Ok(select)
    }

    fn atom(&mut self) -> Result<Ast, Error<'b>> {
        use Token as T;

        match self.peek()? {
            T::Bra => {
                self.bump();
                self.record()
            }

            T::LPar => {
                self.bump();
                let inner = self.decl()?;
                self.lexeme(T::RPar)?;
                Ok(inner)
            }

            &T::Word(w) if !is_keyword(w) => {
                self.bump();
                Ok(Ast::Free(w.to_owned()))
            }

            &T::Int(i) => {
                self.bump();
                Ok(Ast::Var(i))
            }

            t => Err(Error::Unexpected(*t)),
        }
    }

    fn record(&mut self) -> Result<Ast, Error<'b>> {
        use Token as T;

        let mut elems = vec![];
        let mut delimited = true;
        loop {
            let tok = self.peek()?;
            if tok == &T::Ket {
                self.bump();
                return Ok(Ast::Record(elems));
            }

            if !delimited {
                return Err(Error::Unexpected(*tok));
            } else {
                elems.push(self.decl()?);
                delimited = self.lexeme(T::Comma).is_ok();
            }
        }
    }

    fn peek(&mut self) -> Result<&Token<'b>, Error<'b>> {
        self.0.peek().ok_or(Error::Eof)
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

    fn int(&mut self) -> Result<u32, Error<'b>> {
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
            Ast::Select(tuple, ix) => fmt.debug_tuple("Select").field(tuple).field(ix).finish(),

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

fn is_keyword(w: &str) -> bool {
    matches!(w, "let" | "and" | "in")
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
                    Free("a"),
                    2,
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
    fn apply_select() {
        expect![[r#"
            Ok(
                App(
                    Free("a"),
                    [
                        Select(
                            Free("b"),
                            2,
                        ),
                        Select(
                            Free("c"),
                            3,
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
                        Free("a"),
                        2,
                    ),
                    Select(
                        Free("b"),
                        3,
                    ),
                    Select(
                        Free("c"),
                        4,
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
                            Var(1),
                            2,
                        )),
                    ],
                    Let(
                        [
                            Lam(2, Select(
                                Var(0),
                                3,
                            )),
                        ],
                        Record([
                            Free("x"),
                            App(
                                Var(1),
                                [
                                    Free("y"),
                                    Select(
                                        Free("z"),
                                        4,
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
                                    Var(0),
                                    0,
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
}
