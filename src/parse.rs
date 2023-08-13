use std::{fmt, iter::Peekable, str::FromStr};

use crate::lex::{Lexer, Token};

#[derive(Eq, PartialEq, Clone)]
pub(crate) enum AST {
    Free(String),
    Var(u32),
    Let(Vec<(u32, AST)>, Box<AST>),
    Lam(u32, Box<AST>),
    App(Box<AST>, Vec<AST>),
    Record(Vec<AST>),
    Select(Box<AST>, u32),
}

#[derive(Debug)]
pub(crate) enum Error<'b> {
    Unexpected(Token, &'b str),
    EOF,
}

pub(crate) struct Tokenizer<'b>(Peekable<Lexer<'b>>);

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
impl<'b> Tokenizer<'b> {
    pub(crate) fn parse(tokens: Lexer<'b>) -> Result<AST, Error<'b>> {
        let mut parser = Self(tokens.peekable());

        let term = parser.decl()?;
        if let Some(&(t, s)) = parser.peek() {
            Err(Error::Unexpected(t, s))
        } else {
            Ok(term)
        }
    }

    fn decl(&mut self) -> Result<AST, Error<'b>> {
        use Token as T;

        match self.peek() {
            Some(&(T::BSlash, _)) => {
                let (formals, body) = self.lambda()?;
                Ok(AST::Lam(formals, Box::new(body)))
            }

            Some(&(T::Word, "let")) => {
                self.bump();
                let binds = self.binds()?;
                self.lexeme(T::Word, "in")?;
                let body = self.decl()?;
                Ok(AST::Let(binds, Box::new(body)))
            }

            _ => self.application(),
        }
    }

    fn binds(&mut self) -> Result<Vec<(u32, AST)>, Error<'b>> {
        let mut binds = vec![];
        loop {
            binds.push(self.lambda()?);
            if !self.lexeme(Token::Word, "and").is_ok() {
                break Ok(binds);
            }
        }
    }

    fn lambda(&mut self) -> Result<(u32, AST), Error<'b>> {
        use Token as T;
        self.lexeme(T::BSlash, "\\")?;

        let mut args = 1;
        while self.lexeme(T::BSlash, "\\").is_ok() {
            args += 1;
        }

        let body = self.decl()?;
        Ok((args, body))
    }

    fn application(&mut self) -> Result<AST, Error<'b>> {
        let fun = self.select()?;

        let mut actuals = vec![];
        while let Ok(select) = self.select() {
            actuals.push(select);
        }

        Ok(if !actuals.is_empty() {
            AST::App(Box::new(fun), actuals)
        } else {
            fun
        })
    }

    fn select(&mut self) -> Result<AST, Error<'b>> {
        use Token as T;

        let mut select = self.atom()?;
        while self.lexeme(T::Dot, ".").is_ok() {
            select = AST::Select(Box::new(select), self.read(T::Int)?);
        }

        Ok(select)
    }

    fn atom(&mut self) -> Result<AST, Error<'b>> {
        use Token as T;

        match self.peek() {
            None => Err(Error::EOF),

            Some(&(T::Bra, _)) => {
                self.bump();
                self.record()
            }

            Some(&(T::LPar, _)) => {
                self.bump();
                let inner = self.decl()?;
                self.lexeme(T::RPar, ")")?;
                Ok(inner)
            }

            Some(&(T::Word, w)) if !is_keyword(w) => {
                self.bump();
                Ok(AST::Free(w.to_owned()))
            }

            Some(&(T::Int, _)) => Ok(AST::Var(self.read(T::Int)?)),

            Some(&(tok, lex)) => Err(Error::Unexpected(tok, lex)),
        }
    }

    fn record(&mut self) -> Result<AST, Error<'b>> {
        use Token as T;

        let mut elems = vec![];
        let mut delimited = true;
        loop {
            match self.peek() {
                None => return Err(Error::EOF),
                Some(&(T::Ket, _)) => {
                    self.bump();
                    return Ok(AST::Record(elems));
                }
                Some(&(tok, lex)) => {
                    if !delimited {
                        return Err(Error::Unexpected(tok, lex));
                    } else {
                        elems.push(self.decl()?);
                        delimited = self.lexeme(T::Comma, ",").is_ok();
                    }
                }
            }
        }
    }

    fn peek(&mut self) -> Option<&(Token, &'b str)> {
        self.0.peek()
    }

    fn bump(&mut self) {
        self.0.next();
    }

    fn lexeme(&mut self, tok_: Token, lex_: &'b str) -> Result<(), Error<'b>> {
        match self.peek() {
            None => Err(Error::EOF),
            Some(&(tok, lex)) => {
                if tok_ == tok && lex_ == lex {
                    self.bump();
                    Ok(())
                } else {
                    Err(Error::Unexpected(tok, lex))
                }
            }
        }
    }

    fn read<T: FromStr>(&mut self, tok_: Token) -> Result<T, Error<'b>> {
        match self.peek() {
            None => Err(Error::EOF),
            Some(&(tok, lex)) => {
                if tok_ != tok {
                    Err(Error::Unexpected(tok, lex))
                } else {
                    let p = lex.parse().map_err(|_| Error::Unexpected(tok, lex))?;
                    self.bump();
                    Ok(p)
                }
            }
        }
    }
}

impl fmt::Debug for AST {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self {
            AST::Free(v) => write!(fmt, "Free({v:?})"),
            AST::Var(v) => write!(fmt, "Var({v:?})"),
            AST::App(f, x) => fmt.debug_tuple("App").field(f).field(x).finish(),
            AST::Select(tuple, ix) => fmt.debug_tuple("Select").field(tuple).field(ix).finish(),

            AST::Let(binds, body) => {
                let lams: Vec<_> = binds
                    .iter()
                    .map(|(f, b)| AST::Lam(*f, Box::new(b.clone())))
                    .collect();

                fmt.debug_tuple("Let").field(&lams).field(body).finish()
            }

            AST::Lam(f, b) if fmt.alternate() => write!(fmt, "Lam({f}, {b:#?})"),
            AST::Lam(f, b) => write!(fmt, "Lam({f}, {b:?})"),

            AST::Record(es) if fmt.alternate() => write!(fmt, "Record({es:#?})"),
            AST::Record(es) => write!(fmt, "Record({es:?})"),
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
        format!("{:#?}\n", Tokenizer::parse(tokens))
    }

    #[test]
    fn empty() {
        expect![[r#"
            Err(
                EOF,
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
