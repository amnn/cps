use std::{fmt, iter::Peekable};

use crate::lex::{Lexer, Token};

#[derive(Eq, PartialEq, Clone)]
pub(crate) enum Ast<'b> {
    Var(&'b str),
    Let(Vec<(&'b str, Lam<'b>)>, Box<Ast<'b>>),
    Lam(Box<Lam<'b>>),
    App(Box<Ast<'b>>, Vec<Ast<'b>>),
    Record(Vec<Ast<'b>>),
    Select(usize, Box<Ast<'b>>),
}

#[derive(Eq, PartialEq, Clone)]
pub(crate) struct Lam<'b>(pub Vec<&'b str>, pub Ast<'b>);

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
///           | <Word>        ;; variables
///
/// binds  ::= binds bind | ε
/// bind   ::= <Word> lambda
///
/// lambda ::= "(" "fn" "(" <Word>* ")" expr ")"
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

    fn expr(&mut self) -> Result<Ast<'b>, Error<'b>> {
        use Token as T;

        match self.next()? {
            T::Word(name) => return Ok(Ast::Var(name)),
            T::LPar => { /* fall through */ }
            t => return Err(Error::Unexpected(t)),
        }

        match self.peek()? {
            T::Word("let") => {
                self.bump();
                self.lexeme(T::LPar)?;
                let binds = self.tail(|p| {
                    let name = p.word()?;
                    p.lexeme(T::LPar)?;
                    let lambda = p.compound_lambda()?;
                    Ok((name, lambda))
                })?;

                let body = self.expr()?;
                self.lexeme(T::RPar)?;
                Ok(Ast::Let(binds, Box::new(body)))
            }

            T::Word("record") => {
                self.bump();
                Ok(Ast::Record(self.tail(Self::expr)?))
            }

            T::Word("select") => {
                self.bump();
                let ix = self.int()?;
                let expr = self.expr()?;
                self.lexeme(T::RPar)?;
                Ok(Ast::Select(ix, Box::new(expr)))
            }

            T::Word("fn") => Ok(Ast::Lam(Box::new(self.compound_lambda()?))),

            _ => {
                let fun = self.expr()?;
                Ok(Ast::App(Box::new(fun), self.tail(Self::expr)?))
            }
        }
    }

    /// Parses a lambda form, assuming the opening paren has been seen (and consumed).
    ///
    /// compound_lambda ::= "fn" "(" <Word>* ")" expr ")"
    fn compound_lambda(&mut self) -> Result<Lam<'b>, Error<'b>> {
        self.lexeme(Token::Word("fn"))?;
        self.lexeme(Token::LPar)?;
        let params = self.tail(Self::word)?;
        let body = self.expr()?;
        self.lexeme(Token::RPar)?;
        Ok(Lam(params, body))
    }

    fn tail<T, E>(&mut self, mut elem: E) -> Result<Vec<T>, Error<'b>>
    where
        E: FnMut(&mut Self) -> Result<T, Error<'b>>,
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

    fn word(&mut self) -> Result<&'b str, Error<'b>> {
        match self.peek()? {
            &Token::Word(w) => {
                self.bump();
                Ok(w)
            }

            tok => Err(Error::Unexpected(*tok)),
        }
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

impl<'b> fmt::Debug for Ast<'b> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Ast::Var(v) => write!(fmt, "Var({v:?})"),

            Ast::Let(binds, body) => {
                write!(fmt, "Let(")?;
                fmt.debug_map()
                    .entries(binds.iter().map(|(n, l)| (*n, l)))
                    .finish()?;
                write!(fmt, ", ")?;

                if fmt.alternate() {
                    write!(fmt, "{body:#?}")?;
                } else {
                    write!(fmt, "{body:?}")?;
                }

                write!(fmt, ")")
            }

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
                Var("a"),
            )
        "#]]
        .assert_eq(&parse(VARIABLE));
    }

    #[test]
    fn comment() {
        expect![[r#"
            Ok(
                Var("a"),
            )
        "#]]
        .assert_eq(&parse(COMMENT));
    }

    #[test]
    fn multi_comment() {
        expect![[r#"
            Ok(
                Var("b"),
            )
        "#]]
        .assert_eq(&parse(MULTI_COMMENT));
    }

    #[test]
    fn binding() {
        expect![[r#"
            Ok(
                Let({
                    "f": Lam(["x"], Var("x")),
                }, Let({
                    "g": Lam(["y"], Var("y")),
                }, Var("a"))),
            )
        "#]]
        .assert_eq(&parse(BINDING))
    }

    #[test]
    fn shadow() {
        expect![[r#"
            Ok(
                Record([
                    App(
                        Var("f"),
                        [
                            Var("x"),
                        ],
                    ),
                    Let({
                        "f": Lam(["x"], App(
                            Var("x"),
                            [
                                Var("f"),
                            ],
                        )),
                        "g": Lam(["g"], App(
                            Var("g"),
                            [
                                Var("x"),
                            ],
                        )),
                    }, App(
                        Var("f"),
                        [
                            Var("g"),
                        ],
                    )),
                    App(
                        Var("f"),
                        [
                            Var("x"),
                        ],
                    ),
                ]),
            )
        "#]]
        .assert_eq(&parse(SHADOW));
    }

    #[test]
    fn let_shadow() {
        expect![[r#"
            Ok(
                Let({
                    "f": Lam(["x"], App(
                        Var("f"),
                        [
                            Var("x"),
                        ],
                    )),
                    "f": Lam(["f"], App(
                        Var("f"),
                        [
                            Var("x"),
                        ],
                    )),
                }, Var("f")),
            )
        "#]]
        .assert_eq(&parse(LET_SHADOW));
    }

    #[test]
    fn apply() {
        expect![[r#"
            Ok(
                App(
                    Var("a"),
                    [
                        Var("b"),
                        Var("c"),
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
                Select(2, Var("a")),
            )
        "#]]
        .assert_eq(&parse(SELECT));
    }

    #[test]
    fn record() {
        expect![[r#"
            Ok(
                Record([
                    Var("a"),
                    Var("b"),
                    Var("c"),
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
                        Var("a"),
                        [
                            Var("b"),
                        ],
                    ),
                    [
                        App(
                            Var("c"),
                            [
                                Var("d"),
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
                    Var("a"),
                    [
                        Select(2, Var("b")),
                        Select(3, Var("c")),
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
                    Select(2, Var("a")),
                    Select(3, Var("b")),
                    Select(4, Var("c")),
                ]),
            )
        "#]]
        .assert_eq(&parse(RECORD_SELECT));
    }

    #[test]
    fn lambda() {
        expect![[r#"
            Ok(
                Lam(["x", "y", "z"], App(
                    Var("z"),
                    [
                        Var("y"),
                        Var("x"),
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
                Let({
                    "f": Lam(["x", "y"], Select(2, Var("x"))),
                }, Let({
                    "g": Lam(["x", "y"], Select(3, Var("y"))),
                }, Record([
                    Var("x"),
                    App(
                        Var("f"),
                        [
                            Var("y"),
                            Select(4, Var("z")),
                        ],
                    ),
                ]))),
            )
        "#]]
        .assert_eq(&parse(COMPLICATED));
    }

    #[test]
    fn loop_() {
        expect![[r#"
            Ok(
                Let({
                    "f": Lam(["x"], App(
                        Var("f"),
                        [
                            Select(0, Var("x")),
                        ],
                    )),
                }, Var("f")),
            )
        "#]]
        .assert_eq(&parse(LOOP));
    }

    #[test]
    fn co_recursive() {
        expect![[r#"
            Ok(
                Let({
                    "f": Lam(["x"], App(
                        Var("g"),
                        [
                            Var("x"),
                        ],
                    )),
                    "g": Lam(["x"], App(
                        Var("f"),
                        [
                            Var("x"),
                        ],
                    )),
                }, Var("f")),
            )
        "#]]
        .assert_eq(&parse(CO_RECURSIVE));
    }

    #[test]
    fn already_cps() {
        expect![[r#"
            Ok(
                Let({
                    "f": Lam(["x", "k"], App(
                        Var("k"),
                        [
                            Var("x"),
                        ],
                    )),
                }, Var("f")),
            )
        "#]]
        .assert_eq(&parse(ALREADY_CPS));
    }
}
