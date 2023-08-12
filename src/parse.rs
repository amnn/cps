use std::{iter::Peekable, str::FromStr};

use crate::lex::{Lexer, Token};

#[derive(Eq, PartialEq, Debug)]
pub(crate) enum LTerm {
    Free(String),
    Var(u32),
    Fix(Box<LTerm>, Box<LTerm>),
    Lam(Box<LTerm>),
    App(Box<LTerm>, Box<LTerm>),
    Record(Vec<LTerm>),
    Select(Box<LTerm>, u32),
}

#[derive(Debug)]
pub(crate) enum Error<'b> {
    Unexpected(Token, &'b str),
    EOF,
}

pub(crate) struct Tokenizer<'b>(Peekable<Lexer<'b>>);

/// Parses the following grammar
///
/// decl        := "fix" decl "in" decl
///              | "\" decl
///              | application
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
    pub(crate) fn parse(tokens: Lexer<'b>) -> Result<LTerm, Error<'b>> {
        let mut parser = Self(tokens.peekable());

        let term = parser.decl()?;
        if let Some(&(t, s)) = parser.peek() {
            Err(Error::Unexpected(t, s))
        } else {
            Ok(term)
        }
    }

    fn decl(&mut self) -> Result<LTerm, Error<'b>> {
        use LTerm as LT;
        use Token as T;

        match self.peek() {
            Some(&(T::BSlash, _)) => {
                self.bump();
                Ok(LT::Lam(Box::new(self.decl()?)))
            }

            Some(&(T::Word, "fix")) => {
                self.bump();
                let bind = self.decl()?;
                self.lexeme(T::Word, "in")?;
                let body = self.decl()?;
                Ok(LT::Fix(Box::new(bind), Box::new(body)))
            }

            _ => self.application(),
        }
    }

    fn application(&mut self) -> Result<LTerm, Error<'b>> {
        use LTerm as LT;
        let mut app = self.select()?;
        while let Ok(select) = self.select() {
            app = LT::App(Box::new(app), Box::new(select));
        }
        Ok(app)
    }

    fn select(&mut self) -> Result<LTerm, Error<'b>> {
        use LTerm as LT;
        use Token as T;

        let mut select = self.atom()?;
        while self.lexeme(T::Dot, ".").is_ok() {
            select = LT::Select(Box::new(select), self.read(T::Int)?);
        }

        Ok(select)
    }

    fn atom(&mut self) -> Result<LTerm, Error<'b>> {
        use LTerm as LT;
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
                Ok(LT::Free(w.to_owned()))
            }

            Some(&(T::Int, _)) => Ok(LT::Var(self.read(T::Int)?)),

            Some(&(tok, lex)) => Err(Error::Unexpected(tok, lex)),
        }
    }

    fn record(&mut self) -> Result<LTerm, Error<'b>> {
        use LTerm as LT;
        use Token as T;

        let mut elems = vec![];
        let mut delimited = true;
        loop {
            match self.peek() {
                None => return Err(Error::EOF),
                Some(&(T::Ket, _)) => {
                    self.bump();
                    return Ok(LT::Record(elems))
                },
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

fn is_keyword(w: &str) -> bool {
    matches!(w, "fix" | "in")
}


#[cfg(test)]
mod tests {
    use super::*;
    use expect_test::expect;

    fn parse<'b>(buf: &'b str) -> String {
        let tokens = Lexer::new(buf);
        format!("{:?}", Tokenizer::parse(tokens))
    }

    #[test]
    fn empty() {
        expect!["Err(EOF)"].assert_eq(&parse(""));
    }

    #[test]
    fn variable() {
        expect![[r#"Ok(Free("a"))"#]].assert_eq(&parse("a"));
    }

    #[test]
    fn binding() {
        expect![[r#"Ok(Fix(Var(0), Fix(Var(0), Free("a"))))"#]].assert_eq(&parse(r#"
          fix 0 in
          fix 0 in a
        "#))
    }

    #[test]
    fn application() {
        expect![[r#"Ok(App(App(Free("a"), Free("b")), Free("c")))"#]].assert_eq(&parse("a b c"));
    }

    #[test]
    fn apply_select() {
        expect![[r#"Ok(App(App(Free("a"), Select(Free("b"), 2)), Select(Free("c"), 3)))"#]].assert_eq(&parse("a b.2 c.3"));
    }

    #[test]
    fn select() {
        expect![[r#"Ok(Select(Free("a"), 2))"#]].assert_eq(&parse("a.2"));
    }

    #[test]
    fn record() {
        expect![[r#"Ok(Record([Free("a"), Free("b"), Free("c")]))"#]].assert_eq(&parse("[a, b, c]"));
    }

    #[test]
    fn record_select() {
        expect![[r#"Ok(Record([Select(Free("a"), 2), Select(Free("b"), 3), Select(Free("c"), 4)]))"#]].assert_eq(&parse("[a.2, b.3, c.4]"));
    }

    #[test]
    fn complicated() {
        expect![[r#"Ok(Fix(Lam(Select(Var(1), 2)), Fix(Lam(Select(Var(0), 3)), Record([Free("x"), App(App(Var(1), Free("y")), Select(Free("z"), 4))]))))"#]].assert_eq(&parse(r#"
            fix \ 1.2 in
            fix \ 0.3 in
              [x, 1 y z.4]
        "#));
    }
}
