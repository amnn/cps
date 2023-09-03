use std::{iter::Peekable, str::CharIndices};

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub(crate) enum Token<'b> {
    Int(usize),    // integer literals
    Word(&'b str), // identifiers
    LPar,          // "("
    RPar,          // ")"
}

#[derive(Clone, Debug)]
pub(crate) struct Lexer<'b> {
    buf: &'b str,
    cursor: Peekable<CharIndices<'b>>,
}

impl<'b> Lexer<'b> {
    pub(crate) fn new(buf: &'b str) -> Self {
        Lexer {
            buf,
            cursor: buf.char_indices().peekable(),
        }
    }

    fn eat(&mut self, pred: impl Fn(char) -> bool) -> Option<usize> {
        loop {
            let (ix, c) = self.cursor.peek()?;
            if pred(*c) {
                self.cursor.next();
            } else {
                return Some(*ix);
            }
        }
    }

    fn gather(&mut self, from: usize, pred: impl Fn(char) -> bool) -> &'b str {
        match self.eat(pred) {
            Some(to) => &self.buf[from..to],
            None => &self.buf[from..],
        }
    }
}

impl<'b> Iterator for Lexer<'b> {
    type Item = Token<'b>;

    fn next(&mut self) -> Option<Self::Item> {
        self.eat(is_whitespace);
        while let Some((_, ';')) = self.cursor.peek() {
            self.eat(|c| c != '\n');
            self.eat(is_whitespace);
        }

        let (ix, c) = self.cursor.next()?;
        match c {
            '(' => Some(Token::LPar),
            ')' => Some(Token::RPar),

            c if is_ident_start(c) => Some(Token::Word(self.gather(ix, is_ident_rest))),

            n if n.is_numeric() => {
                let int: usize = self.gather(ix, |c| c.is_numeric()).parse().unwrap();
                Some(Token::Int(int))
            }

            _ => None,
        }
    }
}

fn is_whitespace(c: char) -> bool {
    c.is_whitespace() || c == ','
}

fn is_ident_start(c: char) -> bool {
    !c.is_whitespace() && !matches!(c, '(' | ')' | ';' | '0'..='9')
}

fn is_ident_rest(c: char) -> bool {
    !c.is_whitespace() && !matches!(c, '(' | ')' | ';')
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fixtures::*;
    use expect_test::expect;

    fn lex<'b>(buf: &'b str) -> String {
        Lexer::new(buf)
            .map(|t| format!("{t:?}\n"))
            .collect::<Vec<_>>()
            .join("")
    }

    #[test]
    fn empty() {
        expect![""].assert_eq(&lex(EMPTY));
    }

    #[test]
    fn variable() {
        expect![[r#"
            Word("a")
        "#]]
        .assert_eq(&lex(VARIABLE));
    }

    #[test]
    fn comment() {
        expect![[r#"
            Word("a")
        "#]]
        .assert_eq(&lex(COMMENT));
    }

    #[test]
    fn multi_comment() {
        expect![[r#"
            Word("b")
        "#]]
        .assert_eq(&lex(MULTI_COMMENT));
    }

    #[test]
    fn binding() {
        expect![[r#"
            LPar
            Word("let")
            LPar
            Int(1)
            Int(0)
            RPar
            LPar
            Word("let")
            LPar
            Int(1)
            Int(0)
            RPar
            Word("a")
            RPar
            RPar
        "#]]
        .assert_eq(&lex(BINDING));
    }

    #[test]
    fn apply() {
        expect![[r#"
            LPar
            Word("a")
            Word("b")
            Word("c")
            RPar
        "#]]
        .assert_eq(&lex(APPLY));
    }

    #[test]
    fn select() {
        expect![[r#"
            LPar
            Word("select")
            Int(2)
            Word("a")
            RPar
        "#]]
        .assert_eq(&lex(SELECT));
    }

    #[test]
    fn record() {
        expect![[r#"
            LPar
            Word("record")
            Word("a")
            Word("b")
            Word("c")
            RPar
        "#]]
        .assert_eq(&lex(RECORD));
    }

    #[test]
    fn apply_nested() {
        expect![[r#"
            LPar
            LPar
            Word("a")
            Word("b")
            RPar
            LPar
            Word("c")
            Word("d")
            RPar
            RPar
        "#]]
        .assert_eq(&lex(APPLY_NESTED));
    }

    #[test]
    fn apply_select() {
        expect![[r#"
            LPar
            Word("a")
            LPar
            Word("select")
            Int(2)
            Word("b")
            RPar
            LPar
            Word("select")
            Int(3)
            Word("c")
            RPar
            RPar
        "#]]
        .assert_eq(&lex(APPLY_SELECT));
    }

    #[test]
    fn record_select() {
        expect![[r#"
            LPar
            Word("record")
            LPar
            Word("select")
            Int(2)
            Word("a")
            RPar
            LPar
            Word("select")
            Int(3)
            Word("b")
            RPar
            LPar
            Word("select")
            Int(4)
            Word("c")
            RPar
            RPar
        "#]]
        .assert_eq(&lex(RECORD_SELECT));
    }

    #[test]
    fn lambda() {
        expect![[r#"
            LPar
            Word("fn")
            LPar
            Int(3)
            RPar
            LPar
            Int(0)
            Int(1)
            Int(2)
            RPar
            RPar
        "#]]
        .assert_eq(&lex(LAMBDA));
    }

    #[test]
    fn complicated() {
        expect![[r#"
            LPar
            Word("let")
            LPar
            Int(2)
            LPar
            Word("select")
            Int(2)
            Int(1)
            RPar
            RPar
            LPar
            Word("let")
            LPar
            Int(2)
            LPar
            Word("select")
            Int(3)
            Int(0)
            RPar
            RPar
            LPar
            Word("record")
            Word("x")
            LPar
            Int(1)
            Word("y")
            LPar
            Word("select")
            Int(4)
            Word("z")
            RPar
            RPar
            RPar
            RPar
            RPar
        "#]]
        .assert_eq(&lex(COMPLICATED));
    }

    #[test]
    fn loop_() {
        expect![[r#"
            LPar
            Word("let")
            LPar
            Int(1)
            LPar
            Int(1)
            LPar
            Word("select")
            Int(0)
            Int(0)
            RPar
            RPar
            RPar
            Int(0)
            RPar
        "#]]
        .assert_eq(&lex(LOOP));
    }

    #[test]
    fn co_recursive() {
        expect![[r#"
            LPar
            Word("let")
            LPar
            Int(1)
            LPar
            Int(1)
            Int(0)
            RPar
            Int(1)
            LPar
            Int(2)
            Int(0)
            RPar
            RPar
            Int(1)
            RPar
        "#]]
        .assert_eq(&lex(CO_RECURSIVE));
    }

    #[test]
    fn already_cps() {
        expect![[r#"
            LPar
            Word("let")
            LPar
            Int(2)
            LPar
            Int(0)
            Int(1)
            RPar
            RPar
            Int(0)
            RPar
        "#]]
        .assert_eq(&lex(ALREADY_CPS));
    }
}
