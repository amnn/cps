use std::{iter::Peekable, str::CharIndices};

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub(crate) enum Token {
    BSlash, // "\"
    Comma,  // ","
    Dot,    // "."
    Int,    // integer literals
    Word,   // identifiers
    Bra,    // "["
    Ket,    // "]"
    LPar,   // "("
    RPar,   // ")"
}

#[derive(Clone)]
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

    fn eat(&mut self, pred: impl Fn(&char) -> bool) -> Option<usize> {
        loop {
            let (ix, c) = self.cursor.peek()?;
            if pred(c) {
                self.cursor.next();
            } else {
                return Some(*ix);
            }
        }

    }

    fn gather(&mut self, from: usize, pred: impl Fn(&char) -> bool) -> &'b str {
        match self.eat(pred) {
            Some(to) => &self.buf[from..to],
            None => &self.buf[from..],
        }
    }
}

impl<'b> Iterator for Lexer<'b> {
    type Item = (Token, &'b str);

    fn next(&mut self) -> Option<Self::Item> {
        self.eat(|c| c.is_whitespace());
        let (ix, c) = self.cursor.next()?;

        match c {
            '\\' => Some((Token::BSlash, &self.buf[ix..ix + 1])),
            ','  => Some((Token::Comma,  &self.buf[ix..ix + 1])),
            '.'  => Some((Token::Dot,    &self.buf[ix..ix + 1])),
            '['  => Some((Token::Bra,    &self.buf[ix..ix + 1])),
            ']'  => Some((Token::Ket,    &self.buf[ix..ix + 1])),
            '('  => Some((Token::LPar,   &self.buf[ix..ix + 1])),
            ')'  => Some((Token::RPar,   &self.buf[ix..ix + 1])),

            n if n.is_numeric() => Some((Token::Int, self.gather(ix, |c| c.is_numeric()))),
            c if c.is_ascii_alphabetic() || c == '_' => Some((
                Token::Word,
                self.gather(ix, |c| c == &'_' || c.is_ascii_alphanumeric()),
            )),

            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use expect_test::expect;

    fn lex<'b>(buf: &'b str) -> String {
        format!("{:?}", Lexer::new(buf).collect::<Vec<_>>())
    }

    #[test]
    fn empty() {
        expect!["[]"].assert_eq(&lex(""));
    }

    #[test]
    fn variable() {
        expect![[r#"[(Word, "a")]"#]].assert_eq(&lex("a"));
    }

    #[test]
    fn binding() {
        expect![[r#"[(Word, "fix"), (Int, "0"), (Word, "in"), (Word, "fix"), (Int, "0"), (Word, "in"), (Word, "a")]"#]].assert_eq(&lex(r#"
          fix 0 in
          fix 0 in a
        "#));
    }

    #[test]
    fn application() {
        expect![[r#"[(Word, "a"), (Word, "b"), (Word, "c")]"#]].assert_eq(&lex("a b c"));
    }

    #[test]
    fn apply_select() {
        expect![[r#"[(Word, "a"), (Word, "b"), (Dot, "."), (Int, "2"), (Word, "c"), (Dot, "."), (Int, "3")]"#]].assert_eq(&lex("a b.2 c.3"));
    }

    #[test]
    fn select() {
        expect![[r#"[(Word, "a"), (Dot, "."), (Int, "2")]"#]].assert_eq(&lex("a.2"));
    }

    #[test]
    fn record() {
        expect![[r#"[(Bra, "["), (Word, "a"), (Comma, ","), (Word, "b"), (Comma, ","), (Word, "c"), (Ket, "]")]"#]].assert_eq(&lex("[a, b, c]"))
    }

    #[test]
    fn record_select() {
        expect![[r#"[(Bra, "["), (Word, "a"), (Dot, "."), (Int, "2"), (Comma, ","), (Word, "b"), (Dot, "."), (Int, "3"), (Comma, ","), (Word, "c"), (Dot, "."), (Int, "4"), (Ket, "]")]"#]].assert_eq(&lex("[a.2, b.3, c.4]"))
    }

    #[test]
    fn complicated() {
        expect![[r#"[(Word, "fix"), (BSlash, "\\"), (Int, "1"), (Dot, "."), (Int, "2"), (Word, "in"), (Word, "fix"), (BSlash, "\\"), (Int, "0"), (Dot, "."), (Int, "3"), (Word, "in"), (Bra, "["), (Word, "x"), (Comma, ","), (Int, "1"), (Word, "y"), (Word, "z"), (Dot, "."), (Int, "4"), (Ket, "]")]"#]].assert_eq(&lex(r#"
          fix \ 1.2 in
          fix \ 0.3 in
            [x, 1 y z.4]
        "#));
    }
}