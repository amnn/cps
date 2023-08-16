pub(crate) const EMPTY: &str = "";

pub(crate) const VARIABLE: &str = r#"
a
"#;

pub(crate) const COMMENT: &str = r#"
a # a comment
"#;

pub(crate) const BINDING: &str = r#"
let \ 0 in
let \ 0 in
  a
"#;

pub(crate) const APPLY: &str = r#"
a b c
"#;

pub(crate) const SELECT: &str = r#"
a.2
"#;

pub(crate) const RECORD: &str = r#"
[a, b, c]
"#;

pub(crate) const APPLY_NESTED: &str = r#"
(a b) (c d)
"#;

pub(crate) const APPLY_SELECT: &str = r#"
a b.2 c.3
"#;

pub(crate) const RECORD_SELECT: &str = r#"
[a.2, b.3, c.4]
"#;

pub(crate) const LAMBDA: &str = r#"
\\\ 0 1 2
"#;

pub(crate) const COMPLICATED: &str = r#"
let \\ 1.2 in
let \\ 0.3 in
  [x, 1 y z.4]
"#;

pub(crate) const LOOP: &str = r#"
let \ 1 0.0 in 0
"#;

pub(crate) const CO_RECURSIVE: &str = r#"
let \ 1 0
and \ 2 0
in 1
"#;

pub(crate) const ALREADY_CPS: &str = r#"
let \\ 0 1 in 0
"#;
