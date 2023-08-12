pub(crate) const EMPTY: &str = "";

pub(crate) const VARIABLE: &str = r#"
a
"#;

pub(crate) const COMMENT: &str = r#"
a # a comment
"#;

pub(crate) const BINDING: &str = r#"
fix \ 0 in
fix \ 0 in
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

pub(crate) const APPLY_SELECT: &str = r#"
a b.2 c.3
"#;

pub(crate) const RECORD_SELECT: &str = r#"
[a.2, b.3, c.4]
"#;

pub(crate) const COMPLICATED: &str = r#"
fix \\ 1.2 in
fix \\ 0.3 in
  [x, 1 y z.4]
"#;
