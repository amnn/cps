pub(crate) const EMPTY: &str = "";

pub(crate) const VARIABLE: &str = r#"
a
"#;

pub(crate) const COMMENT: &str = r#"
a ; a comment
"#;

pub(crate) const MULTI_COMMENT: &str = r#"
; line 1
; line 2
b
"#;

pub(crate) const BINDING: &str = r#"
(let (1 0) (let (1 0) a))
"#;


pub(crate) const APPLY: &str = r#"
(a b c)
"#;

pub(crate) const SELECT: &str = r#"
(select 2 a)
"#;

pub(crate) const RECORD: &str = r#"
(record a b c)
"#;

pub(crate) const APPLY_NESTED: &str = r#"
((a b) (c d))
"#;

pub(crate) const APPLY_SELECT: &str = r#"
(a (select 2 b) (select 3 c))
"#;

pub(crate) const RECORD_SELECT: &str = r#"
(record
  (select 2 a)
  (select 3 b)
  (select 4 c))
"#;

pub(crate) const LAMBDA: &str = r#"
(fn (3) (0 1 2))
"#;

pub(crate) const COMPLICATED: &str = r#"
(let (2 (select 2 1))
  (let (2 (select 3 0))
    (record x (1 y (select 4 z)))))
"#;

pub(crate) const LOOP: &str = r#"
(let (1 (1 (select 0 0))) 0)
"#;


pub(crate) const CO_RECURSIVE: &str = r#"
(let (1 (1 0) 1 (2 0)) 1)
"#;


pub(crate) const ALREADY_CPS: &str = r#"
(let (2 (0 1)) 0)
"#;
