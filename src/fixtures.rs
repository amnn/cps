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
(let (f (fn (x) x))
  (let (g (fn (y) y))
    a))
"#;

pub(crate) const SHADOW: &str = r#"
(record
  (f x)
  (let (f (fn (x) (x f))
        g (fn (g) (g x)))
    (f g))
  (f x))
"#;

pub(crate) const LET_SHADOW: &str = r#"
(let (f (fn (x) (f x))
      f (fn (f) (f x)))
  f)
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
(fn (x y z) (z y x))
"#;

pub(crate) const COMPLICATED: &str = r#"
(let (f (fn (x y) (select 2 x)))
  (let (g (fn (x y) (select 3 y)))
    (record x (f y (select 4 z)))))
"#;

pub(crate) const LOOP: &str = r#"
(let (f (fn (x) (f (select 0 x)))) f)
"#;

pub(crate) const CO_RECURSIVE: &str = r#"
(let (f (fn (x) (g x))
      g (fn (x) (f x)))
  f)
"#;

pub(crate) const ALREADY_CPS: &str = r#"
(let (f (fn (x k) (k x))) f)
"#;
