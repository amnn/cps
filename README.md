# CPS

A small Rust compiler playground for experimenting with transformations over a
Lisp-like toy language. The current pipeline lexes and parses the source,
replaces local names with de Bruijn indices, and converts the result to
continuation-passing style (CPS).

## Running

Pass a source file, or use `-` to read from standard input. `--Xdump` prints the
state after one or more compiler phases: `lex`, `parse`, `naming`, or `cps`.

```sh
printf '(fn (x) x)\n' | cargo run -- --Xdump cps -
```

Run the test suite with:

```sh
cargo test
```
