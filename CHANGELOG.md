# Current

## `define-language`

- Language from `(terminals ...)` + rules; each case becomes a
  `Lang:Nonterminal` / `Lang:Case` struct, checked by `typed/racket`.
- `,x` marks meta variables explicitly, so heads are never mistaken for fields.
- Ellipsis fields: `,e ...` and `[,x ,e] ...`.
- Untagged headed cases, e.g. `(,fn ,arg)`.
- Pretty forms: `case => pretty-form`, e.g. `(bind ,x ,ty) => (,x : ,ty)`, or
  `(let ([,x ,e] ...) ,e) => (let* ([,x = ,e] ...) in ,e)`. That's the form the
  language prints as and parses back from; only the literals move, so the
  pretty form has to use the case's own meta-variables in the case's order
  (checked at the grammar). `lang-construct` and `r/match*` keep using the
  grammar's `(lead ,field ...)` notation -- that's the shape the structs are
  named after.
- `extends`: inherit, add, remove cases; unchanged cases share the parent struct.
- Generates a `Lang->sexp` unparser.
- Generates a `sexp->Lang:Nonterminal` parser for each nonterminal, the
  unparser's inverse -- per nonterminal, since a bare s-expression doesn't say
  which one it belongs to, and no nonterminal is a privileged entry point.
  Terminal fields are checked at runtime (so a terminal's type has to be one
  `make-predicate` accepts); a case with two `...` fields prints but can't be
  parsed back, and says so.
- Unused terminals are still typechecked; a nested headed form as a field is a
  clear error.

## `lang-construct`

- Builds nodes in the grammar's own notation:

  ```racket
  (lang-construct Lang Nonterminal `(Add ,l ,r))
  ```

- `,@` splicing, including recursive.

## `r/match*`

- Matching with `#:lang` / `#:on`; `,[x]` recurs on a field.
- Omitted cases get a default clause rebuilding the node in the target
  language, so a pass mentions only what it changes.
- Scalar, list, and tuple-list field patterns.

## Examples

- `arith-opt.rkt`: constant folding and algebraic identities.
- `arith-to-asm.rkt`: register-allocated codegen, recursive `,@`.
- `surface-to-asm.rkt`: multi-language pipeline.

## Infrastructure

- CI: tests, coverage badge, docs on GitHub Pages.
