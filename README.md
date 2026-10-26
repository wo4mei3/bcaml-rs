# Core Language Evaluator

This project implements a small ML-like core language as a compact Rust prototype. The repository now defines its own language behavior directly rather than relying on a historical Caml Light implementation as the specification.

See [SPEC.md](./SPEC.md) for the language definition.

## Supported subset

- Literals: integers, floats, strings, characters, booleans, unit
- Expressions: variables, function literals, applications, tuples, lists, conditionals, `let` and `let rec`
- Pattern matching: wildcard, variable, tuple, list constructor, and simple constructor patterns
- Types: Hindley-Milner style inference with function, tuple, and list types
- Runtime: lexical scoping, closures, recursive bindings, refs, and basic primitive operations

## Running the interpreter

```sh
cargo run -- source.ml
```

For interactive use, omit the file argument:

```sh
cargo run
```

## Language notes

The evaluator is intentionally small and educational. It focuses on a core ML subset with REPL behavior, script-mode execution, and type-driven evaluation.

## Example

```ocaml
let rec fact n = if n <= 1 then 1 else n * fact (n - 1);;
fact 5;;
```
