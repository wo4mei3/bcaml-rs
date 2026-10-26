# Core Language Specification

This project defines a compact ML-like core language designed for teaching, experimentation, and REPL-style evaluation. The implementation is intentionally small and self-contained.

## 1. Values

The runtime supports:

- integers: `42`
- floats: `3.14`
- strings: `"hello"`
- characters: `'a'`
- booleans: `true`, `false`
- unit: `()`
- tuples: `(1, 2)`
- lists: `1 :: 2 :: []`
- closures created by `fun`
- references created by `ref`

## 2. Expressions

The expression grammar includes:

- variables and constants
- lambda expressions: `fun x -> body`
- applications: `f x`
- let bindings: `let x = e1 in e2` and `let rec x = e1 in e2`
- conditionals: `if cond then a else b`
- pattern matching: `match e with | p1 -> e1 | ...`
- tuples and lists
- sequencing through `;`
- exceptions and handlers in the same subset style as ML

## 3. Typing model

The type system is a Hindley-Milner style inference engine:

- each variable receives a type variable at first use
- `let` generalizes polymorphic types
- function types are written as `A -> B`
- tuples have product types `(A * B)`
- lists use `A list`

## 4. Evaluation model

Evaluation is eager and lexical:

- variables resolve in the current environment
- closures capture their defining environment
- recursive definitions bind names before evaluation completes
- pattern matching checks constructors and subpatterns structurally
- script mode suppresses REPL-level result printing, while REPL mode prints values and types

## 5. REPL behavior

The interpreter accepts phrases terminated with `;;` in interactive mode.

- REPL mode prints `val name : type = value` for bindings
- REPL mode prints `- : type = value` for top-level expressions
- script mode remains quiet and is intended for execution of source files

## 6. Supported subset for this project

This implementation intentionally targets a compact teaching subset rather than a full industrial ML compiler. It covers the features needed for simple functional examples and parser/evaluator experiments.

## 7. Design principle

The repository aims to define its own language behavior in a small, understandable form. It does not depend on a historical Caml Light source base as the specification itself.
