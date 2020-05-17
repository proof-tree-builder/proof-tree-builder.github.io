# proof-tree-builder
Class project for COS516 with Prof. Zak Kincaid: A web-based interactive proof tree builder for LK and Hoare logic. Later improved as a class project for COS598B with Prof. Aarti Gupta.

[Live here.](https://joom.github.io/proof-tree-builder/src/)

There are many bugs and incomplete parts.

# Guide

You can click the "Add LK goal" button to add a new sequent calculus goal to prove, such as

* `exists x. g(x) |- exists y. g(y)`
* `exists x. g(k,x) |- exists y. g(k,y)`
* `|- ((p -> q) -> p) -> p`
* `x > 0 |- x > 1` (this one cannot be proved without Z3)

Or you can click the "Add Hoare logic goal" button to add a new Hoare triple, such as

* `{true} if true then x := 3 else x := 5 {x = 3}`
* `{true} if x < 0 then x := -1 * x else x := x {x >= 0}`

# Generating the parser

```
pegjs --format globals --export-var peg --allowed-start-rules "Sequent,Formula,Term,HoareTriple,Command" parser.pegjs
```
