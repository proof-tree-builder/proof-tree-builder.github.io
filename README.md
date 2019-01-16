# proof-tree-builder
Class project for COS516 with Prof. Zak Kincaid: A web-based interactive proof tree builder for LK and Hoare logic.

[Live here.](https://joom.github.io/proof-tree-builder/src/)

There are many bugs and incomplete parts.


# Generating the parser

```
pegjs --format globals --export-var peg --allowed-start-rules "Sequent,Formula,Term,HoareTriple,Command" parser.pegjs
```
