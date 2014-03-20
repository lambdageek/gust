gust
====

Small language with Pierce/Turner type inference.

There's a syntax, some semantic types, a parser and a typechecker here.  The typechecker uses bidirectional typechecking with local type inference on function applications to infer the type arguments based on the synthesized types of the expression arguments.

Some examples in the `examples/` directory.  Use with GHCi and the `rp` function from `Example.hs`

There is no pretty printer, so everything is ugly.
