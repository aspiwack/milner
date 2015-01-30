Milner-style tactics
====================

A small implementation of Milner-style tactics (for propositional
minimal logic) for an article of mine.

### Licence ###

The code in this repository is just too short to deserve a licence. It
is freely available, period.

### Remark ###

As far as Ocaml code goes, the code you will find in this repository
positively horrible (I even deactivated all warnings during
compilation). The goal was to make something that was lightweight to
read in an article, not to write good code. And it certainly shows.

### Compilation ###

To compile this code, you need will Ocaml 4.02 (or later) the `PPrint`
pretty-printing library installed with ocamlfind support (for instance
via Opam).

You can then compile it and run the examples with `ocamlbuild
example.byte --` (the `--` tells Ocamlbuild to run `example.byte`
after compiling it).