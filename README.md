A modular module system
=======================

[JFP 2000 paper](http://caml.inria.fr/pub/papers/xleroy-modular_modules-jfp.pdf) and [code](http://gallium.inria.fr/~xleroy/publi/modular-modules-appendix/)
by [Xavier Leroy](http://gallium.inria.fr/~xleroy/)

## Base language-independent code

* modules.ml: the type-checker for modules described in section 2 of the paper.
* modules.ml.extended: a version of the above with the relaxed typing rule for functor applications described in section 5.5.

## First application: mini C (section 3.1)

* miniC.ml: abstract syntax and type-checker for mini-C.
* miniClexer.mll: ocamllex lexical analyzer for mini-C.
* miniCparser.mly: ocamlyacc parser for mini-C.
* miniCmain.ml: driver program for mini-C, typechecks the source given on standard input and prints the inferred types.
example.miniC: an example of mini-C program with structures and functors.

## Second application: mini ML (section 3.2)

* miniML.ml: abstract syntax and type-checker for mini-ML.
* miniMLlexer.mll: ocamllex lexical analyzer for mini-ML.
* miniMLparser.mly: ocamlyacc parser for mini-ML.
* miniMLmain.ml: driver program for mini-ML, typechecks the source given on standard input and prints the inferred types.
* example.miniML: an example of mini-ML program with structures and functors.
