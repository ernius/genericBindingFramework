# Generic Binding Framework

In this work we generalise the techniques developed in the preceding works:

1. [Substitution Lemmas](https://github.com/ernius/formalmetatheory-nominal)
2. [Church-Rosser and Subject Reduction](https://github.com/ernius/formalmetatheory-nominal-Church-Rosser)

, applying *generic programming* methods to address the formalisation of generic *structures with binders*.

We define a universe of regular datatypes with variable binding information, and on  these we define generic formation, elimination, and induction operators. We also introduce an alpha-equivalence relation based on the swapping operation, and we derive alpha-iteration/induction principles that capture the BVC.

# Examples

The principal usage examples are (html):
* [System F](https://ernius.github.io/genericBindingFramework/html/Examples.SystemF.html)
* [Lambda Calculus](https://ernius.github.io/genericBindingFramework/html/Examples.LambdaCalculus.html)

The entire code can be browsed in html format here: [https://ernius.github.io/genericBindingFramework/html/index.html](https://ernius.github.io/genericBindingFramework/html/index.html).

# Authors

* Ernesto Copello 
* Nora Szasz
* Álvaro Tasistro 

# Build Status in Travis CI : [![Build Status](https://travis-ci.org/ernius/genericBindingFramework.svg?branch=master)](https://travis-ci.org/ernius/genericBindingFramework)

Agda version 2.5.2 and standard library version 0.13.

Code compilation available through [docker image](https://hub.docker.com/r/ecopello/agda/) typying `make docker`.


