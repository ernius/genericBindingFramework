# Formalisation in Constructive Type Theory of  Barendregt's Variable Convention for Generic Structures with Binders

We introduce a universe of regular datatypes with variable binding information, for which we define generic formation, elimination, and induction operators. 
We then define a generic alpha-equivalence relation over the types of the universe based on name-swapping, and derive iteration and induction principles which work modulo alpha-conversion capturing  Barendregt's Variable Convention. We instantiate the resulting framework so as to obtain the Lambda Calculus and System F, for which we derive substitution operations and substitution lemmas for alpha-conversion and substitution composition. 
The whole work is carried out in Constructive Type Theory and machine-checked by the system Agda.

We generalise and improve techniques developed in the previous works:

1. [Substitution Lemmas](https://github.com/ernius/formalmetatheory-nominal)
2. [Church-Rosser and Subject Reduction](https://github.com/ernius/formalmetatheory-nominal-Church-Rosser)

, applying *generic programming* methods to address the formalisation of generic *structures with binders*.

# Examples

The principal usage examples are:
* [Examples/System F](https://github.com/ernius/genericBindingFramework/blob/master/Examples/SystemF.lagda)[(html format)](https://ernius.github.io/genericBindingFramework/html/Examples.SystemF.html)
* [Examples/Lambda Calculus](https://github.com/ernius/genericBindingFramework/blob/master/Examples/SystemF.lagda)[(html format)](https://ernius.github.io/genericBindingFramework/html/Examples.LambdaCalculus.html)

The entire code can be browsed in html format here: [https://ernius.github.io/genericBindingFramework/html/index.html](https://ernius.github.io/genericBindingFramework/html/index.html).

# Authors

* Ernesto Copello 
* Nora Szasz
* Álvaro Tasistro 

# Build Status in Travis CI : [![Build Status](https://travis-ci.org/ernius/genericBindingFramework.svg?branch=master)](https://travis-ci.org/ernius/genericBindingFramework)

Agda version 2.5.2 and standard library version 0.13.

Local compilation is available through [docker image](https://hub.docker.com/r/ecopello/agda/) typying `make docker`.


