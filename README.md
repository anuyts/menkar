# Menkar - the multimode presheaf proof assistant
Menkar is (will be) a dependently typed programming language with a special focus on supporting modal and even multimode type systems, as well as type systems based on presheaf models.

It is named after the star [Alpha Ceti](https://en.wikipedia.org/wiki/Alpha_Ceti).

## Features
Currently supported features include:

* type-checking of basic MLTT with natural numbers, Π- and Σ-types, empty, unit and box types, an identity type and function extensionality,
* a single universe that (inconsistently) contains itself,
* implicit arguments in the sense of Agda.

Partly implemented (but presently unusable) features include:

* support for multimode modality systems,
* support for type systems in which type and term have a different modality, via a parametric function `El : {par | Uni} -> UniHS` from a fibrant universe to a possibly non-fibrant (Hofmann-Streicher)-universe whose codes can be promoted to the type level continuously,
* a [definitional relatedness](https://doi.org/10.1145/3209108.3209119) checker (despite linking to Nuyts & Devriese, the concept was coined by Andrea Vezzosi), which may allow for the non-consideration of irrelevant subterms during conversion-checking.

Planned features include:

* instance arguments - a feature analogous to Agda's [instance arguments](https://doi.org/10.1145/2034574.2034796) and Haskell's typeclasses.
A **resolution** is essentially a user-defined open ad-hoc function which takes the role of Agda's and Haskell's instance resolution. **Instance arguments** are arguments annotated with a resolution; their values need not be actively passed, as they can be resolved.
* the resolution-features necessary to implement a relatedness-checker *within* Menkar,
* internal crisp mode and modality polymorphism,
* support for context exponentiation (for working with dependably [atomic](https://ncatlab.org/nlab/show/tiny+object) objects),
* internal presheaf operators, to wit: **fresh weakening** (the left adjoint to the Π-type over substructural shape variables), [amazing](https://ncatlab.org/nlab/show/amazing+right+adjoint) dependent right adjoints (which we prefer to call **transpension types**; these are right adjoint to the Π-type over substructural shape variables), the **initial type extension** (also called Weld) and the **final type extension** (also called Glue). From these, one can implement Moulin's [**Ψ-type**](https://research.chalmers.se/publication/235758).
* perhaps a (somewhat unsound) framework to build inductive and co-inductive types from scratch,
* subtyping (very long term).

## Type systems
Some type systems that we aim to support, are:

* MLTT (already supported),
* cubical type theory,
* [degrees of relatedness](https://people.cs.kuleuven.be/~andreas.nuyts/paper-reldtt.pdf) - hence also [ParamDTT](https://doi.org/10.1145/3110276),
* directed type theory,
* guarded type theory with [time warps](https://arxiv.org/abs/1805.11021v1).

Where applicable, we may or may not want to include diagonals, symmetries and connections in the base category, as well as generalize from binary to n-ary systems.

## Other remarks
Menkar is still in early development. We absolutely do not guarantee any form of backwards compatibility at this stage.

## More info?
Don't hesitate to contact me if this project sparks your interest.
