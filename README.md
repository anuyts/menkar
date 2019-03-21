# Menkar - the multimode presheaf proof assistant
Menkar is (will be) a dependently typed programming language with a special focus on supporting modal and even multimode type systems, as well as type systems based on presheaf models.

It is named after the star [Alpha Ceti][alphaceti].

## Features
Currently supported features include:

* type-checking of basic MLTT with natural numbers, Π- and Σ-types, empty, unit and box types, an identity type and function extensionality,
* a command-line interaction mode that provides the user with a wealth of information, including stack traces for almost everything,
* a single universe that (inconsistently) contains itself,
* smart eliminations, including
   * implicit arguments in the sense of Agda,
   * named arguments,
   * implicit unboxing,
   * named and numbered projections for nested Σ-types.

Partly implemented (but presently unusable) features include:

* support for multimode modality systems,
* internal crisp mode and modality polymorphism,
* support for type systems in which type and term have a different modality, via a parametric function `El : {par | Uni} -> UniHS` from a fibrant universe to a possibly non-fibrant (Hofmann-Streicher)-universe whose codes can be promoted to the type level continuously,
* a [definitional relatedness][reldtt] checker (coined by A. Vezzosi), which may allow for the non-consideration of irrelevant subterms during conversion-checking.

Planned features include:

* instance arguments - a feature analogous to Agda's [instance arguments][bright-side-of-typeclasses] and Haskell's typeclasses.
A **resolution** is essentially a user-defined open ad-hoc function which takes the role of Agda's and Haskell's instance resolution. **Instance arguments** are arguments annotated with a resolution; their values need not be actively passed, as they can be resolved,
* the resolution-features necessary to implement a relatedness-checker *within* Menkar,
* non-recursive HITs via a type former for pushouts along `ΣBφ -> B` (a codependent coproduct),
* non-recursive QITs via a type former for pushouts along `B + B -> B`,
* recursive HITs and QITs via a type former for taking the least fixpoint of a polynomial quotient of a pointed indexed polynomial functor (a very fancy W-type),
* support for context exponentiation (for working with dependably [atomic][nlab-tiny] objects),
*  internal presheaf operators, to wit:

   * definitional extension types,
   * dependent right adjoints (which we prefer to call **transpension types**; these are right adjoint to the Π-type over substructural shape variables),
   * Orton and Pitts's [**strictness**][strictness] axiom.

   From these, one can implement the initial and final type extension operations Glue and Weld, and Moulin's [**Ψ-type**][psi],
* smart constructors, perhaps including
   * implicit first components,
   * named first components,
   * implicit boxing,
   * named and numbered injections for nested codependent coproduct types.
* subtyping (very long term).

## Type systems
Some type systems that we aim to support, are:

* MLTT (already supported),
* cubical type theory,
* [degrees of relatedness][reldtt] - hence also [ParamDTT][paramdtt],
* directed type theory,
* guarded type theory with multiple clocks and [time warps][time-warps].

Where applicable, the user may ask to include/exclude/agnosticlude diagonals, symmetries and connections in the base category, as well as generalize from binary to n-ary systems.

## Other remarks
Menkar is still in early development. We absolutely do not guarantee any form of backwards compatibility at this stage.

## More info?
Don't hesitate to contact me if this project sparks your interest.

[alphaceti]: https://en.wikipedia.org/wiki/Alpha_Ceti
[reldtt]: https://doi.org/10.1145/3209108.3209119
[bright-side-of-typeclasses]: https://doi.org/10.1145/2034574.2034796
[nlab-tiny]: https://ncatlab.org/nlab/show/tiny+object
[nlab-amazing]: https://ncatlab.org/nlab/show/amazing+right+adjoint
[psi]: https://research.chalmers.se/publication/235758
[paramdtt]: https://doi.org/10.1145/3110276
[strictness]: https://doi.org/10.23638/LMCS-14(4:23)2018
[time-warps]: https://arxiv.org/abs/1805.11021v1
