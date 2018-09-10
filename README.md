# Menkar
Menkar is (will be) a dependently typed programming language supporting the following features:

* implicit arguments in the sense of Agda,
* instance arguments - a feature analogous to Agda's [instance arguments](https://doi.org/10.1145/2034574.2034796) and Haskell's typeclasses.
A **resolution** is essentially a user-defined open ad-hoc function which takes the role of Agda's and Haskell's instance resolution. **Instance arguments** are arguments annotated with a resolution; their values need not be actively passed, as they can be resolved.
* support for multimode modality systems
* support for type systems in which type and term have a different modality, via a parametric function `El : {par | Uni} -> UniHS` from a fibrant universe to a possibly non-fibrant (Hofmann-Streicher)-universe whose codes can be promoted to the type level continuously.
* a 'crisp' modality for dependencies that respect no relational structure whatsoever
* internal crisp mode and modality polymorphism,
* internal shape-irrelevant universe polymorphism,
* support for context exponentiation (for working with dependably [atomic](https://ncatlab.org/nlab/show/tiny+object) objects),
* internal presheaf operators, to wit: **fresh weakening** (for non-cartesian base categories), amazing dependent right adjoints (which we prefer to call **transpension types**), and the **initial type extension** (also called Weld type).
From these, one can implement the **final type extension** (Glue) and the **Ψ-type**.
* the possibility to implement inductive and co-inductive types from scratch by unsafely resizing their Church encoding
(which is about as unsafe as omitting the strict positivity check),
* erasure of irrelevant subterms,
* non-unique resolution of irrelevant metavariables,
* subtyping (very long term - even for universes we can use a lift function).

It is named after the star Alpha Ceti.

## Loading/building
Here are some packages currently in use:

* ~~`categories` - Note: you need to add `PolyKinds` to Control.Categorical.Functor.~~
* `megaparsec`
* `nat`
