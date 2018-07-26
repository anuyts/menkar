# Menkar
Menkar is (will be) a dependently typed programming language supporting the following features:

* implicit arguments in the sense of Agda,
* minion arguments - a feature analogous to Agda's [instance arguments](https://doi.org/10.1145/2034574.2034796) and Haskell's typeclasses.
A summoning is a user-defined open ad-hoc function mapping some object (typically a type) to another object (called the minion, typically a set of operations over the type) which takes the role of Agda's and Haskell's instance resolution. Minion arguments are arguments annotated with a summoning; there values need not be actively passed, as they can be summoned.
* support for multimode modality systems with type/term differentiation,
* support for context exponentiation (for working with [tiny](https://ncatlab.org/nlab/show/tiny+object) objects),
* internal presheaf operators,
* the possibility to implement inductive and co-inductive types from scratch by unsafely resizing their Church encoding
(which is about as unsafe as omitting the strict positivity check),
* erasure of irrelevant subterms,
* non-unique resolution of irrelevant metavariables,
* internal shape-irrelevant universe polymorphism,
* pseudopolymorphism for modes and modalities (pseudoparameters must be instantiated before type checking),
* subtyping (very long term - even for universes we can use a lift function).

It is named after the star Alpha Ceti, which is nicknamed Menkar.
