# Menkar
Menkar is (will be) a dependently typed programming language supporting the following features:

* implicit arguments in the sense of Agda,
* [instance arguments](https://doi.org/10.1145/2034574.2034796) in the sense of Agda,
* support for multimode modality systems with type/term differentiation,
* support for context exponentiation (for working with [tiny](https://ncatlab.org/nlab/show/tiny+object) objects),
* internal presheaf operators,
* the possibility to implement co-inductive types using unsafe coercion (which is about as unsafe as omitting the strict positivity check),
* erasure of irrelevant subterms,
* non-unique resolution of irrelevant metavariables,
* internal shape-irrelevant universe polymorphism,
* pseudopolymorphism for modes and modalities (pseudoparameters must be instantiated before type checking),
* subtyping (very long term - even for universes we can use a lift function).

It is named after the star Alpha Ceti, which is nicknamed Menkar.
