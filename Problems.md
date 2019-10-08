Problems with Menkar
--------------------
* Meta-variable solutions may contain same metavariable (no occurs-check)
* Meta-variable solutions may be ill-typed due to modalities
* Judgments should return algorithm-free ASTs?
* No memoization of substitution
* No explicit modality coercions?

Quick-and-dirty solutions
-------------------------
* No polymorphism
* Implement occurs-check
* Implement modality-check
