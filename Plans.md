Normalization
=============

Before proceeding, context, expression and type are weak-head-normalized.
For expressions, this process yields 2 results:

* the normalized expression
* information about what sort of substitution could make the current term reducible again:
   * constructions: nothing
   * neutral terms: substitution of a postulate or variable (+ which ones)
   * blocked terms: substitution of a metavariable (or postulate or variable) (+ which ones)

Note that we have multi-eliminations, e.g. `unglue (P ? f) g` reduces if `P` becomes true and if `g` becomes a `glue` term.

Classification
--------------
We could use a two-dimensional classification of terms.

### Eliminational classification
```
construction =
	| constructor of expressions
	| type constructor of expressions
	| lambda of expression
elimination =
	| application to expression
	| projection
	| induction wrt expressions
neutral = variable | postulate | elimination of neutral
blocked = meta | elimination of blocked
whnf = construction | neutral
whbf = whnf | blocked
reducible = elimination of construction | elimination of reducible
expression = whbf | reducible
```

### Restrictional classification
Actually, this is not so useful.
