Normalization
=============

Before proceeding, context, expression and type are weak-head-normalized.
For expressions, this process yields 3 results:
* the normalized expression
* information about what sort of substitution could make the current term reducible again:
   * constructions
   * neutral terms: substitution of a postulate or variable (+ which one)
   * blocked terms: substitution of a metavariable (+ which one)
* information about what sort of restriction could make the current term reducible again:
   * stable: nothing
   * neutral terms: substitution of a postulate or variable (+ which ones) occurring in a face predicate
   * blocked terms: substitution of a metavariable (or postulate or variable) (+ which ones) occurring in a face predicate

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
