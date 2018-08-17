Normalization
=============

Before proceeding, context, expression and type are weak-head-normalized.
This process yields 2 results:

* the normalized context/expression
* information about what sort of substitution could make the current term reducible again:
   * constructions: nothing
   * neutral terms: substitution of a postulate or variable (+ which ones)
   * blocked terms: substitution of a metavariable (or postulate or variable) (+ which ones)

Note that we have multi-eliminations, e.g. `unglue (P ? f) g` reduces if `P` becomes true and if `g` becomes a `glue` term. Hence, we can at the same time be blocked on metavariable `P` and neutral due to `g`.

BETTER: Weld, implication, assertion and their constructors/eliminators do not reduce at Top. Rather, they are kept as **decorations** which are ignored by definitional relations. So we can only be blocked on one variable/neutral at the same time.

~~Classification~~
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

Type-checking
=============

Declarations
------------
For a declaration, we check everything at the same time.

IS THIS SAFE!? Some judgements presuppose others. Are you going to check judgements if their presuppositions have not been checked? I think this is perfectly safe: eventually, we check the presuppositions, and if they are false, type-checking fails.

Judgements
----------
* If there are 0 ways to derive the judgement, we issue an error but (if this is the only thread) might want to continue type-checking those judgements that do not presuppose one that has now failed.
* If there is 1 way to derive the judgement, we add the premises as constraints and remove the current judgement from the constraints.
* If there are multiple ways (notably, for instance resolution), we postpone as until everything else is blocked or solved, then fork. Every branch in which type-checking succeeds, should ultimately yield the same (definitionally equal) solutions for all original metavariables.
* Sometimes (notably for smart elimination) there are multiple possible derivations, but we can pick one by pattern matching on a whnf. The variable/neutral case is included in the pattern match.

Discreteness: internal or external?
-----------------------------------
* Δ UniHS is certainly discrete, so it makes sense to use 0-relatedness for conversion checking.
* In directed type theory, this is a different story, as we want to use arrows for coercion checking, and an arrow in Δ UniHS is just a mapsto in UniHS, which is only good enough for conversion if we know our type is functorial. In that case, it seems safe to conclude that if `a :~>: b`, then `F a :~>: F b`, since the morphism `φ` from `F a` to `F b` is such that for every `fa : F a` there is a definitional mapsto from `fa` to `φ fa`. So I guess every time you put something behind the `:`, the type checker will look for an instance of functoriality :-)
