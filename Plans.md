Parsing
=======
```
Code
  |
  |  parser
  V
Raw syntax: operators, eliminators, lambdas, telescopes; no variable or name binding
  |
  |  scoper
  |
  |--> [(eliminate, smartelim)]
  V
Fine syntax
  |
  |  type checker
  V
Fine syntax (well-typed)
```

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

NOT REALLY BETTER: Weld, implication, assertion and their constructors/eliminators do not reduce at Top. Rather, they are kept as **decorations** which are ignored by definitional relations. So we can only be blocked on one variable/neutral at the same time. So when normalizing, you can choose whether you want to keep or remove such decorations. (You still want to know whether something is neutral/blocked w.r.t. decoration-removing normalization)

NOTE: The only face predicate i-related to Top (`i < Top`) is Top. So we never need to relate non-reduced and reduced types. (This is only true if Box Top does not reduce. We can be equally expressive by having an equality predicate for every i-interval instead of just for I.)

**Contexts** are not normalized. There is instead a proof-calculus with J-rule as well as an eliminator
```
{C {P : Prop}{p : P} : Uni}{c : C Top tt}{P : Prop}{p : P} -> C P p
```
This is the only approach that allows neutral propositions and still lets substitution preserve definitional equality.
Note: systems need eliminable propositions, so as to be sure that you can check they are consistent on overlaps.
Note: therefore, you need to save the context as an argument to a system!

Classification
--------------
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

Type-checking
=============

Types of metas
--------------
* implicits
   * goals: do not inhabit, so that the user can see the constraints.
* instances
* elaborations (don't solve them, just wait)

Declarations
------------
For a declaration, we check everything at the same time.

IS THIS SAFE!? Some judgements presuppose others. Are you going to check judgements if their presuppositions have not been checked? I think this is perfectly safe: eventually, we check the presuppositions, and if they are false, type-checking fails.

Judgements
----------
* If there are 0 ways to derive the judgement, we issue an error but (if this is the only thread) might want to continue type-checking those judgements that do not presuppose one that has now failed.
* If there is 1 way to derive the judgement, we add the premises as constraints and remove the current judgement from the constraints.
* If there are multiple distinct ways (notably, for instance resolution), we postpone as until everything else is blocked or solved, then fork. Every branch in which type-checking succeeds, should ultimately yield the same (definitionally equal) solutions for all original metavariables.
* Sometimes (notably for smart elimination) there are multiple possible derivations, but we can pick one by pattern matching on a whnf. The variable/neutral case is included in the pattern match.

At the end of a thread
----------------------
Try to inhabit unsolved implicits that are not goals. HOW!?

Aftermath
---------
* If no threads succeeded, report the errors of all failed threads.
* If one or more threads succeeded, all with 0-related resolution of the original metas, just report the solutions of the goals.
* If multiple threads succeeded and do not agree, report the choices of all successful threads.

Discreteness: internal or external?
-----------------------------------
* Δ UniHS is certainly discrete, so it makes sense to use 0-relatedness for conversion checking.
* In directed type theory, this is a different story, as we want to use arrows for coercion checking, and an arrow in Δ UniHS is just a mapsto in UniHS, which is only good enough for conversion if we know our type is functorial. In that case, it seems safe to conclude that if `a :~>: b`, then `F a :~>: F b`, since the morphism `φ` from `F a` to `F b` is such that for every `fa : F a` there is a definitional mapsto from `fa` to `φ fa`. So I guess every time you put something behind the `:`, the type checker will look for an instance of functoriality :-)

Relatedness checking
--------------------
* If checking Top-relatedness: succeed.
* Weak head normalize everything (no decorations).
* If the type has eta, eta expand and recurse.
* If the type is blocked, and both hands are whnf, try to match; at success recurse.
* If both hands are whnf, either fail or match and recurse.
* If one hand is a pure implicit:
   * If you're checking 0-relatedness: solve the meta.
   * If the other hand is a variable: block.
   * If the other hand is a construction: head-solve the meta. Recurse.
* We know that one hand is blocked. Block.

Metavariable introduction
-------------------------
* Add a term judgement with the new metavariable as the term

Term judgement
--------------
* Weak head normalize everything (no decorations)
* If the term is a pure implicit and the type has eta, eta-solve the implicit and recurse.
* If the term is a pure implicit, block.
* Do whatever is appropriate given the term's head.

Smart term judgement
--------------------
* introduce an elaboration-meta
* require that the smart term elaborates to the meta

Smart elimination judgement
---------------------------
Operator expressions are straightforwardly converted to non-operator expressions during parsing.

Gamma |- EliminandType @ smart eliminations ~> dumb eliminations

* weak head normalize the type (keep decorations)
* if there is no elimination, auto-eliminate as long as the type admits.
* if there is a `.~`, require that it be the last and stop.
* if the first elimination of the smart term matches the type, use it.
* otherwise, auto-eliminate once. (This includes peeling off a decoration)

Is this worth the effort!? NO

(Co)-inductive types
====================
`Weld (A i) (P i ? T i , f i)` is just an inductive type cofamily over `T i` (i.e. an extension of `T i`).
```
data Weld {A : Uni} {~ | P : Face} {scheme : P -> {T : Uni} >< (A -> T)} : Set @ ({p : P} > scheme p .T) where {
	val T {p : P} : Uni = p > scheme p .T
	val f {p : P} : A -> T p = scheme p ..2
	constructor weld {a : A} : Weld A scheme @ (p > f p a)
}
```

`Glue (A i) (P i ? T i , f i)` is just a co-inductive type cofamily over `T i`.
```
data Glue {A : Uni} {~ | P : Face} {scheme : P -> {T : Uni} >< (T -> A)} : Set @ ({p : P} > scheme p .T) where {
	val T {p : P} : Uni = p > scheme p .T
	val f {p : P} : T p -> A = scheme p ..2
	field unglue {g : Glue A scheme} : A @ (p > f p g)
}
```
