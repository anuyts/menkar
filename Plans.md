Base categories
===============
There are the following templates
```
cube	cubical sets
bpcube	bridge path cubical sets
dcube	depth cubical sets
procube	directed cubical sets
clock	multiclock type theory
```
There are the following options
```
+s	symmetries
?s	maybe symmetries
-s	no symmetries

+d	diagonals (cartesian; there will be ranges)
?d	maybe diagonals (cancellative symmetric semi-cartesian; a lot of things become unclear)
-d	no diagonals (affine)

+c	connections (only for cartesian; /\ and \/ are available)
?c	maybe connections
-c	no connections (only for affine; Phi is available if affine)

0	nullary (for clock; note that the base category is spooky: you need to use the generalized boundary)
1	unary
2	binary
...
```

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
* a list of variables, postulates and metas that evaluation is blocked on.

Note that we have multi-eliminations, e.g. `unglue (P ? f) g` reduces if `P` becomes true and if `g` becomes a `glue` term. Hence, we can at the same time be blocked on metavariable `P` and neutral due to `g`.

~~Weld, implication, assertion and their constructors/eliminators do not reduce at Top. Rather, they are kept as **decorations** which are ignored by definitional relations. So we can only be blocked on one variable/neutral at the same time. So when normalizing, you can choose whether you want to keep or remove such decorations. (You still want to know whether something is neutral/blocked w.r.t. decoration-removing normalization)~~

NOTE: The only face predicate i-related to Top (`i < Top`) is Top. So we never need to relate non-reduced and reduced types. (This is only true if Box Top does not reduce. We can be equally expressive by having an equality predicate for every i-interval instead of just for I.)

**Contexts** are not normalized. There is instead a proof-calculus with J-rule as well as an eliminator
```
{C {P : Prop}{p : P} : Uni}{c : C Top tt}{P : Prop}{p : P} -> C P p
```
This is the only approach that allows neutral propositions and still lets substitution preserve definitional equality.
Note: systems need eliminable propositions, so as to be sure that you can check they are consistent on overlaps.
Note: therefore, you need to save the context as an argument to a system! Or have compound system elimination rules which is essentially the same.

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

Type-checker
============

Types of metas
--------------
* implicits
   * goals: do not inhabit, so that the user can see the constraints.
* instances: These are just implicits, but you add an additional constraint that the implicit must be equal to an output of the resolution.
* ~~elaborations (don't solve them, just wait)~~ - smart eliminations are just terms.

Declarations
------------
For a declaration, we check everything at the same time.

IS THIS SAFE!? Some judgements presuppose others. Are you going to check judgements if their presuppositions have not been checked? I think this is perfectly safe: eventually, we check the presuppositions, and if they are false, type-checking fails.

Judgements
----------
* If there are 0 ways to derive the judgement, we issue an error but (if this is the only thread) might want to continue type-checking those judgements that do not presuppose one that has now failed.
* If there is 1 way to derive the judgement, we add the premises as constraints and remove the current judgement from the constraints.
* If there are multiple distinct ways (notably, for instance resolution), we postpone as until everything else is blocked or solved, then fork. Every branch in which type-checking succeeds, should ultimately yield the same (definitionally equal) solutions for all original metavariables. Before splitting, announce to the TC-monad the precise judgement that makes you split (with stack-trace). In every thread, announce the assumption you make.
* Sometimes (notably for smart elimination) there are multiple possible derivations, but we can pick one by pattern matching on a whnf. The variable/neutral case is included in the pattern match.

At the end of a thread
----------------------
A thread can terminate the following ways:

* Failure: a constraint is required that does not hold.
* Success: after the constraint solving phase, every object of interest is known up to the desired accuracy. **Subsequently**, there exists some joint resolution of all metas satisfying all remaining constraints.
* Unresolved metas: after the constraint solving phase, some objects of interest are not known up to the desired accuracy.
* Unresolved existence of metas: all objects of interest are known up to the desired accuracy, but we failed to spawn a solution to the remaining metas and constraints.

Aftermath
---------
* If all threads failed, report the errors of all failed threads.
* If some threads terminate with unresolved (existence of) metas, report about all non-failed threads.
* If one or more threads succeeded and agree up to the desired accuracy, just report the solutions of the goals.
* If multiple threads succeeded and do not agree up to the desired accuracy, report the choices of all successful threads.

Discreteness: internal or external?
-----------------------------------
* Δ UniHS is certainly discrete, so it makes sense to use 0-relatedness for conversion checking. However, types whose equality is checked, may be flat in a certain argument, which is then required to be =-related. I guess the solution is that when you define a thing, you can specify that you care about its identity only up to i-relatedness.
* In directed type theory, this is a different story, as we want to use arrows for coercion checking, and an arrow in Δ UniHS is just a mapsto in UniHS, which is only good enough for conversion if we know our type is functorial. In that case, it seems safe to conclude that if `a :~>: b`, then `F a :~>: F b`, since the morphism `φ` from `F a` to `F b` is such that for every `fa : F a` there is a definitional mapsto from `fa` to `φ fa`. So I guess every time you put something behind the `:`, the type checker will look for an instance of functoriality :-)

Relatedness checking
--------------------
* If checking Top-relatedness: succeed.
* Weak head normalize everything (no decorations).
* If the type has eta, eta expand and recurse. †
* If the type is blocked, and both hands are whnf, try to match; at success recurse, otherwise block. (WHY IS THIS OK?)
* If both hands are whnf, either fail or match and recurse.
* If one hand is a pure implicit and the other is not: head-solve the meta and recurse! (We're not checking Top-relatedness, so the head is not i-erased.) †
* If one hand is a pure implicit and the other is a different implicit: ?
* We know that one hand is blocked. Block.

† This no longer works if you have intersection/union types, or any other construction that causes heads to be i-erased.

Metavariable introduction
-------------------------
* Add a term judgement with the new metavariable as the term
* Add an equality judgement that equates the new meta to some eta-expansion. (There should be a special judgement expressing this. If the type turns out not to have eta, the judgement disappears. Otherwise, it actually reduces to the eta-expansion-equation. This way, meta-variables of record types are actually eta-split.) This is then solved using relatedness-checking, leading to weak-head-solving of the meta.

Weak head solving of metas
--------------------------
Replace the meta with a head and a bunch of new metas. Instance arguments to the head are introduced as instance-metas.

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

Substructurality
================
When moving into the body of `merid` or `Transp`, a new shape variable is added to the *front* of the context (using `:^^`) and marked as `right-cartesian`, indicating that the entire context should be viewed as the cartesian product of the shape on the left, and all the rest. An equation is added to the right, which states that the new variable is equal to the argument given to `merid` or `Transp`.

Subsequently, we divide by `i \between`, causing the new shape variable to disappear and all other variables -- including shape variables and the new equation -- to be lollipop'ed. This should work fine, and raises the question whether we should include quantified variables at all. The answer is yes: so that we can type-check `|_`.

Instance arguments
==================
If you give a record an instance field, then the corresponding projection is added as a clause to the resolution.

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
