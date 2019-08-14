# Changelog for menkar
Please add changes in chronological order: newest first.

## Unreleased changes
When releasing, change the changelog and `package.yaml`.

*  Modifications aimed at performance gains:

   *  Entry-checking judgements now get lowest priority and are refuted when there are still open worries, unless marked as @noFlush. The performance gains are underwhelming.
   *  Guard meta dependencies with the `Coyoneda` type, causing a **massive** speedup.
   *  Guard heavily substituted data with the `Coyoneda` type, causing a significant speedup.
   *  Make substitution (CanSwallow typeclass) more efficient.
   *  Use strict monads to no avail.
   *  Reimplemented `DeBruijnLevel` so that it needs to compute the size of the scope less often, causing a speedup.
   *  Contexts are now closed, reducing the need for renaming variables and causing a speedup.
   *  All uses of natural numbers have been replaced with integers, causing a significant speedup.
   *  All renamings that could theoretically be done using coercions, are now done using `unsafeCoerce`, causing a significant speedup.
*  Declarations are now checked without a reference to themselves in scope (bugfix).
*  The type-checking monad now supports metavariables of arbitrary `Solvable` ASTs.
*  Added a collection of "worries" to the type-checker's state. A worry is a blocked constraint.
   This is to avoid phenomena such as the following:

   1. Meta 5 is solved,
   2. Problem X is unblocked because 5 is solved,
   3. Meta 3 is solved,
   4. Problem Y is unblocked because 3 is solved, but thinks 5 is still unsolved!
*  Metavariables: Remember dependencies' modes, and weak-head-normalize them before trying to solve the metavariable.
*  Properly check modalities for smart elimination judgements.
*  Reimplement eta.
*  New annotation syntax:

   * `val *mu x : A = ...` instead of `val [m mu] x : A = ...`
   * `{~ *mu x : A}` instead of `{~ | m mu | x : A}`
*  Removed extremely widespread but redundant mode annotations from syntax. (A lot of trivialized legacy code is present.)
*  Added special function-like modal-lock syntax for Box types.
*  Added support for [Degrees of Relatedness (RelDTT)](https://doi.org/10.1145/3209108.3209119).
*  Put mode classifier of 'UniHSConstructor' in a 'ModalBox' so that it lives in the right context.
*  Annotated raw syntax with system parameter.

## v0.200: Analyzer

*  Fixed long-standing bug:

   After solving a metavariable, constraints might be unblocked. However, these constraints might have previously queried
   the solution of yet unsolved metavariables and may therefore reblock on those. However, the system would forget these
   previous queries, resulting in derivation branches blocking on nothing and therefore never resuming!

*  Instead of passing around the parent constraint **everywhere**, it is now part of the type-checking state.
*  Blocking on a meta, now leaves a blocking constraint to inform the user of what is happening.
*  Added a syntactic equality checker `QuickEq` based on `analyze`.
*  **Major refactoring:** weak-head-normalizer, type-checker, relatedness-checker, meta-resolver are now all based on a universal syntax traversal operation called `analyze`.

#### v0.101.4: Performance tweaks
*  Smart arguments are now checked only once, causing enormous performance gain.
*  The eta-expansion judgement is now only allowed for metas, not checked for solved metas, and lowest priority.

#### v0.101.3: Correct eta-equality
*  Turned eta-flag on metas into neutrality flag.
*  If eta holds, expand inductive pair and box elimination during whnormalization.
*  Put eta-flag on term relatedness judgement.
*  Fix eta-bug by reimplementing TC.Rel and TC.Solve.

#### v0.101.2: Parametrize everything with the system
*  Fixed pieces of code that are incorrect for non-trivial systems.

*  Major refactoring. Project is now organised two-dimensionally.

   One dimension is about processing programs:

   * Basic: things common to raw and fine syntax,
   * Parser: from strings to raw syntax,
   * Raw: raw syntax,
   * Scoper: from raw syntax to fine syntax,
   * Fine: fine syntax,
   * WHN: weak head normalization,
   * TC: type-checking.

   There will be increasingly complex monads for scoping, whnormalization, and type-checking.

   The other dimension is about parametrizing the implementation of the above parts:
   
   * Menkar: the core implementation, parametrized by a system and a monad,
   * Menkar.Monad: the specification of the monad typeclasses for scoping, whnormalizing and type-checking,
   * Menkar.Monads: implementations of the monad typeclasses,
   * Menkar.System: the specification of the system typeclasses,
   * Menkar.Systems: implementations of the system typeclasses.

*  Generalized Menkar.Monad from Trivial to arbitrary systems.

#### v0.101.1: Printing options
* Add options to prettyprinting (mostly available from command line):
```
set help                          Get this help.
set explicit-division <BOOL>      Print left division explicitly.
set factory                       Restore to factory settings.
set print-algorithms <INT>        Print algorithm annotations (smart elimination/goal/resolution).
                                    0: omit entirely; 1: replace with '_'; 2: print fully.
set print-entries <INT>           How to print entries (declarations).
                                    0: just their name; 1: also annotations; 2: entirely.
set print-meta-algorithms <BOOL>  Instead of printing a meta's dependencies, print its algorithm.
set print-modules <INT>           How to print modules. 0: omit contents; n+1: print entries as <n>.
set print-modules-ctx <INT>       How to print modules in context. 0: not at all; n+1: modules as <n>.
set print-solutions <BOOL>        Print solutions instead of metas.
set print-types <BOOL>            Print pedantic type annotations.
set width <INT>                   Set line width.
```
* Major refactoring: index syntax types with a system, rather than with a mode and a modality type.

### v0.101: File concatenation
* Versioning scheme: vA.B0C.D (A is major version, B is major milestone, C for other non-backwards-compatible changes, D for backwards compatible changes.)
* Top-level modules are still in the code, but no longer used. Menkar now takes multiple command-line arguments, each a file path. All files are scoped, then concatenated, and then the result is type-checked as the body of a module called `Root`. Include or import statements may be considered in the future.

## v0.1: Dependent type theory
Menkar now supports dependent type theory.
