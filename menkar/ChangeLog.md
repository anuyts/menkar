# Changelog for menkar
Please add changes in chronological order: newest first.

## Unreleased changes

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
