# Changelog for menkar
Please add changes in chronological order: newest first.

## Unreleased changes
* Add an option to print modules partially or completely in context and on the right.
* Add an option to **not** print left-divisions of contexts explicitly.
* Add options to prettyprinting.
* Major refactoring: index syntax types with a system, rather than with a mode and a modality type.

### v0.101: File concatenation
* Versioning scheme: vA.B0C.D (A is major version, B is major milestone, C for other non-backwards-compatible changes, D for backwards compatible changes.)
* Top-level modules are still in the code, but no longer used. Menkar now takes multiple command-line arguments, each a file path. All files are scoped, then concatenated, and then the result is type-checked as the body of a module called `Root`. Include or import statements may be considered in the future.

## v0.1: Dependent type theory
Menkar now supports dependent type theory.
