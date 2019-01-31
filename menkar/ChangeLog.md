# Changelog for menkar
Please add changes in chronological order: newest first.

## Unreleased changes
* Top-level modules are still in the code, but no longer used. Menkar now takes multiple command-line arguments, each a file path. All files are scoped, then concatenated, and then the result is type-checked as the body of a module called `Root`. Include or import statements may be considered in the future.

## v0.1: Dependent type theory.
Menkar now supports dependent type theory.
