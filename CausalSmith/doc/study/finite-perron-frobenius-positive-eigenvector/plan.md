## Done
- Ground truth: all five source files elaborate directly with `lake env lean`; warnings only. Source scan finds exactly two `sorry`s and no `admit`, declared `axiom`, forbidden research import, or hard error.
- `Basic.lean`: all Rayleigh definitions, three value bridges, maximizer existence, and top unit eigenvector theorem are closed.
- `AbsoluteValue.lean`: all 8 absolute-value norm, maximality, and eigenvector lemmas are closed.
- `Positivity.lean`: all 3 zero-propagation and irreducible strict-positivity lemmas are closed.
- `Restriction.lean`: all restriction, zero-extension, `mulVec`, quadratic-form, symmetry/nonnegativity, eigen-equation, and top-value lemmas are closed.
- Library search found the intended Mathlib Rayleigh/irreducibility primitives but no packaged theorem matching this substrate. [Friedland, Proposition 5.2](https://homepages.math.uic.edu/~friedlan/lectnotesM425S10.pdf) confirms the coordinatewise-absolute Rayleigh-maximizer argument.

## Remaining
- `Main.lean`: `finite_positive_perron_eigenvector`.
- `Main.lean`: `finite_positive_perron_eigenvector_on_restriction`.

## Blocked
- None.

## Decisions
- Use one filler because both remaining declarations share one file and the restriction theorem depends on the headline theorem.
- Keep `EVec ι := EuclideanSpace ℝ ι` and all three top-Rayleigh presentations.
- `Matrix.IsIrreducible` already contains entrywise nonnegativity; do not add a redundant headline hypothesis.
- Assemble the headline from the closed top-eigenvector, absolute-value, and irreducible-positivity lemmas. Assemble the restriction result from the headline plus symmetry restriction and closed-block zero extension; no new helper layer is needed.
- Preserve the existing genuine statements and dependency-clean imports unchanged.