# Study requirement: finite positive Perron eigenvector

Slug: `finite-perron-frobenius-positive-eigenvector`

## Required reusable result

Develop a paper-independent finite-dimensional Perron–Frobenius theorem for a
nonempty finite real matrix that is symmetric, entrywise nonnegative, and
irreducible.  It must produce a unit Euclidean-norm eigenvector whose every
coordinate is strictly positive, with eigenvalue equal to the top Rayleigh
value.

The result should expose enough bridge lemmas to:

1. identify the project's unit-sphere `sSup` Rayleigh value with Mathlib's
   finite-dimensional maximum/`iSup` Rayleigh quotient;
2. replace a maximizing eigenvector by its coordinatewise absolute value and
   retain maximality/eigenvector status;
3. propagate positivity from nonzero to strictly positive using matrix
   irreducibility;
4. restrict a symmetric nonnegative matrix to a connected finite subtype and
   zero-extend the resulting positive eigenvector without changing its
   `mulVec` equation or top Rayleigh value.

## Proposed topical home and imports

Preferred home: `Causalean/Mathlib/LinearAlgebra/PerronFrobenius.lean` (or the
closest existing Causalean linear-algebra namespace selected by the study
coordinator).

Proposed imports:

- `Mathlib.Analysis.InnerProductSpace.Rayleigh`
- `Mathlib.LinearAlgebra.Matrix.Irreducible.Defs`
- only narrower matrix/order/finite-dimensional modules forced by the proof

Do not import any `CausalSmith/*_Research` module.

## Run-local prerequisites to extract or bridge

The live research artifact defines `rayleighRadius` as an `sSup` over unit
coordinate vectors in `Helpers/Spectral.lean`.  The study should define its
generic Rayleigh object independently, or prove its theorem using Mathlib's
Rayleigh quotient.  Main can then extract/promote a generic bridge and relay it
back into the run.  The study must not depend on `SameComponent`,
`componentBlock`, `PerronOrderData`, or the conflict-graph ranking construction.

## Out of scope

Do not build the paper-specific least component representatives, lexicographic
ranking permutation, or `PerronOrderData`.  After the reusable theorem lands,
the current run remains responsible for restricting `conflictMatrix` to each
`SameComponent` subtype, choosing component vectors, and assembling the rank.

## Verification

Require a targeted build of the new Causalean module, source grep with no
`sorry`/`admit`/new `axiom`, and `#print axioms` for the headline reusable
theorem before relay.
