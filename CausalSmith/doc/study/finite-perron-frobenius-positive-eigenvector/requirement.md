# Substrate requirement: finite positive Perron eigenvector

## Goal

Develop a paper-independent finite-dimensional Perron–Frobenius theorem for a nonempty finite real matrix that is symmetric, entrywise nonnegative, and irreducible.

## Provides (API contract)

- A theorem producing a unit Euclidean-norm eigenvector whose every coordinate is strictly positive, with eigenvalue equal to the top Rayleigh value.
- Bridge lemmas identifying a unit-sphere `sSup` Rayleigh value with Mathlib's finite-dimensional maximum or `iSup` Rayleigh quotient.
- Lemmas showing that coordinatewise absolute value preserves maximality and eigenvector status for a symmetric entrywise-nonnegative matrix.
- A positivity propagation lemma from a nonzero nonnegative eigenvector to a strictly positive one under irreducibility.
- Restriction and zero-extension lemmas preserving `mulVec` equations and the top Rayleigh value on a finite connected subtype.

## Statement / milestones

For a nonempty finite index type and a real matrix that is symmetric, entrywise nonnegative, and irreducible, construct a vector `v` and scalar `rho` such that `‖v‖ = 1`, every coordinate of `v` is strictly positive, `A.mulVec v = rho • v`, and `rho` is the maximum Rayleigh value. Prove the absolute-value, strict-positivity, restriction, and zero-extension milestones needed for this theorem from the declared matrix hypotheses.

## Standard reference

The finite-dimensional Perron–Frobenius theorem for irreducible nonnegative matrices, specialized to symmetric real matrices and characterized through the Rayleigh maximum.

## Intended reuse

Finite graph and network arguments that need canonical positive top eigenvectors on connected components. The immediate consumer will prove conflict-matrix component irreducibility and assemble a paper-specific component ordering, but this substrate must remain independent of that construction.

## May assume / must derive

May use Mathlib's finite-dimensional Rayleigh maximum and matrix irreducibility definitions. Must derive the coordinatewise-absolute maximizer step, strict positivity from irreducibility, and the restriction/zero-extension bridges. Do not assume the desired positive eigenvector as an axiom or premise.

## Non-goals

Do not define paper-specific graph components, least representatives, lexicographic rankings, conflict matrices, or ordering records. Do not import any `CausalSmith/*_Research` module.

## Known building blocks

- `LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional`
- `IsSelfAdjoint.hasEigenvector_of_isMaxOn`
- `Matrix.IsIrreducible.exists_pos`
- `Mathlib.Analysis.InnerProductSpace.Rayleigh`
- `Mathlib.LinearAlgebra.Matrix.Irreducible.Defs`
