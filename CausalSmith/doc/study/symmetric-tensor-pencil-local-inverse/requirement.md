# Quantitative symmetric-tensor pencil local inverse

## Goal

Develop reusable, axiom-clean Lean theory for stable recovery of a finite symmetric rank-one tensor decomposition by the tensor-pencil method.

## Provides (API contract)

- Norm control for contractions of symmetric tensors by unit probes.
- Conditioning bounds for lifted factor matrices from a least-singular-value hypothesis.
- Perturbation bounds for simultaneous-congruence or generalized-eigenvalue pencils.
- Gap-based matching of spectral projectors.
- Recovery and normalization of rank-one lifted directions.
- A permutation-aligned local inverse theorem bounding factor-matrix error linearly by tensor Frobenius error.

## Statement / milestones

For two decompositions
\[
T=\sum_{j=1}^n \lambda_j c_j^{\otimes(2d+q)},\qquad
T'=\sum_{j=1}^n \lambda'_j (c'_j)^{\otimes(2d+q)},
\]
assume unit Euclidean columns, coefficient magnitudes in `[kappa, Lambda]`, positive contraction-probe loadings at least `sigma`, least singular value at least `sigma` for both lifted direction matrices, and pairwise separation at least `sigma` of the pencil ratios formed by two unit probes. Under a sufficiently small Frobenius perturbation of `T`, prove that the columns of the two factor matrices can be matched by a permutation and bounded linearly in Frobenius norm by the tensor perturbation.

Expose the complete quantitative chain: contraction bounds, lifted conditioning, pencil perturbation, spectral-projector matching, rank-one lift recovery, normalization, and permutation-aligned original-column recovery. A general explicit assembled constant is acceptable. Applications must be able to specialize it to positive constants such as `eta = kappa * sigma^(q+2)`, `chi = sqrt n / sigma`, and the resulting local radius and Lipschitz factor.

## Standard reference

Standard finite-dimensional tensor-pencil and generalized-eigenvalue perturbation theory. Existing Causalean substrate includes `opNorm_sub_le_of_approximate_simultaneous_congruence`, `Causalean.Mathlib.Analysis.SingularValueWeyl`, and `Causalean.Mathlib.Analysis.RectangularSignalSingularValues`.

## Intended reuse

The immediate consumer is the numerical common-order local-inverse lemma for finite-sample recovery of separated overcomplete-ICA directions. The API should remain independent of that paper and reusable for other finite symmetric rank-one tensor decompositions recovered by contracted pencils.

## May assume / must derive

May assume unit columns; coefficient bounds; positive probe-loading, lifted least-singular-value, and pencil-ratio separation margins; finite dimensions; and a sufficiently small tensor Frobenius perturbation. Must derive the contraction, conditioning, pencil, projector, lifted-direction, normalization, permutation-matching, and final Lipschitz factor-control chain from those assumptions.

## Non-goals

Do not formalize the paper-specific sampling model or asymptotic theorem. Do not import any `CausalSmith/*_Research` module.

## Known building blocks

Use only Mathlib, Causalean, and study-local prerequisites. Current searches found no theorem covering tensor contraction, spectral-projector recovery, and permutation-aligned factor control together.
