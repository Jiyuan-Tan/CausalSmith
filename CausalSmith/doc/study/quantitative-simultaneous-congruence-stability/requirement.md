# Substrate requirement: quantitative simultaneous congruence stability

## Goal
Formalize a paper-independent quantitative stability theorem for finite-dimensional real square matrices under approximate simultaneous congruence diagonalization, together with the compactness/continuity exclusion lemma that yields a positive non-effective radius outside a normalized local chart.

## Provides (API contract)
- A reusable definition of the simultaneous-congruence residual for a finite family of real square matrices and diagonal shift vectors.
- A reusable affine determinant/minor separation predicate for the shift-vector family.
- A theorem giving an explicit linear operator-norm bound between an exact normalized reference matrix and an approximately feasible normalized candidate. The modulus must expose its dependence on dimension, affine separation, covariance/shift scale, and reference/candidate condition-number bounds.
- A compactness/continuity theorem giving a strictly positive minimum residual on the normalized candidates outside a prescribed local chart, hence an existential positive exclusion radius.

## Statement / milestones
For a finite nonempty family of real `d × d` matrices, an exact reference `B₀`, and a candidate `B`, assume unit-diagonal (or an equivalently explicit scale-fixing) normalization, exact simultaneous congruence diagonalization at `B₀`, approximate feasibility at `B`, a positive affine-minor separation margin for the associated diagonal shift vectors, uniform operator-norm scale bounds, and operator-norm condition-number bounds for both matrices. When all covariance congruence residuals are at most `ε` and `ε` is below an explicit admissible threshold, prove `‖B - B₀‖op ≤ C ε`, with `C` expressed from `d`, the separation margin, scale bounds, and condition bounds.

Separately, for a compact normalized candidate set and a continuous nonnegative residual that vanishes only at the reference inside the relevant exact-identification class, prove that the residual has a positive attained minimum on candidates outside a specified open/local neighborhood of the reference. Package the resulting positive non-effective exclusion radius without claiming computability.

The API may choose equivalent finite-dimensional matrix norms if it supplies explicit comparison constants sufficient to recover the operator-norm conclusion.

## Standard reference
Standard finite-dimensional perturbation analysis: continuity and compact extreme-value arguments for isolated zeros, norm equivalence, inverse/condition-number estimates, determinant/minor perturbation bounds, and stability of identifiable simultaneous diagonalization. Existing qualitative uniqueness machinery in `Causalean.Discovery.LinearDisentanglement` is the natural identification reference; the new result must be a neutral quantitative strengthening rather than a paper-specific restatement.

## Intended reuse
Reusable by robust covariance-based linear-disentanglement and BACKSHIFT-style identification results. The immediate consumer is a non-effective four-margin contraction theorem, but the substrate API must mention neither that paper nor confidence unions, corruption budgets, coverage statements, or finite-environment application wiring. It must work for generic finite real matrix families.

## May assume / must derive
May assume: finite dimension; a finite nonempty index family; explicit normalization; positive affine separation; explicit scale and condition bounds; compactness of the candidate set for the non-effective lemma; continuity and unique-zero/isolation hypotheses when stated abstractly.

Must derive: the quantitative residual-to-operator-distance estimate from these assumptions; all norm-conversion, matrix perturbation, and finite-family maximum/minimum steps used by the bound; positivity and attainment of the far-set residual minimum for the compactness lemma. Do not assume the desired Lipschitz bound, a prepackaged local inverse theorem whose conclusion is the target, or the positive far-family minimum itself.

## Non-goals (optional)
No confidence-region construction, real-closed-field quantifier elimination, effective root isolation, release-or-abstain procedure, corruption-aware algorithm, software implementation, finite-sample probability theorem, or paper-specific `*_Research` import. The compactness radius may remain existential/noncomputable; the local linear modulus must be explicit in its declared parameters.

## Known building blocks (optional)
Finite-dimensional real matrices; Frobenius/L2 and operator norms with comparison inequalities; transpose, determinant, invertibility and inverse-norm estimates; continuity of matrix operations and determinants; compactness and extreme-value results; finite sup/max bounds; and `Causalean.Discovery.LinearDisentanglement` for existing qualitative simultaneous-diagonalization uniqueness. Imports may use only Mathlib, Causalean, and neutral modules created within this study staging tree, never a CausalSmith paper module.
