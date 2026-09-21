# Substrate requirement: collinear simultaneous congruence ambiguity

## Goal
Formalize a paper-independent constructive non-identifiability theorem for finite families of real symmetric positive-definite matrices under simultaneous congruence diagonalization when a selected coordinate-pair shift cloud is affine-collinear.

## Provides (API contract)
- A small-parameter selection lemma producing a nonzero real deformation parameter that simultaneously preserves normalization/cycle-product admissibility, positive definiteness, and coordinatewise nonnegativity.
- A constructive ambiguity theorem: from an invertible normalized reference diagonalizer and affine-collinear selected coordinate-pair shift values, construct a distinct normalized invertible diagonalizer, a positive-definite transformed invariant matrix, and nonnegative transformed diagonal shifts representing exactly the same finite covariance family.
- An interior-example corollary producing a finite positive-definite covariance family with the prescribed shift vectors and two distinct compatible normalized diagonalizers.
- Reusable supporting lemmas for the two-coordinate shear/congruence algebra and preservation properties used by the construction.

## Statement / milestones
Let `E` be a finite nonempty index type, `d` a finite dimension with two distinct selected coordinates `i ≠ j`, `B₀` an invertible normalized real `d × d` matrix, `Ω₀` a symmetric positive-definite invariant matrix, and `s : E → Fin d → ℝ` nonnegative diagonal shift vectors. Assume the point cloud `e ↦ (s e i, s e j)` lies in an affine line, expressed by a concrete affine dependence suitable for construction. For the represented family `Σ e = B₀⁻¹ (Ω₀ + diagonal (s e)) B₀⁻ᵀ` (or an algebraically equivalent congruence convention), construct a nonzero sufficiently small two-coordinate shear/deformation parameter and resulting objects `B₁`, `Ω₁`, `s₁` such that:

- `B₁` is normalized, invertible, and `B₁ ≠ B₀`;
- `Ω₁` is symmetric positive definite;
- every `s₁ e` is coordinatewise nonnegative;
- the covariance representation using `B₁`, `Ω₁`, and `s₁` equals `Σ e` for every `e`.

The theorem may require explicit strict interior margins (positive-definiteness lower margin, strict positive selected shift margins, and nondegenerate normalization margin) sufficient to choose the deformation parameter. State these honestly and quantitatively enough for the proof, while keeping the construction generic and reusable.

Also give a corollary that, for an admissible affine-collinear shift family satisfying the stated interior margins, constructs some positive-definite invariant matrix and covariance family with two distinct compatible normalized diagonalizers. This is an existence/interior ambiguity result, not a uniqueness theorem.

## Standard reference
Standard simultaneous-diagonalization non-identifiability by a two-coordinate shear along an affine-collinear eigenvalue/shift cloud, combined with openness of invertibility and positive definiteness and finite-family preservation of strict inequalities. The existing qualitative reference is `Causalean.Discovery.LinearDisentanglement`; the output should be a constructive neutral strengthening in the same mathematical domain.

## Intended reuse
Reusable by covariance-based linear-disentanglement results that need a sharp ambiguity witness when affine separation fails. The immediate consumer packages the construction into a robust replacement-radius theorem, but the substrate must not mention BACKSHIFT systems, corruption/replacement families, confidence sets, or that paper's compatibility/witness structures. It must operate on generic finite real matrix and diagonal-shift families.

## May assume / must derive
May assume: finite dimension and family; two distinct coordinates; invertibility and the chosen explicit normalization of the reference; symmetry/positive definiteness of the invariant matrix; nonnegative shifts plus any explicit strict interior margins needed for a nonzero perturbation; and a concrete affine-collinearity certificate for the selected coordinate pair.

Must derive: existence of one nonzero parameter meeting all finitely many smallness constraints; preservation of normalization/cycle-product admissibility; invertibility and distinctness of the perturbed diagonalizer; symmetry and positive definiteness of the transformed invariant matrix; coordinatewise nonnegativity of every transformed shift; and exact equality of every represented covariance. Do not assume the ambiguity witness or representation equality itself.

## Non-goals (optional)
No paper-specific `*_Research` imports or types; no BACKSHIFT-specific `BackshiftSystem`, replacement/corruption family, `compatibleSet`, confidence region, finite-sample inference, or software. Do not weaken the result to an abstract existential assumption saying a second representation already exists. Do not claim ambiguity for boundary cases lacking the strict margins genuinely needed by the deformation.

## Known building blocks (optional)
`Causalean.Discovery.LinearDisentanglement`, the neutral quantitative module under `Causalean.Discovery.LinearDisentanglement.Quantitative`, finite-dimensional real matrix algebra, diagonal matrices, transpose and inverse identities, congruence preservation of symmetry/positive definiteness, openness or explicit perturbation bounds for positive definiteness and invertibility, and finite minima for simultaneous strict-inequality preservation. Imports may use only Mathlib, Causalean, and neutral modules within this study staging tree.
