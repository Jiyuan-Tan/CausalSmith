# Substrate requirement: pairwise-affine simultaneous congruence stability

## Goal
Extend the reusable quantitative simultaneous-congruence theory with an explicit operator-norm stability theorem based on pairwise affine separation, allowing the witnessing environment triple to depend on the coordinate pair.

## Provides (API contract)
- A paper-independent predicate expressing uniform pairwise affine separation: for every distinct coordinate pair `i,j`, some three environments (depending on `i,j`) have the affine `2 × 2` determinant of their shift-coordinate points bounded below in absolute value by a common positive margin `δ`.
- Coordinate-product and diagonal-branch perturbation lemmas derived directly from one pair's selected triple under approximate simultaneous congruence.
- A theorem bounding the Euclidean/operator norm between an exact unit-diagonal reference and an approximately feasible unit-diagonal candidate linearly in the residual tolerance, under pairwise affine separation and explicit scale/condition envelopes.
- A corollary whose displayed constant is no larger than, or can be monotonically weakened to, `16 * (6*M/γ) * sqrt(p*(p-1)*(1+L^2)) * L^3`, where `L = ((p!)*κ^(p-1))^(1/p)`, under the matching dimension, scale, separation, and condition assumptions.

## Statement / milestones
Let `p > 0`, let `E` be a finite nonempty environment type, and let `s : E → Fin p → ℝ` be bounded diagonal shift vectors. For every `i ≠ j`, assume there exist `e₀,e₁,e₂ : E`—not required to be common across pairs—such that the affine determinant

`(s e₁ i - s e₀ i) * (s e₂ j - s e₀ j) - (s e₂ i - s e₀ i) * (s e₁ j - s e₀ j)`

has absolute value at least `δ > 0`.

Given an invertible unit-diagonal reference matrix `B₀` satisfying exact simultaneous congruence diagonalization for the family, and a unit-diagonal candidate `B` whose simultaneous-congruence off-diagonal residuals are uniformly at most `ε ≥ 0`, assume explicit bounds on shift/covariance scale and on condition numbers (or equivalent inverse/norm envelopes) of `B₀` and `B`. For sufficiently small `ε`, prove an explicit linear bound `‖B-B₀‖op ≤ C ε`.

Derive the needed off-diagonal coordinate-product and diagonal-branch controls pair by pair from that pair's own selected triple. Do not replace pairwise separation by a single base plus `p` environments with a nonzero full `p × p` determinant. The API may first prove a Frobenius/L2 bound and convert it to the Euclidean operator norm with explicit constants.

Provide a final specialized/corollary constant expressible or weakenable to
`16 * (6*M/γ) * sqrt(p*(p-1)*(1+L^2)) * L^3`, `L = ((p!)*κ^(p-1))^(1/p)`, when the generic parameters are instantiated by the corresponding paper-independent scale `M`, pairwise margin `γ`, and determinant/condition envelope `κ`.

## Standard reference
Standard finite-dimensional perturbation analysis for identifiable simultaneous congruence diagonalization: solve each two-coordinate affine system using a determinant lower bound, aggregate entrywise estimates into Frobenius/operator norm control, and use determinant plus condition estimates to control normalization branches. This is the pairwise analogue of the existing neutral quantitative theory under `Causalean.Discovery.LinearDisentanglement.Quantitative`.

## Intended reuse
Reusable whenever simultaneous-diagonalization identifiability is certified by all pairwise affine minors rather than a single full-dimensional affine determinant. The immediate consumer is a non-effective local contraction theorem, but this module must mention neither that paper nor BACKSHIFT systems, confidence unions, corruption, coverage, or finite-environment application wiring. It must expose generic finite real matrix/shift-family results.

## May assume / must derive
May assume: positive finite dimension; finite nonempty environment family; bounded shifts; pairwise affine-separation witnesses and common margin; exact reference feasibility; approximate candidate feasibility; unit-diagonal normalization; invertibility; explicit scale and condition/inverse bounds; nonnegative residual tolerance plus a stated quantitative smallness condition.

Must derive: the two-coordinate affine-system estimates for each pair; off-diagonal product/branch control; aggregation over all ordered or unordered coordinate pairs; the linear operator-norm bound and its explicit parameter dependence; and the stated constant-specialization/weakened corollary. Do not assume full-dimensional affine separation, a common environment tuple for every pair, the final stability estimate, or a local inverse theorem with the desired conclusion.

## Non-goals (optional)
No paper-specific `*_Research` imports or types; no BACKSHIFT model, replacement/corruption family, confidence region, finite-sample inference, real-closed-field algorithm, or software. Do not strengthen pairwise witnesses to a global full-dimensional determinant. Do not claim an effective data-driven radius beyond the explicit deterministic smallness condition used by the stability theorem.

## Known building blocks (optional)
Reuse the definitions, norm estimates, transition-matrix algebra, determinant/condition bounds, and residual machinery in `Causalean.Discovery.LinearDisentanglement.Quantitative` wherever faithful. Add a separate pairwise module rather than changing the meaning of `AffineMinorSeparated`. Use Mathlib finite sums/maxima, real inequalities, square roots/powers/factorials, finite-dimensional matrix norms, determinant and inverse estimates. Imports may use only Mathlib, Causalean, and neutral modules in this study staging tree.
