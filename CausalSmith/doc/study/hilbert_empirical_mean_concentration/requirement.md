# Substrate requirement: hilbert_empirical_mean_concentration

## Goal
Build a dimension-free concentration theorem for empirical means of bounded random variables in an arbitrary complete real Hilbert space, including the expectation/variance estimate needed before scalar McDiarmid.

## Provides (API contract)
- A reusable theorem bounding the second moment of the centered empirical mean of an i.i.d. Hilbert-valued sample by `m⁻¹` times the population second moment, without a `FiniteDimensional` hypothesis.
- A first-moment corollary: for `‖f x‖ ≤ 1` and `1 ≤ m`, the expected norm of the centered empirical mean is at most `1 / Real.sqrt m`.
- A high-probability corollary obtained from scalar `mcdiarmid_inequality_pos` for the norm of the centered empirical mean, with bounded-difference constant `2 / m` and the standard `1 / √m + √(2 log(1/δ)/m)` radius.

## Statement / milestones
For a probability measure `P`, complete real Hilbert space `H`, measurable `f : X → H` with `‖f x‖ ≤ 1`, and `m ≥ 1`, prove under the product law `Measure.pi (fun _ : Fin m => P)` that

`∫ z, ‖(m : ℝ)⁻¹ • ∑ r, f (z r) - ∫ x, f x ∂P‖ ≤ 1 / Real.sqrt m`.

The proof must establish the dimension-free Hilbert variance identity by finite expansion of the squared norm, use independence/bilinearity to cancel off-diagonal centered terms, bound diagonal terms by the population second moment, and pass from second to first moment by Jensen or Cauchy--Schwarz. Then package the scalar McDiarmid tail corollary. All declarations must be sorry-free and axiom-clean.

## Standard reference
The Hilbert-space identity `E ‖m⁻¹ Σ(Yᵣ-EY)‖² = m⁻¹ E ‖Y-EY‖²` is the standard variance-of-the-mean calculation for independent Hilbert-valued random variables; the tail step is the classical bounded-differences inequality of McDiarmid. The construction is a dimension-free extension of the finite-dimensional coordinate proof already documented in `Causalean.Stat.EmpiricalProcess.Equicontinuity.SecondMoment`.

## Intended reuse
Primary consumer: `CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity.bounded_rkhs_empirical_mean`, whose Gaussian feature map lands in a generally infinite-dimensional complete Hilbert space. The result should live in a general Causalean statistical-concentration module and be reusable for kernel mean embeddings and Hilbert-valued empirical processes.

## May assume / must derive
May assume a probability measure, completeness and real inner-product structure on `H`, strong measurability/integrability of the Hilbert-valued map, independence or the product-law i.i.d. representation, `m ≥ 1`, and the pointwise unit-norm bound. Must derive the Bochner mean's integrability, centered second-moment inequality, `1 / √m` expectation bound, bounded-difference constant, and McDiarmid tail; must not assume finite dimensionality, the desired expectation/tail conclusion, or any paper-specific CausalSmith definition.

## Non-goals (optional)
Do not formalize general Banach-space type/cotype theory, Gaussian concentration, or the paper-specific conditional-on-training lift. The current research run will combine this generic fixed-law theorem with `randomParam_event_le` and a finite union bound.

## Known building blocks (optional)
- `ProbabilityTheory.IndepFun.integral_bilin_comp_comp` with `innerSL ℝ` for off-diagonal cancellation.
- `MeasureTheory.Integrable.integral_prod_right`, Bochner integral linearity, and `Measure.pi` independence.
- `mcdiarmid_inequality_pos` / `mcdiarmid_inequality_pos'` from `FoML.McDiarmid`.
- `Causalean.Stat.empProcVec_sq_lintegral_le` as a finite-dimensional near-match whose `FiniteDimensional ℝ H` restriction must not be inherited.
- `Causalean.Mathlib.iid_centered_sum_sq_lintegral_le` as the scalar analogue.
