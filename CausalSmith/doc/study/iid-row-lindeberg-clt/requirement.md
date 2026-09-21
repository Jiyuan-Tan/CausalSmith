# Substrate requirement: iid-row-lindeberg-clt

## Goal
The Lindeberg–Feller central limit theorem for a triangular array whose n-th row consists of n
i.i.d. real variables with a row-dependent law — the CLT that bootstrap arguments need, because a
bootstrap resample is i.i.d. from a law (the empirical distribution) that changes with n.

## Provides (API contract)
- Scaled-row form. For probability measures `Q : ℕ → Measure ℝ` and `σ² : ℝ≥0`: the law of
  `y ↦ ∑ i : Fin n, y i` under `Measure.pi (fun _ : Fin n => Q n)` converges weakly (in
  `ProbabilityMeasure ℝ`) to `gaussianReal 0 σ²`.
- Unscaled-row form (the shape bootstrap consumers use). For probability measures
  `R : ℕ → Measure ℝ`: the law of `y ↦ (√n)⁻¹ ∑ i : Fin n, y i` under
  `Measure.pi (fun _ : Fin n => R n)` converges weakly to `gaussianReal 0 σ²`.

## Statement / milestones
1. Scaled form. Hypotheses, for every n: `Q n` is a probability measure, `id ∈ L²(Q n)`,
   `∫ x ∂(Q n) = 0`; `n · ∫ x² ∂(Q n) → σ²`; Lindeberg: for every ε > 0,
   `n · ∫_{|x| ≥ ε} x² ∂(Q n) → 0`. Conclusion: the weak convergence above.
2. Unscaled form. Hypotheses: `R n` probability, `id ∈ L²(R n)`, `∫ x ∂(R n) = 0`,
   `∫ x² ∂(R n) → σ²`, and for every ε > 0, `∫_{|x| ≥ ε√n} x² ∂(R n) → 0`. Derived from (1) by
   pushing `R n` forward along `x ↦ x/√n`.
3. The degenerate case σ² = 0 (limit `dirac 0`) must be covered, either inside the main proof or
   by a separate Chebyshev argument.

## Standard reference
Billingsley, *Probability and Measure* (3rd ed.), Theorem 27.2 (Lindeberg–Feller); Durrett,
*Probability: Theory and Examples*, Theorem 3.4.10. Used for the bootstrap in Bickel & Freedman
(1981, Ann. Statist. 9:1196), Section 2.

## Intended reuse
Bootstrap CLT for the sample mean (applied pointwise in the data, with `R n` the empirical law of
the centred observations) and any other rowwise-i.i.d. triangular-array limit (local alternatives,
LAN arguments). The laws are deterministic measures on ℝ, so consumers can apply it for each fixed
data realisation.

## May assume / must derive
- May assume: the hypotheses listed above; Lévy's continuity theorem and characteristic-function
  facts from Mathlib; the existing Causalean martingale-array CLT.
- Must derive: the CLT itself. Do not assume a Lindeberg-type CLT as a hypothesis. Do not require
  third or higher moments (Lyapunov) — the Lindeberg condition is the point.

## Non-goals
- Non-identically distributed rows, varying row lengths, multivariate arrays, Berry–Esseen rates.

## Known building blocks
- `Causalean.Stat.martingaleArrayCLT` (`Causalean/Stat/CLT/Martingale/Main.lean`): independent
  centred rows are a martingale-difference array with deterministic predictable variance.
- Mathlib `Mathlib/Probability/CentralLimitTheorem.lean` (i.i.d. CLT via characteristic
  functions, `tendsto_charFun_inv_sqrt_mul_pow`), `MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun`.
- `Causalean/Estimation/Efficiency/LAN/Convolution/TriangularArray.lean` (i.i.d.-row Lindeberg
  lemmas: `iid_sum_sq_tendstoInProbability_of_lindeberg`, `iid_max_tendsto_zero_of_lindeberg`).
