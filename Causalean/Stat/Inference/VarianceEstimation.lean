/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Consistent variance / covariance estimation for the i.i.d. sample type

Consistency of empirical variance- and covariance-matrix estimators for the
`Causalean.Stat.IIDSample` model, supplying the `σ̂ →ₚ σ₀` hypothesis consumed by
the generic studentized CLT (`Causalean/Stat/Inference/Studentize.lean`,
`Tendsto_dist.div_tendsto_inProb_gaussian`).

* `IIDSample.sampleMean_mul_tendsto_inProb` — empirical mean of an arbitrary
  product `g₁ · g₂` of two measurable, jointly-integrable statistics converges
  in probability to its population integral.  Direct application of the WLLN to
  `g := g₁ · g₂`.
* `IIDSample.sampleCov_entry_tendsto_inProb` — entrywise covariance-matrix
  consistency for a vector influence function `ψ : X → E` (`E` a finite-
  dimensional inner-product space).  Coordinates are extracted by two continuous
  linear functionals `φ φ' : E →L[ℝ] ℝ` (the caller supplies the coordinate
  projections — e.g. `EuclideanSpace.proj j`); for each pair, the empirical mean
  of `φ (ψ x) * φ' (ψ x)` converges in probability to
  `∫ x, φ (ψ x) * φ' (ψ x) ∂P`.  Entrywise integrability is derived from the
  single hypothesis `Integrable (fun x => ‖ψ x‖²) P` via the operator-norm
  bound `|φ (ψ x)| ≤ ‖φ‖ · ‖ψ x‖`.  Working through abstract functionals keeps
  the statement basis-agnostic while remaining fully general.
* `IIDSample.empiricalVar` — the plug-in variance `(1/n) Σ ψ(Zᵢ)² − ψ̄ₙ²` of a scalar
  statistic, with its centred form, nonnegativity, and consistency
  `empiricalVar_tendsto_inProb` (to `∫ ψ² dP` when `∫ ψ dP = 0`).
* `sqrt_var_tendsto_inProb` (`Tendsto_inProb.sqrt`) — packaging for the
  studentized layer: from `σ̂² →ₚ σ₀²` with `σ₀ > 0`, conclude
  `√(σ̂²) →ₚ σ₀`.  Continuous mapping with `Real.sqrt` (continuous everywhere),
  reusing `Tendsto_inProb.comp_continuousAt`.
-/

module
public import Causalean.Stat.Limit.WLLN
public import Causalean.Stat.Limit.Convergence
public import Causalean.Stat.Limit.ContinuousMapping
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-!
This file proves variance and covariance consistency tools for i.i.d. samples.
Inside `IIDSample`, `sampleMean_mul_tendsto_inProb` applies the WLLN to empirical
means of products, and `sampleCov_entry_tendsto_inProb` turns a square-integrable
vector influence function into entrywise covariance-matrix consistency for any
pair of continuous linear coordinate functionals.

`IIDSample.empiricalVar` is the plug-in variance of a scalar statistic; the file proves its
centred form, nonnegativity, and consistency for a mean-zero square-integrable statistic.

The helper `abs_apply_mul_le_norm_sq` supplies the domination bound needed for
entrywise integrability.  The final packaging lemmas `Tendsto_inProb.sqrt` and
`sqrt_var_tendsto_inProb` convert variance-estimator consistency into
standard-error consistency, the input expected by the studentized CLT.
-/

@[expose] public section

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}

namespace IIDSample

/-! ## Scalar product means -/

/-- **Empirical mean of a product.**  For two measurable real-valued statistics
`g₁, g₂` of an i.i.d. sample whose product is integrable, the empirical mean
`S.sampleMean (g₁ · g₂) N` converges in probability to the population integral
`∫ x, g₁ x * g₂ x ∂P`.  Direct application of the generic WLLN to the product
`g := fun x => g₁ x * g₂ x`.

Specializing `g₁ = g₂ = ψ` recovers second-moment / variance consistency
(`sampleSecondMoment_tendsto_inProb`); the general two-factor form is what the
entrywise covariance lemma below needs. -/
theorem sampleMean_mul_tendsto_inProb
    (S : IIDSample Ω X μ P) [IsProbabilityMeasure P] {g₁ g₂ : X → ℝ}
    (hg₁_meas : Measurable g₁) (hg₂_meas : Measurable g₂)
    (hint : Integrable (fun ω => g₁ (S.Z 0 ω) * g₂ (S.Z 0 ω)) μ) :
    Tendsto_inProb (S.sampleMean (fun x => g₁ x * g₂ x))
      (fun _ => ∫ x, g₁ x * g₂ x ∂P) μ :=
  have hintP : Integrable (fun x => g₁ x * g₂ x) P := by
    have hint_map : Integrable (fun x => g₁ x * g₂ x) (μ.map (S.Z 0)) :=
      (MeasureTheory.integrable_map_measure
        (hg₁_meas.mul hg₂_meas).aestronglyMeasurable (S.meas 0).aemeasurable).mpr
        (by simpa [Function.comp_def] using hint)
    rwa [S.law] at hint_map
  S.sampleMean_tendsto_inProb (hg₁_meas.mul hg₂_meas) hintP

/-! ## Covariance-matrix consistency (entrywise)

For a vector influence function `ψ : X → E` with `E` a finite-dimensional
inner-product space, each coordinate of `ψ` is recovered by a continuous linear
functional `φ : E →L[ℝ] ℝ`.  The covariance matrix `∫ ψ ψᵀ dP` is estimated
entrywise by the empirical mean of `φ (ψ ·) * φ' (ψ ·)`; consistency is a direct
WLLN application once entrywise integrability is in hand.  The natural single
hypothesis is `Integrable (fun x => ‖ψ x‖²) P`, from which each entry product is
integrable via the operator-norm bound `|φ v| ≤ ‖φ‖ · ‖v‖`.

The coordinate functionals are supplied by the caller; for
`E = EuclideanSpace ℝ (Fin d)` take `φ = EuclideanSpace.proj j`, so
`φ (ψ x) = (ψ x) j` and the conclusion is the literal entry
`(1/n) Σ (ψ Zᵢ) j (ψ Zᵢ) k →ₚ ∫ (ψ x) j (ψ x) k`. -/

section Vector

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace Ω] [MeasurableSpace X]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The pointwise product of two functional-evaluations is dominated by a
constant times `‖ψ x‖²`: `|φ (ψ x) * φ' (ψ x)| ≤ (‖φ‖ * ‖φ'‖) * ‖ψ x‖²`.
Used to derive entrywise integrability of the product from the single
hypothesis `Integrable (fun x => ‖ψ x‖²) P`. -/
theorem abs_apply_mul_le_norm_sq
    (φ φ' : E →L[ℝ] ℝ) (ψ : X → E) (x : X) :
    |φ (ψ x) * φ' (ψ x)| ≤ (‖φ‖ * ‖φ'‖) * ‖ψ x‖ ^ 2 := by
  rw [abs_mul]
  have hb1 : |φ (ψ x)| ≤ ‖φ‖ * ‖ψ x‖ :=
    (Real.norm_eq_abs _).symm.le.trans (φ.le_opNorm (ψ x))
  have hb2 : |φ' (ψ x)| ≤ ‖φ'‖ * ‖ψ x‖ :=
    (Real.norm_eq_abs _).symm.le.trans (φ'.le_opNorm (ψ x))
  calc |φ (ψ x)| * |φ' (ψ x)|
        ≤ (‖φ‖ * ‖ψ x‖) * (‖φ'‖ * ‖ψ x‖) :=
          mul_le_mul hb1 hb2 (abs_nonneg _)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = (‖φ‖ * ‖φ'‖) * ‖ψ x‖ ^ 2 := by ring

omit [FiniteDimensional ℝ E] in
/-- **Entrywise covariance-matrix consistency.**  For an i.i.d. sample `S` and two continuous
linear coordinate functionals `φ φ' : E →L[ℝ] ℝ`, suppose [a vector influence function
`ψ : X → E` is measurable](hyp:hψ_meas) and [has square-integrable norm along the
sample](hyp:hψ_sq_int). Then [the empirical mean of the entry product `φ(ψ·) · φ'(ψ·)` converges
in probability to the population integral `∫ x, φ(ψ x) · φ'(ψ x) ∂P`](goal).

For `E = EuclideanSpace ℝ (Fin d)` and `φ = EuclideanSpace.proj j`,
`φ' = EuclideanSpace.proj k` this is the literal `(j,k)` entry of the empirical
covariance matrix converging to the population covariance entry.

The single integrability hypothesis `Integrable (fun ω => ‖ψ (S.Z 0 ω)‖²) μ`
yields entrywise integrability via `abs_apply_mul_le_norm_sq`; consistency is
then `sampleMean_mul_tendsto_inProb` with `g₁ = fun x => φ (ψ x)`,
`g₂ = fun x => φ' (ψ x)`. -/
theorem sampleCov_entry_tendsto_inProb
    (S : IIDSample Ω X μ P) [IsProbabilityMeasure P]
    {ψ : X → E}
    (hψ_meas : Measurable ψ)
    (hψ_sq_int : Integrable (fun ω => ‖ψ (S.Z 0 ω)‖ ^ 2) μ)
    (φ φ' : E →L[ℝ] ℝ) :
    Tendsto_inProb
      (S.sampleMean (fun x => φ (ψ x) * φ' (ψ x)))
      (fun _ => ∫ x, φ (ψ x) * φ' (ψ x) ∂P) μ := by
  -- coordinate measurability
  have hφ : Measurable (fun x => φ (ψ x)) := by fun_prop
  have hφ' : Measurable (fun x => φ' (ψ x)) := by fun_prop
  -- entrywise integrability of the product, dominated by (‖φ‖‖φ'‖)·‖ψ‖²
  have hprod_int :
      Integrable (fun ω => φ (ψ (S.Z 0 ω)) * φ' (ψ (S.Z 0 ω))) μ := by
    have hmeas :
        AEStronglyMeasurable
          (fun ω => φ (ψ (S.Z 0 ω)) * φ' (ψ (S.Z 0 ω))) μ :=
      ((hφ.comp (S.meas 0)).mul (hφ'.comp (S.meas 0))).aestronglyMeasurable
    refine Integrable.mono'
      (hψ_sq_int.const_mul (‖φ‖ * ‖φ'‖)) hmeas ?_
    filter_upwards with ω
    simpa [Real.norm_eq_abs] using abs_apply_mul_le_norm_sq φ φ' ψ (S.Z 0 ω)
  exact S.sampleMean_mul_tendsto_inProb hφ hφ' hprod_int

end Vector

/-! ## Plug-in variance of a scalar statistic -/

/-- For [an independent and identically distributed sample](hyp:S), [a real-valued
statistic of one observation](hyp:ψ), and [a sample size](hyp:n), [the plug-in (empirical)
variance](goal) is the function that assigns to each sample-space outcome the empirical mean
of the statistic squared minus the square of its empirical mean, computed from the first $n$
observations at that outcome.

It equals the centred form `(1/n) Σ_{i<n} (ψ(Zᵢ) − ψ̄ₙ)²` (`empiricalVar_eq_centered`), so it
is nonnegative. -/
noncomputable def empiricalVar (S : IIDSample Ω X μ P) (ψ : X → ℝ) (n : ℕ) :
    Ω → ℝ :=
  fun ω => S.sampleMean (fun x => (ψ x) ^ 2) n ω - (S.sampleMean ψ n ω) ^ 2

/-- **Centred form of the empirical variance.** For [an iid sample `S`](hyp:S), [a
statistic `ψ`](hyp:ψ), [a sample size `n`](hyp:n), and [a sample-path outcome
`ω`](hyp:ω), [the plug-in variance of `ψ` equals the centered
empirical second moment of `ψ` over the first `n` observations](goal).

This is the standard `mean-of-squares minus square-of-mean` identity for the
empirical expectation, valid for every `n` (the `n = 0` case is `0 = 0`). -/
theorem empiricalVar_eq_centered (S : IIDSample Ω X μ P) (ψ : X → ℝ) (n : ℕ)
    (ω : Ω) :
    empiricalVar S ψ n ω
      = (n : ℝ)⁻¹ *
          ∑ i ∈ Finset.range n, (ψ (S.Z i ω) - S.sampleMean ψ n ω) ^ 2 := by
  rcases eq_or_ne n 0 with hn | hn
  · subst hn; simp [empiricalVar, IIDSample.sampleMean]
  · have hncast : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    simp only [empiricalVar, IIDSample.sampleMean]
    set f : ℕ → ℝ := fun i => ψ (S.Z i ω) with hf
    have hA : ∑ i ∈ Finset.range n,
          (f i - (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, f j) ^ 2
        = (∑ i ∈ Finset.range n, (f i) ^ 2)
          - 2 * ((n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, f j)
              * (∑ i ∈ Finset.range n, f i)
          + (n : ℝ) * ((n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, f j) ^ 2 := by
      have hpt : ∀ i,
          (f i - (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, f j) ^ 2
            = (f i) ^ 2
              - 2 * ((n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, f j) * (f i)
              + ((n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, f j) ^ 2 :=
        fun i => by ring
      simp_rw [hpt]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hA]
    field_simp
    ring

/-- [The empirical variance is nonnegative](goal), for [any sample](hyp:S),
[statistic](hyp:ψ), [sample size](hyp:n), and [outcome](hyp:ω): it is a centred
empirical second moment (`empiricalVar_eq_centered`). -/
theorem empiricalVar_nonneg (S : IIDSample Ω X μ P) (ψ : X → ℝ) (n : ℕ)
    (ω : Ω) : 0 ≤ empiricalVar S ψ n ω := by
  rw [empiricalVar_eq_centered]
  apply mul_nonneg
  · positivity
  · exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

/-- **Consistency of the empirical variance.** Along the i.i.d. sample `S`, if the influence
function `ψ` is [measurable](hyp:hψ_meas), [integrable](hyp:hψ_int),
[square-integrable](hyp:hψ_sq_int), and [has population mean zero](hyp:hmean), then [the
empirical variance converges in probability to the population second moment $\int
\psi^2\,dP$](goal).

    Proof: `S.sampleMean (ψ²) →ₚ ∫ ψ² dP` (second-moment WLLN) and
`(S.sampleMean ψ)² →ₚ (∫ ψ dP)² = 0` (WLLN + continuous mapping); subtract via
`Tendsto_inProb.sub` and use `∫ ψ dP = 0`. -/
theorem empiricalVar_tendsto_inProb (S : IIDSample Ω X μ P)
    [IsProbabilityMeasure P] {ψ : X → ℝ}
    (hψ_meas : Measurable ψ)
    (hψ_int : Integrable (fun ω => ψ (S.Z 0 ω)) μ)
    (hψ_sq_int : Integrable (fun ω => (ψ (S.Z 0 ω)) ^ 2) μ)
    (hmean : ∫ x, ψ x ∂P = 0) :
    Tendsto_inProb (empiricalVar S ψ) (fun _ => ∫ x, (ψ x) ^ 2 ∂P) μ := by
  have hψ_int_P : Integrable ψ P := by
    have hψ_int_map : Integrable ψ (μ.map (S.Z 0)) :=
      (MeasureTheory.integrable_map_measure hψ_meas.aestronglyMeasurable
        (S.meas 0).aemeasurable).mpr (by simpa [Function.comp_def] using hψ_int)
    rwa [S.law] at hψ_int_map
  have hψ_sq_int_P : Integrable (fun x => (ψ x) ^ 2) P := by
    have hψ_sq_int_map : Integrable (fun x => (ψ x) ^ 2) (μ.map (S.Z 0)) :=
      (MeasureTheory.integrable_map_measure (hψ_meas.pow_const 2).aestronglyMeasurable
        (S.meas 0).aemeasurable).mpr (by simpa [Function.comp_def] using hψ_sq_int)
    rwa [S.law] at hψ_sq_int_map
  have h2 : Tendsto_inProb (S.sampleMean (fun x => (ψ x) ^ 2))
      (fun _ => ∫ x, (ψ x) ^ 2 ∂P) μ :=
    S.sampleSecondMoment_tendsto_inProb hψ_meas hψ_sq_int_P
  have h1 : Tendsto_inProb (S.sampleMean ψ) (fun _ => ∫ x, ψ x ∂P) μ :=
    S.sampleMean_tendsto_inProb hψ_meas hψ_int_P
  have h1sq : Tendsto_inProb (fun n ω => (S.sampleMean ψ n ω) ^ 2)
      (fun _ => (∫ x, ψ x ∂P) ^ 2) μ := by
    have hcont : ContinuousAt (fun x : ℝ => x ^ 2) (∫ x, ψ x ∂P) :=
      (continuous_pow 2).continuousAt
    simpa using Tendsto_inProb.comp_continuousAt hcont h1
  have hsub := Tendsto_inProb.sub h2 h1sq
  have heq : (fun _ : Ω => (∫ x, (ψ x) ^ 2 ∂P) - (∫ x, ψ x ∂P) ^ 2)
      = (fun _ : Ω => ∫ x, (ψ x) ^ 2 ∂P) := by
    funext _; rw [hmean]; ring
  rw [heq] at hsub
  exact hsub

end IIDSample

/-! ## Packaging for the studentized layer -/

/-- **Square root preserves convergence in probability.**  If `Vn →ₚ v₀`
under `μ`, then `√Vn →ₚ √v₀`.  Continuous mapping with the (everywhere
continuous) `Real.sqrt`, via `Tendsto_inProb.comp_continuousAt`. -/
theorem Tendsto_inProb.sqrt
    {Ω : Type*} [MeasurableSpace Ω] {Vn : ℕ → Ω → ℝ} {v₀ : ℝ} {μ : Measure Ω}
    (h : Tendsto_inProb Vn (fun _ => v₀) μ) :
    Tendsto_inProb (fun n ω => Real.sqrt (Vn n ω)) (fun _ => Real.sqrt v₀) μ :=
  Tendsto_inProb.comp_continuousAt (Real.continuous_sqrt.continuousAt) h

/-- **Standard-error consistency from variance consistency.**  Fix [a positive scale
`σ₀`](hyp:hσ₀_pos). If [a variance-estimator sequence `varhat` converges in probability to
`σ₀²`](hyp:h), then [the standard-error estimator `√varhat` converges in probability to
`σ₀`](goal).  This is exactly the `σ̂ →ₚ σ₀` input required by the
generic studentized CLT `Tendsto_dist.div_tendsto_inProb_gaussian`; callers feed
`fun N ω => Real.sqrt (varhat N ω)` to it.

Proof: `√varhat →ₚ √(σ₀²) = |σ₀| = σ₀` by continuous mapping
(`Tendsto_inProb.sqrt`) and `√(σ₀²) = σ₀` for `σ₀ ≥ 0`. -/
theorem sqrt_var_tendsto_inProb
    {Ω : Type*} [MeasurableSpace Ω] {varhat : ℕ → Ω → ℝ} {σ₀ : ℝ}
    {μ : Measure Ω} (hσ₀_pos : 0 < σ₀)
    (h : Tendsto_inProb varhat (fun _ => σ₀ ^ 2) μ) :
    Tendsto_inProb (fun n ω => Real.sqrt (varhat n ω)) (fun _ => σ₀) μ := by
  have hsqrt := Tendsto_inProb.sqrt h
  have heq : Real.sqrt (σ₀ ^ 2) = σ₀ := by
    rw [Real.sqrt_sq (le_of_lt hσ₀_pos)]
  rwa [heq] at hsqrt

end Causalean.Stat
