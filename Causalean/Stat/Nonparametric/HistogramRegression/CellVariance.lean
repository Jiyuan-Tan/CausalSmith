module
public import Causalean.Stat.Nonparametric.HistogramRegression.Counts
public import Causalean.Stat.Nonparametric.HistogramRegression.PatternMeans
public import Causalean.Stat.Nonparametric.HistogramRegression.Population

/-!
# Global centered cell-sample variance

Condition on the full subset of observations falling in one cell. Centering
annuls cross terms, leaving the cell variance times the reciprocal count.
The finite-pattern moments are isolated in `PatternMoments`, and their
totalized-mean consequences in `PatternMeans`, independently of the binomial
identity in `Counts`;
the bounded-response consequence controls the nonempty centered mean.
Clipping and the arbitrary empty default are handled separately in `Centered`.
Related infrastructure, without an import dependency on it, is in
`Causalean.Stat.Sample.Stratified.CenteredNoiseBound` and
`Causalean.Stat.Sample.OccupancyWeightedMean.MomentBounds`.
-/

public section

open MeasureTheory
open scoped BigOperators

namespace Causalean.Stat.Nonparametric.HistogramRegression

noncomputable section

variable {Ω A κ : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
  [Finite κ] [DecidableEq κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]

/-- [Measurable inputs and integrable response moments](hyp:hlabel,hX,hY,hint,hsq),
[zero cell residual mean](hyp:hcenter), and [positive cell mass](hyp:hp)
give [the exact reciprocal-binomial-count variance formula](goal). -/
theorem integral_centeredCellMean_sq_eq {m : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (label : A → κ) (X : Ω → A)
    (Y : Ω → ℝ) (c : ℝ) (k : κ)
    (hlabel : Measurable label) (hX : Measurable X) (hY : Measurable Y)
    (hint : Integrable Y μ) (hsq : Integrable (fun ω => Y ω ^ 2) μ)
    (hcenter : (∫ ω in cell label X k, (Y ω - c) ∂μ) = 0)
    (hp : 0 < cellMass μ label X k) :
    (∫ z : Fin m → Ω, (centeredCellMean label X Y c k z) ^ 2
      ∂Measure.pi (fun _ : Fin m => μ)) =
      ((∫ ω in cell label X k, (Y ω - c) ^ 2 ∂μ) / cellMass μ label X k) *
        ∑ j ∈ Finset.range (m + 1),
          Causalean.Mathlib.Probability.binomialWeight m (cellMass μ label X k) j *
            (if 0 < j then (j : ℝ)⁻¹ else 0) := by
  -- Use integrable_centeredCellMean_sq and split both integrals over all
  -- membership patterns T : Finset (Fin m), a measurable disjoint cover.
  -- Sum integral_centeredCellMean_sq_on_pattern. The bounded inverse-count
  -- integrand is integrable; apply integral_cellCount_eq_binomial to it.
  -- This route avoids summing powersetCard/binomial coefficients a second time.
  classical
  let ν := Measure.pi (fun _ : Fin m => μ)
  let R : (Fin m → Ω) → ℝ := fun z =>
    if 0 < cellCount label X k z then (cellCount label X k z : ℝ)⁻¹ else 0
  have hRmeas : Measurable R :=
    (measurable_of_countable (fun j : ℕ => if 0 < j then (j : ℝ)⁻¹ else 0)).comp
      (measurable_cellCount label X k hlabel hX)
  have hR : Integrable R ν := by
    refine (integrable_const (1 : ℝ)).mono' hRmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall ?_)
    intro z
    dsimp [R]
    split_ifs with hn
    · rw [abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
      apply inv_le_one_of_one_le₀
      exact_mod_cast hn
    · simp
  have hmeas := fun T : Finset (Fin m) =>
    measurableSet_cellPattern label X k T hlabel hX
  have hdisj : Pairwise (Function.onFun Disjoint
      (fun T : Finset (Fin m) => cellPattern label X k T)) := by
    intro T U hTU
    apply Set.disjoint_left.mpr
    intro z hzT hzU
    apply hTU
    ext r
    exact (hzT r).symm.trans (hzU r)
  have hcover : (⋃ T : Finset (Fin m), cellPattern label X k T) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    apply Set.mem_iUnion.mpr
    refine ⟨Finset.univ.filter (fun r => label (X (z r)) = k), ?_⟩
    intro r
    simp
  have hmean := integrable_centeredCellMean_sq (m := m)
    μ label X Y c k hlabel hX hY hint hsq
  have hsum := integral_iUnion_fintype hmeas hdisj
    (fun T => hmean.integrableOn (s := cellPattern label X k T))
  have hsumR := integral_iUnion_fintype hmeas hdisj
    (fun T => hR.integrableOn (s := cellPattern label X k T))
  rw [hcover, setIntegral_univ] at hsum hsumR
  rw [hsum]
  simp_rw [integral_centeredCellMean_sq_on_pattern
    μ label X Y c k _ hlabel hX hY hint hsq hcenter hp]
  rw [← Finset.mul_sum, ← hsumR]
  rw [integral_cellCount_eq_binomial μ label X k
    (fun j => if 0 < j then (j : ℝ)⁻¹ else 0) hlabel hX]

/-- [A measurable partition and responses](hyp:hlabel,hX,hY), [unit-interval
responses](hyp:hbound), and [positive cell mass](hyp:hp) imply
[the mass-weighted nonempty-sample centered MSE bound](goal). -/
theorem nonempty_cell_mse_le {m : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (label : A → κ) (X : Ω → A)
    (Y : Ω → ℝ) (k : κ) (hlabel : Measurable label)
    (hX : Measurable X) (hY : Measurable Y)
    (hbound : ∀ᵐ ω ∂μ, Y ω ∈ Set.Icc (0 : ℝ) 1)
    (hp : 0 < cellMass μ label X k) :
    cellMass μ label X k *
      (∫ z : Fin m → Ω, (centeredCellMean label X Y (cellMean μ label X Y k) k z) ^ 2
        ∂Measure.pi (fun _ : Fin m => μ)) ≤ 2 / (m + 1 : ℝ) := by
  -- Dominate Y and Y^2 by 1 to obtain both integrability hypotheses.
  -- cellMean_mem_Icc bounds c. integral_sub, setIntegral_const, and hp
  -- give the zero residual set integral. The squared residual is at most 1
  -- ae on the cell, so its set integral divided by p is at most 1.
  -- Invoke integral_centeredCellMean_sq_eq and the closed
  -- mass_mul_integral_inverse_count_le (rewriting its integral by Counts).
  -- Multipliers are nonnegative; sample size zero and p=1 need no exceptions.
  have hint : Integrable Y μ := by
    apply (integrable_const (1 : ℝ)).mono' hY.aestronglyMeasurable
    filter_upwards [hbound] with ω hω
    simpa [Real.norm_eq_abs, abs_of_nonneg hω.1] using hω.2
  have hsq : Integrable (fun ω => Y ω ^ 2) μ := by
    apply (integrable_const (1 : ℝ)).mono' (hY.pow_const 2).aestronglyMeasurable
    filter_upwards [hbound] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [hω.1, hω.2]
  have hc := cellMean_mem_Icc μ label X Y k hlabel hX hY hbound
  have hresbound : ∀ᵐ ω ∂μ, (Y ω - cellMean μ label X Y k) ^ 2 ≤ 1 := by
    filter_upwards [hbound] with ω hω
    have hl : -1 ≤ Y ω - cellMean μ label X Y k := by linarith [hω.1, hc.2]
    have hu : Y ω - cellMean μ label X Y k ≤ 1 := by linarith [hω.2, hc.1]
    simpa using sq_le_sq' hl hu
  have hres : Integrable (fun ω => (Y ω - cellMean μ label X Y k) ^ 2) μ := by
    apply (integrable_const (1 : ℝ)).mono'
      ((hY.sub measurable_const).pow_const 2).aestronglyMeasurable
    filter_upwards [hresbound] with ω hω
    change ‖(Y ω - cellMean μ label X Y k) ^ 2‖ ≤ 1
    rwa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hcenter : (∫ ω in cell label X k, (Y ω - cellMean μ label X Y k) ∂μ) = 0 := by
    rw [integral_sub hint.integrableOn (integrable_const _), setIntegral_const]
    simp only [smul_eq_mul]
    change (∫ ω in cell label X k, Y ω ∂μ) -
      cellMass μ label X k * cellMean μ label X Y k = 0
    rw [cellMean, mul_div_cancel₀ _ (ne_of_gt hp), sub_self]
  have hvar : (∫ ω in cell label X k, (Y ω - cellMean μ label X Y k) ^ 2 ∂μ) /
      cellMass μ label X k ≤ 1 := by
    apply (div_le_iff₀ hp).mpr
    have hle := integral_mono_ae (μ := μ.restrict (cell label X k))
      hres.integrableOn (integrable_const (1 : ℝ))
      (ae_restrict_of_ae hresbound)
    simpa [setIntegral_const, cellMass, Measure.real] using hle
  have hrecnonneg : 0 ≤ (∫ z : Fin m → Ω,
      (if 0 < cellCount label X k z then (cellCount label X k z : ℝ)⁻¹ else 0)
      ∂Measure.pi (fun _ : Fin m => μ)) := by
    apply integral_nonneg
    intro z
    dsimp only
    split_ifs <;> positivity
  rw [integral_centeredCellMean_sq_eq μ label X Y (cellMean μ label X Y k) k
    hlabel hX hY hint hsq hcenter hp,
    ← integral_cellCount_eq_binomial μ label X k
      (fun j => if 0 < j then (j : ℝ)⁻¹ else 0) hlabel hX]
  calc
    _ ≤ cellMass μ label X k * (1 *
        (∫ z : Fin m → Ω,
          (if 0 < cellCount label X k z then (cellCount label X k z : ℝ)⁻¹ else 0)
          ∂Measure.pi (fun _ : Fin m => μ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hvar hrecnonneg) hp.le
    _ ≤ 2 / (m + 1 : ℝ) := by
      simpa only [one_mul] using
        mass_mul_integral_inverse_count_le (m := m) μ label X k hlabel hX hp

end

end Causalean.Stat.Nonparametric.HistogramRegression
