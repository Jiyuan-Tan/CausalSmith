module
public import Causalean.Stat.Nonparametric.HistogramRegression.CellVariance
public import Causalean.Stat.Nonparametric.HistogramRegression.EstimatorComparison

/-!
# Totalized clipped cell-estimation risk

Combine the closed-form centered-mean variance and empty-cell probability
with the deterministic clipping comparison. The fixed default may be any
point in the unit interval. No lower cell-mass bound is required.
-/

public section

open MeasureTheory
open scoped BigOperators

namespace Causalean.Stat.Nonparametric.HistogramRegression

noncomputable section

variable {Ω A κ : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
  [Finite κ] [DecidableEq κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]

/-- [Measurable inputs](hyp:hlabel,hX,hY), [unit-interval responses and
default](hyp:hbound,ha), and [positive cell mass](hyp:hp) imply
[mass-weighted cell-estimation MSE at most three over the sample-size successor](goal). -/
theorem cell_estimation_mse_le {m : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (label : A → κ) (X : Ω → A)
    (Y : Ω → ℝ) (a : ℝ) (k : κ) (hlabel : Measurable label)
    (hX : Measurable X) (hY : Measurable Y)
    (hbound : ∀ᵐ ω ∂μ, Y ω ∈ Set.Icc (0 : ℝ) 1)
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hp : 0 < cellMass μ label X k) :
    cellMass μ label X k *
      (∫ z : Fin m → Ω, (cellEstimate label X Y a k z - cellMean μ label X Y k) ^ 2
        ∂Measure.pi (fun _ : Fin m => μ)) ≤ 3 / (m + 1 : ℝ) := by
  -- Set c=cellMean and use cellMean_mem_Icc. The pointwise
  -- cellEstimate_sq_error_le comparison avoids lifting ae response bounds
  -- to every training coordinate: clipping contracts distance to c even for
  -- unbounded inputs. Integrability of the left loss is provided by
  -- integrable_cellEstimate_sq_error; the centered square uses PatternMeans.
  -- Integrate the comparison, identify the indicator expectation with
  -- empty_cell_probability, multiply by p, and add the closed nonempty and
  -- mass_mul_empty_probability_le bounds to obtain 3/(m+1).
  let ν := Measure.pi (fun _ : Fin m => μ)
  let c := cellMean μ label X Y k
  let E : (Fin m → Ω) → ℝ := fun z =>
    if cellCount label X k z = 0 then 1 else 0
  have hc := cellMean_mem_Icc μ label X Y k hY hbound
  have hint : Integrable Y μ := by
    apply (integrable_const (1 : ℝ)).mono' hY.aestronglyMeasurable
    filter_upwards [hbound] with ω hω
    simpa [Real.norm_eq_abs, abs_of_nonneg hω.1] using hω.2
  have hsq : Integrable (fun ω => Y ω ^ 2) μ := by
    apply (integrable_const (1 : ℝ)).mono' (hY.pow_const 2).aestronglyMeasurable
    filter_upwards [hbound] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [hω.1, hω.2]
  have hcenter := integrable_centeredCellMean_sq (m := m)
    μ label X Y c k hlabel hX hY hint hsq
  have hs : MeasurableSet {z : Fin m → Ω | cellCount label X k z = 0} :=
    (measurableSet_singleton 0).preimage (measurable_cellCount label X k hlabel hX)
  have hE : Integrable E ν := by
    have hmeas : Measurable E := Measurable.ite hs measurable_const measurable_const
    refine (integrable_const (1 : ℝ)).mono' hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall ?_)
    intro z
    simp only [E]
    split_ifs <;> norm_num
  have hEeq : (∫ z, E z ∂ν) = (1 - cellMass μ label X k) ^ m := by
    have hi := integral_indicator_one (μ := ν) hs
    have hi' : (∫ z, E z ∂ν) = (ν {z | cellCount label X k z = 0}).toReal := by
      simpa only [E, Set.indicator, Set.mem_ofPred_eq, Pi.one_apply, measureReal_def] using hi
    rw [hi']
    exact empty_cell_probability μ label X k hlabel hX
  have hle := integral_mono_ae
    (integrable_cellEstimate_sq_error μ label X Y a c k hlabel hX hY ha hc)
    (hcenter.add hE)
    (Filter.Eventually.of_forall (fun z => cellEstimate_sq_error_le label X Y a c k z ha hc))
  change (∫ z, (cellEstimate label X Y a k z - c) ^ 2 ∂ν) ≤
    ∫ z, (centeredCellMean label X Y c k z) ^ 2 + E z ∂ν at hle
  rw [integral_add hcenter hE, hEeq] at hle
  have hmul := mul_le_mul_of_nonneg_left hle hp.le
  have hn := nonempty_cell_mse_le (m := m) μ label X Y k hlabel hX hY hbound hp
  have he := mass_mul_empty_probability_le m (cellMass μ label X k)
    ⟨hp.le, measureReal_le_one⟩
  dsimp [ν, c] at hmul
  rw [mul_add] at hmul
  exact hmul.trans (by
    calc
      _ ≤ 2 / (m + 1 : ℝ) + 1 / (m + 1 : ℝ) := add_le_add hn he
      _ = 3 / (m + 1 : ℝ) := by ring)

end

end Causalean.Stat.Nonparametric.HistogramRegression
