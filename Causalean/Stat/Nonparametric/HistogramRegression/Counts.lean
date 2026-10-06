module
public import Causalean.Mathlib.Probability.BernoulliMeasure
public import Causalean.Stat.Nonparametric.HistogramRegression.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Binomial cell counts and empty-cell control

This layer transfers iid product sampling to the real binomial weights already
provided by Causalean. The empty-cell inequality includes both endpoints of the
probability interval and sample size zero. No regression or risk assumption is
used here.
-/

public section

open MeasureTheory
open scoped BigOperators

namespace Causalean.Stat.Nonparametric.HistogramRegression

noncomputable section

variable {Ω A κ : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
  [Finite κ] [DecidableEq κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]

/-- [A measurable covariate partition](hyp:hlabel,hX) implies that
[expectations of functions of a cell count equal the corresponding binomial sum](goal). -/
theorem integral_cellCount_eq_binomial {m : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (label : A → κ) (X : Ω → A) (k : κ) (F : ℕ → ℝ)
    (hlabel : Measurable label) (hX : Measurable X) :
    (∫ z : Fin m → Ω, F (cellCount label X k z) ∂Measure.pi (fun _ : Fin m => μ)) =
      ∑ j ∈ Finset.range (m + 1),
        Causalean.Mathlib.Probability.binomialWeight m (cellMass μ label X k) j * F j := by
  -- Push the sample through its Bool membership design, integrate the finite
  -- design law, and reuse sum_bernoulli_eq_binomial. Arbitrary F is harmless:
  -- the count has finite range, so its composition is integrable.
  classical
  let B : Ω → Bool := fun ω => if label (X ω) = k then true else false
  have hs : MeasurableSet (cell label X k) :=
    (measurableSet_singleton k).preimage (hlabel.comp hX)
  have hB : Measurable B := Measurable.ite hs measurable_const measurable_const
  have hp0 : 0 ≤ cellMass μ label X k := ENNReal.toReal_nonneg
  have hp1 : cellMass μ label X k ≤ 1 := by
    exact measureReal_le_one
  have hmap : μ.map B = Causalean.Mathlib.Probability.bernoulliBool
      (cellMass μ label X k) := by
    apply Measure.ext_of_singleton
    intro b
    rw [Measure.map_apply hB (measurableSet_singleton b)]
    cases b
    · have he : B ⁻¹' {false} = (cell label X k)ᶜ := by
        ext ω
        simp [B, cell]
      rw [he, measure_compl hs (measure_ne_top μ _)]
      simp [Causalean.Mathlib.Probability.bernoulliBool, cellMass,
        ENNReal.ofReal_sub, ENNReal.ofReal_toReal (measure_ne_top μ _)]
    · have he : B ⁻¹' {true} = cell label X k := by
        ext ω
        simp [B, cell]
      rw [he]
      simp [Causalean.Mathlib.Probability.bernoulliBool, cellMass,
        ENNReal.ofReal_toReal (measure_ne_top μ _)]
  let T : (Fin m → Ω) → (Fin m → Bool) := fun z r => B (z r)
  have hT : Measurable T := measurable_pi_lambda _ fun r =>
    hB.comp (measurable_pi_apply r)
  have hpi : (Measure.pi (fun _ : Fin m => μ)).map T =
      Measure.pi (fun _ : Fin m =>
        Causalean.Mathlib.Probability.bernoulliBool (cellMass μ label X k)) := by
    rw [Measure.pi_map_pi (fun _ => hB.aemeasurable)]
    simp only [hmap]
  have : IsProbabilityMeasure (Causalean.Mathlib.Probability.bernoulliBool
      (cellMass μ label X k)) :=
    Causalean.Mathlib.Probability.bernoulliBool_isProbabilityMeasure hp0 hp1
  let G : (Fin m → Bool) → ℝ := fun b =>
    F (Finset.univ.filter fun r => b r = true).card
  have hcount (z : Fin m → Ω) : G (T z) = F (cellCount label X k z) := by
    simp [G, T, B, cellCount]
  rw [← show (fun z => G (T z)) = (fun z => F (cellCount label X k z)) from
    funext hcount, ← integral_map hT.aemeasurable
      (measurable_of_finite G).aestronglyMeasurable, hpi,
    integral_fintype Integrable.of_finite]
  calc
    _ = ∑ b : Fin m → Bool,
        (∏ r, if b r then cellMass μ label X k else 1 - cellMass μ label X k) *
          F (Finset.univ.filter fun r => b r = true).card := by
      apply Finset.sum_congr rfl
      intro b _
      rw [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
      simp only [smul_eq_mul, G]
      congr 1
      apply Finset.prod_congr rfl
      intro r _
      cases b r <;>
        simp [Causalean.Mathlib.Probability.bernoulliBool, hp0, sub_nonneg.mpr hp1]
    _ = _ := by
      simpa using Causalean.Mathlib.Probability.sum_bernoulli_eq_binomial
        (ι := Fin m) (cellMass μ label X k) F

/-- [A measurable covariate partition](hyp:hlabel,hX) gives
[empty-cell probability equal to the failure probability raised to the sample size](goal). -/
theorem empty_cell_probability {m : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (label : A → κ) (X : Ω → A) (k : κ)
    (hlabel : Measurable label) (hX : Measurable X) :
    ((Measure.pi (fun _ : Fin m => μ)) {z | cellCount label X k z = 0}).toReal =
      (1 - cellMass μ label X k) ^ m := by
  classical
  have hs : MeasurableSet {z : Fin m → Ω | cellCount label X k z = 0} :=
    (measurableSet_singleton 0).preimage (measurable_cellCount label X k hlabel hX)
  have h := integral_cellCount_eq_binomial (m := m) μ label X k
    (fun j => if j = 0 then 1 else 0) hlabel hX
  have hi : (∫ z : Fin m → Ω,
      (if cellCount label X k z = 0 then (1 : ℝ) else 0)
      ∂Measure.pi (fun _ : Fin m => μ)) =
      ((Measure.pi (fun _ : Fin m => μ)) {z | cellCount label X k z = 0}).toReal := by
    simpa only [Set.indicator, Set.mem_ofPred_eq, Pi.one_apply, measureReal_def] using
      (integral_indicator_one (μ := Measure.pi (fun _ : Fin m => μ)) hs)
  rw [hi] at h
  simpa [Causalean.Mathlib.Probability.binomialWeight] using h

/-- [A probability in the unit interval](hyp:hp) satisfies
[the mass-weighted empty-cell bound](goal), including zero observations. -/
theorem mass_mul_empty_probability_le (m : ℕ) (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    p * (1 - p) ^ m ≤ 1 / (m + 1 : ℝ) := by
  -- The first m+1 terms of the geometric series are each at least (1-p)^m;
  -- multiply by p and use the telescoping sum 1-(1-p)^(m+1) ≤ 1.
  have hq0 : 0 ≤ 1 - p := sub_nonneg.mpr hp.2
  have hq1 : 1 - p ≤ 1 := by linarith [hp.1]
  have hsum : (m + 1 : ℝ) * (1 - p) ^ m ≤
      ∑ j ∈ Finset.range (m + 1), (1 - p) ^ j := by
    calc
      _ = ∑ j ∈ Finset.range (m + 1), (1 - p) ^ m := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro j hj
        exact pow_le_pow_of_le_one hq0 hq1 (by simpa using Finset.mem_range.mp hj)
  have hid := geom_sum_mul_neg (1 - p) (m + 1)
  have hbound : p * ((m + 1 : ℝ) * (1 - p) ^ m) ≤ 1 := by
    have hmul := mul_le_mul_of_nonneg_left hsum hp.1
    have hpow := pow_nonneg hq0 (m + 1)
    simp only [sub_sub_cancel] at hid
    nlinarith
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < m + 1)).2
  nlinarith

/-- [A measurable partition](hyp:hlabel,hX) and [positive cell mass](hyp:hp)
give [mass-weighted expected reciprocal count at most twice the reciprocal
sample-size successor](goal). -/
theorem mass_mul_integral_inverse_count_le {m : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (label : A → κ) (X : Ω → A) (k : κ)
    (hlabel : Measurable label) (hX : Measurable X) (hp : 0 < cellMass μ label X k) :
    cellMass μ label X k *
      (∫ z : Fin m → Ω,
        (if 0 < cellCount label X k z then (cellCount label X k z : ℝ)⁻¹ else 0)
        ∂Measure.pi (fun _ : Fin m => μ)) ≤ 2 / (m + 1 : ℝ) := by
  rw [integral_cellCount_eq_binomial μ label X k
    (fun j => if 0 < j then (j : ℝ)⁻¹ else 0) hlabel hX]
  have hp1 : cellMass μ label X k ≤ 1 := measureReal_le_one
  have h := mul_le_mul_of_nonneg_left
    (Causalean.Mathlib.Probability.binomial_totalized_inverse_count_le
      m (cellMass μ label X k) hp hp1) hp.le
  calc
    _ ≤ cellMass μ label X k *
        (2 / (((m + 1 : ℕ) : ℝ) * cellMass μ label X k)) := h
    _ = 2 / (m + 1 : ℝ) := by
      push_cast
      field_simp


end

end Causalean.Stat.Nonparametric.HistogramRegression
