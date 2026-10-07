module
public import Causalean.Stat.Nonparametric.HistogramRegression.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# Regression cell means and oscillation bias

The conditional-mean premise is the defining set-integral characterization of
`E[Y | X] = g(X)`, together with integrability. It asks only for a population
regression identity, never for any sample-risk or rate estimate. A separate
bridge accepts Mathlib's conditional expectation on the sigma algebra generated
by `X`. Boundedness of the regression representative is derived almost surely.
-/

@[expose] public section

open MeasureTheory

namespace Causalean.Stat.Nonparametric.HistogramRegression

noncomputable section

variable {Ω A κ : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
  [MeasurableSpace κ] [MeasurableSingletonClass κ]

/-- The [conditional-mean relation](goal) for [the observation law, covariates,
responses, and regression function](hyp:μ,X,Y,g) says both responses and fitted
population values are integrable and have equal integrals on every covariate-measurable event. -/
def ConditionalMean (μ : Measure Ω) (X : Ω → A) (Y : Ω → ℝ) (g : A → ℝ) : Prop :=
  Integrable Y μ ∧ Integrable (fun ω => g (X ω)) μ ∧
    ∀ s : Set A, MeasurableSet s →
      (∫ ω in X ⁻¹' s, Y ω ∂μ) = ∫ ω in X ⁻¹' s, g (X ω) ∂μ

/-- The [population cell mean](goal) averages [responses](hyp:Y) under
[the observation law](hyp:μ) within [the specified partition cell](hyp:label,X,k),
totalizing to zero at zero cell mass. -/
def cellMean (μ : Measure Ω) (label : A → κ) (X : Ω → A)
    (Y : Ω → ℝ) (k : κ) : ℝ :=
  (∫ ω in cell label X k, Y ω ∂μ) / cellMass μ label X k

/-- [A conditional-expectation equality](hyp:hcond) for [measurable covariates
and integrable responses](hyp:hX,hY) implies
[the conditional-mean relation](goal). -/
theorem conditionalMean_of_condExp (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → A) (Y : Ω → ℝ) (g : A → ℝ)
    (hX : Measurable X) (hY : Integrable Y μ)
    (hcond : μ[Y | MeasurableSpace.comap X inferInstance] =ᵐ[μ] fun ω => g (X ω)) :
    ConditionalMean μ X Y g := by
  have hm : MeasurableSpace.comap X inferInstance ≤ (inferInstance : MeasurableSpace Ω) :=
    hX.comap_le
  refine ⟨hY, integrable_condExp.congr hcond, ?_⟩
  intro s hs
  have hs' : MeasurableSet[MeasurableSpace.comap X inferInstance] (X ⁻¹' s) :=
    ⟨s, hs, rfl⟩
  calc
    (∫ ω in X ⁻¹' s, Y ω ∂μ) =
        ∫ ω in X ⁻¹' s, (μ[Y | MeasurableSpace.comap X inferInstance]) ω ∂μ :=
      (setIntegral_condExp hm hY hs').symm
    _ = ∫ ω in X ⁻¹' s, g (X ω) ∂μ :=
      integral_congr_ae (ae_restrict_of_ae hcond)

/-- [Measurable covariates and regression function](hyp:hX,hg),
[unit-interval responses](hyp:hY), and [the conditional-mean relation](hyp:hmean)
imply that [the regression function is almost surely in the unit interval](goal). -/
theorem regression_mem_Icc_ae (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → A) (Y : Ω → ℝ) (g : A → ℝ)
    (hX : Measurable X) (hg : Measurable g)
    (hY : ∀ᵐ ω ∂μ, Y ω ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ConditionalMean μ X Y g) :
    ∀ᵐ ω ∂μ, g (X ω) ∈ Set.Icc (0 : ℝ) 1 := by
  have nonneg_of_test (f : A → ℝ) (hf : Measurable f)
      (hfi : Integrable (fun ω => f (X ω)) μ)
      (htest : 0 ≤ ∫ ω in X ⁻¹' {x | f x < 0}, f (X ω) ∂μ) :
      ∀ᵐ ω ∂μ, 0 ≤ f (X ω) := by
    have hs : MeasurableSet (X ⁻¹' {x | f x < 0}) :=
      (measurableSet_lt hf measurable_const).preimage hX
    have hn : ∀ᵐ ω ∂μ.restrict (X ⁻¹' {x | f x < 0}), 0 ≤ -f (X ω) := by
      filter_upwards [ae_restrict_mem hs] with ω hω
      exact neg_nonneg.mpr (le_of_lt hω)
    have hz : (∫ ω in X ⁻¹' {x | f x < 0}, -f (X ω) ∂μ) = 0 := by
      rw [integral_neg]
      have hp := integral_nonneg_of_ae hn
      rw [integral_neg] at hp
      linarith
    have he := (integral_eq_zero_iff_of_nonneg_ae hn hfi.integrableOn.neg).mp hz
    have he' := (ae_restrict_iff' hs).mp he
    filter_upwards [he'] with ω hω
    by_contra h
    have hh := hω (lt_of_not_ge h)
    change -f (X ω) = 0 at hh
    linarith
  have hlo : ∀ᵐ ω ∂μ, 0 ≤ g (X ω) := by
    apply nonneg_of_test g hg hmean.2.1
    rw [← hmean.2.2 _ (measurableSet_lt hg measurable_const)]
    exact setIntegral_nonneg_of_ae (hY.mono fun ω hω => hω.1)
  have hhi : ∀ᵐ ω ∂μ, 0 ≤ 1 - g (X ω) := by
    apply nonneg_of_test (fun x => 1 - g x) (measurable_const.sub hg)
      ((integrable_const 1).sub hmean.2.1)
    rw [integral_sub (integrable_const 1) hmean.2.1.integrableOn,
      ← hmean.2.2 {x | 1 - g x < 0}
        (measurableSet_lt (show Measurable (fun x : A => (1 : ℝ) - g x) from
          measurable_const.sub hg) measurable_const)]
    exact sub_nonneg.mpr (integral_mono_ae hmean.1.integrableOn
      (integrable_const 1) (ae_restrict_of_ae (hY.mono fun ω hω => hω.2)))
  filter_upwards [hlo, hhi] with ω hlo hhi
  exact ⟨hlo, by linarith⟩

/-- [Measurable partition labels](hyp:hlabel) and [the conditional-mean relation](hyp:hmean)
imply that [the response cell mean equals the regression cell mean](goal). -/
theorem cellMean_eq_regression (μ : Measure Ω) (label : A → κ)
    (X : Ω → A) (Y : Ω → ℝ) (g : A → ℝ) (k : κ)
    (hlabel : Measurable label) (hmean : ConditionalMean μ X Y g) :
    cellMean μ label X Y k = cellMean μ label X (fun ω => g (X ω)) k := by
  unfold cellMean
  congr 1
  exact hmean.2.2 (label ⁻¹' {k}) ((measurableSet_singleton k).preimage hlabel)

/-- [Measurable responses](hyp:hYm) and
[bounded responses](hyp:hY)
ensure [the totalized population cell mean belongs to the unit interval](goal). -/
theorem cellMean_mem_Icc (μ : Measure Ω) [IsProbabilityMeasure μ]
    (label : A → κ) (X : Ω → A) (Y : Ω → ℝ) (k : κ)
    (hYm : Measurable Y)
    (hY : ∀ᵐ ω ∂μ, Y ω ∈ Set.Icc (0 : ℝ) 1) :
    cellMean μ label X Y k ∈ Set.Icc (0 : ℝ) 1 := by
  have hi : Integrable Y μ := (integrable_const (1 : ℝ)).mono' hYm.aestronglyMeasurable
    (hY.mono fun ω hω => by simpa [Real.norm_eq_abs, abs_of_nonneg hω.1] using hω.2)
  have hm : 0 ≤ cellMass μ label X k := ENNReal.toReal_nonneg
  by_cases hz : cellMass μ label X k = 0
  · simp [cellMean, hz]
  · have hp : 0 < cellMass μ label X k := lt_of_le_of_ne hm (Ne.symm hz)
    refine ⟨div_nonneg (setIntegral_nonneg_of_ae (hY.mono fun ω hω => hω.1)) hm, ?_⟩
    change (∫ ω in cell label X k, Y ω ∂μ) / cellMass μ label X k ≤ 1
    apply (div_le_iff₀ hp).mpr
    have hle := integral_mono_ae (μ := μ.restrict (cell label X k))
      hi.integrableOn (integrable_const (1 : ℝ))
      (ae_restrict_of_ae (hY.mono fun ω hω => hω.2))
    simpa [setIntegral_const, cellMass, Measure.real] using hle

/-- [Measurable inputs](hyp:hlabel,hX,hg), [bounded responses](hyp:hY),
[the conditional-mean relation](hyp:hmean), and [a nonnegative within-cell
oscillation envelope](hyp:hδ,hosc) imply [the integrated squared cell bias is
at most cell mass times the squared envelope](goal). -/
theorem cell_bias_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (label : A → κ) (X : Ω → A) (Y : Ω → ℝ) (g : A → ℝ) (k : κ)
    (δ : ℝ) (hlabel : Measurable label) (hX : Measurable X) (hg : Measurable g)
    (hY : ∀ᵐ ω ∂μ, Y ω ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ConditionalMean μ X Y g) (hδ : 0 ≤ δ)
    (hosc : ∀ x x', label x = k → label x' = k → |g x - g x'| ≤ δ) :
    (∫ ω in cell label X k, (cellMean μ label X Y k - g (X ω)) ^ 2 ∂μ) ≤
      cellMass μ label X k * δ ^ 2 := by
  have hs : MeasurableSet (cell label X k) :=
    (measurableSet_singleton k).preimage (hlabel.comp hX)
  have hm : 0 ≤ cellMass μ label X k := ENNReal.toReal_nonneg
  by_cases hz : cellMass μ label X k = 0
  · have hzμ : μ (cell label X k) = 0 := by
      exact ((ENNReal.toReal_eq_zero_iff _).mp hz).resolve_right (measure_ne_top μ _)
    simp [Measure.restrict_eq_zero.mpr hzμ, hz]
  · have hp : 0 < cellMass μ label X k := lt_of_le_of_ne hm (Ne.symm hz)
    have he := cellMean_eq_regression μ label X Y g k hlabel hmean
    have hpoint : ∀ ω ∈ cell label X k,
        |cellMean μ label X Y k - g (X ω)| ≤ δ := by
      intro ω hω
      have hlo : (cellMass μ label X k) * (g (X ω) - δ) ≤
          ∫ ω' in cell label X k, g (X ω') ∂μ := by
        have hi := integral_mono_ae (μ := μ.restrict (cell label X k))
          (integrable_const (g (X ω) - δ)) hmean.2.1.integrableOn
          (ae_restrict_of_forall_mem hs fun ω' hω' => by
            have hh := (abs_le.mp (hosc (X ω') (X ω) hω' hω)).1
            linarith)
        simpa [setIntegral_const, cellMass, Measure.real] using hi
      have hhi : (∫ ω' in cell label X k, g (X ω') ∂μ) ≤
          (cellMass μ label X k) * (g (X ω) + δ) := by
        have hi := integral_mono_ae (μ := μ.restrict (cell label X k))
          hmean.2.1.integrableOn (integrable_const (g (X ω) + δ))
          (ae_restrict_of_forall_mem hs fun ω' hω' => by
            have hh := (abs_le.mp (hosc (X ω') (X ω) hω' hω)).2
            linarith)
        simpa [setIntegral_const, cellMass, Measure.real] using hi
      rw [he, cellMean]
      apply abs_le.mpr
      have hl := (le_div_iff₀ hp).mpr (by simpa [mul_comm] using hlo)
      have hu := (div_le_iff₀ hp).mpr (by simpa [mul_comm] using hhi)
      constructor <;> linarith
    have hb := regression_mem_Icc_ae μ X Y g hX hg hY hmean
    have hc : cellMean μ label X Y k ∈ Set.Icc (0 : ℝ) 1 := by
      rw [he]
      exact cellMean_mem_Icc μ label X (fun ω => g (X ω)) k (hg.comp hX) hb
    have hi : Integrable (fun ω => (cellMean μ label X Y k - g (X ω)) ^ 2) μ := by
      apply (integrable_const (1 : ℝ)).mono'
        ((measurable_const.sub (hg.comp hX)).pow_const 2).aestronglyMeasurable
      filter_upwards [hb] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hl : -1 ≤ cellMean μ label X Y k - g (X ω) := by linarith [hc.1, hω.2]
      have hu : cellMean μ label X Y k - g (X ω) ≤ 1 := by linarith [hc.2, hω.1]
      simpa using sq_le_sq' hl hu
    have hle := integral_mono_ae (μ := μ.restrict (cell label X k))
      hi.integrableOn (integrable_const (δ ^ 2))
      (ae_restrict_of_forall_mem hs fun ω hω => by
        exact sq_le_sq.mpr (by simpa [abs_of_nonneg hδ] using hpoint ω hω))
    simpa [setIntegral_const, cellMass, Measure.real] using hle

end

end Causalean.Stat.Nonparametric.HistogramRegression
