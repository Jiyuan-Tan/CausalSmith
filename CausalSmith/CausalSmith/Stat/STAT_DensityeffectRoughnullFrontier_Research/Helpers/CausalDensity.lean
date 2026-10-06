module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Causal
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.ProjectionMeans

/-!
Normalization of the conditional potential-outcome laws and their identified marginals.
Fubini gives the marginal event probabilities required by the causal-completion construction.
-/

public section

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- Each conditional outcome density defines a probability law on the unit interval. -/
-- @node: conditionalOutcome_isProbabilityMeasure
lemma conditionalOutcome_isProbabilityMeasure (P : ObsLaw) (a : Bool) (x : ℝ)
    (hx : x ∈ Set.Icc 0 1) :
    IsProbabilityMeasure (unitVolume.withDensity (fun y => ENNReal.ofReal (P.eta a x y))) := by
  constructor
  have hn : 0 ≤ᵐ[unitVolume] P.eta a x := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact P.eta_nonneg a x y hx hy
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (P.eta_integrable a x hx) hn,
    P.eta_normalized a x hx]
  norm_num

/-- Covariate integration preserves measurability of the outcome density. -/
@[fun_prop] lemma measurable_marginalDensity (P : ObsLaw) (a : Bool) :
    Measurable (marginalDensity P a) := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  exact (P.eta_measurable a).stronglyMeasurable.integral_prod_left'.measurable

/-- The bounded joint density has an integrable outcome marginal by Fubini. -/
-- @node: integrable_marginalDensity
lemma integrable_marginalDensity (P : ObsLaw) (hModel : Model P) (a : Bool) :
    Integrable (marginalDensity P a) unitVolume := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  exact (integrable_eta_joint P hModel a).integral_prod_right

/-- A potential-outcome marginal density is nonnegative on its outcome support. -/
-- @node: marginalDensity_nonneg
lemma marginalDensity_nonneg (P : ObsLaw) (a : Bool) (y : ℝ)
    (hy : y ∈ Set.Icc 0 1) : 0 ≤ marginalDensity P a y := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  exact P.eta_nonneg a x y hx hy

/-- The marginal integrates to one because each conditional density integrates to one. -/
-- @node: marginalDensity_normalized
lemma marginalDensity_normalized (P : ObsLaw) (hModel : Model P) (a : Bool) :
    ∫ y, marginalDensity P a y ∂unitVolume = 1 := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  calc
    _ = ∫ x, ∫ y, P.eta a x y ∂unitVolume ∂unitVolume :=
      (integral_integral_swap (integrable_eta_joint P hModel a)).symm
    _ = ∫ x, (1 : ℝ) ∂unitVolume := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      exact P.eta_normalized a x hx
    _ = 1 := by simp

/-- The identified counterfactual measure is a genuine probability measure. -/
-- @node: counterfactualMeasure_isProbabilityMeasure
lemma counterfactualMeasure_isProbabilityMeasure (P : ObsLaw) (hModel : Model P)
    (a : Bool) : IsProbabilityMeasure (counterfactualMeasure P a) := by
  constructor
  have hn : 0 ≤ᵐ[unitVolume] marginalDensity P a := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact marginalDensity_nonneg P a y hy
  rw [counterfactualMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_marginalDensity P hModel a) hn,
    marginalDensity_normalized P hModel a]
  norm_num

/-- Marginal event probabilities equal the covariate mixture of conditional event probabilities. -/
-- @node: counterfactualMeasure_apply_eq_mixture
lemma counterfactualMeasure_apply_eq_mixture (P : ObsLaw) (hModel : Model P)
    (a : Bool) (D : Set ℝ) (hD : MeasurableSet D) :
    counterfactualMeasure P a D =
      ENNReal.ofReal (∫ x, ∫ y in D, P.eta a x y ∂unitVolume ∂unitVolume) := by
  have hn : 0 ≤ᵐ[unitVolume.restrict D] marginalDensity P a := by
    filter_upwards [(ae_restrict_mem measurableSet_Icc).filter_mono ae_restrict_le] with y hy
    exact marginalDensity_nonneg P a y hy
  rw [counterfactualMeasure, withDensity_apply _ hD,
    ← ofReal_integral_eq_lintegral_ofReal
      (integrable_marginalDensity P hModel a).integrableOn hn]
  congr 1
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  exact (integral_integral_swap
    ((integrable_eta_joint P hModel a).mono_measure
      (Measure.prod_mono le_rfl Measure.restrict_le_self))).symm

end CausalSmith.Stat.DensityEffectRoughNull
