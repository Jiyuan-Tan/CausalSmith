module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.LowerPairMarginals

/-! # Regularity of the bounded binary witness

The binary support and normalization give integrability without adding model
assumptions. The cube-wise nuisance ranges supply the remaining range checks
in the law semantics, as in equations (13)--(16) of the membership roadmap.
-/
public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate
open MeasureTheory

/-- Both recorded regression versions take values in the outcome interval. -/
-- @node: lowerPair_regression_ranges
lemma lowerPair_regression_ranges (d : ℕ) (β q h δ M : ℝ)
    (hβ : 0 < β) (hδ : 0 ≤ δ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hM : 0 < M) (hsmall : δ ≤ M / 4) (sign : Bool) :
    (∀ x ∈ cube d, (lowerPair d β q h δ M sign).mu1 x ∈ Set.Icc (-M) M) ∧
    (∀ x ∈ cube d, (lowerPair d β q h δ M sign).mu0 x ∈ Set.Icc (-M) M) := by
  constructor
  · intro x hx
    change witnessMean d β δ h sign x ∈ Set.Icc (-M) M
    have hb := witnessMean_abs_le_delta_on_cube d β δ h hβ hδ hh hh1 sign x hx
    have hr := abs_le.mp hb
    constructor <;> linarith
  · intro x hx
    change (0 : ℝ) ∈ Set.Icc (-M) M
    constructor <;> linarith

variable (d : ℕ) (β q h δ M : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hβ : 0 < β) (hδ : 0 ≤ δ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hM : 0 < M) (hsmall : δ ≤ M / 4)
    (sign : Bool)

include hd hq hβ hδ hh hh1 hM hsmall

/-- The treated potential outcome is integrable under the actual normalized law. -/
-- @node: lowerPair_integrable_treated
lemma lowerPair_integrable_treated :
    Integrable (fun u : Full d => u.2.2.2) (lowerPair d β q h δ M sign).full := by
  have := lowerPair_isProbabilityMeasure d β q h δ M hd hq hβ hδ hh hh1 hM hsmall sign
  apply Integrable.of_bound (by fun_prop) M
  filter_upwards [lowerPair_boundedOutcomes d β q h δ M hM.le sign] with u hu
  simpa only [Real.norm_eq_abs] using hu.2

/-- The common control potential outcome is integrable under either signed law. -/
-- @node: lowerPair_integrable_control
lemma lowerPair_integrable_control :
    Integrable (fun u : Full d => u.2.2.1) (lowerPair d β q h δ M sign).full := by
  have := lowerPair_isProbabilityMeasure d β q h δ M hd hq hβ hδ hh hh1 hM hsmall sign
  apply Integrable.of_bound (by fun_prop) M
  filter_upwards [lowerPair_boundedOutcomes d β q h δ M hM.le sign] with u hu
  simpa only [Real.norm_eq_abs] using hu.1

/-- The treatment indicator is integrable, so its conditional expectation is
well posed along with both potential outcome conditional means. -/
-- @node: lowerPair_integrable_treatment
lemma lowerPair_integrable_treatment :
    Integrable (fun u : Full d => if u.2.1 then (1 : ℝ) else 0)
      (lowerPair d β q h δ M sign).full := by
  have := lowerPair_isProbabilityMeasure d β q h δ M hd hq hβ hδ hh hh1 hM hsmall sign
  have hm : Measurable (fun u : Full d => if u.2.1 then (1 : ℝ) else 0) := by
    apply Measurable.ite _ measurable_const measurable_const
    exact (measurableSet_singleton true).preimage (by fun_prop)
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun u => by cases u.2.1 <;> norm_num)

end CausalSmith.Stat.GlobalTailDesignRobustCate
