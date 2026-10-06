module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.CateLowerPair

/-! # Sampling and regularity of compatible CATE witnesses

The normalized uniform marginal proves that the zero-control witness in (C27)
is a probability law. Its product samples have the stipulated observed image,
and bounded support supplies integrability without additional assumptions.
The deterministic control outcome has conditional mean zero.
-/
public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate
open MeasureTheory

/-- The compatible witness has unit total mass, as does its uniform marginal. -/
-- @node: cateLowerPair_isProbabilityMeasure
lemma cateLowerPair_isProbabilityMeasure (d : ℕ) (β q s h δ M : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hβ : 0 < β) (hδ : 0 ≤ δ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hM : 0 < M) (hsmall : δ ≤ M / 4) (sign : Bool) :
    IsProbabilityMeasure (cateLowerPair d β q s h δ M sign).full := by
  apply isProbabilityMeasure_iff.mpr
  have hu := cateLowerPair_uniformDesign d β q s h δ M
    hd hq hs hs1 hβ hδ hh hh1 hM hsmall sign
  have heq := congrArg (fun μ : Measure (Fin d → ℝ) => μ Set.univ) hu
  simpa [Law.xLaw, Measure.map_apply measurable_fst MeasurableSet.univ,
    cube, Real.volume_Icc_pi] using heq

/-- The compatible witness uses independent replicas and the consistent
observed image of its latent product sample, as prescribed after (C27). -/
-- @node: cateLowerPair_iidSampling
lemma cateLowerPair_iidSampling (d : ℕ) (β q s h δ M : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hβ : 0 < β) (hδ : 0 ≤ δ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hM : 0 < M) (hsmall : δ ≤ M / 4) (sign : Bool) :
    IidSampling (cateLowerPair d β q s h δ M sign) := by
  have := cateLowerPair_isProbabilityMeasure d β q s h δ M
    hd hq hs hs1 hβ hδ hh hh1 hM hsmall sign
  have ho : Measurable (observe (d := d)) := by
    unfold observe
    apply Measurable.prodMk (by fun_prop)
    apply Measurable.prodMk (by fun_prop)
    apply Measurable.ite _ (by fun_prop) (by fun_prop)
    exact (measurableSet_singleton true).preimage (by fun_prop)
  refine ⟨inferInstance, fun _ _ => rfl, ?_⟩
  intro n hn
  change Measure.pi (fun _ : Fin n =>
    ((cateLowerPair d β q s h δ M sign).full).map observe) =
    (Measure.pi (fun _ : Fin n => (cateLowerPair d β q s h δ M sign).full)).map
      (fun units i => observe (units i))
  have : IsProbabilityMeasure (((cateLowerPair d β q s h δ M sign).full).map observe) :=
    Measure.isProbabilityMeasure_map ho.aemeasurable
  exact (Measure.pi_map_pi (fun _ => ho.aemeasurable)).symm

/-- The recorded outcome means take values in the model's outcome interval. -/
-- @node: cateLowerPair_regression_ranges
lemma cateLowerPair_regression_ranges (d : ℕ) (β q s h δ M : ℝ)
    (hβ : 0 < β) (hδ : 0 ≤ δ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hM : 0 < M) (hsmall : δ ≤ M / 4) (sign : Bool) :
    (∀ x ∈ cube d, (cateLowerPair d β q s h δ M sign).mu1 x ∈ Set.Icc (-M) M) ∧
    (∀ x ∈ cube d, (cateLowerPair d β q s h δ M sign).mu0 x ∈ Set.Icc (-M) M) := by
  constructor
  · intro x hx
    change witnessMean d β δ h sign x ∈ Set.Icc (-M) M
    have hb := witnessMean_abs_le_delta_on_cube d β δ h hβ hδ hh hh1 sign x hx
    have hr := abs_le.mp hb
    constructor <;> linarith
  · intro x hx
    change (0 : ℝ) ∈ Set.Icc (-M) M
    constructor <;> linarith

variable (d : ℕ) (β q s h δ M : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hβ : 0 < β) (hδ : 0 ≤ δ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hM : 0 < M) (hsmall : δ ≤ M / 4) (sign : Bool)
include hd hq hs hs1 hβ hδ hh hh1 hM hsmall

/-- Bounded treated outcomes are integrable under the normalized witness. -/
-- @node: cateLowerPair_integrable_treated
lemma cateLowerPair_integrable_treated :
    Integrable (fun u : Full d => u.2.2.2) (cateLowerPair d β q s h δ M sign).full := by
  have := cateLowerPair_isProbabilityMeasure d β q s h δ M
    hd hq hs hs1 hβ hδ hh hh1 hM hsmall sign
  apply Integrable.of_bound (by fun_prop) M
  filter_upwards [cateLowerPair_boundedOutcomes d β q s h δ M hM.le sign] with u hu
  simpa only [Real.norm_eq_abs] using hu.2

/-- Bounded control outcomes are integrable under the normalized witness. -/
-- @node: cateLowerPair_integrable_control
lemma cateLowerPair_integrable_control :
    Integrable (fun u : Full d => u.2.2.1) (cateLowerPair d β q s h δ M sign).full := by
  have := cateLowerPair_isProbabilityMeasure d β q s h δ M
    hd hq hs hs1 hβ hδ hh hh1 hM hsmall sign
  apply Integrable.of_bound (by fun_prop) M
  filter_upwards [cateLowerPair_boundedOutcomes d β q s h δ M hM.le sign] with u hu
  simpa only [Real.norm_eq_abs] using hu.1

/-- The bounded treatment indicator has a well-posed conditional expectation. -/
-- @node: cateLowerPair_integrable_treatment
lemma cateLowerPair_integrable_treatment :
    Integrable (fun u : Full d => if u.2.1 then (1 : ℝ) else 0)
      (cateLowerPair d β q s h δ M sign).full := by
  have := cateLowerPair_isProbabilityMeasure d β q s h δ M
    hd hq hs hs1 hβ hδ hh hh1 hM hsmall sign
  have hm : Measurable (fun u : Full d => if u.2.1 then (1 : ℝ) else 0) := by
    apply Measurable.ite _ measurable_const measurable_const
    exact (measurableSet_singleton true).preimage (by fun_prop)
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun u => by cases u.2.1 <;> norm_num)

omit hd hq hs hs1 hβ hδ hh hh1 hM hsmall in
/-- Every latent draw records a deterministic zero control potential outcome. -/
-- @node: cateLowerPair_control_ae_zero
lemma cateLowerPair_control_ae_zero :
    (fun u : Full d => u.2.2.1) =ᵐ[(cateLowerPair d β q s h δ M sign).full]
      fun _ => (0 : ℝ) := by
  change ∀ᵐ u ∂(cateLowerPair d β q s h δ M sign).full, u.2.2.1 = (0 : ℝ)
  unfold cateLowerPair
  dsimp only
  have hset : MeasurableSet {u : Full d | u.2.2.1 = (0 : ℝ)} := by
    measurability
  apply ae_bind_of_ae_fibres _ _ _ hset
  apply Filter.Eventually.of_forall
  intro x
  apply ae_bind_of_ae_fibres _ _ _ hset
  apply Filter.Eventually.of_forall
  intro a
  apply (ae_map_iff (by fun_prop) hset).mpr
  exact Filter.Eventually.of_forall (fun _ => rfl)

omit hd hq hs hs1 hβ hδ hh hh1 hM hsmall in
/-- The zero control regression is the conditional mean of the actual
control potential outcome in (C24)--(C27). -/
-- @node: cateLowerPair_condExp_control
lemma cateLowerPair_condExp_control :
    (cateLowerPair d β q s h δ M sign).full[(fun u : Full d => u.2.2.1) |
      MeasurableSpace.comap (fun u : Full d => u.1) inferInstance] =ᵐ[
        (cateLowerPair d β q s h δ M sign).full] fun _ => (0 : ℝ) := by
  have heq := condExp_congr_ae (m := MeasurableSpace.comap
    (fun u : Full d => u.1) inferInstance)
    (cateLowerPair_control_ae_zero d β q s h δ M sign)
  change _ =ᵐ[_] (cateLowerPair d β q s h δ M sign).full[
    (0 : Full d → ℝ) | MeasurableSpace.comap (fun u : Full d => u.1) inferInstance] at heq
  rw [condExp_zero] at heq
  exact heq

end CausalSmith.Stat.GlobalTailDesignRobustCate
