module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.CateLowerDesign
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.LowerPairHolder
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.LowerPairSampling

/-! # Compatible CATE binary witnesses

The witnesses in (C24)--(C28) use the calibrated propensity from (C21),
the existing smooth treated bump, and deterministic zero control outcomes.
This file establishes their regression regularity and exact CATE separation;
law-side membership and information bounds are proved separately.
-/
@[expose] public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate

open MeasureTheory
open scoped ENNReal

/-- The compatible lower pair samples treatment independently of a binary
treated potential outcome, conditional on uniform covariates; the control
potential outcome is identically zero, as prescribed in (C27). -/
-- @node: cateLowerPair
noncomputable def cateLowerPair (d : ℕ) (β q s h δ M : ℝ) (sign : Bool) : Law d :=
  let fullMeasure : Measure (Full d) :=
    (volume.restrict (cube d)).bind (fun x =>
      (treatmentMeasure (cateLowerPropensity d q s x)).bind (fun a =>
        (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
          (fun y1 => (x, a, (0 : ℝ), y1))))
  { full := fullMeasure
    observed := fullMeasure.map observe
    observedRecord := observe
    latentSample := fun n => Measure.pi (fun _ : Fin n => fullMeasure)
    sample := fun n => Measure.pi (fun _ : Fin n => fullMeasure.map observe)
    e := cateLowerPropensity d q s
    mu1 := witnessMean d β δ h sign
    mu0 := fun _ => 0 }

/-- The zero ambient extension satisfies every derivative and modulus bound
at any nonnegative Hölder radius. -/
-- @node: holderOnCube_zero
lemma holderOnCube_zero (d : ℕ) (β L : ℝ) (hL : 0 ≤ L) :
    holderOnCube (fun _ : Fin d → ℝ => (0 : ℝ)) β L := by
  refine ⟨fun _ => 0, ⟨contDiff_const, ?_, ?_⟩, fun _ _ => rfl⟩
  · intro j _ x
    simpa only [iteratedFDeriv_zero_fun, Pi.zero_apply, norm_zero] using hL
  · intro x y
    simp only [iteratedFDeriv_zero_fun, Pi.zero_apply, sub_self, norm_zero]
    exact mul_nonneg hL (Real.rpow_nonneg (norm_nonneg _) _)

/-- The deterministic zero control regression has the required same-radius
ambient Hölder extension in (C24)--(C25). -/
-- @node: cateLowerPair_controlHolder
lemma cateLowerPair_controlHolder (d : ℕ) (β q s h δ M L : ℝ)
    (hL : 0 ≤ L) (sign : Bool) :
    ControlHolder (cateLowerPair d β q s h δ M sign) β L := by
  exact holderOnCube_zero d β L hL

/-- A single positive amplitude threshold ensures the same-radius treated
Hölder bounds for both signs at every admissible bandwidth, as in (C25). -/
-- @node: cateLowerPair_uniform_treatedHolder
lemma cateLowerPair_uniform_treatedHolder (d : ℕ) (β L M : ℝ)
    (hβ : 0 < β) (hL : 0 < L) (hM : 0 < M) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ M / 4 ∧
      ∀ (q s h δ : ℝ), 0 ≤ δ → δ ≤ δ₀ → 0 < h → h ≤ 1 →
        ∀ sign : Bool, TreatedHolder (cateLowerPair d β q s h δ M sign) β L := by
  obtain ⟨B, hB, hball⟩ := witnessMean_uniform_holderBall_euclid d β hβ
  refine ⟨min (L / B) (M / 4), lt_min (div_pos hL hB) (by positivity),
    min_le_right _ _, ?_⟩
  intro q s h δ hδ hδsmall hh hh1 sign
  have hδB : δ * B ≤ L :=
    (le_div_iff₀ hB).mp (hδsmall.trans (min_le_left _ _))
  refine ⟨fun x => witnessMean d β δ h sign (WithLp.ofLp x),
    ?_, fun _ _ => rfl⟩
  obtain ⟨hsmooth, hderiv, hmod⟩ := hball δ h hδ hh hh1 sign
  refine ⟨hsmooth, ?_, ?_⟩
  · intro k hk x
    exact (hderiv k hk x).trans hδB
  · intro x y
    exact (hmod x y).trans
      (mul_le_mul_of_nonneg_right hδB (Real.rpow_nonneg (norm_nonneg _) _))

/-- The CATE target of either witness is its treated bump, since the selected
control regression is zero. -/
-- @node: cateLowerPair_tau
lemma cateLowerPair_tau (d : ℕ) (β q s h δ M : ℝ) (sign : Bool) :
    (cateLowerPair d β q s h δ M sign).tau = witnessMean d β δ h sign := by
  funext x
  exact sub_zero _

/-- The two compatible CATE targets have precisely the separation in (C28),
attained at the cube's lower corner. -/
-- @node: cateLowerPair_supLoss
lemma cateLowerPair_supLoss (d : ℕ) (β q s h δ M : ℝ)
    (hδ : 0 ≤ δ) (hh : 0 < h) :
    supLoss (cateLowerPair d β q s h δ M true).tau
      (cateLowerPair d β q s h δ M false).tau = ENNReal.ofReal (2 * δ * h ^ β) := by
  rw [cateLowerPair_tau, cateLowerPair_tau]
  exact witnessMean_supLoss d β δ h hδ hh

/-- Both potential outcomes of the compatible witness are bounded by the
outcome radius, including its deterministic zero control outcome. -/
-- @node: cateLowerPair_boundedOutcomes
lemma cateLowerPair_boundedOutcomes (d : ℕ) (β q s h δ M : ℝ)
    (hM : 0 ≤ M) (sign : Bool) :
    BoundedOutcomes (cateLowerPair d β q s h δ M sign) M := by
  unfold BoundedOutcomes cateLowerPair
  dsimp only
  have hset : MeasurableSet {u : Full d | |u.2.2.1| ≤ M ∧ |u.2.2.2| ≤ M} := by
    measurability
  apply ae_bind_of_ae_fibres _ _ _ hset
  apply Filter.Eventually.of_forall
  intro x
  apply ae_bind_of_ae_fibres _ _ _ hset
  apply Filter.Eventually.of_forall
  intro a
  apply (ae_map_iff (by fun_prop) hset).mpr
  filter_upwards [binaryMeasure_ae_bounded M
    (treatedPlusProbability d β δ h M sign x) hM] with y1 hy1
  exact ⟨by simpa using hM, hy1⟩

/-- The observed record and measure satisfy pathwise consistency by
construction of the compatible witness. -/
-- @node: cateLowerPair_consistency
lemma cateLowerPair_consistency (d : ℕ) (β q s h δ M : ℝ) (sign : Bool) :
    Consistency (cateLowerPair d β q s h δ M sign) := by
  exact ⟨Filter.Eventually.of_forall (fun _ => rfl), rfl⟩

/-- The conditional full-data channel of the compatible witness is measurable. -/
-- @node: cateLowerPair_fullKernel_measurable
@[fun_prop] lemma cateLowerPair_fullKernel_measurable
    (d : ℕ) (β q s h δ M : ℝ) (hq : 0 < q) (sign : Bool) :
    Measurable (fun x : Fin d → ℝ =>
      (treatmentMeasure (cateLowerPropensity d q s x)).bind (fun a =>
        (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
          (fun y1 => (x, a, (0 : ℝ), y1)))) := by
  have hchannel : Measurable (fun z : (Fin d → ℝ) × Bool =>
      (binaryMeasure M (treatedPlusProbability d β δ h M sign z.1)).map
        (fun y1 => (z.1, z.2, (0 : ℝ), y1))) := by
    simpa only [Function.comp_def] using
      (lowerPair_outcomeMap_measurable d β δ h M sign).comp
        (show Measurable (fun z : (Fin d → ℝ) × Bool => (z.1, z.2, (0 : ℝ)))
          from by fun_prop)
  have hinner (x : Fin d → ℝ) : Measurable (fun a : Bool =>
      (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
        (fun y1 => (x, a, (0 : ℝ), y1))) := by
    simpa only [Function.comp_def] using hchannel.comp
      (show Measurable (fun a : Bool => (x, a)) from by fun_prop)
  simp_rw [treatmentMeasure, twoAtom_bind _ _ _ _ _ (hinner _)]
  apply weightedChannels_measurable
  · simpa only [Function.comp_def] using hchannel.comp
      (show Measurable (fun x : Fin d → ℝ => (x, true)) from by fun_prop)
  · simpa only [Function.comp_def] using hchannel.comp
      (show Measurable (fun x : Fin d → ℝ => (x, false)) from by fun_prop)
  · exact (cateLowerPropensity_measurable d q s hq).ennreal_ofReal
  · exact (measurable_const.sub (cateLowerPropensity_measurable d q s hq)).ennreal_ofReal

/-- Normalized treatment and outcome channels preserve the uniform covariate
marginal of the compatible witness. -/
-- @node: cateLowerPair_uniformDesign
lemma cateLowerPair_uniformDesign (d : ℕ) (β q s h δ M : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hβ : 0 < β) (hδ : 0 ≤ δ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hM : 0 < M) (hsmall : δ ≤ M / 4) (sign : Bool) :
    UniformDesign (cateLowerPair d β q s h δ M sign) := by
  let ν (x : Fin d → ℝ) (a : Bool) : Measure (Full d) :=
    (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
      (fun y1 => (x, a, (0 : ℝ), y1))
  let η (x : Fin d → ℝ) :=
    (treatmentMeasure (cateLowerPropensity d q s x)).bind (ν x)
  have hν (x : Fin d → ℝ) : Measurable (ν x) := by
    simpa only [Function.comp_def] using
      (lowerPair_outcomeMap_measurable d β δ h M sign).comp
        (show Measurable (fun a : Bool => (x, a, (0 : ℝ))) from by fun_prop)
  have hη : Measurable η :=
    cateLowerPair_fullKernel_measurable d β q s h δ M hq sign
  have hkey (x : Fin d → ℝ) (hx : x ∈ cube d) :
      (η x).map Prod.fst = Measure.dirac x := by
    have hp := treatedPlusProbability_quarter_bounds d β δ h M
      hβ hδ hh hh1 hM hsmall sign x hx
    haveI : IsProbabilityMeasure (binaryMeasure M
        (treatedPlusProbability d β δ h M sign x)) :=
      binaryMeasure_isProbabilityMeasure M _ ⟨by linarith [hp.1], by linarith [hp.2]⟩
    have he := cateLowerPropensity_bounds d q s hd hq hs x hx
    haveI : IsProbabilityMeasure (treatmentMeasure (cateLowerPropensity d q s x)) := by
      apply isProbabilityMeasure_iff.mpr
      simp only [treatmentMeasure, Measure.add_apply, Measure.smul_apply,
        Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
      rw [← ENNReal.ofReal_add he.1 (by linarith : 0 ≤ 1 - cateLowerPropensity d q s x)]
      norm_num
    have hlast (a : Bool) : (ν x a).map Prod.fst = Measure.dirac x := by
      dsimp [ν]
      rw [Measure.map_map measurable_fst (by fun_prop)]
      change (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
        (fun _ => x) = Measure.dirac x
      rw [Measure.map_const, measure_univ, one_smul]
    rw [show η x = (treatmentMeasure (cateLowerPropensity d q s x)).bind (ν x) from rfl,
      map_bind_channel _ _ _ (hν x) measurable_fst]
    simp_rw [hlast]
    rw [Measure.bind_const, measure_univ, one_smul]
  change ((volume.restrict (cube d)).bind η).map Prod.fst = volume.restrict (cube d)
  rw [map_bind_channel _ _ _ hη measurable_fst]
  calc
    _ = (volume.restrict (cube d)).bind Measure.dirac := by
      apply Measure.bind_congr_right
      filter_upwards [ae_restrict_mem (by simp [cube] : MeasurableSet (cube d))] with x hx
      exact hkey x hx
    _ = volume.restrict (cube d) := Measure.bind_dirac

/-- Once its uniform marginal is established, the compatible witness inherits
the full calibrated tail envelope from (C22). -/
-- @node: cateLowerPair_globalTail_of_uniformDesign
lemma cateLowerPair_globalTail_of_uniformDesign (d : ℕ) (β γ C s h δ M : ℝ)
    (hd : 1 ≤ d) (hγ : 1 < γ) (hC : 0 ≤ C) (hs : 0 < s)
    (hcal : C * s ^ tailExponent γ = 1) (sign : Bool)
    (hu : UniformDesign (cateLowerPair d β (tailExponent γ) s h δ M sign)) :
    GlobalTail (cateLowerPair d β (tailExponent γ) s h δ M sign) C γ := by
  intro t ht
  rw [hu]
  exact cateLowerPropensity_global_tail d (tailExponent γ) C s hd
    (by unfold tailExponent; linarith) hC hs hcal t ht

/-- Uniform design converts the pointwise compatible propensity floor to
the almost-sure control overlap required of the constructed law. -/
-- @node: cateLowerPair_controlOverlap_of_uniformDesign
lemma cateLowerPair_controlOverlap_of_uniformDesign (d : ℕ) (β q s h δ M κ : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hs : 0 ≤ s) (hcompat : s ≤ 1 - κ)
    (sign : Bool) (hu : UniformDesign (cateLowerPair d β q s h δ M sign)) :
    ControlOverlap (cateLowerPair d β q s h δ M sign) κ := by
  unfold ControlOverlap
  rw [hu]
  filter_upwards [ae_restrict_mem (by simp [cube] : MeasurableSet (cube d))] with x hx
  exact cateLowerPropensity_control_overlap d q s κ hd hq hs hcompat x hx

end CausalSmith.Stat.GlobalTailDesignRobustCate
