module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.CateLowerSampling
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.LowerPairInformation

/-! # Information bounds for compatible zero-control CATE witnesses

Roadmap (C29)--(C31): the deterministic shared control channel contributes
zero divergence, and the scaled treatment channel retains the localized KL rate.
-/
public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

/-- For a shared Bernoulli treatment draw, the common control outcome contributes
zero KL; adding the fixed covariate coordinate is a measurable observation. -/
-- @node: zeroControlObservedFiber_klDiv_le
lemma zeroControlObservedFiber_klDiv_le (d : ℕ) (M e p r : ℝ)
    (he : e ∈ Set.Icc (0 : ℝ) 1) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hr : r ∈ Set.Icc (0 : ℝ) 1)
    (hac : binaryMeasure M p ≪ binaryMeasure M r) (x : Fin d → ℝ) :
    klDiv
      (ENNReal.ofReal e • (binaryMeasure M p).map (fun y => (x, true, y)) +
        ENNReal.ofReal (1 - e) • (Measure.dirac (0 : ℝ)).map (fun y => (x, false, y)))
      (ENNReal.ofReal e • (binaryMeasure M r).map (fun y => (x, true, y)) +
        ENNReal.ofReal (1 - e) • (Measure.dirac (0 : ℝ)).map (fun y => (x, false, y))) ≤
      ENNReal.ofReal e * klDiv (binaryMeasure M p) (binaryMeasure M r) := by
  let κ : Kernel Bool ℝ := ⟨fun a => if a then binaryMeasure M p else Measure.dirac 0,
    measurable_of_countable _⟩
  let η : Kernel Bool ℝ := ⟨fun a => if a then binaryMeasure M r else Measure.dirac 0,
    measurable_of_countable _⟩
  have : IsMarkovKernel κ := ⟨fun a => by
    cases a
    · exact Measure.dirac.isProbabilityMeasure
    · exact binaryMeasure_isProbabilityMeasure M p hp⟩
  have : IsMarkovKernel η := ⟨fun a => by
    cases a
    · exact Measure.dirac.isProbabilityMeasure
    · exact binaryMeasure_isProbabilityMeasure M r hr⟩
  have := treatmentMeasure_isProbabilityMeasure e he
  have hchain := Causalean.Mathlib.InformationTheory.Measure.klDiv_compProd_right_of_forall_ac
    (μ := treatmentMeasure e) (κ := κ) (η := η)
    (Filter.Eventually.of_forall (fun a => by
      cases a
      · exact Measure.AbsolutelyContinuous.rfl
      · exact hac))
  have hvalue : (∫⁻ a, klDiv (κ a) (η a) ∂treatmentMeasure e) =
      ENNReal.ofReal e * klDiv (binaryMeasure M p) (binaryMeasure M r) := by
    simp [treatmentMeasure, κ, η, lintegral_add_measure, lintegral_smul_measure]
  have hmap (k : Kernel Bool ℝ) [IsSFiniteKernel k] :
      ((treatmentMeasure e) ⊗ₘ k).map (fun z => (x, z.1, z.2)) =
        ENNReal.ofReal e • (k true).map (fun y => (x, true, y)) +
        ENNReal.ofReal (1 - e) • (k false).map (fun y => (x, false, y)) := by
    have hdir (a : Bool) : Measure.dirac a ⊗ₘ k = (k a).map (Prod.mk a) := by
      ext s hs
      rw [Measure.dirac_compProd_apply hs, Measure.map_apply (by fun_prop) hs]
    rw [treatmentMeasure, Measure.compProd_add_left, Measure.compProd_smul_left,
      Measure.compProd_smul_left, Measure.map_add _ _ (by fun_prop),
      Measure.map_smul, Measure.map_smul, hdir, hdir,
      Measure.map_map (by fun_prop) (by fun_prop),
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have hdp := InformationTheory.klDiv_map_le
    ((treatmentMeasure e) ⊗ₘ κ) ((treatmentMeasure e) ⊗ₘ η)
    (show Measurable (fun z : Bool × ℝ => (x, z.1, z.2)) from by fun_prop)
  rw [hmap κ, hmap η, hchain, hvalue] at hdp
  exact hdp

/-- Observation keeps the treated draw on treatment and records zero otherwise. -/
-- @node: cateLowerPair_observedFiber
lemma cateLowerPair_observedFiber (d : ℕ) (β q s h δ M : ℝ)
    (hβ : 0 < β) (hδ : 0 ≤ δ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hM : 0 < M) (hsmall : δ ≤ M / 4)
    (sign : Bool) (x : Fin d → ℝ) (hx : x ∈ cube d) :
    ((treatmentMeasure (cateLowerPropensity d q s x)).bind (fun a =>
      (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
        (fun y1 => (x, a, (0 : ℝ), y1)))).map observe =
      ENNReal.ofReal (cateLowerPropensity d q s x) •
        (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
          (fun y => (x, true, y)) +
      ENNReal.ofReal (1 - cateLowerPropensity d q s x) •
        (Measure.dirac (0 : ℝ)).map (fun y => (x, false, y)) := by
  let ν (a : Bool) : Measure (Full d) :=
    (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
      (fun y1 => (x, a, (0 : ℝ), y1))
  have hν : Measurable ν := measurable_of_countable _
  have ho : Measurable (observe (d := d)) := by
    unfold observe
    apply Measurable.prodMk (by fun_prop)
    apply Measurable.prodMk (by fun_prop)
    apply Measurable.ite _ (by fun_prop) (by fun_prop)
    exact (measurableSet_singleton true).preimage (by fun_prop)
  have hp := treatedPlusProbability_quarter_bounds d β δ h M
    hβ hδ hh hh1 hM hsmall sign x hx
  have : IsProbabilityMeasure (binaryMeasure M
      (treatedPlusProbability d β δ h M sign x)) :=
    binaryMeasure_isProbabilityMeasure M _ ⟨by linarith [hp.1], by linarith [hp.2]⟩
  have htrue : (ν true).map observe =
      (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
        (fun y => (x, true, y)) := by
    dsimp [ν]
    rw [Measure.map_map ho (by fun_prop)]
    rfl
  have hfalse : (ν false).map observe =
      (Measure.dirac (0 : ℝ)).map (fun y => (x, false, y)) := by
    dsimp [ν]
    rw [Measure.map_map ho (by fun_prop)]
    change (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
      (fun _ => (x, false, (0 : ℝ))) = _
    rw [Measure.map_const, measure_univ, one_smul, Measure.map_dirac' (by fun_prop)]
  change ((treatmentMeasure (cateLowerPropensity d q s x)).bind ν).map observe = _
  rw [treatmentMeasure, twoAtom_bind _ _ _ _ _ hν,
    Measure.map_add _ _ ho, Measure.map_smul, Measure.map_smul, htrue, hfalse]

/-- The actual observed law mixes the treated binary and deterministic control channels. -/
-- @node: cateLowerPair_obs_eq_bind_binary
lemma cateLowerPair_obs_eq_bind_binary (d : ℕ) (β q s h δ M : ℝ)
    (hq : 0 < q) (hβ : 0 < β) (hδ : 0 ≤ δ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hM : 0 < M) (hsmall : δ ≤ M / 4) (sign : Bool) :
    (cateLowerPair d β q s h δ M sign).obs =
      (volume.restrict (cube d)).bind (fun x =>
        ENNReal.ofReal (cateLowerPropensity d q s x) •
          (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
            (fun y => (x, true, y)) +
        ENNReal.ofReal (1 - cateLowerPropensity d q s x) •
          (Measure.dirac (0 : ℝ)).map (fun y => (x, false, y))) := by
  have ho : Measurable (observe (d := d)) := by
    unfold observe
    apply Measurable.prodMk (by fun_prop)
    apply Measurable.prodMk (by fun_prop)
    apply Measurable.ite _ (by fun_prop) (by fun_prop)
    exact (measurableSet_singleton true).preimage (by fun_prop)
  change ((volume.restrict (cube d)).bind (fun x =>
    (treatmentMeasure (cateLowerPropensity d q s x)).bind (fun a =>
      (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
        (fun y1 => (x, a, (0 : ℝ), y1))))).map observe = _
  rw [map_bind_channel _ _ _
    (cateLowerPair_fullKernel_measurable d β q s h δ M hq sign) ho]
  apply Measure.bind_congr_right
  filter_upwards [ae_restrict_mem (by simp [cube] : MeasurableSet (cube d))] with x hx
  exact cateLowerPair_observedFiber d β q s h δ M hβ hδ hh hh1 hM hsmall sign x hx

/-- The origin convention changes the scaled propensity only on a null set. -/
-- @node: cateLowerPropensity_ae_le_baseline
lemma cateLowerPropensity_ae_le_baseline (d : ℕ) (q s : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (_hs : 0 ≤ s) (hs1 : s ≤ 1) :
    ∀ᵐ x ∂volume.restrict (cube d),
      cateLowerPropensity d q s x ≤ baselinePropensity d q x := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hne : ∀ᵐ x ∂(volume : Measure (Fin d → ℝ)), x ≠ 0 := by
    simp [ae_iff]
  filter_upwards [hne.filter_mono (ae_mono Measure.restrict_le_self),
    ae_restrict_mem (by simp [cube] : MeasurableSet (cube d))] with x hx0 hx
  rw [cateLowerPropensity, if_neg hx0]
  have hb := baselinePropensity_unit_interval d q hd hq x hx
  exact (mul_le_mul_of_nonneg_right hs1 hb.1).trans_eq (one_mul _)

/-- Scaling the propensity down preserves the existing localized information bound. -/
-- @node: cateLowerPair_integrated_treated_klDiv_le
lemma cateLowerPair_integrated_treated_klDiv_le (d : ℕ) (β γ s h δ M : ℝ)
    (hd : 1 ≤ d) (hγ : 1 < γ) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hβ : 0 < β) (hδ : 0 ≤ δ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hM : 0 < M) (hsmall : δ ≤ M / 4) :
    (∫⁻ x in cube d, ENNReal.ofReal (cateLowerPropensity d (tailExponent γ) s x) *
      klDiv (binaryMeasure M (treatedPlusProbability d β δ h M true x))
        (binaryMeasure M (treatedPlusProbability d β δ h M false x))) ≤
      ENNReal.ofReal (16 * δ ^ 2 / M ^ 2 * h ^ (2 * β + effectiveDimension d γ)) := by
  apply le_trans _ (treatedBinary_integrated_klDiv_le d β γ δ h M
    hd hβ hγ hδ hh hh1 hM hsmall)
  apply lintegral_mono_ae
  filter_upwards [cateLowerPropensity_ae_le_baseline d (tailExponent γ) s hd
    (by unfold tailExponent; linarith) hs hs1] with x hx
  exact mul_le_mul (ENNReal.ofReal_le_ofReal hx) le_rfl (by positivity) (by positivity)

/-- The shared-base bind chain rule transfers the localized conditional
information bound to the actual one-observation experiment. -/
-- @node: cateLowerPair_obs_klDiv_le
lemma cateLowerPair_obs_klDiv_le (d : ℕ) (β γ s h δ M : ℝ)
    (hd : 1 ≤ d) (hγ : 1 < γ) (hs : 0 ≤ s) (hs1 : s ≤ 1) (hβ : 0 < β) (hδ : 0 ≤ δ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hM : 0 < M) (hsmall : δ ≤ M / 4) :
    klDiv (cateLowerPair d β (tailExponent γ) s h δ M true).obs
      (cateLowerPair d β (tailExponent γ) s h δ M false).obs ≤
      ENNReal.ofReal (16 * δ ^ 2 / M ^ 2 * h ^ (2 * β + effectiveDimension d γ)) := by
  classical
  have hq : 0 < tailExponent γ := by unfold tailExponent; linarith
  let F (sign : Bool) (x : Fin d → ℝ) : Measure (Obs d) :=
    ENNReal.ofReal (cateLowerPropensity d (tailExponent γ) s x) •
      (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
        (fun y => (x, true, y)) +
    ENNReal.ofReal (1 - cateLowerPropensity d (tailExponent γ) s x) •
      (Measure.dirac (0 : ℝ)).map (fun y => (x, false, y))
  have hF (sign : Bool) : Measurable (F sign) := by
    apply weightedChannels_measurable
    · have ht (x : Fin d → ℝ) : Measurable (fun y : ℝ => (x, true, y)) := by fun_prop
      simp_rw [binaryMeasure, Measure.map_add _ _ (ht _), Measure.map_smul,
        Measure.map_dirac' (ht _)]
      fun_prop
    · have ht (x : Fin d → ℝ) : Measurable (fun y : ℝ => (x, false, y)) := by fun_prop
      simp_rw [Measure.map_dirac' (ht _)]
      fun_prop
    · exact (cateLowerPropensity_measurable d (tailExponent γ) s hq).ennreal_ofReal
    · exact (measurable_const.sub
        (cateLowerPropensity_measurable d (tailExponent γ) s hq)).ennreal_ofReal
  have hc : MeasurableSet (cube d) := by simp [cube]
  let K (sign : Bool) : Kernel (Fin d → ℝ) (Obs d) :=
    ⟨fun x => if x ∈ cube d then F sign x else 0, (hF sign).ite hc measurable_const⟩
  have hprob (sign : Bool) (x : Fin d → ℝ) (hx : x ∈ cube d) :
      IsProbabilityMeasure (F sign x) := by
    have hp := treatedPlusProbability_quarter_bounds d β δ h M
      hβ hδ hh hh1 hM hsmall sign x hx
    have := binaryMeasure_isProbabilityMeasure M _
      (show treatedPlusProbability d β δ h M sign x ∈ Set.Icc (0 : ℝ) 1 from
        ⟨by linarith [hp.1], by linarith [hp.2]⟩)
    have he := show cateLowerPropensity d (tailExponent γ) s x ∈ Set.Icc (0 : ℝ) 1 from
      ⟨(cateLowerPropensity_bounds d (tailExponent γ) s hd hq hs x hx).1,
        (cateLowerPropensity_bounds d (tailExponent γ) s hd hq hs x hx).2.trans hs1⟩
    apply isProbabilityMeasure_iff.mpr
    dsimp [F]
    simp only [Measure.map_apply (show Measurable (fun y : ℝ => (x, true, y)) from by fun_prop)
        MeasurableSet.univ,
      Measure.map_apply (show Measurable (fun y : ℝ => (x, false, y)) from by fun_prop)
        MeasurableSet.univ, Set.preimage_univ, measure_univ, mul_one]
    rw [← ENNReal.ofReal_add he.1 (sub_nonneg.mpr he.2)]
    simp
  have (sign : Bool) : IsFiniteKernel (K sign) := by
    refine ⟨⟨1, by simp, ?_⟩⟩
    intro x
    by_cases hx : x ∈ cube d
    · have := hprob sign x hx
      simp [K, hx, measure_univ]
    · simp [K, hx]
  have heq (sign : Bool) : (cateLowerPair d β (tailExponent γ) s h δ M sign).obs =
      (volume.restrict (cube d)).bind (K sign) := by
    rw [cateLowerPair_obs_eq_bind_binary d β (tailExponent γ) s h δ M
      hq hβ hδ hh hh1 hM hsmall sign]
    apply Measure.bind_congr_right
    filter_upwards [ae_restrict_mem hc] with x hx
    simp [K, hx, F]
  have hsupp (sign : Bool) : ∀ᵐ x ∂volume.restrict (cube d),
      (K sign x) {z | z.1 = x}ᶜ = 0 := by
    filter_upwards [ae_restrict_mem hc] with x hx
    simp only [K, Kernel.coe_mk, if_pos hx, F, Measure.add_apply, Measure.smul_apply]
    rw [Measure.map_apply (by fun_prop) (by measurability),
      Measure.map_apply (by fun_prop) (by measurability)]
    simp
  have hac : ∀ᵐ x ∂volume.restrict (cube d), K true x ≪ K false x := by
    filter_upwards [ae_restrict_mem hc] with x hx
    simp only [K, Kernel.coe_mk, if_pos hx, F]
    exact ((treatedBinary_absolutelyContinuous d β δ h M
      hβ hδ hh hh1 hM hsmall x hx).map (by fun_prop)).smul _ |>.add
        (Measure.AbsolutelyContinuous.rfl.smul _)
  have : IsProbabilityMeasure (volume.restrict (cube d)) := by
    apply isProbabilityMeasure_iff.mpr
    simp [cube, Real.volume_Icc_pi]
  rw [heq true, heq false,
    Causalean.Mathlib.InformationTheory.Measure.klDiv_bind_eq_of_base_recording
      _ _ _ Prod.fst (by fun_prop) (by measurability) (hsupp true) (hsupp false) hac]
  apply le_trans _ (cateLowerPair_integrated_treated_klDiv_le d β γ s h δ M
    hd hγ hs hs1 hβ hδ hh hh1 hM hsmall)
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem hc] with x hx
  simp only [K, Kernel.coe_mk, if_pos hx, F]
  have hp := treatedPlusProbability_quarter_bounds d β δ h M
    hβ hδ hh hh1 hM hsmall true x hx
  have hr := treatedPlusProbability_quarter_bounds d β δ h M
    hβ hδ hh hh1 hM hsmall false x hx
  exact zeroControlObservedFiber_klDiv_le d M (cateLowerPropensity d (tailExponent γ) s x) _ _
    (show cateLowerPropensity d (tailExponent γ) s x ∈ Set.Icc (0 : ℝ) 1 from
      ⟨(cateLowerPropensity_bounds d (tailExponent γ) s hd hq hs x hx).1,
        (cateLowerPropensity_bounds d (tailExponent γ) s hd hq hs x hx).2.trans hs1⟩)
    ⟨by linarith [hp.1], by linarith [hp.2]⟩
    ⟨by linarith [hr.1], by linarith [hr.2]⟩
    (treatedBinary_absolutelyContinuous d β δ h M hβ hδ hh hh1 hM hsmall x hx) x

/-- Observation preserves the normalized probability law of either witness. -/
-- @node: cateLowerPair_obs_isProbabilityMeasure
lemma cateLowerPair_obs_isProbabilityMeasure (d : ℕ) (β q s h δ M : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hs : 0 ≤ s) (hs1 : s ≤ 1) (hβ : 0 < β) (hδ : 0 ≤ δ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hM : 0 < M) (hsmall : δ ≤ M / 4)
    (sign : Bool) : IsProbabilityMeasure (cateLowerPair d β q s h δ M sign).obs := by
  have := cateLowerPair_isProbabilityMeasure d β q s h δ M
    hd hq hs hs1 hβ hδ hh hh1 hM hsmall sign
  rw [(cateLowerPair_consistency d β q s h δ M sign).2]
  apply Measure.isProbabilityMeasure_map
  change AEMeasurable (observe (d := d)) _
  apply Measurable.aemeasurable
  unfold observe
  apply Measurable.prodMk (by fun_prop)
  apply Measurable.prodMk (by fun_prop)
  apply Measurable.ite _ (by fun_prop) (by fun_prop)
  exact (measurableSet_singleton true).preimage (by fun_prop)

/-- Independent replication multiplies the localized information bound by the
sample size. Finiteness supplies absolute continuity and log-ratio integrability
rather than adding either as an assumption. -/
-- @node: cateLowerPair_product_klDiv_le
lemma cateLowerPair_product_klDiv_le (d n : ℕ) (β γ s h δ M : ℝ)
    (hd : 1 ≤ d) (hγ : 1 < γ) (hs : 0 ≤ s) (hs1 : s ≤ 1) (hβ : 0 < β) (hδ : 0 ≤ δ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hM : 0 < M) (hsmall : δ ≤ M / 4) :
    klDiv (Measure.pi (fun _ : Fin n => (cateLowerPair d β (tailExponent γ) s h δ M true).obs))
      (Measure.pi (fun _ : Fin n => (cateLowerPair d β (tailExponent γ) s h δ M false).obs)) ≤
      ENNReal.ofReal (16 * δ ^ 2 / M ^ 2 * (n : ℝ) *
        h ^ (2 * β + effectiveDimension d γ)) := by
  have hq : 0 < tailExponent γ := by unfold tailExponent; linarith
  have := cateLowerPair_obs_isProbabilityMeasure d β (tailExponent γ) s h δ M
    hd hq hs hs1 hβ hδ hh hh1 hM hsmall true
  have := cateLowerPair_obs_isProbabilityMeasure d β (tailExponent γ) s h δ M
    hd hq hs hs1 hβ hδ hh hh1 hM hsmall false
  have hb := cateLowerPair_obs_klDiv_le d β γ s h δ M hd hγ hs hs1 hβ hδ hh hh1 hM hsmall
  have hf := klDiv_ne_top_iff.mp (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb)
  have ht := Causalean.Mathlib.InformationTheory.productKL_tensorization n
    (cateLowerPair d β (tailExponent γ) s h δ M true).obs
    (cateLowerPair d β (tailExponent γ) s h δ M false).obs hf.1 hf.2
  apply (ENNReal.toReal_le_toReal ht.1 ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (by positivity)]
  calc
    _ ≤ (n : ℝ) * (klDiv (cateLowerPair d β (tailExponent γ) s h δ M true).obs
        (cateLowerPair d β (tailExponent γ) s h δ M false).obs).toReal := ht.2.2
    _ ≤ (n : ℝ) * (16 * δ ^ 2 / M ^ 2 * h ^ (2 * β + effectiveDimension d γ)) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
      have hre := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
      rw [ENNReal.toReal_ofReal (show 0 ≤ 16 * δ ^ 2 / M ^ 2 *
        h ^ (2 * β + effectiveDimension d γ) from by positivity)] at hre
      exact hre
    _ = _ := by ring

/-- The prescribed small-amplitude condition gives a KL constant uniform over
all admitted amplitudes, as required by the membership theorem's quantifiers. -/
-- @node: cateLowerPair_product_klDiv_le_unit
lemma cateLowerPair_product_klDiv_le_unit (d n : ℕ) (β γ s h δ M : ℝ)
    (hd : 1 ≤ d) (hγ : 1 < γ) (hs : 0 ≤ s) (hs1 : s ≤ 1) (hβ : 0 < β) (hδ : 0 ≤ δ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hM : 0 < M) (hsmall : δ ≤ M / 4) :
    klDiv (Measure.pi (fun _ : Fin n => (cateLowerPair d β (tailExponent γ) s h δ M true).obs))
      (Measure.pi (fun _ : Fin n => (cateLowerPair d β (tailExponent γ) s h δ M false).obs)) ≤
      ENNReal.ofReal ((n : ℝ) * h ^ (2 * β + effectiveDimension d γ)) := by
  apply (cateLowerPair_product_klDiv_le d n β γ s h δ M
    hd hγ hs hs1 hβ hδ hh hh1 hM hsmall).trans
  apply ENNReal.ofReal_le_ofReal
  have hcoef : 16 * δ ^ 2 / M ^ 2 ≤ 1 := by
    apply (div_le_iff₀ (sq_pos_of_pos hM)).mpr
    have hscaled : 4 * δ ≤ M := by linarith
    nlinarith [mul_nonneg (by linarith : 0 ≤ M - 4 * δ)
      (by positivity : 0 ≤ M + 4 * δ)]
  calc
    _ ≤ 1 * (n : ℝ) * h ^ (2 * β + effectiveDimension d γ) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg n)) (by positivity)
    _ = _ := by ring

end CausalSmith.Stat.GlobalTailDesignRobustCate
