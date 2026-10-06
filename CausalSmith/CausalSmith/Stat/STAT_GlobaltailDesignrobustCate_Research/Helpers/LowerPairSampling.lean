module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.LowerPairBounds

/-! # Sampling and marginal checks for the binary lower pair

The finite conditional channels are measurable, and normalizing their weights
preserves the uniform covariate marginal of the nested witness construction.
-/
public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate
open MeasureTheory
open scoped ENNReal

/-- Binding a two-atom measure evaluates the channel at its two support points. -/
-- @node: twoAtom_bind
lemma twoAtom_bind {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    (a b : α) (p q : ℝ≥0∞) (κ : α → Measure Ω) (hκ : Measurable κ) :
    (p • Measure.dirac a + q • Measure.dirac b).bind κ = p • κ a + q • κ b := by
  ext s hs
  rw [Measure.bind_apply hs hκ.aemeasurable]
  rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]
  have hm : Measurable (fun x => κ x s) := (Measure.measurable_coe hs).comp hκ
  rw [lintegral_dirac' a hm, lintegral_dirac' b hm]
  rfl

/-- A varying two-atom law remains measurable when its weights and atoms are measurable. -/
-- @node: twoAtom_measurable
@[fun_prop] lemma twoAtom_measurable {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    (a b : α → Ω) (p q : α → ℝ≥0∞) (ha : Measurable a) (hb : Measurable b)
    (hp : Measurable p) (hq : Measurable q) :
    Measurable (fun x => p x • Measure.dirac (a x) + q x • Measure.dirac (b x)) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  exact (hp.mul ((Measure.measurable_coe hs).comp (Measure.measurable_dirac.comp ha))).add
    (hq.mul ((Measure.measurable_coe hs).comp (Measure.measurable_dirac.comp hb)))

/-- The final outcome pushforward is a measurable channel in the recorded coordinates. -/
-- @node: lowerPair_outcomeMap_measurable
@[fun_prop] lemma lowerPair_outcomeMap_measurable (d : ℕ) (β δ h M : ℝ) (sign : Bool) :
    Measurable (fun z : (Fin d → ℝ) × Bool × ℝ =>
      (binaryMeasure M (treatedPlusProbability d β δ h M sign z.1)).map
        (fun y1 => (z.1, z.2.1, z.2.2, y1))) := by
  have heq (z : (Fin d → ℝ) × Bool × ℝ) :
      (binaryMeasure M (treatedPlusProbability d β δ h M sign z.1)).map
        (fun y1 => (z.1, z.2.1, z.2.2, y1)) =
      ENNReal.ofReal (treatedPlusProbability d β δ h M sign z.1) •
        Measure.dirac (z.1, z.2.1, z.2.2, M / 2) +
      ENNReal.ofReal (1 - treatedPlusProbability d β δ h M sign z.1) •
        Measure.dirac (z.1, z.2.1, z.2.2, -M / 2) := by
    rw [binaryMeasure, Measure.map_add _ _ (by fun_prop), Measure.map_smul,
      Measure.map_smul, Measure.map_dirac' (by fun_prop), Measure.map_dirac' (by fun_prop)]
  simp_rw [heq]
  apply twoAtom_measurable <;> fun_prop

/-- Measurable weights may scale measurable measure-valued channels. -/
-- @node: weightedChannels_measurable
@[fun_prop] lemma weightedChannels_measurable {α Ω : Type*}
    [MeasurableSpace α] [MeasurableSpace Ω]
    (κ η : α → Measure Ω) (p q : α → ℝ≥0∞)
    (hκ : Measurable κ) (hη : Measurable η) (hp : Measurable p) (hq : Measurable q) :
    Measurable (fun x => p x • κ x + q x • η x) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  exact (hp.mul ((Measure.measurable_coe hs).comp hκ)).add
    (hq.mul ((Measure.measurable_coe hs).comp hη))

/-- Integrating out the symmetric control outcome gives a measurable channel. -/
-- @node: lowerPair_controlMap_measurable
@[fun_prop] lemma lowerPair_controlMap_measurable (d : ℕ) (β δ h M : ℝ) (sign : Bool) :
    Measurable (fun z : (Fin d → ℝ) × Bool =>
      (binaryMeasure M (1 / 2)).bind (fun y0 =>
        (binaryMeasure M (treatedPlusProbability d β δ h M sign z.1)).map
          (fun y1 => (z.1, z.2, y0, y1)))) := by
  have hinner (z : (Fin d → ℝ) × Bool) : Measurable (fun y0 : ℝ =>
      (binaryMeasure M (treatedPlusProbability d β δ h M sign z.1)).map
        (fun y1 => (z.1, z.2, y0, y1))) := by
    simpa only [Function.comp_def] using (lowerPair_outcomeMap_measurable d β δ h M sign).comp
      (show Measurable (fun y0 : ℝ => (z.1, z.2, y0)) from by fun_prop)
  simp_rw [show binaryMeasure M (1 / 2) =
    ENNReal.ofReal (1 / 2) • Measure.dirac (M / 2) +
    ENNReal.ofReal (1 - 1 / 2) • Measure.dirac (-M / 2) from rfl,
    twoAtom_bind _ _ _ _ _ (hinner _)]
  apply weightedChannels_measurable
  · simpa only [Function.comp_def] using (lowerPair_outcomeMap_measurable d β δ h M sign).comp
      (show Measurable (fun z : (Fin d → ℝ) × Bool => (z.1, z.2, M / 2)) from by fun_prop)
  · simpa only [Function.comp_def] using (lowerPair_outcomeMap_measurable d β δ h M sign).comp
      (show Measurable (fun z : (Fin d → ℝ) × Bool => (z.1, z.2, -M / 2)) from by fun_prop)
  all_goals fun_prop

/-- Integrating out treatment gives a measurable full conditional channel. -/
-- @node: lowerPair_fullKernel_measurable
@[fun_prop] lemma lowerPair_fullKernel_measurable (d : ℕ) (β q h δ M : ℝ)
    (hq : 0 < q) (sign : Bool) :
    Measurable (fun x : Fin d → ℝ =>
      (treatmentMeasure (baselinePropensity d q x)).bind (fun a =>
        (binaryMeasure M (1 / 2)).bind (fun y0 =>
          (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
            (fun y1 => (x, a, y0, y1))))) := by
  have hinner (x : Fin d → ℝ) : Measurable (fun a : Bool =>
      (binaryMeasure M (1 / 2)).bind (fun y0 =>
        (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
          (fun y1 => (x, a, y0, y1)))) := by
    simpa only [Function.comp_def] using (lowerPair_controlMap_measurable d β δ h M sign).comp
      (show Measurable (fun a : Bool => (x, a)) from by fun_prop)
  simp_rw [treatmentMeasure, twoAtom_bind _ _ _ _ _ (hinner _)]
  apply weightedChannels_measurable
  · simpa only [Function.comp_def] using (lowerPair_controlMap_measurable d β δ h M sign).comp
      (show Measurable (fun x : Fin d → ℝ => (x, true)) from by fun_prop)
  · simpa only [Function.comp_def] using (lowerPair_controlMap_measurable d β δ h M sign).comp
      (show Measurable (fun x : Fin d → ℝ => (x, false)) from by fun_prop)
  · exact (baselinePropensity_measurable d q hq).ennreal_ofReal
  · exact (measurable_const.sub (baselinePropensity_measurable d q hq)).ennreal_ofReal

/-- A measurable pushforward commutes with binding a measurable channel. -/
-- @node: map_bind_channel
lemma map_bind_channel {α Ω Ξ : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    [MeasurableSpace Ξ] (μ : Measure α) (κ : α → Measure Ω) (f : Ω → Ξ)
    (hκ : Measurable κ) (hf : Measurable f) :
    (μ.bind κ).map f = μ.bind (fun x => (κ x).map f) := by
  rw [← Measure.bind_dirac_eq_map _ hf,
    Measure.bind_bind hκ.aemeasurable
      (show AEMeasurable (fun x => Measure.dirac (f x)) (μ.bind κ) from
        (Measure.measurable_dirac.comp hf).aemeasurable)]
  simp_rw [Measure.bind_dirac_eq_map _ hf]

/-- Normalized conditional draws preserve the witness's initial uniform covariates. -/
-- @node: lowerPair_uniformDesign
lemma lowerPair_uniformDesign (d : ℕ) (β q h δ M : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hβ : 0 < β) (hδ : 0 ≤ δ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hM : 0 < M) (hsmall : δ ≤ M / 4)
    (sign : Bool) : UniformDesign (lowerPair d β q h δ M sign) := by
  let ν (x : Fin d → ℝ) (a : Bool) (y0 : ℝ) : Measure (Full d) :=
    (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
      (fun y1 => (x, a, y0, y1))
  let η (x : Fin d → ℝ) (a : Bool) := (binaryMeasure M (1 / 2)).bind (ν x a)
  let κ (x : Fin d → ℝ) :=
    (treatmentMeasure (baselinePropensity d q x)).bind (η x)
  have hν (x : Fin d → ℝ) (a : Bool) : Measurable (ν x a) := by
    simpa only [Function.comp_def] using (lowerPair_outcomeMap_measurable d β δ h M sign).comp
      (show Measurable (fun y0 : ℝ => (x, a, y0)) from by fun_prop)
  have hη (x : Fin d → ℝ) : Measurable (η x) := by
    simpa only [Function.comp_def] using (lowerPair_controlMap_measurable d β δ h M sign).comp
      (show Measurable (fun a : Bool => (x, a)) from by fun_prop)
  have hκ : Measurable κ := lowerPair_fullKernel_measurable d β q h δ M hq sign
  have hkey (x : Fin d → ℝ) (hx : x ∈ cube d) : (κ x).map Prod.fst = Measure.dirac x := by
    have hp := treatedPlusProbability_quarter_bounds d β δ h M
      hβ hδ hh hh1 hM hsmall sign x hx
    haveI : IsProbabilityMeasure (binaryMeasure M
        (treatedPlusProbability d β δ h M sign x)) :=
      binaryMeasure_isProbabilityMeasure M _ ⟨by linarith [hp.1], by linarith [hp.2]⟩
    haveI : IsProbabilityMeasure (binaryMeasure M (1 / 2)) :=
      binaryMeasure_isProbabilityMeasure M _ (by norm_num)
    haveI : IsProbabilityMeasure (treatmentMeasure (baselinePropensity d q x)) :=
      baselineTreatment_isProbabilityMeasure d q hd hq x hx
    have hlast (a : Bool) (y0 : ℝ) : (ν x a y0).map Prod.fst = Measure.dirac x := by
      dsimp [ν]
      rw [Measure.map_map measurable_fst (by fun_prop)]
      change (binaryMeasure M (treatedPlusProbability d β δ h M sign x)).map
        (fun _ => x) = Measure.dirac x
      rw [Measure.map_const, measure_univ, one_smul]
    have hmiddle (a : Bool) : (η x a).map Prod.fst = Measure.dirac x := by
      rw [show η x a = (binaryMeasure M (1 / 2)).bind (ν x a) from rfl,
        map_bind_channel _ _ _ (hν x a) measurable_fst]
      simp_rw [hlast]
      rw [Measure.bind_const, measure_univ, one_smul]
    rw [show κ x = (treatmentMeasure (baselinePropensity d q x)).bind (η x) from rfl,
      map_bind_channel _ _ _ (hη x) measurable_fst]
    simp_rw [hmiddle]
    rw [Measure.bind_const, measure_univ, one_smul]
  change ((volume.restrict (cube d)).bind κ).map Prod.fst = volume.restrict (cube d)
  rw [map_bind_channel _ _ _ hκ measurable_fst]
  calc
    _ = (volume.restrict (cube d)).bind Measure.dirac := by
      apply Measure.bind_congr_right
      filter_upwards [ae_restrict_mem (by simp [cube] : MeasurableSet (cube d))] with x hx
      exact hkey x hx
    _ = volume.restrict (cube d) := Measure.bind_dirac

/-- The normalized witness also satisfies the global tail envelope unconditionally. -/
-- @node: lowerPair_globalTail
lemma lowerPair_globalTail (d : ℕ) (β γ C h δ M : ℝ)
    (hd : 1 ≤ d) (hγ : 1 < γ) (hC : 1 ≤ C) (hβ : 0 < β) (hδ : 0 ≤ δ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hM : 0 < M) (hsmall : δ ≤ M / 4)
    (sign : Bool) : GlobalTail (lowerPair d β (tailExponent γ) h δ M sign) C γ := by
  apply lowerPair_globalTail_of_uniformDesign d β γ C h δ M hd hγ hC sign
  exact lowerPair_uniformDesign d β (tailExponent γ) h δ M hd
    (by unfold tailExponent; linarith) hβ hδ hh hh1 hM hsmall sign

/-- The witness is a probability law because its covariate marginal has unit mass. -/
-- @node: lowerPair_isProbabilityMeasure
lemma lowerPair_isProbabilityMeasure (d : ℕ) (β q h δ M : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hβ : 0 < β) (hδ : 0 ≤ δ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hM : 0 < M) (hsmall : δ ≤ M / 4)
    (sign : Bool) : IsProbabilityMeasure (lowerPair d β q h δ M sign).full := by
  apply isProbabilityMeasure_iff.mpr
  have hu := lowerPair_uniformDesign d β q h δ M hd hq hβ hδ hh hh1 hM hsmall sign
  have heq := congrArg (fun μ : Measure (Fin d → ℝ) => μ Set.univ) hu
  simpa [Law.xLaw, Measure.map_apply measurable_fst MeasurableSet.univ,
    cube, Real.volume_Icc_pi] using heq

/-- The witness's product samples are independent replicas with the pathwise observed image. -/
-- @node: lowerPair_iidSampling
lemma lowerPair_iidSampling (d : ℕ) (β q h δ M : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hβ : 0 < β) (hδ : 0 ≤ δ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hM : 0 < M) (hsmall : δ ≤ M / 4)
    (sign : Bool) : IidSampling (lowerPair d β q h δ M sign) := by
  haveI := lowerPair_isProbabilityMeasure d β q h δ M hd hq hβ hδ hh hh1 hM hsmall sign
  have ho : Measurable (observe (d := d)) := by
    unfold observe
    apply Measurable.prodMk (by fun_prop)
    apply Measurable.prodMk (by fun_prop)
    apply Measurable.ite _ (by fun_prop) (by fun_prop)
    exact (measurableSet_singleton true).preimage (by fun_prop)
  refine ⟨inferInstance, fun _ _ => rfl, ?_⟩
  intro n hn
  change Measure.pi (fun _ : Fin n =>
    ((lowerPair d β q h δ M sign).full).map observe) =
    (Measure.pi (fun _ : Fin n => (lowerPair d β q h δ M sign).full)).map
      (fun units i => observe (units i))
  haveI : IsProbabilityMeasure (((lowerPair d β q h δ M sign).full).map observe) :=
    Measure.isProbabilityMeasure_map ho.aemeasurable
  exact (Measure.pi_map_pi (fun _ => ho.aemeasurable)).symm

end CausalSmith.Stat.GlobalTailDesignRobustCate
