module
public import Causalean.Mathlib.Probability.Kernel.BernoulliMark
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.CausalKernels

/-!
The independent treatment/potential-outcome experiment and its consistency pushforward.
These construct a probability causal law with unit support; identifying its observed marginal
and proving conditional independence on the pushed-forward space remain separate steps.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- Uniform design represented on the covariate support subtype. -/
-- @node: causalCovariateLaw
def causalCovariateLaw : Measure (Set.Icc (0 : ℝ) 1) :=
  unitVolume.comap Subtype.val

/-- The supported uniform design is a probability measure. -/
-- @node: causalCovariateLaw_isProbabilityMeasure
instance causalCovariateLaw_isProbabilityMeasure : IsProbabilityMeasure causalCovariateLaw := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  apply (MeasurableEmbedding.subtype_coe measurableSet_Icc).isProbabilityMeasure_comap
  simpa [unitVolume] using
    (ae_restrict_mem (μ := (volume : Measure ℝ)) (measurableSet_Icc : MeasurableSet (Set.Icc (0 : ℝ) 1)))

/-- Forgetting the subtype recovers the original uniform design measure. -/
-- @node: causalCovariateLaw_map_val
lemma causalCovariateLaw_map_val : causalCovariateLaw.map Subtype.val = unitVolume := by
  rw [causalCovariateLaw, map_comap_subtype_coe measurableSet_Icc]
  simp [unitVolume, Measure.restrict_restrict]

/-- Conditional treatment law with the observed propensity. -/
-- @node: causalTreatmentKernel
def causalTreatmentKernel (P : ObsLaw) : Kernel (Set.Icc (0 : ℝ) 1) Bool :=
  Causalean.Mathlib.Probability.bernoulliMarkKernel (fun x => P.e x.val)

/-- Every conditional treatment law is normalized. -/
-- @node: causalTreatmentKernel_isMarkov
instance causalTreatmentKernel_isMarkov (P : ObsLaw) :
    IsMarkovKernel (causalTreatmentKernel P) where
  isProbabilityMeasure x := by
    have hm : Measurable (fun x : Set.Icc (0 : ℝ) 1 => P.e x.val) := by
      first | fun_prop | exact P.e_measurable.comp measurable_subtype_coe
    rw [causalTreatmentKernel,
      Causalean.Mathlib.Probability.bernoulliMarkKernel_apply _ hm]
    exact Causalean.Mathlib.Probability.bernoulliBool_isProbabilityMeasure
      (P.e_range x.val x.property).1 (P.e_range x.val x.property).2

/-- Each treatment singleton has the prescribed arm probability. -/
-- @node: causalTreatmentKernel_apply_singleton
lemma causalTreatmentKernel_apply_singleton (P : ObsLaw) (x : Set.Icc (0 : ℝ) 1)
    (a : Bool) : causalTreatmentKernel P x {a} = ENNReal.ofReal (pi P a x.val) := by
  cases a
  · exact Causalean.Mathlib.Probability.bernoulliMarkKernel_apply_false _
      (P.e_measurable.comp measurable_subtype_coe) x
  · exact Causalean.Mathlib.Probability.bernoulliMarkKernel_apply_true _
      (P.e_measurable.comp measurable_subtype_coe) x

/-- Draw treatment independently of the independent potential-outcome pair given covariate. -/
-- @node: causalExperimentKernel
def causalExperimentKernel (P : ObsLaw) :
    Kernel (Set.Icc (0 : ℝ) 1) (Bool × (ℝ × ℝ)) :=
  (causalTreatmentKernel P).prod (potentialPairKernel P)

/-- The conditional three-coordinate experiment is a probability kernel. -/
-- @node: causalExperimentKernel_isMarkov
instance causalExperimentKernel_isMarkov (P : ObsLaw) :
    IsMarkovKernel (causalExperimentKernel P) := by
  unfold causalExperimentKernel
  infer_instance

/-- Treatment and the potential pair are independent at each covariate. -/
-- @node: causalExperimentKernel_indepFun
lemma causalExperimentKernel_indepFun (P : ObsLaw) (x : Set.Icc (0 : ℝ) 1) :
    IndepFun (Prod.fst : Bool × (ℝ × ℝ) → Bool) Prod.snd
      (causalExperimentKernel P x) := by
  rw [causalExperimentKernel, Kernel.prod_apply]
  exact indepFun_prod (X := id) (Y := id) measurable_id measurable_id

/-- The experiment has the required product probabilities on treatment/outcome rectangles. -/
-- @node: causalExperimentKernel_apply_rectangle
lemma causalExperimentKernel_apply_rectangle (P : ObsLaw) (x : Set.Icc (0 : ℝ) 1)
    (a : Bool) (D0 D1 : Set ℝ) :
    causalExperimentKernel P x ({a} ×ˢ (D0 ×ˢ D1)) =
      ENNReal.ofReal (pi P a x.val) *
        (conditionalOutcomeKernel P false x D0 * conditionalOutcomeKernel P true x D1) := by
  rw [causalExperimentKernel, Kernel.prod_apply_prod,
    causalTreatmentKernel_apply_singleton, potentialPairKernel_apply_prod]

/-- The consistency map retains both potential outcomes and reports the selected outcome. -/
-- @node: causalConsistencyMap
def causalConsistencyMap (z : Set.Icc (0 : ℝ) 1 × (Bool × (ℝ × ℝ))) : CausalSpace :=
  ((z.1.val, z.2.1, if z.2.1 then z.2.2.2 else z.2.2.1), z.2.2)

/-- The consistency pushforward is measurable. -/
-- @node: measurable_causalConsistencyMap
@[fun_prop] lemma measurable_causalConsistencyMap : Measurable causalConsistencyMap := by
  have hm : Measurable (fun z : Set.Icc (0 : ℝ) 1 × (Bool × (ℝ × ℝ)) =>
      if z.2.1 then z.2.2.2 else z.2.2.1) :=
    Measurable.ite ((measurable_fst.comp measurable_snd) (measurableSet_singleton true))
      (by fun_prop) (by fun_prop)
  exact ((measurable_subtype_coe.comp measurable_fst).prodMk
    ((measurable_fst.comp measurable_snd).prodMk hm)).prodMk (by fun_prop)

/-- The consistency map satisfies consistency at every point. -/
-- @node: causalConsistencyMap_consistency
lemma causalConsistencyMap_consistency (z : Set.Icc (0 : ℝ) 1 × (Bool × (ℝ × ℝ))) :
    Y (causalConsistencyMap z).1 =
      potentialY (A (causalConsistencyMap z).1) (causalConsistencyMap z) := by
  rfl

/-- A concrete causal law from the independent experiment and the consistency map. -/
-- @node: constructedCausalLaw
def constructedCausalLaw (P : ObsLaw) : Measure CausalSpace :=
  (causalCovariateLaw ⊗ₘ causalExperimentKernel P).map causalConsistencyMap

/-- The constructed causal law is normalized. -/
-- @node: constructedCausalLaw_isProbabilityMeasure
instance constructedCausalLaw_isProbabilityMeasure (P : ObsLaw) :
    IsProbabilityMeasure (constructedCausalLaw P) :=
  Measure.isProbabilityMeasure_map measurable_causalConsistencyMap.aemeasurable

/-- The constructed law satisfies the paper's almost-sure consistency assumption. -/
-- @node: constructedCausalLaw_consistency
lemma constructedCausalLaw_consistency (P : ObsLaw) :
    CausalConsistency (constructedCausalLaw P) := by
  have hp : Measurable (fun o : CausalSpace => potentialY (A o.1) o) :=
    Measurable.ite (by
      exact (measurable_fst.comp (measurable_snd.comp measurable_fst))
        (measurableSet_singleton true)) (by fun_prop [potentialY]) (by fun_prop [potentialY])
  apply (ae_map_iff measurable_causalConsistencyMap.aemeasurable
    (measurableSet_eq_fun (by fun_prop [Y]) hp)).2
  exact ae_of_all _ causalConsistencyMap_consistency

/-- The independent experiment keeps both potential outcomes in the unit interval. -/
-- @node: causalExperimentKernel_ae_mem
lemma causalExperimentKernel_ae_mem (P : ObsLaw) (x : Set.Icc (0 : ℝ) 1) :
    ∀ᵐ z ∂causalExperimentKernel P x,
      z.2.1 ∈ Set.Icc 0 1 ∧ z.2.2 ∈ Set.Icc 0 1 := by
  rw [causalExperimentKernel, Kernel.prod_apply]
  apply (Measure.ae_prod_iff_ae_ae (by
    exact measurable_snd (measurableSet_Icc.prod measurableSet_Icc))).2
  exact ae_of_all _ (fun _ => potentialPairKernel_ae_mem P x)

/-- The consistency pushforward keeps the two potential outcomes on their support. -/
-- @node: constructedCausalLaw_ae_mem
lemma constructedCausalLaw_ae_mem (P : ObsLaw) :
    ∀ᵐ o ∂constructedCausalLaw P,
      o.2.1 ∈ Set.Icc 0 1 ∧ o.2.2 ∈ Set.Icc 0 1 := by
  apply (ae_map_iff measurable_causalConsistencyMap.aemeasurable
    (measurable_snd (measurableSet_Icc.prod measurableSet_Icc))).2
  apply Measure.ae_compProd_of_ae_ae (by
    exact (measurable_snd.comp measurable_snd)
      (measurableSet_Icc.prod measurableSet_Icc))
  exact ae_of_all _ (fun x => causalExperimentKernel_ae_mem P x)

/-- The observed coordinates of the consistency pushforward also have unit support. -/
-- @node: constructedCausalLaw_observed_support
lemma constructedCausalLaw_observed_support (P : ObsLaw) :
    ∀ᵐ o ∂constructedCausalLaw P, X o.1 ∈ Set.Icc 0 1 ∧ Y o.1 ∈ Set.Icc 0 1 := by
  have hm : MeasurableSet {o : CausalSpace |
      X o.1 ∈ Set.Icc 0 1 ∧ Y o.1 ∈ Set.Icc 0 1} :=
    (measurableSet_Icc.preimage (by fun_prop [X])).inter
      (measurableSet_Icc.preimage (by fun_prop [Y]))
  apply (ae_map_iff measurable_causalConsistencyMap.aemeasurable hm).2
  have hs : ∀ᵐ z ∂causalCovariateLaw ⊗ₘ causalExperimentKernel P,
      z.2.2.1 ∈ Set.Icc 0 1 ∧ z.2.2.2 ∈ Set.Icc 0 1 := by
    apply Measure.ae_compProd_of_ae_ae (by
      exact (measurable_snd.comp measurable_snd)
        (measurableSet_Icc.prod measurableSet_Icc))
    exact ae_of_all _ (fun x => causalExperimentKernel_ae_mem P x)
  filter_upwards [hs] with z hz
  refine ⟨z.1.property, ?_⟩
  change (if z.2.1 then z.2.2.2 else z.2.2.1) ∈ Set.Icc 0 1
  cases z.2.1
  · exact hz.1
  · exact hz.2

/-- The constructed causal law has the paper's uniform covariate marginal. -/
-- @node: constructedCausalLaw_map_causalX
lemma constructedCausalLaw_map_causalX (P : ObsLaw) :
    (constructedCausalLaw P).map causalX = unitVolume := by
  rw [constructedCausalLaw,
    Measure.map_map measurable_causalX measurable_causalConsistencyMap]
  change (causalCovariateLaw ⊗ₘ causalExperimentKernel P).map
    (Subtype.val ∘ Prod.fst) = unitVolume
  rw [← Measure.map_map measurable_subtype_coe measurable_fst]
  change ((causalCovariateLaw ⊗ₘ causalExperimentKernel P).fst).map Subtype.val = unitVolume
  rw [Measure.fst_compProd, causalCovariateLaw_map_val]

private lemma conditionalOutcomeKernel_apply_set (P : ObsLaw) (a : Bool)
    (x : Set.Icc (0 : ℝ) 1) (D : Set ℝ) (hD : MeasurableSet D) :
    conditionalOutcomeKernel P a x D =
      ENNReal.ofReal (∫ y in D, P.eta a x.val y ∂unitVolume) := by
  rw [conditionalOutcomeKernel_apply, withDensity_apply _ hD]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (P.eta_integrable a x.val x.property).integrableOn]
  filter_upwards [(ae_restrict_mem measurableSet_Icc).filter_mono ae_restrict_le] with y hy
  exact P.eta_nonneg a x.val y x.property hy

private lemma measurable_pi (P : ObsLaw) (a : Bool) : Measurable (pi P a) := by
  cases a
  · exact measurable_const.sub P.e_measurable
  · exact P.e_measurable

private lemma measurable_eta_bin (P : ObsLaw) (a : Bool) (D : Set ℝ) :
    Measurable (fun x => ∫ y in D, P.eta a x y ∂unitVolume) := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  exact (P.eta_measurable a).stronglyMeasurable.integral_prod_right'.measurable

private lemma eta_bin_mem (P : ObsLaw) (a : Bool) (D : Set ℝ)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (∫ y in D, P.eta a x y ∂unitVolume) ∈ Set.Icc (0 : ℝ) 1 := by
  have hn : ∀ᵐ y ∂unitVolume, 0 ≤ P.eta a x y := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact P.eta_nonneg a x y hx hy
  exact ⟨integral_nonneg_of_ae (ae_restrict_of_ae hn), by
    rw [← P.eta_normalized a x hx]
    exact setIntegral_le_integral (P.eta_integrable a x hx) hn⟩

private lemma integrable_observed_rectangle_weight (P : ObsLaw) (a : Bool) (D : Set ℝ) :
    Integrable (fun x => pi P a x * ∫ y in D, P.eta a x y ∂unitVolume)
      unitVolume := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  apply Integrable.of_bound
    ((measurable_pi P a).mul (measurable_eta_bin P a D)).aestronglyMeasurable 1
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  have hd := eta_bin_mem P a D x hx
  have he := P.e_range x hx
  have hp : pi P a x ∈ Set.Icc (0 : ℝ) 1 := by
    cases a <;> simp only [pi, armProbability, Bool.false_eq_true, ↓reduceIte,
      Set.mem_Icc] <;> constructor <;> linarith [he.1, he.2]
  change |pi P a x * ∫ y in D, P.eta a x y ∂unitVolume| ≤ 1
  rw [abs_of_nonneg (mul_nonneg hp.1 hd.1)]
  exact (mul_le_mul hp.2 hd.2 hd.1 (by norm_num)).trans_eq (by norm_num)

private lemma constructedCausalLaw_observed_rectangle (P : ObsLaw)
    (B D : Set ℝ) (hB : MeasurableSet B) (hD : MeasurableSet D) (a : Bool) :
    ((constructedCausalLaw P).map Prod.fst) (B ×ˢ ({a} ×ˢ D)) =
      P.law (B ×ˢ ({a} ×ˢ D)) := by
  rw [constructedCausalLaw, Measure.map_map measurable_fst measurable_causalConsistencyMap]
  rw [Measure.map_apply (measurable_fst.comp measurable_causalConsistencyMap)
    (hB.prod ((measurableSet_singleton a).prod hD))]
  cases a
  · have hpre : (Prod.fst ∘ causalConsistencyMap) ⁻¹'
        (B ×ˢ ({false} ×ˢ D)) =
        (Subtype.val ⁻¹' B) ×ˢ ({false} ×ˢ (D ×ˢ Set.univ)) := by
      ext z
      simp [causalConsistencyMap]
      aesop
    rw [hpre, Measure.compProd_apply_prod (hB.preimage measurable_subtype_coe)
      ((measurableSet_singleton false).prod (hD.prod MeasurableSet.univ))]
    simp_rw [causalExperimentKernel_apply_rectangle]
    simp only [measure_univ, mul_one]
    simp_rw [conditionalOutcomeKernel_apply_set P false _ D hD]
    have hp (x : Set.Icc (0 : ℝ) 1) : 0 ≤ pi P false x.val := by
      have he := P.e_range x.val x.property
      simp only [pi, armProbability, Bool.false_eq_true, ↓reduceIte]
      exact sub_nonneg.mpr he.2
    simp_rw [← ENNReal.ofReal_mul (hp _)]
    have hf : Measurable (fun x : ℝ =>
        ENNReal.ofReal (pi P false x * ∫ y in D, P.eta false x y ∂unitVolume)) :=
      ((measurable_pi P false).mul (measurable_eta_bin P false D)).ennreal_ofReal
    rw [← MeasureTheory.setLIntegral_map hB hf measurable_subtype_coe,
      causalCovariateLaw_map_val]
    rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_observed_rectangle_weight P false D).integrableOn]
    · rw [← ENNReal.ofReal_toReal (measure_ne_top P.law _)]
      congr 1
      rw [show B ×ˢ ({false} ×ˢ D) =
          {o : Omega | X o ∈ B ∧ A o = false ∧ Y o ∈ D} by
        ext o
        simp [X, A, Y]]
      simpa only [measureReal_def, pi] using (P.rectangles B D hB hD false).symm
    · filter_upwards [(ae_restrict_mem measurableSet_Icc).filter_mono ae_restrict_le] with x hx
      exact mul_nonneg (by
        have he := P.e_range x hx
        simp only [pi, armProbability, Bool.false_eq_true, ↓reduceIte]
        exact sub_nonneg.mpr he.2) (eta_bin_mem P false D x hx).1
  · have hpre : (Prod.fst ∘ causalConsistencyMap) ⁻¹'
        (B ×ˢ ({true} ×ˢ D)) =
        (Subtype.val ⁻¹' B) ×ˢ ({true} ×ˢ (Set.univ ×ˢ D)) := by
      ext z
      simp [causalConsistencyMap]
      aesop
    rw [hpre, Measure.compProd_apply_prod (hB.preimage measurable_subtype_coe)
      ((measurableSet_singleton true).prod (MeasurableSet.univ.prod hD))]
    simp_rw [causalExperimentKernel_apply_rectangle]
    simp only [measure_univ, one_mul]
    simp_rw [conditionalOutcomeKernel_apply_set P true _ D hD]
    have hp (x : Set.Icc (0 : ℝ) 1) : 0 ≤ pi P true x.val := by
      exact (P.e_range x.val x.property).1
    simp_rw [← ENNReal.ofReal_mul (hp _)]
    have hf : Measurable (fun x : ℝ =>
        ENNReal.ofReal (pi P true x * ∫ y in D, P.eta true x y ∂unitVolume)) :=
      ((measurable_pi P true).mul (measurable_eta_bin P true D)).ennreal_ofReal
    rw [← MeasureTheory.setLIntegral_map hB hf measurable_subtype_coe,
      causalCovariateLaw_map_val]
    rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_observed_rectangle_weight P true D).integrableOn]
    · rw [← ENNReal.ofReal_toReal (measure_ne_top P.law _)]
      congr 1
      rw [show B ×ˢ ({true} ×ˢ D) =
          {o : Omega | X o ∈ B ∧ A o = true ∧ Y o ∈ D} by
        ext o
        simp [X, A, Y]]
      simpa only [measureReal_def, pi] using (P.rectangles B D hB hD true).symm
    · filter_upwards [(ae_restrict_mem measurableSet_Icc).filter_mono ae_restrict_le] with x hx
      exact mul_nonneg (P.e_range x hx).1 (eta_bin_mem P true D x hx).1

/-- The observed marginal of the constructed causal law is the supplied observed law. -/
-- @node: constructedCausalLaw_map_observed
lemma constructedCausalLaw_map_observed (P : ObsLaw) :
    (constructedCausalLaw P).map Prod.fst = P.law := by
  apply Measure.ext_prod₃
  intro B C D hB hC hD
  by_cases hf : false ∈ C <;> by_cases ht : true ∈ C
  · have hC : C = Set.univ := by
      ext a
      cases a <;> simp [hf, ht]
    subst C
    let S0 : Set Omega := B ×ˢ ({false} ×ˢ D)
    let S1 : Set Omega := B ×ˢ ({true} ×ˢ D)
    have hu : B ×ˢ (Set.univ ×ˢ D) = S0 ∪ S1 := by
      ext o
      cases o.2.1 <;> simp [S0, S1] <;> aesop
    rw [hu]
    rw [measure_union]
    · rw [measure_union]
      · exact congrArg₂ (· + ·)
          (constructedCausalLaw_observed_rectangle P B D hB hD false)
          (constructedCausalLaw_observed_rectangle P B D hB hD true)
      · simp [S0, S1]
      · exact hB.prod ((measurableSet_singleton true).prod hD)
    · simp [S0, S1]
    · exact hB.prod ((measurableSet_singleton true).prod hD)
  · have hC : C = {false} := by
      ext a
      cases a <;> simp [hf, ht]
    subst C
    exact constructedCausalLaw_observed_rectangle P B D hB hD false
  · have hC : C = {true} := by
      ext a
      cases a <;> simp [hf, ht]
    subst C
    exact constructedCausalLaw_observed_rectangle P B D hB hD true
  · have hC : C = ∅ := by
      ext a
      cases a <;> simp [hf, ht]
    subst C
    simp

/-- The constructed law is a probability causal extension of the observed law. -/
-- @node: constructedCausalLaw_isExtension
lemma constructedCausalLaw_isExtension (P : ObsLaw) :
    IsCausalExtension P (constructedCausalLaw P) := by
  exact ⟨inferInstance, constructedCausalLaw_map_observed P,
    constructedCausalLaw_ae_mem P⟩

end CausalSmith.Stat.DensityEffectRoughNull
