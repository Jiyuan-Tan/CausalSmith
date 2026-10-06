module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.CausalConstruction
public import Causalean.Mathlib.Probability.Independence.Conditional.Transport

/-!
Conditional independence of the constructed causal experiment, obtained by disintegrating
its composition-product law and transporting through the consistency map.
-/

public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- A conditional law obtained by sampling a kernel has that kernel's mapped conditional laws. -/
-- @node: causalExperiment_condDistrib
lemma causalExperiment_condDistrib
    {S E F : Type*} [MeasurableSpace S] [StandardBorelSpace S]
    [MeasurableSpace E] [StandardBorelSpace E]
    [MeasurableSpace F] [StandardBorelSpace F] [Nonempty F]
    (μ : Measure S) [IsFiniteMeasure μ] (κ : Kernel S E) [IsMarkovKernel κ]
    (f : E → F) (hf : Measurable f) :
    condDistrib (f ∘ Prod.snd) Prod.fst (μ ⊗ₘ κ) =ᵐ[μ] κ.map f := by
  have hm : (μ ⊗ₘ κ).map (Prod.fst : S × E → S) = μ := by
    change (μ ⊗ₘ κ).fst = μ
    exact Measure.fst_compProd μ κ
  have h := condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (μ := μ ⊗ₘ κ) measurable_fst (hf.comp measurable_snd) (κ := κ.map f)
    (by rw [hm, Measure.compProd_map hf]; rfl)
  rwa [hm] at h

/-- Pointwise kernel independence yields conditional independence given the sampled covariate. -/
-- @node: causalExperiment_condIndepFun
lemma causalExperiment_condIndepFun
    {S E F G : Type*} [MeasurableSpace S] [StandardBorelSpace S]
    [MeasurableSpace E] [StandardBorelSpace E]
    [MeasurableSpace F] [StandardBorelSpace F] [Nonempty F]
    [MeasurableSpace G] [StandardBorelSpace G] [Nonempty G]
    (μ : Measure S) [IsFiniteMeasure μ] (κ : Kernel S E) [IsMarkovKernel κ]
    (f : E → F) (g : E → G) (hf : Measurable f) (hg : Measurable g)
    (hi : ∀ x, IndepFun f g (κ x)) :
    CondIndepFun (MeasurableSpace.comap (Prod.fst : S × E → S) inferInstance)
      measurable_fst.comap_le (f ∘ Prod.snd) (g ∘ Prod.snd) (μ ⊗ₘ κ) := by
  rw [condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib
    (hf.comp measurable_snd) (hg.comp measurable_snd) measurable_fst]
  have hm : (μ ⊗ₘ κ).map (Prod.fst : S × E → S) = μ := by
    change (μ ⊗ₘ κ).fst = μ
    exact Measure.fst_compProd μ κ
  rw [hm, ← Measure.compProd_eq_comp_prod]
  change (μ ⊗ₘ κ).map (Prod.map id (fun z => (f z, g z))) = _
  rw [← Measure.compProd_map (hf.prodMk hg)]
  apply Measure.compProd_congr
  filter_upwards [causalExperiment_condDistrib μ κ f hf,
    causalExperiment_condDistrib μ κ g hg] with x hx hy
  rw [Kernel.prod_apply, hx, hy, Kernel.map_apply _ (hf.prodMk hg),
    Kernel.map_apply _ hf, Kernel.map_apply _ hg]
  exact (hi x).map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable

/-- Forgetting the support subtype does not change the covariate sigma-algebra. -/
-- @node: causalExperiment_covariate_comap
lemma causalExperiment_covariate_comap :
    MeasurableSpace.comap (fun z : Set.Icc (0 : ℝ) 1 × (Bool × (ℝ × ℝ)) => z.1.val)
      inferInstance = MeasurableSpace.comap
        (Prod.fst : Set.Icc (0 : ℝ) 1 × (Bool × (ℝ × ℝ)) → Set.Icc (0 : ℝ) 1)
        inferInstance := by
  change MeasurableSpace.comap (Subtype.val ∘ Prod.fst) inferInstance = _
  rw [← MeasurableSpace.comap_comp,
    (MeasurableEmbedding.subtype_coe measurableSet_Icc).comap_eq]

/-- Treatment is conditionally independent of both potentials in the constructed causal law. -/
-- @node: constructedCausalLaw_exchangeability
lemma constructedCausalLaw_exchangeability (P : ObsLaw) :
    CausalExchangeability (constructedCausalLaw P) inferInstance := by
  unfold CausalExchangeability
  change CondIndepFun _ _ _ _
    ((causalCovariateLaw ⊗ₘ causalExperimentKernel P).map causalConsistencyMap)
  apply Causalean.Mathlib.Probability.Independence.Conditional.condIndepFun_of_map
    measurable_causalConsistencyMap (by fun_prop [A]) measurable_snd measurable_causalX
  change CondIndepFun
    (MeasurableSpace.comap (fun z : Set.Icc (0 : ℝ) 1 × (Bool × (ℝ × ℝ)) => z.1.val)
      inferInstance) _ (Prod.fst ∘ Prod.snd) (Prod.snd ∘ Prod.snd) _
  simp only [causalExperiment_covariate_comap]
  exact causalExperiment_condIndepFun causalCovariateLaw (causalExperimentKernel P)
    Prod.fst Prod.snd measurable_fst measurable_snd (causalExperimentKernel_indepFun P)

/-- Removing the independent treatment mark leaves the potential-pair kernel. -/
-- @node: causalExperimentKernel_map_snd
lemma causalExperimentKernel_map_snd (P : ObsLaw) (x : Set.Icc (0 : ℝ) 1) :
    (causalExperimentKernel P x).map Prod.snd = potentialPairKernel P x := by
  rw [causalExperimentKernel, Kernel.prod_apply, Measure.map_snd_prod, measure_univ, one_smul]

/-- The two potential coordinates remain independent when the treatment mark is included. -/
-- @node: causalExperimentKernel_indepPotentials
lemma causalExperimentKernel_indepPotentials (P : ObsLaw) (x : Set.Icc (0 : ℝ) 1) :
    IndepFun (fun z : Bool × (ℝ × ℝ) => z.2.1) (fun z => z.2.2)
      (causalExperimentKernel P x) := by
  apply (indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)).2
  have h := (potentialPairKernel_indepFun P x).map_prod_eq_prod_map_map
    measurable_fst.aemeasurable measurable_snd.aemeasurable
  rw [← causalExperimentKernel_map_snd P x,
    Measure.map_map measurable_fst measurable_snd,
    Measure.map_map measurable_snd measurable_snd] at h
  change ((causalExperimentKernel P x).map Prod.snd).map id = _ at h
  rw [Measure.map_id] at h
  exact h

/-- The constructed causal completion has independent potential outcomes conditional on X. -/
-- @node: constructedCausalLaw_independentPotentials
lemma constructedCausalLaw_independentPotentials (P : ObsLaw) :
    IndependentPotentials (constructedCausalLaw P) inferInstance := by
  unfold IndependentPotentials
  change CondIndepFun _ _ _ _
    ((causalCovariateLaw ⊗ₘ causalExperimentKernel P).map causalConsistencyMap)
  apply Causalean.Mathlib.Probability.Independence.Conditional.condIndepFun_of_map
    (X := potentialY false) (Y := potentialY true)
    measurable_causalConsistencyMap
    (measurable_fst.comp measurable_snd) (measurable_snd.comp measurable_snd)
    measurable_causalX
  change CondIndepFun
    (MeasurableSpace.comap (fun z : Set.Icc (0 : ℝ) 1 × (Bool × (ℝ × ℝ)) => z.1.val)
      inferInstance) _ ((fun z : Bool × (ℝ × ℝ) => z.2.1) ∘ Prod.snd)
      ((fun z : Bool × (ℝ × ℝ) => z.2.2) ∘ Prod.snd) _
  simp only [causalExperiment_covariate_comap]
  exact causalExperiment_condIndepFun causalCovariateLaw (causalExperimentKernel P)
    _ _ (by fun_prop) (by fun_prop) (causalExperimentKernel_indepPotentials P)

/-- The marginal potential-outcome kernel is the given arm-specific outcome kernel. -/
-- @node: causalExperimentKernel_map_potential
lemma causalExperimentKernel_map_potential (P : ObsLaw) (a : Bool) :
    (causalExperimentKernel P).map (fun z => if a then z.2.2 else z.2.1) =
      conditionalOutcomeKernel P a := by
  cases a
  · change (causalExperimentKernel P).map (Prod.fst ∘ Prod.snd) = _
    rw [Kernel.map_comp_right _ measurable_snd measurable_fst]
    rw [← Kernel.snd_eq, ← Kernel.fst_eq]
    rw [causalExperimentKernel, Kernel.snd_prod, potentialPairKernel, Kernel.fst_prod]
  · change (causalExperimentKernel P).map (Prod.snd ∘ Prod.snd) = _
    rw [Kernel.map_comp_right _ measurable_snd measurable_snd]
    rw [← Kernel.snd_eq, ← Kernel.snd_eq]
    rw [causalExperimentKernel, Kernel.snd_prod, potentialPairKernel, Kernel.snd_prod]

/-- Each arm-specific potential coordinate is a measurable random variable. -/
-- @node: measurable_potentialY
@[fun_prop] lemma measurable_potentialY (a : Bool) : Measurable (potentialY a) := by
  first | fun_prop | (cases a)
  · exact measurable_fst.comp measurable_snd
  · exact measurable_snd.comp measurable_snd

/-- The potential marginal of the constructed law is the design mixture of its outcome kernel. -/
-- @node: constructedCausalLaw_map_potential_mixture
lemma constructedCausalLaw_map_potential_mixture (P : ObsLaw) (a : Bool) :
    (constructedCausalLaw P).map (potentialY a) =
      conditionalOutcomeKernel P a ∘ₘ causalCovariateLaw := by
  have hf : Measurable (fun z : Bool × (ℝ × ℝ) => if a then z.2.2 else z.2.1) := by
    first | fun_prop | (cases a <;> simp only [Bool.false_eq_true, reduceIte] <;> fun_prop)
  have hp : Measurable (potentialY a) := by
    fun_prop
  rw [constructedCausalLaw, Measure.map_map hp measurable_causalConsistencyMap]
  change (causalCovariateLaw ⊗ₘ causalExperimentKernel P).map
    ((fun z : Bool × (ℝ × ℝ) => if a then z.2.2 else z.2.1) ∘ Prod.snd) = _
  rw [← Measure.map_map hf measurable_snd]
  change ((causalCovariateLaw ⊗ₘ causalExperimentKernel P).snd).map _ = _
  rw [Measure.snd_compProd, Measure.map_comp _ _ hf, causalExperimentKernel_map_potential]

/-- Mixing the conditional outcome kernel over the uniform design gives the identified density. -/
-- @node: conditionalOutcomeKernel_mixture
lemma conditionalOutcomeKernel_mixture (P : ObsLaw) (hModel : Model P) (a : Bool) :
    conditionalOutcomeKernel P a ∘ₘ causalCovariateLaw = counterfactualMeasure P a := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  ext D hD
  rw [Measure.bind_apply hD (Kernel.aemeasurable _),
    counterfactualMeasure_apply_eq_mixture P hModel a D hD]
  have hf : Measurable (fun x : ℝ => ENNReal.ofReal (∫ y in D, P.eta a x y ∂unitVolume)) :=
    ((P.eta_measurable a).stronglyMeasurable.integral_prod_right'.measurable).ennreal_ofReal
  have hk (x : Set.Icc (0 : ℝ) 1) : conditionalOutcomeKernel P a x D =
      ENNReal.ofReal (∫ y in D, P.eta a x.val y ∂unitVolume) := by
    rw [conditionalOutcomeKernel_apply, withDensity_apply _ hD,
      ← ofReal_integral_eq_lintegral_ofReal (P.eta_integrable a x.val x.property).integrableOn]
    filter_upwards [(ae_restrict_mem measurableSet_Icc).filter_mono ae_restrict_le] with y hy
    exact P.eta_nonneg a x.val y x.property hy
  simp_rw [hk]
  rw [← lintegral_map hf measurable_subtype_coe, causalCovariateLaw_map_val]
  symm
  apply ofReal_integral_eq_lintegral_ofReal
    ((integrable_eta_joint P hModel a).mono_measure
      (Measure.prod_mono le_rfl Measure.restrict_le_self)).integral_prod_left
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  apply integral_nonneg_of_ae
  filter_upwards [(ae_restrict_mem measurableSet_Icc).filter_mono ae_restrict_le] with y hy
  exact P.eta_nonneg a x y hx hy

/-- The constructed causal law realizes each identified potential-outcome marginal. -/
-- @node: constructedCausalLaw_map_potential
lemma constructedCausalLaw_map_potential (P : ObsLaw) (hModel : Model P) (a : Bool) :
    (constructedCausalLaw P).map (potentialY a) = counterfactualMeasure P a := by
  rw [constructedCausalLaw_map_potential_mixture, conditionalOutcomeKernel_mixture P hModel]

/-- The independent-kernel construction satisfies all existence claims of causal completion. -/
-- @node: independentCausalCompletion_exists
lemma independentCausalCompletion_exists (P : ObsLaw) (hModel : Model P) :
    ∃ Q : Measure CausalSpace, ∃ hQ : IsProbabilityMeasure Q,
      IsCausalExtension P Q ∧ CausalConsistency Q ∧ CausalExchangeability Q hQ ∧
      IndependentPotentials Q hQ ∧ ∀ a, Q.map (potentialY a) = counterfactualMeasure P a := by
  exact ⟨constructedCausalLaw P, inferInstance, constructedCausalLaw_isExtension P,
    constructedCausalLaw_consistency P, constructedCausalLaw_exchangeability P,
    constructedCausalLaw_independentPotentials P, constructedCausalLaw_map_potential P hModel⟩

end CausalSmith.Stat.DensityEffectRoughNull
