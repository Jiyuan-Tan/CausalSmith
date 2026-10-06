module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.CausalIndependence

/-!
Identification bridges for arbitrary consistent exchangeable extensions. Arm masking retains
exactly the observed information for one potential, and a positive treatment mass lets one
recover its distribution from the masked independent product law.
-/

public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- Every causal extension has the same covariate marginal as the observed law. -/
-- @node: causalExtension_map_causalX
lemma causalExtension_map_causalX (P : ObsLaw) (Q : Measure CausalSpace)
    (hExt : IsCausalExtension P Q) : Q.map causalX = P.law.map X := by
  rw [← hExt.2.1, Measure.map_map (by fun_prop [X]) measurable_fst]
  rfl

/-- Exchangeability of the pair implies exchangeability of either potential coordinate. -/
-- @node: causalExchangeability_potential
lemma causalExchangeability_potential (Q : Measure CausalSpace)
    (hQ : IsProbabilityMeasure Q) (hEx : CausalExchangeability Q hQ) (a : Bool) :
    letI : IsProbabilityMeasure Q := hQ
    CondIndepFun (MeasurableSpace.comap causalX inferInstance) measurable_causalX.comap_le
      (fun o : CausalSpace => A o.1) (potentialY a) Q := by
  letI := hQ
  have hf : Measurable (fun z : ℝ × ℝ => if a then z.2 else z.1) := by
    cases a <;> simp only [Bool.false_eq_true, reduceIte] <;> fun_prop
  exact hEx.comp measurable_id hf

/-- For conditionally independent variables, the joint conditional kernel is their product. -/
-- @node: condDistrib_pair_of_condIndep
lemma condDistrib_pair_of_condIndep
    {S E F G : Type*} [MeasurableSpace S] [StandardBorelSpace S] [MeasurableSpace E]
    [MeasurableSpace F] [StandardBorelSpace F] [Nonempty F]
    [MeasurableSpace G] [StandardBorelSpace G] [Nonempty G]
    (μ : Measure S) [IsFiniteMeasure μ] (x : S → E) (f : S → F) (g : S → G)
    (hx : Measurable x) (hf : Measurable f) (hg : Measurable g)
    (hi : CondIndepFun (MeasurableSpace.comap x inferInstance) hx.comap_le f g μ) :
    condDistrib (fun z => (f z, g z)) x μ =ᵐ[μ.map x]
      condDistrib f x μ ×ₖ condDistrib g x μ := by
  apply condDistrib_ae_eq_of_measure_eq_compProd_of_measurable hx (hf.prodMk hg)
  rw [Measure.compProd_eq_comp_prod]
  exact (condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib hf hg hx).1 hi

/-- Equal covariate/joint laws have identical conditional kernels. -/
-- @node: condDistrib_eq_of_joint_map_eq
lemma condDistrib_eq_of_joint_map_eq
    {S T E F : Type*} [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace E]
    [MeasurableSpace F] [StandardBorelSpace F] [Nonempty F]
    (μ : Measure S) (ν : Measure T) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (x : S → E) (y : T → E) (f : S → F) (g : T → F)
    (hx : Measurable x) (hy : Measurable y) (hf : Measurable f) (hg : Measurable g)
    (hbase : μ.map x = ν.map y)
    (hjoint : μ.map (fun z => (x z, f z)) = ν.map (fun z => (y z, g z))) :
    condDistrib f x μ =ᵐ[μ.map x] condDistrib g y ν := by
  apply condDistrib_ae_eq_of_measure_eq_compProd_of_measurable hx hf
  rw [hbase, compProd_map_condDistrib hg.aemeasurable, hjoint]

/-- Consistency makes a masked potential record an observable function of the data. -/
-- @node: causalConsistency_masked_joint
lemma causalConsistency_masked_joint (P : ObsLaw) (Q : Measure CausalSpace)
    (hExt : IsCausalExtension P Q) (hCons : CausalConsistency Q) (a : Bool) :
    Q.map (fun o => (causalX o, A o.1, if A o.1 = a then potentialY a o else 0)) =
      P.law.map (fun o => (X o, A o, if A o = a then Y o else 0)) := by
  have hm : Measurable (fun o : Omega => (X o, A o, if A o = a then Y o else 0)) := by
    apply (by fun_prop [X] : Measurable X).prodMk
    apply (by fun_prop [A] : Measurable A).prodMk
    exact (by fun_prop [Y] : Measurable Y).ite
      ((measurableSet_singleton a).preimage (by fun_prop [A])) measurable_const
  rw [← hExt.2.1, Measure.map_map hm measurable_fst]
  apply Measure.map_congr
  filter_upwards [hCons] with o ho
  dsimp [Function.comp_def, causalX]
  by_cases ha : A o.1 = a
  · rw [ha] at ho
    simp [ha, ho]
  · simp [ha]

/-- The binary arm mask is measurable. -/
-- @node: measurable_armMaskedPair
@[fun_prop] lemma measurable_armMaskedPair (a : Bool) :
    Measurable (fun z : Bool × ℝ => (z.1, if z.1 = a then z.2 else 0)) := by
  first | fun_prop | skip
  exact measurable_fst.prodMk (measurable_snd.ite
    ((measurableSet_singleton a).preimage measurable_fst) measurable_const)

/-- The conditional masked record of an exchangeable extension is a masked product kernel. -/
-- @node: causalExchangeability_masked_kernel
lemma causalExchangeability_masked_kernel (Q : Measure CausalSpace)
    (hQ : IsProbabilityMeasure Q) (hEx : CausalExchangeability Q hQ) (a : Bool) :
    letI : IsProbabilityMeasure Q := hQ
    condDistrib (fun o => (A o.1, if A o.1 = a then potentialY a o else 0)) causalX Q
      =ᵐ[Q.map causalX]
      (condDistrib (fun o : CausalSpace => A o.1) causalX Q ×ₖ
        condDistrib (potentialY a) causalX Q).map
          (fun z => (z.1, if z.1 = a then z.2 else 0)) := by
  letI := hQ
  have hpair := condDistrib_pair_of_condIndep Q causalX (fun o => A o.1)
    (potentialY a) measurable_causalX (by fun_prop [A]) (by fun_prop)
    (causalExchangeability_potential Q hQ hEx a)
  have hmap := condDistrib_comp (μ := Q) (mβ := inferInstance) causalX
    ((by fun_prop [A] : Measurable (fun o : CausalSpace => (A o.1, potentialY a o))).aemeasurable)
    (measurable_armMaskedPair a)
  filter_upwards [hpair, hmap] with x hp hm
  simp only [Function.comp_def] at hm
  rw [hm, Kernel.map_apply _ (measurable_armMaskedPair a), hp,
    Kernel.map_apply _ (measurable_armMaskedPair a)]

/-- The treatment/covariate joint law is fixed by the observed marginal. -/
-- @node: causalExtension_treatment_joint
lemma causalExtension_treatment_joint (P : ObsLaw) (Q : Measure CausalSpace)
    (hExt : IsCausalExtension P Q) :
    Q.map (fun o => (causalX o, A o.1)) = P.law.map (fun o => (X o, A o)) := by
  rw [← hExt.2.1, Measure.map_map (by fun_prop [X, A]) measurable_fst]
  rfl

/-- Two extensions of the same observed law have exactly the same treatment conditional kernel. -/
-- @node: causalExtensions_treatment_kernel_eq
lemma causalExtensions_treatment_kernel_eq (P : ObsLaw) (Q R : Measure CausalSpace)
    (hQ : IsProbabilityMeasure Q) (hR : IsProbabilityMeasure R)
    (hExtQ : IsCausalExtension P Q) (hExtR : IsCausalExtension P R) :
    letI : IsProbabilityMeasure Q := hQ
    letI : IsProbabilityMeasure R := hR
    condDistrib (fun o : CausalSpace => A o.1) causalX Q =
      condDistrib (fun o : CausalSpace => A o.1) causalX R := by
  letI := hQ
  letI := hR
  simp only [condDistrib_def, causalExtension_treatment_joint P Q hExtQ,
    causalExtension_treatment_joint P R hExtR]

/-- Consistent extensions of the same observed law have the same masked conditional kernel. -/
-- @node: causalExtensions_masked_kernel_eq
lemma causalExtensions_masked_kernel_eq (P : ObsLaw) (Q R : Measure CausalSpace)
    (hQ : IsProbabilityMeasure Q) (hR : IsProbabilityMeasure R)
    (hExtQ : IsCausalExtension P Q) (hExtR : IsCausalExtension P R)
    (hConsQ : CausalConsistency Q) (hConsR : CausalConsistency R) (a : Bool) :
    letI : IsProbabilityMeasure Q := hQ
    letI : IsProbabilityMeasure R := hR
    condDistrib (fun o => (A o.1, if A o.1 = a then potentialY a o else 0)) causalX Q =
      condDistrib (fun o => (A o.1, if A o.1 = a then potentialY a o else 0)) causalX R := by
  letI := hQ
  letI := hR
  simp only [condDistrib_def, causalConsistency_masked_joint P Q hExtQ hConsQ,
    causalConsistency_masked_joint P R hExtR hConsR]

/-- Masking an independent product leaves the original outcome law on the selected arm. -/
-- @node: masked_product_apply_arm
lemma masked_product_apply_arm (τ : Measure Bool) (ν : Measure ℝ)
    [IsFiniteMeasure τ] [IsFiniteMeasure ν] (a : Bool) (D : Set ℝ)
    (hD : MeasurableSet D) :
    ((τ.prod ν).map (fun z => (z.1, if z.1 = a then z.2 else 0))) ({a} ×ˢ D) =
      τ {a} * ν D := by
  have hm : Measurable (fun z : Bool × ℝ => (z.1, if z.1 = a then z.2 else 0)) := by
    exact measurable_fst.prodMk (measurable_snd.ite
      ((measurableSet_singleton a).preimage measurable_fst) measurable_const)
  rw [Measure.map_apply hm ((measurableSet_singleton a).prod hD)]
  have hpre : (fun z : Bool × ℝ => (z.1, if z.1 = a then z.2 else 0)) ⁻¹'
      ({a} ×ˢ D) = {a} ×ˢ D := by
    ext z
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff]
    by_cases ha : z.1 = a <;> simp [ha]
  rw [hpre, Measure.prod_prod]

/-- A nonzero arm probability identifies the independent outcome law from masked records. -/
-- @node: masked_product_identifies
lemma masked_product_identifies (τ : Measure Bool) (ν ν' : Measure ℝ)
    [IsFiniteMeasure τ] [IsFiniteMeasure ν] [IsFiniteMeasure ν'] (a : Bool)
    (ha : τ {a} ≠ 0)
    (h : (τ.prod ν).map (fun z => (z.1, if z.1 = a then z.2 else 0)) =
      (τ.prod ν').map (fun z => (z.1, if z.1 = a then z.2 else 0))) : ν = ν' := by
  ext D hD
  have he := congrArg (fun ρ : Measure (Bool × ℝ) => ρ ({a} ×ˢ D)) h
  rw [masked_product_apply_arm τ ν a D hD,
    masked_product_apply_arm τ ν' a D hD] at he
  exact (ENNReal.mul_left_inj ha (measure_ne_top τ _)).1 (by simpa [mul_comm] using he)

/-- Positive conditional arm mass identifies a potential marginal across any two completions. -/
-- @node: causalExtensions_potential_eq_of_positive_arm
lemma causalExtensions_potential_eq_of_positive_arm (P : ObsLaw) (Q R : Measure CausalSpace)
    (hQ : IsProbabilityMeasure Q) (hR : IsProbabilityMeasure R)
    (hExtQ : IsCausalExtension P Q) (hExtR : IsCausalExtension P R)
    (hConsQ : CausalConsistency Q) (hConsR : CausalConsistency R)
    (hExQ : CausalExchangeability Q hQ) (hExR : CausalExchangeability R hR) (a : Bool)
    (hpos : letI : IsProbabilityMeasure Q := hQ
      ∀ᵐ x ∂Q.map causalX, condDistrib (fun o : CausalSpace => A o.1) causalX Q x {a} ≠ 0) :
    Q.map (potentialY a) = R.map (potentialY a) := by
  letI := hQ
  letI := hR
  have hbase : Q.map causalX = R.map causalX := by
    rw [causalExtension_map_causalX P Q hExtQ, causalExtension_map_causalX P R hExtR]
  have hRmask := causalExchangeability_masked_kernel R hR hExR a
  rw [← hbase] at hRmask
  have hkern : condDistrib (potentialY a) causalX Q =ᵐ[Q.map causalX]
      condDistrib (potentialY a) causalX R := by
    filter_upwards [causalExchangeability_masked_kernel Q hQ hExQ a, hRmask, hpos]
      with x hxQ hxR hxpos
    have he : ((condDistrib (fun o : CausalSpace => A o.1) causalX Q x).prod
          (condDistrib (potentialY a) causalX Q x)).map
          (fun z => (z.1, if z.1 = a then z.2 else 0)) =
        ((condDistrib (fun o : CausalSpace => A o.1) causalX Q x).prod
          (condDistrib (potentialY a) causalX R x)).map
          (fun z => (z.1, if z.1 = a then z.2 else 0)) := by
      have hh := hxQ.symm.trans ((congrArg (fun κ : Kernel ℝ (Bool × ℝ) => κ x)
        (causalExtensions_masked_kernel_eq P Q R hQ hR hExtQ hExtR hConsQ hConsR a)).trans hxR)
      simp only [Kernel.map_apply _ (measurable_armMaskedPair a), Kernel.prod_apply] at hh
      rwa [← causalExtensions_treatment_kernel_eq P Q R hQ hR hExtQ hExtR] at hh
    exact masked_product_identifies _ _ _ a hxpos he
  rw [← condDistrib_comp_map measurable_causalX.aemeasurable
      (measurable_potentialY a).aemeasurable,
    ← condDistrib_comp_map measurable_causalX.aemeasurable
      (measurable_potentialY a).aemeasurable, ← hbase]
  exact Measure.comp_congr hkern

/-- Treatment rectangles of the constructed law integrate the prescribed arm probabilities. -/
-- @node: constructedCausalLaw_treatment_rectangle
lemma constructedCausalLaw_treatment_rectangle (P : ObsLaw) (B : Set ℝ)
    (hB : MeasurableSet B) (a : Bool) :
    ((constructedCausalLaw P).map (fun o => (causalX o, A o.1))) (B ×ˢ {a}) =
      ∫⁻ x in Subtype.val ⁻¹' B, causalTreatmentKernel P x {a} ∂causalCovariateLaw := by
  rw [constructedCausalLaw, Measure.map_map (by fun_prop [causalX, X, A])
    measurable_causalConsistencyMap]
  rw [Measure.map_apply (by fun_prop [causalConsistencyMap, causalX, X, A])
    (hB.prod (measurableSet_singleton a))]
  have hpre : ((fun o : CausalSpace => (causalX o, A o.1)) ∘ causalConsistencyMap) ⁻¹'
      (B ×ˢ {a}) = (Subtype.val ⁻¹' B) ×ˢ ({a} ×ˢ Set.univ) := by
    ext z
    simp [Function.comp_def, causalConsistencyMap, causalX, X, A]
  rw [hpre, Measure.compProd_apply_prod (hB.preimage measurable_subtype_coe)
    ((measurableSet_singleton a).prod MeasurableSet.univ)]
  simp only [causalExperimentKernel, Kernel.prod_apply_prod, measure_univ, mul_one]

/-- Model overlap makes both singleton masses strictly positive in the treatment kernel. -/
-- @node: causalTreatmentKernel_singleton_ne_zero
lemma causalTreatmentKernel_singleton_ne_zero (P : ObsLaw) (hModel : Model P)
    (x : Set.Icc (0 : ℝ) 1) (a : Bool) : causalTreatmentKernel P x {a} ≠ 0 := by
  rw [causalTreatmentKernel_apply_singleton]
  apply ne_of_gt
  apply ENNReal.ofReal_pos.mpr
  have he := hModel.overlap x.val x.property
  cases a <;> simp only [pi, armProbability, Bool.false_eq_true, reduceIte] <;>
    linarith [he.1, he.2]

/-- Positivity is inherited by every extension's conditional treatment law, without an added premise. -/
-- @node: causalExtension_conditional_arm_ne_zero
lemma causalExtension_conditional_arm_ne_zero (P : ObsLaw) (hModel : Model P)
    (Q : Measure CausalSpace) (hQ : IsProbabilityMeasure Q)
    (hExt : IsCausalExtension P Q) (a : Bool) :
    letI : IsProbabilityMeasure Q := hQ
    ∀ᵐ x ∂Q.map causalX, condDistrib (fun o : CausalSpace => A o.1) causalX Q x {a} ≠ 0 := by
  letI := hQ
  let κ := condDistrib (fun o : CausalSpace => A o.1) causalX Q
  let Z : Set ℝ := {x | κ x {a} = 0}
  have hZ : MeasurableSet Z := (Kernel.measurable_coe κ (measurableSet_singleton a))
    (measurableSet_singleton 0)
  have hz : (Q.map (fun o => (causalX o, A o.1))) (Z ×ˢ {a}) = 0 := by
    rw [← compProd_map_condDistrib (by fun_prop [A]),
      Measure.compProd_apply_prod hZ (measurableSet_singleton a)]
    apply lintegral_eq_zero_iff (Kernel.measurable_coe κ (measurableSet_singleton a)) |>.2
    filter_upwards [ae_restrict_mem hZ] with x hx
    exact hx
  have hjoint : Q.map (fun o => (causalX o, A o.1)) =
      (constructedCausalLaw P).map (fun o => (causalX o, A o.1)) := by
    rw [causalExtension_treatment_joint P Q hExt,
      causalExtension_treatment_joint P _ (constructedCausalLaw_isExtension P)]
  rw [hjoint, constructedCausalLaw_treatment_rectangle P Z hZ a] at hz
  have hzker := (lintegral_eq_zero_iff
    (Kernel.measurable_coe (causalTreatmentKernel P) (measurableSet_singleton a))).1 hz
  have hn : ∀ᵐ x ∂causalCovariateLaw, x.val ∉ Z := by
    filter_upwards [ae_imp_of_ae_restrict hzker] with x hx
    intro hxZ
    exact causalTreatmentKernel_singleton_ne_zero P hModel x a (hx hxZ)
  rw [causalExtension_map_causalX P Q hExt, hModel.design,
    ← causalCovariateLaw_map_val]
  exact (ae_map_iff measurable_subtype_coe.aemeasurable hZ.compl).2 hn

/-- All consistent exchangeable extensions have the constructed potential marginals. -/
-- @node: causalExtension_map_potential
lemma causalExtension_map_potential (P : ObsLaw) (hModel : Model P)
    (Q : Measure CausalSpace) (hQ : IsProbabilityMeasure Q)
    (hExt : IsCausalExtension P Q) (hCons : CausalConsistency Q)
    (hEx : CausalExchangeability Q hQ) (a : Bool) :
    Q.map (potentialY a) = counterfactualMeasure P a := by
  rw [← constructedCausalLaw_map_potential P hModel a]
  exact causalExtensions_potential_eq_of_positive_arm P Q (constructedCausalLaw P) hQ
    inferInstance hExt (constructedCausalLaw_isExtension P) hCons
    (constructedCausalLaw_consistency P) hEx (constructedCausalLaw_exchangeability P) a
    (causalExtension_conditional_arm_ne_zero P hModel Q hQ hExt a)

end CausalSmith.Stat.DensityEffectRoughNull
