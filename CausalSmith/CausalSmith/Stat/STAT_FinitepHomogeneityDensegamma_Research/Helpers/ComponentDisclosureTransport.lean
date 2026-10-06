module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ComponentRecordTransport
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ComponentTotalVariation

/-! Measure-level averaging of the finite boundary disclosure and full labels. -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- Finite disclosure averaging commutes with conversion of nonnegative densities into extended nonnegative masses. No analytic integrability premise is needed. This statement assumes [the hf condition](hyp:hf). [This is the stated conclusion](goal). -/
-- @node: lintegral_disclosure_ofReal
lemma lintegral_disclosure_ofReal (K M : ℕ) (f : Disclosure K → ℝ)
    (hf : ∀ δ, 0 ≤ f δ) :
    (∫⁻ δ, ENNReal.ofReal (f δ) ∂disclosureLaw K M) =
      ENNReal.ofReal (∫ δ, f δ ∂disclosureLaw K M) := by
  rw [integral_disclosureLaw]
  unfold disclosureLaw
  rw [lintegral_finsetSum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  rw [ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_sum_of_nonneg (fun q _ => hf (disclose K M q)), Finset.mul_sum]

/-- Averaging the full finite label measure over disclosure can be performed one label at a time, retaining also the unused sign in a zero mark. This statement assumes [the hf condition](hyp:hf). [This is the stated conclusion](goal). -/
-- @node: fairLabelMeasure_bind_disclosure
lemma fairLabelMeasure_bind_disclosure (n K M : ℕ)
    (f : Disclosure K → Labels n → ℝ) (hf : ∀ δ l, 0 ≤ f δ l) :
    (disclosureLaw K M).bind (fun δ => fairLabelMeasure n (f δ)) =
      fairLabelMeasure n (fun l => ∫ δ, f δ l ∂disclosureLaw K M) := by
  classical
  ext s hs
  rw [Measure.bind_apply hs (measurable_of_finite _).aemeasurable]
  simp only [fairLabelMeasure, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.smul_apply, smul_eq_mul]
  rw [lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro l _
    simp_rw [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (4:ℝ)^(-(n:ℤ)))]
    rw [lintegral_mul_const _ _, lintegral_const_mul _ _,
      lintegral_disclosure_ofReal K M _ (fun δ => hf δ l)] <;>
      exact measurable_of_finite _
  · intro l _
    exact measurable_of_finite _

/-- Disclosure averaging recovers the original null full-label likelihood as an actual measure, rather than merely an identity of real densities. This statement assumes [the hK condition](hyp:hK), [the hM condition](hyp:hM), [the hdiv condition](hyp:hdiv), [the heven condition](hyp:heven), [the ha condition](hyp:ha), [the hu condition](hyp:hu). [This is the stated conclusion](goal). -/
-- @node: nullConditionalLaw_bind_disclosure
lemma nullConditionalLaw_bind_disclosure (n K M : ℕ) (a u : ℝ)
    (hK : 0 < K) (hM : 0 < M) (hdiv : M ∣ K) (heven : 2 ∣ M)
    (ha : 0 < a ∧ a ≤ 1 / 16) (hu : 0 < u ∧ u ≤ 1 / 16)
    (xs : Fin n → unitInterval) (marks : Fin n → Bool) :
    (disclosureLaw K M).bind (fun δ => nullConditionalLaw n K M a u (xs,marks,δ)) =
      fairLabelMeasure n (fun labels => ∑ idx : CopulaIndex K M,
        copulaWeight false K M idx *
          ∏ i : Fin n, labelDensity false K M a u idx (xs i) (marks i) (labels i)) := by
  change (disclosureLaw K M).bind (fun δ =>
    fairLabelMeasure n (nullConditionalDensity n K M a u (xs,marks,δ))) = _
  rw [fairLabelMeasure_bind_disclosure]
  · congr 1
    funext labels
    exact nullConditionalDensity_integral_disclosure n K M a u hK hM hdiv heven xs marks labels
  · intro δ labels
    unfold nullConditionalDensity
    apply Finset.prod_nonneg
    intro C _
    exact le_trans (by positivity)
      (component_denominator_bounds n K M a u hK ha hu (xs,marks,δ) C labels).1

/-- The alternative has the same measure-level transport, with each undisclosed coarse sign still averaged according to the original copula prior. This statement assumes [the hK condition](hyp:hK), [the ha condition](hyp:ha), [the hu condition](hyp:hu). [This is the stated conclusion](goal). -/
-- @node: alternativeConditionalLaw_bind_disclosure
lemma alternativeConditionalLaw_bind_disclosure (n K M : ℕ) (a u : ℝ)
    (hK : 0 < K) (ha : 0 < a ∧ a ≤ 1 / 16) (hu : 0 < u ∧ u ≤ 1 / 16)
    (xs : Fin n → unitInterval) (marks : Fin n → Bool) :
    (disclosureLaw K M).bind (fun δ => alternativeConditionalLaw n K M a u (xs,marks,δ)) =
      fairLabelMeasure n (fun labels => ∑ idx : CopulaIndex K M,
        copulaWeight true K M idx *
          ∏ i : Fin n, labelDensity true K M a u idx (xs i) (marks i) (labels i)) := by
  change (disclosureLaw K M).bind (fun δ =>
    fairLabelMeasure n (alternativeConditionalDensity n K M a u (xs,marks,δ))) = _
  rw [fairLabelMeasure_bind_disclosure]
  · congr 1
    funext labels
    exact alternativeConditionalDensity_integral_disclosure n K M a u hK xs marks labels
  · intro δ labels
    exact alternativeConditionalDensity_nonneg n K M a u hK ha hu (xs,marks,δ) labels

/-- Forgetting a finite disclosure after sampling labels is equivalent to averaging its conditional label law first. The observation retains the design and marks. This statement assumes [the hε condition](hyp:hε), [the hf condition](hyp:hf). [This is the stated conclusion](goal). -/
-- @node: projected_disclosure_compProd
lemma projected_disclosure_compProd (n K M : ℕ) (ε L : ℝ)
    (hε : 0 ≤ ε ∧ ε ≤ 1) (P : Kernel (Augmentation n K) (Labels n))
    [IsSFiniteKernel P]
    (hf : Measurable (fun xm : (Fin n → unitInterval) × (Fin n → Bool) =>
      ((disclosureLaw K M).bind (fun δ => P (xm.1,xm.2,δ))).map
        (fun labels => fun i =>
          (xm.1 i,(labels i).1,if xm.2 i then signVal (labels i).2*L else 0)))) :
    (commonAugmentation n K M ε ⊗ₘ P).map (augmentedObserve n K L) =
      ((Measure.pi fun _ : Fin n => design).prod
        (Measure.pi fun _ : Fin n => markFlagLaw ε)).bind
        (fun xm => ((disclosureLaw K M).bind (fun δ => P (xm.1,xm.2,δ))).map
          (fun labels => fun i =>
            (xm.1 i,(labels i).1,if xm.2 i then signVal (labels i).2*L else 0))) := by
  classical
  let : IsProbabilityMeasure design := by unfold design; infer_instance
  let : IsProbabilityMeasure (markFlagLaw ε) := markFlagLaw_probability ε hε.1 hε.2
  let : IsProbabilityMeasure (disclosureLaw K M) := disclosureLaw_probability K M
  let : IsProbabilityMeasure (commonAugmentation n K M ε) := by
    unfold commonAugmentation
    infer_instance
  have ho : Measurable (augmentedObserve n K L) := measurable_augmentedObserve n K L
  ext s hs
  rw [Measure.map_apply ho hs, Measure.compProd_apply (hs.preimage ho),
    Measure.bind_apply hs hf.aemeasurable]
  have hg : Measurable (fun aug : Augmentation n K =>
      P aug (Prod.mk aug ⁻¹' (augmentedObserve n K L ⁻¹' s))) :=
    P.measurable_kernel_prodMk_left (hs.preimage ho)
  have hj := (Measure.measurable_coe hs).comp hf
  dsimp only [Function.comp_def] at hj
  rw [commonAugmentation, lintegral_prod _ hg.aemeasurable,
    lintegral_prod _ hj.aemeasurable]
  apply lintegral_congr
  intro xs
  have hi := hg.comp (measurable_prodMk_left (x := xs))
  dsimp only [Function.comp_def] at hi
  rw [lintegral_prod _ hi.aemeasurable]
  apply lintegral_congr
  intro marks
  rw [Measure.map_apply (by fun_prop) hs,
    Measure.bind_apply (hs.preimage (by fun_prop)) (measurable_of_finite _).aemeasurable]
  rfl

/-- The prior-averaged full-label law, pushed to the original records, varies measurably with the common design and mark flags. [This is the stated conclusion](goal). -/
-- @node: measurable_prior_label_observation
@[fun_prop] lemma measurable_prior_label_observation (ν : Bool) (n K M : ℕ) (a u L : ℝ) :
    Measurable (fun xm : (Fin n → unitInterval) × (Fin n → Bool) =>
      (fairLabelMeasure n (fun labels => ∑ idx : CopulaIndex K M,
        copulaWeight ν K M idx *
          ∏ i : Fin n, labelDensity ν K M a u idx (xm.1 i) (xm.2 i) (labels i))).map
        (fun labels => fun i =>
          (xm.1 i,(labels i).1,if xm.2 i then signVal (labels i).2*L else 0))) := by
  classical
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [Measure.map_apply (measurable_of_finite _) hs, fairLabelMeasure,
    Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
  simp_rw [Measure.dirac_apply' _ (hs.preimage (measurable_of_finite _))]
  apply Finset.measurable_sum
  intro labels _
  have hd : Measurable (fun xm : (Fin n → unitInterval) × (Fin n → Bool) =>
      ∑ idx : CopulaIndex K M, copulaWeight ν K M idx *
        ∏ i : Fin n, labelDensity ν K M a u idx (xm.1 i) (xm.2 i) (labels i)) := by
    fun_prop
  have ho : Measurable (fun xm : (Fin n → unitInterval) × (Fin n → Bool) =>
      fun i => (xm.1 i,(labels i).1,if xm.2 i then signVal (labels i).2*L else 0)) := by
    exact (measurable_augmentedObserve n K L).comp
      (show Measurable (fun xm : (Fin n → unitInterval) × (Fin n → Bool) =>
        (((xm.1,xm.2,fun _ => none) : Augmentation n K),labels)) by fun_prop)
  have hmem := hs.preimage ho
  exact (ENNReal.measurable_ofReal.comp (hd.const_mul ((4:ℝ)^(-(n:ℤ))))).mul
    (Measurable.ite hmem measurable_const measurable_const)

/-- The null augmented experiment projects to the common design/mark mixture of the original prior-averaged label measures, with disclosure completely integrated out. This statement assumes [the hK condition](hyp:hK), [the hM condition](hyp:hM), [the hdiv condition](hyp:hdiv), [the heven condition](hyp:heven), [the ha condition](hyp:ha), [the hu condition](hyp:hu), [the hε condition](hyp:hε), [the hP condition](hyp:hP). [This is the stated conclusion](goal). -/
-- @node: null_augmented_projection_label_bind
lemma null_augmented_projection_label_bind (n K M : ℕ) (a u ε L : ℝ)
    (hK : 0 < K) (hM : 0 < M) (hdiv : M ∣ K) (heven : 2 ∣ M)
    (ha : 0 < a ∧ a ≤ 1 / 16) (hu : 0 < u ∧ u ≤ 1 / 16) (hε : 0 ≤ ε ∧ ε ≤ 1)
    (P : Kernel (Augmentation n K) (Labels n)) [IsSFiniteKernel P]
    (hP : ∀ aug, P aug = nullConditionalLaw n K M a u aug) :
    (commonAugmentation n K M ε ⊗ₘ P).map (augmentedObserve n K L) =
      ((Measure.pi fun _ : Fin n => design).prod
        (Measure.pi fun _ : Fin n => markFlagLaw ε)).bind (fun xm =>
          (fairLabelMeasure n (fun labels => ∑ idx : CopulaIndex K M,
            copulaWeight false K M idx *
              ∏ i : Fin n, labelDensity false K M a u idx (xm.1 i) (xm.2 i) (labels i))).map
            (fun labels => fun i =>
              (xm.1 i,(labels i).1,if xm.2 i then signVal (labels i).2*L else 0))) := by
  have havg (xm : (Fin n → unitInterval) × (Fin n → Bool)) :
      (disclosureLaw K M).bind (fun δ => P (xm.1,xm.2,δ)) =
        fairLabelMeasure n (fun labels => ∑ idx : CopulaIndex K M,
          copulaWeight false K M idx *
            ∏ i : Fin n, labelDensity false K M a u idx (xm.1 i) (xm.2 i) (labels i)) := by
    simp_rw [hP]
    exact nullConditionalLaw_bind_disclosure n K M a u hK hM hdiv heven ha hu xm.1 xm.2
  have hf : Measurable (fun xm : (Fin n → unitInterval) × (Fin n → Bool) =>
      ((disclosureLaw K M).bind (fun δ => P (xm.1,xm.2,δ))).map
        (fun labels => fun i =>
          (xm.1 i,(labels i).1,if xm.2 i then signVal (labels i).2*L else 0))) := by
    simp_rw [havg]
    exact measurable_prior_label_observation false n K M a u L
  rw [projected_disclosure_compProd n K M ε L hε P hf]
  simp_rw [havg]

/-- The same projection identity holds for the alternative without disclosing or removing any coarse sign from its original prior average. This statement assumes [the hK condition](hyp:hK), [the ha condition](hyp:ha), [the hu condition](hyp:hu), [the hε condition](hyp:hε), [the hP condition](hyp:hP). [This is the stated conclusion](goal). -/
-- @node: alternative_augmented_projection_label_bind
lemma alternative_augmented_projection_label_bind (n K M : ℕ) (a u ε L : ℝ)
    (hK : 0 < K) (ha : 0 < a ∧ a ≤ 1 / 16) (hu : 0 < u ∧ u ≤ 1 / 16)
    (hε : 0 ≤ ε ∧ ε ≤ 1) (P : Kernel (Augmentation n K) (Labels n)) [IsSFiniteKernel P]
    (hP : ∀ aug, P aug = alternativeConditionalLaw n K M a u aug) :
    (commonAugmentation n K M ε ⊗ₘ P).map (augmentedObserve n K L) =
      ((Measure.pi fun _ : Fin n => design).prod
        (Measure.pi fun _ : Fin n => markFlagLaw ε)).bind (fun xm =>
          (fairLabelMeasure n (fun labels => ∑ idx : CopulaIndex K M,
            copulaWeight true K M idx *
              ∏ i : Fin n, labelDensity true K M a u idx (xm.1 i) (xm.2 i) (labels i))).map
            (fun labels => fun i =>
              (xm.1 i,(labels i).1,if xm.2 i then signVal (labels i).2*L else 0))) := by
  have havg (xm : (Fin n → unitInterval) × (Fin n → Bool)) :
      (disclosureLaw K M).bind (fun δ => P (xm.1,xm.2,δ)) =
        fairLabelMeasure n (fun labels => ∑ idx : CopulaIndex K M,
          copulaWeight true K M idx *
            ∏ i : Fin n, labelDensity true K M a u idx (xm.1 i) (xm.2 i) (labels i)) := by
    simp_rw [hP]
    exact alternativeConditionalLaw_bind_disclosure n K M a u hK ha hu xm.1 xm.2
  have hf : Measurable (fun xm : (Fin n → unitInterval) × (Fin n → Bool) =>
      ((disclosureLaw K M).bind (fun δ => P (xm.1,xm.2,δ))).map
        (fun labels => fun i =>
          (xm.1 i,(labels i).1,if xm.2 i then signVal (labels i).2*L else 0))) := by
    simp_rw [havg]
    exact measurable_prior_label_observation true n K M a u L
  rw [projected_disclosure_compProd n K M ε L hε P hf]
  simp_rw [havg]

/-- The iid mark flags enumerate every flag vector with its independent Bernoulli mass. This statement assumes [the hε condition](hyp:hε). [This is the stated conclusion](goal). -/
-- @node: markFlagLaw_pi_atomic
lemma markFlagLaw_pi_atomic (n : ℕ) (ε : ℝ) (hε : 0 ≤ ε ∧ ε ≤ 1) :
    Measure.pi (fun _ : Fin n => markFlagLaw ε) =
      ∑ marks : Fin n → Bool,
        (∏ i, ENNReal.ofReal (if marks i then ε else 1-ε)) • Measure.dirac marks := by
  classical
  have hf : markFlagLaw ε = ∑ b : Bool,
      ENNReal.ofReal (if b then ε else 1-ε) • Measure.dirac b := by
    simp [markFlagLaw, Fintype.sum_bool]
  let : IsProbabilityMeasure (markFlagLaw ε) := markFlagLaw_probability ε hε.1 hε.2
  let : ∀ i : Fin n, IsProbabilityMeasure (∑ b : Bool,
      ENNReal.ofReal (if b then ε else 1-ε) • Measure.dirac b) := fun _ => by rw [← hf]; infer_instance
  rw [hf]
  exact record_pi_finite_atomic _ _

/-- Binding a measurable finite family of measures commutes with its finite sum. This statement assumes [the hf condition](hyp:hf). [This is the stated conclusion](goal). -/
-- @node: record_bind_finite_sum
lemma record_bind_finite_sum {X Ω J : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    [Fintype J] (μ : Measure X) (f : J → X → Measure Ω)
    (hf : ∀ j, Measurable (f j)) :
    μ.bind (fun x => ∑ j, f j x) = ∑ j, μ.bind (f j) := by
  classical
  ext s hs
  rw [Measure.bind_apply hs (Finset.measurable_sum _ (fun j _ => hf j)).aemeasurable]
  simp only [Measure.coe_finsetSum, Finset.sum_apply]
  rw [lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    exact (Measure.bind_apply hs (hf j).aemeasurable).symm
  · intro j _
    exact (Measure.measurable_coe hs).comp (hf j)

/-- A constant finite mass can be pulled out of the conditional sampling bind. This statement assumes [the c condition](hyp:c), [the hf condition](hyp:hf). [This is the stated conclusion](goal). -/
-- @node: record_bind_const_smul
lemma record_bind_const_smul {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    (μ : Measure X) (c : ℝ≥0∞) (f : X → Measure Ω) (hf : Measurable f) :
    μ.bind (fun x => c • f x) = c • μ.bind f := by
  ext s hs
  have hg : Measurable (fun x => c • f x) := by
    apply Measure.measurable_of_measurable_coe
    intro t ht
    exact measurable_const.mul ((Measure.measurable_coe ht).comp hf)
  rw [Measure.bind_apply hs hg.aemeasurable,
    Measure.smul_apply, Measure.bind_apply hs hf.aemeasurable]
  simp only [Measure.smul_apply, smul_eq_mul]
  exact lintegral_const_mul c ((Measure.measurable_coe hs).comp hf)

/-- Every original copula prior mass is nonnegative, including each coarse-sign draw. [This is the stated conclusion](goal). -/
-- @node: copulaWeight_nonneg
lemma copulaWeight_nonneg (ν : Bool) (K M : ℕ) (idx : CopulaIndex K M) :
    0 ≤ copulaWeight ν K M idx := by
  unfold copulaWeight
  apply mul_nonneg (by positivity)
  apply Finset.prod_nonneg
  intro j _
  exact pairWeight_nonneg _ _ (coarseTent_abs_le_one _ _ _) _ _

/-- The full-label prior average can be expanded before its deterministic observation map. This statement assumes [the hK condition](hyp:hK), [the ha condition](hyp:ha), [the hu condition](hyp:hu). [This is the stated conclusion](goal). -/
-- @node: prior_label_observation_atomic
lemma prior_label_observation_atomic (ν : Bool) (n K M : ℕ) (a u L : ℝ)
    (hK : 0 < K) (ha : 0 < a ∧ a ≤ 1/16) (hu : 0 < u ∧ u ≤ 1/16)
    (xs : Fin n → unitInterval) (marks : Fin n → Bool) :
    (fairLabelMeasure n (fun labels => ∑ idx : CopulaIndex K M,
      copulaWeight ν K M idx * ∏ i, labelDensity ν K M a u idx (xs i) (marks i) (labels i))).map
        (fun labels => fun i => (xs i,(labels i).1,if marks i then signVal (labels i).2*L else 0)) =
    ∑ idx : CopulaIndex K M, ENNReal.ofReal (copulaWeight ν K M idx) •
      ∑ labels : Labels n, ENNReal.ofReal ((4:ℝ)^(-(n:ℤ)) *
        ∏ i, labelDensity ν K M a u idx (xs i) (marks i) (labels i)) •
        Measure.dirac (fun i => (xs i,(labels i).1,if marks i then signVal (labels i).2*L else 0)) := by
  classical
  have hd (idx : CopulaIndex K M) (labels : Labels n) :
      0 ≤ ∏ i, labelDensity ν K M a u idx (xs i) (marks i) (labels i) := by
    apply Finset.prod_nonneg
    intro i _
    exact le_trans (by norm_num) (labelDensity_bounds ν K M a u hK ha hu idx _ _ _).1
  ext t ht
  rw [Measure.map_apply (measurable_of_finite _) ht]
  simp only [fairLabelMeasure, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.smul_apply, smul_eq_mul]
  simp_rw [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (4:ℝ)^(-(n:ℤ))),
    ENNReal.ofReal_sum_of_nonneg (fun idx _ => mul_nonneg (copulaWeight_nonneg ν K M idx) (hd idx _)),
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro idx _
  apply Finset.sum_congr rfl
  intro labels _
  rw [ENNReal.ofReal_mul (copulaWeight_nonneg ν K M idx)]
  simp only [Measure.dirac_apply' _ ht, Measure.dirac_apply' _ (ht.preimage (measurable_of_finite _))]
  simp only [Set.indicator_apply, Set.mem_preimage, Pi.one_apply]
  ring

/-- Independent Bernoulli masses times fair-label masses equal the original marked table masses. This statement assumes [the hε condition](hyp:hε), [the hd condition](hyp:hd). [This is the stated conclusion](goal). -/
-- @node: mark_label_mass_product
lemma mark_label_mass_product (n : ℕ) (ε : ℝ) (hε : 0 ≤ ε ∧ ε ≤ 1)
    (marks : Fin n → Bool) (d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i) :
    (∏ i, ENNReal.ofReal ((if marks i then ε/4 else (1-ε)/4) * d i)) =
      (∏ i, ENNReal.ofReal (if marks i then ε else 1-ε)) *
        ENNReal.ofReal ((4:ℝ)^(-(n:ℤ)) * ∏ i, d i) := by
  have hi (i : Fin n) :
      ENNReal.ofReal ((if marks i then ε/4 else (1-ε)/4) * d i) =
        ENNReal.ofReal (if marks i then ε else 1-ε) * ENNReal.ofReal (1/4:ℝ) *
          ENNReal.ofReal (d i) := by
    rw [← ENNReal.ofReal_mul (by split <;> linarith),
      ← ENNReal.ofReal_mul (by apply mul_nonneg <;> first | positivity | (split <;> linarith))]
    apply congrArg ENNReal.ofReal
    cases marks i <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> ring
  simp_rw [hi]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ 1/4),
    ← ENNReal.ofReal_prod_of_nonneg (fun i _ => hd i),
    mul_assoc, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (1/4)^n)]
  rw [zpow_neg, zpow_natCast, ← inv_pow]
  norm_num

/-- Joint flag/label functions and separate flag and label vectors enumerate the same samples. [This is the stated conclusion](goal). -/
-- @node: sum_flag_label_vectors
lemma sum_flag_label_vectors {R : Type*} [AddCommMonoid R] (n : ℕ)
    (f : (Fin n → Bool × (Bool × Bool)) → R) :
    (∑ tags, f tags) = ∑ marks : Fin n → Bool, ∑ labels : Labels n,
      f (fun i => (marks i,labels i)) := by
  simpa only [Fintype.sum_prod_type] using
    (Fintype.sum_equiv
      (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Bool) (fun _ => Bool × Bool))
      f (fun p => f (fun i => (p.1 i,p.2 i))) (fun _ => rfl))

/-- Sampling independent flags and then the prior-averaged labels reproduces the exact finite prior average of the original joint flag/label enumeration at a fixed design. This statement assumes [the hK condition](hyp:hK), [the ha condition](hyp:ha), [the hu condition](hyp:hu), [the hε condition](hyp:hε). [This is the stated conclusion](goal). -/
-- @node: prior_label_mark_bind
lemma prior_label_mark_bind (ν : Bool) (n K M : ℕ) (a u ε L : ℝ)
    (hK : 0 < K) (ha : 0 < a ∧ a ≤ 1/16) (hu : 0 < u ∧ u ≤ 1/16)
    (hε : 0 ≤ ε ∧ ε ≤ 1) (xs : Fin n → unitInterval) :
    (Measure.pi (fun _ : Fin n => markFlagLaw ε)).bind (fun marks =>
      (fairLabelMeasure n (fun labels => ∑ idx : CopulaIndex K M,
        copulaWeight ν K M idx * ∏ i, labelDensity ν K M a u idx (xs i) (marks i) (labels i))).map
          (fun labels => fun i => (xs i,(labels i).1,if marks i then signVal (labels i).2*L else 0))) =
    ∑ idx : CopulaIndex K M, ENNReal.ofReal (copulaWeight ν K M idx) •
      ∑ tags : Fin n → Bool × (Bool × Bool),
        (∏ i, ENNReal.ofReal ((if (tags i).1 then ε/4 else (1-ε)/4) *
          labelDensity ν K M a u idx (xs i) (tags i).1 (tags i).2)) •
        Measure.dirac (fun i => (xs i,(tags i).2.1,if (tags i).1 then signVal (tags i).2.2*L else 0)) := by
  classical
  simp_rw [prior_label_observation_atomic ν n K M a u L hK ha hu xs]
  ext t ht
  rw [Measure.bind_apply ht (measurable_of_finite _).aemeasurable,
    markFlagLaw_pi_atomic n ε hε, lintegral_finsetSum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul,
    Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply]
  simp_rw [sum_flag_label_vectors]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro idx _
  apply Finset.sum_congr rfl
  intro marks _
  apply Finset.sum_congr rfl
  intro labels _
  rw [mark_label_mass_product n ε hε marks _ (fun i =>
    le_trans (by norm_num) (labelDensity_bounds ν K M a u hK ha hu idx _ _ _).1)]
  ring

/-- Measurable locations and nonnegative masses give a measurable finite atomic sampling law. This statement assumes [the w condition](hyp:w), [the hw condition](hyp:hw), [the hf condition](hyp:hf). [This is the stated conclusion](goal). -/
-- @node: record_measurable_atomic
@[fun_prop] lemma record_measurable_atomic {X Ω J : Type*} [MeasurableSpace X]
    [MeasurableSpace Ω] [Fintype J] (w : X → J → ℝ≥0∞) (f : X → J → Ω)
    (hw : ∀ j, Measurable (fun x => w x j)) (hf : ∀ j, Measurable (fun x => f x j)) :
    Measurable (fun x => ∑ j, w x j • Measure.dirac (f x j)) := by
  apply Finset.measurable_sum
  intro j _
  apply Measure.measurable_of_measurable_coe
  intro t ht
  exact (hw j).mul ((Measure.measurable_coe ht).comp (Measure.measurable_dirac.comp (hf j)))

/-- Integrating the common iid design and independent flags gives exactly the original full-record copula mixture. The finite prior is interchanged with sampling, not altered. [This is the stated conclusion](goal). -/
-- @node: prior_label_design_bind_eq_mixture
lemma prior_label_design_bind_eq_mixture (ν : Bool) (v : Params) (n K M : ℕ)
    (a u ε L : ℝ) (h : CopulaDomain n K M a u ε L) :
    ((Measure.pi fun _ : Fin n => design).prod
      (Measure.pi fun _ : Fin n => markFlagLaw ε)).bind (fun xm =>
        (fairLabelMeasure n (fun labels => ∑ idx : CopulaIndex K M,
          copulaWeight ν K M idx *
            ∏ i, labelDensity ν K M a u idx (xm.1 i) (xm.2 i) (labels i))).map
          (fun labels => fun i =>
            (xm.1 i,(labels i).1,if xm.2 i then signVal (labels i).2*L else 0))) =
      copulaMixture ν n v K M a u ε L := by
  classical
  have hK : 0 < K := by have := h.2.2.2.1; have := h.2.2.2.2.1; omega
  have ha := h.2.2.2.2.2.1
  have hu := h.2.2.2.2.2.2.1
  have hε : 0 ≤ ε ∧ ε ≤ 1 := ⟨h.2.2.2.2.2.2.2.1.1.le, h.2.2.2.2.2.2.2.1.2.le⟩
  let : IsProbabilityMeasure design := by unfold design; infer_instance
  let : IsProbabilityMeasure (markFlagLaw ε) := markFlagLaw_probability ε hε.1 hε.2
  let T (idx : CopulaIndex K M) (xs : Fin n → unitInterval) : Measure (Fin n → Record) :=
    ∑ tags : Fin n → Bool × (Bool × Bool),
      (∏ i, ENNReal.ofReal ((if (tags i).1 then ε/4 else (1-ε)/4) *
        labelDensity ν K M a u idx (xs i) (tags i).1 (tags i).2)) •
      Measure.dirac (fun i => (xs i,(tags i).2.1,if (tags i).1 then signVal (tags i).2.2*L else 0))
  have hT (idx : CopulaIndex K M) : Measurable (T idx) := by
    apply record_measurable_atomic
    · intro tags
      fun_prop
    · intro tags
      fun_prop
  have hwT (idx : CopulaIndex K M) : Measurable
      (fun xs => ENNReal.ofReal (copulaWeight ν K M idx) • T idx xs) := by
    apply Measure.measurable_of_measurable_coe
    intro t ht
    exact measurable_const.mul ((Measure.measurable_coe ht).comp (hT idx))
  have hsum : Measurable (fun xs => ∑ idx : CopulaIndex K M,
      ENNReal.ofReal (copulaWeight ν K M idx) • T idx xs) :=
    Finset.measurable_sum _ (fun idx _ => hwT idx)
  have htransport :
      ((Measure.pi fun _ : Fin n => design).prod
        (Measure.pi fun _ : Fin n => markFlagLaw ε)).bind (fun xm =>
          (fairLabelMeasure n (fun labels => ∑ idx : CopulaIndex K M,
            copulaWeight ν K M idx *
              ∏ i, labelDensity ν K M a u idx (xm.1 i) (xm.2 i) (labels i))).map
            (fun labels => fun i =>
              (xm.1 i,(labels i).1,if xm.2 i then signVal (labels i).2*L else 0))) =
        (Measure.pi fun _ : Fin n => design).bind (fun xs =>
          ∑ idx : CopulaIndex K M, ENNReal.ofReal (copulaWeight ν K M idx) • T idx xs) := by
    ext t ht
    have hg := (Measure.measurable_coe ht).comp
      (measurable_prior_label_observation ν n K M a u L)
    dsimp only [Function.comp_def] at hg
    rw [Measure.bind_apply ht (measurable_prior_label_observation ν n K M a u L).aemeasurable,
      Measure.bind_apply ht hsum.aemeasurable, lintegral_prod _ hg.aemeasurable]
    apply lintegral_congr
    intro xs
    rw [← Measure.bind_apply ht (measurable_of_finite _).aemeasurable,
      prior_label_mark_bind ν n K M a u ε L hK ha hu hε xs]
  rw [htransport, record_bind_finite_sum _ _ hwT]
  simp_rw [record_bind_const_smul _ _ _ (hT _)]
  exact (copulaMixture_eq_flag_label_bind ν v n K M a u ε L h).symm

end CausalSmith.Stat.FinitepHomogeneityDensegamma
