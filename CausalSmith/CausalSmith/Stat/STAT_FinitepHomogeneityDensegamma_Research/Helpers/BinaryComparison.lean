module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.PairedTent
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.TwoPrior
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.TCausalNonempty

/-! Finite-moment homogeneity testing: binary conversion and risk comparisons. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma


/-- Binaryconversion: the displayed mathematical construction or bound. This statement assumes [the law parameter](hyp:law). [This is the stated defined object](goal). -/
def binaryConversion (law : ObservedLaw) : ObservedLaw := binaryRealization law.e law.m0 law.tau
/-- Binaryrandomizationrule: the displayed mathematical construction or bound. This statement assumes [the n parameter](hyp:n), [the ψ parameter](hyp:ψ), [the z parameter](hyp:z). [This is the stated defined object](goal). -/
def binaryRandomizationRule (n : ℕ) (ψ : Test n) (z : Experiment n) : ℝ :=
  ∑ signs : Fin n → Bool,
    ψ.1 ((fun i => (X (z.1 i),A (z.1 i),signVal (signs i))),z.2)*
    ∏ i : Fin n, (1+signVal (signs i)*clipY 1 (Y (z.1 i)))/2
/-- Clipping at one puts every conversion mean in the sign probability interval. [This is the stated conclusion](goal). -/
-- @node: binary_clip_bounds
lemma binary_clip_bounds (y : ℝ) : -1 ≤ clipY 1 y ∧ clipY 1 y ≤ 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_right _ _)

/-- Every one-record sign probability is nonnegative. [This is the stated conclusion](goal). -/
-- @node: binary_sign_weight_nonneg
lemma binary_sign_weight_nonneg (b : Bool) (y : ℝ) :
    0 ≤ (1+signVal b*clipY 1 y)/2 := by
  have h := binary_clip_bounds y
  cases b <;> simp only [signVal, Bool.false_eq_true, if_false, if_true] <;> nlinarith

/-- Independent conversion probabilities sum to one over all sign sequences. [This is the stated conclusion](goal). -/
-- @node: binary_sign_weights_sum
lemma binary_sign_weights_sum (n : ℕ) (y : Fin n → ℝ) :
    (∑ signs : Fin n → Bool, ∏ i : Fin n, (1+signVal (signs i)*clipY 1 (y i))/2) = 1 := by
  rw [← Fintype.prod_sum (fun (i : Fin n) (b : Bool) => (1+signVal b*clipY 1 (y i))/2)]
  have h : ∀ i : Fin n, (∑ b : Bool, (1+signVal b*clipY 1 (y i))/2) = 1 := by
    intro i
    simp only [Fintype.sum_bool, signVal, if_true, Bool.false_eq_true, if_false]
    ring
  simp only [h, Finset.prod_const_one]

/-- The explicit rejection rule is Borel measurable and takes values between zero and one. [This is the stated conclusion](goal). -/
-- @node: binaryRandomization_test
lemma binaryRandomization_test (n : ℕ) (ψ : Test n) : Measurable (binaryRandomizationRule n ψ) ∧
    ∀ z, 0 ≤ binaryRandomizationRule n ψ z ∧ binaryRandomizationRule n ψ z ≤ 1 := by
  constructor
  · have hψ := ψ.2.1
    unfold binaryRandomizationRule X A Y clipY
    fun_prop
  · intro z
    have hw (signs : Fin n → Bool) :
        0 ≤ ∏ i : Fin n, (1+signVal (signs i)*clipY 1 (Y (z.1 i)))/2 :=
      Finset.prod_nonneg (fun i _ => binary_sign_weight_nonneg (signs i) _)
    constructor
    · exact Finset.sum_nonneg (fun signs _ => mul_nonneg (ψ.2.2 _).1 (hw signs))
    · calc
        binaryRandomizationRule n ψ z ≤
            ∑ signs : Fin n → Bool, ∏ i : Fin n,
              (1+signVal (signs i)*clipY 1 (Y (z.1 i)))/2 := by
          apply Finset.sum_le_sum
          intro signs _
          exact mul_le_of_le_one_left (hw signs) (ψ.2.2 _).2
        _ = 1 := binary_sign_weights_sum n (fun i => Y (z.1 i))
/-- Binaryrandomizationtest: the displayed mathematical construction or bound. This statement assumes [the n parameter](hyp:n), [the ψ parameter](hyp:ψ). [This is the stated defined object](goal). -/
def binaryRandomizationTest (n : ℕ) (ψ : Test n) : Test n := ⟨binaryRandomizationRule n ψ,binaryRandomization_test n ψ⟩
/-- Every binary arm kernel is supported on the two displayed signs. [This is the stated conclusion](goal). -/
-- @node: binaryArm_support
lemma binaryArm_support (m : Nuisance) (x : unitInterval) :
    ∀ᵐ y ∂binaryArm m x, y = -1 ∨ y = 1 := by
  change ∀ᵐ y ∂binaryArmMeasure m x, y = -1 ∨ y = 1
  rw [binaryArmMeasure, ae_add_measure_iff]
  constructor <;> apply Measure.ae_smul_measure <;> simp

/-- A legal binary arm has raw moment one for every positive moment exponent. This statement assumes [the hm condition](hyp:hm). [This is the stated conclusion](goal). -/
-- @node: binaryArm_raw_moment
lemma binaryArm_raw_moment (m : Nuisance) (hm : ∀ x, |m x| ≤ 1)
    (p : ℝ) (x : unitInterval) :
    (∫⁻ y, ENNReal.ofReal (|y| ^ p) ∂binaryArm m x) = 1 := by
  let : IsMarkovKernel (binaryArm m) := binaryArm_markov m hm
  calc
    _ = ∫⁻ _, (1 : ℝ≥0∞) ∂binaryArm m x := by
      apply lintegral_congr_ae
      filter_upwards [binaryArm_support m x] with y hy
      rcases hy with rfl | rfl <;> simp
    _ = 1 := by simp

/-- The realized sign law retains each prescribed continuous primitive. This statement assumes [the h0 condition](hyp:h0), [the hτ condition](hyp:hτ). [This is the stated conclusion](goal). -/
-- @node: binaryConversion_primitives
lemma binaryConversion_primitives (law : ObservedLaw) (h0 : BaselineCap law)
    (hτ : EffectCap law) :
    (binaryConversion law).e = law.e ∧ (binaryConversion law).m0 = law.m0 ∧
    (binaryConversion law).tau = law.tau ∧
    (binaryConversion law).P = design ⊗ₘ recordKernel law.e law.e.continuous.measurable
      (fun a => binaryArm (if a then law.m0+law.tau else law.m0)) ∧
    (binaryConversion law).Q = (fun a => binaryArm (if a then law.m0+law.tau else law.m0)) := by
  have hmeans : ∀ x, |law.m0 x| ≤ 1 ∧ |law.m0 x+law.tau x| ≤ 1 := by
    intro x
    constructor
    · linarith [h0 x]
    · exact (abs_add_le _ _).trans (by linarith [h0 x, hτ x])
  have hc : (∀ x, 0 ≤ law.e x ∧ law.e x ≤ 1) ∧
      (∀ x, |law.m0 x| ≤ 1 ∧ |law.m0 x+law.tau x| ≤ 1) := ⟨law.e_range, hmeans⟩
  dsimp only [binaryConversion, binaryRealization]
  rw [dif_pos hc]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Sign support is preserved after mixing treatment labels and the uniform design. This statement assumes [the h0 condition](hyp:h0), [the hτ condition](hyp:hτ). [This is the stated conclusion](goal). -/
-- @node: binaryConversion_support
lemma binaryConversion_support (law : ObservedLaw) (h0 : BaselineCap law)
    (hτ : EffectCap law) : SignedBinaryOutcome (binaryConversion law) := by
  have hc := binaryConversion_primitives law h0 hτ
  let : IsMarkovKernel (binaryArm law.m0) := binaryArm_markov _ (fun x => by linarith [h0 x])
  let : IsMarkovKernel (binaryArm (law.m0+law.tau)) := binaryArm_markov _
    (fun x => (abs_add_le _ _).trans (by linarith [h0 x, hτ x]))
  have hs : MeasurableSet {o : Record | Y o = -1 ∨ Y o = 1} := by
    exact (measurableSet_eq_fun (by unfold Y; fun_prop) measurable_const).union
      (measurableSet_eq_fun (by unfold Y; fun_prop) measurable_const)
  apply (mem_ae_iff_prob_eq_one hs).mp
  rw [hc.2.2.2.1]
  apply Measure.ae_compProd_of_ae_ae hs
  apply ae_of_all
  intro x
  change ∀ᵐ z ∂recordMeasure law.e
    (fun a => binaryArm (if a then law.m0+law.tau else law.m0)) x,
    z.2 = -1 ∨ z.2 = 1
  rw [recordMeasure, ae_add_measure_iff]
  constructor <;> apply Measure.ae_smul_measure
  · simp only [if_true]
    apply (Measure.ae_prod_iff_ae_ae (by
      exact (measurableSet_eq_fun measurable_snd measurable_const).union
        (measurableSet_eq_fun measurable_snd measurable_const))).mpr
    exact ae_of_all _ (fun _ => binaryArm_support (law.m0+law.tau) x)
  · simp only [Bool.false_eq_true, if_false]
    apply (Measure.ae_prod_iff_ae_ae (by
      exact (measurableSet_eq_fun measurable_snd measurable_const).union
        (measurableSet_eq_fun measurable_snd measurable_const))).mpr
    exact ae_of_all _ (fun _ => binaryArm_support law.m0 x)

/-- Sign realization retains the primitive means while allowing any raw-moment exponent. This statement assumes [the hm condition](hyp:hm). [This is the stated conclusion](goal). -/
-- @node: binaryConversion_inModel_at
lemma binaryConversion_inModel_at (v : Params) (p : ℝ) (law : ObservedLaw)
    (hm : InModel v law) : InModel {v with p := p} (binaryConversion law) := by
  obtain ⟨he, h0, hτ, hP, hQ⟩ := binaryConversion_primitives law hm.baselineCap hm.effectCap
  have hmean0 : ∀ x, |law.m0 x| ≤ 1 := fun x => by linarith [hm.baselineCap x]
  have hmean1 : ∀ x, |(law.m0+law.tau) x| ≤ 1 := fun x =>
    (abs_add_le _ _).trans (by linarith [hm.baselineCap x, hm.effectCap x])
  let Q : Bool → Kernel unitInterval ℝ := fun a => binaryArm (if a then law.m0+law.tau else law.m0)
  have hmarkov : ∀ a, IsMarkovKernel (Q a) := by
    intro a
    cases a
    · exact binaryArm_markov law.m0 hmean0
    · exact binaryArm_markov (law.m0+law.tau) hmean1
  let : IsMarkovKernel (recordKernel law.e law.e.continuous.measurable Q) :=
    recordKernel_markov _ _ _ law.e_range hmarkov
  let : IsProbabilityMeasure design := (inferInstance : IsProbabilityMeasure (volume : Measure unitInterval))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (binaryConversion law).P.map X = design
    rw [hP]
    exact Measure.fst_compProd design (recordKernel law.e law.e.continuous.measurable Q)
  · simpa only [Overlap, he] using hm.overlap
  · simpa only [PropensitySmooth, he] using hm.propensitySmooth
  · simpa only [BaselineSmooth, h0] using hm.baselineSmooth
  · simpa only [EffectSmooth, hτ] using hm.effectSmooth
  · simpa only [BaselineCap, h0] using hm.baselineCap
  · simpa only [EffectCap, hτ] using hm.effectCap
  · intro a
    apply ae_of_all
    intro x
    rw [hQ]
    cases a
    · change (∫⁻ y, ENNReal.ofReal (|y| ^ p) ∂binaryArm law.m0 x) ≤ 10
      rw [binaryArm_raw_moment law.m0 hmean0]
      norm_num
    · change (∫⁻ y, ENNReal.ofReal (|y| ^ p) ∂binaryArm (law.m0+law.tau) x) ≤ 10
      rw [binaryArm_raw_moment (law.m0+law.tau) hmean1]
      norm_num

/-- Every allowed primitive mean triple has a legal signed-binary realization. This statement assumes [the hm condition](hyp:hm). [This is the stated conclusion](goal). -/
-- @node: binaryConversion_inModel
lemma binaryConversion_inModel (w : Smooth3) (law : ObservedLaw)
    (hm : InModel (Params.ofBounded w) law) : InBinaryModel w (binaryConversion law) := by
  have h := binaryConversion_inModel_at (Params.ofBounded w) 2 law hm
  exact ⟨h.uniform, h.overlap, h.propensitySmooth, h.baselineSmooth,
    h.effectSmooth, h.baselineCap, h.effectCap, h.rawMoment,
    binaryConversion_support law hm.baselineCap hm.effectCap⟩

/-- Every finite-moment model's primitive means have a signed-binary realization. This statement assumes [the hm condition](hyp:hm). [This is the stated conclusion](goal). -/
-- @node: binaryConversion_inBinaryModel
lemma binaryConversion_inBinaryModel (v : Params) (law : ObservedLaw)
    (hm : InModel v law) : InBinaryModel v.toSmooth3 (binaryConversion law) := by
  have h := binaryConversion_inModel_at v 2 law hm
  exact ⟨h.uniform, h.overlap, h.propensitySmooth, h.baselineSmooth,
    h.effectSmooth, h.baselineCap, h.effectCap, h.rawMoment,
    binaryConversion_support law hm.baselineCap hm.effectCap⟩

/-- Mean-preserving realization preserves centered effect distance and the entire constant null. This statement assumes [the h0 condition](hyp:h0), [the hτ condition](hyp:hτ). [This is the stated conclusion](goal). -/
-- @node: binaryConversion_preserves_effect
lemma binaryConversion_preserves_effect (law : ObservedLaw) (h0 : BaselineCap law)
    (hτ : EffectCap law) :
    hetDist (binaryConversion law) = hetDist law ∧
    (NullConstancy (binaryConversion law) ↔ NullConstancy law) := by
  have ht := (binaryConversion_primitives law h0 hτ).2.2.1
  constructor
  · simp only [hetDist, meanTau, ht]
  · simp only [NullConstancy, ht]

/-- Signed-binary support implies the bounded outcome envelope. This statement assumes [the hm condition](hyp:hm). [This is the stated conclusion](goal). -/
-- @node: binaryModel_inBoundedModel
lemma binaryModel_inBoundedModel (w : Smooth3) (law : ObservedLaw)
    (hm : InBinaryModel w law) : InBoundedModel w law := by
  refine ⟨hm.uniform, hm.overlap, hm.propensitySmooth, hm.baselineSmooth,
    hm.effectSmooth, hm.baselineCap, hm.effectCap, hm.rawMoment, ?_⟩
  have hs : MeasurableSet {o : Record | Y o = -1 ∨ Y o = 1} := by
    exact (measurableSet_eq_fun (by unfold Y; fun_prop) measurable_const).union
      (measurableSet_eq_fun (by unfold Y; fun_prop) measurable_const)
  have hb : MeasurableSet {o : Record | |Y o| ≤ 1} := by
    exact measurableSet_le (by unfold Y; fun_prop) measurable_const
  apply (mem_ae_iff_prob_eq_one hb).mp
  have hae := (mem_ae_iff_prob_eq_one hs).mpr hm.signedBinaryOutcome
  filter_upwards [hae] with o ho
  rcases ho with ho | ho <;> rw [ho] <;> norm_num

/-- Overlap transfers the observed bounded envelope to each conditional arm. This statement assumes [the hu condition](hyp:hu), [the ho condition](hyp:ho), [the hb condition](hyp:hb). [This is the stated conclusion](goal). -/
-- @node: boundedOutcome_arm_support
lemma boundedOutcome_arm_support (law : ObservedLaw) (hu : UniformDesign law)
    (ho : Overlap law) (hb : BoundedOutcome law) (a : Bool) :
    ∀ᵐ x ∂design, ∀ᵐ y ∂law.Q a x, |y| ≤ 1 := by
  have hs : MeasurableSet {o : Record | |Y o| ≤ 1} := by
    exact measurableSet_le (by unfold Y; fun_prop) measurable_const
  have hae := (mem_ae_iff_prob_eq_one hs).mpr hb
  rw [law.record_version, show law.P.map X = design from hu] at hae
  let : IsProbabilityMeasure design :=
    (inferInstance : IsProbabilityMeasure (volume : Measure unitInterval))
  let : IsMarkovKernel (recordKernel law.e law.e.continuous.measurable law.Q) :=
    recordKernel_markov _ _ _ law.e_range law.markov
  have hx := Measure.ae_ae_of_ae_compProd hae
  filter_upwards [hx] with x hx
  change ∀ᵐ z ∂recordMeasure law.e law.Q x, |z.2| ≤ 1 at hx
  rw [recordMeasure, ae_add_measure_iff] at hx
  have htrue : ENNReal.ofReal (law.e x) ≠ 0 := by
    apply ne_of_gt
    exact ENNReal.ofReal_pos.mpr (by linarith [(ho x).1])
  have hfalse : ENNReal.ofReal (1-law.e x) ≠ 0 := by
    apply ne_of_gt
    exact ENNReal.ofReal_pos.mpr (by linarith [(ho x).2])
  have hp : MeasurableSet {z : Bool × ℝ | |z.2| ≤ 1} :=
    measurableSet_le (by fun_prop) measurable_const
  cases a
  · have h := (Measure.ae_ennreal_smul_measure_iff hfalse).mp hx.2
    have h' := (Measure.ae_prod_iff_ae_ae hp).mp h
    simpa using h'
  · have h := (Measure.ae_ennreal_smul_measure_iff htrue).mp hx.1
    have h' := (Measure.ae_prod_iff_ae_ae hp).mp h
    simpa using h'

/-- A bounded arm has raw moment at most one at every nonnegative exponent. This statement assumes [the hu condition](hyp:hu), [the ho condition](hyp:ho), [the hb condition](hyp:hb), [the hp condition](hyp:hp). [This is the stated conclusion](goal). -/
-- @node: boundedOutcome_rawMoment
lemma boundedOutcome_rawMoment (law : ObservedLaw) (hu : UniformDesign law)
    (ho : Overlap law) (hb : BoundedOutcome law) (p : ℝ) (hp : 0 ≤ p) :
    ∀ a : Bool, ∀ᵐ x ∂design,
      (∫⁻ y, ENNReal.ofReal (|y| ^ p) ∂law.Q a x) ≤ 1 := by
  intro a
  filter_upwards [boundedOutcome_arm_support law hu ho hb a] with x hx
  calc
    _ ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂law.Q a x := by
      apply lintegral_mono_ae
      filter_upwards [hx] with y hy
      exact (ENNReal.ofReal_le_ofReal (Real.rpow_le_one (abs_nonneg y) hy hp)).trans
        (by simp)
    _ = 1 := by simp

/-- Bounded laws retain all primitive predicates in the finite-moment model. This statement assumes [the hv condition](hyp:hv), [the hm condition](hyp:hm). [This is the stated conclusion](goal). -/
-- @node: boundedModel_inModel
lemma boundedModel_inModel (v : Params) (hv : v.Valid) (law : ObservedLaw)
    (hm : InBoundedModel v.toSmooth3 law) : InModel v law := by
  refine ⟨hm.uniform, hm.overlap, hm.propensitySmooth, hm.baselineSmooth,
    hm.effectSmooth, hm.baselineCap, hm.effectCap, ?_⟩
  intro a
  filter_upwards [boundedOutcome_rawMoment law hm.uniform hm.overlap
    hm.boundedOutcome v.p (by linarith [hv.1.1]) a] with x hx
  exact hx.trans (by norm_num)

/-- Bounded and signed-binary models attain exactly the same effect distances. [This is the stated conclusion](goal). -/
-- @node: binary_bounded_distance_image
lemma binary_bounded_distance_image (w : Smooth3) :
    hetDist '' {law | InBinaryModel w law} =
      hetDist '' {law | InBoundedModel w law} := by
  apply Set.Subset.antisymm
  · rintro r ⟨law, hm, rfl⟩
    exact ⟨law, binaryModel_inBoundedModel w law hm, rfl⟩
  · rintro r ⟨law, hm, rfl⟩
    have hmodel : InModel (Params.ofBounded w) law :=
      ⟨hm.uniform, hm.overlap, hm.propensitySmooth, hm.baselineSmooth,
        hm.effectSmooth, hm.baselineCap, hm.effectCap, hm.rawMoment⟩
    exact ⟨binaryConversion law, binaryConversion_inModel w law hmodel,
      (binaryConversion_preserves_effect law hm.baselineCap hm.effectCap).1⟩

/-- Bounded and finite-moment models attain exactly the same effect distances. [This is the stated conclusion](goal). -/
-- @node: bounded_model_distance_image
lemma bounded_model_distance_image (v : Params) :
    hetDist '' {law | InBoundedModel v.toSmooth3 law} =
      hetDist '' {law | InModel v law} := by
  apply Set.Subset.antisymm
  · rintro r ⟨law, hm, rfl⟩
    have hmodel : InModel (Params.ofBounded v.toSmooth3) law :=
      ⟨hm.uniform, hm.overlap, hm.propensitySmooth, hm.baselineSmooth,
        hm.effectSmooth, hm.baselineCap, hm.effectCap, hm.rawMoment⟩
    exact ⟨binaryConversion law,
      binaryConversion_inModel_at (Params.ofBounded v.toSmooth3) v.p law hmodel,
      (binaryConversion_preserves_effect law hm.baselineCap hm.effectCap).1⟩
  · rintro r ⟨law, hm, rfl⟩
    exact ⟨binaryConversion law,
      binaryModel_inBoundedModel v.toSmooth3 _ (binaryConversion_inBinaryModel v law hm),
      (binaryConversion_preserves_effect law hm.baselineCap hm.effectCap).1⟩

/-- The common attained distance set gives the same bounded and binary suprema. [This is the stated conclusion](goal). -/
-- @node: maxDistBinary_eq_maxDistBounded
lemma maxDistBinary_eq_maxDistBounded (w : Smooth3) :
    maxDistBinary w = maxDistBounded w := by
  exact congrArg sSup (binary_bounded_distance_image w)

/-- The common attained distance set gives the same bounded and full-model suprema. [This is the stated conclusion](goal). -/
-- @node: maxDistBounded_eq_maxDist
lemma maxDistBounded_eq_maxDist (v : Params) :
    maxDistBounded v.toSmooth3 = maxDist v := by
  exact congrArg sSup (bounded_model_distance_image v)

/-- Restricting both the null and alternative classes cannot increase testing risk. This statement assumes [the hnull condition](hyp:hnull), [the halt condition](hyp:halt). [This is the stated conclusion](goal). -/
-- @node: testingRiskOn_submodel
lemma testingRiskOn_submodel (n : ℕ) (r : ℝ)
    (NullSmall AltSmall NullLarge AltLarge : Set ObservedLaw)
    (hnull : NullSmall ⊆ NullLarge) (halt : AltSmall ⊆ AltLarge) :
    testingRiskOn n r NullSmall AltSmall ≤ testingRiskOn n r NullLarge AltLarge := by
  let zeroTest : Test n := ⟨fun _ => 0, measurable_const, fun _ => by norm_num⟩
  have hz : LevelValid n NullLarge zeroTest := by
    intro law _
    simp [rejectProb, zeroTest]
  let : Nonempty {φ : Test n // LevelValid n NullLarge φ} := ⟨⟨zeroTest, hz⟩⟩
  unfold testingRiskOn
  apply le_ciInf
  intro φ
  have hlevel : LevelValid n NullSmall φ.1 := fun law hlaw => φ.2 law (hnull hlaw)
  refine ciInf_le_of_le ?_ ⟨φ.1, hlevel⟩ ?_
  · refine ⟨0, ?_⟩
    rintro _ ⟨ψ, rfl⟩
    exact worstError_nonneg n AltSmall r ψ.1
  · by_cases hA : Nonempty {law : ObservedLaw // law ∈ AltSmall ∧ r ≤ hetDist law}
    · let := hA
      have hb : BddAbove (Set.range (fun law :
          {law : ObservedLaw // law ∈ AltLarge ∧ r ≤ hetDist law} =>
          1-rejectProb n law.1.P φ.1)) := by
        refine ⟨1, ?_⟩
        rintro _ ⟨law, rfl⟩
        linarith [(rejectProb_bounds n law.1 φ.1).1]
      apply ciSup_le
      intro law
      exact le_ciSup hb ⟨law.1, halt law.2.1, law.2.2⟩
    · let := not_nonempty_iff.mp hA
      rw [Real.iSup_of_isEmpty]
      exact worstError_nonneg n AltLarge r φ.1

/-- With a common nonnegative cap, pointwise smaller risk gives a smaller critical radius. This statement assumes [the hD condition](hyp:hD), [the hB condition](hyp:hB). [This is the stated conclusion](goal). -/
-- @node: cappedRadius_mono_risk
lemma cappedRadius_mono_risk (D : ℝ) (hD : 0 ≤ D) (Bsmall Blarge : ℝ → ℝ)
    (hB : ∀ r, 0 < r → r < D → Bsmall r ≤ Blarge r) :
    cappedRadius D Bsmall ≤ cappedRadius D Blarge := by
  have hb : BddBelow ({r | 0 < r ∧ r < D ∧ Bsmall r ≤ 1/10} ∪ {D}) := by
    refine ⟨0, ?_⟩
    intro r hr
    rcases hr with hr | hr
    · exact hr.1.le
    · simpa only [Set.mem_singleton_iff.mp hr] using hD
  apply le_csInf ⟨D, Or.inr (Set.mem_singleton D)⟩
  intro r hr
  apply csInf_le hb
  rcases hr with hr | hr
  · exact Or.inl ⟨hr.1, hr.2.1, (hB r hr.1 hr.2.1).trans hr.2.2⟩
  · exact Or.inr hr

/-- Restricting a full-model test gives the bounded-model risk comparison. This statement assumes [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: boundedTestingRisk_le_testingRisk
lemma boundedTestingRisk_le_testingRisk (v : Params) (hv : v.Valid) (n : ℕ) (r : ℝ) :
    boundedTestingRisk n v.toSmooth3 r ≤ testingRisk n v r := by
  apply testingRiskOn_submodel
  · intro law hm
    have hb : InBoundedModel v.toSmooth3 law :=
      ⟨hm.uniform, hm.overlap, hm.propensitySmooth, hm.baselineSmooth,
        hm.effectSmooth, hm.baselineCap, hm.effectCap, hm.rawMoment, hm.boundedOutcome⟩
    have h := boundedModel_inModel v hv law hb
    exact ⟨h.uniform, h.overlap, h.propensitySmooth, h.baselineSmooth,
      h.effectSmooth, h.baselineCap, h.effectCap, h.rawMoment, hm.nullConstancy⟩
  · intro law hm
    exact boundedModel_inModel v hv law hm

/-- Restricting a bounded-model test gives the signed-binary risk comparison. [This is the stated conclusion](goal). -/
-- @node: binaryTestingRisk_le_boundedTestingRisk
lemma binaryTestingRisk_le_boundedTestingRisk (w : Smooth3) (n : ℕ) (r : ℝ) :
    binaryTestingRisk n w r ≤ boundedTestingRisk n w r := by
  apply testingRiskOn_submodel
  · intro law hm
    have hb : InBinaryModel w law :=
      ⟨hm.uniform, hm.overlap, hm.propensitySmooth, hm.baselineSmooth,
        hm.effectSmooth, hm.baselineCap, hm.effectCap, hm.rawMoment, hm.signedBinaryOutcome⟩
    have h := binaryModel_inBoundedModel w law hb
    exact ⟨h.uniform, h.overlap, h.propensitySmooth, h.baselineSmooth,
      h.effectSmooth, h.baselineCap, h.effectCap, h.rawMoment, h.boundedOutcome,
      hm.nullConstancy⟩
  · intro law hm
    exact binaryModel_inBoundedModel w law hm

/-- Exact recordwise conversion transfers binary tests to bounded tests without changing risk. This statement assumes [the hconversion condition](hyp:hconversion). [This is the stated conclusion](goal). -/
-- @node: boundedTestingRisk_eq_binary_of_conversion
lemma boundedTestingRisk_eq_binary_of_conversion (w : Smooth3) (n : ℕ) (r : ℝ)
    (hconversion : ∀ ψ : Test n, ∀ law, InBoundedModel w law →
      rejectProb n law.P (binaryRandomizationTest n ψ) =
        rejectProb n (binaryConversion law).P ψ) :
    boundedTestingRisk n w r = binaryTestingRisk n w r := by
  apply le_antisymm ?_ (binaryTestingRisk_le_boundedTestingRisk w n r)
  let zeroTest : Test n := ⟨fun _ => 0, measurable_const, fun _ => by norm_num⟩
  have hz : LevelValid n {law | InBinaryNull w law} zeroTest := by
    intro law _
    simp [rejectProb, zeroTest]
  let : Nonempty {φ : Test n // LevelValid n {law | InBinaryNull w law} φ} :=
    ⟨⟨zeroTest, hz⟩⟩
  unfold boundedTestingRisk binaryTestingRisk testingRiskOn
  apply le_ciInf
  intro ψ
  have hlevel : LevelValid n {law | InBoundedNull w law}
      (binaryRandomizationTest n ψ.1) := by
    intro law hm
    have hb : InBoundedModel w law :=
      ⟨hm.uniform, hm.overlap, hm.propensitySmooth, hm.baselineSmooth,
        hm.effectSmooth, hm.baselineCap, hm.effectCap, hm.rawMoment, hm.boundedOutcome⟩
    have hc := binaryConversion_inModel w law hb.toInModel
    rw [hconversion ψ.1 law hb]
    exact ψ.2 _ ⟨hc.uniform, hc.overlap, hc.propensitySmooth, hc.baselineSmooth,
      hc.effectSmooth, hc.baselineCap, hc.effectCap, hc.rawMoment, hc.signedBinaryOutcome,
      (binaryConversion_preserves_effect law hm.baselineCap hm.effectCap).2.mpr hm.nullConstancy⟩
  refine ciInf_le_of_le ?_ ⟨binaryRandomizationTest n ψ.1, hlevel⟩ ?_
  · refine ⟨0, ?_⟩
    rintro _ ⟨φ, rfl⟩
    exact worstError_nonneg n {law | InBoundedModel w law} r φ.1
  · by_cases hA : Nonempty {law : ObservedLaw // law ∈ {law | InBoundedModel w law} ∧ r ≤ hetDist law}
    · let := hA
      have hb : BddAbove (Set.range (fun law :
          {law : ObservedLaw // InBinaryModel w law ∧ r ≤ hetDist law} =>
          1-rejectProb n law.1.P ψ.1)) := by
        refine ⟨1, ?_⟩
        rintro _ ⟨law, rfl⟩
        linarith [(rejectProb_bounds n law.1 ψ.1).1]
      apply ciSup_le
      intro law
      have hc := binaryConversion_inModel w law.1 law.2.1.toInModel
      have hd := (binaryConversion_preserves_effect law.1
        law.2.1.baselineCap law.2.1.effectCap).1
      rw [hconversion ψ.1 law.1 law.2.1]
      exact le_ciSup hb ⟨binaryConversion law.1, hc, hd.symm ▸ law.2.2⟩
    · let := not_nonempty_iff.mp hA
      rw [Real.iSup_of_isEmpty]
      exact worstError_nonneg n {law | InBinaryModel w law} r ψ.1

/-- Equality of risks on the admissible interval and a common cap give equal capped radii. This statement assumes [the hB condition](hyp:hB). [This is the stated conclusion](goal). -/
-- @node: cappedRadius_eq_of_risk_eq
lemma cappedRadius_eq_of_risk_eq (D : ℝ) (B₁ B₂ : ℝ → ℝ)
    (hB : ∀ r, 0 < r → r < D → B₁ r = B₂ r) :
    cappedRadius D B₁ = cappedRadius D B₂ := by
  unfold cappedRadius
  congr 1
  apply congrArg (fun s : Set ℝ => s ∪ {D})
  ext r
  constructor
  · rintro ⟨hr, hrD, hb⟩
    exact ⟨hr, hrD, (hB r hr hrD) ▸ hb⟩
  · rintro ⟨hr, hrD, hb⟩
    exact ⟨hr, hrD, (hB r hr hrD).symm ▸ hb⟩

/-- The shared maximum distance and restricted-test risk imply the capped-radius comparison. This statement assumes [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: boundedCriticalRadius_le_criticalRadius
lemma boundedCriticalRadius_le_criticalRadius (v : Params) (hv : v.Valid) (n : ℕ) :
    boundedCriticalRadius n v.toSmooth3 ≤ criticalRadius n v := by
  unfold boundedCriticalRadius criticalRadius
  rw [maxDistBounded_eq_maxDist]
  apply cappedRadius_mono_risk
  · exact (by unfold d0; positivity : (0 : ℝ) ≤ d0).trans (model_distance_lower v hv)
  · intro r _ _
    exact boundedTestingRisk_le_testingRisk v hv n r

end CausalSmith.Stat.FinitepHomogeneityDensegamma
