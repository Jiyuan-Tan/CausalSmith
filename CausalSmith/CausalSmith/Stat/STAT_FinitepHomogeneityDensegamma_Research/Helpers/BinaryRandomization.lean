module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.BinaryRadiusPositivity
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.TruncationMoments
public import Causalean.Stat.Minimax.MarkovKernelTransport

/-! Independent mean-preserving sign conversion of original records. -/
@[expose] public section
noncomputable section
set_option linter.style.longLine false
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators ProbabilityTheory
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- Replace only the outcome coordinate by a sign. This statement assumes [the o parameter](hyp:o), [the b parameter](hyp:b). [This is the stated defined object](goal). -/
-- @node: binaryRecordAtom
def binaryRecordAtom (o : Record) (b : Bool) : Record := (X o, A o, signVal b)

/-- The two conversion probabilities use the clipped original outcome. This statement assumes [the o parameter](hyp:o), [the b parameter](hyp:b). [This is the stated defined object](goal). -/
-- @node: binaryRecordWeight
def binaryRecordWeight (o : Record) (b : Bool) : ℝ := (1+signVal b*clipY 1 (Y o))/2

/-- The sign conversion is an explicit finite atomic Borel kernel. [This is the stated defined object](goal). -/
-- @node: binaryRecordKernel
def binaryRecordKernel : Kernel Record Record :=
  ⟨fun o => ∑ b : Bool, ENNReal.ofReal (binaryRecordWeight o b) • Measure.dirac (binaryRecordAtom o b), by
    apply Measure.measurable_of_measurable_coe
    intro S hS
    simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
    apply Finset.measurable_sum
    intro b _
    apply Measurable.mul
    · unfold binaryRecordWeight Y clipY
      fun_prop
    · exact (Measure.measurable_coe hS).comp (Measure.measurable_dirac.comp (by
        unfold binaryRecordAtom X A
        fun_prop))⟩

/-- The conversion probabilities normalize for every original record. [This is the stated conclusion](goal). -/
-- @node: binaryRecordWeight_sum
lemma binaryRecordWeight_sum (o : Record) : ∑ b : Bool, binaryRecordWeight o b = 1 := by
  simp only [Fintype.sum_bool, binaryRecordWeight, signVal, if_true, Bool.false_eq_true, if_false]
  ring

/-- Sign conversion preserves probability mass. [This is the stated defined object](goal). -/
-- @node: binaryRecordKernel_markov
instance binaryRecordKernel_markov : IsMarkovKernel binaryRecordKernel := by
  constructor
  intro o
  constructor
  change (∑ b : Bool, ENNReal.ofReal (binaryRecordWeight o b) • Measure.dirac (binaryRecordAtom o b)) univ = 1
  simp only [Measure.finsetSum_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun b _ => (show 0 ≤ binaryRecordWeight o b from binary_sign_weight_nonneg b (Y o))), binaryRecordWeight_sum]
  norm_num

/-- Integrating a sign probability over a bounded arm retains its original mean. This statement assumes [the hb condition](hyp:hb). [This is the stated conclusion](goal). -/
-- @node: binary_arm_weight_integral
lemma binary_arm_weight_integral (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hb : ∀ᵐ y ∂μ, |y| ≤ 1) (b : Bool) :
    (∫⁻ y, ENNReal.ofReal ((1+signVal b*clipY 1 y)/2) ∂μ) =
      ENNReal.ofReal ((1+signVal b*(∫ y, y ∂μ))/2) := by
  have hy : Integrable (fun y : ℝ => y) μ :=
    (integrable_const (1:ℝ)).mono' measurable_id.aestronglyMeasurable (by
      filter_upwards [hb] with y hy
      simpa only [Real.norm_eq_abs] using hy)
  have hclip : (fun y => clipY 1 y) =ᵐ[μ] fun y => y := by
    filter_upwards [hb] with y hy
    exact clipY_eq_of_abs_le 1 y hy
  have hi : Integrable (fun y => (1+signVal b*clipY 1 y)/2) μ :=
    ((integrable_const (1:ℝ)).add ((hy.congr hclip.symm).const_mul _)).div_const _
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun y => binary_sign_weight_nonneg b y))]
  rw [integral_div, integral_add (integrable_const _) ((hy.congr hclip.symm).const_mul _),
    integral_const_mul, integral_congr_ae hclip]
  simp

/-- Each arm's sign randomization is exactly its signed-binary realization. This statement assumes [the hb condition](hyp:hb), [the f condition](hyp:f). [This is the stated conclusion](goal). -/
-- @node: binary_arm_conversion_lintegral
lemma binary_arm_conversion_lintegral (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hb : ∀ᵐ y ∂μ, |y| ≤ 1) (f : Bool → ℝ≥0∞) :
    (∫⁻ y, ∑ b : Bool, ENNReal.ofReal ((1+signVal b*clipY 1 y)/2)*f b ∂μ) =
      ∑ b : Bool, ENNReal.ofReal ((1+signVal b*(∫ y, y ∂μ))/2)*f b := by
  rw [lintegral_finsetSum _ (fun b _ => by unfold clipY; fun_prop)]
  apply Finset.sum_congr rfl
  intro b _
  rw [lintegral_mul_const _ (by unfold clipY; fun_prop), binary_arm_weight_integral μ hb b]

/-- The atomic conversion kernel integrates by its two sign weights. This statement assumes [the f condition](hyp:f), [the hf condition](hyp:hf). [This is the stated conclusion](goal). -/
-- @node: binaryRecordKernel_lintegral
lemma binaryRecordKernel_lintegral (o : Record) (f : Record → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, f z ∂binaryRecordKernel o) =
      ∑ b : Bool, ENNReal.ofReal (binaryRecordWeight o b)*f (binaryRecordAtom o b) := by
  change (∫⁻ z, f z ∂∑ b : Bool, ENNReal.ofReal (binaryRecordWeight o b) • Measure.dirac (binaryRecordAtom o b)) = _
  rw [lintegral_finsetSum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac' _ hf, smul_eq_mul]

/-- The observed treatment mixture integrates by its two arm weights. This statement assumes [the f condition](hyp:f), [the hf condition](hyp:hf). [This is the stated conclusion](goal). -/
-- @node: recordMeasure_lintegral_arms
lemma recordMeasure_lintegral_arms (e : unitInterval → ℝ) (Q : Bool → Kernel unitInterval ℝ) [∀ a, IsMarkovKernel (Q a)]
    (x : unitInterval) (f : Bool × ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ r, f r ∂recordMeasure e Q x) =
      ENNReal.ofReal (e x)*(∫⁻ y, f (true,y) ∂Q true x)+
      ENNReal.ofReal (1-e x)*(∫⁻ y, f (false,y) ∂Q false x) := by
  rw [recordMeasure, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    Measure.dirac_prod, Measure.dirac_prod,
    lintegral_map hf measurable_prodMk_left, lintegral_map hf measurable_prodMk_left]
  simp only [smul_eq_mul]

/-- Bounded arm conversion agrees with the prescribed binary arm kernel. This statement assumes [the hb condition](hyp:hb), [the hm condition](hyp:hm), [the f condition](hyp:f), [the hf condition](hyp:hf). [This is the stated conclusion](goal). -/
-- @node: binary_arm_conversion_eq
lemma binary_arm_conversion_eq (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hb : ∀ᵐ y ∂μ, |y| ≤ 1) (m : Nuisance) (x : unitInterval)
    (hm : m x = ∫ y, y ∂μ) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ y, ∑ b : Bool, ENNReal.ofReal ((1+signVal b*clipY 1 y)/2)*f (signVal b) ∂μ) =
      ∫⁻ y, f y ∂binaryArm m x := by
  rw [binary_arm_conversion_lintegral μ hb, ← hm]
  change _ = ∫⁻ y, f y ∂binaryArmMeasure m x
  rw [binaryArmMeasure, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    lintegral_dirac' _ hf, lintegral_dirac' _ hf]
  simp only [Fintype.sum_bool, signVal, if_true, Bool.false_eq_true, if_false, one_mul, neg_one_mul]
  rfl

/-- Passing one bounded original record through sign conversion gives its binary realization. This statement assumes [the hm condition](hyp:hm). [This is the stated conclusion](goal). -/
-- @node: binaryRecordKernel_comp
lemma binaryRecordKernel_comp (w : Smooth3) (law : ObservedLaw) (hm : InBoundedModel w law) :
    binaryRecordKernel ∘ₘ law.P = (binaryConversion law).P := by
  let : IsProbabilityMeasure design := (inferInstance : IsProbabilityMeasure (volume : Measure unitInterval))
  have hc := binaryConversion_primitives law hm.baselineCap hm.effectCap
  let Qbin := fun a : Bool => binaryArm (if a then law.m0+law.tau else law.m0)
  have hb0 := boundedOutcome_arm_support law hm.uniform hm.overlap hm.boundedOutcome false
  have hb1 := boundedOutcome_arm_support law hm.uniform hm.overlap hm.boundedOutcome true
  let : ∀ a, IsMarkovKernel (Qbin a) := by
    intro a
    apply binaryArm_markov
    intro x
    cases a
    · exact (hm.baselineCap x).trans (by norm_num)
    · exact (abs_add_le _ _).trans (by linarith [hm.baselineCap x, hm.effectCap x])
  let : IsMarkovKernel (recordKernel law.e law.e.continuous.measurable law.Q) :=
    recordKernel_markov _ _ _ law.e_range law.markov
  let : IsMarkovKernel (recordKernel law.e law.e.continuous.measurable Qbin) :=
    recordKernel_markov _ _ _ law.e_range (fun a => inferInstance)
  apply Measure.ext_of_lintegral
  intro f hf
  change (∫⁻ o, f o ∂law.P.bind binaryRecordKernel) = _
  rw [Measure.lintegral_bind binaryRecordKernel.measurable.aemeasurable hf.aemeasurable, hc.2.2.2.1]
  conv_lhs => rw [law.record_version, show law.P.map X = design from hm.uniform]
  rw [Measure.lintegral_compProd (by fun_prop), Measure.lintegral_compProd hf]
  apply lintegral_congr_ae
  filter_upwards [hb0, hb1, law.mean0_version, law.mean1_version] with x h0 h1 hm0 hm1
  change (∫⁻ r, ∫⁻ z, f z ∂binaryRecordKernel (x,r) ∂recordMeasure law.e law.Q x) =
    ∫⁻ r, f (x,r) ∂recordMeasure law.e Qbin x
  simp_rw [binaryRecordKernel_lintegral _ f hf]
  rw [recordMeasure_lintegral_arms _ _ _ _ (by unfold binaryRecordWeight binaryRecordAtom X A Y clipY; fun_prop),
    recordMeasure_lintegral_arms _ _ _ _ (by fun_prop)]
  congr 1
  · congr 1
    exact binary_arm_conversion_eq (law.Q true x) h1 (law.m0+law.tau) x hm1
      (fun y => f (x,true,y)) (by fun_prop)
  · congr 1
    exact binary_arm_conversion_eq (law.Q false x) h0 law.m0 x hm0
      (fun y => f (x,false,y)) (by fun_prop)

/-- The independent sample conversion has the displayed finite sum over sign sequences. [This is the stated conclusion](goal). -/
-- @node: binaryProductKernel_atomic
lemma binaryProductKernel_atomic (n : ℕ) (data : Dataset n) :
    Causalean.Stat.finProductKernel n binaryRecordKernel data =
      ∑ signs : Fin n → Bool,
        ENNReal.ofReal (∏ i : Fin n, binaryRecordWeight (data i) (signs i)) •
          Measure.dirac (fun i => binaryRecordAtom (data i) (signs i)) := by
  classical
  rw [Causalean.Stat.finProductKernel_apply]
  apply Measure.pi_eq
  intro S hS
  have hrect : MeasurableSet (univ.pi S) := MeasurableSet.pi (Set.to_countable _) (fun i _ => hS i)
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ hrect]
  change (∑ signs : Fin n → Bool, ENNReal.ofReal (∏ i, binaryRecordWeight (data i) (signs i))*
    (univ.pi S).indicator 1 (fun i => binaryRecordAtom (data i) (signs i))) =
    ∏ i, (∑ b : Bool, ENNReal.ofReal (binaryRecordWeight (data i) b) •
      Measure.dirac (binaryRecordAtom (data i) b)) (S i)
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ (hS _)]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro signs _
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => (show 0 ≤ binaryRecordWeight (data i) (signs i) from binary_sign_weight_nonneg _ _)),
    Finset.prod_mul_distrib]
  congr 1
  by_cases hall : ∀ i, binaryRecordAtom (data i) (signs i) ∈ S i
  · simp [Set.indicator, Set.mem_pi, hall]
  · push Not at hall
    obtain ⟨i, hi⟩ := hall
    have hnot : (fun i => binaryRecordAtom (data i) (signs i)) ∉ univ.pi S := by
      intro h
      exact hi (h i (mem_univ i))
    rw [Set.indicator_of_notMem hnot]
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact Set.indicator_of_notMem hi _

/-- The kernel average of a sample test is its explicit finite randomization formula. [This is the stated conclusion](goal). -/
-- @node: binaryProductKernel_mean
lemma binaryProductKernel_mean (n : ℕ) (ψ : Test n) (data : Dataset n) (u : unitInterval) :
    Causalean.Stat.kernelMean (Causalean.Stat.finProductKernel n binaryRecordKernel)
      (fun z => ψ.1 (z,u)) data = binaryRandomizationRule n ψ (data,u) := by
  unfold Causalean.Stat.kernelMean
  rw [binaryProductKernel_atomic]
  have hi : ∀ signs ∈ (Finset.univ : Finset (Fin n → Bool)),
      Integrable (fun z : Dataset n => ψ.1 (z,u))
        (ENNReal.ofReal (∏ i : Fin n, binaryRecordWeight (data i) (signs i)) •
          Measure.dirac (fun i => binaryRecordAtom (data i) (signs i))) := by
    intro signs _
    exact (integrable_dirac (by simp) : Integrable (fun z : Dataset n => ψ.1 (z,u))
      (Measure.dirac (fun i => binaryRecordAtom (data i) (signs i)))).smul_measure ENNReal.ofReal_ne_top
  rw [integral_finsetSum_measure hi]
  simp only [integral_smul_measure, integral_dirac, smul_eq_mul]
  unfold binaryRandomizationRule
  apply Finset.sum_congr rfl
  intro signs _
  rw [ENNReal.toReal_ofReal (Finset.prod_nonneg (fun i _ =>
    (show 0 ≤ binaryRecordWeight (data i) (signs i) from binary_sign_weight_nonneg _ _)))]
  exact mul_comm _ _

/-- A bounded randomized test is integrable under its probability experiment. [This is the stated conclusion](goal). -/
-- @node: binary_test_integrable
lemma binary_test_integrable (n : ℕ) (ψ : Test n) (law : ObservedLaw) :
    Integrable ψ.1 (expLaw n law.P) := by
  let : IsProbabilityMeasure design := (inferInstance : IsProbabilityMeasure (volume : Measure unitInterval))
  unfold expLaw
  exact (integrable_const (1:ℝ)).mono' ψ.2.1.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (ψ.2.2 z).1]
      exact (ψ.2.2 z).2))

/-- Independent sign conversion integrates exactly, including the unchanged public seed. This statement assumes [the hm condition](hyp:hm). [This is the stated conclusion](goal). -/
-- @node: binaryRandomization_rejectProb
lemma binaryRandomization_rejectProb (w : Smooth3) (n : ℕ) (ψ : Test n)
    (law : ObservedLaw) (hm : InBoundedModel w law) :
    rejectProb n law.P (binaryRandomizationTest n ψ) = rejectProb n (binaryConversion law).P ψ := by
  let : IsProbabilityMeasure design := (inferInstance : IsProbabilityMeasure (volume : Measure unitInterval))
  have hs (u : unitInterval) :
      (∫ data, binaryRandomizationRule n ψ (data,u) ∂Measure.pi (fun _ : Fin n => law.P)) =
        ∫ data, ψ.1 (data,u) ∂Measure.pi (fun _ : Fin n => (binaryConversion law).P) := by
    calc
      _ = ∫ data, Causalean.Stat.kernelMean (Causalean.Stat.finProductKernel n binaryRecordKernel)
          (fun z => ψ.1 (z,u)) data ∂Measure.pi (fun _ : Fin n => law.P) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun data => (binaryProductKernel_mean n ψ data u).symm)
      _ = ∫ data, ψ.1 (data,u) ∂(Causalean.Stat.finProductKernel n binaryRecordKernel ∘ₘ
          Measure.pi (fun _ : Fin n => law.P)) :=
        Causalean.Stat.integral_kernelMean_eq_integral_comp _ _
          (ψ.2.1.comp measurable_prodMk_right)
          ⟨1, by norm_num, fun data => by
            rw [abs_of_nonneg (ψ.2.2 (data,u)).1]
            exact (ψ.2.2 (data,u)).2⟩
      _ = _ := by
        rw [Causalean.Stat.finProductKernel_comp_pi, binaryRecordKernel_comp w law hm]
  unfold rejectProb expLaw
  rw [integral_prod_symm _ (binary_test_integrable n (binaryRandomizationTest n ψ) law),
    integral_prod_symm _ (binary_test_integrable n ψ (binaryConversion law))]
  exact integral_congr_ae (Filter.Eventually.of_forall hs)

end CausalSmith.Stat.FinitepHomogeneityDensegamma
