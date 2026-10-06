module
public import CausalSmith.Stat.STAT_PomdpBinaryhiddenRate_Research.Constructions
public import Causalean.Mathlib.Probability.Certified.Existence
public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing

/-!
# Positive four-state testing family

The fair-policy binary-hidden family gives two stationary models separated in
target value while their observed trajectory laws have small KL divergence.
-/

public section

namespace CausalSmith.Stat.PomdpBinaryhiddenRate

open MeasureTheory

/-- The positive perturbation lies in the probability range. [Under the listed formal conditions](hyp:hT), [the stated conclusion holds](goal).-/
lemma vT_bound (T : Nat) (hT : 12 ≤ T) : |vT T| ≤ 1 / 16 := by
  have hv := vT_mem_Ioc T (by omega : 0 < T)
  rw [abs_of_pos hv.1]
  exact hv.2

/-- The negative perturbation lies in the probability range. [Under the listed formal conditions](hyp:hT), [the stated conclusion holds](goal).-/
lemma neg_vT_bound (T : Nat) (hT : 12 ≤ T) : |-(vT T)| ≤ 1 / 16 := by
  simpa only [abs_neg] using vT_bound T hT

-- @node: testingExperiment_policyOverlap
/-- The fair coincident policies of either testing experiment satisfy target
overlap for every nonnegative log-overlap radius. [Under the listed formal conditions](hyp:hvFamily,hv,hzeta), [the stated conclusion holds](goal).-/
lemma testingExperiment_policyOverlap (T : Nat) (v zeta : ℝ)
    (hvFamily : v = vT T ∨ v = -(vT T)) (hv : |v| ≤ 1 / 16)
    (hzeta : 0 ≤ zeta) :
    PolicyOverlap (policyFactor zeta) (testingExperiment T v hvFamily hv) := by
  have hL : 1 ≤ policyFactor zeta := by
    unfold policyFactor
    simpa using (Real.exp_le_exp.mpr hzeta : Real.exp 0 ≤ Real.exp zeta)
  constructor
  · intro x
    constructor
    · intro a
      change 0 ≤ (1 / 2 : ℝ)
      norm_num
    · change (∑ _a : Bool, (1 / 2 : ℝ)) = 1
      simp
  · intro x a
    change (1 / 2 : ℝ) ≤ policyFactor zeta * (1 / 2 : ℝ)
    nlinarith

-- @node: testingRewardProb_mem_Icc
/-- Both testing reward probabilities stay uniformly away from zero and one. [Under the listed formal conditions](hyp:hv,h), [the stated conclusion holds](goal).-/
lemma testingRewardProb_mem_Icc (v : ℝ) (hv : |v| ≤ 1 / 16) (h : Fin 2) :
    testingRewardProb v h ∈ Set.Icc (1 / 4 : ℝ) (3 / 4 : ℝ) := by
  have hv' := abs_le.mp hv
  fin_cases h <;> simp only [testingRewardProb, Fin.isValue] <;>
    simp <;> constructor <;> norm_num at * <;> linarith

-- @node: testingKernel_probability
/-- The explicit Bernoulli reward and successor-state kernel has unit mass. [Under the listed formal conditions](hyp:hv), [the stated conclusion holds](goal).-/
lemma testingKernel_probability (v : ℝ) (hv : |v| ≤ 1 / 16)
    (s : JointState 2 2) (a : Bool) :
    IsProbabilityMeasure (testingKernel v s a) := by
  constructor
  simp only [testingKernel, MeasureTheory.Measure.finsetSum_apply,
    MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.dirac_apply]
  simp only [Set.indicator_univ, Pi.one_apply, smul_eq_mul, mul_one]
  let w (y : Bool) (sp : JointState 2 2) : ℝ :=
    (if y then testingRewardProb v s.2 else 1 - testingRewardProb v s.2) *
      (if sp.2 = 1 then testingHiddenProb a else 1 - testingHiddenProb a) *
      testingEmission sp.1 sp.2
  change (∑ y : Bool, ∑ sp : JointState 2 2, ENNReal.ofReal (w y sp)) = 1
  have hq := testingRewardProb_mem_Icc v hv s.2
  have hw (y : Bool) (sp : JointState 2 2) : 0 ≤ w y sp := by
    dsimp [w]
    apply mul_nonneg
    · apply mul_nonneg
      · split_ifs <;> linarith [hq.1, hq.2]
      · cases a <;> split_ifs <;> norm_num [testingHiddenProb]
    · rcases sp with ⟨x, h⟩
      fin_cases x <;> fin_cases h <;> norm_num [testingEmission]
  have hinner (y : Bool) :
      (∑ sp : JointState 2 2, ENNReal.ofReal (w y sp)) =
        ENNReal.ofReal (∑ sp : JointState 2 2, w y sp) := by
    rw [ENNReal.ofReal_sum_of_nonneg]
    intro sp _
    exact hw y sp
  simp_rw [hinner]
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · have hsum : (∑ y : Bool, ∑ sp : JointState 2 2, w y sp) = 1 := by
      dsimp [w]
      simp_rw [mul_assoc, ← Finset.mul_sum, testingStepMass_sum, mul_one]
      exact testingRewardMass_sum v s.2
    rw [hsum]
    norm_num
  · intro y _
    exact Finset.sum_nonneg (by intro sp _; exact hw y sp)

-- @node: testingKernel_rewardSupport
/-- Every atom of the testing kernel has reward zero or one. [Under the listed formal conditions](hyp:hv), [the stated conclusion holds](goal).-/
lemma testingKernel_rewardSupport (v : ℝ) (hv : |v| ≤ 1 / 16)
    (s : JointState 2 2) (a : Bool) :
    testingKernel v s a {q | q.1 ∈ Set.Icc (0 : ℝ) 1} = 1 := by
  have hmass := (testingKernel_probability v hv s a).measure_univ
  convert hmass using 1
  simp [testingKernel]

-- @node: testingExperiment_policyKernel_eq
/-- Averaging the testing transition over the fair action gives the same row
at every current state, independently of the reward perturbation. [Under the listed formal conditions](hyp:hvFamily,hv), [the stated conclusion holds](goal).-/
lemma testingExperiment_policyKernel_eq (T : Nat) (v : ℝ)
    (hvFamily : v = vT T ∨ v = -(vT T)) (hv : |v| ≤ 1 / 16)
    (s sp : JointState 2 2) :
    policyKernel (testingExperiment T v hvFamily hv)
      (testingExperiment T v hvFamily hv).e s sp = testingNextStateMass sp := by
  have hq := testingRewardProb_mem_Icc v hv s.2
  have hq0 : 0 ≤ testingRewardProb v s.2 := le_trans (by norm_num) hq.1
  have hq1 : 0 ≤ 1 - testingRewardProb v s.2 := by linarith [hq.2]
  rcases sp with ⟨px, ph⟩
  fin_cases px <;> fin_cases ph <;>
    simp [policyKernel, testingExperiment, testingKernel, testingNextStateMass,
      testingHiddenProb, testingEmission, Fintype.sum_prod_type,
      Fin.sum_univ_two, ENNReal.toReal_add] <;>
    norm_num [ENNReal.toReal_ofReal, hq0, hq1] <;> ring

-- @node: testingExperiment_stationary
/-- The common transition row is a stationary probability vector. [Under the listed formal conditions](hyp:hvFamily,hv), [the stated conclusion holds](goal).-/
lemma testingExperiment_stationary (T : Nat) (v : ℝ)
    (hvFamily : v = vT T ∨ v = -(vT T)) (hv : |v| ≤ 1 / 16) :
    IsStationary
      (policyKernel (testingExperiment T v hvFamily hv)
        (testingExperiment T v hvFamily hv).e)
      testingNextStateMass := by
  constructor
  · constructor
    · intro sp
      rcases sp with ⟨x, h⟩
      fin_cases x <;> fin_cases h <;>
        norm_num [testingNextStateMass, testingHiddenProb, testingEmission]
    · exact testingNextStateMass_sum
  · funext sp
    change (∑ s, testingNextStateMass s *
      policyKernel (testingExperiment T v hvFamily hv)
        (testingExperiment T v hvFamily hv).e s sp) = testingNextStateMass sp
    simp_rw [testingExperiment_policyKernel_eq]
    simp [← Finset.sum_mul, testingNextStateMass_sum]

-- @node: testingExperiment_stationaryLaw_eq
/-- The selected stationary law of a testing experiment is its common
transition row. [Under the listed formal conditions](hyp:hvFamily,hv,hS), [the stated conclusion holds](goal).-/
lemma testingExperiment_stationaryLaw_eq (T : Nat) (v : ℝ)
    (hvFamily : v = vT T ∨ v = -(vT T)) (hv : |v| ≤ 1 / 16)
    (hS : IsStationary
      (policyKernel (testingExperiment T v hvFamily hv)
        (testingExperiment T v hvFamily hv).e)
      (stationaryLaw (policyKernel (testingExperiment T v hvFamily hv)
        (testingExperiment T v hvFamily hv).e))) :
    stationaryLaw (policyKernel (testingExperiment T v hvFamily hv)
      (testingExperiment T v hvFamily hv).e) = testingNextStateMass := by
  funext sp
  have hh := congrFun hS.2 sp
  change (∑ s, stationaryLaw (policyKernel
    (testingExperiment T v hvFamily hv)
    (testingExperiment T v hvFamily hv).e) s *
    policyKernel (testingExperiment T v hvFamily hv)
      (testingExperiment T v hvFamily hv).e s sp) = _ at hh
  simp_rw [testingExperiment_policyKernel_eq] at hh
  simpa [← Finset.sum_mul, hS.1.2] using hh.symm

-- @node: testingExperiment_contraction
/-- The common transition row contracts every pair of state distributions. [Under the listed formal conditions](hyp:hvFamily,hv,hAlpha), [the stated conclusion holds](goal).-/
lemma testingExperiment_contraction (T : Nat) (v : ℝ)
    (hvFamily : v = vT T ∨ v = -(vT T)) (hv : |v| ≤ 1 / 16)
    (alpha : ℝ) (hAlpha : 0 ≤ alpha) :
    BehaviorContraction alpha (testingExperiment T v hvFamily hv) ∧
      TargetContraction alpha (testingExperiment T v hvFamily hv) := by
  let M := testingExperiment T v hvFamily hv
  have hcommon : Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.ContractsL1
      (policyKernel M M.e) alpha := by
    intro p q hp hq
    have hstep : Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.markovStep p
        (policyKernel M M.e) =
        Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.markovStep q
          (policyKernel M M.e) := by
      funext sp
      change (∑ s, p s * policyKernel M M.e s sp) =
        (∑ s, q s * policyKernel M M.e s sp)
      dsimp only [M]
      simp_rw [testingExperiment_policyKernel_eq]
      simp only [← Finset.sum_mul, hp.2, hq.2, one_mul]
    rw [hstep]
    simpa only [Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.l1Distance,
      sub_self, abs_zero, Finset.sum_const_zero] using
      (mul_nonneg hAlpha (Finset.sum_nonneg (by intro i hi; exact abs_nonneg _)))
  constructor
  · change Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.ContractsL1
      (policyKernel M M.b) alpha
    simpa [M, testingExperiment] using hcommon
  · exact hcommon

-- @node: testingKernel_reward_integral
/-- Integrating the reward coordinate of a testing kernel recovers its Bernoulli parameter. [Under the listed formal conditions](hyp:hv), [the stated conclusion holds](goal).-/
lemma testingKernel_reward_integral (v : ℝ) (hv : |v| ≤ 1 / 16)
    (s : JointState 2 2) (a : Bool) :
    (∫ p, p.1 ∂testingKernel v s a) = testingRewardProb v s.2 := by
  rw [testingKernel, MeasureTheory.integral_finsetSum_measure (by
    intro y hy
    apply MeasureTheory.integrable_finsetSum_measure.mpr
    intro sp hsp
    exact (MeasureTheory.integrable_dirac (by simp)).smul_measure (by simp))]
  simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false]
  rw [MeasureTheory.integral_finsetSum_measure (by
    intro sp hsp
    exact (MeasureTheory.integrable_dirac (by simp)).smul_measure (by simp))]
  rw [MeasureTheory.integral_finsetSum_measure (by
    intro sp hsp
    exact (MeasureTheory.integrable_dirac (by simp)).smul_measure (by simp))]
  simp only [MeasureTheory.integral_smul_measure, MeasureTheory.integral_dirac]
  have hq0 : 0 ≤ testingRewardProb v s.2 :=
    le_trans (by norm_num) (testingRewardProb_mem_Icc v hv s.2).1
  simp only [smul_eq_mul, mul_one, mul_zero, Finset.sum_const_zero, add_zero]
  cases a <;>
    simp [Fintype.sum_prod_type, Fin.sum_univ_two, testingHiddenProb,
      testingEmission, ENNReal.toReal_ofReal, hq0] <;>
    norm_num [ENNReal.toReal_ofReal, hq0] <;>
    ring

-- @node: testingExperiment_rewardRegression_eq
/-- The testing reward regression depends only on the current hidden state. [Under the listed formal conditions](hyp:hvFamily,hv), [the stated conclusion holds](goal).-/
lemma testingExperiment_rewardRegression_eq (T : Nat) (v : ℝ)
    (hvFamily : v = vT T ∨ v = -(vT T)) (hv : |v| ≤ 1 / 16)
    (s : JointState 2 2) :
    rewardRegression (testingExperiment T v hvFamily hv) s =
      testingRewardProb v s.2 := by
  simp [rewardRegression, testingExperiment, testingKernel_reward_integral v hv]

-- @node: testingExperiment_targetValue_eq
/-- Every stationary testing experiment has target value one half plus its perturbation. [Under the listed formal conditions](hyp:hvFamily,hv,hS), [the stated conclusion holds](goal).-/
lemma testingExperiment_targetValue_eq (T : Nat) (v : ℝ)
    (hvFamily : v = vT T ∨ v = -(vT T)) (hv : |v| ≤ 1 / 16)
    (hS : IsStationary
      (policyKernel (testingExperiment T v hvFamily hv)
        (testingExperiment T v hvFamily hv).e)
      (stationaryLaw (policyKernel (testingExperiment T v hvFamily hv)
        (testingExperiment T v hvFamily hv).e))) :
    targetValue (testingExperiment T v hvFamily hv) = 1 / 2 + v := by
  simp only [targetValue]
  rw [testingExperiment_stationaryLaw_eq T v hvFamily hv hS]
  simp_rw [testingExperiment_rewardRegression_eq T v hvFamily hv]
  simp [testingNextStateMass, testingHiddenProb, testingEmission,
    testingRewardProb, Fintype.sum_prod_type, Fin.sum_univ_two]
  <;> ring

-- @node: coincidentPolicy_occupancy_bound
/-- A stationary on-policy law obeys every occupancy-ratio bound above one. [Under the listed formal conditions](hyp:hS,heq,hC), [the stated conclusion holds](goal).-/
lemma coincidentPolicy_occupancy_bound {T : Nat}
    (M : RawPomdpExperiment T 2 2) (hS : StationaryStart M)
    (heq : M.e = M.b) (C : ℝ) (hC : 1 < C) (s : JointState 2 2) :
    stationaryLaw (policyKernel M M.e) s ≤
      C * stationaryLaw (policyKernel M M.b) s := by
  rw [heq]
  have hs : 0 ≤ stationaryLaw (policyKernel M M.b) s := hS.1.1.1 s
  nlinarith

-- @node: testingPathWeight_initial_sum
/-- Summing every continuation of a fixed initial state recovers its
initial mass. [the stated conclusion holds](goal).-/
lemma testingPathWeight_initial_sum (T : Nat) (v : ℝ)
    (s : JointState 2 2) :
    (∑ c : TestingPath T,
      if c.1 0 = s then testingPathWeight v c else 0) =
      (1 / 2 : ℝ) * testingEmission s.1 s.2 := by
  let step (xs : Fin (T + 1) → JointState 2 2)
      (t : Fin T) (ay : Bool × Bool) : ℝ :=
    (1 / 2 : ℝ) *
      (if ay.2 then testingRewardProb v (xs t.castSucc).2
        else 1 - testingRewardProb v (xs t.castSucc).2) *
      (if (xs t.succ).2 = 1 then testingHiddenProb ay.1
        else 1 - testingHiddenProb ay.1) *
      testingEmission (xs t.succ).1 (xs t.succ).2
  have hpi (xs : Fin (T + 1) → JointState 2 2) :
      (∑ ys : Fin T → Bool × Bool, ∏ t : Fin T, step xs t (ys t)) =
        ∏ t : Fin T, ∑ ay : Bool × Bool, step xs t ay := by
    simpa [Fintype.piFinset_univ] using
      (Finset.sum_prod_piFinset (Finset.univ : Finset (Bool × Bool)) (step xs))
  have hq : (∑ f : Fin T → JointState 2 2,
      ∏ t : Fin T, testingNextStateMass (f t)) = 1 := by
    simpa [Fintype.piFinset_univ, testingNextStateMass_sum] using
      (Finset.sum_prod_piFinset
        (Finset.univ : Finset (JointState 2 2))
        (fun (_ : Fin T) sp => testingNextStateMass sp))
  calc
    _ = ∑ xs : Fin (T + 1) → JointState 2 2,
          (if xs 0 = s then (1 / 2 : ℝ) *
            testingEmission (xs 0).1 (xs 0).2 else 0) *
            ∏ t : Fin T, testingNextStateMass (xs t.succ) := by
      simp only [Fintype.sum_prod_type, testingPathWeight]
      apply Finset.sum_congr rfl
      intro xs _
      by_cases hs : xs 0 = s
      · simp only [if_pos hs]
        rw [← Finset.mul_sum, hpi xs]
        congr 1
        apply Finset.prod_congr rfl
        intro t _
        exact testingStepMarginal_sum v (xs t.castSucc) (xs t.succ)
      · simp [hs]
    _ = ∑ z : JointState 2 2 × (Fin T → JointState 2 2),
          (if z.1 = s then (1 / 2 : ℝ) *
            testingEmission z.1.1 z.1.2 else 0) *
            ∏ t : Fin T, testingNextStateMass (z.2 t) := by
      exact (Fintype.sum_equiv
        (Fin.consEquiv (fun _ : Fin (T + 1) => JointState 2 2)) _ _
        (by intro z; simp)).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum, hq, mul_one]
      simp

end CausalSmith.Stat.PomdpBinaryhiddenRate
