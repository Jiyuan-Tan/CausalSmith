module
public import CausalSmith.Stat.STAT_PomdpBinaryhiddenRate_Research.Helpers.TestingHistoryEncoding

/-!
# Testing family membership

History factorization, class membership, and positivity of the testing laws.
-/

public section

namespace CausalSmith.Stat.PomdpBinaryhiddenRate

open MeasureTheory

/-- The finite path weights realize the conditional reward/transition law,
fair-action assignment, and stationary initial state. [Under the listed formal conditions](hyp:hvFamily,hv), [the stated conclusion holds](goal).-/
-- @node: testingExperiment_historyConditions
lemma testingExperiment_historyConditions (T : Nat) (v : ℝ)
    (hvFamily : v = vT T ∨ v = -(vT T)) (hv : |v| ≤ 1 / 16) :
    let M := testingExperiment T v hvFamily hv
    PomdpKernelLaw M ∧ SequentialIgnorability M ∧ StationaryStart M := by
  dsimp
  constructor
  · refine ⟨testingKernel_probability v hv, testingKernel_rewardSupport v hv, ?_⟩
    exact testingExperiment_kernelHistory T v hvFamily hv
  constructor
  · constructor
    · intro x
      constructor
      · intro a
        change 0 ≤ (1 / 2 : ℝ)
        norm_num
      · change (∑ _a : Bool, (1 / 2 : ℝ)) = 1
        simp
    · exact testingExperiment_actionHistory T v hvFamily hv
  · constructor
    · exact stationaryLaw_isStationary_of_exists
        ⟨testingNextStateMass, testingExperiment_stationary T v hvFamily hv⟩
    · intro s
      have hS : IsStationary
          (policyKernel (testingExperiment T v hvFamily hv)
            (testingExperiment T v hvFamily hv).e)
          (stationaryLaw (policyKernel (testingExperiment T v hvFamily hv)
            (testingExperiment T v hvFamily hv).e)) :=
        stationaryLaw_isStationary_of_exists
          ⟨testingNextStateMass, testingExperiment_stationary T v hvFamily hv⟩
      have hbe : (testingExperiment T v hvFamily hv).b =
          (testingExperiment T v hvFamily hv).e := rfl
      rw [hbe, testingExperiment_stationaryLaw_eq T v hvFamily hv hS]
      have hmass : testingNextStateMass s =
          (1 / 2 : ℝ) * testingEmission s.1 s.2 := by
        rcases s with ⟨x, h⟩
        fin_cases x <;> fin_cases h <;>
          norm_num [testingNextStateMass, testingHiddenProb, testingEmission]
      rw [hmass]
      change ((testingTrajectoryLaw T v).map
          (stateAt (T := T) (nX := 2) (nH := 2) 0)) {s} = _
      rw [Measure.map_apply (by unfold stateAt; fun_prop) (MeasurableSet.singleton s)]
      simp only [testingTrajectoryLaw, MeasureTheory.Measure.finsetSum_apply,
        MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.dirac_apply]
      simp only [Set.indicator, Set.mem_preimage, Set.mem_singleton_iff,
        stateAt, decodeTestingPath, Pi.one_apply, smul_eq_mul]
      conv_lhs =>
        arg 2
        ext c
        rw [show ENNReal.ofReal (testingPathWeight v c) *
            (if c.1 0 = s then (1 : ENNReal) else 0) =
            ENNReal.ofReal (if c.1 0 = s then testingPathWeight v c else 0) by
              split_ifs <;> simp]
      rw [← ENNReal.ofReal_sum_of_nonneg]
      · rw [testingPathWeight_initial_sum]
      · intro c _
        split_ifs
        · exact testingPathWeight_nonneg v hv c
        · exact le_refl _

-- @node: testingExperiment_class_of_history
/-- The explicit testing laws meet the remaining overlap and contraction
conditions once their finite-history factorization is established. [Under the listed formal conditions](hyp:ht0,hzeta,hvFamily,hv), [the stated conclusion holds](goal).-/
lemma testingExperiment_class_of_history (T : Nat) (t0 zeta v : ℝ)
    (ht0 : 0 < t0) (hzeta : 0 ≤ zeta)
    (hvFamily : v = vT T ∨ v = -(vT T)) (hv : |v| ≤ 1 / 16) :
    BinaryPomdpClass t0 zeta (testingExperiment T v hvFamily hv) := by
  rcases testingExperiment_historyConditions T v hvFamily hv with ⟨hK, hI, hS⟩
  have hAlpha : 0 ≤ mixingAlpha t0 := by
    unfold mixingAlpha
    exact (Real.exp_pos _).le
  have hContract := testingExperiment_contraction T v hvFamily hv
    (mixingAlpha t0) hAlpha
  exact {
    t0_pos := ht0
    zeta_nonneg := hzeta
    pomdp_kernel := hK
    sequential_ignorability := hI
    stationary_start := hS
    policy_overlap := testingExperiment_policyOverlap T v zeta hvFamily hv hzeta
    behavior_contraction := hContract.1
    target_contraction := hContract.2 }

/-- Every testing path has strictly positive mass throughout the perturbation range. [Under the listed formal conditions](hyp:hv), [the stated conclusion holds](goal).-/
-- @node: testingPathWeight_pos
lemma testingPathWeight_pos {T : Nat} (v : ℝ) (hv : |v| ≤ 1 / 16)
    (c : TestingPath T) : 0 < testingPathWeight v c := by
  have hreward (h : Fin 2) :
      0 < testingRewardProb v h ∧ testingRewardProb v h < 1 := by
    have hq := testingRewardProb_mem_Icc v hv h
    constructor <;> linarith [hq.1, hq.2]
  have hhidden (a : Bool) :
      0 < testingHiddenProb a ∧ testingHiddenProb a < 1 := by
    cases a <;> norm_num [testingHiddenProb]
  have hemission (x h : Fin 2) : 0 < testingEmission x h := by
    unfold testingEmission
    split_ifs <;> norm_num
  unfold testingPathWeight
  apply mul_pos
  · exact mul_pos (by norm_num) (hemission _ _)
  · apply Finset.prod_pos
    intro t _
    apply mul_pos
    · apply mul_pos
      · apply mul_pos (by norm_num)
        split_ifs
        · exact (hreward _).1
        · linarith [(hreward (c.1 t.castSucc).2).2]
      · split_ifs
        · exact (hhidden _).1
        · linarith [(hhidden (c.2 t).1).2]
    · exact hemission _ _

/-- The testing laws have common finite support, hence every alternative is
absolutely continuous with respect to every other admissible alternative. [Under the listed formal conditions](hyp:hw), [the stated conclusion holds](goal).-/
-- @node: testingTrajectoryLaw_absolutelyContinuous
lemma testingTrajectoryLaw_absolutelyContinuous (T : Nat) (v w : ℝ)
    (hw : |w| ≤ 1 / 16) :
    testingTrajectoryLaw T v ≪ testingTrajectoryLaw T w := by
  intro A hA
  simp only [testingTrajectoryLaw, Measure.finsetSum_apply,
    Measure.smul_apply, smul_eq_mul] at hA ⊢
  have hzero := Finset.sum_eq_zero_iff.mp hA
  apply Finset.sum_eq_zero_iff.mpr
  intro c hc
  have hc0 := hzero c hc
  have hpos : ENNReal.ofReal (testingPathWeight w c) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (testingPathWeight_pos w hw c))
  have hdirac : Measure.dirac (decodeTestingPath c) A = 0 :=
    (mul_eq_zero.mp hc0).resolve_left hpos
  rw [hdirac, mul_zero]

/-- Finite support and common positive path masses give finite KL divergence,
which remains finite after projection to the observed trajectory. [Under the listed formal conditions](hyp:hvFamily,hv,hwFamily,hw), [the stated conclusion holds](goal).-/
-- @node: testingObservedLaw_klDiv_ne_top
lemma testingObservedLaw_klDiv_ne_top (T : Nat) (v w : ℝ)
    (hvFamily : v = vT T ∨ v = -(vT T)) (hv : |v| ≤ 1 / 16)
    (hwFamily : w = vT T ∨ w = -(vT T)) (hw : |w| ≤ 1 / 16) :
    InformationTheory.klDiv
      (obsLaw (testingExperiment T v hvFamily hv))
      (obsLaw (testingExperiment T w hwFamily hw)) ≠ ⊤ := by
  let := testingTrajectoryLaw_isProbability T v hv
  let := testingTrajectoryLaw_isProbability T w hw
  have hI : Integrable (llr (testingTrajectoryLaw T v) (testingTrajectoryLaw T w))
      (testingTrajectoryLaw T v) := by
    rw [testingTrajectoryLaw]
    apply integrable_finsetSum_measure.mpr
    intro c _
    exact (integrable_dirac (by simp)).smul_measure (by simp)
  have hfin := InformationTheory.klDiv_ne_top
    (testingTrajectoryLaw_absolutelyContinuous T v w hw) hI
  have hproj : Measurable (obsProj (T := T) (nX := 2) (nH := 2)) := by
    unfold obsProj curState actionAt rewardAt
    fun_prop
  exact ne_top_of_le_ne_top hfin
    (InformationTheory.klDiv_map_le (testingTrajectoryLaw T v)
      (testingTrajectoryLaw T w) hproj)

end CausalSmith.Stat.PomdpBinaryhiddenRate
