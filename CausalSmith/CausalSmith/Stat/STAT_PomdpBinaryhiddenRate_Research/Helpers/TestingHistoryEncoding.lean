module
public import CausalSmith.Stat.STAT_PomdpBinaryhiddenRate_Research.Helpers.TestingFamilyCore
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.FiniteEncoding

/-!
# Finite encoding of the binary testing paths

The explicit testing weights are the chronological finite-model construction.
Transporting its history factorizations gives the required conditional laws.
-/

@[expose] public section

namespace CausalSmith.Stat.PomdpBinaryhiddenRate

open MeasureTheory ProbabilityTheory
open scoped BigOperators



/-- The testing reward and successor mass on a two-symbol reward alphabet. -/
-- @node: testingFiniteWeight
noncomputable def testingFiniteWeight (v : ℝ) (s : JointState 2 2) (a : Bool)
    (q : Fin 2 × JointState 2 2) : ℝ :=
  (if finTwoEquiv q.1 then testingRewardProb v s.2 else 1 - testingRewardProb v s.2) *
    (if q.2.2 = 1 then testingHiddenProb a else 1 - testingHiddenProb a) *
      testingEmission q.2.1 q.2.2

/-- All finite reward-transition weights are nonnegative in the testing range. [Under the listed formal conditions](hyp:hv), [the stated conclusion holds](goal).-/
-- @node: testingFiniteWeight_nonneg
lemma testingFiniteWeight_nonneg (v : ℝ) (hv : |v| ≤ 1 / 16)
    (s : JointState 2 2) (a : Bool) (q : Fin 2 × JointState 2 2) :
    0 ≤ testingFiniteWeight v s a q := by
  have hq := testingRewardProb_mem_Icc v hv s.2
  rcases q with ⟨y, x, h⟩
  fin_cases y <;> fin_cases x <;> fin_cases h <;> cases a <;>
    norm_num [testingFiniteWeight, finTwoEquiv, testingHiddenProb, testingEmission] <;>
    linarith [hq.1, hq.2]

/-- The finite reward-transition weights have unit total mass. [the stated conclusion holds](goal).-/
-- @node: testingFiniteWeight_sum
lemma testingFiniteWeight_sum (v : ℝ) (s : JointState 2 2) (a : Bool) :
    ∑ q, testingFiniteWeight v s a q = 1 := by
  cases a <;>
    simp [testingFiniteWeight, finTwoEquiv, Fintype.sum_prod_type,
      Fin.sum_univ_two, testingHiddenProb, testingEmission] <;> ring

/-- The finite PMF version of the joint testing kernel. -/
-- @node: testingFiniteKernel
noncomputable def testingFiniteKernel (v : ℝ) (s : JointState 2 2) (a : Bool) :
    PMF (Fin 2 × JointState 2 2) := CausalSmith.Stat.PomdpLatentOverlapMinimax.pmfOfRealWeight (testingFiniteWeight v s a)

/-- Normalization preserves the explicit finite testing kernel weights. [Under the listed formal conditions](hyp:hv), [the stated conclusion holds](goal).-/
-- @node: testingFiniteKernel_apply
lemma testingFiniteKernel_apply (v : ℝ) (hv : |v| ≤ 1 / 16)
    (s : JointState 2 2) (a : Bool) (q : Fin 2 × JointState 2 2) :
    testingFiniteKernel v s a q = ENNReal.ofReal (testingFiniteWeight v s a q) := by
  exact CausalSmith.Stat.PomdpLatentOverlapMinimax.pmfOfRealWeight_apply_of_nonneg_sum_one _
    (testingFiniteWeight_nonneg v hv s a) (testingFiniteWeight_sum v s a) q

/-- The stationary initialization as a finite PMF. -/
-- @node: testingFiniteInit
noncomputable def testingFiniteInit : PMF (JointState 2 2) :=
  CausalSmith.Stat.PomdpLatentOverlapMinimax.pmfOfRealWeight (fun s => (1 / 2 : ℝ) * testingEmission s.1 s.2)

/-- The initialization PMF preserves the displayed stationary masses. [the stated conclusion holds](goal).-/
-- @node: testingFiniteInit_apply
lemma testingFiniteInit_apply (s : JointState 2 2) :
    testingFiniteInit s = ENNReal.ofReal ((1 / 2 : ℝ) * testingEmission s.1 s.2) := by
  apply CausalSmith.Stat.PomdpLatentOverlapMinimax.pmfOfRealWeight_apply_of_nonneg_sum_one
  · intro s
    rcases s with ⟨x, h⟩
    fin_cases x <;> fin_cases h <;> norm_num [testingEmission]
  · norm_num [Fintype.sum_prod_type, Fin.sum_univ_two, testingEmission]

/-- The fair action PMF. -/
-- @node: testingFairPMF
noncomputable def testingFairPMF : PMF Bool :=
  CausalSmith.Stat.PomdpLatentOverlapMinimax.pmfOfRealWeight (fun _ => (1 / 2 : ℝ))

/-- Each action has probability one half. [the stated conclusion holds](goal).-/
-- @node: testingFairPMF_apply
lemma testingFairPMF_apply (a : Bool) :
    testingFairPMF a = ENNReal.ofReal (1 / 2 : ℝ) := by
  apply CausalSmith.Stat.PomdpLatentOverlapMinimax.pmfOfRealWeight_apply_of_nonneg_sum_one
  · intro _; norm_num
  · simp

/-- A chronological finite reward model for the testing experiment. -/
-- @node: testingFiniteModel
noncomputable def testingFiniteModel (T : Nat) (v : ℝ) :
    CausalSmith.Stat.PomdpLatentOverlapMinimax.FiniteRewardModel T 2 2 2 where
  kernel := testingFiniteKernel v
  rew := fun y => if finTwoEquiv y then 1 else 0
  rew_mem := by intro y; split_ifs <;> norm_num
  init := testingFiniteInit
  b := fun _ => testingFairPMF
  e := fun _ => testingFairPMF
  law := CausalSmith.Stat.PomdpLatentOverlapMinimax.finitePathPMF (testingFiniteKernel v) testingFiniteInit (fun _ => testingFairPMF)
  law_generated := CausalSmith.Stat.PomdpLatentOverlapMinimax.finitePathPMF_apply _ _ _



/-- Changing the reward alphabet between two finite symbols and Booleans. -/
-- @node: testingFinitePathEquiv
def testingFinitePathEquiv (T : Nat) :
    CausalSmith.Stat.PomdpLatentOverlapMinimax.FiniteTrajectory T 2 2 2 ≃ TestingPath T :=
  Equiv.prodCongr (Equiv.refl _) (Equiv.piCongrRight fun _ =>
    Equiv.prodCongr (Equiv.refl Bool) finTwoEquiv)

/-- The chronological finite weight is exactly the displayed testing weight. [Under the listed formal conditions](hyp:hv), [the stated conclusion holds](goal).-/
-- @node: testingFinitePathWeight_eq
lemma testingFinitePathWeight_eq (T : Nat) (v : ℝ) (hv : |v| ≤ 1 / 16)
    (c : CausalSmith.Stat.PomdpLatentOverlapMinimax.FiniteTrajectory T 2 2 2) :
    CausalSmith.Stat.PomdpLatentOverlapMinimax.finitePathWeight
      (testingFiniteKernel v) testingFiniteInit (fun _ => testingFairPMF) c =
      testingPathWeight v (testingFinitePathEquiv T c) := by
  have hi (s : JointState 2 2) : 0 ≤ (1 / 2 : ℝ) * testingEmission s.1 s.2 := by
    rcases s with ⟨x, h⟩
    fin_cases x <;> fin_cases h <;> norm_num [testingEmission]
  simp only [CausalSmith.Stat.PomdpLatentOverlapMinimax.finitePathWeight,
    testingFiniteInit_apply, testingFairPMF_apply, testingFiniteKernel_apply v hv,
    ENNReal.toReal_ofReal (hi _), ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ENNReal.toReal_ofReal (testingFiniteWeight_nonneg v hv _ _ _)]
  unfold testingPathWeight testingFinitePathEquiv testingFiniteWeight
  simp only [Equiv.prodCongr_apply, Prod.map, Pi.map, Equiv.refl_apply, Equiv.piCongrRight_apply]
  congr 1
  apply Finset.prod_congr rfl
  intro t _
  ring

/-- The finite path PMF has the explicit testing path masses. [Under the listed formal conditions](hyp:hv), [the stated conclusion holds](goal).-/
-- @node: testingFiniteModel_law_apply
lemma testingFiniteModel_law_apply (T : Nat) (v : ℝ) (hv : |v| ≤ 1 / 16)
    (c : CausalSmith.Stat.PomdpLatentOverlapMinimax.FiniteTrajectory T 2 2 2) :
    (testingFiniteModel T v).law c =
      ENNReal.ofReal (testingPathWeight v (testingFinitePathEquiv T c)) := by
  change CausalSmith.Stat.PomdpLatentOverlapMinimax.finitePathPMF _ _ _ c = _
  rw [CausalSmith.Stat.PomdpLatentOverlapMinimax.finitePathPMF,
    CausalSmith.Stat.PomdpLatentOverlapMinimax.pmfOfRealWeight_apply_of_nonneg_sum_one _
      (CausalSmith.Stat.PomdpLatentOverlapMinimax.finitePathWeight_nonneg _ _ _)
      (CausalSmith.Stat.PomdpLatentOverlapMinimax.sum_finitePathWeight_eq_one _ _ _),
    testingFinitePathWeight_eq T v hv]

/-- Decoding the finite kernel recovers the real-reward testing kernel. [Under the listed formal conditions](hyp:hv), [the stated conclusion holds](goal).-/
-- @node: testingFiniteModel_kernel_eq
lemma testingFiniteModel_kernel_eq (T : Nat) (v : ℝ) (hv : |v| ≤ 1 / 16)
    (s : JointState 2 2) (a : Bool) :
    (CausalSmith.Stat.PomdpLatentOverlapMinimax.embed (testingFiniteModel T v)).K s a =
      testingKernel v s a := by
  ext E hE
  change ((testingFiniteKernel v s a).map
    (fun q => ((if finTwoEquiv q.1 then (1 : ℝ) else 0), q.2))).toMeasure E = _
  rw [PMF.toMeasure_map_apply _ _ _ (measurable_of_finite _) hE,
    PMF.toMeasure_apply_fintype]
  simp only [Set.indicator_apply, Set.mem_preimage, testingFiniteKernel_apply v hv,
    testingKernel, Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply,
    Set.indicator, Pi.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Fintype.sum_prod_type]
  apply Fintype.sum_equiv finTwoEquiv
  intro y
  apply Finset.sum_congr rfl
  intro sp _
  simp only [testingFiniteWeight, mul_ite, Set.mem_preimage]
  rfl

/-- Decoding the finite path law recovers the displayed testing trajectory law. [Under the listed formal conditions](hyp:hv), [the stated conclusion holds](goal).-/
-- @node: testingFiniteModel_law_eq
lemma testingFiniteModel_law_eq (T : Nat) (v : ℝ) (hv : |v| ≤ 1 / 16) :
    (CausalSmith.Stat.PomdpLatentOverlapMinimax.embed (testingFiniteModel T v)).law =
      testingTrajectoryLaw T v := by
  ext E hE
  change ((testingFiniteModel T v).law.map
    (CausalSmith.Stat.PomdpLatentOverlapMinimax.decodeTraj (testingFiniteModel T v).rew)).toMeasure E = _
  rw [PMF.toMeasure_map_apply _ _ _ (measurable_of_finite _) hE,
    PMF.toMeasure_apply_fintype]
  simp only [testingFiniteModel_law_apply T v hv,
    testingTrajectoryLaw, Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply]
  apply Fintype.sum_equiv (testingFinitePathEquiv T)
  intro c
  simp only [Set.indicator, Set.mem_preimage, smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp only [testingFiniteModel_law_apply T v hv, Pi.one_apply, mul_one]
  rfl


/-- The decoded finite model has the fair behavior policy. [the stated conclusion holds](goal).-/
-- @node: testingFiniteModel_policy_eq
lemma testingFiniteModel_policy_eq (T : Nat) (v : ℝ) :
    (CausalSmith.Stat.PomdpLatentOverlapMinimax.embed (testingFiniteModel T v)).b =
      fun _ _ => (1 / 2 : ℝ) := by
  funext x a
  change (testingFairPMF a).toReal = _
  rw [testingFairPMF_apply, ENNReal.toReal_ofReal (by norm_num)]

/-- The testing joint kernel is the conditional law given the complete action history. [Under the listed formal conditions](hyp:hvFamily,hv), [the stated conclusion holds](goal).-/
-- @node: testingExperiment_kernelHistory
lemma testingExperiment_kernelHistory (T : Nat) (v : ℝ)
    (hvFamily : v = vT T ∨ v = -(vT T)) (hv : |v| ≤ 1 / 16) :
    ∀ t : Fin T,
      (testingExperiment T v hvFamily hv).law.map (histNextPair t) =
        ((testingExperiment T v hvFamily hv).law.map (histView t)).compProd
          (Kernel.comap (kernelOfK (testingExperiment T v hvFamily hv))
            (currentStateAction t) (measurable_currentStateAction t)) := by
  intro t
  have h := (CausalSmith.Stat.PomdpLatentOverlapMinimax.embed_pomdpKernelLaw
    (testingFiniteModel T v)).2 t
  have hkernel : (CausalSmith.Stat.PomdpLatentOverlapMinimax.embed
      (testingFiniteModel T v)).K = testingKernel v := by
    funext s a
    exact testingFiniteModel_kernel_eq T v hv s a
  unfold CausalSmith.Stat.PomdpLatentOverlapMinimax.kernelOfK at h
  rw [hkernel, testingFiniteModel_law_eq T v hv] at h
  exact h

/-- The fair behavior policy is the conditional action law given the complete state history. [Under the listed formal conditions](hyp:hvFamily,hv), [the stated conclusion holds](goal).-/
-- @node: testingExperiment_actionHistory
lemma testingExperiment_actionHistory (T : Nat) (v : ℝ)
    (hvFamily : v = vT T ∨ v = -(vT T)) (hv : |v| ≤ 1 / 16) :
    ∀ t : Fin T,
      (testingExperiment T v hvFamily hv).law.map (histActionPair t) =
        ((testingExperiment T v hvFamily hv).law.map (histStateView t)).compProd
          (Kernel.comap (behaviourKernel (testingExperiment T v hvFamily hv))
            (currentObsState t) (measurable_currentObsState t)) := by
  intro t
  have h := (CausalSmith.Stat.PomdpLatentOverlapMinimax.embed_sequentialIgnorability
    (testingFiniteModel T v)).2 t
  unfold CausalSmith.Stat.PomdpLatentOverlapMinimax.behaviourKernel at h
  rw [testingFiniteModel_policy_eq, testingFiniteModel_law_eq T v hv] at h
  exact h

end CausalSmith.Stat.PomdpBinaryhiddenRate
