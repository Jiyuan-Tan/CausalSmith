module
public import CausalSmith.Stat.STAT_PomdpBinaryhiddenRate_Research.Helpers.ScoreMoments
public import CausalSmith.Stat.STAT_PomdpBinaryhiddenRate_Research.Helpers.ModelRegularity
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.PhiwFutureEndpoint
public import Mathlib.Probability.Moments.Variance

/-!
# Observable intervention moments

The action-weighted short-history scores identify target-policy transition
moments. Their second moments and separated-window covariances are controlled
by policy overlap and behavior contraction.
-/

@[expose] public section

namespace CausalSmith.Stat.PomdpBinaryhiddenRate

open MeasureTheory
open scoped BigOperators
open Causalean.Mathlib.Probability.FiniteMarkovOscillation

-- @node: fourMatrixPower
/-- Matrix power of a four-state kernel, using matrix multiplication. -/
noncomputable def fourMatrixPower (P : FourMatrix) (k : Nat) : FourMatrix := P ^ k

/-- This result establishes the stated mathematical relation for the construction under consideration. [the stated conclusion holds](goal).
-/
-- @node: fourMatrixPower_zero
lemma fourMatrixPower_zero (P : FourMatrix) : fourMatrixPower P 0 = 1 := by
  simp [fourMatrixPower]

/-- Covariance of two observable score windows under the full trajectory law. -/
noncomputable def scoreCovariance {T : Nat} (M : RawPomdpExperiment T 2 2)
    (k : Nat) (t u : Fin T) : ℝ :=
  ∫ tau,
    (score k M.b M.e (obsProj tau) t - populationMoment M k t) *
    (score k M.b M.e (obsProj tau) u - populationMoment M k u) ∂M.law

/-- Likelihood peeling and backward Markov contraction control separated score windows.
The unit reward support gives oscillation one, rather than the signed-reward constant two. [Under the listed formal conditions](hyp:hM,htk,hu), [the stated conclusion holds](goal).-/
-- @node: scoreCovariance_le_separated
lemma scoreCovariance_le_separated {T k : Nat} {t0 zeta : ℝ}
    (M : RawPomdpExperiment T 2 2) (hM : BinaryPomdpClass t0 zeta M)
    (t u : Fin T) (htk : k ≤ t.val) (hu : k + 1 ≤ u.val - t.val) :
    |scoreCovariance M k t u| ≤ mixingAlpha t0 ^ (u.val - t.val - k - 1) := by
  let N := finitePomdpView M
  let gap := u.val - t.val - k - 1
  have hgap : t.val + 1 + gap + k < T := by dsimp [gap]; omega
  have hL : 1 ≤ policyFactor zeta := by
    simpa only [policyFactor, Real.exp_zero] using Real.exp_le_exp.mpr hM.zeta_nonneg
  obtain ⟨hK, hI, hO, hY⟩ := finitePomdpView_laws M hM.pomdp_kernel
    hM.sequential_ignorability hM.policy_overlap
  have hcross := PomdpLatentOverlapMinimax.integral_phiwScore_mul_eq_futureFunction_full
    (M := N) (k := k) (gap := gap) hI hO hL hK hY t htk hgap
  have hmean := PomdpLatentOverlapMinimax.integral_phiwScore_eq_futureFunction_full
    (M := N) (k := k) (gap := gap) hI hO hL hK hY t hgap
  let uu : Fin T := ⟨t.val + 1 + gap + k, hgap⟩
  have huu : uu = u := by apply Fin.ext; dsimp [uu, gap]; omega
  change (∫ tau, score k M.b M.e (obsProj tau) t *
    score k M.b M.e (obsProj tau) uu ∂M.law) = _ at hcross
  change (∫ tau, score k M.b M.e (obsProj tau) uu ∂M.law) = _ at hmean
  rw [huu] at hcross hmean
  let F := PomdpLatentOverlapMinimax.phiwFutureFunction N gap k
  open Causalean.Mathlib.Probability.FiniteMarkovOscillation in
  have hFosc : OscillationBound (mixingAlpha t0 ^ gap) F := by
    have hr := rewardRegression_unit M hM.pomdp_kernel hM.policy_overlap.1
    have hrosc : OscillationBound 1 (rewardRegression M) := by
      intro x y
      exact abs_le.mpr ⟨by linarith [(hr x).1, (hr y).2],
        by linarith [(hr x).2, (hr y).1]⟩
    have ha0 : 0 ≤ mixingAlpha t0 := Real.exp_nonneg _
    have ha1 : mixingAlpha t0 ≤ 1 := by
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (one_div_nonneg.mpr hM.t0_pos.le))
    have he := oscillationBound_markovOperatorIter (policyKernel M M.e)
      (fun s => ⟨(policyKernel_stochastic_of_kernelLaw M hM.pomdp_kernel M.e hM.policy_overlap.1).1 s,
        (policyKernel_stochastic_of_kernelLaw M hM.pomdp_kernel M.e hM.policy_overlap.1).2 s⟩)
      ha0 (fun p q hp hq => by
        have hc := hM.target_contraction p q hp hq
        unfold Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.l1Distance at hc
        nlinarith) hrosc k
    have he1 : OscillationBound 1
        (markovOperatorIter (policyKernel M M.e) k (rewardRegression M)) :=
      he.mono (by simpa using pow_le_one₀ ha0 ha1 (n := k))
    have hb := oscillationBound_markovOperatorIter (policyKernel M M.b)
      (fun s => ⟨(policyKernel_stochastic_of_kernelLaw M hM.pomdp_kernel M.b hM.sequential_ignorability.1).1 s,
        (policyKernel_stochastic_of_kernelLaw M hM.pomdp_kernel M.b hM.sequential_ignorability.1).2 s⟩)
      ha0 (fun p q hp hq => by
        have hc := hM.behavior_contraction p q hp hq
        unfold Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.l1Distance at hc
        nlinarith) he1 gap
    change OscillationBound (mixingAlpha t0 ^ gap)
      (markovOperatorIter (policyKernel M M.b) gap
        (markovOperatorIter (policyKernel M M.e) k (rewardRegression M)))
    simpa only [mul_one] using hb
  have hXt := PomdpLatentOverlapMinimax.phiwScore_memLp (k := k) hI hO hL hY 2 t
  have hXu := PomdpLatentOverlapMinimax.phiwScore_memLp (k := k) hI hO hL hY 2 u
  have hXtFull : MemLp (fun tau => score k M.b M.e (obsProj tau) t) 2 M.law := by
    exact (memLp_map_measure_iff
      (PomdpLatentOverlapMinimax.phiwScore_measurable M.b M.e t).aestronglyMeasurable
      PomdpLatentOverlapMinimax.measurable_obsProj.aemeasurable).mp hXt
  have hXuFull : MemLp (fun tau => score k M.b M.e (obsProj tau) u) 2 M.law := by
    exact (memLp_map_measure_iff
      (PomdpLatentOverlapMinimax.phiwScore_measurable M.b M.e u).aestronglyMeasurable
      PomdpLatentOverlapMinimax.measurable_obsProj.aemeasurable).mp hXu
  have hFint : Integrable (fun tau => F (nextState t tau)) M.law := by
    apply (integrable_const (∑ s, ‖F s‖)).mono' (by unfold nextState; fun_prop)
    exact Filter.Eventually.of_forall (fun tau =>
      Finset.single_le_sum (fun s _ => norm_nonneg (F s)) (Finset.mem_univ _))
  have hc := PomdpLatentOverlapMinimax.abs_integral_mul_sub_mul_integral_le_oscillation
    M.law (hXtFull.integrable one_le_two) hFint
    (score_abs_first_moment_le_one M hM.pomdp_kernel hM.sequential_ignorability
      hM.policy_overlap hL t htk) hFosc
  change |(∫ tau, score k M.b M.e (obsProj tau) t * F (nextState t tau) ∂M.law) -
    populationMoment M k t * ∫ tau, F (nextState t tau) ∂M.law| ≤ _ at hc
  change |ProbabilityTheory.covariance
    (fun tau => score k M.b M.e (obsProj tau) t)
    (fun tau => score k M.b M.e (obsProj tau) u) M.law| ≤ _
  rw [ProbabilityTheory.covariance_eq_sub hXtFull hXuFull]
  simp only [Pi.mul_apply]
  rw [hcross, hmean]
  exact hc

/-- Each state coordinate integrates against the stationary behavior law. [Under the listed formal conditions](hyp:hK,hI,hS), [the stated conclusion holds](goal).-/
-- @node: integral_binary_curState_eq_stationary
lemma integral_binary_curState_eq_stationary {T : Nat}
    (M : RawPomdpExperiment T 2 2) (hK : PomdpKernelLaw M)
    (hI : SequentialIgnorability M) (hS : StationaryStart M)
    (t : Fin T) (F : JointState 2 2 → ℝ) :
    ∫ tau, F (curState t tau) ∂M.law =
      ∑ s, stationaryLaw (policyKernel M M.b) s * F s := by
  have hK' : PomdpLatentOverlapMinimax.PomdpKernelLaw (finitePomdpView M) :=
    ⟨hK.1, hK.2.2⟩
  have hI' : PomdpLatentOverlapMinimax.SequentialIgnorability (finitePomdpView M) := hI
  induction hn : t.val using Nat.strong_induction_on generalizing t F with
  | h n ih =>
    by_cases hn0 : n = 0
    · have ht0 : t = ⟨0, by omega⟩ := Fin.ext (hn.trans hn0)
      rw [ht0]
      have hm : Measurable (stateAt (T := T) (nX := 2) (nH := 2) 0) := by
        unfold stateAt
        fun_prop
      have hi : Integrable F
          (M.law.map (stateAt (T := T) (nX := 2) (nH := 2) 0)) := Integrable.of_finite
      change ∫ tau, F (stateAt 0 tau) ∂M.law = _
      rw [← integral_map hm.aemeasurable hi.aestronglyMeasurable,
        MeasureTheory.integral_fintype hi]
      apply Finset.sum_congr rfl
      intro s _
      change (M.law.map (stateAt (T := T) (nX := 2) (nH := 2) 0) {s}).toReal * F s = _
      rw [hS.2 s,
        ENNReal.toReal_ofReal (hS.1.1.1 s)]
    · let p : Fin T := ⟨n - 1, by omega⟩
      have hp : p.val + 1 < T := by dsimp [p]; omega
      have ht : PomdpLatentOverlapMinimax.nextEpoch p hp = t := by
        apply Fin.ext
        dsimp [PomdpLatentOverlapMinimax.nextEpoch, p]
        omega
      have hFB (s : JointState 2 2) : |F s| ≤ ∑ x, |F x| :=
        Finset.single_le_sum (fun x _ ↦ abs_nonneg (F x)) (Finset.mem_univ s)
      have hob := PomdpLatentOverlapMinimax.integrable_behaviorPeel_obligations hI'
        hK' p (fun _ ↦ (1 : ℝ)) measurable_const (integrable_const 1) F hFB
      have hstep := PomdpLatentOverlapMinimax.integral_history_mul_behavior_nextState hI'
        hK' p (fun _ ↦ (1 : ℝ)) F hob.1 hob.2
      simp only [one_mul] at hstep
      have hleft : (∫ z, F z.2.2 ∂(M.law.map (histNextPair p))) =
          ∫ tau, F (curState (PomdpLatentOverlapMinimax.nextEpoch p hp) tau) ∂M.law := by
        have hmF : AEStronglyMeasurable
            (fun z : ActionHistoryView T 2 2 p × Step 2 2 ↦ F z.2.2)
            (M.law.map (histNextPair p)) :=
          ((measurable_of_finite F).comp
            (measurable_snd.comp measurable_snd)).aestronglyMeasurable
        exact integral_map (f := fun z : ActionHistoryView T 2 2 p × Step 2 2 ↦ F z.2.2)
          (PomdpLatentOverlapMinimax.measurable_histNextPair p).aemeasurable hmF
      have hright : (∫ h, markovOperator (policyKernel M M.b) F h.2
          ∂(M.law.map (histStateView p))) =
          ∫ tau, markovOperator (policyKernel M M.b) F (curState p tau) ∂M.law := by
        exact integral_map
          (f := fun h : StateHistoryView T 2 2 p ↦
            markovOperator (policyKernel M M.b) F h.2)
          (PomdpLatentOverlapMinimax.measurable_histStateView p).aemeasurable
          (((measurable_of_finite (markovOperator (policyKernel M M.b) F)).comp
            measurable_snd).aestronglyMeasurable)
      change (∫ z, F z.2.2 ∂(M.law.map (histNextPair p))) =
        ∫ h, markovOperator (policyKernel M M.b) F h.2
          ∂(M.law.map (histStateView p)) at hstep
      rw [hleft, hright] at hstep
      rw [← ht, hstep, ih (n - 1) (by omega) p
        (markovOperator (policyKernel M M.b) F) rfl]
      unfold markovOperator
      calc
        ∑ s, stationaryLaw (policyKernel M M.b) s *
              ∑ x, policyKernel M M.b s x * F x =
            ∑ s, ∑ x, stationaryLaw (policyKernel M M.b) s *
              (policyKernel M M.b s x * F x) := by
          apply Finset.sum_congr rfl
          intro s _
          rw [Finset.mul_sum]
        _ = ∑ x, ∑ s, stationaryLaw (policyKernel M M.b) s *
              (policyKernel M M.b s x * F x) := Finset.sum_comm
        _ = ∑ x, (∑ s, stationaryLaw (policyKernel M M.b) s *
              policyKernel M M.b s x) * F x := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro s _
          ring
        _ = ∑ x, stationaryLaw (policyKernel M M.b) x * F x := by
          apply Finset.sum_congr rfl
          intro x _
          have hx := congrFun hS.1.2 x
          change (∑ s, stationaryLaw (policyKernel M M.b) s * policyKernel M M.b s x) =
            stationaryLaw (policyKernel M M.b) x at hx
          rw [hx]

/-- Iterating the Markov operator agrees with multiplying by matrix powers. [the stated conclusion holds](goal).-/
-- @node: binary_markovOperatorIter_eq_mulVec
lemma binary_markovOperatorIter_eq_mulVec
    (P : Matrix (JointState 2 2) (JointState 2 2) ℝ) (k : Nat)
    (r : JointState 2 2 → ℝ) :
    Causalean.Mathlib.Probability.FiniteMarkovOscillation.markovOperatorIter (fun i j => P i j) k r =
      Matrix.mulVec (P ^ k) r := by
  induction k with
  | zero => simp [Causalean.Mathlib.Probability.FiniteMarkovOscillation.markovOperatorIter]
  | succ k ih =>
    rw [Causalean.Mathlib.Probability.FiniteMarkovOscillation.markovOperatorIter_succ, ih,
      pow_succ']
    change Matrix.mulVec P (Matrix.mulVec (P ^ k) r) = _
    exact Matrix.mulVec_mulVec r P (P ^ k)

-- @node: lem:observable-intervention-moments
/-- The seven observable scores have the intervention identity, bounded second
moments, and geometric covariance decay for separated windows. [Under the listed formal conditions](hyp:hM), [the stated conclusion holds](goal).-/
lemma observable_intervention_moments {T : Nat} {t0 zeta : ℝ}
    (M : RawPomdpExperiment T 2 2) (hM : BinaryPomdpClass t0 zeta M) :
    ∀ k : Fin 7, ∀ t : Fin T, k.val ≤ t.val →
      populationMoment M k.val t =
        ∑ s, (Matrix.vecMul (stationaryLaw (policyKernel M M.b))
          (fourMatrixPower (Matrix.of (policyKernel M M.e)) k.val)) s *
          rewardRegression M s ∧
      (∫ tau, (score k.val M.b M.e (obsProj tau) t) ^ 2 ∂M.law) ≤
        (policyFactor zeta) ^ (k.val + 1) ∧
      ∀ u : Fin T, k.val + 1 ≤ u.val - t.val →
        |scoreCovariance M k.val t u| ≤
          (mixingAlpha t0) ^ (u.val - t.val - k.val - 1) := by
  intro k t hkt
  have hL : 1 ≤ policyFactor zeta := by
    simpa only [policyFactor, Real.exp_zero] using Real.exp_le_exp.mpr hM.zeta_nonneg
  refine ⟨?_, score_second_moment_le M hM.pomdp_kernel
    hM.sequential_ignorability hM.policy_overlap hL t hkt, ?_⟩
  · obtain ⟨hK, hI, hO, hY⟩ := finitePomdpView_laws M hM.pomdp_kernel
      hM.sequential_ignorability hM.policy_overlap
    let r : Fin T := ⟨t.val - k.val, by omega⟩
    have hhor : r.val + 0 + k.val < T := by dsimp [r]; omega
    have hp := PomdpLatentOverlapMinimax.integral_phiwScore_eq_futureFunction_from_state
      hI hO hL hK hY r hhor
    have hu : PomdpLatentOverlapMinimax.epochAdd
        (PomdpLatentOverlapMinimax.epochAdd r 0 (by omega)) k.val
        (by dsimp [PomdpLatentOverlapMinimax.epochAdd, r]; omega) = t := by
      apply Fin.ext
      dsimp [PomdpLatentOverlapMinimax.epochAdd, r]
      omega
    dsimp only at hp
    rw [hu] at hp
    simp only [finitePomdpView] at hp
    rw [PomdpLatentOverlapMinimax.obsLaw,
      integral_map PomdpLatentOverlapMinimax.measurable_obsProj.aemeasurable
        (PomdpLatentOverlapMinimax.phiwScore_measurable M.b M.e t).aestronglyMeasurable] at hp
    change populationMoment M k.val t =
      ∫ tau, Causalean.Mathlib.Probability.FiniteMarkovOscillation.markovOperatorIter
        (policyKernel M M.e) k.val (rewardRegression M) (curState r tau) ∂M.law at hp
    rw [hp, integral_binary_curState_eq_stationary M hM.pomdp_kernel
      hM.sequential_ignorability hM.stationary_start]
    have hiter := binary_markovOperatorIter_eq_mulVec
      (Matrix.of (policyKernel M M.e)) k.val (rewardRegression M)
    change markovOperatorIter (policyKernel M M.e) k.val (rewardRegression M) = _ at hiter
    rw [hiter]
    exact Matrix.dotProduct_mulVec _ _ _
  · intro u hu
    exact scoreCovariance_le_separated M hM t u hkt hu

/-- The zero-lag intervention identity under the four conditions used in the
coincident-policy reduction. [Under the listed formal conditions](hyp:ht0,hK,hI,hS,hB,heq), [the stated conclusion holds](goal).-/
-- @node: observable_intervention_moment_zero
lemma observable_intervention_moment_zero {T : Nat} {t0 : ℝ}
    (M : RawPomdpExperiment T 2 2)
    (ht0 : 0 < t0)
    (hK : PomdpKernelLaw M) (hI : SequentialIgnorability M)
    (hS : StationaryStart M) (hB : BehaviorContraction (mixingAlpha t0) M)
    (heq : M.e = M.b) (t : Fin T) :
    populationMoment M 0 t = targetValue M := by
  have hOverlap : PolicyOverlap (policyFactor 0) M := by
    refine ⟨?_, ?_⟩
    · simpa only [heq] using hI.1
    · intro x a
      simp only [heq, policyFactor, Real.exp_zero, one_mul, le_refl]
  have hClass : BinaryPomdpClass t0 0 M :=
    { t0_pos := ht0
      zeta_nonneg := le_refl 0
      pomdp_kernel := hK
      sequential_ignorability := hI
      stationary_start := hS
      policy_overlap := hOverlap
      behavior_contraction := hB
      target_contraction := by
        change Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.ContractsL1
          (policyKernel M M.e) (mixingAlpha t0)
        rw [heq]
        exact hB }
  have hm := (observable_intervention_moments M hClass ⟨0, by norm_num⟩ t (by norm_num)).1
  have hk : (⟨0, by norm_num⟩ : Fin 7).val = 0 := rfl
  rw [hk, fourMatrixPower_zero, Matrix.vecMul_one] at hm
  simpa only [targetValue, heq] using hm

end CausalSmith.Stat.PomdpBinaryhiddenRate
