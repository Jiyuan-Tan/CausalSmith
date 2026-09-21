module
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.PhiwFutureIteration

set_option linter.style.longLine false

/-! # Reward bounds on the behavior-stationary support -/

public section

namespace CausalSmith.Stat.PomdpLatentOverlapMinimax

open Causalean.Mathlib.Probability.FiniteMarkovOscillation
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

-- @node: rewardRegression_abs_le_one_of_behaviorSupport
/-- The trajectory reward bound controls the reward regression on every state charged by the
behavior stationary law. [the h T condition](hyp:hT); and [the h M condition](hyp:hM); and [the hs condition](hyp:hs). [the stated conclusion](goal). -/
lemma rewardRegression_abs_le_one_of_behaviorSupport {T nX nH : Nat} {t0 zeta C : ℝ}
    {M : RawPomdpExperiment T nX nH} (hT : 1 ≤ T)
    (hM : LatentOverlapClass t0 zeta C M) (s : JointState nX nH)
    (hs : 0 < stationaryLaw (policyKernel M M.b) s) :
    |rewardRegression M s| ≤ 1 := by
  let t : Fin T := ⟨0, hT⟩
  let J : StateHistoryView T nX nH t × Bool → ℝ :=
    fun z ↦ ∫ y, y.1 ∂(M.K z.1.2 z.2)
  have hJb : ∀ᵐ z ∂(M.law.map (histActionPair t)), |J z| ≤ 1 := by
    letI : IsMarkovKernel (kernelOfK M) := ⟨fun sa ↦ hM.pomdp_kernel.1 sa.1 sa.2⟩
    have hset : MeasurableSet
        {z : ActionHistoryView T nX nH t × Step nX nH | |z.2.1| ≤ 1} :=
      measurableSet_le (continuous_abs.measurable.comp
        (measurable_fst.comp measurable_snd)) measurable_const
    have hpair : ∀ᵐ z ∂(M.law.map (histNextPair t)), |z.2.1| ≤ 1 := by
      apply (MeasureTheory.ae_map_iff (measurable_histNextPair t).aemeasurable hset).2
      exact boundedReward_law_ae hM.bounded_reward t
    rw [hM.pomdp_kernel.2 t] at hpair
    have hsections := MeasureTheory.Measure.ae_ae_of_ae_compProd hpair
    filter_upwards [hsections] with z hz
    letI : IsProbabilityMeasure (M.K z.1.2 z.2) := hM.pomdp_kernel.1 z.1.2 z.2
    change ∀ᵐ y ∂(M.K z.1.2 z.2), |y.1| ≤ 1 at hz
    have hz' : ∀ᵐ y ∂(M.K z.1.2 z.2), ‖y.1‖ ≤ (1 : ℝ) := by
      simpa only [Real.norm_eq_abs] using hz
    simpa only [J, Real.norm_eq_abs, mul_one, probReal_univ] using
      (norm_integral_le_of_norm_le_const (μ := M.K z.1.2 z.2)
        (f := fun y : Step nX nH ↦ y.1) (C := (1 : ℝ)) hz')
  have hrow (a : Bool) (ha : 0 < M.b s.1 a) :
      |∫ y, y.1 ∂(M.K s a)| ≤ 1 := by
    let z : StateHistoryView T nX nH t × Bool :=
      ((((fun i ↦ Fin.elim0 i), (fun i ↦ Fin.elim0 i)), s), a)
    have hz_mass : 0 < (M.law.map (histActionPair t)) {z} := by
      letI : IsMarkovKernel (behaviourKernel M) := by
        constructor
        intro x
        constructor
        change (∑ a : Bool, ENNReal.ofReal (M.b x a) • Measure.dirac a) Set.univ = 1
        simp
        rw [← ENNReal.ofReal_add ((hM.sequential_ignorability.1 x).1 true)
          ((hM.sequential_ignorability.1 x).1 false)]
        rw [show M.b x true + M.b x false = 1 by
          simpa using (hM.sequential_ignorability.1 x).2]
        norm_num
      rw [hM.sequential_ignorability.2 t]
      rw [show {z} = {z.1} ×ˢ {a} by ext x; simp [z]]
      change 0 < (M.law.map (histStateView t)).compProd
        (Kernel.comap (behaviourKernel M) (currentObsState t) (measurable_currentObsState t))
        ({z.1} ×ˢ {a})
      rw [Measure.compProd_apply_prod (MeasurableSet.singleton _) (MeasurableSet.singleton _)]
      simp only [Measure.restrict_singleton]
      rw [Measure.map_apply (measurable_histStateView t) (MeasurableSet.singleton _)]
      have hpre : histStateView t ⁻¹' {z.1} =
          stateAt (T := T) (nX := nX) (nH := nH) 0 ⁻¹' {s} := by
        ext tau
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        constructor
        · intro hz'
          simpa [histStateView, curState, stateAt, t, z] using congrArg Prod.snd hz'
        · intro hs'
          change (((fun j : Fin 0 ↦ curState (prefixIndex t j) tau,
            fun j : Fin 0 ↦ tau.2 (prefixIndex t j)), curState t tau)) =
              (((fun i ↦ Fin.elim0 i), (fun i ↦ Fin.elim0 i)), s)
          congr 2
          · exact Subsingleton.elim _ _
          · exact Subsingleton.elim _ _
      rw [hpre, ← Measure.map_apply (by unfold stateAt; fun_prop)
        (MeasurableSet.singleton _), hM.stationary_start.2 s]
      have hba : 0 < (behaviourKernel M s.1) {a} := by
        change 0 < (∑ a' : Bool, ENNReal.ofReal (M.b s.1 a') • Measure.dirac a') {a}
        cases a <;> simp [ENNReal.ofReal_pos.mpr ha]
      simpa [currentObsState, z, ENNReal.ofReal_pos.mpr hs] using hba
    have hz : |J z| ≤ 1 := by
      by_contra hn
      have hzero : (M.law.map (histActionPair t)) {z} = 0 := by
        have hcompl := ae_iff.mp hJb
        apply le_antisymm
        · apply le_trans (measure_mono ?_) (le_of_eq hcompl)
          intro x hx
          simp only [Set.mem_singleton_iff] at hx
          subst x
          exact hn
        · exact bot_le
      exact (ne_of_gt hz_mass) hzero
    simpa [J, z] using hz
  unfold rewardRegression
  calc
    |∑ a : Bool, M.e s.1 a * ∫ p, p.1 ∂(M.K s a)| ≤
        ∑ a : Bool, |M.e s.1 a * ∫ p, p.1 ∂(M.K s a)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a : Bool, M.e s.1 a * 1 := by
      apply Finset.sum_le_sum
      intro a _
      rw [abs_mul, abs_of_nonneg ((hM.policy_overlap.1 s.1).1 a)]
      by_cases hea : M.e s.1 a = 0
      · simp [hea]
      · have hepos : 0 < M.e s.1 a :=
          lt_of_le_of_ne ((hM.policy_overlap.1 s.1).1 a) (Ne.symm hea)
        have hbpos : 0 < M.b s.1 a := by
          have hover := hM.policy_overlap.2 s.1 a
          by_contra hn
          have hb0 : M.b s.1 a = 0 := le_antisymm (le_of_not_gt hn)
            ((hM.sequential_ignorability.1 s.1).1 a)
          rw [hb0, mul_zero] at hover
          exact (not_lt_of_ge hover) hepos
        exact mul_le_mul_of_nonneg_left (hrow a hbpos)
          ((hM.policy_overlap.1 s.1).1 a)
    _ = 1 := by simpa using (hM.policy_overlap.1 s.1).2

-- @node: behaviorSupport_closed_policyKernel
/-- Either policy kernel preserves the support of the behavior stationary law. [the h M condition](hyp:hM); and [the hp condition](hyp:hp); and [the hs condition](hyp:hs); and [the hpx condition](hyp:hpx). [the stated conclusion](goal). -/
lemma behaviorSupport_closed_policyKernel {T nX nH : Nat} {t0 zeta C : ℝ}
    {M : RawPomdpExperiment T nX nH} (hM : LatentOverlapClass t0 zeta C M)
    (p : Policy nX) (hp : p = M.b ∨ p = M.e) {s x : JointState nX nH}
    (hs : 0 < stationaryLaw (policyKernel M M.b) s)
    (hpx : 0 < policyKernel M p s x) :
    0 < stationaryLaw (policyKernel M M.b) x := by
  have hpb : 0 < policyKernel M M.b s x := by
    rcases hp with rfl | rfl
    · exact hpx
    · by_contra hn
      have hb0 : policyKernel M M.b s x = 0 := le_antisymm (le_of_not_gt hn)
        ((policyKernel_probabilityVector M hM.pomdp_kernel M.b
          hM.sequential_ignorability.1 s).1 x)
      unfold policyKernel at hpx hb0
      have hterm (a : Bool) : M.b s.1 a * (M.K s a {q | q.2 = x}).toReal = 0 := by
        have hnonneg (a' : Bool) :
            0 ≤ M.b s.1 a' * (M.K s a' {q | q.2 = x}).toReal :=
          mul_nonneg ((hM.sequential_ignorability.1 s.1).1 a') ENNReal.toReal_nonneg
        exact (Finset.sum_eq_zero_iff_of_nonneg fun a' _ ↦ hnonneg a').mp hb0 a
          (Finset.mem_univ a)
      have heterm (a : Bool) : M.e s.1 a * (M.K s a {q | q.2 = x}).toReal = 0 := by
        by_cases hk : (M.K s a {q | q.2 = x}).toReal = 0
        · simp [hk]
        · have hb : M.b s.1 a = 0 := by
            apply (mul_eq_zero.mp (hterm a)).resolve_right hk
          have := hM.policy_overlap.2 s.1 a
          rw [hb, mul_zero] at this
          have he0 : M.e s.1 a = 0 :=
            le_antisymm this ((hM.policy_overlap.1 s.1).1 a)
          rw [he0, zero_mul]
      rw [show (∑ a : Bool, M.e s.1 a * (M.K s a {q | q.2 = x}).toReal) = 0 by
        exact Finset.sum_eq_zero fun a _ ↦ heterm a] at hpx
      exact (lt_irrefl 0 hpx)
  rw [← hM.behavior_stationary_law.2 x]
  have hnonneg (y : JointState nX nH) :
      0 ≤ stationaryLaw (policyKernel M M.b) y * policyKernel M M.b y x :=
    mul_nonneg (hM.behavior_stationary_law.1.1 y)
      ((policyKernel_probabilityVector M hM.pomdp_kernel M.b
        hM.sequential_ignorability.1 y).1 x)
  have hsingle : stationaryLaw (policyKernel M M.b) s * policyKernel M M.b s x ≤
      ∑ y, stationaryLaw (policyKernel M M.b) y * policyKernel M M.b y x :=
    Finset.single_le_sum (fun y _ ↦ hnonneg y) (Finset.mem_univ s)
  exact lt_of_lt_of_le (mul_pos hs hpb) hsingle

-- @node: markovOperatorIter_congr_on_behaviorSupport
/-- Iterated policy operators agree on behavior-supported states when their terminal
functions agree there. [the h M condition](hyp:hM); and [the hp condition](hyp:hp); and [the hfg condition](hyp:hfg); and [the hs condition](hyp:hs). [the stated conclusion](goal). -/
lemma markovOperatorIter_congr_on_behaviorSupport {T nX nH : Nat} {t0 zeta C : ℝ}
    {M : RawPomdpExperiment T nX nH} (hM : LatentOverlapClass t0 zeta C M)
    (p : Policy nX) (hp : p = M.b ∨ p = M.e) (f g : JointState nX nH → ℝ)
    (hfg : ∀ s, 0 < stationaryLaw (policyKernel M M.b) s → f s = g s)
    (k : Nat) (s : JointState nX nH)
    (hs : 0 < stationaryLaw (policyKernel M M.b) s) :
    markovOperatorIter (policyKernel M p) k f s =
      markovOperatorIter (policyKernel M p) k g s := by
  induction k generalizing s with
  | zero => exact hfg s hs
  | succ k ih =>
      simp only [markovOperatorIter_succ, markovOperator]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hrow : policyKernel M p s x = 0
      · simp [hrow]
      · rw [ih x (behaviorSupport_closed_policyKernel hM p hp hs
          (lt_of_le_of_ne ((policyKernel_probabilityVector M hM.pomdp_kernel p
            (hp.elim (fun h ↦ h ▸ hM.sequential_ignorability.1)
              (fun h ↦ h ▸ hM.policy_overlap.1)) s).1 x) (Ne.symm hrow)))]

-- @node: integral_curState_eq_behaviorStationary
/-- Every state coordinate of the behavior trajectory has its stationary initial law. [the h M condition](hyp:hM). [the stated conclusion](goal). -/
lemma integral_curState_eq_behaviorStationary {T nX nH : Nat} {t0 zeta C : ℝ}
    {M : RawPomdpExperiment T nX nH} (hM : LatentOverlapClass t0 zeta C M)
    (t : Fin T) (F : JointState nX nH → ℝ) :
    ∫ tau, F (curState t tau) ∂M.law =
      ∑ s, stationaryLaw (policyKernel M M.b) s * F s := by
  induction hn : t.val using Nat.strong_induction_on generalizing t F with
  | h n ih =>
    by_cases hn0 : n = 0
    · have ht0 : t = ⟨0, by omega⟩ := Fin.ext (hn.trans hn0)
      rw [ht0]
      have hm : Measurable (stateAt (T := T) (nX := nX) (nH := nH) 0) := by
        unfold stateAt
        fun_prop
      have hi : Integrable F
          (M.law.map (stateAt (T := T) (nX := nX) (nH := nH) 0)) := Integrable.of_finite
      change ∫ tau, F (stateAt 0 tau) ∂M.law = _
      rw [← integral_map hm.aemeasurable hi.aestronglyMeasurable,
        MeasureTheory.integral_fintype hi]
      apply Finset.sum_congr rfl
      intro s _
      change (M.law.map (stateAt (T := T) (nX := nX) (nH := nH) 0) {s}).toReal * F s = _
      rw [hM.stationary_start.2 s,
        ENNReal.toReal_ofReal (hM.behavior_stationary_law.1.1 s)]
    · let p : Fin T := ⟨n - 1, by omega⟩
      have hp : p.val + 1 < T := by dsimp [p]; omega
      have ht : nextEpoch p hp = t := by
        apply Fin.ext
        dsimp [nextEpoch, p]
        omega
      have hFB (s : JointState nX nH) : |F s| ≤ ∑ x, |F x| :=
        Finset.single_le_sum (fun x _ ↦ abs_nonneg (F x)) (Finset.mem_univ s)
      have hob := integrable_behaviorPeel_obligations hM.sequential_ignorability
        hM.pomdp_kernel p (fun _ ↦ (1 : ℝ)) measurable_const (integrable_const 1) F hFB
      have hstep := integral_history_mul_behavior_nextState hM.sequential_ignorability
        hM.pomdp_kernel p (fun _ ↦ (1 : ℝ)) F hob.1 hob.2
      simp only [one_mul] at hstep
      have hleft : (∫ z, F z.2.2 ∂(M.law.map (histNextPair p))) =
          ∫ tau, F (curState (nextEpoch p hp) tau) ∂M.law := by
        have hmF : AEStronglyMeasurable
            (fun z : ActionHistoryView T nX nH p × Step nX nH ↦ F z.2.2)
            (M.law.map (histNextPair p)) :=
          ((measurable_of_finite F).comp
            (measurable_snd.comp measurable_snd)).aestronglyMeasurable
        exact integral_map
          (f := fun z : ActionHistoryView T nX nH p × Step nX nH ↦ F z.2.2)
          (measurable_histNextPair p).aemeasurable hmF
      have hright : (∫ h, markovOperator (policyKernel M M.b) F h.2
          ∂(M.law.map (histStateView p))) =
          ∫ tau, markovOperator (policyKernel M M.b) F (curState p tau) ∂M.law := by
        exact integral_map
          (f := fun h : StateHistoryView T nX nH p ↦
            markovOperator (policyKernel M M.b) F h.2)
          (measurable_histStateView p).aemeasurable
          (((measurable_of_finite (markovOperator (policyKernel M M.b) F)).comp
            measurable_snd).aestronglyMeasurable)
      rw [hleft, hright] at hstep
      rw [← ht, hstep, ih (n - 1) (by omega) p
        (markovOperator (policyKernel M M.b) F) rfl]
      unfold markovOperator
      calc
        ∑ s, stationaryLaw (policyKernel M M.b) s * ∑ x, policyKernel M M.b s x * F x =
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
          rw [hM.behavior_stationary_law.2 x]

end CausalSmith.Stat.PomdpLatentOverlapMinimax
