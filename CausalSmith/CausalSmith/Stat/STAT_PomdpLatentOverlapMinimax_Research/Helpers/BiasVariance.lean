import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.PhiwVariance
import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.StationaryRewardSupport
import Mathlib.Probability.Moments.Variance

set_option linter.style.longLine false

/-! # Bias and variance bound for partial-history weighting -/

namespace CausalSmith.Stat.PomdpLatentOverlapMinimax

open Causalean.Mathlib.Probability.FiniteMarkovOscillation
open MeasureTheory ProbabilityTheory
open Filter
open scoped BigOperators ENNReal NNReal
open scoped Topology

/-- The latent-overlap residual law bounds stationary total variation by `q_C`. [the h M condition](hyp:hM); and [the h C condition](hyp:hC). [the stated conclusion](goal). -/
lemma stationary_tv_le_overlapRadius {T nX nH : Nat} {t0 zeta C : ℝ}
    {M : RawPomdpExperiment T nX nH} (hM : LatentOverlapClass t0 zeta C M)
    (hC : 1 ≤ C) :
    tvNorm (stationaryLaw (policyKernel M M.b) -
      stationaryLaw (policyKernel M M.e)) ≤ overlapRadius C := by
  let dB := stationaryLaw (policyKernel M M.b)
  let dE := stationaryLaw (policyKernel M M.e)
  have hdB : ProbabilityVector dB := hM.behavior_stationary_law.1
  have hdE : ProbabilityVector dE := hM.target_stationary_law.1
  have hdom : ∀ s, dE s ≤ C * dB s := hM.latent_stationary_overlap.2
  by_cases hC1 : C = 1
  · subst C
    have heq : dE = dB := by
      funext s
      apply le_antisymm
      · simpa using hdom s
      · by_contra hnot
        have hlt : dE s < dB s := lt_of_not_ge hnot
        have hsum_lt : ∑ i, dE i < ∑ i, dB i := by
          exact Finset.sum_lt_sum (fun i _ ↦ by simpa using hdom i)
            ⟨s, Finset.mem_univ s, hlt⟩
        linarith [hdB.2, hdE.2]
    simp [dB, dE, heq, tvNorm, overlapRadius]
  · have hCgt : 1 < C := lt_of_le_of_ne hC (Ne.symm hC1)
    let nu : JointState nX nH → ℝ := fun s ↦ (C * dB s - dE s) / (C - 1)
    have hnu : ProbabilityVector nu := by
      constructor
      · intro s
        exact div_nonneg (sub_nonneg.mpr (hdom s)) (sub_nonneg.mpr hC)
      · dsimp [nu]
        rw [← Finset.sum_div]
        simp_rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hdB.2, hdE.2]
        field_simp
    have hq0 : 0 ≤ overlapRadius C := by
      unfold overlapRadius
      positivity
    have hdiff : dB - dE = fun s ↦ overlapRadius C * (nu s - dE s) := by
      funext s
      dsimp [nu, overlapRadius]
      field_simp
      ring
    rw [hdiff]
    unfold tvNorm
    rw [show (∑ i, |overlapRadius C * (nu i - dE i)|) =
        overlapRadius C * ∑ i, |nu i - dE i| by
      simp_rw [abs_mul, abs_of_nonneg hq0, Finset.mul_sum]]
    have hvariation : ∑ i, |nu i - dE i| ≤ 2 := by
      calc
        ∑ i, |nu i - dE i| ≤ ∑ i, (nu i + dE i) := by
          apply Finset.sum_le_sum
          intro i _
          exact (abs_sub (nu i) (dE i)).trans_eq
            (by rw [abs_of_nonneg (hnu.1 i), abs_of_nonneg (hdE.1 i)])
        _ = 2 := by rw [Finset.sum_add_distrib, hnu.2, hdE.2]; norm_num
    calc
      (1 / 2 : ℝ) * (overlapRadius C * ∑ i, |nu i - dE i|) ≤
          (1 / 2 : ℝ) * (overlapRadius C * 2) := by gcongr
      _ = overlapRadius C := by ring

-- @node: sqRisk_clipUnit_le_variance_add_bias_sq
/-- Clipping reduces squared risk, after which the usual bias--variance identity applies. [the h Xmeas condition](hyp:hXmeas); and [the h X condition](hyp:hX); and [the htheta condition](hyp:htheta). [the stated conclusion](goal). -/
lemma sqRisk_clipUnit_le_variance_add_bias_sq {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] {X : Omega → ℝ} {theta : ℝ}
    (hXmeas : Measurable X) (hX : MemLp X 2 mu)
    (htheta : theta ∈ Set.Icc (-1 : ℝ) 1) :
    Causalean.Stat.sqRisk mu (fun omega ↦ clipUnit (X omega)) theta ≤
      variance X mu + (∫ omega, X omega ∂mu - theta) ^ 2 := by
  have hdiff : MemLp (fun omega ↦ X omega - theta) 2 mu := by
    change MemLp (X - fun _ ↦ theta) 2 mu
    exact hX.sub (memLp_const theta)
  have hdiffInt : Integrable (fun omega ↦ (X omega - theta) ^ 2) mu := by
    simpa only [Pi.pow_apply] using hdiff.integrable_sq
  have hclipInt : Integrable (fun omega ↦ (clipUnit (X omega) - theta) ^ 2) mu := by
    apply hdiffInt.mono'
    · unfold clipUnit
      fun_prop
    · filter_upwards with omega
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact clipUnit_sq_sub_le htheta
  have hriskRaw :
      (∫ omega, (X omega - theta) ^ 2 ∂mu) =
        variance X mu + (∫ omega, X omega ∂mu - theta) ^ 2 := by
    rw [variance_eq_sub hX]
    have hXint : Integrable X mu := hX.integrable one_le_two
    have hXsq : Integrable (fun omega ↦ X omega ^ 2) mu := hX.integrable_sq
    calc
      (∫ omega, (X omega - theta) ^ 2 ∂mu) =
          ∫ omega, (X omega ^ 2 - 2 * theta * X omega + theta ^ 2) ∂mu := by
            apply integral_congr_ae
            filter_upwards with omega
            ring
      _ = (∫ omega, X omega ^ 2 ∂mu) -
            2 * theta * (∫ omega, X omega ∂mu) + theta ^ 2 := by
          (integral_linearity; simp)
      _ = ((∫ omega, (X ^ 2) omega ∂mu) - (∫ omega, X omega ∂mu) ^ 2) +
            (∫ omega, X omega ∂mu - theta) ^ 2 := by
          simp only [Pi.pow_apply]
          ring
  unfold Causalean.Stat.sqRisk
  calc
    (∫ omega, (clipUnit (X omega) - theta) ^ 2 ∂mu) ≤
        ∫ omega, (X omega - theta) ^ 2 ∂mu := by
      exact integral_mono hclipInt hdiffInt (fun omega ↦ clipUnit_sq_sub_le htheta)
    _ = variance X mu + (∫ omega, X omega ∂mu - theta) ^ 2 := hriskRaw

/-- Every state coordinate has the stationary behavior initial law. [the h M condition](hyp:hM). [the stated conclusion](goal). -/
lemma integral_curState_eq_init {T nX nH : Nat} {t0 zeta C : ℝ}
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
        exact integral_map (f := fun z : ActionHistoryView T nX nH p × Step nX nH ↦ F z.2.2)
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
          rw [hM.behavior_stationary_law.2 x]

/-- A stationary vector integrates every iterate of its Markov operator as it integrates the
original function. [the hd condition](hyp:hd). [the stated conclusion](goal). -/
lemma sum_stationary_mul_markovOperatorIter {S : Type*} [Fintype S]
    (P : S → S → ℝ) (d : S → ℝ) (hd : IsStationary P d)
    (F : S → ℝ) (m : Nat) :
    ∑ s, d s * markovOperatorIter P m F s = ∑ s, d s * F s := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [markovOperatorIter_succ]
      unfold markovOperator
      calc
        ∑ s, d s * ∑ x, P s x * markovOperatorIter P m F x =
            ∑ s, ∑ x, d s * (P s x * markovOperatorIter P m F x) := by
          apply Finset.sum_congr rfl
          intro s _
          rw [Finset.mul_sum]
        _ = ∑ x, ∑ s, d s * (P s x * markovOperatorIter P m F x) := Finset.sum_comm
        _ = ∑ x, (∑ s, d s * P s x) * markovOperatorIter P m F x := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro s _
          ring
        _ = ∑ x, d x * markovOperatorIter P m F x := by
          apply Finset.sum_congr rfl
          intro x _
          rw [hd.2 x]
        _ = _ := ih

/-- Every mature PHIW score has the same target-window expectation from the stationary
behavior law. [the h M condition](hyp:hM); and [the htk condition](hyp:htk). [the stated conclusion](goal). -/
lemma integral_phiwScore_eq_init_targetIter {T nX nH k : Nat} {t0 zeta C : ℝ}
    {M : RawPomdpExperiment T nX nH} (hM : LatentOverlapClass t0 zeta C M)
    (t : Fin T) (htk : k ≤ t.val) :
    ∫ w, phiwScore k M.b M.e w t ∂obsLaw M =
      ∑ s, stationaryLaw (policyKernel M M.b) s *
        markovOperatorIter (policyKernel M M.e) k (rewardRegression M) s := by
  have hL : 1 ≤ policyFactor zeta := by
    rw [policyFactor, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr hM.zeta_pos.le
  let r : Fin T := ⟨t.val - k, by omega⟩
  have hhor : r.val + 0 + k < T := by dsimp [r]; omega
  let q := epochAdd r 0 (by omega)
  let u := epochAdd q k (by dsimp [q, epochAdd]; omega)
  have hu : u = t := by
    apply Fin.ext
    dsimp [u, q, r, epochAdd]
    omega
  have hp := integral_phiwScore_eq_futureFunction_from_state hM.sequential_ignorability
    hM.policy_overlap hL hM.pomdp_kernel hM.bounded_reward r hhor
  change (∫ w, phiwScore k M.b M.e w u ∂obsLaw M) =
      ∫ tau, phiwFutureFunction M 0 k (curState r tau) ∂M.law at hp
  rw [hu] at hp
  rw [hp, integral_curState_eq_init hM]
  rfl

/-- Iterated contraction gives the geometric bias term. [the h M condition](hyp:hM); and [the h C condition](hyp:hC); and [the h T condition](hyp:hT); and [the hk condition](hyp:hk). [the stated conclusion](goal). -/
lemma phiw_bias_le {T nX nH k : Nat} {t0 zeta C : ℝ}
    {M : RawPomdpExperiment T nX nH} (hM : LatentOverlapClass t0 zeta C M)
    (hC : 1 ≤ C) (hT : 1 ≤ T) (hk : k ≤ T / 2) :
    |∫ w, phiwRaw k M.b M.e w ∂(obsLaw M) - targetValue M| ≤
      2 * overlapRadius C * mixingAlpha t0 ^ k := by
  letI : Nonempty (JointState nX nH) :=
    nonemptyOfProbabilityVector (stationaryLaw (policyKernel M M.b))
      hM.behavior_stationary_law.1
  letI : IsProbabilityMeasure (obsLaw M) := by
    unfold obsLaw
    exact Measure.isProbabilityMeasure_map measurable_obsProj.aemeasurable
  have hL : 1 ≤ policyFactor zeta := by
    rw [policyFactor, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr hM.zeta_pos.le
  let F := markovOperatorIter (policyKernel M M.e) k (rewardRegression M)
  have hscoreBias :
      |∑ s, stationaryLaw (policyKernel M M.b) s * F s - targetValue M| ≤
        2 * overlapRadius C * mixingAlpha t0 ^ k := by
    let dB := stationaryLaw (policyKernel M M.b)
    let dE := stationaryLaw (policyKernel M M.e)
    let g : JointState nX nH → ℝ := fun s ↦
      if 0 < dB s then rewardRegression M s else 0
    let Fc := markovOperatorIter (policyKernel M M.e) k g
    have hg (s : JointState nX nH) : |g s| ≤ 1 := by
      dsimp [g]
      split_ifs with hs
      · exact rewardRegression_abs_le_one_of_behaviorSupport hT hM s hs
      · simp
    have hgosc : OscillationBound 2 g := by
      intro x y
      calc
        |g x - g y| ≤ |g x| + |g y| := abs_sub _ _
        _ ≤ 2 := by linarith [hg x, hg y]
    have hFcosc : OscillationBound (2 * mixingAlpha t0 ^ k) Fc := by
      have hh := oscillationBound_markovOperatorIter
        (policyKernel M M.e)
        (policyKernel_probabilityVector M hM.pomdp_kernel M.e hM.policy_overlap.1)
        (Real.exp_nonneg _) (hM.uniform_contraction M.e (Or.inr rfl)) hgosc k
      simpa only [Fc, mixingAlpha, mul_comm] using hh
    have hFc (s : JointState nX nH) (hs : 0 < dB s) : F s = Fc s := by
      exact markovOperatorIter_congr_on_behaviorSupport hM M.e (Or.inr rfl)
        (rewardRegression M) g (fun x hx ↦ by simp [g, dB, hx]) k s hs
    have hleft : ∑ s, dB s * F s = ∑ s, dB s * Fc s := by
      apply Finset.sum_congr rfl
      intro s _
      by_cases hs : dB s = 0
      · simp [hs]
      · rw [hFc s (lt_of_le_of_ne (hM.behavior_stationary_law.1.1 s) (Ne.symm hs))]
    have hright : targetValue M = ∑ s, dE s * Fc s := by
      have htargetg : targetValue M = ∑ s, dE s * g s := by
        unfold targetValue
        apply Finset.sum_congr rfl
        intro s _
        by_cases hs : dE s = 0
        · simp [dE, hs]
        · have hspos : 0 < dE s :=
            lt_of_le_of_ne (hM.target_stationary_law.1.1 s) (Ne.symm hs)
          have hbpos : 0 < dB s := by
            have hdom := hM.latent_stationary_overlap.2 s
            change dE s ≤ C * dB s at hdom
            by_contra hn
            have hb0 : dB s = 0 :=
              le_antisymm (le_of_not_gt hn) (hM.behavior_stationary_law.1.1 s)
            rw [hb0, mul_zero] at hdom
            exact (not_lt_of_ge hdom) hspos
          change dE s * rewardRegression M s = dE s * g s
          simp [g, hbpos]
      rw [htargetg]
      symm
      exact sum_stationary_mul_markovOperatorIter (policyKernel M M.e) dE
        hM.target_stationary_law g k
    rw [hleft, hright]
    have hrewrite :
        (∑ s, dB s * Fc s) - ∑ s, dE s * Fc s =
          ∑ s, (dB s - dE s) * Fc s := by
      calc
        _ = ∑ s, (dB s * Fc s - dE s * Fc s) := by
          symm
          rw [Finset.sum_sub_distrib]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro s _
          ring
    rw [hrewrite]
    refine (abs_sum_sub_mul_le_oscillation_halfL1 hM.behavior_stationary_law.1
      hM.target_stationary_law.1 hFcosc).trans ?_
    have htv := stationary_tv_le_overlapRadius hM hC
    have hpow : 0 ≤ mixingAlpha t0 ^ k := pow_nonneg (Real.exp_nonneg _) _
    calc
      (2 * mixingAlpha t0 ^ k) * tvNorm (dB - dE) ≤
          (2 * mixingAlpha t0 ^ k) * overlapRadius C :=
        mul_le_mul_of_nonneg_left (by simpa [dB, dE] using htv)
          (mul_nonneg (by norm_num) hpow)
      _ = 2 * overlapRadius C * mixingAlpha t0 ^ k := by ring
  have hklt : k < T := by omega
  let I : Finset (Fin T) := Finset.univ.filter (fun t ↦ k ≤ t.val)
  have hI : I = Finset.Ici (⟨k, hklt⟩ : Fin T) := by
    ext t
    simp only [I, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ici]
    change k ≤ t.val ↔ k ≤ t.val
    rfl
  have hIcard : I.card = T - k := by
    rw [hI, Fin.card_Ici]
  have hNpos : 0 < T - k := by omega
  have hrawMean : ∫ w, phiwRaw k M.b M.e w ∂obsLaw M =
      ∑ s, stationaryLaw (policyKernel M M.b) s * F s := by
    unfold phiwRaw
    rw [integral_const_mul]
    rw [integral_finset_sum]
    · rw [show (∑ t ∈ I, ∫ w, phiwScore k M.b M.e w t ∂obsLaw M) =
          ∑ _t ∈ I, ∑ s, stationaryLaw (policyKernel M M.b) s * F s by
        apply Finset.sum_congr rfl
        intro t ht
        exact integral_phiwScore_eq_init_targetIter hM t (Finset.mem_filter.mp ht).2]
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [hIcard]
      have hcast : ((T - k : Nat) : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hNpos)
      rw [← mul_assoc, inv_mul_cancel₀ hcast, one_mul]
    · intro t ht
      exact (phiwScore_memLp hM.sequential_ignorability hM.policy_overlap hL
        hM.bounded_reward 2 t).integrable one_le_two
  rw [hrawMean]
  exact hscoreBias

-- @node: lem:radius-sensitive-phiw
/-- The radius-sensitive squared-risk bound, uniform in both alphabet cardinalities. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC); and [the h T condition](hyp:hT); and [the h M condition](hyp:hM); and [the hk condition](hyp:hk). [the stated conclusion](goal). -/
lemma radius_sensitive_phiw {T nX nH k : Nat} {t0 zeta C : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C) (hT : 1 ≤ T)
    (M : RawPomdpExperiment T nX nH) (hM : LatentOverlapClass t0 zeta C M)
    (hk : k ≤ T / 2) :
    Causalean.Stat.sqRisk (obsLaw M) (phiwEstimator k (by omega) M.b M.e) (targetValue M) ≤
      4 * overlapRadius C ^ 2 * mixingAlpha t0 ^ (2 * k) +
      (2 / (T : ℝ)) *
        (policyFactor zeta ^ (k + 1) * (1 + 4 / (policyFactor zeta - 1)) +
          4 / (1 - mixingAlpha t0)) := by
  letI : IsProbabilityMeasure (obsLaw M) := by
    unfold obsLaw
    exact Measure.isProbabilityMeasure_map measurable_obsProj.aemeasurable
  have hL : 1 ≤ policyFactor zeta := by
    rw [policyFactor, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr hzeta.le
  have hrawMeas : Measurable (phiwRaw (T := T) k M.b M.e) := by
    unfold phiwRaw
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro t ht
    exact phiwScore_measurable M.b M.e t
  have hrawLp : MemLp (phiwRaw k M.b M.e) 2 (obsLaw M) := by
    unfold phiwRaw
    exact (memLp_finsetSum _ fun t _ ↦
      phiwScore_memLp hM.sequential_ignorability hM.policy_overlap hL
        hM.bounded_reward 2 t).const_mul _
  have hrisk := sqRisk_clipUnit_le_variance_add_bias_sq (obsLaw M) hrawMeas hrawLp
    (targetValue_mem_unit
      { horizon_pos := hT, nX := nX, nH := nH, raw := M, mem := hM })
  have hvar := variance_phiwRaw_le hT M hM hk
  have hbias := phiw_bias_le hM hC hT hk
  have hq0 : 0 ≤ overlapRadius C := by unfold overlapRadius; positivity
  have ha0 : 0 ≤ mixingAlpha t0 := by unfold mixingAlpha; positivity
  have hbound0 : 0 ≤ 2 * overlapRadius C * mixingAlpha t0 ^ k := by positivity
  have hbiasSq :
      (∫ w, phiwRaw k M.b M.e w ∂obsLaw M - targetValue M) ^ 2 ≤
        4 * overlapRadius C ^ 2 * mixingAlpha t0 ^ (2 * k) := by
    have hsquare := (sq_le_sq₀ (abs_nonneg
      (∫ w, phiwRaw k M.b M.e w ∂obsLaw M - targetValue M)) hbound0).2 hbias
    rw [sq_abs] at hsquare
    calc
      _ ≤ (2 * overlapRadius C * mixingAlpha t0 ^ k) ^ 2 := hsquare
      _ = _ := by
        rw [show mixingAlpha t0 ^ (2 * k) = (mixingAlpha t0 ^ k) ^ 2 by
          rw [← pow_mul]
          congr 1
          omega]
        ring
  exact hrisk.trans (add_le_add hvar hbiasSq) |>.trans_eq (by ring)

/-- The fixed-radius depth balances the geometric bias and weighted variance terms. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta). [the stated conclusion](goal). -/
-- @node: historyDepth_rate
lemma historyDepth_rate {t0 zeta : ℝ} (ht0 : 0 < t0) (hzeta : 0 < zeta) :
    ∃ c : ℝ, 0 < c ∧ ∃ TStar : Nat, ∀ T ≥ TStar,
      mixingAlpha t0 ^ (2 * historyDepth T t0 zeta) +
        (policyFactor zeta ^ (historyDepth T t0 zeta + 1)) / (T : ℝ) ≤
      c * (T : ℝ) ^ (-rateExponent t0 zeta) := by
  let D : ℝ := 2 * Real.log (1 / mixingAlpha t0) + Real.log (policyFactor zeta)
  have halpha0 : 0 < mixingAlpha t0 := by unfold mixingAlpha; positivity
  have hlogalpha : Real.log (mixingAlpha t0) = -(1 / t0) := by
    simp [mixingAlpha]
  have hlogL : Real.log (policyFactor zeta) = zeta := by simp [policyFactor]
  have hlogInvAlpha : Real.log (1 / mixingAlpha t0) = 1 / t0 := by
    rw [Real.log_div (by norm_num) (ne_of_gt halpha0), Real.log_one, hlogalpha]
    ring
  have hD : D = 2 / t0 + zeta := by
    dsimp [D]
    rw [hlogInvAlpha, hlogL]
    ring
  have hDpos : 0 < D := by rw [hD]; positivity
  have hbeta : rateExponent t0 zeta = (2 / t0) / D := by
    rw [rateExponent, hD]
    field_simp
  have heventReal : ∀ᶠ x : ℝ in atTop, |Real.log x| ≤ (D / 2) * |x| := by
    have h := Real.isLittleO_log_id_atTop.bound (show 0 < D / 2 by positivity)
    simpa [Real.norm_eq_abs] using h
  have heventNat : ∀ᶠ T : Nat in atTop,
      |Real.log (T : ℝ)| ≤ (D / 2) * |(T : ℝ)| :=
    tendsto_natCast_atTop_atTop.eventually heventReal
  rw [eventually_atTop] at heventNat
  obtain ⟨T0, hT0⟩ := heventNat
  let c : ℝ := Real.exp (2 / t0) + Real.exp zeta
  refine ⟨c, by dsimp [c]; positivity, max T0 1, ?_⟩
  intro T hT
  have hlogbound := hT0 T ((le_max_left T0 1).trans hT)
  have hT1 : 1 ≤ T := (le_max_right T0 1).trans hT
  have hTpos : 0 < (T : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hT1)
  have hlog0 : 0 ≤ Real.log (T : ℝ) := Real.log_nonneg (by exact_mod_cast hT1)
  have hx0 : 0 ≤ Real.log (T : ℝ) / D := div_nonneg hlog0 hDpos.le
  have hxle : Real.log (T : ℝ) / D ≤ (T : ℝ) / 2 := by
    rw [abs_of_nonneg hlog0, abs_of_nonneg hTpos.le] at hlogbound
    apply (div_le_iff₀ hDpos).2
    nlinarith
  let k : Nat := ⌊Real.log (T : ℝ) / D⌋₊
  have hkT : k ≤ T / 2 := by
    apply Nat.le_div_iff_mul_le (by norm_num : 0 < 2) |>.2
    rw [Nat.mul_comm]
    apply_mod_cast (show (2 : ℝ) * k ≤ T from ?_)
    have hkx : (k : ℝ) ≤ Real.log (T : ℝ) / D := Nat.floor_le hx0
    nlinarith
  have hdepth : historyDepth T t0 zeta = k := by
    unfold historyDepth
    rw [show 2 * Real.log (1 / mixingAlpha t0) + Real.log (policyFactor zeta) = D by rfl]
    rw [Int.floor_toNat]
    exact Nat.min_eq_right hkT
  have hk_lower : Real.log (T : ℝ) / D - 1 < (k : ℝ) := Nat.sub_one_lt_floor _
  have hk_upper : (k : ℝ) ≤ Real.log (T : ℝ) / D := Nat.floor_le hx0
  have hbarg : ((2 * k : Nat) : ℝ) * (-(1 / t0)) ≤
      2 / t0 + Real.log (T : ℝ) * (-rateExponent t0 zeta) := by
    have hm := mul_le_mul_of_nonpos_left (le_of_lt hk_lower)
      (neg_nonpos.mpr (by positivity : 0 ≤ 2 / t0))
    rw [hbeta]
    push_cast
    calc
      2 * (k : ℝ) * (-(1 / t0)) = (-(2 / t0)) * (k : ℝ) := by ring
      _ ≤ (-(2 / t0)) * (Real.log (T : ℝ) / D - 1) := hm
      _ = 2 / t0 + Real.log (T : ℝ) * (-(2 / t0 / D)) := by ring
  have hbias : mixingAlpha t0 ^ (2 * k) ≤
      Real.exp (2 / t0) * (T : ℝ) ^ (-rateExponent t0 zeta) := by
    rw [← Real.exp_log halpha0, ← Real.exp_nat_mul, hlogalpha,
      Real.rpow_def_of_pos hTpos, ← Real.exp_add]
    exact Real.exp_le_exp.mpr hbarg
  have hvarg : (((k + 1 : Nat) : ℝ) * zeta - Real.log (T : ℝ)) ≤
      zeta + Real.log (T : ℝ) * (-rateExponent t0 zeta) := by
    have hm := mul_le_mul_of_nonneg_right hk_upper hzeta.le
    rw [hbeta]
    push_cast
    calc
      ((k : ℝ) + 1) * zeta - Real.log (T : ℝ) ≤
          (Real.log (T : ℝ) / D + 1) * zeta - Real.log (T : ℝ) := by
        nlinarith
      _ = zeta + Real.log (T : ℝ) * (-(2 / t0 / D)) := by
        rw [hD]
        field_simp <;> ring
  have hvar : policyFactor zeta ^ (k + 1) / (T : ℝ) ≤
      Real.exp zeta * (T : ℝ) ^ (-rateExponent t0 zeta) := by
    rw [policyFactor, ← Real.exp_nat_mul, div_eq_mul_inv,
      show (T : ℝ)⁻¹ = Real.exp (-Real.log (T : ℝ)) by
        rw [Real.exp_neg, Real.exp_log hTpos],
      ← Real.exp_add, Real.rpow_def_of_pos hTpos, ← Real.exp_add]
    exact Real.exp_le_exp.mpr hvarg
  rw [hdepth]
  calc
    mixingAlpha t0 ^ (2 * k) + policyFactor zeta ^ (k + 1) / (T : ℝ) ≤
        Real.exp (2 / t0) * (T : ℝ) ^ (-rateExponent t0 zeta) +
          Real.exp zeta * (T : ℝ) ^ (-rateExponent t0 zeta) := add_le_add hbias hvar
    _ = c * (T : ℝ) ^ (-rateExponent t0 zeta) := by simp [c]; ring

/-- The adaptive depth realizes the common value on the nonparametric branch. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta). [the stated conclusion](goal). -/
-- @node: radiusAdaptiveDepth_rate
lemma radiusAdaptiveDepth_rate {t0 zeta : ℝ} (ht0 : 0 < t0) (hzeta : 0 < zeta) :
    ∃ c : ℝ, 0 < c ∧ ∃ TStar : Nat, 1 ≤ TStar ∧
      ∀ T ≥ TStar, ∀ C : ℝ, 1 ≤ C →
        overlapRadius C ^ 2 * mixingAlpha t0 ^ (2 * radiusAdaptiveDepth T t0 zeta C) +
          policyFactor zeta ^ (radiusAdaptiveDepth T t0 zeta C) / (T : ℝ) ≤
        c * ((T : ℝ)⁻¹ + (T : ℝ) ^ (-rateExponent t0 zeta) *
          overlapRadius C ^ (2 * (1 - rateExponent t0 zeta))) := by
  let D : ℝ := 2 * Real.log (1 / mixingAlpha t0) + Real.log (policyFactor zeta)
  have halpha0 : 0 < mixingAlpha t0 := by unfold mixingAlpha; positivity
  have hlogalpha : Real.log (mixingAlpha t0) = -(1 / t0) := by simp [mixingAlpha]
  have hlogL : Real.log (policyFactor zeta) = zeta := by simp [policyFactor]
  have hlogInvAlpha : Real.log (1 / mixingAlpha t0) = 1 / t0 := by
    rw [Real.log_div (by norm_num) (ne_of_gt halpha0), Real.log_one, hlogalpha]
    ring
  have hD : D = 2 / t0 + zeta := by
    dsimp [D]
    rw [hlogInvAlpha, hlogL]
    ring
  have hDpos : 0 < D := by rw [hD]; positivity
  have hbeta : rateExponent t0 zeta = (2 / t0) / D := by
    rw [rateExponent, hD]
    field_simp
  have heventReal : ∀ᶠ x : ℝ in atTop, |Real.log x| ≤ (D / 2) * |x| := by
    have h := Real.isLittleO_log_id_atTop.bound (show 0 < D / 2 by positivity)
    simpa [Real.norm_eq_abs] using h
  have heventNat : ∀ᶠ T : Nat in atTop,
      |Real.log (T : ℝ)| ≤ (D / 2) * |(T : ℝ)| :=
    tendsto_natCast_atTop_atTop.eventually heventReal
  rw [eventually_atTop] at heventNat
  obtain ⟨T0, hT0⟩ := heventNat
  let c : ℝ := max 2 (Real.exp (2 / t0) + 1)
  refine ⟨c, lt_of_lt_of_le (by norm_num) (le_max_left _ _), max T0 1,
    le_max_right _ _, ?_⟩
  intro T hT C hC
  have hT0' : T0 ≤ T := (le_max_left T0 1).trans hT
  have hT1 : 1 ≤ T := (le_max_right T0 1).trans hT
  have hTpos : 0 < (T : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hT1)
  let q := overlapRadius C
  let x : ℝ := T * q ^ 2
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hq0 : 0 ≤ q := by
    dsimp [q, overlapRadius]
    positivity
  have hq1 : q ≤ 1 := by
    dsimp [q, overlapRadius]
    exact (div_le_one hCpos).2 (by linarith)
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hxT : x ≤ T := by
    dsimp [x]
    nlinarith [sq_nonneg q, mul_nonneg hq0 (sub_nonneg.mpr hq1)]
  have hhidden : 0 ≤ (T : ℝ) ^ (-rateExponent t0 zeta) *
      q ^ (2 * (1 - rateExponent t0 zeta)) := by positivity
  by_cases hx : x ≤ 1
  · have hdepth : radiusAdaptiveDepth T t0 zeta C = 0 := by
      simp [radiusAdaptiveDepth, x, q, hx]
    have hqT : q ^ 2 ≤ (T : ℝ)⁻¹ := by
      rw [inv_eq_one_div]
      apply (le_div_iff₀ hTpos).2
      simpa [x, mul_comm] using hx
    have hc2 : 2 ≤ c := le_max_left _ _
    rw [hdepth, pow_zero, mul_one, pow_zero, one_div]
    calc
      q ^ 2 + (T : ℝ)⁻¹ ≤ 2 * (T : ℝ)⁻¹ := by linarith
      _ ≤ 2 * ((T : ℝ)⁻¹ +
          (T : ℝ) ^ (-rateExponent t0 zeta) *
            q ^ (2 * (1 - rateExponent t0 zeta))) := by
        gcongr
        exact le_add_of_nonneg_right hhidden
      _ ≤ c * ((T : ℝ)⁻¹ +
          (T : ℝ) ^ (-rateExponent t0 zeta) *
            q ^ (2 * (1 - rateExponent t0 zeta))) := by
        gcongr
  · have hx1 : 1 < x := lt_of_not_ge hx
    have hxpos : 0 < x := lt_trans zero_lt_one hx1
    have hqpos : 0 < q := by
      by_contra hnot
      have : q = 0 := le_antisymm (le_of_not_gt hnot) hq0
      have : (1 : ℝ) < 0 := by simpa [x, this] using hx1
      linarith
    have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg hx1.le
    have hlogT0 : 0 ≤ Real.log (T : ℝ) := Real.log_nonneg (by exact_mod_cast hT1)
    have hlogxT : Real.log x ≤ Real.log (T : ℝ) := Real.log_le_log hxpos hxT
    have hlogbound := hT0 T hT0'
    rw [abs_of_nonneg hlogT0, abs_of_nonneg hTpos.le] at hlogbound
    let k : Nat := ⌊Real.log x / D⌋₊
    have hkT : k ≤ T / 2 := by
      apply Nat.le_div_iff_mul_le (by norm_num : 0 < 2) |>.2
      rw [Nat.mul_comm]
      apply_mod_cast (show (2 : ℝ) * k ≤ T from ?_)
      have hkx : (k : ℝ) ≤ Real.log x / D := Nat.floor_le (div_nonneg hlogx0 hDpos.le)
      have hquot : Real.log x / D ≤ (T : ℝ) / 2 := by
        apply (div_le_iff₀ hDpos).2
        nlinarith
      nlinarith
    have hdepth : radiusAdaptiveDepth T t0 zeta C = k := by
      unfold radiusAdaptiveDepth
      rw [if_neg (not_le.mpr hx1)]
      simp only [q, x] at *
      rw [show 2 * Real.log (1 / mixingAlpha t0) + Real.log (policyFactor zeta) = D by rfl]
      rw [Int.floor_toNat]
      exact Nat.min_eq_right hkT
    have hk_lower : Real.log x / D - 1 < (k : ℝ) := Nat.sub_one_lt_floor _
    have hk_upper : (k : ℝ) ≤ Real.log x / D :=
      Nat.floor_le (div_nonneg hlogx0 hDpos.le)
    have hbarg : ((2 * k : Nat) : ℝ) * (-(1 / t0)) ≤
        2 / t0 + Real.log x * (-rateExponent t0 zeta) := by
      have hm := mul_le_mul_of_nonpos_left (le_of_lt hk_lower)
        (neg_nonpos.mpr (by positivity : 0 ≤ 2 / t0))
      rw [hbeta]
      push_cast
      calc
        2 * (k : ℝ) * (-(1 / t0)) = (-(2 / t0)) * (k : ℝ) := by ring
        _ ≤ (-(2 / t0)) * (Real.log x / D - 1) := hm
        _ = 2 / t0 + Real.log x * (-(2 / t0 / D)) := by ring
    have hbias : mixingAlpha t0 ^ (2 * k) ≤
        Real.exp (2 / t0) * x ^ (-rateExponent t0 zeta) := by
      rw [← Real.exp_log halpha0, ← Real.exp_nat_mul, hlogalpha,
        Real.rpow_def_of_pos hxpos, ← Real.exp_add]
      exact Real.exp_le_exp.mpr hbarg
    have hvarg : ((k : ℝ) * zeta - Real.log (T : ℝ)) ≤
        Real.log x * (1 - rateExponent t0 zeta) - Real.log (T : ℝ) := by
      have hm := mul_le_mul_of_nonneg_right hk_upper hzeta.le
      rw [hbeta]
      calc
        (k : ℝ) * zeta - Real.log (T : ℝ) ≤
            Real.log x / D * zeta - Real.log (T : ℝ) := by linarith
        _ = Real.log x * (1 - (2 / t0 / D)) - Real.log (T : ℝ) := by
          rw [hD]
          field_simp
          ring
    have hvar : policyFactor zeta ^ k / (T : ℝ) ≤
        x ^ (1 - rateExponent t0 zeta) / (T : ℝ) := by
      calc
        policyFactor zeta ^ k / (T : ℝ) =
            Real.exp ((k : ℝ) * zeta - Real.log (T : ℝ)) := by
          rw [policyFactor, ← Real.exp_nat_mul, Real.exp_sub, Real.exp_log hTpos]
        _ ≤ Real.exp (Real.log x * (1 - rateExponent t0 zeta) -
            Real.log (T : ℝ)) := Real.exp_le_exp.mpr hvarg
        _ = x ^ (1 - rateExponent t0 zeta) / (T : ℝ) := by
          rw [Real.rpow_def_of_pos hxpos, Real.exp_sub, Real.exp_log hTpos]
    have hcommonBias : q ^ 2 * x ^ (-rateExponent t0 zeta) =
        (T : ℝ) ^ (-rateExponent t0 zeta) *
          q ^ (2 * (1 - rateExponent t0 zeta)) := by
      rw [show x = (T : ℝ) * q ^ 2 by rfl,
        Real.mul_rpow hTpos.le (sq_nonneg q),
        ← Real.rpow_natCast_mul hq0 2 (-rateExponent t0 zeta)]
      calc
        q ^ 2 * ((T : ℝ) ^ (-rateExponent t0 zeta) *
            q ^ ((2 : ℕ) * (-rateExponent t0 zeta))) =
            (T : ℝ) ^ (-rateExponent t0 zeta) *
              (q ^ 2 * q ^ ((2 : ℝ) * (-rateExponent t0 zeta))) := by ring
        _ = (T : ℝ) ^ (-rateExponent t0 zeta) *
              (q ^ (2 : ℝ) * q ^ ((2 : ℝ) * (-rateExponent t0 zeta))) := by
          congr 2
          exact (Real.rpow_natCast q 2).symm
        _ = (T : ℝ) ^ (-rateExponent t0 zeta) *
            q ^ ((2 : ℝ) + 2 * (-rateExponent t0 zeta)) := by
          rw [Real.rpow_add hqpos]
        _ = (T : ℝ) ^ (-rateExponent t0 zeta) *
            q ^ (2 * (1 - rateExponent t0 zeta)) := by ring_nf
    have hcommonVar : x ^ (1 - rateExponent t0 zeta) / (T : ℝ) =
        (T : ℝ) ^ (-rateExponent t0 zeta) *
          q ^ (2 * (1 - rateExponent t0 zeta)) := by
      rw [show x = (T : ℝ) * q ^ 2 by rfl,
        Real.mul_rpow hTpos.le (sq_nonneg q),
        ← Real.rpow_natCast_mul hq0 2 (1 - rateExponent t0 zeta),
        div_eq_mul_inv, ← Real.rpow_neg_one]
      calc
        (T : ℝ) ^ (1 - rateExponent t0 zeta) *
              q ^ ((2 : ℕ) * (1 - rateExponent t0 zeta)) *
                (T : ℝ) ^ (-(1 : ℝ)) =
            ((T : ℝ) ^ (1 - rateExponent t0 zeta) *
                (T : ℝ) ^ (-(1 : ℝ))) *
              q ^ ((2 : ℝ) * (1 - rateExponent t0 zeta)) := by ring
        _ = (T : ℝ) ^ ((1 - rateExponent t0 zeta) + (-1)) *
              q ^ ((2 : ℝ) * (1 - rateExponent t0 zeta)) := by
          rw [Real.rpow_add hTpos]
        _ = (T : ℝ) ^ (-rateExponent t0 zeta) *
              q ^ (2 * (1 - rateExponent t0 zeta)) := by
          congr 2
          ring
    rw [hdepth]
    calc
      q ^ 2 * mixingAlpha t0 ^ (2 * k) + policyFactor zeta ^ k / (T : ℝ) ≤
          Real.exp (2 / t0) * (q ^ 2 * x ^ (-rateExponent t0 zeta)) +
            x ^ (1 - rateExponent t0 zeta) / (T : ℝ) := by
        have hbias' := mul_le_mul_of_nonneg_left hbias (sq_nonneg q)
        calc
          q ^ 2 * mixingAlpha t0 ^ (2 * k) + policyFactor zeta ^ k / (T : ℝ) ≤
              q ^ 2 * (Real.exp (2 / t0) * x ^ (-rateExponent t0 zeta)) +
                x ^ (1 - rateExponent t0 zeta) / (T : ℝ) := add_le_add hbias' hvar
          _ = Real.exp (2 / t0) * (q ^ 2 * x ^ (-rateExponent t0 zeta)) +
                x ^ (1 - rateExponent t0 zeta) / (T : ℝ) := by ring
      _ = Real.exp (2 / t0) *
              ((T : ℝ) ^ (-rateExponent t0 zeta) *
                q ^ (2 * (1 - rateExponent t0 zeta))) +
            ((T : ℝ) ^ (-rateExponent t0 zeta) *
              q ^ (2 * (1 - rateExponent t0 zeta))) := by
        rw [hcommonBias, hcommonVar]
      _ = (Real.exp (2 / t0) + 1) *
          ((T : ℝ) ^ (-rateExponent t0 zeta) *
            q ^ (2 * (1 - rateExponent t0 zeta))) := by ring
      _ ≤ c * ((T : ℝ)⁻¹ +
          (T : ℝ) ^ (-rateExponent t0 zeta) *
            q ^ (2 * (1 - rateExponent t0 zeta))) := by
        have hc : Real.exp (2 / t0) + 1 ≤ c := le_max_right _ _
        have hinv : 0 ≤ (T : ℝ)⁻¹ := inv_nonneg.mpr hTpos.le
        have hc0 : 0 ≤ c := le_trans (by positivity : 0 ≤ Real.exp (2 / t0) + 1) hc
        calc
          (Real.exp (2 / t0) + 1) *
              ((T : ℝ) ^ (-rateExponent t0 zeta) *
                q ^ (2 * (1 - rateExponent t0 zeta))) ≤
              c * ((T : ℝ) ^ (-rateExponent t0 zeta) *
                q ^ (2 * (1 - rateExponent t0 zeta))) :=
            mul_le_mul_of_nonneg_right hc hhidden
          _ ≤ c * ((T : ℝ)⁻¹ +
              (T : ℝ) ^ (-rateExponent t0 zeta) *
                q ^ (2 * (1 - rateExponent t0 zeta))) := by
            gcongr
            exact le_add_of_nonneg_left hinv

end CausalSmith.Stat.PomdpLatentOverlapMinimax
