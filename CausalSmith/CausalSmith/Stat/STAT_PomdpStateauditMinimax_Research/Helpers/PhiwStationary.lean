module
public import CausalSmith.Stat.STAT_PomdpStateauditMinimax_Research.Helpers.FullHistory

/-! # Stationary marginal identities for arbitrary finite action alphabets. -/

@[expose] public section

namespace CausalSmith.Stat.PomdpStateauditMinimax

open MeasureTheory ProbabilityTheory

/-- The behavior-policy transition operator on functions of the joint state. -/
noncomputable def behaviorStep {T nX nH k : Nat} (M : PomdpModel T nX nH k)
    (F : JointState nX nH → ℝ) : JointState nX nH → ℝ :=
  fun s => ∑ s', policyKernel M M.b s s' * F s'

/-- Averaging successor-state expectations first over behavior actions gives
the behavior transition operator. -/
lemma behaviorStep_eq_action_integral {T nX nH k : Nat}
    (M : PomdpModel T nX nH k) (hK : FullFiltrationPomdp M)
    (s : JointState nX nH) (F : JointState nX nH → ℝ) :
    ∑ a : Fin k, M.b s.1 a * ∫ y, F y.2 ∂(M.K s a) = behaviorStep M F s := by
  simp_rw [integral_nextState_eq_sum M hK]
  unfold behaviorStep policyKernel
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s' _
  conv_rhs => rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- One behavior transition advances expectations of joint-state functions by
the behavior transition operator. -/
lemma integral_nextState_eq_behaviorStep {T nX nH k : Nat}
    (M : PomdpModel T nX nH k) (hK : FullFiltrationPomdp M)
    (hA : FullFiltrationRandomization M) (t : Fin T)
    (F : JointState nX nH → ℝ) :
    ∫ w, F (nextState w t) ∂M.law =
      ∫ w, behaviorStep M F (currentState w t) ∂M.law := by
  letI : IsMarkovKernel (kernelOfK M) := ⟨fun sa => hK.1 sa.1 sa.2⟩
  letI : IsMarkovKernel (actionKernel M) := by
    refine ⟨fun x => ⟨?_⟩⟩
    change (∑ a : Fin k, ENNReal.ofReal (M.b x a) • Measure.dirac a) Set.univ = 1
    simp only [Measure.finsetSum_apply, Measure.smul_apply,
      Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (by intro a _; exact (hA.1 x).1 a)]
    simp [(hA.1 x).2]
  obtain ⟨C, hC⟩ := Finite.exists_le (fun s : JointState nX nH => |F s|)
  have henc : Measurable (fun w : FullPath T nX nH k =>
      (postHist t w, (rewardAt w t, nextState w t))) := by
    unfold postHist preHist currentState pastIndex actionAt rewardAt nextState
    fun_prop
  have hfull : Integrable
      (fun z : PostHistory T nX nH k t × (ℝ × JointState nX nH) => F z.2.2)
      (M.law.map (fun w => (postHist t w, (rewardAt w t, nextState w t)))) := by
    refine Integrable.of_bound ((measurable_of_finite F).comp
      (measurable_snd.comp measurable_snd)).aestronglyMeasurable C ?_
    filter_upwards with z
    simpa [Real.norm_eq_abs] using hC z.2.2
  have hpost : Measurable (postHist t : FullPath T nX nH k → _) := by
    unfold postHist preHist currentState pastIndex actionAt
    fun_prop
  have hinner : Integrable
      (fun h : PostHistory T nX nH k t => ∫ y, F y.2 ∂(M.K h.1.2.2 h.2))
      (M.law.map (postHist t)) := by
    apply Integrable.of_bound
    · exact (measurable_of_countable fun sa : JointState nX nH × Fin k =>
          ∫ y, F y.2 ∂(M.K sa.1 sa.2)).comp
          ((measurable_snd.comp (measurable_snd.comp measurable_fst)).prodMk
            measurable_snd) |>.aestronglyMeasurable
    · filter_upwards with h
      have hprob : IsProbabilityMeasure (M.K h.1.2.2 h.2) := hK.1 _ _
      letI : IsProbabilityMeasure (M.K h.1.2.2 h.2) := hprob
      simpa [Real.norm_eq_abs] using
        (norm_integral_le_of_norm_le_const (μ := M.K h.1.2.2 h.2) (f := fun y => F y.2)
          (by filter_upwards with y; simpa [Real.norm_eq_abs] using hC y.2))
  calc
    ∫ w, F (nextState w t) ∂M.law =
        ∫ z, F z.2.2
          ∂(M.law.map (fun w => (postHist t w, (rewardAt w t, nextState w t)))) := by
      rw [integral_map henc.aemeasurable hfull.aestronglyMeasurable]
    _ = ∫ h, ∫ y, F y.2 ∂(M.K h.1.2.2 h.2) ∂(M.law.map (postHist t)) :=
      full_history_integral_kernel_step M hK t _ hfull
    _ = ∫ h, ∑ a : Fin k, M.b h.2.2.1 a * ∫ y, F y.2 ∂(M.K h.2.2 a)
          ∂(M.law.map (preHist t)) := by
      change (∫ h, ∫ y, F y.2 ∂(M.K h.1.2.2 h.2)
        ∂(M.law.map (fun w => (preHist t w, actionAt w t)))) = _
      change Integrable
        (fun h : PreHistory T nX nH k t × Fin k =>
          ∫ y, F y.2 ∂(M.K h.1.2.2 h.2))
        (M.law.map (fun w => (preHist t w, actionAt w t))) at hinner
      rw [hA.2 t] at hinner ⊢
      rw [Measure.integral_compProd hinner]
      apply integral_congr_ae
      filter_upwards with h
      change (∫ a, ∫ y, F y.2 ∂(M.K h.2.2 a) ∂
        ∑ a : Fin k, ENNReal.ofReal (M.b h.2.2.1 a) • Measure.dirac a) = _
      rw [integral_finsetSum_measure (fun a _ =>
        (integrable_dirac (f := fun a : Fin k => ∫ y, F y.2 ∂(M.K h.2.2 a))
          enorm_lt_top).smul_measure ENNReal.ofReal_ne_top)]
      simp_rw [integral_smul_measure, integral_dirac,
        ENNReal.toReal_ofReal ((hA.1 _).1 _), smul_eq_mul]
    _ = ∫ h, behaviorStep M F h.2.2 ∂(M.law.map (preHist t)) := by
      apply integral_congr_ae
      filter_upwards with h
      exact behaviorStep_eq_action_integral M hK h.2.2 F
    _ = _ := by
      rw [integral_map]
      · rfl
      · unfold preHist currentState pastIndex
        fun_prop
      · exact ((measurable_of_finite (behaviorStep M F)).comp (by fun_prop)).aestronglyMeasurable

/-- Every current-state coordinate has the stationary behavior marginal. -/
lemma integral_currentState_eq_stationary {T nX nH k : Nat}
    (M : PomdpModel T nX nH k) (hK : FullFiltrationPomdp M)
    (hA : FullFiltrationRandomization M) (hStart : StationaryStart M)
    (t : Fin T) (F : JointState nX nH → ℝ) :
    ∫ w, F (currentState w t) ∂M.law =
      ∑ s, stationaryLaw (policyKernel M M.b) s * F s := by
  induction hn : t.val using Nat.strong_induction_on generalizing t F with
  | h n ih =>
      by_cases hn0 : n = 0
      · have ht0 : t = ⟨0, by omega⟩ := Fin.ext (hn.trans hn0)
        rw [ht0]
        have hm : Measurable (fun w : FullPath T nX nH k => stateAt w 0) := by
          unfold stateAt
          fun_prop
        have hi : Integrable F (M.law.map (fun w => stateAt w 0)) := Integrable.of_finite
        change ∫ w, F (stateAt w 0) ∂M.law = _
        rw [← integral_map hm.aemeasurable hi.aestronglyMeasurable,
          MeasureTheory.integral_fintype hi]
        apply Finset.sum_congr rfl
        intro s _
        change (M.law.map (fun w => stateAt w 0) {s}).toReal * F s = _
        rw [hStart.2 s, ENNReal.toReal_ofReal (hStart.1.1.1 s)]
      · let p : Fin T := ⟨n - 1, by omega⟩
        have hp : p.val + 1 < T := by dsimp [p]; omega
        have hstep := integral_nextState_eq_behaviorStep M hK hA p F
        have hnext : (fun w : FullPath T nX nH k => currentState w t) =
            fun w : FullPath T nX nH k => nextState w p := by
          funext w
          unfold currentState nextState
          apply congrArg w.1
          apply Fin.ext
          dsimp [p]
          omega
        have hnextF : (fun w : FullPath T nX nH k => F (currentState w t)) =
            fun w : FullPath T nX nH k => F (nextState w p) := by
          funext w
          rw [congrFun hnext w]
        rw [hnextF, hstep, ih (n - 1) (by omega) p (behaviorStep M F) rfl]
        unfold behaviorStep
        calc
          ∑ s, stationaryLaw (policyKernel M M.b) s *
              ∑ x, policyKernel M M.b s x * F x =
              ∑ x, (∑ s, stationaryLaw (policyKernel M M.b) s *
                policyKernel M M.b s x) * F x := by
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro x _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro s _
            ring
          _ = _ := by
            apply Finset.sum_congr rfl
            intro x _
            rw [hStart.1.2 x]

end CausalSmith.Stat.PomdpStateauditMinimax
