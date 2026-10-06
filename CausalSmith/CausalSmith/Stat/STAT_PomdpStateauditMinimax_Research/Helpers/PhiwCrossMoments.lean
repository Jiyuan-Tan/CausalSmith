module
public import CausalSmith.Stat.STAT_PomdpStateauditMinimax_Research.Helpers.PhiwSharpMoments

/-! # Cross moments of separated and overlapping PHIW windows. -/

@[expose] public section

namespace CausalSmith.Stat.PomdpStateauditMinimax

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability.FiniteMarkovOscillation
open Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation

lemma behaviorStep_iter_eq_markovOperatorIter {T nX nH k depth : Nat}
    (M : PomdpModel T nX nH k) (F : JointState nX nH → ℝ) :
    ((behaviorStep M)^[depth] F) =
      markovOperatorIter (policyKernel M M.b) depth F := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      rw [Function.iterate_succ_apply']
      simp only [markovOperatorIter_succ]
      rw [ih]
      rfl

lemma sum_stationary_mul_behaviorStep_iter {T nX nH k depth : Nat}
    (M : PomdpModel T nX nH k) (d : JointState nX nH → ℝ)
    (hd : IsStationary (policyKernel M M.b) d)
    (F : JointState nX nH → ℝ) :
    ∑ s, d s * ((behaviorStep M)^[depth] F) s = ∑ s, d s * F s := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      rw [Function.iterate_succ_apply']
      unfold behaviorStep
      calc
        ∑ s, d s * ∑ x, policyKernel M M.b s x * ((behaviorStep M)^[depth] F) x =
            ∑ s, ∑ x, d s * (policyKernel M M.b s x *
              ((behaviorStep M)^[depth] F) x) := by
          apply Finset.sum_congr rfl
          intro s _
          rw [Finset.mul_sum]
        _ = ∑ x, ∑ s, d s * (policyKernel M M.b s x *
              ((behaviorStep M)^[depth] F) x) := Finset.sum_comm
        _ = ∑ x, (∑ s, d s * policyKernel M M.b s x) *
              ((behaviorStep M)^[depth] F) x := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro s _
          ring
        _ = ∑ x, d x * ((behaviorStep M)^[depth] F) x := by
          apply Finset.sum_congr rfl
          intro x _
          rw [hd.2 x]
        _ = _ := ih

/-- A behavior iterate is uniformly close to its stationary average at the
geometric oscillation rate. -/
lemma behaviorStep_iter_centered_le {T nX nH k depth : Nat} {t0 zeta : ℝ}
    (M : PomdpModel T nX nH k) (hM : HuWagerClass t0 zeta M)
    (hnX : 1 ≤ nX) (hnH : 1 ≤ nH) (B : ℝ)
    (F : JointState nX nH → ℝ) (hF : OscillationBound B F)
    (x : JointState nX nH) :
    |((behaviorStep M)^[depth] F) x -
      ∑ s, stationaryLaw (policyKernel M M.b) s * F s| ≤
        mixingAlpha t0 ^ depth * B := by
  letI : Nonempty (JointState nX nH) := ⟨(⟨0, hnX⟩, ⟨0, hnH⟩)⟩
  let d := stationaryLaw (policyKernel M M.b)
  let H := (behaviorStep M)^[depth] F
  have hd : ProbabilityVector d := hM.start.1.1
  have hH : OscillationBound (mixingAlpha t0 ^ depth * B) H := by
    rw [show H = markovOperatorIter (policyKernel M M.b) depth F from
      behaviorStep_iter_eq_markovOperatorIter M F]
    apply oscillationBound_markovOperatorIter
      (policyKernel M M.b)
      (policyKernel_probabilityVector_fin M hM.pomdp M.b hM.randomization.1)
      (Real.exp_nonneg _)
    · intro p q hp hq
      simpa [tvNorm, applyKernel, mixingAlpha, markovStep,
        Matrix.vecMul, dotProduct] using
        hM.contraction M.b (Or.inl rfl) p q hp hq
    · exact hF
  have hstat : ∑ s, d s * H s = ∑ s, d s * F s :=
    sum_stationary_mul_behaviorStep_iter M d hM.start.1 F
  rw [← hstat]
  have hre : H x - ∑ s, d s * H s = ∑ s, d s * (H x - H s) := by
    rw [show (∑ s, d s * (H x - H s)) =
        (∑ s, d s) * H x - ∑ s, d s * H s by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, Finset.sum_mul]]
    rw [hd.2, one_mul]
  rw [hre]
  calc
    |∑ s, d s * (H x - H s)| ≤ ∑ s, |d s * (H x - H s)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ s, d s * |H x - H s| := by
      apply Finset.sum_congr rfl
      intro s _
      rw [abs_mul, abs_of_nonneg (hd.1 s)]
    _ ≤ ∑ s, d s * (mixingAlpha t0 ^ depth * B) := by
      apply Finset.sum_le_sum
      intro s _
      exact mul_le_mul_of_nonneg_left (hH x s) (hd.1 s)
    _ = mixingAlpha t0 ^ depth * B := by
      rw [← Finset.sum_mul, hd.2, one_mul]

lemma targetStep_abs_le_one {T nX nH k : Nat} {zeta : ℝ}
    (M : PomdpModel T nX nH k) (hK : FullFiltrationPomdp M)
    (hOverlap : PolicyOverlap zeta M) (F : JointState nX nH → ℝ)
    (hF : ∀ s, |F s| ≤ 1) (x : JointState nX nH) :
    |targetStep M F x| ≤ 1 := by
  have hp := policyKernel_probabilityVector_fin M hK M.e hOverlap.1 x
  unfold targetStep
  calc
    |∑ s, policyKernel M M.e x s * F s| ≤
        ∑ s, |policyKernel M M.e x s * F s| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ s, policyKernel M M.e x s * |F s| := by
      apply Finset.sum_congr rfl
      intro s _
      rw [abs_mul, abs_of_nonneg (hp.1 s)]
    _ ≤ ∑ s, policyKernel M M.e x s * 1 := by
      apply Finset.sum_le_sum
      intro s _
      exact mul_le_mul_of_nonneg_left (hF s) (hp.1 s)
    _ = 1 := by simp [hp.2]

lemma targetIter_reward_abs_le_one {T nX nH k depth : Nat} {t0 zeta : ℝ}
    (M : PomdpModel T nX nH k) (hM : HuWagerClass t0 zeta M)
    (x : JointState nX nH) :
    |((targetStep M)^[depth] (rewardRegression M)) x| ≤ 1 := by
  induction depth generalizing x with
  | zero => simpa using rewardRegression_abs_le_one M hM x
  | succ depth ih =>
      rw [Function.iterate_succ_apply']
      exact targetStep_abs_le_one M hM.pomdp hM.overlap _ (fun s => ih s) x

lemma targetIter_reward_oscillation_two {T nX nH k depth : Nat} {t0 zeta : ℝ}
    (M : PomdpModel T nX nH k) (hM : HuWagerClass t0 zeta M) :
    OscillationBound 2 ((targetStep M)^[depth] (rewardRegression M)) := by
  intro x y
  calc
    |((targetStep M)^[depth] (rewardRegression M)) x -
        ((targetStep M)^[depth] (rewardRegression M)) y| ≤
      |((targetStep M)^[depth] (rewardRegression M)) x| +
        |((targetStep M)^[depth] (rewardRegression M)) y| := abs_sub _ _
    _ ≤ 2 := by linarith [targetIter_reward_abs_le_one (depth := depth) M hM x,
      targetIter_reward_abs_le_one (depth := depth) M hM y]

/-- A completed likelihood-ratio window, represented as a function of any
strictly later complete pre-action history. -/
noncomputable def pastWindowScore {T nX nH k : Nat}
    (M : PomdpModel T nX nH k) (a t j : Fin T)
    (htj : t.val < j.val) (h : PreHistory T nX nH k j) : ℝ :=
  (h.2.1 ⟨t.val, htj⟩).2 * ∏ q ∈ Finset.univ.filter
    (fun q : Fin j.val => a.val ≤ q.val ∧ q.val ≤ t.val),
      ratio M.b M.e (h.1 q).1 (h.2.1 q).1

lemma pastWindowScore_measurable {T nX nH k : Nat}
    (M : PomdpModel T nX nH k) (a t j : Fin T) (htj : t.val < j.val) :
    Measurable (pastWindowScore M a t j htj) := by
  unfold pastWindowScore
  apply Measurable.mul (by fun_prop)
  apply Finset.measurable_prod
  intro q _
  exact (measurable_of_countable fun xa : Fin nX × Fin k =>
    ratio M.b M.e xa.1 xa.2).comp
      (((by fun_prop : Measurable fun h : PreHistory T nX nH k j =>
        (h.1 q).1)).prodMk (by fun_prop))

lemma pastWindowScore_preHist {T nX nH k : Nat}
    (M : PomdpModel T nX nH k) (a t j : Fin T) (hat : a.val ≤ t.val)
    (htj : t.val < j.val) (w : FullPath T nX nH k) :
    pastWindowScore M a t j htj (preHist j w) = windowScore M a t w := by
  unfold pastWindowScore windowScore preHist currentState pastIndex actionAt rewardAt
  congr 1
  apply Finset.prod_bij (fun q _ => (⟨q.val, lt_trans q.isLt j.isLt⟩ : Fin T))
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    exact hq
  · intro q _ q' _ he
    apply Fin.ext
    simpa using congrArg Fin.val he
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    exact ⟨⟨q.val, lt_of_le_of_lt hq.2 htj⟩, by simpa using hq, Fin.ext rfl⟩
  · intro q _
    rfl

lemma pastWindowScore_preHist_memLp_two {T nX nH k : Nat} {zeta : ℝ}
    (M : PomdpModel T nX nH k) (hK : FullFiltrationPomdp M)
    (hA : FullFiltrationRandomization M) (hY : RewardMomentEnvelope M)
    (hOverlap : PolicyOverlap zeta M) (a t j : Fin T) (hat : a.val ≤ t.val)
    (htj : t.val < j.val) :
    MemLp (fun w => pastWindowScore M a t j htj (preHist j w)) 2 M.law := by
  let depth := t.val - a.val
  have hd : depth ≤ t.val := by dsimp [depth]; omega
  have hobs := observed_phiwScore_memLp_two M hK hA hY hOverlap t hd
  apply (memLp_congr_ae ?_).2 hobs
  filter_upwards with w
  rw [pastWindowScore_preHist M a t j hat htj w]
  have heq := phiwScore_observedRecord_eq_windowScore M t hd w
  simpa [depth, Nat.sub_sub_self hat] using heq.symm

/-- Kernel-side integrability for terminal weighted peeling when the history
multiplier and terminal reward are square integrable. -/
lemma weighted_terminal_kernel_integrable_of_memLp_two
    {T nX nH k : Nat} {zeta : ℝ}
    (M : PomdpModel T nX nH k) (hK : FullFiltrationPomdp M)
    (hA : FullFiltrationRandomization M) (hY : RewardMomentEnvelope M)
    (hOverlap : PolicyOverlap zeta M) (j t : Fin T) (hjt : j.val ≤ t.val)
    (G : PreHistory T nX nH k j → ℝ) (hGm : Measurable G)
    (hG2 : MemLp (fun w => G (preHist j w)) 2 M.law) :
    Integrable
      (fun z : PostHistory T nX nH k t × (ℝ × JointState nX nH) =>
        weightedRatioCarrier M j t hjt G z.1.1 *
          ratio M.b M.e z.1.1.2.2.1 z.1.2 * z.2.1)
      (M.law.map (fun w => (postHist t w, (rewardAt w t, nextState w t)))) := by
  have henc : Measurable (fun w : FullPath T nX nH k =>
      (postHist t w, (rewardAt w t, nextState w t))) := by
    unfold postHist preHist currentState pastIndex actionAt rewardAt nextState
    fun_prop
  have hm : Measurable
      (fun z : PostHistory T nX nH k t × (ℝ × JointState nX nH) =>
        weightedRatioCarrier M j t hjt G z.1.1 *
          ratio M.b M.e z.1.1.2.2.1 z.1.2 * z.2.1) := by
    exact (((weightedRatioCarrier_measurable M j t hjt G hGm).comp
      (show Measurable (fun z : PostHistory T nX nH k t ×
        (ℝ × JointState nX nH) => z.1.1) by fun_prop)).mul
      ((measurable_of_countable fun xa : Fin nX × Fin k =>
        ratio M.b M.e xa.1 xa.2).comp
          (show Measurable (fun z : PostHistory T nX nH k t ×
            (ℝ × JointState nX nH) => (z.1.1.2.2.1, z.1.2)) by fun_prop))).mul
      (by fun_prop)
  rw [integrable_map_measure hm.aestronglyMeasurable henc.aemeasurable]
  have hry := reward_sq_integrable_and_integral_le_one M hK hY t
  have hrm : AEStronglyMeasurable (fun w : FullPath T nX nH k => rewardAt w t) M.law := by
    apply Measurable.aestronglyMeasurable
    unfold rewardAt
    fun_prop
  have hr2 : MemLp (fun w : FullPath T nX nH k => rewardAt w t) 2 M.law :=
    (memLp_two_iff_integrable_sq hrm).2 hry.1
  have hprod := hG2.integrable_mul hr2
  let D := max 1 (policyFactor zeta) ^ t.val * policyFactor zeta
  apply (hprod.abs.const_mul D).mono' ((hm.comp henc).aestronglyMeasurable)
  filter_upwards with w
  dsimp only [Function.comp_apply]
  change ‖weightedRatioCarrier M j t hjt G (preHist t w) *
    ratio M.b M.e (currentState w t).1 (actionAt w t) * rewardAt w t‖ ≤
      D * |G (preHist j w) * rewardAt w t|
  simp only [norm_mul, Real.norm_eq_abs, abs_mul]
  have hc := weightedRatioCarrier_norm_bound M hA hOverlap j t hjt G (preHist t w)
  rw [restrictPreHist_preHist] at hc
  have hr := (policy_ratio_bounds M hOverlap hA.1
    (currentState w t).1 (actionAt w t)).2
  have hr0 := (policy_ratio_bounds M hOverlap hA.1
    (currentState w t).1 (actionAt w t)).1
  have hc' : |weightedRatioCarrier M j t hjt G (preHist t w)| ≤
      |G (preHist j w)| * max 1 (policyFactor zeta) ^ t.val := by
    simpa [Real.norm_eq_abs] using hc
  rw [abs_of_nonneg (policy_ratio_bounds M hOverlap hA.1 _ _).1]
  calc
    |weightedRatioCarrier M j t hjt G (preHist t w)| *
        ratio M.b M.e (currentState w t).1 (actionAt w t) * |rewardAt w t| ≤
      (|G (preHist j w)| * max 1 (policyFactor zeta) ^ t.val) *
        policyFactor zeta * |rewardAt w t| := by
          exact mul_le_mul
            (mul_le_mul hc' hr hr0
              (mul_nonneg (abs_nonneg _) (pow_nonneg (by positivity) _)))
            le_rfl (abs_nonneg _) (mul_nonneg
              (mul_nonneg (abs_nonneg _) (pow_nonneg (by positivity) _))
              (Real.exp_nonneg _))
    _ = D * (|G (preHist j w)| * |rewardAt w t|) := by
      dsimp [D]
      ring

lemma weighted_terminal_action_integrable_of_memLp_two
    {T nX nH k : Nat} {zeta : ℝ}
    (M : PomdpModel T nX nH k) (hA : FullFiltrationRandomization M)
    (hOverlap : PolicyOverlap zeta M) (j t : Fin T) (hjt : j.val ≤ t.val)
    (G : PreHistory T nX nH k j → ℝ) (hGm : Measurable G)
    (hG2 : MemLp (fun w => G (preHist j w)) 2 M.law) :
    Integrable
      (fun z : PreHistory T nX nH k t × Fin k =>
        weightedRatioCarrier M j t hjt G z.1 *
          ∫ y, y.1 ∂M.K z.1.2.2 z.2)
      (M.law.map (fun w => (preHist t w, actionAt w t))) := by
  let H : JointState nX nH × Fin k → ℝ := fun sa => ∫ y, y.1 ∂M.K sa.1 sa.2
  obtain ⟨C, hC⟩ := Finite.exists_le (fun sa : JointState nX nH × Fin k => ‖H sa‖)
  let D := max 1 (policyFactor zeta) ^ t.val * C
  have henc : Measurable (fun w : FullPath T nX nH k =>
      (preHist t w, actionAt w t)) := by
    unfold preHist currentState pastIndex actionAt
    fun_prop
  have hm : Measurable (fun z : PreHistory T nX nH k t × Fin k =>
      weightedRatioCarrier M j t hjt G z.1 * H (z.1.2.2, z.2)) := by
    exact ((weightedRatioCarrier_measurable M j t hjt G hGm).comp measurable_fst).mul
      ((measurable_of_finite H).comp
        (show Measurable (fun z : PreHistory T nX nH k t × Fin k =>
          (z.1.2.2, z.2)) by fun_prop))
  rw [integrable_map_measure hm.aestronglyMeasurable henc.aemeasurable]
  apply (hG2.integrable one_le_two).abs.const_mul D |>.mono'
    ((hm.comp henc).aestronglyMeasurable)
  filter_upwards with w
  change ‖weightedRatioCarrier M j t hjt G (preHist t w) *
    H (currentState w t, actionAt w t)‖ ≤ D * |G (preHist j w)|
  rw [norm_mul]
  have hc := weightedRatioCarrier_norm_bound M hA hOverlap j t hjt G (preHist t w)
  rw [restrictPreHist_preHist] at hc
  calc
    _ ≤ (‖G (preHist j w)‖ * max 1 (policyFactor zeta) ^ t.val) * C :=
      mul_le_mul hc (hC (currentState w t, actionAt w t)) (norm_nonneg _)
        (mul_nonneg (norm_nonneg _) (pow_nonneg (by positivity) _))
    _ = D * |G (preHist j w)| := by dsimp [D]; ring

/-- A square-integrable history multiplier can be carried through an entire
future target window, including its terminal reward. -/
lemma weighted_target_window_of_memLp_two {T nX nH k : Nat} {zeta : ℝ}
    (M : PomdpModel T nX nH k) (hK : FullFiltrationPomdp M)
    (hA : FullFiltrationRandomization M) (hY : RewardMomentEnvelope M)
    (hOverlap : PolicyOverlap zeta M) (j t : Fin T) (hjt : j.val ≤ t.val)
    (G : PreHistory T nX nH k j → ℝ) (hGm : Measurable G)
    (hG2 : MemLp (fun w => G (preHist j w)) 2 M.law) :
    ∫ w, G (preHist j w) * windowScore M j t w ∂M.law =
      ∫ w, G (preHist j w) *
        ((targetStep M)^[t.val - j.val] (rewardRegression M))
          (currentState w j) ∂M.law := by
  calc
    _ = ∫ w, weightedRatioCarrier M j t hjt G (preHist t w) *
          rewardRegression M (currentState w t) ∂M.law :=
      weightedRatioCarrier_terminal_peeling M hK hA hY hOverlap j t hjt G hGm
        (weighted_terminal_kernel_integrable_of_memLp_two
          M hK hA hY hOverlap j t hjt G hGm hG2)
        (weighted_terminal_action_integrable_of_memLp_two
          M hA hOverlap j t hjt G hGm hG2)
    _ = _ := weightedRatioCarrier_iteration M hK hA hOverlap j G hGm
      (hG2.integrable one_le_two) t.val hjt t.isLt (rewardRegression M)

/-- Exact cross moment for two disjoint windows: the later window becomes a
target iterate evaluated at its initial state. -/
lemma integral_disjoint_windowScore_mul {T nX nH k : Nat} {zeta : ℝ}
    (M : PomdpModel T nX nH k) (hK : FullFiltrationPomdp M)
    (hA : FullFiltrationRandomization M) (hY : RewardMomentEnvelope M)
    (hOverlap : PolicyOverlap zeta M)
    (a t j u : Fin T) (hat : a.val ≤ t.val) (htj : t.val < j.val)
    (hju : j.val ≤ u.val) :
    ∫ w, windowScore M a t w * windowScore M j u w ∂M.law =
      ∫ w, windowScore M a t w *
        ((targetStep M)^[u.val - j.val] (rewardRegression M))
          (currentState w j) ∂M.law := by
  let G := pastWindowScore M a t j htj
  have hGm : Measurable G := pastWindowScore_measurable M a t j htj
  have hG2 : MemLp (fun w => G (preHist j w)) 2 M.law :=
    pastWindowScore_preHist_memLp_two M hK hA hY hOverlap a t j hat htj
  have hmain := weighted_target_window_of_memLp_two
    M hK hA hY hOverlap j u hju G hGm hG2
  calc
    _ = ∫ w, G (preHist j w) * windowScore M j u w ∂M.law := by
      apply integral_congr_ae
      filter_upwards with w
      dsimp [G]
      rw [pastWindowScore_preHist M a t j hat htj w]
    _ = ∫ w, G (preHist j w) *
          ((targetStep M)^[u.val - j.val] (rewardRegression M))
            (currentState w j) ∂M.law := hmain
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with w
      dsimp [G]
      rw [pastWindowScore_preHist M a t j hat htj w]

lemma integral_windowScore_mul_future_eq_behaviorIter
    {T nX nH k gap : Nat} {zeta : ℝ}
    (M : PomdpModel T nX nH k) (hK : FullFiltrationPomdp M)
    (hA : FullFiltrationRandomization M) (hY : RewardMomentEnvelope M)
    (hOverlap : PolicyOverlap zeta M) (a t : Fin T) (hat : a.val ≤ t.val)
    (ht : t.val + 1 + gap < T) (F : JointState nX nH → ℝ) :
    ∫ w, windowScore M a t w *
        F (currentState w ⟨t.val + 1 + gap, ht⟩) ∂M.law =
      ∫ w, windowScore M a t w *
        ((behaviorStep M)^[gap] F)
          (currentState w ⟨t.val + 1, by omega⟩) ∂M.law := by
  let r : Fin T := ⟨t.val + 1, by omega⟩
  let G := pastWindowScore M a t r (by dsimp [r]; omega)
  have hGm : Measurable G := pastWindowScore_measurable M a t r (by dsimp [r]; omega)
  have hG2 : MemLp (fun w => G (preHist r w)) 2 M.law :=
    pastWindowScore_preHist_memLp_two M hK hA hY hOverlap a t r hat
      (by dsimp [r]; omega)
  have hmain := integral_preHist_mul_behaviorIter M hK hA r ht G hGm
    (hG2.integrable one_le_two) F
  calc
    _ = ∫ w, G (preHist r w) *
          F (currentState w ⟨r.val + gap, ht⟩) ∂M.law := by
      apply integral_congr_ae
      filter_upwards with w
      dsimp [G]
      rw [pastWindowScore_preHist M a t r hat (by dsimp [r]; omega) w]
    _ = ∫ w, G (preHist r w) *
          ((behaviorStep M)^[gap] F) (currentState w r) ∂M.law := hmain
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with w
      dsimp [G]
      rw [pastWindowScore_preHist M a t r hat (by dsimp [r]; omega) w]

lemma integral_abs_windowScore_le_power {T nX nH k : Nat} {t0 zeta : ℝ}
    (M : PomdpModel T nX nH k) (hM : HuWagerClass t0 zeta M)
    (a t : Fin T) (hat : a.val ≤ t.val) (ht : t.val + 1 < T) :
    ∫ w, |windowScore M a t w| ∂M.law ≤
      policyFactor zeta ^ (t.val - a.val + 1) := by
  let r : Fin T := ⟨t.val + 1, ht⟩
  have hX2 : MemLp (fun w => windowScore M a t w) 2 M.law := by
    have hG2 := pastWindowScore_preHist_memLp_two M hM.pomdp hM.randomization
      hM.moment hM.overlap a t r hat (by dsimp [r]; omega)
    apply (memLp_congr_ae ?_).2 hG2
    filter_upwards with w
    exact (pastWindowScore_preHist M a t r hat (by dsimp [r]; omega) w).symm
  have habs : Integrable (fun w => |windowScore M a t w|) M.law :=
    (hX2.integrable one_le_two).abs
  have hsq : Integrable (fun w => windowScore M a t w ^ 2) M.law :=
    (memLp_two_iff_integrable_sq hX2.1).1 hX2
  let Ld := policyFactor zeta ^ (t.val - a.val + 1)
  have hLd1 : 1 ≤ Ld := by
    apply one_le_pow₀
    rw [policyFactor, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr hM.zeta_pos.le
  calc
    (∫ w, |windowScore M a t w| ∂M.law) ≤
        ∫ w, (windowScore M a t w ^ 2 + 1) / 2 ∂M.law := by
      apply integral_mono habs
      · exact (hsq.add (integrable_const 1)).div_const 2
      · intro w
        nlinarith [sq_nonneg (|windowScore M a t w| - 1),
          sq_abs (windowScore M a t w)]
    _ = ((∫ w, windowScore M a t w ^ 2 ∂M.law) + 1) / 2 := by
      rw [integral_div, integral_add hsq (integrable_const 1), integral_const]
      simp
    _ ≤ (Ld + 1) / 2 := by
      gcongr
      exact integral_windowScore_sq_le M hM.pomdp hM.randomization hM.moment
        hM.overlap hM.start a t hat
    _ ≤ Ld := by linarith

lemma abs_integral_windowScore_mul_centered_behavior_le
    {T nX nH k gap : Nat} {t0 zeta : ℝ}
    (M : PomdpModel T nX nH k) (hM : HuWagerClass t0 zeta M)
    (hnX : 1 ≤ nX) (hnH : 1 ≤ nH) (a t : Fin T) (hat : a.val ≤ t.val)
    (ht : t.val + 1 + gap < T) (B : ℝ) (hB : 0 ≤ B)
    (F : JointState nX nH → ℝ) (hF : OscillationBound B F) :
    |∫ w, windowScore M a t w *
      (((behaviorStep M)^[gap] F) (currentState w ⟨t.val + 1, by omega⟩) -
        ∑ s, stationaryLaw (policyKernel M M.b) s * F s) ∂M.law| ≤
      mixingAlpha t0 ^ gap * B *
        policyFactor zeta ^ (t.val - a.val + 1) := by
  let C := mixingAlpha t0 ^ gap * B
  have hC : 0 ≤ C := mul_nonneg (pow_nonneg (Real.exp_nonneg _) _) hB
  have hcenter (w : FullPath T nX nH k) :
      |((behaviorStep M)^[gap] F) (currentState w ⟨t.val + 1, by omega⟩) -
        ∑ s, stationaryLaw (policyKernel M M.b) s * F s| ≤ C :=
    behaviorStep_iter_centered_le M hM hnX hnH B F hF _
  have hX : Integrable (fun w => windowScore M a t w) M.law := by
    let r : Fin T := ⟨t.val + 1, by omega⟩
    have hX2 := pastWindowScore_preHist_memLp_two M hM.pomdp hM.randomization
      hM.moment hM.overlap a t r hat (by dsimp [r]; omega)
    have heq : (fun w => windowScore M a t w) =
        fun w => pastWindowScore M a t r (by dsimp [r]; omega) (preHist r w) := by
      funext w
      exact (pastWindowScore_preHist M a t r hat (by dsimp [r]; omega) w).symm
    rw [heq]
    exact hX2.integrable one_le_two
  calc
    _ ≤ ∫ w, |windowScore M a t w *
        (((behaviorStep M)^[gap] F) (currentState w ⟨t.val + 1, by omega⟩) -
          ∑ s, stationaryLaw (policyKernel M M.b) s * F s)| ∂M.law :=
      abs_integral_le_integral_abs
    _ ≤ ∫ w, C * |windowScore M a t w| ∂M.law := by
      apply integral_mono
      · exact hX.mul_bdd
          ((measurable_of_finite fun x : JointState nX nH =>
            ((behaviorStep M)^[gap] F) x -
              ∑ s, stationaryLaw (policyKernel M M.b) s * F s).comp
            (by unfold currentState; fun_prop) |>.aestronglyMeasurable)
          (by filter_upwards with w; exact hcenter w)
        |>.abs
      · exact hX.abs.const_mul C
      · intro w
        dsimp only
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hcenter w) (abs_nonneg _)
          |>.trans_eq (by ring)
    _ = C * ∫ w, |windowScore M a t w| ∂M.law := by rw [integral_const_mul]
    _ ≤ C * policyFactor zeta ^ (t.val - a.val + 1) :=
      mul_le_mul_of_nonneg_left
        (integral_abs_windowScore_le_power M hM a t hat (by omega)) hC
    _ = _ := rfl

/-- Disjoint equal-depth window covariance numerator decays geometrically in
the gap after the first window. -/
lemma abs_windowScore_cross_sub_means_le_disjoint
    {T nX nH k depth lag : Nat} {t0 zeta : ℝ}
    (M : PomdpModel T nX nH k) (hM : HuWagerClass t0 zeta M)
    (hnX : 1 ≤ nX) (hnH : 1 ≤ nH) (t u : Fin T)
    (hdepth : depth ≤ t.val) (hu : u.val = t.val + lag)
    (hdisjoint : depth + 1 ≤ lag) :
    |(∫ w, windowScore M ⟨t.val - depth, by omega⟩ t w *
          windowScore M ⟨u.val - depth, by omega⟩ u w ∂M.law) -
      (∫ w, windowScore M ⟨t.val - depth, by omega⟩ t w ∂M.law) *
      (∫ w, windowScore M ⟨u.val - depth, by omega⟩ u w ∂M.law)| ≤
      mixingAlpha t0 ^ (lag - depth - 1) * 2 *
        policyFactor zeta ^ (depth + 1) := by
  let a : Fin T := ⟨t.val - depth, by omega⟩
  let j : Fin T := ⟨u.val - depth, by omega⟩
  let gap := lag - depth - 1
  let F := (targetStep M)^[depth] (rewardRegression M)
  have hat : a.val ≤ t.val := by dsimp [a]; omega
  have htj : t.val < j.val := by dsimp [j]; omega
  have hju : j.val ≤ u.val := by dsimp [j]; omega
  have hj : j.val = t.val + 1 + gap := by dsimp [j, gap]; omega
  have hud : u.val - j.val = depth := by dsimp [j]; omega
  have hcross := integral_disjoint_windowScore_mul M hM.pomdp hM.randomization
    hM.moment hM.overlap a t j u hat htj hju
  have hprop := integral_windowScore_mul_future_eq_behaviorIter
    M hM.pomdp hM.randomization hM.moment hM.overlap a t hat
      (gap := gap) (by omega) F
  have hy := integral_windowScore_eq_stationary_targetIter M hM.pomdp
    hM.randomization hM.moment hM.overlap hM.start j u hju
  rw [hud] at hcross hy
  change |(∫ w, windowScore M a t w * windowScore M j u w ∂M.law) -
    (∫ w, windowScore M a t w ∂M.law) *
      (∫ w, windowScore M j u w ∂M.law)| ≤ _
  rw [hcross, hy]
  have hji : j = (⟨t.val + 1 + gap, by omega⟩ : Fin T) := Fin.ext hj
  rw [hji]
  rw [hprop]
  let c := ∑ s, stationaryLaw (policyKernel M M.b) s * F s
  have hX : Integrable (fun w => windowScore M a t w) M.law := by
    let r : Fin T := ⟨t.val + 1, by omega⟩
    have hX2 := pastWindowScore_preHist_memLp_two M hM.pomdp hM.randomization
      hM.moment hM.overlap a t r hat (by dsimp [r]; omega)
    apply (memLp_congr_ae ?_).2 hX2 |>.integrable one_le_two
    filter_upwards with w
    exact (pastWindowScore_preHist M a t r hat (by dsimp [r]; omega) w).symm
  have hBint : Integrable (fun w => windowScore M a t w *
      ((behaviorStep M)^[gap] F) (currentState w ⟨t.val + 1, by omega⟩)) M.law := by
    obtain ⟨C, hC⟩ := Finite.exists_le
      (fun s : JointState nX nH => ‖((behaviorStep M)^[gap] F) s‖)
    apply hX.mul_bdd
      ((measurable_of_finite ((behaviorStep M)^[gap] F)).comp
        (by unfold currentState; fun_prop) |>.aestronglyMeasurable)
    filter_upwards with w
    simpa only [Function.comp_apply] using hC (currentState w ⟨t.val + 1, by omega⟩)
  have hre : (∫ w, windowScore M a t w *
      (((behaviorStep M)^[gap] F) (currentState w ⟨t.val + 1, by omega⟩) - c)
      ∂M.law) =
      (∫ w, windowScore M a t w *
        ((behaviorStep M)^[gap] F) (currentState w ⟨t.val + 1, by omega⟩) ∂M.law) -
        (∫ w, windowScore M a t w ∂M.law) * c := by
    simp_rw [mul_sub]
    rw [integral_sub hBint (hX.mul_const c), integral_mul_const]
  rw [← hre]
  simpa [a, gap, F, Nat.sub_sub_self hdepth] using
    abs_integral_windowScore_mul_centered_behavior_le M hM hnX hnH a t hat
      (gap := gap) (by omega) 2 (by norm_num) F
      (targetIter_reward_oscillation_two M hM)

lemma abs_covariance_windowScore_le_disjoint
    {T nX nH k depth lag : Nat} {t0 zeta : ℝ}
    (M : PomdpModel T nX nH k) (hM : HuWagerClass t0 zeta M)
    (hnX : 1 ≤ nX) (hnH : 1 ≤ nH) (t u : Fin T)
    (hdepth : depth ≤ t.val) (hu : u.val = t.val + lag)
    (hdisjoint : depth + 1 ≤ lag) :
    |covariance
      (fun w => windowScore M ⟨t.val - depth, by omega⟩ t w)
      (fun w => windowScore M ⟨u.val - depth, by omega⟩ u w) M.law| ≤
      mixingAlpha t0 ^ (lag - depth - 1) * 2 *
        policyFactor zeta ^ (depth + 1) := by
  have hXt : MemLp
      (fun w => windowScore M ⟨t.val - depth, by omega⟩ t w) 2 M.law := by
    have h := observed_phiwScore_memLp_two M hM.pomdp hM.randomization
      hM.moment hM.overlap t hdepth
    apply (memLp_congr_ae ?_).2 h
    filter_upwards with w
    exact (phiwScore_observedRecord_eq_windowScore M t hdepth w).symm
  have hdu : depth ≤ u.val := by omega
  have hXu : MemLp
      (fun w => windowScore M ⟨u.val - depth, by omega⟩ u w) 2 M.law := by
    have h := observed_phiwScore_memLp_two M hM.pomdp hM.randomization
      hM.moment hM.overlap u hdu
    apply (memLp_congr_ae ?_).2 h
    filter_upwards with w
    exact (phiwScore_observedRecord_eq_windowScore M u hdu w).symm
  rw [covariance_eq_sub hXt hXu]
  exact abs_windowScore_cross_sub_means_le_disjoint M hM hnX hnH t u
    hdepth hu hdisjoint

end CausalSmith.Stat.PomdpStateauditMinimax
