module
public import CausalSmith.Stat.STAT_PomdpStateauditMinimax_Research.Helpers.PhiwCrossMoments

/-! # Mixed likelihood carriers for overlapping PHIW windows. -/

@[expose] public section

namespace CausalSmith.Stat.PomdpStateauditMinimax

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability.FiniteMarkovOscillation
open Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation

/-- Target-policy conditional absolute reward mean. -/
noncomputable def absRewardRegression {T nX nH k : Nat}
    (M : PomdpModel T nX nH k) (s : JointState nX nH) : ℝ :=
  ∑ a : Fin k, M.e s.1 a * ∫ y, |y.1| ∂M.K s a

lemma absRewardRegression_nonneg_le_one {T nX nH k : Nat} {t0 zeta : ℝ}
    (M : PomdpModel T nX nH k) (hM : HuWagerClass t0 zeta M)
    (s : JointState nX nH) :
    0 ≤ absRewardRegression M s ∧ absRewardRegression M s ≤ 1 := by
  have habs (a : Fin k) : Integrable (fun y => |y.1|) (M.K s a) :=
    (hM.moment s a).1.abs
  have hmean (a : Fin k) : ∫ y, |y.1| ∂M.K s a ≤ 1 := by
    letI : IsProbabilityMeasure (M.K s a) := hM.pomdp.1 s a
    calc
      (∫ y, |y.1| ∂M.K s a) ≤ ∫ y, (y.1 ^ 2 + 1) / 2 ∂M.K s a := by
        apply integral_mono (habs a)
        · exact ((hM.moment s a).2.1.add (integrable_const 1)).div_const 2
        · intro y
          nlinarith [sq_nonneg (|y.1| - 1), sq_abs y.1]
      _ = ((∫ y, y.1 ^ 2 ∂M.K s a) + 1) / 2 := by
        rw [integral_div, integral_add (hM.moment s a).2.1 (integrable_const 1),
          integral_const]
        simp
      _ ≤ 1 := by linarith [(hM.moment s a).2.2.2]
  unfold absRewardRegression
  constructor
  · apply Finset.sum_nonneg
    intro a _
    exact mul_nonneg ((hM.overlap.1 s.1).1 a)
      (integral_nonneg fun y => abs_nonneg y.1)
  · calc
      (∑ a : Fin k, M.e s.1 a * ∫ y, |y.1| ∂M.K s a) ≤
          ∑ a : Fin k, M.e s.1 a * 1 := by
        apply Finset.sum_le_sum
        intro a _
        exact mul_le_mul_of_nonneg_left (hmean a) ((hM.overlap.1 s.1).1 a)
      _ = 1 := by simp [(hM.overlap.1 s.1).2]

lemma targetIter_absReward_nonneg_le_one {T nX nH k depth : Nat} {t0 zeta : ℝ}
    (M : PomdpModel T nX nH k) (hM : HuWagerClass t0 zeta M)
    (s : JointState nX nH) :
    0 ≤ ((targetStep M)^[depth] (absRewardRegression M)) s ∧
      ((targetStep M)^[depth] (absRewardRegression M)) s ≤ 1 := by
  induction depth generalizing s with
  | zero => simpa using absRewardRegression_nonneg_le_one M hM s
  | succ depth ih =>
      rw [Function.iterate_succ_apply']
      constructor
      · exact targetStep_nonneg M hM.pomdp hM.overlap _ (fun x => (ih x).1) s
      · exact targetStep_le_const M hM.pomdp hM.overlap _ 1 (fun x => (ih x).2) s

/-- At the earlier reward epoch, the later absolute-reward continuation is
multiplied by the current absolute reward inside the transition kernel. -/
noncomputable def twoRewardBridge {T nX nH k : Nat}
    (M : PomdpModel T nX nH k) (F : JointState nX nH → ℝ)
    (s : JointState nX nH) : ℝ :=
  ∑ a : Fin k, M.e s.1 a * ∫ y, |y.1| * F y.2 ∂M.K s a

lemma twoRewardBridge_nonneg_le_one {T nX nH k : Nat} {t0 zeta : ℝ}
    (M : PomdpModel T nX nH k) (hM : HuWagerClass t0 zeta M)
    (F : JointState nX nH → ℝ) (hF : ∀ s, 0 ≤ F s ∧ F s ≤ 1)
    (s : JointState nX nH) :
    0 ≤ twoRewardBridge M F s ∧ twoRewardBridge M F s ≤ 1 := by
  have hint (a : Fin k) : Integrable (fun y => |y.1| * F y.2) (M.K s a) := by
    refine (hM.moment s a).1.abs.mul_bdd (c := 1)
      ((measurable_of_finite F).comp (by fun_prop) |>.aestronglyMeasurable)
      ?_
    filter_upwards with y
    change ‖F y.2‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (hF y.2).1]
    exact (hF y.2).2
  have hinner0 (a : Fin k) : 0 ≤ ∫ y, |y.1| * F y.2 ∂M.K s a :=
    integral_nonneg fun y => mul_nonneg (abs_nonneg _) (hF y.2).1
  have hinner1 (a : Fin k) : ∫ y, |y.1| * F y.2 ∂M.K s a ≤ 1 := by
    calc
      _ ≤ ∫ y, |y.1| ∂M.K s a := by
        apply integral_mono (hint a) (hM.moment s a).1.abs
        intro y
        simpa using mul_le_of_le_one_right (abs_nonneg y.1) (hF y.2).2
      _ ≤ 1 := by
        have hh := absRewardRegression_nonneg_le_one M hM s
        have he0 := (hM.overlap.1 s.1).1 a
        -- Use the direct conditional second-moment calculation.
        letI : IsProbabilityMeasure (M.K s a) := hM.pomdp.1 s a
        calc
          _ ≤ ∫ y, (y.1 ^ 2 + 1) / 2 ∂M.K s a := by
            apply integral_mono (hM.moment s a).1.abs
            · exact ((hM.moment s a).2.1.add (integrable_const 1)).div_const 2
            · intro y
              nlinarith [sq_nonneg (|y.1| - 1), sq_abs y.1]
          _ = ((∫ y, y.1 ^ 2 ∂M.K s a) + 1) / 2 := by
            rw [integral_div, integral_add (hM.moment s a).2.1
              (integrable_const 1), integral_const]
            simp
          _ ≤ 1 := by linarith [(hM.moment s a).2.2.2]
  unfold twoRewardBridge
  constructor
  · exact Finset.sum_nonneg fun a _ =>
      mul_nonneg ((hM.overlap.1 s.1).1 a) (hinner0 a)
  · calc
      _ ≤ ∑ a : Fin k, M.e s.1 a * 1 := by
        apply Finset.sum_le_sum
        intro a _
        exact mul_le_mul_of_nonneg_left (hinner1 a) ((hM.overlap.1 s.1).1 a)
      _ = 1 := by simp [(hM.overlap.1 s.1).2]

/-- The target-policy one-step regression of an arbitrary terminal
reward/next-state functional. -/
noncomputable def terminalFunctionalRegression {T nX nH k : Nat}
    (M : PomdpModel T nX nH k) (R : ℝ × JointState nX nH → ℝ)
    (s : JointState nX nH) : ℝ :=
  ∑ a : Fin k, M.e s.1 a * ∫ y, R y ∂M.K s a

/-- Terminal peeling with a general reward/next-state functional.  This is
the carrier-parameter form needed for two overlapping score windows. -/
lemma weightedRatioCarrier_terminalFunctional_peeling {T nX nH k : Nat}
    {zeta : ℝ} (M : PomdpModel T nX nH k) (hK : FullFiltrationPomdp M)
    (hA : FullFiltrationRandomization M) (hOverlap : PolicyOverlap zeta M)
    (j t : Fin T) (hjt : j.val ≤ t.val)
    (G : PreHistory T nX nH k j → ℝ) (hGm : Measurable G)
    (R : ℝ × JointState nX nH → ℝ)
    (hjoint : Integrable
      (fun z : PostHistory T nX nH k t × (ℝ × JointState nX nH) =>
        weightedRatioCarrier M j t hjt G z.1.1 *
          ratio M.b M.e z.1.1.2.2.1 z.1.2 * R z.2)
      (M.law.map (fun w => (postHist t w, (rewardAt w t, nextState w t)))))
    (haction : Integrable
      (fun z : PreHistory T nX nH k t × Fin k =>
        weightedRatioCarrier M j t hjt G z.1 *
          ∫ y, R y ∂M.K z.1.2.2 z.2)
      (M.law.map (fun w => (preHist t w, actionAt w t)))) :
    ∫ w, weightedRatioCarrier M j t hjt G (preHist t w) *
          ratio M.b M.e (currentState w t).1 (actionAt w t) *
          R (rewardAt w t, nextState w t) ∂M.law =
      ∫ w, weightedRatioCarrier M j t hjt G (preHist t w) *
          terminalFunctionalRegression M R (currentState w t) ∂M.law := by
  have henc : Measurable (fun w : FullPath T nX nH k =>
      (postHist t w, (rewardAt w t, nextState w t))) := by
    unfold postHist preHist currentState pastIndex actionAt rewardAt nextState
    fun_prop
  have hpre : Measurable (preHist t : FullPath T nX nH k → _) := by
    unfold preHist currentState pastIndex
    fun_prop
  calc
    _ = ∫ z, weightedRatioCarrier M j t hjt G z.1.1 *
          ratio M.b M.e z.1.1.2.2.1 z.1.2 * R z.2
          ∂(M.law.map (fun w => (postHist t w,
            (rewardAt w t, nextState w t)))) := by
      rw [integral_map henc.aemeasurable hjoint.aestronglyMeasurable]
      rfl
    _ = ∫ h, ∫ y, weightedRatioCarrier M j t hjt G h.1 *
          ratio M.b M.e h.1.2.2.1 h.2 * R y ∂M.K h.1.2.2 h.2
          ∂(M.law.map (postHist t)) :=
      full_history_integral_kernel_step M hK t _ hjoint
    _ = ∫ z, ratio M.b M.e z.1.2.2.1 z.2 *
          (weightedRatioCarrier M j t hjt G z.1 *
            ∫ y, R y ∂M.K z.1.2.2 z.2)
          ∂(M.law.map (fun w => (preHist t w, actionAt w t))) := by
      apply integral_congr_ae
      filter_upwards with z
      rw [integral_const_mul]
      ring
    _ = ∫ h, ∑ a : Fin k, M.e h.2.2.1 a *
          (weightedRatioCarrier M j t hjt G h *
            ∫ y, R y ∂M.K h.2.2 a) ∂(M.law.map (preHist t)) :=
      full_history_integral_ratio_step M hA hOverlap t _ haction
    _ = ∫ h, weightedRatioCarrier M j t hjt G h *
          terminalFunctionalRegression M R h.2.2
          ∂(M.law.map (preHist t)) := by
      apply integral_congr_ae
      filter_upwards with h
      unfold terminalFunctionalRegression
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by
      rw [integral_map hpre.aemeasurable]
      · rfl
      · exact ((weightedRatioCarrier_measurable M j t hjt G hGm).mul
          ((measurable_of_finite (terminalFunctionalRegression M R)).comp
            (by fun_prop))).aestronglyMeasurable

lemma weighted_terminalFunctional_kernel_integrable_of_memLp_two
    {T nX nH k : Nat} {zeta : ℝ}
    (M : PomdpModel T nX nH k) (hK : FullFiltrationPomdp M)
    (hA : FullFiltrationRandomization M) (hY : RewardMomentEnvelope M)
    (hOverlap : PolicyOverlap zeta M) (j t : Fin T) (hjt : j.val ≤ t.val)
    (G : PreHistory T nX nH k j → ℝ) (hGm : Measurable G)
    (hG2 : MemLp (fun w => G (preHist j w)) 2 M.law)
    (R : ℝ × JointState nX nH → ℝ) (hRm : Measurable R)
    (hR : ∀ y, |R y| ≤ |y.1|) :
    Integrable
      (fun z : PostHistory T nX nH k t × (ℝ × JointState nX nH) =>
        weightedRatioCarrier M j t hjt G z.1.1 *
          ratio M.b M.e z.1.1.2.2.1 z.1.2 * R z.2)
      (M.law.map (fun w => (postHist t w, (rewardAt w t, nextState w t)))) := by
  have hm : Measurable
      (fun z : PostHistory T nX nH k t × (ℝ × JointState nX nH) =>
        weightedRatioCarrier M j t hjt G z.1.1 *
          ratio M.b M.e z.1.1.2.2.1 z.1.2 * R z.2) :=
    (((weightedRatioCarrier_measurable M j t hjt G hGm).comp
      (show Measurable (fun z : PostHistory T nX nH k t ×
        (ℝ × JointState nX nH) => z.1.1) by fun_prop)).mul
      ((measurable_of_countable fun xa : Fin nX × Fin k =>
        ratio M.b M.e xa.1 xa.2).comp
          (show Measurable (fun z : PostHistory T nX nH k t ×
            (ℝ × JointState nX nH) => (z.1.1.2.2.1, z.1.2)) by fun_prop))).mul
      (hRm.comp measurable_snd)
  apply (weighted_terminal_kernel_integrable_of_memLp_two
    M hK hA hY hOverlap j t hjt G hGm hG2).abs.mono' hm.aestronglyMeasurable
  filter_upwards with z
  simp only [norm_mul, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left (hR z.2)
    (mul_nonneg (abs_nonneg _) (abs_nonneg _))

lemma weighted_terminalFunctional_action_integrable_of_memLp_two
    {T nX nH k : Nat} {zeta : ℝ}
    (M : PomdpModel T nX nH k) (hA : FullFiltrationRandomization M)
    (hOverlap : PolicyOverlap zeta M) (j t : Fin T) (hjt : j.val ≤ t.val)
    (G : PreHistory T nX nH k j → ℝ) (hGm : Measurable G)
    (hG2 : MemLp (fun w => G (preHist j w)) 2 M.law)
    (R : ℝ × JointState nX nH → ℝ) :
    Integrable
      (fun z : PreHistory T nX nH k t × Fin k =>
        weightedRatioCarrier M j t hjt G z.1 *
          ∫ y, R y ∂M.K z.1.2.2 z.2)
      (M.law.map (fun w => (preHist t w, actionAt w t))) := by
  let H : JointState nX nH × Fin k → ℝ := fun sa => ∫ y, R y ∂M.K sa.1 sa.2
  obtain ⟨C, hC⟩ := Finite.exists_le (fun sa : JointState nX nH × Fin k => ‖H sa‖)
  let D := max 1 (policyFactor zeta) ^ t.val * C
  have henc : Measurable (fun w : FullPath T nX nH k =>
      (preHist t w, actionAt w t)) := by
    unfold preHist currentState pastIndex actionAt
    fun_prop
  have hm : Measurable (fun z : PreHistory T nX nH k t × Fin k =>
      weightedRatioCarrier M j t hjt G z.1 * H (z.1.2.2, z.2)) :=
    ((weightedRatioCarrier_measurable M j t hjt G hGm).comp measurable_fst).mul
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

lemma weighted_terminalFunctional_of_memLp_two
    {T nX nH k : Nat} {zeta : ℝ}
    (M : PomdpModel T nX nH k) (hK : FullFiltrationPomdp M)
    (hA : FullFiltrationRandomization M) (hY : RewardMomentEnvelope M)
    (hOverlap : PolicyOverlap zeta M) (j t : Fin T) (hjt : j.val ≤ t.val)
    (G : PreHistory T nX nH k j → ℝ) (hGm : Measurable G)
    (hG2 : MemLp (fun w => G (preHist j w)) 2 M.law)
    (R : ℝ × JointState nX nH → ℝ) (hRm : Measurable R)
    (hR : ∀ y, |R y| ≤ |y.1|) :
    ∫ w, weightedRatioCarrier M j t hjt G (preHist t w) *
          ratio M.b M.e (currentState w t).1 (actionAt w t) *
          R (rewardAt w t, nextState w t) ∂M.law =
      ∫ w, G (preHist j w) *
          ((targetStep M)^[t.val - j.val] (terminalFunctionalRegression M R))
            (currentState w j) ∂M.law := by
  calc
    _ = ∫ w, weightedRatioCarrier M j t hjt G (preHist t w) *
          terminalFunctionalRegression M R (currentState w t) ∂M.law :=
      weightedRatioCarrier_terminalFunctional_peeling M hK hA hOverlap
        j t hjt G hGm R
        (weighted_terminalFunctional_kernel_integrable_of_memLp_two
          M hK hA hY hOverlap j t hjt G hGm hG2 R hRm hR)
        (weighted_terminalFunctional_action_integrable_of_memLp_two
          M hA hOverlap j t hjt G hGm hG2 R)
    _ = _ := weightedRatioCarrier_iteration M hK hA hOverlap j G hGm
      (hG2.integrable one_le_two) t.val hjt t.isLt
      (terminalFunctionalRegression M R)

lemma targetIter_nonneg_le_one {T nX nH k depth : Nat} {t0 zeta : ℝ}
    (M : PomdpModel T nX nH k) (hM : HuWagerClass t0 zeta M)
    (F : JointState nX nH → ℝ) (hF : ∀ s, 0 ≤ F s ∧ F s ≤ 1)
    (s : JointState nX nH) :
    0 ≤ ((targetStep M)^[depth] F) s ∧ ((targetStep M)^[depth] F) s ≤ 1 := by
  induction depth generalizing s with
  | zero => simpa using hF s
  | succ depth ih =>
      rw [Function.iterate_succ_apply']
      exact ⟨targetStep_nonneg M hM.pomdp hM.overlap _ (fun x => (ih x).1) s,
        targetStep_le_const M hM.pomdp hM.overlap _ 1 (fun x => (ih x).2) s⟩

lemma weightedRatioCarrier_terminal_preHist {T nX nH k : Nat}
    (M : PomdpModel T nX nH k) (j t : Fin T) (hjt : j.val ≤ t.val)
    (G : PreHistory T nX nH k j → ℝ) (w : FullPath T nX nH k) :
    weightedRatioCarrier M j t hjt G (preHist t w) *
        ratio M.b M.e (currentState w t).1 (actionAt w t) =
      G (preHist j w) *
        ∏ q ∈ Finset.univ.filter
          (fun q : Fin T => j.val ≤ q.val ∧ q.val ≤ t.val),
          ratio M.b M.e (currentState w q).1 (actionAt w q) := by
  rw [weightedRatioCarrier_preHist]
  have hp : (∏ q : Fin t.val, if j.val ≤ q.val then
      ratio M.b M.e (currentState w (pastIndex t q)).1
        (actionAt w (pastIndex t q)) else 1) =
      ∏ q ∈ Finset.univ.filter
        (fun q : Fin T => j.val ≤ q.val ∧ q.val < t.val),
        ratio M.b M.e (currentState w q).1 (actionAt w q) := by
    rw [← Finset.prod_filter]
    apply Finset.prod_bij (fun q _ => (⟨q.val, lt_trans q.isLt t.isLt⟩ : Fin T))
    · intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      exact ⟨hq, q.isLt⟩
    · intro q _ q' _ he
      apply Fin.ext
      simpa using congrArg Fin.val he
    · intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
      exact ⟨⟨q.val, hq.2⟩, by simpa using hq.1, Fin.ext rfl⟩
    · intro q _
      rfl
  rw [hp]
  have hsets : insert t (Finset.univ.filter
      (fun q : Fin T => j.val ≤ q.val ∧ q.val < t.val)) =
      Finset.univ.filter (fun q : Fin T => j.val ≤ q.val ∧ q.val ≤ t.val) := by
    ext q
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (rfl | h)
      · exact ⟨hjt, le_rfl⟩
      · exact ⟨h.1, Nat.le_of_lt h.2⟩
    · intro h
      by_cases hqt : q = t
      · exact Or.inl hqt
      · exact Or.inr ⟨h.1,
          lt_of_le_of_ne h.2 (fun hv => hqt (Fin.ext hv))⟩
  rw [← hsets, Finset.prod_insert (by simp)]
  ring

lemma interval_filter_union_succ {T : Nat} (a t u j : Fin T)
    (hj : j.val = t.val + 1) (hat : a.val ≤ t.val) (htu : t.val < u.val) :
    Finset.univ.filter (fun q : Fin T => a.val ≤ q.val ∧ q.val ≤ t.val) ∪
      Finset.univ.filter (fun q : Fin T => j.val ≤ q.val ∧ q.val ≤ u.val) =
    Finset.univ.filter (fun q : Fin T => a.val ≤ q.val ∧ q.val ≤ u.val) := by
  ext q
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  omega

lemma interval_filter_disjoint_succ {T : Nat} (a t u j : Fin T)
    (hj : j.val = t.val + 1) :
    Disjoint
      (Finset.univ.filter (fun q : Fin T => a.val ≤ q.val ∧ q.val ≤ t.val))
      (Finset.univ.filter (fun q : Fin T => j.val ≤ q.val ∧ q.val ≤ u.val)) := by
  rw [Finset.disjoint_left]
  intro q hq ht
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ht
  omega

/-- A single-copy likelihood product over a contiguous interval, with two
rewards at distinct epochs, has expectation at most one. -/
lemma integral_intervalRatio_twoRewards_le_one
    {T nX nH k : Nat} {t0 zeta : ℝ}
    (M : PomdpModel T nX nH k) (hM : HuWagerClass t0 zeta M)
    (a t u : Fin T) (hat : a.val ≤ t.val) (htu : t.val < u.val) :
    ∫ w, (∏ q ∈ Finset.univ.filter
          (fun q : Fin T => a.val ≤ q.val ∧ q.val ≤ u.val),
          ratio M.b M.e (currentState w q).1 (actionAt w q)) *
          |rewardAt w t * rewardAt w u| ∂M.law ≤ 1 := by
  let j : Fin T := ⟨t.val + 1, by omega⟩
  have htj : t.val < j.val := by simp [j]
  have hju : j.val ≤ u.val := by dsimp [j]; omega
  let G : PreHistory T nX nH k j → ℝ := fun h =>
    |pastWindowScore M a t j htj h|
  have hGm : Measurable G := by
    exact continuous_abs.measurable.comp (pastWindowScore_measurable M a t j htj)
  have hG2 : MemLp (fun w => G (preHist j w)) 2 M.law := by
    have hh := pastWindowScore_preHist_memLp_two M hM.pomdp hM.randomization
      hM.moment hM.overlap a t j hat htj
    exact hh.abs
  let F : JointState nX nH → ℝ :=
    ((targetStep M)^[u.val - j.val] (absRewardRegression M))
  have hF (s : JointState nX nH) : 0 ≤ F s ∧ F s ≤ 1 := by
    exact targetIter_absReward_nonneg_le_one M hM s
  let Rlater : ℝ × JointState nX nH → ℝ := fun y => |y.1|
  have hlater := weighted_terminalFunctional_of_memLp_two M hM.pomdp
    hM.randomization hM.moment hM.overlap j u hju G hGm hG2 Rlater
    (by fun_prop) (fun y => by simp [Rlater])
  have hterminalLater : terminalFunctionalRegression M Rlater =
      absRewardRegression M := by
    funext s
    simp [terminalFunctionalRegression, absRewardRegression, Rlater]
  have hlater' :
      (∫ w, weightedRatioCarrier M j u hju G (preHist u w) *
          ratio M.b M.e (currentState w u).1 (actionAt w u) *
          |rewardAt w u| ∂M.law) =
        ∫ w, G (preHist j w) * F (currentState w j) ∂M.law := by
    rw [hterminalLater] at hlater
    simpa [Rlater, F] using hlater
  let Gone : PreHistory T nX nH k a → ℝ := fun _ => 1
  let Rearly : ℝ × JointState nX nH → ℝ := fun y => |y.1| * F y.2
  have hRearlym : Measurable Rearly := by
    exact continuous_abs.measurable.comp measurable_fst |>.mul
      ((measurable_of_finite F).comp measurable_snd)
  have hRearly (y : ℝ × JointState nX nH) : |Rearly y| ≤ |y.1| := by
    rw [abs_mul, abs_abs, abs_of_nonneg (hF y.2).1]
    exact mul_le_of_le_one_right (abs_nonneg y.1) (hF y.2).2
  have hearly := weighted_terminalFunctional_of_memLp_two M hM.pomdp
    hM.randomization hM.moment hM.overlap a t hat Gone (by fun_prop)
    (memLp_const (1 : ℝ)) Rearly hRearlym hRearly
  have hterminalEarly : terminalFunctionalRegression M Rearly =
      twoRewardBridge M F := by
    funext s
    simp [terminalFunctionalRegression, twoRewardBridge, Rearly]
  rw [hterminalEarly] at hearly
  have hearly' :
      (∫ w, (∏ q ∈ Finset.univ.filter
            (fun q : Fin T => a.val ≤ q.val ∧ q.val ≤ t.val),
            ratio M.b M.e (currentState w q).1 (actionAt w q)) *
          (|rewardAt w t| * F (nextState w t)) ∂M.law) =
        ∫ w, ((targetStep M)^[t.val - a.val]
          (twoRewardBridge M F)) (currentState w a) ∂M.law := by
    calc
      _ = ∫ w, weightedRatioCarrier M a t hat Gone (preHist t w) *
          ratio M.b M.e (currentState w t).1 (actionAt w t) *
          Rearly (rewardAt w t, nextState w t) ∂M.law := by
        apply integral_congr_ae
        filter_upwards with w
        rw [weightedRatioCarrier_terminal_preHist]
        simp [Gone, Rearly]
      _ = _ := by simpa [Gone] using hearly
  calc
    _ = ∫ w, weightedRatioCarrier M j u hju G (preHist u w) *
          ratio M.b M.e (currentState w u).1 (actionAt w u) *
          |rewardAt w u| ∂M.law := by
      apply integral_congr_ae
      filter_upwards with w
      rw [weightedRatioCarrier_terminal_preHist]
      change _ = (|pastWindowScore M a t j htj (preHist j w)| * _) * _
      rw [
        pastWindowScore_preHist M a t j hat htj]
      unfold windowScore
      simp only [abs_mul]
      rw [abs_of_nonneg (Finset.prod_nonneg fun q _ =>
        (policy_ratio_bounds M hM.overlap hM.randomization.1 _ _).1)]
      have hs := interval_filter_union_succ a t u j (by simp [j]) hat htu
      have hd := interval_filter_disjoint_succ a t u j (by simp [j])
      rw [← hs, Finset.prod_union hd]
      ring
    _ = ∫ w, G (preHist j w) * F (currentState w j) ∂M.law := hlater'
    _ = ∫ w, (∏ q ∈ Finset.univ.filter
            (fun q : Fin T => a.val ≤ q.val ∧ q.val ≤ t.val),
            ratio M.b M.e (currentState w q).1 (actionAt w q)) *
          (|rewardAt w t| * F (nextState w t)) ∂M.law := by
      apply integral_congr_ae
      filter_upwards with w
      change |pastWindowScore M a t j htj (preHist j w)| * F (currentState w j) = _
      rw [pastWindowScore_preHist M a t j hat htj]
      unfold windowScore nextState currentState
      rw [abs_mul, abs_of_nonneg (Finset.prod_nonneg fun q _ =>
        (policy_ratio_bounds M hM.overlap hM.randomization.1 _ _).1)]
      have hjstate : w.1 j.castSucc = w.1 t.succ := by
        congr 2
      rw [hjstate]
      ring
    _ = ∫ w, ((targetStep M)^[t.val - a.val]
          (twoRewardBridge M F)) (currentState w a) ∂M.law := hearly'
    _ ≤ ∫ _w : FullPath T nX nH k, 1 ∂M.law := by
      apply integral_mono
      · apply Integrable.of_bound
          ((measurable_of_finite ((targetStep M)^[t.val - a.val]
            (twoRewardBridge M F))).comp
              (show Measurable (fun w : FullPath T nX nH k => w.1 a.castSucc) by
                fun_prop)).aestronglyMeasurable 1
        filter_upwards with w
        change |((targetStep M)^[t.val - a.val] (twoRewardBridge M F))
          (currentState w a)| ≤ 1
        rw [abs_of_nonneg (targetIter_nonneg_le_one M hM
          (twoRewardBridge M F) (fun s => twoRewardBridge_nonneg_le_one M hM F hF s)
          (currentState w a)).1]
        exact (targetIter_nonneg_le_one M hM (twoRewardBridge M F)
          (fun s => twoRewardBridge_nonneg_le_one M hM F hF s)
          (currentState w a)).2
      · exact integrable_const 1
      · intro w
        exact (targetIter_nonneg_le_one M hM (twoRewardBridge M F)
          (fun s => twoRewardBridge_nonneg_le_one M hM F hF s)
          (currentState w a)).2
    _ = 1 := by simp

lemma prod_mul_prod_eq_union_mul_inter {ι : Type*} [DecidableEq ι]
    (f : ι → ℝ) (A B : Finset ι) :
    (∏ i ∈ A, f i) * (∏ i ∈ B, f i) =
      (∏ i ∈ A ∪ B, f i) * (∏ i ∈ A ∩ B, f i) := by
  simpa using (Finset.prod_union_inter (s₁ := A) (s₂ := B) (f := f)).symm

/-- Pointwise overlap reduction: one copy of every ratio belongs to the union
carrier, while the duplicate copy on the intersection is bounded by `L`. -/
lemma abs_windowScore_mul_le_unionProduct {T nX nH k : Nat} {zeta : ℝ}
    (M : PomdpModel T nX nH k) (hA : FullFiltrationRandomization M)
    (hOverlap : PolicyOverlap zeta M) (a t m u : Fin T)
    (w : FullPath T nX nH k) :
    let A := Finset.univ.filter (fun q : Fin T => a.val ≤ q.val ∧ q.val ≤ t.val)
    let B := Finset.univ.filter (fun q : Fin T => m.val ≤ q.val ∧ q.val ≤ u.val)
    |windowScore M a t w * windowScore M m u w| ≤
      policyFactor zeta ^ (A ∩ B).card *
        ((∏ q ∈ A ∪ B, ratio M.b M.e (currentState w q).1 (actionAt w q)) *
          |rewardAt w t * rewardAt w u|) := by
  dsimp only
  let A := Finset.univ.filter (fun q : Fin T => a.val ≤ q.val ∧ q.val ≤ t.val)
  let B := Finset.univ.filter (fun q : Fin T => m.val ≤ q.val ∧ q.val ≤ u.val)
  let R : Fin T → ℝ := fun q => ratio M.b M.e (currentState w q).1 (actionAt w q)
  have hR0 (q : Fin T) : 0 ≤ R q := (policy_ratio_bounds M hOverlap hA.1 _ _).1
  have hRL (q : Fin T) : R q ≤ policyFactor zeta :=
    (policy_ratio_bounds M hOverlap hA.1 _ _).2
  have hI : (∏ q ∈ A ∩ B, R q) ≤ policyFactor zeta ^ (A ∩ B).card := by
    calc
      _ ≤ ∏ _q ∈ A ∩ B, policyFactor zeta :=
        Finset.prod_le_prod (fun q _ => hR0 q) (fun q _ => hRL q)
      _ = _ := by simp
  have hU0 : 0 ≤ ∏ q ∈ A ∪ B, R q := Finset.prod_nonneg fun q _ => hR0 q
  unfold windowScore
  change |rewardAt w t * (∏ q ∈ A, R q) *
    (rewardAt w u * ∏ q ∈ B, R q)| ≤ _
  rw [abs_mul, abs_mul, abs_mul,
    abs_of_nonneg (Finset.prod_nonneg fun q _ => hR0 q),
    abs_of_nonneg (Finset.prod_nonneg fun q _ => hR0 q)]
  calc
    _ = ((∏ q ∈ A, R q) * ∏ q ∈ B, R q) *
        |rewardAt w t * rewardAt w u| := by
      rw [abs_mul]
      ring
    _ = ((∏ q ∈ A ∪ B, R q) * ∏ q ∈ A ∩ B, R q) *
        |rewardAt w t * rewardAt w u| := by
      rw [prod_mul_prod_eq_union_mul_inter]
    _ ≤ ((∏ q ∈ A ∪ B, R q) * policyFactor zeta ^ (A ∩ B).card) *
        |rewardAt w t * rewardAt w u| := by
      gcongr
    _ = _ := by ring

lemma overlap_interval_union {T depth lag : Nat} (t u : Fin T)
    (hdepth : depth ≤ t.val) (hu : u.val = t.val + lag)
    (hlag : lag ≤ depth) :
    let a : Fin T := ⟨t.val - depth, by omega⟩
    let m : Fin T := ⟨u.val - depth, by omega⟩
    Finset.univ.filter (fun q : Fin T => a.val ≤ q.val ∧ q.val ≤ t.val) ∪
      Finset.univ.filter (fun q : Fin T => m.val ≤ q.val ∧ q.val ≤ u.val) =
      Finset.univ.filter (fun q : Fin T => a.val ≤ q.val ∧ q.val ≤ u.val) := by
  dsimp only
  ext q
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · omega
  · intro hq
    by_cases hqt : q.val ≤ t.val
    · left; omega
    · right; omega

lemma overlap_interval_inter_card_le {T depth lag : Nat} (t u : Fin T)
    (hdepth : depth ≤ t.val) (hu : u.val = t.val + lag)
    (hlag : lag ≤ depth) :
    let a : Fin T := ⟨t.val - depth, by omega⟩
    let m : Fin T := ⟨u.val - depth, by omega⟩
    (Finset.univ.filter (fun q : Fin T => a.val ≤ q.val ∧ q.val ≤ t.val) ∩
      Finset.univ.filter (fun q : Fin T => m.val ≤ q.val ∧ q.val ≤ u.val)).card ≤
      depth + 1 - lag := by
  dsimp only
  let f : Fin T → Nat := fun q => t.val - q.val
  have hsub : u.val - depth = (t.val - depth) + lag := by omega
  calc
    _ ≤ (Finset.range (depth + 1 - lag)).card := by
      apply Finset.card_le_card_of_injOn f
      · intro q hq
        change q ∈ (Finset.univ.filter
          (fun q : Fin T => t.val - depth ≤ q.val ∧ q.val ≤ t.val) ∩
          Finset.univ.filter
          (fun q : Fin T => u.val - depth ≤ q.val ∧ q.val ≤ u.val)) at hq
        rw [Finset.mem_inter] at hq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
        rw [hsub] at hq
        apply Finset.mem_range.mpr
        dsimp [f]
        omega
      · intro i hi q hq heq
        change i ∈ (Finset.univ.filter
          (fun q : Fin T => t.val - depth ≤ q.val ∧ q.val ≤ t.val) ∩
          Finset.univ.filter
          (fun q : Fin T => u.val - depth ≤ q.val ∧ q.val ≤ u.val)) at hi
        change q ∈ (Finset.univ.filter
          (fun q : Fin T => t.val - depth ≤ q.val ∧ q.val ≤ t.val) ∩
          Finset.univ.filter
          (fun q : Fin T => u.val - depth ≤ q.val ∧ q.val ≤ u.val)) at hq
        rw [Finset.mem_inter] at hi hq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hq
        dsimp [f] at heq
        apply Fin.ext
        omega
    _ = _ := Finset.card_range _

lemma intervalRatio_twoRewards_integrable
    {T nX nH k : Nat} {zeta : ℝ}
    (M : PomdpModel T nX nH k) (hK : FullFiltrationPomdp M)
    (hA : FullFiltrationRandomization M) (hY : RewardMomentEnvelope M)
    (hOverlap : PolicyOverlap zeta M) (a t u : Fin T) :
    Integrable (fun w => (∏ q ∈ Finset.univ.filter
        (fun q : Fin T => a.val ≤ q.val ∧ q.val ≤ u.val),
        ratio M.b M.e (currentState w q).1 (actionAt w q)) *
        |rewardAt w t * rewardAt w u|) M.law := by
  have hrt := reward_sq_integrable_and_integral_le_one M hK hY t
  have hru := reward_sq_integrable_and_integral_le_one M hK hY u
  have hmt : AEStronglyMeasurable (fun w : FullPath T nX nH k => rewardAt w t)
      M.law := (by unfold rewardAt; fun_prop : Measurable _).aestronglyMeasurable
  have hmu : AEStronglyMeasurable (fun w : FullPath T nX nH k => rewardAt w u)
      M.law := (by unfold rewardAt; fun_prop : Measurable _).aestronglyMeasurable
  have ht2 := (memLp_two_iff_integrable_sq hmt).2 hrt.1
  have hu2 := (memLp_two_iff_integrable_sq hmu).2 hru.1
  have hprod : Integrable (fun w : FullPath T nX nH k =>
      |rewardAt w t * rewardAt w u|) M.law := (ht2.integrable_mul hu2).abs
  let D := max 1 (policyFactor zeta) ^ T
  have hm : Measurable (fun w : FullPath T nX nH k =>
      (∏ q ∈ Finset.univ.filter
        (fun q : Fin T => a.val ≤ q.val ∧ q.val ≤ u.val),
        ratio M.b M.e (currentState w q).1 (actionAt w q)) *
        |rewardAt w t * rewardAt w u|) := by
    apply Measurable.mul
    · apply Finset.measurable_prod
      intro q _
      exact (measurable_of_countable fun xa : Fin nX × Fin k =>
        ratio M.b M.e xa.1 xa.2).comp
          (show Measurable (fun w : FullPath T nX nH k =>
            ((w.1 q.castSucc).1, (w.2 q).1)) by fun_prop)
    · exact continuous_abs.measurable.comp
        ((show Measurable (fun w : FullPath T nX nH k => (w.2 t).2) by
          fun_prop).mul
        (show Measurable (fun w : FullPath T nX nH k => (w.2 u).2) by
          fun_prop))
  apply (hprod.const_mul D).mono' hm.aestronglyMeasurable
  filter_upwards with w
  simp only [norm_mul, Real.norm_eq_abs, abs_abs]
  rw [abs_of_nonneg
    (Finset.prod_nonneg fun q _ =>
      (policy_ratio_bounds M hOverlap hA.1 _ _).1)]
  have hp : (∏ q ∈ Finset.univ.filter
      (fun q : Fin T => a.val ≤ q.val ∧ q.val ≤ u.val),
      ratio M.b M.e (currentState w q).1 (actionAt w q)) ≤ D := by
    calc
      _ ≤ ∏ _q ∈ Finset.univ.filter
          (fun q : Fin T => a.val ≤ q.val ∧ q.val ≤ u.val),
          max 1 (policyFactor zeta) := by
        apply Finset.prod_le_prod
        · intro q _
          exact (policy_ratio_bounds M hOverlap hA.1 _ _).1
        · intro q _
          exact (policy_ratio_bounds M hOverlap hA.1 _ _).2.trans
            (le_max_right _ _)
      _ = max 1 (policyFactor zeta) ^
          (Finset.univ.filter
            (fun q : Fin T => a.val ≤ q.val ∧ q.val ≤ u.val)).card := by simp
      _ ≤ D := by
        apply pow_le_pow_right₀ (le_max_left _ _)
        have hc := Finset.card_le_card (Finset.filter_subset
          (fun q : Fin T => a.val ≤ q.val ∧ q.val ≤ u.val) Finset.univ)
        simpa using hc
  exact mul_le_mul_of_nonneg_right hp (abs_nonneg _)

lemma integral_abs_windowScore_le_one
    {T nX nH k : Nat} {t0 zeta : ℝ}
    (M : PomdpModel T nX nH k) (hM : HuWagerClass t0 zeta M)
    (a t : Fin T) (hat : a.val ≤ t.val) :
    ∫ w, |windowScore M a t w| ∂M.law ≤ 1 := by
  let Gone : PreHistory T nX nH k a → ℝ := fun _ => 1
  let R : ℝ × JointState nX nH → ℝ := fun y => |y.1|
  have he := weighted_terminalFunctional_of_memLp_two M hM.pomdp
    hM.randomization hM.moment hM.overlap a t hat Gone (by fun_prop)
    (memLp_const (1 : ℝ)) R (by fun_prop) (fun y => by simp [R])
  have hterm : terminalFunctionalRegression M R = absRewardRegression M := by
    funext s
    simp [terminalFunctionalRegression, absRewardRegression, R]
  rw [hterm] at he
  calc
    _ = ∫ w, Gone (preHist a w) *
        ((targetStep M)^[t.val - a.val] (absRewardRegression M))
          (currentState w a) ∂M.law := by
      rw [← he]
      apply integral_congr_ae
      filter_upwards with w
      rw [weightedRatioCarrier_terminal_preHist]
      unfold windowScore
      simp only [Gone, one_mul, R, abs_mul]
      rw [abs_of_nonneg (Finset.prod_nonneg fun q _ =>
        (policy_ratio_bounds M hM.overlap hM.randomization.1 _ _).1)]
      ring
    _ ≤ ∫ _w : FullPath T nX nH k, 1 ∂M.law := by
      apply integral_mono
      · apply Integrable.of_bound
          (((measurable_of_finite ((targetStep M)^[t.val - a.val]
            (absRewardRegression M))).comp
              (show Measurable (fun w : FullPath T nX nH k => w.1 a.castSucc) by
                fun_prop)).const_mul 1).aestronglyMeasurable 1
        filter_upwards with w
        simp only [Gone, one_mul, Function.comp_apply, Real.norm_eq_abs]
        change |((targetStep M)^[t.val - a.val] (absRewardRegression M))
          (currentState w a)| ≤ 1
        rw [abs_of_nonneg (targetIter_absReward_nonneg_le_one M hM _).1]
        exact (targetIter_absReward_nonneg_le_one M hM _).2
      · exact integrable_const 1
      · intro w
        simp only [Gone, one_mul]
        exact (targetIter_absReward_nonneg_le_one M hM _).2
    _ = 1 := by simp

lemma abs_integral_windowScore_mul_centered_behavior_le_one
    {T nX nH k gap : Nat} {t0 zeta : ℝ}
    (M : PomdpModel T nX nH k) (hM : HuWagerClass t0 zeta M)
    (hnX : 1 ≤ nX) (hnH : 1 ≤ nH) (a t : Fin T) (hat : a.val ≤ t.val)
    (ht : t.val + 1 + gap < T) (B : ℝ) (hB : 0 ≤ B)
    (F : JointState nX nH → ℝ) (hF : OscillationBound B F) :
    |∫ w, windowScore M a t w *
      (((behaviorStep M)^[gap] F) (currentState w ⟨t.val + 1, by omega⟩) -
        ∑ s, stationaryLaw (policyKernel M M.b) s * F s) ∂M.law| ≤
      mixingAlpha t0 ^ gap * B := by
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
    apply (memLp_congr_ae ?_).2 hX2 |>.integrable one_le_two
    filter_upwards with w
    exact (pastWindowScore_preHist M a t r hat (by dsimp [r]; omega) w).symm
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
          (by filter_upwards with w; exact hcenter w) |>.abs
      · exact hX.abs.const_mul C
      · intro w
        dsimp only
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hcenter w) (abs_nonneg _)
          |>.trans_eq (by ring)
    _ = C * ∫ w, |windowScore M a t w| ∂M.law := by rw [integral_const_mul]
    _ ≤ C := by
      simpa using mul_le_mul_of_nonneg_left
        (integral_abs_windowScore_le_one M hM a t hat) hC
    _ = _ := rfl

lemma abs_windowScore_cross_sub_means_le_disjoint_one
    {T nX nH k depth lag : Nat} {t0 zeta : ℝ}
    (M : PomdpModel T nX nH k) (hM : HuWagerClass t0 zeta M)
    (hnX : 1 ≤ nX) (hnH : 1 ≤ nH) (t u : Fin T)
    (hdepth : depth ≤ t.val) (hu : u.val = t.val + lag)
    (hdisjoint : depth + 1 ≤ lag) :
    |(∫ w, windowScore M ⟨t.val - depth, by omega⟩ t w *
          windowScore M ⟨u.val - depth, by omega⟩ u w ∂M.law) -
      (∫ w, windowScore M ⟨t.val - depth, by omega⟩ t w ∂M.law) *
      (∫ w, windowScore M ⟨u.val - depth, by omega⟩ u w ∂M.law)| ≤
      mixingAlpha t0 ^ (lag - depth - 1) * 2 := by
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
    abs_integral_windowScore_mul_centered_behavior_le_one M hM hnX hnH a t hat
      (gap := gap) (by omega) 2 (by norm_num) F
      (targetIter_reward_oscillation_two M hM)

lemma abs_covariance_windowScore_le_disjoint_one
    {T nX nH k depth lag : Nat} {t0 zeta : ℝ}
    (M : PomdpModel T nX nH k) (hM : HuWagerClass t0 zeta M)
    (hnX : 1 ≤ nX) (hnH : 1 ≤ nH) (t u : Fin T)
    (hdepth : depth ≤ t.val) (hu : u.val = t.val + lag)
    (hdisjoint : depth + 1 ≤ lag) :
    |covariance
      (fun w => windowScore M ⟨t.val - depth, by omega⟩ t w)
      (fun w => windowScore M ⟨u.val - depth, by omega⟩ u w) M.law| ≤
      mixingAlpha t0 ^ (lag - depth - 1) * 2 := by
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
  exact abs_windowScore_cross_sub_means_le_disjoint_one M hM hnX hnH t u
    hdepth hu hdisjoint


lemma integral_abs_windowScore_mul_le_overlap
    {T nX nH k depth lag : Nat} {t0 zeta : ℝ}
    (M : PomdpModel T nX nH k) (hM : HuWagerClass t0 zeta M)
    (t u : Fin T) (hdepth : depth ≤ t.val) (hu : u.val = t.val + lag)
    (hlag0 : 1 ≤ lag) (hlag : lag ≤ depth) :
    ∫ w, |windowScore M ⟨t.val - depth, by omega⟩ t w *
      windowScore M ⟨u.val - depth, by omega⟩ u w| ∂M.law ≤
      policyFactor zeta ^ (depth + 1 - lag) := by
  let a : Fin T := ⟨t.val - depth, by omega⟩
  let m : Fin T := ⟨u.val - depth, by omega⟩
  let U := Finset.univ.filter
    (fun q : Fin T => a.val ≤ q.val ∧ q.val ≤ u.val)
  let Z : FullPath T nX nH k → ℝ := fun w =>
    (∏ q ∈ U, ratio M.b M.e (currentState w q).1 (actionAt w q)) *
      |rewardAt w t * rewardAt w u|
  have hcross : Integrable (fun w => |windowScore M a t w *
      windowScore M m u w|) M.law := by
    have ht := pastWindowScore_preHist_memLp_two M hM.pomdp hM.randomization
      hM.moment hM.overlap a t ⟨t.val + 1, by omega⟩ (by dsimp [a]; omega) (by simp)
    have hu2 := observed_phiwScore_memLp_two M hM.pomdp hM.randomization
      hM.moment hM.overlap u (by omega : depth ≤ u.val)
    have ht' : MemLp (fun w => windowScore M a t w) 2 M.law := by
      apply (memLp_congr_ae ?_).2 ht
      filter_upwards with w
      exact (pastWindowScore_preHist M a t ⟨t.val + 1, by omega⟩
        (by dsimp [a]; omega) (by simp) w).symm
    have hu' : MemLp (fun w => windowScore M m u w) 2 M.law := by
      apply (memLp_congr_ae ?_).2 hu2
      filter_upwards with w
      simpa [m, Nat.sub_sub_self (by omega : depth ≤ u.val)] using
        (phiwScore_observedRecord_eq_windowScore M u
          (by omega : depth ≤ u.val) w).symm
    exact (ht'.integrable_mul hu').abs
  have hZ : Integrable Z M.law := by
    exact intervalRatio_twoRewards_integrable M hM.pomdp hM.randomization
      hM.moment hM.overlap a t u
  have hcard :
      (Finset.univ.filter (fun q : Fin T => a.val ≤ q.val ∧ q.val ≤ t.val) ∩
        Finset.univ.filter (fun q : Fin T => m.val ≤ q.val ∧ q.val ≤ u.val)).card ≤
        depth + 1 - lag := by
    simpa [a, m] using overlap_interval_inter_card_le t u hdepth hu hlag
  have hL : 1 ≤ policyFactor zeta := by
    unfold policyFactor
    exact Real.one_le_exp hM.zeta_pos.le
  calc
    _ ≤ ∫ w, policyFactor zeta ^ (depth + 1 - lag) * Z w ∂M.law := by
      apply integral_mono hcross (hZ.const_mul _)
      intro w
      have hp := abs_windowScore_mul_le_unionProduct M hM.randomization
        hM.overlap a t m u w
      have hU := overlap_interval_union t u hdepth hu hlag
      dsimp only at hU
      have hU' : Finset.univ.filter
          (fun q : Fin T => a.val ≤ q.val ∧ q.val ≤ t.val) ∪
          Finset.univ.filter (fun q : Fin T => m.val ≤ q.val ∧ q.val ≤ u.val) = U := by
        simpa [a, m, U] using hU
      dsimp only at hp
      rw [hU'] at hp
      change |windowScore M a t w * windowScore M m u w| ≤ _
      calc
        _ ≤ policyFactor zeta ^
            (Finset.univ.filter (fun q : Fin T => a.val ≤ q.val ∧ q.val ≤ t.val) ∩
              Finset.univ.filter (fun q : Fin T => m.val ≤ q.val ∧ q.val ≤ u.val)).card *
            Z w := by
          simpa [Z, U, abs_mul] using hp
        _ ≤ policyFactor zeta ^ (depth + 1 - lag) * Z w := by
          apply mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hL hcard)
          exact mul_nonneg (Finset.prod_nonneg fun q _ =>
            (policy_ratio_bounds M hM.overlap hM.randomization.1 _ _).1) (abs_nonneg _)
    _ = policyFactor zeta ^ (depth + 1 - lag) * ∫ w, Z w ∂M.law := by
      rw [integral_const_mul]
    _ ≤ policyFactor zeta ^ (depth + 1 - lag) * 1 := by
      apply mul_le_mul_of_nonneg_left
      · exact integral_intervalRatio_twoRewards_le_one M hM a t u
          (by dsimp [a]; omega) (by omega)
      · positivity
    _ = _ := mul_one _

lemma abs_covariance_windowScore_le_overlap
    {T nX nH k depth lag : Nat} {t0 zeta : ℝ}
    (M : PomdpModel T nX nH k) (hM : HuWagerClass t0 zeta M)
    (t u : Fin T) (hdepth : depth ≤ t.val) (hu : u.val = t.val + lag)
    (hlag0 : 1 ≤ lag) (hlag : lag ≤ depth) :
    |covariance
      (fun w => windowScore M ⟨t.val - depth, by omega⟩ t w)
      (fun w => windowScore M ⟨u.val - depth, by omega⟩ u w) M.law| ≤
      2 * policyFactor zeta ^ (depth + 1 - lag) := by
  let a : Fin T := ⟨t.val - depth, by omega⟩
  let m : Fin T := ⟨u.val - depth, by omega⟩
  let X : FullPath T nX nH k → ℝ := fun w => windowScore M a t w
  let Y : FullPath T nX nH k → ℝ := fun w => windowScore M m u w
  have hX : MemLp X 2 M.law := by
    have hh := pastWindowScore_preHist_memLp_two M hM.pomdp hM.randomization
      hM.moment hM.overlap a t ⟨t.val + 1, by omega⟩ (by dsimp [a]; omega) (by simp)
    apply (memLp_congr_ae ?_).2 hh
    filter_upwards with w
    exact (pastWindowScore_preHist M a t ⟨t.val + 1, by omega⟩
      (by dsimp [a]; omega) (by simp) w).symm
  have hdu : depth ≤ u.val := by omega
  have hY : MemLp Y 2 M.law := by
    have hh := observed_phiwScore_memLp_two M hM.pomdp hM.randomization
      hM.moment hM.overlap u hdu
    apply (memLp_congr_ae ?_).2 hh
    filter_upwards with w
    simpa [Y, m, Nat.sub_sub_self hdu] using
      (phiwScore_observedRecord_eq_windowScore M u hdu w).symm
  have hXone : ∫ w, |X w| ∂M.law ≤ 1 :=
    integral_abs_windowScore_le_one M hM a t (by dsimp [a]; omega)
  have hYone : ∫ w, |Y w| ∂M.law ≤ 1 :=
    integral_abs_windowScore_le_one M hM m u (by dsimp [m]; omega)
  have hcross : ∫ w, |X w * Y w| ∂M.law ≤
      policyFactor zeta ^ (depth + 1 - lag) := by
    simpa [X, Y, a, m] using integral_abs_windowScore_mul_le_overlap
      M hM t u hdepth hu hlag0 hlag
  have hB : 1 ≤ policyFactor zeta ^ (depth + 1 - lag) := by
    apply one_le_pow₀
    unfold policyFactor
    exact Real.one_le_exp hM.zeta_pos.le
  rw [covariance_eq_sub hX hY]
  calc
    |(∫ w, X w * Y w ∂M.law) - (∫ w, X w ∂M.law) * ∫ w, Y w ∂M.law| ≤
        |∫ w, X w * Y w ∂M.law| +
          |(∫ w, X w ∂M.law) * ∫ w, Y w ∂M.law| := abs_sub _ _
    _ ≤ (∫ w, |X w * Y w| ∂M.law) +
          (∫ w, |X w| ∂M.law) * ∫ w, |Y w| ∂M.law := by
      gcongr
      · exact abs_integral_le_integral_abs
      · rw [abs_mul]
        gcongr <;> exact abs_integral_le_integral_abs
    _ ≤ policyFactor zeta ^ (depth + 1 - lag) + 1 := by
      gcongr
      have hx0 : 0 ≤ ∫ w, |X w| ∂M.law := integral_nonneg fun _ => abs_nonneg _
      have hy0 : 0 ≤ ∫ w, |Y w| ∂M.law := integral_nonneg fun _ => abs_nonneg _
      nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hYone),
        mul_nonneg hy0 (sub_nonneg.mpr hXone)]
    _ ≤ 2 * policyFactor zeta ^ (depth + 1 - lag) := by linarith

end CausalSmith.Stat.PomdpStateauditMinimax
