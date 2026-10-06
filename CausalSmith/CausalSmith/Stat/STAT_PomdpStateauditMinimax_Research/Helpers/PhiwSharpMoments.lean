module
public import CausalSmith.Stat.STAT_PomdpStateauditMinimax_Research.Helpers.PhiwWeightedFuture

/-! # Sharp second-moment bounds for PHIW windows.

This file develops the squared likelihood-ratio change of measure needed to
keep one factor of the overlap envelope per action, rather than two factors
from a pointwise bound.
-/

@[expose] public section

namespace CausalSmith.Stat.PomdpStateauditMinimax

open MeasureTheory ProbabilityTheory

lemma behavior_mul_ratio_sq_eq_target_mul_ratio {T nX nH k : Nat} {zeta : ℝ}
    (M : PomdpModel T nX nH k) (hOverlap : PolicyOverlap zeta M)
    (x : Fin nX) (a : Fin k) :
    M.b x a * ratio M.b M.e x a ^ 2 =
      M.e x a * ratio M.b M.e x a := by
  by_cases hb : M.b x a = 0
  · have he : M.e x a = 0 := by
      apply le_antisymm
      · simpa [hb] using hOverlap.2 x a
      · exact (hOverlap.1 x).1 a
    simp [ratio, hb, he]
  · simp only [ratio, if_neg hb, pow_two]
    field_simp

/-- One behavior-weighted squared importance ratio costs only one overlap
factor after changing the action weight to the target policy. -/
lemma behavior_mul_ratio_sq_le {T nX nH k : Nat} {zeta : ℝ}
    (M : PomdpModel T nX nH k) (hA : FullFiltrationRandomization M)
    (hOverlap : PolicyOverlap zeta M) (x : Fin nX) (a : Fin k) :
    M.b x a * ratio M.b M.e x a ^ 2 ≤
      policyFactor zeta * M.e x a := by
  by_cases hb : M.b x a = 0
  · have he : M.e x a = 0 := by
      apply le_antisymm
      · simpa [hb] using hOverlap.2 x a
      · exact (hOverlap.1 x).1 a
    simp [ratio, hb, he]
  · have hbpos : 0 < M.b x a :=
      lt_of_le_of_ne ((hA.1 x).1 a) (Ne.symm hb)
    have he0 : 0 ≤ M.e x a := (hOverlap.1 x).1 a
    have hratio := (policy_ratio_bounds M hOverlap hA.1 x a).2
    calc
      M.b x a * ratio M.b M.e x a ^ 2 =
          M.e x a * ratio M.b M.e x a := by
            exact behavior_mul_ratio_sq_eq_target_mul_ratio M hOverlap x a
      _ ≤ M.e x a * policyFactor zeta :=
        mul_le_mul_of_nonneg_left hratio he0
      _ = policyFactor zeta * M.e x a := by ring

/-- Summing a nonnegative continuation over the behavior action law with a
squared ratio costs one overlap factor and changes the action law to target. -/
lemma sum_behavior_mul_ratio_sq_le {T nX nH k : Nat} {zeta : ℝ}
    (M : PomdpModel T nX nH k) (hA : FullFiltrationRandomization M)
    (hOverlap : PolicyOverlap zeta M) (x : Fin nX)
    (F : Fin k → ℝ) (hF : ∀ a, 0 ≤ F a) :
    (∑ a, M.b x a * ratio M.b M.e x a ^ 2 * F a) ≤
      policyFactor zeta * ∑ a, M.e x a * F a := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  simpa [mul_assoc] using mul_le_mul_of_nonneg_right
    (behavior_mul_ratio_sq_le M hA hOverlap x a) (hF a)

/-- The one-step operator obtained after squaring the action likelihood ratio. -/
noncomputable def squaredRatioStep {T nX nH k : Nat}
    (M : PomdpModel T nX nH k) (F : JointState nX nH → ℝ) :
    JointState nX nH → ℝ := fun s =>
  ∑ a : Fin k, M.b s.1 a * ratio M.b M.e s.1 a ^ 2 *
    ∫ y, F y.2 ∂(M.K s a)

/-- On nonnegative continuations, the squared-ratio operator is bounded by
one overlap factor times the target transition operator. -/
lemma squaredRatioStep_le_targetStep {T nX nH k : Nat} {zeta : ℝ}
    (M : PomdpModel T nX nH k) (hK : FullFiltrationPomdp M)
    (hA : FullFiltrationRandomization M) (hOverlap : PolicyOverlap zeta M)
    (F : JointState nX nH → ℝ) (hF : ∀ s, 0 ≤ F s) (x : JointState nX nH) :
    squaredRatioStep M F x ≤ policyFactor zeta * targetStep M F x := by
  have hint (a : Fin k) : 0 ≤ ∫ y, F y.2 ∂(M.K x a) := by
    exact integral_nonneg fun y => hF y.2
  calc
    squaredRatioStep M F x ≤ policyFactor zeta *
        ∑ a : Fin k, M.e x.1 a * ∫ y, F y.2 ∂(M.K x a) := by
      unfold squaredRatioStep
      exact sum_behavior_mul_ratio_sq_le M hA hOverlap x.1 _ hint
    _ = policyFactor zeta * targetStep M F x := by
      rw [targetStep_eq_action_integral M hK x F]

/-- Conditional squared terminal reward after applying the squared importance
ratio for the terminal action. -/
noncomputable def squaredRatioReward {T nX nH k : Nat}
    (M : PomdpModel T nX nH k) : JointState nX nH → ℝ := fun s =>
  ∑ a : Fin k, M.b s.1 a * ratio M.b M.e s.1 a ^ 2 *
    ∫ y, y.1 ^ 2 ∂(M.K s a)

/-- The terminal squared score has conditional expectation at most one overlap
factor. -/
lemma squaredRatioReward_le {T nX nH k : Nat} {zeta : ℝ}
    (M : PomdpModel T nX nH k) (hA : FullFiltrationRandomization M)
    (hY : RewardMomentEnvelope M) (hOverlap : PolicyOverlap zeta M)
    (x : JointState nX nH) :
    squaredRatioReward M x ≤ policyFactor zeta := by
  calc
    squaredRatioReward M x ≤ policyFactor zeta *
        ∑ a : Fin k, M.e x.1 a * ∫ y, y.1 ^ 2 ∂(M.K x a) := by
      unfold squaredRatioReward
      apply sum_behavior_mul_ratio_sq_le M hA hOverlap
      intro a
      exact integral_nonneg fun y => sq_nonneg y.1
    _ ≤ policyFactor zeta * ∑ a : Fin k, M.e x.1 a * 1 := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_left (hY x a).2.2.2 ((hOverlap.1 x.1).1 a)
    _ = policyFactor zeta := by
      simp [(hOverlap.1 x.1).2]

/-- The squared-ratio transition and terminal reward functions are
nonnegative. -/
lemma squaredRatioReward_nonneg {T nX nH k : Nat}
    (M : PomdpModel T nX nH k) (hA : FullFiltrationRandomization M)
    (x : JointState nX nH) : 0 ≤ squaredRatioReward M x := by
  unfold squaredRatioReward
  apply Finset.sum_nonneg
  intro a _
  exact mul_nonneg
    (mul_nonneg ((hA.1 x.1).1 a) (sq_nonneg _))
    (integral_nonneg fun y => sq_nonneg y.1)

lemma targetStep_nonneg {T nX nH k : Nat} {zeta : ℝ}
    (M : PomdpModel T nX nH k) (hK : FullFiltrationPomdp M)
    (hOverlap : PolicyOverlap zeta M) (F : JointState nX nH → ℝ)
    (hF : ∀ s, 0 ≤ F s) (x : JointState nX nH) :
    0 ≤ targetStep M F x := by
  unfold targetStep
  apply Finset.sum_nonneg
  intro s _
  exact mul_nonneg
    ((policyKernel_probabilityVector_fin M hK M.e hOverlap.1 x).1 s) (hF s)

lemma targetStep_le_const {T nX nH k : Nat} {zeta : ℝ}
    (M : PomdpModel T nX nH k) (hK : FullFiltrationPomdp M)
    (hOverlap : PolicyOverlap zeta M) (F : JointState nX nH → ℝ)
    (C : ℝ) (hF : ∀ s, F s ≤ C) (x : JointState nX nH) :
    targetStep M F x ≤ C := by
  have hp := policyKernel_probabilityVector_fin M hK M.e hOverlap.1 x
  calc
    targetStep M F x ≤ ∑ s, policyKernel M M.e x s * C := by
      unfold targetStep
      apply Finset.sum_le_sum
      intro s _
      exact mul_le_mul_of_nonneg_left (hF s) (hp.1 s)
    _ = C := by rw [← Finset.sum_mul, hp.2, one_mul]

lemma squaredRatioStep_nonneg {T nX nH k : Nat}
    (M : PomdpModel T nX nH k) (hA : FullFiltrationRandomization M)
    (F : JointState nX nH → ℝ) (hF : ∀ s, 0 ≤ F s)
    (x : JointState nX nH) : 0 ≤ squaredRatioStep M F x := by
  unfold squaredRatioStep
  apply Finset.sum_nonneg
  intro a _
  exact mul_nonneg
    (mul_nonneg ((hA.1 x.1).1 a) (sq_nonneg _))
    (integral_nonneg fun y => hF y.2)

lemma squaredRatioIter_reward_nonneg {T nX nH k : Nat}
    (M : PomdpModel T nX nH k) (hA : FullFiltrationRandomization M)
    (d : Nat) (x : JointState nX nH) :
    0 ≤ ((squaredRatioStep M)^[d] (squaredRatioReward M)) x := by
  induction d generalizing x with
  | zero => simpa using squaredRatioReward_nonneg M hA x
  | succ d ih =>
      rw [Function.iterate_succ_apply']
      exact squaredRatioStep_nonneg M hA _
        (fun s => ih s) x

/-- Iterating the squared likelihood-ratio transition for `d` preceding
actions and then the squared terminal reward costs at most `L^(d+1)`. -/
lemma squaredRatioIter_reward_le {T nX nH k : Nat} {zeta : ℝ}
    (M : PomdpModel T nX nH k) (hK : FullFiltrationPomdp M)
    (hA : FullFiltrationRandomization M) (hY : RewardMomentEnvelope M)
    (hOverlap : PolicyOverlap zeta M) (d : Nat) (x : JointState nX nH) :
    ((squaredRatioStep M)^[d] (squaredRatioReward M)) x ≤
      policyFactor zeta ^ (d + 1) := by
  induction d generalizing x with
  | zero => simpa using squaredRatioReward_le M hA hY hOverlap x
  | succ d ih =>
      rw [Function.iterate_succ_apply']
      calc
        squaredRatioStep M ((squaredRatioStep M)^[d] (squaredRatioReward M)) x ≤
            policyFactor zeta * targetStep M
              ((squaredRatioStep M)^[d] (squaredRatioReward M)) x := by
          apply squaredRatioStep_le_targetStep M hK hA hOverlap
          exact fun s => squaredRatioIter_reward_nonneg M hA d s
        _ ≤ policyFactor zeta * policyFactor zeta ^ (d + 1) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
          exact targetStep_le_const M hK hOverlap _ _
            (fun s => ih s) x
        _ = policyFactor zeta ^ (d + 1 + 1) := by ring

/-- Product of squared likelihood ratios from `j` up to but excluding `r`. -/
noncomputable def squaredRatioCarrier {T nX nH k : Nat}
    (M : PomdpModel T nX nH k) (j r : Fin T) (hjr : j.val ≤ r.val)
    (h : PreHistory T nX nH k r) : ℝ :=
  ∏ q : Fin r.val, if j.val ≤ q.val then
    ratio M.b M.e (h.1 q).1 (h.2.1 q).1 ^ 2 else 1

lemma squaredRatioCarrier_measurable {T nX nH k : Nat}
    (M : PomdpModel T nX nH k) (j r : Fin T) (hjr : j.val ≤ r.val) :
    Measurable (squaredRatioCarrier M j r hjr) := by
  unfold squaredRatioCarrier
  apply Finset.measurable_prod
  intro q _
  by_cases hq : j.val ≤ q.val
  · simp only [if_pos hq]
    exact ((measurable_of_countable fun xa : Fin nX × Fin k =>
      ratio M.b M.e xa.1 xa.2).comp
        (((by fun_prop : Measurable fun h : PreHistory T nX nH k r =>
          (h.1 q).1)).prodMk (by fun_prop))).pow_const 2
  · simp only [if_neg hq]
    fun_prop

lemma squaredRatioCarrier_self {T nX nH k : Nat}
    (M : PomdpModel T nX nH k) (j : Fin T)
    (h : PreHistory T nX nH k j) :
    squaredRatioCarrier M j j le_rfl h = 1 := by
  unfold squaredRatioCarrier
  have hq : ∀ q : Fin j.val, ¬j.val ≤ q.val := by intro q; omega
  simp [hq]

lemma squaredRatioCarrier_next {T nX nH k : Nat}
    (M : PomdpModel T nX nH k) (j r : Fin T) (hjr : j.val ≤ r.val)
    (hr : r.val + 1 < T)
    (q : PostHistory T nX nH k r × (ℝ × JointState nX nH)) :
    squaredRatioCarrier M j ⟨r.val + 1, hr⟩ (Nat.le_succ_of_le hjr)
        (nextPreHistory r hr q) =
      squaredRatioCarrier M j r hjr q.1.1 *
        ratio M.b M.e q.1.1.2.2.1 q.1.2 ^ 2 := by
  unfold squaredRatioCarrier
  rw [Fin.prod_univ_castSucc]
  simp only [nextPreHistory, Fin.snoc_castSucc, Fin.snoc_last]
  have hprod : (∏ x : Fin r.val, if j.val ≤ x.castSucc.val then
      ratio M.b M.e (q.1.1.1 x).1 (q.1.1.2.1 x).1 ^ 2 else 1) =
      ∏ x : Fin r.val, if j.val ≤ x.val then
        ratio M.b M.e (q.1.1.1 x).1 (q.1.1.2.1 x).1 ^ 2 else 1 := by
    apply Finset.prod_congr rfl
    intro x _
    rfl
  rw [hprod, if_pos (by simpa using hjr)]

lemma squaredRatioCarrier_norm_bound {T nX nH k : Nat} {zeta : ℝ}
    (M : PomdpModel T nX nH k) (hA : FullFiltrationRandomization M)
    (hOverlap : PolicyOverlap zeta M) (j r : Fin T) (hjr : j.val ≤ r.val)
    (h : PreHistory T nX nH k r) :
    ‖squaredRatioCarrier M j r hjr h‖ ≤
      max 1 (policyFactor zeta ^ 2) ^ r.val := by
  unfold squaredRatioCarrier
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg fun q _ => by
    split_ifs
    · exact sq_nonneg _
    · exact zero_le_one)]
  calc
    (∏ q : Fin r.val, if j.val ≤ q.val then
        ratio M.b M.e (h.1 q).1 (h.2.1 q).1 ^ 2 else 1) ≤
        ∏ _q : Fin r.val, max 1 (policyFactor zeta ^ 2) := by
      apply Finset.prod_le_prod
      · intro q _
        split_ifs
        · exact sq_nonneg _
        · exact zero_le_one
      · intro q _
        split_ifs
        · exact (pow_le_pow_left₀ (policy_ratio_bounds M hOverlap hA.1 _ _).1
            (policy_ratio_bounds M hOverlap hA.1 _ _).2 2).trans (le_max_right _ _)
        · exact le_max_left _ _
    _ = _ := by simp

lemma squaredRatioCarrier_kernel_integrable {T nX nH k : Nat} {zeta : ℝ}
    (M : PomdpModel T nX nH k) (hA : FullFiltrationRandomization M)
    (hOverlap : PolicyOverlap zeta M) (j r : Fin T) (hjr : j.val ≤ r.val)
    (F : JointState nX nH → ℝ) :
    Integrable
      (fun z : PostHistory T nX nH k r × (ℝ × JointState nX nH) =>
        squaredRatioCarrier M j r hjr z.1.1 *
          ratio M.b M.e z.1.1.2.2.1 z.1.2 ^ 2 * F z.2.2)
      (M.law.map (fun w => (postHist r w, (rewardAt w r, nextState w r)))) := by
  obtain ⟨C, hC⟩ := Finite.exists_le (fun s : JointState nX nH => ‖F s‖)
  let D := max 1 (policyFactor zeta ^ 2) ^ r.val * policyFactor zeta ^ 2 * C
  have hm : Measurable
      (fun z : PostHistory T nX nH k r × (ℝ × JointState nX nH) =>
        squaredRatioCarrier M j r hjr z.1.1 *
          ratio M.b M.e z.1.1.2.2.1 z.1.2 ^ 2 * F z.2.2) := by
    exact (((squaredRatioCarrier_measurable M j r hjr).comp
      (show Measurable (fun z : PostHistory T nX nH k r ×
        (ℝ × JointState nX nH) => z.1.1) by fun_prop)).mul
      (((measurable_of_countable fun xa : Fin nX × Fin k =>
        ratio M.b M.e xa.1 xa.2).comp
          (show Measurable (fun z : PostHistory T nX nH k r ×
            (ℝ × JointState nX nH) => (z.1.1.2.2.1, z.1.2)) by fun_prop)).pow_const 2)).mul
          ((measurable_of_finite F).comp
            (show Measurable (fun z : PostHistory T nX nH k r ×
              (ℝ × JointState nX nH) => z.2.2) by fun_prop))
  apply Integrable.of_bound hm.aestronglyMeasurable D
  filter_upwards with z
  simp only [norm_mul, norm_pow]
  have hr : ‖ratio M.b M.e z.1.1.2.2.1 z.1.2‖ ≤ policyFactor zeta := by
    rw [Real.norm_eq_abs, abs_of_nonneg (policy_ratio_bounds M hOverlap hA.1 _ _).1]
    exact (policy_ratio_bounds M hOverlap hA.1 _ _).2
  exact mul_le_mul
    (mul_le_mul (squaredRatioCarrier_norm_bound M hA hOverlap j r hjr z.1.1)
      (pow_le_pow_left₀ (norm_nonneg _) hr 2)
      (sq_nonneg _) (pow_nonneg (by positivity) _))
    (hC z.2.2) (norm_nonneg _) (mul_nonneg (pow_nonneg (by positivity) _)
      (sq_nonneg _))

lemma squaredRatioCarrier_action_integrable {T nX nH k : Nat} {zeta : ℝ}
    (M : PomdpModel T nX nH k) (hA : FullFiltrationRandomization M)
    (hOverlap : PolicyOverlap zeta M) (j r : Fin T) (hjr : j.val ≤ r.val)
    (F : JointState nX nH → ℝ) :
    Integrable
      (fun z : PreHistory T nX nH k r × Fin k =>
        squaredRatioCarrier M j r hjr z.1 *
          ratio M.b M.e z.1.2.2.1 z.2 *
            ∫ y, F y.2 ∂M.K z.1.2.2 z.2)
      (M.law.map (fun w => (preHist r w, actionAt w r))) := by
  obtain ⟨C, hC⟩ := Finite.exists_le (fun sa : JointState nX nH × Fin k =>
    ‖∫ y, F y.2 ∂M.K sa.1 sa.2‖)
  let D := max 1 (policyFactor zeta ^ 2) ^ r.val * policyFactor zeta * C
  have hm : Measurable (fun z : PreHistory T nX nH k r × Fin k =>
      squaredRatioCarrier M j r hjr z.1 * ratio M.b M.e z.1.2.2.1 z.2 *
        ∫ y, F y.2 ∂M.K z.1.2.2 z.2) := by
    exact (((squaredRatioCarrier_measurable M j r hjr).comp measurable_fst).mul
      ((measurable_of_countable fun xa : Fin nX × Fin k =>
        ratio M.b M.e xa.1 xa.2).comp
          (show Measurable (fun z : PreHistory T nX nH k r × Fin k =>
            (z.1.2.2.1, z.2)) by fun_prop))).mul
          ((measurable_of_countable fun sa : JointState nX nH × Fin k =>
            ∫ y, F y.2 ∂M.K sa.1 sa.2).comp
              (show Measurable (fun z : PreHistory T nX nH k r × Fin k =>
                (z.1.2.2, z.2)) by fun_prop))
  apply Integrable.of_bound hm.aestronglyMeasurable D
  filter_upwards with z
  simp only [norm_mul]
  have hr : ‖ratio M.b M.e z.1.2.2.1 z.2‖ ≤ policyFactor zeta := by
    rw [Real.norm_eq_abs, abs_of_nonneg (policy_ratio_bounds M hOverlap hA.1 _ _).1]
    exact (policy_ratio_bounds M hOverlap hA.1 _ _).2
  exact mul_le_mul
    (mul_le_mul (squaredRatioCarrier_norm_bound M hA hOverlap j r hjr z.1)
      hr (norm_nonneg _) (pow_nonneg (by positivity) _))
    (hC (z.1.2.2, z.2)) (norm_nonneg _)
      (mul_nonneg (pow_nonneg (by positivity) _) (Real.exp_nonneg _))

/-- One exact squared-ratio transition, with the analytic integrability
premises separated from the factorization algebra. -/
lemma squaredRatioCarrier_peeling {T nX nH k : Nat} {zeta : ℝ}
    (M : PomdpModel T nX nH k) (hK : FullFiltrationPomdp M)
    (hA : FullFiltrationRandomization M) (hOverlap : PolicyOverlap zeta M)
    (j r : Fin T) (hjr : j.val ≤ r.val) (hr : r.val + 1 < T)
    (F : JointState nX nH → ℝ)
    (hjoint : Integrable
      (fun z : PostHistory T nX nH k r × (ℝ × JointState nX nH) =>
        squaredRatioCarrier M j r hjr z.1.1 *
          ratio M.b M.e z.1.1.2.2.1 z.1.2 ^ 2 * F z.2.2)
      (M.law.map (fun w => (postHist r w, (rewardAt w r, nextState w r)))))
    (haction : Integrable
      (fun z : PreHistory T nX nH k r × Fin k =>
        squaredRatioCarrier M j r hjr z.1 *
          ratio M.b M.e z.1.2.2.1 z.2 *
            ∫ y, F y.2 ∂M.K z.1.2.2 z.2)
      (M.law.map (fun w => (preHist r w, actionAt w r)))) :
    ∫ w, squaredRatioCarrier M j ⟨r.val + 1, hr⟩
          (Nat.le_succ_of_le hjr) (preHist ⟨r.val + 1, hr⟩ w) *
          F (currentState w ⟨r.val + 1, hr⟩) ∂M.law =
      ∫ w, squaredRatioCarrier M j r hjr (preHist r w) *
          squaredRatioStep M F (currentState w r) ∂M.law := by
  have henc : Measurable (fun w : FullPath T nX nH k =>
      (postHist r w, (rewardAt w r, nextState w r))) := by
    unfold postHist preHist currentState pastIndex actionAt rewardAt nextState
    fun_prop
  have hpre : Measurable (preHist r : FullPath T nX nH k → _) := by
    unfold preHist currentState pastIndex
    fun_prop
  calc
    _ = ∫ z, squaredRatioCarrier M j r hjr z.1.1 *
          ratio M.b M.e z.1.1.2.2.1 z.1.2 ^ 2 * F z.2.2
          ∂(M.law.map (fun w => (postHist r w, (rewardAt w r, nextState w r)))) := by
      rw [integral_map henc.aemeasurable hjoint.aestronglyMeasurable]
      apply integral_congr_ae
      filter_upwards with w
      rw [← nextPreHistory_path r hr w, squaredRatioCarrier_next M j r hjr hr]
      rfl
    _ = ∫ h, ∫ y, squaredRatioCarrier M j r hjr h.1 *
          ratio M.b M.e h.1.2.2.1 h.2 ^ 2 * F y.2 ∂M.K h.1.2.2 h.2
          ∂(M.law.map (postHist r)) :=
      full_history_integral_kernel_step M hK r _ hjoint
    _ = ∫ z, ratio M.b M.e z.1.2.2.1 z.2 *
          (squaredRatioCarrier M j r hjr z.1 *
            ratio M.b M.e z.1.2.2.1 z.2 *
              ∫ y, F y.2 ∂M.K z.1.2.2 z.2)
          ∂(M.law.map (fun w => (preHist r w, actionAt w r))) := by
      apply integral_congr_ae
      filter_upwards with z
      rw [integral_const_mul]
      ring
    _ = ∫ h, ∑ a : Fin k, M.e h.2.2.1 a *
          (squaredRatioCarrier M j r hjr h * ratio M.b M.e h.2.2.1 a *
            ∫ y, F y.2 ∂M.K h.2.2 a) ∂(M.law.map (preHist r)) :=
      full_history_integral_ratio_step M hA hOverlap r _ haction
    _ = ∫ h, squaredRatioCarrier M j r hjr h * squaredRatioStep M F h.2.2
          ∂(M.law.map (preHist r)) := by
      apply integral_congr_ae
      filter_upwards with h
      unfold squaredRatioStep
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [behavior_mul_ratio_sq_eq_target_mul_ratio M hOverlap]
      ring
    _ = _ := by
      rw [integral_map hpre.aemeasurable]
      · rfl
      · exact ((squaredRatioCarrier_measurable M j r hjr).mul
          ((measurable_of_finite (squaredRatioStep M F)).comp
            (by fun_prop))).aestronglyMeasurable

/-- Exact terminal conditional second-moment peeling, separated from its
integrability premises. -/
lemma squaredRatioCarrier_terminal_peeling {T nX nH k : Nat} {zeta : ℝ}
    (M : PomdpModel T nX nH k) (hK : FullFiltrationPomdp M)
    (hA : FullFiltrationRandomization M) (hOverlap : PolicyOverlap zeta M)
    (j t : Fin T) (hjt : j.val ≤ t.val)
    (hjoint : Integrable
      (fun z : PostHistory T nX nH k t × (ℝ × JointState nX nH) =>
        squaredRatioCarrier M j t hjt z.1.1 *
          ratio M.b M.e z.1.1.2.2.1 z.1.2 ^ 2 * z.2.1 ^ 2)
      (M.law.map (fun w => (postHist t w, (rewardAt w t, nextState w t)))))
    (haction : Integrable
      (fun z : PreHistory T nX nH k t × Fin k =>
        squaredRatioCarrier M j t hjt z.1 *
          ratio M.b M.e z.1.2.2.1 z.2 *
            ∫ y, y.1 ^ 2 ∂M.K z.1.2.2 z.2)
      (M.law.map (fun w => (preHist t w, actionAt w t)))) :
    ∫ w, squaredRatioCarrier M j t hjt (preHist t w) *
          ratio M.b M.e (currentState w t).1 (actionAt w t) ^ 2 *
            rewardAt w t ^ 2 ∂M.law =
      ∫ w, squaredRatioCarrier M j t hjt (preHist t w) *
          squaredRatioReward M (currentState w t) ∂M.law := by
  have henc : Measurable (fun w : FullPath T nX nH k =>
      (postHist t w, (rewardAt w t, nextState w t))) := by
    unfold postHist preHist currentState pastIndex actionAt rewardAt nextState
    fun_prop
  have hpre : Measurable (preHist t : FullPath T nX nH k → _) := by
    unfold preHist currentState pastIndex
    fun_prop
  calc
    _ = ∫ z, squaredRatioCarrier M j t hjt z.1.1 *
          ratio M.b M.e z.1.1.2.2.1 z.1.2 ^ 2 * z.2.1 ^ 2
          ∂(M.law.map (fun w => (postHist t w, (rewardAt w t, nextState w t)))) := by
      rw [integral_map henc.aemeasurable hjoint.aestronglyMeasurable]
      rfl
    _ = ∫ h, ∫ y, squaredRatioCarrier M j t hjt h.1 *
          ratio M.b M.e h.1.2.2.1 h.2 ^ 2 * y.1 ^ 2 ∂M.K h.1.2.2 h.2
          ∂(M.law.map (postHist t)) :=
      full_history_integral_kernel_step M hK t _ hjoint
    _ = ∫ z, ratio M.b M.e z.1.2.2.1 z.2 *
          (squaredRatioCarrier M j t hjt z.1 *
            ratio M.b M.e z.1.2.2.1 z.2 *
              ∫ y, y.1 ^ 2 ∂M.K z.1.2.2 z.2)
          ∂(M.law.map (fun w => (preHist t w, actionAt w t))) := by
      apply integral_congr_ae
      filter_upwards with z
      rw [integral_const_mul]
      ring
    _ = ∫ h, ∑ a : Fin k, M.e h.2.2.1 a *
          (squaredRatioCarrier M j t hjt h * ratio M.b M.e h.2.2.1 a *
            ∫ y, y.1 ^ 2 ∂M.K h.2.2 a) ∂(M.law.map (preHist t)) :=
      full_history_integral_ratio_step M hA hOverlap t _ haction
    _ = ∫ h, squaredRatioCarrier M j t hjt h * squaredRatioReward M h.2.2
          ∂(M.law.map (preHist t)) := by
      apply integral_congr_ae
      filter_upwards with h
      unfold squaredRatioReward
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [behavior_mul_ratio_sq_eq_target_mul_ratio M hOverlap]
      ring
    _ = _ := by
      rw [integral_map hpre.aemeasurable]
      · rfl
      · exact ((squaredRatioCarrier_measurable M j t hjt).mul
          ((measurable_of_finite (squaredRatioReward M)).comp
            (by fun_prop))).aestronglyMeasurable

lemma squaredRatioCarrier_terminal_action_integrable {T nX nH k : Nat} {zeta : ℝ}
    (M : PomdpModel T nX nH k) (hA : FullFiltrationRandomization M)
    (hY : RewardMomentEnvelope M) (hOverlap : PolicyOverlap zeta M)
    (j t : Fin T) (hjt : j.val ≤ t.val) :
    Integrable
      (fun z : PreHistory T nX nH k t × Fin k =>
        squaredRatioCarrier M j t hjt z.1 *
          ratio M.b M.e z.1.2.2.1 z.2 *
            ∫ y, y.1 ^ 2 ∂M.K z.1.2.2 z.2)
      (M.law.map (fun w => (preHist t w, actionAt w t))) := by
  let H : JointState nX nH × Fin k → ℝ := fun sa =>
    ∫ y, y.1 ^ 2 ∂M.K sa.1 sa.2
  obtain ⟨C, hC⟩ := Finite.exists_le (fun sa : JointState nX nH × Fin k => ‖H sa‖)
  let D := max 1 (policyFactor zeta ^ 2) ^ t.val * policyFactor zeta * C
  have hm : Measurable (fun z : PreHistory T nX nH k t × Fin k =>
      squaredRatioCarrier M j t hjt z.1 * ratio M.b M.e z.1.2.2.1 z.2 *
        H (z.1.2.2, z.2)) := by
    exact (((squaredRatioCarrier_measurable M j t hjt).comp measurable_fst).mul
      ((measurable_of_countable fun xa : Fin nX × Fin k =>
        ratio M.b M.e xa.1 xa.2).comp
          (show Measurable (fun z : PreHistory T nX nH k t × Fin k =>
            (z.1.2.2.1, z.2)) by fun_prop))).mul
      ((measurable_of_finite H).comp
        (show Measurable (fun z : PreHistory T nX nH k t × Fin k =>
          (z.1.2.2, z.2)) by fun_prop))
  apply Integrable.of_bound hm.aestronglyMeasurable D
  filter_upwards with z
  change ‖squaredRatioCarrier M j t hjt z.1 *
    ratio M.b M.e z.1.2.2.1 z.2 * H (z.1.2.2, z.2)‖ ≤ D
  simp only [norm_mul]
  have hr : ‖ratio M.b M.e z.1.2.2.1 z.2‖ ≤ policyFactor zeta := by
    rw [Real.norm_eq_abs, abs_of_nonneg (policy_ratio_bounds M hOverlap hA.1 _ _).1]
    exact (policy_ratio_bounds M hOverlap hA.1 _ _).2
  exact mul_le_mul
    (mul_le_mul (squaredRatioCarrier_norm_bound M hA hOverlap j t hjt z.1)
      hr (norm_nonneg _) (pow_nonneg (by positivity) _))
    (hC (z.1.2.2, z.2)) (norm_nonneg _)
      (mul_nonneg (pow_nonneg (by positivity) _) (Real.exp_nonneg _))

lemma squaredRatioCarrier_terminal_integrable {T nX nH k : Nat} {zeta : ℝ}
    (M : PomdpModel T nX nH k) (hK : FullFiltrationPomdp M)
    (hA : FullFiltrationRandomization M) (hY : RewardMomentEnvelope M)
    (hOverlap : PolicyOverlap zeta M) (j t : Fin T) (hjt : j.val ≤ t.val) :
    Integrable
      (fun z : PostHistory T nX nH k t × (ℝ × JointState nX nH) =>
        squaredRatioCarrier M j t hjt z.1.1 *
          ratio M.b M.e z.1.1.2.2.1 z.1.2 ^ 2 * z.2.1 ^ 2)
      (M.law.map (fun w => (postHist t w, (rewardAt w t, nextState w t)))) := by
  letI : IsMarkovKernel (kernelOfK M) := ⟨fun sa => hK.1 sa.1 sa.2⟩
  rw [hK.2 t]
  let κ := Kernel.comap (kernelOfK M)
    (fun h : PostHistory T nX nH k t => (h.1.2.2, h.2)) (by fun_prop)
  have hm : Measurable
      (fun z : PostHistory T nX nH k t × (ℝ × JointState nX nH) =>
        squaredRatioCarrier M j t hjt z.1.1 *
          ratio M.b M.e z.1.1.2.2.1 z.1.2 ^ 2 * z.2.1 ^ 2) := by
    exact (((squaredRatioCarrier_measurable M j t hjt).comp
      (show Measurable (fun z : PostHistory T nX nH k t ×
        (ℝ × JointState nX nH) => z.1.1) by fun_prop)).mul
      (((measurable_of_countable fun xa : Fin nX × Fin k =>
        ratio M.b M.e xa.1 xa.2).comp
          (show Measurable (fun z : PostHistory T nX nH k t ×
            (ℝ × JointState nX nH) => (z.1.1.2.2.1, z.1.2)) by fun_prop)).pow_const 2)).mul
      ((by fun_prop : Measurable fun z : PostHistory T nX nH k t ×
        (ℝ × JointState nX nH) => z.2.1).pow_const 2)
  rw [Measure.integrable_compProd_iff hm.aestronglyMeasurable]
  constructor
  · filter_upwards with h
    change Integrable (fun y =>
      (squaredRatioCarrier M j t hjt h.1 *
        ratio M.b M.e h.1.2.2.1 h.2 ^ 2) * y.1 ^ 2) (M.K h.1.2.2 h.2)
    exact (hY h.1.2.2 h.2).2.1.const_mul _
  · have hout : StronglyMeasurable (fun x : PostHistory T nX nH k t =>
        ∫ y, ‖squaredRatioCarrier M j t hjt x.1 *
          ratio M.b M.e x.1.2.2.1 x.2 ^ 2 * y.1 ^ 2‖ ∂κ x) :=
      hm.norm.stronglyMeasurable.integral_kernel_prod_right'
    let D := max 1 (policyFactor zeta ^ 2) ^ t.val * policyFactor zeta ^ 2
    apply Integrable.of_bound hout.aestronglyMeasurable D
    filter_upwards with h
    change ‖∫ y, ‖squaredRatioCarrier M j t hjt h.1 *
      ratio M.b M.e h.1.2.2.1 h.2 ^ 2 * y.1 ^ 2‖
        ∂M.K h.1.2.2 h.2‖ ≤ D
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    simp_rw [norm_mul, norm_pow, Real.norm_eq_abs]
    rw [MeasureTheory.integral_const_mul]
    have hr : ‖ratio M.b M.e h.1.2.2.1 h.2‖ ≤ policyFactor zeta := by
      rw [Real.norm_eq_abs, abs_of_nonneg (policy_ratio_bounds M hOverlap hA.1 _ _).1]
      exact (policy_ratio_bounds M hOverlap hA.1 _ _).2
    have hi : 0 ≤ ∫ y, |y.1| ^ 2 ∂M.K h.1.2.2 h.2 :=
      integral_nonneg fun _ => sq_nonneg _
    have hc : |squaredRatioCarrier M j t hjt h.1| *
        |ratio M.b M.e h.1.2.2.1 h.2| ^ 2 ≤
          max 1 (policyFactor zeta ^ 2) ^ t.val * policyFactor zeta ^ 2 := by
      simpa [Real.norm_eq_abs] using
        mul_le_mul (squaredRatioCarrier_norm_bound M hA hOverlap j t hjt h.1)
          (pow_le_pow_left₀ (norm_nonneg _) hr 2)
          (sq_nonneg _) (pow_nonneg (by positivity) _)
    have hy : (∫ y, |y.1| ^ 2 ∂M.K h.1.2.2 h.2) ≤ 1 := by
      simpa [sq_abs] using (hY h.1.2.2 h.2).2.2.2
    calc
      |squaredRatioCarrier M j t hjt h.1| *
          |ratio M.b M.e h.1.2.2.1 h.2| ^ 2 *
            ∫ y, |y.1| ^ 2 ∂M.K h.1.2.2 h.2 ≤
          (max 1 (policyFactor zeta ^ 2) ^ t.val * policyFactor zeta ^ 2) * 1 :=
        mul_le_mul hc hy hi (mul_nonneg (pow_nonneg (by positivity) _) (sq_nonneg _))
      _ = D := by simp [D]

lemma squaredRatioCarrier_terminal {T nX nH k : Nat} {zeta : ℝ}
    (M : PomdpModel T nX nH k) (hK : FullFiltrationPomdp M)
    (hA : FullFiltrationRandomization M) (hY : RewardMomentEnvelope M)
    (hOverlap : PolicyOverlap zeta M) (j t : Fin T) (hjt : j.val ≤ t.val) :
    ∫ w, squaredRatioCarrier M j t hjt (preHist t w) *
          ratio M.b M.e (currentState w t).1 (actionAt w t) ^ 2 *
            rewardAt w t ^ 2 ∂M.law =
      ∫ w, squaredRatioCarrier M j t hjt (preHist t w) *
          squaredRatioReward M (currentState w t) ∂M.law :=
  squaredRatioCarrier_terminal_peeling M hK hA hOverlap j t hjt
    (squaredRatioCarrier_terminal_integrable M hK hA hY hOverlap j t hjt)
    (squaredRatioCarrier_terminal_action_integrable M hA hY hOverlap j t hjt)

lemma squaredRatioCarrier_transition {T nX nH k : Nat} {zeta : ℝ}
    (M : PomdpModel T nX nH k) (hK : FullFiltrationPomdp M)
    (hA : FullFiltrationRandomization M) (hOverlap : PolicyOverlap zeta M)
    (j r : Fin T) (hjr : j.val ≤ r.val) (hr : r.val + 1 < T)
    (F : JointState nX nH → ℝ) :
    ∫ w, squaredRatioCarrier M j ⟨r.val + 1, hr⟩
          (Nat.le_succ_of_le hjr) (preHist ⟨r.val + 1, hr⟩ w) *
          F (currentState w ⟨r.val + 1, hr⟩) ∂M.law =
      ∫ w, squaredRatioCarrier M j r hjr (preHist r w) *
          squaredRatioStep M F (currentState w r) ∂M.law :=
  squaredRatioCarrier_peeling M hK hA hOverlap j r hjr hr F
    (squaredRatioCarrier_kernel_integrable M hA hOverlap j r hjr F)
    (squaredRatioCarrier_action_integrable M hA hOverlap j r hjr F)

lemma squaredRatioCarrier_iteration {T nX nH k : Nat} {zeta : ℝ}
    (M : PomdpModel T nX nH k) (hK : FullFiltrationPomdp M)
    (hA : FullFiltrationRandomization M) (hOverlap : PolicyOverlap zeta M)
    (j : Fin T) (n : Nat) (hjn : j.val ≤ n) (hnT : n < T)
    (F : JointState nX nH → ℝ) :
    ∫ w, squaredRatioCarrier M j ⟨n, hnT⟩ hjn (preHist ⟨n, hnT⟩ w) *
        F (currentState w ⟨n, hnT⟩) ∂M.law =
      ∫ w, ((squaredRatioStep M)^[n - j.val] F) (currentState w j) ∂M.law := by
  induction n, hjn using Nat.le_induction generalizing F with
  | base =>
      have he : (⟨j.val, hnT⟩ : Fin T) = j := Fin.ext rfl
      cases he
      simp [squaredRatioCarrier_self]
  | succ n hjn ih =>
      have hnT' : n < T := lt_trans (Nat.lt_succ_self n) hnT
      calc
        _ = ∫ w, squaredRatioCarrier M j ⟨n, hnT'⟩ hjn (preHist ⟨n, hnT'⟩ w) *
              squaredRatioStep M F (currentState w ⟨n, hnT'⟩) ∂M.law :=
          squaredRatioCarrier_transition M hK hA hOverlap j ⟨n, hnT'⟩ hjn hnT F
        _ = ∫ w, ((squaredRatioStep M)^[n - j.val] (squaredRatioStep M F))
              (currentState w j) ∂M.law := ih hnT' (squaredRatioStep M F)
        _ = _ := by
          have hd : n + 1 - j.val = (n - j.val) + 1 := by omega
          have hc : ((squaredRatioStep M)^[n - j.val] (squaredRatioStep M F)) =
              squaredRatioStep M ((squaredRatioStep M)^[n - j.val] F) :=
            (Function.iterate_succ_apply (squaredRatioStep M) (n - j.val) F).symm.trans
              (Function.iterate_succ_apply' (squaredRatioStep M) (n - j.val) F)
          rw [hd, Function.iterate_succ_apply', hc]

lemma squaredRatioCarrier_windowScore {T nX nH k : Nat}
    (M : PomdpModel T nX nH k) (j t : Fin T) (hjt : j.val ≤ t.val)
    (w : FullPath T nX nH k) :
    squaredRatioCarrier M j t hjt (preHist t w) *
        ratio M.b M.e (currentState w t).1 (actionAt w t) ^ 2 *
          rewardAt w t ^ 2 = windowScore M j t w ^ 2 := by
  have hlin := terminalCarrier_windowScore M j t hjt
    (Set.univ : Set (PreHistory T nX nH k j)) w
  simp only [Set.indicator_of_mem (Set.mem_univ _)] at hlin
  have hc : squaredRatioCarrier M j t hjt (preHist t w) =
      historyRatioCarrier M j t hjt Set.univ (preHist t w) ^ 2 := by
    unfold squaredRatioCarrier historyRatioCarrier
    simp only [Set.indicator_of_mem (Set.mem_univ _), one_mul]
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro q _
    by_cases hq : j.val ≤ q.val <;> simp [hq]
  rw [hc, ← hlin]
  ring

/-- Exact second moment of a likelihood-ratio window as an iterate of the
squared-ratio operator from the stationary behavior marginal. -/
lemma integral_windowScore_sq_eq_stationary_squaredIter
    {T nX nH k : Nat} {zeta : ℝ}
    (M : PomdpModel T nX nH k) (hK : FullFiltrationPomdp M)
    (hA : FullFiltrationRandomization M) (hY : RewardMomentEnvelope M)
    (hOverlap : PolicyOverlap zeta M) (hStart : StationaryStart M)
    (j t : Fin T) (hjt : j.val ≤ t.val) :
    ∫ w, windowScore M j t w ^ 2 ∂M.law =
      ∑ s, stationaryLaw (policyKernel M M.b) s *
        ((squaredRatioStep M)^[t.val - j.val] (squaredRatioReward M)) s := by
  calc
    _ = ∫ w, squaredRatioCarrier M j t hjt (preHist t w) *
          ratio M.b M.e (currentState w t).1 (actionAt w t) ^ 2 *
            rewardAt w t ^ 2 ∂M.law := by
      apply integral_congr_ae
      filter_upwards with w
      exact (squaredRatioCarrier_windowScore M j t hjt w).symm
    _ = ∫ w, squaredRatioCarrier M j t hjt (preHist t w) *
          squaredRatioReward M (currentState w t) ∂M.law :=
      squaredRatioCarrier_terminal M hK hA hY hOverlap j t hjt
    _ = ∫ w, ((squaredRatioStep M)^[t.val - j.val] (squaredRatioReward M))
          (currentState w j) ∂M.law :=
      squaredRatioCarrier_iteration M hK hA hOverlap j t.val hjt t.isLt
        (squaredRatioReward M)
    _ = _ := integral_currentState_eq_stationary M hK hA hStart j _

/-- The rate-sharp diagonal PHIW window moment has one overlap factor per
action in the window. -/
lemma integral_windowScore_sq_le {T nX nH k : Nat} {zeta : ℝ}
    (M : PomdpModel T nX nH k) (hK : FullFiltrationPomdp M)
    (hA : FullFiltrationRandomization M) (hY : RewardMomentEnvelope M)
    (hOverlap : PolicyOverlap zeta M) (hStart : StationaryStart M)
    (j t : Fin T) (hjt : j.val ≤ t.val) :
    ∫ w, windowScore M j t w ^ 2 ∂M.law ≤
      policyFactor zeta ^ (t.val - j.val + 1) := by
  rw [integral_windowScore_sq_eq_stationary_squaredIter
    M hK hA hY hOverlap hStart j t hjt]
  have hp := hStart.1.1
  calc
    (∑ s, stationaryLaw (policyKernel M M.b) s *
      ((squaredRatioStep M)^[t.val - j.val] (squaredRatioReward M)) s) ≤
        ∑ s, stationaryLaw (policyKernel M M.b) s *
          policyFactor zeta ^ (t.val - j.val + 1) := by
      apply Finset.sum_le_sum
      intro s _
      exact mul_le_mul_of_nonneg_left
        (squaredRatioIter_reward_le M hK hA hY hOverlap (t.val - j.val) s)
        (hp.1 s)
    _ = _ := by rw [← Finset.sum_mul, hp.2, one_mul]

end CausalSmith.Stat.PomdpStateauditMinimax
