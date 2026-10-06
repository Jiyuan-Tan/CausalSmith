module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.BlockPhiwMoments

/-!
# One-step change of measure for arbitrary-start segments

These identities integrate the common reward-successor law jointly. They are
the one-step building blocks for chronological cancellation in equation (1)
of the block PHIW moment roadmap, with no reward-successor independence.
-/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open MeasureTheory
open CausalSmith.Stat.PomdpLatentOverlapMinimax
open scoped BigOperators ENNReal

/-- Domination makes behavior-null cells target-null, so multiplying the zero-convention ratio
by behavior mass recovers the target mass exactly. For [the observed-state count](hyp:nX),
[the behavior policy](hyp:b), [the target policy](hyp:e),
[the target policy assumption](hyp:he), [the action-overlap factor](hyp:L),
[the dom assumption](hyp:hdom), [the observed state](hyp:x), and [the action](hyp:a), this
establishes [the partial-history importance-weighted ratio behavior cancel result](goal). -/
-- @node: phiw_ratio_behavior_cancel
lemma phiw_ratio_behavior_cancel {nX : Nat} (b e : Policy nX)
    (he : PolicyVector e) (L : ℝ) (hdom : ∀ x a, e x a ≤ L * b x a)
    (x : Fin nX) (a : Bool) : b x a * ratio b e x a = e x a := by
  unfold ratio
  split_ifs with hz
  · have he0 : e x a = 0 := le_antisymm
      (by simpa [hz] using hdom x a) ((he x).1 a)
    simp [hz, he0]
  · exact mul_div_cancel₀ _ hz

/-- Integrating a measurable test against the structural behavior step amounts to mixing its
joint reward-successor integrals over behavior actions. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the model](hyp:m),
[the behavior policy assumption](hyp:hb), [the state](hyp:s), [the f](hyp:f),
[the f assumption](hyp:hf), and [the int assumption](hyp:hint), this establishes
[the partial-history importance-weighted segment step integral result](goal). -/
-- @node: phiw_segmentStep_integral
lemma phiw_segmentStep_integral {T M : Nat} (m : ModelIndex T M)
    (hb : PolicyVector m.Mx.b) (s : JointState m.nX m.nH)
    (f : Bool × ℝ × JointState m.nX m.nH → ℝ) (hf : Measurable f)
    (hint : ∀ a, Integrable (fun ys ↦ f (a, ys.1, ys.2)) (m.Mx.K s a)) :
    (∫ step, f step ∂segmentStepLaw m s) =
      ∑ a : Bool, m.Mx.b s.1 a * ∫ ys, f (a, ys.1, ys.2) ∂m.Mx.K s a := by
  have hmap : ∀ a : Bool, Measurable
      (fun ys : ℝ × JointState m.nX m.nH ↦ (a, ys.1, ys.2)) := by
    intro a
    fun_prop
  unfold segmentStepLaw
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro a _
    rw [integral_smul_measure,
      integral_map (hmap a).aemeasurable hf.aestronglyMeasurable,
      ENNReal.toReal_ofReal ((hb s.1).1 a)]
    rfl
  · intro a _
    apply Integrable.smul_measure _ ENNReal.ofReal_ne_top
    exact (integrable_map_measure hf.aestronglyMeasurable (hmap a).aemeasurable).2
      (hint a)

/-- A current likelihood ratio replaces behavior by target in any integrable joint
reward-successor test, including tests coupling both outputs. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the model](hyp:m),
[the behavior policy assumption](hyp:hb), [the target policy](hyp:e),
[the target policy assumption](hyp:he), [the action-overlap factor](hyp:L),
[the dom assumption](hyp:hdom), [the state](hyp:s), [the f](hyp:f), [the f assumption](hyp:hf),
and [the int assumption](hyp:hint), this establishes
[the partial-history importance-weighted segment step change of measure result](goal). -/
-- @node: phiw_segmentStep_changeOfMeasure
lemma phiw_segmentStep_changeOfMeasure {T M : Nat} (m : ModelIndex T M)
    (hb : PolicyVector m.Mx.b) (e : Policy m.nX) (he : PolicyVector e)
    (L : ℝ) (hdom : ∀ x a, e x a ≤ L * m.Mx.b x a)
    (s : JointState m.nX m.nH)
    (f : Bool × ℝ × JointState m.nX m.nH → ℝ) (hf : Measurable f)
    (hint : ∀ a, Integrable (fun ys ↦ f (a, ys.1, ys.2)) (m.Mx.K s a)) :
    (∫ step, ratio m.Mx.b e s.1 step.1 * f step ∂segmentStepLaw m s) =
      ∑ a : Bool, e s.1 a * ∫ ys, f (a, ys.1, ys.2) ∂m.Mx.K s a := by
  have hratio : Measurable (fun step : Bool × ℝ × JointState m.nX m.nH ↦
      ratio m.Mx.b e s.1 step.1) :=
    (measurable_of_countable (fun a : Bool ↦ ratio m.Mx.b e s.1 a)).comp measurable_fst
  rw [phiw_segmentStep_integral m hb s
    (fun step ↦ ratio m.Mx.b e s.1 step.1 * f step) (hratio.mul hf)
    (fun a ↦ (hint a).const_mul (ratio m.Mx.b e s.1 a))]
  apply Finset.sum_congr rfl
  intro a _
  dsimp only
  rw [integral_const_mul, ← mul_assoc,
    phiw_ratio_behavior_cancel m.Mx.b e he L hdom s.1 a]

/-- Unit reward support holds almost everywhere under each joint kernel. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the model](hyp:m),
[the state](hyp:s), and [the action](hyp:a), this establishes
[the partial-history importance-weighted kernel reward ae unit result](goal). -/
-- @node: phiw_kernel_reward_ae_unit
lemma phiw_kernel_reward_ae_unit {T M : Nat} (m : ModelIndex T M)
    (s : JointState m.nX m.nH) (a : Bool) :
    ∀ᵐ ys ∂m.Mx.K s a, ys.1 ∈ Set.Icc (0 : ℝ) 1 := by
  rw [ae_iff]
  convert m.reward_unit s a using 1
  congr 1
  ext ys
  simp

/-- The construction's unit reward support supplies integrability for free. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the model](hyp:m),
[the state](hyp:s), and [the action](hyp:a), this establishes
[the partial-history importance-weighted kernel reward integrability result](goal). -/
@[fun_prop]
-- @node: phiw_kernel_reward_integrable
lemma phiw_kernel_reward_integrable {T M : Nat} (m : ModelIndex T M)
    (s : JointState m.nX m.nH) (a : Bool) :
    Integrable (fun ys ↦ ys.1) (m.Mx.K s a) := by
  have : IsProbabilityMeasure (m.Mx.K s a) := m.kernel_law.1 s a
  have hm : Measurable (fun ys : ℝ × JointState m.nX m.nH ↦ ys.1) := by fun_prop
  apply Integrable.of_mem_Icc 0 1 hm.aemeasurable
  exact phiw_kernel_reward_ae_unit m s a

/-- The final weighted action and reward give exactly the target reward regression, the terminal
step in equation (1) of the block moment proof. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j), and [the state](hyp:s), this
establishes [the partial-history importance-weighted segment step weighted reward result](goal). -/
-- @node: phiw_segmentStep_weighted_reward
lemma phiw_segmentStep_weighted_reward {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m)
    (j : Fin M) (s : JointState m.nX m.nH) :
    (∫ step, ratio m.Mx.b (m.Mx.E j) s.1 step.1 * step.2.1
      ∂segmentStepLaw m s) = listRewardRegression m (m.Mx.E j) s := by
  exact phiw_segmentStep_changeOfMeasure m hClass.sequential_ignorability.1
    (m.Mx.E j) (hClass.action_overlap j).1 (policyFactor zeta)
    (hClass.action_overlap j).2 s (fun step ↦ step.2.1)
    (by fun_prop) (phiw_kernel_reward_integrable m s)

/-- The ordinary one-step likelihood ratio has expectation one even when some behavior actions
have zero probability. For [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the model](hyp:m), [the class assumption](hyp:hClass),
[the candidate index](hyp:j), and [the state](hyp:s), this establishes
[the partial-history importance-weighted segment step ratio mean one result](goal). -/
-- @node: phiw_segmentStep_ratio_mean_one
lemma phiw_segmentStep_ratio_mean_one {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m)
    (j : Fin M) (s : JointState m.nX m.nH) :
    (∫ step, ratio m.Mx.b (m.Mx.E j) s.1 step.1 ∂segmentStepLaw m s) = 1 := by
  have hint : ∀ a : Bool, Integrable (fun _ : ℝ × JointState m.nX m.nH ↦ (1 : ℝ))
      (m.Mx.K s a) := by
    intro a
    have : IsProbabilityMeasure (m.Mx.K s a) := m.kernel_law.1 s a
    fun_prop
  have h := phiw_segmentStep_changeOfMeasure m hClass.sequential_ignorability.1
    (m.Mx.E j) (hClass.action_overlap j).1 (policyFactor zeta)
    (hClass.action_overlap j).2 s (fun _ ↦ 1) (by fun_prop) hint
  have hmass : ∀ a : Bool, (∫ _ : ℝ × JointState m.nX m.nH, (1 : ℝ)
      ∂m.Mx.K s a) = 1 := by
    intro a
    have : IsProbabilityMeasure (m.Mx.K s a) := m.kernel_law.1 s a
    simp
  simp only [mul_one, hmass] at h
  exact h.trans ((hClass.action_overlap j).1 s.1).2

/-- Squared kernel rewards are integrable and have mean at most one, using only the
construction's unit support and probability law. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the model](hyp:m), [the state](hyp:s), and
[the action](hyp:a), this establishes
[the partial-history importance-weighted kernel reward square bound result](goal). -/
-- @node: phiw_kernel_reward_square_bound
lemma phiw_kernel_reward_square_bound {T M : Nat} (m : ModelIndex T M)
    (s : JointState m.nX m.nH) (a : Bool) :
    Integrable (fun ys ↦ ys.1 ^ 2) (m.Mx.K s a) ∧
      (∫ ys, ys.1 ^ 2 ∂m.Mx.K s a) ≤ 1 := by
  have : IsProbabilityMeasure (m.Mx.K s a) := m.kernel_law.1 s a
  have hunit : ∀ᵐ ys ∂m.Mx.K s a, ys.1 ^ 2 ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [phiw_kernel_reward_ae_unit m s a] with ys hy
    exact ⟨sq_nonneg _, by nlinarith [hy.1, hy.2]⟩
  have hm : Measurable (fun ys : ℝ × JointState m.nX m.nH ↦ ys.1 ^ 2) := by
    fun_prop
  have hi := Integrable.of_mem_Icc 0 1 hm.aemeasurable hunit
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ _ : ℝ × JointState m.nX m.nH, (1 : ℝ) ∂m.Mx.K s a :=
      integral_mono_ae hi (integrable_const 1) (hunit.mono fun _ hy ↦ hy.2)
    _ = 1 := by simp

/-- A squared weighted one-step reward costs at most one factor of `L`. This is the terminal
one-step bound used in chronological equation (6). For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j), and [the state](hyp:s), this
establishes
[the partial-history importance-weighted segment step weighted reward second moment result](goal). -/
-- @node: phiw_segmentStep_weighted_reward_second_moment
lemma phiw_segmentStep_weighted_reward_second_moment {T M : Nat}
    (t0 zeta C : ℝ) (m : ModelIndex T M)
    (hClass : PolicyListClass t0 zeta C m) (j : Fin M)
    (s : JointState m.nX m.nH) :
    (∫ step, (ratio m.Mx.b (m.Mx.E j) s.1 step.1 * step.2.1) ^ 2
      ∂segmentStepLaw m s) ≤ policyFactor zeta := by
  have hm : Measurable (fun step : Bool × ℝ × JointState m.nX m.nH ↦
      (ratio m.Mx.b (m.Mx.E j) s.1 step.1 * step.2.1) ^ 2) := by
    have hr : Measurable (fun step : Bool × ℝ × JointState m.nX m.nH ↦
        ratio m.Mx.b (m.Mx.E j) s.1 step.1) :=
      (measurable_of_countable (fun a : Bool ↦ ratio m.Mx.b (m.Mx.E j) s.1 a)).comp
        measurable_fst
    exact (hr.mul measurable_snd.fst).pow_const 2
  have hint : ∀ a : Bool, Integrable
      (fun ys ↦ (ratio m.Mx.b (m.Mx.E j) s.1 a * ys.1) ^ 2) (m.Mx.K s a) := by
    intro a
    simpa only [mul_pow] using (phiw_kernel_reward_square_bound m s a).1.const_mul
      ((ratio m.Mx.b (m.Mx.E j) s.1 a) ^ 2)
  rw [phiw_segmentStep_integral m hClass.sequential_ignorability.1 s _ hm hint]
  calc
    _ ≤ ∑ a : Bool, m.Mx.b s.1 a * (ratio m.Mx.b (m.Mx.E j) s.1 a) ^ 2 := by
      apply Finset.sum_le_sum
      intro a _
      dsimp only
      simp_rw [mul_pow]
      rw [integral_const_mul]
      have h := mul_le_mul_of_nonneg_left
        (phiw_kernel_reward_square_bound m s a).2
        (sq_nonneg (ratio m.Mx.b (m.Mx.E j) s.1 a))
      exact mul_le_mul_of_nonneg_left (by simpa using h)
        ((hClass.sequential_ignorability.1 s.1).1 a)
    _ ≤ policyFactor zeta :=
      phiw_model_ratio_action_second_moment t0 zeta C m hClass j s.1

end CausalSmith.Stat.PomdpPolicyclassRegret
