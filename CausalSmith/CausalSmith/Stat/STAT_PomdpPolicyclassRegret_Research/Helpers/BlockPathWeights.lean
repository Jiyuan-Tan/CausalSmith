module
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.Weights
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.BlockChronological
public import Causalean.Mathlib.MeasureTheory.IntegralBind

/-!
# Likelihood-ratio products on generated behavior paths

Chronological cancellation is performed under the actual structural segment
measure, integrating rewards and successors jointly. The ordinary path weight
has mean one and second moment at most one overlap factor per action, as used
in equations (6) and (7) of the block moment roadmap.
-/

@[expose] public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open MeasureTheory ProbabilityTheory
open CausalSmith.Stat.PomdpLatentOverlapMinimax
open Causalean.Mathlib.Probability.FiniteMarkovOscillation
open scoped BigOperators ENNReal

/-- Dropping a prefix preserves the coordinate-generated list sigma algebra. For
[the first event](hyp:A) and [the sample size](hyp:n), this establishes
[the segment list drop measurability result](goal). -/
@[fun_prop]
-- @node: segment_list_drop_measurable
lemma segment_list_drop_measurable {A : Type*} [MeasurableSpace A] (n : Nat) :
    Measurable (fun l : List A ↦ l.drop n) := by
  apply measurable_generateFrom
  rintro _ ⟨k, B, hB, rfl⟩
  have hcoord : MeasurableSet {l : List A | ∃ a ∈ B, l[n + k]? = some a} :=
    MeasurableSpace.measurableSet_generateFrom ⟨n + k, B, hB, rfl⟩
  convert hcoord using 1
  ext l
  simp

/-- The measurable family which prepends a current step to a generated future. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the model](hyp:m),
[the behavior policy assumption](hyp:hb), and [the sample size](hyp:n), this establishes
[the segment from cons family measurability result](goal). -/
@[fun_prop]
-- @node: segmentFrom_cons_family_measurable
lemma segmentFrom_cons_family_measurable {T M : Nat} (m : ModelIndex T M)
    (hb : PolicyVector m.Mx.b) (n : Nat) :
    Measurable (fun step : Bool × ℝ × JointState m.nX m.nH ↦
      (segmentFrom m n step.2.2).map (fun tail ↦ step :: tail)) := by
  let κ : Kernel (Bool × ℝ × JointState m.nX m.nH)
      (List (Bool × ℝ × JointState m.nX m.nH)) :=
    ⟨fun step ↦ segmentFrom m n step.2.2,
      (measurable_of_countable (segmentFrom m n)).comp measurable_snd.snd⟩
  have : IsMarkovKernel κ :=
    ⟨fun step ↦ segmentFrom_isProbability m hb n step.2.2⟩
  apply Measure.measurable_of_measurable_coe
  intro B hB
  have hcons : MeasurableSet
      ((fun p : (Bool × ℝ × JointState m.nX m.nH) ×
        List (Bool × ℝ × JointState m.nX m.nH) ↦ p.1 :: p.2) ⁻¹' B) :=
    segment_list_cons_measurable hB
  convert Kernel.measurable_kernel_prodMk_left (κ := κ) hcons using 1
  funext step
  exact Measure.map_apply
    (segment_list_cons_measurable.comp (measurable_prodMk_left (x := step))) hB

/-- A segment integral is the chronological joint-step integral followed by its successor's
segment integral. Integrability is the usual Bochner condition. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the model](hyp:m),
[the behavior policy assumption](hyp:hb), [the sample size](hyp:n), [the state](hyp:s),
[the f](hyp:f), and [the f assumption](hyp:hf), this establishes
[the segment from integral succ result](goal). -/
-- @node: segmentFrom_integral_succ
lemma segmentFrom_integral_succ {T M : Nat} (m : ModelIndex T M)
    (hb : PolicyVector m.Mx.b) (n : Nat)
    (s : JointState m.nX m.nH)
    (f : List (Bool × ℝ × JointState m.nX m.nH) → ℝ)
    (hf : Integrable f (segmentFrom m (n + 1) s)) :
    (∫ path, f path ∂segmentFrom m (n + 1) s) =
      ∫ step, ∫ tail, f (step :: tail) ∂segmentFrom m n step.2.2
        ∂segmentStepLaw m s := by
  exact Causalean.Mathlib.MeasureTheory.integral_bind_map
    (fun step ↦ segment_list_cons_measurable.comp (measurable_prodMk_left (x := step)))
    (segmentFrom_cons_family_measurable m hb n) hf

/-- Product of the first `n` chronological action ratios, starting at `s`.
Padding is only to make the function total; generated paths have the required length. -/
-- @node: phiwPathWeight
noncomputable def phiwPathWeight {T M : Nat} (m : ModelIndex T M) (j : Fin M) :
    Nat → JointState m.nX m.nH → List (Bool × ℝ × JointState m.nX m.nH) → ℝ
  | 0, _, _ => 1
  | n + 1, s, path =>
      let step := path.getD 0 (false, 0, s)
      ratio m.Mx.b (m.Mx.E j) s.1 step.1 *
        phiwPathWeight m j n step.2.2 (path.drop 1)

/-- Path weights are measurable functions of the full-state start and path. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the model](hyp:m),
[the candidate index](hyp:j), and [the sample size](hyp:n), this establishes
[the partial-history importance-weighted path weight measurability result](goal). -/
@[fun_prop]
-- @node: phiwPathWeight_measurable
lemma phiwPathWeight_measurable {T M : Nat} (m : ModelIndex T M) (j : Fin M)
    (n : Nat) : Measurable (fun p : JointState m.nX m.nH ×
      List (Bool × ℝ × JointState m.nX m.nH) ↦ phiwPathWeight m j n p.1 p.2) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    apply measurable_from_prod_countable_right
    intro s
    have hg := segment_list_getD_measurable 0 (false, (0 : ℝ), s)
    have hr := (measurable_of_finite
      (fun a : Bool ↦ ratio m.Mx.b (m.Mx.E j) s.1 a)).comp hg.fst
    exact hr.mul (ih.comp (hg.snd.snd.prodMk (segment_list_drop_measurable 1)))

/-- Every chronological path weight lies between zero and `L^n`. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j), [the sample size](hyp:n),
[the state](hyp:s), and [the path](hyp:path), this establishes
[the partial-history importance-weighted path weight bounds result](goal). -/
-- @node: phiwPathWeight_bounds
lemma phiwPathWeight_bounds {T M : Nat} (t0 zeta C : ℝ) (m : ModelIndex T M)
    (hClass : PolicyListClass t0 zeta C m) (j : Fin M) (n : Nat)
    (s : JointState m.nX m.nH) (path : List (Bool × ℝ × JointState m.nX m.nH)) :
    0 ≤ phiwPathWeight m j n s path ∧
      phiwPathWeight m j n s path ≤ policyFactor zeta ^ n := by
  induction n generalizing s path with
  | zero => simp [phiwPathWeight]
  | succ n ih =>
    let step := path.getD 0 (false, (0 : ℝ), s)
    have hr := ratio_mem hClass.sequential_ignorability.1 (hClass.action_overlap j).1
      (hClass.action_overlap j).2 (Real.exp_nonneg zeta) s.1 step.1
    change 0 ≤ ratio m.Mx.b (m.Mx.E j) s.1 step.1 ∧
      ratio m.Mx.b (m.Mx.E j) s.1 step.1 ≤ policyFactor zeta at hr
    have ht := ih step.2.2 (path.drop 1)
    refine ⟨mul_nonneg hr.1 ht.1, ?_⟩
    change ratio m.Mx.b (m.Mx.E j) s.1 step.1 *
      phiwPathWeight m j n step.2.2 (path.drop 1) ≤ _
    simpa only [pow_succ, mul_comm] using
      mul_le_mul hr.2 ht.2 ht.1 (Real.exp_nonneg zeta)

/-- The bounded measurable path weight is square-integrable for free. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j), [the sample size](hyp:n),
[the state](hyp:s), and [the policy](hyp:p), this establishes
[the partial-history importance-weighted path weight membership lp result](goal). -/
-- @node: phiwPathWeight_memLp
lemma phiwPathWeight_memLp {T M : Nat} (t0 zeta C : ℝ) (m : ModelIndex T M)
    (hClass : PolicyListClass t0 zeta C m) (j : Fin M) (n : Nat)
    (s : JointState m.nX m.nH) (p : ℝ≥0∞) :
    MemLp (phiwPathWeight m j n s) p (segmentFrom m n s) := by
  have : IsProbabilityMeasure (segmentFrom m n s) :=
    segmentFrom_isProbability m hClass.sequential_ignorability.1 n s
  apply memLp_of_bounded (a := 0) (b := policyFactor zeta ^ n)
  · exact Filter.Eventually.of_forall (phiwPathWeight_bounds t0 zeta C m hClass j n s)
  · exact ((phiwPathWeight_measurable m j n).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable

/-- The ordinary likelihood-ratio product has expectation one under the generated behavior path,
by cancelling actions in chronological order. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j), [the sample size](hyp:n), and
[the state](hyp:s), this establishes
[the partial-history importance-weighted path weight integral one result](goal). -/
-- @node: phiwPathWeight_integral_one
lemma phiwPathWeight_integral_one {T M : Nat} (t0 zeta C : ℝ) (m : ModelIndex T M)
    (hClass : PolicyListClass t0 zeta C m) (j : Fin M) (n : Nat)
    (s : JointState m.nX m.nH) :
    (∫ path, phiwPathWeight m j n s path ∂segmentFrom m n s) = 1 := by
  induction n generalizing s with
  | zero => simp [phiwPathWeight, segmentFrom]
  | succ n ih =>
    have : IsProbabilityMeasure (segmentFrom m (n + 1) s) :=
      segmentFrom_isProbability m hClass.sequential_ignorability.1 (n + 1) s
    rw [segmentFrom_integral_succ m hClass.sequential_ignorability.1 n s _
      ((phiwPathWeight_memLp t0 zeta C m hClass j (n + 1) s 1).integrable le_rfl)]
    simp only [phiwPathWeight, List.getD_cons_zero, List.drop_succ_cons,
      List.drop_zero]
    simp_rw [integral_const_mul, ih, mul_one]
    exact phiw_segmentStep_ratio_mean_one t0 zeta C m hClass j s

/-- The generated path weight has second moment at most one factor of `L` per action. The
ordinary likelihood-ratio mean, rather than a supremum bound alone, removes half the exponent.
For [the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j), [the sample size](hyp:n), and
[the state](hyp:s), this establishes
[the partial-history importance-weighted path weight second moment bound result](goal). -/
-- @node: phiwPathWeight_second_moment_le
lemma phiwPathWeight_second_moment_le {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m)
    (j : Fin M) (n : Nat) (s : JointState m.nX m.nH) :
    (∫ path, (phiwPathWeight m j n s path) ^ 2 ∂segmentFrom m n s) ≤
      policyFactor zeta ^ n := by
  have : IsProbabilityMeasure (segmentFrom m n s) :=
    segmentFrom_isProbability m hClass.sequential_ignorability.1 n s
  have hi := phiwPathWeight_memLp t0 zeta C m hClass j n s 2
  have hsq : Integrable (fun path ↦ phiwPathWeight m j n s path *
      phiwPathWeight m j n s path) (segmentFrom m n s) := hi.integrable_mul hi
  calc
    _ ≤ ∫ path, policyFactor zeta ^ n * phiwPathWeight m j n s path
        ∂segmentFrom m n s := by
      apply integral_mono (by simpa only [pow_two] using hsq)
        ((hi.integrable (by norm_num)).const_mul _)
      intro path
      have h := phiwPathWeight_bounds t0 zeta C m hClass j n s path
      nlinarith [mul_nonneg h.1 (sub_nonneg.mpr h.2)]
    _ = policyFactor zeta ^ n := by
      rw [integral_const_mul, phiwPathWeight_integral_one t0 zeta C m hClass, mul_one]

/-- Weighted terminal reward as a function of a generated path. Clipping
makes the total function bounded even off the kernel's unit-reward support. -/
-- @node: phiwPathReward
noncomputable def phiwPathReward {T M : Nat} (m : ModelIndex T M) (j : Fin M) :
    Nat → JointState m.nX m.nH → List (Bool × ℝ × JointState m.nX m.nH) → ℝ
  | 0, s, path =>
      let step := path.getD 0 (false, 0, s)
      ratio m.Mx.b (m.Mx.E j) s.1 step.1 * clipUnit01 step.2.1
  | k + 1, s, path =>
      let step := path.getD 0 (false, 0, s)
      ratio m.Mx.b (m.Mx.E j) s.1 step.1 *
        phiwPathReward m j k step.2.2 (path.drop 1)

/-- The terminal weighted reward is measurable in its start and path. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the model](hyp:m),
[the candidate index](hyp:j), and [the history length](hyp:k), this establishes
[the partial-history importance-weighted path reward measurability result](goal). -/
@[fun_prop]
-- @node: phiwPathReward_measurable
lemma phiwPathReward_measurable {T M : Nat} (m : ModelIndex T M) (j : Fin M)
    (k : Nat) : Measurable (fun p : JointState m.nX m.nH ×
      List (Bool × ℝ × JointState m.nX m.nH) ↦ phiwPathReward m j k p.1 p.2) := by
  induction k with
  | zero =>
    apply measurable_from_prod_countable_right
    intro s
    have hg := segment_list_getD_measurable 0 (false, (0 : ℝ), s)
    have hr := (measurable_of_finite
      (fun a : Bool ↦ ratio m.Mx.b (m.Mx.E j) s.1 a)).comp hg.fst
    exact hr.mul ((measurable_const.max (measurable_const.min hg.snd.fst)))
  | succ k ih =>
    apply measurable_from_prod_countable_right
    intro s
    have hg := segment_list_getD_measurable 0 (false, (0 : ℝ), s)
    have hr := (measurable_of_finite
      (fun a : Bool ↦ ratio m.Mx.b (m.Mx.E j) s.1 a)).comp hg.fst
    exact hr.mul (ih.comp (hg.snd.snd.prodMk (segment_list_drop_measurable 1)))

/-- Clipping the terminal reward bounds the path score by `L^(k+1)`. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j), [the history length](hyp:k),
[the state](hyp:s), and [the path](hyp:path), this establishes
[the partial-history importance-weighted path reward bounds result](goal). -/
-- @node: phiwPathReward_bounds
lemma phiwPathReward_bounds {T M : Nat} (t0 zeta C : ℝ) (m : ModelIndex T M)
    (hClass : PolicyListClass t0 zeta C m) (j : Fin M) (k : Nat)
    (s : JointState m.nX m.nH) (path : List (Bool × ℝ × JointState m.nX m.nH)) :
    0 ≤ phiwPathReward m j k s path ∧
      phiwPathReward m j k s path ≤ policyFactor zeta ^ (k + 1) := by
  induction k generalizing s path with
  | zero =>
    let step := path.getD 0 (false, (0 : ℝ), s)
    have hr := ratio_mem hClass.sequential_ignorability.1 (hClass.action_overlap j).1
      (hClass.action_overlap j).2 (Real.exp_nonneg zeta) s.1 step.1
    change 0 ≤ ratio m.Mx.b (m.Mx.E j) s.1 step.1 ∧
      ratio m.Mx.b (m.Mx.E j) s.1 step.1 ≤ policyFactor zeta at hr
    have hc : 0 ≤ clipUnit01 step.2.1 ∧ clipUnit01 step.2.1 ≤ 1 := by
      unfold clipUnit01
      exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
    refine ⟨mul_nonneg hr.1 hc.1, ?_⟩
    change ratio m.Mx.b (m.Mx.E j) s.1 step.1 * clipUnit01 step.2.1 ≤ _
    simpa using mul_le_mul hr.2 hc.2 hc.1 (Real.exp_nonneg zeta)
  | succ k ih =>
    let step := path.getD 0 (false, (0 : ℝ), s)
    have hr := ratio_mem hClass.sequential_ignorability.1 (hClass.action_overlap j).1
      (hClass.action_overlap j).2 (Real.exp_nonneg zeta) s.1 step.1
    change 0 ≤ ratio m.Mx.b (m.Mx.E j) s.1 step.1 ∧
      ratio m.Mx.b (m.Mx.E j) s.1 step.1 ≤ policyFactor zeta at hr
    have ht := ih step.2.2 (path.drop 1)
    refine ⟨mul_nonneg hr.1 ht.1, ?_⟩
    change ratio m.Mx.b (m.Mx.E j) s.1 step.1 *
      phiwPathReward m j k step.2.2 (path.drop 1) ≤ _
    simpa only [pow_succ, mul_comm] using
      mul_le_mul hr.2 ht.2 ht.1 (Real.exp_nonneg zeta)

/-- The path reward is in every finite-measure Lp space, with no new assumption. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j), [the history length](hyp:k),
[the sample size](hyp:n), [the state](hyp:s), and [the policy](hyp:p), this establishes
[the partial-history importance-weighted path reward membership lp result](goal). -/
-- @node: phiwPathReward_memLp
lemma phiwPathReward_memLp {T M : Nat} (t0 zeta C : ℝ) (m : ModelIndex T M)
    (hClass : PolicyListClass t0 zeta C m) (j : Fin M) (k n : Nat)
    (s : JointState m.nX m.nH) (p : ℝ≥0∞) :
    MemLp (phiwPathReward m j k s) p (segmentFrom m n s) := by
  have : IsProbabilityMeasure (segmentFrom m n s) :=
    segmentFrom_isProbability m hClass.sequential_ignorability.1 n s
  apply memLp_of_bounded (a := 0) (b := policyFactor zeta ^ (k + 1))
  · exact Filter.Eventually.of_forall (phiwPathReward_bounds t0 zeta C m hClass j k s)
  · exact ((phiwPathReward_measurable m j k).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable

/-- Clipping changes no kernel reward integral because the construction already provides rewards
in the unit interval almost everywhere. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the model](hyp:m), [the state](hyp:s), and
[the action](hyp:a), this establishes
[the partial-history importance-weighted kernel clip reward integral result](goal). -/
-- @node: phiw_kernel_clip_reward_integral
lemma phiw_kernel_clip_reward_integral {T M : Nat} (m : ModelIndex T M)
    (s : JointState m.nX m.nH) (a : Bool) :
    (∫ ys, clipUnit01 ys.1 ∂m.Mx.K s a) = ∫ ys, ys.1 ∂m.Mx.K s a := by
  apply integral_congr_ae
  filter_upwards [phiw_kernel_reward_ae_unit m s a] with ys hy
  unfold clipUnit01
  rw [min_eq_right hy.2, max_eq_right hy.1]

/-- The weighted reward on the actual generated path has precisely the nested chronological
mean, the weighted portion of roadmap equation (1). For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j), [the history length](hyp:k),
and [the state](hyp:s), this establishes
[the partial-history importance-weighted path reward integral equality chronological result](goal). -/
-- @node: phiwPathReward_integral_eq_chronological
lemma phiwPathReward_integral_eq_chronological {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m)
    (j : Fin M) (k : Nat) (s : JointState m.nX m.nH) :
    (∫ path, phiwPathReward m j k s path ∂segmentFrom m (k + 1) s) =
      phiwChronologicalMean m j k s := by
  induction k generalizing s with
  | zero =>
    have : IsProbabilityMeasure (segmentFrom m 1 s) :=
      segmentFrom_isProbability m hClass.sequential_ignorability.1 1 s
    rw [segmentFrom_integral_succ m hClass.sequential_ignorability.1 0 s _
      ((phiwPathReward_memLp t0 zeta C m hClass j 0 1 s 1).integrable le_rfl)]
    simp only [phiwPathReward, List.getD_cons_zero, segmentFrom,
      integral_const, probReal_univ, one_smul, phiwChronologicalMean]
    have hm : Measurable (fun step : Bool × ℝ × JointState m.nX m.nH ↦
        ratio m.Mx.b (m.Mx.E j) s.1 step.1 * clipUnit01 step.2.1) := by
      have hr : Measurable (fun step : Bool × ℝ × JointState m.nX m.nH ↦
          ratio m.Mx.b (m.Mx.E j) s.1 step.1) := (measurable_of_finite
        (fun a : Bool ↦ ratio m.Mx.b (m.Mx.E j) s.1 a)).comp measurable_fst
      exact hr.mul (measurable_const.max (measurable_const.min measurable_snd.fst))
    have hi : ∀ a : Bool, Integrable (fun ys : ℝ × JointState m.nX m.nH ↦
        clipUnit01 ys.1) (m.Mx.K s a) := by
      intro a
      have : IsProbabilityMeasure (m.Mx.K s a) := m.kernel_law.1 s a
      apply Integrable.of_mem_Icc 0 1
        (measurable_const.max (measurable_const.min measurable_fst)).aemeasurable
      exact Filter.Eventually.of_forall fun ys ↦
        ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
    rw [phiw_segmentStep_integral m hClass.sequential_ignorability.1 s _ hm
      (fun a ↦ (hi a).const_mul (ratio m.Mx.b (m.Mx.E j) s.1 a))]
    simp_rw [integral_const_mul, phiw_kernel_clip_reward_integral]
    rw [phiw_segmentStep_integral m hClass.sequential_ignorability.1 s _
      (by
        have hr : Measurable (fun step : Bool × ℝ × JointState m.nX m.nH ↦
            ratio m.Mx.b (m.Mx.E j) s.1 step.1) := (measurable_of_finite
          (fun a : Bool ↦ ratio m.Mx.b (m.Mx.E j) s.1 a)).comp measurable_fst
        exact hr.mul measurable_snd.fst)
      (fun a ↦ (phiw_kernel_reward_integrable m s a).const_mul
        (ratio m.Mx.b (m.Mx.E j) s.1 a))]
    simp_rw [integral_const_mul]
  | succ k ih =>
    have : IsProbabilityMeasure (segmentFrom m (k + 2) s) :=
      segmentFrom_isProbability m hClass.sequential_ignorability.1 (k + 2) s
    rw [segmentFrom_integral_succ m hClass.sequential_ignorability.1 (k + 1) s _
      ((phiwPathReward_memLp t0 zeta C m hClass j (k + 1) (k + 2) s 1).integrable
        le_rfl)]
    simp only [phiwPathReward, List.getD_cons_zero, List.drop_succ_cons, List.drop_zero]
    simp_rw [integral_const_mul, ih]
    rfl

/-- A clipped terminal reward is dominated pointwise by the ordinary likelihood-ratio product
over its whole weighted window. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j), [the history length](hyp:k),
[the state](hyp:s), and [the path](hyp:path), this establishes
[the partial-history importance-weighted path reward bound path weight result](goal). -/
-- @node: phiwPathReward_le_pathWeight
lemma phiwPathReward_le_pathWeight {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m) (j : Fin M)
    (k : Nat) (s : JointState m.nX m.nH)
    (path : List (Bool × ℝ × JointState m.nX m.nH)) :
    phiwPathReward m j k s path ≤ phiwPathWeight m j (k + 1) s path := by
  induction k generalizing s path with
  | zero =>
    let step := path.getD 0 (false, (0 : ℝ), s)
    have hr := (ratio_mem hClass.sequential_ignorability.1 (hClass.action_overlap j).1
      (hClass.action_overlap j).2 (Real.exp_nonneg zeta) s.1 step.1).1
    change ratio m.Mx.b (m.Mx.E j) s.1 step.1 * clipUnit01 step.2.1 ≤
      ratio m.Mx.b (m.Mx.E j) s.1 step.1 * 1
    apply mul_le_mul_of_nonneg_left _ hr
    exact max_le (by norm_num) (min_le_left _ _)
  | succ k ih =>
    let step := path.getD 0 (false, (0 : ℝ), s)
    have hr := (ratio_mem hClass.sequential_ignorability.1 (hClass.action_overlap j).1
      (hClass.action_overlap j).2 (Real.exp_nonneg zeta) s.1 step.1).1
    exact mul_le_mul_of_nonneg_left (ih step.2.2 (path.drop 1)) hr

/-- Equation (6) holds for the weighted terminal reward under the generated path measure. The
proof uses chronological normalization of the ordinary likelihood ratio and the construction's
bounded rewards. For [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the model](hyp:m), [the class assumption](hyp:hClass),
[the candidate index](hyp:j), [the history length](hyp:k), and [the state](hyp:s), this
establishes
[the partial-history importance-weighted path reward second moment bound result](goal). -/
-- @node: phiwPathReward_second_moment_le
lemma phiwPathReward_second_moment_le {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m)
    (j : Fin M) (k : Nat) (s : JointState m.nX m.nH) :
    (∫ path, (phiwPathReward m j k s path) ^ 2 ∂segmentFrom m (k + 1) s) ≤
      policyFactor zeta ^ (k + 1) := by
  have : IsProbabilityMeasure (segmentFrom m (k + 1) s) :=
    segmentFrom_isProbability m hClass.sequential_ignorability.1 (k + 1) s
  have hi := phiwPathReward_memLp t0 zeta C m hClass j k (k + 1) s 2
  have hw := phiwPathWeight_memLp t0 zeta C m hClass j (k + 1) s 2
  have hsq : Integrable (fun path ↦ phiwPathReward m j k s path *
      phiwPathReward m j k s path) (segmentFrom m (k + 1) s) := hi.integrable_mul hi
  have hwsq : Integrable (fun path ↦ phiwPathWeight m j (k + 1) s path *
      phiwPathWeight m j (k + 1) s path) (segmentFrom m (k + 1) s) :=
    hw.integrable_mul hw
  calc
    _ ≤ ∫ path, (phiwPathWeight m j (k + 1) s path) ^ 2
        ∂segmentFrom m (k + 1) s := by
      apply integral_mono (by simpa only [pow_two] using hsq)
        (by simpa only [pow_two] using hwsq)
      intro path
      exact pow_le_pow_left₀ (phiwPathReward_bounds t0 zeta C m hClass j k s path).1
        (phiwPathReward_le_pathWeight t0 zeta C m hClass j k s path) 2
    _ ≤ policyFactor zeta ^ (k + 1) :=
      phiwPathWeight_second_moment_le t0 zeta C m hClass j (k + 1) s

/-- The actual path reward integral equals the target Markov iterate of its reward regression,
without a reward-successor independence assumption. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j), [the history length](hyp:k),
and [the state](hyp:s), this establishes
[the partial-history importance-weighted path reward integral equality target iterate result](goal). -/
-- @node: phiwPathReward_integral_eq_target_iterate
lemma phiwPathReward_integral_eq_target_iterate {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m)
    (j : Fin M) (k : Nat) (s : JointState m.nX m.nH) :
    (∫ path, phiwPathReward m j k s path ∂segmentFrom m (k + 1) s) =
      markovOperatorIter (listPolicyKernel m (m.Mx.E j)) k
        (listRewardRegression m (m.Mx.E j)) s := by
  rw [phiwPathReward_integral_eq_chronological t0 zeta C m hClass,
    phiwChronologicalMean_eq_markovOperatorIter t0 zeta C m hClass]

end CausalSmith.Stat.PomdpPolicyclassRegret
