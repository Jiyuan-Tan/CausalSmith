module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.BlockPathOverlap

/-!
# Arbitrary-start means of generated PHIW windows

Unused future tails leave a weighted reward's expectation unchanged. An
unweighted chronological prefix acts by the behavior backward operator,
proving the generated-path version of equation (1) of the block roadmap.
Averaging over arbitrary initial probability vectors gives the transient bias.
Proved marginal and cross-moment identities give the disjoint covariance
envelope in equation (9), without independence of reward and successor.
-/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open MeasureTheory
open CausalSmith.Stat.PomdpLatentOverlapMinimax
open Causalean.Mathlib.Probability.FiniteMarkovOscillation
open scoped BigOperators ENNReal

/-- Marginalizing one unweighted joint reward-successor step applies the behavior backward
operator to any finite-state test. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the model](hyp:m),
[the behavior policy assumption](hyp:hb), [the f](hyp:f), and [the state](hyp:s), this
establishes
[the partial-history importance-weighted segment step behavior successor result](goal). -/
-- @node: phiw_segmentStep_behavior_successor
lemma phiw_segmentStep_behavior_successor {T M : Nat} (m : ModelIndex T M)
    (hb : PolicyVector m.Mx.b) (f : JointState m.nX m.nH → ℝ)
    (s : JointState m.nX m.nH) :
    (∫ step, f step.2.2 ∂segmentStepLaw m s) =
      markovOperator (listPolicyKernel m m.Mx.b) f s := by
  rw [phiw_segmentStep_integral m hb s _ (by fun_prop)
    (fun a ↦ phiw_kernel_successor_integrable m s a f)]
  simp_rw [phiw_kernel_successor_integral]
  unfold markovOperator listPolicyKernel policyKernel
  simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/-- An unused generated future tail does not change the weighted window's chronological mean.
Rewards and successors are integrated jointly. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j), [the history length](hyp:k),
[the extra](hyp:extra), and [the state](hyp:s), this establishes
[the partial-history importance-weighted path reward integral horizon result](goal). -/
-- @node: phiwPathReward_integral_horizon
lemma phiwPathReward_integral_horizon {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m) (j : Fin M)
    (k extra : Nat) (s : JointState m.nX m.nH) :
    (∫ path, phiwPathReward m j k s path ∂segmentFrom m ((k + 1) + extra) s) =
      phiwChronologicalMean m j k s := by
  induction k generalizing s with
  | zero =>
    have : IsProbabilityMeasure (segmentFrom m (extra + 1) s) :=
      segmentFrom_isProbability m hClass.sequential_ignorability.1 _ s
    have : IsProbabilityMeasure (segmentFrom m 1 s) :=
      segmentFrom_isProbability m hClass.sequential_ignorability.1 _ s
    have hi := (phiwPathReward_memLp t0 zeta C m hClass j 0 (extra + 1) s 1).integrable le_rfl
    rw [show (0 + 1) + extra = extra + 1 by omega,
      segmentFrom_integral_succ m hClass.sequential_ignorability.1 extra s _ hi]
    have hp : ∀ step : Bool × ℝ × JointState m.nX m.nH,
        IsProbabilityMeasure (segmentFrom m extra step.2.2) :=
      fun step ↦ segmentFrom_isProbability m hClass.sequential_ignorability.1 extra step.2.2
    simp only [phiwPathReward, List.getD_cons_zero,
      integral_const, @probReal_univ _ _ _ (hp _), one_smul]
    have hbase := phiwPathReward_integral_eq_chronological t0 zeta C m hClass j 0 s
    rw [segmentFrom_integral_succ m hClass.sequential_ignorability.1 0 s _
      ((phiwPathReward_memLp t0 zeta C m hClass j 0 1 s 1).integrable le_rfl)] at hbase
    simpa [phiwPathReward, segmentFrom] using hbase
  | succ k ih =>
    have : IsProbabilityMeasure (segmentFrom m (((k + 1) + extra) + 1) s) :=
      segmentFrom_isProbability m hClass.sequential_ignorability.1 _ s
    have hi := (phiwPathReward_memLp t0 zeta C m hClass j (k + 1)
      (((k + 1) + extra) + 1) s 1).integrable le_rfl
    rw [show ((k + 1) + 1) + extra = ((k + 1) + extra) + 1 by omega,
      segmentFrom_integral_succ m hClass.sequential_ignorability.1 ((k + 1) + extra) s _ hi]
    simp only [phiwPathReward, List.getD_cons_zero, List.drop_succ_cons, List.drop_zero]
    simp_rw [integral_const_mul, ih]
    rfl

/-- Integrating an unweighted prefix propagates the starting state by the behavior operator
before evaluating the chronological target reward mean. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j), [the reward symbol](hyp:r),
[the history length](hyp:k), [the extra](hyp:extra), and [the state](hyp:s), this establishes
[the partial-history importance-weighted path shift reward integral equality behavior iterate result](goal). -/
-- @node: phiwPathShift_reward_integral_eq_behavior_iterate
lemma phiwPathShift_reward_integral_eq_behavior_iterate {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m) (j : Fin M)
    (r k extra : Nat) (s : JointState m.nX m.nH) :
    (∫ path, phiwPathShift (phiwPathReward m j k) r s path
      ∂segmentFrom m (r + ((k + 1) + extra)) s) =
      markovOperatorIter (listPolicyKernel m m.Mx.b) r
        (phiwChronologicalMean m j k) s := by
  induction r generalizing s with
  | zero =>
    simpa only [phiwPathShift, Nat.zero_add, markovOperatorIter] using
      phiwPathReward_integral_horizon t0 zeta C m hClass j k extra s
  | succ r ih =>
    have : IsProbabilityMeasure (segmentFrom m ((r + ((k + 1) + extra)) + 1) s) :=
      segmentFrom_isProbability m hClass.sequential_ignorability.1 _ s
    have hi := phiwPathShift_memLp m hClass.sequential_ignorability.1
      (phiwPathReward m j k) (phiwPathReward_measurable m j k)
      (policyFactor zeta ^ (k + 1)) (phiwPathReward_bounds t0 zeta C m hClass j k)
      (r + 1) ((r + ((k + 1) + extra)) + 1) s 1
    rw [show r + 1 + ((k + 1) + extra) = (r + ((k + 1) + extra)) + 1 by omega,
      segmentFrom_integral_succ m hClass.sequential_ignorability.1 _ s _
        (hi.integrable le_rfl)]
    simp only [phiwPathShift, List.getD_cons_zero, List.drop_succ_cons, List.drop_zero]
    simp_rw [ih]
    exact phiw_segmentStep_behavior_successor m hClass.sequential_ignorability.1 _ s

/-- Equation (1) for an arbitrary initial full-state distribution, under the actual generated
path measure and with any unused future tail. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j),
[the initial distribution](hyp:nu), [the reward symbol](hyp:r), [the history length](hyp:k), and
[the extra](hyp:extra), this establishes
[the partial-history importance-weighted path shift reward initial mean result](goal). -/
-- @node: phiwPathShift_reward_initial_mean
lemma phiwPathShift_reward_initial_mean {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m) (j : Fin M)
    (nu : JointState m.nX m.nH → ℝ) (r k extra : Nat) :
    (∑ s, nu s * ∫ path, phiwPathShift (phiwPathReward m j k) r s path
      ∂segmentFrom m (r + ((k + 1) + extra)) s) =
      ∑ s, Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.markovIterate
        (listPolicyKernel m m.Mx.b) nu r s * phiwChronologicalMean m j k s := by
  simp_rw [phiwPathShift_reward_integral_eq_behavior_iterate t0 zeta C m hClass]
  exact phiw_markovIterate_operator_duality _ _ _ r

/-- The arbitrary-start window bias holds for the generated behavior path, including the
unweighted prefix and every unused future suffix. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j),
[the initial distribution](hyp:nu), [the initial distribution assumption](hyp:hnu),
[the reward symbol](hyp:r), [the history length](hyp:k), and [the extra](hyp:extra), this
establishes
[the partial-history importance-weighted path shift reward initial bias result](goal). -/
-- @node: phiwPathShift_reward_initial_bias
lemma phiwPathShift_reward_initial_bias {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m) (j : Fin M)
    (nu : JointState m.nX m.nH → ℝ) (hnu : ProbabilityVector nu) (r k extra : Nat) :
    |(∑ s, nu s * ∫ path, phiwPathShift (phiwPathReward m j k) r s path
      ∂segmentFrom m (r + ((k + 1) + extra)) s) - policyValue m j| ≤
      mixingAlpha t0 ^ k * (overlapRadius C + mixingAlpha t0 ^ r) := by
  rw [phiwPathShift_reward_initial_mean t0 zeta C m hClass]
  exact phiwChronologicalMean_transient_bias t0 zeta C m hClass j nu hnu r k

/-- The future conditional mean stays in the unit interval, because its generated reward is
nonnegative and dominated by a normalized window ratio. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j), [the reward symbol](hyp:r),
[the history length](hyp:k), and [the state](hyp:s), this establishes
[the partial-history importance-weighted behavior future mean unit result](goal). -/
-- @node: phiw_behavior_future_mean_unit
lemma phiw_behavior_future_mean_unit {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m) (j : Fin M)
    (r k : Nat) (s : JointState m.nX m.nH) :
    0 ≤ markovOperatorIter (listPolicyKernel m m.Mx.b) r
        (phiwChronologicalMean m j k) s ∧
      markovOperatorIter (listPolicyKernel m m.Mx.b) r
        (phiwChronologicalMean m j k) s ≤ 1 := by
  rw [← phiwPathShift_reward_integral_eq_behavior_iterate t0 zeta C m hClass j r k 0 s]
  refine ⟨integral_nonneg (fun path ↦ ?_), ?_⟩
  · exact (phiwPathShift_bounds _ _ (phiwPathReward_bounds t0 zeta C m hClass j k)
      r s path).1
  · exact phiwPathShift_reward_integral_le_one t0 zeta C m hClass j r k 0 s

/-- Integrating a later disjoint window is the same as substituting its backward mean at the
successor of the earlier window. This cross-moment identity integrates each reward-successor
pair jointly. For [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the model](hyp:m), [the class assumption](hyp:hClass),
[the candidate index](hyp:j), [the action](hyp:a), [the behavior policy](hyp:b),
[the reward symbol](hyp:r), [the extra](hyp:extra), and [the state](hyp:s), this establishes
[the partial-history importance-weighted path reward disjoint cross identity result](goal). -/
-- @node: phiwPathReward_disjoint_cross_identity
lemma phiwPathReward_disjoint_cross_identity {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m) (j : Fin M)
    (a b r extra : Nat) (s : JointState m.nX m.nH) :
    (∫ path, phiwPathReward m j a s path *
      phiwPathShift (phiwPathReward m j b) (a + 1 + r) s path
      ∂segmentFrom m ((a + 1) + (r + ((b + 1) + extra))) s) =
    ∫ path, phiwPathReward m j a s path *
      phiwPathShift (fun u _ ↦ markovOperatorIter (listPolicyKernel m m.Mx.b) r
        (phiwChronologicalMean m j b) u) (a + 1) s path
      ∂segmentFrom m ((a + 1) + (r + ((b + 1) + extra))) s := by
  let f := markovOperatorIter (listPolicyKernel m m.Mx.b) r
    (phiwChronologicalMean m j b)
  have hf : Measurable (fun p : JointState m.nX m.nH ×
      List (Bool × ℝ × JointState m.nX m.nH) ↦ f p.1) := by fun_prop
  have hbound : ∀ u (_ : List (Bool × ℝ × JointState m.nX m.nH)),
      0 ≤ f u ∧ f u ≤ 1 := fun u _ ↦
    phiw_behavior_future_mean_unit t0 zeta C m hClass j r b u
  change (∫ path, phiwPathReward m j a s path *
      phiwPathShift (phiwPathReward m j b) (a + 1 + r) s path
      ∂segmentFrom m ((a + 1) + (r + ((b + 1) + extra))) s) =
    ∫ path, phiwPathReward m j a s path * phiwPathShift (fun u _ ↦ f u) (a + 1) s path
      ∂segmentFrom m ((a + 1) + (r + ((b + 1) + extra))) s
  induction a generalizing s with
  | zero =>
    let n := r + ((b + 1) + extra)
    have : IsProbabilityMeasure (segmentFrom m (n + 1) s) :=
      segmentFrom_isProbability m hClass.sequential_ignorability.1 _ s
    have hX := phiwPathReward_memLp t0 zeta C m hClass j 0 (n + 1) s 2
    have hY := phiwPathShift_memLp m hClass.sequential_ignorability.1
      (phiwPathReward m j b) (phiwPathReward_measurable m j b)
      (policyFactor zeta ^ (b + 1)) (phiwPathReward_bounds t0 zeta C m hClass j b)
      (r + 1) (n + 1) s 2
    have hF := phiwPathShift_memLp m hClass.sequential_ignorability.1
      (fun u _ ↦ f u) hf 1 hbound 1 (n + 1) s 2
    rw [show (0 + 1) + (r + ((b + 1) + extra)) = n + 1 by dsimp [n]; omega,
      show 0 + 1 + r = r + 1 by omega]
    rw [segmentFrom_integral_succ m hClass.sequential_ignorability.1 n s _
      (by
        convert hX.integrable_mul hY using 1
        ext path
        exact (Pi.mul_apply _ _ path).symm),
      segmentFrom_integral_succ m hClass.sequential_ignorability.1 n s _
      (by
        convert hX.integrable_mul hF using 1
        ext path
        exact (Pi.mul_apply _ _ path).symm)]
    simp only [phiwPathReward, phiwPathShift, List.getD_cons_zero,
      List.drop_succ_cons, List.drop_zero]
    simp_rw [integral_const_mul]
    congr 1
    funext step
    have : IsProbabilityMeasure (segmentFrom m n step.2.2) :=
      segmentFrom_isProbability m hClass.sequential_ignorability.1 _ _
    dsimp [n]
    rw [phiwPathShift_reward_integral_eq_behavior_iterate t0 zeta C m hClass]
    simp [f]
  | succ a ih =>
    let n := (a + 1) + (r + ((b + 1) + extra))
    have : IsProbabilityMeasure (segmentFrom m (n + 1) s) :=
      segmentFrom_isProbability m hClass.sequential_ignorability.1 _ s
    have hX := phiwPathReward_memLp t0 zeta C m hClass j (a + 1) (n + 1) s 2
    have hY := phiwPathShift_memLp m hClass.sequential_ignorability.1
      (phiwPathReward m j b) (phiwPathReward_measurable m j b)
      (policyFactor zeta ^ (b + 1)) (phiwPathReward_bounds t0 zeta C m hClass j b)
      ((a + 1 + r) + 1) (n + 1) s 2
    have hF := phiwPathShift_memLp m hClass.sequential_ignorability.1
      (fun u _ ↦ f u) hf 1 hbound ((a + 1) + 1) (n + 1) s 2
    rw [show ((a + 1) + 1) + (r + ((b + 1) + extra)) = n + 1 by dsimp [n]; omega,
      show (a + 1) + 1 + r = (a + 1 + r) + 1 by omega]
    rw [segmentFrom_integral_succ m hClass.sequential_ignorability.1 n s _
      (by
        convert hX.integrable_mul hY using 1
        ext path
        exact (Pi.mul_apply _ _ path).symm),
      segmentFrom_integral_succ m hClass.sequential_ignorability.1 n s _
      (by
        convert hX.integrable_mul hF using 1
        ext path
        exact (Pi.mul_apply _ _ path).symm)]
    simp only [phiwPathReward, phiwPathShift, List.getD_cons_zero,
      List.drop_succ_cons, List.drop_zero]
    simp_rw [mul_assoc, integral_const_mul]
    congr 1
    funext step
    exact congrArg (fun v ↦ ratio m.Mx.b (m.Mx.E j) s.1 step.1 * v) (ih step.2.2)

/-- The marginal counterpart of the disjoint cross-moment identity replaces a later weighted
reward by its backward mean at any earlier split point. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j), [the code dimension](hyp:d),
[the reward symbol](hyp:r), [the behavior policy](hyp:b), [the extra](hyp:extra), and
[the state](hyp:s), this establishes
[the partial-history importance-weighted path shift future mean identity result](goal). -/
-- @node: phiwPathShift_future_mean_identity
lemma phiwPathShift_future_mean_identity {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m) (j : Fin M)
    (d r b extra : Nat) (s : JointState m.nX m.nH) :
    (∫ path, phiwPathShift (phiwPathReward m j b) (d + r) s path
      ∂segmentFrom m (d + (r + ((b + 1) + extra))) s) =
    ∫ path, phiwPathShift (fun u _ ↦ markovOperatorIter (listPolicyKernel m m.Mx.b) r
      (phiwChronologicalMean m j b) u) d s path
      ∂segmentFrom m (d + (r + ((b + 1) + extra))) s := by
  let f := markovOperatorIter (listPolicyKernel m m.Mx.b) r (phiwChronologicalMean m j b)
  have hf : Measurable (fun p : JointState m.nX m.nH ×
      List (Bool × ℝ × JointState m.nX m.nH) ↦ f p.1) := by fun_prop
  have hbound : ∀ u (_ : List (Bool × ℝ × JointState m.nX m.nH)),
      0 ≤ f u ∧ f u ≤ 1 := fun u _ ↦
    phiw_behavior_future_mean_unit t0 zeta C m hClass j r b u
  change _ = ∫ path, phiwPathShift (fun u _ ↦ f u) d s path
    ∂segmentFrom m (d + (r + ((b + 1) + extra))) s
  induction d generalizing s with
  | zero =>
    have : IsProbabilityMeasure (segmentFrom m (r + ((b + 1) + extra)) s) :=
      segmentFrom_isProbability m hClass.sequential_ignorability.1 _ s
    simpa [phiwPathShift, f] using
      phiwPathShift_reward_integral_eq_behavior_iterate t0 zeta C m hClass j r b extra s
  | succ d ih =>
    let n := d + (r + ((b + 1) + extra))
    have : IsProbabilityMeasure (segmentFrom m (n + 1) s) :=
      segmentFrom_isProbability m hClass.sequential_ignorability.1 _ s
    have hY := phiwPathShift_memLp m hClass.sequential_ignorability.1
      (phiwPathReward m j b) (phiwPathReward_measurable m j b)
      (policyFactor zeta ^ (b + 1)) (phiwPathReward_bounds t0 zeta C m hClass j b)
      ((d + r) + 1) (n + 1) s 1
    have hF := phiwPathShift_memLp m hClass.sequential_ignorability.1
      (fun u _ ↦ f u) hf 1 hbound (d + 1) (n + 1) s 1
    rw [show d + 1 + (r + ((b + 1) + extra)) = n + 1 by dsimp [n]; omega,
      show d + 1 + r = (d + r) + 1 by omega,
      segmentFrom_integral_succ m hClass.sequential_ignorability.1 n s _
        (hY.integrable le_rfl),
      segmentFrom_integral_succ m hClass.sequential_ignorability.1 n s _
        (hF.integrable le_rfl)]
    simp only [phiwPathShift, List.getD_cons_zero, List.drop_succ_cons, List.drop_zero]
    congr 1
    funext step
    exact ih step.2.2

/-- A uniform bound around a fixed anchor survives a chronological shift. For
[the index subset](hyp:S), [the f](hyp:f), [the c](hyp:c), [the d](hyp:D),
[the f assumption](hyp:hf), [the code dimension](hyp:d), [the state](hyp:s), and
[the path](hyp:path), this establishes
[the partial-history importance-weighted path shift anchored bound result](goal). -/
-- @node: phiwPathShift_anchored_bound
lemma phiwPathShift_anchored_bound {S : Type*}
    (f : S → List (Bool × ℝ × S) → ℝ) (c D : ℝ)
    (hf : ∀ s path, |f s path - c| ≤ D) (d : Nat) (s : S)
    (path : List (Bool × ℝ × S)) :
    |phiwPathShift f d s path - c| ≤ D := by
  induction d generalizing s path with
  | zero => exact hf s path
  | succ d ih => exact ih (path.getD 0 (false, 0, s)).2.2 (path.drop 1)

/-- Equation (9) for two disjoint windows of a generated behavior path. The conditional future
identities are proved by chronological integration, so the reward and successor of the earlier
window may be dependent. For [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the model](hyp:m), [the class assumption](hyp:hClass),
[the candidate index](hyp:j), [the history length](hyp:k), [the reward symbol](hyp:r),
[the extra](hyp:extra), and [the state](hyp:s), this establishes
[the partial-history importance-weighted path reward disjoint covariance bound result](goal). -/
-- @node: phiwPathReward_disjoint_covariance_le
lemma phiwPathReward_disjoint_covariance_le {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m) (j : Fin M)
    (k r extra : Nat) (s : JointState m.nX m.nH) :
    |ProbabilityTheory.covariance (phiwPathReward m j k s)
      (phiwPathShift (phiwPathReward m j k) (k + 1 + r) s)
      (segmentFrom m ((k + 1) + (r + ((k + 1) + extra))) s)| ≤
      2 * mixingAlpha t0 ^ (k + r) := by
  let n := (k + 1) + (r + ((k + 1) + extra))
  let μ := segmentFrom m n s
  have : IsProbabilityMeasure μ :=
    segmentFrom_isProbability m hClass.sequential_ignorability.1 n s
  let f := markovOperatorIter (listPolicyKernel m m.Mx.b) r (phiwChronologicalMean m j k)
  let F := phiwPathShift (fun u _ ↦ f u) (k + 1) s
  have hX := phiwPathReward_memLp t0 zeta C m hClass j k n s 2
  have hY := phiwPathShift_memLp m hClass.sequential_ignorability.1
    (phiwPathReward m j k) (phiwPathReward_measurable m j k)
    (policyFactor zeta ^ (k + 1)) (phiwPathReward_bounds t0 zeta C m hClass j k)
    (k + 1 + r) n s 2
  have hF : MemLp F 2 μ := phiwPathShift_memLp m hClass.sequential_ignorability.1
    (fun u _ ↦ f u) (by fun_prop) 1
    (fun u _ ↦ phiw_behavior_future_mean_unit t0 zeta C m hClass j r k u)
    (k + 1) n s 2
  have hmean := phiwPathShift_future_mean_identity t0 zeta C m hClass j (k + 1) r k extra s
  have hcross := phiwPathReward_disjoint_cross_identity t0 zeta C m hClass j k k r extra s
  rw [phiw_covariance_eq_centered_future μ _ _ F hX hY hF hmean hcross (f s)]
  apply phiw_centered_pairing_le μ _ F hX hF
  · exact Filter.Eventually.of_forall fun path ↦
      (phiwPathReward_bounds t0 zeta C m hClass j k s path).1
  · have hh := phiwPathShift_reward_integral_le_one t0 zeta C m hClass j 0 k
      (r + ((k + 1) + extra)) s
    simpa only [phiwPathShift, Nat.zero_add] using hh
  · exact pow_nonneg (Real.exp_nonneg _) _
  · apply Filter.Eventually.of_forall
    intro path
    apply phiwPathShift_anchored_bound (fun u _ ↦ f u) (f s) _ _ (k + 1) s path
    intro u _
    have ho := phiw_disjoint_future_oscillation t0 zeta C m hClass j k
      (k + 1 + r) (by omega) u s
    simpa only [show k + 1 + r - k - 1 = r by omega,
      show k + 1 + r - 1 = k + r by omega] using ho

end CausalSmith.Stat.PomdpPolicyclassRegret
