module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.BlockBias
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.BlockChangeOfMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Chronological PHIW reward integrals

Structural iterated integrals cancel the target-to-behavior ratios one epoch
at a time and bound their second moments. Each step integrates the common
joint reward-successor law; no conditional independence of its outputs is used.
The separate identification with decoded segment coordinates is not asserted here.
-/

@[expose] public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open MeasureTheory
open CausalSmith.Stat.PomdpLatentOverlapMinimax
open Causalean.Mathlib.Probability.FiniteMarkovOscillation
open Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation
  (markovIterate markovStep)
open scoped BigOperators

/-- Every test of the finite successor state is integrable under the joint kernel. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the model](hyp:m),
[the state](hyp:s), [the action](hyp:a), and [the f](hyp:f), this establishes
[the partial-history importance-weighted kernel successor integrability result](goal). -/
-- @node: phiw_kernel_successor_integrable
lemma phiw_kernel_successor_integrable {T M : Nat} (m : ModelIndex T M)
    (s : JointState m.nX m.nH) (a : Bool) (f : JointState m.nX m.nH → ℝ) :
    Integrable (fun ys ↦ f ys.2) (m.Mx.K s a) := by
  have : IsProbabilityMeasure (m.Mx.K s a) := m.kernel_law.1 s a
  have hm : Measurable f := measurable_of_finite f
  have : IsProbabilityMeasure ((m.Mx.K s a).map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  exact (integrable_map_measure hm.aestronglyMeasurable measurable_snd.aemeasurable).1
    Integrable.of_finite

/-- Marginalizing the joint kernel gives the finite successor-state sum. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the model](hyp:m),
[the state](hyp:s), [the action](hyp:a), and [the f](hyp:f), this establishes
[the partial-history importance-weighted kernel successor integral result](goal). -/
-- @node: phiw_kernel_successor_integral
lemma phiw_kernel_successor_integral {T M : Nat} (m : ModelIndex T M)
    (s : JointState m.nX m.nH) (a : Bool) (f : JointState m.nX m.nH → ℝ) :
    (∫ ys, f ys.2 ∂m.Mx.K s a) =
      ∑ s', (m.Mx.K s a {ys | ys.2 = s'}).toReal * f s' := by
  have hm : Measurable f := measurable_of_finite f
  have : IsProbabilityMeasure (m.Mx.K s a) := m.kernel_law.1 s a
  have : IsProbabilityMeasure ((m.Mx.K s a).map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  rw [← integral_map measurable_snd.aemeasurable hm.aestronglyMeasurable,
    integral_fintype Integrable.of_finite]
  apply Finset.sum_congr rfl
  intro s' _
  rw [Measure.real, Measure.map_apply measurable_snd (measurableSet_singleton s')]
  rfl

/-- A weighted transition acts by the target backward Markov operator. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j), [the f](hyp:f), and
[the state](hyp:s), this establishes
[the partial-history importance-weighted segment step weighted successor result](goal). -/
-- @node: phiw_segmentStep_weighted_successor
lemma phiw_segmentStep_weighted_successor {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m)
    (j : Fin M) (f : JointState m.nX m.nH → ℝ) (s : JointState m.nX m.nH) :
    (∫ step, ratio m.Mx.b (m.Mx.E j) s.1 step.1 * f step.2.2
      ∂segmentStepLaw m s) = markovOperator (listPolicyKernel m (m.Mx.E j)) f s := by
  rw [phiw_segmentStep_changeOfMeasure m hClass.sequential_ignorability.1
    (m.Mx.E j) (hClass.action_overlap j).1 (policyFactor zeta)
    (hClass.action_overlap j).2 s (fun step ↦ f step.2.2)
    ((measurable_of_finite f).comp measurable_snd.snd)
    (fun a ↦ phiw_kernel_successor_integrable m s a f)]
  simp_rw [phiw_kernel_successor_integral]
  unfold markovOperator listPolicyKernel policyKernel
  simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/-- Nested integration of the `k+1` weighted actions ending in a reward. -/
-- @node: phiwChronologicalMean
noncomputable def phiwChronologicalMean {T M : Nat} (m : ModelIndex T M)
    (j : Fin M) : Nat → JointState m.nX m.nH → ℝ
  | 0, s => ∫ step, ratio m.Mx.b (m.Mx.E j) s.1 step.1 * step.2.1
      ∂segmentStepLaw m s
  | k + 1, s => ∫ step, ratio m.Mx.b (m.Mx.E j) s.1 step.1 *
      phiwChronologicalMean m j k step.2.2 ∂segmentStepLaw m s

/-- Chronological ratio cancellation leaves exactly `P_e^k g_e`. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j), and
[the history length](hyp:k), this establishes
[the partial-history importance-weighted chronological mean equality markov operator iter result](goal). -/
-- @node: phiwChronologicalMean_eq_markovOperatorIter
lemma phiwChronologicalMean_eq_markovOperatorIter {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m)
    (j : Fin M) (k : Nat) :
    phiwChronologicalMean m j k = markovOperatorIter (listPolicyKernel m (m.Mx.E j))
      k (listRewardRegression m (m.Mx.E j)) := by
  induction k with
  | zero =>
    funext s
    exact phiw_segmentStep_weighted_reward t0 zeta C m hClass j s
  | succ k ih =>
    funext s
    change (∫ step, ratio m.Mx.b (m.Mx.E j) s.1 step.1 *
      phiwChronologicalMean m j k step.2.2 ∂segmentStepLaw m s) = _
    rw [phiw_segmentStep_weighted_successor t0 zeta C m hClass, ih]
    rfl

/-- Forward state propagation and backward evaluation are dual finite sums. For
[the index subset](hyp:S), [the probability law](hyp:P), [the initial distribution](hyp:nu), and
[the f](hyp:f), this establishes
[the partial-history importance-weighted markov step operator duality result](goal). -/
-- @node: phiw_markovStep_operator_duality
lemma phiw_markovStep_operator_duality {S : Type*} [Fintype S]
    (P : S → S → ℝ) (nu f : S → ℝ) :
    (∑ s, nu s * markovOperator P f s) = ∑ s, markovStep nu P s * f s := by
  unfold markovOperator markovStep
  simp only [Matrix.vecMul, dotProduct]
  simp_rw [Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

/-- The duality persists through every structural iterate. For [the index subset](hyp:S),
[the probability law](hyp:P), [the initial distribution](hyp:nu), [the f](hyp:f), and
[the history length](hyp:k), this establishes
[the partial-history importance-weighted markov iterate operator duality result](goal). -/
-- @node: phiw_markovIterate_operator_duality
lemma phiw_markovIterate_operator_duality {S : Type*} [Fintype S]
    (P : S → S → ℝ) (nu f : S → ℝ) (k : Nat) :
    (∑ s, nu s * markovOperatorIter P k f s) =
      ∑ s, markovIterate P nu k s * f s := by
  induction k generalizing nu with
  | zero => rfl
  | succ k ih =>
    rw [markovOperatorIter_succ, phiw_markovStep_operator_duality, ih]
    congr 1
    funext s
    have hcomm : ∀ n, markovIterate P (markovStep nu P) n =
        markovStep (markovIterate P nu n) P := by
      intro n
      induction n with
      | zero => rfl
      | succ n ihn =>
        change markovStep (markovIterate P (markovStep nu P) n) P = _
        rw [ihn]
        rfl
    exact congrArg (fun v ↦ v s * f s) (hcomm k)

/-- The nested weighted reward mean, after an unweighted behavior prefix, has the
arbitrary-start pointwise bias in equation (4) of the roadmap. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j),
[the initial distribution](hyp:nu), [the initial distribution assumption](hyp:hnu),
[the reward symbol](hyp:r), and [the history length](hyp:k), this establishes
[the partial-history importance-weighted chronological mean transient bias result](goal). -/
-- @node: phiwChronologicalMean_transient_bias
lemma phiwChronologicalMean_transient_bias {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m) (j : Fin M)
    (nu : JointState m.nX m.nH → ℝ) (hnu : ProbabilityVector nu) (r k : Nat) :
    |(∑ s, markovIterate (listPolicyKernel m m.Mx.b) nu r s *
        phiwChronologicalMean m j k s) - policyValue m j| ≤
      mixingAlpha t0 ^ k * (overlapRadius C + mixingAlpha t0 ^ r) := by
  rw [phiwChronologicalMean_eq_markovOperatorIter t0 zeta C m hClass,
    phiw_markovIterate_operator_duality]
  exact phiw_list_transient_bias t0 zeta C m hClass j nu hnu r k

/-- Averaging the chronological means gives the bias rate in equation (5). For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j),
[the initial distribution](hyp:nu), [the initial distribution assumption](hyp:hnu),
[the effective sample size](hyp:N), [the history length](hyp:k), and
[the effective sample size assumption](hyp:hN), this establishes
[the partial-history importance-weighted chronological mean average bias result](goal). -/
-- @node: phiwChronologicalMean_average_bias
lemma phiwChronologicalMean_average_bias {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m) (j : Fin M)
    (nu : JointState m.nX m.nH → ℝ) (hnu : ProbabilityVector nu)
    (N k : Nat) (hN : 0 < N) :
    |(∑ r ∈ Finset.range N, ∑ s,
        markovIterate (listPolicyKernel m m.Mx.b) nu r s *
          phiwChronologicalMean m j k s) / (N : ℝ) - policyValue m j| ≤
      mixingAlpha t0 ^ k *
        (overlapRadius C + 1 / ((N : ℝ) * (1 - mixingAlpha t0))) := by
  simp_rw [phiwChronologicalMean_eq_markovOperatorIter t0 zeta C m hClass,
    phiw_markovIterate_operator_duality]
  exact phiw_list_average_transient_bias t0 zeta C m hClass j nu hnu N k hN

/-- A bounded future test costs at most one factor of `L` when a squared current ratio is
integrated. This is the inductive step for equation (6). For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j), [the f](hyp:f),
[the second event](hyp:B), [the f assumption](hyp:hf), [the state](hyp:s), and
[the second event assumption](hyp:hB), this establishes
[the partial-history importance-weighted segment step squared ratio bound result](goal). -/
-- @node: phiw_segmentStep_squared_ratio_bound
lemma phiw_segmentStep_squared_ratio_bound {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m) (j : Fin M)
    (f : JointState m.nX m.nH → ℝ) (B : ℝ) (hf : ∀ s, f s ≤ B)
    (s : JointState m.nX m.nH) (hB : 0 ≤ B) :
    (∫ step, (ratio m.Mx.b (m.Mx.E j) s.1 step.1) ^ 2 * f step.2.2
      ∂segmentStepLaw m s) ≤ policyFactor zeta * B := by
  have hm : Measurable (fun step : Bool × ℝ × JointState m.nX m.nH ↦
      (ratio m.Mx.b (m.Mx.E j) s.1 step.1) ^ 2 * f step.2.2) := by
    have hr : Measurable (fun step : Bool × ℝ × JointState m.nX m.nH ↦
        ratio m.Mx.b (m.Mx.E j) s.1 step.1) :=
      (measurable_of_finite (fun a : Bool ↦ ratio m.Mx.b (m.Mx.E j) s.1 a)).comp
        measurable_fst
    exact (hr.pow_const 2).mul ((measurable_of_finite f).comp measurable_snd.snd)
  rw [phiw_segmentStep_integral m hClass.sequential_ignorability.1 s _ hm
    (fun a ↦ (phiw_kernel_successor_integrable m s a f).const_mul
      ((ratio m.Mx.b (m.Mx.E j) s.1 a) ^ 2))]
  have hmean : ∀ a : Bool, (∫ ys, f ys.2 ∂m.Mx.K s a) ≤ B := by
    intro a
    have : IsProbabilityMeasure (m.Mx.K s a) := m.kernel_law.1 s a
    calc
      _ ≤ ∫ _ : ℝ × JointState m.nX m.nH, B ∂m.Mx.K s a :=
        integral_mono (phiw_kernel_successor_integrable m s a f)
          (integrable_const B) (fun ys ↦ hf ys.2)
      _ = B := by simp
  calc
    _ ≤ ∑ a : Bool, m.Mx.b s.1 a *
        ((ratio m.Mx.b (m.Mx.E j) s.1 a) ^ 2 * B) := by
      apply Finset.sum_le_sum
      intro a _
      dsimp only
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hmean a) (sq_nonneg _))
        ((hClass.sequential_ignorability.1 s.1).1 a)
    _ = (∑ a : Bool, m.Mx.b s.1 a *
        (ratio m.Mx.b (m.Mx.E j) s.1 a) ^ 2) * B := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ ≤ policyFactor zeta * B := mul_le_mul_of_nonneg_right
      (phiw_model_ratio_action_second_moment t0 zeta C m hClass j s.1) hB

/-- Nested joint-kernel integration of the square of a weighted terminal reward. -/
-- @node: phiwChronologicalSecondMoment
noncomputable def phiwChronologicalSecondMoment {T M : Nat} (m : ModelIndex T M)
    (j : Fin M) : Nat → JointState m.nX m.nH → ℝ
  | 0, s => ∫ step, (ratio m.Mx.b (m.Mx.E j) s.1 step.1 * step.2.1) ^ 2
      ∂segmentStepLaw m s
  | k + 1, s => ∫ step, (ratio m.Mx.b (m.Mx.E j) s.1 step.1) ^ 2 *
      phiwChronologicalSecondMoment m j k step.2.2 ∂segmentStepLaw m s

/-- Chronological integration of squared ratios proves the `L^(k+1)` second-moment bound
uniformly over every full-state starting point. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j), [the history length](hyp:k),
and [the state](hyp:s), this establishes
[the partial-history importance-weighted chronological second moment bound result](goal). -/
-- @node: phiwChronologicalSecondMoment_le
lemma phiwChronologicalSecondMoment_le {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m) (j : Fin M)
    (k : Nat) (s : JointState m.nX m.nH) :
    phiwChronologicalSecondMoment m j k s ≤ policyFactor zeta ^ (k + 1) := by
  induction k generalizing s with
  | zero =>
    simpa only [phiwChronologicalSecondMoment, Nat.zero_add, pow_one] using
      phiw_segmentStep_weighted_reward_second_moment t0 zeta C m hClass j s
  | succ k ih =>
    change (∫ step, (ratio m.Mx.b (m.Mx.E j) s.1 step.1) ^ 2 *
      phiwChronologicalSecondMoment m j k step.2.2 ∂segmentStepLaw m s) ≤ _
    have h := phiw_segmentStep_squared_ratio_bound t0 zeta C m hClass j
      (phiwChronologicalSecondMoment m j k) (policyFactor zeta ^ (k + 1)) ih s
      (pow_nonneg (Real.exp_nonneg _) _)
    simpa only [pow_succ, mul_comm] using h

/-- The same second-moment bound holds under any arbitrary probability-vector start. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j),
[the initial distribution](hyp:nu), [the initial distribution assumption](hyp:hnu), and
[the history length](hyp:k), this establishes
[the partial-history importance-weighted chronological second moment average bound result](goal). -/
-- @node: phiwChronologicalSecondMoment_average_le
lemma phiwChronologicalSecondMoment_average_le {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m) (j : Fin M)
    (nu : JointState m.nX m.nH → ℝ) (hnu : ProbabilityVector nu) (k : Nat) :
    (∑ s, nu s * phiwChronologicalSecondMoment m j k s) ≤
      policyFactor zeta ^ (k + 1) := by
  calc
    _ ≤ ∑ s, nu s * policyFactor zeta ^ (k + 1) := Finset.sum_le_sum fun s _ ↦
      mul_le_mul_of_nonneg_left
        (phiwChronologicalSecondMoment_le t0 zeta C m hClass j k s) (hnu.1 s)
    _ = policyFactor zeta ^ (k + 1) := by rw [← Finset.sum_mul, hnu.2, one_mul]

/-- For disjoint windows, the backward future reward mean has oscillation at most `alpha^(h-1)`,
the contraction estimate used in equation (9). For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j), [the history length](hyp:k),
[the stated assumption](hyp:h), and [the h assumption](hyp:hh), this establishes
[the partial-history importance-weighted disjoint future oscillation result](goal). -/
-- @node: phiw_disjoint_future_oscillation
lemma phiw_disjoint_future_oscillation {T M : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m)
    (j : Fin M) (k h : Nat) (hh : k < h) :
    OscillationBound (mixingAlpha t0 ^ (h - 1))
      (markovOperatorIter (listPolicyKernel m m.Mx.b) (h - k - 1)
        (phiwChronologicalMean m j k)) := by
  let : Nonempty (JointState m.nX m.nH) :=
    ⟨(⟨0, hClass.finite_state.1⟩, ⟨0, hClass.finite_state.2⟩)⟩
  have hg : OscillationBound 1 (listRewardRegression m (m.Mx.E j)) := by
    intro s s'
    have hs := phiw_list_reward_regression_unit m (m.Mx.E j) (hClass.action_overlap j).1 s
    have hs' := phiw_list_reward_regression_unit m (m.Mx.E j) (hClass.action_overlap j).1 s'
    exact abs_le.mpr ⟨by linarith [hs.1, hs'.2], by linarith [hs.2, hs'.1]⟩
  have he := oscillationBound_markovOperatorIter (listPolicyKernel m (m.Mx.E j))
    (policyKernel_probabilityVector m.Mx.toRawB m.kernel_law _
      (hClass.action_overlap j).1) (Real.exp_nonneg _)
    (hClass.uniform_contraction j _ (Or.inr rfl)) hg k
  rw [← phiwChronologicalMean_eq_markovOperatorIter t0 zeta C m hClass] at he
  have hb := oscillationBound_markovOperatorIter (listPolicyKernel m m.Mx.b)
    (policyKernel_probabilityVector m.Mx.toRawB m.kernel_law _
      hClass.sequential_ignorability.1) (Real.exp_nonneg _)
    (hClass.uniform_contraction j _ (Or.inl rfl)) he (h - k - 1)
  have hexp : h - k - 1 + k = h - 1 := by omega
  simpa only [mul_one, ← pow_add, hexp, mixingAlpha, neg_div] using hb

end CausalSmith.Stat.PomdpPolicyclassRegret
