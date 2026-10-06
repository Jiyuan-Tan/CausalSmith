module
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Basic
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.FiniteStationary
public import Causalean.Stat.Minimax.MinimaxValue
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Finite-list POMDP policy selection

The paper-local list experiment uses the finite trajectory carrier of the
latent-overlap POMDP development. Causalean's potential-outcome and estimation
systems describe a different abstraction; its real minimax operator is reused.
-/

@[expose] public section

set_option linter.style.longLine false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
open CausalSmith.Stat.PomdpLatentOverlapMinimax

/-- One common kernel, logging policy, and revealed list of target policies. -/
structure ListPomdpExperiment (T M nX nH : Nat) where
  K : JointState nX nH → Bool → Measure (Step nX nH) -- @realizes K(common reward-transition kernel)
  b : Policy nX -- @realizes b(known behavior policy)
  E : Fin M → Policy nX -- @realizes Elist(revealed finite policy list; probability vectors via ModelIndex.target_policies) @realizes theta_j(candidate policies constrained by target_policies)
  init : JointState nX nH → ℝ
  law : Measure (FullTrajectory T nX nH) -- @realizes X_t(observed state coordinate) @realizes H_t(latent state coordinate) @realizes S_t(joint path) @realizes A_t(binary action coordinate) @realizes Y_t(reward coordinate)
  law_isProbability : IsProbabilityMeasure law
/-- [the to raw object](goal) is defined from [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the observed-state count](hyp:nX),
[the hidden-state count](hyp:nH), [the list experiment](hyp:Mx), and
[the candidate index](hyp:j). -/

def ListPomdpExperiment.toRaw {T M nX nH : Nat}
    (Mx : ListPomdpExperiment T M nX nH) (j : Fin M) :
    RawPomdpExperiment T nX nH :=
  ⟨Mx.K, Mx.b, Mx.E j, Mx.init, Mx.law, Mx.law_isProbability⟩
/-- [the to raw b object](goal) is defined from [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the observed-state count](hyp:nX),
[the hidden-state count](hyp:nH), and [the list experiment](hyp:Mx). -/

def ListPomdpExperiment.toRawB {T M nX nH : Nat}
    (Mx : ListPomdpExperiment T M nX nH) :
    RawPomdpExperiment T nX nH :=
  ⟨Mx.K, Mx.b, Mx.b, Mx.init, Mx.law, Mx.law_isProbability⟩

/-- The kernel law and its reward range are semantics of the world, while the
seven model restrictions below remain separate assumption atoms. -/
structure ModelIndex (T M : Nat) where
  list_size : 2 ≤ M -- @realizes M(at least two supplied policies)
  nX : Nat -- @realizes Xspace(finite observed alphabet)
  nH : Nat -- @realizes Hspace(finite latent alphabet)
  Mx : ListPomdpExperiment T M nX nH -- @realizes T(trajectory length) @realizes M(list cardinality) @realizes Sspace(Xspace times Hspace) @realizes Aspace(Bool)
  target_policies : ∀ j, PolicyVector (Mx.E j) -- @realizes Elist(candidate probability policies) @realizes theta_j(probability-vector weights) @realizes Reg(candidate policies are probability vectors)
  kernel_law : PomdpKernelLaw Mx.toRawB -- @realizes K(common conditional law)
  reward_unit : ∀ s a, Mx.K s a ((Set.Icc (0 : ℝ) 1)ᶜ ×ˢ Set.univ) = 0 -- @realizes Yspace(kernel rewards in [0,1]) @realizes Y_t(reward range)
/-- [the list policy kernel quantity](goal) is defined from [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the model](hyp:m), and [the policy](hyp:p). -/

noncomputable def listPolicyKernel {T M : Nat} (m : ModelIndex T M)
    (p : Policy m.nX) : JointState m.nX m.nH → JointState m.nX m.nH → ℝ :=
  policyKernel m.Mx.toRawB p
  -- @realizes P_p(reward-marginalized policy-induced state kernel)
/-- [the list stationary law quantity](goal) is defined from [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the model](hyp:m), and [the policy](hyp:p). -/

noncomputable def listStationaryLaw {T M : Nat} (m : ModelIndex T M)
    (p : Policy m.nX) : JointState m.nX m.nH → ℝ :=
  stationaryLaw (listPolicyKernel m p)
  -- @realizes d_p(stationary probability vector when the contraction atom holds)
/-- [the list reward regression quantity](goal) is defined from [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the model](hyp:m), [the policy](hyp:p), and
[the state](hyp:s). -/

noncomputable def listRewardRegression {T M : Nat} (m : ModelIndex T M)
    (p : Policy m.nX) (s : JointState m.nX m.nH) : ℝ :=
  ∑ a : Bool, p s.1 a * ∫ y, y.1 ∂(m.Mx.K s a)
  -- @realizes g_p(policy reward regression)
/-- [the list information ratio quantity](goal) is defined from [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the time horizon assumption](hyp:_hT), and
[the candidate-policy count assumption](hyp:_hM). -/

noncomputable def listInformationRatio (T M : Nat) (_hT : 1 ≤ T) (_hM : 2 ≤ M) : ℝ :=
  Real.log (M : ℝ) / T
  -- @realizes u(log M / T on T ≥ 1 and M ≥ 2)

/-- The information ratio is strictly positive on the paper domain. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the time horizon assumption](hyp:hT), and [the candidate-policy count assumption](hyp:hM), this
establishes [the list information ratio positivity result](goal). -/
-- keep: public range certificate for the realized rate coordinate `u = log M / T`
lemma listInformationRatio_pos (T M : Nat) (hT : 1 ≤ T) (hM : 2 ≤ M) :
    0 < listInformationRatio T M hT hM := by
  exact div_pos (Real.log_pos (by exact_mod_cast (show 1 < M by omega)))
    (by exact_mod_cast (show 0 < T by omega))
  -- @realizes u(strict positivity on the declared domain)

-- @env: S1
variable {T M : Nat} (t0 zeta C : ℝ) (m : ModelIndex T M)

-- @node: ass:finite-state
/-- [the finite state predicate](goal) is defined from [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), and [the model](hyp:m). -/
def FiniteState : Prop := 0 < m.nX ∧ 0 < m.nH
  -- @realizes Xspace(nonempty finite) @realizes Hspace(nonempty finite)

-- @node: ass:sequential-ignorability
/-- [the list sequential ignorability predicate](goal) is defined from
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), and [the model](hyp:m). -/
def ListSequentialIgnorability : Prop := SequentialIgnorability m.Mx.toRawB
  -- @realizes b(action law given observed state)

-- @node: ass:stationary-start
/-- [the list stationary start predicate](goal) is defined from [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), and [the model](hyp:m). -/
def ListStationaryStart : Prop := StationaryStart m.Mx.toRawB
  -- @realizes d_p(behavior stationary initialization)

-- @node: ass:uniform-contraction
/-- [the list uniform contraction predicate](goal) is defined from [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the model](hyp:m), and
[the contraction factor](hyp:alpha). -/
def ListUniformContraction (alpha : ℝ) : Prop :=
  ∀ j : Fin M, UniformContraction alpha (m.Mx.toRaw j)
  -- @realizes alpha(contraction factor) @realizes P_p(policy-induced kernel)

-- @node: ass:action-overlap
/-- [the list action overlap predicate](goal) is defined from [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the model](hyp:m), and [the action-overlap factor](hyp:L). -/
def ListActionOverlap (L : ℝ) : Prop :=
  ∀ j : Fin M, PolicyOverlap L (m.Mx.toRaw j)
  -- @realizes L(action-ratio envelope) @realizes Elist(target policies)

-- @node: ass:latent-stationary-overlap
/-- [the list latent stationary overlap predicate](goal) is defined from
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the model](hyp:m), and
[the latent-overlap radius](hyp:C). -/
def ListLatentStationaryOverlap (C : ℝ) : Prop :=
  1 ≤ C ∧ -- @realizes C(radius at least one even for an empty index type)
    ∀ j : Fin M, LatentStationaryOverlap C (m.Mx.toRaw j)

-- @node: ass:supplied-list
/-- [the supplied list predicate](goal) is defined from [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), and [the model](hyp:m). -/
def SuppliedList : Prop :=
  Function.Injective m.Mx.E
  -- @realizes Elist(fixed revealed list of distinct target policies)

-- @node: def:model-class
/-- The policy list class structure packages the required fields for [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), and
[the model](hyp:m). -/
structure PolicyListClass : Prop where
  t0_pos : 0 < t0 -- @realizes t0(positive mixing scale) @realizes alpha(exp(-1/t0) in (0,1))
  zeta_pos : 0 < zeta -- @realizes zeta(positive log policy-overlap bound)
  C_ge_one : 1 ≤ C -- @realizes C(radius at least one)
  finite_state : FiniteState m
  sequential_ignorability : ListSequentialIgnorability m
  stationary_start : ListStationaryStart m
  uniform_contraction : ListUniformContraction m (mixingAlpha t0) -- @realizes alpha(exp(-1/t0))
  action_overlap : ListActionOverlap m (policyFactor zeta) -- @realizes L(exp(zeta))
  latent_stationary_overlap : ListLatentStationaryOverlap m C -- @realizes ModelClass(seven-atom class)
  supplied_list : SuppliedList m -- @realizes ModelClass(fixed revealed list of pairwise-distinct policies)

-- @node: def:hw-aligned-model-class
/-- The Hu–Wager policy-list class structure packages the required fields for
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), and [the model](hyp:m). -/
structure HWPolicyListClass : Prop where
  t0_pos : 0 < t0 -- @realizes t0(positive mixing scale) @realizes alpha(exp(-1/t0) in (0,1))
  zeta_pos : 0 < zeta -- @realizes zeta(positive log policy-overlap bound)
  finite_state : FiniteState m
  sequential_ignorability : ListSequentialIgnorability m
  stationary_start : ListStationaryStart m
  uniform_contraction : ListUniformContraction m (mixingAlpha t0)
  action_overlap : ListActionOverlap m (policyFactor zeta)
  supplied_list : SuppliedList m -- @realizes ModelClassHW(fixed revealed list of pairwise-distinct policies)
/-- For the time horizon, the candidate-policy count,
the mixing scale, the policy-overlap scale,
the latent-overlap radius, the model, and [the stated assumption](hyp:h), this
establishes [the to Hu–Wager result](goal). -/

lemma PolicyListClass.toHW (h : PolicyListClass t0 zeta C m) :
    HWPolicyListClass t0 zeta m := by
  exact ⟨h.t0_pos, h.zeta_pos, h.finite_state, h.sequential_ignorability,
    h.stationary_start, h.uniform_contraction, h.action_overlap, h.supplied_list⟩

-- @env: S2
variable (sel : (nX : Nat) → Policy nX → (Fin M → Policy nX) → ObsView T nX → Fin M)

/-- Observable selectors take only the revealed alphabet, policies, and observed word. -/
def ObservableSelector (T M : Nat) : Type :=
  {sel : (nX : Nat) → Policy nX → (Fin M → Policy nX) → ObsView T nX → Fin M //
    ∀ nX b E, Measurable (sel nX b E)}
  -- @realizes jhat(measurable observable policy selector)

-- @node: def:value-regret
/-- [the policy value quantity](goal) is defined from [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the model](hyp:m), and [the candidate index](hyp:j). -/
noncomputable def policyValue (m : ModelIndex T M) (j : Fin M) : ℝ :=
  targetValue (m.Mx.toRaw j)
  -- @realizes theta_j(stationary value of candidate j) @realizes g_p(policy reward regression through targetValue) @realizes d_p(policy stationary law through targetValue)
/-- [the simple regret quantity](goal) is defined from [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the model](hyp:m), and [the candidate index](hyp:j). -/

noncomputable def simpleRegret (m : ModelIndex T M) (j : Fin M) : ℝ :=
  (⨆ i : Fin M, policyValue m i) - policyValue m j
  -- @realizes Reg(best candidate value minus selected value)

/-- A candidate's probability policy and the common finite kernel supply a stationary
probability law. No stationarity fact is assumed as a model field. For
the time horizon, the candidate-policy count, [the model](hyp:m), and
[the candidate index](hyp:j), this establishes [the list target stationary result](goal). -/
-- @node: listTargetStationary
lemma listTargetStationary (m : ModelIndex T M) (j : Fin M) :
    IsStationary (listPolicyKernel m (m.Mx.E j))
      (listStationaryLaw m (m.Mx.E j)) := by
  let : IsProbabilityMeasure m.Mx.law := m.Mx.law_isProbability
  let : Nonempty (FullTrajectory T m.nX m.nH) :=
    nonempty_of_isProbabilityMeasure m.Mx.law
  let : Nonempty (JointState m.nX m.nH) :=
    ⟨(Classical.choice (inferInstance : Nonempty (FullTrajectory T m.nX m.nH))).1 0⟩
  apply stationaryLaw_isStationary_of_exists
  exact finite_stochastic_stationary_exists _ (fun s ↦
    policyKernel_probabilityVector m.Mx.toRawB m.kernel_law (m.Mx.E j)
      (m.target_policies j) s)
  -- @realizes d_p(candidate stationary probability law) @realizes theta_j(stationary weights are probability vectors) @realizes Reg(stationary candidate weights)

/-- Every common-kernel reward mean lies in the unit interval, including states unreachable from
the recorded stationary trajectory. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the model](hyp:m), [the state](hyp:s), and
[the action](hyp:a), this establishes
[the partial-history importance-weighted kernel reward mean unit result](goal). -/
-- @node: phiw_kernel_reward_mean_unit
lemma phiw_kernel_reward_mean_unit {T M : Nat} (m : ModelIndex T M)
    (s : JointState m.nX m.nH) (a : Bool) :
    (∫ y, y.1 ∂(m.Mx.K s a)) ∈ Set.Icc (0 : ℝ) 1 := by
  have : IsProbabilityMeasure (m.Mx.K s a) := m.kernel_law.1 s a
  have hy : ∀ᵐ y ∂(m.Mx.K s a), y.1 ∈ Set.Icc (0 : ℝ) 1 := by
    rw [ae_iff]
    convert m.reward_unit s a using 1
    congr 1
    ext y
    simp
  constructor
  · apply integral_nonneg_of_ae
    filter_upwards [hy] with y hy
    exact hy.1
  · have hnorm : ∀ᵐ y ∂(m.Mx.K s a), ‖y.1‖ ≤ (1 : ℝ) := by
      filter_upwards [hy] with y hy
      simpa [Real.norm_eq_abs, abs_of_nonneg hy.1] using hy.2
    have h := norm_integral_le_of_norm_le_const hnorm
    simp only [Real.norm_eq_abs, probReal_univ, mul_one] at h
    exact (le_abs_self _).trans h

/-- A probability policy averages the common kernel's unit-interval rewards. For
the time horizon, the candidate-policy count, [the model](hyp:m),
[the candidate index](hyp:j), and [the state](hyp:s), this establishes
[the list target reward regression membership unit result](goal). -/
-- @node: listTargetRewardRegression_mem_unit
lemma listTargetRewardRegression_mem_unit (m : ModelIndex T M) (j : Fin M)
    (s : JointState m.nX m.nH) :
    listRewardRegression m (m.Mx.E j) s ∈ Set.Icc (0 : ℝ) 1 := by
  have hp := m.target_policies j s.1
  constructor
  · exact Finset.sum_nonneg fun a _ ↦
      mul_nonneg (hp.1 a) (phiw_kernel_reward_mean_unit m s a).1
  · calc
      _ ≤ ∑ a : Bool, m.Mx.E j s.1 a * 1 := Finset.sum_le_sum fun a _ ↦
        mul_le_mul_of_nonneg_left (phiw_kernel_reward_mean_unit m s a).2 (hp.1 a)
      _ = 1 := by simpa using hp.2
  -- @realizes g_p(candidate regression in [0,1]) @realizes theta_j(unit-interval reward regression)

/-- Stationary candidate values lie in the reward interval. For the time horizon,
the candidate-policy count, [the model](hyp:m), and [the candidate index](hyp:j), this
establishes [the policy value membership unit result](goal). -/
lemma policyValue_mem_unit (m : ModelIndex T M) (j : Fin M) :
    policyValue m j ∈ Set.Icc (0 : ℝ) 1 := by
  have hd := (listTargetStationary m j).1
  have hg := listTargetRewardRegression_mem_unit m j
  change (∑ s, listStationaryLaw m (m.Mx.E j) s *
    listRewardRegression m (m.Mx.E j) s) ∈ Set.Icc (0 : ℝ) 1
  constructor
  · exact Finset.sum_nonneg (fun s _ ↦ mul_nonneg (hd.1 s) (hg s).1)
  · calc
      _ ≤ ∑ s, listStationaryLaw m (m.Mx.E j) s * 1 :=
        Finset.sum_le_sum (fun s _ ↦ mul_le_mul_of_nonneg_left (hg s).2 (hd.1 s))
      _ = 1 := by simpa only [mul_one] using hd.2
  -- @realizes theta_j(stationary policy value in [0,1]) @realizes Reg(candidate values in [0,1])

/-- The existing supremum-minus-selected formula lies in the unit interval. For
the time horizon, the candidate-policy count, [the model](hyp:m), and
[the candidate index](hyp:j), this establishes [the simple regret membership unit result](goal). -/
-- keep: public range certificate for the realized simple-regret symbol `Reg`
lemma simpleRegret_mem_unit (m : ModelIndex T M) (j : Fin M) :
    simpleRegret m j ∈ Set.Icc (0 : ℝ) 1 := by
  let : Nonempty (Fin M) := ⟨j⟩
  have hbest : (⨆ i : Fin M, policyValue m i) ≤ 1 :=
    ciSup_le (fun i ↦ (policyValue_mem_unit m i).2)
  constructor
  · exact sub_nonneg.mpr (le_ciSup (Finite.bddAbove_range _) j)
  · have hj := (policyValue_mem_unit m j).1
    unfold simpleRegret
    linarith
  -- @realizes Reg(supremum minus selected value in [0,1])
/-- [the expected regret quantity](goal) is defined from [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the observable selector](hyp:sel), and [the model](hyp:m). -/

noncomputable def expectedRegret (sel : ObservableSelector T M) (m : ModelIndex T M) : ℝ :=
  ∫ w, simpleRegret m (sel.1 m.nX m.Mx.b m.Mx.E w) ∂ obsLaw m.Mx.toRawB

-- @node: def:minimax-risk
/-- [the minimax regret quantity](goal) is defined from [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), and [the latent-overlap radius](hyp:C). -/
noncomputable def minimaxRegret (T M : Nat) (t0 zeta C : ℝ) : ℝ :=
  Causalean.Stat.minimaxValueReal
    (fun (sel : ObservableSelector T M)
      (m : {m : ModelIndex T M // PolicyListClass t0 zeta C m}) ↦
      expectedRegret sel m.1)
  -- @realizes Qrisk(infimum over selectors and supremum over fixed lists of pairwise-distinct policies)

-- @node: def:hw-minimax-risk
/-- [the hu–wager minimax regret quantity](goal) is defined from [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the mixing scale](hyp:t0), and
[the policy-overlap scale](hyp:zeta). -/
noncomputable def hwMinimaxRegret (T M : Nat) (t0 zeta : ℝ) : ℝ :=
  Causalean.Stat.minimaxValueReal
    (fun (sel : ObservableSelector T M)
      (m : {m : ModelIndex T M // HWPolicyListClass t0 zeta m}) ↦
      expectedRegret sel m.1)
  -- @realizes QriskHW(broader-class minimax expected regret)

/-- Smallest odd number at least three and at least log(2M). -/
noncomputable def numBlocks (M : Nat) : Nat :=
  let b := max 3 (Nat.ceil (Real.log (2 * M : ℝ)))
  if b % 2 = 1 then b else b + 1
  -- @realizes B(smallest odd block count)
/-- [the block len quantity](goal) is defined from [the time horizon](hyp:T) and
[the candidate-policy count](hyp:M). -/

noncomputable def blockLen (T M : Nat) : Nat := T / numBlocks M
  -- @realizes n(floor T/B)

/-- Under the standing positive mixing and overlap scales, the hidden-memory exponent lies in
its declared open unit interval. For [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the mixing scale assumption](hyp:ht0), and
[the policy-overlap scale assumption](hyp:hzeta), this establishes
[the rate exponent membership ioo result](goal). -/
-- keep: semantic range certificate for the core beta symbol's @realizes crosswalk
lemma rateExponent_mem_Ioo (t0 zeta : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) :
    rateExponent t0 zeta ∈ Set.Ioo (0 : ℝ) 1 := by
  -- @realizes beta(range (0,1) under t0 > 0 and zeta > 0)
  have hprod : 0 < t0 * zeta := mul_pos ht0 hzeta
  have hden : 0 < 2 + t0 * zeta := by linarith
  unfold rateExponent
  exact ⟨div_pos (by norm_num) hden, (div_lt_one hden).2 (by linarith)⟩

/-- Under the standing occupancy-envelope condition, the normalized radius lies in its declared
half-open unit interval. For [the latent-overlap radius](hyp:C) and
[the latent-overlap radius assumption](hyp:hC), this establishes
[the overlap radius membership ico result](goal). -/
-- keep: semantic range certificate for the core q symbol's @realizes crosswalk
lemma overlapRadius_mem_Ico (C : ℝ) (hC : 1 ≤ C) :
    overlapRadius C ∈ Set.Ico (0 : ℝ) 1 := by
  -- @realizes q(range [0,1) under C ≥ 1)
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  unfold overlapRadius
  exact ⟨div_nonneg (sub_nonneg.mpr hC) hCpos.le,
    (div_lt_one hCpos).2 (by linarith)⟩

/-- Radius-adaptive depth, shared by all candidates. -/
noncomputable def adaptiveDepth (n : Nat) (t0 zeta C : ℝ) : Nat :=
  if (n : ℝ) * overlapRadius C ^ 2 ≤ 1 then 0 else
    min (n / 2) (Int.toNat ⌊Real.log ((n : ℝ) * overlapRadius C ^ 2) /
      (2 * Real.log (1 / mixingAlpha t0) + Real.log (policyFactor zeta))⌋)
  -- @realizes k(common partial-history depth) @realizes q(normalized overlap radius)
/-- [the conservative depth quantity](goal) is defined from [the sample size](hyp:n),
[the mixing scale](hyp:t0), and [the policy-overlap scale](hyp:zeta). -/

noncomputable def conservativeDepth (n : Nat) (t0 zeta : ℝ) : Nat :=
  min (n / 2) (Int.toNat ⌊Real.log n /
    (2 * Real.log (1 / mixingAlpha t0) + Real.log (policyFactor zeta))⌋)

/-- Reindex a common block from zero, using the sibling PHIW score. -/
noncomputable def blockScore (T M nX : Nat) (k : Nat) (b e : Policy nX)
    (ell : Fin (numBlocks M)) (w : ObsView T nX) : ℝ :=
  let n := blockLen T M
  let N := n - k
  ((N : ℝ)⁻¹) *
    ∑ t ∈ Finset.range n |>.filter (fun t ↦ k ≤ t),
      if ht : ell.val * n + t < T then
        (w ⟨ell.val * n + t, ht⟩).2.2 *
          ∏ r ∈ (Finset.range n).filter (fun r ↦ r ≤ t ∧ t - r ≤ k),
            if hr : ell.val * n + r < T then
              ratio b e (w ⟨ell.val * n + r, hr⟩).1
                (w ⟨ell.val * n + r, hr⟩).2.1 else 0
      else 0
  -- @realizes N(usable observations per block) @realizes Z_jt(partial-history weighted reward) @realizes V_jl(normalized block score)

/-- Median as a finite max of subset minima. For odd block counts this is the
middle order statistic. -/
noncomputable def blockMedian (T M nX : Nat) (k : Nat) (b e : Policy nX)
    (w : ObsView T nX) : ℝ :=
  let B := numBlocks M
  ⨆ S : {S : Finset (Fin B) // S.card = (B + 1) / 2},
    ⨅ ell : S.1, blockScore T M nX k b e ell.1 w
/-- [the clip unit01 quantity](goal) is defined from [the observed state](hyp:x). -/

noncomputable def clipUnit01 (x : ℝ) : ℝ := max 0 (min 1 x)
/-- [the candidate estimate quantity](goal) is defined from [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the observed-state count](hyp:nX),
[the history length](hyp:k), [the behavior policy](hyp:b), [the candidate-policy list](hyp:E),
[the observed word](hyp:w), and [the candidate index](hyp:j). -/

noncomputable def candidateEstimate (T M nX : Nat) (k : Nat)
    (b : Policy nX) (E : Fin M → Policy nX) (w : ObsView T nX) (j : Fin M) : ℝ :=
  clipUnit01 (blockMedian T M nX k b (E j) w)
  -- @realizes theta_hat_j(clipped median block score)

/-- Smallest maximizer of the finite candidate scores. For [the candidate-policy count](hyp:M),
[the candidate-policy count assumption](hyp:hM), and [the candidate score](hyp:score), this
establishes [the maximizer nonempty result](goal). -/
-- @node: maximizer_nonempty
lemma maximizer_nonempty (M : Nat) (hM : 0 < M) (score : Fin M → ℝ) :
    (Finset.univ.filter (fun j : Fin M ↦ ∀ i : Fin M, score i ≤ score j)).Nonempty := by
  classical
  obtain ⟨j, hj, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin M)) score
      ⟨⟨0, hM⟩, Finset.mem_univ _⟩
  exact ⟨j, Finset.mem_filter.mpr ⟨hj, fun i ↦ hmax i (Finset.mem_univ i)⟩⟩
/-- [the smallest maximizer object](goal) is defined from [the candidate-policy count](hyp:M),
[the candidate-policy count assumption](hyp:hM), and [the candidate score](hyp:score). -/

noncomputable def smallestMaximizer (M : Nat) (hM : 0 < M)
    (score : Fin M → ℝ) : Fin M :=
  (Finset.univ.filter (fun j : Fin M ↦ ∀ i : Fin M, score i ≤ score j)).min'
    (maximizer_nonempty M hM score)
  -- @realizes jhat_star(smallest maximizing candidate)
/-- [the block selector raw object](goal) is defined from [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the candidate-policy count assumption](hyp:hM),
[the history depth](hyp:depth), [the observed-state count](hyp:nX),
[the behavior policy](hyp:b), [the candidate-policy list](hyp:E), and
[the observed word](hyp:w). -/

noncomputable def blockSelectorRaw (T M : Nat) (hM : 0 < M) (depth : Nat → Nat)
    (nX : Nat) (b : Policy nX) (E : Fin M → Policy nX)
    (w : ObsView T nX) : Fin M :=
  if blockLen T M < 4 then ⟨0, hM⟩ else
    smallestMaximizer M hM (candidateEstimate T M nX (depth (blockLen T M)) b E w)

-- @node: blockScore_measurable
/-- For [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the observed-state count](hyp:nX), [the history length](hyp:k), [the behavior policy](hyp:b),
[the target policy](hyp:e), and [the block index](hyp:ell), this establishes
[the block score measurability result](goal). -/
@[fun_prop]
lemma blockScore_measurable (T M nX k : Nat) (b e : Policy nX)
    (ell : Fin (numBlocks M)) :
    Measurable (blockScore T M nX k b e ell) := by
  unfold blockScore
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro t ht
  split_ifs with h
  · apply Measurable.mul
    · fun_prop
    · apply Finset.measurable_prod
      intro r hr
      split_ifs with h'
      · fun_prop
      · fun_prop
  · fun_prop

-- @node: candidateEstimate_measurable
/-- For [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the observed-state count](hyp:nX), [the history length](hyp:k), [the behavior policy](hyp:b),
[the candidate-policy list](hyp:E), and [the candidate index](hyp:j), this establishes
[the candidate estimate measurability result](goal). -/
lemma candidateEstimate_measurable (T M nX k : Nat) (b : Policy nX)
    (E : Fin M → Policy nX) (j : Fin M) :
    Measurable (fun w : ObsView T nX ↦ candidateEstimate T M nX k b E w j) := by
  unfold candidateEstimate clipUnit01 blockMedian
  fun_prop (disch := assumption)

-- @node: smallestMaximizer_measurable
/-- For [the sample space](hyp:Ω), [the candidate-policy count](hyp:M),
[the candidate-policy count assumption](hyp:hM), [the candidate score](hyp:score), and
[the state assumption](hyp:hs), this establishes
[the smallest maximizer measurability result](goal). -/
lemma smallestMaximizer_measurable {Ω : Type*} [MeasurableSpace Ω]
    (M : Nat) (hM : 0 < M) (score : Ω → Fin M → ℝ)
    (hs : ∀ j, Measurable (fun w ↦ score w j)) :
    Measurable (fun w ↦ smallestMaximizer M hM (score w)) := by
  let f : Ω → Fin M := fun w ↦ smallestMaximizer M hM (score w)
  have hmax (j : Fin M) : MeasurableSet {w : Ω | ∀ i : Fin M, score w i ≤ score w j} := by
    simpa only [Set.ofPred_forall] using
      (MeasurableSet.iInter (fun i : Fin M ↦ measurableSet_le (hs i) (hs j)))
  have hmin (j : Fin M) :
      MeasurableSet {w : Ω | ∀ i : Fin M,
        (∀ p : Fin M, score w p ≤ score w i) → j ≤ i} := by
    rw [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    by_cases h : j ≤ i
    · simpa [h] using (MeasurableSet.univ : MeasurableSet (Set.univ : Set Ω))
    · convert (hmax i).compl using 1 <;> ext w <;> simp [h]
  have hfiber (j : Fin M) : MeasurableSet {w : Ω | f w = j} := by
    have heq : {w : Ω | f w = j} =
        {w : Ω | (∀ i : Fin M, score w i ≤ score w j) ∧
          (∀ i : Fin M, (∀ p : Fin M, score w p ≤ score w i) → j ≤ i)} := by
      ext w
      simp only [Set.mem_ofPred_eq]
      unfold f smallestMaximizer
      rw [Finset.min'_eq_iff]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [heq]
    exact (hmax j).inter (hmin j)
  intro s hs'
  have heq : f ⁻¹' s = ⋃ j : Fin M, ⋃ (_ : j ∈ s), {w : Ω | f w = j} := by
    ext w
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · intro hw
      exact ⟨f w, ⟨hw, rfl⟩⟩
    · rintro ⟨j, ⟨hj, hw⟩⟩
      simpa [hw] using hj
  rw [heq]
  exact MeasurableSet.iUnion (fun j ↦ MeasurableSet.iUnion (fun _ ↦ hfiber j))

-- @node: blockSelectorRaw_measurable
/-- For [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the candidate-policy count assumption](hyp:hM), [the history depth](hyp:depth),
[the observed-state count](hyp:nX), [the behavior policy](hyp:b), and
[the candidate-policy list](hyp:E), this establishes
[the block selector raw measurability result](goal). -/
lemma blockSelectorRaw_measurable (T M : Nat) (hM : 0 < M) (depth : Nat → Nat) (nX : Nat)
    (b : Policy nX) (E : Fin M → Policy nX) :
    Measurable (blockSelectorRaw T M hM depth nX b E) := by
  unfold blockSelectorRaw
  by_cases h : blockLen T M < 4
  · simpa [h] using (measurable_const : Measurable (fun _ : ObsView T nX ↦ (⟨0, hM⟩ : Fin M)))
  · simp only [if_neg h]
    apply smallestMaximizer_measurable
    intro j
    exact candidateEstimate_measurable T M nX (depth (blockLen T M)) b E j
/-- [the block selector at depth object](goal) is defined from [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the candidate-policy count assumption](hyp:hM), and
[the history depth](hyp:depth). -/

noncomputable def blockSelectorAtDepth (T M : Nat) (hM : 0 < M) (depth : Nat → Nat) :
    ObservableSelector T M :=
  ⟨blockSelectorRaw T M hM depth, blockSelectorRaw_measurable T M hM depth⟩

-- @node: def:block-selector
/-- [the block selector object](goal) is defined from [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the candidate-policy count assumption](hyp:hM),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta), and
[the latent-overlap radius](hyp:C). -/
noncomputable def blockSelector (T M : Nat) (hM : 0 < M) (t0 zeta C : ℝ) :
    ObservableSelector T M :=
  blockSelectorAtDepth T M hM (fun n ↦ adaptiveDepth n t0 zeta C)
  -- @realizes jhat_star(observable clipped-median smallest-argmax selector)

-- @node: def:hw-block-selector
/-- [the hu–wager block selector object](goal) is defined from [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the candidate-policy count assumption](hyp:hM),
[the mixing scale](hyp:t0), and [the policy-overlap scale](hyp:zeta). -/
noncomputable def hwBlockSelector (T M : Nat) (hM : 0 < M) (t0 zeta : ℝ) :
    ObservableSelector T M :=
  blockSelectorAtDepth T M hM (fun n ↦ conservativeDepth n t0 zeta)
  -- @realizes jhatHW(conservative-depth observable selector)

-- @node: def:frontier
/-- [the regret frontier quantity](goal) is defined from [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C),
[the mixing scale assumption](hyp:ht0), [the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the time horizon assumption](hyp:hT), and
[the candidate-policy count assumption](hyp:hM). -/
noncomputable def regretFrontier (T M : Nat) (t0 zeta C : ℝ)
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (hT : 1 ≤ T) (hM : 2 ≤ M) : ℝ :=
  min 1 (Real.sqrt (listInformationRatio T M hT hM) +
    overlapRadius C ^ (1 - rateExponent t0 zeta) *
      (listInformationRatio T M hT hM) ^ (rateExponent t0 zeta / 2))
  -- @realizes F(candidate frontier) @realizes beta(hidden-memory exponent) @realizes u(log M / T) @realizes q((C-1)/C)

end CausalSmith.Stat.PomdpPolicyclassRegret
