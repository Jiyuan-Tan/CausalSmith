module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.BlockMoments

/-! # Support and arbitrary-start moments in the broader HW class

Action overlap preserves behavior support under target transitions. Geometric
contraction then confines the target stationary laws to that support, producing
a finite model-specific overlap radius as in equations (61)--(65).
-/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open CausalSmith.Stat.PomdpLatentOverlapMinimax
open Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation
  (markovIterate markovStep IsStochasticMatrix)
open MeasureTheory
open scoped BigOperators

/-- Contraction supplies each target stationary law without a stationary-overlap radius. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the model](hyp:m), [the class assumption](hyp:hClass),
and [the candidate index](hyp:j), this establishes
[the Hu–Wager target stationary result](goal). -/
-- @node: hw_target_stationary
lemma hw_target_stationary {T M : Nat} (t0 zeta : ℝ)
    (m : ModelIndex T M) (hClass : HWPolicyListClass t0 zeta m) (j : Fin M) :
    IsStationary (listPolicyKernel m (m.Mx.E j)) (listStationaryLaw m (m.Mx.E j)) := by
  apply stationaryLaw_isStationary_of_exists
  apply exists_stationary_of_contraction
    (P := listPolicyKernel m (m.Mx.E j))
    (p0 := listStationaryLaw m m.Mx.b) (alpha := mixingAlpha t0)
  · exact policyKernel_probabilityVector m.Mx.toRawB m.kernel_law _
      (hClass.action_overlap j).1
  · exact hClass.stationary_start.1.1
  · exact Real.exp_nonneg _
  · rw [mixingAlpha, Real.exp_lt_one_iff]
    exact neg_neg_of_pos (one_div_pos.mpr hClass.t0_pos)
  · exact hClass.uniform_contraction j _ (Or.inr rfl)

/-- Pointwise action overlap dominates the target transition matrix by the behavior transition
matrix, as in equation (61). For [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta), [the model](hyp:m),
[the class assumption](hyp:hClass), [the candidate index](hyp:j), [the state](hyp:s), and
[the successor state](hyp:s'), this establishes
[the Hu–Wager policy kernel bound behavior result](goal). -/
-- @node: hw_policyKernel_le_behavior
lemma hw_policyKernel_le_behavior {T M : Nat} (t0 zeta : ℝ)
    (m : ModelIndex T M) (hClass : HWPolicyListClass t0 zeta m)
    (j : Fin M) (s s' : JointState m.nX m.nH) :
    listPolicyKernel m (m.Mx.E j) s s' ≤
      policyFactor zeta * listPolicyKernel m m.Mx.b s s' := by
  change (∑ a : Bool, m.Mx.E j s.1 a * (m.Mx.K s a {q | q.2 = s'}).toReal) ≤
    policyFactor zeta * ∑ a : Bool, m.Mx.b s.1 a * (m.Mx.K s a {q | q.2 = s'}).toReal
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  simpa only [ListPomdpExperiment.toRaw, mul_assoc] using mul_le_mul_of_nonneg_right
    ((hClass.action_overlap j).2 s.1 a) ENNReal.toReal_nonneg

/-- A target transition cannot leave the positive support of the behavior stationary law.
Stationarity first forces the behavior transition to vanish. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the model](hyp:m), [the class assumption](hyp:hClass),
[the candidate index](hyp:j), [the state](hyp:s), [the successor state](hyp:s'),
[the state assumption](hyp:hs), and [the state alternate assumption](hyp:hs'), this establishes
[the Hu–Wager behavior support closed result](goal). -/
-- @node: hw_behavior_support_closed
lemma hw_behavior_support_closed {T M : Nat} (t0 zeta : ℝ)
    (m : ModelIndex T M) (hClass : HWPolicyListClass t0 zeta m)
    (j : Fin M) (s s' : JointState m.nX m.nH)
    (hs : 0 < listStationaryLaw m m.Mx.b s)
    (hs' : listStationaryLaw m m.Mx.b s' = 0) :
    listPolicyKernel m (m.Mx.E j) s s' = 0 := by
  have hdb := hClass.stationary_start.1
  have hPb := policyKernel_probabilityVector m.Mx.toRawB m.kernel_law _
    hClass.sequential_ignorability.1
  have hPe := policyKernel_probabilityVector m.Mx.toRawB m.kernel_law _
    (hClass.action_overlap j).1
  have hterm : listStationaryLaw m m.Mx.b s * listPolicyKernel m m.Mx.b s s' ≤ 0 := by
    calc
      _ ≤ ∑ r, listStationaryLaw m m.Mx.b r * listPolicyKernel m m.Mx.b r s' :=
        Finset.single_le_sum (fun r _ ↦ mul_nonneg (hdb.1.1 r) ((hPb r).1 s'))
          (Finset.mem_univ s)
      _ = 0 := (hdb.2 s').trans hs'
  have hzero : listPolicyKernel m m.Mx.b s s' = 0 := by
    have hnonneg := (hPb s).1 s'
    change 0 ≤ listPolicyKernel m m.Mx.b s s' at hnonneg
    nlinarith
  apply le_antisymm
  · simpa only [hzero, mul_zero] using hw_policyKernel_le_behavior t0 zeta m hClass j s s'
  · exact (hPe s).1 s'

/-- Every target iterate initialized at the behavior stationary law remains zero off behavior
support, the finite-state form of equation (61). For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the model](hyp:m), [the class assumption](hyp:hClass),
[the candidate index](hyp:j), [the reward symbol](hyp:r), [the successor state](hyp:s'), and
[the state alternate assumption](hyp:hs'), this establishes
[the Hu–Wager target iterate zero off support result](goal). -/
-- @node: hw_targetIterate_zero_off_support
lemma hw_targetIterate_zero_off_support {T M : Nat} (t0 zeta : ℝ)
    (m : ModelIndex T M) (hClass : HWPolicyListClass t0 zeta m)
    (j : Fin M) (r : Nat) (s' : JointState m.nX m.nH)
    (hs' : listStationaryLaw m m.Mx.b s' = 0) :
    markovIterate (listPolicyKernel m (m.Mx.E j))
      (listStationaryLaw m m.Mx.b) r s' = 0 := by
  classical
  induction r generalizing s' with
  | zero => exact hs'
  | succ r ih =>
    change (∑ s, markovIterate (listPolicyKernel m (m.Mx.E j))
      (listStationaryLaw m m.Mx.b) r s * listPolicyKernel m (m.Mx.E j) s s') = 0
    apply Finset.sum_eq_zero
    intro s _
    by_cases hs : listStationaryLaw m m.Mx.b s = 0
    · rw [ih s hs, zero_mul]
    · have hpos : 0 < listStationaryLaw m m.Mx.b s :=
        lt_of_le_of_ne (hClass.stationary_start.1.1.1 s) (Ne.symm hs)
      rw [hw_behavior_support_closed t0 zeta m hClass j s s' hpos hs', mul_zero]

/-- Taking the geometric contraction limit in equation (62) shows that each target stationary
law vanishes outside behavior support. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the model](hyp:m), [the class assumption](hyp:hClass),
[the candidate index](hyp:j), [the state](hyp:s), and [the state assumption](hyp:hs), this
establishes [the Hu–Wager target stationary support result](goal). -/
-- @node: hw_target_stationary_support
lemma hw_target_stationary_support {T M : Nat} (t0 zeta : ℝ)
    (m : ModelIndex T M) (hClass : HWPolicyListClass t0 zeta m)
    (j : Fin M) (s : JointState m.nX m.nH)
    (hs : listStationaryLaw m m.Mx.b s = 0) :
    listStationaryLaw m (m.Mx.E j) s = 0 := by
  have hde := hw_target_stationary t0 zeta m hClass j
  have hα0 : 0 ≤ mixingAlpha t0 := (Real.exp_pos _).le
  have hα1 : mixingAlpha t0 < 1 :=
    Real.exp_lt_one_iff.mpr (neg_neg_of_pos (one_div_pos.mpr hClass.t0_pos))
  have hPe : IsStochasticMatrix (listPolicyKernel m (m.Mx.E j)) := by
    have h := policyKernel_probabilityVector m.Mx.toRawB m.kernel_law
      (m.Mx.E j) (hClass.action_overlap j).1
    exact ⟨fun u v ↦ (h u).1 v, fun u ↦ (h u).2⟩
  have hbound : ∀ r : Nat, listStationaryLaw m (m.Mx.E j) s ≤ 2 * mixingAlpha t0 ^ r := by
    intro r
    have ht := phiw_markovIterate_transient_tv _ hPe _ hα0
      (hClass.uniform_contraction j _ (Or.inr rfl)) _ _ hClass.stationary_start.1.1 hde r
    have hc : |markovIterate (listPolicyKernel m (m.Mx.E j))
        (listStationaryLaw m m.Mx.b) r s - listStationaryLaw m (m.Mx.E j) s| ≤
        ∑ u, |markovIterate (listPolicyKernel m (m.Mx.E j))
          (listStationaryLaw m m.Mx.b) r u - listStationaryLaw m (m.Mx.E j) u| :=
      Finset.single_le_sum (fun u _ ↦ abs_nonneg
        (markovIterate (listPolicyKernel m (m.Mx.E j))
          (listStationaryLaw m m.Mx.b) r u - listStationaryLaw m (m.Mx.E j) u))
        (Finset.mem_univ s)
    rw [hw_targetIterate_zero_off_support t0 zeta m hClass j r s hs,
      zero_sub, abs_neg, abs_of_nonneg (hde.1.1 s)] at hc
    change (1 / 2 : ℝ) * (∑ u,
      |markovIterate (listPolicyKernel m (m.Mx.E j))
        (listStationaryLaw m m.Mx.b) r u - listStationaryLaw m (m.Mx.E j) u|) ≤
      mixingAlpha t0 ^ r at ht
    linarith
  have hlim : Filter.Tendsto (fun r : Nat ↦ 2 * mixingAlpha t0 ^ r)
      Filter.atTop (nhds (0 : ℝ)) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hα0 hα1).const_mul 2
  exact le_antisymm (ge_of_tendsto hlim (Filter.Eventually.of_forall hbound)) (hde.1.1 s)

/-- Finiteness of the state space and policy list supplies a single finite radius for this
model, as in equation (63); it is not used to tune the HW rule. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the model](hyp:m), and
[the class assumption](hyp:hClass), this establishes
[the Hu–Wager exists policy list class radius result](goal). -/
-- @node: hw_exists_policyListClass_radius
lemma hw_exists_policyListClass_radius {T M : Nat} (t0 zeta : ℝ)
    (m : ModelIndex T M) (hClass : HWPolicyListClass t0 zeta m) :
    ∃ C : ℝ, PolicyListClass t0 zeta C m := by
  classical
  let C : ℝ := 1 + ∑ j : Fin M, ∑ s : JointState m.nX m.nH,
    listStationaryLaw m (m.Mx.E j) s / listStationaryLaw m m.Mx.b s
  have hratio : ∀ j s, 0 ≤ listStationaryLaw m (m.Mx.E j) s /
      listStationaryLaw m m.Mx.b s := fun j s ↦
    div_nonneg ((hw_target_stationary t0 zeta m hClass j).1.1 s)
      (hClass.stationary_start.1.1.1 s)
  have hC : 1 ≤ C := by
    dsimp [C]
    have hsum := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) ↦
      Finset.sum_nonneg (fun s (_ : s ∈ Finset.univ) ↦ hratio j s))
    linarith
  have hdom : ∀ j s, listStationaryLaw m (m.Mx.E j) s ≤ C * listStationaryLaw m m.Mx.b s := by
    intro j s
    by_cases hs : listStationaryLaw m m.Mx.b s = 0
    · rw [hw_target_stationary_support t0 zeta m hClass j s hs, hs, mul_zero]
    · have hpos : 0 < listStationaryLaw m m.Mx.b s :=
        lt_of_le_of_ne (hClass.stationary_start.1.1.1 s) (Ne.symm hs)
      apply (div_le_iff₀ hpos).mp
      calc
        _ ≤ ∑ u, listStationaryLaw m (m.Mx.E j) u / listStationaryLaw m m.Mx.b u :=
          Finset.single_le_sum (fun u _ ↦ hratio j u) (Finset.mem_univ s)
        _ ≤ ∑ i : Fin M, ∑ u, listStationaryLaw m (m.Mx.E i) u / listStationaryLaw m m.Mx.b u :=
          Finset.single_le_sum (fun i _ ↦ Finset.sum_nonneg (fun u _ ↦ hratio i u))
            (Finset.mem_univ j)
        _ ≤ C := by dsimp [C]; linarith
  refine ⟨C, hClass.t0_pos, hClass.zeta_pos, hC, hClass.finite_state,
    hClass.sequential_ignorability, hClass.stationary_start, hClass.uniform_contraction,
    hClass.action_overlap, ?_, hClass.supplied_list⟩
  exact ⟨hC, fun j ↦ ⟨hC, hdom j⟩⟩

/-- The broader class enjoys the same arbitrary-start block moments, with unit stationary bias
coefficient, as in equations (64)--(65). For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the sample size](hyp:n), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the model](hyp:m), [the class assumption](hyp:hClass),
[the candidate index](hyp:j), [the history length](hyp:k),
[the history length assumption](hyp:hk), [the sample size assumption](hyp:hn),
[the initial distribution](hyp:nu), and [the initial distribution assumption](hyp:hnu), this
establishes [the Hu–Wager block partial-history importance-weighted moments result](goal). -/
-- @node: hw_block_phiw_moments
lemma hw_block_phiw_moments {T M n : Nat} (t0 zeta : ℝ) (m : ModelIndex T M)
    (hClass : HWPolicyListClass t0 zeta m) (j : Fin M) (k : Nat)
    (hk : 2 * k ≤ n) (hn : 4 ≤ n)
    (nu : JointState m.nX m.nH → ℝ) (hnu : ProbabilityVector nu) :
    |∫ w, phiwRaw k m.Mx.b (m.Mx.E j) w
        ∂((segmentLaw m hClass.finite_state nu n).map obsProj) - policyValue m j| ≤
      mixingAlpha t0 ^ k *
        (1 + 1 / ((n - k : Nat) * (1 - mixingAlpha t0))) ∧
    ProbabilityTheory.variance (phiwRaw k m.Mx.b (m.Mx.E j))
        ((segmentLaw m hClass.finite_state nu n).map obsProj) ≤
      (1 + 2 / (policyFactor zeta - 1) + 4 / (1 - mixingAlpha t0)) *
        policyFactor zeta ^ (k + 1) / (n - k : Nat) := by
  obtain ⟨C, hC⟩ := hw_exists_policyListClass_radius t0 zeta m hClass
  obtain ⟨hb, hv⟩ := block_phiw_moments t0 zeta C m hC
    hClass.t0_pos hClass.zeta_pos j k hk hn nu hnu
  refine ⟨hb.trans ?_, hv⟩
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Real.exp_nonneg _) k)
  apply add_le_add_left
  unfold overlapRadius
  apply (div_le_one (by linarith [hC.C_ge_one])).mpr
  linarith

end CausalSmith.Stat.PomdpPolicyclassRegret
