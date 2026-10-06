module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SelectorBlockTails
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SelectorSegmentGenerated

/-! # Actual-law prefix transport for selector concentration

The stationary structural-law identity transports a shorter observed prefix
of the actual trajectory to the arbitrary-start block moment interface.
-/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open MeasureTheory
open CausalSmith.Stat.PomdpLatentOverlapMinimax

/-- The actual trajectory's full prefix has the stationary structural law. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the sample size](hyp:n),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the model](hyp:m), [the class assumption](hyp:hClass), and
[the sample size assumption](hyp:hn), this establishes
[the selector actual prefix law result](goal). -/
-- @node: selector_actual_prefix_law
lemma selector_actual_prefix_law {T M n : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m) (hn : n ≤ T) :
    m.Mx.law.map (segmentTrajectoryTake hn) =
      segmentLaw m hClass.finite_state
        (stationaryLaw (policyKernel m.Mx.toRawB m.Mx.b)) n := by
  rw [selector_actual_law_eq_stationary_segment t0 zeta C m hClass]
  exact segmentLaw_map_trajectoryTake m hClass.finite_state
    hClass.sequential_ignorability.1 _ hn

/-- Projecting the actual full prefix recovers exactly the observed segment law. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the sample size](hyp:n),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the model](hyp:m), [the class assumption](hyp:hClass), and
[the sample size assumption](hyp:hn), this establishes
[the selector actual observed prefix law result](goal). -/
-- @node: selector_actual_observed_prefix_law
lemma selector_actual_observed_prefix_law {T M n : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m) (hn : n ≤ T) :
    m.Mx.law.map (obsProj ∘ segmentTrajectoryTake hn) =
      (segmentLaw m hClass.finite_state
        (stationaryLaw (policyKernel m.Mx.toRawB m.Mx.b)) n).map obsProj := by
  rw [← Measure.map_map (by fun_prop) (segmentTrajectoryTake_measurable hn),
    selector_actual_prefix_law t0 zeta C m hClass hn]

/-- Equation (10) for a prefix of the actual trajectory, rather than a separately constructed
structural observation law. For [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the sample size](hyp:n), [the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the model](hyp:m), [the class assumption](hyp:hClass),
[the n t assumption](hyp:hnT), [the candidate index](hyp:j), [the history length](hyp:k),
[the history length assumption](hyp:hk), [the sample size assumption](hyp:hn),
[the observed state](hyp:x), and [the observed state assumption](hyp:hx), this establishes
[the selector actual prefix chebyshev result](goal). -/
-- @node: selector_actual_prefix_chebyshev
lemma selector_actual_prefix_chebyshev {T M n : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m)
    (hnT : n ≤ T) (j : Fin M) (k : Nat) (hk : 2 * k ≤ n) (hn : 4 ≤ n)
    (x : ℝ) (hx : 0 < x) :
    m.Mx.law {w | mixingAlpha t0 ^ k *
      (overlapRadius C + 1 / ((n - k : Nat) * (1 - mixingAlpha t0))) + x <
        |phiwRaw k m.Mx.b (m.Mx.E j) (obsProj (segmentTrajectoryTake hnT w)) -
          policyValue m j|} ≤
      ENNReal.ofReal (((1 + 2 / (policyFactor zeta - 1) +
        4 / (1 - mixingAlpha t0)) * policyFactor zeta ^ (k + 1) /
          (n - k : Nat)) / x ^ 2) := by
  have hbad : MeasurableSet {w : ObsView n m.nX | mixingAlpha t0 ^ k *
      (overlapRadius C + 1 / ((n - k : Nat) * (1 - mixingAlpha t0))) + x <
        |phiwRaw k m.Mx.b (m.Mx.E j) w - policyValue m j|} := by
    apply measurableSet_lt measurable_const
    have hraw : Measurable (phiwRaw (T := n) k m.Mx.b (m.Mx.E j)) := by
      unfold phiwRaw
      apply Measurable.const_mul
      apply Finset.measurable_sum
      intro t ht
      exact phiwScore_measurable (k := k) m.Mx.b (m.Mx.E j) t
    exact continuous_abs.measurable.comp (hraw.sub_const _)
  have hmap := selector_actual_observed_prefix_law t0 zeta C m hClass hnT
  have hnu : ProbabilityVector (stationaryLaw (policyKernel m.Mx.toRawB m.Mx.b)) := by
    simpa only [ListPomdpExperiment.toRawB] using hClass.stationary_start.1.1
  have htail := selector_block_chebyshev t0 zeta C m hClass hClass.t0_pos
    hClass.zeta_pos j k hk hn
    (stationaryLaw (policyKernel m.Mx.toRawB m.Mx.b)) hnu x hx
  rw [← hmap, Measure.map_apply (by fun_prop) hbad] at htail
  exact htail

end CausalSmith.Stat.PomdpPolicyclassRegret
