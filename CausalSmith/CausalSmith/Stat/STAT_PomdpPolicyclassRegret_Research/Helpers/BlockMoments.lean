module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.BlockVariance

/-!
# Arbitrary-start block PHIW moment theorem

The chronological bias calculation and the covariance variance assembly apply
to the same observable segment law, without reward-successor independence.
-/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open MeasureTheory
open CausalSmith.Stat.PomdpLatentOverlapMinimax

-- @node: lem:block-phiw-moments
/-- For [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the sample size](hyp:n), [the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the model](hyp:m), [the class assumption](hyp:hClass),
[the mixing scale assumption](hyp:ht0), [the policy-overlap scale assumption](hyp:hzeta),
[the candidate index](hyp:j), [the history length](hyp:k),
[the history length assumption](hyp:hk), [the sample size assumption](hyp:hn),
[the initial distribution](hyp:nu), and [the initial distribution assumption](hyp:hnu), this
establishes [the block partial-history importance-weighted moments result](goal). -/
lemma block_phiw_moments {T M n : Nat} (t0 zeta C : ℝ) (m : ModelIndex T M)
    (hClass : PolicyListClass t0 zeta C m) (ht0 : 0 < t0) (hzeta : 0 < zeta)
    (j : Fin M) (k : Nat) (hk : 2 * k ≤ n) (hn : 4 ≤ n)
    (nu : JointState m.nX m.nH → ℝ) (hnu : ProbabilityVector nu) :
    |∫ w, phiwRaw k m.Mx.b (m.Mx.E j) w
        ∂((segmentLaw m hClass.finite_state nu n).map obsProj) - policyValue m j| ≤
      mixingAlpha t0 ^ k *
        (overlapRadius C + 1 / ((n - k : Nat) * (1 - mixingAlpha t0))) ∧
    ProbabilityTheory.variance
        (phiwRaw k m.Mx.b (m.Mx.E j))
        ((segmentLaw m hClass.finite_state nu n).map obsProj) ≤
      (1 + 2 / (policyFactor zeta - 1) + 4 / (1 - mixingAlpha t0)) *
        policyFactor zeta ^ (k + 1) / (n - k : Nat) := by
  have hkn : k < n := by omega
  exact ⟨phiwRaw_observedSegment_bias t0 zeta C m hClass j nu hnu k hkn,
    phiwRaw_observedSegment_variance t0 zeta C m hClass ht0 hzeta j nu hnu k hkn⟩


end CausalSmith.Stat.PomdpPolicyclassRegret
