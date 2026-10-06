module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.StreamPilot
public import Causalean.Stat.Concentration.Poisson.Threshold

/-!
# Poisson tails for pilot selection

The exponential tilt by `log 4` gives the light-selection lower tail and the
complementary heavy-selection upper tail used in the upper-risk proof.
-/

public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open Causalean.Stat.Concentration.Poisson

open MeasureTheory ProbabilityTheory



-- @node: upper_stream_pilot_light_tail
/-- The light-branch selection probability obeys the Poisson lower-tail
estimate at the arrived-cell rate. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
lemma upper_stream_pilot_light_tail {n d : ℕ} (P : FullLaw d)
    (x : Fin d) (a s : Bool) :
    streamPilotLightProb n P x a s ≤
      Real.exp (polyThreshold n * Real.log 4 / 4 -
        3 * streamZ n P x a s / 4) := by
  have hr : ((streamPoissonRate n P x a s : NNReal) : ℝ) =
      streamZ n P x a s := by
    unfold streamPoissonRate streamZ
    change (((n : NNReal) / 8 : NNReal) : ℝ) * arrivedCellMass P x a s = _
    rw [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_ofNat]
  rw [upper_stream_pilot_light_prob_poisson]
  simpa only [hr] using
    poisson_pilot_lower_tail (streamPoissonRate n P x a s) (polyThreshold n)

-- @node: upper_stream_pilot_heavy_tail
/-- The heavy-branch selection probability obeys the Poisson upper-tail
estimate at the arrived-cell rate. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
lemma upper_stream_pilot_heavy_tail {n d : ℕ} (P : FullLaw d)
    (x : Fin d) (a s : Bool) :
    1 - streamPilotLightProb n P x a s ≤
      Real.exp (3 * streamZ n P x a s -
        polyThreshold n * Real.log 4 / 4) := by
  have hr : ((streamPoissonRate n P x a s : NNReal) : ℝ) =
      streamZ n P x a s := by
    unfold streamPoissonRate streamZ
    change (((n : NNReal) / 8 : NNReal) : ℝ) * arrivedCellMass P x a s = _
    rw [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_ofNat]
  let A : Set ℕ := {k : ℕ | (k : ℝ) ≤ polyThreshold n / 4}
  have hA : MeasurableSet A := by
    exact measurableSet_le (measurable_of_countable _) measurable_const
  have hcomp : Aᶜ = {k : ℕ | polyThreshold n / 4 < (k : ℝ)} := by
    ext k
    simp only [A, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
  have hp := upper_stream_pilot_light_prob_poisson (n := n) P x a s
  have hprob : 1 - (poissonMeasure (streamPoissonRate n P x a s)).real A =
      (poissonMeasure (streamPoissonRate n P x a s)).real Aᶜ := by
    rw [measureReal_compl hA, probReal_univ]
  calc
    1 - streamPilotLightProb n P x a s =
        (poissonMeasure (streamPoissonRate n P x a s)).real
          {k : ℕ | polyThreshold n / 4 < (k : ℝ)} := by
      rw [hp]
      change 1 - (poissonMeasure (streamPoissonRate n P x a s)).real A = _
      rw [hprob, hcomp]
    _ ≤ Real.exp (3 * ((streamPoissonRate n P x a s : NNReal) : ℝ) -
          polyThreshold n * Real.log 4 / 4) :=
      poisson_pilot_upper_tail (streamPoissonRate n P x a s) (polyThreshold n)
    _ = Real.exp (3 * streamZ n P x a s -
          polyThreshold n * Real.log 4 / 4) := by rw [hr]

end CausalSmith.Stat.MarNearcompleteFrontier
