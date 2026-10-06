module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Basic

/-! # Convexity of the staircase information profile

The profile is a nonnegative weighted sum of squared affine scores. -/

public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open scoped BigOperators

-- @node: informationObjective_convex_time
/-- Under the supplied quantities and conditions, the information objective convex time assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hα,hmass,ha,hb,hab), [the information Objective convex time](goal).

Under the stated assumptions, the information Objective convex time. -/
lemma informationObjective_convex_time (θ : TrialParameter) (p ε : ℝ)
    (α : StaircaseWeight) (hα : ∀ s, 0 ≤ α s)
    (hmass : ∀ s, 0 < patternMass θ p ε s)
    (t u a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    informationObjective θ p ε α (a * t + b * u) ≤
      a * informationObjective θ p ε α t +
        b * informationObjective θ p ε α u := by
  unfold informationObjective
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro s _
  have hslope : projectedGradient p ε s (a * t + b * u) =
      a * projectedGradient p ε s t +
        b * projectedGradient p ε s u := by
    simp [projectedGradient, direction, Fin.sum_univ_succ]
    linear_combination -(patternGradient p ε s 1) * hab
  have hsq :
      (a * projectedGradient p ε s t +
        b * projectedGradient p ε s u) ^ 2 ≤
      a * (projectedGradient p ε s t) ^ 2 +
        b * (projectedGradient p ε s u) ^ 2 := by
    have h := mul_nonneg (mul_nonneg ha hb)
      (sq_nonneg (projectedGradient p ε s t - projectedGradient p ε s u))
    nlinarith [h]
  unfold patternInformation
  rw [hslope]
  have hc : 0 ≤ α s / patternMass θ p ε s :=
    div_nonneg (hα s) (hmass s).le
  calc
    α s * ((a * projectedGradient p ε s t +
        b * projectedGradient p ε s u) ^ 2 /
          patternMass θ p ε s) =
        (α s / patternMass θ p ε s) *
          (a * projectedGradient p ε s t +
            b * projectedGradient p ε s u) ^ 2 := by ring
    _ ≤ (α s / patternMass θ p ε s) *
          (a * (projectedGradient p ε s t) ^ 2 +
            b * (projectedGradient p ε s u) ^ 2) :=
        mul_le_mul_of_nonneg_left hsq hc
    _ = a * (α s * ((projectedGradient p ε s t) ^ 2 /
          patternMass θ p ε s)) +
        b * (α s * ((projectedGradient p ε s u) ^ 2 /
          patternMass θ p ε s)) := by ring

-- @node: informationObjective_convexOn_time
/-- Under the supplied quantities and conditions, the information objective convex on time assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hα,hmass), [the information Objective convex On time](goal).

Under the stated assumptions, the information Objective convex On time. -/
lemma informationObjective_convexOn_time (θ : TrialParameter) (p ε : ℝ)
    (α : StaircaseWeight) (hα : ∀ s, 0 ≤ α s)
    (hmass : ∀ s, 0 < patternMass θ p ε s) :
    ConvexOn ℝ Set.univ (informationObjective θ p ε α) := by
  refine ⟨convex_univ, ?_⟩
  intro t _ u _ a b ha hb hab
  simpa only [smul_eq_mul] using
    informationObjective_convex_time θ p ε α hα hmass t u a b ha hb hab

end CausalSmith.Stat.LdpAteEfficiencySurface
