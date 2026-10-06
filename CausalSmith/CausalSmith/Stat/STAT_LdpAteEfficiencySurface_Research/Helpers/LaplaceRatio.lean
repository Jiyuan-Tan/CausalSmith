module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.Pilot
public import Causalean.Stat.Limit.Modes

/-! # Coupled variance-ratio continuity

A nonnegative estimated denominator makes the ordinary square-root ratio agree
with the total fallback map.  Consequently marginal convergence in probability
passes through every coupling of the two rows.
-/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open MeasureTheory Filter Causalean.Stat

/-- Under [the supplied quantities and conditions](hyp:p,m), [the vhat star nonneg assertion](goal) holds. For [the displayed quantities and conditions](hyp:select,z), these specify the stated inputs. -/
lemma VhatStar_nonneg (p ε : ℝ) (m : ℕ → ℕ)
    (select : TrialParameter → StaircaseWeight × ℝ × ℝ)
    {n : ℕ} (z : Transcript (pilotOutputFamily n)) :
    0 ≤ VhatStar p ε m select z := by
  unfold VhatStar
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun i _ => by
      split_ifs
      · exact sq_nonneg _
      · exact le_rfl)

end CausalSmith.Stat.LdpAteEfficiencySurface
