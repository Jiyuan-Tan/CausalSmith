module
public import Causalean.Stat.RecurrentEvent.CountingProcess.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
A subject's at-risk hazard integral stops at its censor time. This pathwise
fact identifies the compensator value used at an observed censor jump.
-/

public section

open MeasureTheory

namespace Causalean.Stat.RecurrentEvent.CountingProcess

/-- If [a subject's censor time is nonnegative](hyp:hc0) and [occurs by the horizon u](hyp:hcu),
and [the subject's at-risk payoff weighted by the censor hazard is integrable from 0 to
u](hyp:hazard,hPath), then
[the integral of that payoff from 0 to u equals its integral from 0 to the censor time](goal),
since the subject leaves the risk set after censoring. -/
theorem subject_hazard_stops_at_censor {n : ℕ}
    (hazard : ℝ → ℝ) (H : ℝ → Sample n → ℝ)
    (i : Fin n) (x : Sample n) (u : ℝ)
    (hc0 : 0 ≤ (x i).2) (hcu : (x i).2 ≤ u)
    (hPath : Integrable (fun s => H s x * hazard s * riskIndicator i s x)
      (volume.restrict (Set.Icc 0 u))) :
    (∫ s in Set.Icc 0 u, H s x * hazard s * riskIndicator i s x ∂volume) =
      ∫ s in Set.Icc 0 (x i).2,
        H s x * hazard s * riskIndicator i s x ∂volume := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc
  · exact Set.Icc_subset_Icc_right hcu
  · intro s hs
    have hcs : (x i).2 < s := by
      by_contra h
      exact hs.2 ⟨hs.1.1, le_of_not_gt h⟩
    simp [riskIndicator, not_le.mpr hcs]

end Causalean.Stat.RecurrentEvent.CountingProcess
