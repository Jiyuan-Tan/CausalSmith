module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.Capping

/-! # Complete-arrival and small-scale estimator branches -/

public section
namespace CausalSmith.Stat.MarNearcompleteFrontier

/-- If [arrival is incomplete](hyp:hq) and [the scale is in the fallback regime](hyp:hsmall), [the missing-membership estimator equals the fallback estimator](goal). -/
lemma tauhatMM_fallback (n d : ℕ) (q : ℝ) (o : Fin n → Obs d)
    (hq : q ≠ 1)
    (hsmall : ell n < 128 ∨ (d : ℝ) ≥ (n : ℝ) * ell n) :
    tauhatMM n d q o = fallbackHT o := by
  simp [tauhatMM, hq, hsmall]

end CausalSmith.Stat.MarNearcompleteFrontier
