module
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinCertifiedInitialFalse
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinCertifiedInitialTrue

@[expose] public section

namespace CausalSmith.Stat.PomdpLatentOverlapMinimax

open Causalean.Mathlib.Analysis.IntervalArithmetic
open Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation

/-- For [the target input](hyp:target), [this defines the insulin Certified Initial object](goal). -/
def insulinCertifiedInitial (target : Bool) : RationalProbabilityVector (Fin 360) :=
  if target then insulinTrueCertifiedInitial else insulinFalseCertifiedInitial

/-- [the insulin Certified Initial checked assertion holds](goal). -/
theorem insulinCertifiedInitial_checked (target : Bool) : ∀ i : Fin 360,
    (RatInterval.point ((insulinCertifiedInitial target).value i)).Subinterval
      (insulinTraceInterval target 0 i) := by
  cases target <;> simp only [insulinCertifiedInitial, Bool.false_eq_true, if_false, if_true]
  · exact insulinFalseCertifiedInitial_checked
  · exact insulinTrueCertifiedInitial_checked

end CausalSmith.Stat.PomdpLatentOverlapMinimax
