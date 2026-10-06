module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.IdentificationContinuity
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.IdentificationObservables
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PromotedFullIdentification
public import Causalean.Stat.RecurrentEvent

/-!
# Identification of the causal horizon count

The latent mean equals the survival-weighted intensity integral. Equality of
observed histories identifies that mean within the endpoint-censor class.
-/

public section

open MeasureTheory Set
open scoped Interval

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

-- @node: prop:causal-identification
theorem causal_identification (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) :
    causalTarget P =
      ∫ t in (0 : ℝ)..1,
        (survival P true t * P.lam true t -
          survival P false t * P.lam false t) ∧
    (∀ P' : SubjectLaw, ModelClass c P' →
      observedLaw P = observedLaw P' →
      (∀ ε : ℝ, 0 < ε → ∀ a : Arm,
        ∀ t ∈ Set.Icc (0 : ℝ) (1 - ε),
          P.lam a t = P'.lam a t ∧ P.hazard a t = P'.hazard a t) ∧
      (∀ a : Arm, P.lam a 1 = P'.lam a 1 ∧
        P.hazard a 1 = P'.hazard a 1) ∧
      causalTarget P = causalTarget P') := by
  exact causal_identification_adapter c P hP

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
