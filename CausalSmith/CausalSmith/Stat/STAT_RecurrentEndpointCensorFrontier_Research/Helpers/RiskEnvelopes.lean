module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ContinuationBias

/-!
# Explicit envelope constants for the upper-risk calculation

This module isolates the continuation-weight and reciprocal-retention constants
used by the finite-sample risk bounds.
-/

@[expose] public section

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

noncomputable def continuationCoeff (ell : ℕ) (m : Fin (ell + 1)) : ℝ :=
  ((continuationGram ell)⁻¹.mulVec (continuationRhs ell)) m

noncomputable def continuationNorm (c : ClassConstants) : ℝ :=
  ∑ m : Fin (holderOrder c + 1),
    |continuationCoeff (holderOrder c) m| * (2 : ℝ) ^ m.val

noncomputable def weightEnvelope (c : ClassConstants) : ℝ :=
  1 + continuationNorm c

noncomputable def reciprocalRetentionEnvelope (c : ClassConstants) : ℝ :=
  (1 - c.x0) / c.Gint +
    if c.kappa < 1 then
      2 * c.x0 ^ (1 - c.kappa) / (c.gMin * (1 - c.kappa))
    else if c.kappa = 1 then 2 / c.gMin
    else 2 / (c.gMin * (c.kappa - 1))

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
