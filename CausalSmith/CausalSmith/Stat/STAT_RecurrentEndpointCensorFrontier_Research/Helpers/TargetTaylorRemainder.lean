module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ContinuationBias
public import Causalean.Mathlib.Analysis.Calculus.HolderTaylor

/-!
# Endpoint Taylor form for the recurrent-event target integrand

This file aligns the paper's Hölder order and endpoint-polynomial convention
with the generic scalar Hölder--Taylor API.  A uniform Taylor remainder for the
target integrand additionally needs a uniform Hölder closure theorem for the
product of the recurrence intensity and survival function.
-/

public section

open Set
open scoped BigOperators

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
