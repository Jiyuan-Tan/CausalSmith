/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Mathlib.LinearAlgebra.StackedVandermonde

/-!
# Compatibility reexports for stacked contraction rank

The paper-independent block-Vandermonde construction lives in Causalean. This
module preserves the names used by the paper-specific apolar specialization.
-/

public section

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

export Causalean.Mathlib.LinearAlgebra
  (affineBinaryPower stackedContraction blockVandermondeWitnessWeights
   exists_weights_stackedContraction_injective)

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
