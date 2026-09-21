/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Mathlib.AlgebraicGeometry.Dimension.PolynomialMap.CodimensionOne
public import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.FiniteCodimensionTransfer

/-!
# Compatibility reexports for affine codimension-one certificates

The reusable chain and principal-height arguments live in Causalean. This file
preserves the paper-facing names used by the exceptional-locus specialization.
-/

public section

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

export Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension
  (no_three_chain_of_minimalPrime_span
   no_intermediate_of_exact_affine_dimensions
   irreducibleAffineComponent_of_no_intermediate
   vanishingIdeal_mem_minimalPrimes_span_of_no_intermediate
   hasAffineCodimensionIn_one_of_minimalPrime_span)

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
