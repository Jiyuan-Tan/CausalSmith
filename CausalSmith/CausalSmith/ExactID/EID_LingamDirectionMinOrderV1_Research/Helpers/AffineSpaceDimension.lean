/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Mathlib.AlgebraicGeometry.Dimension.PolynomialMap.AffineSpaceDimension
public import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.AlgebraicSetChains

/-!
# Compatibility reexports for affine-space dimension

The chain-dimension implementation is neutral substrate; this file preserves
the original paper-facing declaration names.
-/

public section

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

export Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension
  (HasAffineZariskiDimension affineSpace_hasAffineZariskiDimension)

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
