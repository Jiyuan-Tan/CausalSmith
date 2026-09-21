/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

/-!
# Positive-density graphoid intersection

This module gathers the product-density factorization tools, the four-block graphoid
intersection theorem, and its finite-coordinate specialization.  It is graph-independent:
any finite law with an almost-everywhere strictly positive density relative to a product
reference measure can use the exported conditional-independence conclusions.
-/

import Causalean.Mathlib.CondIndep.PositiveDensityIntersection.FiniteCoordinates
