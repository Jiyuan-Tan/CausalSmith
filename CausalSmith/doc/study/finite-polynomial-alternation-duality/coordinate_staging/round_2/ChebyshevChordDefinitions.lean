/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema

/-!
# Chord data for the Chebyshev root grid

This module defines the finite chord list used in the trigonometric proof of
the Chebyshev vertical-modulus comparison. The list records the two circle
chords associated with each cosine root.
-/

namespace Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality

/-- The angle `(2k+1)π/(2L)` of the `k`-th degree-`L` Chebyshev root. [the stated inputs](hyp:L,k) establish [the defined object](goal). -/
noncomputable def chebyshevRootAngle (L k : ℕ) : ℝ :=
  (((2 * k + 1 : ℕ) : ℝ) * Real.pi) / (2 * (L : ℝ))

/-- The `k`-th cosine root used in the degree-`L` Chebyshev product, indexed by
`0 ≤ k < L`. [the stated inputs](hyp:L,k) establish [the defined object](goal). -/
noncomputable def chebyshevZero (L k : ℕ) : ℝ :=
  Real.cos (chebyshevRootAngle L k)

/-- The squared chord length from `1` to the point of the unit circle with
argument `θ`. [The stated angle](hyp:θ) determines [the defined object](goal). -/
noncomputable def cosineChordSq (θ : ℝ) : ℝ :=
  2 - 2 * Real.cos θ

/-- The `2L` chord squares associated with an abscissa angle `θ`, listed in
the two-element pairs belonging to the `L` Chebyshev root angles. [The degree
and angle](hyp:L,θ) determine [the defined object](goal). -/
noncomputable def chebyshevPairedChordList (L : ℕ) (θ : ℝ) : List ℝ :=
  (Finset.range L).val.toList.flatMap fun k =>
    [cosineChordSq (θ + chebyshevRootAngle L k),
      cosineChordSq (θ - chebyshevRootAngle L k)]

end Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality
