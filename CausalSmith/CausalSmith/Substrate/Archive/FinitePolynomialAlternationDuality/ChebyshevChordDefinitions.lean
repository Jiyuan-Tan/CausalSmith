/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema

/-!
# Chord data for the Chebyshev root grid

This module defines the finite chord list used in the trigonometric proof of
the Chebyshev vertical-modulus comparison. The list records the two circle
chords associated with each cosine root.
-/

@[expose] public section

namespace CausalSmith.Substrate.FinitePolynomialAlternationDuality

/-- The angle `(2k+1)π/(2L)` of the `k`-th degree-`L` Chebyshev root. -/
noncomputable def chebyshevRootAngle (L k : ℕ) : ℝ :=
  (((2 * k + 1 : ℕ) : ℝ) * Real.pi) / (2 * (L : ℝ))

/-- The `k`-th cosine root used in the degree-`L` Chebyshev product, indexed by
`0 ≤ k < L`. -/
noncomputable def chebyshevZero (L k : ℕ) : ℝ :=
  Real.cos (chebyshevRootAngle L k)

/-- The squared chord length from `1` to the point of the unit circle with
argument `θ`. -/
noncomputable def cosineChordSq (θ : ℝ) : ℝ :=
  2 - 2 * Real.cos θ

/-- The `2L` chord squares associated with an abscissa angle `θ`, listed in
the two-element pairs belonging to the `L` Chebyshev root angles. -/
noncomputable def chebyshevPairedChordList (L : ℕ) (θ : ℝ) : List ℝ :=
  (Finset.range L).val.toList.flatMap fun k =>
    [cosineChordSq (θ + chebyshevRootAngle L k),
      cosineChordSq (θ - chebyshevRootAngle L k)]

end CausalSmith.Substrate.FinitePolynomialAlternationDuality
