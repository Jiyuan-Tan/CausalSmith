module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.Converse.Interpolation
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.LobattoLagrange

/-! # Exterior Lagrange mass for the normalized paired prior -/

@[expose] public section

open Polynomial
open scoped BigOperators

namespace CausalSmith.Stat.MarNearcompleteFrontier

open Causalean.Mathlib.Analysis.Approximation.Chebyshev






-- @node: lagrangeNorm_eq_abs_chebyshev
/-- The qid's Lagrange normalization is exactly its calibrated exterior
Chebyshev value. Given [the specified input `n`](hyp:n), [the stated mathematical conclusion holds](goal). -/
lemma lagrangeNorm_eq_abs_chebyshev (n : ℕ) :
    lagrangeNorm n =
      |(Polynomial.Chebyshev.T ℝ ((priorK n - 1 : ℕ) : ℤ)).eval
        (-(1 + priorH n) / (1 - priorH n))| := by
  have hK := priorK_ge_two n
  have ha0 : 0 < priorH n := by
    unfold priorH
    positivity
  have ha1 : priorH n < 1 := by
    have hk : (1 : ℝ) < priorK n := by exact_mod_cast (show 1 < priorK n by omega)
    have hi : (priorK n : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hk
    have hi0 : (0 : ℝ) < (priorK n : ℝ)⁻¹ := by positivity
    unfold priorH
    nlinarith
  have hcard : priorK n - 1 + 1 = priorK n := by omega
  have h := shifted_chebyshev_lagrange_abs_sum (priorK n - 1) (priorH n) ha0 ha1
  rw [hcard] at h
  have hnodes : interpolationNode n =
      (fun j : Fin (priorK n) =>
        (1 + priorH n) / 2 + (1 - priorH n) / 2 *
          Real.cos ((j : ℝ) * Real.pi / ((priorK n - 1 : ℕ) : ℝ))) := by
    rfl
  rw [lagrangeNorm]
  simp only [lagrangeAtZero, hnodes]
  simpa [Polynomial.Chebyshev.node] using h

-- @node: lagrangeNorm_le_cosh_two
/-- Uniform exterior mass bound for the normalized paired prior. Given [the specified input `n`](hyp:n), [the stated mathematical conclusion holds](goal). -/
lemma lagrangeNorm_le_cosh_two (n : ℕ) : lagrangeNorm n ≤ Real.cosh 2 := by
  rw [lagrangeNorm_eq_abs_chebyshev]
  simpa [priorH] using
    calibrated_chebyshev_exterior_le_cosh_two (priorK n) (priorK_ge_two n)

end CausalSmith.Stat.MarNearcompleteFrontier
