/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import CausalSmith.Substrate.Archive.FinitePolynomialAlternationDuality.ChebyshevRootReflection
public import CausalSmith.Substrate.Archive.FinitePolynomialAlternationDuality.HalfPlaneBoundaryDerivative

/-!
# Half-plane derivative comparison at Chebyshev roots

This module isolates the half-plane comparison input in the
Duffin--Schaeffer proof.  It is the first-derivative, Chebyshev-denominator
specialization of the classical comparison theorem: derivative control at
the real roots propagates from a vertical modulus comparison to the endpoint.
-/

public section

open Polynomial Set

namespace CausalSmith.Substrate.FinitePolynomialAlternationDuality

/-- Suppose a degree-at-most-`L` real polynomial has derivative bounded by
`T_L'` at every real zero of `T_L`.  At a point `x ∈ [-1,1]`, if the complex
modulus of `T_L` on the vertical line through `x` is dominated by the vertical
line through `1`, then the polynomial's derivative at `x` is bounded by
`|T_L'(1)|`. -/
theorem abs_eval_derivative_le_chebyshev_endpoint_of_root_control
    {L : ℕ} (hL : 0 < L) (Q : Polynomial ℝ) (hQ : Q.natDegree ≤ L)
    (hroots : ∀ z : ℝ,
      (Polynomial.Chebyshev.T ℝ (L : ℤ)).eval z = 0 →
        |Q.derivative.eval z| ≤
          |(Polynomial.Chebyshev.T ℝ (L : ℤ)).derivative.eval z|)
    {x : ℝ} (hx : x ∈ Set.Icc (-1) 1)
    (hvertical : ∀ y : ℝ,
      ‖(Polynomial.Chebyshev.T ℂ (L : ℤ)).eval
          ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤
        ‖(Polynomial.Chebyshev.T ℂ (L : ℤ)).eval
          ((1 : ℂ) + (y : ℂ) * Complex.I)‖) :
    |Q.derivative.eval x| ≤
      |(Polynomial.Chebyshev.T ℝ (L : ℤ)).derivative.eval 1| := by
  obtain ⟨R, hRdeg, hRvertical, hQderiv⟩ :=
    exists_chebyshevRootReflection hL Q hQ hroots x
  refine hQderiv.trans (norm_eval_derivative_zero_le_chebyshev_endpoint_of_vertical
    hL R hRdeg ?_)
  intro y
  rw [hRvertical y]
  exact hvertical y

end CausalSmith.Substrate.FinitePolynomialAlternationDuality
