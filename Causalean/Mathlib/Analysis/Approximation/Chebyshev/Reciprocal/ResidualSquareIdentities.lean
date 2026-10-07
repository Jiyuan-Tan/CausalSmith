module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Reciprocal.WitnessPolynomial
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

/-!
# Square identities for the reciprocal residual

The two trigonometric square identities from Plonka and Tasche, Lemma 3.3,
turn the Chebyshev residual into sharp upper and lower bounds on `[-1,1]`.
They also identify the equality conditions used to construct alternation points.
-/

public section

namespace Causalean.Mathlib.Analysis.Approximation.Chebyshev.Reciprocal

open Polynomial

/-- For a [positive lower endpoint a and a strictly larger upper endpoint b](hyp:a,b,ha,hab), a
[degree bound m](hyp:m), and an [angle θ](hyp:θ), [the residual polynomial evaluated at cos θ
equals 2 (v − cos θ) minus 2 / ρ times the square of sin((m + 1)θ/2) − ρ sin((m − 1)θ/2), where v
is the interval shape parameter and ρ the decay parameter](goal). -/
theorem reciprocalResidualPoly_sin_square {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (m : ℕ) (θ : ℝ) :
    (reciprocalResidualPoly a b m).eval (Real.cos θ) =
      2 * (intervalShape a b - Real.cos θ) -
        (2 / intervalDecay a b) *
          (Real.sin (((m : ℝ) + 1) * θ / 2) -
            intervalDecay a b * Real.sin (((m : ℝ) - 1) * θ / 2)) ^ 2 := by
  -- Expand `T_real_cos`, then apply the cosine subtraction and double-angle
  -- identities. `intervalDecay_add_inv` identifies `ρ + ρ⁻¹` with `2v`.
  -- A useful intermediate form (Plonka--Tasche, Lemma 3.3) is
  -- R(cos θ) - 2(v-cos θ) = ρ⁻¹(cos((m+1)θ)-1)
  --   - 2(cos(mθ)-cos θ) + ρ(cos((m-1)θ)-1).
  -- Rewrite the three differences as squares/products of half-angle sines;
  -- `ring` then factors the result. The integer Chebyshev index covers m=0.
  let ρ := intervalDecay a b
  let v := intervalShape a b
  let x := (((m : ℝ) + 1) * θ) / 2
  let y := (((m : ℝ) - 1) * θ) / 2
  have hρ : ρ ≠ 0 := ne_of_gt (intervalDecay_mem_Ioo ha hab).1
  have hsum : ρ + ρ⁻¹ = 2 * v := intervalDecay_add_inv ha hab
  have hR : (reciprocalResidualPoly a b m).eval (Real.cos θ) =
      ρ⁻¹ * Real.cos (((m : ℝ) + 1) * θ) -
        2 * Real.cos ((m : ℝ) * θ) +
        ρ * Real.cos (((m : ℝ) - 1) * θ) := by
    simp only [reciprocalResidualPoly, eval_add, eval_sub, eval_mul, eval_C,
      Chebyshev.T_real_cos]
    push_cast
    ring
  have hplus : Real.cos (((m : ℝ) + 1) * θ) = 1 - 2 * Real.sin x ^ 2 := by
    calc
      _ = Real.cos (2 * x) := by congr 1; dsimp [x]; ring
      _ = _ := Real.cos_two_mul_eq_one_sub x
  have hminus : Real.cos (((m : ℝ) - 1) * θ) = 1 - 2 * Real.sin y ^ 2 := by
    calc
      _ = Real.cos (2 * y) := by congr 1; dsimp [y]; ring
      _ = _ := Real.cos_two_mul_eq_one_sub y
  have hx : (((m : ℝ) * θ + θ) / 2) = x := by dsimp [x]; ring
  have hy : (((m : ℝ) * θ - θ) / 2) = y := by dsimp [y]; ring
  have hmid : Real.cos ((m : ℝ) * θ) - Real.cos θ =
      -2 * Real.sin x * Real.sin y := by
    simpa only [hx, hy] using Real.cos_sub_cos ((m : ℝ) * θ) θ
  change (reciprocalResidualPoly a b m).eval (Real.cos θ) =
    2 * (v - Real.cos θ) - (2 / ρ) * (Real.sin x - ρ * Real.sin y) ^ 2
  rw [hR, hplus, hminus]
  have hmid' : Real.cos ((m : ℝ) * θ) =
      Real.cos θ - 2 * Real.sin x * Real.sin y := by linarith
  rw [hmid']
  field_simp [hρ] at hsum ⊢
  nlinarith [hsum]

/-- [Positive interval endpoints](hyp:a,b,ha,hab), a [degree bound](hyp:m), and
an [angle](hyp:θ) imply [the cosine-square identity for the residual at that
angle](goal). -/
theorem reciprocalResidualPoly_cos_square {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (m : ℕ) (θ : ℝ) :
    (reciprocalResidualPoly a b m).eval (Real.cos θ) =
      -2 * (intervalShape a b - Real.cos θ) +
        (2 / intervalDecay a b) *
          (Real.cos (((m : ℝ) + 1) * θ / 2) -
            intervalDecay a b * Real.cos (((m : ℝ) - 1) * θ / 2)) ^ 2 := by
  -- Expand `T_real_cos`, then apply the cosine addition and double-angle
  -- identities. `intervalDecay_add_inv` identifies `ρ + ρ⁻¹` with `2v`.
  -- The corresponding intermediate form is
  -- R(cos θ) + 2(v-cos θ) = ρ⁻¹(cos((m+1)θ)+1)
  --   - 2(cos(mθ)+cos θ) + ρ(cos((m-1)θ)+1).
  -- Rewrite the three sums as half-angle cosine products and factor by `ring`.
  let ρ := intervalDecay a b
  let v := intervalShape a b
  let x := (((m : ℝ) + 1) * θ) / 2
  let y := (((m : ℝ) - 1) * θ) / 2
  have hρ : ρ ≠ 0 := ne_of_gt (intervalDecay_mem_Ioo ha hab).1
  have hsum : ρ + ρ⁻¹ = 2 * v := intervalDecay_add_inv ha hab
  have hR : (reciprocalResidualPoly a b m).eval (Real.cos θ) =
      ρ⁻¹ * Real.cos (((m : ℝ) + 1) * θ) -
        2 * Real.cos ((m : ℝ) * θ) +
        ρ * Real.cos (((m : ℝ) - 1) * θ) := by
    simp only [reciprocalResidualPoly, eval_add, eval_sub, eval_mul, eval_C,
      Chebyshev.T_real_cos]
    push_cast
    ring
  have hplus : Real.cos (((m : ℝ) + 1) * θ) = 2 * Real.cos x ^ 2 - 1 := by
    calc
      _ = Real.cos (2 * x) := by congr 1; dsimp [x]; ring
      _ = _ := Real.cos_two_mul x
  have hminus : Real.cos (((m : ℝ) - 1) * θ) = 2 * Real.cos y ^ 2 - 1 := by
    calc
      _ = Real.cos (2 * y) := by congr 1; dsimp [y]; ring
      _ = _ := Real.cos_two_mul y
  have hx : (((m : ℝ) * θ + θ) / 2) = x := by dsimp [x]; ring
  have hy : (((m : ℝ) * θ - θ) / 2) = y := by dsimp [y]; ring
  have hmid : Real.cos ((m : ℝ) * θ) + Real.cos θ =
      2 * Real.cos x * Real.cos y := by
    simpa only [hx, hy] using Real.cos_add_cos ((m : ℝ) * θ) θ
  change (reciprocalResidualPoly a b m).eval (Real.cos θ) =
    -2 * (v - Real.cos θ) + (2 / ρ) * (Real.cos x - ρ * Real.cos y) ^ 2
  rw [hR, hplus, hminus]
  have hmid' : Real.cos ((m : ℝ) * θ) =
      2 * Real.cos x * Real.cos y - Real.cos θ := by linarith
  rw [hmid']
  field_simp [hρ] at hsum ⊢
  nlinarith [hsum]

end Causalean.Mathlib.Analysis.Approximation.Chebyshev.Reciprocal
