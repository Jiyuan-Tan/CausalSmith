module
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.ENNReal.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Scalar quadratic minimization

Completion of the square for positive real weights and complex scalars provides
the pointwise engine for weighted L² interpolation. This module is independent
of the measure-theoretic and embedded-endpoint branches.
-/

public section
noncomputable section
namespace Causalean.Mathlib.Analysis.RealInterpolation

/-- [Positive real weights](hyp:a,b,ha,hb) and [two complex summands](hyp:z0,z1)
satisfy [the harmonic-weight quadratic lower bound](goal).

Multiply by a+b and use the nonnegativity of the squared norm of a*z0-b*z1,
or complete the square using the real and imaginary parts. -/
theorem harmonic_quadratic_le (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (z0 z1 : ℂ) :
    a * b / (a + b) * ‖z0 + z1‖ ^ 2 ≤ a * ‖z0‖ ^ 2 + b * ‖z1‖ ^ 2 := by
  have hab : 0 < a + b := add_pos ha hb
  rw [div_mul_eq_mul_div, div_le_iff₀ hab]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im]
  nlinarith [sq_nonneg (a * z0.re - b * z1.re),
    sq_nonneg (a * z0.im - b * z1.im)]

/-- [Positive real weights](hyp:a,b,ha,hb) and [a complex vector](hyp:z)
have [an explicit minimizing quadratic decomposition](goal).
The first summand has coefficient b/(a+b), and the second has coefficient a/(a+b). -/
theorem harmonic_quadratic_attained (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (z : ℂ) :
    z = (b / (a + b)) • z + (a / (a + b)) • z ∧
    a * ‖(b / (a + b)) • z‖ ^ 2 + b * ‖(a / (a + b)) • z‖ ^ 2 =
      a * b / (a + b) * ‖z‖ ^ 2 := by
  have hab : a + b ≠ 0 := ne_of_gt (add_pos ha hb)
  constructor
  · rw [← add_smul]
    have hsum : b / (a + b) + a / (a + b) = 1 := by
      field_simp
      ring
    rw [hsum, one_smul]
  · simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    field_simp
    ring

/-- For [positive real weights a and b](hyp:a,b,ha,hb) and [a complex number z](hyp:z),
[the infimum of a·|z0|² + b·|z1|² over all decompositions z = z0 + z1 equals
a·b/(a+b)·|z|²](goal). -/
theorem harmonic_quadratic_iInf (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (z : ℂ) :
    (⨅ (z0 : ℂ) (z1 : ℂ) (_ : z = z0 + z1),
      ENNReal.ofReal (a * ‖z0‖ ^ 2 + b * ‖z1‖ ^ 2)) =
        ENNReal.ofReal (a * b / (a + b) * ‖z‖ ^ 2) := by
  apply le_antisymm
  · obtain ⟨hsum, hvalue⟩ := harmonic_quadratic_attained a b ha hb z
    calc
      _ ≤ ENNReal.ofReal (a * ‖(b / (a + b)) • z‖ ^ 2 +
          b * ‖(a / (a + b)) • z‖ ^ 2) :=
        iInf_le_of_le ((b / (a + b)) • z)
          (iInf_le_of_le ((a / (a + b)) • z) (iInf_le_of_le hsum le_rfl))
      _ = _ := congrArg ENNReal.ofReal hvalue
  · refine le_iInf fun z0 => le_iInf fun z1 => le_iInf fun hsum => ?_
    apply ENNReal.ofReal_le_ofReal
    rw [hsum]
    exact harmonic_quadratic_le a b ha hb z0 z1

end Causalean.Mathlib.Analysis.RealInterpolation
