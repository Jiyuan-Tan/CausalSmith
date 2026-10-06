module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.GKCoefficient
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.Coefficients

/-! Fejér/Chebyshev representation used by the generic `GK` certificate. -/

@[expose] public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open scoped BigOperators
open Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson

/-- The normalized finite Fejér cosine polynomial of order `K`. -/
@[no_expose]
noncomputable def fejerResidual (K : ℕ) (u : ℝ) : ℝ :=
  (∑ j ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
    triangle K j * Real.cos ((j : ℝ) * u)) / (K : ℝ) ^ 2

/-- The finite Fejér polynomial is the normalized square of `U_{K-1}`. -/
lemma fejerResidual_eq_chebyshev_sq (K : ℕ) (hK : 0 < K) (u : ℝ) :
    fejerResidual K u =
      ((Polynomial.Chebyshev.U ℝ ((K - 1 : ℕ) : ℤ)).eval
        (Real.cos (u / 2))) ^ 2 / (K : ℝ) ^ 2 := by
  unfold fejerResidual
  rw [← triangle_fourier K hK u]

/-- Away from the zeros of the denominator, the Fejér polynomial is the
squared multiple-angle sine quotient from equation (21). -/
lemma fejerResidual_eq_sine_quotient_sq (K : ℕ) (hK : 0 < K) (u : ℝ)
    (hsin : Real.sin (u / 2) ≠ 0) :
    fejerResidual K u =
      (Real.sin ((K : ℝ) * (u / 2)) /
        ((K : ℝ) * Real.sin (u / 2))) ^ 2 := by
  rw [fejerResidual_eq_chebyshev_sq K hK]
  have hU := Polynomial.Chebyshev.U_real_cos (u / 2) ((K - 1 : ℕ) : ℤ)
  have hU' :
      (Polynomial.Chebyshev.U ℝ ((K - 1 : ℕ) : ℤ)).eval
          (Real.cos (u / 2)) * Real.sin (u / 2) =
        Real.sin ((K : ℝ) * (u / 2)) := by
    convert hU using 1
    congr 2
    norm_num
    exact_mod_cast (show K = K - 1 + 1 by omega)
  have hsquare := congrArg (fun z : ℝ => z ^ 2) hU'
  have hang : Real.sin ((K : ℝ) * (u / 2)) = Real.sin (u * K / 2) := by
    congr 1
    ring
  rw [hang] at hsquare
  ring_nf at hsquare
  field_simp [hsin, show (K : ℝ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hK]
  simpa [div_eq_mul_inv, mul_assoc] using hsquare

/-- The elementary multiple-angle estimate needed for the unit Fejér bound. -/
lemma abs_sin_nat_mul_le (K : ℕ) (u : ℝ) :
    |Real.sin ((K : ℝ) * u)| ≤ (K : ℝ) * |Real.sin u| := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Nat.cast_succ]
      have harg : ((K : ℝ) + 1) * u = (K : ℝ) * u + u := by ring
      rw [harg, Real.sin_add]
      calc
        |Real.sin ((K : ℝ) * u) * Real.cos u +
            Real.cos ((K : ℝ) * u) * Real.sin u| ≤
            |Real.sin ((K : ℝ) * u)| * |Real.cos u| +
              |Real.cos ((K : ℝ) * u)| * |Real.sin u| := by
                simpa only [abs_mul] using
                  (abs_add_le (Real.sin ((K : ℝ) * u) * Real.cos u)
                    (Real.cos ((K : ℝ) * u) * Real.sin u))
        _ ≤ |Real.sin ((K : ℝ) * u)| + |Real.sin u| := by
          have hsin0 : 0 ≤ |Real.sin ((K : ℝ) * u)| := abs_nonneg _
          have hsin1 : 0 ≤ |Real.sin u| := abs_nonneg _
          nlinarith [Real.abs_cos_le_one u,
            Real.abs_cos_le_one ((K : ℝ) * u)]
        _ ≤ ((K : ℝ) + 1) * |Real.sin u| := by
          nlinarith [abs_nonneg (Real.sin u)]

/-- A positive-order Fejér residual is nonnegative. -/
lemma fejerResidual_nonneg (K : ℕ) (hK : 0 < K) (u : ℝ) :
    0 ≤ fejerResidual K u := by
  rw [fejerResidual_eq_chebyshev_sq K hK]
  positivity

/-- Away from denominator zeros, the normalized Fejér residual is at most one. -/
lemma fejerResidual_le_one (K : ℕ) (hK : 0 < K) (u : ℝ)
    (hsin : Real.sin (u / 2) ≠ 0) :
    fejerResidual K u ≤ 1 := by
  rw [fejerResidual_eq_sine_quotient_sq K hK u hsin]
  have hK0 : (0 : ℝ) ≤ K := by positivity
  have habs := abs_sin_nat_mul_le K (u / 2)
  have hden : |(K : ℝ) * Real.sin (u / 2)| =
      (K : ℝ) * |Real.sin (u / 2)| := by rw [abs_mul, abs_of_nonneg hK0]
  have hquot :
      |Real.sin ((K : ℝ) * (u / 2)) /
          ((K : ℝ) * Real.sin (u / 2))| ≤ 1 := by
    rw [abs_div, hden]
    exact (div_le_one (mul_pos (by positivity) (abs_pos.mpr hsin))).2 habs
  simpa only [one_pow] using (sq_le_sq).2 (show
    |Real.sin ((K : ℝ) * (u / 2)) / ((K : ℝ) * Real.sin (u / 2))| ≤ |(1 : ℝ)| by
      simpa using hquot)

/-- The unit bound also holds at the removable zeros of the sine quotient. -/
lemma fejerResidual_le_one_all (K : ℕ) (hK : 0 < K) (u : ℝ) :
    fejerResidual K u ≤ 1 := by
  by_cases hsin : Real.sin (u / 2) = 0
  · rw [fejerResidual_eq_chebyshev_sq K hK]
    rcases Real.sin_eq_zero_iff_cos_eq.mp hsin with hcos | hcos
    · rw [hcos, Polynomial.Chebyshev.U_eval_one]
      have hcast : ((((K - 1 : ℕ) : ℤ) : ℝ) + 1) = (K : ℝ) := by
        exact_mod_cast (show K - 1 + 1 = K by omega)
      rw [hcast]
      field_simp [show (K : ℝ) ≠ 0 by positivity]
      exact le_rfl
    · rw [hcos, Polynomial.Chebyshev.U_eval_neg_one]
      have hcast : ((((K - 1 : ℕ) : ℤ) : ℝ) + 1) = (K : ℝ) := by
        exact_mod_cast (show K - 1 + 1 = K by omega)
      rw [hcast, mul_pow]
      field_simp [show (K : ℝ) ≠ 0 by positivity]
      have hu :
          (((((K - 1 : ℕ) : ℤ).negOnePow : ℤ) : ℝ) *
            (((K - 1 : ℕ) : ℤ).negOnePow : ℤ) : ℝ) = 1 := by
        simpa only [Units.val_mul, Units.val_one, Int.cast_mul, Int.cast_one] using
          congrArg (fun z : ℤˣ => (((z : ℤ) : ℝ)))
            (Int.units_mul_self (((K - 1 : ℕ) : ℤ).negOnePow))
      calc
        (((((K - 1 : ℕ) : ℤ).negOnePow : ℤ) : ℝ)) ^ 2 = 1 := by
          simpa only [pow_two] using hu
        _ ≤ 1 := le_rfl
  · apply fejerResidual_le_one K hK u
    exact hsin

/-- Away from denominator zeros, the normalized Fejér residual has the
inverse-square bound used in equation (22). -/
lemma fejerResidual_le_inv_sin_sq (K : ℕ) (hK : 0 < K) (u : ℝ)
    (hsin : Real.sin (u / 2) ≠ 0) :
    fejerResidual K u ≤ 1 / ((K : ℝ) ^ 2 * Real.sin (u / 2) ^ 2) := by
  rw [fejerResidual_eq_sine_quotient_sq K hK u hsin]
  have hnum := Real.abs_sin_le_one ((K : ℝ) * (u / 2))
  have hden : (0 : ℝ) < ((K : ℝ) * Real.sin (u / 2)) ^ 2 :=
    sq_pos_of_ne_zero (mul_ne_zero (by positivity) hsin)
  rw [div_pow]
  have hdeneq : ((K : ℝ) * Real.sin (u / 2)) ^ 2 =
      (K : ℝ) ^ 2 * Real.sin (u / 2) ^ 2 := by ring
  rw [← hdeneq]
  apply (div_le_div_iff_of_pos_right hden).2
  simpa only [one_pow] using (sq_le_sq).2 (show
    |Real.sin ((K : ℝ) * (u / 2))| ≤ |(1 : ℝ)| by simpa using hnum)

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
