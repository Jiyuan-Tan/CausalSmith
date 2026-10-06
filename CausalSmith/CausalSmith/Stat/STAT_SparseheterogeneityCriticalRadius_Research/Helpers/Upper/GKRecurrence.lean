module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.GKFejer

/-! The order recurrence reducing the binomial residual to the Fejér residual. -/

@[expose] public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open scoped BigOperators

/-- Unnormalized residual coefficients.  The corresponding polynomial is
`K² (1 - x GK(x))`. -/
@[no_expose]
noncomputable def scaledResidualCoeff (K r : ℕ) : ℝ :=
  (K : ℝ) ^ 2 * gResidualCoeff K r

/-- The constant coefficient of the unnormalized residual is `K²`. -/
lemma scaledResidualCoeff_zero (K : ℕ) (hK : 0 < K) :
    scaledResidualCoeff K 0 = (K : ℝ) ^ 2 := by
  rw [scaledResidualCoeff, gResidualCoeff_zero K hK, mul_one]

/-- The constant coefficients obey the inhomogeneous part of the Fejér
order recurrence. -/
lemma scaledResidualCoeff_zero_order_recurrence (K : ℕ) (hK : 1 < K) :
    scaledResidualCoeff (K + 1) 0 + scaledResidualCoeff (K - 1) 0 =
      2 * scaledResidualCoeff K 0 + 2 := by
  rw [scaledResidualCoeff_zero (K + 1) (by omega),
    scaledResidualCoeff_zero (K - 1) (by omega),
    scaledResidualCoeff_zero K (by omega)]
  rw [Nat.cast_sub (by omega : 1 ≤ K)]
  push_cast
  ring

/-- A denominator-free binomial presentation of every nonzero-order scaled
coefficient. -/
lemma scaledResidualCoeff_closed (K r : ℕ) (hK : 0 < K) :
    scaledResidualCoeff K r =
      (-1 : ℝ) ^ r * 2 ^ (2 * r + 1) * (K : ℝ) *
        (Nat.choose (K + r) (2 * r + 1) : ℝ) / (2 * r + 2 : ℕ) := by
  rw [scaledResidualCoeff]
  rw [gResidualCoeff_def]
  have hc := congrArg (fun n : ℕ => (n : ℝ))
    (Nat.add_one_mul_choose_eq (K + r) (2 * r + 1))
  push_cast at hc
  have hKn : (K : ℝ) ≠ 0 := by positivity
  have hsum : ((K + r + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have htwo : ((2 * r + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  have hratio :
      (Nat.choose (K + r + 1) (2 * r + 2) : ℝ) /
          (K + r + 1 : ℕ) =
        (Nat.choose (K + r) (2 * r + 1) : ℝ) /
          (2 * r + 2 : ℕ) := by
    apply (div_eq_div_iff hsum htwo).2
    push_cast
    ring_nf at hc ⊢
    linear_combination -hc
  calc
    (K : ℝ) ^ 2 *
        ((-1 : ℝ) ^ r * 2 ^ (2 * r + 1) *
          (Nat.choose (K + r + 1) (2 * r + 2) : ℝ) /
          ((K : ℝ) * (K + r + 1 : ℕ))) =
      (-1 : ℝ) ^ r * 2 ^ (2 * r + 1) *
        (Nat.choose (K + r + 1) (2 * r + 2) : ℝ) * (K : ℝ) /
          (K + r + 1 : ℕ) := by
            field_simp [hKn, hsum]
    _ = _ := by
      calc
        _ = (-1 : ℝ) ^ r * 2 ^ (2 * r + 1) * (K : ℝ) *
            ((Nat.choose (K + r + 1) (2 * r + 2) : ℝ) /
              (K + r + 1 : ℕ)) := by ring
        _ = _ := by rw [hratio]; ring

private lemma choose_order_second_difference (K r : ℕ) (hK : 0 < K)
    (hr : 0 < r) (hrK : r ≤ K) :
    (r : ℝ) *
        (((K + 1 : ℕ) : ℝ) * (Nat.choose (K + r + 1) (2 * r + 1) : ℝ) +
          ((K - 1 : ℕ) : ℝ) * (Nat.choose (K + r - 1) (2 * r + 1) : ℝ) -
          2 * (K : ℝ) * (Nat.choose (K + r) (2 * r + 1) : ℝ)) =
      ((r + 1 : ℕ) : ℝ) * (K : ℝ) *
        (Nat.choose (K + r - 1) (2 * r - 1) : ℝ) := by
  have hp : (Nat.choose (K + r + 1) (2 * r + 1) : ℝ) =
      (Nat.choose (K + r) (2 * r) : ℝ) +
        (Nat.choose (K + r) (2 * r + 1) : ℝ) := by
    exact_mod_cast Nat.choose_succ_succ' (K + r) (2 * r)
  have h0 : (Nat.choose (K + r) (2 * r + 1) : ℝ) =
      (Nat.choose (K + r - 1) (2 * r) : ℝ) +
        (Nat.choose (K + r - 1) (2 * r + 1) : ℝ) := by
    have hKr : K + r = (K + r - 1) + 1 := by omega
    rw [hKr]
    exact_mod_cast Nat.choose_succ_succ' (K + r - 1) (2 * r)
  have h1 : (Nat.choose (K + r) (2 * r) : ℝ) =
      (Nat.choose (K + r - 1) (2 * r - 1) : ℝ) +
        (Nat.choose (K + r - 1) (2 * r) : ℝ) := by
    have hKr : K + r = (K + r - 1) + 1 := by omega
    have h2r : 2 * r = (2 * r - 1) + 1 := by omega
    rw [hKr, h2r]
    exact_mod_cast Nat.choose_succ_succ' (K + r - 1) (2 * r - 1)
  have haNat := Nat.choose_succ_right_eq (K + r - 1) (2 * r - 1)
  have hsub : K + r - 1 - (2 * r - 1) = K - r := by omega
  have hidx : 2 * r - 1 + 1 = 2 * r := by omega
  rw [hsub, hidx] at haNat
  have ha := congrArg (fun n : ℕ => (n : ℝ)) haNat
  push_cast at ha ⊢
  rw [Nat.cast_sub (by omega : 1 ≤ K)]
  rw [Nat.cast_sub hrK] at ha
  ring_nf at hp h0 h1 ha ⊢
  rw [hp, h0, h1]
  ring_nf
  linear_combination ha

/-- Interior nonconstant coefficients obey the homogeneous part of the
Fejér order recurrence. -/
lemma scaledResidualCoeff_order_recurrence (K r : ℕ) (hK : 1 < K)
    (hr : 0 < r) (hrK : r ≤ K) :
    scaledResidualCoeff (K + 1) r + scaledResidualCoeff (K - 1) r =
      2 * scaledResidualCoeff K r - 4 * scaledResidualCoeff K (r - 1) := by
  rw [scaledResidualCoeff_closed (K + 1) r (by omega),
    scaledResidualCoeff_closed (K - 1) r (by omega),
    scaledResidualCoeff_closed K r (by omega),
    scaledResidualCoeff_closed K (r - 1) (by omega)]
  have hc := choose_order_second_difference K r (by omega) hr hrK
  have hrpred : r = (r - 1) + 1 := by omega
  have hsign : (-1 : ℝ) ^ r = -((-1 : ℝ) ^ (r - 1)) := by
    have hpw := congrArg (fun n : ℕ => (-1 : ℝ) ^ n) hrpred
    calc
      (-1 : ℝ) ^ r = (-1 : ℝ) ^ ((r - 1) + 1) := hpw
      _ = -((-1 : ℝ) ^ (r - 1)) := by rw [pow_succ]; ring
  have hpow : (2 : ℝ) ^ (2 * r + 1) =
      4 * (2 : ℝ) ^ (2 * r - 1) := by
    have he : 2 * r + 1 = (2 * r - 1) + 2 := by omega
    rw [he, pow_add]
    norm_num
    ring
  have hplus : K + 1 + r = K + r + 1 := by omega
  have hminus : K - 1 + r = K + r - 1 := by omega
  have hprevK : K + (r - 1) = K + r - 1 := by omega
  have hprevIdx : 2 * (r - 1) + 1 = 2 * r - 1 := by omega
  have hprevDen : 2 * (r - 1) + 2 = 2 * r := by omega
  have hden1 : ((2 * r + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  have hden0 : ((2 * (r - 1) + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [hplus, hminus, hprevK, hprevIdx, hprevDen, hsign]
  field_simp [hden1, hden0]
  rw [Nat.cast_sub (by omega : 1 ≤ K)] at hc ⊢
  push_cast at hc ⊢
  rw [hpow]
  have hs := congrArg
    (fun z : ℝ => -((2 : ℝ) ^ (2 * r - 1) * 8) * z) hc
  ring_nf at hs ⊢
  linear_combination hs

/-- The nonconstant order recurrence, including the zero-extended tail. -/
lemma scaledResidualCoeff_order_recurrence_all (K r : ℕ) (hK : 1 < K)
    (hr : 0 < r) :
    scaledResidualCoeff (K + 1) r + scaledResidualCoeff (K - 1) r =
      2 * scaledResidualCoeff K r - 4 * scaledResidualCoeff K (r - 1) := by
  by_cases hrK : r ≤ K
  · exact scaledResidualCoeff_order_recurrence K r hK hr hrK
  · have hK1r : K + 1 ≤ r := by omega
    have hKr : K ≤ r := by omega
    have hKm1r : K - 1 ≤ r := by omega
    have hKpred : K ≤ r - 1 := by omega
    simp only [scaledResidualCoeff]
    rw [gResidualCoeff_eq_zero_of_le hK1r,
      gResidualCoeff_eq_zero_of_le hKm1r,
      gResidualCoeff_eq_zero_of_le hKr,
      gResidualCoeff_eq_zero_of_le hKpred]
    ring

/-- The unnormalized explicit residual polynomial. -/
@[no_expose]
noncomputable def scaledResidual (K : ℕ) (x : ℝ) : ℝ :=
  ∑ r ∈ Finset.range K, scaledResidualCoeff K r * x ^ r

/-- Scaling the generic coefficient expansion gives the polynomial form
suited to the order recurrence. -/
lemma scaledResidual_eq (K : ℕ) (hK : 0 < K) (x : ℝ) :
    scaledResidual K x = (K : ℝ) ^ 2 * (1 - x * GK K x) := by
  rw [scaledResidual, one_sub_mul_GK_eq_residual_sum K hK]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  simp only [scaledResidualCoeff]
  ring

/-- The first unnormalized residual is constant one. -/
lemma scaledResidual_one (x : ℝ) : scaledResidual 1 x = 1 := by
  simp [scaledResidual, scaledResidualCoeff, gResidualCoeff_zero]

/-- The second unnormalized residual is `4(1-x)`. -/
lemma scaledResidual_two (x : ℝ) : scaledResidual 2 x = 4 * (1 - x) := by
  rw [scaledResidual_eq 2 (by omega), GK_two]
  ring

/-- Polynomial packaging of the unnormalized residual. -/
@[no_expose]
noncomputable def scaledResidualPoly (K : ℕ) : Polynomial ℝ :=
  ∑ r ∈ Finset.range K,
    Polynomial.C (scaledResidualCoeff K r) * Polynomial.X ^ r

lemma scaledResidualPoly_coeff (K r : ℕ) :
    (scaledResidualPoly K).coeff r =
      if r < K then scaledResidualCoeff K r else 0 := by
  simp [scaledResidualPoly, Finset.mem_range]

lemma scaledResidualPoly_eval (K : ℕ) (x : ℝ) :
    (scaledResidualPoly K).eval x = scaledResidual K x := by
  simp [scaledResidualPoly, scaledResidual, Polynomial.eval_finsetSum]

/-- Summing the coefficient recurrences gives the Fejér order recurrence. -/
lemma scaledResidualPoly_order_recurrence (K : ℕ) (hK : 1 < K) :
    scaledResidualPoly (K + 1) + scaledResidualPoly (K - 1) =
      Polynomial.C 2 * (1 - Polynomial.C 2 * Polynomial.X) *
          scaledResidualPoly K + Polynomial.C 2 := by
  have hform :
      Polynomial.C 2 * (1 - Polynomial.C 2 * Polynomial.X) *
          scaledResidualPoly K + Polynomial.C 2 =
        Polynomial.C 2 * scaledResidualPoly K -
          Polynomial.C 4 * (Polynomial.X * scaledResidualPoly K) + Polynomial.C 2 := by
    have hC : (Polynomial.C 2 : Polynomial ℝ) ^ 2 = Polynomial.C 4 := by
      ext n
      by_cases hn : n = 0 <;> simp [Polynomial.coeff_C, hn, pow_two] <;> norm_num
    calc
      _ = Polynomial.C 2 * scaledResidualPoly K -
          (Polynomial.C 2) ^ 2 * (Polynomial.X * scaledResidualPoly K) +
            Polynomial.C 2 := by ring
      _ = _ := by rw [hC]
  rw [hform]
  ext r
  simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_mul, scaledResidualPoly_coeff]
  by_cases hr : r = 0
  · subst r
    simp only [Nat.zero_lt_succ, if_true, Nat.not_lt_zero, if_false,
      Polynomial.coeff_C_zero, Polynomial.coeff_X_mul_zero, mul_zero, sub_zero]
    rw [if_pos (by omega : 0 < K - 1), if_pos (by omega : 0 < K)]
    simpa using scaledResidualCoeff_zero_order_recurrence K hK
  · have hr0 : 0 < r := Nat.pos_of_ne_zero hr
    have hx : (Polynomial.X * scaledResidualPoly K).coeff r =
        (scaledResidualPoly K).coeff (r - 1) := by
      have hre : (r - 1) + 1 = r := by omega
      rw [← hre]
      exact Polynomial.coeff_X_mul (scaledResidualPoly K) (r - 1)
    rw [hx, scaledResidualPoly_coeff]
    simp only [hr, if_false, Polynomial.coeff_C]
    have hrec := scaledResidualCoeff_order_recurrence_all K r hK hr0
    by_cases hrTop : r < K + 1
    · rw [if_pos hrTop, if_pos (by omega : r - 1 < K)]
      by_cases hrK : r < K
      · rw [if_pos hrK]
        by_cases hrKm : r < K - 1
        · rw [if_pos hrKm]
          simpa using hrec
        · rw [if_neg hrKm]
          have hz : scaledResidualCoeff (K - 1) r = 0 := by
            simp [scaledResidualCoeff,
              gResidualCoeff_eq_zero_of_le (show K - 1 ≤ r by omega)]
          rw [hz] at hrec
          simpa using hrec
      · rw [if_neg hrK, if_neg (by omega : ¬r < K - 1)]
        have hzK : scaledResidualCoeff K r = 0 := by
          simp [scaledResidualCoeff,
            gResidualCoeff_eq_zero_of_le (show K ≤ r by omega)]
        have hzKm : scaledResidualCoeff (K - 1) r = 0 := by
          simp [scaledResidualCoeff,
            gResidualCoeff_eq_zero_of_le (show K - 1 ≤ r by omega)]
        rw [hzK, hzKm] at hrec
        simpa using hrec
    · rw [if_neg hrTop, if_neg (by omega : ¬r < K - 1),
        if_neg (by omega : ¬r < K), if_neg (by omega : ¬r - 1 < K)]
      norm_num

/-- Evaluation form of the summed order recurrence. -/
lemma scaledResidual_order_recurrence (K : ℕ) (hK : 1 < K) (x : ℝ) :
    scaledResidual (K + 1) x + scaledResidual (K - 1) x =
      2 * (1 - 2 * x) * scaledResidual K x + 2 := by
  have h := congrArg (fun p : Polynomial ℝ => p.eval x)
    (scaledResidualPoly_order_recurrence K hK)
  simpa [scaledResidualPoly_eval, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_sub] using h

private lemma sin_sq_order_recurrence (K : ℕ) (hK : 0 < K) (t : ℝ) :
    Real.sin (((K + 1 : ℕ) : ℝ) * t) ^ 2 +
        Real.sin (((K - 1 : ℕ) : ℝ) * t) ^ 2 =
      2 * Real.cos (2 * t) * Real.sin ((K : ℝ) * t) ^ 2 +
        2 * Real.sin t ^ 2 := by
  have hp : (((K + 1 : ℕ) : ℝ) * t) = (K : ℝ) * t + t := by
    push_cast
    ring
  have hm : (((K - 1 : ℕ) : ℝ) * t) = (K : ℝ) * t - t := by
    rw [Nat.cast_sub (by omega : 1 ≤ K)]
    push_cast
    ring
  rw [hp, hm, Real.sin_add, Real.sin_sub, Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq t,
    Real.sin_sq_add_cos_sq ((K : ℝ) * t)]

/-- Unnormalized Fejér residual. -/
@[no_expose]
noncomputable def scaledFejerResidual (K : ℕ) (u : ℝ) : ℝ :=
  (K : ℝ) ^ 2 * fejerResidual K u

lemma scaledFejerResidual_order_recurrence (K : ℕ) (hK : 1 < K) (u : ℝ) :
    scaledFejerResidual (K + 1) u + scaledFejerResidual (K - 1) u =
      2 * Real.cos u * scaledFejerResidual K u + 2 := by
  by_cases hsin : Real.sin (u / 2) = 0
  · have hcosHalf := Real.sin_eq_zero_iff_cos_eq.mp hsin
    have hfej (L : ℕ) (hL : 0 < L) : fejerResidual L u = 1 := by
      rw [fejerResidual_eq_chebyshev_sq L hL]
      rcases hcosHalf with hcos | hcos
      · rw [hcos, Polynomial.Chebyshev.U_eval_one]
        have hc : (((((L - 1 : ℕ) : ℤ) : ℝ)) + 1) = (L : ℝ) := by
          exact_mod_cast (show L - 1 + 1 = L by omega)
        rw [hc]
        field_simp [show (L : ℝ) ≠ 0 by positivity]
      · rw [hcos, Polynomial.Chebyshev.U_eval_neg_one]
        have hc : (((((L - 1 : ℕ) : ℤ) : ℝ)) + 1) = (L : ℝ) := by
          exact_mod_cast (show L - 1 + 1 = L by omega)
        rw [hc, mul_pow]
        have hu := congrArg (fun z : ℤˣ => (((z : ℤ) : ℝ)))
          (Int.units_mul_self (((L - 1 : ℕ) : ℤ).negOnePow))
        simp only [Units.val_mul, Units.val_one, Int.cast_mul, Int.cast_one] at hu
        rw [pow_two, hu]
        field_simp [show (L : ℝ) ≠ 0 by positivity]
    rw [scaledFejerResidual, scaledFejerResidual, scaledFejerResidual,
      hfej (K + 1) (by omega), hfej (K - 1) (by omega), hfej K (by omega)]
    have hcosu : Real.cos u = 1 := by
      rw [show u = 2 * (u / 2) by ring, Real.cos_two_mul]
      nlinarith [Real.sin_sq_add_cos_sq (u / 2)]
    rw [hcosu]
    push_cast
    rw [Nat.cast_sub (by omega : 1 ≤ K)]
    ring
  · rw [scaledFejerResidual, scaledFejerResidual, scaledFejerResidual,
      fejerResidual_eq_sine_quotient_sq (K + 1) (by omega) u hsin,
      fejerResidual_eq_sine_quotient_sq (K - 1) (by omega) u hsin,
      fejerResidual_eq_sine_quotient_sq K (by omega) u hsin]
    have hs := sin_sq_order_recurrence K (by omega) (u / 2)
    have hcos : Real.cos u = Real.cos (2 * (u / 2)) := by congr 1 <;> ring
    have hKm : (((K - 1 : ℕ) : ℝ)) ≠ 0 := by
      exact_mod_cast (show K - 1 ≠ 0 by omega)
    rw [hcos]
    field_simp [hsin, show (K : ℝ) ≠ 0 by positivity,
      show ((K + 1 : ℕ) : ℝ) ≠ 0 by positivity,
      hKm]
    ring_nf at hs ⊢
    nlinarith

lemma scaledFejerResidual_one (u : ℝ) : scaledFejerResidual 1 u = 1 := by
  rw [scaledFejerResidual, fejerResidual_eq_chebyshev_sq 1 (by omega)]
  norm_num

lemma scaledFejerResidual_two (x u : ℝ) (hcos : Real.cos u = 1 - 2 * x) :
    scaledFejerResidual 2 u = 4 * (1 - x) := by
  rw [scaledFejerResidual, fejerResidual_eq_chebyshev_sq 2 (by omega)]
  norm_num [Polynomial.Chebyshev.U_one]
  have hdouble := Real.cos_two_mul (u / 2)
  have hu : 2 * (u / 2) = u := by ring
  rw [hu, hcos] at hdouble
  field_simp
  nlinarith

/-- The explicit binomial residual and Fejér residual agree whenever their
arguments are related by `cos u = 1 - 2x`. -/
lemma scaledResidual_eq_scaledFejerResidual (K : ℕ) (hK : 0 < K)
    (x u : ℝ) (hcos : Real.cos u = 1 - 2 * x) :
    scaledResidual K x = scaledFejerResidual K u := by
  induction K using Nat.strong_induction_on with
  | h K ih =>
      by_cases h1 : K = 1
      · subst K
        rw [scaledResidual_one, scaledFejerResidual_one]
      by_cases h2 : K = 2
      · subst K
        rw [scaledResidual_two, scaledFejerResidual_two x u hcos]
      have hK3 : 3 ≤ K := by omega
      have hq := scaledResidual_order_recurrence (K - 1) (by omega) x
      have hf := scaledFejerResidual_order_recurrence (K - 1) (by omega) u
      have hi1 := ih (K - 1) (by omega) (by omega : 0 < K - 1)
      have hi2 := ih (K - 2) (by omega) (by omega : 0 < K - 2)
      rw [show K - 1 + 1 = K by omega, show K - 1 - 1 = K - 2 by omega] at hq hf
      rw [hi1, hi2] at hq
      rw [hcos] at hf
      linarith

/-- Angle realizing a light-range point as a squared sine. -/
@[no_expose]
noncomputable def residualAngle (x : ℝ) : ℝ :=
  2 * Real.arcsin √x

lemma cos_residualAngle (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.cos (residualAngle x) = 1 - 2 * x := by
  have hsqrt0 : 0 ≤ √x := Real.sqrt_nonneg x
  have hsqrt1 : √x ≤ 1 := by nlinarith [Real.sq_sqrt hx0]
  have hsin := Real.sin_arcsin (by linarith : -1 ≤ √x) hsqrt1
  have hsinsq := congrArg (fun z : ℝ => z ^ 2) hsin
  rw [residualAngle, Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq (Real.arcsin √x), Real.sq_sqrt hx0]

/-- Fejér representation of the generic explicit residual on `[0,1]`. -/
lemma one_sub_mul_GK_eq_fejerResidual (K : ℕ) (hK : 0 < K)
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    1 - x * GK K x = fejerResidual K (residualAngle x) := by
  have heq := scaledResidual_eq_scaledFejerResidual K hK x (residualAngle x)
    (cos_residualAngle x hx0 hx1)
  rw [scaledResidual_eq K hK, scaledFejerResidual] at heq
  exact (mul_left_cancel₀ (show (K : ℝ) ^ 2 ≠ 0 by positivity) heq)

/-- Equation (21), with the removable endpoint excluded so the ordinary real
quotient has its intended meaning. -/
-- keep: paper equation (21) closed form for the approximation residual
lemma one_sub_mul_GK_eq_sine_quotient_sq (K : ℕ) (hK : 0 < K)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    1 - x * GK K x =
      (Real.sin ((K : ℝ) * Real.arcsin √x) / ((K : ℝ) * √x)) ^ 2 := by
  rw [one_sub_mul_GK_eq_fejerResidual K hK x hx0.le hx1]
  have hsqrt0 : 0 ≤ √x := Real.sqrt_nonneg x
  have hsqrt1 : √x ≤ 1 := by nlinarith [Real.sq_sqrt hx0.le]
  have hsin : Real.sin (residualAngle x / 2) ≠ 0 := by
    rw [residualAngle, show 2 * Real.arcsin √x / 2 = Real.arcsin √x by ring,
      Real.sin_arcsin (by linarith : -1 ≤ √x) hsqrt1]
    positivity
  rw [fejerResidual_eq_sine_quotient_sq K hK _ hsin, residualAngle]
  ring_nf
  rw [Real.sin_arcsin (by linarith : -1 ≤ √x) hsqrt1]

/-- Equation (22): positivity and both generic upper bounds. -/
lemma one_sub_mul_GK_bounds (K : ℕ) (hK : 0 < K)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    0 ≤ 1 - x * GK K x ∧
      1 - x * GK K x ≤ 1 ∧
      1 - x * GK K x ≤ 1 / ((K : ℝ) ^ 2 * x) := by
  have hrep := one_sub_mul_GK_eq_fejerResidual K hK x hx0.le hx1
  have hsqrt0 : 0 ≤ √x := Real.sqrt_nonneg x
  have hsqrt1 : √x ≤ 1 := by nlinarith [Real.sq_sqrt hx0.le]
  have hsinval : Real.sin (residualAngle x / 2) = √x := by
    rw [residualAngle, show 2 * Real.arcsin √x / 2 = Real.arcsin √x by ring,
      Real.sin_arcsin (by linarith : -1 ≤ √x) hsqrt1]
  have hsin : Real.sin (residualAngle x / 2) ≠ 0 := by
    rw [hsinval]
    positivity
  refine ⟨hrep ▸ fejerResidual_nonneg K hK _, hrep ▸ fejerResidual_le_one_all K hK _, ?_⟩
  rw [hrep]
  have hi := fejerResidual_le_inv_sin_sq K hK (residualAngle x) hsin
  rw [hsinval, Real.sq_sqrt hx0.le] at hi
  exact hi

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
