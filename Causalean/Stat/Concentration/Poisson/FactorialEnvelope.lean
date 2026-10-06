module
public import Causalean.Stat.Concentration.Poisson.FactorialPolynomial

/-!
# Exponential envelopes for centered Poisson factorial lifts

This module turns the exact scalar mixed-moment formula for centered Poisson falling-factorial
lifts into the exponential square-moment envelope used by finite factorial-polynomial processes.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Causalean.Stat.Concentration.Poisson

/-- [A Poisson rate](hyp:rate), [normalization, center, radius, and scale](hyp:m,z,R,L), [positive normalization, radius, and scale](hyp:hm,hR,hL), [a centering condition](hyp:hcenter), [a normalized variance condition](hyp:hvariance), and [a factorial order](hyp:h) give [the exponential square-moment envelope for the normalized centered factorial lift](goal).

If the mean is within one radius of the centering point and the variance of the
normalized count is at most `R²/L`, the normalized square moment is at most `exp(h²/L)`.

For a Poisson count of rate `rate`, the variance of `N/m` is `rate/m²`. The factor `m²`
is necessary even when `m` is smaller than one.

Specialize `poisson_factorialLift_mixed` to `h=t`, divide by `R^(2*h)`, use the center and
variance premises termwise, then bound `choose h r ^ 2 * r!` by `h^(2*r)/r!` and compare the
finite exponential sum with `Real.exp`.
-/
theorem poisson_factorialLift_square_envelope (rate : NNReal)
    (m z R L : ℝ) (hm : 0 < m) (hR : 0 < R) (hL : 0 < L)
    (hcenter : |(rate : ℝ) / m - z| ≤ R)
    (hvariance : (rate : ℝ) / (m ^ 2 * R ^ 2) ≤ 1 / L)
    (h : ℕ) :
    (∫ N : ℕ, (factorialLift m z N h / R ^ h) ^ 2
      ∂poissonMeasure rate) ≤ Real.exp ((h : ℝ) ^ 2 / L) := by
  have hR0 : R ≠ 0 := ne_of_gt hR
  have hm0 : m ≠ 0 := ne_of_gt hm
  let c : ℝ := (rate : ℝ) / m - z
  let v : ℝ := (rate : ℝ) / m ^ 2
  let x : ℝ := (h : ℝ) ^ 2 / L
  have hc2 : c ^ 2 ≤ R ^ 2 := by
    simpa only [c, sq_abs] using
      (pow_le_pow_left₀ (abs_nonneg ((rate : ℝ) / m - z)) hcenter 2)
  have hc : c ^ 2 / R ^ 2 ≤ 1 :=
    (div_le_one (pow_pos hR 2)).mpr hc2
  have hc0 : 0 ≤ c ^ 2 / R ^ 2 := by positivity
  have hv0 : 0 ≤ v / R ^ 2 := by dsimp [v]; positivity
  have hv : v / R ^ 2 ≤ 1 / L := by
    have heq : v / R ^ 2 = (rate : ℝ) / (m ^ 2 * R ^ 2) := by
      dsimp [v]
      ring
    rw [heq]
    exact hvariance
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hfirst :
      (∫ N : ℕ, (factorialLift m z N h / R ^ h) ^ 2
        ∂poissonMeasure rate) =
      ∑ r ∈ Finset.range (h + 1),
        ((h.choose r : ℝ) ^ 2 * (Nat.factorial r : ℝ) *
          (v / R ^ 2) ^ r * (c ^ 2 / R ^ 2) ^ (h - r)) := by
    have hp (N : ℕ) : (factorialLift m z N h / R ^ h) ^ 2 =
        (R ^ h)⁻¹ ^ 2 * (factorialLift m z N h * factorialLift m z N h) := by
      rw [div_pow]
      field_simp
    simp_rw [hp]
    rw [integral_const_mul, poisson_factorialLift_mixed rate m z hm0 h h,
      Nat.min_self, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    have hrh : r ≤ h := by have := Finset.mem_range.mp hr; omega
    have hex : h + h - 2 * r = 2 * (h - r) := by omega
    change (R ^ h)⁻¹ ^ 2 *
      ((h.choose r : ℝ) * (h.choose r : ℝ) * (Nat.factorial r : ℝ) *
        v ^ r * c ^ (h + h - 2 * r)) =
      (h.choose r : ℝ) ^ 2 * (Nat.factorial r : ℝ) *
        (v / R ^ 2) ^ r * (c ^ 2 / R ^ 2) ^ (h - r)
    generalize v = w, c = y
    rw [hex, show y ^ (2 * (h - r)) = (y ^ 2) ^ (h - r) by rw [pow_mul]]
    rw [show R ^ h = R ^ r * R ^ (h - r) by
      rw [← pow_add, Nat.add_sub_of_le hrh]]
    rw [div_pow, div_pow]
    field_simp [hR0]
    ring
  rw [hfirst]
  calc
    (∑ r ∈ Finset.range (h + 1),
      (h.choose r : ℝ) ^ 2 * (Nat.factorial r : ℝ) *
        (v / R ^ 2) ^ r * (c ^ 2 / R ^ 2) ^ (h - r))
        ≤ ∑ r ∈ Finset.range (h + 1), x ^ r / (Nat.factorial r : ℝ) := by
          apply Finset.sum_le_sum
          intro r hr
          have hfac : 0 < (Nat.factorial r : ℝ) := by positivity
          have hchoose : (h.choose r : ℝ) ≤ (h : ℝ) ^ r / (Nat.factorial r : ℝ) :=
            Nat.choose_le_pow_div r h
          have hcoeff : (h.choose r : ℝ) ^ 2 * (Nat.factorial r : ℝ) ≤
              (h : ℝ) ^ (2 * r) / (Nat.factorial r : ℝ) := by
            have hs := pow_le_pow_left₀ (Nat.cast_nonneg _) hchoose 2
            calc
              (h.choose r : ℝ) ^ 2 * (Nat.factorial r : ℝ) ≤
                  ((h : ℝ) ^ r / (Nat.factorial r : ℝ)) ^ 2 *
                    (Nat.factorial r : ℝ) :=
                mul_le_mul_of_nonneg_right hs hfac.le
              _ = (h : ℝ) ^ (2 * r) / (Nat.factorial r : ℝ) := by
                rw [mul_comm 2 r, pow_mul, div_pow]
                field_simp
          have hc_pow := pow_le_pow_left₀ hc0 hc (h - r)
          have hv_pow := pow_le_pow_left₀ hv0 hv r
          have hnonneg : 0 ≤ (h.choose r : ℝ) ^ 2 * (Nat.factorial r : ℝ) := by positivity
          calc
            _ ≤ (h.choose r : ℝ) ^ 2 * (Nat.factorial r : ℝ) *
                (v / R ^ 2) ^ r := by
              have := mul_le_mul_of_nonneg_left hc_pow
                (mul_nonneg hnonneg (pow_nonneg hv0 r))
              simpa only [one_pow, mul_one] using this
            _ ≤ (h.choose r : ℝ) ^ 2 * (Nat.factorial r : ℝ) *
                (1 / L) ^ r := by
              exact mul_le_mul_of_nonneg_left hv_pow hnonneg
            _ ≤ ((h : ℝ) ^ (2 * r) / (Nat.factorial r : ℝ)) *
                (1 / L) ^ r :=
              mul_le_mul_of_nonneg_right hcoeff (pow_nonneg (by positivity) r)
            _ = x ^ r / (Nat.factorial r : ℝ) := by
              dsimp [x]
              rw [div_pow, one_pow, mul_comm 2 r, pow_mul]
              ring
    _ ≤ Real.exp x := Real.sum_le_exp_of_nonneg hx0 (h + 1)

end Causalean.Stat.Concentration.Poisson

