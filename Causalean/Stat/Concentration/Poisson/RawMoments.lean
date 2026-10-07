module
public import Causalean.Stat.Concentration.Poisson.FactorialPolynomial
public import Mathlib.Combinatorics.Enumerative.Stirling

/-! # Raw moments of Poisson counts

Exact formula and a simple bound for the raw moments of a Poisson variable N with rate λ ≥ 0.
Writing an ordinary power as a combination of falling factorials with Stirling numbers of the
second kind S(r, v), and using E[N(N−1)⋯(N−v+1)] = λ^v, gives E[N^r] = Σ over v ≤ r of S(r, v) λ^v
(the Touchard polynomial), and hence E[N^r] ≤ (λ + r)^r.

## Main results

* `count_power_factorial_expansion`, `count_power_factorial_expansion_real` —
  k^r = Σ over v ≤ r of S(r, v) · k(k−1)⋯(k−v+1).
* `stirlingSecond_le_choose_mul_pow` — S(r, v) ≤ C(r, v) · R^(r−v) for v ≤ r ≤ R.
* `poisson_power_integrable` — every power of a Poisson count is integrable.
* `poisson_power_moment_eq` — E[N^r] = Σ over v ≤ r of S(r, v) λ^v.
* `poisson_power_moment_le` — E[N^r] ≤ (λ + r)^r.
-/

public section

namespace Causalean.Stat.Concentration.Poisson

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- For a [count](hyp:k) and [factorial order](hyp:v), multiplying a descending
factorial by the count raises its order plus the stated lower-order correction, including when the factorial vanishes. The result is [the count-times-descending-factorial recurrence](goal). -/
lemma count_mul_descFactorial (k v : ℕ) :
    k * k.descFactorial v = k.descFactorial (v + 1) + v * k.descFactorial v := by
  by_cases h : v ≤ k
  · rw [Nat.descFactorial_succ]
    have hk : k = k - v + v := by omega
    calc
      k * k.descFactorial v = (k - v + v) * k.descFactorial v :=
        congrArg (fun t => t * k.descFactorial v) hk
      _ = _ := by ring
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega : k < v),
      Nat.descFactorial_eq_zero_iff_lt.mpr (by omega : k < v + 1)]
    simp

/-- For a [count](hyp:k) and [power](hyp:r), the ordinary power is the finite
Stirling-weighted sum of descending factorials. The result is [the Stirling expansion of an ordinary count power](goal). -/
lemma count_power_factorial_expansion (k r : ℕ) :
    k ^ r = ∑ v ∈ Finset.range (r + 1),
      Nat.stirlingSecond r v * k.descFactorial v := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ', ih, Finset.mul_sum]
    simp_rw [show ∀ v, k * (Nat.stirlingSecond r v * k.descFactorial v) =
        Nat.stirlingSecond r v * k.descFactorial (v + 1) +
          v * Nat.stirlingSecond r v * k.descFactorial v by
      intro v
      rw [mul_left_comm k, count_mul_descFactorial]
      ring]
    rw [Finset.sum_add_distrib]
    have hb : (∑ v ∈ Finset.range (r + 1),
        v * Nat.stirlingSecond r v * k.descFactorial v) =
        ∑ v ∈ Finset.range (r + 1),
          (v + 1) * Nat.stirlingSecond r (v + 1) * k.descFactorial (v + 1) := by
      rw [Finset.sum_range_succ' (f := fun v =>
        v * Nat.stirlingSecond r v * k.descFactorial v)]
      rw [Finset.sum_range_succ (f := fun v =>
        (v + 1) * Nat.stirlingSecond r (v + 1) * k.descFactorial (v + 1))]
      simp [Nat.stirlingSecond_eq_zero_of_lt (Nat.lt_succ_self r)]
    rw [hb, Finset.sum_range_succ' (f := fun v =>
      Nat.stirlingSecond (r + 1) v * k.descFactorial v)]
    simp only [Nat.stirlingSecond_succ_zero, zero_mul, add_zero,
      Nat.stirlingSecond_succ_succ, add_mul, Finset.sum_add_distrib]
    exact add_comm _ _

/-- For [orders](hyp:r,R,v) with [the smaller order bounded by the ambient
order](hyp:hr) and [the block count bounded by the smaller order](hyp:hv), the
second-kind Stirling number is bounded by the stated binomial-power expression. The result is [the stated binomial-power upper bound on the Stirling number](goal). -/
lemma stirlingSecond_le_choose_mul_pow {r R v : ℕ}
    (hr : r ≤ R) (hv : v ≤ r) :
    Nat.stirlingSecond r v ≤ r.choose v * R ^ (r - v) := by
  induction r generalizing v with
  | zero =>
    have hv0 : v = 0 := by omega
    subst v
    simp
  | succ r ih =>
    cases v with
    | zero => simp
    | succ v =>
      by_cases ht : v + 1 = r + 1
      · have ht' : v = r := by omega
        subst v
        simp [Nat.stirlingSecond_self]
      · have hv1 : v + 1 ≤ r := by omega
        have h1 := ih (by omega : r ≤ R) hv1
        have h0 := ih (by omega : r ≤ R) (by omega : v ≤ r)
        have hR : v + 1 ≤ R := by omega
        have hterm : (v + 1) * Nat.stirlingSecond r (v + 1) ≤
            r.choose (v + 1) * R ^ (r - v) := by
          calc
            _ ≤ R * (r.choose (v + 1) * R ^ (r - (v + 1))) :=
              Nat.mul_le_mul hR h1
            _ = _ := by
              rw [show r - v = (r - (v + 1)) + 1 by omega, pow_succ]
              ring
        rw [Nat.stirlingSecond_succ_succ, Nat.choose_succ_succ,
          show (r + 1) - (v + 1) = r - v by omega]
        nlinarith only [hterm, h0]

/-- For a [count](hyp:k) and [power](hyp:r), casting the count power to the
reals preserves its finite Stirling expansion in descending factorials. The result is [the real-valued Stirling expansion of a count power](goal). -/
lemma count_power_factorial_expansion_real (k r : ℕ) :
    (k : ℝ) ^ r = ∑ v ∈ Finset.range (r + 1),
      (Nat.stirlingSecond r v : ℝ) * (k.descFactorial v : ℝ) := by
  exact_mod_cast count_power_factorial_expansion k r

/-- For a [Poisson rate](hyp:rate) and [natural power](hyp:r), the corresponding
raw power of the count is integrable under the Poisson law. The result is [integrability of the raw Poisson count power](goal). -/
lemma poisson_power_integrable (rate : NNReal) (r : ℕ) :
    Integrable (fun k : ℕ => (k : ℝ) ^ r) (poissonMeasure rate) := by
  simp_rw [count_power_factorial_expansion_real]
  exact integrable_finsetSum _ (fun v _ =>
    (Causalean.Stat.Concentration.Poisson.poisson_descFactorial_integrable rate v).const_mul _)

/-- For a [Poisson rate](hyp:rate) and [natural power](hyp:r), the raw moment equals
the finite Stirling-weighted sum of powers of the rate. The result is [the Stirling-weighted formula for the raw Poisson moment](goal). -/
lemma poisson_power_moment_eq (rate : NNReal) (r : ℕ) :
    (∫ k : ℕ, (k : ℝ) ^ r ∂poissonMeasure rate) =
      ∑ v ∈ Finset.range (r + 1),
        (Nat.stirlingSecond r v : ℝ) * (rate : ℝ) ^ v := by
  simp_rw [count_power_factorial_expansion_real]
  rw [integral_finsetSum _ (fun v _ =>
    (Causalean.Stat.Concentration.Poisson.poisson_descFactorial_integrable rate v).const_mul _)]
  simp_rw [integral_const_mul,
    Causalean.Stat.Concentration.Poisson.poisson_descFactorial_moment]

/-- For a [Poisson rate](hyp:rate) and [natural power](hyp:r), the raw moment is
bounded by the sum of the rate and the order raised to that order. The result is [the rate-plus-order upper bound on the raw Poisson moment](goal). -/
lemma poisson_power_moment_le (rate : NNReal) (r : ℕ) :
    (∫ k : ℕ, (k : ℝ) ^ r ∂poissonMeasure rate) ≤
      ((rate : ℝ) + (r : ℝ)) ^ r := by
  rw [poisson_power_moment_eq, add_pow]
  apply Finset.sum_le_sum
  intro v hv
  have hvr : v ≤ r := by have := Finset.mem_range.mp hv; omega
  have hs : (Nat.stirlingSecond r v : ℝ) ≤
      (r.choose v : ℝ) * (r : ℝ) ^ (r - v) := by
    exact_mod_cast stirlingSecond_le_choose_mul_pow (le_refl r) hvr
  have hh := mul_le_mul_of_nonneg_right hs (pow_nonneg rate.coe_nonneg v)
  convert hh using 1
  ring

end Causalean.Stat.Concentration.Poisson
