import Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.CertifiedNormalCDFEnclosure.Basic
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Exact power-series enclosures for the Gaussian integral

The unnormalised integral `∫₀ˣ exp (-t²/2) dt` has rational coefficients
`(-1)^k x^(2k+1) / (2^k k! (2k+1))`.  Once the coefficient magnitudes are
decreasing, two consecutive partial sums bracket the integral.  This is the
central-range engine; it uses a finite sum whose degree grows with requested
precision and never constructs a mesh of reciprocal-width size.

The formulas follow the classical error-function series recorded in NIST DLMF
§7.6(i), after substituting `z = x / sqrt 2`.
-/

open scoped BigOperators

namespace Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.CertifiedNormalCDFEnclosure

open Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic

/-- The magnitude of the `k`th integrated Gaussian-series term at `x`, namely `x` to the power
`2k+1` divided by `2^k k! (2k+1)`. It is nonnegative for nonnegative `x`, which is how it is used; for
negative `x` the same formula is negative. -/
noncomputable def gaussianIntegralMagnitude (x : ℝ) (k : ℕ) : ℝ :=
  x ^ (2 * k + 1) /
    ((2 : ℝ) ^ k * (k.factorial : ℝ) * (2 * k + 1 : ℕ))

/-- The `k`th function in the power series for `exp (-t²/2)`. -/
noncomputable def gaussianIntegrandTerm (k : ℕ) (t : ℝ) : ℝ :=
  (-1 : ℝ) ^ k * t ^ (2 * k) /
    ((2 : ℝ) ^ k * (k.factorial : ℝ))

/-- At every real argument, the Gaussian integrand is the sum of its classical
everywhere-convergent power series. -/
theorem gaussianIntegrand_hasSum (t : ℝ) :
    HasSum (fun k => gaussianIntegrandTerm k t)
      (Real.exp (-(t ^ 2) / 2)) := by
  rw [Real.exp_eq_exp_ℝ]
  have hfun : (fun k => gaussianIntegrandTerm k t) =
      (fun k => ((k.factorial : ℝ)⁻¹ • (-(t ^ 2) / 2) ^ k)) := by
    funext k
    simp [gaussianIntegrandTerm, div_pow]
    ring
  rw [hfun]
  exact NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (x := (-(t ^ 2) / 2 : ℝ))

/-- Integrating one Gaussian power-series term from zero to a nonnegative
endpoint gives the corresponding signed integrated-series coefficient. -/
theorem gaussianIntegrandTerm_integral (x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
    (∫ t in (0 : ℝ)..x, gaussianIntegrandTerm k t) =
      (-1 : ℝ) ^ k * gaussianIntegralMagnitude x k := by
  unfold gaussianIntegrandTerm gaussianIntegralMagnitude
  simp_rw [div_eq_mul_inv]
  rw [show (fun t : ℝ => (-1) ^ k * t ^ (2 * k) *
      (2 ^ k * (k.factorial : ℝ))⁻¹) =
      (fun t : ℝ => ((-1) ^ k * (2 ^ k * (k.factorial : ℝ))⁻¹) *
        t ^ (2 * k)) by
    funext t
    ring]
  rw [intervalIntegral.integral_const_mul, integral_pow]
  simp
  ring

/-- On `[0,x]`, the norm of one Gaussian-series function is bounded by the
same unsigned monomial evaluated at the nonnegative right endpoint. -/
theorem gaussianIntegrandTerm_norm_le (x : ℝ) (hx : 0 ≤ x) (k : ℕ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) x) :
    ‖gaussianIntegrandTerm k t‖ ≤
      x ^ (2 * k) / ((2 : ℝ) ^ k * (k.factorial : ℝ)) := by
  -- Expand the norm and use `0 ≤ t ≤ x` to compare the even powers.
  have habs : |t| ≤ x := by simpa [abs_of_nonneg ht.1] using ht.2
  have hp : |t| ^ (2 * k) ≤ x ^ (2 * k) :=
    pow_le_pow_left₀ (abs_nonneg t) habs _
  have hden : 0 ≤ (2 : ℝ) ^ k * (k.factorial : ℝ) := by positivity
  rw [gaussianIntegrandTerm, Real.norm_eq_abs, abs_div, abs_mul, abs_pow,
    abs_pow, abs_of_nonneg hden, abs_neg, abs_one, one_pow, one_mul]
  exact div_le_div_of_nonneg_right hp hden

/-- The endpoint majorants for the Gaussian integrand's power series are
summable for every fixed nonnegative endpoint. -/
theorem gaussianIntegrandMajorant_summable (x : ℝ) (hx : 0 ≤ x) :
    Summable (fun k =>
      x ^ (2 * k) / ((2 : ℝ) ^ k * (k.factorial : ℝ))) := by
  -- Identify this nonnegative series with the absolute exponential series at
  -- `x²/2`, using `Real.summable_pow_div_factorial`.
  refine (Real.summable_pow_div_factorial (x ^ 2 / 2)).congr ?_
  intro k
  rw [div_pow, ← pow_mul]
  ring

/-- The exact rational `k`th signed term in the integrated Gaussian power
series at the rational endpoint `x`. -/
def gaussianIntegralTerm (x : ℚ) (k : ℕ) : ℚ :=
  (-1 : ℚ) ^ k * x ^ (2 * k + 1) /
    ((2 : ℚ) ^ k * (k.factorial : ℚ) * (2 * k + 1 : ℕ))

/-- The exact rational Gaussian-integral partial sum through degree index `n`. -/
def gaussianIntegralPartial (x : ℚ) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), gaussianIntegralTerm x k

/-- The first omitted coefficient magnitude after partial sum index `n`. -/
def gaussianIntegralRemainder (x : ℚ) (n : ℕ) : ℚ :=
  |x| ^ (2 * (n + 1) + 1) /
    ((2 : ℚ) ^ (n + 1) * ((n + 1).factorial : ℚ) *
      (2 * (n + 1) + 1 : ℕ))

/-- The alternating enclosure is the rational interval whose endpoints are two
consecutive Gaussian-integral partial sums. -/
def gaussianIntegralInterval (x : ℚ) (n : ℕ) : RatInterval :=
  ⟨min (gaussianIntegralPartial x n) (gaussianIntegralPartial x (n + 1)),
    max (gaussianIntegralPartial x n) (gaussianIntegralPartial x (n + 1)),
    min_le_max⟩

/-- For a nonnegative endpoint, all unsigned Gaussian-series coefficients are
nonnegative. -/
theorem gaussianIntegralMagnitude_nonneg (x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
    0 ≤ gaussianIntegralMagnitude x k := by
  -- Unfold; every factor in the numerator and denominator is nonnegative and
  -- the natural-number factors in the denominator are strictly positive.
  unfold gaussianIntegralMagnitude
  positivity

/-- If `x² ≤ 2(n+2)`, the coefficient magnitudes decrease at every index after
the partial sum boundary `n`. -/
theorem gaussianIntegralMagnitude_antitone_from (x : ℝ) (hx : 0 ≤ x) (n : ℕ)
    (hmono : x ^ 2 ≤ 2 * (n + 2 : ℕ)) :
    ∀ k, n + 1 ≤ k →
      gaussianIntegralMagnitude x (k + 1) ≤ gaussianIntegralMagnitude x k := by
  intro k hk
  have hk' : n + 2 ≤ k + 1 := by omega
  have hbound : x ^ 2 ≤ 2 * ((k + 1 : ℕ) : ℝ) := by
    apply hmono.trans
    exact_mod_cast Nat.mul_le_mul_left 2 hk'
  have h₁ : x ^ 2 / (2 * (k + 1 : ℕ)) ≤ (1 : ℝ) :=
    (div_le_one (by positivity)).2 hbound
  have h₁nonneg : 0 ≤ x ^ 2 / (2 * (k + 1 : ℕ) : ℝ) := by positivity
  have h₂ : ((2 * k + 1 : ℕ) : ℝ) / (2 * k + 3 : ℕ) ≤ (1 : ℝ) := by
    apply (div_le_one (by positivity)).2
    norm_num
  have h₂nonneg : 0 ≤ ((2 * k + 1 : ℕ) : ℝ) / (2 * k + 3 : ℕ) := by positivity
  have hid :
      gaussianIntegralMagnitude x (k + 1) =
        gaussianIntegralMagnitude x k *
          (x ^ 2 / (2 * (k + 1 : ℕ))) *
          (((2 * k + 1 : ℕ) : ℝ) / (2 * k + 3 : ℕ)) := by
    unfold gaussianIntegralMagnitude
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    ring
  rw [hid]
  have hm := gaussianIntegralMagnitude_nonneg x hx k
  calc
    gaussianIntegralMagnitude x k * (x ^ 2 / (2 * ↑(k + 1))) *
        (↑(2 * k + 1) / ↑(2 * k + 3)) ≤
      gaussianIntegralMagnitude x k * 1 * (↑(2 * k + 1) / ↑(2 * k + 3)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h₁ hm) h₂nonneg
    _ ≤ gaussianIntegralMagnitude x k * 1 :=
        by simpa only [mul_one] using
          mul_le_mul_of_nonneg_left h₂ (mul_nonneg hm zero_le_one)
    _ = gaussianIntegralMagnitude x k := by ring

/-- The signed integrated Gaussian coefficients sum to the exact Gaussian
integral on every finite nonnegative interval. -/
theorem gaussianIntegral_hasSum (x : ℝ) (hx : 0 ≤ x) :
    HasSum (fun k => (-1 : ℝ) ^ k * gaussianIntegralMagnitude x k)
      (∫ t in (0 : ℝ)..x, Real.exp (-(t ^ 2) / 2)) := by
  -- Rewrite `exp (-(t^2)/2)` by `Real.hasSum_exp`, justify termwise
  -- integration on `[0,x]` using summable sup norms, then integrate monomials.
  -- `intervalIntegral.hasSum_intervalIntegral_of_summable_norm` is available.
  let f : ℕ → C(ℝ, ℝ) := fun k =>
    ⟨gaussianIntegrandTerm k, by
      unfold gaussianIntegrandTerm
      fun_prop⟩
  have hnorm : Summable (fun k =>
      ‖(f k).restrict
        (⟨Set.uIcc (0 : ℝ) x, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun k => ?_) (gaussianIntegrandMajorant_summable x hx)
    apply (ContinuousMap.norm_le _ (by positivity)).2
    intro t
    change ‖gaussianIntegrandTerm k t‖ ≤ _
    simpa only [ContinuousMap.restrict_apply] using
      gaussianIntegrandTerm_norm_le x hx k
        (by simpa [Set.uIcc_of_le hx] using t.property)
  have hi := intervalIntegral.hasSum_intervalIntegral_of_summable_norm hnorm
  have hterms : (fun k => ∫ t in (0 : ℝ)..x, f k t) =
      (fun k => (-1 : ℝ) ^ k * gaussianIntegralMagnitude x k) := by
    funext k
    change (∫ t in (0 : ℝ)..x, gaussianIntegrandTerm k t) = _
    exact gaussianIntegrandTerm_integral x hx k
  rw [hterms] at hi
  rw [show (∫ t in (0 : ℝ)..x, Real.exp (-(t ^ 2) / 2)) =
      ∫ t in (0 : ℝ)..x, ∑' k, f k t by
    apply intervalIntegral.integral_congr
    intro t _
    change Real.exp (-(t ^ 2) / 2) = ∑' k, gaussianIntegrandTerm k t
    exact (gaussianIntegrand_hasSum t).tsum_eq.symm]
  exact hi

/-- At [a rational endpoint](hyp:x) that is [nonnegative](hyp:hx), with [a partial-sum index](hyp:n) satisfying [the exact decreasing-tail condition](hyp:hmono), [two consecutive rational Gaussian-series sums enclose the unnormalised Gaussian integral](goal). -/
theorem gaussianIntegralInterval_sound (x : ℚ) (hx : 0 ≤ x) (n : ℕ)
    (hmono : x ^ 2 ≤ 2 * (n + 2 : ℕ)) :
    (gaussianIntegralInterval x n).Contains
      (∫ t in (0 : ℝ)..(x : ℝ), Real.exp (-(t ^ 2) / 2)) := by
  have hxR : (0 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hmonoR : (x : ℝ) ^ 2 ≤ 2 * ((n + 2 : ℕ) : ℝ) := by
    exact_mod_cast hmono
  let a : ℕ → ℝ := fun k => gaussianIntegralMagnitude (x : ℝ) k
  let s : ℕ → ℝ := fun k => (-1 : ℝ) ^ k * a k
  have hs : HasSum s (∫ t in (0 : ℝ)..(x : ℝ), Real.exp (-(t ^ 2) / 2)) := by
    exact gaussianIntegral_hasSum (x : ℝ) hxR
  have ha : Summable a := by
    have habs : Summable (fun k => ‖s k‖) := hs.summable.norm
    apply habs.congr
    intro k
    simp only [s, Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one,
      one_pow, one_mul, abs_of_nonneg (gaussianIntegralMagnitude_nonneg (x : ℝ) hxR k), a]
  have hanti := gaussianIntegralMagnitude_antitone_from (x : ℝ) hxR n hmonoR
  have hb : Summable (fun j => a (j + (n + 1))) :=
    (summable_nat_add_iff (n + 1)).2 ha
  have hbanti : Antitone (fun j => a (j + (n + 1))) := by
    refine antitone_nat_of_succ_le ?_
    intro j
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      hanti (j + (n + 1)) (by omega)
  let r : ℝ := ∑' j, (-1 : ℝ) ^ j * a (j + (n + 1))
  have hr_tendsto := hb.tendsto_alternating_series_tsum
  have hr0 : 0 ≤ r := by
    have h := hbanti.alternating_series_le_tendsto hr_tendsto 0
    exact h
  have hrle : r ≤ a (n + 1) := by
    have h := hbanti.tendsto_le_alternating_series hr_tendsto 0
    simpa [r] using h
  have htail : (∑' j, s (j + (n + 1))) = (-1 : ℝ) ^ (n + 1) * r := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro j
    simp only [s, pow_add]
    ring
  have hsplit := hs.summable.sum_add_tsum_nat_add (n + 1)
  rw [hs.tsum_eq, htail] at hsplit
  have hrepresentation :
      (∫ t in (0 : ℝ)..(x : ℝ), Real.exp (-(t ^ 2) / 2)) =
        (∑ k ∈ Finset.range (n + 1), s k) + (-1 : ℝ) ^ (n + 1) * r :=
    hsplit.symm
  have hterm_cast (k : ℕ) :
      ((gaussianIntegralTerm x k : ℚ) : ℝ) = s k := by
    simp only [gaussianIntegralTerm, gaussianIntegralMagnitude, s, a]
    push_cast
    ring
  have hpartial_cast (m : ℕ) :
      ((gaussianIntegralPartial x m : ℚ) : ℝ) =
        ∑ k ∈ Finset.range (m + 1), s k := by
    simp only [gaussianIntegralPartial, Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro k hk
    exact hterm_cast k
  have hnext_cast : ((gaussianIntegralPartial x (n + 1) : ℚ) : ℝ) =
      (∑ k ∈ Finset.range (n + 1), s k) + (-1 : ℝ) ^ (n + 1) * a (n + 1) := by
    rw [hpartial_cast]
    simpa only [Nat.add_assoc] using
      (Finset.sum_range_succ s (n + 1))
  rw [gaussianIntegralInterval, RatInterval.Contains, Rat.cast_min, Rat.cast_max,
    hpartial_cast, hnext_cast]
  obtain heven | hodd := Nat.even_or_odd (n + 1)
  · have hsign : (-1 : ℝ) ^ (n + 1) = 1 := by
      simpa using heven.neg_one_pow
    rw [hsign, one_mul] at hrepresentation ⊢
    constructor
    · apply min_le_iff.mpr
      left
      linarith
    · apply le_max_iff.mpr
      right
      linarith
  · have hsign : (-1 : ℝ) ^ (n + 1) = -1 := by
      simpa using hodd.neg_one_pow
    rw [hsign, neg_one_mul] at hrepresentation ⊢
    constructor
    · apply min_le_iff.mpr
      right
      linarith
    · apply le_max_iff.mpr
      left
      linarith

/-- On the full central range `0 ≤ x ≤ 8`, once index 64 is reached each next
remainder is at most half the preceding remainder. -/
theorem gaussianIntegralRemainder_geometric_step (x : ℚ) (hx0 : 0 ≤ x)
    (hx8 : x ≤ centralCutoff) (n : ℕ) (hn : 64 ≤ n) :
    gaussianIntegralRemainder x (n + 1) ≤
      gaussianIntegralRemainder x n / 2 := by
  -- Divide consecutive explicit remainders.  With `x ≤ 8` and `n ≥ 64`, the
  -- ratio is bounded by `32/(n+2) ≤ 1/2`; all denominators are positive.
  have hx8' : x ≤ 8 := by simpa [centralCutoff] using hx8
  have hx2 : x ^ 2 ≤ 64 := by nlinarith
  have hn2 : (66 : ℚ) ≤ (n + 2 : ℕ) := by
    exact_mod_cast (show 66 ≤ n + 2 by omega)
  have hratio : x ^ 2 / (2 * (n + 2 : ℕ) : ℚ) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity)).2
    nlinarith
  have hfactor : ((2 * n + 3 : ℕ) : ℚ) / (2 * n + 5 : ℕ) ≤ 1 := by
    apply (div_le_one (by positivity)).2
    norm_num
  have hfactor0 : 0 ≤ ((2 * n + 3 : ℕ) : ℚ) / (2 * n + 5 : ℕ) := by
    positivity
  have hid :
      gaussianIntegralRemainder x (n + 1) =
        gaussianIntegralRemainder x n *
          (x ^ 2 / (2 * (n + 2 : ℕ))) *
          (((2 * n + 3 : ℕ) : ℚ) / (2 * n + 5 : ℕ)) := by
    unfold gaussianIntegralRemainder
    rw [abs_of_nonneg hx0, Nat.factorial_succ]
    push_cast
    field_simp
    ring
  rw [hid]
  have hr0 : 0 ≤ gaussianIntegralRemainder x n := by
    unfold gaussianIntegralRemainder
    positivity
  calc
    gaussianIntegralRemainder x n * (x ^ 2 / (2 * ↑(n + 2))) *
        (↑(2 * n + 3) / ↑(2 * n + 5)) ≤
      gaussianIntegralRemainder x n * (1 / 2) *
        (↑(2 * n + 3) / ↑(2 * n + 5)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hratio hr0) hfactor0
    _ ≤ gaussianIntegralRemainder x n * (1 / 2) * 1 :=
          mul_le_mul_of_nonneg_left hfactor (mul_nonneg hr0 (by norm_num))
    _ = gaussianIntegralRemainder x n / 2 := by ring

/-- Consequently, adding `j` terms beyond index 64 reduces the central-series
remainder by at least the rational factor `2^j`; this records logarithmic
precision scaling for the checker. -/
theorem gaussianIntegralRemainder_geometric (x : ℚ) (hx0 : 0 ≤ x)
    (hx8 : x ≤ centralCutoff) (j : ℕ) :
    gaussianIntegralRemainder x (64 + j) ≤
      gaussianIntegralRemainder x 64 / (2 : ℚ) ^ j := by
  -- Induct on `j`, invoke the one-step bound at `64+j`, and clear the positive
  -- power-of-two denominator.
  induction j with
  | zero => simp
  | succ j ih =>
      have hstep := gaussianIntegralRemainder_geometric_step x hx0 hx8
        (64 + j) (by omega)
      rw [show 64 + (j + 1) = (64 + j) + 1 by omega]
      calc
        gaussianIntegralRemainder x ((64 + j) + 1) ≤
            gaussianIntegralRemainder x (64 + j) / 2 := hstep
        _ ≤ (gaussianIntegralRemainder x 64 / (2 : ℚ) ^ j) / 2 :=
            div_le_div_of_nonneg_right ih (by norm_num)
        _ = gaussianIntegralRemainder x 64 / (2 : ℚ) ^ (j + 1) := by
            rw [pow_succ]
            ring

end Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.CertifiedNormalCDFEnclosure
