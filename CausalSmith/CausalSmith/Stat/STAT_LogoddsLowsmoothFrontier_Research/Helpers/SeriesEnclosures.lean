module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.EngineRoutines
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # Factorial tails for the prescribed scalar series

The last half of the factorial dominates the public range bound. The resulting
geometric remainder certifies both literal polynomials. Monotonicity extends the
exponential enclosure, and cosine Lipschitz continuity extends its midpoint bracket.
-/
public section
noncomputable section
open Causalean.Mathlib.Analysis.IntervalArithmetic
open scoped BigOperators
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [The last half of the factorial supplies the roadmap's power lower bound. [the stated conclusion](goal) holds. -/
-- @node: series_half_factorial_bound
lemma series_half_factorial_bound (m : ℕ) : m ^ m ≤ Nat.factorial (2 * m) := by
  have h := Nat.factorial_mul_pow_sub_le_factorial (n := m) (m := 2 * m) (by omega)
  have hp : 1 ≤ Nat.factorial m := Nat.factorial_pos m
  rw [show 2 * m - m = m by omega] at h
  nlinarith

/-- The rational range bound dominates the absolute scalar argument. [the stated conclusion](goal) holds. -/
-- @node: seriesBound_abs_le
lemma seriesBound_abs_le (z : ℚ) : |(z : ℝ)| ≤ (seriesBound z : ℝ) := by
  have hceil := Int.le_ceil |z|
  have hn : (0 : ℤ) ≤ ⌈|z|⌉ := Int.ceil_nonneg (abs_nonneg z)
  have hc : (⌈|z|⌉ : ℤ) ≤ (seriesBound z : ℕ) := by
    unfold seriesBound
    rw [← Int.toNat_of_nonneg hn]
    exact_mod_cast le_max_right 1 (⌈|z|⌉ : ℤ).toNat
  have hz : |z| ≤ (seriesBound z : ℚ) := hceil.trans (by exact_mod_cast hc)
  exact_mod_cast hz

/-- A factorial term at the prescribed quadratic cutoff is at most a dyadic power. Under the stated assumptions. [The stated hypotheses](hyp:hB,hm,hm0) hold, and [the stated conclusion follows](goal). -/
-- @node: series_first_omitted_bound
lemma series_first_omitted_bound (x : ℝ) (B m : ℕ) (hB : |x| ≤ B)
    (hm : 2 * B ^ 2 ≤ m) (hm0 : 0 < m) :
    |x| ^ (2 * m) / (Nat.factorial (2 * m) : ℝ) ≤ (1 / 2 : ℝ) ^ m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hf : (m : ℝ) ^ m ≤ (Nat.factorial (2 * m) : ℝ) := by
    exact_mod_cast series_half_factorial_bound m
  calc
    |x| ^ (2 * m) / (Nat.factorial (2 * m) : ℝ) ≤
        (B : ℝ) ^ (2 * m) / (m : ℝ) ^ m := by gcongr
    _ = ((B : ℝ) ^ 2 / m) ^ m := by rw [div_pow, ← pow_mul]
    _ ≤ (1 / 2 : ℝ) ^ m := by
      apply pow_le_pow_left₀ (by positivity)
      apply (div_le_iff₀ hmR).mpr
      have hh : 2 * (B : ℝ) ^ 2 ≤ m := by exact_mod_cast hm
      linarith

/-- [The public cutoff makes twice the first omitted term smaller than the scalar error. [the stated conclusion](goal) holds. -/
-- @node: series_tail_budget
lemma series_tail_budget (q : ℕ) (z : ℚ) :
    |(z : ℝ)| ^ (2 * seriesCount q z) /
      (Nat.factorial (2 * seriesCount q z) : ℝ) * 2 ≤ (rationalError (q + 3) : ℝ) := by
  have hm : q + 6 ≤ seriesCount q z := le_max_right _ _
  have hfirst := series_first_omitted_bound (z : ℝ) (seriesBound z) (seriesCount q z)
    (seriesBound_abs_le z) (le_max_left _ _) (by omega)
  calc
    _ ≤ (1 / 2 : ℝ) ^ seriesCount q z * 2 := mul_le_mul_of_nonneg_right hfirst (by norm_num)
    _ ≤ (1 / 2 : ℝ) ^ (q + 4) * 2 := by
      apply mul_le_mul_of_nonneg_right _ (by norm_num)
      exact pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) (by omega)
    _ = (rationalError (q + 3) : ℝ) := by
      push_cast [rationalError]
      rw [div_pow, one_pow, show q + 4 = (q + 3) + 1 by omega, pow_succ]
      field_simp

/-- The geometric tail estimate for the real exponential series, including negative inputs. Under the stated assumptions. Under the stated assumptions. [The stated hypotheses](hyp:h) hold, and [the stated conclusion follows](goal). -/
-- @node: series_exp_remainder
lemma series_exp_remainder (x : ℝ) (n : ℕ) (h : |x| / (n + 1) ≤ 1 / 2) :
    |Real.exp x - ∑ j ∈ Finset.range n, x ^ j / (Nat.factorial j : ℝ)| ≤
      |x| ^ n / (Nat.factorial n : ℝ) * 2 := by
  have hc := Complex.exp_bound' (x := (x : ℂ)) (n := n) (by simpa using h)
  simpa only [← Complex.ofReal_pow, ← Complex.ofReal_natCast, ← Complex.ofReal_div,
    ← Complex.ofReal_sum, ← Complex.ofReal_exp, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] using hc

/-- [Successive tail terms have ratio at most one half at the public cutoff. [the stated conclusion](goal) holds. -/
-- @node: series_argument_ratio
lemma series_argument_ratio (q : ℕ) (z : ℚ) :
    |(z : ℝ)| / (2 * seriesCount q z + 1) ≤ 1 / 2 := by
  have hB : 1 ≤ seriesBound z := le_max_left _ _
  have hm : 2 * seriesBound z ^ 2 ≤ seriesCount q z := le_max_left _ _
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * seriesCount q z + 1)).mpr
  have hBR : (1 : ℝ) ≤ seriesBound z := by exact_mod_cast hB
  have hmR : 2 * (seriesBound z : ℝ) ^ 2 ≤ seriesCount q z := by exact_mod_cast hm
  nlinarith [seriesBound_abs_le z]

/-- The specified exponential polynomial approximates its scalar value at the internal precision. [the stated conclusion](goal) holds. -/
-- @node: expPolynomial_error
lemma expPolynomial_error (q : ℕ) (z : ℚ) :
    |Real.exp (z : ℝ) - (expPolynomial q z : ℝ)| ≤ (rationalError (q + 3) : ℝ) := by
  have hrat := series_argument_ratio q z
  have h := (series_exp_remainder (z : ℝ) (2 * seriesCount q z)
    (by simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hrat)).trans
      (series_tail_budget q z)
  simpa only [expPolynomial, Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast] using h

/-- The positive floor in the scalar exponential bracket lies below its true value. [the stated conclusion](goal) holds. -/
-- @node: paperExpScalar_floor_le
lemma paperExpScalar_floor_le (z : ℚ) :
    (1 / (3 : ℚ) ^ seriesBound z : ℝ) ≤ Real.exp (z : ℝ) := by
  have hz : -(seriesBound z : ℝ) ≤ (z : ℝ) := by
    have h := (abs_le.mp (seriesBound_abs_le z)).1
    exact h
  calc
    _ = 1 / (3 : ℝ) ^ seriesBound z := by push_cast; rfl
    _ ≤ 1 / (Real.exp 1) ^ seriesBound z := by
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le (seriesBound z)
    _ = Real.exp (-(seriesBound z : ℝ)) := by
      rw [Real.exp_neg, ← Real.exp_nat_mul]
      simp
    _ ≤ Real.exp (z : ℝ) := Real.exp_le_exp.mpr hz

/-- The internal two-sided error is smaller than the primitive tolerance. [the stated conclusion](goal) holds. -/
-- @node: series_scalar_error_budget
lemma series_scalar_error_budget (q : ℕ) :
    2 * (rationalError (q + 3) : ℝ) ≤ precisionError q := by
  simp only [rationalError, precisionError, zpow_neg, zpow_natCast]
  push_cast
  rw [pow_add]
  norm_num
  have hp : (0 : ℝ) < 2 ^ q := by positivity
  have hi : (0 : ℝ) ≤ (2 ^ q)⁻¹ := by positivity
  linarith

/-- The scalar bracket contains the exponential, has positive floor, and bounded endpoint excess. [the stated conclusion](goal) holds. -/
-- @node: paperExpScalar_spec
lemma paperExpScalar_spec (q : ℕ) (z : ℚ) :
    (paperExpScalar q z).Contains (Real.exp z) ∧
    0 < (paperExpScalar q z).lo ∧
    Real.exp z - (paperExpScalar q z).lo ≤ precisionError q ∧
    (paperExpScalar q z).hi - Real.exp z ≤ precisionError q := by
  have he := abs_le.mp (expPolynomial_error q z)
  have hf := paperExpScalar_floor_le z
  have hord : max (1 / (3 : ℚ) ^ seriesBound z)
      (expPolynomial q z - rationalError (q + 3)) ≤
        expPolynomial q z + rationalError (q + 3) := by
    have hl : ((max (1 / (3 : ℚ) ^ seriesBound z)
      (expPolynomial q z - rationalError (q + 3))) : ℝ) ≤ Real.exp z := by
      push_cast
      exact max_le hf (by linarith)
    have hu : Real.exp z ≤ ((expPolynomial q z + rationalError (q + 3)) : ℝ) := by
      linarith
    exact_mod_cast hl.trans hu
  simp only [paperExpScalar, rationalBox, min_eq_left hord, max_eq_right hord,
    RatInterval.Contains]
  have hfloor : (0 : ℚ) < 1 / (3 : ℚ) ^ seriesBound z := by positivity
  have hbudget := series_scalar_error_budget q
  refine ⟨⟨?_, ?_⟩, hfloor.trans_le (le_max_left _ _), ?_, ?_⟩
  · push_cast
    exact max_le hf (by linarith)
  · push_cast
    linarith
  · have hmax : (expPolynomial q z : ℝ) - rationalError (q + 3) ≤
        ((max (1 / (3 : ℚ) ^ seriesBound z)
          (expPolynomial q z - rationalError (q + 3))) : ℝ) := by
      push_cast
      exact le_max_right _ _
    push_cast
    linarith
  · push_cast
    linarith

/-- Monotonicity extends scalar containment and excess to the two endpoint evaluations. Under the stated assumptions. Under the stated assumptions. [The stated hypotheses](hyp:hF,hS) hold, and [the stated conclusion follows](goal). -/
-- @node: endpointExtension_monotone_contract
lemma endpointExtension_monotone_contract (F : ℝ → ℝ) (hF : Monotone F)
    (S : ℕ → ℚ → RatInterval) (q : ℕ) (I : RatInterval)
    (hS : ∀ z, (S q z).Contains (F z) ∧
      F z - (S q z).lo ≤ precisionError q ∧ (S q z).hi - F z ≤ precisionError q) :
    MonotoneContract F q I (endpointExtension S q I) ∧
    (endpointExtension S q I).lo = (S q I.lo).lo := by
  obtain ⟨hl, hlE, _⟩ := hS I.lo
  obtain ⟨hu, _, huE⟩ := hS I.hi
  have horderR : ((S q I.lo).lo : ℝ) ≤ (S q I.hi).hi :=
    hl.1.trans ((hF (by exact_mod_cast I.lo_le_hi)).trans hu.2)
  have horder : (S q I.lo).lo ≤ (S q I.hi).hi := by exact_mod_cast horderR
  simp only [endpointExtension, rationalBox, min_eq_left horder, max_eq_right horder,
    MonotoneContract, RatInterval.Contains]
  refine ⟨⟨?_, sub_nonneg.mpr hl.1, hlE, sub_nonneg.mpr hu.2, huE⟩, True.intro⟩
  intro x hx
  exact ⟨hl.1.trans (hF hx.1), (hF hx.2).trans hu.2⟩

/-- The literal concrete exponential routine meets the primitive image and excess contract. [the stated conclusion](goal) holds. -/
-- @node: concreteEngine_exp_contract
lemma concreteEngine_exp_contract (q : ℕ) (I : RatInterval) :
    MonotoneContract Real.exp q I (concreteEngine.expBox q I) ∧
    0 < (concreteEngine.expBox q I).lo := by
  have h := endpointExtension_monotone_contract Real.exp Real.exp_monotone
    paperExpScalar q I (fun z =>
      ⟨(paperExpScalar_spec q z).1, (paperExpScalar_spec q z).2.2⟩)
  refine ⟨h.1, ?_⟩
  change 0 < (endpointExtension paperExpScalar q I).lo
  rw [h.2]
  exact (paperExpScalar_spec q I.lo).2.1

/-- The real part of the even-length imaginary exponential polynomial is the cosine polynomial. [the stated conclusion](goal) holds. -/
-- @node: cosine_exp_partial_re
lemma cosine_exp_partial_re (z : ℝ) (m : ℕ) :
    (∑ j ∈ Finset.range (2*m), ((z : ℂ)*Complex.I)^j / (Nat.factorial j : ℂ)).re =
      ∑ j ∈ Finset.range m, (-1 : ℝ)^j*z^(2*j)/(Nat.factorial (2*j) : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2*(m+1) = (2*m+1)+1 by omega, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ]
    simp only [Complex.add_re, ih]
    have he : ((z : ℂ)*Complex.I)^(2*m) = (z : ℂ)^(2*m)*(-1 : ℂ)^m := by
      rw [mul_pow, pow_mul Complex.I 2 m, Complex.I_sq]
    rw [pow_succ, he]
    simp only [← Complex.ofReal_one, ← Complex.ofReal_neg, ← Complex.ofReal_pow,
      Complex.div_natCast_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring

/-- The cosine remainder is the real part of an exponential remainder at an imaginary argument. [the stated conclusion](goal) holds. -/
-- @node: cosPolynomial_error
lemma cosPolynomial_error (q : ℕ) (z : ℚ) :
    |Real.cos (z : ℝ) - (cosPolynomial q z : ℝ)| ≤ (rationalError (q + 3) : ℝ) := by
  have hr := series_argument_ratio q z
  have hx : ‖((z : ℝ) : ℂ) * Complex.I‖ / (2 * seriesCount q z + 1 : ℕ) ≤ 1 / 2 := by
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
      mul_one, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hr
  have h := Complex.exp_bound' (x := ((z : ℝ) : ℂ) * Complex.I)
    (n := 2 * seriesCount q z) hx
  have hRe := (Complex.abs_re_le_norm
    (Complex.exp (((z : ℝ) : ℂ) * Complex.I) -
      ∑ j ∈ Finset.range (2 * seriesCount q z),
        (((z : ℝ) : ℂ) * Complex.I) ^ j / (Nat.factorial j : ℂ))).trans h
  simp only [Complex.sub_re, Complex.exp_ofReal_mul_I_re,
    cosine_exp_partial_re, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_I, mul_one] at hRe
  apply le_trans _ (series_tail_budget q z)
  simpa only [cosPolynomial, Rat.cast_sum, Rat.cast_div, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_one, Rat.cast_natCast] using hRe

/-- Clipping the scalar cosine bracket preserves containment and bounds both endpoint excesses. [the stated conclusion](goal) holds. -/
-- @node: paperCosScalar_spec
lemma paperCosScalar_spec (q : ℕ) (z : ℚ) :
    (paperCosScalar q z).Contains (Real.cos z) ∧
    Real.cos z - (paperCosScalar q z).lo ≤ precisionError q ∧
    (paperCosScalar q z).hi - Real.cos z ≤ precisionError q ∧
    -1 ≤ (paperCosScalar q z).lo ∧ (paperCosScalar q z).hi ≤ 1 := by
  have he := abs_le.mp (cosPolynomial_error q z)
  have hlo : ((max (-1) (cosPolynomial q z - rationalError (q + 3)) : ℚ) : ℝ) ≤
      Real.cos z := by
    push_cast
    exact max_le (Real.neg_one_le_cos _) (by linarith)
  have hhi : Real.cos z ≤
      ((min 1 (cosPolynomial q z + rationalError (q + 3)) : ℚ) : ℝ) := by
    push_cast
    exact le_min (Real.cos_le_one _) (by linarith)
  have hord : max (-1) (cosPolynomial q z - rationalError (q + 3)) ≤
      min 1 (cosPolynomial q z + rationalError (q + 3)) := by exact_mod_cast hlo.trans hhi
  simp only [paperCosScalar, rationalBox, min_eq_left hord, max_eq_right hord,
    RatInterval.Contains]
  have hbudget := series_scalar_error_budget q
  refine ⟨⟨hlo, hhi⟩, ?_, ?_, le_max_left _ _, min_le_left _ _⟩
  · have hl : (cosPolynomial q z : ℝ) - rationalError (q + 3) ≤
        ((max (-1) (cosPolynomial q z - rationalError (q + 3)) : ℚ) : ℝ) := by
      push_cast
      exact le_max_right _ _
    push_cast at *
    linarith
  · have hu : ((min 1 (cosPolynomial q z + rationalError (q + 3)) : ℚ) : ℝ) ≤
        (cosPolynomial q z : ℝ) + rationalError (q + 3) := by
      push_cast
      exact min_le_right _ _
    push_cast at *
    linarith

/-- The midpoint bracket, enlarged by the half width and clipped, satisfies the cosine primitive. [the stated conclusion](goal) holds. -/
-- @node: concreteEngine_cos_contract
lemma concreteEngine_cos_contract (q : ℕ) (I : RatInterval) :
    let m : ℝ := ((I.lo : ℝ) + I.hi) / 2
    let w : ℝ := ((I.hi : ℝ) - I.lo) / 2
    (∀ x, I.Contains x → (concreteEngine.cosBox q I).Contains (Real.cos x)) ∧
    ∃ a b : ℚ, (a : ℝ) ≤ Real.cos m ∧ Real.cos m ≤ b ∧
      Real.cos m - a ≤ precisionError q ∧ (b : ℝ) - Real.cos m ≤ precisionError q ∧
      -1 ≤ a ∧ b ≤ 1 ∧
      (concreteEngine.cosBox q I).lo = max (-1) (a - (I.hi - I.lo) / 2) ∧
      (concreteEngine.cosBox q I).hi = min 1 (b + (I.hi - I.lo) / 2) ∧
      ((concreteEngine.cosBox q I).width : ℝ) ≤ 2 * w + 2 * precisionError q := by
  dsimp only
  let z : ℚ := (I.lo + I.hi) / 2
  let J := paperCosScalar q z
  obtain ⟨hJ, hlE, huE, hl, hu⟩ := paperCosScalar_spec q z
  have hz : (z : ℝ) = ((I.lo : ℝ) + I.hi) / 2 := by dsimp [z]; push_cast; rfl
  have hw : (0 : ℚ) ≤ I.width / 2 := div_nonneg I.width_nonneg (by norm_num)
  have hwR : (0 : ℝ) ≤ ((I.hi : ℝ) - I.lo) / 2 := by
    exact div_nonneg (sub_nonneg.mpr (by exact_mod_cast I.lo_le_hi)) (by norm_num)
  have horder : max (-1) (J.lo - I.width / 2) ≤ min 1 (J.hi + I.width / 2) := by
    apply max_le
    · exact le_min (by norm_num) (by linarith [J.lo_le_hi])
    · exact le_min (by linarith [J.lo_le_hi]) (by linarith [J.lo_le_hi])
  have hlo : (concreteEngine.cosBox q I).lo = max (-1) (J.lo - I.width / 2) := by
    change min (max (-1) (J.lo - I.width / 2)) (min 1 (J.hi + I.width / 2)) = _
    exact min_eq_left horder
  have hhi : (concreteEngine.cosBox q I).hi = min 1 (J.hi + I.width / 2) := by
    change max (max (-1) (J.lo - I.width / 2)) (min 1 (J.hi + I.width / 2)) = _
    exact max_eq_right horder
  constructor
  · intro x hx
    have hdist : |x - (z : ℝ)| ≤ ((I.hi : ℝ) - I.lo) / 2 := by
      rw [hz, abs_le]
      constructor <;> linarith [hx.1, hx.2]
    have hc := abs_le.mp ((Real.abs_cos_sub_cos_le x z).trans hdist)
    simp only [RatInterval.Contains, hlo, hhi]
    push_cast [RatInterval.width]
    constructor
    · exact max_le (Real.neg_one_le_cos _) (by linarith [hJ.1])
    · exact le_min (Real.cos_le_one _) (by linarith [hJ.2])
  · refine ⟨J.lo, J.hi, ?_, ?_, ?_, ?_, hl, hu, ?_, ?_, ?_⟩
    · simpa only [← hz] using hJ.1
    · simpa only [← hz] using hJ.2
    · simpa only [← hz] using hlE
    · simpa only [← hz] using huE
    · simpa only [RatInterval.width] using hlo
    · simpa only [RatInterval.width] using hhi
    · have hLo : (J.lo : ℝ) - ((I.hi : ℝ) - I.lo) / 2 ≤
          ((concreteEngine.cosBox q I).lo : ℝ) := by
        rw [hlo]
        push_cast [RatInterval.width]
        exact le_max_right _ _
      have hHi : ((concreteEngine.cosBox q I).hi : ℝ) ≤
          (J.hi : ℝ) + ((I.hi : ℝ) - I.lo) / 2 := by
        rw [hhi]
        push_cast [RatInterval.width]
        exact min_le_right _ _
      simp only [RatInterval.width, Rat.cast_sub]
      linarith
end CausalSmith.Stat.LogoddsLowsmoothFrontier
