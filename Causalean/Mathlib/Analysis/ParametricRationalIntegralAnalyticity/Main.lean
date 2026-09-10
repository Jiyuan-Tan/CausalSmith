import Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity.Affine
import Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity.PowerSeries

/-!
# Analyticity of polynomial-over-affine parameter integrals

This file specializes dominated power-series integration to finite-degree polynomial numerators
and affine denominators. The integration set need only have finite measure, so compact sets under
a locally finite measure are an important special case.
-/

open scoped ENNReal
open MeasureTheory Set

namespace Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity

/-- Given [a measure](hyp:μ), [a measurable integration set of finite measure](hyp:hK,hμK), [a polynomial degree, coefficient functions, and affine endpoint functions](hyp:N,c,a,b), [an expansion center, positive separation margin, nonnegative slope bound, and coefficient bounds](hyp:t₀,ε,L,C), [positivity and nonnegativity of those bounds](hyp:hε,hL), [measurability of the coefficients and endpoints](hyp:hc,ha,hb), [uniform coefficient and slope bounds on the integration set](hyp:hc_bound,hslope), and [uniform separation of the central denominator from zero](hyp:hden), [the polynomial-over-affine set integral is real analytic at the expansion center](goal). -/
theorem analyticAt_setIntegral_polynomial_div_affine
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {K : Set α} (hK : MeasurableSet K) (hμK : μ K ≠ ∞)
    (N : ℕ) (c : Fin (N + 1) → α → ℝ) (a b : α → ℝ)
    (t₀ ε L : ℝ) (C : Fin (N + 1) → ℝ)
    (hε : 0 < ε) (hL : 0 ≤ L)
    (hc : ∀ i, Measurable (c i)) (ha : Measurable a) (hb : Measurable b)
    (hc_bound : ∀ i, ∀ x ∈ K, |c i x| ≤ C i)
    (hslope : ∀ x ∈ K, |b x - a x| ≤ L)
    (hden : ∀ x ∈ K, ε ≤ |affineDenominator a b t₀ x|) :
    AnalyticAt ℝ
      (fun t ↦ ∫ x in K, polynomialNumerator N c t x / affineDenominator a b t x ∂μ) t₀ := by
  -- Proof route: work with `μ.restrict K`, whose finiteness follows from `hμK`.  For each
  -- numerator coefficient `i`, expand `c i x / affineDenominator a b t x` geometrically at
  -- `t₀` and apply `analyticAt_integral_of_powerSeries_domination`.  A radius proportional to
  -- `ε / (L + 1)` makes the coefficient majorant geometric.  Finally pull the scalar `t ^ i`
  -- through the integral and use the finite-sum/product analytic closure lemmas.
  letI : IsFiniteMeasure (μ.restrict K) := isFiniteMeasure_restrict.mpr hμK
  let r : ℝ := ε / (2 * (L + 1))
  let coeff : Fin (N + 1) → ℕ → α → ℝ := fun i n x ↦
    c i x *
      ((-(b x - a x) / affineDenominator a b t₀ x) ^ n /
        affineDenominator a b t₀ x)
  let M : Fin (N + 1) → ℕ → ℝ := fun i n ↦
    |C i| * (((L + 1) / ε) ^ n / ε)
  have hL1 : 0 < L + 1 := by linarith
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hd_meas : Measurable (fun x ↦ affineDenominator a b t₀ x) := by
    unfold affineDenominator
    fun_prop
  have hcoeff_meas (i : Fin (N + 1)) (n : ℕ) :
      AEStronglyMeasurable (coeff i n) (μ.restrict K) := by
    apply Measurable.aestronglyMeasurable
    dsimp [coeff]
    fun_prop
  have hM_nonneg (i : Fin (N + 1)) (n : ℕ) : 0 ≤ M i n := by
    dsimp [M]
    positivity
  have hcoeff_bound (i : Fin (N + 1)) (n : ℕ) :
      ∀ᵐ x ∂μ.restrict K, ‖coeff i n x‖ ≤ M i n := by
    filter_upwards [ae_restrict_mem hK] with x hx
    have hci : |c i x| ≤ |C i| := (hc_bound i x hx).trans (le_abs_self _)
    have hd : ε ≤ |affineDenominator a b t₀ x| := hden x hx
    have hdpos : 0 < |affineDenominator a b t₀ x| := hε.trans_le hd
    have hs : |b x - a x| ≤ L + 1 := (hslope x hx).trans (by linarith)
    dsimp [coeff, M]
    rw [abs_mul, abs_div, abs_pow, abs_div, abs_neg]
    gcongr
  have hM_summable (i : Fin (N + 1)) :
      Summable (fun n ↦ M i n * r ^ n) := by
    have hbase : ((L + 1) / ε) * r = (1 : ℝ) / 2 := by
      dsimp [r]
      field_simp
    have heq : (fun n ↦ M i n * r ^ n) =
        (fun n ↦ (|C i| / ε) * ((1 : ℝ) / 2) ^ n) := by
      funext n
      dsimp [M]
      rw [← hbase]
      rw [mul_pow]
      ring
    rw [heq]
    exact summable_geometric_two.mul_left (|C i| / ε)
  have hseries (i : Fin (N + 1)) :
      ∀ t, |t - t₀| < r → ∀ᵐ x ∂μ.restrict K,
        c i x / affineDenominator a b t x =
          ∑' n : ℕ, coeff i n x * (t - t₀) ^ n := by
    intro t ht
    filter_upwards [ae_restrict_mem hK] with x hx
    have hd : ε ≤ |affineDenominator a b t₀ x| := hden x hx
    have hdpos : 0 < |affineDenominator a b t₀ x| := hε.trans_le hd
    have hs : |b x - a x| ≤ L + 1 := (hslope x hx).trans (by linarith)
    have hsmall :
        |(t - t₀) * (b x - a x) / affineDenominator a b t₀ x| < 1 := by
      calc
        |(t - t₀) * (b x - a x) / affineDenominator a b t₀ x| =
            |t - t₀| * |b x - a x| / |affineDenominator a b t₀ x| := by
              rw [abs_div, abs_mul]
        _ ≤ |t - t₀| * (L + 1) / |affineDenominator a b t₀ x| := by gcongr
        _ < r * (L + 1) / |affineDenominator a b t₀ x| := by gcongr
        _ ≤ r * (L + 1) / ε := by gcongr
        _ = 1 / 2 := by
          dsimp [r]
          field_simp
        _ < 1 := by norm_num
    have hrec := affineDenominator_reciprocal_eq_tsum
      (a := a) (b := b) (t := t) (t₀ := t₀) (x := x) (abs_pos.mp hdpos) hsmall
    calc
      c i x / affineDenominator a b t x =
          c i x * (affineDenominator a b t x)⁻¹ := div_eq_mul_inv _ _
      _ = c i x * ∑' n : ℕ,
          ((-(b x - a x) / affineDenominator a b t₀ x) ^ n /
            affineDenominator a b t₀ x) * (t - t₀) ^ n := by rw [hrec]
      _ = ∑' n : ℕ, c i x *
          (((-(b x - a x) / affineDenominator a b t₀ x) ^ n /
            affineDenominator a b t₀ x) * (t - t₀) ^ n) := by
              rw [tsum_mul_left]
      _ = ∑' n : ℕ, coeff i n x * (t - t₀) ^ n := by
        apply tsum_congr
        intro n
        dsimp [coeff]
        ring
  have hAi (i : Fin (N + 1)) :
      AnalyticAt ℝ
        (fun t ↦ ∫ x, c i x / affineDenominator a b t x ∂μ.restrict K) t₀ :=
    analyticAt_integral_of_powerSeries_domination
      (μ.restrict K)
      (fun t x ↦ c i x / affineDenominator a b t x)
      (coeff i) (M i) t₀ r hr (hcoeff_meas i) (hM_nonneg i)
      (hcoeff_bound i) (hM_summable i) (hseries i)
  have hsum : AnalyticAt ℝ
      (fun t ↦ ∑ i : Fin (N + 1),
        t ^ (i : ℕ) * ∫ x, c i x / affineDenominator a b t x ∂μ.restrict K) t₀ := by
    apply ((Finset.univ : Finset (Fin (N + 1))).analyticAt_sum
        (f := fun (i : Fin (N + 1)) (t : ℝ) ↦
        t ^ (i : ℕ) * ∫ x, c i x / affineDenominator a b t x ∂μ.restrict K)
        (fun (i : Fin (N + 1)) _ ↦ (analyticAt_id.pow (i : ℕ)).mul (hAi i))).congr
    exact Filter.Eventually.of_forall (fun t ↦ by simp)
  apply hsum.congr
  rcases affineDenominator_uniformly_nonzero_near hε hL hden hslope with
    ⟨δ, hδ, hden_near⟩
  filter_upwards [Metric.ball_mem_nhds t₀ hδ] with t ht
  have hd_t_meas : Measurable (fun x ↦ affineDenominator a b t x) := by
    unfold affineDenominator
    fun_prop
  have hfi (i : Fin (N + 1)) :
      Integrable (fun x ↦ t ^ (i : ℕ) *
        (c i x / affineDenominator a b t x)) (μ.restrict K) := by
    apply Integrable.const_mul
    apply Integrable.of_bound ((hc i).div hd_t_meas).aestronglyMeasurable (|C i| / (ε / 2))
    filter_upwards [ae_restrict_mem hK] with x hx
    have hci : |c i x| ≤ |C i| := (hc_bound i x hx).trans (le_abs_self _)
    have hd : ε / 2 ≤ |affineDenominator a b t x| :=
      hden_near t (by simpa [Real.dist_eq] using ht) x hx
    have hdpos : 0 < |affineDenominator a b t x| := (half_pos hε).trans_le hd
    change |c i x / affineDenominator a b t x| ≤ |C i| / (ε / 2)
    rw [abs_div]
    gcongr
  simp only [polynomialNumerator]
  have hpoint :
      (fun x ↦ (∑ i : Fin (N + 1), c i x * t ^ (i : ℕ)) /
        affineDenominator a b t x) =
      (fun x ↦ ∑ i : Fin (N + 1), t ^ (i : ℕ) *
        (c i x / affineDenominator a b t x)) := by
    funext x
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hpoint]
  rw [integral_finsetSum Finset.univ (fun i _ ↦ hfi i)]
  simp only [integral_const_mul]

/-- Given [a measure](hyp:μ), [a measurable integration set of finite measure](hyp:hK,hμK), [a polynomial degree, coefficient functions, and affine endpoint functions](hyp:N,c,a,b), [an open parameter set, positive separation margin, nonnegative slope bound, and coefficient bounds](hyp:O,ε,L,C), [openness and valid numerical bounds](hyp:hO,hε,hL), [measurability of the coefficients and endpoints](hyp:hc,ha,hb), [uniform coefficient and slope bounds on the integration set](hyp:hc_bound,hslope), and [uniform denominator separation over the parameter and integration sets](hyp:hden), [the polynomial-over-affine set integral is real analytic throughout the open parameter set](goal). -/
theorem analyticOnNhd_setIntegral_polynomial_div_affine
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {K : Set α} (hK : MeasurableSet K) (hμK : μ K ≠ ∞)
    (N : ℕ) (c : Fin (N + 1) → α → ℝ) (a b : α → ℝ)
    (O : Set ℝ) (ε L : ℝ) (C : Fin (N + 1) → ℝ)
    (hO : IsOpen O) (hε : 0 < ε) (hL : 0 ≤ L)
    (hc : ∀ i, Measurable (c i)) (ha : Measurable a) (hb : Measurable b)
    (hc_bound : ∀ i, ∀ x ∈ K, |c i x| ≤ C i)
    (hslope : ∀ x ∈ K, |b x - a x| ≤ L)
    (hden : ∀ t ∈ O, ∀ x ∈ K, ε ≤ |affineDenominator a b t x|) :
    AnalyticOnNhd ℝ
      (fun t ↦ ∫ x in K, polynomialNumerator N c t x / affineDenominator a b t x ∂μ) O := by
  -- `AnalyticOnNhd` is pointwise; specialize the preceding local theorem at each `t ∈ O`.
  intro t ht
  exact analyticAt_setIntegral_polynomial_div_affine μ hK hμK N c a b t ε L C
    hε hL hc ha hb hc_bound hslope (hden t ht)

/-- Given [a measure](hyp:μ), [a measurable integration set of finite measure](hyp:hK,hμK), [a polynomial degree, coefficient functions, and affine endpoint functions](hyp:N,c,a,b), [an expansion center, positive separation margin, nonnegative relative-slope bound, and coefficient bounds](hyp:t₀,ε,Q,C), [positivity and nonnegativity of those bounds](hyp:hε,hQ), [measurability of the coefficients and endpoints](hyp:hc,ha,hb), [a uniform coefficient bound](hyp:hc_bound), [a uniform relative affine-slope bound](hyp:hratio), and [uniform central denominator separation](hyp:hden), [the polynomial-over-affine set integral is real analytic at the expansion center](goal). -/
theorem analyticAt_setIntegral_polynomial_div_affine_of_slope_div_bound
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {K : Set α} (hK : MeasurableSet K) (hμK : μ K ≠ ∞)
    (N : ℕ) (c : Fin (N + 1) → α → ℝ) (a b : α → ℝ)
    (t₀ ε Q : ℝ) (C : Fin (N + 1) → ℝ)
    (hε : 0 < ε) (hQ : 0 ≤ Q)
    (hc : ∀ i, Measurable (c i)) (ha : Measurable a) (hb : Measurable b)
    (hc_bound : ∀ i, ∀ x ∈ K, |c i x| ≤ C i)
    (hratio : ∀ x ∈ K,
      |(b x - a x) / affineDenominator a b t₀ x| ≤ Q)
    (hden : ∀ x ∈ K, ε ≤ |affineDenominator a b t₀ x|) :
    AnalyticAt ℝ
      (fun t ↦ ∫ x in K, polynomialNumerator N c t x / affineDenominator a b t x ∂μ) t₀ := by
  -- Proof route: repeat the dominated geometric-series argument from
  -- `analyticAt_setIntegral_polynomial_div_affine`, but majorize the reciprocal-series
  -- coefficient directly by `Q ^ n / ε`.  Taking radius `1 / (2 * (Q + 1))` makes the
  -- scalar majorant geometric.  The final finite-sum/integrability rewrite uses
  -- `affineDenominator_uniformly_nonzero_near_of_slope_div_bound`.
  letI : IsFiniteMeasure (μ.restrict K) := isFiniteMeasure_restrict.mpr hμK
  let r : ℝ := 1 / (2 * (Q + 1))
  let coeff : Fin (N + 1) → ℕ → α → ℝ := fun i n x ↦
    c i x *
      ((-(b x - a x) / affineDenominator a b t₀ x) ^ n /
        affineDenominator a b t₀ x)
  let M : Fin (N + 1) → ℕ → ℝ := fun i n ↦
    |C i| * (Q ^ n / ε)
  have hQ1 : 0 < Q + 1 := by linarith
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hd_meas : Measurable (fun x ↦ affineDenominator a b t₀ x) := by
    unfold affineDenominator
    fun_prop
  have hcoeff_meas (i : Fin (N + 1)) (n : ℕ) :
      AEStronglyMeasurable (coeff i n) (μ.restrict K) := by
    apply Measurable.aestronglyMeasurable
    dsimp [coeff]
    fun_prop
  have hM_nonneg (i : Fin (N + 1)) (n : ℕ) : 0 ≤ M i n := by
    dsimp [M]
    positivity
  have hcoeff_bound (i : Fin (N + 1)) (n : ℕ) :
      ∀ᵐ x ∂μ.restrict K, ‖coeff i n x‖ ≤ M i n := by
    filter_upwards [ae_restrict_mem hK] with x hx
    have hci : |c i x| ≤ |C i| := (hc_bound i x hx).trans (le_abs_self _)
    have hd : ε ≤ |affineDenominator a b t₀ x| := hden x hx
    have hdpos : 0 < |affineDenominator a b t₀ x| := hε.trans_le hd
    have hrat :
        |(b x - a x) / affineDenominator a b t₀ x| ≤ Q := hratio x hx
    have hrat' :
        |-(b x - a x) / affineDenominator a b t₀ x| ≤ Q := by
      simpa only [abs_div, abs_neg] using hrat
    dsimp [coeff, M]
    rw [abs_mul, abs_div, abs_pow]
    gcongr
  have hM_summable (i : Fin (N + 1)) :
      Summable (fun n ↦ M i n * r ^ n) := by
    have hQr_nonneg : 0 ≤ Q * r := mul_nonneg hQ hr.le
    have hQr_le : Q * r ≤ (1 : ℝ) / 2 := by
      calc
        Q * r = Q / (2 * (Q + 1)) := by simp [r, div_eq_mul_inv]
        _ ≤ (1 : ℝ) / 2 := by
          apply (div_le_iff₀ (by positivity : 0 < 2 * (Q + 1))).2
          nlinarith
    have hQr_norm : ‖Q * r‖ < (1 : ℝ) := by
      rw [Real.norm_eq_abs, abs_of_nonneg hQr_nonneg]
      exact hQr_le.trans_lt (by norm_num)
    have heq : (fun n ↦ M i n * r ^ n) =
        (fun n ↦ (|C i| / ε) * (Q * r) ^ n) := by
      funext n
      dsimp [M]
      rw [mul_pow]
      ring
    rw [heq]
    exact (summable_geometric_of_norm_lt_one hQr_norm).mul_left (|C i| / ε)
  have hseries (i : Fin (N + 1)) :
      ∀ t, |t - t₀| < r → ∀ᵐ x ∂μ.restrict K,
        c i x / affineDenominator a b t x =
          ∑' n : ℕ, coeff i n x * (t - t₀) ^ n := by
    intro t ht
    filter_upwards [ae_restrict_mem hK] with x hx
    have hd : ε ≤ |affineDenominator a b t₀ x| := hden x hx
    have hdpos : 0 < |affineDenominator a b t₀ x| := hε.trans_le hd
    have hrat :
        |(b x - a x) / affineDenominator a b t₀ x| ≤ Q := hratio x hx
    have hsmall :
        |(t - t₀) * (b x - a x) / affineDenominator a b t₀ x| < 1 := by
      calc
        |(t - t₀) * (b x - a x) / affineDenominator a b t₀ x| =
            |t - t₀| * |(b x - a x) / affineDenominator a b t₀ x| := by
              rw [mul_div_assoc, abs_mul]
        _ ≤ |t - t₀| * Q := by gcongr
        _ ≤ |t - t₀| * (Q + 1) := by
          gcongr
          linarith
        _ < r * (Q + 1) := mul_lt_mul_of_pos_right ht hQ1
        _ = 1 / 2 := by
          dsimp [r]
          field_simp
        _ < 1 := by norm_num
    have hrec := affineDenominator_reciprocal_eq_tsum
      (a := a) (b := b) (t := t) (t₀ := t₀) (x := x) (abs_pos.mp hdpos) hsmall
    calc
      c i x / affineDenominator a b t x =
          c i x * (affineDenominator a b t x)⁻¹ := div_eq_mul_inv _ _
      _ = c i x * ∑' n : ℕ,
          ((-(b x - a x) / affineDenominator a b t₀ x) ^ n /
            affineDenominator a b t₀ x) * (t - t₀) ^ n := by rw [hrec]
      _ = ∑' n : ℕ, c i x *
          (((-(b x - a x) / affineDenominator a b t₀ x) ^ n /
            affineDenominator a b t₀ x) * (t - t₀) ^ n) := by
              rw [tsum_mul_left]
      _ = ∑' n : ℕ, coeff i n x * (t - t₀) ^ n := by
        apply tsum_congr
        intro n
        dsimp [coeff]
        ring
  have hAi (i : Fin (N + 1)) :
      AnalyticAt ℝ
        (fun t ↦ ∫ x, c i x / affineDenominator a b t x ∂μ.restrict K) t₀ :=
    analyticAt_integral_of_powerSeries_domination
      (μ.restrict K)
      (fun t x ↦ c i x / affineDenominator a b t x)
      (coeff i) (M i) t₀ r hr (hcoeff_meas i) (hM_nonneg i)
      (hcoeff_bound i) (hM_summable i) (hseries i)
  have hsum : AnalyticAt ℝ
      (fun t ↦ ∑ i : Fin (N + 1),
        t ^ (i : ℕ) * ∫ x, c i x / affineDenominator a b t x ∂μ.restrict K) t₀ := by
    apply ((Finset.univ : Finset (Fin (N + 1))).analyticAt_sum
        (f := fun (i : Fin (N + 1)) (t : ℝ) ↦
        t ^ (i : ℕ) * ∫ x, c i x / affineDenominator a b t x ∂μ.restrict K)
        (fun (i : Fin (N + 1)) _ ↦ (analyticAt_id.pow (i : ℕ)).mul (hAi i))).congr
    exact Filter.Eventually.of_forall (fun t ↦ by simp)
  apply hsum.congr
  rcases affineDenominator_uniformly_nonzero_near_of_slope_div_bound hε hQ hden hratio with
    ⟨δ, hδ, hden_near⟩
  filter_upwards [Metric.ball_mem_nhds t₀ hδ] with t ht
  have hd_t_meas : Measurable (fun x ↦ affineDenominator a b t x) := by
    unfold affineDenominator
    fun_prop
  have hfi (i : Fin (N + 1)) :
      Integrable (fun x ↦ t ^ (i : ℕ) *
        (c i x / affineDenominator a b t x)) (μ.restrict K) := by
    apply Integrable.const_mul
    apply Integrable.of_bound ((hc i).div hd_t_meas).aestronglyMeasurable (|C i| / (ε / 2))
    filter_upwards [ae_restrict_mem hK] with x hx
    have hci : |c i x| ≤ |C i| := (hc_bound i x hx).trans (le_abs_self _)
    have hd : ε / 2 ≤ |affineDenominator a b t x| :=
      hden_near t (by simpa [Real.dist_eq] using ht) x hx
    have hdpos : 0 < |affineDenominator a b t x| := (half_pos hε).trans_le hd
    change |c i x / affineDenominator a b t x| ≤ |C i| / (ε / 2)
    rw [abs_div]
    gcongr
  simp only [polynomialNumerator]
  have hpoint :
      (fun x ↦ (∑ i : Fin (N + 1), c i x * t ^ (i : ℕ)) /
        affineDenominator a b t x) =
      (fun x ↦ ∑ i : Fin (N + 1), t ^ (i : ℕ) *
        (c i x / affineDenominator a b t x)) := by
    funext x
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hpoint]
  rw [integral_finsetSum Finset.univ (fun i _ ↦ hfi i)]
  simp only [integral_const_mul]

/-- Given [a measure](hyp:μ), [a measurable integration set of finite measure](hyp:hK,hμK), [a polynomial degree, coefficient functions, and affine endpoint functions](hyp:N,c,a,b), [a center, positive separation margin and radius, and coefficient bounds](hyp:t₀,ε,r,C), [positive numerical bounds](hyp:hε,hr), [measurability of the coefficients and endpoints](hyp:hc,ha,hb), [a uniform coefficient bound](hyp:hc_bound), and [uniform denominator separation throughout the parameter ball](hyp:hden), [the polynomial-over-affine set integral is real analytic at the ball center](goal). -/
theorem analyticAt_setIntegral_polynomial_div_affine_of_uniform_nonzero_near
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {K : Set α} (hK : MeasurableSet K) (hμK : μ K ≠ ∞)
    (N : ℕ) (c : Fin (N + 1) → α → ℝ) (a b : α → ℝ)
    (t₀ ε r : ℝ) (C : Fin (N + 1) → ℝ)
    (hε : 0 < ε) (hr : 0 < r)
    (hc : ∀ i, Measurable (c i)) (ha : Measurable a) (hb : Measurable b)
    (hc_bound : ∀ i, ∀ x ∈ K, |c i x| ≤ C i)
    (hden : ∀ t, |t - t₀| < r → ∀ x ∈ K,
      ε ≤ |affineDenominator a b t x|) :
    AnalyticAt ℝ
      (fun t ↦ ∫ x in K, polynomialNumerator N c t x / affineDenominator a b t x ∂μ) t₀ := by
  -- Derive the center-relative slope bound `r⁻¹` from the nonvanishing ball using
  -- `affineDenominator_slope_div_le_inv_radius`, then invoke the preceding theorem.
  have hden₀ : ∀ x ∈ K, ε ≤ |affineDenominator a b t₀ x| :=
    hden t₀ (by simpa using hr)
  have hratio := affineDenominator_slope_div_le_inv_radius hr hε hden
  have hQ : 0 ≤ r⁻¹ := inv_nonneg.mpr (le_of_lt hr)
  exact analyticAt_setIntegral_polynomial_div_affine_of_slope_div_bound
    μ hK hμK N c a b t₀ ε r⁻¹ C hε hQ hc ha hb hc_bound hratio hden₀

/-- Given [a measure](hyp:μ), [a measurable integration set of finite measure](hyp:hK,hμK), [a polynomial degree, coefficient functions, and affine endpoint functions](hyp:N,c,a,b), [an open parameter set, a positive separation margin, and coefficient bounds](hyp:O,ε,C), [openness and positivity](hyp:hO,hε), [measurability of the coefficients and endpoints](hyp:hc,ha,hb), [a uniform coefficient bound](hyp:hc_bound), and [uniform denominator separation throughout the parameter and integration sets](hyp:hden), [the polynomial-over-affine set integral is real analytic throughout the open parameter set](goal). -/
theorem analyticOnNhd_setIntegral_polynomial_div_affine_of_uniform_nonzero
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {K : Set α} (hK : MeasurableSet K) (hμK : μ K ≠ ∞)
    (N : ℕ) (c : Fin (N + 1) → α → ℝ) (a b : α → ℝ)
    (O : Set ℝ) (ε : ℝ) (C : Fin (N + 1) → ℝ)
    (hO : IsOpen O) (hε : 0 < ε)
    (hc : ∀ i, Measurable (c i)) (ha : Measurable a) (hb : Measurable b)
    (hc_bound : ∀ i, ∀ x ∈ K, |c i x| ≤ C i)
    (hden : ∀ t ∈ O, ∀ x ∈ K, ε ≤ |affineDenominator a b t x|) :
    AnalyticOnNhd ℝ
      (fun t ↦ ∫ x in K, polynomialNumerator N c t x / affineDenominator a b t x ∂μ) O := by
  -- Unfold `AnalyticOnNhd` pointwise.  Openness supplies a positive parameter ball contained
  -- in `O`; restrict `hden` to that ball and apply the preceding ball-local theorem.
  intro t₀ ht₀
  rcases affineDenominator_uniformly_nonzero_on_open_near hO hε hden ht₀ with
    ⟨r, hr, _hball, hden_ball⟩
  exact analyticAt_setIntegral_polynomial_div_affine_of_uniform_nonzero_near
    μ hK hμK N c a b t₀ ε r C hε hr hc ha hb hc_bound fun t ht ↦
      hden_ball t (by simpa [Metric.mem_ball, Real.dist_eq] using ht)

end Causalean.Mathlib.Analysis.ParametricRationalIntegralAnalyticity
