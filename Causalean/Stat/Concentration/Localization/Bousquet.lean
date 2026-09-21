module
public import Causalean.Stat.Concentration.EntropyMethod.CountableEmpiricalBousquet
public import Causalean.Stat.Concentration.Rademacher.Symmetrization
public import FoML.BoundedDifference
public import Mathlib.Probability.Moments.Variance

/-!
# Variance-sensitive concentration for countable uniform deviations

This file specializes the countable-class Bousquet inequality to the absolute empirical
deviation used by the localized-complexity API.  The class is centered, divided by twice its
uniform envelope, and doubled by a Boolean sign; this represents the absolute supremum without
assuming that any countable supremum is attained.
-/

public section

open MeasureTheory ProbabilityTheory

namespace Causalean.Stat.Concentration

open EntropyMethod

universe u v

private noncomputable def normalizedSignedScore
    {Ω : Type u} {ι : Type v} [MeasurableSpace Ω]
    (mu : Measure Ω) (f : ι → Ω → ℝ) (b : ℝ) : Bool × ι → Ω → ℝ :=
  fun q x => if q.1 then
    (f q.2 x - ∫ y, f q.2 y ∂mu) / (2 * b)
  else
    -(f q.2 x - ∫ y, f q.2 y ∂mu) / (2 * b)

private lemma normalizedSignedScore_measurable
    {Ω : Type u} {ι : Type v} [MeasurableSpace Ω]
    (mu : Measure Ω) (f : ι → Ω → ℝ) (hf : ∀ i, Measurable (f i)) (b : ℝ) :
    ∀ q, Measurable (normalizedSignedScore mu f b q) := by
  rintro ⟨sign, i⟩
  cases sign
  · unfold normalizedSignedScore
    dsimp
    fun_prop
  · unfold normalizedSignedScore
    dsimp
    fun_prop

private lemma integral_abs_le_envelope
    {Ω : Type u} {ι : Type v} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (f : ι → Ω → ℝ) (hf : ∀ i, Measurable (f i))
    {b : ℝ} (hbound : ∀ i x, |f i x| ≤ b) (i : ι) :
    |∫ x, f i x ∂mu| ≤ b := by
  have hint : Integrable (f i) mu :=
    Integrable.of_bound (hf i).aestronglyMeasurable b
      (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hbound i x)
  calc
    |∫ x, f i x ∂mu| ≤ ∫ x, |f i x| ∂mu := abs_integral_le_integral_abs
    _ ≤ ∫ _x, b ∂mu := integral_mono hint.abs (integrable_const b) (hbound i)
    _ = b := by simp

private lemma normalizedSignedScore_abs_le_one
    {Ω : Type u} {ι : Type v} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (f : ι → Ω → ℝ) (hf : ∀ i, Measurable (f i))
    {b : ℝ} (hb : 0 < b) (hbound : ∀ i x, |f i x| ≤ b) :
    ∀ q x, |normalizedSignedScore mu f b q x| ≤ 1 := by
  rintro ⟨sign, i⟩ x
  have hmean := integral_abs_le_envelope mu f hf hbound i
  have hcenter : |f i x - ∫ y, f i y ∂mu| ≤ 2 * b :=
    (abs_sub _ _).trans (by linarith [hbound i x])
  cases sign <;> simp only [normalizedSignedScore, Bool.false_eq_true, ↓reduceIte,
    abs_div, abs_neg]
  all_goals
    rw [abs_of_pos (by positivity : 0 < 2 * b)]
    exact (div_le_one (by positivity : 0 < 2 * b)).mpr hcenter

private lemma normalizedSignedScore_integral_eq_zero
    {Ω : Type u} {ι : Type v} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (f : ι → Ω → ℝ) (hf : ∀ i, Measurable (f i))
    {b : ℝ} (hb : 0 < b) (hbound : ∀ i x, |f i x| ≤ b) :
    ∀ q, ∫ x, normalizedSignedScore mu f b q x ∂mu = 0 := by
  rintro ⟨sign, i⟩
  have hint : Integrable (f i) mu :=
    Integrable.of_bound (hf i).aestronglyMeasurable b
      (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hbound i x)
  cases sign
  · simp only [normalizedSignedScore, Bool.false_eq_true, ↓reduceIte]
    rw [integral_div, integral_neg, integral_sub hint (integrable_const _)]
    simp
  · simp only [normalizedSignedScore, ↓reduceIte]
    rw [integral_div, integral_sub hint (integrable_const _)]
    simp

private lemma normalizedSignedScore_second_le
    {Ω : Type u} {ι : Type v} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (f : ι → Ω → ℝ) (hf : ∀ i, Measurable (f i))
    {b r : ℝ} (hb : 0 < b)
    (hvariance : ∀ i, variance (f i) mu ≤ r ^ 2) :
    ∀ q, (∫ x, (normalizedSignedScore mu f b q x) ^ 2 ∂mu) ≤
      r ^ 2 / (4 * b ^ 2) := by
  rintro ⟨sign, i⟩
  have hvar := hvariance i
  rw [variance_eq_integral (hf i).aemeasurable] at hvar
  cases sign <;> simp only [normalizedSignedScore, Bool.false_eq_true, ↓reduceIte,
    neg_div, neg_sq]
  all_goals
    simp_rw [div_pow]
    rw [show (2 * b) ^ 2 = 4 * b ^ 2 by ring, integral_div]
    exact div_le_div_of_nonneg_right hvar (by positivity)

private lemma finiteScore_normalizedSignedScore
    {Ω : Type u} {ι : Type v} [MeasurableSpace Ω]
    (mu : Measure Ω) (f : ι → Ω → ℝ) {b : ℝ} (hb : 0 < b)
    (n : ℕ) (hn : 0 < n) (s : Fin n → Ω) (q : Bool × ι) :
    finiteEmpiricalScore (normalizedSignedScore mu f b) n (fun _ => 0) q s =
      if q.1 then
        (n : ℝ) / (2 * b) *
          ((n : ℝ)⁻¹ * ∑ k, f q.2 (s k) - ∫ x, f q.2 x ∂mu)
      else
        -((n : ℝ) / (2 * b) *
          ((n : ℝ)⁻¹ * ∑ k, f q.2 (s k) - ∫ x, f q.2 x ∂mu)) := by
  rcases q with ⟨sign, i⟩
  cases sign <;> simp only [finiteEmpiricalScore, normalizedSignedScore,
    Bool.false_eq_true, ↓reduceIte]
  · rw [zero_add, ← Finset.sum_div]
    simp_rw [neg_sub]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hb.ne', Nat.cast_ne_zero.mpr hn.ne']
    ring
  · rw [zero_add, ← Finset.sum_div, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hb.ne', Nat.cast_ne_zero.mpr hn.ne']

private lemma countableEmpiricalSupremum_normalizedSignedScore
    {Ω : Type u} {ι : Type v} [MeasurableSpace Ω] [Nonempty ι] [Countable ι]
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (f : ι → Ω → ℝ) (hf : ∀ i, Measurable (f i))
    {b : ℝ} (hb : 0 < b) (hbound : ∀ i x, |f i x| ≤ b)
    (n : ℕ) (hn : 0 < n) (s : Fin n → Ω) :
    countableEmpiricalSupremum (Bool × ι) (normalizedSignedScore mu f b) n s =
      (n : ℝ) / (2 * b) * uniformDeviation n f mu id s := by
  let scale : ℝ := (n : ℝ) / (2 * b)
  have hscale : 0 < scale := div_pos (Nat.cast_pos.mpr hn) (by positivity)
  let dev : ι → ℝ := fun i =>
    (n : ℝ)⁻¹ * ∑ k, f i (s k) - ∫ x, f i x ∂mu
  have hdev_abs : ∀ i, |dev i| ≤ 2 * b := by
    intro i
    have hmean := integral_abs_le_envelope mu f hf hbound i
    have havg : |(n : ℝ)⁻¹ * ∑ k, f i (s k)| ≤ b := by
      calc
        |(n : ℝ)⁻¹ * ∑ k, f i (s k)| =
            (n : ℝ)⁻¹ * |∑ k, f i (s k)| := by
              rw [abs_mul, abs_of_pos (inv_pos.mpr (Nat.cast_pos.mpr hn))]
        _ ≤ (n : ℝ)⁻¹ * ∑ k, |f i (s k)| := by
          gcongr
          exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ (n : ℝ)⁻¹ * ∑ _k : Fin n, b := by
          gcongr with k
          exact hbound i (s k)
        _ = b := by simp [hn.ne']
    exact (abs_sub _ _).trans (by linarith)
  have hdev_bdd : BddAbove (Set.range fun i : ι => |dev i|) :=
    ⟨2 * b, by rintro _ ⟨i, rfl⟩; exact hdev_abs i⟩
  have hscore (q : Bool × ι) :
      finiteEmpiricalScore (normalizedSignedScore mu f b) n (fun _ => 0) q s =
        if q.1 then scale * dev q.2 else -(scale * dev q.2) := by
    rw [finiteScore_normalizedSignedScore mu f hb n hn s q]
  have hg_abs : ∀ q x, |normalizedSignedScore mu f b q x| ≤ 1 :=
    normalizedSignedScore_abs_le_one mu f hf hb hbound
  have hscore_bdd : BddAbove (Set.range fun q : Bool × ι =>
      finiteEmpiricalScore (normalizedSignedScore mu f b) n (fun _ => 0) q s) := by
    refine ⟨(n : ℝ), ?_⟩
    rintro _ ⟨q, rfl⟩
    exact (le_abs_self _).trans
      (by
        have h := abs_finiteEmpiricalScore_le (A := 0) (B := 1)
          (normalizedSignedScore mu f b) hg_abs n (fun _ => 0)
          (fun _ => by simp) q s
        simpa using h)
  unfold countableEmpiricalSupremum uniformDeviation
  simp only [id_eq]
  apply le_antisymm
  · apply ciSup_le
    rintro ⟨sign, i⟩
    rw [hscore]
    have hi : |dev i| ≤ ⨆ j : ι, |dev j| := le_ciSup hdev_bdd i
    cases sign
    · simp only [Bool.false_eq_true, ↓reduceIte]
      calc
        -(scale * dev i) ≤ |scale * dev i| := neg_le_abs _
        _ = scale * |dev i| := by rw [abs_mul, abs_of_pos hscale]
        _ ≤ scale * ⨆ j : ι, |dev j| := mul_le_mul_of_nonneg_left hi hscale.le
    · simp only [↓reduceIte]
      calc
        scale * dev i ≤ |scale * dev i| := le_abs_self _
        _ = scale * |dev i| := by rw [abs_mul, abs_of_pos hscale]
        _ ≤ scale * ⨆ j : ι, |dev j| := mul_le_mul_of_nonneg_left hi hscale.le
  · rw [Real.mul_iSup_of_nonneg hscale.le]
    apply ciSup_le
    intro i
    by_cases hdi : 0 ≤ dev i
    · rw [abs_of_nonneg hdi]
      have hle := le_ciSup hscore_bdd (true, i)
      simpa [hscore] using hle
    · rw [abs_of_nonpos (le_of_not_ge hdi)]
      have hle := le_ciSup hscore_bdd (false, i)
      simpa [hscore] using hle

/-- **Variance-sensitive countable uniform-deviation tail.** For [a positive sample size
`n`](hyp:hn), [a countable measurable class `f`](hyp:f,hf) [bounded by the positive envelope
`b`](hyp:hb,hbound), suppose [every class member has variance at most `r²`](hyp:hvariance), [the
    expected uniform deviation is at most `M`](hyp:hmean_le), and [the localized radius is positive
and the mean proxy is nonnegative](hyp:hr,hM). Then for [positive `x`](hyp:hx), [the probability that the
uniform deviation exceeds `M + 2√((r² + 4bM)x/n) + 8bx/n` is at most `exp(-x)`](goal). -/
theorem uniform_deviation_bousquet_tail_countable
    {Ω : Type u} {ι : Type v} [MeasurableSpace Ω] [Nonempty ι] [Countable ι]
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (f : ι → Ω → ℝ) (hf : ∀ i, Measurable (f i))
    {b r M : ℝ} (hb : 0 < b) (hbound : ∀ i x, |f i x| ≤ b)
    (hr : 0 < r) (hvariance : ∀ i, variance (f i) mu ≤ r ^ 2)
    (hM : 0 ≤ M) (n : ℕ) (hn : 0 < n)
    (hmean_le : ∫ s, uniformDeviation n f mu id s
        ∂Measure.pi (fun _ : Fin n => mu) ≤ M)
    {x : ℝ} (hx : 0 < x) :
    (Measure.pi (fun _ : Fin n => mu)).real
        {s | M + 2 * Real.sqrt ((r ^ 2 + 4 * b * M) * x / n) + 8 * b * x / n ≤
          uniformDeviation n f mu id s} ≤ Real.exp (-x) := by
  classical
  let productMeasure : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => mu)
  let g := normalizedSignedScore mu f b
  let Z := countableEmpiricalSupremum (Bool × ι) g n
  let W := uniformDeviation n f mu id
  let scale : ℝ := (n : ℝ) / (2 * b)
  let sigma2 : ℝ := r ^ 2 / (4 * b ^ 2)
  let meanZ : ℝ := ∫ s, Z s ∂productMeasure
  let slack : ℝ :=
    2 * Real.sqrt ((r ^ 2 + 4 * b * M) * x / n) + 8 * b * x / n
  let t : ℝ := scale * slack
  have hscale : 0 < scale := div_pos (Nat.cast_pos.mpr hn) (by positivity)
  have hZW : ∀ s, Z s = scale * W s := by
    intro s
    exact countableEmpiricalSupremum_normalizedSignedScore mu f hf hb hbound n hn s
  have hmeanZ : meanZ = scale * ∫ s, W s ∂productMeasure := by
    dsimp [meanZ]
    calc
      ∫ s, Z s ∂productMeasure = ∫ s, scale * W s ∂productMeasure :=
        integral_congr_ae (ae_of_all _ hZW)
      _ = scale * ∫ s, W s ∂productMeasure := by
        exact integral_const_mul scale W
  have hmeanZ_le : meanZ ≤ scale * M := by
    rw [hmeanZ]
    exact mul_le_mul_of_nonneg_left hmean_le hscale.le
  have hsigma_nonneg : 0 ≤ sigma2 := by
    dsimp [sigma2]
    positivity
  have hsigma_pos : 0 < sigma2 := by
    dsimp [sigma2]
    positivity
  have htailScale : 0 < meanZ + (n : ℝ) * sigma2 / 2 := by
    have hZ_nonneg : ∀ s, 0 ≤ Z s := by
      intro s
      rw [hZW]
      apply mul_nonneg hscale.le
      dsimp [W, uniformDeviation]
      exact Real.iSup_nonneg fun i => abs_nonneg _
    have hmeanZ_nonneg : 0 ≤ meanZ := by
      dsimp [meanZ]
      exact integral_nonneg hZ_nonneg
    positivity
  have hA_nonneg : 0 ≤ r ^ 2 + 4 * b * M := by positivity
  have hsqrt_pos : 0 < Real.sqrt ((r ^ 2 + 4 * b * M) * x / n) := by
    apply Real.sqrt_pos.2
    positivity
  have hslack_pos : 0 < slack := by
    dsimp [slack]
    positivity
  have ht : 0 < t := mul_pos hscale hslack_pos
  have htail := countableEmpiricalSupremum_upper_tail mu g
    (normalizedSignedScore_measurable mu f hf b) (B := 1) (sigma2 := sigma2)
    (by norm_num)
    (normalizedSignedScore_abs_le_one mu f hf hb hbound)
    (fun q y => (le_abs_self (g q y)).trans
      (normalizedSignedScore_abs_le_one mu f hf hb hbound q y))
    (normalizedSignedScore_integral_eq_zero mu f hf hb hbound)
    hsigma_nonneg (normalizedSignedScore_second_le mu f hf hb hvariance)
    n htailScale ht
  have htarget_subset :
      {s | M + slack ≤ W s} ⊆ {s | t ≤ Z s - meanZ} := by
    intro s hs
    change M + slack ≤ W s at hs
    change t ≤ Z s - meanZ
    rw [hZW s]
    dsimp [t]
    calc
      scale * slack ≤ scale * (W s - ∫ u, W u ∂productMeasure) := by
        apply mul_le_mul_of_nonneg_left _ hscale.le
        linarith
      _ = scale * W s - meanZ := by rw [hmeanZ]; ring
  have hmeasure_le : productMeasure.real {s | M + slack ≤ W s} ≤
      productMeasure.real {s | t ≤ Z s - meanZ} := by
    exact ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono htarget_subset)
  let denom : ℝ := 8 * (meanZ + (n : ℝ) * sigma2 / 2) + 4 * t
  have hdenom_pos : 0 < denom := by dsimp [denom]; positivity
  have hdenom_le : denom ≤
      (n : ℝ) / b ^ 2 * (r ^ 2 + 4 * b * M + 2 * b * slack) := by
    calc
      denom ≤ 8 * (scale * M + (n : ℝ) * sigma2 / 2) + 4 * t := by
        dsimp [denom]
        gcongr
      _ = (n : ℝ) / b ^ 2 *
          (r ^ 2 + 4 * b * M + 2 * b * slack) := by
        dsimp [sigma2, t, scale]
        field_simp [hb.ne']
        ring
  have harith : x * ((n : ℝ) / b ^ 2 *
      (r ^ 2 + 4 * b * M + 2 * b * slack)) ≤ t ^ 2 := by
    have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb
    have hsqrt_sq :
        (Real.sqrt ((r ^ 2 + 4 * b * M) * x / n)) ^ 2 =
          (r ^ 2 + 4 * b * M) * x / n := by
      rw [Real.sq_sqrt]
      positivity
    have hsqrt_nonneg :
        0 ≤ Real.sqrt ((r ^ 2 + 4 * b * M) * x / n) := Real.sqrt_nonneg _
    dsimp [t, scale, slack]
    field_simp [hb.ne', hnR.ne'] at hsqrt_sq ⊢
    nlinarith [mul_nonneg (mul_nonneg hnR.le hx.le) hsqrt_nonneg]
  have hratio : x ≤ t ^ 2 / denom := by
    rw [le_div_iff₀ hdenom_pos]
    calc
      x * denom ≤ x * ((n : ℝ) / b ^ 2 *
          (r ^ 2 + 4 * b * M + 2 * b * slack)) :=
        mul_le_mul_of_nonneg_left hdenom_le hx.le
      _ ≤ t ^ 2 := harith
  have hfinal : productMeasure.real {s | M + slack ≤ W s} ≤ Real.exp (-x) := by
    calc
      productMeasure.real {s | M + slack ≤ W s} ≤
        productMeasure.real {s | t ≤ Z s - meanZ} := hmeasure_le
      _ ≤ Real.exp (-t ^ 2 / denom) := by
        simpa [productMeasure, Z, meanZ, g, sigma2, t, denom] using htail
      _ ≤ Real.exp (-x) := Real.exp_le_exp.mpr (by
        simpa only [neg_div] using neg_le_neg hratio)
  simpa only [productMeasure, W, slack, add_assoc] using hfinal

/-- If [the variance-sensitive normalized peeling slack at radius `ρ` is at most
`ρ`](hyp:hdom), [the corresponding unnormalized slack at any shell radius `q ≥ ρ`, with variance
center at most `ρ`](hyp:hq,hc), [is at most `qρ`](goal), provided [the envelope, radii, logarithmic
factor, and sample size have the stated signs](hyp:hb,hρ,hx,hn). -/
lemma bousquet_shell_slack_le
    {b ρ q c x : ℝ} {n : ℕ}
    (hb : 0 ≤ b) (hρ : 0 < ρ) (hq : ρ ≤ q) (hc : c ≤ ρ)
    (hx : 0 ≤ x) (hn : 0 < n)
    (hdom : 2 * Real.sqrt ((1 + 8 * b) * x / n)
        + 8 * b * x / (n * ρ) ≤ ρ) :
    2 * Real.sqrt ((q ^ 2 + 8 * b * q * c) * x / n)
        + 8 * b * x / n ≤ q * ρ := by
  have hq0 : 0 ≤ q := hρ.le.trans hq
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  let a : ℝ := x / n
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hinside :
      (q ^ 2 + 8 * b * q * c) * a ≤ q ^ 2 * ((1 + 8 * b) * a) := by
    have hprod : 0 ≤ b * q * (q - c) * a :=
      mul_nonneg (mul_nonneg (mul_nonneg hb hq0) (sub_nonneg.mpr (hc.trans hq))) ha
    nlinarith
  have hsqrt :
      Real.sqrt ((q ^ 2 + 8 * b * q * c) * a) ≤
        q * Real.sqrt ((1 + 8 * b) * a) := by
    calc
      _ ≤ Real.sqrt (q ^ 2 * ((1 + 8 * b) * a)) := Real.sqrt_le_sqrt hinside
      _ = q * Real.sqrt ((1 + 8 * b) * a) := by
        rw [Real.sqrt_mul (sq_nonneg q), Real.sqrt_sq_eq_abs, abs_of_nonneg hq0]
  have hfactor : 0 ≤ 8 * b * x / (n * ρ) := by positivity
  have hlinear : 8 * b * x / n ≤ q * (8 * b * x / (n * ρ)) := by
    calc
      8 * b * x / n = ρ * (8 * b * x / (n * ρ)) := by
        field_simp [hρ.ne', hnR.ne']
      _ ≤ q * (8 * b * x / (n * ρ)) := mul_le_mul_of_nonneg_right hq hfactor
  calc
    2 * Real.sqrt ((q ^ 2 + 8 * b * q * c) * x / n) + 8 * b * x / n =
        2 * Real.sqrt ((q ^ 2 + 8 * b * q * c) * a) + 8 * b * x / n := by
      dsimp [a]
      congr 2
      ring
    _ ≤ q * (2 * Real.sqrt ((1 + 8 * b) * a) + 8 * b * x / (n * ρ)) := by
      nlinarith [hsqrt, hlinear]
    _ ≤ q * ρ := by
      apply mul_le_mul_of_nonneg_left _ hq0
      have haform : (1 + 8 * b) * a = (1 + 8 * b) * x / n := by
        dsimp [a]
        ring
      rw [haform]
      exact hdom

end Causalean.Stat.Concentration
