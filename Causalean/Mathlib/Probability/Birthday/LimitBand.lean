module
public import Causalean.Mathlib.Probability.Birthday.LimitScale

/-!
# Relative-band scale estimates for the birthday limit

The binomial mean is negligible relative to the alphabet at positive finite
collision scale. Pair counts on a relative mean band have uniform limits with
both the full and the remaining-alphabet denominators.
-/

public section

namespace Causalean.Mathlib.Probability.Birthday

open Filter

/-- For [valid success probabilities](hyp:heta), a [diverging mean](hyp:hmean),
[positive alphabets](hyp:hm), and a [convergent collision scale](hyp:hscale),
the [mean divided by the alphabet](goal) tends to zero. -/
theorem mean_div_alphabet_tendsto_zero
    (Tseq mseq : ℕ → ℕ) (etaseq : ℕ → ℝ) {q : ℝ}
    (heta : ∀ j, etaseq j ∈ Set.Icc (0 : ℝ) 1)
    (hmean : Tendsto (fun j => mean (Tseq j) (etaseq j)) atTop atTop)
    (hm : ∀ j, 0 < mseq j)
    (hscale : Tendsto
      (fun j => pairScale (Tseq j) (etaseq j) / (mseq j : ℝ)) atTop (nhds q)) :
    Tendsto (fun j => mean (Tseq j) (etaseq j) / (mseq j : ℝ))
      atTop (nhds 0) := by
  -- Factor μ/m as (A/m)·(μ/A); A/(μ²/2)→1 and μ→∞.
  -- Alternatively derive m/μ→∞ from A/m→q and A~μ²/2.
  have hd : Tendsto (fun j => mean (Tseq j) (etaseq j) - etaseq j)
      atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [hmean.eventually_ge_atTop (b + 1)] with j hj
    have he := (heta j).2
    linarith
  have hinv : Tendsto (fun j => (mean (Tseq j) (etaseq j) - etaseq j)⁻¹)
      atTop (nhds 0) := tendsto_inv_atTop_zero.comp hd
  have hprod := (hscale.const_mul 2).mul hinv
  have hpos := hd.eventually_gt_atTop 0
  have hprod' : Tendsto (fun j => 2 * (pairScale (Tseq j) (etaseq j) /
      (mseq j : ℝ)) * (mean (Tseq j) (etaseq j) - etaseq j)⁻¹)
      atTop (nhds 0) := by simpa using hprod
  apply hprod'.congr'
  filter_upwards [hpos] with j hj
  have hmj : (mseq j : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hm j))
  have hdj : mean (Tseq j) (etaseq j) - etaseq j ≠ 0 := ne_of_gt hj
  have hident : 2 * pairScale (Tseq j) (etaseq j) =
      mean (Tseq j) (etaseq j) *
        (mean (Tseq j) (etaseq j) - etaseq j) := by
    simp only [pairScale, mean, Nat.cast_choose_two]
    ring
  field_simp [hmj, hdj]
  nlinarith [hident]

/-- For [valid success probabilities](hyp:heta), a [diverging mean](hyp:hmean),
[positive alphabets](hyp:hm), a [convergent collision scale](hyp:hscale),
and a [fixed relative band width](hyp:hε), draw counts in that band are
[eventually below the alphabet](goal). -/
theorem relative_band_below_alphabet
    (Tseq mseq : ℕ → ℕ) (etaseq : ℕ → ℝ) {q ε : ℝ}
    (heta : ∀ j, etaseq j ∈ Set.Icc (0 : ℝ) 1)
    (hmean : Tendsto (fun j => mean (Tseq j) (etaseq j)) atTop atTop)
    (hm : ∀ j, 0 < mseq j)
    (hscale : Tendsto
      (fun j => pairScale (Tseq j) (etaseq j) / (mseq j : ℝ)) atTop (nhds q))
    (hε : 0 < ε) :
    ∀ᶠ j in atTop, ∀ r : ℕ,
      |(r : ℝ) - mean (Tseq j) (etaseq j)| <
        ε * mean (Tseq j) (etaseq j) → r ≤ mseq j := by
  -- The band gives r < (1+ε)μ; μ/m→0 implies (1+ε)μ<m eventually.
  have hzero := mean_div_alphabet_tendsto_zero Tseq mseq etaseq heta hmean hm hscale
  have hc : (0 : ℝ) < 1 / (1 + ε) := by positivity
  have hsmall := hzero.eventually (eventually_lt_nhds hc)
  have hpos := hmean.eventually_gt_atTop 0
  filter_upwards [hsmall, hpos] with j hs hμ r hr
  have hmj : (0 : ℝ) < (mseq j : ℝ) := by exact_mod_cast hm j
  have hmul : mean (Tseq j) (etaseq j) / (mseq j : ℝ) * (1 + ε) < 1 :=
    (lt_div_iff₀ (by linarith : (0 : ℝ) < 1 + ε)).mp hs
  have hbound : mean (Tseq j) (etaseq j) * (1 + ε) < (mseq j : ℝ) := by
    have ht : mean (Tseq j) (etaseq j) * (1 + ε) / (mseq j : ℝ) < 1 := by
      calc
      mean (Tseq j) (etaseq j) * (1 + ε) / (mseq j : ℝ) =
          mean (Tseq j) (etaseq j) / (mseq j : ℝ) * (1 + ε) := by ring
      _ < 1 := hmul
    exact (div_lt_iff₀ hmj).mp ht |>.trans_eq (one_mul _)
  have hrlt : (r : ℝ) < (mseq j : ℝ) := by
    rw [abs_lt] at hr
    nlinarith [hr.2]
  exact Nat.le_of_lt (by exact_mod_cast hrlt)

/-- For [valid success probabilities](hyp:heta), a [diverging mean](hyp:hmean),
[positive alphabets](hyp:hm), and a [positive finite collision scale](hyp:hscale,hq),
the [pair count per alphabet](goal) is uniformly close to that scale on a
sufficiently narrow relative mean band. -/
theorem pairCount_div_alphabet_uniform_on_relative_band
    (Tseq mseq : ℕ → ℕ) (etaseq : ℕ → ℝ) {q : ℝ}
    (heta : ∀ j, etaseq j ∈ Set.Icc (0 : ℝ) 1)
    (hmean : Tendsto (fun j => mean (Tseq j) (etaseq j)) atTop atTop)
    (hm : ∀ j, 0 < mseq j)
    (hscale : Tendsto
      (fun j => pairScale (Tseq j) (etaseq j) / (mseq j : ℝ)) atTop (nhds q))
    (hq : 0 < q) :
    ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧
      ∀ᶠ j in atTop, ∀ r : ℕ,
        |(r : ℝ) - mean (Tseq j) (etaseq j)| <
          ε * mean (Tseq j) (etaseq j) →
        |(r.choose 2 : ℝ) / (mseq j : ℝ) - q| ≤ δ := by
  -- Write choose(r,2)=r(r-1)/2 and A~μ²/2; choose ε to bound
  -- |(r/μ)²-1| and use μ/m→0 for the linear r term.
  intro δ hδ
  let C : ℝ := 2 * q + 3
  have hC : 0 < C := by dsimp [C]; linarith
  let ε : ℝ := min (1 / 2) (δ / (12 * C))
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  have hεhalf : ε ≤ 1 / 2 := min_le_left _ _
  have hεC : ε * C ≤ δ / 12 := by
    calc
      ε * C ≤ (δ / (12 * C)) * C :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (le_of_lt hC)
      _ = δ / 12 := by field_simp
  refine ⟨ε, hε, ?_⟩
  have hzero := mean_div_alphabet_tendsto_zero Tseq mseq etaseq heta hmean hm hscale
  have hsmall := hzero.eventually (eventually_lt_nhds (show (0 : ℝ) < δ / 12 by positivity))
  have hone := hzero.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
  have hμpos := hmean.eventually_gt_atTop 0
  have hAnear := (Metric.tendsto_nhds.mp hscale) (δ / 4) (by positivity)
  have hAupper := hscale.eventually (eventually_lt_nhds (show q < q + 1 by linarith))
  filter_upwards [hsmall, hone, hμpos, hAnear, hAupper] with j hs hμone hμ hn hAu r hr
  let μ : ℝ := mean (Tseq j) (etaseq j)
  let A : ℝ := pairScale (Tseq j) (etaseq j)
  let m : ℝ := mseq j
  have hmpos : 0 < m := by dsimp [m]; exact_mod_cast hm j
  have hmne : m ≠ 0 := ne_of_gt hmpos
  have hsmall' : μ < (δ / 12) * m := (div_lt_iff₀ hmpos).mp hs
  have hμone' : μ < m := by simpa using (div_lt_iff₀ hmpos).mp hμone
  have hAupper' : A < (q + 1) * m := (div_lt_iff₀ hmpos).mp hAu
  have hident : 2 * A = μ * (μ - etaseq j) := by
    dsimp [A, μ]
    simp only [pairScale, mean, Nat.cast_choose_two]
    ring
  have he0 : 0 ≤ etaseq j := (heta j).1
  have he1 : etaseq j ≤ 1 := (heta j).2
  have heμ : μ * etaseq j ≤ μ := by
    nlinarith [mul_nonneg (le_of_lt hμ) (sub_nonneg.mpr he1)]
  have hμsq : μ ^ 2 ≤ C * m := by
    dsimp [C]
    nlinarith [hident]
  have hsqcap : 3 * ε * μ ^ 2 ≤ (δ / 4) * m := by
    calc
      3 * ε * μ ^ 2 ≤ (3 * ε) * (C * m) :=
        mul_le_mul_of_nonneg_left hμsq (by positivity)
      _ = (3 * (ε * C)) * m := by ring
      _ ≤ (δ / 4) * m :=
        mul_le_mul_of_nonneg_right (by nlinarith [hεC]) (le_of_lt hmpos)
  have hrband := (abs_lt.mp hr)
  have hrupper : (r : ℝ) ≤ 2 * μ := by
    have hh := mul_le_mul_of_nonneg_right hεhalf (le_of_lt hμ)
    nlinarith
  have hsum : 0 ≤ (r : ℝ) + μ := by positivity
  have hsumupper : (r : ℝ) + μ ≤ 3 * μ := by linarith
  have hsqabs : |(r : ℝ) ^ 2 - μ ^ 2| ≤ 3 * ε * μ ^ 2 := by
    have hf : (r : ℝ) ^ 2 - μ ^ 2 = ((r : ℝ) - μ) * ((r : ℝ) + μ) := by ring
    rw [hf, abs_mul, abs_of_nonneg hsum]
    calc
      |(r : ℝ) - μ| * ((r : ℝ) + μ) ≤ (ε * μ) * ((r : ℝ) + μ) :=
        mul_le_mul_of_nonneg_right (le_of_lt hr) hsum
      _ ≤ (ε * μ) * (3 * μ) :=
        mul_le_mul_of_nonneg_left hsumupper (by positivity)
      _ = 3 * ε * μ ^ 2 := by ring
  have hnum : |(r : ℝ) ^ 2 - (r : ℝ) - 2 * A| ≤ (δ / 2) * m := by
    rw [abs_le]
    have hsqbounds := abs_le.mp hsqabs
    constructor <;> nlinarith [hident, hsqcap, hsmall', hrupper, heμ]
  have hpairident : (r.choose 2 : ℝ) / m - A / m =
      ((r : ℝ) ^ 2 - (r : ℝ) - 2 * A) / (2 * m) := by
    rw [Nat.cast_choose_two]
    field_simp
  have hpair : |(r.choose 2 : ℝ) / m - A / m| ≤ δ / 4 := by
    rw [hpairident, abs_div, abs_of_pos (show 0 < 2 * m by positivity)]
    calc
      |(r : ℝ) ^ 2 - (r : ℝ) - 2 * A| / (2 * m) ≤
          ((δ / 2) * m) / (2 * m) :=
        div_le_div_of_nonneg_right hnum (by positivity)
      _ = δ / 4 := by field_simp; ring
  have hAnear' : |A / m - q| < δ / 4 := by simpa [Real.dist_eq, A, m] using hn
  have hfinal : |(r.choose 2 : ℝ) / m - q| ≤ δ := by
    calc
      |(r.choose 2 : ℝ) / m - q| ≤
          |(r.choose 2 : ℝ) / m - A / m| + |A / m - q| := by
        calc
          |(r.choose 2 : ℝ) / m - q| =
              |((r.choose 2 : ℝ) / m - A / m) + (A / m - q)| := by congr 1; ring
          _ ≤ _ := abs_add_le _ _
      _ ≤ δ := by linarith
  simpa [m] using hfinal

/-- For [valid success probabilities](hyp:heta), a [diverging mean](hyp:hmean),
[positive alphabets](hyp:hm), and a [positive finite collision scale](hyp:hscale,hq),
[for every tolerance there is a relative band width such that, eventually, every
draw count r not exceeding the alphabet size m and within that relative band of
the mean has its pair count divided by the remaining alphabet m + 1 − r within
the tolerance of that scale](goal). -/
theorem pairCount_div_remaining_uniform_on_relative_band
    (Tseq mseq : ℕ → ℕ) (etaseq : ℕ → ℝ) {q : ℝ}
    (heta : ∀ j, etaseq j ∈ Set.Icc (0 : ℝ) 1)
    (hmean : Tendsto (fun j => mean (Tseq j) (etaseq j)) atTop atTop)
    (hm : ∀ j, 0 < mseq j)
    (hscale : Tendsto
      (fun j => pairScale (Tseq j) (etaseq j) / (mseq j : ℝ)) atTop (nhds q))
    (hq : 0 < q) :
    ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧
      ∀ᶠ j in atTop, ∀ r : ℕ, r ≤ mseq j →
        |(r : ℝ) - mean (Tseq j) (etaseq j)| <
          ε * mean (Tseq j) (etaseq j) →
        |(r.choose 2 : ℝ) / (mseq j + 1 - r : ℕ) - q| ≤ δ := by
  -- On the band, r/m→0 uniformly. Compare denominators using
  -- (m+1-r)/m = 1 + 1/m - r/m, then apply the full-denominator estimate.
  intro δ hδ
  obtain ⟨εa, hεa, ha⟩ :=
    pairCount_div_alphabet_uniform_on_relative_band Tseq mseq etaseq heta hmean hm
      hscale hq (δ / 2) (by positivity)
  obtain ⟨εb, hεb, hb⟩ :=
    pairCount_div_alphabet_uniform_on_relative_band Tseq mseq etaseq heta hmean hm
      hscale hq 1 (by norm_num)
  let ε : ℝ := min εa (min εb 1)
  have hε : 0 < ε := lt_min hεa (lt_min hεb (by norm_num))
  have hεa' : ε ≤ εa := min_le_left _ _
  have hεb' : ε ≤ εb := le_trans (min_le_right _ _) (min_le_left _ _)
  have hεone : ε ≤ 1 := le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨ε, hε, ?_⟩
  have hzero := mean_div_alphabet_tendsto_zero Tseq mseq etaseq heta hmean hm hscale
  have hQ : 0 < q + 1 := by linarith
  have hc : 0 < min (1 / 4 : ℝ) (δ / (8 * (q + 1))) :=
    lt_min (by norm_num) (by positivity)
  have hsmall := hzero.eventually (eventually_lt_nhds hc)
  have hμpos := hmean.eventually_gt_atTop 0
  filter_upwards [ha, hb, hsmall, hμpos] with j haj hbj hs hμ r hrle hr
  let μ : ℝ := mean (Tseq j) (etaseq j)
  let m : ℝ := mseq j
  let c : ℝ := (r.choose 2 : ℝ)
  let d : ℝ := (mseq j + 1 - r : ℕ)
  have hmpos : 0 < m := by dsimp [m]; exact_mod_cast hm j
  have hmne : m ≠ 0 := ne_of_gt hmpos
  have hbandA : |(r : ℝ) - μ| < εa * μ := by
    exact lt_of_lt_of_le hr (mul_le_mul_of_nonneg_right hεa' (le_of_lt hμ))
  have hbandB : |(r : ℝ) - μ| < εb * μ := by
    exact lt_of_lt_of_le hr (mul_le_mul_of_nonneg_right hεb' (le_of_lt hμ))
  have hnear : |c / m - q| ≤ δ / 2 := haj r hbandA
  have hupper : c / m ≤ q + 1 := by
    have ht := hbj r hbandB
    have := (abs_le.mp ht).2
    linarith
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hcmax : c ≤ (q + 1) * m := (div_le_iff₀ hmpos).mp hupper
  have hμquarter : μ < m / 4 := by
    have ht : μ / m < (1 / 4 : ℝ) := lt_of_lt_of_le hs (min_le_left _ _)
    have ht' := (div_lt_iff₀ hmpos).mp ht
    nlinarith
  have hμdelta : (q + 1) * μ < (δ / 8) * m := by
    have ht : μ / m < δ / (8 * (q + 1)) :=
      lt_of_lt_of_le hs (min_le_right _ _)
    have ht' := (lt_div_iff₀ (show 0 < 8 * (q + 1) by positivity)).mp ht
    have ht'' : μ * (8 * (q + 1)) < δ * m := by
      calc
        μ * (8 * (q + 1)) = (μ / m * (8 * (q + 1))) * m := by
          field_simp
        _ < δ * m := mul_lt_mul_of_pos_right ht' hmpos
    nlinarith
  have hrupper : (r : ℝ) ≤ 2 * μ := by
    have hh := mul_le_mul_of_nonneg_right hεone (le_of_lt hμ)
    have ht := (abs_lt.mp hr).2
    nlinarith
  have hrhalf : (r : ℝ) ≤ m / 2 := by linarith
  have hrdelta : (q + 1) * (r : ℝ) ≤ (δ / 4) * m := by
    nlinarith [mul_le_mul_of_nonneg_left hrupper (le_of_lt hQ)]
  have hdidentity : d = m + 1 - (r : ℝ) := by
    dsimp [d, m]
    rw [Nat.cast_sub (by omega : r ≤ mseq j + 1)]
    push_cast
    ring
  have hdhalf : m / 2 ≤ d := by rw [hdidentity]; linarith
  have hdpos : 0 < d := by linarith
  have hdne : d ≠ 0 := ne_of_gt hdpos
  by_cases hrzero : r = 0
  · subst r
    have ht : |q| ≤ δ / 2 := by simpa [c] using hnear
    simpa [c, d] using (le_trans ht (by linarith : δ / 2 ≤ δ))
  have hrone : (1 : ℝ) ≤ r := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hrzero)
  have hdiffident : c / d - c / m = c * ((r : ℝ) - 1) / (m * d) := by
    rw [hdidentity]
    have hdne' : m + 1 - (r : ℝ) ≠ 0 := by rw [← hdidentity]; exact hdne
    field_simp [hmne, hdne']
    ring
  have hdiffnonneg : 0 ≤ c / d - c / m := by
    rw [hdiffident]
    positivity
  have hdiffcap : c / d - c / m ≤ δ / 2 := by
    rw [hdiffident]
    apply (div_le_iff₀ (mul_pos hmpos hdpos)).mpr
    have h1 : c * ((r : ℝ) - 1) ≤ c * (r : ℝ) := by nlinarith
    have h2 : c * (r : ℝ) ≤ ((q + 1) * m) * (r : ℝ) :=
      mul_le_mul_of_nonneg_right hcmax (by positivity)
    have h3 : ((q + 1) * m) * (r : ℝ) ≤ (δ / 4) * m ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hrdelta (le_of_lt hmpos)]
    have h4 : (δ / 4) * m ^ 2 ≤ (δ / 2) * (m * d) := by
      nlinarith [mul_le_mul_of_nonneg_left hdhalf (by positivity : 0 ≤ (δ / 2) * m)]
    exact le_trans h1 (le_trans h2 (le_trans h3 h4))
  have hfinal : |c / d - q| ≤ δ := by
    calc
      |c / d - q| = |(c / d - c / m) + (c / m - q)| := by congr 1; ring
      _ ≤ |c / d - c / m| + |c / m - q| := abs_add_le _ _
      _ ≤ δ := by rw [abs_of_nonneg hdiffnonneg]; linarith
  simpa [c, d] using hfinal

end Causalean.Mathlib.Probability.Birthday
