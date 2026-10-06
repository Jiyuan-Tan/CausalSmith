module
public import Causalean.Mathlib.Probability.Birthday.LimitAverage
public import Causalean.Mathlib.Probability.Birthday.LimitBand

/-!
# The binomial birthday collision limit

The finite birthday sandwich gives uniform control on a relative mean band.
Together with concentration, this yields the averaged collision limit.
-/

public section

namespace Causalean.Mathlib.Probability.Birthday

open Filter

/-- If [valid success probabilities](hyp:heta) have a
[diverging expected count](hyp:hmean), [positive alphabets](hyp:hm), and
[positive finite pair scale](hyp:hscale,hq), then the [birthday kernel](goal)
approaches its Poisson collision value uniformly on a sufficiently narrow
relative band around the binomial mean. -/
theorem repeatKernel_uniform_on_relative_band
    (Tseq mseq : ℕ → ℕ) (etaseq : ℕ → ℝ) {q : ℝ}
    (heta : ∀ j, etaseq j ∈ Set.Icc (0 : ℝ) 1)
    (hmean : Tendsto (fun j => mean (Tseq j) (etaseq j)) atTop atTop)
    (hm : ∀ j, 0 < mseq j)
    (hscale : Tendsto
      (fun j => pairScale (Tseq j) (etaseq j) / (mseq j : ℝ)) atTop (nhds q))
    (hq : 0 < q) :
    ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧
      ∀ᶠ j in atTop, ∀ r : ℕ, r ≤ Tseq j →
        |(r : ℝ) - mean (Tseq j) (etaseq j)| <
          ε * mean (Tseq j) (etaseq j) →
        |repeatKernel (mseq j) r - (1 - Real.exp (-q))| ≤ δ := by
  -- Given δ, use continuity of x ↦ exp (-x) at q to choose a smaller
  -- exponent tolerance. Intersect the two uniform scale bands from
  -- LimitBand and shrink their widths with `min`; include the eventual
  -- `relative_band_below_alphabet` condition. The finite sandwich
  -- `exp_le_noRepeat` / `noRepeat_le_exp` then bounds noRepeat between
  -- exponentials whose arguments are both close to q. Subtract from 1.
  intro δ hδ
  have hcont : ContinuousAt (fun x : ℝ => Real.exp (-x)) q := by
    fun_prop
  obtain ⟨ρ, hρ, hρexp⟩ := (Metric.continuousAt_iff.mp hcont) δ hδ
  obtain ⟨εa, hεa, ha⟩ :=
    pairCount_div_alphabet_uniform_on_relative_band Tseq mseq etaseq
      heta hmean hm hscale hq (ρ / 2) (by positivity)
  obtain ⟨εb, hεb, hb⟩ :=
    pairCount_div_remaining_uniform_on_relative_band Tseq mseq etaseq
      heta hmean hm hscale hq (ρ / 2) (by positivity)
  let ε : ℝ := min εa εb
  have hε : 0 < ε := lt_min hεa hεb
  have hbelow := relative_band_below_alphabet Tseq mseq etaseq
    heta hmean hm hscale hq hε
  refine ⟨ε, hε, ?_⟩
  filter_upwards [ha, hb, hbelow, hmean.eventually_gt_atTop 0] with
    j haj hbj hjbelow hμ r hrT hrband
  have hbandA : |(r : ℝ) - mean (Tseq j) (etaseq j)| <
      εa * mean (Tseq j) (etaseq j) :=
    lt_of_lt_of_le hrband
      (mul_le_mul_of_nonneg_right (min_le_left _ _) (le_of_lt hμ))
  have hbandB : |(r : ℝ) - mean (Tseq j) (etaseq j)| <
      εb * mean (Tseq j) (etaseq j) :=
    lt_of_lt_of_le hrband
      (mul_le_mul_of_nonneg_right (min_le_right _ _) (le_of_lt hμ))
  have hrm : r ≤ mseq j := hjbelow r hrband
  have hA := haj r hbandA
  have hB := hbj r hrm hbandB
  have hAexp : |Real.exp (-((r.choose 2 : ℝ) / (mseq j : ℝ))) -
      Real.exp (-q)| ≤ δ := by
    have ht := hρexp (x := (r.choose 2 : ℝ) / (mseq j : ℝ))
      (by simpa [Real.dist_eq] using (lt_of_le_of_lt hA (by linarith : ρ / 2 < ρ)))
    exact le_of_lt (by simpa [Real.dist_eq] using ht)
  have hBexp : |Real.exp (-((r.choose 2 : ℝ) /
      (mseq j + 1 - r : ℕ))) - Real.exp (-q)| ≤ δ := by
    have ht := hρexp (x := (r.choose 2 : ℝ) /
      (mseq j + 1 - r : ℕ))
      (by simpa [Real.dist_eq] using (lt_of_le_of_lt hB (by linarith : ρ / 2 < ρ)))
    exact le_of_lt (by simpa [Real.dist_eq] using ht)
  have hlo := exp_le_noRepeat (mseq j) r (hm j) hrm
  have hhi := noRepeat_le_exp (mseq j) r (hm j)
  have hlo' : Real.exp (-((r.choose 2 : ℝ) /
      (mseq j + 1 - r : ℕ))) ≤ noRepeat (mseq j) r := by
    convert hlo using 1 <;> ring
  have hhi' : noRepeat (mseq j) r ≤
      Real.exp (-((r.choose 2 : ℝ) / (mseq j : ℝ))) := by
    convert hhi using 1 <;> ring
  change |(1 - noRepeat (mseq j) r) - (1 - Real.exp (-q))| ≤ δ
  rw [show (1 - noRepeat (mseq j) r) - (1 - Real.exp (-q)) =
      Real.exp (-q) - noRepeat (mseq j) r by ring]
  apply abs_le.mpr
  constructor
  · have := (abs_le.mp hAexp).2
    linarith [hhi']
  · have := (abs_le.mp hBexp).1
    linarith [hlo']

/-- For [valid success probabilities](hyp:heta), a
[diverging expected draw count](hyp:hmean), [positive alphabets](hyp:hm), and
[pair scale per label tending to a positive value](hyp:hscale,hq), the
[binomially averaged repeat probability](goal) tends to one minus the
corresponding Poisson no-collision probability. -/
theorem repeat_tendsto
    (Tseq mseq : ℕ → ℕ) (etaseq : ℕ → ℝ) {q : ℝ}
    (heta : ∀ j, etaseq j ∈ Set.Icc (0 : ℝ) 1)
    (hmean : Tendsto (fun j => mean (Tseq j) (etaseq j)) atTop atTop)
    (hm : ∀ j, 0 < mseq j)
    (hscale : Tendsto
      (fun j => pairScale (Tseq j) (etaseq j) / (mseq j : ℝ)) atTop (nhds q))
    (hq : 0 < q) :
    Tendsto (fun j => birthdayRepeat (Tseq j) (mseq j) (etaseq j))
      atTop (nhds (1 - Real.exp (-q))) := by
  -- Apply `binomialAverage_tendsto_of_relative_band` to
  -- `fun j r => repeatKernel (mseq j) r`. The finite kernel bound is
  -- `repeatKernel_mem_Icc`; rewrite the average by `birthdayRepeat`.
  have hc : 1 - Real.exp (-q) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · have := (Real.exp_le_one_iff).2 (by linarith : -q ≤ 0)
      linarith
    · have := Real.exp_nonneg (-q)
      linarith
  have hbound : ∀ j r, r ≤ Tseq j →
      repeatKernel (mseq j) r ∈ Set.Icc (0 : ℝ) 1 := by
    intro j r _
    exact repeatKernel_mem_Icc (mseq j) r (hm j)
  have h := binomialAverage_tendsto_of_relative_band Tseq etaseq
    (fun j r => repeatKernel (mseq j) r) (1 - Real.exp (-q))
    heta hmean hc hbound
    (repeatKernel_uniform_on_relative_band Tseq mseq etaseq
      heta hmean hm hscale hq)
  simpa only [birthdayRepeat] using h

end Causalean.Mathlib.Probability.Birthday
