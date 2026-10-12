module
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.FrontierRiskAssembly

/-!
# Connected-length converse

Separate supported block and matching interval tests assemble the square-root frontier.
-/

public section
noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory
namespace CausalSmith.Experimentation.NoisygraphTtePrecision
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.whitespace false

/-- Given [the stated assumptions](hyp:hn,hd,hdu,hqr), [Rounded block target separation controls the square root of both block costs.](goal) -/
-- @node: degree_missing_length_strong
lemma degree_missing_length_strong (n d : ℕ) (hn : 512 ≤ n) (hd : 1 ≤ d)
    (hdu : d ≤ n-1) (q r : ℝ) (hqr : ChannelDomain q r) :
    ENNReal.ofReal ((1/(4*10^9*Real.pi^2)) *
      Real.sqrt (min 1 ((d : ℝ)^2/n + d/(n*q)))) ≤
      minimaxLength (noisyDesign (V := Fin n) q r) d := by
  let s := min d (n/8)
  let B := n/(2*s)
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hsd : s ≤ d := Nat.min_le_left _ _
  have hsmall : 4*s < n := by dsimp [s]; omega
  obtain ⟨hB, hfit, hquarter⟩ :=
    CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.frontier_block_rounding n s hs hsmall
  have hcap : s = d ∨ (n : ℝ)/16 ≤ s := by
    by_cases heq : s = d
    · exact Or.inl heq
    · right
      have hround : n ≤ 16*s := by dsimp [s] at *; omega
      have hr : (n : ℝ) ≤ 16*(s : ℝ) := by exact_mod_cast hround
      linarith
  let t := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.testingScale B s
    (channelSourceProb q r)
  let k := (100*Real.pi)⁻¹
  let a : ℝ := (B*s : ℕ)*(k*t)/n
  have hscale := noisy_block_scale_dominates n d B s hn hd hB hs (by change 2*(B*s) ≤ n at hfit; omega) hcap q r hqr
  have ht := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.testingScale_pos_le_one
    B s (channelSourceProb q r) hB hs
  have hk : 0 < k := by dsimp [k]; positivity
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hratio : (1/4 : ℝ) ≤ (B*s : ℕ)/(n : ℝ) :=
    (le_div_iff₀ hnpos).mpr (by change (n : ℝ)/4 ≤ (B*s : ℕ) at hquarter; nlinarith [hquarter])
  have htarget : k*t/4 ≤ a := by
    calc
      k*t/4 = (1/4 : ℝ)*(k*t) := by ring
      _ ≤ ((B*s : ℕ)/(n : ℝ))*(k*t) :=
        mul_le_mul_of_nonneg_right hratio (mul_pos hk ht.1).le
      _ = a := by dsimp [a]; ring
  have hnonneg : 0 ≤ min 1 ((d : ℝ)^2/n + d/(n*q)) :=
    le_min (by norm_num) (add_nonneg (by positivity)
      (div_nonneg (by positivity) (mul_nonneg (by positivity) (hqr.1.trans hqr.2.1))))
  have hsqrt : Real.sqrt (min 1 ((d : ℝ)^2/n + d/(n*q))) ≤ 2*t := by
    nlinarith [Real.sq_sqrt hnonneg, Real.sqrt_nonneg
      (min 1 ((d : ℝ)^2/n + d/(n*q))), ht.1]
  have hc : 2*(1/(4*10^9*Real.pi^2)) ≤ 3*k/20 := by
    dsimp [k]
    field_simp
    nlinarith [Real.pi_gt_three]
  have hl := (noisy_block_decisions_lower n d B s (by omega) hd hdu hB hs hsd hfit q r hqr).2
  apply (ENNReal.ofReal_le_ofReal ?_).trans hl
  change (1/(4*10^9*Real.pi^2)) *
    Real.sqrt (min 1 ((d : ℝ)^2/n + d/(n*q))) ≤ 3*a/5
  calc
    _ ≤ (1/(4*10^9*Real.pi^2)) * (2*t) :=
      mul_le_mul_of_nonneg_left hsqrt (by positivity)
    _ ≤ (3*k/20)*t := by nlinarith [mul_le_mul_of_nonneg_right hc ht.1.le]
    _ ≤ 3*a/5 := by linarith

/-- Given [the stated assumptions](hyp:hn,hd,hdu), [Zero acquisition retains a constant interval-testing separation.](goal) -/
-- @node: zero_acquisition_length_lower
lemma zero_acquisition_length_lower (n d : ℕ) (hn : 512 ≤ n) (hd : 1 ≤ d)
    (hdu : d ≤ n-1) :
    ENNReal.ofReal (3/(2000*Real.pi)) ≤
      minimaxLength (noisyDesign (V := Fin n) 0 0) d := by
  let s := min d (n/8)
  let B := n/(2*s)
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hsd : s ≤ d := Nat.min_le_left _ _
  have hsmall : 4*s < n := by dsimp [s]; omega
  obtain ⟨hB, hfit, hquarter⟩ :=
    CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.frontier_block_rounding n s hs hsmall
  have ht : CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.testingScale B s
      (channelSourceProb 0 0) = 1 := by
    simp [channelSourceProb, CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.testingScale,
      CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.retentionP]
  let k : ℝ := (100*Real.pi)⁻¹
  let a : ℝ := (B*s : ℕ)*k/n
  have hk : 0 < k := by dsimp [k]; positivity
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hratio : (1/4 : ℝ) ≤ (B*s : ℕ)/(n : ℝ) :=
    (le_div_iff₀ hnpos).mpr (by
      change (n : ℝ)/4 ≤ (B*s : ℕ) at hquarter
      linarith)
  have htarget : k/4 ≤ a := by
    calc
      k/4 = (1/4 : ℝ)*k := by ring
      _ ≤ ((B*s : ℕ)/(n : ℝ))*k := mul_le_mul_of_nonneg_right hratio hk.le
      _ = a := by dsimp [a]; ring
  have hl := (noisy_block_decisions_lower n d B s (by omega) hd hdu hB hs hsd hfit
    0 0 (by norm_num [ChannelDomain])).2
  simp only [ht, mul_one] at hl
  apply (ENNReal.ofReal_le_ofReal ?_).trans hl
  change 3/(2000*Real.pi) ≤ 3*a/5
  have hid : 3/(2000*Real.pi) = 3*(k/4)/5 := by
    dsimp [k]
    field_simp
    ring
  rw [hid]
  linarith

/-- Given [the stated assumptions](hyp:hx,hy,h), [A quadratic domination yields a convenient linear square-root comparison.](goal) -/
-- @node: sqrt_le_twice_of_le_three_mul
lemma sqrt_le_twice_of_le_three_mul (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x ≤ 3*y) : Real.sqrt x ≤ 2*Real.sqrt y := by
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy,
    Real.sqrt_nonneg x, Real.sqrt_nonneg y]

/-- Given [the stated assumptions](hyp:hn,hd,hdu,hqr), [The separate connected-interval tests give the complete precision frontier.](goal) -/
-- @node: frontier_length_lower
lemma frontier_length_lower (n d : ℕ) (hn : nZero ≤ n) (hd : 1 ≤ d)
    (hdu : d ≤ n-1) (q r : ℝ) (hqr : ChannelDomain q r) :
    ENNReal.ofReal (cLower*ell n d q r) ≤
      minimaxLength (noisyDesign (V := Fin n) q r) d := by
  have hn512 : 512 ≤ n := by simpa [nZero] using hn
  have hc : 0 < cLower := constants_valid.1
  have hck : 2*cLower ≤ 1/(4*10^9*Real.pi^2) := by
    unfold cLower
    field_simp
    nlinarith [sq_pos_of_pos Real.pi_pos]
  by_cases hq : 0 < q
  · let A : ℝ := (d : ℝ)^2/n + d/(n*q)
    let B : ℝ := r/q^2
    have hA : 0 ≤ A := by dsimp [A]; positivity
    have hB : 0 ≤ B := div_nonneg hqr.1 (sq_nonneg _)
    have hcapA : 0 ≤ min 1 A := le_min (by norm_num) hA
    have hcapB : 0 ≤ min 1 B := le_min (by norm_num) hB
    have hρ : rho n d q r = min 1 (A+B) := by rw [rho, if_pos hq]
    have hcap : 0 ≤ min 1 (A+B) := le_min (by norm_num) (add_nonneg hA hB)
    have hbase := degree_missing_length_strong n d hn512 hd hdu q r hqr
    by_cases hreg : q/2 ≤ (n/2 : ℕ)*r
    · have hr : 0 < r := by
        have hm : (0 : ℝ) ≤ (n/2 : ℕ) := by positivity
        by_contra hh
        have := mul_nonpos_of_nonneg_of_nonpos hm (le_of_not_gt hh)
        linarith
      have hfalse := (matching_false_positive_lower n d hn512 hd hdu q r hqr hr hreg).2
      have hsum := capped_sum_le_twice_max A B hA hB
      by_cases hab : min 1 A ≤ min 1 B
      · rw [max_eq_right hab] at hsum
        have hs := sqrt_le_twice_of_le_three_mul _ _ hcap hcapB
          (by linarith)
        apply (ENNReal.ofReal_le_ofReal ?_).trans hfalse
        change cLower * Real.sqrt (rho n d q r) ≤
          (1/(4*10^9*Real.pi^2))*Real.sqrt (min 1 B)
        rw [hρ]
        calc
          _ ≤ cLower*(2*Real.sqrt (min 1 B)) := mul_le_mul_of_nonneg_left hs hc.le
          _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hck (Real.sqrt_nonneg (min 1 B))]
      · rw [max_eq_left (le_of_not_ge hab)] at hsum
        have hs := sqrt_le_twice_of_le_three_mul _ _ hcap hcapA (by linarith)
        apply (ENNReal.ofReal_le_ofReal ?_).trans hbase
        change cLower * Real.sqrt (rho n d q r) ≤
          (1/(4*10^9*Real.pi^2))*Real.sqrt (min 1 A)
        rw [hρ]
        calc
          _ ≤ cLower*(2*Real.sqrt (min 1 A)) := mul_le_mul_of_nonneg_left hs hc.le
          _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hck (Real.sqrt_nonneg (min 1 A))]
    · have hsmall := false_cost_le_missing_small_regime n d hn512 hd q r hq (lt_of_not_ge hreg)
      have hBA : B ≤ (3/2 : ℝ)*A := by
        dsimp [A, B]
        nlinarith [div_nonneg (sq_nonneg (d : ℝ)) (by positivity : (0 : ℝ) ≤ n)]
      have hsum := capped_sum_le_five_halves A B hA hBA
      have hs := sqrt_le_twice_of_le_three_mul _ _ hcap hcapA (by linarith)
      apply (ENNReal.ofReal_le_ofReal ?_).trans hbase
      change cLower * Real.sqrt (rho n d q r) ≤
        (1/(4*10^9*Real.pi^2))*Real.sqrt (min 1 A)
      rw [hρ]
      calc
        _ ≤ cLower*(2*Real.sqrt (min 1 A)) := mul_le_mul_of_nonneg_left hs hc.le
        _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hck (Real.sqrt_nonneg (min 1 A))]
  · have hq0 : q = 0 := le_antisymm (le_of_not_gt hq) (hqr.1.trans hqr.2.1)
    have hr0 : r = 0 := by linarith [hqr.1, hqr.2.1]
    subst q
    subst r
    have hl := zero_acquisition_length_lower n d hn512 hd hdu
    apply (ENNReal.ofReal_le_ofReal ?_).trans hl
    simp only [ell, rho, lt_self_iff_false, if_false, Real.sqrt_one, mul_one]
    unfold cLower
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [Real.pi_gt_three]

end CausalSmith.Experimentation.NoisygraphTtePrecision
