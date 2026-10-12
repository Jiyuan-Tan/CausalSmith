module
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.FrontierLower

/-!
# Assembly of the finite risk converse

Rounded block tests cover the zero-acquisition branch. For positive acquisition,
combine the degree/missing-edge and matching tests in the two precision regimes.
-/

public section
noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory
namespace CausalSmith.Experimentation.NoisygraphTtePrecision
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.whitespace false

/-- Given [the stated assumptions](hyp:hn,hd,hdu), [Zero acquisition leaves the rounded supported block targets separated at a constant scale.](goal) -/
-- @node: zero_acquisition_risk_lower
lemma zero_acquisition_risk_lower (n d : ℕ) (hn : 512 ≤ n) (hd : 1 ≤ d)
    (hdu : d ≤ n-1) :
    ENNReal.ofReal (1/(640000*Real.pi^2)) ≤
      minimaxRisk (noisyDesign (V := Fin n) 0 0) d := by
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
  have hsq : (k/4)^2 ≤ a^2 :=
    (sq_le_sq₀ (by positivity) ((by positivity : 0 ≤ k/4).trans htarget)).mpr htarget
  have hid : (k/4)^2/4 = 1/(640000*Real.pi^2) := by
    dsimp [k]
    field_simp
    ring
  have hl := (noisy_block_decisions_lower n d B s (by omega) hd hdu hB hs hsd hfit
    0 0 (by norm_num [ChannelDomain])).1
  simp only [ht, mul_one] at hl
  apply (ENNReal.ofReal_le_ofReal ?_).trans hl
  change 1/(640000*Real.pi^2) ≤ a^2/4
  rw [← hid]
  exact div_le_div_of_nonneg_right hsq (by norm_num)

/-- Given [the stated assumptions](hyp:hA,hB), [Capping the sum of two nonnegative costs is bounded by twice the larger capped cost.](goal) -/
-- @node: capped_sum_le_twice_max
lemma capped_sum_le_twice_max (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    min 1 (A+B) ≤ 2 * max (min 1 A) (min 1 B) := by
  by_cases hA1 : 1 ≤ A
  · rw [min_eq_left hA1]
    linarith [le_max_left (1 : ℝ) (min 1 B), min_le_left (1 : ℝ) (A+B)]
  by_cases hB1 : 1 ≤ B
  · rw [min_eq_left hB1]
    linarith [le_max_right (min 1 A) (1 : ℝ), min_le_left (1 : ℝ) (A+B)]
  rw [min_eq_right (le_of_not_ge hA1), min_eq_right (le_of_not_ge hB1)]
  linarith [le_max_left A B, le_max_right A B, min_le_right (1 : ℝ) (A+B)]

/-- Given [the stated assumptions](hyp:hn,hd,hq,hr), [Below the matching regime, the false-edge cost is absorbed by the missing-edge cost.](goal) -/
-- @node: false_cost_le_missing_small_regime
lemma false_cost_le_missing_small_regime (n d : ℕ) (hn : 512 ≤ n) (hd : 1 ≤ d)
    (q r : ℝ) (hq : 0 < q) (hr : (n/2 : ℕ)*r < q/2) :
    r/q^2 ≤ (3/2 : ℝ)*(d/(n*q)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hmpos : (0 : ℝ) < (n/2 : ℕ) := by exact_mod_cast (show 0 < n/2 by omega)
  have hround : (n : ℝ) ≤ 3*(n/2 : ℕ) := by
    exact_mod_cast (show n ≤ 3*(n/2) by omega)
  have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast hd
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (sq_pos_of_pos hq) (mul_pos hnpos hq)).mpr
  have h1 : r ≤ q/(2*(n/2 : ℕ)) := by
    apply (le_div_iff₀ (by positivity)).mpr
    linarith
  have h2 : r*n ≤ (3/2 : ℝ)*q := by
    have hmul := mul_le_mul_of_nonneg_right h1 hnpos.le
    have hratio : (n : ℝ)/(2*(n/2 : ℕ)) ≤ 3/2 := by
      apply (div_le_iff₀ (by positivity)).mpr
      linarith
    have hmul2 := mul_le_mul_of_nonneg_left hratio hq.le
    nlinarith [hmul, hmul2]
  nlinarith [mul_le_mul_of_nonneg_right h2 hq.le,
    mul_le_mul_of_nonneg_right hdreal (sq_nonneg q)]

/-- Given [the stated assumptions](hyp:hA,hB), [A dominated nonnegative second cost gives the capped five-halves comparison.](goal) -/
-- @node: capped_sum_le_five_halves
lemma capped_sum_le_five_halves (A B : ℝ) (hA : 0 ≤ A)
    (hB : B ≤ (3/2 : ℝ)*A) : min 1 (A+B) ≤ (5/2 : ℝ)*min 1 A := by
  by_cases hA1 : 1 ≤ A
  · rw [min_eq_left hA1]
    linarith [min_le_left (1 : ℝ) (A+B)]
  · rw [min_eq_right (le_of_not_ge hA1)]
    linarith [min_le_right (1 : ℝ) (A+B)]

/-- Given [the stated assumptions](hyp:hn,hd,hdu,hqr), [Supported full-record testing bounds assemble the published finite MSE frontier.](goal) -/
-- @node: frontier_risk_lower
lemma frontier_risk_lower (n d : ℕ) (hn : nZero ≤ n) (hd : 1 ≤ d)
    (hdu : d ≤ n-1) (q r : ℝ) (hqr : ChannelDomain q r) :
    ENNReal.ofReal (cLower*rho n d q r) ≤
      minimaxRisk (noisyDesign (V := Fin n) q r) d := by
  have hn512 : 512 ≤ n := by simpa [nZero] using hn
  have hc : 0 < cLower := constants_valid.1
  have hck : 2*cLower ≤ 1/(4*10^9*Real.pi^2) := by
    unfold cLower
    field_simp
    nlinarith [sq_pos_of_pos Real.pi_pos]
  have hca : (5/2 : ℝ)*cLower ≤ 1/(1280000*Real.pi^2) := by
    unfold cLower
    field_simp
    nlinarith [sq_pos_of_pos Real.pi_pos]
  by_cases hq : 0 < q
  · let A : ℝ := (d : ℝ)^2/n + d/(n*q)
    let B : ℝ := r/q^2
    have hA : 0 ≤ A := by dsimp [A]; positivity
    have hB : 0 ≤ B := div_nonneg hqr.1 (sq_nonneg _)
    have hcapA : 0 ≤ min 1 A := le_min (by norm_num) hA
    have hρ : rho n d q r = min 1 (A+B) := by rw [rho, if_pos hq]
    have hbase := degree_missing_risk_strong n d hn512 hd hdu q r hqr
    by_cases hreg : q/2 ≤ (n/2 : ℕ)*r
    · have hr : 0 < r := by
        have hm : (0 : ℝ) ≤ (n/2 : ℕ) := by positivity
        by_contra hh
        have := mul_nonpos_of_nonneg_of_nonpos hm (le_of_not_gt hh)
        linarith
      have hfalse := (matching_false_positive_lower n d hn512 hd hdu q r hqr hr hreg).1
      have hsum := capped_sum_le_twice_max A B hA hB
      by_cases hab : min 1 A ≤ min 1 B
      · apply (ENNReal.ofReal_le_ofReal ?_).trans hfalse
        rw [hρ]
        rw [max_eq_right hab] at hsum
        have hm := mul_le_mul_of_nonneg_left hsum hc.le
        have hk := mul_le_mul_of_nonneg_right hck (le_min (by norm_num : (0 : ℝ) ≤ 1) hB)
        dsimp [B] at *
        nlinarith
      · apply (ENNReal.ofReal_le_ofReal ?_).trans hbase
        rw [hρ]
        rw [max_eq_left (le_of_not_ge hab)] at hsum
        have hm := mul_le_mul_of_nonneg_left hsum hc.le
        have hk := mul_le_mul_of_nonneg_right hca hcapA
        change cLower * min 1 (A+B) ≤ min 1 A / (1280000*Real.pi^2)
        calc
          _ ≤ cLower * (2 * min 1 A) := hm
          _ ≤ (5/2 : ℝ)*cLower*min 1 A := by nlinarith [mul_nonneg hc.le hcapA]
          _ ≤ (1/(1280000*Real.pi^2))*min 1 A := hk
          _ = _ := by ring
    · have hsmall := false_cost_le_missing_small_regime n d hn512 hd q r hq (lt_of_not_ge hreg)
      have hBA : B ≤ (3/2 : ℝ)*A := by
        dsimp [A, B]
        nlinarith [div_nonneg (sq_nonneg (d : ℝ)) (by positivity : (0 : ℝ) ≤ n)]
      have hsum := capped_sum_le_five_halves A B hA hBA
      apply (ENNReal.ofReal_le_ofReal ?_).trans hbase
      rw [hρ]
      have hm := mul_le_mul_of_nonneg_left hsum hc.le
      have hk := mul_le_mul_of_nonneg_right hca hcapA
      change cLower * min 1 (A+B) ≤ min 1 A / (1280000*Real.pi^2)
      calc
        _ ≤ cLower * ((5/2 : ℝ)*min 1 A) := hm
        _ = (5/2 : ℝ)*cLower*min 1 A := by ring
        _ ≤ (1/(1280000*Real.pi^2))*min 1 A := hk
        _ = _ := by ring
  · have hq0 : q = 0 := le_antisymm (le_of_not_gt hq) (hqr.1.trans hqr.2.1)
    have hr0 : r = 0 := by linarith [hqr.1, hqr.2.1]
    subst q
    subst r
    have hl := zero_acquisition_risk_lower n d hn512 hd hdu
    apply (ENNReal.ofReal_le_ofReal ?_).trans hl
    simp only [rho, lt_self_iff_false, if_false, mul_one]
    unfold cLower
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [sq_pos_of_pos Real.pi_pos]

end CausalSmith.Experimentation.NoisygraphTtePrecision
