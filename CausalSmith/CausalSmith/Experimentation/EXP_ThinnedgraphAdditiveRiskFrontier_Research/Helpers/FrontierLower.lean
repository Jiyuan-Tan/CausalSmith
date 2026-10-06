module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.SuppliedBlockLower
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.TBlockTestingScale
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Explicit frontier lower bound

The supported two-prior reduction and integer block rounding assemble the
complete-record testing bound into the explicit minimax scale.
-/

public section

open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- At the prescribed testing amplitude, the opposite supported priors give a
squared-target minimax lower bound, including estimator randomization.  [For the stated data and conditions](hyp:n,B,d,q,hn,hB,hd,hdu,hfit,hq), [the stated conclusion holds](goal). -/
-- @node: block_testing_minimax_lower
lemma block_testing_minimax_lower (n B d : ℕ) (q : ℝ)
    (hn : 4 ≤ n) (hB : 1 ≤ B) (hd : 1 ≤ d) (hdu : d ≤ n - 1)
    (hfit : 2 * (B * d) ≤ n) (hq : q ∈ Set.Icc 0 1) :
    ENNReal.ofReal (((B * d : ℕ) * ((100 * Real.pi)⁻¹ * testingScale B d q) / n) ^ 2 / 4) ≤
      R (Fin n) d q := by
  let h := (100 * Real.pi)⁻¹ * testingScale B d q
  have hs := testingScale_pos_le_one B d q hB hd
  have hk : 0 < (100 * Real.pi)⁻¹ := inv_pos.mpr (by positivity)
  have hkquarter : (100 * Real.pi)⁻¹ ≤ (1 / 4 : ℝ) := by
    have hp := Real.pi_gt_three
    rw [← one_div]
    apply (div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 4)).2
    nlinarith
  have hh : h ∈ Set.Icc 0 (1 / 4) :=
    ⟨(mul_pos hk hs.1).le, (mul_le_of_le_one_right hk.le hs.2).trans hkquarter⟩
  let D := thinnedDesign (Fin n) q
  let := partitionLaw_probability B d
  let := blockBaselineLaw_probability B
  let : IsProbabilityMeasure (blockParamLaw B d) := by unfold blockParamLaw; infer_instance
  have htv := (block_testing_scale n B d q D hn hB hd hfit hq
    (thinnedDesign_assignment q hq) (thinnedDesign_audit q hq)
    (thinnedDesign_independent q hq)).1 h hh.1 le_rfl
  have hp := block_support n B d true h hB hd hfit hh
  have hm := block_support n B d false h hB hd hfit hh
  simp only [signOf, Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul] at hp hm
  have hm' : ∀ᵐ ξ ∂blockParamLaw B d, ScheduleClass (blockSchedule n B d false h ξ) d ∧
      tte (blockSchedule n B d false h ξ) = -((B * d : ℕ) * h / n) := by
    filter_upwards [hm] with ξ hξ
    exact ⟨hξ.1, by rw [hξ.2]; ring⟩
  have hl := full_record_two_prior_risk n d q hn hd hdu hq
    (blockParamLaw B d) (blockParamLaw B d)
    (blockSchedule n B d true h) (blockSchedule n B d false h)
    (block_record_measurable n B d true h) (block_record_measurable n B d false h)
    ((B * d : ℕ) * h / n) (by
      have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hm' : (0 : ℝ) < (B * d : ℕ) := by exact_mod_cast (show 0 < B * d by positivity)
      exact div_pos (mul_pos hm' (mul_pos hk hs.1)) hn') hp hm'
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) hl
  change _ ≤ ((B * d : ℕ) * h / n) ^ 2 / 2 * (1 -
    Causalean.Stat.tvDist (blockMixtureLawOf n B d D true h) (blockMixtureLawOf n B d D false h))
  nlinarith [sq_nonneg ((B * d : ℕ) * h / n)]

/-- Squaring the testing scale dominates the frontier scale whenever the
block sources fit inside the population.  [For the stated data and conditions](hyp:n,B,d,q,hn,hB,hd,hmn,hq), [the stated conclusion holds](goal). -/
-- @node: frontierScale_le_testingScale_sq
lemma frontierScale_le_testingScale_sq (n B d : ℕ) (q : ℝ)
    (hn : 4 ≤ n) (hB : 1 ≤ B) (hd : 1 ≤ d) (hmn : B * d ≤ n)
    (hq : q ∈ Set.Icc 0 1) :
    frontierScale n d q ≤ (testingScale B d q) ^ 2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hm' : (0 : ℝ) < (B * d : ℕ) := by exact_mod_cast (show 0 < B * d by positivity)
  have hd' : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  by_cases hqpos : 0 < q
  · have hp : 0 < retentionP d q := by
      unfold retentionP
      exact sub_pos.mpr (pow_lt_one₀ (sub_nonneg.mpr hq.2) (by linarith) (by omega))
    have hmp : 0 < (B * d : ℕ) * retentionP d q := mul_pos hm' hp
    have hnp : 0 < (n : ℝ) * retentionP d q := mul_pos hn' hp
    have hsqrt : 0 < Real.sqrt ((B * d : ℕ) * retentionP d q) := Real.sqrt_pos.2 hmp
    have hsq : ((d : ℝ) / Real.sqrt ((B * d : ℕ) * retentionP d q)) ^ 2 =
        (d : ℝ) ^ 2 / ((B * d : ℕ) * retentionP d q) := by
      rw [div_pow, Real.sq_sqrt hmp.le]
    have hv : (d : ℝ) ^ 2 / ((n : ℝ) * retentionP d q) ≤
        (d : ℝ) ^ 2 / ((B * d : ℕ) * retentionP d q) := by
      apply div_le_div_of_nonneg_left (sq_nonneg _) hmp
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hmn) hp.le
    rw [frontierScale, if_pos hqpos, testingScale, if_pos hp]
    change min 1 ((d : ℝ) ^ 2 / ((n : ℝ) * retentionP d q)) ≤ _
    by_cases ht : (d : ℝ) / Real.sqrt ((B * d : ℕ) * retentionP d q) ≤ 1
    · rw [min_eq_right ht, hsq]
      exact (min_le_right _ _).trans hv
    · rw [min_eq_left (le_of_not_ge ht), one_pow]
      exact min_le_left _ _
  · have hzero : q = 0 := by linarith [hq.1]
    subst q
    simp [frontierScale, testingScale, retentionP]

/-- Floor rounding supplies between a quarter and a half population of sources
in the small-degree regime.  [For the stated data and conditions](hyp:n,d,hd,hsmall), [the stated conclusion holds](goal). -/
-- @node: frontier_block_rounding
lemma frontier_block_rounding (n d : ℕ) (hd : 1 ≤ d) (hsmall : 4 * d < n) :
    1 ≤ n / (2 * d) ∧ 2 * (n / (2 * d) * d) ≤ n ∧
      (n : ℝ) / 4 ≤ (n / (2 * d) * d : ℕ) := by
  have hd0 : 0 < 2 * d := by omega
  have hmul := Nat.div_mul_le_self n (2 * d)
  have hmod := Nat.mod_lt n hd0
  have heq := Nat.mod_add_div n (2 * d)
  have hfit : 2 * (n / (2 * d) * d) ≤ n := by nlinarith
  have hl : n < 2 * (n / (2 * d) * d) + 2 * d := by nlinarith
  have hquarter : n ≤ 4 * (n / (2 * d) * d) := by nlinarith
  refine ⟨?_, hfit, ?_⟩
  · exact (Nat.le_div_iff_mul_le hd0).2 (by omega)
  · have hc : (n : ℝ) ≤ 4 * (n / (2 * d) * d : ℕ) := by exact_mod_cast hquarter
    linarith

/-- The explicit frontier minimax lower constant follows from supplied blocks
at large degree and rounded hidden-partition blocks at small degree.  [For the stated data and conditions](hyp:n,d,q,hn,hd,hdu,hq), [the stated conclusion holds](goal). -/
-- @node: frontier_minimax_lower
lemma frontier_minimax_lower (n d : ℕ) (q : ℝ)
    (hn : 4 ≤ n) (hd : 1 ≤ d) (hdu : d ≤ n - 1) (hq : q ∈ Set.Icc 0 1) :
    ENNReal.ofReal (frontierScale n d q / (2560000 * Real.pi ^ 2)) ≤ R (Fin n) d q := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hc : 0 < 160000 * Real.pi ^ 2 := by positivity
  have hc' : 0 < 2560000 * Real.pi ^ 2 := by positivity
  have hF : frontierScale n d q ≤ 1 := by
    unfold frontierScale
    split_ifs <;> first | exact min_le_left _ _ | exact le_rfl
  by_cases hlarge : (1 / 16 : ℝ) ≤ (d : ℝ) ^ 2 / n
  · have hl := supplied_block_record_lower n d q (thinnedDesign (Fin n) q)
      hn hd hdu hq (thinnedDesign_assignment q hq) (thinnedDesign_audit q hq)
      (thinnedDesign_independent q hq)
    apply le_trans (ENNReal.ofReal_le_ofReal ?_) hl
    have hdeg : (1 / 16 : ℝ) ≤ ((d : ℝ) + 1) ^ 2 / n := by
      apply hlarge.trans
      exact div_le_div_of_nonneg_right (by nlinarith) hn'.le
    have hmin : (1 / 16 : ℝ) ≤ min 1 (((d : ℝ) + 1) ^ 2 / n) := le_min (by norm_num) hdeg
    rw [← div_eq_inv_mul]
    apply (div_le_div_iff₀ hc' hc).2
    have heq : 2560000 * Real.pi ^ 2 = 16 * (160000 * Real.pi ^ 2) := by ring
    rw [heq]
    nlinarith [mul_le_mul_of_nonneg_right hmin hc.le]
  · have hsmall : 4 * d < n := by
      have hs : (d : ℝ) ^ 2 < (n : ℝ) / 16 := by
        have := (div_lt_iff₀ hn').mp (lt_of_not_ge hlarge)
        linarith
      have hreal : 4 * (d : ℝ) < n := by nlinarith
      exact_mod_cast hreal
    obtain ⟨hB, hfit, hquarter⟩ := frontier_block_rounding n d hd hsmall
    let B := n / (2 * d)
    let m : ℝ := (B * d : ℕ)
    let s := testingScale B d q
    let k := (100 * Real.pi)⁻¹
    have hs := testingScale_pos_le_one B d q hB hd
    have hk : 0 < k := by dsimp [k]; positivity
    have hspos : 0 < s := hs.1
    have hmpos : 0 < m := by dsimp [m]; exact_mod_cast (show 0 < B * d by positivity)
    have hmn : B * d ≤ n := by dsimp [B]; omega
    have hFs : frontierScale n d q ≤ s ^ 2 :=
      frontierScale_le_testingScale_sq n B d q hn hB hd hmn hq
    have hl := block_testing_minimax_lower n B d q hn hB hd hdu hfit hq
    apply le_trans (ENNReal.ofReal_le_ofReal ?_) hl
    change frontierScale n d q / (2560000 * Real.pi ^ 2) ≤ (m * (k * s) / n) ^ 2 / 4
    have hratio : (1 / 4 : ℝ) ≤ m / n := (le_div_iff₀ hn').2 (by linarith)
    have htarget : k * s / 4 ≤ m * (k * s) / n := by
      calc
        k * s / 4 = (1 / 4 : ℝ) * (k * s) := by ring
        _ ≤ (m / n) * (k * s) := mul_le_mul_of_nonneg_right hratio (mul_pos hk hs.1).le
        _ = m * (k * s) / n := by ring
    have hsquared : (k * s / 4) ^ 2 ≤ (m * (k * s) / n) ^ 2 :=
      (sq_le_sq₀ (by positivity) (by positivity)).2 htarget
    have hidentity : (k * s / 4) ^ 2 / 4 = s ^ 2 / (640000 * Real.pi ^ 2) := by
      dsimp [k]
      field_simp
      <;> ring
    calc
      frontierScale n d q / (2560000 * Real.pi ^ 2) ≤
          s ^ 2 / (2560000 * Real.pi ^ 2) := div_le_div_of_nonneg_right hFs hc'.le
      _ ≤ s ^ 2 / (640000 * Real.pi ^ 2) :=
        div_le_div_of_nonneg_left (sq_nonneg s) (by positivity) (by nlinarith [sq_pos_of_pos Real.pi_pos])
      _ = (k * s / 4) ^ 2 / 4 := hidentity.symm
      _ ≤ (m * (k * s) / n) ^ 2 / 4 := div_le_div_of_nonneg_right hsquared (by norm_num)

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
