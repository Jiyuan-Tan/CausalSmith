module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.ChebyshevRiskBounds
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.StreamBiasAlgebra

/-!
# Small-cell pilot bias rate bounds

The arrival-floor comparison converts the Chebyshev quotient rate bound into
a missing-mass-weighted cell estimate for equation (13).
-/

public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open scoped BigOperators

-- @node: upper_small_cell_missing_qPoly_le
/-- In a light-rate cell, missing mass times the Chebyshev remainder is
controlled by the arrival floor and the quotient rate bound. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `P`](hyp:P), [the specified input `h`](hyp:h), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the specified input `hzB`](hyp:hzB), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
lemma upper_small_cell_missing_qPoly_le {n d : ℕ} {q : ℝ}
    (hn : 0 < n) (P : FullLaw d) (h : LawClass d q P)
    (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (x : Fin d) (a s : Bool)
    (hzB : streamZ n P x a s ≤ polyThreshold n) :
    missingCellMass P x a s *
      (qPoly n).eval (streamZ n P x a s) ≤
      (2 * delta q / ((n : ℝ) / 8)) *
        (polyThreshold n / (polyDegree n : ℝ) ^ 2) := by
  have hnR : 0 < (n : ℝ) / 8 := by exact div_pos (by exact_mod_cast hn) (by norm_num)
  have hnOne : 1 ≤ n := hn
  have hδ : 0 ≤ delta q := by
    unfold delta
    linarith [hq.2]
  have hB : 0 < polyThreshold n := by
    have he : 1 < Real.exp (1 : ℝ) + (n : ℝ) := by
      have hexp : 1 < Real.exp (1 : ℝ) := Real.one_lt_exp_iff.mpr (by norm_num)
      linarith [hexp, (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
    have hell : 0 < ell n := Real.log_pos (by simpa [ell] using he)
    unfold polyThreshold
    positivity
  have hk : 0 < (polyDegree n : ℝ) := by
    exact_mod_cast (show 0 < polyDegree n by unfold polyDegree; omega)
  have hb := missingCellMass_bounds P h hq x a s
  by_cases hz : streamZ n P x a s = 0
  · have ha : arrivedCellMass P x a s = 0 := by
      unfold streamZ at hz
      exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hnR)
    have hw : missingCellMass P x a s = 0 := by
      have := hb.2.2
      rw [ha, mul_zero] at this
      exact le_antisymm this hb.1
    rw [hw, zero_mul]
    exact mul_nonneg (div_nonneg (mul_nonneg (by norm_num) hδ) hnR.le)
      (div_nonneg hB.le (sq_nonneg _))
  · have hzpos : 0 < streamZ n P x a s := by
      have hznonneg : 0 ≤ streamZ n P x a s := by
        unfold streamZ
        exact mul_nonneg hnR.le (arrivedCellMass_nonneg P x a s)
      exact lt_of_le_of_ne hznonneg (Ne.symm hz)
    have hq0 := upper_qPoly_nonneg_on_positive hnOne hzpos hzB
    have hzq := upper_z_mul_qPoly_le hnOne hzpos hzB
    calc
      missingCellMass P x a s *
          (qPoly n).eval (streamZ n P x a s) ≤
          (2 * delta q * arrivedCellMass P x a s) *
            (qPoly n).eval (streamZ n P x a s) :=
        mul_le_mul_of_nonneg_right hb.2.2 hq0
      _ = (2 * delta q / ((n : ℝ) / 8)) *
          (streamZ n P x a s *
            (qPoly n).eval (streamZ n P x a s)) := by
        unfold streamZ
        field_simp [ne_of_gt hnR]
      _ ≤ (2 * delta q / ((n : ℝ) / 8)) *
          (polyThreshold n / (polyDegree n : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hzq
          (div_nonneg (mul_nonneg (by norm_num) hδ) hnR.le)

-- @node: upper_polyDegree_log_lower
/-- In the nonfallback regime the polynomial degree is at least one
hundred twenty-eighth of the logarithmic sample scale. Given [the specified input `n`](hyp:n), [the specified input `hL`](hyp:hL), [the stated mathematical conclusion holds](goal). -/
lemma upper_polyDegree_log_lower {n : ℕ} (hL : 128 ≤ ell n) :
    ell n / 128 ≤ (polyDegree n : ℝ) := by
  have hf := Nat.lt_floor_add_one (ell n / 64)
  have hm : (Nat.floor (ell n / 64) : ℝ) ≤ (polyDegree n : ℝ) := by
    exact_mod_cast (show Nat.floor (ell n / 64) ≤ polyDegree n from
      le_max_right _ _)
  linarith

-- @node: upper_polyThreshold_degree_rate
/-- The threshold-to-squared-degree ratio has the inverse logarithmic rate
used in the light-cell bias calculation. Given [the specified input `n`](hyp:n), [the specified input `hL`](hyp:hL), [the stated mathematical conclusion holds](goal). -/
lemma upper_polyThreshold_degree_rate {n : ℕ} (hL : 128 ≤ ell n) :
    polyThreshold n / (polyDegree n : ℝ) ^ 2 ≤ 4194304 / ell n := by
  have hLpos : 0 < ell n := by linarith
  have hk := upper_polyDegree_log_lower hL
  have hkpos : 0 < (polyDegree n : ℝ) := by linarith
  have hsq : (ell n / 128) ^ 2 ≤ (polyDegree n : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hk 2
  rw [div_le_div_iff₀ (sq_pos_of_pos hkpos) hLpos]
  unfold polyThreshold
  nlinarith

-- @node: upper_small_cell_missing_abs_qPoly_le
/-- The light-cell remainder bound also holds in absolute value, including
null arrived cells where the missing mass vanishes. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `P`](hyp:P), [the specified input `h`](hyp:h), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the specified input `hzB`](hyp:hzB), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
lemma upper_small_cell_missing_abs_qPoly_le {n d : ℕ} {q : ℝ}
    (hn : 0 < n) (P : FullLaw d) (h : LawClass d q P)
    (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (x : Fin d) (a s : Bool)
    (hzB : streamZ n P x a s ≤ polyThreshold n) :
    missingCellMass P x a s * |(qPoly n).eval (streamZ n P x a s)| ≤
      (2 * delta q / ((n : ℝ) / 8)) *
        (polyThreshold n / (polyDegree n : ℝ) ^ 2) := by
  by_cases hz : streamZ n P x a s = 0
  · have hm : 0 < (n : ℝ) / 8 := by positivity
    have ha : arrivedCellMass P x a s = 0 := by
      unfold streamZ at hz
      exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hm)
    have hb := missingCellMass_bounds P h hq x a s
    have hw : missingCellMass P x a s = 0 := by
      have hb' := hb.2.2
      rw [ha, mul_zero] at hb'
      exact le_antisymm hb' hb.1
    simpa only [hw, zero_mul] using
      upper_small_cell_missing_qPoly_le hn P h hq x a s hzB
  · have hzpos : 0 < streamZ n P x a s := by
      have hnonneg : 0 ≤ streamZ n P x a s := by
        unfold streamZ
        exact mul_nonneg (by positivity) (arrivedCellMass_nonneg P x a s)
      exact lt_of_le_of_ne hnonneg (Ne.symm hz)
    rw [abs_of_nonneg (upper_qPoly_nonneg_on_positive hn hzpos hzB)]
    exact upper_small_cell_missing_qPoly_le hn P h hq x a s hzB

-- @node: upper_small_cell_pilot_bias_sum_rate
/-- The light-rate cells' pilot-weighted Chebyshev remainders sum to a
universal multiple of delta times alphabet size divided by n log(e+n). Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hL`](hyp:hL), [the specified input `P`](hyp:P), [the specified input `h`](hyp:h), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
lemma upper_small_cell_pilot_bias_sum_rate {n d : ℕ} {q : ℝ}
    (hn : 0 < n) (hL : 128 ≤ ell n)
    (P : FullLaw d) (h : LawClass d q P)
    (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) :
    (∑ x : Fin d, ∑ a : Bool, ∑ s : Bool,
      if streamZ n P x a s ≤ polyThreshold n then
        missingCellMass P x a s * streamPilotLightProb n P x a s *
          |(qPoly n).eval (streamZ n P x a s)| else 0) ≤
      268435456 * (delta q * (d : ℝ) / ((n : ℝ) * ell n)) := by
  classical
  have hm : 0 < (n : ℝ) / 8 := by positivity
  have hδ : 0 ≤ delta q := by unfold delta; linarith [hq.2]
  have hLpos : 0 < ell n := by linarith
  let b : ℝ := (2 * delta q / ((n : ℝ) / 8)) * (4194304 / ell n)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hcell : ∀ x : Fin d, ∀ a s : Bool,
      (if streamZ n P x a s ≤ polyThreshold n then
        missingCellMass P x a s * streamPilotLightProb n P x a s *
          |(qPoly n).eval (streamZ n P x a s)| else 0) ≤ b := by
    intro x a s
    split_ifs with hzB
    · have hw := (missingCellMass_bounds P h hq x a s).1
      have hp := (upper_streamPilotLightProb_bounds (n := n) P x a s).2
      have hpilot := mul_le_mul_of_nonneg_left hp hw
      have hsmall := upper_small_cell_missing_abs_qPoly_le hn P h hq x a s hzB
      calc
        missingCellMass P x a s * streamPilotLightProb n P x a s *
            |(qPoly n).eval (streamZ n P x a s)| ≤
            missingCellMass P x a s * |(qPoly n).eval (streamZ n P x a s)| := by
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_right hpilot (abs_nonneg _)
        _ ≤ (2 * delta q / ((n : ℝ) / 8)) *
            (polyThreshold n / (polyDegree n : ℝ) ^ 2) := hsmall
        _ ≤ b := mul_le_mul_of_nonneg_left (upper_polyThreshold_degree_rate hL)
          (by positivity)
    · exact hb
  calc
    _ ≤ ∑ x : Fin d, ∑ a : Bool, ∑ s : Bool, b := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro s hs
      exact hcell x a s
    _ = 268435456 * (delta q * (d : ℝ) / ((n : ℝ) * ell n)) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool,
        Fintype.card_fin, nsmul_eq_mul]
      dsimp [b]
      ring

end CausalSmith.Stat.MarNearcompleteFrontier

