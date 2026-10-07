module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ExternalLowerScoreLogQuantileExact

/-! Exact lower quantiles for the ordered three-atom inverse-score law. -/

public section

namespace CausalSmith.PartialID.UnlinkedPropensityAte

open MeasureTheory ProbabilityTheory Set
open Causalean.Stat

noncomputable section

private def orderedThreeAtomLaw (A B C a b c : ℝ) : Measure ℝ :=
  (ENNReal.ofReal a • Measure.dirac C +
    ENNReal.ofReal b • Measure.dirac B) +
    ENNReal.ofReal c • Measure.dirac A

private lemma orderedThreeAtomLaw_isProbabilityMeasure
    (A B C a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hsum : a + b + c = 1) :
    IsProbabilityMeasure (orderedThreeAtomLaw A B C a b c) := by
  rw [isProbabilityMeasure_iff]
  unfold orderedThreeAtomLaw
  simp only [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply,
    Set.mem_univ, Set.indicator_of_mem, Pi.one_apply, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add ha hb,
    ← ENNReal.ofReal_add (add_nonneg ha hb) hc, hsum]
  norm_num

private lemma orderedThreeAtomLaw_cdf_A
    (A B C a b c : ℝ) (hAB : A < B) (hBC : B < C)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hsum : a + b + c = 1) :
    cdf (orderedThreeAtomLaw A B C a b c) A = c := by
  letI := orderedThreeAtomLaw_isProbabilityMeasure A B C a b c ha hb hc hsum
  rw [cdf_eq_real]
  have hCA : ¬C ≤ A := not_le.mpr (lt_trans hAB hBC)
  have hBA : ¬B ≤ A := not_le.mpr hAB
  simp [orderedThreeAtomLaw, Measure.real, hCA, hBA, hc]

private lemma orderedThreeAtomLaw_cdf_B
    (A B C a b c : ℝ) (hAB : A < B) (hBC : B < C)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hsum : a + b + c = 1) :
    cdf (orderedThreeAtomLaw A B C a b c) B = c + b := by
  letI := orderedThreeAtomLaw_isProbabilityMeasure A B C a b c ha hb hc hsum
  rw [cdf_eq_real]
  have hCB : ¬C ≤ B := not_le.mpr hBC
  simp [orderedThreeAtomLaw, Measure.real, hCB, hAB.le, hb, hc]
  rw [← ENNReal.ofReal_add hb hc, ENNReal.toReal_ofReal (add_nonneg hb hc)]
  ring

private lemma orderedThreeAtomLaw_cdf_C
    (A B C a b c : ℝ) (hAB : A < B) (hBC : B < C)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hsum : a + b + c = 1) :
    cdf (orderedThreeAtomLaw A B C a b c) C = 1 := by
  letI := orderedThreeAtomLaw_isProbabilityMeasure A B C a b c ha hb hc hsum
  rw [cdf_eq_real]
  simp only [orderedThreeAtomLaw, Measure.real, Measure.add_apply,
    Measure.smul_apply, Measure.dirac_apply]
  rw [Set.indicator_of_mem (show C ∈ Iic C by simp),
    Set.indicator_of_mem (show B ∈ Iic C by exact hBC.le),
    Set.indicator_of_mem (show A ∈ Iic C by exact (lt_trans hAB hBC).le)]
  simp only [Pi.one_apply, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add ha hb,
    ← ENNReal.ofReal_add (add_nonneg ha hb) hc, hsum]
  norm_num

private lemma orderedThreeAtomLaw_cdf_lt_A
    (A B C a b c r : ℝ) (hAB : A < B) (hBC : B < C)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hsum : a + b + c = 1)
    (hr : r < A) :
    cdf (orderedThreeAtomLaw A B C a b c) r = 0 := by
  letI := orderedThreeAtomLaw_isProbabilityMeasure A B C a b c ha hb hc hsum
  rw [cdf_eq_real]
  have hCr : ¬C ≤ r := not_le.mpr (lt_trans hr (lt_trans hAB hBC))
  have hBr : ¬B ≤ r := not_le.mpr (lt_trans hr hAB)
  have hAr : ¬A ≤ r := not_le.mpr hr
  simp [orderedThreeAtomLaw, Measure.real, hCr, hBr, hAr]

private lemma orderedThreeAtomLaw_cdf_lt_B
    (A B C a b c r : ℝ) (hAB : A < B) (hBC : B < C)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hsum : a + b + c = 1)
    (hr : r < B) :
    cdf (orderedThreeAtomLaw A B C a b c) r ≤ c := by
  letI := orderedThreeAtomLaw_isProbabilityMeasure A B C a b c ha hb hc hsum
  rw [cdf_eq_real]
  have hCr : ¬C ≤ r := not_le.mpr (lt_trans hr hBC)
  have hBr : ¬B ≤ r := not_le.mpr hr
  by_cases hAr : A ≤ r
  · simp [orderedThreeAtomLaw, Measure.real, hCr, hBr, hAr, hc]
  · simp [orderedThreeAtomLaw, Measure.real, hCr, hBr, hAr, hc]

private lemma orderedThreeAtomLaw_cdf_lt_C
    (A B C a b c r : ℝ) (hAB : A < B) (hBC : B < C)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hsum : a + b + c = 1)
    (hr : r < C) :
    cdf (orderedThreeAtomLaw A B C a b c) r ≤ c + b := by
  letI := orderedThreeAtomLaw_isProbabilityMeasure A B C a b c ha hb hc hsum
  rw [cdf_eq_real]
  have hCr : ¬C ≤ r := not_le.mpr hr
  by_cases hBr : B ≤ r
  · have hAr : A ≤ r := le_trans hAB.le hBr
    simp [orderedThreeAtomLaw, Measure.real, hCr, hBr, hAr, hb, hc]
    rw [← ENNReal.ofReal_add hb hc, ENNReal.toReal_ofReal (add_nonneg hb hc)]
    linarith
  · by_cases hAr : A ≤ r
    · simp [orderedThreeAtomLaw, Measure.real, hCr, hBr, hAr, hb, hc]
    · simp [orderedThreeAtomLaw, Measure.real, hCr, hBr, hAr, hb, hc]
      positivity

private lemma orderedThreeAtomLaw_quantile
    (A B C a b c u : ℝ) (hAB : A < B) (hBC : B < C)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hsum : a + b + c = 1)
    (hu0 : 0 < u) (hu1 : u < 1) :
    quantile (orderedThreeAtomLaw A B C a b c) u =
      if u ≤ c then A else if u ≤ c + b then B else C := by
  letI := orderedThreeAtomLaw_isProbabilityMeasure A B C a b c ha hb hc hsum
  split_ifs with huc hucb
  · apply le_antisymm
    · apply quantile_le_of_le_cdf hu0
      rw [orderedThreeAtomLaw_cdf_A A B C a b c hAB hBC ha hb hc hsum]
      exact huc
    · by_contra hn
      have hlt : quantile (orderedThreeAtomLaw A B C a b c) u < A := lt_of_not_ge hn
      have hle := (quantile_le_iff hu0 hu1).mp
        (le_refl (quantile (orderedThreeAtomLaw A B C a b c) u))
      rw [orderedThreeAtomLaw_cdf_lt_A A B C a b c _ hAB hBC ha hb hc hsum hlt] at hle
      linarith
  · apply le_antisymm
    · apply quantile_le_of_le_cdf hu0
      rw [orderedThreeAtomLaw_cdf_B A B C a b c hAB hBC ha hb hc hsum]
      exact hucb
    · by_contra hn
      have hlt : quantile (orderedThreeAtomLaw A B C a b c) u < B := lt_of_not_ge hn
      have hle := (quantile_le_iff hu0 hu1).mp
        (le_refl (quantile (orderedThreeAtomLaw A B C a b c) u))
      have hcdf := orderedThreeAtomLaw_cdf_lt_B A B C a b c _
        hAB hBC ha hb hc hsum hlt
      exact huc (hle.trans hcdf)
  · apply le_antisymm
    · apply quantile_le_of_le_cdf hu0
      rw [orderedThreeAtomLaw_cdf_C A B C a b c hAB hBC ha hb hc hsum]
      exact hu1.le
    · by_contra hn
      have hlt : quantile (orderedThreeAtomLaw A B C a b c) u < C := lt_of_not_ge hn
      have hle := (quantile_le_iff hu0 hu1).mp
        (le_refl (quantile (orderedThreeAtomLaw A B C a b c) u))
      have hcdf := orderedThreeAtomLaw_cdf_lt_C A B C a b c _
        hAB hBC ha hb hc hsum hlt
      exact hucb (hle.trans hcdf)

/-- Given [the stated mathematical inputs and assumptions](hyp:x,y,z,w₁,w₂,w₃,u,hx,hxy,hyz,hw₁,hw₂,hw₃,hq,hu0,hu1), this result [establishes the stated mathematical conclusion](goal). -/
lemma threeScoreInverseLaw_quantile
    (x y z w₁ w₂ w₃ u : ℝ)
    (hx : 0 < x) (hxy : x < y) (hyz : y < z)
    (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hw₃ : 0 ≤ w₃)
    (hq : 0 < x * w₁ + y * w₂ + z * w₃)
    (hu0 : 0 < u) (hu1 : u < 1) :
    quantile (threeScoreInverseLaw x y z w₁ w₂ w₃) u =
      if u ≤ z * w₃ / (x * w₁ + y * w₂ + z * w₃) then 1 / z
      else if u ≤ z * w₃ / (x * w₁ + y * w₂ + z * w₃) +
          y * w₂ / (x * w₁ + y * w₂ + z * w₃) then 1 / y
      else 1 / x := by
  have hy : 0 < y := lt_trans hx hxy
  have hz : 0 < z := lt_trans hy hyz
  have hAB : 1 / z < 1 / y := one_div_lt_one_div_of_lt hy hyz
  have hBC : 1 / y < 1 / x := one_div_lt_one_div_of_lt hx hxy
  have ha : 0 ≤ x * w₁ / (x * w₁ + y * w₂ + z * w₃) :=
    div_nonneg (mul_nonneg hx.le hw₁) hq.le
  have hb : 0 ≤ y * w₂ / (x * w₁ + y * w₂ + z * w₃) :=
    div_nonneg (mul_nonneg hy.le hw₂) hq.le
  have hc : 0 ≤ z * w₃ / (x * w₁ + y * w₂ + z * w₃) :=
    div_nonneg (mul_nonneg hz.le hw₃) hq.le
  have hsum :
      x * w₁ / (x * w₁ + y * w₂ + z * w₃) +
        y * w₂ / (x * w₁ + y * w₂ + z * w₃) +
        z * w₃ / (x * w₁ + y * w₂ + z * w₃) = 1 := by
    field_simp
  unfold threeScoreInverseLaw
  exact orderedThreeAtomLaw_quantile (1 / z) (1 / y) (1 / x)
    (x * w₁ / (x * w₁ + y * w₂ + z * w₃))
    (y * w₂ / (x * w₁ + y * w₂ + z * w₃))
    (z * w₃ / (x * w₁ + y * w₂ + z * w₃)) u
    hAB hBC ha hb hc hsum hu0 hu1

end
end CausalSmith.PartialID.UnlinkedPropensityAte
