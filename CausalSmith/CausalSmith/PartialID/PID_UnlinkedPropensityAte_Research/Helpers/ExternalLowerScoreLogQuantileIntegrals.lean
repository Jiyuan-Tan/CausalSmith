module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ExternalLowerScoreLogInverseQuantile

/-! Exact integrals of the Bernoulli and inverse-score quantile steps. -/

public section

namespace CausalSmith.PartialID.UnlinkedPropensityAte

open MeasureTheory ProbabilityTheory Set
open Causalean.Stat

noncomputable section

private lemma upper_step_integral
    (r s B C : ℝ) (hr0 : 0 ≤ r) (hrs : r ≤ s) (hs1 : s ≤ 1) :
    (∫ u in Ioo (0 : ℝ) 1,
      (if u ≤ r then 0 else if u ≤ s then B else C)) =
      (s - r) * B + (1 - s) * C := by
  have heq : ∀ᵐ u ∂volume.restrict (Ioo (0 : ℝ) 1),
      (if u ≤ r then 0 else if u ≤ s then B else C) =
        (Ioo r s).indicator (fun _ => B) u +
          (Ioo s 1).indicator (fun _ => C) u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae (volume.ae_ne r), ae_restrict_of_ae (volume.ae_ne s)]
      with u hu hur hus
    by_cases hur' : u ≤ r
    · have hsr : ¬s < u := not_lt_of_ge (hur'.trans hrs)
      simp [Set.indicator, Set.mem_Ioo, hur', not_lt_of_ge hur', hsr]
    · by_cases hus' : u ≤ s
      · have hru : r < u := lt_of_not_ge hur'
        have huslt : u < s := lt_of_le_of_ne hus' hus
        simp [Set.indicator, Set.mem_Ioo, hur', hus', hru, huslt,
          not_lt_of_ge hus']
      · have hru : r < u := lt_of_not_ge hur'
        have hsu : s < u := lt_of_not_ge hus'
        have hnus : ¬u < s := not_lt_of_ge hsu.le
        simp [Set.indicator, Set.mem_Ioo, hur', hus', hru, hsu, hnus, hu.2]
  rw [integral_congr_ae heq]
  rw [integral_add]
  · rw [setIntegral_indicator measurableSet_Ioo,
      setIntegral_indicator measurableSet_Ioo]
    have hleft : Ioo (0 : ℝ) 1 ∩ Ioo r s = Ioo r s := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_Ioo]
      constructor
      · exact And.right
      · intro hu
        exact ⟨⟨lt_of_le_of_lt hr0 hu.1, hu.2.trans_le hs1⟩, hu⟩
    have hright : Ioo (0 : ℝ) 1 ∩ Ioo s 1 = Ioo s 1 := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_Ioo]
      constructor
      · exact And.right
      · intro hu
        exact ⟨⟨lt_of_le_of_lt (hr0.trans hrs) hu.1, hu.2⟩, hu⟩
    rw [hleft, hright, setIntegral_const, setIntegral_const]
    simp only [smul_eq_mul, measureReal_def, Real.volume_Ioo,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hrs),
      ENNReal.toReal_ofReal (sub_nonneg.mpr hs1)]
  · exact ((integrableOn_const (μ := volume) (s := Ioo r s) (by simp)).integrable_indicator
      measurableSet_Ioo).integrableOn
  · exact ((integrableOn_const (μ := volume) (s := Ioo s 1) (by simp)).integrable_indicator
      measurableSet_Ioo).integrableOn

private lemma lower_reflected_step_integral
    (s A : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (∫ u in Ioo (0 : ℝ) 1, if u ≤ 1 - s then 0 else A) = s * A := by
  have heq : ∀ᵐ u ∂volume.restrict (Ioo (0 : ℝ) 1),
      (if u ≤ 1 - s then 0 else A) =
        (Ioo (1 - s) 1).indicator (fun _ => A) u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae (volume.ae_ne (1 - s))] with u hu hune
    by_cases hu' : u ≤ 1 - s
    · simp [Set.indicator, Set.mem_Ioo, hu', not_lt_of_ge hu']
    · have hlu : 1 - s < u := lt_of_not_ge hu'
      simp [Set.indicator, Set.mem_Ioo, hu', hlu, hu.2]
  rw [integral_congr_ae heq, setIntegral_indicator measurableSet_Ioo]
  have hset : Ioo (0 : ℝ) 1 ∩ Ioo (1 - s) 1 = Ioo (1 - s) 1 := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Ioo]
    constructor
    · exact And.right
    · intro hu
      exact ⟨⟨lt_of_le_of_lt (sub_nonneg.mpr hs1) hu.1, hu.2⟩, hu⟩
  rw [hset, setIntegral_const]
  rw [smul_eq_mul, measureReal_def, Real.volume_Ioo,
    ENNReal.toReal_ofReal (by linarith : 0 ≤ 1 - (1 - s))]
  ring

/-- Given [the stated mathematical inputs and assumptions](hyp:x,y,z,w₁,w₂,w₃,t,hx,hxy,hyz,hw₁,hw₂,hw₃,hsum,ht₁,ht₂), this result [establishes the stated mathematical conclusion](goal). -/
lemma threeScore_quantileProduct_upper
    (x y z w₁ w₂ w₃ t : ℝ)
    (hx : 0 < x) (hxy : x < y) (hyz : y < z)
    (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hw₃ : 0 ≤ w₃)
    (hsum : w₁ + w₂ + w₃ = 1)
    (ht₁ : x * w₁ < t)
    (ht₂ : t < min (x * w₁ + y * w₂) (z * w₃)) :
    let q := x * w₁ + y * w₂ + z * w₃
    q * (∫ u in Ioo (0 : ℝ) 1,
      quantile (threeScoreOutcomeLaw q t) u *
        quantile (threeScoreInverseLaw x y z w₁ w₂ w₃) u) =
      threeScoreUpperEndpoint x y w₁ t := by
  dsimp only
  let q := x * w₁ + y * w₂ + z * w₃
  change q * (∫ u in Ioo (0 : ℝ) 1,
    quantile (threeScoreOutcomeLaw q t) u *
      quantile (threeScoreInverseLaw x y z w₁ w₂ w₃) u) =
    threeScoreUpperEndpoint x y w₁ t
  have hy : 0 < y := lt_trans hx hxy
  have hz : 0 < z := lt_trans hy hyz
  have hq : 0 < q := by
    dsimp [q]
    have hone : 0 < w₁ + w₂ + w₃ := by rw [hsum]; norm_num
    nlinarith [mul_nonneg hx.le hw₁, mul_nonneg hy.le hw₂, mul_nonneg hz.le hw₃]
  have hs0 : 0 ≤ t / q := by
    have ht0 : 0 < t := lt_of_le_of_lt (mul_nonneg hx.le hw₁) ht₁
    positivity
  have hs1 : t / q ≤ 1 := by
    have htq : t < q := by
      dsimp [q]
      have := lt_of_lt_of_le ht₂ (min_le_left _ _)
      nlinarith [mul_nonneg hz.le hw₃]
    exact (div_lt_one hq).2 htq |>.le
  have ha0 : 0 ≤ x * w₁ / q := div_nonneg (mul_nonneg hx.le hw₁) hq.le
  have ha1 : x * w₁ / q ≤ 1 := by
    apply (div_le_one hq).2
    dsimp [q]
    nlinarith [mul_nonneg hy.le hw₂, mul_nonneg hz.le hw₃]
  have hrs : 1 - t / q ≤ 1 - x * w₁ / q := by
    apply sub_le_sub_left
    exact (div_lt_div_iff_of_pos_right hq).2 ht₁ |>.le
  have heq : ∀ᵐ u ∂volume.restrict (Ioo (0 : ℝ) 1),
      quantile (threeScoreOutcomeLaw q t) u *
          quantile (threeScoreInverseLaw x y z w₁ w₂ w₃) u =
        if u ≤ 1 - t / q then 0
        else if u ≤ 1 - x * w₁ / q then 1 / y else 1 / x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    rw [threeScoreOutcomeLaw_quantile q t u hs0 hs1 hu.1 hu.2,
      threeScoreInverseLaw_quantile x y z w₁ w₂ w₃ u hx hxy hyz
        hw₁ hw₂ hw₃ hq hu.1 hu.2]
    rw [show x * w₁ + y * w₂ + z * w₃ = q by rfl]
    have hthreshold :
        z * w₃ / q + y * w₂ / q = 1 - x * w₁ / q := by
      calc
        z * w₃ / q + y * w₂ / q = (z * w₃ + y * w₂) / q := by ring
        _ = (q - x * w₁) / q := by
          congr 1
          dsimp [q]
          ring
        _ = 1 - x * w₁ / q := by field_simp [ne_of_gt hq]
    rw [hthreshold]
    by_cases hu0 : u ≤ 1 - t / q
    · simp [hu0]
    · have htFirstTwo : t / q < (x * w₁ + y * w₂) / q := by
        exact (div_lt_div_iff_of_pos_right hq).2
          (lt_of_lt_of_le ht₂ (min_le_left _ _))
      have htotal :
          (x * w₁ + y * w₂) / q = 1 - z * w₃ / q := by
        calc
          (x * w₁ + y * w₂) / q = (q - z * w₃) / q := by
            congr 1
            dsimp [q]
            ring
          _ = 1 - z * w₃ / q := by field_simp [ne_of_gt hq]
      have hthird : z * w₃ / q < u := by linarith
      have hnthird : ¬u ≤ z * w₃ / q := not_le.mpr hthird
      simp [hu0, hnthird]
  rw [integral_congr_ae heq,
    upper_step_integral (1 - t / q) (1 - x * w₁ / q) (1 / y) (1 / x)
      (sub_nonneg.mpr hs1) hrs (sub_le_self 1 ha0)]
  unfold threeScoreUpperEndpoint
  field_simp [ne_of_gt hq, ne_of_gt hx, ne_of_gt hy]
  ring

/-- Given [the stated mathematical inputs and assumptions](hyp:x,y,z,w₁,w₂,w₃,t,hx,hxy,hyz,hw₁,hw₂,hw₃,hsum,ht₁,ht₂), this result [establishes the stated mathematical conclusion](goal). -/
lemma threeScore_quantileProduct_lower
    (x y z w₁ w₂ w₃ t : ℝ)
    (hx : 0 < x) (hxy : x < y) (hyz : y < z)
    (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hw₃ : 0 ≤ w₃)
    (hsum : w₁ + w₂ + w₃ = 1)
    (ht₁ : x * w₁ < t)
    (ht₂ : t < min (x * w₁ + y * w₂) (z * w₃)) :
    let q := x * w₁ + y * w₂ + z * w₃
    q * (∫ u in Ioo (0 : ℝ) 1,
      quantile (threeScoreOutcomeLaw q t) u *
        quantile (threeScoreInverseLaw x y z w₁ w₂ w₃) (1 - u)) =
      threeScoreLowerEndpoint z t := by
  dsimp only
  let q := x * w₁ + y * w₂ + z * w₃
  change q * (∫ u in Ioo (0 : ℝ) 1,
    quantile (threeScoreOutcomeLaw q t) u *
      quantile (threeScoreInverseLaw x y z w₁ w₂ w₃) (1 - u)) =
    threeScoreLowerEndpoint z t
  have hy : 0 < y := lt_trans hx hxy
  have hz : 0 < z := lt_trans hy hyz
  have hq : 0 < q := by
    dsimp [q]
    have hone : 0 < w₁ + w₂ + w₃ := by rw [hsum]; norm_num
    nlinarith [mul_nonneg hx.le hw₁, mul_nonneg hy.le hw₂, mul_nonneg hz.le hw₃]
  have hs0 : 0 ≤ t / q := by
    have ht0 : 0 < t := lt_of_le_of_lt (mul_nonneg hx.le hw₁) ht₁
    positivity
  have hs1 : t / q ≤ 1 := by
    have htq : t < q := by
      dsimp [q]
      have := lt_of_lt_of_le ht₂ (min_le_left _ _)
      nlinarith [mul_nonneg hz.le hw₃]
    exact (div_lt_one hq).2 htq |>.le
  have heq : ∀ᵐ u ∂volume.restrict (Ioo (0 : ℝ) 1),
      quantile (threeScoreOutcomeLaw q t) u *
          quantile (threeScoreInverseLaw x y z w₁ w₂ w₃) (1 - u) =
        if u ≤ 1 - t / q then 0 else 1 / z := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    have huv0 : 0 < 1 - u := by linarith [hu.2]
    have huv1 : 1 - u < 1 := by linarith [hu.1]
    rw [threeScoreOutcomeLaw_quantile q t u hs0 hs1 hu.1 hu.2,
      threeScoreInverseLaw_quantile x y z w₁ w₂ w₃ (1 - u) hx hxy hyz
        hw₁ hw₂ hw₃ hq huv0 huv1]
    rw [show x * w₁ + y * w₂ + z * w₃ = q by rfl]
    by_cases hu0 : u ≤ 1 - t / q
    · simp [hu0]
    · have htThird : t / q < z * w₃ / q := by
        exact (div_lt_div_iff_of_pos_right hq).2
          (lt_of_lt_of_le ht₂ (min_le_right _ _))
      have hfirst : 1 - u ≤ z * w₃ / q := by linarith
      simp [hu0, hfirst]
  rw [integral_congr_ae heq, lower_reflected_step_integral (t / q) (1 / z) hs0 hs1]
  unfold threeScoreLowerEndpoint
  field_simp [ne_of_gt hq, ne_of_gt hz]

end
end CausalSmith.PartialID.UnlinkedPropensityAte
