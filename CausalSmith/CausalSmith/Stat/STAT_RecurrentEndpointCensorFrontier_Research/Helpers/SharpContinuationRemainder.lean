module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ContinuationBias

/-!
# Sharp integrated continuation remainder

Integrating the endpoint power before bounding it preserves the explicit
bias coefficient. The order-zero survival product has a direct remainder
bound from the hazard band and the recurrence Hölder condition.
-/

public section

open MeasureTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- An endpoint-power envelope integrates with its exact coefficient. -/
-- @node: endpointPower_abs_integral_le
lemma endpointPower_abs_integral_le {β C x y : ℝ}
    (hβ : 0 < β) (hC : 0 ≤ C) (hxy : x ≤ y) (hy : y ≤ 1)
    (r : ℝ → ℝ) (hr : ContinuousOn r (Icc x y))
    (hb : ∀ t ∈ Icc x y, |r t| ≤ C * (1 - t) ^ β) :
    |∫ t in x..y, r t| ≤ C * ∫ t in x..y, (1 - t) ^ β := by
  have hp : Continuous (fun t : ℝ => (1 - t) ^ β) :=
    (by fun_prop : Continuous (fun t : ℝ => 1 - t)).rpow_const (fun _ => Or.inr hβ.le)
  calc
    _ ≤ ∫ t in x..y, |r t| := intervalIntegral.abs_integral_le_integral_abs hxy
    _ ≤ ∫ t in x..y, C * (1 - t) ^ β :=
      intervalIntegral.integral_mono_on hxy
        (hr.abs.intervalIntegrable_of_Icc hxy)
        ((continuous_const.mul hp).intervalIntegrable _ _) hb
    _ = _ := by rw [intervalIntegral.integral_const_mul]

/-- Integrating the Taylor envelope in the band and terminal interval gives
exactly the coefficient used by the paper's explicit bias constant. -/
-- @node: continuationWeight_sharp_remainder_bound
lemma continuationWeight_sharp_remainder_bound (ell : ℕ) {h β C : ℝ}
    (hh : 0 < h) (hhalf : h ≤ 1 / 2) (hβ : 0 < β) (hC : 0 ≤ C)
    (r : ℝ → ℝ) (hr : ContinuousOn r (Icc (0 : ℝ) 1))
    (hb : ∀ t ∈ Icc (1 - 2 * h) 1, |r t| ≤ C * (1 - t) ^ β) :
    |(∫ t in (0 : ℝ)..(1 - h), continuationWeight ell h t * r t) -
      ∫ t in (0 : ℝ)..1, r t| ≤
      C * ((∑ m : Fin (ell + 1),
        |((continuationGram ell)⁻¹.mulVec (continuationRhs ell)) m| * (2 : ℝ) ^ m.val) *
        ((2 : ℝ) ^ (β + 1) - 1) / (β + 1) + 1 / (β + 1)) * h ^ (β + 1) := by
  let K : ℝ := ∑ m : Fin (ell + 1),
    |((continuationGram ell)⁻¹.mulVec (continuationRhs ell)) m| * (2 : ℝ) ^ m.val
  have hK : 0 ≤ K := Finset.sum_nonneg (fun _ _ => by positivity)
  have hband : ContinuousOn r (Icc (1 - 2 * h) (1 - h)) :=
    hr.mono (by intro t ht; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  have hterm : ContinuousOn r (Icc (1 - h) 1) :=
    hr.mono (by intro t ht; exact ⟨by linarith [ht.1], ht.2⟩)
  have hk : Continuous (fun t : ℝ => continuationPoly ell ((1 - t) / h)) :=
    (continuationPoly_continuous ell).comp (by fun_prop)
  have hbi := endpointPower_abs_integral_le hβ (mul_nonneg hK hC)
    (by linarith : 1 - 2 * h ≤ 1 - h) (by linarith : 1 - h ≤ 1)
    (fun t => continuationPoly ell ((1 - t) / h) * r t)
    (hk.continuousOn.mul hband) (by
      intro t ht
      have hx0 : 0 ≤ (1 - t) / h := div_nonneg (by linarith [ht.2]) hh.le
      have hx2 : (1 - t) / h ≤ 2 := (div_le_iff₀ hh).2 (by linarith [ht.1])
      rw [abs_mul]
      exact (mul_le_mul (continuationPoly_abs_le_coeffSum ell hx0 hx2)
        (hb t ⟨ht.1, by linarith [ht.2]⟩) (abs_nonneg _) hK).trans_eq (by ring))
  have hti := endpointPower_abs_integral_le hβ hC
    (by linarith : 1 - h ≤ 1) le_rfl r hterm
    (fun t ht => hb t ⟨by linarith [ht.1], ht.2⟩)
  rw [endpointRpow_band_integral hβ] at hbi
  rw [endpointRpow_terminal_integral hβ] at hti
  rw [continuationWeight_remainder_band_terminal ell hh hhalf r hr]
  have hmul := Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hh.le (z := β + 1)
  calc
    _ ≤ K * C * (((2 * h) ^ (β + 1) - h ^ (β + 1)) / (β + 1)) +
        C * (h ^ (β + 1) / (β + 1)) := (abs_sub _ _).trans (add_le_add hbi hti)
    _ = _ := by rw [hmul]; dsimp [K]; ring

/-- A bounded nonnegative hazard gives a Lipschitz survival increment to the
endpoint, without differentiability assumptions. -/
-- @node: survival_endpoint_increment_le
lemma survival_endpoint_increment_le (c : ClassConstants) (P : SubjectLaw)
    (hD : DeathBounds c P) (a : Arm)
    (hInt : IntervalIntegrable (P.hazard a) volume 0 1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |survival P a t - survival P a 1| ≤ c.dMax * (1 - t) := by
  let J := ∫ u in t..1, P.hazard a u
  have hJ : 0 ≤ J := intervalIntegral.integral_nonneg ht.2 (fun u hu =>
    c.dMin_pos.le.trans (hD a u ⟨ht.1.trans hu.1, hu.2⟩).1)
  have hJbound : J ≤ c.dMax * (1 - t) := by
    have hb := intervalIntegral.integral_mono_on ht.2
      (hInt.mono_set (by
        rw [uIcc_of_le ht.2, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        exact Icc_subset_Icc ht.1 le_rfl)) intervalIntegrable_const
      (fun u hu => (hD a u ⟨ht.1.trans hu.1, hu.2⟩).2)
    simpa [J, mul_comm] using hb
  have hsplit : (∫ u in (0 : ℝ)..t, P.hazard a u) + J =
      ∫ u in (0 : ℝ)..1, P.hazard a u := by
    exact intervalIntegral.integral_add_adjacent_intervals
      (hInt.mono_set (by
        rw [uIcc_of_le ht.1, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        exact Icc_subset_Icc le_rfl ht.2))
      (hInt.mono_set (by
        rw [uIcc_of_le ht.2, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        exact Icc_subset_Icc ht.1 le_rfl))
  have heq : survival P a 1 = survival P a t * Real.exp (-J) := by
    unfold survival
    rw [← hsplit, neg_add, Real.exp_add]
  have hS := (survival_bounds_of_deathBounds c P hD a ht).2
  have hSpos := (Real.exp_pos (-(∫ u in (0 : ℝ)..t, P.hazard a u))).le
  change 0 ≤ survival P a t at hSpos
  have he : Real.exp (-J) ≤ 1 := by simpa using Real.exp_le_exp.mpr (neg_nonpos.mpr hJ)
  have hl := Real.add_one_le_exp (-J)
  rw [heq, abs_of_nonneg (by nlinarith : 0 ≤ survival P a t - survival P a t * Real.exp (-J))]
  nlinarith [mul_nonneg hSpos (by linarith : 0 ≤ Real.exp (-J) - (1 - J)),
    mul_nonneg (sub_nonneg.mpr hS) hJ]

/-- In order zero, the product remainder coefficient is the recurrence
Hölder constant plus the hazard bound times the recurrence bound. -/
-- @node: survival_product_orderZero_remainder
lemma survival_product_orderZero_remainder (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) (hzero : holderOrder c = 0)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |survival P a t * P.lam a t - survival P a 1 * P.lam a 1| ≤
      (c.Llambda + c.dMax * c.lambdaMax) * (1 - t) ^ c.beta := by
  have hβ : c.beta ≤ 1 := by simpa [hzero] using (holderOrder_remainder_exponent c).2
  have hl := (hP.recurrenceHolder a).2 t ht 1 (by norm_num)
  simp only [hzero, iteratedDerivWithin_zero, Nat.cast_zero, sub_zero] at hl
  rw [abs_sub_comm t 1, abs_of_nonneg (sub_nonneg.mpr ht.2)] at hl
  have hs := survival_endpoint_increment_le c P hP.deathBounds a (hP.deathHazard.1 a) ht
  have hp : 1 - t ≤ (1 - t) ^ c.beta :=
    Real.self_le_rpow_of_le_one (by linarith [ht.2]) (by linarith [ht.1]) hβ
  have hSp := (Real.exp_pos (-(∫ u in (0 : ℝ)..t, P.hazard a u))).le
  change 0 ≤ survival P a t at hSp
  have hSu := (survival_bounds_of_deathBounds c P hP.deathBounds a ht).2
  have hLam := hP.recurrenceBounds a 1 (by norm_num)
  have hLamp : 0 ≤ P.lam a 1 := c.lambdaMin_pos.le.trans hLam.1
  have hd : 0 ≤ c.dMax := c.dMin_pos.le.trans c.dMin_lt.le
  calc
    _ = |survival P a t * (P.lam a t - P.lam a 1) +
        (survival P a t - survival P a 1) * P.lam a 1| := by congr 1; ring
    _ ≤ |survival P a t * (P.lam a t - P.lam a 1)| +
        |(survival P a t - survival P a 1) * P.lam a 1| := abs_add_le _ _
    _ ≤ 1 * (c.Llambda * (1 - t) ^ c.beta) +
        (c.dMax * (1 - t)) * c.lambdaMax := by
      rw [abs_mul, abs_mul, abs_of_nonneg hSp, abs_of_nonneg hLamp]
      exact add_le_add (mul_le_mul hSu hl (abs_nonneg _) (by norm_num))
        (mul_le_mul hs hLam.2 hLamp (mul_nonneg hd (by linarith [ht.2])))
    _ ≤ _ := by
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hd)
        (c.lambdaMin_pos.le.trans c.lambdaMin_lt.le)
      nlinarith only [this]

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
