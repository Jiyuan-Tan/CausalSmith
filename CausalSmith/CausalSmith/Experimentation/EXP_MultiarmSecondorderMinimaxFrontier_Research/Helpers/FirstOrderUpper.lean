import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.T_contrast_risk_continuity
import Causalean.Experimentation.DesignBased.ProductVariance

/-! The contrast-weighted finite-sample upper risk bound, split out to avoid theorem cycles. -/

open scoped BigOperators

namespace CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

/-- The upper-bound unit score is the contrast-weighted inverse-probability score used by the explicit first-order procedure. -/
noncomputable def upperUnitScore (c : Contrast ℝ K) (t : RespType K) (a : Arm K) : ℝ :=
  if qStar c a = 0 then 0
  else c a * ((if t a then 1 else 0) - 1 / 2) / qStar c a

/-- [the upper unit score mean property holds](goal). -/
lemma upperUnitScore_mean (c : Contrast ℝ K) (t : RespType K) :
    (qStarDesign c).E (upperUnitScore c t) = ∑ a, c a * (if t a then 1 else 0) := by
  classical
  unfold Causalean.Experimentation.DesignBased.FiniteDesign.E upperUnitScore qStarDesign
  calc
    ∑ a, qStar c a * (if qStar c a = 0 then 0 else
        c a * ((if t a then 1 else 0) - 1 / 2) / qStar c a) =
        ∑ a, c a * ((if t a then 1 else 0) - 1 / 2) := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases hc : c a = 0
      · simp [qStar, hc]
      · have hq : qStar c a ≠ 0 :=
          div_ne_zero (abs_ne_zero.mpr hc) (ne_of_gt (Lc_pos c))
        rw [if_neg hq]
        field_simp [hq]
    _ = ∑ a, c a * (if t a then 1 else 0) := by
      calc
        _ = ∑ a, (c a * (if t a then 1 else 0) - c a / 2) := by
          apply Finset.sum_congr rfl
          intro a _
          ring
        _ = (∑ a, c a * (if t a then 1 else 0)) - ∑ a, c a / 2 := by
          rw [Finset.sum_sub_distrib]
        _ = _ := by rw [← Finset.sum_div, c.sum_zero]; norm_num

/-- [the upper unit score second moment property holds](goal). -/
lemma upperUnitScore_secondMoment (c : Contrast ℝ K) (t : RespType K) :
    (qStarDesign c).E (fun a => upperUnitScore c t a ^ 2) = C0 c := by
  classical
  unfold Causalean.Experimentation.DesignBased.FiniteDesign.E upperUnitScore qStarDesign
  rw [C0]
  have hhalf (a : Arm K) : ((if t a then (1 : ℝ) else 0) - 1 / 2) ^ 2 = 1 / 4 := by
    by_cases ht : t a <;> simp [ht] <;> norm_num
  calc
    ∑ a, qStar c a * (if qStar c a = 0 then 0 else
        c a * ((if t a then 1 else 0) - 1 / 2) / qStar c a) ^ 2 =
        ∑ a, Lc c * |c a| / 4 := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases hc : c a = 0
      · simp [qStar, hc]
      · have hq : qStar c a ≠ 0 :=
          div_ne_zero (abs_ne_zero.mpr hc) (ne_of_gt (Lc_pos c))
        rw [if_neg hq, div_pow, mul_pow, hhalf]
        simp only [qStar]
        field_simp [abs_ne_zero.mpr hc, ne_of_gt (Lc_pos c)]
        rw [sq_abs]
    _ = Lc c ^ 2 / 4 := by
      rw [← Finset.sum_div, ← Finset.mul_sum]
      simp only [Lc]
      ring

-- @node: contrastWeightedProcedure_upperRisk
/-- [the population size is positive](hyp:hn), [the contrast weighted procedure upper risk property holds](goal). -/
lemma contrastWeightedProcedure_upperRisk (K n : ℕ) (c : Contrast ℝ K) (hn : 0 < n) :
    Causalean.Stat.worstCaseRisk
      (fun (p : Procedure K n c) (z : Schedule K n) => labeledRisk c p z)
      (contrastWeightedProcedure K n c) ≤ C0 c / n := by
  classical
  apply Causalean.Stat.worstCaseRisk_le
  intro z
  let D := Causalean.Experimentation.DesignBased.prodDesign
    (fun _ : Unit n => qStarDesign c)
  let raw : Assign K n → ℝ := fun A => (n : ℝ)⁻¹ * ∑ i, upperUnitScore c (z i) (A i)
  have hunbiased : D.Unbiased raw (tauC c z) := by
    unfold Causalean.Experimentation.DesignBased.FiniteDesign.Unbiased raw D tauC
    rw [Causalean.Experimentation.DesignBased.FiniteDesign.E_const_mul,
      Causalean.Experimentation.DesignBased.FiniteDesign.E_sum]
    simp_rw [Causalean.Experimentation.DesignBased.FiniteDesign.E_prod_apply,
      upperUnitScore_mean]
  have hvar : D.Var raw ≤ C0 c / n := by
    rw [show raw = fun A => ∑ i, (n : ℝ)⁻¹ * upperUnitScore c (z i) (A i) by
      funext A; simp only [raw]; rw [Finset.mul_sum],
      Causalean.Experimentation.DesignBased.FiniteDesign.Var_prod_linear_comb]
    calc
      _ ≤ ∑ _i : Unit n, (n : ℝ)⁻¹ ^ 2 * C0 c := by
        apply Finset.sum_le_sum
        intro i _
        gcongr
        rw [Causalean.Experimentation.DesignBased.FiniteDesign.Var_eq,
          upperUnitScore_secondMoment]
        exact sub_le_self _ (sq_nonneg _)
      _ = C0 c / n := by simp; field_simp
  unfold labeledRisk contrastWeightedProcedure
  change D.mse (fun A => clip c (centeredContrastScore c A (obsOutcome z A)))
    (tauC c z) ≤ C0 c / n
  calc
    _ ≤ D.mse raw (tauC c z) := by
      unfold Causalean.Experimentation.DesignBased.FiniteDesign.mse
      apply Finset.sum_le_sum
      intro A _
      apply mul_le_mul_of_nonneg_left _ (D.p_nonneg A)
      change (clip c (centeredContrastScore c A (obsOutcome z A)) - tauC c z) ^ 2 ≤
        (raw A - tauC c z) ^ 2
      have hraw : centeredContrastScore c A (obsOutcome z A) = raw A := rfl
      rw [hraw]
      exact clip_sq_dist_le c _ _ (tauC_mem_naturalInterval c z hn)
    _ = D.Var raw := D.mse_eq_var_of_unbiased hunbiased
    _ ≤ _ := hvar

end CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier
