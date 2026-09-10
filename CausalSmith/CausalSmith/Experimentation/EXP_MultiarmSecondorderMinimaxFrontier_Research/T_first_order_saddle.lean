import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.T_exact_response_type_game
import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.T_embedded_two_arm_converse
import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.T_contrast_risk_continuity
import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.ScoreDesign
import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.BayesInformation
import Causalean.Experimentation.DesignBased.ProductVariance

/-! First-order minimax constant and contrast-weighted upper procedure. -/

open Filter

namespace CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

-- @node: firstOrderUnitScore
/-- The first-order unit score is the contrast-weighted inverse-probability score under the contrast-optimal assignment law. -/
noncomputable def firstOrderUnitScore (c : Contrast ℝ K) (t : RespType K) (a : Arm K) : ℝ :=
  if qStar c a = 0 then 0
  else c a * ((if t a then 1 else 0) - 1 / 2) / qStar c a

-- @node: firstOrderUnitScore_mean
/-- [the first order unit score mean property holds](goal). -/
lemma firstOrderUnitScore_mean (c : Contrast ℝ K) (t : RespType K) :
    (qStarDesign c).E (firstOrderUnitScore c t) =
      ∑ a, c a * (if t a then 1 else 0) := by
  classical
  unfold Causalean.Experimentation.DesignBased.FiniteDesign.E firstOrderUnitScore qStarDesign
  calc
    ∑ a, qStar c a *
        (if qStar c a = 0 then 0
          else c a * ((if t a then 1 else 0) - 1 / 2) / qStar c a) =
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
            ∑ a, c a * ((if t a then (1 : ℝ) else 0) - 1 / 2) =
                ∑ a, (c a * (if t a then 1 else 0) - c a / 2) := by
                  apply Finset.sum_congr rfl
                  intro a _
                  ring
            _ = (∑ a, c a * (if t a then 1 else 0)) - ∑ a, c a / 2 := by
              rw [Finset.sum_sub_distrib]
            _ = ∑ a, c a * (if t a then 1 else 0) := by
              rw [← Finset.sum_div, c.sum_zero]
              norm_num

-- @node: firstOrderUnitScore_secondMoment
/-- [the first order unit score second moment property holds](goal). -/
lemma firstOrderUnitScore_secondMoment (c : Contrast ℝ K) (t : RespType K) :
    (qStarDesign c).E (fun a => firstOrderUnitScore c t a ^ 2) = C0 c := by
  classical
  unfold Causalean.Experimentation.DesignBased.FiniteDesign.E firstOrderUnitScore qStarDesign
  rw [C0]
  have hhalf (a : Arm K) :
      ((if t a then (1 : ℝ) else 0) - 1 / 2) ^ 2 = 1 / 4 := by
    by_cases ht : t a <;> simp [ht] <;> norm_num
  calc
    ∑ a, qStar c a *
        (if qStar c a = 0 then 0
          else c a * ((if t a then 1 else 0) - 1 / 2) / qStar c a) ^ 2 =
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

-- @node: contrastWeightedProcedure_risk
/-- [the population size is positive](hyp:hn), [the contrast weighted procedure risk property holds](goal). -/
lemma contrastWeightedProcedure_risk (K n : ℕ) (c : Contrast ℝ K) (hn : 0 < n) :
    Causalean.Stat.worstCaseRisk
      (fun (p : Procedure K n c) (z : Schedule K n) => labeledRisk c p z)
      (contrastWeightedProcedure K n c) ≤ C0 c / n := by
  classical
  apply Causalean.Stat.worstCaseRisk_le
  intro z
  let D : Causalean.Experimentation.DesignBased.FiniteDesign (Assign K n) :=
    Causalean.Experimentation.DesignBased.prodDesign (fun _ : Unit n => qStarDesign c)
  let raw : Assign K n → ℝ := fun A =>
    (n : ℝ)⁻¹ * ∑ i, firstOrderUnitScore c (z i) (A i)
  have hraw : ∀ A, centeredContrastScore c A (obsOutcome z A) = raw A := by
    intro A
    rfl
  have htau : tauC c z ∈ Set.Icc (-Lc c / 2) (Lc c / 2) :=
    tauC_mem_naturalInterval c z hn
  have hunbiased : D.Unbiased raw (tauC c z) := by
    unfold Causalean.Experimentation.DesignBased.FiniteDesign.Unbiased raw D tauC
    rw [Causalean.Experimentation.DesignBased.FiniteDesign.E_const_mul,
      Causalean.Experimentation.DesignBased.FiniteDesign.E_sum]
    simp_rw [Causalean.Experimentation.DesignBased.FiniteDesign.E_prod_apply,
      firstOrderUnitScore_mean]
  have hvar : D.Var raw ≤ C0 c / n := by
    have hrawSum : raw = fun A => ∑ i, (n : ℝ)⁻¹ * firstOrderUnitScore c (z i) (A i) := by
      funext A
      simp only [raw]
      rw [Finset.mul_sum]
    rw [hrawSum,
      Causalean.Experimentation.DesignBased.FiniteDesign.Var_prod_linear_comb]
    calc
      ∑ i : Unit n, (n : ℝ)⁻¹ ^ 2 *
          (qStarDesign c).Var (firstOrderUnitScore c (z i)) ≤
          ∑ _i : Unit n, (n : ℝ)⁻¹ ^ 2 * C0 c := by
            apply Finset.sum_le_sum
            intro i _
            gcongr
            rw [Causalean.Experimentation.DesignBased.FiniteDesign.Var_eq,
              firstOrderUnitScore_secondMoment]
            exact sub_le_self _ (sq_nonneg _)
      _ = C0 c / n := by
            simp
            field_simp
  unfold labeledRisk contrastWeightedProcedure
  change D.mse (fun A => clip c (centeredContrastScore c A (obsOutcome z A)))
      (tauC c z) ≤ C0 c / n
  calc
    D.mse (fun A => clip c (centeredContrastScore c A (obsOutcome z A))) (tauC c z) ≤
        D.mse raw (tauC c z) := by
          unfold Causalean.Experimentation.DesignBased.FiniteDesign.mse
          unfold Causalean.Experimentation.DesignBased.FiniteDesign.E
          apply Finset.sum_le_sum
          intro A _
          exact mul_le_mul_of_nonneg_left
            (by
              change (clip c (centeredContrastScore c A (obsOutcome z A)) - tauC c z) ^ 2 ≤
                (raw A - tauC c z) ^ 2
              rw [hraw A]
              exact clip_sq_dist_le c _ _ htau)
            (D.p_nonneg A)
    _ = D.Var raw := D.mse_eq_var_of_unbiased hunbiased
    _ ≤ C0 c / n := hvar

-- @node: contrast_has_admissible_arm_count
/-- [the contrast has admissible arm count property holds](goal). -/
lemma contrast_has_admissible_arm_count (c : Contrast ℝ K) : AdmissibleArmCount K := by
  unfold AdmissibleArmCount
  by_contra hK
  have hKle : K ≤ 1 := by omega
  interval_cases K
  · apply c.nonzero
    funext a
    exact Fin.elim0 a
  · apply c.nonzero
    funext a
    have ha : a = 0 := Fin.eq_zero a
    subst a
    simpa using c.sum_zero

-- @node: firstOrder_minimax_limit
/-- [the first order minimax limit property holds](goal). -/
lemma firstOrder_minimax_limit (K : ℕ) (c : Contrast ℝ K) :
    Tendsto (fun n : ℕ => (n : ℝ) * rhoN K n c) atTop (nhds (C0 c)) := by
  have hC0 : 0 ≤ C0 c := by unfold C0; positivity
  have herr : Tendsto (fun n : ℕ => |(n : ℝ) * rhoN K n c - C0 c|)
      atTop (nhds 0) := by
    apply squeeze_zero' (g := fun n : ℕ =>
      43 * C0 c * (n : ℝ) ^ (-(1 / 3 : ℝ)))
    · exact Filter.Eventually.of_forall fun _ => abs_nonneg _
    · filter_upwards [eventually_atTop.2 ⟨8, fun n hn => hn⟩] with n hn8
      have hnpos : 0 < n := by omega
      have hd := (embedded_two_arm_converse K n c
        (contrast_has_admissible_arm_count c) hnpos).2.2.1 hn8
      have hid : (n : ℝ) * rhoN K n c - C0 c = -(n : ℝ) * dN K c n := by
        unfold dN
        field_simp [hnpos.ne']
        ring
      have hpow : (n : ℝ) * (n : ℝ) ^ (-(4 / 3 : ℝ)) =
          (n : ℝ) ^ (-(1 / 3 : ℝ)) := by
        calc
          (n : ℝ) * (n : ℝ) ^ (-(4 / 3 : ℝ)) =
              (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-(4 / 3 : ℝ)) := by
                rw [Real.rpow_one]
          _ = (n : ℝ) ^ ((1 : ℝ) + -(4 / 3 : ℝ)) :=
            (Real.rpow_add (Nat.cast_pos.mpr hnpos) _ _).symm
          _ = (n : ℝ) ^ (-(1 / 3 : ℝ)) := by congr 1 <;> ring
      rw [hid, abs_mul, abs_neg, abs_of_nonneg (Nat.cast_nonneg n),
        abs_of_nonneg hd.1]
      calc
        (n : ℝ) * dN K c n ≤
            (n : ℝ) * (43 * C0 c * (n : ℝ) ^ (-(4 / 3 : ℝ))) :=
          mul_le_mul_of_nonneg_left hd.2.2 (Nat.cast_nonneg n)
        _ = 43 * C0 c * ((n : ℝ) * (n : ℝ) ^ (-(4 / 3 : ℝ))) := by ring
        _ = 43 * C0 c * (n : ℝ) ^ (-(1 / 3 : ℝ)) := by rw [hpow]
    · simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
        tendsto_natCast_atTop_atTop).const_mul (43 * C0 c)
  exact tendsto_iff_dist_tendsto_zero.2 (by simpa [Real.dist_eq] using herr)

-- @node: thm:first-order-saddle
/-- [the contrast-weighted design and estimator attain the asymptotic first-order minimax constant, and the matching lower bound makes this constant a saddle value](goal). -/
theorem first_order_saddle (K : ℕ) (c : Contrast ℝ K) :
    Tendsto (fun n : ℕ => (n : ℝ) * rhoN K n c) atTop (nhds (C0 c)) ∧
    (∀ n, 0 < n →
      Causalean.Stat.worstCaseRisk
        (fun (p : Procedure K n c) (z : Schedule K n) => labeledRisk c p z)
        (contrastWeightedProcedure K n c) ≤ C0 c / n) := by
  constructor
  · exact firstOrder_minimax_limit K c
  · exact fun n hn => contrastWeightedProcedure_risk K n c hn

end CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier
