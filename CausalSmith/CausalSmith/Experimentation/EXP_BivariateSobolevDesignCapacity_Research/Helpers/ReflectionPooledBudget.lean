module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.ReflectionCoefficientTransport
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.ReflectionTargetInterpolation

/-! # Pooled canonical reflection budget

Exact Fourier component separation and local coordinate transport sum the
constant-one component contractions into the pooled ambient spectral bound.
-/

public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

/-- [ Nonnegative Fourier masses commute with a finite sum of components.](goal) Under [the stated conditions](hyp:f). -/
-- @node: component_mass_tsum_sum
lemma component_mass_tsum_sum {d : ℕ} {K : Type*} (f : Fin d → K → ℝ≥0∞) :
    (∑' k, ∑ j, f j k) = ∑ j, ∑' k, f j k := by
  have h := ENNReal.tsum_comm (f := fun k j => f j k)
  simpa only [tsum_fintype] using h

/-- [ At each active frequency only its unique canonical component contributes to the
weighted outcome mass; summing gives a bound by the ambient component budgets.](goal) Under [the stated conditions](hyp:hm). -/
-- @node: reflectedBudget_le_ambient_component_budgets
lemma reflectedBudget_le_ambient_component_budgets {d : ℕ} (m : CenteredL2Fn d)
    (hm : OrderTwo m) (s : ℝ) :
    reflectedBudget s m.val ≤
      (∑ j, ∑' k : Fin d → ℤ, ENNReal.ofReal
        ((1 + Real.pi ^ 2 * frequencyComplexity k) ^ s *
          ‖Fhat (fun x : Cube d => g1 m.val j (x j)) k‖ ^ 2)) +
      ∑ j, ∑ l, if j < l then
        (∑' k : Fin d → ℤ, ENNReal.ofReal
          ((1 + Real.pi ^ 2 * frequencyComplexity k) ^ s *
            ‖Fhat (fun x : Cube d => g2 m.val j l (x j) (x l)) k‖ ^ 2)) else 0 := by
  classical
  let A : Fin d → (Fin d → ℤ) → ℝ≥0∞ := fun j k => ENNReal.ofReal
    ((1 + Real.pi ^ 2 * frequencyComplexity k) ^ s *
      ‖Fhat (fun x : Cube d => g1 m.val j (x j)) k‖ ^ 2)
  let B : Fin d → Fin d → (Fin d → ℤ) → ℝ≥0∞ := fun j l k =>
    if j < l then ENNReal.ofReal
      ((1 + Real.pi ^ 2 * frequencyComplexity k) ^ s *
        ‖Fhat (fun x : Cube d => g2 m.val j l (x j) (x l)) k‖ ^ 2) else 0
  have hpoint (k : Fin d → ℤ) :
      (if 1 ≤ (frequencySupport k).card ∧ (frequencySupport k).card ≤ 2 then
        ENNReal.ofReal ((1 + Real.pi ^ 2 * frequencyComplexity k) ^ s *
          ‖Fhat m.val k‖ ^ 2) else 0) ≤ (∑ j, A j k) + ∑ j, ∑ l, B j l k := by
    by_cases hk : 1 ≤ (frequencySupport k).card ∧ (frequencySupport k).card ≤ 2
    · rw [if_pos hk]
      by_cases hc : (frequencySupport k).card = 1
      · obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hc
        rw [Fhat_orderTwo_single_component m hm j k hj]
        change A j k ≤ _
        calc
          A j k ≤ ∑ r, A r k :=
            Finset.single_le_sum (f := fun r => A r k)
              (fun _ _ => bot_le) (Finset.mem_univ j)
          _ ≤ (∑ r, A r k) + ∑ r, ∑ t, B r t k := le_add_of_nonneg_right bot_le
      · obtain ⟨j, l, hjl, hsupport⟩ := (Finset.card_eq_two (s := frequencySupport k)).mp (by omega)
        have hp (r t : Fin d) (hrt : r < t) (heq : frequencySupport k = {r, t}) :
            ENNReal.ofReal ((1 + Real.pi ^ 2 * frequencyComplexity k) ^ s *
              ‖Fhat m.val k‖ ^ 2) ≤ (∑ j, A j k) + ∑ j, ∑ l, B j l k := by
          rw [Fhat_orderTwo_pair_component m hm r t hrt k heq]
          have ht : B r t k ≤ ∑ l, B r l k :=
            Finset.single_le_sum (f := fun l => B r l k)
              (fun _ _ => bot_le) (Finset.mem_univ t)
          have hr : (∑ l, B r l k) ≤ ∑ j, ∑ l, B j l k :=
            Finset.single_le_sum (f := fun j => ∑ l, B j l k)
              (fun _ _ => bot_le) (Finset.mem_univ r)
          have h : B r t k ≤ (∑ j, A j k) + ∑ j, ∑ l, B j l k :=
            (ht.trans hr).trans (le_add_of_nonneg_left bot_le)
          simpa only [B, if_pos hrt] using h
        rcases lt_or_gt_of_ne hjl with hlt | hgt
        · exact hp j l hlt hsupport
        · exact hp l j hgt (hsupport.trans (Finset.pair_comm j l))
    · rw [if_neg hk]
      exact bot_le
  have hsum := ENNReal.tsum_le_tsum hpoint
  rw [ENNReal.tsum_add, component_mass_tsum_sum] at hsum
  simp_rw [component_mass_tsum_sum] at hsum
  change reflectedBudget s m.val ≤ _ at hsum
  convert hsum using 1
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  by_cases hjl : j < l <;> simp [B, hjl]

/-- [ Local coordinate transport pools the ambient spectral mass into local component budgets.](goal) Under [the stated conditions](hyp:hm). -/
-- @node: reflectedBudget_le_local_component_budgets
lemma reflectedBudget_le_local_component_budgets {d : ℕ} (m : CenteredL2Fn d)
    (hm : OrderTwo m) (s : ℝ) :
    reflectedBudget s m.val ≤
      (∑ j, componentFourierBudget 1 s (fun u => g1 m.val j (u 0))) +
      ∑ j, ∑ l, if j < l then
        componentFourierBudget 2 s (fun u => g2 m.val j l (u 0) (u 1)) else 0 := by
  apply (reflectedBudget_le_ambient_component_budgets m hm s).trans
  apply add_le_add
  · exact Finset.sum_le_sum (fun j _ => g1_ambient_budget_le_local m j s)
  · apply Finset.sum_le_sum
    intro j _
    apply Finset.sum_le_sum
    intro l _
    by_cases hjl : j < l
    · simp only [if_pos hjl]
      exact g2_ambient_budget_le_local m j l (ne_of_lt hjl) s
    · simp only [if_neg hjl, le_refl]

/-- [ Exact component contraction and the defining pooled restriction budget bound the
reflected outcome's weighted Fourier budget by one.](goal) Under [the stated conditions](hyp:hs,hs1,hm). -/
-- @node: reflectedBudget_le_one_of_sobolevClass
lemma reflectedBudget_le_one_of_sobolevClass {d : ℕ} {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (m : CenteredL2Fn d) (hm : SobolevClass d s m) :
    reflectedBudget s m.val ≤ 1 := by
  apply (reflectedBudget_le_local_component_budgets m hm.orderTwo s).trans
  apply le_trans _ hm.pooledBudget
  apply add_le_add
  · apply Finset.sum_le_sum
    intro j _
    exact componentFourierBudget_le_sobolevNormSq 1 (Or.inl rfl) s hs hs1 _
  · apply Finset.sum_le_sum
    intro j _
    apply Finset.sum_le_sum
    intro l _
    by_cases hjl : j < l
    · simp only [if_pos hjl]
      exact componentFourierBudget_le_sobolevNormSq 2 (Or.inr rfl) s hs hs1 _
    · simp only [if_neg hjl, le_refl]

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
