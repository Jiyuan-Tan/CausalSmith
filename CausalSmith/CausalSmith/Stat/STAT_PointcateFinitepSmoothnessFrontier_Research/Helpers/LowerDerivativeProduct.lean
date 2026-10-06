module
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Product-rule bounds for the lower likelihood's mixed derivative ledger. -/
public section
noncomputable section
open scoped BigOperators
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier

/-- Product-rule induction counts both same-factor and different-factor derivatives.
The sum of unscaled outcome marks is retained throughout the induction. -/
-- @node: lower_product_derivative_ledger
lemma lower_product_derivative_ledger {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f fS : ι → ℝ → ℝ → ℝ) (fT fST : ι → ℝ → ℝ)
    (w : ι → ℝ) (s t : ℝ)
    (hfS : ∀ i, HasDerivAt (fun u => f i u t) (fS i s t) s)
    (hfT : ∀ i u, HasDerivAt (fun v => f i u v) (fT i u) t)
    (hfST : ∀ i, HasDerivAt (fT i) (fST i s) s)
    (hw : ∀ i, 0 ≤ w i)
    (hbound : ∀ i ∈ S, |f i s t| ≤ 3/2 ∧ |fS i s t| ≤ 6*(3/2) ∧
      |fT i s| ≤ 2*(3/2)*w i ∧ |fST i s| ≤ 12*(3/2)*w i) :
    ∃ dS dST : ℝ, ∃ dT : ℝ → ℝ,
      HasDerivAt (fun u => ∏ i ∈ S, f i u t) dS s ∧
      (∀ u, HasDerivAt (fun v => ∏ i ∈ S, f i u v) (dT u) t) ∧
      HasDerivAt dT dST s ∧
      |∏ i ∈ S, f i s t| ≤ (3/2 : ℝ)^S.card ∧
      |dS| ≤ 6*(S.card : ℝ)*(3/2 : ℝ)^S.card ∧
      |dT s| ≤ 2*(3/2 : ℝ)^S.card*(∑ i ∈ S, w i) ∧
      |dST| ≤ 12*(S.card : ℝ)*(3/2 : ℝ)^S.card*(∑ i ∈ S, w i) := by
  induction S using Finset.induction_on with
  | empty =>
      refine ⟨0, 0, fun _ => 0, ?_, ?_, hasDerivAt_const s 0, ?_⟩
      · simpa using hasDerivAt_const s (1 : ℝ)
      · intro u; simpa using hasDerivAt_const t (1 : ℝ)
      · simp
  | @insert i S hi ih =>
      obtain ⟨dS, dST, dT, hS, hT, hST, hP, hdS, hdT, hdST⟩ :=
        ih (fun j hj => hbound j (Finset.mem_insert_of_mem hj))
      obtain ⟨hb, hbS, hbT, hbST⟩ := hbound i (Finset.mem_insert_self _ _)
      let P := fun u => ∏ j ∈ S, f j u t
      let D := fun u => fT i u*P u + f i u t*dT u
      refine ⟨fS i s t*P s+f i s t*dS,
        (fST i s*P s+fT i s*dS)+(fS i s t*dT s+f i s t*dST), D, ?_, ?_, ?_, ?_⟩
      · simpa only [Finset.prod_insert hi, Pi.mul_apply, P] using (hfS i).fun_mul hS
      · intro u
        simpa only [Finset.prod_insert hi, D, P, Pi.mul_apply] using (hfT i u).fun_mul (hT u)
      · exact ((hfST i).mul hS).add ((hfS i).fun_mul hST)
      · have hwi := hw i
        have hsum : 0 ≤ ∑ j ∈ S, w j := Finset.sum_nonneg (fun j _ => hw j)
        simp only [Finset.card_insert_of_notMem hi, Nat.cast_add, Nat.cast_one,
          Finset.prod_insert hi, Finset.sum_insert hi, pow_succ]
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [abs_mul]
          calc
            _ ≤ (3/2)*(3/2 : ℝ)^S.card := mul_le_mul hb hP (abs_nonneg _) (by norm_num)
            _ = _ := by ring
        · calc
            _ ≤ |fS i s t| *|P s|+|f i s t| *|dS| := by
              simpa only [abs_mul] using abs_add_le (fS i s t*P s) (f i s t*dS)
            _ ≤ (6*(3/2))*(3/2 : ℝ)^S.card+(3/2)*(6*(S.card : ℝ)*(3/2 : ℝ)^S.card) := by
              gcongr
            _ = _ := by ring
        · dsimp [D]
          calc
            _ ≤ |fT i s| *|P s|+|f i s t| *|dT s| := by
              simpa only [abs_mul] using abs_add_le (fT i s*P s) (f i s t*dT s)
            _ ≤ (2*(3/2)*w i)*(3/2 : ℝ)^S.card+
                (3/2)*(2*(3/2 : ℝ)^S.card*(∑ j ∈ S, w j)) := by gcongr <;> positivity
            _ = _ := by ring
        · calc
            _ ≤ (|fST i s| *|P s|+|fT i s| *|dS|)+
                (|fS i s t| *|dT s|+|f i s t| *|dST|) := by
              exact (abs_add_le _ _).trans (add_le_add
                (by simpa only [abs_mul] using abs_add_le (fST i s*P s) (fT i s*dS))
                (by simpa only [abs_mul] using abs_add_le (fS i s t*dT s) (f i s t*dST)))
            _ ≤ ((12*(3/2)*w i)*(3/2 : ℝ)^S.card+
                (2*(3/2)*w i)*(6*(S.card : ℝ)*(3/2 : ℝ)^S.card))+
                ((6*(3/2))*(2*(3/2 : ℝ)^S.card*(∑ j ∈ S, w j))+
                (3/2)*(12*(S.card : ℝ)*(3/2 : ℝ)^S.card*(∑ j ∈ S, w j))) := by gcongr <;> positivity
            _ = _ := by ring

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
