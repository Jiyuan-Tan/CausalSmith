module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.CompatibleCompletions
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.Words

/-!
# Exact multiplicities of labeled hidden completions

The multinomial word-fiber theorem counts capacity-constrained allocations of
original hidden source labels. The counts include all compatible partitions,
rather than unlabeled or reduced-information observations.
-/

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- Functions with specified row-fiber sizes on an arbitrary finite label type. -/
-- @node: FiniteRowWord
abbrev FiniteRowWord (ι : Type*) [Fintype ι] [DecidableEq ι] (B : ℕ) (u : Fin B → ℕ) :=
  {g : ι → Fin B // ∀ ℓ, (Finset.univ.filter (fun j => g j = ℓ)).card = u ℓ}

/-- Reindexing original labels preserves every row-fiber cardinality.  [For the stated data and conditions](hyp:ι,κ,B,e,g,ℓ), [the stated conclusion holds](goal). -/
-- @node: row_fiber_card_equiv
lemma row_fiber_card_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    {B : ℕ} (e : ι ≃ κ) (g : κ → Fin B) (ℓ : Fin B) :
    (Finset.univ.filter (fun j : ι => g (e j) = ℓ)).card =
      (Finset.univ.filter (fun j : κ => g j = ℓ)).card := by
  classical
  simpa only [Fintype.card_subtype] using
    Fintype.card_congr (e.subtypeEquiv (p := fun j => g (e j) = ℓ)
      (q := fun j => g j = ℓ) (fun _ => Iff.rfl))

/-- Capacity-constrained words are invariant under bijections of the original labels. -/
-- @node: finiteRowWordEquiv
def finiteRowWordEquiv {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    {B : ℕ} (e : ι ≃ κ) (u : Fin B → ℕ) :
    FiniteRowWord ι B u ≃ FiniteRowWord κ B u where
  toFun g := ⟨fun j => g.1 (e.symm j), fun ℓ =>
    (row_fiber_card_equiv e.symm g.1 ℓ).trans (g.2 ℓ)⟩
  invFun g := ⟨fun j => g.1 (e j), fun ℓ =>
    (row_fiber_card_equiv e g.1 ℓ).trans (g.2 ℓ)⟩
  left_inv g := by apply Subtype.ext; funext j; simp
  right_inv g := by apply Subtype.ext; funext j; simp

/-- The exact multinomial count on an arbitrary finite original-label type, with no division
or rounding ambiguity: the count times the row factorials is the total factorial.  [For the stated data and conditions](hyp:ι,B,u,hu), [the stated conclusion holds](goal). -/
-- @node: finiteRowWord_card_mul_factorial
lemma finiteRowWord_card_mul_factorial {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : ℕ) (u : Fin B → ℕ) (hu : ∑ ℓ, u ℓ = Fintype.card ι) :
    Fintype.card (FiniteRowWord ι B u) * (∏ ℓ, (u ℓ).factorial) =
      (Fintype.card ι).factorial := by
  let e := finiteRowWordEquiv (Fintype.equivFin ι) u
  rw [Fintype.card_congr e]
  have hc := Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.word_fiber_card_mul_factorial
    u hu
  simpa [FiniteRowWord, Fintype.card_subtype,
    Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.wordFiber,
    Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.coordCount,
    Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.multiFactorial, funext_iff] using hc

/-- Counting each hidden original source in its unique completed row gives total capacity.  [For the stated data and conditions](hyp:n,B,d,hfit,H,s), [the stated conclusion holds](goal). -/
-- @node: hiddenSource_card
lemma hiddenSource_card (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (H : OffDiag (Fin n) → Bool) (s : CompatiblePartition n B d H) :
    Fintype.card (HiddenSource n B d H) = undiscovered n B d H := by
  have hc := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (HiddenSource n B d H)) (Finset.univ : Finset (Fin B))
    (fun j => s.1.1 j.1)
  simpa [compatiblePartition_hidden_fiber_card n B d hfit H s, undiscovered] using hc.symm

/-- The exact count of compatible partitions times the remaining row factorials is M!.
This is the common labeled-completion denominator, including M = 0.  [For the stated data and conditions](hyp:n,B,d,hfit,H,s), [the stated conclusion holds](goal). -/
-- @node: compatiblePartition_card_mul_factorial
lemma compatiblePartition_card_mul_factorial (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (H : OffDiag (Fin n) → Bool) (s : CompatiblePartition n B d H) :
    Fintype.card (CompatiblePartition n B d H) *
      (∏ ℓ, (capacity n B d H ℓ).factorial) = (undiscovered n B d H).factorial := by
  classical
  rw [Fintype.card_congr (compatiblePartitionEquivHiddenCompletion n B d hfit H s)]
  have hc := finiteRowWord_card_mul_factorial (ι := HiddenSource n B d H) B
    (capacity n B d H) (hiddenSource_card n B d hfit H s).symm
  simpa only [hiddenSource_card n B d hfit H s] using hc

/-- The uniform posterior atom is the product of row factorials divided by M!, with
all original hidden labels counted and the zero-capacity endpoint included.  [For the stated data and conditions](hyp:n,B,d,hfit,H,s), [the stated conclusion holds](goal). -/
-- @node: hiddenCompletion_inverse_card
lemma hiddenCompletion_inverse_card (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (H : OffDiag (Fin n) → Bool) (s : CompatiblePartition n B d H) :
    (Fintype.card (HiddenCompletion n B d H) : ℝ≥0∞)⁻¹ =
      (∏ ℓ, (capacity n B d H ℓ).factorial : ℕ) / (undiscovered n B d H).factorial := by
  have hcount := compatiblePartition_card_mul_factorial n B d hfit H s
  rw [Fintype.card_congr (compatiblePartitionEquivHiddenCompletion n B d hfit H s)] at hcount
  have hc : (Fintype.card (HiddenCompletion n B d H) : ℝ≥0∞) *
      (∏ ℓ, (capacity n B d H ℓ).factorial : ℕ) = (undiscovered n B d H).factorial := by
    exact_mod_cast hcount
  have hp : (∏ ℓ, (capacity n B d H ℓ).factorial : ℕ) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun ℓ _ => Nat.factorial_ne_zero _)
  rw [← hc]
  simpa only [mul_one, one_mul, one_div] using
    (ENNReal.mul_div_mul_right 1 (Fintype.card (HiddenCompletion n B d H) : ℝ≥0∞)
      (by exact_mod_cast hp) (by finiteness)).symm

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
