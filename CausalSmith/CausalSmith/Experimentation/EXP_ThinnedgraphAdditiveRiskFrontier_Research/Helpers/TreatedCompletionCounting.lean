module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.PosteriorCompletionLaw

/-!
# Treated-label fibers of compatible completions

Splitting the original hidden labels into treated and untreated subtypes gives
exact multiplicities of completed row treatment counts.
-/

@[expose] public section
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance 1] Classical.propDecidable

/-- Row counts on the treated original labels of a finite word. -/
-- @node: treatedRowCount
def treatedRowCount {ι : Type*} [Fintype ι] (p : ι → Prop) [DecidablePred p] (g : ι → Fin B)
    (ℓ : Fin B) : ℕ :=
  (Finset.univ.filter (fun j : {j // p j} => g j.1 = ℓ)).card

/-- Splitting a row into treated and untreated labels preserves its full cardinality.  [For the stated data and conditions](hyp:ι,p,g,ℓ), [the stated conclusion holds](goal). -/
-- @node: rowCount_split_treatment
lemma rowCount_split_treatment {ι : Type*} [Fintype ι] (p : ι → Prop) [DecidablePred p]
    (g : ι → Fin B) (ℓ : Fin B) :
    treatedRowCount p g ℓ + treatedRowCount (fun j => ¬ p j) g ℓ =
      (Finset.univ.filter (fun j => g j = ℓ)).card := by
  let e : {j : ι // g j = ℓ} ≃
      {j : {j // p j} // g j.1 = ℓ} ⊕ {j : {j // ¬ p j} // g j.1 = ℓ} := {
    toFun := fun j => if hj : p j.1 then Sum.inl ⟨⟨j.1,hj⟩,j.2⟩
      else Sum.inr ⟨⟨j.1,hj⟩,j.2⟩
    invFun := fun j => Sum.elim (fun a => ⟨a.1.1,a.2⟩) (fun a => ⟨a.1.1,a.2⟩) j
    left_inv := by intro j; dsimp only; split_ifs <;> rfl
    right_inv := by
      intro j
      cases j with
      | inl j => simp [j.1.2]
      | inr j => simp [j.1.2] }
  simpa only [Fintype.card_sum, Fintype.card_subtype, treatedRowCount]
    using (Fintype.card_congr e).symm

/-- A fixed treated-count fiber splits bijectively into words on treated and untreated
original labels. No label permutations are identified or discarded. -/
-- @node: treatedRowFiberEquiv
def treatedRowFiberEquiv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → Prop) [DecidablePred p] (u k : Fin B → ℕ) (hk : ∀ ℓ, k ℓ ≤ u ℓ) :
    {g : FiniteRowWord ι B u // ∀ ℓ, treatedRowCount p g.1 ℓ = k ℓ} ≃
      FiniteRowWord {j // p j} B k ×
        FiniteRowWord {j // ¬ p j} B (fun ℓ => u ℓ - k ℓ) where
  toFun g := (⟨fun j => g.1.1 j.1, g.2⟩,
    ⟨fun j => g.1.1 j.1, fun ℓ => by
      have hc := rowCount_split_treatment p g.1.1 ℓ
      rw [g.2 ℓ, g.1.2 ℓ] at hc
      change treatedRowCount (fun j => ¬ p j) g.1.1 ℓ = u ℓ - k ℓ
      omega⟩)
  invFun g :=
    let f := (Equiv.piEquivPiSubtypeProd p (fun _ => Fin B)).symm (g.1.1,g.2.1)
    have ht (ℓ) : treatedRowCount p f ℓ = k ℓ := by
      unfold treatedRowCount
      have he (j : {j // p j}) : f j.1 = g.1.1 j := dif_pos j.2
      simpa only [he] using g.1.2 ℓ
    have hn (ℓ) : treatedRowCount (fun j => ¬ p j) f ℓ = u ℓ - k ℓ := by
      unfold treatedRowCount
      have he (j : {j // ¬ p j}) : f j.1 = g.2.1 j := dif_neg j.2
      simpa only [he] using g.2.2 ℓ
    ⟨⟨f, fun ℓ => by
      have hc := rowCount_split_treatment p f ℓ
      rw [ht ℓ, hn ℓ] at hc
      have := hk ℓ
      omega⟩, ht⟩
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    funext j
    change (if hj : p j then g.1.1 j else g.1.1 j) = g.1.1 j
    split_ifs <;> rfl
  right_inv g := by
    apply Prod.ext <;> apply Subtype.ext <;> funext j
    · exact dif_pos j.2
    · exact dif_neg j.2

/-- Counts across rows exhaust the treated original labels.  [For the stated data and conditions](hyp:ι,p,g), [the stated conclusion holds](goal). -/
-- @node: treatedRowCount_sum
lemma treatedRowCount_sum {ι : Type*} [Fintype ι] (p : ι → Prop) [DecidablePred p]
    (g : ι → Fin B) : ∑ ℓ, treatedRowCount p g ℓ = Fintype.card {j // p j} := by
  have hc := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset {j // p j}) (Finset.univ : Finset (Fin B))
    (fun j => g j.1)
  simpa [treatedRowCount] using hc

/-- The fixed treated-count fiber has the product of the two multinomial counts.  [For the stated data and conditions](hyp:ι,p,u,k,hk,hu,hkt), [the stated conclusion holds](goal). -/
-- @node: treatedRowFiber_card_mul_factorials
lemma treatedRowFiber_card_mul_factorials {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → Prop) [DecidablePred p] (u k : Fin B → ℕ) (hk : ∀ ℓ, k ℓ ≤ u ℓ)
    (hu : ∑ ℓ, u ℓ = Fintype.card ι)
    (hkt : ∑ ℓ, k ℓ = Fintype.card {j // p j}) :
    Fintype.card {g : FiniteRowWord ι B u // ∀ ℓ, treatedRowCount p g.1 ℓ = k ℓ} *
      ((∏ ℓ, (k ℓ).factorial) * (∏ ℓ, (u ℓ - k ℓ).factorial)) =
        (Fintype.card {j // p j}).factorial * (Fintype.card {j // ¬ p j}).factorial := by
  have hc : Fintype.card {j // p j} + Fintype.card {j // ¬ p j} = Fintype.card ι := by
    simpa only [Fintype.card_subtype, Finset.card_univ] using
      Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset ι)) p
  have hkn : ∑ ℓ, (u ℓ - k ℓ) = Fintype.card {j // ¬ p j} := by
    have he : (∑ ℓ, k ℓ) + (∑ ℓ, (u ℓ - k ℓ)) = ∑ ℓ, u ℓ := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro ℓ _
      have := hk ℓ
      omega
    omega
  rw [Fintype.card_congr (treatedRowFiberEquiv p u k hk), Fintype.card_prod]
  calc
    _ = (Fintype.card (FiniteRowWord {j // p j} B k) * ∏ ℓ, (k ℓ).factorial) *
        (Fintype.card (FiniteRowWord {j // ¬ p j} B (fun ℓ => u ℓ - k ℓ)) *
          ∏ ℓ, (u ℓ - k ℓ).factorial) := by ac_rfl
    _ = _ := by rw [finiteRowWord_card_mul_factorial B k hkt,
      finiteRowWord_card_mul_factorial B _ hkn]

/-- The treated-count fiber multiplicity relative to all labeled words is the
hypergeometric weight, including zero treated or zero hidden labels.  [For the stated data and conditions](hyp:ι,p,u,k,hk,hu,hkt), [the stated conclusion holds](goal). -/
-- @node: treatedRowFiber_hypergeometric_weight
lemma treatedRowFiber_hypergeometric_weight {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → Prop) [DecidablePred p] (u k : Fin B → ℕ) (hk : ∀ ℓ, k ℓ ≤ u ℓ)
    (hu : ∑ ℓ, u ℓ = Fintype.card ι)
    (hkt : ∑ ℓ, k ℓ = Fintype.card {j // p j}) :
    (Fintype.card {g : FiniteRowWord ι B u // ∀ ℓ, treatedRowCount p g.1 ℓ = k ℓ} : ℝ≥0∞) /
      Fintype.card (FiniteRowWord ι B u) =
        (∏ ℓ, ((u ℓ).choose (k ℓ) : ℝ≥0∞)) /
          (Fintype.card ι).choose (Fintype.card {j // p j}) := by
  let A := Fintype.card {g : FiniteRowWord ι B u // ∀ ℓ, treatedRowCount p g.1 ℓ = k ℓ}
  let W := Fintype.card (FiniteRowWord ι B u)
  let P := (∏ ℓ, (k ℓ).factorial) * (∏ ℓ, (u ℓ - k ℓ).factorial)
  let R := ∏ ℓ, (u ℓ).choose (k ℓ)
  let C := (Fintype.card ι).choose (Fintype.card {j // p j})
  have hc : Fintype.card {j // p j} + Fintype.card {j // ¬ p j} = Fintype.card ι := by
    simpa only [Fintype.card_subtype, Finset.card_univ] using
      Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset ι)) p
  have ha : A * P =
      (Fintype.card {j // p j}).factorial * (Fintype.card {j // ¬ p j}).factorial :=
    treatedRowFiber_card_mul_factorials p u k hk hu hkt
  have hw : W * (∏ ℓ, (u ℓ).factorial) = (Fintype.card ι).factorial :=
    finiteRowWord_card_mul_factorial B u hu
  have hr : R * P = ∏ ℓ, (u ℓ).factorial := by
    dsimp only [R, P]
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro ℓ _
    simpa only [Nat.mul_assoc] using Nat.choose_mul_factorial_mul_factorial (hk ℓ)
  have hchoose : C *
      ((Fintype.card {j // p j}).factorial * (Fintype.card {j // ¬ p j}).factorial) =
        (Fintype.card ι).factorial := by
    have he : Fintype.card ι - Fintype.card {j // p j} = Fintype.card {j // ¬ p j} := by omega
    simpa only [C, he, Nat.mul_assoc] using
      Nat.choose_mul_factorial_mul_factorial
        (show Fintype.card {j // p j} ≤ Fintype.card ι by omega)
  have hp : P ≠ 0 := by
    apply Nat.mul_ne_zero <;>
      exact Finset.prod_ne_zero_iff.mpr (fun ℓ _ => Nat.factorial_ne_zero _)
  have hw0 : W ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hw
    exact Nat.factorial_ne_zero _ hw.symm
  have hc0 : C ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hchoose
    exact Nat.factorial_ne_zero _ hchoose.symm
  have hid : A * C = R * W := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hp)
    calc
      A * C * P = C * (A * P) := by ac_rfl
      _ = (Fintype.card ι).factorial := by rw [ha, hchoose]
      _ = W * (R * P) := by rw [hr, hw]
      _ = R * W * P := by ac_rfl
  have hid' : (A : ℝ≥0∞) * C = (R : ℝ≥0∞) * W := by exact_mod_cast hid
  change (A : ℝ≥0∞) / W = _
  rw [← Nat.cast_prod]
  change (A : ℝ≥0∞) / W = (R : ℝ≥0∞) / C
  apply (ENNReal.div_eq_div_iff (by exact_mod_cast hc0) (by finiteness)
    (by exact_mod_cast hw0) (by finiteness)).mpr
  simpa only [mul_comm] using hid'

/-- The completed row counts are bounded by their row capacities. -/
-- @node: finiteRowAllocation
def finiteRowAllocation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → Prop) [DecidablePred p] (u : Fin B → ℕ) (g : FiniteRowWord ι B u) :
    ∀ ℓ, Fin (u ℓ + 1) := fun ℓ =>
  ⟨treatedRowCount p g.1 ℓ, by
    have hc := rowCount_split_treatment p g.1 ℓ
    rw [g.2 ℓ] at hc
    omega⟩

/-- Averaging any function of the completed treated counts over labeled words gives
exact hypergeometric weights. This is the finite posterior averaging identity.  [For the stated data and conditions](hyp:ι,p,u,hu,F), [the stated conclusion holds](goal). -/
-- @node: finiteRowWord_average_eq_treated_counts
lemma finiteRowWord_average_eq_treated_counts {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → Prop) [DecidablePred p] (u : Fin B → ℕ)
    (hu : ∑ ℓ, u ℓ = Fintype.card ι)
    (F : (∀ ℓ, Fin (u ℓ + 1)) → ℝ≥0∞) :
    (Fintype.card (FiniteRowWord ι B u) : ℝ≥0∞)⁻¹ *
      (∑ g : FiniteRowWord ι B u, F (finiteRowAllocation p u g)) =
    ∑ k : ∀ ℓ, Fin (u ℓ + 1),
      if Fintype.card {j // p j} = ∑ ℓ, (k ℓ).val then
        ((∏ ℓ, ((u ℓ).choose (k ℓ).val : ℝ≥0∞)) /
          (Fintype.card ι).choose (Fintype.card {j // p j})) * F k else 0 := by
  let a := finiteRowAllocation p u
  have hsplit := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (FiniteRowWord ι B u)))
    (t := (Finset.univ : Finset (∀ ℓ, Fin (u ℓ + 1))))
    (g := a) (f := fun g => F (a g)) (fun _ _ => Finset.mem_univ _)
  rw [← hsplit, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have he (g : FiniteRowWord ι B u) :
      a g = k ↔ ∀ ℓ, treatedRowCount p g.1 ℓ = (k ℓ).val := by
    constructor
    · intro h ℓ
      exact congrArg (fun a => (a ℓ).val) h
    · intro h
      funext ℓ
      exact Fin.ext (h ℓ)
  have hf : (∑ g ∈ Finset.univ.filter (fun g => a g = k), F (a g)) =
      ((Finset.univ.filter (fun g => a g = k)).card : ℝ≥0∞) * F k := by
    have heq : (∑ g ∈ Finset.univ.filter (fun g => a g = k), F (a g)) =
        ∑ g ∈ Finset.univ.filter (fun g => a g = k), F k := by
      apply Finset.sum_congr rfl
      intro g hg
      rw [(Finset.mem_filter.mp hg).2]
    rw [heq, Finset.sum_const, nsmul_eq_mul]
  rw [hf]
  have hcard : (Finset.univ.filter (fun g => a g = k)).card =
      Fintype.card {g : FiniteRowWord ι B u //
        ∀ ℓ, treatedRowCount p g.1 ℓ = (k ℓ).val} := by
    simp only [he, Fintype.card_subtype]
  rw [hcard, ← mul_assoc]
  by_cases hkt : Fintype.card {j // p j} = ∑ ℓ, (k ℓ).val
  · rw [if_pos hkt]
    congr 1
    rw [mul_comm, ← div_eq_mul_inv]
    exact treatedRowFiber_hypergeometric_weight p u (fun ℓ => (k ℓ).val)
      (fun ℓ => Nat.le_of_lt_succ (k ℓ).isLt) hu hkt.symm
  · rw [if_neg hkt]
    have hz : Fintype.card {g : FiniteRowWord ι B u //
        ∀ ℓ, treatedRowCount p g.1 ℓ = (k ℓ).val} = 0 := by
      rw [Fintype.card_eq_zero_iff]
      refine ⟨fun g => hkt ?_⟩
      have ht := treatedRowCount_sum p g.1.1
      simpa only [g.2] using ht.symm
    rw [hz]
    simp

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
