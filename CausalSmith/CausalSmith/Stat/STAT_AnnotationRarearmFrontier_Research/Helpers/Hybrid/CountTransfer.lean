module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Hybrid.CanonicalRate

/-!
Transfer from independent count families to the canonical four-count product law.
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

/-- [Under the stated inputs and conditions](hyp:d,Om,mu,X,hX,hind), Grouping four independent counts in each cell gives the product of their
four marginal laws, jointly over all cells.  This gives [the stated result](goal).-/
-- @node: hybrid_four_count_product_law
lemma hybrid_four_count_product_law {d : Nat} {Om : Type} [MeasurableSpace Om]
    (mu : Measure Om) [IsProbabilityMeasure mu] (X : Fin 4 × Fin d → Om → Nat)
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X mu) :
    mu.map (fun om j => (X (0,j) om, X (1,j) om, X (2,j) om, X (3,j) om)) =
      Measure.pi (fun j => (mu.map (X (0,j))).prod
        ((mu.map (X (1,j))).prod ((mu.map (X (2,j))).prod (mu.map (X (3,j)))))) := by
  classical
  apply Measure.ext_of_singleton
  intro z
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton z)]
  have hset : (fun om j => (X (0,j) om, X (1,j) om, X (2,j) om, X (3,j) om)) ⁻¹' {z} =
      ⋂ i ∈ (Finset.univ : Finset (Fin 4 × Fin d)), X i ⁻¹'
        {if i.1 = 0 then (z i.2).1 else if i.1 = 1 then (z i.2).2.1
          else if i.1 = 2 then (z i.2).2.2.1 else (z i.2).2.2.2} := by
    ext om
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter,
      Finset.mem_univ, forall_const]
    constructor
    · intro h i
      rw [← h]
      rcases i with ⟨i,j⟩
      fin_cases i <;> simp
    · intro h
      funext j
      exact Prod.ext (by simpa using h (0,j))
        (Prod.ext (by simpa using h (1,j))
          (Prod.ext (by simpa using h (2,j)) (by simpa using h (3,j))))
  rw [hset, hind.measure_inter_preimage_eq_mul Finset.univ (fun _ _ => measurableSet_singleton _)]
  have hpre (i : Fin 4 × Fin d) (k : Nat) :
      mu (X i ⁻¹' {k}) = (mu.map (X i)) {k} :=
    (Measure.map_apply (hX i) (measurableSet_singleton k)).symm
  simp_rw [hpre]
  have hz : ({z} : Set (Fin d → Nat × (Nat × Nat × Nat))) =
      Set.univ.pi (fun j => {z j}) := by ext y; simp [funext_iff]
  rw [hz, Measure.pi_pi]
  simp only [Fintype.prod_prod_type]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro j _
  rw [show ({z j} : Set (Nat × (Nat × Nat × Nat))) =
    {(z j).1} ×ˢ ({(z j).2.1} ×ˢ ({(z j).2.2.1} ×ˢ {(z j).2.2.2})) by ext y; simp]
  simp only [Measure.prod_prod, Fin.prod_univ_four, Fin.reduceEq, if_true, if_false]
  ac_rfl

end CausalSmith.Stat.AnnotationRarearmFrontier
