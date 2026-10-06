module
public import Mathlib

/-!
# Compact finite-dimensional convex hulls

The joint target and moment features live in a finite-dimensional real vector
space. Compactness of their convex hull supplies attained extrema and allows
strong separation in the constrained moment argument.
-/

public section

namespace Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate

/- Use Carathéodory's theorem to express each hull point with at most
  `finrank ℝ E + 1` points of `S`. The bounded-length simplex of weights
  and the finite product of `S` are compact, and the barycenter map is
  continuous. Mathlib's `Set.Finite.isCompact_convexHull` handles finite
  sets only; it does not apply directly to the feature range. -/

/-- The [compact set](hyp:hS) in a finite-dimensional real normed space has [a compact convex hull](goal). -/
theorem isCompact_convexHull_finiteDimensional
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {S : Set E} (hS : IsCompact S) :
    IsCompact (convexHull ℝ S) := by
  classical
  let K (n : ℕ) : Set E :=
    Set.range (fun p : (stdSimplex ℝ (Fin n)) × (Fin n → S) =>
      ∑ i, (p.1 : Fin n → ℝ) i • (p.2 i : E))
  have hK (n : ℕ) : IsCompact (K n) := by
    have : CompactSpace S := isCompact_iff_compactSpace.mp hS
    have : CompactSpace (stdSimplex ℝ (Fin n)) :=
      isCompact_iff_compactSpace.mp (isCompact_stdSimplex ℝ (Fin n))
    have hc : Continuous (fun p : (stdSimplex ℝ (Fin n)) × (Fin n → S) =>
        ∑ i, (p.1 : Fin n → ℝ) i • (p.2 i : E)) := by
      apply continuous_finsetSum
      intro i hi
      exact ((continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)).smul
        (continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd))
    simpa only [K, Set.image_univ] using (isCompact_univ.image hc)
  have hEq : convexHull ℝ S = ⋃ n ∈ Set.Iic (Module.finrank ℝ E + 1), K n := by
    apply Set.Subset.antisymm
    · intro x hx
      let t := Caratheodory.minCardFinsetOfMemConvexHull hx
      have ht : (t : Set E) ⊆ S :=
        Caratheodory.minCardFinsetOfMemConvexHull_subseteq hx
      have hcard : t.card ≤ Module.finrank ℝ E + 1 := by
        have h :=
          (Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hx).card_le_finrank_succ
        rw [Fintype.card_coe] at h
        exact h.trans (Nat.add_le_add_right
          (Submodule.finrank_le (vectorSpan ℝ (Set.range ((↑) : t → E)))) 1)
      have hx' : x ∈ convexHull ℝ (t : Set E) :=
        Caratheodory.mem_minCardFinsetOfMemConvexHull hx
      obtain ⟨w, hw0, hw1, hsum⟩ := Finset.mem_convexHull'.mp hx'
      let e : Fin t.card ≃ t := (Finset.equivFin t).symm
      let v : Fin t.card → ℝ := fun i => w (e i : E)
      let z : Fin t.card → S := fun i => ⟨(e i : E), ht (e i).property⟩
      have hv0 : ∀ i, 0 ≤ v i := fun i => hw0 _ (e i).property
      have hv1 : ∑ i, v i = 1 := by
        calc
          ∑ i, v i = ∑ y : t, w (y : E) := by
            simpa only [v] using (Equiv.sum_comp e (fun y : t => w (y : E)))
          _ = ∑ y ∈ t, w y := Finset.sum_attach t w
          _ = 1 := hw1
      have hvsum : (∑ i, v i • (z i : E)) = x := by
        calc
          ∑ i, v i • (z i : E) = ∑ y : t, w (y : E) • (y : E) := by
            simpa only [v, z] using
              (Equiv.sum_comp e (fun y : t => w (y : E) • (y : E)))
          _ = ∑ y ∈ t, w y • y := by
            simpa only [Finset.univ_eq_attach] using
              (Finset.sum_attach t (fun y => w y • y))
          _ = x := hsum
      have hv : v ∈ stdSimplex ℝ (Fin t.card) := ⟨hv0, hv1⟩
      simp only [Set.mem_iUnion, Set.mem_Iic, K, Set.mem_range]
      exact ⟨t.card, hcard, ⟨⟨v, hv⟩, z⟩, hvsum⟩
    · simp only [Set.iUnion_subset_iff]
      intro n hn x hx
      rcases hx with ⟨⟨v, z⟩, rfl⟩
      exact mem_convexHull_of_exists_fintype (v : Fin n → ℝ) (fun i => (z i : E))
        v.property.1 v.property.2 (fun i => (z i).property) rfl
  rw [hEq]
  exact (Set.finite_Iic _).isCompact_biUnion (fun n hn => hK n)

end Causalean.Stat.Minimax.Mixture.MomentMatched.BoundedMultivariate
