module

public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.TCompatibilityCompletion

/-! Sharp entries of completion matrices. -/

public section

namespace CausalSmith.ExactID.EIDCountshiftUnlabeledMatching

/-- A new edge from an uncovered column cannot close a path already forced by
the observed columns. -/
-- @node: forced_path_completion_zero
lemma forced_path_completion_zero {p q : ℕ} (v : Fin q → Fin p → ℝ)
    (f : Fin q ↪ Fin p) (B : Matrix (Fin p) (Fin p) ℝ)
    (hf : f ∈ assignmentFiber v) (hB : B ∈ completionFiberAt v f) {i u : Fin p}
    (hiu : i ≠ u) (hpath : Relation.TransGen (Hf v f) i u) :
    B i u = 0 := by
  by_contra hne
  apply hB.2.2 u
  have hforced : ∀ a b, Hf v f a b → a ≠ b ∧ B b a ≠ 0 := by
    intro a b hab
    obtain ⟨g, hga, hb, hba⟩ := hab
    subst a
    refine ⟨hba.symm, ?_⟩
    rw [hB.1 g b]
    have hbg : v g b ≠ 0 := by simpa [support] using hb
    have hag : v g (f g) ≠ 0 := by simpa [support] using hf.1 g
    exact div_ne_zero hbg hag
  have hpathB : Relation.TransGen
      (fun a b => a ≠ b ∧ B b a ≠ 0) i u :=
    hpath.lift id (by intro a b hab; exact hforced a b hab)
  exact (Relation.TransGen.single ⟨hiu.symm, hne⟩).trans hpathB

/-- The covered columns and identity columns elsewhere give a feasible completion. -/
-- @node: canonical_completion_exists
lemma canonical_completion_exists {p q : ℕ} (v : Fin q → Fin p → ℝ)
    (f : Fin q ↪ Fin p) (hf : f ∈ assignmentFiber v) :
    ∃ B ∈ completionFiberAt v f,
      (∀ u, u ∉ Set.range f → ∀ i, i ≠ u → B i u = 0) ∧
      (∀ i j, i ≠ j ∧ B j i ≠ 0 → Hf v f i j) := by
  classical
  let B : Matrix (Fin p) (Fin p) ℝ := Matrix.of fun i j =>
    if h : j ∈ Set.range f then
      v (Classical.choose h) i / v (Classical.choose h) j
    else if i = j then 1 else 0
  have hcol (g : Fin q) (i : Fin p) :
      B i (f g) = v g i / v g (f g) := by
    have h : f g ∈ Set.range f := ⟨g, rfl⟩
    simp only [B, Matrix.of_apply, dif_pos h]
    have heq : Classical.choose h = g :=
      f.injective (Classical.choose_spec h)
    rw [heq]
  have hdiag (i : Fin p) : B i i = 1 := by
    by_cases h : i ∈ Set.range f
    · obtain ⟨g, rfl⟩ := h
      rw [hcol]
      exact div_self (by simpa [support] using hf.1 g)
    · change (if h' : i ∈ Set.range f then _ else if i = i then 1 else 0) = 1
      rw [dif_neg h]
      simp
  have hedge (i j : Fin p) (hij : i ≠ j ∧ B j i ≠ 0) :
      Hf v f i j := by
    by_cases h : i ∈ Set.range f
    · let g := Classical.choose h
      have hfg : f g = i := Classical.choose_spec h
      have hj : v g j ≠ 0 := by
        intro hz
        apply hij.2
        rw [← hfg, hcol, hz]
        simp
      exact ⟨g, hfg, by simpa [support] using hj, hij.1.symm⟩
    · have hzero : B j i = 0 := by
        change (if h' : i ∈ Set.range f then _ else if j = i then 1 else 0) = 0
        rw [dif_neg h]
        simp [hij.1.symm]
      exact False.elim (hij.2 hzero)
  refine ⟨B, ⟨hcol, hdiag, ?_⟩, ?_, hedge⟩
  · intro i hcycle
    exact hf.2 i (hcycle.lift id (by intro a b hab; exact hedge a b hab))
  · intro u hu i hiu
    change (if h : u ∈ Set.range f then _ else if i = u then 1 else 0) = 0
    rw [dif_neg hu]
    simp [hiu]

/-- Adding a forward edge preserves acyclicity when no return path exists. -/
-- @node: acyclic_add_edge_of_no_return
lemma acyclic_add_edge_of_no_return {α : Type*} (R : α → α → Prop)
    (u i : α) (hacyc : ∀ x, ¬ Relation.TransGen R x x)
    (hui : u ≠ i) (hnpath : ¬ Relation.TransGen R i u) :
    ∀ x, ¬ Relation.TransGen (fun a b => R a b ∨ (a = u ∧ b = i)) x x := by
  let S : α → α → Prop := fun a b => R a b ∨ (a = u ∧ b = i)
  have hdecomp {a b : α} (h : Relation.TransGen S a b) :
      Relation.TransGen R a b ∨
        Relation.ReflTransGen R a u ∧ Relation.ReflTransGen R i b := by
    induction h with
    | single h =>
        rcases h with hR | ⟨rfl, rfl⟩
        · exact Or.inl (Relation.TransGen.single hR)
        · exact Or.inr ⟨.refl, .refl⟩
    | tail h hab ih =>
        rcases ih with hR | ⟨hau, hib⟩
        · rcases hab with hbc | ⟨hbu, hci⟩
          · exact Or.inl (hR.tail hbc)
          · exact Or.inr ⟨hbu ▸ hR.to_reflTransGen, hci ▸ .refl⟩
        · rcases hab with hbc | ⟨hbu, _⟩
          · exact Or.inr ⟨hau, hib.trans (.single hbc)⟩
          · have hbad : Relation.TransGen R i u := by
              have hib' : Relation.ReflTransGen R i u := hbu ▸ hib
              rcases (Relation.reflTransGen_iff_eq_or_transGen).mp hib' with hEq | hpath
              · exact False.elim (hui hEq)
              · exact hpath
            exact False.elim (hnpath hbad)
  intro x hx
  rcases hdecomp hx with hR | ⟨hxu, hix⟩
  · exact hacyc x hR
  · have hixu := hix.trans hxu
    rcases (Relation.reflTransGen_iff_eq_or_transGen).mp hixu with heq | hpath
    · exact hui heq
    · exact hnpath hpath

/-- Every value is realized in an uncovered entry unless its reverse forced path exists. -/
-- @node: free_uncovered_entry_completion
lemma free_uncovered_entry_completion {p q : ℕ} (v : Fin q → Fin p → ℝ)
    (f : Fin q ↪ Fin p) (hf : f ∈ assignmentFiber v)
    {i u : Fin p} (hu : u ∉ Set.range f) (hiu : i ≠ u)
    (hnpath : ¬ Relation.TransGen (Hf v f) i u) (t : ℝ) :
    ∃ B ∈ completionFiberAt v f, B i u = t := by
  classical
  obtain ⟨B₀, hB₀, hzero, hedge₀⟩ := canonical_completion_exists v f hf
  let B : Matrix (Fin p) (Fin p) ℝ := Matrix.of fun a b =>
    if a = i ∧ b = u then t else B₀ a b
  have hentry : B i u = t := by simp [B]
  have hcol (g : Fin q) (a : Fin p) :
      B a (f g) = v g a / v g (f g) := by
    have hne : f g ≠ u := fun heq => hu ⟨g, heq⟩
    have hnot : ¬ (a = i ∧ f g = u) := fun h => hne h.2
    simpa [B, hnot] using hB₀.1 g a
  have hdiag (a : Fin p) : B a a = 1 := by
    have hnot : ¬ (a = i ∧ a = u) := by
      rintro ⟨rfl, heq⟩
      exact hiu heq
    simpa [B, hnot] using hB₀.2.1 a
  have hedge (a b : Fin p) (hab : a ≠ b ∧ B b a ≠ 0) :
      Hf v f a b ∨ (a = u ∧ b = i) := by
    by_cases hspecial : b = i ∧ a = u
    · exact Or.inr ⟨hspecial.2, hspecial.1⟩
    · left
      apply hedge₀ a b
      refine ⟨hab.1, ?_⟩
      simpa [B, hspecial] using hab.2
  refine ⟨B, ⟨hcol, hdiag, ?_⟩, hentry⟩
  intro a hcycle
  apply acyclic_add_edge_of_no_return (Hf v f) u i hf.2 hiu.symm hnpath a
  exact hcycle.lift id (by intro x y hxy; exact hedge x y hxy)

-- @node: prop:entrywise-completion
theorem entrywise_completion {p q : ℕ} (v : Fin q → Fin p → ℝ)
    (f : Fin q ↪ Fin p) (hf : f ∈ assignmentFiber v) :
    (∀ B ∈ completionFiberAt v f,
      ∀ g i, B i (f g) = v g i / v g (f g)) ∧
    (∀ u ∈ uncovered f, ∀ i, i ≠ u →
      ((∀ B ∈ completionFiberAt v f, B i u = 0) ↔
        Relation.TransGen (Hf v f) i u) ∧
      (¬ Relation.TransGen (Hf v f) i u →
        (fun B : Matrix (Fin p) (Fin p) ℝ => B i u) ''
          completionFiberAt v f = Set.univ)) ∧
    completionFiberAt v f =
      ⋃ σ : Equiv.Perm (Fin p),
        ⋃ _ : IsLinearExtension v f σ, triangularFamily v f σ := by
  refine ⟨?_, ?_, ?_⟩
  · intro B hB g i
    exact hB.1 g i
  · intro u hu i hiu
    constructor
    · constructor
      · intro hall
        by_contra hnpath
        have hu' : u ∉ Set.range f := by
          simpa [uncovered] using hu
        obtain ⟨B, hB, hvalue⟩ :=
          free_uncovered_entry_completion v f hf hu' hiu hnpath 1
        have hzero := hall B hB
        linarith
      · intro hpath B hB
        exact forced_path_completion_zero v f B hf hB hiu hpath
    · intro hnpath
      have hu' : u ∉ Set.range f := by
        simpa [uncovered] using hu
      ext t
      simp only [Set.mem_image, Set.mem_univ, iff_true]
      obtain ⟨B, hB, hvalue⟩ :=
        free_uncovered_entry_completion v f hf hu' hiu hnpath t
      exact ⟨B, hB, hvalue⟩
  · classical
    apply Set.Subset.antisymm
    · intro B hB
      let edge : Fin p → Fin p → Prop :=
        fun j k => j ≠ k ∧ B k j ≠ 0
      let G := Causalean.Graph.DAG.ofAcyclic edge hB.2.2
      let ord : LinearOrder (Fin p) :=
        LinearOrder.lift' G.topoOrder G.topoOrder_injective
      let e := @Fintype.orderIsoFinOfCardEq (Fin p) ord (inferInstance) p
        (by simp : Fintype.card (Fin p) = p)
      let σ : Equiv.Perm (Fin p) := e.toEquiv
      have hσ (i j : Fin p) : σ.symm i < σ.symm j ↔ G.topoOrder i < G.topoOrder j := by
        have h := @OrderIso.lt_iff_lt (Fin p) (Fin p)
          (inferInstance) ord.toPreorder e (σ.symm i) (σ.symm j)
        have hi : e (σ.symm i) = i := σ.apply_symm_apply i
        have hj : e (σ.symm j) = j := σ.apply_symm_apply j
        rw [hi, hj] at h
        change (G.topoOrder i < G.topoOrder j) ↔
          (σ.symm i < σ.symm j) at h
        exact h.symm
      simp only [Set.mem_iUnion]
      refine ⟨σ, ?_, ⟨hB, ?_⟩⟩
      · intro a b hab
        apply (hσ a b).mpr
        obtain ⟨g, rfl, hb, hne⟩ := hab
        apply G.topoOrder_lt
        rw [Causalean.Graph.DAG.ofAcyclic_edge]
        refine ⟨hne.symm, ?_⟩
        rw [hB.1 g b]
        have hnum : v g b ≠ 0 := by simpa [support] using hb
        have hden : v g (f g) ≠ 0 := by simpa [support] using hf.1 g
        exact div_ne_zero hnum hden
      · intro i j hij horder
        by_contra hne
        have hedge : G.edge j i := by
          rw [Causalean.Graph.DAG.ofAcyclic_edge]
          exact ⟨hij.symm, hne⟩
        have hlt : σ.symm j < σ.symm i := (hσ j i).mpr (G.topoOrder_lt j i hedge)
        exact (not_lt_of_ge horder) hlt
    · intro B hB
      simp only [Set.mem_iUnion] at hB
      obtain ⟨σ, _, hB, _⟩ := hB
      exact hB

end CausalSmith.ExactID.EIDCountshiftUnlabeledMatching
