module

public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.TCompatibilityCompletion
public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.TEntrywiseCompletion

/-! Distinct frontiers for label and mechanism identification. -/

public section

namespace CausalSmith.ExactID.EIDCountshiftUnlabeledMatching

/-- Under full cover, the compatible total-effect matrix is unique. -/
-- @node: full_cover_completion_subsingleton
lemma full_cover_completion_subsingleton {p : ℕ}
    (v : Fin p → Fin p → ℝ)
    (hcompat : (assignmentFiber v).Nonempty) :
    (completionFiber v).Subsingleton := by
  obtain ⟨B, hB, hunique⟩ := full_cover_completion_unique v hcompat
  intro B₁ hB₁ B₂ hB₂
  exact (hunique B₁ hB₁).trans (hunique B₂ hB₂).symm

/-- A forced-support path starts at a covered coordinate. -/
-- @node: Hf_path_source_covered
lemma Hf_path_source_covered {p q : ℕ} (v : Fin q → Fin p → ℝ)
    (f : Fin q ↪ Fin p) {i j : Fin p}
    (hpath : Relation.TransGen (Hf v f) i j) : i ∈ Set.range f := by
  induction hpath with
  | single h =>
      obtain ⟨g, rfl, _, _⟩ := h
      exact ⟨g, rfl⟩
  | tail _ _ ih => exact ih

/-- Every forced path ends at a coordinate in an observed support. -/
-- @node: Hf_path_target_supported
lemma Hf_path_target_supported {p q : ℕ} (v : Fin q → Fin p → ℝ)
    (f : Fin q ↪ Fin p) {i j : Fin p}
    (hpath : Relation.TransGen (Hf v f) i j) :
    j ∈ Finset.univ.biUnion (support v) := by
  induction hpath with
  | single h =>
      obtain ⟨g, _, hj, _⟩ := h
      exact Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ _, hj⟩
  | tail _ h _ =>
      obtain ⟨g, _, hj, _⟩ := h
      exact Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ _, hj⟩

/-- When the support union has exactly one coordinate per group, every
compatible assignment covers that union. -/
-- @node: assignment_range_eq_support_union_of_card
lemma assignment_range_eq_support_union_of_card {p q : ℕ}
    (v : Fin q → Fin p → ℝ)
    (hcard : (Finset.univ.biUnion (support v)).card = q)
    (f : Fin q ↪ Fin p) (hf : f ∈ assignmentFiber v) :
    Set.range f = (↑(Finset.univ.biUnion (support v)) : Set (Fin p)) := by
  classical
  let R : Finset (Fin p) := Finset.univ.image f
  have hsub : R ⊆ Finset.univ.biUnion (support v) := by
    intro i hi
    obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ _, hf.1 g⟩
  have hRcard : R.card = q := by
    simpa [R] using Finset.card_image_of_injective Finset.univ f.injective
  have hEq : R = Finset.univ.biUnion (support v) :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hRcard])
  ext i
  rw [← hEq]
  simp [R]

/-- An observed support coordinate outside an assignment's range can replace
the latest of its assigned parents in a topological ordering. -/
-- @node: assignment_swap_into_uncovered_support
lemma assignment_swap_into_uncovered_support {p q : ℕ}
    (v : Fin q → Fin p → ℝ) (f : Fin q ↪ Fin p)
    (hf : f ∈ assignmentFiber v) (u : Fin p)
    (hu : u ∈ Finset.univ.biUnion (support v))
    (hurange : u ∉ Set.range f) :
    ∃ e : Fin q ↪ Fin p, e ∈ assignmentFiber v ∧ e ≠ f := by
  classical
  let G : Causalean.Graph.DAG (Fin p) :=
    { edge := Hf v f, decEdge := Classical.decRel _, acyclic := hf.2 }
  let ρ := G.topoOrder
  let P : Finset (Fin p) := Finset.univ.filter (fun j => Hf v f j u)
  have hP : P.Nonempty := by
    obtain ⟨g, _, hg⟩ := Finset.mem_biUnion.mp hu
    refine ⟨f g, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact ⟨g, rfl, hg, fun heq => hurange ⟨g, heq.symm⟩⟩
  obtain ⟨w, hw, hwmax⟩ := Finset.exists_max_image P ρ hP
  obtain ⟨g, hgw, hgu, _⟩ := (Finset.mem_filter.mp hw).2
  have hne : u ≠ f g := by
    intro heq
    exact hurange ⟨g, heq.symm⟩
  let e0 : Fin q → Fin p := fun h => if h = g then u else f h
  have heinj : Function.Injective e0 := by
    intro a b hab
    by_cases ha : a = g <;> by_cases hb : b = g
    · exact ha.trans hb.symm
    · have : u = f b := by simpa [e0, ha, hb] using hab
      exact (hurange ⟨b, this.symm⟩).elim
    · have : f a = u := by simpa [e0, ha, hb] using hab
      exact (hurange ⟨a, this⟩).elim
    · exact f.injective (by simpa [e0, ha, hb] using hab)
  let e : Fin q ↪ Fin p := ⟨e0, heinj⟩
  have heval_g : e g = u := by simp [e, e0]
  have heval_other (h : Fin q) (hh : h ≠ g) : e h = f h := by
    simp [e, e0, hh]
  have hesupport : ∀ h, e h ∈ support v h := by
    intro h
    by_cases hh : h = g
    · subst h
      simpa [heval_g] using hgu
    · rw [heval_other h hh]
      exact hf.1 h
  let N : ℕ := Finset.univ.sup ρ + 1
  have hN (x : Fin p) : ρ x < N := by
    have hle : ρ x ≤ Finset.univ.sup ρ := Finset.le_sup (Finset.mem_univ x)
    omega
  let τ : Fin p → ℕ := fun x => if x = u then ρ w else if x = w then N else ρ x
  have hw_eq : w = f g := hgw.symm
  have hτ : ∀ a b, Hf v e a b → τ a < τ b := by
    intro a b hab
    obtain ⟨h, rfl, hb, hba⟩ := hab
    by_cases hh : h = g
    · subst h
      rw [heval_g]
      by_cases hbw : b = w
      · subst b
        have hwu : w ≠ u := by simpa [hw_eq] using hne.symm
        simpa [τ, hwu] using hN w
      · have hold : Hf v f w b := by
          refine ⟨g, hgw, hb, ?_⟩
          exact hbw
        have hlt := G.topoOrder_lt w b hold
        have hbu : b ≠ u := by simpa [heval_g] using hba
        simpa [τ, hne, hbw, hbu, ρ] using hlt
    · rw [heval_other h hh]
      have hsrcu : f h ≠ u := by
        intro heq
        exact hurange ⟨h, heq⟩
      have hsrcw : f h ≠ w := by
        rw [hw_eq]
        intro heq
        exact hh (f.injective heq)
      have hold : Hf v f (f h) b := by
        refine ⟨h, rfl, hb, ?_⟩
        simpa [heval_other h hh] using hba
      by_cases hbu : b = u
      · subst b
        have hmem : f h ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hold⟩
        have hle : ρ (f h) ≤ ρ w := hwmax _ hmem
        have hstrict : ρ (f h) < ρ w :=
          lt_of_le_of_ne hle (fun heq => hsrcw (G.topoOrder_injective heq))
        simpa [τ, hsrcu, hsrcw, hne, ρ] using hstrict
      · by_cases hbw : b = w
        · subst b
          have hwu : w ≠ u := by simpa [hw_eq] using hne.symm
          simpa [τ, hsrcu, hsrcw, hwu] using hN (f h)
        · have hlt := G.topoOrder_lt (f h) b hold
          simpa [τ, hsrcu, hsrcw, hbu, hbw, ρ] using hlt
  have heacyc : ∀ x, ¬ Relation.TransGen (Hf v e) x x := by
    intro x hx
    have hpath : ∀ {a b}, Relation.TransGen (Hf v e) a b → τ a < τ b := by
      intro a b hab
      induction hab with
      | single h => exact hτ _ _ h
      | tail _ h ih => exact ih.trans (hτ _ _ h)
    exact (lt_irrefl _ (hpath hx))
  refine ⟨e, ⟨hesupport, heacyc⟩, ?_⟩
  intro heq
  have hfg : f g = u := by simpa [heq] using heval_g
  exact hurange ⟨g, hfg⟩

/-- A fixed compatible assignment has a unique completion precisely when its
uncovered part is empty or consists of a terminal coordinate reached by all others. -/
-- @node: completionFiberAt_subsingleton_iff
lemma completionFiberAt_subsingleton_iff {p q : ℕ}
    (v : Fin q → Fin p → ℝ) (f : Fin q ↪ Fin p)
    (hf : f ∈ assignmentFiber v) :
    (completionFiberAt v f).Subsingleton ↔
      uncovered f = ∅ ∨
      ∃ u, uncovered f = {u} ∧
        ∀ i, i ≠ u → Relation.TransGen (Hf v f) i u := by
  classical
  constructor
  · intro hsingle
    have hreach (u : Fin p) (hu : u ∈ uncovered f)
        (i : Fin p) (hi : i ≠ u) :
        Relation.TransGen (Hf v f) i u := by
      by_contra hn
      have hu' : u ∉ Set.range f := by simpa [uncovered] using hu
      obtain ⟨B₀, hB₀, hzero⟩ :=
        free_uncovered_entry_completion v f hf hu' hi hn 0
      obtain ⟨B₁, hB₁, hone⟩ :=
        free_uncovered_entry_completion v f hf hu' hi hn 1
      have heq := hsingle hB₀ hB₁
      have := congrArg (fun B : Matrix (Fin p) (Fin p) ℝ => B i u) heq
      rw [hzero, hone] at this
      norm_num at this
    by_cases hempty : uncovered f = ∅
    · exact Or.inl hempty
    · right
      obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      refine ⟨u, ?_, hreach u hu⟩
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hu, ?_⟩
      intro i hi
      by_contra hne
      have hpath := hreach u hu i hne
      have hi' : i ∉ Set.range f := by simpa [uncovered] using hi
      exact hi' (Hf_path_source_covered v f hpath)
  · intro hshape B₁ hB₁ B₂ hB₂
    apply Matrix.ext
    intro i j
    by_cases hj : j ∈ Set.range f
    · obtain ⟨g, rfl⟩ := hj
      rw [hB₁.1 g i, hB₂.1 g i]
    · have hju : j ∈ uncovered f := by simpa [uncovered] using hj
      rcases hshape with hempty | ⟨u, hunit, hreach⟩
      · exact False.elim (by simp [hempty] at hju)
      · have hju' : j = u := by simpa [hunit] using hju
        subst j
        by_cases hi : i = u
        · subst i
          rw [hB₁.2.1, hB₂.2.1]
        · rw [forced_path_completion_zero v f B₁ hf hB₁ hi (hreach i hi),
              forced_path_completion_zero v f B₂ hf hB₂ hi (hreach i hi)]

/-- Inversion preserves uniqueness on a compatible completion slice. -/
-- @node: coefficient_image_subsingleton_iff
lemma coefficient_image_subsingleton_iff {p q : ℕ}
    (v : Fin q → Fin p → ℝ) (f : Fin q ↪ Fin p) :
    (((fun B : Matrix (Fin p) (Fin p) ℝ => 1 - B⁻¹) ''
      completionFiberAt v f).Subsingleton ↔
      (completionFiberAt v f).Subsingleton) := by
  classical
  constructor
  · intro himage B₁ hB₁ B₂ hB₂
    have heq : 1 - B₁⁻¹ = 1 - B₂⁻¹ :=
      himage ⟨B₁, hB₁, rfl⟩ ⟨B₂, hB₂, rfl⟩
    have hinv : B₁⁻¹ = B₂⁻¹ := sub_right_inj.mp heq
    exact Matrix.inv_inj hinv
      (acyclic_unit_matrix_invertible B₁ hB₁.2.1 hB₁.2.2)
  · intro hsource A₁ hA₁ A₂ hA₂
    obtain ⟨B₁, hB₁, rfl⟩ := hA₁
    obtain ⟨B₂, hB₂, rfl⟩ := hA₂
    rw [hsource hB₁ hB₂]

/-- A single invertible completion cannot realize two target assignments. -/
-- @node: assignment_eq_of_common_completion
lemma assignment_eq_of_common_completion {p q : ℕ}
    (v : Fin q → Fin p → ℝ) (f e : Fin q ↪ Fin p)
    (hf : f ∈ assignmentFiber v) (he : e ∈ assignmentFiber v)
    (B : Matrix (Fin p) (Fin p) ℝ)
    (hBf : B ∈ completionFiberAt v f)
    (hBe : B ∈ completionFiberAt v e) : f = e := by
  classical
  have hunit : IsUnit B := (Matrix.isUnit_iff_isUnit_det B).mpr
    (acyclic_unit_matrix_invertible B hBf.2.1 hBf.2.2)
  have hinj := Matrix.mulVec_injective_of_isUnit hunit
  apply DFunLike.ext f e
  intro g
  let c : ℝ := v g (f g) / v g (e g)
  have hfnz : v g (f g) ≠ 0 := by simpa [support] using hf.1 g
  have henz : v g (e g) ≠ 0 := by simpa [support] using he.1 g
  have hcol : B.col (e g) = c • B.col (f g) := by
    funext i
    change B i (e g) = c * B i (f g)
    rw [hBe.1 g i, hBf.1 g i]
    dsimp [c]
    field_simp
  have hsingle : Pi.single (e g) (1 : ℝ) =
      c • Pi.single (f g) (1 : ℝ) := by
    apply hinj
    simp [Matrix.mulVec_smul, Matrix.mulVec_single, hcol]
  by_contra hne
  have heval := congrFun hsingle (e g)
  have hne' : e g ≠ f g := Ne.symm hne
  simp [hne'] at heval

-- @node: thm:label-mechanism-frontier
theorem label_mechanism_frontier {p q : ℕ}
    (v : Fin q → Fin p → ℝ)
    (hcompat : (assignmentFiber v).Nonempty) :
    ((assignmentFiber v).Subsingleton ↔
      (Finset.univ.biUnion (support v)).card = q) ∧
    (∀ f ∈ assignmentFiber v,
      (completionFiberAt v f).Subsingleton ↔
        uncovered f = ∅ ∨
        ∃ u, uncovered f = {u} ∧
          ∀ i, i ≠ u → Relation.TransGen (Hf v f) i u) ∧
    (∀ f ∈ assignmentFiber v,
      ((fun B : Matrix (Fin p) (Fin p) ℝ => 1 - B⁻¹) ''
        completionFiberAt v f).Subsingleton ↔
        uncovered f = ∅ ∨
        ∃ u, uncovered f = {u} ∧
          ∀ i, i ≠ u → Relation.TransGen (Hf v f) i u) ∧
    (2 ≤ p → ((completionFiber v).Subsingleton ↔ q = p)) := by
  have hlabels : (assignmentFiber v).Subsingleton ↔
      (Finset.univ.biUnion (support v)).card = q := by
    constructor
    · intro hsingle
      classical
      obtain ⟨f, hf⟩ := hcompat
      let U := Finset.univ.biUnion (support v)
      let R := Finset.univ.image f
      have hRU : R ⊆ U := by
        intro i hi
        obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp hi
        exact Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ _, hf.1 g⟩
      have hUR : U ⊆ R := by
        intro i hi
        by_contra hn
        have hirange : i ∉ Set.range f := by
          intro ⟨g, hg⟩
          exact hn (Finset.mem_image.mpr ⟨g, Finset.mem_univ _, hg⟩)
        obtain ⟨e, he, hne⟩ :=
          assignment_swap_into_uncovered_support v f hf i hi hirange
        exact hne (hsingle he hf)
      have hEq : U = R := Finset.Subset.antisymm hUR hRU
      rw [show Finset.univ.biUnion (support v) = R from hEq]
      simpa [R] using Finset.card_image_of_injective Finset.univ f.injective
    · intro hcard f hf e he
      classical
      apply Eq.symm
      apply assignment_unique_on_range v f hf e
      intro g
      refine ⟨he.1 g, ?_⟩
      rw [assignment_range_eq_support_union_of_card v hcard f hf]
      exact Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ _, he.1 g⟩
  refine ⟨hlabels, ?_, ?_, ?_⟩
  · intro f hf
    exact completionFiberAt_subsingleton_iff v f hf
  · intro f hf
    rw [coefficient_image_subsingleton_iff]
    exact completionFiberAt_subsingleton_iff v f hf
  · intro hp
    constructor
    · intro hsingle
      by_contra hqp
      classical
      obtain ⟨f, hf⟩ := hcompat
      have hle : q ≤ p := by
        simpa using Fintype.card_le_of_embedding f
      have hlt : q < p := by omega
      have hassignsingle : (assignmentFiber v).Subsingleton := by
        intro a ha b hb
        obtain ⟨A, hA, _⟩ := canonical_completion_exists v a ha
        obtain ⟨B, hB, _⟩ := canonical_completion_exists v b hb
        have hAfull : A ∈ completionFiber v :=
          Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨ha, hA⟩⟩
        have hBfull : B ∈ completionFiber v :=
          Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨hb, hB⟩⟩
        have hAB : A = B := hsingle hAfull hBfull
        exact assignment_eq_of_common_completion v a b ha hb A hA (hAB ▸ hB)
      have hcard' := hlabels.mp hassignsingle
      by_cases hcard : (Finset.univ.biUnion (support v)).card = q
      · have hslice : (completionFiberAt v f).Subsingleton := by
          intro B hB C hC
          apply hsingle
          · exact Set.mem_iUnion.mpr ⟨f, Set.mem_iUnion.mpr ⟨hf, hB⟩⟩
          · exact Set.mem_iUnion.mpr ⟨f, Set.mem_iUnion.mpr ⟨hf, hC⟩⟩
        have hshape := (completionFiberAt_subsingleton_iff v f hf).mp hslice
        have hnotempty : uncovered f ≠ ∅ := by
          intro hempty
          have hsurj : Function.Surjective f := by
            intro i
            by_contra hi
            have himap : i ∉ Finset.univ.map f := by
              intro himap
              obtain ⟨g, _, hg⟩ := Finset.mem_map.mp himap
              exact hi ⟨g, hg⟩
            have hu : i ∈ uncovered f := by simp [uncovered, himap]
            simpa [hempty] using hu
          have heq : q = p := by
            simpa using Fintype.card_congr
              (Equiv.ofBijective f ⟨f.injective, hsurj⟩)
          omega
        rcases hshape with hempty | ⟨u, hunit, hreach⟩
        · exact hnotempty hempty
        · have hu : u ∈ uncovered f := by simp [hunit]
          have hnotrange : u ∉ Set.range f := by
            rintro ⟨g, hg⟩
            have himap : u ∈ Finset.univ.map f :=
              Finset.mem_map.mpr ⟨g, Finset.mem_univ _, hg⟩
            exact (Finset.mem_sdiff.mp hu).2 himap
          have hunion : u ∉ Finset.univ.biUnion (support v) := by
            intro hmem
            apply hnotrange
            rw [assignment_range_eq_support_union_of_card v hcard f hf]
            exact hmem
          let i0 : Fin p := ⟨0, by omega⟩
          let i1 : Fin p := ⟨1, by omega⟩
          have h01 : i0 ≠ i1 := by
            intro heq
            have hval := congrArg Fin.val heq
            norm_num [i0, i1] at hval
          obtain ⟨i, hi⟩ : ∃ i : Fin p, i ≠ u := by
            by_cases hui : u = i0
            · exact ⟨i1, by simpa [hui] using h01.symm⟩
            · exact ⟨i0, Ne.symm hui⟩
          exact hunion (Hf_path_target_supported v f (hreach i hi))
      · exact hcard hcard'
    · intro hqp
      subst q
      exact full_cover_completion_subsingleton v hcompat

end CausalSmith.ExactID.EIDCountshiftUnlabeledMatching
