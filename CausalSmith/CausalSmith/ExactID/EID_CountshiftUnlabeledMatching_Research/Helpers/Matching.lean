module

public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.Basic
public import Mathlib.GroupTheory.Perm.Support

/-! Alternating cycles and private-row peeling for support matchings. -/

public section

namespace CausalSmith.ExactID.EIDCountshiftUnlabeledMatching

/-- A directed cycle in a relation on a finite type supports a nonidentity
permutation whose moved points follow edges of the relation. -/
lemma exists_ne_perm_of_transGen_self {α : Type*} [Finite α]
    (R : α → α → Prop) (hirr : ∀ x, ¬ R x x)
    {a : α} (hcycle : Relation.TransGen R a a) :
    ∃ σ : Equiv.Perm α, σ ≠ 1 ∧ ∀ x, σ x ≠ x → R x (σ x) := by
  classical
  letI := Fintype.ofFinite α
  let Good : Finset α → Prop := fun C =>
    C.Nonempty ∧ ∀ x ∈ C, ∃ y ∈ C, R x y
  have hgood_exists : ∃ C : Finset α, Good C := by
    let C := Finset.univ.filter fun x =>
      Relation.ReflTransGen R a x ∧ Relation.ReflTransGen R x a
    refine ⟨C, ?_, ?_⟩
    · exact ⟨a, by simp [C, Relation.ReflTransGen.refl]⟩
    · intro x hx
      simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      have hxa : Relation.TransGen R x a := by
        rcases (Relation.reflTransGen_iff_eq_or_transGen.mp hx.2) with hax | hxa
        · simpa [hax] using hcycle
        · exact hxa
      obtain ⟨y, hxy, hya⟩ := Relation.TransGen.head'_iff.mp hxa
      refine ⟨y, ?_, hxy⟩
      simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hx.1.tail hxy, hya⟩
  let n := Nat.find (show ∃ n, ∃ C : Finset α, Good C ∧ C.card = n by
    obtain ⟨C, hC⟩ := hgood_exists
    exact ⟨C.card, C, hC, rfl⟩)
  obtain ⟨C, hC, hCcard⟩ := Nat.find_spec
    (show ∃ n, ∃ C : Finset α, Good C ∧ C.card = n by
      obtain ⟨D, hD⟩ := hgood_exists
      exact ⟨D.card, D, hD, rfl⟩)
  let next : {x // x ∈ C} → {x // x ∈ C} := fun x =>
    ⟨Classical.choose (hC.2 x x.property),
      (Classical.choose_spec (hC.2 x x.property)).1⟩
  have hnext (x : {x // x ∈ C}) : R x (next x) :=
    (Classical.choose_spec (hC.2 x x.property)).2
  let Dsub : Finset {x // x ∈ C} := Finset.univ.image next
  let D : Finset α := Dsub.image ((↑) : {x // x ∈ C} → α)
  have hD : Good D := by
    constructor
    · obtain ⟨x, hx⟩ := hC.1
      have hmem : next ⟨x, hx⟩ ∈ Dsub := Finset.mem_image.mpr ⟨⟨x, hx⟩, by simp, rfl⟩
      exact ⟨next ⟨x, hx⟩, Finset.mem_image.mpr ⟨next ⟨x, hx⟩, hmem, rfl⟩⟩
    · intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨w, _hw, rfl⟩ := Finset.mem_image.mp hz
      refine ⟨next (next w), ?_, hnext (next w)⟩
      apply Finset.mem_image.mpr
      refine ⟨next (next w), ?_, rfl⟩
      exact Finset.mem_image.mpr ⟨next w, by simp, rfl⟩
  have hmin : C.card ≤ D.card := by
    rw [hCcard]
    exact Nat.find_min'
      (show ∃ n, ∃ C : Finset α, Good C ∧ C.card = n by
        obtain ⟨E, hE⟩ := hgood_exists
        exact ⟨E.card, E, hE, rfl⟩)
      ⟨D, hD, rfl⟩
  have hDcard : D.card = Dsub.card :=
    Finset.card_image_of_injective Dsub Subtype.val_injective
  have hnext_injective : Function.Injective next := by
    have hcard : (Finset.univ.image next).card =
        (Finset.univ : Finset {x // x ∈ C}).card := by
      change Dsub.card = _
      rw [Finset.card_univ, Fintype.card_coe]
      have hle : Dsub.card ≤ C.card := by
        simpa using Finset.card_le_univ Dsub
      omega
    have hinjOn : Set.InjOn next (↑(Finset.univ : Finset {x // x ∈ C}) : Set _) :=
      Finset.card_image_iff.mp hcard
    intro x y hxy
    exact hinjOn (by simp) (by simp) hxy
  have hnext_surjective : Function.Surjective next :=
    Finite.surjective_of_injective hnext_injective
  let τ : Equiv.Perm {x // x ∈ C} := Equiv.ofBijective next
    ⟨hnext_injective, hnext_surjective⟩
  let σ : Equiv.Perm α := τ.extendDomain (Equiv.refl {x // x ∈ C})
  refine ⟨σ, ?_, ?_⟩
  · intro hσ
    obtain ⟨x, hx⟩ := hC.1
    have hedge := hnext ⟨x, hx⟩
    have hfix : next ⟨x, hx⟩ = ⟨x, hx⟩ := by
      apply Subtype.ext
      have heq := congrArg (fun e : Equiv.Perm α => e x) hσ
      have happ := Equiv.Perm.extendDomain_apply_image τ
        (Equiv.refl {x // x ∈ C}) ⟨x, hx⟩
      have hsigma : σ x = next ⟨x, hx⟩ := by
        calc
          σ x = (τ ⟨x, hx⟩ : {x // x ∈ C}) := by simpa [σ] using happ
          _ = next ⟨x, hx⟩ := congrArg Subtype.val (rfl : τ ⟨x, hx⟩ = next ⟨x, hx⟩)
      rw [hsigma] at heq
      simpa using heq
    have hval := congrArg Subtype.val hfix
    rw [hval] at hedge
    exact hirr x hedge
  · intro x hmove
    by_cases hx : x ∈ C
    · have hsigma : σ x = next ⟨x, hx⟩ := by
        have happ := Equiv.Perm.extendDomain_apply_image τ
          (Equiv.refl {x // x ∈ C}) ⟨x, hx⟩
        calc
          σ x = (τ ⟨x, hx⟩ : {x // x ∈ C}) := by simpa [σ] using happ
          _ = next ⟨x, hx⟩ := congrArg Subtype.val (rfl : τ ⟨x, hx⟩ = next ⟨x, hx⟩)
      rw [hsigma]
      exact hnext ⟨x, hx⟩
    · have : σ x = x := by
        simp [σ, Equiv.Perm.extendDomain_apply_not_subtype, hx]
      exact (hmove this).elim

/-- A directed cycle in the graph induced by a support-respecting embedding
produces a distinct support-respecting embedding with the same range. -/
-- @node: gate:directed-cycle-matching-switch
lemma exists_ne_induced_matching_of_cycle {α β : Type*} [Finite β]
    (S : α → β → Prop) (f : α ↪ β) (hf : ∀ a, S a (f a))
    {b : β}
    (hcycle : Relation.TransGen
      (fun x y => ∃ a, f a = x ∧ S a y ∧ y ≠ x) b b) :
    ∃ e : α ↪ β, e ≠ f ∧ ∀ a, S a (e a) ∧ e a ∈ Set.range f := by
  classical
  let R : β → β → Prop := fun x y => ∃ a, f a = x ∧ S a y ∧ y ≠ x
  have hirr (x : β) : ¬ R x x := by
    rintro ⟨a, _ha, _hS, hne⟩
    exact hne rfl
  obtain ⟨σ, hσne, hσ⟩ := exists_ne_perm_of_transGen_self R hirr hcycle
  let e : α ↪ β := ⟨fun a => σ (f a), σ.injective.comp f.injective⟩
  have he (a : α) : S a (e a) ∧ e a ∈ Set.range f := by
    by_cases ha : σ (f a) = f a
    · exact ⟨by simpa [e, ha] using hf a, ⟨a, by simpa [e, ha]⟩⟩
    · have hedge := hσ (f a) ha
      rcases hedge with ⟨a', ha', hSa', _⟩
      have haa' : a' = a := f.injective ha'
      subst a'
      refine ⟨by simpa [e] using hSa', ?_⟩
      have hmove_next : σ (σ (f a)) ≠ σ (f a) := by
        intro hfix
        exact ha (σ.injective hfix)
      rcases hσ (σ (f a)) hmove_next with ⟨c, hc, _⟩
      exact ⟨c, by simpa [e] using hc⟩
  refine ⟨e, ?_, he⟩
  intro hef
  apply hσne
  apply Equiv.ext
  intro x
  by_cases hx : σ x = x
  · simpa using hx
  · rcases hσ x hx with ⟨a, ha, _⟩
    have hea := DFunLike.congr_fun hef a
    change σ (f a) = f a at hea
    exact (hx (by simpa [ha] using hea)).elim

/-- An injective self-map of a finite set cannot move every point along an
acyclic relation: a moved point with no moved predecessor would contradict
surjectivity. -/
-- @node: acyclic_injective_map_fixed
lemma acyclic_injective_map_fixed {α : Type*} [Finite α]
    (R : α → α → Prop) (hacyc : ∀ x, ¬ Relation.TransGen R x x)
    (k : α → α) (hk : Function.Injective k)
    (hstep : ∀ x, k x ≠ x → R x (k x)) : ∀ x, k x = x := by
  classical
  let T := Relation.TransGen R
  have htrans : IsTrans α T := inferInstance
  have hirrefl : Std.Irrefl T := ⟨hacyc⟩
  let _ : IsTrans α T := htrans
  let _ : Std.Irrefl T := hirrefl
  have hwf : WellFounded T := Finite.wellFounded_of_trans_of_irrefl T
  by_contra h
  have hnonempty : ({x | k x ≠ x} : Set α).Nonempty := by
    obtain ⟨x, hx⟩ := not_forall.mp h
    exact ⟨x, hx⟩
  obtain ⟨x, hx, hmin⟩ := hwf.has_min {x | k x ≠ x} hnonempty
  obtain ⟨y, hy⟩ := (Finite.surjective_of_injective hk) x
  have hy' : k y ≠ y := by
    intro hfix
    apply hx
    have hxy : x = y := hy.symm.trans hfix
    simpa [hxy] using hfix
  exact hmin y hy' (by simpa [hy] using (Relation.TransGen.single (hstep y hy')))

-- @node: assignment_unique_on_range
lemma assignment_unique_on_range {p q : ℕ}
    (v : Fin q → Fin p → ℝ) (f : Fin q ↪ Fin p) :
    f ∈ assignmentFiber v →
      ∀ e : Fin q ↪ Fin p,
        (∀ g, e g ∈ support v g ∧ e g ∈ Set.range f) → e = f := by
  rintro ⟨_, hacyc⟩ e he
  classical
  let k : Fin q → Fin q := fun g => Classical.choose (he g).2
  have hkval (g : Fin q) : f (k g) = e g :=
    Classical.choose_spec (he g).2
  have hk : Function.Injective k := by
    intro g h hgh
    apply e.injective
    calc
      e g = f (k g) := (hkval g).symm
      _ = f (k h) := by rw [hgh]
      _ = e h := hkval h
  have hacyc' : ∀ g, ¬ Relation.TransGen
      (fun a b : Fin q => Hf v f (f a) (f b)) g g := by
    intro g hg
    apply hacyc (f g)
    exact hg.lift f (by intro a b hab; exact hab)
  have hstep (g : Fin q) (hg : k g ≠ g) : Hf v f (f g) (f (k g)) := by
    refine ⟨g, rfl, ?_, ?_⟩
    · rw [hkval]
      exact (he g).1
    · exact fun h => hg (f.injective h)
  have hfix := acyclic_injective_map_fixed
    (fun a b : Fin q => Hf v f (f a) (f b)) hacyc' k hk hstep
  apply DFunLike.ext e f
  intro g
  rw [← hkval, hfix]

/-- Compatible projective groups have distinct coordinate supports. Equal
supports would force the two assigned coordinates to form a directed cycle. -/
-- @node: assignment_distinct_supports
lemma assignment_distinct_supports {p q : ℕ}
    (v : Fin q → Fin p → ℝ) (f : Fin q ↪ Fin p)
    (hf : f ∈ assignmentFiber v) {g h : Fin q} (hgh : g ≠ h) :
    support v g ≠ support v h := by
  intro heq
  have hfg : f g ∈ support v h := heq ▸ hf.1 g
  have hfh : f h ∈ support v g := heq.symm ▸ hf.1 h
  have hne : f g ≠ f h := fun hEq => hgh (f.injective hEq)
  have hforward : Hf v f (f g) (f h) :=
    ⟨g, rfl, hfh, hne.symm⟩
  have hbackward : Hf v f (f h) (f g) :=
    ⟨h, rfl, hfg, hne⟩
  exact hf.2 (f g) ((Relation.TransGen.single hforward).trans
    (Relation.TransGen.single hbackward))

/-- In every nonempty collection of groups, an acyclic assignment supplies a
private assigned coordinate. This is the next legal private-row deletion. -/
-- @node: assignment_private_in_subset
lemma assignment_private_in_subset {p q : ℕ}
    (v : Fin q → Fin p → ℝ) (f : Fin q ↪ Fin p)
    (hf : f ∈ assignmentFiber v) (R : Finset (Fin q)) (hR : R.Nonempty) :
    ∃ g ∈ R, ∃ i ∈ support v g,
      ∀ h ∈ R, h ≠ g → i ∉ support v h := by
  classical
  let T := Relation.TransGen (Hf v f)
  have htrans : IsTrans (Fin p) T := inferInstance
  have hirrefl : Std.Irrefl T := ⟨hf.2⟩
  let _ : IsTrans (Fin p) T := htrans
  let _ : Std.Irrefl T := hirrefl
  have hwf : WellFounded T := Finite.wellFounded_of_trans_of_irrefl T
  let C : Set (Fin p) := {i | ∃ g ∈ R, f g = i}
  have hC : C.Nonempty := by
    obtain ⟨g, hg⟩ := hR
    exact ⟨f g, g, hg, rfl⟩
  obtain ⟨i, hi, hmin⟩ := hwf.has_min C hC
  obtain ⟨g, hg, rfl⟩ := hi
  refine ⟨g, hg, f g, hf.1 g, ?_⟩
  intro h hh hne hmem
  have hfh : f h ∈ C := ⟨h, hh, rfl⟩
  have hedge : Hf v f (f h) (f g) :=
    ⟨h, rfl, hmem, fun heq => hne (f.injective heq.symm)⟩
  exact hmin (f h) hfh (Relation.TransGen.single hedge)

-- @node: compatible_peelStep_strict
lemma compatible_peelStep_strict {p q : ℕ}
    (v : Fin q → Fin p → ℝ) (f : Fin q ↪ Fin p)
    (hf : f ∈ assignmentFiber v) (R : Finset (Fin q)) (hR : R.Nonempty) :
    peelStep (fun g => support v g) none R ⊂ R := by
  classical
  obtain ⟨g, hg, i, hi, hprivate⟩ :=
    assignment_private_in_subset v f hf R hR
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro x hx
    simp only [peelStep, Finset.mem_filter] at hx
    exact hx.1
  intro heq
  have hg' : g ∈ peelStep (fun g => support v g) none R := heq.symm ▸ hg
  simp only [peelStep, Finset.mem_filter] at hg'
  rcases hg'.2 with hfalse | hnot
  · cases hfalse
  · exact hnot ⟨i, hi, hprivate⟩

-- @node: compatible_peeling_exhausts
lemma compatible_peeling_exhausts {p q : ℕ}
    (v : Fin q → Fin p → ℝ) (f : Fin q ↪ Fin p)
    (hf : f ∈ assignmentFiber v) :
    peelsAll (fun g => support v g) := by
  classical
  let step := peelStep (fun g => support v g) none
  have hstep (R : Finset (Fin q)) (hR : R.Nonempty) : step R ⊂ R :=
    compatible_peelStep_strict v f hf R hR
  have hzero (k : ℕ) : step^[k] ∅ = ∅ := by
    induction k with
    | zero => rfl
    | succ k ih => simp [Function.iterate_succ_apply, ih, step, peelStep]
  have hiter (k : ℕ) : ∀ R : Finset (Fin q), R.card ≤ k →
      step^[k] R = ∅ := by
    induction k with
    | zero =>
      intro R hcard
      have hR : R = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hcard)
      simp [hR]
    | succ k ih =>
      intro R hcard
      by_cases hR : R.Nonempty
      · have hstrict := hstep R hR
        have hnext : (step R).card ≤ k := by
          have hlt := Finset.card_lt_card hstrict
          omega
        simpa only [Function.iterate_succ_apply] using ih (step R) hnext
      · have hempty : R = ∅ := Finset.not_nonempty_iff_eq_empty.mp hR
        simpa [hempty, Function.iterate_succ_apply] using hzero (k + 1)
  simpa [peelsAll, peelResidual, step] using
    (hiter q Finset.univ (by simp))

-- @node: assignment_iff_unique_induced_matching
lemma assignment_iff_unique_induced_matching {p q : ℕ}
    (v : Fin q → Fin p → ℝ) (f : Fin q ↪ Fin p) :
    f ∈ assignmentFiber v ↔
      (∀ g, f g ∈ support v g) ∧
      (∀ e : Fin q ↪ Fin p,
        (∀ g, e g ∈ support v g ∧ e g ∈ Set.range f) → e = f) := by
  constructor
  · intro hf
    exact ⟨hf.1, assignment_unique_on_range v f hf⟩
  · intro h
    exact ⟨h.1, by
      intro i hcycle
      obtain ⟨e, hene, he⟩ := exists_ne_induced_matching_of_cycle
        (fun g j => j ∈ support v g) f h.1 hcycle
      exact hene (h.2 e he)⟩

-- @node: full_cover_assignment_unique
lemma full_cover_assignment_unique {p : ℕ} (v : Fin p → Fin p → ℝ)
    (h : (assignmentFiber v).Nonempty) :
    ∃! f : Fin p ↪ Fin p, f ∈ assignmentFiber v := by
  obtain ⟨f, hf⟩ := h
  refine ⟨f, hf, ?_⟩
  intro e he
  apply assignment_unique_on_range v f hf e
  intro g
  exact ⟨he.1 g, (Finite.surjective_of_injective f.injective) (e g)⟩

-- @node: full_cover_completion_unique
lemma full_cover_completion_unique {p : ℕ} (v : Fin p → Fin p → ℝ)
    (h : (assignmentFiber v).Nonempty) :
    ∃! B : Matrix (Fin p) (Fin p) ℝ, B ∈ completionFiber v := by
  classical
  obtain ⟨f, hf⟩ := h
  have hsurj : Function.Surjective f := Finite.surjective_of_injective f.injective
  let σ : Fin p ≃ Fin p := Equiv.ofBijective f ⟨f.injective, hsurj⟩
  let B : Matrix (Fin p) (Fin p) ℝ :=
    Matrix.of fun i j => v (σ.symm j) i / v (σ.symm j) j
  have hBcol (g : Fin p) (i : Fin p) : B i (f g) = v g i / v g (f g) := by
    change v (σ.symm (σ g)) i / v (σ.symm (σ g)) (f g) = _
    rw [σ.symm_apply_apply]
  have hdiag : ∀ i, B i i = 1 := by
    intro i
    let g := σ.symm i
    have hi : f g = i := σ.apply_symm_apply i
    have hne : v g i ≠ 0 := by
      have hs := hf.1 g
      simpa [support, hi] using hs
    change v g i / v g i = 1
    exact div_self hne
  have hedge : ∀ i j, i ≠ j ∧ B j i ≠ 0 → Hf v f i j := by
    intro i j hij
    let g := σ.symm i
    have hi : f g = i := σ.apply_symm_apply i
    have hj : v g j ≠ 0 := by
      intro hz
      apply hij.2
      simp [B, g, hz]
    exact ⟨g, hi, by simpa [support] using hj, hij.1.symm⟩
  have hac : ∀ i, ¬ Relation.TransGen (fun j k => j ≠ k ∧ B k j ≠ 0) i i := by
    intro i hc
    exact hf.2 i (hc.lift id (by intro j k hjk; exact hedge j k hjk))
  have hmem : B ∈ completionFiber v := by
    simp only [completionFiber, Set.mem_iUnion]
    exact ⟨f, ⟨hf, ⟨hBcol, hdiag, hac⟩⟩⟩
  refine ⟨B, hmem, ?_⟩
  intro C hC
  simp only [completionFiber, Set.mem_iUnion] at hC
  obtain ⟨e, he, hCe⟩ := hC
  obtain ⟨_, _, huniq⟩ := full_cover_assignment_unique v ⟨f, hf⟩
  have hef : e = f := (huniq e he).trans (huniq f hf).symm
  subst e
  apply Matrix.ext
  intro i j
  obtain ⟨g, rfl⟩ := hsurj j
  exact (hCe.1 g i).trans (hBcol g i).symm

lemma assignment_nonempty_iff_peelsAll {p q : ℕ}
    (v : Fin q → Fin p → ℝ) :
    (assignmentFiber v).Nonempty ↔ peelsAll (fun g => support v g) := by
  constructor
  · rintro ⟨f, hf⟩
    exact compatible_peeling_exhausts v f hf
  · intro hall
    classical
    let S : Fin q → Finset (Fin p) := fun g => support v g
    let step := peelStep S none
    let R : ℕ → Finset (Fin q) := fun n => step^[n] Finset.univ
    have hsub (T : Finset (Fin q)) : step T ⊆ T := by
      intro g hg
      simp only [step, peelStep, Finset.mem_filter] at hg
      exact hg.1
    have hsucc (n : ℕ) : R (n + 1) = step (R n) := by
      simp only [R, Function.iterate_succ_apply']
    have hmono (a b : ℕ) (hab : a ≤ b) : R b ⊆ R a := by
      induction b, hab using Nat.le_induction with
      | base => exact Finset.Subset.rfl
      | succ b _ ih =>
          calc
            R (b + 1) = step (R b) := hsucc b
            _ ⊆ R b := hsub _
            _ ⊆ R a := ih
    have hq : R q = ∅ := by
      simpa [R, peelsAll, peelResidual, S, step] using hall
    have hdrop (g : Fin q) :
        ∃ n : ℕ, n < q ∧ g ∈ R n ∧ g ∉ R (n + 1) := by
      by_contra hn
      have hstay : ∀ n ≤ q, g ∈ R n := by
        intro n hnq
        induction n with
        | zero => simp [R]
        | succ n ih =>
          have hng : g ∈ R n := ih (by omega)
          by_contra hnot
          exact hn ⟨n, by omega, hng, hnot⟩
      have : g ∈ (∅ : Finset (Fin q)) := hq ▸ hstay q le_rfl
      simp at this
    let τ (g : Fin q) : ℕ := Classical.choose (hdrop g)
    have hτ (g : Fin q) :
        τ g < q ∧ g ∈ R (τ g) ∧ g ∉ R (τ g + 1) :=
      Classical.choose_spec (hdrop g)
    have hprivate (g : Fin q) :
        ∃ i ∈ S g, ∀ h ∈ R (τ g), h ≠ g → i ∉ S h := by
      have hg := (hτ g).2.1
      have hgone := (hτ g).2.2
      rw [hsucc] at hgone
      simp only [step, peelStep, Finset.mem_filter] at hgone
      have hnot : ¬ (some g = none ∨
          ¬ ∃ i ∈ S g, ∀ h ∈ R (τ g), h ≠ g → i ∉ S h) := by
        intro hkeep
        exact hgone ⟨hg, hkeep⟩
      exact not_not.mp (not_or.mp hnot).2
    let c (g : Fin q) : Fin p := Classical.choose (hprivate g)
    have hc (g : Fin q) : c g ∈ S g ∧
        ∀ h ∈ R (τ g), h ≠ g → c g ∉ S h :=
      Classical.choose_spec (hprivate g)
    have hinj : Function.Injective c := by
      intro g h heq
      by_contra hne
      rcases le_total (τ g) (τ h) with hgh | hhg
      · have hh : h ∈ R (τ g) := hmono _ _ hgh (hτ h).2.1
        exact (hc g).2 h hh (Ne.symm hne) (heq ▸ (hc h).1)
      · have hg : g ∈ R (τ h) := hmono _ _ hhg (hτ g).2.1
        exact (hc h).2 g hg hne (heq.symm ▸ (hc g).1)
    let f : Fin q ↪ Fin p := ⟨c, hinj⟩
    let ρ (i : Fin p) : ℕ :=
      if hi : i ∈ Set.range f then τ (Classical.choose hi) + 1 else q + 1
    have hρ (g : Fin q) : ρ (f g) = τ g + 1 := by
      have hi : f g ∈ Set.range f := ⟨g, rfl⟩
      simp only [ρ, dif_pos hi]
      have hcg : Classical.choose hi = g := f.injective (Classical.choose_spec hi)
      rw [hcg]
    have hedge (i j : Fin p) (hij : Hf v f i j) : ρ i < ρ j := by
      obtain ⟨g, rfl, hjs, hjne⟩ := hij
      rw [hρ g]
      by_cases hj : j ∈ Set.range f
      · obtain ⟨h, rfl⟩ := hj
        rw [hρ h]
        have hne : g ≠ h := by
          intro he
          exact hjne (he ▸ rfl)
        have hlt : τ g < τ h := by
          by_contra hn
          have hle : τ h ≤ τ g := by omega
          have hg : g ∈ R (τ h) := hmono _ _ hle (hτ g).2.1
          exact (hc h).2 g hg hne hjs
        omega
      · simp only [ρ, dif_neg hj]
        have := (hτ g).1
        omega
    refine ⟨f, ?_⟩
    constructor
    · exact fun g => (hc g).1
    · intro i hcycle
      have hpath {a b : Fin p} (hab : Relation.TransGen (Hf v f) a b) :
          ρ a < ρ b := by
        induction hab with
        | single h => exact hedge _ _ h
        | tail _ h ih => exact lt_trans ih (hedge _ _ h)
      exact (lt_irrefl _ (hpath hcycle))

/-- A coordinate private for a frozen group after parallel peeling is realized
by a compatible assignment. -/
-- @node: frozen_private_realized_by_assignment
lemma frozen_private_realized_by_assignment {p q : ℕ}
    (v : Fin q → Fin p → ℝ) (f₀ : Fin q ↪ Fin p)
    (hf₀ : f₀ ∈ assignmentFiber v) (g₀ : Fin q) (i : Fin p)
    (hi : i ∈ frozenPeeling (fun g => support v g) g₀) :
    ∃ f ∈ assignmentFiber v, f g₀ = i := by
  letI finForallDecidable (P : Fin q → Prop) [DecidablePred P] :
      Decidable (∀ g, P g) := Fintype.decidableForallFintype
  let S : Fin q → Finset (Fin p) := fun g => support v g
  let step := peelStep S (some g₀)
  let R : ℕ → Finset (Fin q) := fun n => step^[n] Finset.univ
  let residual := R q
  have hsub (T : Finset (Fin q)) : step T ⊆ T := by
    dsimp only [step, peelStep]
    exact Finset.filter_subset _ _
  have hsucc (n : ℕ) : R (n + 1) = step (R n) := by
    simp only [R, Function.iterate_succ_apply']
  have hmono (a b : ℕ) (hab : a ≤ b) : R b ⊆ R a := by
    induction b, hab using Nat.le_induction with
    | base => exact Finset.Subset.rfl
    | succ b _ ih =>
        calc
          R (b + 1) = step (R b) := hsucc b
          _ ⊆ R b := hsub _
          _ ⊆ R a := ih
  have hg₀ (n : ℕ) : g₀ ∈ R n := by
    induction n with
    | zero => simp [R]
    | succ n ih =>
        rw [hsucc]
        dsimp only [step, peelStep]
        exact Finset.mem_filter.mpr ⟨ih, Or.inl rfl⟩
  rw [frozenPeeling] at hi
  obtain ⟨hiSraw, hiprivateRaw⟩ := Finset.mem_filter.mp hi
  have hiS : i ∈ S g₀ := hiSraw
  have hiprivate : ∀ h ∈ residual, h ≠ g₀ → i ∉ S h := by
    intro h hh hne
    exact hiprivateRaw h
      (by simpa [residual, R, peelResidual, S] using hh) hne
  classical
  have hdrop (g : Fin q) (hg : g ∉ residual) :
      ∃ n : ℕ, n < q ∧ g ∈ R n ∧ g ∉ R (n + 1) := by
    by_contra hn
    have hstay : ∀ n ≤ q, g ∈ R n := by
      intro n hnq
      induction n with
      | zero => simp [R]
      | succ n ih =>
          have hng : g ∈ R n := ih (by omega)
          by_contra hnot
          exact hn ⟨n, by omega, hng, hnot⟩
    exact hg (hstay q le_rfl)
  let τ (g : Fin q) (hg : g ∉ residual) : ℕ := Classical.choose (hdrop g hg)
  have hτ (g : Fin q) (hg : g ∉ residual) :
      τ g hg < q ∧ g ∈ R (τ g hg) ∧ g ∉ R (τ g hg + 1) :=
    Classical.choose_spec (hdrop g hg)
  have hprivate (g : Fin q) (hg : g ∉ residual) :
      ∃ j ∈ S g, ∀ h ∈ R (τ g hg), h ≠ g → j ∉ S h := by
    have hgone := (hτ g hg).2.2
    rw [hsucc] at hgone
    simp only [step, peelStep, Finset.mem_filter] at hgone
    have hnot : ¬ (some g = some g₀ ∨
        ¬ ∃ j ∈ S g, ∀ h ∈ R (τ g hg), h ≠ g → j ∉ S h) := by
      intro hkeep
      exact hgone ⟨(hτ g hg).2.1, hkeep⟩
    exact not_not.mp (not_or.mp hnot).2
  let c (g : Fin q) : Fin p :=
    if hg : g ∈ residual then if g = g₀ then i else f₀ g
    else Classical.choose (hprivate g hg)
  have hc0 : c g₀ = i := by
    dsimp only [c]
    rw [dif_pos (hg₀ q), if_pos rfl]
  have hcS (g : Fin q) : c g ∈ S g := by
    by_cases hg : g ∈ residual
    · by_cases heq : g = g₀
      · subst g
        change (if h : g₀ ∈ residual then if g₀ = g₀ then i else f₀ g₀
          else Classical.choose (hprivate g₀ h)) ∈ S g₀
        rw [dif_pos (hg₀ q), if_pos rfl]
        exact hiS
      · simpa [c, hg, heq, S] using hf₀.1 g
    · simpa [c, hg] using (Classical.choose_spec (hprivate g hg)).1
  have hcprivate (g : Fin q) (hg : g ∉ residual) :
      ∀ h ∈ R (τ g hg), h ≠ g → c g ∉ S h := by
    simpa [c, hg] using (Classical.choose_spec (hprivate g hg)).2
  have hres_mono (n : ℕ) (hn : n ≤ q) : residual ⊆ R n := hmono n q hn
  have hcinj : Function.Injective c := by
    intro g h heq
    by_cases hg : g ∈ residual
    · by_cases hh : h ∈ residual
      · by_cases gg₀ : g = g₀
        · subst g
          by_cases hg₀h : h = g₀
          · exact hg₀h.symm
          · exfalso
            apply hiprivate h hh hg₀h
            have hch : c h = f₀ h := by simp only [c, dif_pos hh, if_neg hg₀h]
            have hval : f₀ h = i := hch.symm.trans (heq.symm.trans hc0)
            simpa [hval] using hf₀.1 h
        · by_cases hg₀h : h = g₀
          · subst h
            exfalso
            apply hiprivate g hg gg₀
            have hcg : c g = f₀ g := by simp only [c, dif_pos hg, if_neg gg₀]
            have hval : f₀ g = i := hcg.symm.trans (heq.trans hc0)
            simpa [hval] using hf₀.1 g
          · apply f₀.injective
            simpa [c, hg, hh, gg₀, hg₀h] using heq
      · exfalso
        have hgR : g ∈ R (τ h hh) := hres_mono _ (Nat.le_of_lt (hτ h hh).1) hg
        apply hcprivate h hh g hgR (Ne.symm (fun hEq => hh (hEq ▸ hg)))
        exact heq ▸ hcS g
    · by_cases hh : h ∈ residual
      · exfalso
        have hhR : h ∈ R (τ g hg) := hres_mono _ (Nat.le_of_lt (hτ g hg).1) hh
        apply hcprivate g hg h hhR (fun hEq => hg (hEq ▸ hh))
        exact heq.symm ▸ hcS h
      · by_contra hne
        rcases le_total (τ g hg) (τ h hh) with hgh | hhg
        · have hhR : h ∈ R (τ g hg) := hmono _ _ hgh (hτ h hh).2.1
          exact hcprivate g hg h hhR (Ne.symm hne) (heq.symm ▸ hcS h)
        · have hgR : g ∈ R (τ h hh) := hmono _ _ hhg (hτ g hg).2.1
          exact hcprivate h hh g hgR hne (heq ▸ hcS g)
  let f : Fin q ↪ Fin p := ⟨c, hcinj⟩
  have hf_unique : ∀ e : Fin q ↪ Fin p,
      (∀ g, e g ∈ support v g ∧ e g ∈ Set.range f) → e = f := by
    intro e he
    have he_range (g : Fin q) : ∃ h, e g = c h := by
      obtain ⟨h, hh⟩ := (he g).2
      exact ⟨h, hh.symm⟩
    let pick (g : Fin q) : Fin q := Classical.choose (he_range g)
    have hpick (g : Fin q) : e g = c (pick g) := Classical.choose_spec (he_range g)
    let Inner := {g : Fin q // g ∈ residual}
    let kI : Inner → Inner := fun g => by
      have hh : pick g ∈ residual := by
        by_contra hh
        have hgR : g.1 ∈ R (τ (pick g) hh) :=
          hres_mono _ (Nat.le_of_lt (hτ (pick g) hh).1) g.2
        exact hcprivate (pick g) hh g hgR (fun hEq => hh (hEq ▸ g.2))
          (hpick g ▸ (he g).1)
      exact ⟨pick g, hh⟩
    have hkI_val (g : Inner) : c (kI g) = e g := by
      exact (hpick g).symm
    have hkI_inj : Function.Injective kI := by
      intro g h hgh
      apply Subtype.ext
      apply e.injective
      rw [← hkI_val g, ← hkI_val h, hgh]
    have hkI_surj : Function.Surjective kI := Finite.surjective_of_injective hkI_inj
    have hkI_g₀ : kI ⟨g₀, hg₀ q⟩ = ⟨g₀, hg₀ q⟩ := by
      obtain ⟨y, hy⟩ := hkI_surj ⟨g₀, hg₀ q⟩
      have hey : e y = i := by
        rw [← hkI_val y, hy]
        exact hc0
      have hy0val : y.1 = g₀ := by
        by_contra hne
        exact hiprivate y y.2 hne (hey ▸ (he y).1)
      have hy0 : y = ⟨g₀, hg₀ q⟩ := Subtype.ext hy0val
      simpa [hy0] using hy
    have hkI_fix : ∀ g : Inner, kI g = g := by
      apply acyclic_injective_map_fixed (fun a b : Inner => Hf v f₀ (f₀ a) (f₀ b))
      · intro g hcycle
        exact hf₀.2 (f₀ g) (hcycle.lift (fun x : Inner => f₀ x)
          (by intro a b hab; exact hab))
      · exact hkI_inj
      · intro g hmove
        have hg0 : g.1 ≠ g₀ := by
          intro heq
          have hgeq : g = ⟨g₀, hg₀ q⟩ := Subtype.ext heq
          subst g
          exact hmove hkI_g₀
        have hkg0 : (kI g).1 ≠ g₀ := by
          intro heq
          have hEq : kI g = ⟨g₀, hg₀ q⟩ := Subtype.ext heq
          apply hg0
          exact congrArg Subtype.val (hkI_inj (hEq.trans hkI_g₀.symm))
        refine ⟨g.1, rfl, ?_, ?_⟩
        · have hgS := (he g).1
          have hck : c (kI g) = f₀ (kI g) := by
            simp only [c, dif_pos (kI g).2, if_neg hkg0]
          rw [← hkI_val g, hck] at hgS
          exact hgS
        · intro heq
          apply hmove
          apply Subtype.ext
          exact f₀.injective heq
    have he_inner (g : Fin q) (hg : g ∈ residual) : e g = c g := by
      let x : Inner := ⟨g, hg⟩
      rw [← hkI_val x, hkI_fix x]
    let Outer := {g : Fin q // g ∉ residual}
    let kO : Outer → Outer := fun g => by
      have hh : pick g ∉ residual := by
        intro hh
        have heh' : e (pick g) = c (pick g) := he_inner (pick g) hh
        have hEq : g.1 = pick g := e.injective ((hpick g).trans heh'.symm)
        exact g.2 (hEq ▸ hh)
      exact ⟨pick g, hh⟩
    have hkO_val (g : Outer) : c (kO g) = e g := by
      exact (hpick g).symm
    have hkO_inj : Function.Injective kO := by
      intro g h hgh
      apply Subtype.ext
      apply e.injective
      rw [← hkO_val g, ← hkO_val h, hgh]
    have hkO_fix : ∀ g : Outer, kO g = g := by
      apply acyclic_injective_map_fixed (fun a b : Outer => τ a a.2 < τ b b.2)
      · intro g hcycle
        have hgen := hcycle.lift (fun x : Outer => τ x x.2)
          (by intro a b hab; exact hab)
        have hmin : Relation.TransGen ((· < ·) : ℕ → ℕ → Prop) ≤ (· < ·) :=
          Relation.transGen_minimal (fun _ _ h => h)
        have hlt : τ g g.2 < τ g g.2 := hmin _ _ hgen
        exact (lt_irrefl _ hlt)
      · exact hkO_inj
      · intro g hmove
        have hne : (kO g).1 ≠ g.1 := fun heq => hmove (Subtype.ext heq)
        have hnle : ¬ τ (kO g) (kO g).2 ≤ τ g g.2 := by
          intro hle
          have hgR : g.1 ∈ R (τ (kO g) (kO g).2) := hmono _ _ hle (hτ g g.2).2.1
          exact hcprivate (kO g) (kO g).2 g hgR hne.symm (hkO_val g ▸ (he g).1)
        omega
    apply DFunLike.ext e f
    intro g
    by_cases hg : g ∈ residual
    · change e g = c g
      exact he_inner g hg
    · let x : Outer := ⟨g, hg⟩
      change e g = c g
      rw [← hkO_val x, hkO_fix x]
  refine ⟨f, (assignment_iff_unique_induced_matching v f).2 ⟨?_, hf_unique⟩, ?_⟩
  · intro g
    change c g ∈ support v g
    exact hcS g
  · change c g₀ = i
    exact hc0

end CausalSmith.ExactID.EIDCountshiftUnlabeledMatching
