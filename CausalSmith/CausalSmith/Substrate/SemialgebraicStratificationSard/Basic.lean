import Mathlib

/-!
# Semialgebraic sets in finite real coordinate spaces

This file gives a paper-independent, quantifier-free definition of semialgebraic subsets of
finite real coordinate spaces.  It records the Boolean closure operations, coordinate products,
graphs, and the Tarski--Seidenberg projection theorem.  The definition is deliberately not phrased
using first-order definability: stability under projection remains a substantive theorem.
-/

open Set

namespace CausalSmith.SemialgebraicStratificationSard

/-- A subset of a finite real coordinate space is semialgebraic when it is generated from
polynomial zero and strict-positivity loci by finitely many Boolean operations. -/
inductive IsSemialgebraic {ι : Type*} [Fintype ι] : Set (ι → ℝ) → Prop
  | polynomial_zero (p : MvPolynomial ι ℝ) :
      IsSemialgebraic {x | MvPolynomial.eval x p = 0}
  | polynomial_pos (p : MvPolynomial ι ℝ) :
      IsSemialgebraic {x | 0 < MvPolynomial.eval x p}
  | union {s t : Set (ι → ℝ)} : IsSemialgebraic s → IsSemialgebraic t →
      IsSemialgebraic (s ∪ t)
  | inter {s t : Set (ι → ℝ)} : IsSemialgebraic s → IsSemialgebraic t →
      IsSemialgebraic (s ∩ t)
  | compl {s : Set (ι → ℝ)} : IsSemialgebraic s → IsSemialgebraic sᶜ

/-- The empty subset of a finite real coordinate space is semialgebraic. -/
theorem isSemialgebraic_empty {ι : Type*} [Fintype ι] :
    IsSemialgebraic (∅ : Set (ι → ℝ)) := by
  simpa using IsSemialgebraic.polynomial_pos (0 : MvPolynomial ι ℝ)

/-- The whole finite real coordinate space is semialgebraic. -/
theorem isSemialgebraic_univ {ι : Type*} [Fintype ι] :
    IsSemialgebraic (Set.univ : Set (ι → ℝ)) := by
  simpa using isSemialgebraic_empty.compl

/-- A finite union of semialgebraic sets is semialgebraic. -/
theorem isSemialgebraic_iUnion_fin {ι : Type*} [Fintype ι] {n : ℕ}
    {s : Fin n → Set (ι → ℝ)} (hs : ∀ i, IsSemialgebraic (s i)) :
    IsSemialgebraic (⋃ i, s i) := by
  have hfin : ∀ u : Finset (Fin n), IsSemialgebraic (⋃ i ∈ u, s i) := by
    intro u
    induction u using Finset.induction_on with
    | empty => simpa using (isSemialgebraic_empty (ι := ι))
    | @insert a u ha ih =>
        simpa only [Finset.set_biUnion_insert] using (hs a).union ih
  simpa using hfin Finset.univ

/-- Restrict a point to the coordinates selected by an embedding. -/
def coordinateProjection {ι κ : Type*} (e : κ ↪ ι) : (ι → ℝ) → (κ → ℝ) :=
  fun x k => x (e k)

/-- Pulling a semialgebraic set back along a coordinate map preserves semialgebraicity. -/
private theorem IsSemialgebraic.coordinatePreimage {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : κ → ι) {s : Set (κ → ℝ)} (hs : IsSemialgebraic s) :
    IsSemialgebraic {x | (fun k => x (e k)) ∈ s} := by
  induction hs with
  | polynomial_zero p =>
      convert IsSemialgebraic.polynomial_zero (MvPolynomial.rename e p) using 1
      ext x
      simp [Function.comp_def, MvPolynomial.eval_rename]
  | polynomial_pos p =>
      convert IsSemialgebraic.polynomial_pos (MvPolynomial.rename e p) using 1
      ext x
      simp [Function.comp_def, MvPolynomial.eval_rename]
  | union hs ht ihs iht =>
      convert ihs.union iht using 1
      ext x
      simp
  | inter hs ht ihs iht =>
      convert ihs.inter iht using 1
      ext x
      simp
  | compl hs ih =>
      convert ih.compl using 1
      ext x
      simp

/-- **Tarski--Seidenberg.** The image of a semialgebraic set under any coordinate projection is
semialgebraic (Bochnak--Coste--Roy, Theorem 2.2.1). -/
theorem isSemialgebraic_coordinateProjection {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : κ ↪ ι) {s : Set (ι → ℝ)} (hs : IsSemialgebraic s) :
    IsSemialgebraic (coordinateProjection e '' s) := by
  -- Foundational proof obligation: eliminate the finitely many coordinates outside `e.range`
  -- from the quantifier-free Boolean combination represented by `hs`.  Mathlib's available
  -- quantifier-elimination development is Presburger/semilinear, not real-closed-field
  -- quantifier elimination, so this cannot be discharged by importing an existing theorem.
  sorry

/-- The coordinate product of two subsets, represented in the coordinate space indexed by a sum. -/
def coordinateProduct {ι κ : Type*} (s : Set (ι → ℝ)) (t : Set (κ → ℝ)) :
    Set (Sum ι κ → ℝ) :=
  {z | (fun i => z (.inl i)) ∈ s ∧ (fun k => z (.inr k)) ∈ t}

/-- Products of semialgebraic subsets of finite coordinate spaces are semialgebraic. -/
theorem IsSemialgebraic.coordinateProduct {ι κ : Type*} [Fintype ι] [Fintype κ]
    {s : Set (ι → ℝ)} {t : Set (κ → ℝ)} (hs : IsSemialgebraic s)
    (ht : IsSemialgebraic t) : IsSemialgebraic (coordinateProduct s t) := by
  exact (hs.coordinatePreimage Sum.inl).inter (ht.coordinatePreimage Sum.inr)

/-- The graph of a map over a specified domain, represented in a sum-indexed coordinate space. -/
def graphOn {ι κ : Type*} (f : (ι → ℝ) → (κ → ℝ)) (s : Set (ι → ℝ)) :
    Set (Sum ι κ → ℝ) :=
  {z | (fun i => z (.inl i)) ∈ s ∧ f (fun i => z (.inl i)) = fun k => z (.inr k)}

/-- A map on a semialgebraic domain is semialgebraic when its restricted graph is semialgebraic. -/
def IsSemialgebraicMap {ι κ : Type*} [Fintype ι] [Fintype κ]
    (s : Set (ι → ℝ)) (f : (ι → ℝ) → (κ → ℝ)) : Prop :=
  IsSemialgebraic (graphOn f s)

/-- The image of a semialgebraic set under a semialgebraic map is semialgebraic. -/
theorem IsSemialgebraicMap.image {ι κ : Type*} [Fintype ι] [Fintype κ]
    {s : Set (ι → ℝ)} {f : (ι → ℝ) → (κ → ℝ)}
    (hf : IsSemialgebraicMap s f) : IsSemialgebraic (f '' s) := by
  let e : κ ↪ Sum ι κ := ⟨Sum.inr, Sum.inr_injective⟩
  have h := isSemialgebraic_coordinateProjection e hf
  convert h using 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨Sum.elim x (f x), ?_, ?_⟩
    · exact ⟨hx, rfl⟩
    · rfl
  · rintro ⟨z, ⟨hzs, hzf⟩, hzy⟩
    refine ⟨fun i => z (.inl i), hzs, ?_⟩
    rw [hzf]
    exact hzy

private theorem isSemialgebraic_iInter_fintype {ι κ : Type*} [Fintype ι] [Finite κ]
    {t : κ → Set (ι → ℝ)} (ht : ∀ k, IsSemialgebraic (t k)) :
    IsSemialgebraic (⋂ k, t k) := by
  classical
  let _ := Fintype.ofFinite κ
  have hfin : ∀ u : Finset κ, IsSemialgebraic (⋂ k ∈ u, t k) := by
    intro u
    induction u using Finset.induction_on with
    | empty => simpa using (isSemialgebraic_univ (ι := ι))
    | @insert k u hk ih =>
        simpa only [Finset.set_biInter_insert] using (ht k).inter ih
  simpa using hfin Finset.univ

/-- The closure of a semialgebraic set is semialgebraic. -/
theorem IsSemialgebraic.closure {ι : Type*} [Fintype ι] {s : Set (ι → ℝ)}
    (hs : IsSemialgebraic s) : IsSemialgebraic (closure s) := by
  classical
  let big := Sum (Sum ι Unit) ι
  let _ : Fintype big := inferInstance
  let boxWitness : Set (big → ℝ) :=
    {z | (fun i => z (.inr i)) ∈ s ∧
      ∀ i, z (.inr i) - z (.inl (.inl i)) < z (.inl (.inr ())) ∧
        z (.inl (.inl i)) - z (.inr i) < z (.inl (.inr ()))}
  have hupper (i : ι) : IsSemialgebraic
      {z : big → ℝ | z (.inr i) - z (.inl (.inl i)) < z (.inl (.inr ()))} := by
    convert IsSemialgebraic.polynomial_pos
      (MvPolynomial.X (Sum.inl (Sum.inr ()) : big) -
        (MvPolynomial.X (Sum.inr i : big) -
          MvPolynomial.X (Sum.inl (Sum.inl i) : big))) using 1
    ext z
    simp only [MvPolynomial.eval_sub, MvPolynomial.eval_X, sub_pos]
    rfl
  have hlower (i : ι) : IsSemialgebraic
      {z : big → ℝ | z (.inl (.inl i)) - z (.inr i) < z (.inl (.inr ()))} := by
    convert IsSemialgebraic.polynomial_pos
      (MvPolynomial.X (Sum.inl (Sum.inr ()) : big) -
        (MvPolynomial.X (Sum.inl (Sum.inl i) : big) -
          MvPolynomial.X (Sum.inr i : big))) using 1
    ext z
    simp only [MvPolynomial.eval_sub, MvPolynomial.eval_X, sub_pos]
    rfl
  have hboxes : IsSemialgebraic
      {z : big → ℝ | ∀ i,
        z (.inr i) - z (.inl (.inl i)) < z (.inl (.inr ())) ∧
          z (.inl (.inl i)) - z (.inr i) < z (.inl (.inr ()))} := by
    convert isSemialgebraic_iInter_fintype
      (fun i => (hupper i).inter (hlower i)) using 1
    ext z
    simp only [mem_iInter, mem_inter_iff, mem_ofPred_eq]
  have hboxWitness : IsSemialgebraic boxWitness := by
    have hsBig : IsSemialgebraic
        {z : big → ℝ | (fun i => z (.inr i)) ∈ s} :=
      hs.coordinatePreimage (fun i : ι => (Sum.inr i : big))
    unfold boxWitness
    convert hsBig.inter hboxes using 1
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq]
  let keepXR : Sum ι Unit ↪ big := ⟨Sum.inl, Sum.inl_injective⟩
  let hasBoxWitness : Set (Sum ι Unit → ℝ) :=
    coordinateProjection keepXR '' boxWitness
  have hHasBoxWitness : IsSemialgebraic hasBoxWitness :=
    isSemialgebraic_coordinateProjection keepXR hboxWitness
  have hHasBoxWitness_iff (q : Sum ι Unit → ℝ) :
      q ∈ hasBoxWitness ↔ ∃ y ∈ s, ∀ i,
        y i - q (.inl i) < q (.inr ()) ∧ q (.inl i) - y i < q (.inr ()) := by
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨fun i => z (.inr i), hz.1, hz.2⟩
    · rintro ⟨y, hys, hy⟩
      let z : big → ℝ := Sum.elim q y
      refine ⟨z, ?_, ?_⟩
      · exact ⟨hys, hy⟩
      · rfl
  have hpositive : IsSemialgebraic
      {q : Sum ι Unit → ℝ | 0 < q (.inr ())} := by
    convert IsSemialgebraic.polynomial_pos
      (MvPolynomial.X (.inr ()) : MvPolynomial (Sum ι Unit) ℝ) using 1
    ext q
    simp only [MvPolynomial.eval_X]
  let badPairs : Set (Sum ι Unit → ℝ) :=
    {q | 0 < q (.inr ())} ∩ hasBoxWitnessᶜ
  have hBadPairs : IsSemialgebraic badPairs := by
    exact hpositive.inter hHasBoxWitness.compl
  let keepX : ι ↪ Sum ι Unit := ⟨Sum.inl, Sum.inl_injective⟩
  have hBadX : IsSemialgebraic (coordinateProjection keepX '' badPairs) :=
    isSemialgebraic_coordinateProjection keepX hBadPairs
  have hBadX_iff (x : ι → ℝ) :
      x ∈ coordinateProjection keepX '' badPairs ↔
        ∃ r > 0, ¬ ∃ y ∈ s, ∀ i, y i - x i < r ∧ x i - y i < r := by
    constructor
    · rintro ⟨q, hq, hqx⟩
      have hcoord (i : ι) : q (.inl i) = x i := by
        have hqx' := hqx
        dsimp [coordinateProjection, keepX] at hqx'
        exact congrFun hqx' i
      refine ⟨q (.inr ()), hq.1, ?_⟩
      intro hy
      apply hq.2
      apply (hHasBoxWitness_iff q).2
      simpa only [hcoord] using hy
    · rintro ⟨r, hr, hnone⟩
      let q : Sum ι Unit → ℝ := Sum.elim x (fun _ => r)
      refine ⟨q, ⟨hr, ?_⟩, ?_⟩
      · change q ∉ hasBoxWitness
        rw [hHasBoxWitness_iff]
        simpa only [q, Sum.elim_inl, Sum.elim_inr] using hnone
      · rfl
  have hresult : IsSemialgebraic
      ((coordinateProjection keepX '' badPairs)ᶜ) := hBadX.compl
  convert hresult using 1
  ext x
  change (x ∈ _root_.closure s ↔ x ∉ coordinateProjection keepX '' badPairs)
  rw [Metric.mem_closure_iff, hBadX_iff]
  constructor
  · intro h
    rintro ⟨r, hr, hnone⟩
    rcases h r hr with ⟨y, hys, hy⟩
    apply hnone
    refine ⟨y, hys, ?_⟩
    rw [dist_pi_lt_iff hr] at hy
    intro i
    have hi := hy i
    rw [Real.dist_eq, abs_lt] at hi
    constructor <;> linarith
  · intro h ε hε
    by_contra hnone
    apply h
    refine ⟨ε, hε, ?_⟩
    rintro ⟨y, hys, hy⟩
    apply hnone
    refine ⟨y, hys, ?_⟩
    rw [dist_pi_lt_iff hε]
    intro i
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hy i]

/-- The interior of a semialgebraic set is semialgebraic. -/
theorem IsSemialgebraic.interior {ι : Type*} [Fintype ι] {s : Set (ι → ℝ)}
    (hs : IsSemialgebraic s) : IsSemialgebraic (interior s) := by
  simpa only [interior_eq_compl_closure_compl] using hs.compl.closure.compl

/-- The topological boundary of a semialgebraic set is semialgebraic. -/
theorem IsSemialgebraic.frontier {ι : Type*} [Fintype ι] {s : Set (ι → ℝ)}
    (hs : IsSemialgebraic s) : IsSemialgebraic (frontier s) := by
  rw [frontier_eq_closure_inter_closure]
  exact hs.closure.inter hs.compl.closure

end CausalSmith.SemialgebraicStratificationSard
