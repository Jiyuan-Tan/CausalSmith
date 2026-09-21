module
public import Causalean.Stat.Concentration.Covering.DudleyEntropy.PartA
public import Causalean.Stat.Concentration.TailBounds.Massart

/-!
This module contains the finite-class construction underlying the Part B
chaining estimate. It uses the canonical Massart bound and exposes only the
adjacent-pair finite set and the intermediate estimate needed by `PartB`.
-/

@[expose] public section

namespace Causalean.Stat.Concentration

universe v u
open scoped BigOperators
open ProbabilityTheory

section Empirical
variable {Z : Type v}
variable {n m : ℕ} {ι : Type u} [Nonempty ι]
variable {F : ι → Z → ℝ}
variable {S : Fin m → Z}

variable {c : ℝ}
/-- For [a function class on a finite sample](hyp:Z,m,ι,F,S), [a radius](hyp:c),
[positivity](hyp:c_pos), [total boundedness](hyp:h), [a number of levels](hyp:n), and [a
level](hyp:j), this is [the set of adjacent chaining increments](goal). -/
private noncomputable def incrementSet (c_pos : 0 < c)
    (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ)
    (j : Fin n)
  := {chainApprox c_pos h fh (j + 1) - chainApprox c_pos h fh j | fh : ι}

/-- For [a function class on a finite sample](hyp:Z,m,ι,F,S), [a radius](hyp:c),
[positivity of that radius](hyp:c_pos), [total boundedness](hyp:h), [a number of
levels](hyp:n), and [a level](hyp:j), this is [the set of adjacent chaining-approximation
pairs](goal). -/
noncomputable def incrementPairSet (c_pos : 0 < c)
    (h : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ)
    (j : Fin n)
  := {(chainApprox c_pos h fh (j + 1), chainApprox c_pos h fh j) | fh : ι}

/-- For [a function class on a finite sample](hyp:Z,m,ι,F,S), [a radius](hyp:c),
[positivity](hyp:c_pos), [total boundedness](hyp:h'), [a number of levels](hyp:n), and [a
level](hyp:j), [the image of the chaining approximation is finite](goal). -/
private lemma finite_chainApprox_image (c_pos : 0 < c)
    (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ)
    (j : Fin n) :
  {chainApprox c_pos h' fh j | fh : ι}.Finite := by
  dsimp [chainApprox]
  by_cases h : (j : ℕ) = 0
  · rw [h]
    simp
  · simp [h]
    dsimp [coverApprox]
    have finite_F_image : {F f.index | f ∈ cj c_pos h' (j : ℕ)}.Finite := by
      have : (SetLike.coe (cj c_pos h' (j : ℕ))).Finite := Finset.finite_toSet _
      exact this.image (fun f => F f.index)
    apply finite_F_image.subset
    intro p hp
    simp at hp
    obtain ⟨r, hpr⟩ := hp
    simp
    use Classical.choose (exists_cover_approximation c_pos h' r (j : ℕ))
    constructor
    · rcases Classical.choose_spec (exists_cover_approximation c_pos h' r (j : ℕ)) with ⟨hmem, hle⟩
      exact hmem
    · exact hpr

/-- For [a function class on a finite sample](hyp:Z,m,ι,F,S), [a radius](hyp:c),
[positivity](hyp:c_pos), [total boundedness](hyp:h'), [a number of levels](hyp:n), and [a
level](hyp:j), this is [the set of next-level approximations](goal). -/
private noncomputable def nextApproxSet (c_pos : 0 < c)
    (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ)
    (j : Fin n) :=
  {chainApprox c_pos h' fh (j + 1) | fh : ι}

/-- For [a function class on a finite sample](hyp:Z,m,ι,F,S), [a radius](hyp:c),
[positivity](hyp:c_pos), [total boundedness](hyp:h'), [a number of levels](hyp:n), and [a
level](hyp:j), this is [the set of current-level approximations](goal). -/
private noncomputable def currApproxSet (c_pos : 0 < c)
    (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ)
    (j : Fin n) :=
  {chainApprox c_pos h' fh j | fh : ι}

/-- For [a function class on a finite sample](hyp:Z,m,ι,F,S), [a radius](hyp:c),
[positivity](hyp:c_pos), [total boundedness](hyp:h'), [a number of levels](hyp:n), and [a
level](hyp:j), this is [the product of the next- and current-level approximation sets](goal). -/
private noncomputable def approxPairSet (c_pos : 0 < c)
    (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ)
    (j : Fin n) :=
  (nextApproxSet c_pos h' n j) ×ˢ (currApproxSet c_pos h' n j)

/-- For [a function class on a finite sample](hyp:Z,m,ι,F,S), [a radius](hyp:c),
[positivity](hyp:c_pos), [total boundedness](hyp:h'), [a number of levels](hyp:n), and [a
level](hyp:j), [the next-level approximation set is finite](goal). -/
private lemma finite_nextApproxSet (c_pos : 0 < c)
    (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ)
    (j : Fin n) :
  (nextApproxSet c_pos h' n j).Finite :=
    finite_chainApprox_image c_pos h' (n + 1) ⟨j + 1, by simp⟩

/-- For [a function class on a finite sample](hyp:Z,m,ι,F,S), [a radius](hyp:c),
[positivity](hyp:c_pos), [total boundedness](hyp:h'), [a number of levels](hyp:n), and [a
level](hyp:j), [the current-level approximation set is finite](goal). -/
private lemma finite_currApproxSet (c_pos : 0 < c)
    (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ)
    (j : Fin n) :
  (currApproxSet c_pos h' n j).Finite := finite_chainApprox_image c_pos h' n j

/-- For [a function class on a finite sample](hyp:Z,m,ι,F,S), [a radius](hyp:c),
[positivity](hyp:c_pos), [total boundedness](hyp:h'), [a number of levels](hyp:n), and [a
level](hyp:j), [the product approximation set is finite](goal). -/
private lemma finite_approxPairSet (c_pos : 0 < c)
    (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ)
    (j : Fin n) :
  ((nextApproxSet c_pos h' n j) ×ˢ (currApproxSet c_pos h' n j)).Finite :=
    (finite_nextApproxSet c_pos h' n j).prod (finite_currApproxSet c_pos h' n j)

omit [Nonempty ι] in
/-- For [a function class on a finite sample](hyp:Z,m,ι,F,S), [a radius](hyp:c),
[positivity](hyp:c_pos), [total boundedness](hyp:h'), [a number of levels](hyp:n), and [a
level](hyp:j), [each adjacent pair lies in the product approximation set](goal). -/
private lemma incrementPairSet_subset_approxPairSet (c_pos : 0 < c)
    (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ)
    (j : Fin n) :
    (incrementPairSet c_pos h' n j) ⊆ (approxPairSet c_pos h' n j) := by
  intro f hf
  obtain ⟨f0, hg⟩ := hf
  rw [<- hg]
  refine Set.mk_mem_prod (by use f0) (by use f0)

/-- For [a function class on a finite sample](hyp:Z,m,ι,F,S), [a radius](hyp:c),
[positivity](hyp:c_pos), [total boundedness](hyp:h'), [a number of levels](hyp:n), and [a
level](hyp:j), [the adjacent-pair set is finite](goal). -/
lemma finite_incrementPairSet (c_pos : 0 < c)
    (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ)
    (j : Fin n) :
  (incrementPairSet c_pos h' n j).Finite := by
  unfold incrementPairSet
  refine (finite_approxPairSet c_pos h' n j).subset ?_
  apply incrementPairSet_subset_approxPairSet

/-- For [a function class on a finite sample](hyp:Z,m,ι,F,S), [a radius](hyp:c),
[positivity](hyp:c_pos), [total boundedness](hyp:h'), [a number of levels](hyp:n), and [a
level](hyp:j), [the increment set is finite](goal). -/
private lemma finite_incrementSet (c_pos : 0 < c)
    (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ)
    (j : Fin n) :
  (incrementSet c_pos h' n j).Finite := by
  unfold incrementSet
  let f : (Z → ℝ) × (Z → ℝ) → (Z → ℝ) := fun p => p.1 - p.2
  have :
      {chainApprox c_pos h' fh (j + 1) - chainApprox c_pos h' fh j | fh : ι} =
        f '' incrementPairSet c_pos h' n j := by
    ext x
    simp [incrementPairSet]
    constructor
    · rintro ⟨fh, rfl⟩
      use fh
    · rintro ⟨w', hw⟩
      use w'
  rw [this]
  exact (finite_incrementPairSet c_pos h' n j).image f

/-- For [a function class on a finite sample](hyp:Z,m,ι,F,S), [a radius](hyp:c),
[positivity](hyp:c_pos), [total boundedness](hyp:h'), [a number of levels](hyp:n), and [a
level](hyp:j), this is [the finite set of next-level approximations](goal). -/
private noncomputable def nextApproxFinset (c_pos : 0 < c)
    (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ)
    (j : Fin n)
  := Set.Finite.toFinset (finite_nextApproxSet c_pos h' n j)

/-- For [a function class on a finite sample](hyp:Z,m,ι,F,S), [a radius](hyp:c),
[positivity](hyp:c_pos), [total boundedness](hyp:h'), [a number of levels](hyp:n), and [a
level](hyp:j), this is [the finite set of current-level approximations](goal). -/
private noncomputable def currApproxFinset (c_pos : 0 < c)
    (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ)
    (j : Fin n)
  := Set.Finite.toFinset (finite_currApproxSet c_pos h' n j)

/-- For [a function class on a finite sample](hyp:Z,m,ι,F,S), [a radius](hyp:c),
[positivity](hyp:c_pos), [total boundedness](hyp:h'), [a number of levels](hyp:n), and [a
level](hyp:j), this is [the finite set of adjacent chaining increments](goal). -/
private noncomputable def incrementFinset (c_pos : 0 < c)
    (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ)
    (j : Fin n)
  := Set.Finite.toFinset (finite_incrementSet c_pos h' n j)

/-- For [a function class on a finite sample](hyp:Z,m,ι,F,S), [a radius](hyp:c),
[positivity of that radius](hyp:c_pos), [total boundedness](hyp:h'), [a number of
levels](hyp:n), and [a level](hyp:j), this is [the finite set of distinct adjacent
chaining-approximation pairs](goal). -/
noncomputable def incrementPairFinset (c_pos : 0 < c)
    (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ)
    (j : Fin n)
  := Set.Finite.toFinset (finite_incrementPairSet c_pos h' n j)

/-- For [a function class on a finite sample](hyp:Z,m,ι,F,S), [a radius](hyp:c),
[positivity](hyp:c_pos), [total boundedness](hyp:h'), [a number of levels](hyp:n), and [a
level](hyp:j), this is [the finite product approximation set](goal). -/
private noncomputable def approxPairFinset (c_pos : 0 < c)
    (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ)
    (j : Fin n)
  := Set.Finite.toFinset (finite_approxPairSet c_pos h' n j)

/-- For [a function class on a finite sample](hyp:Z,m,ι,F,S), [a radius](hyp:c),
[positivity](hyp:c_pos), [total boundedness](hyp:h'), [a number of levels](hyp:n), and [a
level](hyp:j), [the increment finite set is nonempty](goal). -/
private lemma incrementFinset_nonempty (c_pos : 0 < c)
    (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ)
    (j : Fin n) :
  (incrementFinset c_pos h' n j).Nonempty := by
  dsimp [incrementFinset]
  simp only [Set.Finite.toFinset_nonempty]
  exact ⟨_, ⟨Classical.arbitrary ι, rfl⟩⟩

/-- For [a function class on a finite sample](hyp:Z,m,ι,F,S), [a radius](hyp:c),
[positivity of that radius](hyp:c_pos), [total boundedness](hyp:h'), [a number of
levels](hyp:n), and [a level](hyp:j), the finite set of adjacent chaining-approximation pairs
is [nonempty](goal). -/
lemma incrementPairFinset_nonempty (c_pos : 0 < c)
    (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ)
    (j : Fin n) :
  (incrementPairFinset c_pos h' n j).Nonempty := by
  dsimp [incrementPairFinset]
  simp only [Set.Finite.toFinset_nonempty]
  exact ⟨_, ⟨Classical.arbitrary ι, rfl⟩⟩

/-- For [a function class on a finite sample](hyp:Z,m,ι,F,S), [a radius](hyp:c),
[positivity](hyp:c_pos), [total boundedness](hyp:h'), [a number of levels](hyp:n), and [a
level](hyp:j), [the increment-set cardinality is at most the adjacent-pair cardinality](goal). -/
private lemma incrementFinset_card_le_incrementPairFinset_card (c_pos : 0 < c)
    (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ)
    (j : Fin n) :
  (incrementFinset c_pos h' n j).card ≤ (incrementPairFinset c_pos h' n j).card := by
  unfold incrementFinset incrementPairFinset
  let f : (Z → ℝ) × (Z → ℝ) → (Z → ℝ) := fun p => p.1 - p.2
  apply Finset.card_le_card_of_surjOn f
  dsimp [Set.SurjOn]
  intro e es
  simp at es
  simp
  rcases es with ⟨fh, rfl⟩
  refine ⟨_, _, ?_, rfl⟩
  exact ⟨fh, rfl⟩

/-- For [a function class on a finite sample](hyp:Z,m,ι,F,S), [a radius](hyp:c),
[positivity](hyp:c_pos), [total boundedness](hyp:h'), [a number of levels](hyp:n), and [a
level](hyp:j), [the adjacent-pair cardinality is at most the product-set cardinality](goal). -/
private lemma incrementPairFinset_card_le_approxPairFinset_card (c_pos : 0 < c)
    (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ)
    (j : Fin n) :
    (incrementPairFinset c_pos h' n j).card ≤ (approxPairFinset c_pos h' n j).card := by
  unfold incrementPairFinset approxPairFinset
  refine Finset.card_le_card ?_
  refine Set.Finite.toFinset_subset_toFinset.mpr ?_
  apply incrementPairSet_subset_approxPairSet

/-- For [a function class on a finite sample](hyp:Z,m,ι,F,S), [a radius](hyp:c),
[positivity](hyp:c_pos), [total boundedness](hyp:h'), [a number of levels](hyp:n), and [a
level](hyp:j), [the product-set cardinality factors into its two marginal cardinalities](goal). -/
private lemma approxPairFinset_card_eq_product (c_pos : 0 < c)
    (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ)
    (j : Fin n) :
  (approxPairFinset c_pos h' n j).card =
    (nextApproxFinset c_pos h' n j).card * (currApproxFinset c_pos h' n j).card := by
  rw [<- Finset.card_product]
  refine Finset.card_eq_of_equiv ?_
  simp
  dsimp [nextApproxFinset, approxPairFinset, currApproxFinset]
  simp
  exact Equiv.refl _

/-- For [a function class on a finite sample](hyp:Z,m,ι,F,S), [a radius](hyp:c),
[positivity](hyp:c_pos), [total boundedness](hyp:h'), [a number of levels](hyp:n), and [a
level](hyp:j), [the next-approximation cardinality is bounded by the next cover](goal). -/
private lemma nextApproxFinset_card_le_cover_card (c_pos : 0 < c)
    (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ)
    (j : Fin n) :
  (nextApproxFinset c_pos h' n j).card ≤ (cj c_pos h' ((j : ℕ) + 1)).card := by
  -- expand `nextApproxFinset`: functions of the form `chainApprox c_pos h' fh (j+1)`
  -- coming from the cover at scale `j+1`.
  dsimp [nextApproxFinset]
  classical
  -- image of the cover under coercion to functions
  -- coerce elements of the cover to functions before taking the image
  let T : Finset (Z → ℝ) :=
    (cj c_pos h' ((j : ℕ) + 1)).image
      (fun q : EmpiricalFunctionSpace F S => (q : Z → ℝ))
  -- every element of `nextApproxFinset` comes from this image via `coverApprox_mem_cover`
  have hsubset : Set.Finite.toFinset (finite_nextApproxSet c_pos h' n j) ⊆ T := by
    intro x hx
    have hxA : x ∈ nextApproxSet c_pos h' n j := by
      simpa [nextApproxFinset] using hx
    rcases hxA with ⟨fh, rfl⟩
    -- rewrite chainApprox at successor
    have hG :
        chainApprox c_pos h' fh ((j : ℕ) + 1) =
          (coverApprox c_pos h' fh ((j : ℕ) + 1) : Z → ℝ) := by
      simp [chainApprox_succ]
    -- show the corresponding `coverApprox` lies in the cover
    have hmem :
        coverApprox c_pos h' fh ((j : ℕ) + 1) ∈ cj c_pos h' ((j : ℕ) + 1) := by
      apply coverApprox_mem_cover
    -- build membership in the image finset
    -- membership in the image finset
    have hQmem : (coverApprox c_pos h' fh ((j : ℕ) + 1) : Z → ℝ) ∈ T := by
      -- unfold `T` and register the element explicitly
      dsimp [T]
      refine Finset.mem_image.mpr ?_
      refine ⟨coverApprox c_pos h' fh ((j : ℕ) + 1), hmem, rfl⟩
    simpa [hG] using hQmem
  have hcard_le_T : (Set.Finite.toFinset (finite_nextApproxSet c_pos h' n j)).card ≤ T.card := by
    exact Finset.card_le_card hsubset
  have hT_le : T.card ≤ (cj c_pos h' ((j : ℕ) + 1)).card := Finset.card_image_le
  exact hcard_le_T.trans hT_le

/-- For [a function class on a finite sample](hyp:Z,m,ι,F,S), [a radius](hyp:c),
[positivity](hyp:c_pos), [total boundedness](hyp:h'), [a number of levels](hyp:n), [a
level](hyp:j), and [a positive number of levels](hyp:n_pos), [the current-approximation
cardinality is bounded by the current cover](goal). -/
private lemma currApproxFinset_card_le_cover_card (c_pos : 0 < c)
    (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ)
    (j : Fin n) (n_pos : 0 < n) :
  (currApproxFinset c_pos h' n j).card ≤ (cj c_pos h' (j : ℕ)).card := by
  -- expand `currApproxFinset`: functions of the form `chainApprox … fh j` live in the
  -- cover at scale `j`
  dsimp [currApproxFinset]
  classical
  -- image of the cover under coercion to functions
  let T : Finset (Z → ℝ) :=
    (cj c_pos h' ((j : ℕ))).image (fun q : EmpiricalFunctionSpace F S => (q : Z → ℝ))
  -- every element of `currApproxFinset` comes from this image via `coverApprox_mem_cover`,
  -- with a small case split on `(j : ℕ) = 0`
  by_cases hzero : ((j : ℕ)) = 0
  · -- when j = 0, chainApprox = 0, so currApproxFinset has card 1 ≤ cover card
    rw [hzero]
    -- currApproxFinset card is 1
    have hKB : (currApproxFinset c_pos h' n ⟨0, by
      -- j.isLt : ((j : ℕ)) < n; with hzero we get 0 < n
      have := j.isLt
      simpa [hzero] using this⟩).card = 1 := by
      -- currApproxSet is {0}, so its toFinset has one element
      simp [currApproxFinset, currApproxSet, chainApprox]
    -- cover at scale 0 is nonempty: use any fh
    classical
    obtain ⟨fh0⟩ := (inferInstance : Nonempty ι)
    have hcov : (cj c_pos h' 0).Nonempty := by
      exact ⟨coverApprox c_pos h' fh0 0, coverApprox_mem_cover c_pos h' fh0 0⟩
    have hcover_card : 1 ≤ (cj c_pos h' 0).card := by
      simpa [Nat.succ_le_iff, Finset.card_pos] using hcov
    -- rewrite j to ⟨0, _⟩ to align indices and conclude
    have hj : j = ⟨0, by
      have := j.isLt
      simpa [hzero] using this⟩ := by
      cases j with
      | mk jv jlt =>
        cases hzero
        rfl
    rw [hj]
    -- relate the left card to 1 using hKB, then compare with the cover card
    have hBcard : (Set.Finite.toFinset (finite_currApproxSet c_pos h' n ⟨0, n_pos⟩)).card = 1 := by
      -- currApproxFinset is exactly this toFinset
      simpa [currApproxFinset] using hKB
    have :
        (Set.Finite.toFinset (finite_currApproxSet c_pos h' n ⟨0, n_pos⟩)).card ≤
          (cj c_pos h' 0).card := by
      -- rewrite the left card to 1 and use the cover-card lower bound
      simpa [hBcard] using hcover_card
    exact this
  · -- j ≠ 0: use chainApprox_succ and coverApprox_mem_cover to build the subset/image argument
    have hsubset : Set.Finite.toFinset (finite_currApproxSet c_pos h' n j) ⊆ T := by
      intro x hx
      have hxB : x ∈ currApproxSet c_pos h' n j := by simpa [currApproxFinset] using hx
      rcases hxB with ⟨fh, rfl⟩
      have hG :
          chainApprox c_pos h' fh ((j : ℕ)) =
            (coverApprox c_pos h' fh ((j : ℕ)) : Z → ℝ) := by
        have : ∃ k, (j : ℕ) = k + 1 := Nat.exists_eq_succ_of_ne_zero hzero
        rcases this with ⟨k, hk⟩
        rw [hk]
        simp [chainApprox_succ]
      have hmem : coverApprox c_pos h' fh ((j : ℕ)) ∈ cj c_pos h' ((j : ℕ)) :=
        coverApprox_mem_cover c_pos h' fh ((j : ℕ))
      have hQmem : (coverApprox c_pos h' fh ((j : ℕ)) : Z → ℝ) ∈ T := by
        dsimp [T]
        refine Finset.mem_image.mpr ?_
        exact ⟨coverApprox c_pos h' fh ((j : ℕ)), hmem, rfl⟩
      simpa [hG] using hQmem
    have hcard_le_T : (Set.Finite.toFinset (finite_currApproxSet c_pos h' n j)).card ≤ T.card := by
      exact Finset.card_le_card hsubset
    have hT_le : T.card ≤ (cj c_pos h' ((j : ℕ))).card := Finset.card_image_le
    exact hcard_le_T.trans hT_le

/-- For [a function class on a finite sample](hyp:Z,m,ι,F,S), [a radius](hyp:c),
[positivity](hyp:c_pos), [total boundedness](hyp:h'), [a number of levels](hyp:n), [a
level](hyp:j), and [a positive number of levels](hyp:n_pos), [the adjacent-pair cardinality is
bounded by the product of two covering cardinalities](goal). -/
private lemma incrementPairFinset_card_le_cover_product_card (c_pos : 0 < c)
    (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ)
    (j : Fin n) (n_pos : 0 < n) :
  (incrementPairFinset c_pos h' n j).card ≤
    (cj c_pos h' (j + 1)).card * (cj c_pos h' j).card := by
  calc
  _ ≤ (approxPairFinset c_pos h' n j).card := by
    apply incrementPairFinset_card_le_approxPairFinset_card
  _ = (nextApproxFinset c_pos h' n j).card * (currApproxFinset c_pos h' n j).card := by
    apply approxPairFinset_card_eq_product
  _ ≤ _ := by
    apply mul_le_mul
    apply nextApproxFinset_card_le_cover_card
    apply currApproxFinset_card_le_cover_card
    exact n_pos
    simp
    simp

omit [Nonempty ι] in
/-- For [a function class on a finite sample](hyp:Z,m,ι,F,S), [a radius](hyp:c),
[positivity](hyp:c_pos), [total boundedness](hyp:h'), [a level](hyp:j), [a sign vector](hyp:σ),
[a function index](hyp:fh), and [a uniform empirical-radius bound](hyp:cs), [the signed
chaining increment is bounded by its adjacent dyadic radii](goal). -/
private lemma chainApprox_increment_signed_sum_bound (c_pos : 0 < c)
    (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (j : ℕ)
  (σ : Signs m) (fh : ι) (cs : ∀ f : ι, empiricalNorm S (F f) ≤ c) :
  ∑ i : Fin m, (σ i : ℝ) *
      (chainApprox c_pos h' fh (j + 1) - chainApprox c_pos h' fh j) (S i) ≤
    m * (c / 2 ^ (j + 1) + c / 2 ^ j) := by
  calc
  _ ≤ m * empiricalDist S (chainApprox c_pos h' fh (j + 1))
      (chainApprox c_pos h' fh j) := by
    apply signed_sum_le_empiricalDist (chainApprox c_pos h' fh (j + 1))
      (chainApprox c_pos h' fh j) σ
  _ ≤ _ := by
    apply mul_le_mul_of_nonneg_left _ (by simp)
    calc
    _ ≤ empiricalDist S (chainApprox c_pos h' fh (j + 1)) (F fh) +
        empiricalDist S (F fh) (chainApprox c_pos h' fh j) := by
      apply @dist_triangle _ (empiricalPMet S)
        (chainApprox c_pos h' fh (j + 1)) (F fh) (chainApprox c_pos h' fh j)
    _ ≤ _ := by
      rw [←empiricalDist_comm S (F fh) (chainApprox c_pos h' fh (j+1))]
      apply add_le_add
      · exact empiricalDist_to_chainApprox_le_ej c_pos h' fh (j+1) cs
      · exact empiricalDist_to_chainApprox_le_ej c_pos h' fh j cs

/-- For [a function class on a finite sample](hyp:Z,m,ι,F,S), [a radius](hyp:c),
[positivity](hyp:c_pos), [total boundedness](hyp:h'), [a number of levels](hyp:n), [a
level](hyp:j), [positive sample size](hyp:m_pos), and [a uniform empirical-radius bound](hyp:cs),
[the expected signed increment is bounded by its finite-class Massart expression](goal). -/
private lemma massart_bound_for_increment_term (c_pos : 0 < c)
    (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ)
    (j : Fin n) (m_pos : 0 < m)
  (cs : ∀ f : ι, empiricalNorm S (F f) ≤ c) :
  ((m : ℝ)⁻¹ * signs_card_inv m * ∑ σ : Signs m, ⨆ fh : ι,
    (∑ i : Fin m, (σ i : ℝ) *
      ((chainApprox c_pos h' fh (j + 1) - chainApprox c_pos h' fh j) (S i))))
  ≤ ((incrementFinset c_pos h' n j).sup' (incrementFinset_nonempty c_pos h' n j)
      fun j ↦ √(∑ i, (|j (S i)|) ^ 2)) *
      (√(2 * Real.log ((Set.Finite.toFinset (finite_incrementSet c_pos h' n j)).card))) /
      m := by
  let C :=
    ((incrementFinset c_pos h' n j).sup' (incrementFinset_nonempty c_pos h' n j)
      fun j ↦ √(∑ i, (|j (S i)|) ^ 2))
  calc
  _ = ((m : ℝ)⁻¹ * signs_card_inv m * ∑ σ : Signs m,
    ⨆ (fh : {x // x ∈ incrementFinset c_pos h' n j}),
    (∑ i : Fin m, (σ i : ℝ) * (fh.val (S i)))) := by
    congr
    ext σ
    apply le_antisymm
    · apply ciSup_le
      intro fh
      let hfh : {x // x ∈ incrementFinset c_pos h' n j} := by
        use chainApprox c_pos h' fh (j + 1) - chainApprox c_pos h' fh j
        exact (finite_incrementSet c_pos h' n j).mem_toFinset.mpr ⟨fh, rfl⟩
      convert le_ciSup _ hfh
      · congr
      · use m * (c / 2 ^ (j.1 + 1) + c / 2 ^ j.1)
        rintro x ⟨⟨g, hg'⟩, hg⟩
        rw [<-hg]
        dsimp [incrementFinset] at hg'
        simp at hg'
        obtain ⟨fh, hfh⟩ := hg'
        simp
        rw [<-hfh]
        exact chainApprox_increment_signed_sum_bound c_pos h' j.1 σ fh cs
    · have : Nonempty {x // x ∈ incrementFinset c_pos h' n j} := by
        obtain ⟨fh⟩ := (by assumption : Nonempty ι)
        use chainApprox c_pos h' fh (j + 1) - chainApprox c_pos h' fh j
        exact (finite_incrementSet c_pos h' n j).mem_toFinset.mpr ⟨fh, rfl⟩
      apply ciSup_le
      rintro ⟨g, hg⟩
      dsimp [incrementFinset] at hg
      simp at hg
      obtain ⟨fh, hfh⟩ := hg
      convert le_ciSup _ fh
      · congr
        ext i
        simp
        rw [<- hfh]
        simp
      · use m * (c / 2 ^ (j.1 + 1) + c / 2 ^ j.1)
        rintro x ⟨fh, hfh⟩
        rw [<-hfh]
        exact chainApprox_increment_signed_sum_bound c_pos h' j.1 σ fh cs
  _ = signs_card_inv m * ∑ σ : Signs m, ⨆ (fh : {x // x ∈ incrementFinset c_pos h' n j}),
    ((m : ℝ)⁻¹ * ∑ i : Fin m, (σ i : ℝ) * (fh.val (S i))) := by
    rw [mul_comm (m : ℝ)⁻¹ _, mul_assoc]
    congr
    rw [Finset.mul_sum]
    congr
    ext σ
    apply Real.mul_iSup_of_nonneg
    apply inv_nonneg_of_nonneg
    exact Nat.cast_nonneg' m
  _ = empiricalRademacherComplexity_pmf_without_abs m
      (Causalean.Stat.Concentration.F_on
        (ι := (Z → ℝ)) (Z := Z) (fun hk : Z → ℝ => hk)
        (incrementFinset c_pos h' n j)) S := by
    simp only [empiricalRademacherComplexity_pmf_without_abs, signVecPMF,
      Signs.card, Nat.cast_pow, Nat.cast_ofNat, Int.reduceNeg, Finset.mul_sum,
      PMF.integral_eq_sum, PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_pow,
      ENNReal.toReal_ofNat, smul_eq_mul, signs_card_inv]
    rfl
  _ ≤ C *
      (√(2 * Real.log ((Set.Finite.toFinset (finite_incrementSet c_pos h' n j)).card))) /
      m := by
    apply le_of_le_of_eq
    · apply Causalean.Stat.Concentration.massart_lemma_pmf
      · exact incrementFinset_nonempty c_pos h' n j
    · have :
          √(2 * Real.log ((Set.Finite.toFinset (finite_incrementSet c_pos h' n j)).card)) =
            √(2 * Real.log ↑(incrementFinset c_pos h' n j).card) := by
        apply congrArg
        apply congrArg
        apply congrArg
        exact rfl
      rw [this]
      dsimp [C]
      rw [mul_div_right_comm]
      rw [Mathlib.Tactic.LinearCombination.mul_eq_const]
      field_simp
      rw [Finset.mul₀_sup']
      apply congrArg
      ext i
      rw [<- Finset.sum_div]
      simp only [sq_abs, Nat.cast_nonneg, pow_succ_nonneg, Real.sqrt_div', Real.sqrt_sq]
      field_simp
      exact Nat.cast_nonneg m

/-- For [a function class on a finite sample](hyp:Z,m,ι,F,S), [a radius](hyp:c),
[positivity](hyp:c_pos), [total boundedness](hyp:h'), [a number of levels](hyp:n), [a
level](hyp:j), [an approximation pair](hyp:hk), and [membership in the increment-pair finite
set](hyp:hk0), [the pair is represented by adjacent chain approximations](goal). -/
theorem partB.mem_incrementPairFinset_repr (c_pos : 0 < c)
    (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ)
  (j : Fin n) (hk : (Z → ℝ) × (Z → ℝ))
  (hk0 : hk ∈ incrementPairFinset c_pos h' n j) :
  ∃ fh,
    (chainApprox c_pos h' fh ((j : ℕ) + 1),
      chainApprox c_pos h' fh (j : ℕ)) = hk := by
  dsimp [incrementPairFinset] at hk0
  simp at hk0
  dsimp [incrementPairSet] at hk0
  exact hk0

/-- For [a function class on a finite sample](hyp:Z,m,ι,F,S), [a radius](hyp:c),
[positivity of that radius](hyp:c_pos), [total boundedness](hyp:h'), [a number of
levels](hyp:n), [positive sample size](hyp:m_pos), [a uniform empirical-radius bound](hyp:cs),
and [at least one chaining level](hyp:n_pos), the signed increment sum is [bounded by the
Massart finite-class expression over adjacent approximation pairs](goal). -/
lemma partB_sum_bound_via_massart (c_pos : 0 < c)
    (h' : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S))) (n : ℕ)
    (m_pos : 0 < m)
  (cs : ∀ f : ι, empiricalNorm S (F f) ≤ c) (n_pos : 0 < n) :
  ∑ j : Fin n, ((m : ℝ)⁻¹ * signs_card_inv m * ∑ σ : Signs m, ⨆ fh : ι,
    (∑ i : Fin m, (σ i : ℝ) *
      ((chainApprox c_pos h' fh (j + 1) - chainApprox c_pos h' fh j) (S i)))) ≤
  ∑ j : Fin n,
    (Finset.sup' (incrementPairFinset c_pos h' n j)
      (incrementPairFinset_nonempty c_pos h' n j)
      fun hk ↦ √(∑ i : Fin m, ((hk.1 - hk.2) (S i)) ^ 2)) *
      (√(2 * Real.log (coveringNumber' h' (ej c (j + 1)) *
        coveringNumber' h' (ej c j)))) / ↑m := by
  -- It suffices to prove the bound term-by-term in the finite sum over j.
  apply Finset.sum_le_sum
  intro j hj
  -- Replace the supremum over f with a finite supremum over the paired class.
  calc
  _ ≤ ((incrementFinset c_pos h' n j).sup' (incrementFinset_nonempty c_pos h' n j)
          fun j ↦ √(∑ i, (|j (S i)|) ^ 2)) *
        (√(2 * Real.log ((Set.Finite.toFinset (finite_incrementSet c_pos h' n j)).card))) /
        m := massart_bound_for_increment_term c_pos h' n j m_pos cs
  _ ≤ ((Finset.sup' (incrementPairFinset c_pos h' n j)
          (incrementPairFinset_nonempty c_pos h' n j)
          fun hk ↦ √(∑ i : Fin m, ((hk.1 - hk.2) (S i) ) ^ 2)) *
        (√(2 * Real.log
          ((Set.Finite.toFinset (finite_incrementSet c_pos h' n j)).card)))) / m := by
    apply div_le_div_of_nonneg_right _ _
    apply mul_le_mul_of_nonneg_right _ _
    apply Finset.sup'_le _ _
    intro hk hk0
    simp only [Set.Finite.mem_toFinset, incrementFinset] at hk0
    obtain ⟨fh, hfh⟩ := hk0
    rw [<- hfh]
    have :
        √(∑ i,
          |(chainApprox c_pos h' fh ((j : ℕ) + 1) -
              chainApprox c_pos h' fh (j : ℕ)) (S i)| ^ 2) =
        √(∑ i : Fin m,
          ((chainApprox c_pos h' fh ((j : ℕ) + 1) -
              chainApprox c_pos h' fh (j : ℕ)) (S i)) ^ 2) := by
      congr
      ext i
      exact sq_abs _
    rw [this]
    have :
        ⟨chainApprox c_pos h' fh ((j : ℕ) + 1),
          chainApprox c_pos h' fh (j : ℕ)⟩ ∈ incrementPairFinset c_pos h' n j := by
      simp only [Set.Finite.mem_toFinset, incrementPairFinset, incrementPairSet]
      use fh
    exact Finset.le_sup'
      (fun hk : (Z → ℝ) × (Z → ℝ) ↦
        Real.sqrt (∑ i : Fin m, ((hk.1 - hk.2) (S i) ) ^ 2)) this
    simp
    simp
  _ ≤ _ := by
    refine div_le_div_of_nonneg_right ?_ ?_
    · apply mul_le_mul_of_nonneg_left
      · apply Real.sqrt_le_sqrt
        refine mul_le_mul_of_nonneg_left ?_ (by simp)
        apply Real.log_le_log
        · simp
          exact (Set.Finite.toFinset_nonempty (finite_incrementSet c_pos h' n j)).mp
            (incrementFinset_nonempty c_pos h' n j)
        · norm_cast
          apply (incrementFinset_card_le_incrementPairFinset_card c_pos h' n j).trans
          refine (incrementPairFinset_card_le_cover_product_card c_pos h' n j n_pos).trans_eq ?_
          simp only [coveringFinset_card]
      · obtain ⟨fh⟩ := (by assumption : Nonempty ι)
        have hem :
            ⟨chainApprox c_pos h' fh (j + 1),
              chainApprox c_pos h' fh j⟩ ∈ incrementPairFinset c_pos h' n j := by
          simp only [Set.Finite.mem_toFinset, incrementPairFinset, incrementPairSet]
          use fh
        apply le_trans _ (Finset.le_sup' _ hem)
        apply Real.sqrt_nonneg
    · simp

end Empirical
end Causalean.Stat.Concentration
