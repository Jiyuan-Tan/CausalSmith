import CausalSmith.Substrate.SemialgebraicStratificationSard.Basic

/-!
# Semialgebraic dimension and boundary nullity

This file defines the semialgebraic dimension through coordinate projections with nonempty
interior.  Empty sets have dimension `-1`.  It states the boundary dimension theorem and the
bridge from strict dimension drop to ambient Lebesgue nullity.
-/

open Set MeasureTheory

namespace CausalSmith.SemialgebraicStratificationSard

/-- The semialgebraic dimension of a subset of a finite real coordinate space, with the empty set
assigned dimension `-1`, is the largest coordinate-projection dimension having nonempty interior. -/
noncomputable def semialgebraicDim {ι : Type*} [Fintype ι] (s : Set (ι → ℝ)) : ℤ :=
  by
    classical
    exact Int.ofNat ((Finset.range (Fintype.card ι + 1)).sup fun k =>
      if ∃ e : Fin k ↪ ι, (interior (coordinateProjection e '' s)).Nonempty then k + 1 else 0) - 1

/-- A semialgebraic set has dimension `-1` exactly when it is empty. -/
theorem semialgebraicDim_eq_neg_one_iff {ι : Type*} [Fintype ι]
    {s : Set (ι → ℝ)} (hs : IsSemialgebraic s) :
    semialgebraicDim s = -1 ↔ s = ∅ := by
  classical
  constructor
  · intro hdim
    by_contra hne
    have hnonempty : s.Nonempty := Set.nonempty_iff_ne_empty.mpr hne
    let e : Fin 0 ↪ ι := ⟨Fin.elim0, fun a => Fin.elim0 a⟩
    have himage : coordinateProjection e '' s = Set.univ := by
      apply Set.eq_univ_of_forall
      intro y
      obtain ⟨x, hx⟩ := hnonempty
      exact ⟨x, hx, Subsingleton.elim _ _⟩
    have hproj : (interior (coordinateProjection e '' s)).Nonempty := by
      rw [himage, interior_univ]
      exact Set.univ_nonempty
    have hex : ∃ e : Fin 0 ↪ ι,
        (interior (coordinateProjection e '' s)).Nonempty := ⟨e, hproj⟩
    let n := (Finset.range (Fintype.card ι + 1)).sup fun k =>
      if ∃ e : Fin k ↪ ι, (interior (coordinateProjection e '' s)).Nonempty
      then k + 1 else 0
    have hle : 1 ≤ n := by
      dsimp only [n]
      have hmem : 0 ∈ Finset.range (Fintype.card ι + 1) := by simp
      have h := Finset.le_sup
        (s := Finset.range (Fintype.card ι + 1))
        (f := fun k => if ∃ e : Fin k ↪ ι,
          (interior (coordinateProjection e '' s)).Nonempty then k + 1 else 0)
        hmem
      simpa only [hex, if_true, zero_add] using h
    have hdim' : (n : ℤ) - 1 = -1 := by
      simpa only [semialgebraicDim, n, Int.ofNat_eq_natCast] using hdim
    omega
  · rintro rfl
    simp [semialgebraicDim]

/-- Semialgebraic dimension never exceeds the dimension of the ambient coordinate space. -/
theorem semialgebraicDim_le_ambient {ι : Type*} [Fintype ι] (s : Set (ι → ℝ)) :
    semialgebraicDim s ≤ (Fintype.card ι : ℤ) := by
  classical
  unfold semialgebraicDim
  let n := (Finset.range (Fintype.card ι + 1)).sup fun k =>
    if ∃ e : Fin k ↪ ι, (interior (coordinateProjection e '' s)).Nonempty
    then k + 1 else 0
  have hsup : n ≤ Fintype.card ι + 1 := by
    dsimp [n]
    apply Finset.sup_le
    intro k hk
    simp only [Finset.mem_range] at hk
    split <;> omega
  have hsup' : Int.ofNat n ≤ Int.ofNat (Fintype.card ι + 1) :=
    Int.ofNat_le.mpr hsup
  simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one] at hsup' ⊢
  omega

/-- A semialgebraic subset has full ambient dimension exactly when it has nonempty interior. -/
theorem semialgebraicDim_eq_ambient_iff {ι : Type*} [Fintype ι]
    {s : Set (ι → ℝ)} (hs : IsSemialgebraic s) :
    semialgebraicDim s = (Fintype.card ι : ℤ) ↔ (interior s).Nonempty := by
  sorry

/-- **Semialgebraic boundary dimension theorem.** The boundary of a semialgebraic subset has
dimension strictly below the ambient coordinate dimension (cf. Bochnak--Coste--Roy,
Proposition 2.8.13). -/
theorem semialgebraicDim_frontier_lt_ambient {ι : Type*} [Fintype ι]
    {s : Set (ι → ℝ)} (hs : IsSemialgebraic s) :
    semialgebraicDim (frontier s) < (Fintype.card ι : ℤ) := by
  -- This is the first place where projection closure alone is insufficient: a proof needs a
  -- finite semialgebraic cell decomposition (or an equivalent dimension theory) showing that
  -- the frontier contains no ambient-dimensional cell.
  sorry

/-- The boundary of a full-dimensional semialgebraic set has dimension strictly smaller than the
set itself. -/
theorem semialgebraicDim_frontier_lt {ι : Type*} [Fintype ι]
    {s : Set (ι → ℝ)} (hs : IsSemialgebraic s)
    (hfull : semialgebraicDim s = (Fintype.card ι : ℤ)) :
    semialgebraicDim (frontier s) < semialgebraicDim s := by
  rw [hfull]
  exact semialgebraicDim_frontier_lt_ambient hs

/-- A semialgebraic subset of dimension strictly below its ambient coordinate dimension has zero
ambient Lebesgue measure. -/
theorem volume_eq_zero_of_semialgebraicDim_lt_ambient {ι : Type*} [Fintype ι]
    {s : Set (ι → ℝ)} (hs : IsSemialgebraic s)
    (hdim : semialgebraicDim s < (Fintype.card ι : ℤ)) :
    volume s = 0 := by
  -- A reusable route is cell decomposition followed by nullity of each lower-dimensional smooth
  -- cell; the existing Hausdorff-dimension lemmas do not identify `semialgebraicDim` with `dimH`.
  sorry

/-- The topological boundary of every semialgebraic subset of a finite real coordinate space has
zero ambient Lebesgue measure. -/
theorem volume_frontier_eq_zero {ι : Type*} [Fintype ι]
    {s : Set (ι → ℝ)} (hs : IsSemialgebraic s) : volume (frontier s) = 0 := by
  exact volume_eq_zero_of_semialgebraicDim_lt_ambient hs.frontier
    (semialgebraicDim_frontier_lt_ambient hs)

end CausalSmith.SemialgebraicStratificationSard
