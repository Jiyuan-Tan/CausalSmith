import Mathlib

/-!
# Uniform slices and their inclusion-degree filtration

This module defines the uniform `M`-slice of `Fin n`, real functions on that
slice, the uniform inner product and mean, inclusion monomials, and the nested
subspaces spanned by monomials of bounded degree.  It contains no
Johnson/Kneser spectral conclusions.
-/

open scoped BigOperators

namespace Causalean.Mathlib.Combinatorics.JohnsonKneser

/-- For [a population with `n` labelled units](hyp:n) and [a requested subset size `M`](hyp:M),
[the uniform slice](goal) is [represented by the `M`-element subsets of that population](step:1). -/
def Omega (n M : ℕ) := {A : Finset (Fin n) // A.card = M}
  deriving Fintype, DecidableEq

/-- For [a population size `n`](hyp:n) and [a slice size `M`](hyp:M), [the slice-function space](goal)
is [the real Euclidean space of functions on that uniform slice](step:1). -/
abbrev SliceFn (n M : ℕ) := EuclideanSpace ℝ (Omega n M)

/-- For [a first slice function](hyp:f) and [a second slice function](hyp:g), [the uniform-slice inner product](goal)
is [the average of their pointwise products over all slice points](step:1). -/
noncomputable def sliceInner (f g : SliceFn n M) : ℝ :=
  (Fintype.card (Omega n M) : ℝ)⁻¹ * ∑ A, f A * g A

/-- For [a slice function](hyp:f), [its uniform mean](goal) is [the average of its values over the slice](step:1). -/
noncomputable def mean (f : SliceFn n M) : ℝ :=
  (Fintype.card (Omega n M) : ℝ)⁻¹ * ∑ A, f A

/-- For [a real value](hyp:c), [the constant slice function](goal) is [the function taking that value at every slice point](step:1). -/
def constFn (c : ℝ) : SliceFn n M :=
  WithLp.toLp 2 (fun _ => c)

/-- For [a slice function](hyp:f), [its centered version](goal) is [obtained by subtracting its uniform mean at every slice point](step:1). -/
noncomputable def center (f : SliceFn n M) : SliceFn n M :=
  f - constFn (mean f)

/-- For [a set of labelled units](hyp:S), [its inclusion monomial](goal) is [one on slice points containing that set and zero elsewhere](step:1). -/
def inclusionMonomial (S : Finset (Fin n)) : SliceFn n M :=
  WithLp.toLp 2 (fun A => if S ⊆ A.1 then 1 else 0)

/-- For [a population size](hyp:n), [a slice size](hyp:M), and [a degree bound](hyp:d),
[the degree-at-most subspace](goal) is [the linear span of inclusion monomials indexed by sets no larger than that bound](step:1). -/
def degreeAtMost (n M d : ℕ) : Submodule ℝ (SliceFn n M) :=
  Submodule.span ℝ {f | ∃ S : Finset (Fin n), S.card ≤ d ∧ f = inclusionMonomial (M := M) S}

/-- When [the first degree bound does not exceed the second](hyp:hde), [every function in the first inclusion-degree subspace also belongs to the second](goal). -/
theorem degreeAtMost_mono {d e : ℕ} (hde : d ≤ e) :
    degreeAtMost n M d ≤ degreeAtMost n M e := by
  exact Submodule.span_mono fun f ⟨S, hSd, hf⟩ => ⟨S, hSd.trans hde, hf⟩

/-- When [the requested slice size is feasible](hyp:hMn), [a slice function belongs to the degree-zero subspace exactly when it is constant](goal), for [the given slice function](hyp:f). -/
theorem mem_degreeAtMost_zero_iff (hMn : M ≤ n) (f : SliceFn n M) :
    f ∈ degreeAtMost n M 0 ↔ ∃ c : ℝ, f = constFn c := by
  have hgen :
      {g : SliceFn n M | ∃ S : Finset (Fin n), S.card ≤ 0 ∧
        g = inclusionMonomial (M := M) S} = {constFn 1} := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨S, hS, rfl⟩
      have hS0 : S = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hS)
      subst S
      ext A
      simp [inclusionMonomial, constFn]
    · intro hg
      subst g
      refine ⟨∅, by simp, ?_⟩
      ext A
      simp [inclusionMonomial, constFn]
  rw [degreeAtMost, hgen, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, hc.symm.trans ?_⟩
    ext A
    simp [constFn]
  · rintro ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    ext A
    simp [constFn]

/-- When [the requested slice size is feasible](hyp:hMn), [inclusion monomials through degree `M` span every real function on the uniform slice](goal). -/
theorem degreeAtMost_eq_top (hMn : M ≤ n) :
    degreeAtMost n M M = ⊤ := by
  apply top_unique
  intro f hf
  have hsubset_iff (A B : Omega n M) : A.1 ⊆ B.1 ↔ A = B := by
    constructor
    · intro hAB
      apply Subtype.ext
      exact Finset.eq_of_subset_of_card_le hAB (by rw [A.2, B.2])
    · rintro rfl
      exact Finset.Subset.rfl
  have hmono (A : Omega n M) :
      inclusionMonomial (M := M) A.1 ∈ degreeAtMost n M M :=
    Submodule.subset_span ⟨A.1, A.2.le, rfl⟩
  have hsum :
      (∑ A : Omega n M, f A • inclusionMonomial (M := M) A.1) ∈
        degreeAtMost n M M :=
    Submodule.sum_mem _ fun A _ => Submodule.smul_mem _ _ (hmono A)
  convert hsum using 1
  ext B
  simp [inclusionMonomial, hsubset_iff]

/-- When [the requested slice size is feasible](hyp:hMn), [the uniform slice has exactly the usual binomial number of points](goal). -/
theorem card_omega (hMn : M ≤ n) : Fintype.card (Omega n M) = n.choose M := by
  let e : Omega n M ≃
      {S // S ∈ (Finset.univ : Finset (Fin n)).powersetCard M} :=
    { toFun := fun A => ⟨A.1, by simp [A.2]⟩
      invFun := fun S => ⟨S.1, (Finset.mem_powersetCard.mp S.2).2⟩
      left_inv := fun A => by cases A; rfl
      right_inv := fun S => by cases S; rfl }
  calc
    Fintype.card (Omega n M) =
        Fintype.card {S // S ∈ (Finset.univ : Finset (Fin n)).powersetCard M} :=
      Fintype.card_congr e
    _ = ((Finset.univ : Finset (Fin n)).powersetCard M).card :=
      Fintype.card_coe _
    _ = n.choose M := by simp

/-- When [the requested slice size is feasible](hyp:hMn), [the uniform inner product of the two given slice functions](goal) equals the ordinary function-space inner product divided by the number of slice points, for [the first function](hyp:f) and [the second function](hyp:g). -/
theorem sliceInner_eq (hMn : M ≤ n) (f g : SliceFn n M) :
    sliceInner f g = (n.choose M : ℝ)⁻¹ * inner ℝ f g := by
  rw [sliceInner, card_omega hMn, PiLp.inner_apply]
  simp only [Real.inner_apply]

/-- When [the requested slice size is feasible](hyp:hMn), [the uniform mean of the given constant slice function equals its constant value](goal), for [the real value](hyp:c). -/
theorem mean_constFn (hMn : M ≤ n) (c : ℝ) :
    mean (constFn (n := n) (M := M) c) = c := by
  have hchoose : n.choose M ≠ 0 := Nat.ne_of_gt (Nat.choose_pos hMn)
  simp [mean, constFn, card_omega hMn, hchoose]

end Causalean.Mathlib.Combinatorics.JohnsonKneser
