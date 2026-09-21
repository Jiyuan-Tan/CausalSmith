import Causalean.Mathlib.Combinatorics.JohnsonKneser.Basic

/-!
# Canonical Johnson harmonic subspaces and projections

The degree-`k` Johnson harmonic subspace is the new orthogonal layer in the
inclusion-degree filtration.  Finite-dimensional orthogonal projection gives a
canonical linear projector.  The declarations here state its range,
fixed-point, residual-orthogonality, cross-degree orthogonality, and complete
slice decomposition properties.
-/

open scoped BigOperators

namespace Causalean.Mathlib.Combinatorics.JohnsonKneser

/-- For [a population size](hyp:n) and [a slice size](hyp:M), [the Johnson harmonic subspaces](goal) are [the degree-zero inclusion layer at degree zero](step:1) and [the new orthogonal inclusion-degree layer at each positive degree](step:2). -/
noncomputable def johnsonHarmonic (n M : ℕ) : ℕ → Submodule ℝ (SliceFn n M)
  | 0 => degreeAtMost n M 0
  | d + 1 => degreeAtMost n M (d + 1) ⊓ (degreeAtMost n M d)ᗮ

/-- For [a population size](hyp:n), [a slice size](hyp:M), and [a harmonic degree](hyp:k), [the harmonic projection](goal) is [the canonical linear orthogonal projection onto that degree's Johnson harmonic subspace](step:1). -/
noncomputable def harmonicProjection (n M : ℕ) (k : Fin (M + 1)) :
    SliceFn n M →ₗ[ℝ] SliceFn n M :=
  (johnsonHarmonic n M k.1).starProjection.toLinearMap

/-- For [a harmonic degree](hyp:k), [the projection of the sum](goal) equals the sum of the projections of [the first slice function](hyp:f) and [the second slice function](hyp:g). -/
theorem harmonicProjection_add (k : Fin (M + 1)) (f g : SliceFn n M) :
    harmonicProjection n M k (f + g) =
      harmonicProjection n M k f + harmonicProjection n M k g :=
  map_add (harmonicProjection n M k) f g

/-- For [a harmonic degree](hyp:k), [a real scalar](hyp:c), and [a slice function](hyp:f), [projecting after scalar multiplication equals scalar multiplication after projection](goal). -/
theorem harmonicProjection_smul (k : Fin (M + 1)) (c : ℝ) (f : SliceFn n M) :
    harmonicProjection n M k (c • f) = c • harmonicProjection n M k f :=
  map_smul (harmonicProjection n M k) c f

private theorem johnsonHarmonic_le_degreeAtMost (d : ℕ) :
    johnsonHarmonic n M d ≤ degreeAtMost n M d := by
  cases d with
  | zero => exact le_rfl
  | succ d => exact inf_le_left

private theorem degreeAtMost_eq_iSup_harmonic_fin (d : ℕ) :
    degreeAtMost n M d = ⨆ k : Fin (d + 1), johnsonHarmonic n M k.1 := by
  induction d with
  | zero =>
      apply le_antisymm
      · simp [johnsonHarmonic]
      · refine iSup_le fun k => ?_
        simp [Fin.eq_zero k, johnsonHarmonic]
  | succ d ih =>
      have hstep : degreeAtMost n M (d + 1) =
          degreeAtMost n M d ⊔ johnsonHarmonic n M (d + 1) := by
        rw [johnsonHarmonic, inf_comm]
        exact (Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection
          (degreeAtMost_mono (Nat.le_succ d))).symm
      rw [hstep]
      apply le_antisymm
      · apply sup_le
        · rw [ih]
          exact iSup_le fun k => le_iSup_of_le k.castSucc le_rfl
        · exact le_iSup (fun k : Fin (d + 2) => johnsonHarmonic n M k.1)
            (Fin.last (d + 1))
      · rw [← hstep]
        refine iSup_le fun k => ?_
        exact (johnsonHarmonic_le_degreeAtMost k.1).trans
          (degreeAtMost_mono (Nat.le_of_lt_succ k.2))

private theorem johnsonHarmonic_inner_eq_zero
    {j k : Fin (M + 1)} (hjk : j ≠ k)
    {f g : SliceFn n M} (hf : f ∈ johnsonHarmonic n M j.1)
    (hg : g ∈ johnsonHarmonic n M k.1) :
    inner ℝ f g = 0 := by
  have hv : j.1 ≠ k.1 := fun h => hjk (Fin.ext h)
  rcases lt_or_gt_of_ne hv with hjk' | hkj'
  · cases hk : k.1 with
    | zero => omega
    | succ d =>
      simp only [hk] at hg
      change g ∈ degreeAtMost n M (d + 1) ⊓ (degreeAtMost n M d)ᗮ at hg
      exact hg.2 f (degreeAtMost_mono (by omega)
        (johnsonHarmonic_le_degreeAtMost j.1 hf))
  · cases hj : j.1 with
    | zero => omega
    | succ d =>
      simp only [hj] at hf
      change f ∈ degreeAtMost n M (d + 1) ⊓ (degreeAtMost n M d)ᗮ at hf
      rw [real_inner_comm]
      exact hf.2 g (degreeAtMost_mono (by omega)
        (johnsonHarmonic_le_degreeAtMost k.1 hg))

/-- For [a degree bound](hyp:d), [the next inclusion-degree space is the sum of the preceding space and its new Johnson harmonic layer](goal). -/
theorem degreeAtMost_succ_eq_sup_harmonic (d : ℕ) :
    degreeAtMost n M (d + 1) =
      degreeAtMost n M d ⊔ johnsonHarmonic n M (d + 1) := by
  rw [johnsonHarmonic, inf_comm]
  exact (Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection
    (degreeAtMost_mono (Nat.le_succ d))).symm

/-- [The full degree-at-most-`M` space is the supremum of the Johnson harmonic layers from degree zero through degree `M`](goal). -/
theorem degreeAtMost_eq_iSup_harmonic :
    degreeAtMost n M M = ⨆ k : Fin (M + 1), johnsonHarmonic n M k.1 := by
  exact degreeAtMost_eq_iSup_harmonic_fin M

/-- For [a harmonic degree](hyp:k) and [a slice function](hyp:f), [the projected component belongs to that degree's Johnson harmonic subspace](goal). -/
theorem harmonicProjection_mem (k : Fin (M + 1)) (f : SliceFn n M) :
    harmonicProjection n M k f ∈ johnsonHarmonic n M k.1 := by
  exact Submodule.starProjection_apply_mem _ _

/-- For [a harmonic degree](hyp:k) and [a slice function](hyp:f), [projection leaves the function unchanged exactly when it already lies in that harmonic subspace](goal). -/
theorem harmonicProjection_eq_self_iff (k : Fin (M + 1)) (f : SliceFn n M) :
    harmonicProjection n M k f = f ↔ f ∈ johnsonHarmonic n M k.1 := by
  exact Submodule.starProjection_eq_self_iff

/-- For [a harmonic degree](hyp:k) and [a slice function](hyp:f), [applying the harmonic projection twice gives the same component as applying it once](goal). -/
theorem harmonicProjection_idem (k : Fin (M + 1)) (f : SliceFn n M) :
    harmonicProjection n M k (harmonicProjection n M k f) = harmonicProjection n M k f := by
  exact Submodule.starProjection_eq_self_iff.mpr
    (Submodule.starProjection_apply_mem _ _)

/-- When [the requested slice size is feasible](hyp:hMn), [the residual after projection is orthogonal under the uniform slice inner product to the given harmonic function](goal), for [a harmonic degree](hyp:k), [a slice function](hyp:f), [a comparison function](hyp:g), and [evidence that the comparison function is in that harmonic subspace](hyp:hg). -/
theorem sliceInner_residual_eq_zero (hMn : M ≤ n) (k : Fin (M + 1))
    (f g : SliceFn n M) (hg : g ∈ johnsonHarmonic n M k.1) :
    sliceInner (f - harmonicProjection n M k f) g = 0 := by
  rw [sliceInner_eq hMn]
  change (n.choose M : ℝ)⁻¹ *
    inner ℝ (f - (johnsonHarmonic n M k.1).starProjection f) g = 0
  rw [Submodule.starProjection_inner_eq_zero _ _ hg, mul_zero]

/-- When [the requested slice size is feasible](hyp:hMn) and [the two harmonic degrees are distinct](hyp:hjk), [functions in those two Johnson harmonic subspaces are orthogonal under the uniform slice inner product](goal), for [the first function's membership evidence](hyp:hf) and [the second function's membership evidence](hyp:hg). -/
theorem johnsonHarmonic_pairwise_orthogonal (hMn : M ≤ n)
    {j k : Fin (M + 1)} (hjk : j ≠ k)
    {f g : SliceFn n M} (hf : f ∈ johnsonHarmonic n M j.1)
    (hg : g ∈ johnsonHarmonic n M k.1) :
    sliceInner f g = 0 := by
  rw [sliceInner_eq hMn, johnsonHarmonic_inner_eq_zero hjk hf hg, mul_zero]

/-- When [the requested slice size is feasible](hyp:hMn), [the given slice function equals the finite sum of its harmonic projections from degree zero through degree `M`](goal), for [the slice function](hyp:f). -/
theorem sum_harmonicProjection_eq (hMn : M ≤ n) (f : SliceFn n M) :
    (∑ k : Fin (M + 1), harmonicProjection n M k f) = f := by
  let V : Fin (M + 1) → Submodule ℝ (SliceFn n M) :=
    fun k => johnsonHarmonic n M k.1
  have hV : OrthogonalFamily ℝ (fun k => V k) fun k => (V k).subtypeₗᵢ := by
    intro j k hjk x y
    exact johnsonHarmonic_inner_eq_zero hjk x.2 y.2
  have htop : iSup V = ⊤ := by
    rw [← degreeAtMost_eq_iSup_harmonic, degreeAtMost_eq_top hMn]
  exact hV.sum_projection_of_mem_iSup f (by rw [htop]; trivial)

/-- When [the requested slice size is feasible](hyp:hMn), [the degree-zero projection of the given slice function is the constant function at its uniform mean](goal), for [the slice function](hyp:f). -/
theorem harmonicProjection_zero_eq_mean (hMn : M ≤ n) (f : SliceFn n M) :
    harmonicProjection n M (⟨0, Nat.zero_lt_succ M⟩ : Fin (M + 1)) f =
      constFn (mean f) := by
  change (degreeAtMost n M 0).starProjection f = constFn (mean f)
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact (mem_degreeAtMost_zero_iff hMn _).2 ⟨mean f, rfl⟩
  · intro g hg
    obtain ⟨c, rfl⟩ := (mem_degreeAtMost_zero_iff hMn g).1 hg
    rw [PiLp.inner_apply]
    simp only [Real.inner_apply, PiLp.sub_apply, constFn]
    rw [← Finset.sum_mul]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    rw [mean, card_omega hMn]
    rw [show (Finset.univ : Finset (Omega n M)).card = n.choose M by
      simpa using card_omega hMn]
    have hcard : (n.choose M : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.choose_pos hMn))
    field_simp
    ring

/-- When [the requested slice size is feasible](hyp:hMn), [centering the given slice function equals the sum of its positive-degree harmonic projections](goal), for [the slice function](hyp:f). -/
theorem sum_positive_harmonicProjection_eq_center (hMn : M ≤ n)
    (f : SliceFn n M) :
    (∑ k ∈ Finset.univ.filter (fun k : Fin (M + 1) => 0 < k.1),
      harmonicProjection n M k f) = center f := by
  let z : Fin (M + 1) := ⟨0, Nat.zero_lt_succ M⟩
  have hnot :
      Finset.univ.filter (fun k : Fin (M + 1) => ¬ 0 < k.1) = {z} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · intro hk
      apply Fin.ext
      simp only [z]
      omega
    · rintro rfl
      simp [z]
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Fin (M + 1)))
    (fun k : Fin (M + 1) => 0 < k.1)
    (fun k => harmonicProjection n M k f)
  rw [hnot, Finset.sum_singleton, sum_harmonicProjection_eq hMn f,
    harmonicProjection_zero_eq_mean hMn f] at hsplit
  rw [center]
  exact eq_sub_of_add_eq hsplit

/-- When [the requested slice size is feasible](hyp:hMn) and [the two harmonic degrees are distinct](hyp:hjk), [the corresponding projected components of the given function are orthogonal under the uniform slice inner product](goal), for [the slice function](hyp:f). -/
theorem harmonicProjection_pairwise_orthogonal (hMn : M ≤ n)
    (f : SliceFn n M) {j k : Fin (M + 1)} (hjk : j ≠ k) :
    sliceInner (harmonicProjection n M j f) (harmonicProjection n M k f) = 0 := by
  exact johnsonHarmonic_pairwise_orthogonal hMn hjk
    (harmonicProjection_mem j f) (harmonicProjection_mem k f)

end Causalean.Mathlib.Combinatorics.JohnsonKneser
