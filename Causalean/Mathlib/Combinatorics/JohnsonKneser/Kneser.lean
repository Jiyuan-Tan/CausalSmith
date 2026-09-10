import Causalean.Mathlib.Combinatorics.JohnsonKneser.Harmonics

/-!
# The Kneser disjointness operator on Johnson harmonics

This module defines the unnormalized adjacency sum over disjoint slice points.
It states the classical Kneser eigenvalue on every canonical Johnson harmonic
degree, as well as the normalized falling-factorial form.
-/

open scoped BigOperators

namespace Causalean.Mathlib.Combinatorics.JohnsonKneser

/-- For [a population size](hyp:n) and [a slice size](hyp:M), [the unnormalized Kneser adjacency operator](goal) is [specified by summing a function over all equally sized subsets disjoint from the argument](step:1), [preserving addition](step:2), and [commuting with real scalar multiplication](step:3). -/
noncomputable def kneserAdjacency (n M : ℕ) : SliceFn n M →ₗ[ℝ] SliceFn n M where
  toFun f := WithLp.toLp 2 (fun A : Omega n M =>
    ∑ B : Omega n M, if Disjoint A.1 B.1 then f B else 0)
  map_add' f g := by
    ext A
    change (∑ B : Omega n M, if Disjoint A.1 B.1 then f B + g B else 0) =
      (∑ B : Omega n M, if Disjoint A.1 B.1 then f B else 0) +
      ∑ B : Omega n M, if Disjoint A.1 B.1 then g B else 0
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro B _
    split_ifs <;> simp_all
  map_smul' c f := by
    ext A
    simp [Finset.mul_sum]

/-- For [a set of labelled units](hyp:S), [its disjointness indicator](goal) is [one at slice points disjoint from that set and zero elsewhere](step:1). -/
def disjointIndicator (S : Finset (Fin n)) : SliceFn n M :=
  WithLp.toLp 2 (fun A => if Disjoint S A.1 then 1 else 0)

/-
Proof route for the next two lemmas: evaluate at a slice point.  For
inclusion--exclusion, filter `S.powerset` to the subsets of `S ∩ A` and use
`Finset.sum_powerset_neg_one_pow_card`.  For the exact adjacency formula,
when `A` and `S` are disjoint, identify every admissible neighbor uniquely as
`S ∪ C`, where `C` has size `M - S.card` in the complement of `A ∪ S`; count
those `C` with `powersetCard`.
-/

/-- For [a set of labelled units](hyp:S), [its disjointness indicator equals the alternating inclusion-exclusion sum of the inclusion monomials of its subsets](goal). -/
theorem disjointIndicator_eq_sum_powerset (S : Finset (Fin n)) :
    disjointIndicator (M := M) S =
      ∑ T ∈ S.powerset, ((-1 : ℝ) ^ T.card) • inclusionMonomial (M := M) T := by
  ext A
  simp only [disjointIndicator, inclusionMonomial]
  simp
  have hsum : (∑ T ∈ (S ∩ A.1).powerset, (-1 : ℝ) ^ T.card) =
      if S ∩ A.1 = ∅ then 1 else 0 := by
    exact_mod_cast (Finset.sum_powerset_neg_one_pow_card (x := S ∩ A.1))
  have hfilter : S.powerset.filter (fun T => T ⊆ A.1) = (S ∩ A.1).powerset := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨hTS, hTA⟩ x hx
      exact Finset.mem_inter.mpr ⟨hTS hx, hTA hx⟩
    · intro hT
      exact ⟨hT.trans Finset.inter_subset_left, hT.trans Finset.inter_subset_right⟩
  calc
    (if Disjoint S A.1 then 1 else 0) =
        if S ∩ A.1 = ∅ then 1 else 0 := by
      simp only [Finset.disjoint_iff_inter_eq_empty]
    _ = ∑ T ∈ (S ∩ A.1).powerset, (-1 : ℝ) ^ T.card := hsum.symm
    _ = ∑ T ∈ S.powerset.filter (fun T => T ⊆ A.1), (-1 : ℝ) ^ T.card := by
      rw [hfilter]
    _ = ∑ T ∈ S.powerset, if T ⊆ A.1 then (-1 : ℝ) ^ T.card else 0 := by
      rw [Finset.sum_filter]

/-- When [two disjoint slice-sized subsets can fit in the population](hyp:h2) and [the indexing set is no larger than the slice size](hyp:hSM), [Kneser adjacency maps the given inclusion monomial to its disjointness indicator times the number of compatible completions](goal), for [the indexing set](hyp:S). -/
theorem kneserAdjacency_inclusionMonomial_eq (h2 : 2 * M ≤ n)
    (S : Finset (Fin n)) (hSM : S.card ≤ M) :
    kneserAdjacency n M (inclusionMonomial (M := M) S) =
      ((n - M - S.card).choose (M - S.card) : ℝ) •
        disjointIndicator (M := M) S := by
  ext A
  simp [kneserAdjacency, inclusionMonomial, disjointIndicator]
  by_cases hSA : Disjoint S A.1
  · rw [if_pos hSA]
    let U : Finset (Fin n) := Finset.univ \ A.1
    let goodOmega : Finset (Omega n M) :=
      Finset.univ.filter (fun B => Disjoint A.1 B.1 ∧ S ⊆ B.1)
    let goodSets : Finset (Finset (Fin n)) :=
      (U.powersetCard M).filter (fun B => S ⊆ B)
    have hSsubU : S ⊆ U := by
      intro x hxS
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x,
        fun hxA => Finset.disjoint_left.mp hSA hxS hxA⟩
    have hcardU : U.card = n - M := by
      simp only [U]
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ A.1), A.2]
      simp
    have hcard : goodOmega.card = goodSets.card := by
      apply Finset.card_bij (fun B _ => B.1)
      · intro B hB
        simp only [goodOmega, Finset.mem_filter, Finset.mem_univ, true_and] at hB
        simp only [goodSets, Finset.mem_filter, Finset.mem_powersetCard]
        refine ⟨⟨?_, B.2⟩, hB.2⟩
        intro x hxB
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x,
          fun hxA => Finset.disjoint_left.mp hB.1 hxA hxB⟩
      · intro B₁ hB₁ B₂ hB₂ h
        exact Subtype.ext h
      · intro C hC
        simp only [goodSets, Finset.mem_filter, Finset.mem_powersetCard] at hC
        let B : Omega n M := ⟨C, hC.1.2⟩
        have hAB : Disjoint A.1 C := by
          rw [Finset.disjoint_left]
          intro x hxA hxC
          exact (Finset.mem_sdiff.mp (hC.1.1 hxC)).2 hxA
        refine ⟨B, ?_, rfl⟩
        change B ∈ goodOmega
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ B, hAB, hC.2⟩
    have hgoodSets : goodSets.card =
        (n - M - S.card).choose (M - S.card) := by
      rw [show goodSets = (U.powersetCard M).filter (fun B => S ⊆ B) by rfl,
        Finset.card_filter_powersetCard_subset S U M hSsubU hSM, hcardU]
    calc
      (∑ B : Omega n M,
          if Disjoint A.1 B.1 then if S ⊆ B.1 then 1 else 0 else 0) =
          (goodOmega.card : ℝ) := by
        simp only [goodOmega, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
          Nat.cast_one, Nat.cast_zero]
        apply Finset.sum_congr rfl
        intro B _
        by_cases hAB : Disjoint A.1 B.1 <;> by_cases hSB : S ⊆ B.1 <;>
          simp [hAB, hSB]
      _ = (goodSets.card : ℝ) := by rw [hcard]
      _ = ((n - M - S.card).choose (M - S.card) : ℝ) := by rw [hgoodSets]
  · rw [if_neg hSA]
    apply Finset.sum_eq_zero
    intro B _
    by_cases hAB : Disjoint A.1 B.1
    · rw [if_pos hAB, if_neg]
      intro hSB
      apply hSA
      rw [Finset.disjoint_left]
      intro x hxS hxA
      exact Finset.disjoint_left.mp hAB hxA (hSB hxS)
    · rw [if_neg hAB]

/-
After rewriting by `kneserAdjacency_inclusionMonomial_eq` and the powerset
expansion, isolate the `T = S` summand.  Every other `T ⊆ S` has cardinality at
most `d - 1`, so its inclusion monomial lies in the lower filtration.  Extend
from generators with `Submodule.span_induction`; generators of cardinality
strictly below `d` are already in the lower filtration.
-/

/-- When [two disjoint slice-sized subsets can fit in the population](hyp:h2), [the degree is positive](hyp:hd), [the indexing set](hyp:S) has [exactly that degree](hyp:hSd), and [the degree does not exceed the slice size](hyp:hdM), [Kneser adjacency differs from its classical degree eigenvalue times that monomial only by a lower-degree function](goal). -/
theorem kneserAdjacency_inclusionMonomial_mod_lower (h2 : 2 * M ≤ n)
    {d : ℕ} (hd : 0 < d) (S : Finset (Fin n))
    (hSd : S.card = d) (hdM : d ≤ M) :
    kneserAdjacency n M (inclusionMonomial (M := M) S) -
        (((-1 : ℝ) ^ d) * ((n - M - d).choose (M - d) : ℝ)) •
          inclusionMonomial (M := M) S ∈
      degreeAtMost n M (d - 1) := by
  subst d
  have hSM : S.card ≤ M := hdM
  rw [kneserAdjacency_inclusionMonomial_eq h2 S hSM,
    disjointIndicator_eq_sum_powerset]
  let c : ℝ := ((n - M - S.card).choose (M - S.card) : ℝ)
  have hSps : S ∈ S.powerset := by simp
  have hlower : ∀ T ∈ S.powerset.erase S,
      inclusionMonomial (M := M) T ∈ degreeAtMost n M (S.card - 1) := by
    intro T hT
    have hTS : T ⊆ S := Finset.mem_powerset.mp (Finset.mem_of_mem_erase hT)
    have hTne : T ≠ S := Finset.ne_of_mem_erase hT
    have hcard : T.card ≤ S.card - 1 := by
      have : T.card < S.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hTS, hTne⟩)
      omega
    exact Submodule.subset_span ⟨T, hcard, rfl⟩
  have hsum : (∑ T ∈ S.powerset.erase S,
      (c * (-1 : ℝ) ^ T.card) • inclusionMonomial (M := M) T) ∈
      degreeAtMost n M (S.card - 1) := by
    exact Submodule.sum_mem _ fun T hT => Submodule.smul_mem _ _ (hlower T hT)
  convert hsum using 1
  rw [← Finset.sum_erase_add _ _ hSps]
  rw [smul_add, Finset.smul_sum]
  simp_rw [smul_smul]
  dsimp only [c]
  module

/-- When [two disjoint slice-sized subsets can fit in the population](hyp:h2), [the degree bound does not exceed the slice size](hyp:hdM), and [the given function belongs to that inclusion-degree subspace](hyp:hf), [Kneser adjacency remains in the same inclusion-degree subspace](goal), for [the slice function](hyp:f). -/
theorem kneserAdjacency_mem_degreeAtMost (h2 : 2 * M ≤ n)
    {d : ℕ} (hdM : d ≤ M) (f : SliceFn n M)
    (hf : f ∈ degreeAtMost n M d) :
    kneserAdjacency n M f ∈ degreeAtMost n M d := by
  change f ∈ Submodule.span ℝ
    {f | ∃ S : Finset (Fin n), S.card ≤ d ∧ f = inclusionMonomial (M := M) S} at hf
  refine Submodule.span_induction
    (p := fun f _ => kneserAdjacency n M f ∈ degreeAtMost n M d) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨S, hSd, rfl⟩
    rw [kneserAdjacency_inclusionMonomial_eq h2 S (hSd.trans hdM),
      disjointIndicator_eq_sum_powerset]
    apply Submodule.smul_mem
    apply Submodule.sum_mem
    intro T hT
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨T,
      (Finset.card_le_card (Finset.mem_powerset.mp hT)).trans hSd, rfl⟩
  · simpa using (degreeAtMost n M d).zero_mem
  · intro x y _ _ hx hy
    rw [map_add]
    exact (degreeAtMost n M d).add_mem hx hy
  · intro c x _ hx
    rw [map_smul]
    exact (degreeAtMost n M d).smul_mem c hx

/-- When [two disjoint slice-sized subsets can fit in the population](hyp:h2), [the degree is positive](hyp:hd), [the degree does not exceed the slice size](hyp:hdM), and [the given function has inclusion degree at most that degree](hyp:hf), [subtracting the classical degree eigenvalue leaves a function one degree lower](goal), for [the slice function](hyp:f). -/
theorem kneserAdjacency_sub_eigen_mem_lower (h2 : 2 * M ≤ n)
    {d : ℕ} (hd : 0 < d) (hdM : d ≤ M) (f : SliceFn n M)
    (hf : f ∈ degreeAtMost n M d) :
    kneserAdjacency n M f -
        (((-1 : ℝ) ^ d) * ((n - M - d).choose (M - d) : ℝ)) • f ∈
      degreeAtMost n M (d - 1) := by
  let eig : ℝ := ((-1 : ℝ) ^ d) * ((n - M - d).choose (M - d) : ℝ)
  change f ∈ Submodule.span ℝ
    {f | ∃ S : Finset (Fin n), S.card ≤ d ∧ f = inclusionMonomial (M := M) S} at hf
  change kneserAdjacency n M f - eig • f ∈ degreeAtMost n M (d - 1)
  refine Submodule.span_induction
    (p := fun f _ => kneserAdjacency n M f - eig • f ∈ degreeAtMost n M (d - 1))
    ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨S, hSd, rfl⟩
    by_cases hcard : S.card = d
    · dsimp only [eig]
      exact kneserAdjacency_inclusionMonomial_mod_lower h2 hd S hcard hdM
    · have hSlo : S.card ≤ d - 1 := by omega
      have hmono : inclusionMonomial (M := M) S ∈ degreeAtMost n M (d - 1) :=
        Submodule.subset_span ⟨S, hSlo, rfl⟩
      exact (degreeAtMost n M (d - 1)).sub_mem
        (kneserAdjacency_mem_degreeAtMost h2 (by omega) _ hmono)
        ((degreeAtMost n M (d - 1)).smul_mem eig hmono)
  · simp
  · intro x y _ _ hx hy
    have hxy := (degreeAtMost n M (d - 1)).add_mem hx hy
    rw [map_add, smul_add]
    convert hxy using 1; module
  · intro c x _ hx
    have hcx := (degreeAtMost n M (d - 1)).smul_mem c hx
    rw [map_smul, smul_smul]
    convert hcx using 1; module

/-- For [a first slice function](hyp:f) and [a second slice function](hyp:g), [Kneser adjacency is self-adjoint under the uniform slice inner product](goal). -/
theorem sliceInner_kneserAdjacency (f g : SliceFn n M) :
    sliceInner (kneserAdjacency n M f) g =
      sliceInner f (kneserAdjacency n M g) := by
  rw [sliceInner, sliceInner]
  congr 1
  change (∑ A : Omega n M,
      (∑ B : Omega n M, if Disjoint A.1 B.1 then f B else 0) * g A) =
    ∑ A : Omega n M,
      f A * (∑ B : Omega n M, if Disjoint A.1 B.1 then g B else 0)
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A _
  apply Finset.sum_congr rfl
  intro B _
  by_cases hAB : Disjoint A.1 B.1
  · rw [if_pos hAB, if_pos hAB.symm]
  · have hBA : ¬ Disjoint B.1 A.1 := fun h => hAB h.symm
    rw [if_neg hAB, if_neg hBA]
    simp

/-
For positive degree, `kneserAdjacency_sub_eigen_mem_lower` puts the residual
in the preceding filtration level.  Self-adjointness and preservation of that
level put the same residual in its orthogonal complement; its inner product
with itself therefore vanishes.  Degree zero is handled separately using
`mem_degreeAtMost_zero_iff` and the exact action on the empty-set inclusion
monomial.  The projection corollary then only needs `harmonicProjection_mem`.
-/

/-- When [two disjoint slice-sized subsets can fit in the population](hyp:h2), [the selected harmonic degree](hyp:k), and [the given function belongs to that degree's Johnson harmonic subspace](hyp:hf), [unnormalized Kneser adjacency acts by its classical signed binomial eigenvalue](goal), for [the slice function](hyp:f). -/
theorem kneserAdjacency_eigen (h2 : 2 * M ≤ n) (k : Fin (M + 1))
    (f : SliceFn n M) (hf : f ∈ johnsonHarmonic n M k.1) :
    kneserAdjacency n M f =
      (((-1 : ℝ) ^ k.1) * ((n - M - k.1).choose (M - k.1) : ℝ)) • f := by
  have hMn : M ≤ n := by omega
  cases hk : k.1 with
  | zero =>
      have hf0 : f ∈ degreeAtMost n M 0 := by
        simpa [johnsonHarmonic, hk] using hf
      obtain ⟨c, rfl⟩ := (mem_degreeAtMost_zero_iff hMn _).1 hf0
      have hconst :
          constFn (n := n) (M := M) c =
            c • inclusionMonomial (M := M) (∅ : Finset (Fin n)) := by
        ext A
        simp [constFn, inclusionMonomial]
      rw [hconst, map_smul,
        kneserAdjacency_inclusionMonomial_eq h2 ∅ (by simp)]
      ext A
      simp [disjointIndicator, inclusionMonomial, mul_comm]
  | succ d =>
      have hdM : d + 1 ≤ M := by omega
      have hfharm :
          f ∈ degreeAtMost n M (d + 1) ⊓ (degreeAtMost n M d)ᗮ := by
        simpa [johnsonHarmonic, hk] using hf
      have hf' : f ∈ degreeAtMost n M (d + 1) := by
        exact hfharm.1
      let eig : ℝ :=
        ((-1 : ℝ) ^ (d + 1)) * ((n - M - (d + 1)).choose (M - (d + 1)) : ℝ)
      let r : SliceFn n M := kneserAdjacency n M f - eig • f
      have hr : r ∈ degreeAtMost n M d := by
        have h := kneserAdjacency_sub_eigen_mem_lower h2 (d := d + 1)
          (by omega) hdM f hf'
        simpa [r, eig] using h
      have hforth : ∀ g ∈ degreeAtMost n M d, sliceInner f g = 0 := by
        intro g hg
        rw [sliceInner_eq hMn, real_inner_comm]
        have hfg : inner ℝ g f = 0 := by
          exact hfharm.2 g hg
        rw [hfg, mul_zero]
      have hrorth : ∀ g ∈ degreeAtMost n M d, sliceInner r g = 0 := by
        intro g hg
        have hAg : kneserAdjacency n M g ∈ degreeAtMost n M d :=
          kneserAdjacency_mem_degreeAtMost h2 (by omega) g hg
        have hexpand :
            sliceInner r g = sliceInner (kneserAdjacency n M f) g -
              eig * sliceInner f g := by
          rw [sliceInner_eq hMn, sliceInner_eq hMn, sliceInner_eq hMn]
          simp only [r, inner_sub_left, inner_smul_left]
          change (n.choose M : ℝ)⁻¹ *
              (inner ℝ (kneserAdjacency n M f) g - eig * inner ℝ f g) =
            (n.choose M : ℝ)⁻¹ * inner ℝ (kneserAdjacency n M f) g -
              eig * ((n.choose M : ℝ)⁻¹ * inner ℝ f g)
          ring
        have hself := sliceInner_kneserAdjacency (n := n) (M := M) f g
        rw [hexpand, hself, hforth g hg,
          hforth (kneserAdjacency n M g) hAg]
        ring
      have hs : sliceInner r r = 0 := hrorth r hr
      have hchoose : n.choose M ≠ 0 := Nat.ne_of_gt (Nat.choose_pos hMn)
      have hscale : ((n.choose M : ℝ)⁻¹) ≠ 0 :=
        inv_ne_zero (Nat.cast_ne_zero.mpr hchoose)
      have hir : inner ℝ r r = 0 := by
        rw [sliceInner_eq hMn] at hs
        exact (mul_eq_zero.mp hs).resolve_left hscale
      have hr0 : r = 0 := inner_self_eq_zero.mp hir
      exact sub_eq_zero.mp (by simpa [r, eig, hk] using hr0)

/-- When [two disjoint slice-sized subsets can fit in the population](hyp:h2), [the selected harmonic degree](hyp:k), and [the given slice function](hyp:f), [Kneser adjacency acts on its projected harmonic component by the classical signed binomial eigenvalue](goal). -/
theorem kneserAdjacency_harmonicProjection (h2 : 2 * M ≤ n)
    (k : Fin (M + 1)) (f : SliceFn n M) :
    kneserAdjacency n M (harmonicProjection n M k f) =
      (((-1 : ℝ) ^ k.1) * ((n - M - k.1).choose (M - k.1) : ℝ)) •
        harmonicProjection n M k f := by
  exact kneserAdjacency_eigen h2 k _ (harmonicProjection_mem k f)

/-- For [a population size](hyp:n) and [a slice size](hyp:M), [the normalized Kneser adjacency operator](goal) is [the unnormalized disjointness sum divided by the number of disjoint neighbors](step:1). -/
noncomputable def normalizedKneserAdjacency (n M : ℕ) :
    SliceFn n M →ₗ[ℝ] SliceFn n M :=
  ((n - M).choose M : ℝ)⁻¹ • kneserAdjacency n M

/-
For the normalization identity, first record the natural-number bounds forced
by `h2` and `k.isLt`.  Rewrite binomial coefficients with
`Nat.descFactorial_eq_factorial_mul_choose` (or the equivalent division form),
use positivity to discharge the real-cast denominators, and cancel in `ℝ`.
The two normalized action theorems then follow by unfolding the scaled linear
map, rewriting the unnormalized eigen theorem, and using the ratio identity.
-/

/-- When [two disjoint slice-sized subsets can fit in the population](hyp:h2) and [the selected harmonic degree](hyp:k), [the normalized Kneser eigenvalue magnitude equals the corresponding ratio of falling factorials](goal). -/
theorem normalizedKneser_eigenvalue_eq (h2 : 2 * M ≤ n)
    (k : Fin (M + 1)) :
    ((n - M).choose M : ℝ)⁻¹ *
        ((n - M - k.1).choose (M - k.1) : ℝ) =
      (M.descFactorial k.1 : ℝ) / ((n - M).descFactorial k.1 : ℝ) := by
  have hkM : k.1 ≤ M := by omega
  have hM : M ≤ n - M := by omega
  have hsub : M - k.1 ≤ n - M - k.1 := Nat.sub_le_sub_right hM k.1
  have hdiff : n - M - k.1 - (M - k.1) = n - M - M :=
    Nat.sub_sub_sub_cancel_right hkM
  rw [Nat.cast_choose ℝ hM, Nat.cast_choose ℝ hsub, hdiff]
  have hfacM : ((M - k.1).factorial : ℝ) * (M.descFactorial k.1 : ℝ) =
      (M.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_mul_descFactorial hkM
  have hfacN : ((n - M - k.1).factorial : ℝ) *
      ((n - M).descFactorial k.1 : ℝ) = ((n - M).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_mul_descFactorial (hkM.trans hM)
  have hdescN : ((n - M).descFactorial k.1 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.descFactorial_pos.mpr (hkM.trans hM)))
  field_simp [hdescN]
  rw [← hfacM, ← hfacN]
  ring

/-- When [two disjoint slice-sized subsets can fit in the population](hyp:h2), [the selected harmonic degree](hyp:k), and [the given function belongs to that degree's Johnson harmonic subspace](hyp:hf), [normalized Kneser adjacency acts by the signed falling-factorial eigenvalue](goal), for [the slice function](hyp:f). -/
theorem normalizedKneserAdjacency_eigen (h2 : 2 * M ≤ n)
    (k : Fin (M + 1)) (f : SliceFn n M)
    (hf : f ∈ johnsonHarmonic n M k.1) :
    normalizedKneserAdjacency n M f =
      (((-1 : ℝ) ^ k.1) *
        ((M.descFactorial k.1 : ℝ) / ((n - M).descFactorial k.1 : ℝ))) • f := by
  rw [normalizedKneserAdjacency]
  simp only [LinearMap.smul_apply]
  rw [kneserAdjacency_eigen h2 k f hf, smul_smul]
  congr 1
  rw [mul_left_comm ((n - M).choose M : ℝ)⁻¹]
  rw [normalizedKneser_eigenvalue_eq h2 k]

/-- When [two disjoint slice-sized subsets can fit in the population](hyp:h2), [the selected harmonic degree](hyp:k), and [the given slice function](hyp:f), [normalized Kneser adjacency acts on its projected harmonic component by the signed falling-factorial eigenvalue](goal). -/
theorem normalizedKneserAdjacency_harmonicProjection (h2 : 2 * M ≤ n)
    (k : Fin (M + 1)) (f : SliceFn n M) :
    normalizedKneserAdjacency n M (harmonicProjection n M k f) =
      (((-1 : ℝ) ^ k.1) *
        ((M.descFactorial k.1 : ℝ) / ((n - M).descFactorial k.1 : ℝ))) •
        harmonicProjection n M k f := by
  exact normalizedKneserAdjacency_eigen h2 k _ (harmonicProjection_mem k f)

end Causalean.Mathlib.Combinatorics.JohnsonKneser
