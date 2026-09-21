/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Codimension-one certificates for affine chains
-/

module
public import Causalean.Mathlib.AlgebraicGeometry.Dimension.PolynomialMap.AffineSpaceDimension
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Ambient closed-chain codimension in complex affine space

This file defines maximal ambient-closed irreducible subsets and endpoint-fixed
ambient closed-chain codimension, then proves dimension-chain and
principal-minimal-prime certificates for rank one.  These notions recover the
usual component notion on affine-closed loci.  The codimension notion recovers
the usual minimum codimension of the locus's irreducible components when the
locus is affine-closed and the ambient locus is irreducible affine-closed;
neither is a subspace-topological notion for arbitrary nonclosed subsets.
-/

@[expose] public section

namespace Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension

noncomputable section

/-- For [a coordinate index set](hyp:ι),
[a candidate subset $C$ of the corresponding complex affine space](hyp:C), and
[a prescribed locus $Z$ in that space](hyp:Z),
[the set $C$ is a maximal ambient-closed irreducible subset of $Z$](goal) when
[$C$ is irreducible and closed in the ambient affine space](step:1),
[$C$ is contained in $Z$](step:2), and
[every ambient-closed irreducible subset of $Z$ containing $C$ equals $C$](step:3).

For affine-closed `Z`, these are its usual irreducible components.  For
nonclosed `Z`, this predicate does not describe components in the subspace
Zariski topology. -/
def IsIrreducibleAffineComponent {ι : Type*}
    (C Z : Set (ι → ℂ)) : Prop :=
  IsIrreducibleAffineClosed C ∧ C ⊆ Z ∧
    ∀ C', IsIrreducibleAffineClosed C' → C ⊆ C' → C' ⊆ Z → C' = C

/-- The [endpoint-fixed ambient closed-chain codimension relation](goal) measures how many
strict irreducible affine-closed enlargements separate [a locus](hyp:Z) from
[an ambient set](hyp:X) in [complex affine space indexed by a coordinate set](hyp:ι).
It assigns [nonnegative rank $d$](hyp:d) when
[each maximal ambient-closed irreducible subset of the locus starts a chain of $d+1$
subsets ending at the ambient set](step:1), while
[at least one starts no such chain of $d+2$ subsets](step:2).

When `Z` is affine-closed and `X` is irreducible affine-closed, this expresses
the usual minimum codimension of the irreducible components of `Z` in `X`.
On arbitrary nonclosed inputs it is only the stated ambient-chain invariant,
not ordinary subspace codimension. -/
def HasAffineCodimensionIn {ι : Type*} (d : ℕ)
    (Z X : Set (ι → ℂ)) : Prop :=
  (∀ C, IsIrreducibleAffineComponent C Z →
    ∃ chain : Fin (d + 1) → Set (ι → ℂ),
      StrictMono chain ∧ (∀ i, IsIrreducibleAffineClosed (chain i)) ∧
      chain 0 = C ∧ chain (Fin.last d) = X) ∧
  ∃ C, IsIrreducibleAffineComponent C Z ∧
    ¬ ∃ chain : Fin (d + 2) → Set (ι → ℂ),
      StrictMono chain ∧ (∀ i, IsIrreducibleAffineClosed (chain i)) ∧
      chain 0 = C ∧ chain (Fin.last (d + 1)) = X

/-- If one ideal is strictly contained in another and both contain a third ideal, their images in
the quotient by that third ideal remain strictly ordered. -/
lemma map_quotient_strictMono {R : Type*} [CommRing R]
    (I A B : Ideal R) (hIA : I ≤ A) (hAB : A < B) :
    A.map (Ideal.Quotient.mk I) < B.map (Ideal.Quotient.mk I) := by
  refine lt_of_le_of_ne (Ideal.map_mono hAB.le) ?_
  intro heq
  apply hAB.ne
  have hc := congrArg (Ideal.comap (Ideal.Quotient.mk I)) heq
  simpa [Ideal.comap_map_mk hIA, Ideal.comap_map_mk (hIA.trans hAB.le)] using hc

/-- A prime affine subvariety whose prime ideal is minimal over one additional
equation in the coordinate ring of `X` admits no intermediate irreducible
closed set.  This is the endpoint-fixed form of Krull's principal ideal
theorem needed by `HasAffineCodimensionIn 1`. -/
theorem no_three_chain_of_minimalPrime_span
    {ι : Type*} [Finite ι] {C X : Set (ι → ℂ)}
    (hC : IsIrreducibleAffineClosed C)
    (hX : IsIrreducibleAffineClosed X)
    (P : MvPolynomial ι ℂ)
    (hmin : MvPolynomial.vanishingIdeal ℂ C ∈
      (MvPolynomial.vanishingIdeal ℂ X ⊔ Ideal.span {P}).minimalPrimes) :
    ¬ ∃ chain : Fin 3 → Set (ι → ℂ),
      StrictMono chain ∧ (∀ i, IsIrreducibleAffineClosed (chain i)) ∧
      chain 0 = C ∧ chain (Fin.last 2) = X := by
  rintro ⟨chain, hmono, hirr, hzero, hlast⟩
  let mid : Fin 3 := ⟨1, by omega⟩
  have h0mid : (0 : Fin 3) < mid := by simp [mid]
  have hmidlast : mid < Fin.last 2 := by simp [mid, Fin.last]
  have hCY : C ⊂ chain mid := by simpa [hzero] using hmono h0mid
  have hYX : chain mid ⊂ X := by
    have h := hmono hmidlast
    rw [hlast] at h
    exact h
  let I : Ideal (MvPolynomial ι ℂ) := MvPolynomial.vanishingIdeal ℂ X
  let J : Ideal (MvPolynomial ι ℂ) := MvPolynomial.vanishingIdeal ℂ C
  let K : Ideal (MvPolynomial ι ℂ) :=
    MvPolynomial.vanishingIdeal ℂ (chain mid)
  have hIK : I < K := by
    exact vanishingIdeal_strict_anti (hirr mid).1 hX.1 hYX
  have hKJ : K < J := by
    exact vanishingIdeal_strict_anti hC.1 (hirr mid).1 hCY
  haveI hIprime : I.IsPrime :=
    (irreducibleAffineClosed_iff_isPrime hX.1 hX.2.1).mp hX
  haveI hKprime : K.IsPrime :=
    (irreducibleAffineClosed_iff_isPrime (hirr mid).1 (hirr mid).2.1).mp (hirr mid)
  haveI hJprime : J.IsPrime :=
    (irreducibleAffineClosed_iff_isPrime hC.1 hC.2.1).mp hC
  let q := Ideal.Quotient.mk I
  have hmapKJ : K.map q < J.map q :=
    map_quotient_strictMono I K J hIK.le hKJ
  have hmapIK : I.map q < K.map q :=
    map_quotient_strictMono I I K le_rfl hIK
  haveI hmapKprime : (K.map q).IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime hIK.le
  haveI hmapJprime : (J.map q).IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime (hIK.le.trans hKJ.le)
  have hheightJ : (J.map q).height ≤ 1 := by
    exact Ideal.map_height_le_one_of_mem_minimalPrimes hmin
  have hheightK_lt : (K.map q).height < 1 :=
    (Ideal.height_le_iff.mp hheightJ) (K.map q) inferInstance hmapKJ
  have hmapIbot : I.map q = ⊥ := Ideal.map_quotient_self I
  have hbotK : (⊥ : Ideal ((MvPolynomial ι ℂ) ⧸ I)) < K.map q := by
    simpa [hmapIbot] using hmapIK
  have hheightK_pos : (0 : ℕ∞) < (K.map q).height := by
    have hstrict := Ideal.height_strict_mono_of_isPrime hbotK
    simpa [Ideal.height_bot] using hstrict
  have hheightK_zero : (K.map q).height = 0 :=
    ENat.lt_one_iff_eq_zero.mp hheightK_lt
  simp [hheightK_zero] at hheightK_pos

private def affineTwoSetChain {ι : Type*}
    (C X : Set (ι → ℂ)) : Fin 2 → Set (ι → ℂ)
  | ⟨0, _⟩ => C
  | ⟨1, _⟩ => X
  | ⟨n + 2, hn⟩ => by omega

private lemma affineTwoSetChain_strictMono {ι : Type*}
    {C X : Set (ι → ℂ)} (hCX : C ⊂ X) :
    StrictMono (affineTwoSetChain C X) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  fin_cases i
  exact hCX

private def affineAppendTwo {ι : Type*} {d : ℕ}
    (chain : Fin (d + 1) → Set (ι → ℂ))
    (Y X : Set (ι → ℂ)) : Fin (d + 3) → Set (ι → ℂ) := fun i =>
  if hi : i.val < d + 1 then chain ⟨i.val, hi⟩
  else if i.val = d + 1 then Y else X

private lemma affineAppendTwo_strictMono {ι : Type*} {d : ℕ}
    {chain : Fin (d + 1) → Set (ι → ℂ)} (hchain : StrictMono chain)
    {C Y X : Set (ι → ℂ)} (hsub : ∀ i, chain i ⊆ C)
    (hCY : C ⊂ Y) (hYX : Y ⊂ X) :
    StrictMono (affineAppendTwo chain Y X) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  by_cases hi : i.val < d
  · have hi0 : i.val < d + 1 := by omega
    have hic : i.castSucc.val < d + 1 := by simpa using hi0
    have hi1 : i.succ.val < d + 1 := by simp; omega
    simp only [affineAppendTwo, dif_pos hic, dif_pos hi1]
    apply hchain
    simp
  · have hcases : i.val = d ∨ i.val = d + 1 := by omega
    rcases hcases with hid | hid
    · have hi0 : i.val < d + 1 := by omega
      have hic : i.castSucc.val < d + 1 := by simpa using hi0
      have hi1 : ¬ i.succ.val < d + 1 := by simp; omega
      have hi2 : i.succ.val = d + 1 := by simp; omega
      simp only [affineAppendTwo, dif_pos hic, dif_neg hi1, if_pos hi2]
      exact lt_of_le_of_lt (hsub ⟨i.val, hi0⟩) hCY
    · have hi0 : ¬ i.val < d + 1 := by omega
      have hic : ¬ i.castSucc.val < d + 1 := by simpa using hi0
      have hieq : i.castSucc.val = d + 1 := by simpa using hid
      have hi1 : i.val = d + 1 := hid
      have hs0 : ¬ i.succ.val < d + 1 := by simp; omega
      have hs1 : i.succ.val ≠ d + 1 := by simp; omega
      simp only [affineAppendTwo, dif_neg hic, if_pos hieq,
        dif_neg hs0, if_neg hs1]
      exact hYX

/-- Ambient affine-closed-chain ranks differing by one exclude an intermediate
irreducible affine-closed set.  The proof appends `Y` and `X` to a
maximal-length ambient-closed chain inside `C`, contradicting the upper bound
for `X`. -/
theorem no_intermediate_of_exact_affine_dimensions
    {ι : Type*} {d : ℕ} {C X : Set (ι → ℂ)}
    (hX : IsIrreducibleAffineClosed X)
    (hCdim : HasAffineZariskiDimension d C)
    (hXdim : HasAffineZariskiDimension (d + 1) X) :
    ¬ ∃ Y, IsIrreducibleAffineClosed Y ∧ C ⊂ Y ∧ Y ⊂ X := by
  rintro ⟨Y, hY, hCY, hYX⟩
  obtain ⟨chain, hmono, hirr, hsub⟩ := hCdim.1
  apply hXdim.2
  refine ⟨affineAppendTwo chain Y X,
    affineAppendTwo_strictMono hmono hsub hCY hYX, ?_, ?_⟩
  · intro i
    by_cases hi : i.val < d + 1
    · simpa [affineAppendTwo, hi] using hirr ⟨i.val, hi⟩
    · by_cases hy : i.val = d + 1
      · simpa [affineAppendTwo, hi, hy] using hY
      · simpa [affineAppendTwo, hi, hy] using hX
  · intro i
    by_cases hi : i.val < d + 1
    · simpa [affineAppendTwo, hi] using (hsub ⟨i.val, hi⟩).trans (hCY.le.trans hYX.le)
    · by_cases hy : i.val = d + 1
      · simpa [affineAppendTwo, hy] using hYX.le
      · have hi' : ¬ i.val ≤ d := by omega
        simp [affineAppendTwo, hi', hy]

/-- An irreducible affine-closed subset with no irreducible affine-closed set
strictly between it and an ambient irreducible variety is a maximal
ambient-closed irreducible subset of every proper intermediate locus. -/
theorem irreducibleAffineComponent_of_no_intermediate
    {ι : Type*} {C Z X : Set (ι → ℂ)}
    (hC : IsIrreducibleAffineClosed C)
    (hCZ : C ⊆ Z) (hZX : Z ⊆ X) (hne : Z ≠ X)
    (hno : ¬ ∃ Y, IsIrreducibleAffineClosed Y ∧ C ⊂ Y ∧ Y ⊂ X) :
    IsIrreducibleAffineComponent C Z := by
  refine ⟨hC, hCZ, ?_⟩
  intro Y hY hCY hYZ
  apply Set.Subset.antisymm
  · by_contra hYC
    have hCneY : C ≠ Y := by
      intro heq
      apply hYC
      rw [heq]
    have hCYstrict : C ⊂ Y :=
      Set.ssubset_iff_subset_ne.mpr ⟨hCY, hCneY⟩
    have hYX : Y ⊆ X := hYZ.trans hZX
    have hYXne : Y ≠ X := by
      intro heq
      apply hne
      exact Set.Subset.antisymm hZX (by simpa [heq] using hYZ)
    exact hno ⟨Y, hY, hCYstrict,
      Set.ssubset_iff_subset_ne.mpr ⟨hYX, hYXne⟩⟩
  · exact hCY

/-- In [a finite-dimensional complex affine space](hyp:ι), let
[the sublocus be irreducible and affine-closed](hyp:hC) and
[the ambient locus be irreducible and affine-closed](hyp:hX).
Adding [a polynomial equation](hyp:P) to the ambient locus makes
[the sublocus's vanishing ideal a minimal prime over the enlarged ideal](goal), provided
[the sublocus lies in the ambient locus](hyp:hCX),
[the equation vanishes on the sublocus](hyp:hPC),
[the equation does not vanish identically on the ambient locus](hyp:hPX), and
[no irreducible affine-closed locus lies strictly between them](hyp:hno).

This converts a no-intermediate-subvariety argument into an explicit
minimal-prime certificate in the coordinate ring of `X`. -/
theorem vanishingIdeal_mem_minimalPrimes_span_of_no_intermediate
    {ι : Type*} [Finite ι] {C X : Set (ι → ℂ)}
    (hC : IsIrreducibleAffineClosed C)
    (hX : IsIrreducibleAffineClosed X)
    (hCX : C ⊆ X)
    (P : MvPolynomial ι ℂ)
    (hPC : P ∈ MvPolynomial.vanishingIdeal ℂ C)
    (hPX : P ∉ MvPolynomial.vanishingIdeal ℂ X)
    (hno : ¬ ∃ Y, IsIrreducibleAffineClosed Y ∧ C ⊂ Y ∧ Y ⊂ X) :
    MvPolynomial.vanishingIdeal ℂ C ∈
      (MvPolynomial.vanishingIdeal ℂ X ⊔ Ideal.span {P}).minimalPrimes := by
  let I := MvPolynomial.vanishingIdeal ℂ X
  let J := MvPolynomial.vanishingIdeal ℂ C
  haveI hIprime : I.IsPrime :=
    (irreducibleAffineClosed_iff_isPrime hX.1 hX.2.1).mp hX
  haveI hJprime : J.IsPrime :=
    (irreducibleAffineClosed_iff_isPrime hC.1 hC.2.1).mp hC
  have hIJ : I ≤ J := MvPolynomial.vanishingIdeal_anti_mono hCX
  have hspanJ : Ideal.span {P} ≤ J :=
    Ideal.span_le.mpr (by simpa [J] using hPC)
  have hsupJ : I ⊔ Ideal.span {P} ≤ J := sup_le hIJ hspanJ
  refine ⟨⟨inferInstance, hsupJ⟩, ?_⟩
  intro Q hQ hQJ
  haveI hQprime : Q.IsPrime := hQ.1
  have hIQ : I ≤ Q := le_sup_left.trans hQ.2
  have hPQ : P ∈ Q :=
    hQ.2 (Ideal.mem_sup_right (Ideal.subset_span (by simp)))
  have hIQne : I ≠ Q := by
    intro heq
    apply hPX
    change P ∈ I
    rw [heq]
    exact hPQ
  have hIQlt : I < Q := lt_of_le_of_ne hIQ hIQne
  by_contra hJQ
  change ¬ J ≤ Q at hJQ
  change Q ≤ J at hQJ
  have hQJne : Q ≠ J := by
    intro heq
    apply hJQ
    rw [← heq]
  have hQJlt : Q < J := lt_of_le_of_ne hQJ hQJne
  have hzeroJ : MvPolynomial.zeroLocus ℂ J = C := by
    simpa [J, affineZariskiClosure] using hC.1
  have hzeroI : MvPolynomial.zeroLocus ℂ I = X := by
    simpa [I, affineZariskiClosure] using hX.1
  apply hno
  exact ⟨MvPolynomial.zeroLocus ℂ Q,
    irreducible_zeroLocus_of_prime Q,
    by simpa only [hzeroJ] using (zeroLocus_strict_anti hQJlt),
    by simpa only [hzeroI] using (zeroLocus_strict_anti hIQlt)⟩

/-- For subsets `C`, `Z`, `X` of `ι → ℂ` (with `ι` finite), suppose [`X` is irreducible
Zariski-closed](hyp:hX), [`Z` is a proper subset of `X`](hyp:hZX,hne), [`C` is a maximal
ambient-closed irreducible subset of `Z`](hyp:hC), and [the vanishing ideal of `C` is a minimal
prime over the vanishing ideal of `X` joined with the principal ideal generated by some polynomial
`P`](hyp:hmin). Then [the endpoint-fixed ambient closed-chain codimension of `Z` relative to `X`
is exactly `1`](goal). -/
theorem hasAffineCodimensionIn_one_of_minimalPrime_span
    {ι : Type*} [Finite ι] {C Z X : Set (ι → ℂ)}
    (hX : IsIrreducibleAffineClosed X)
    (hZX : Z ⊆ X) (hne : Z ≠ X)
    (hC : IsIrreducibleAffineComponent C Z)
    (P : MvPolynomial ι ℂ)
    (hmin : MvPolynomial.vanishingIdeal ℂ C ∈
      (MvPolynomial.vanishingIdeal ℂ X ⊔ Ideal.span {P}).minimalPrimes) :
    HasAffineCodimensionIn 1 Z X := by
  constructor
  · intro D hD
    have hDX : D ⊂ X := by
      refine Set.ssubset_iff_subset_ne.mpr ⟨hD.2.1.trans hZX, ?_⟩
      intro heq
      apply hne
      apply Set.Subset.antisymm hZX
      simpa [heq] using hD.2.1
    exact ⟨affineTwoSetChain D X, affineTwoSetChain_strictMono hDX,
      (by
        intro i
        fin_cases i
        · exact hD.1
        · exact hX), rfl, rfl⟩
  · refine ⟨C, hC, ?_⟩
    exact no_three_chain_of_minimalPrime_span hC.1 hX P hmin

end

end Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension
