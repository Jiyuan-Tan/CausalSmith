/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.ChebyshevChordDefinitions
import Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.PairingRearrangement

/-!
# Adjacent ordering of centered Chebyshev chords

For an angle in the centered cell of the odd Chebyshev grid, the two chord
squares belonging to each root become an adjacent pair after decreasing
sorting. This is the order-theoretic core of the chord rearrangement proof.
-/

namespace Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality

private lemma cosineChordSq_mono_on_zero_pi {x y : ℝ}
    (hx : 0 ≤ x) (hy : y ≤ Real.pi) (hxy : x ≤ y) :
    cosineChordSq x ≤ cosineChordSq y := by
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi hx hy hxy
  unfold cosineChordSq
  linarith

private lemma adjacentPairProduct_flatMap_two (t : ℝ) (ks : List ℕ)
    (a b : ℕ → ℝ) :
    adjacentPairProduct t (ks.flatMap fun k => [a k, b k]) =
      (ks.map fun k => a k * b k + t).prod := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
      simpa [adjacentPairProduct] using
        congrArg (fun z => (a k * b k + t) * z) ih

/-- At a centered angle `|φ| ≤ π/(2L)`, decreasingly sorting all `2L` chord
squares can be done without changing the product obtained from the root-angle
pairing, for any common additive term. [The degree, its positivity, the angle,
and the additive term](hyp:L,hL,φ,hφ,t) establish [the stated conclusion](goal). -/
theorem exists_sorted_chebyshevChordList_with_adjacentPairProduct_eq_of_centered
    {L : ℕ} (hL : 0 < L) {φ t : ℝ}
    (hφ : |φ| ≤ Real.pi / (2 * (L : ℝ))) :
    ∃ zs : List ℝ,
      zs.Perm (chebyshevPairedChordList L φ) ∧
        zs.Pairwise (fun a b => b ≤ a) ∧
          adjacentPairProduct t zs =
            adjacentPairProduct t (chebyshevPairedChordList L φ) := by
  let δ : ℝ := Real.pi / (2 * (L : ℝ))
  let u : ℝ := |φ|
  let a : ℕ → ℝ := fun k =>
    cosineChordSq (chebyshevRootAngle L k + u)
  let b : ℕ → ℝ := fun k =>
    cosineChordSq (chebyshevRootAngle L k - u)
  -- Reverse the roots, and put the larger circular distance first in each
  -- root block. At `u = δ`, neighboring blocks may tie.
  let zs := (List.range L).reverse.flatMap fun k => [a k, b k]
  have hLr : 0 < (L : ℝ) := by exact_mod_cast hL
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hu0 : 0 ≤ u := abs_nonneg φ
  have huδ : u ≤ δ := hφ
  have hangle (k : ℕ) :
      chebyshevRootAngle L k = ((2 * k + 1 : ℕ) : ℝ) * δ := by
    simp only [chebyshevRootAngle, δ]
    ring
  have hcast (k : ℕ) : ((2 * k + 1 : ℕ) : ℝ) = 2 * (k : ℝ) + 1 := by
    push_cast
    ring
  have hδpi : 2 * (L : ℝ) * δ = Real.pi := by
    dsimp [δ]
    field_simp
  have hbounds (k : ℕ) (hk : k < L) :
      0 ≤ chebyshevRootAngle L k - u ∧
        chebyshevRootAngle L k + u ≤ Real.pi := by
    have hkcast : (k : ℝ) ≤ (L : ℝ) - 1 := by
      have hkn : k + 1 ≤ L := by omega
      have hkr : (k : ℝ) + 1 ≤ (L : ℝ) := by exact_mod_cast hkn
      linarith
    have hk0 : 0 ≤ (k : ℝ) := by positivity
    rw [hangle, hcast]
    constructor <;> nlinarith
  have hwithin (k : ℕ) (hk : k < L) : b k ≤ a k := by
    dsimp [a, b]
    apply cosineChordSq_mono_on_zero_pi
    · exact (hbounds k hk).1
    · exact (hbounds k hk).2
    · linarith
  have hcross (j k : ℕ) (hj : j < L) (hk : k < L) (hjk : j < k) :
      a j ≤ b k := by
    have hjk' : (j : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hjk
    dsimp [a, b]
    apply cosineChordSq_mono_on_zero_pi
    · have h := (hbounds j hj).1
      rw [hangle, hcast] at h ⊢
      nlinarith
    · have h := (hbounds k hk).2
      rw [hangle, hcast] at h ⊢
      nlinarith
    · rw [hangle, hangle, hcast, hcast]
      nlinarith
  have hsorted : zs.Pairwise (fun x y => y ≤ x) := by
    dsimp [zs]
    rw [List.pairwise_flatMap]
    constructor
    · intro k hk
      simp only [List.mem_reverse, List.mem_range] at hk
      simpa using hwithin k hk
    · rw [List.pairwise_reverse]
      have hrangePair : (List.range L).Pairwise
          (fun j k => j < k ∧ k < L) := by
        rw [List.pairwise_iff_getElem]
        intro i j hi hj hij
        simp only [List.length_range] at hi hj
        simp only [List.getElem_range]
        omega
      apply hrangePair.imp
      intro j k hjk x hx y hy
      have hj : j < L := lt_trans hjk.1 hjk.2
      have hk : k < L := hjk.2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact (hcross j k hj hk hjk.1).trans (hwithin k hk)
      · exact (hwithin j hj).trans
          ((hcross j k hj hk hjk.1).trans (hwithin k hk))
      · exact hcross j k hj hk hjk.1
      · exact (hwithin j hj).trans (hcross j k hj hk hjk.1)
  -- Replacing `φ` by `|φ|` only swaps the two entries in each root block.
  have hpairs (k : ℕ) (hk : k < L) :
      [a k, b k].Perm
        [cosineChordSq (φ + chebyshevRootAngle L k),
          cosineChordSq (φ - chebyshevRootAngle L k)] := by
    by_cases hφ0 : 0 ≤ φ
    · have hu : u = φ := abs_of_nonneg hφ0
      have ha : a k = cosineChordSq (φ + chebyshevRootAngle L k) := by
        dsimp [a]
        rw [hu]
        congr 1 <;> ring
      have hb : b k = cosineChordSq (φ - chebyshevRootAngle L k) := by
        dsimp [b]
        rw [hu]
        rw [show chebyshevRootAngle L k - φ =
          -(φ - chebyshevRootAngle L k) by ring]
        simp only [cosineChordSq]
        rw [Real.cos_neg]
      rw [ha, hb]
    · have hφ0' : φ ≤ 0 := le_of_not_ge hφ0
      have hu : u = -φ := abs_of_nonpos hφ0'
      have ha : a k = cosineChordSq (φ - chebyshevRootAngle L k) := by
        dsimp [a]
        rw [hu]
        rw [show chebyshevRootAngle L k + -φ =
          -(φ - chebyshevRootAngle L k) by ring]
        simp only [cosineChordSq]
        rw [Real.cos_neg]
      have hb : b k = cosineChordSq (φ + chebyshevRootAngle L k) := by
        dsimp [b]
        rw [hu]
        congr 1 <;> ring
      rw [ha, hb]
      exact List.Perm.swap _ _ []
  have hrange : (Finset.range L).val.toList.Perm (List.range L) := by
    refine (List.perm_ext_iff_of_nodup ?_ List.nodup_range).2 ?_
    · rw [← Multiset.coe_nodup, Multiset.coe_toList]
      exact (Finset.range L).nodup
    · simp
  have hperm : zs.Perm (chebyshevPairedChordList L φ) := by
    dsimp [zs]
    rw [chebyshevPairedChordList]
    exact ((List.reverse_perm (List.range L)).flatMap
      (fun k hk => List.Perm.refl _)).trans <|
        hrange.symm.flatMap fun k hk => hpairs k (by simpa using hk)
  refine ⟨zs, hperm, hsorted, ?_⟩
  rw [chebyshevPairedChordList]
  rw [adjacentPairProduct_flatMap_two, adjacentPairProduct_flatMap_two]
  rw [List.map_reverse, List.prod_reverse]
  rw [(hrange.symm.map (fun k => a k * b k + t)).prod_eq]
  congr 1
  apply List.map_congr_left
  intro k hk
  have hp := (hpairs k (by simpa using hk)).prod_eq
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    congrArg (fun z => z + t) hp

end Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality
