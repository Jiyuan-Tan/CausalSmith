/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Ring

/-!
# Pairing rearrangements and Chebyshev chord products

This module proves the finite adjacent-pair rearrangement inequality, defines the
Chebyshev chord list, and identifies its paired product with the complex
root-distance product.
-/

@[expose] public section

namespace Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality

/-! ## Adjacent-pair rearrangement -/


/-- `adjacentPairProduct t xs` multiplies `a * b + t` over consecutive pairs
`a, b` of `xs`. A final unpaired entry contributes no factor. [The input](hyp:t) determines
[this pairing product](goal). -/
def adjacentPairProduct (t : ℝ) : List ℝ → ℝ
  | a :: b :: xs => (a * b + t) * adjacentPairProduct t xs
  | _ => 1

/-- For four decreasing real numbers, replacing the crossing pairs `(a,c)`
and `(b,d)` by the adjacent pairs `(a,b)` and `(c,d)` cannot decrease the
product after adding the same nonnegative constant to each pair.
[The inputs](hyp:a,b,c,d,t,ht,hab,hbc,hcd) imply [this comparison](goal). -/
lemma crossingPairProduct_le_adjacentPairProduct
    {a b c d t : ℝ} (ht : 0 ≤ t) (hab : b ≤ a) (hbc : c ≤ b)
    (hcd : d ≤ c) :
    (a * c + t) * (b * d + t) ≤ (a * b + t) * (c * d + t) := by
  have had : d ≤ a := hcd.trans (hbc.trans hab)
  have hnonneg : 0 ≤ t * (a - d) * (b - c) :=
    mul_nonneg (mul_nonneg ht (sub_nonneg.mpr had)) (sub_nonneg.mpr hbc)
  calc
    (a * c + t) * (b * d + t) ≤
        (a * c + t) * (b * d + t) + t * (a - d) * (b - c) :=
      le_add_of_nonneg_right hnonneg
    _ = (a * b + t) * (c * d + t) := by ring

/-- For four decreasing real numbers, replacing the outer/inner pairs `(a,d)`
and `(b,c)` by the adjacent pairs `(a,b)` and `(c,d)` cannot decrease the
product after adding the same nonnegative constant to each pair.
[The inputs](hyp:a,b,c,d,t,ht,hab,hbc,hcd) imply [this comparison](goal). -/
lemma nestedPairProduct_le_adjacentPairProduct
    {a b c d t : ℝ} (ht : 0 ≤ t) (hab : b ≤ a) (hbc : c ≤ b)
    (hcd : d ≤ c) :
    (a * d + t) * (b * c + t) ≤ (a * b + t) * (c * d + t) := by
  have hac : c ≤ a := hbc.trans hab
  have hbd : d ≤ b := hcd.trans hbc
  have hnonneg : 0 ≤ t * (a - c) * (b - d) :=
    mul_nonneg (mul_nonneg ht (sub_nonneg.mpr hac)) (sub_nonneg.mpr hbd)
  calc
    (a * d + t) * (b * c + t) ≤
        (a * d + t) * (b * c + t) + t * (a - c) * (b - d) :=
      le_add_of_nonneg_right hnonneg
    _ = (a * b + t) * (c * d + t) := by ring

private def pairedEntries : List (ℝ × ℝ) → List ℝ
  | [] => []
  | (a, b) :: ps => a :: b :: pairedEntries ps

private def pairedProduct (t : ℝ) : List (ℝ × ℝ) → ℝ
  | [] => 1
  | (a, b) :: ps => (a * b + t) * pairedProduct t ps

private lemma extract_pair {t x : ℝ} {ps : List (ℝ × ℝ)}
    (hx : x ∈ pairedEntries ps) :
    ∃ u qs, (pairedEntries ps).Perm (x :: u :: pairedEntries qs) ∧
      pairedProduct t ps = (x * u + t) * pairedProduct t qs := by
  induction ps with
  | nil => simp [pairedEntries] at hx
  | cons p ps ih =>
      rcases p with ⟨a, b⟩
      simp only [pairedEntries, List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · exact ⟨b, ps, .refl _, rfl⟩
      · exact ⟨a, ps, List.Perm.swap _ _ _, by
          simp only [pairedProduct]
          ring⟩
      · rcases ih hx with ⟨u, qs, hp, heq⟩
        refine ⟨u, (a, b) :: qs, ?_, ?_⟩
        · have h₁ := hp.cons b |>.cons a
          have h₂ := List.Perm.append_right (pairedEntries qs)
            (List.perm_append_comm (l₁ := [a, b]) (l₂ := [x, u]))
          exact h₁.trans (by simpa [pairedEntries] using h₂)
        · simp only [pairedProduct]
          rw [heq]
          ring

private lemma pairedProduct_nonneg {t : ℝ} (ht : 0 ≤ t)
    {ps : List (ℝ × ℝ)}
    (h : ∀ x ∈ pairedEntries ps, 0 ≤ x) :
    0 ≤ pairedProduct t ps := by
  induction ps with
  | nil => simp [pairedProduct]
  | cons p ps ih =>
      rcases p with ⟨a, b⟩
      simp only [pairedEntries, List.mem_cons] at h
      simp only [pairedProduct]
      exact mul_nonneg (add_nonneg (mul_nonneg (h a (Or.inl rfl))
        (h b (Or.inr (Or.inl rfl)))) ht)
        (ih fun x hx => h x (Or.inr (Or.inr hx)))

private lemma even_tail_of_even_cons_cons {a b : α} {xs : List α}
    (h : Even (a :: b :: xs).length) : Even xs.length := by
  rcases h with ⟨k, hk⟩
  simp only [List.length_cons] at hk
  have hkpos : 1 ≤ k := by omega
  refine ⟨k - 1, ?_⟩
  omega

private lemma pairedProduct_le_of_perm_sorted
    {t : ℝ} (ht : 0 ≤ t) {xs : List ℝ} {ps : List (ℝ × ℝ)}
    (heven : Even xs.length)
    (hsorted : xs.Pairwise (fun a b => b ≤ a))
    (hnonneg : ∀ a ∈ xs, 0 ≤ a)
    (hperm : (pairedEntries ps).Perm xs) :
    pairedProduct t ps ≤ adjacentPairProduct t xs := by
  cases xs with
  | nil =>
      have hempty : pairedEntries ps = [] := hperm.eq_nil
      cases ps with
      | nil => simp [pairedProduct, adjacentPairProduct]
      | cons p ps =>
          rcases p with ⟨a, b⟩
          simp [pairedEntries] at hempty
  | cons a xs =>
      cases xs with
      | nil =>
          rcases heven with ⟨k, hk⟩
          simp only [List.length_cons, List.length_nil] at hk
          omega
      | cons b tail =>
          have heven' : Even tail.length := even_tail_of_even_cons_cons heven
          rcases List.pairwise_cons.mp hsorted with ⟨ha, hsorted_b⟩
          rcases List.pairwise_cons.mp hsorted_b with ⟨hb, hsorted_tail⟩
          have hab : b ≤ a := ha b (by simp)
          have hnonneg_tail : ∀ x ∈ tail, 0 ≤ x :=
            fun x hx => hnonneg x (by simp [hx])
          have ha_mem : a ∈ pairedEntries ps := (hperm.mem_iff).2 (by simp)
          rcases extract_pair ha_mem with ⟨u, qs, hp, hprod⟩
          have hrest : (u :: pairedEntries qs).Perm (b :: tail) :=
            List.Perm.cons_inv (hp.symm.trans hperm)
          by_cases hu : u = b
          · subst u
            have htailperm : (pairedEntries qs).Perm tail :=
              List.Perm.cons_inv hrest
            have hind := pairedProduct_le_of_perm_sorted ht heven'
              hsorted_tail hnonneg_tail htailperm
            have hfactor : 0 ≤ a * b + t :=
              add_nonneg (mul_nonneg (hnonneg a (by simp))
                (hnonneg b (by simp))) ht
            rw [hprod]
            exact mul_le_mul_of_nonneg_left hind hfactor
          · have hb_mem : b ∈ pairedEntries qs := by
              have hm : b ∈ u :: pairedEntries qs :=
                (hrest.mem_iff).2 (by simp)
              simpa [show b ≠ u from Ne.symm hu] using hm
            rcases extract_pair hb_mem with ⟨v, rs, hp₂, hprod₂⟩
            have hsource : (u :: b :: v :: pairedEntries rs).Perm
                (b :: tail) :=
              (hp₂.cons u).symm.trans hrest
            have hrem : (u :: v :: pairedEntries rs).Perm tail := by
              apply List.Perm.cons_inv
              exact (List.Perm.swap b u (v :: pairedEntries rs)).symm.trans hsource
            have hu_tail : u ∈ tail := (hrem.mem_iff).1 (by simp)
            have hv_tail : v ∈ tail := (hrem.mem_iff).1 (by simp)
            have hub : u ≤ b := hb u hu_tail
            have hvb : v ≤ b := hb v hv_tail
            have hexchange :
                (a * u + t) * (b * v + t) ≤
                  (a * b + t) * (u * v + t) := by
              by_cases huv : v ≤ u
              · exact crossingPairProduct_le_adjacentPairProduct ht hab hub huv
              · have huv' : u ≤ v := le_of_not_ge huv
                simpa [mul_comm u v] using
                  (nestedPairProduct_le_adjacentPairProduct ht hab hvb huv')
            have hrs_nonneg : ∀ x ∈ pairedEntries rs, 0 ≤ x := by
              intro x hx
              exact hnonneg_tail x ((hrem.mem_iff).1 (by simp [hx]))
            have hprod_nonneg : 0 ≤ pairedProduct t rs :=
              pairedProduct_nonneg ht hrs_nonneg
            have hind := pairedProduct_le_of_perm_sorted (ps := (u, v) :: rs)
              ht heven' hsorted_tail hnonneg_tail
                (by simpa [pairedEntries] using hrem)
            have hfactor : 0 ≤ a * b + t :=
              add_nonneg (mul_nonneg (hnonneg a (by simp))
                (hnonneg b (by simp))) ht
            calc
              pairedProduct t ps =
                  ((a * u + t) * (b * v + t)) * pairedProduct t rs := by
                    rw [hprod, hprod₂]
                    ring
              _ ≤ ((a * b + t) * (u * v + t)) * pairedProduct t rs :=
                mul_le_mul_of_nonneg_right hexchange hprod_nonneg
              _ = (a * b + t) * pairedProduct t ((u, v) :: rs) := by
                simp only [pairedProduct]
                ring
              _ ≤ (a * b + t) * adjacentPairProduct t tail :=
                mul_le_mul_of_nonneg_left hind hfactor
              _ = adjacentPairProduct t (a :: b :: tail) := rfl
termination_by xs.length

private def listPairs : List ℝ → List (ℝ × ℝ)
  | a :: b :: xs => (a, b) :: listPairs xs
  | _ => []

private lemma pairedProduct_listPairs (t : ℝ) (xs : List ℝ) :
    pairedProduct t (listPairs xs) = adjacentPairProduct t xs := by
  induction xs using listPairs.induct <;>
    simp_all [listPairs, pairedProduct, adjacentPairProduct]

private lemma pairedEntries_listPairs_of_even {xs : List ℝ}
    (heven : Even xs.length) :
    pairedEntries (listPairs xs) = xs := by
  cases xs with
  | nil => rfl
  | cons a xs =>
      cases xs with
      | nil =>
          rcases heven with ⟨k, hk⟩
          simp only [List.length_cons, List.length_nil] at hk
          omega
      | cons b tail =>
          have heven' : Even tail.length := even_tail_of_even_cons_cons heven
          rw [show listPairs (a :: b :: tail) = (a, b) :: listPairs tail from rfl]
          rw [show pairedEntries ((a, b) :: listPairs tail) =
            a :: b :: pairedEntries (listPairs tail) from rfl]
          rw [pairedEntries_listPairs_of_even heven']
termination_by xs.length

/-- Let `xs` be a decreasing list of nonnegative real numbers of even length.
For every permutation `ys` of `xs`, the consecutive-pair product of `ys` is
at most the consecutive-pair product of `xs` itself.
[The inputs](hyp:t,ht,xs,ys,heven,hsorted,hnonneg,hperm) imply [this bound](goal). -/
theorem adjacentPairProduct_le_of_perm_sorted
    {t : ℝ} (ht : 0 ≤ t) {xs ys : List ℝ} (heven : Even xs.length)
    (hsorted : xs.Pairwise (fun a b => b ≤ a))
    (hnonneg : ∀ a ∈ xs, 0 ≤ a) (hperm : ys.Perm xs) :
    adjacentPairProduct t ys ≤ adjacentPairProduct t xs := by
  -- Duffin--Schaeffer (1941), Lemma II.  Induct on the number of pairs.
  -- In a nonempty permuted pairing, locate the two largest entries of `xs`.
  -- If they are not paired together, their partners and the four-term lemmas
  -- above give an exchange that does not decrease the product.  Remove the
  -- resulting largest adjacent pair and apply the induction hypothesis to the
  -- remaining sorted tail.  Nonnegativity makes multiplication monotone.
  have heven_ys : Even ys.length := hperm.length_eq ▸ heven
  rw [← pairedProduct_listPairs t ys]
  apply pairedProduct_le_of_perm_sorted ht heven hsorted hnonneg
  rw [pairedEntries_listPairs_of_even heven_ys]
  exact hperm

/-! ## Chebyshev chord data -/


/-- [A degree and index](hyp:L,k) determine [the corresponding Chebyshev root angle](goal),
equal to the odd multiple `(2k+1)π/(2L)`. -/
noncomputable def chebyshevRootAngle (L k : ℕ) : ℝ :=
  (((2 * k + 1 : ℕ) : ℝ) * Real.pi) / (2 * (L : ℝ))

/-- The `k`-th cosine root used in the degree-`L` Chebyshev product, indexed by
`0 ≤ k < L`. [the stated inputs](hyp:L,k) establish [the defined object](goal). -/
noncomputable def chebyshevZero (L k : ℕ) : ℝ :=
  Real.cos (chebyshevRootAngle L k)

/-- The squared chord length from `1` to the point of the unit circle with
argument `θ`. [The stated angle](hyp:θ) determines [the defined object](goal). -/
noncomputable def cosineChordSq (θ : ℝ) : ℝ :=
  2 - 2 * Real.cos θ

/-- The `2L` chord squares associated with an abscissa angle `θ`, listed in
the two-element pairs belonging to the `L` Chebyshev root angles. [The degree
and angle](hyp:L,θ) determine [the defined object](goal). -/
noncomputable def chebyshevPairedChordList (L : ℕ) (θ : ℝ) : List ℝ :=
  (Finset.range L).val.toList.flatMap fun k =>
    [cosineChordSq (θ + chebyshevRootAngle L k),
      cosineChordSq (θ - chebyshevRootAngle L k)]

/-! ## Chord-product factorization -/


private lemma adjacentPairProduct_flatMap_pairs
    (t : ℝ) (xs : List ℕ) (a b : ℕ → ℝ) :
    adjacentPairProduct t (xs.flatMap fun k => [a k, b k]) =
      (xs.map fun k => a k * b k + t).prod := by
  induction xs with
  | nil => simp [adjacentPairProduct]
  | cons k xs ih => simp [adjacentPairProduct, ih]

/-- Pairing the two chord squares belonging to each Chebyshev root converts
`a*b + 4y²` into four times the squared distance from `cos θ + iy` to that
root. [The degree, angle, and height](hyp:L,θ,y) determine [this factorization](goal). -/
theorem adjacentPairProduct_chebyshevPairedChordList
    (L : ℕ) (θ y : ℝ) :
    adjacentPairProduct (4 * y ^ 2) (chebyshevPairedChordList L θ) =
      ∏ k ∈ Finset.range L,
        4 * ‖((Real.cos θ - chebyshevZero L k : ℝ) : ℂ) +
          (y : ℂ) * Complex.I‖ ^ 2 := by
  have pair_identity (α : ℝ) :
      (2 - 2 * Real.cos (θ + α)) * (2 - 2 * Real.cos (θ - α)) + 4 * y ^ 2 =
        4 * ‖((Real.cos θ - Real.cos α : ℝ) : ℂ) +
          (y : ℂ) * Complex.I‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_add_mul_I]
    rw [Real.cos_add, Real.cos_sub]
    nlinarith [Real.sin_sq_add_cos_sq θ, Real.sin_sq_add_cos_sq α]
  rw [chebyshevPairedChordList, adjacentPairProduct_flatMap_pairs]
  rw [Multiset.prod_map_toList]
  apply Finset.prod_congr rfl
  intro k hk
  rw [cosineChordSq, chebyshevZero]
  exact pair_identity (chebyshevRootAngle L k)

end Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality
