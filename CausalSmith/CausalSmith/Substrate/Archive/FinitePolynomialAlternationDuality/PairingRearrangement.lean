/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Ring

/-!
# A finite adjacent-pair product rearrangement inequality

This module isolates the purely finite inequality used in the
Duffin--Schaeffer chord proof.  If a nonnegative list is sorted in decreasing
order, pairing adjacent entries maximizes the product of the pairwise products
after adding the same nonnegative constant to every pair.
-/

@[expose] public section

namespace CausalSmith.Substrate.FinitePolynomialAlternationDuality

/-- `adjacentPairProduct t xs` multiplies `a * b + t` over consecutive pairs
`a, b` of `xs`.  A final unpaired entry contributes no factor. -/
def adjacentPairProduct (t : ℝ) : List ℝ → ℝ
  | a :: b :: xs => (a * b + t) * adjacentPairProduct t xs
  | _ => 1

/-- For four decreasing real numbers, replacing the crossing pairs `(a,c)`
and `(b,d)` by the adjacent pairs `(a,b)` and `(c,d)` cannot decrease the
product after adding the same nonnegative constant to each pair. -/
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
product after adding the same nonnegative constant to each pair. -/
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
at most the consecutive-pair product of `xs` itself. -/
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

end CausalSmith.Substrate.FinitePolynomialAlternationDuality
