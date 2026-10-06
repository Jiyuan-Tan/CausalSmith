module
public import Causalean.Mathlib.Analysis.Calculus.FiniteProduct.Basic

/-!
# Support-visible finite Leibniz expansions

The second-coordinate support is the set of hit indices, while the occurrence count
retains the order at each index. The total order is two for every (2,2) summand.
The expansion separates a single factor's (2,2) jet from two distinct factors with
positive second-coordinate order. A companion expansion displays the familiar
diagonal and off-diagonal formula for the (2,0) jet.
-/

@[expose] public section

open scoped BigOperators
noncomputable section

namespace Causalean.Mathlib.Analysis.Calculus.FiniteProduct

variable {ι : Type*} [DecidableEq ι]

/-- The [second-coordinate derivative support](goal) of [a hit list](hyp:ys)
is its set of distinct indices. The list, rather than this set alone, retains
the order at each index. -/
def secondSupport (ys : List ι) : Finset ι := ys.toFinset

/-- [An index](hyp:i) lies in [the second-coordinate support](hyp:ys)
[exactly when its derivative order is positive](goal). -/
theorem mem_secondSupport_iff (ys : List ι) (i : ι) :
    i ∈ secondSupport ys ↔ 0 < ys.count i := by
  simpa only [secondSupport, List.mem_toFinset] using
    (List.count_pos_iff (a := i) (l := ys)).symm

/-- If [every entry of a hit list ys](hyp:ys) [lies in a finite index set I](hyp:I,hys), then
[the number of occurrences of each index of I in ys, summed over I, equals the length of
ys](goal). -/
theorem sum_second_orders (I : Finset ι) (ys : List ι)
    (hys : ∀ i ∈ ys, i ∈ I) :
    ∑ i ∈ I, ys.count i = ys.length := by
  induction ys with
  | nil => simp
  | cons r ys ih =>
    have hr : r ∈ I := hys r (by simp)
    have htail : ∀ i ∈ ys, i ∈ I := fun i hi => hys i (by simp [hi])
    simp only [List.count_cons, List.length_cons, Finset.sum_add_distrib, ih htail]
    simp only [beq_iff_eq, Finset.sum_ite_eq, hr, ite_true]

/-- If [two second-coordinate hits r and s](hyp:r,s) [both lie in a finite index set
I](hyp:I,hr,hs), then [the occurrence counts of the indices of I in the two-element hit list r, s
sum to two](goal), including when r and s are equal. -/
theorem summand22_total_second_order (I : Finset ι) (r s : ι)
    (hr : r ∈ I) (hs : s ∈ I) :
    ∑ i ∈ I, ([r, s] : List ι).count i = 2 := by
  simpa using sum_second_orders I [r, s] (by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> assumption)

/-- [The support of two second-coordinate hits](hyp:r,s)
[is precisely the pair of hit indices](goal); equal hits give a singleton. -/
theorem secondSupport_pair (r s : ι) : secondSupport [r, s] = {r, s} := by
  simp [secondSupport]

/-- [The explicit (2,0) jet](hyp:I,J,a,u) [equals the diagonal sum of second
factor jets plus the ordered distinct-index sum of products of first factor
jets](goal). Thus both first-coordinate Leibniz cases are exposed. -/
theorem productJet20_eq_diagonal_add_offDiagonal (I : Finset ι) (J : FactorJets ι)
    (a u : ℝ) :
    productJet20 I J a u =
      (∑ i ∈ I, J.f20 i a u * ∏ k ∈ I.erase i, J.f00 k a u) +
      ∑ i ∈ I, ∑ j ∈ I.erase i,
        J.f10 i a u * J.f10 j a u *
          ∏ k ∈ (I.erase i).erase j, J.f00 k a u := by
  unfold productJet20
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.add_sum_erase I _ hi]
  congr 1
  · unfold leibnizTerm
    rw [← Finset.mul_prod_erase I _ hi]
    simp only [List.count_cons, List.count_nil, beq_self_eq_true, ite_true,
      factorJet]
    congr 1
    apply Finset.prod_congr rfl
    intro k hk
    have hik : i ≠ k := (Finset.mem_erase.mp hk).1.symm
    simp [hik]
  · apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    unfold leibnizTerm
    rw [← Finset.mul_prod_erase I _ hi,
      ← Finset.mul_prod_erase (I.erase i) _ hj]
    simp only [List.count_cons, List.count_nil, beq_self_eq_true, ite_true,
      beq_iff_eq, hji, hji.symm, ite_false, factorJet]
    rw [← mul_assoc]
    congr 1
    apply Finset.prod_congr rfl
    intro k hk
    have hjk : j ≠ k := (Finset.mem_erase.mp hk).1.symm
    have hik : i ≠ k := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1.symm
    simp [hik, hjk]

/-- For [factor jets J of a finite index set I](hyp:I,J) at [a point (a, u)](hyp:a,u), if
[an index r of I](hyp:r,hr) is hit twice in the second coordinate and [the two first-coordinate
hits p and q are not both r](hyp:p,q,hnot), then [the corresponding (2,2) Leibniz summand is
zero](goal). -/
theorem leibnizTerm22_repeated_u_zero (I : Finset ι) (J : FactorJets ι)
    (p q r : ι) (a u : ℝ) (hr : r ∈ I) (hnot : p ≠ r ∨ q ≠ r) :
    leibnizTerm I J [p, q] [r, r] a u = 0 := by
  unfold leibnizTerm
  rw [← Finset.mul_prod_erase I _ hr]
  have hz : factorJet J r (([p, q] : List ι).count r) 2 a u = 0 := by
    rcases hnot with hp | hq
    · by_cases hq : q = r <;> simp [hp, hq, factorJet]
    · by_cases hp : p = r <;> simp [hp, hq, factorJet]
  simpa using congrArg (fun x : ℝ => x *
    ∏ i ∈ I.erase r, factorJet J i (([p, q] : List ι).count i)
      (([r, r] : List ι).count i) a u) hz

/-- For [factor jets J of a finite index set I](hyp:I,J) at [a point (a, u)](hyp:a,u), if
[all four hits fall on one index r of I](hyp:r,hr), then [the Leibniz summand equals the (2,2)
jet of r times the product of the base factors of the other indices](goal). -/
theorem leibnizTerm22_all_same (I : Finset ι) (J : FactorJets ι)
    (r : ι) (a u : ℝ) (hr : r ∈ I) :
    leibnizTerm I J [r, r] [r, r] a u =
      J.f22 r a u * ∏ i ∈ I.erase r, J.f00 i a u := by
  unfold leibnizTerm
  rw [← Finset.mul_prod_erase I _ hr]
  simp only [List.count_cons, List.count_nil, beq_self_eq_true, ite_true,
    factorJet]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hri : r ≠ i := (Finset.mem_erase.mp hi).1.symm
  simp [hri]

/-- [The explicit fourth mixed jet](hyp:I,J,a,u) [splits into terms whose
second-coordinate support is a singleton carrying the (2,2) factor jet,
and terms whose support is two distinct indices each carrying order one](goal).
The indices in the fourfold sum remain ordered, retaining every Leibniz multiplicity. -/
theorem productJet22_support_decomposition (I : Finset ι) (J : FactorJets ι)
    (a u : ℝ) :
    productJet22 I J a u =
      (∑ r ∈ I, J.f22 r a u * ∏ i ∈ I.erase r, J.f00 i a u) +
      ∑ p ∈ I, ∑ q ∈ I, ∑ r ∈ I, ∑ s ∈ I.erase r,
        leibnizTerm I J [p, q] [r, s] a u := by
  unfold productJet22
  calc
    _ = (∑ p ∈ I, ∑ q ∈ I, ∑ r ∈ I,
          leibnizTerm I J [p, q] [r, r] a u) +
        ∑ p ∈ I, ∑ q ∈ I, ∑ r ∈ I, ∑ s ∈ I.erase r,
          leibnizTerm I J [p, q] [r, s] a u := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro q hq
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro r hr
      exact (Finset.add_sum_erase I _ hr).symm
    _ = _ := by
      congr 1
      calc
        _ = ∑ r ∈ I, ∑ p ∈ I, ∑ q ∈ I,
            leibnizTerm I J [p, q] [r, r] a u := by
          calc
            _ = ∑ p ∈ I, ∑ r ∈ I, ∑ q ∈ I,
                leibnizTerm I J [p, q] [r, r] a u := by
              apply Finset.sum_congr rfl
              intro p hp
              rw [Finset.sum_comm]
            _ = _ := Finset.sum_comm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [Finset.sum_eq_single r]
          · rw [Finset.sum_eq_single r]
            · exact leibnizTerm22_all_same I J r a u hr
            · intro q hq hqr
              exact leibnizTerm22_repeated_u_zero I J r q r a u hr (Or.inr hqr)
            · exact fun h => (h hr).elim
          · intro p hp hpr
            apply Finset.sum_eq_zero
            intro q hq
            exact leibnizTerm22_repeated_u_zero I J p q r a u hr (Or.inl hpr)
          · exact fun h => (h hr).elim

/-- For [factor jets J of a finite index set I](hyp:I,J) at [a point (a, u)](hyp:a,u) and
[first-coordinate hits p and q](hyp:p,q), suppose [the second-coordinate hits r and s lie in
I](hyp:r,s,hr,hs), [every factor of I outside a set M has vanishing (0,1), (1,1), (2,1) and (2,2)
jets](hyp:M,hzero), and [r or s lies outside M](hyp:houtside). Then [the corresponding (2,2)
Leibniz summand is zero](goal). -/
theorem leibnizTerm22_vanishes_outside (I M : Finset ι) (J : FactorJets ι)
    (p q r s : ι) (a u : ℝ) (hr : r ∈ I) (hs : s ∈ I)
    (hzero : ∀ i ∈ I, i ∉ M →
      J.f01 i a u = 0 ∧ J.f11 i a u = 0 ∧
        J.f21 i a u = 0 ∧ J.f22 i a u = 0)
    (houtside : r ∉ M ∨ s ∉ M) :
    leibnizTerm I J [p, q] [r, s] a u = 0 := by
  obtain ⟨t, ht, htm, hhit⟩ :
      ∃ t ∈ I, t ∉ M ∧ (r = t ∨ s = t) := by
    rcases houtside with hrm | hsm
    · exact ⟨r, hr, hrm, Or.inl rfl⟩
    · exact ⟨s, hs, hsm, Or.inr rfl⟩
  obtain ⟨h01, h11, h21, h22⟩ := hzero t ht htm
  unfold leibnizTerm
  rw [← Finset.mul_prod_erase I _ ht]
  have hz : factorJet J t (([p, q] : List ι).count t)
      (([r, s] : List ι).count t) a u = 0 := by
    rcases hhit with hr | hs
    · subst r
      by_cases hp : p = t <;> by_cases hq : q = t <;>
        by_cases hs : s = t <;>
        simp [hp, hq, hs, factorJet, h01, h11, h21, h22]
    · subst s
      by_cases hp : p = t <;> by_cases hq : q = t <;>
        by_cases hr : r = t <;>
        simp [hp, hq, hr, factorJet, h01, h11, h21, h22]
  rw [hz, zero_mul]

end Causalean.Mathlib.Analysis.Calculus.FiniteProduct
