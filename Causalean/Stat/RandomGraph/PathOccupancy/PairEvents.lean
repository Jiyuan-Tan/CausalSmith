module
public import Causalean.Stat.RandomGraph.PathOccupancy.Components
public import Causalean.Stat.RandomGraph.PathOccupancy.Counting

/-!
# Connected marked pair events on disjoint labelled subsets

This layer combines exact uniform assignment probabilities and independent
Bernoulli marks with connected-run pair counting. Disjointness concerns sample
labels; the occupied fine cells and run anchors may coincide.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Causalean.Stat.RandomGraph.PathOccupancy

variable {Ω : Type*} [MeasurableSpace Ω]

/-- In [the uniform marked model](hyp:h) with [a coarse cell count](hyp:M) that is [positive, even,
and divides the positive fine cell count](hyp:hM,hK,heven,hdiv), [two disjoint label subsets of
size at least two](hyp:C,D,hdisj,hC,hD) satisfy the following: [the probability that each subset
occupies a path-connected set of cells, each carries at least one mark, and the two share a coarse
pair is at most 2 ε² K² / M times |C| to the power |C| + 1 times |D| to the power |D| + 1, divided
by K to the power |C| + |D|](goal).

Use connected_same_pair_assignment_count on C and D. Equal occupied anchors
must be retained even though the label subsets are disjoint.

Proof route: take the finite subtype of assignment pairs satisfying both
ConnectedAssignment predicates and SamePair. Lift a realized event into that
subtype using the univ-image/subset-image identity from SingleEvents. Union its
assignment-and-mark events and apply assignment_pair_marks_probability_le to
each member. Cast connected_same_pair_assignment_count to reals and divide by
positive M. The resulting constant sum is the cardinality times the uniform
Bernoulli bound; pow_add and ring give the displayed expression. SamePair on
the subtype is exactly SameCoarsePair after moving subtype quantifiers to
membership quantifiers. Do not require distinct occupied anchors.
-/
theorem subsets_connected_pair_marks_le {n K : ℕ} {μ : Measure Ω}
    {X : Fin n → Ω → Fin K} {B : Fin n → Ω → Bool} {ε : ℝ}
    (h : UniformMarkedSample μ X B ε) (M : ℕ)
    (hM : 0 < M) (hK : 0 < K) (heven : 2 ∣ M) (hdiv : M ∣ K)
    (C D : Finset (Fin n)) (hdisj : Disjoint C D)
    (hC : 2 ≤ C.card) (hD : 2 ≤ D.card) :
    (μ {ω | PathConnected (C.image (fun i => X i ω)) ∧
      PathConnected (D.image (fun i => X i ω)) ∧
      1 ≤ markCount C (fun i => B i ω) ∧
      1 ≤ markCount D (fun i => B i ω) ∧
      SameCoarsePair M C D (fun i => X i ω)}).toReal ≤
      2 * ε ^ 2 * (K : ℝ) ^ 2 / M *
        (C.card : ℝ) ^ (C.card + 1) * (D.card : ℝ) ^ (D.card + 1) /
        (K : ℝ) ^ (C.card + D.card) := by
  classical
  have : IsProbabilityMeasure μ := h.probability
  let A := {p : (C → Fin K) × (D → Fin K) //
    ConnectedAssignment p.1 ∧ ConnectedAssignment p.2 ∧ SamePair K M p.1 p.2}
  let E : A → Set Ω := fun a =>
    {ω | (∀ i : C, X i ω = a.val.1 i) ∧
      (∀ i : D, X i ω = a.val.2 i) ∧
      1 ≤ markCount C (fun i => B i ω) ∧
      1 ≤ markCount D (fun i => B i ω)}
  have himage (S : Finset (Fin n)) (ω : Ω) :
      Finset.univ.image (fun i : S => X i ω) = S.image (fun i => X i ω) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, i.property, hi⟩
    · rintro ⟨i, hi, hix⟩
      exact ⟨⟨i, hi⟩, hix⟩
  have hsub : {ω | PathConnected (C.image (fun i => X i ω)) ∧
      PathConnected (D.image (fun i => X i ω)) ∧
      1 ≤ markCount C (fun i => B i ω) ∧
      1 ≤ markCount D (fun i => B i ω) ∧
      SameCoarsePair M C D (fun i => X i ω)} ⊆ ⋃ a, E a := by
    rintro ω ⟨hc, hd, hmc, hmd, hp⟩
    have hac : ConnectedAssignment (fun i : C => X i ω) := by
      simpa only [ConnectedAssignment, himage] using hc
    have had : ConnectedAssignment (fun i : D => X i ω) := by
      simpa only [ConnectedAssignment, himage] using hd
    obtain ⟨p, hpm, hpc, hpd⟩ := hp
    have hap : SamePair K M (fun i : C => X i ω) (fun i : D => X i ω) :=
      ⟨p, hpm, (fun i => hpc i i.property), (fun i => hpd i i.property)⟩
    exact Set.mem_iUnion.mpr
      ⟨⟨((fun i : C => X i ω), (fun i : D => X i ω)), hac, had, hap⟩,
        (fun _ => rfl), (fun _ => rfl), hmc, hmd⟩
  have hbound (a : A) : μ.real (E a) ≤
      ε ^ 2 * (C.card : ℝ) * (D.card : ℝ) / (K : ℝ) ^ (C.card + D.card) :=
    assignment_pair_marks_probability_le h C D hdisj a.val.1 a.val.2
  have hcard : (Fintype.card A : ℝ) ≤
      2 * (K : ℝ) ^ 2 * (C.card : ℝ) ^ C.card * (D.card : ℝ) ^ D.card / M := by
    have hc := connected_same_pair_assignment_count (ι := C) (κ := D) K M
      (by simpa only [Fintype.card_coe] using (show 1 ≤ C.card by omega))
      (by simpa only [Fintype.card_coe] using (show 1 ≤ D.card by omega))
      hM hK heven hdiv
    have hc' : M * Fintype.card A ≤
        2 * K ^ 2 * C.card ^ C.card * D.card ^ D.card := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hc
    apply (le_div_iff₀ (Nat.cast_pos.mpr hM)).mpr
    have hc'' : (M : ℝ) * (Fintype.card A : ℝ) ≤
        2 * (K : ℝ) ^ 2 * (C.card : ℝ) ^ C.card * (D.card : ℝ) ^ D.card := by
      exact_mod_cast hc'
    simpa only [mul_comm] using hc''
  have hnonneg : 0 ≤
      ε ^ 2 * (C.card : ℝ) * (D.card : ℝ) / (K : ℝ) ^ (C.card + D.card) := by
    positivity
  calc
    _ ≤ μ.real (⋃ a, E a) := measureReal_mono hsub
    _ ≤ ∑ a : A, μ.real (E a) := measureReal_iUnion_fintype_le E
    _ ≤ ∑ _a : A,
        ε ^ 2 * (C.card : ℝ) * (D.card : ℝ) / (K : ℝ) ^ (C.card + D.card) :=
      Finset.sum_le_sum (fun a _ => hbound a)
    _ = (Fintype.card A : ℝ) *
        (ε ^ 2 * (C.card : ℝ) * (D.card : ℝ) / (K : ℝ) ^ (C.card + D.card)) := by
      simp
    _ ≤ (2 * (K : ℝ) ^ 2 * (C.card : ℝ) ^ C.card * (D.card : ℝ) ^ D.card / M) *
        (ε ^ 2 * (C.card : ℝ) * (D.card : ℝ) / (K : ℝ) ^ (C.card + D.card)) :=
      mul_le_mul_of_nonneg_right hcard hnonneg
    _ = _ := by simp only [pow_add, pow_one]; ring

end Causalean.Stat.RandomGraph.PathOccupancy
