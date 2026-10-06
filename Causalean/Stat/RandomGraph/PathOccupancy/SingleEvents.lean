module
public import Causalean.Stat.RandomGraph.PathOccupancy.ConnectedAssignments
public import Causalean.Stat.RandomGraph.PathOccupancy.Probability

/-!
# Connected two-mark events on a fixed labelled subset

The single-subset union bound combines the exact uniform assignment law, the
quadratic Bernoulli mark bound, and the connected-run assignment count. This
layer does not depend on paired counting or random component measurability.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Causalean.Stat.RandomGraph.PathOccupancy

variable {Ω : Type*} [MeasurableSpace Ω]

/-- In [the iid uniform marked model](hyp:h), [a fixed subset of size at
least two](hyp:C,hC) has [connected occupied cells and two marks with probability
bounded by K times m^m times the quadratic mark factor over K^m](goal),
with [positive cell count](hyp:hK).

Union over assignments to the subtype C, use connected_assignment_count, and
apply assignment_two_marks_probability_le to each assignment.
-/
theorem subset_connected_two_marks_le {n K : ℕ} {μ : Measure Ω}
    {X : Fin n → Ω → Fin K} {B : Fin n → Ω → Bool} {ε : ℝ}
    (h : UniformMarkedSample μ X B ε) (hK : 0 < K)
    (C : Finset (Fin n)) (hC : 2 ≤ C.card) :
    (μ {ω | PathConnected (C.image (fun i => X i ω)) ∧
      2 ≤ markCount C (fun i => B i ω)}).toReal ≤
      ε ^ 2 * K * (C.card : ℝ) ^ (C.card + 2) / (K : ℝ) ^ C.card := by
  classical
  have : IsProbabilityMeasure μ := h.probability
  let A := {a : C → Fin K // ConnectedAssignment a}
  let E : A → Set Ω := fun a =>
    {ω | (∀ i : C, X i ω = a.val i) ∧
      2 ≤ markCount C (fun i => B i ω)}
  have himage (ω : Ω) :
      Finset.univ.image (fun i : C => X i ω) = C.image (fun i => X i ω) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, i.property, hi⟩
    · rintro ⟨i, hi, hix⟩
      exact ⟨⟨i, hi⟩, hix⟩
  have hsub : {ω | PathConnected (C.image (fun i => X i ω)) ∧
      2 ≤ markCount C (fun i => B i ω)} ⊆ ⋃ a, E a := by
    rintro ω ⟨hc, hm⟩
    have ha : ConnectedAssignment (fun i : C => X i ω) := by
      simpa only [ConnectedAssignment, himage] using hc
    exact Set.mem_iUnion.mpr ⟨⟨(fun i : C => X i ω), ha⟩,
      (fun _ => rfl), hm⟩
  have hbound (a : A) :
      μ.real (E a) ≤ ε ^ 2 * (C.card : ℝ) ^ 2 / (K : ℝ) ^ C.card :=
    assignment_two_marks_probability_le h C a.val
  have hcard : (Fintype.card A : ℝ) ≤ (K : ℝ) * (C.card : ℝ) ^ C.card := by
    have hc := connected_assignment_count (ι := C) K (by
      simpa only [Fintype.card_coe] using (show 1 ≤ C.card by omega))
    have hc' : Fintype.card A ≤ K * C.card ^ C.card := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hc
    exact_mod_cast hc'
  have hnonneg : 0 ≤ ε ^ 2 * (C.card : ℝ) ^ 2 / (K : ℝ) ^ C.card :=
    div_nonneg (mul_nonneg (sq_nonneg ε) (sq_nonneg _))
      (pow_nonneg (le_of_lt (Nat.cast_pos.mpr hK)) _)
  calc
    _ ≤ μ.real (⋃ a, E a) := measureReal_mono hsub
    _ ≤ ∑ a : A, μ.real (E a) := measureReal_iUnion_fintype_le E
    _ ≤ ∑ _a : A, ε ^ 2 * (C.card : ℝ) ^ 2 / (K : ℝ) ^ C.card :=
      Finset.sum_le_sum (fun a _ => hbound a)
    _ = (Fintype.card A : ℝ) *
        (ε ^ 2 * (C.card : ℝ) ^ 2 / (K : ℝ) ^ C.card) := by simp
    _ ≤ ((K : ℝ) * (C.card : ℝ) ^ C.card) *
        (ε ^ 2 * (C.card : ℝ) ^ 2 / (K : ℝ) ^ C.card) :=
      mul_le_mul_of_nonneg_right hcard hnonneg
    _ = _ := by rw [pow_add]; ring

end Causalean.Stat.RandomGraph.PathOccupancy
