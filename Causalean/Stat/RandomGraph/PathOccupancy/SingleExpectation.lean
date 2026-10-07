module
public import Causalean.Stat.RandomGraph.PathOccupancy.ScoreMeasurability
public import Causalean.Stat.RandomGraph.PathOccupancy.SingleEvents
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Expected single-component score via labelled subsets

Pointwise domination by all connected labelled subsets, the fixed-subset
two-mark event bound, and cardinality grouping give a finite labelled occupancy
majorant. The random relation may depend on marks and extra randomness.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Causalean.Stat.RandomGraph.PathOccupancy

variable {Ω : Type*} [MeasurableSpace Ω]

/-- In [the iid uniform marked model](hyp:h), for [a measurable random
local subrelation](hyp:R,hR,hlocal), [the expected single score is at most
ε² K times the labelled-subset occupancy sum](goal), with [positive K](hyp:hK) and [coarse count M](hyp:M). The labelled-subset occupancy sum runs
over sizes m from two through n and adds choose(n, m) · m^10 · 8^m · m^m / K^m.

First apply the pointwise subset domination. Integrate the finite nonnegative
sum, group by cardinality using the cardinality of powersetCard, and apply the
fixed-subset event estimate. All random scores have finite range and are bounded.

Reusable Mathlib facts found this round: integral_indicator_const and
integral_finset_sum; Finset.sum_powerset_apply_card, Finset.sum_powerset, and
Finset.sum_powersetCard. Their pinned upstream sources were inspected.

Proof route: set E C to the conjunction of PathConnected and two marks. Its
indicator is measurable by composing a predicate on the finite pair of cell
and mark vectors with their measurable product. An integrable constant times
that indicator permits integral_mono with integrable_singleScore. Rewrite the
finite integrals as the constant weight times μ.real (E C), then apply
subset_connected_two_marks_le when 2 ≤ C.card. For smaller C, markCount ≤ C.card
makes the integrand zero. Group the cardinality-only bound with
sum_powerset_apply_card (or sum_powerset followed by sum_powersetCard), dropping
sizes zero and one and identifying range with Icc 2 n. Do not introduce
independence of the random relation or any extra measurable-event assumption.
-/
theorem single_expectation_labelled_le {n K : ℕ} {μ : Measure Ω}
    {X : Fin n → Ω → Fin K} {B : Fin n → Ω → Bool} {ε : ℝ}
    (h : UniformMarkedSample μ X B ε) (M : ℕ) (hK : 0 < K)
    (R : Ω → Fin n → Fin n → Prop)
    (hR : ∀ i j, MeasurableSet {ω | R ω i j})
    (hlocal : ∀ ω, Admissible M (fun i => X i ω) (R ω)) :
    (∫ ω, singleScore (R ω) (fun i => B i ω) ∂μ) ≤
      ε ^ 2 * K * ∑ m ∈ Finset.Icc 2 n,
        (n.choose m : ℝ) * (m : ℝ) ^ 10 * 8 ^ m * (m : ℝ) ^ m / (K : ℝ) ^ m := by
  classical
  let : IsProbabilityMeasure μ := h.probability
  let E : Finset (Fin n) → Set Ω := fun C =>
    {ω | PathConnected (C.image (fun i => X i ω)) ∧
      2 ≤ markCount C (fun i => B i ω)}
  let w : ℕ → ℝ := fun m => (m : ℝ) ^ 8 * 8 ^ m
  let f : Finset (Fin n) → Ω → ℝ := fun C => (E C).indicator (fun _ => w C.card)
  let g : ℕ → ℝ := fun m => if 2 ≤ m then
    ε ^ 2 * K * (m : ℝ) ^ 10 * 8 ^ m * (m : ℝ) ^ m / (K : ℝ) ^ m else 0
  have hinput : Measurable (fun ω => (fun i => X i ω, fun i => B i ω)) :=
    (measurable_pi_lambda _ h.cells_measurable).prodMk
      (measurable_pi_lambda _ h.marks_measurable)
  have hE (C : Finset (Fin n)) : MeasurableSet (E C) := by
    exact hinput (Set.toFinite
      {p : (Fin n → Fin K) × (Fin n → Bool) |
        PathConnected (C.image p.1) ∧ 2 ≤ markCount C p.2}).measurableSet
  have hf (C : Finset (Fin n)) : Integrable (f C) μ :=
    (integrable_const (w C.card)).indicator (hE C)
  have hpoint (ω : Ω) :
      singleScore (R ω) (fun i => B i ω) ≤ ∑ C ∈ Finset.univ.powerset, f C ω := by
    convert singleScore_le_subsets M (fun i => X i ω) (R ω)
      (fun i => B i ω) (hlocal ω) using 1
    apply Finset.sum_congr rfl
    intro C _
    simp only [f, E, Set.indicator, Set.mem_ofPred_eq, singleWeight, w]
    split_ifs <;> simp_all
  have hbound (C : Finset (Fin n)) : (∫ ω, f C ω ∂μ) ≤ g C.card := by
    by_cases hC : 2 ≤ C.card
    · rw [show (∫ ω, f C ω ∂μ) = μ.real (E C) * w C.card by
        exact (integral_indicator_const _ (hE C)).trans (by simp [smul_eq_mul])]
      have hp := mul_le_mul_of_nonneg_right
        (subset_connected_two_marks_le h hK C hC) (show 0 ≤ w C.card by dsimp [w]; positivity)
      calc
        _ ≤ (ε ^ 2 * K * (C.card : ℝ) ^ (C.card + 2) /
            (K : ℝ) ^ C.card) * w C.card := hp
        _ = g C.card := by
          simp only [g, if_pos hC, w, pow_add]
          ring
    · have hempty : E C = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro ω hω
        have hc : markCount C (fun i => B i ω) ≤ C.card := Finset.card_filter_le _ _
        exact hC (le_trans hω.2 hc)
      simp [f, hempty, g, hC]
  calc
    _ ≤ ∫ ω, ∑ C ∈ Finset.univ.powerset, f C ω ∂μ :=
      integral_mono (integrable_singleScore μ R B hR h.marks_measurable)
        (integrable_finsetSum _ (fun C _ => hf C)) hpoint
    _ = ∑ C ∈ Finset.univ.powerset, ∫ ω, f C ω ∂μ :=
      integral_finsetSum _ (fun C _ => hf C)
    _ ≤ ∑ C ∈ Finset.univ.powerset, g C.card :=
      Finset.sum_le_sum (fun C _ => hbound C)
    _ = ∑ m ∈ Finset.range (n + 1), (n.choose m : ℝ) * g m := by
      rw [Finset.sum_powerset_apply_card]
      simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = ∑ m ∈ Finset.Icc 2 n, (n.choose m : ℝ) * g m := by
      symm
      apply Finset.sum_subset
      · intro m hm
        simp only [Finset.mem_Icc] at hm
        simp only [Finset.mem_range]
        omega
      · intro m _ hm
        have hsmall : ¬ 2 ≤ m := by
          simp only [Finset.mem_Icc, not_and_or, not_le] at hm
          simp only [Finset.mem_range] at *
          omega
        simp [g, hsmall]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      simp only [g, if_pos (Finset.mem_Icc.mp hm).1]
      ring

end Causalean.Stat.RandomGraph.PathOccupancy
