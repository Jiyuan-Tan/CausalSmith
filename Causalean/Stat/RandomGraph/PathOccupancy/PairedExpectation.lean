module
public import Causalean.Stat.RandomGraph.PathOccupancy.PairEvents
public import Causalean.Stat.RandomGraph.PathOccupancy.ScoreMeasurability
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Expected paired-component score via labelled subsets

The marked disjoint-subset event bound and pointwise component domination yield
an expected paired score bounded by a square of a finite labelled-subset sum.
Only deterministic sums are factorized; random components need not be independent.
Both component cardinality cutoffs remain at two, and occupied cells may coincide.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Causalean.Stat.RandomGraph.PathOccupancy

variable {Ω : Type*} [MeasurableSpace Ω]

/-- In [the iid uniform marked model](hyp:h), for [a measurable local
subrelation](hyp:R,hR,hlocal), [the expected distinct-component score is bounded
by twice ε² K²/M times the square of the labelled-subset sum](goal), under
[positive even coarse count and divisibility](hyp:hM,hK,heven,hdiv).
The labelled-subset sum runs over sizes m from two through n and adds
choose(n, m) · m^5 · 8^m · m^m / K^m.

The half ordered component sum allows a sharper factor, but discarding that
half yields the requested convenient constant. Count disjoint labelled subsets
by choose(n,m) choose(n-m,l), then bound by choose(n,m) choose(n,l).

Proof route (all probability/counting prerequisites are closed): let q(m)
be zero for m < 2 and m^5 * 8^m * m^m / K^m otherwise. Let E(C,D)
be the event in subsets_connected_pair_marks_le, and integrate its constant
indicator only when Disjoint C D and both sizes are at least two. All other
pairWeight summands are zero. Event measurability follows from the finite
cell/mark vector, exactly as in SingleExpectation; use h.probability to supply
IsProbabilityMeasure and integrability of constants. integral_indicator_const
and twice integral_finsetSum reduce the expected subset sum to finite event
probabilities. The event estimate times the fourth-power weights is
(2 * ε^2 * K^2 / M) * q(C.card) * q(D.card), by pow_add and ring.
For non-disjoint labels the summand is zero; dominate it by that nonnegative
product without applying the disjoint-subset event estimate. After this bound,
discard the factor one half using nonnegativity. Finset.sum_mul_sum factorizes
the full ordered powerset sum. Finset.sum_powerset_apply_card groups q by
cardinality, and Finset.sum_subset removes sizes zero and one, as in the proven
single expectation proof. This avoids counting disjoint subsets explicitly.
Never factor random events or assume independence of components.

Mathlib primary sources fetched at pinned revision
 db584cd6d46c92f209a44c0f1c829460d327499d:
Data/Nat/Choose/Sum.lean (sum_powerset_apply_card),
MeasureTheory/Integral/Bochner/Set.lean (integral_indicator_const), and
Algebra/BigOperators/Ring/Finset.lean (sum_mul_sum).
-/
theorem paired_expectation_labelled_le {n K : ℕ} {μ : Measure Ω}
    {X : Fin n → Ω → Fin K} {B : Fin n → Ω → Bool} {ε : ℝ}
    (h : UniformMarkedSample μ X B ε) (M : ℕ)
    (hM : 0 < M) (hK : 0 < K) (heven : 2 ∣ M) (hdiv : M ∣ K)
    (R : Ω → Fin n → Fin n → Prop)
    (hR : ∀ i j, MeasurableSet {ω | R ω i j})
    (hlocal : ∀ ω, Admissible M (fun i => X i ω) (R ω)) :
    (∫ ω, pairedScore M (R ω) (fun i => X i ω) (fun i => B i ω) ∂μ) ≤
      2 * ε ^ 2 * (K : ℝ) ^ 2 / M *
        (∑ m ∈ Finset.Icc 2 n,
          (n.choose m : ℝ) * (m : ℝ) ^ 5 * 8 ^ m * (m : ℝ) ^ m / (K : ℝ) ^ m) ^ 2 := by
  classical
  let : IsProbabilityMeasure μ := h.probability
  let E : Finset (Fin n) → Finset (Fin n) → Set Ω := fun C D =>
    {ω | PathConnected (C.image (fun i => X i ω)) ∧
      PathConnected (D.image (fun i => X i ω)) ∧
      1 ≤ markCount C (fun i => B i ω) ∧
      1 ≤ markCount D (fun i => B i ω) ∧
      SameCoarsePair M C D (fun i => X i ω)}
  let w : ℕ → ℝ := fun m => (m : ℝ) ^ 4 * 8 ^ m
  let q : ℕ → ℝ := fun m => if 2 ≤ m then
    (m : ℝ) ^ 5 * 8 ^ m * (m : ℝ) ^ m / (K : ℝ) ^ m else 0
  let a : ℝ := 2 * ε ^ 2 * (K : ℝ) ^ 2 / M
  let f : Finset (Fin n) → Finset (Fin n) → Ω → ℝ := fun C D =>
    if Disjoint C D ∧ 2 ≤ C.card ∧ 2 ≤ D.card then
      (E C D).indicator (fun _ => w C.card * w D.card) else fun _ => 0
  have hinput : Measurable (fun ω => (fun i => X i ω, fun i => B i ω)) :=
    (measurable_pi_lambda _ h.cells_measurable).prodMk
      (measurable_pi_lambda _ h.marks_measurable)
  have hE (C D : Finset (Fin n)) : MeasurableSet (E C D) := by
    exact hinput (Set.toFinite
      {p : (Fin n → Fin K) × (Fin n → Bool) |
        PathConnected (C.image p.1) ∧ PathConnected (D.image p.1) ∧
        1 ≤ markCount C p.2 ∧ 1 ≤ markCount D p.2 ∧
        SameCoarsePair M C D p.1}).measurableSet
  have hf (C D : Finset (Fin n)) : Integrable (f C D) μ := by
    dsimp [f]
    split_ifs
    · exact (integrable_const _).indicator (hE C D)
    · exact integrable_const 0
  have hq (m : ℕ) : 0 ≤ q m := by dsimp [q]; split_ifs <;> positivity
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hpoint (ω : Ω) : pairedScore M (R ω) (fun i => X i ω)
      (fun i => B i ω) ≤ (1 / 2 : ℝ) *
      ∑ C ∈ (Finset.univ : Finset (Fin n)).powerset,
        ∑ D ∈ (Finset.univ : Finset (Fin n)).powerset, f C D ω := by
    convert pairedScore_le_subsets M (fun i => X i ω) (R ω)
      (fun i => B i ω) (hlocal ω) using 1
    congr 1
    apply Finset.sum_congr rfl
    intro C _
    apply Finset.sum_congr rfl
    intro D _
    simp only [f, E, pairWeight, w]
    split_ifs <;> simp_all
    ring
  have hbound (C D : Finset (Fin n)) :
      (∫ ω, f C D ω ∂μ) ≤ a * q C.card * q D.card := by
    by_cases hc : Disjoint C D ∧ 2 ≤ C.card ∧ 2 ≤ D.card
    · rw [show (∫ ω, f C D ω ∂μ) = μ.real (E C D) *
          (w C.card * w D.card) by
        simp only [f, if_pos hc]
        exact (integral_indicator_const _ (hE C D)).trans (by simp [smul_eq_mul])]
      have hp := mul_le_mul_of_nonneg_right
        (subsets_connected_pair_marks_le h M hM hK heven hdiv C D hc.1 hc.2.1 hc.2.2)
        (show 0 ≤ w C.card * w D.card by dsimp [w]; positivity)
      calc
        _ ≤ (a * (C.card : ℝ) ^ (C.card + 1) *
            (D.card : ℝ) ^ (D.card + 1) / (K : ℝ) ^ (C.card + D.card)) *
            (w C.card * w D.card) := hp
        _ = _ := by
          simp only [q, if_pos hc.2.1, if_pos hc.2.2, w, pow_add, pow_one]
          ring
    · simp only [f, if_neg hc, integral_zero]
      exact mul_nonneg (mul_nonneg ha (hq _)) (hq _)
  have hgroup : (∑ C ∈ (Finset.univ : Finset (Fin n)).powerset, q C.card) =
      ∑ m ∈ Finset.Icc 2 n,
        (n.choose m : ℝ) * (m : ℝ) ^ 5 * 8 ^ m * (m : ℝ) ^ m / (K : ℝ) ^ m := by
    calc
      _ = ∑ m ∈ Finset.range (n + 1), (n.choose m : ℝ) * q m := by
        rw [Finset.sum_powerset_apply_card]
        simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = ∑ m ∈ Finset.Icc 2 n, (n.choose m : ℝ) * q m := by
        symm
        apply Finset.sum_subset
        · intro m hm
          simp only [Finset.mem_Icc] at hm
          simp only [Finset.mem_range]
          omega
        · intro m hm hnot
          have hsmall : ¬ 2 ≤ m := by
            simp only [Finset.mem_Icc, not_and_or, not_le] at hnot
            simp only [Finset.mem_range] at hm
            omega
          simp [q, hsmall]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro m hm
        simp only [q, if_pos (Finset.mem_Icc.mp hm).1]
        ring
  have hsum : Integrable (fun ω =>
      ∑ C ∈ (Finset.univ : Finset (Fin n)).powerset,
        ∑ D ∈ (Finset.univ : Finset (Fin n)).powerset, f C D ω) μ :=
    integrable_finsetSum _ (fun C _ => integrable_finsetSum _ (fun D _ => hf C D))
  calc
    _ ≤ ∫ ω, (1 / 2 : ℝ) *
        (∑ C ∈ (Finset.univ : Finset (Fin n)).powerset,
        ∑ D ∈ (Finset.univ : Finset (Fin n)).powerset, f C D ω) ∂μ :=
      integral_mono (integrable_pairedScore μ M R X B hR
        h.cells_measurable h.marks_measurable) (hsum.const_mul _) hpoint
    _ = (1 / 2 : ℝ) *
        ∑ C ∈ (Finset.univ : Finset (Fin n)).powerset,
        ∑ D ∈ (Finset.univ : Finset (Fin n)).powerset,
          ∫ ω, f C D ω ∂μ := by
      rw [integral_const_mul, integral_finsetSum _
        (fun C _ => integrable_finsetSum _ (fun D _ => hf C D))]
      congr 1
      apply Finset.sum_congr rfl
      intro C _
      exact integral_finsetSum _ (fun D _ => hf C D)
    _ ≤ (1 / 2 : ℝ) *
        ∑ C ∈ (Finset.univ : Finset (Fin n)).powerset,
        ∑ D ∈ (Finset.univ : Finset (Fin n)).powerset,
          a * q C.card * q D.card := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun C _ => Finset.sum_le_sum (fun D _ => hbound C D)))
        (by norm_num : (0 : ℝ) ≤ 1 / 2)
    _ ≤ ∑ C ∈ (Finset.univ : Finset (Fin n)).powerset,
        ∑ D ∈ (Finset.univ : Finset (Fin n)).powerset,
          a * q C.card * q D.card := by
      have hs : 0 ≤ ∑ C ∈ (Finset.univ : Finset (Fin n)).powerset,
          ∑ D ∈ (Finset.univ : Finset (Fin n)).powerset, a * q C.card * q D.card :=
        Finset.sum_nonneg (fun C _ => Finset.sum_nonneg
          (fun D _ => mul_nonneg (mul_nonneg ha (hq _)) (hq _)))
      exact mul_le_of_le_one_left hs (by norm_num)
    _ = a * (∑ C ∈ (Finset.univ : Finset (Fin n)).powerset, q C.card) ^ 2 := by
      rw [pow_two, Finset.sum_mul_sum]
      simp only [Finset.mul_sum, mul_assoc]
    _ = _ := by rw [hgroup]

end Causalean.Stat.RandomGraph.PathOccupancy
