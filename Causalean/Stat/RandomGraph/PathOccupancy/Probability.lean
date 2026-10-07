module
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.Independence.Basic

/-!
# Fixed labelled subset probabilities for uniform samples and independent marks

The model specifies exact uniform singleton masses on the finite path, exact
Bernoulli marginals, independence within each family, and independence of the
two complete vectors. Thus it is a genuine iid uniform model, with no upper-mass
surrogate. All event bounds are derived, rather than assumed in the model.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Causalean.Stat.RandomGraph.PathOccupancy

variable {Ω : Type*} [MeasurableSpace Ω]

/-- [The sample measure](hyp:μ), [cell variables](hyp:X), [mark variables](hyp:B),
and [success probability](hyp:ε) specify an iid uniform marked sample through
[probability-law normalization](hyp:probability), [a valid mark probability]
(hyp:epsilon_nonneg,epsilon_le_one), [measurable cells and marks]
(hyp:cells_measurable,marks_measurable), [uniform cell and Bernoulli mark
marginals](hyp:cells_uniform,marks_bernoulli), [within-family independence]
(hyp:cells_independent,marks_independent), and [independence of the two complete
vectors](hyp:blocks_independent). -/
structure UniformMarkedSample {n K : ℕ} (μ : Measure Ω)
    (X : Fin n → Ω → Fin K) (B : Fin n → Ω → Bool) (ε : ℝ) : Prop where
  probability : IsProbabilityMeasure μ
  epsilon_nonneg : 0 ≤ ε
  epsilon_le_one : ε ≤ 1
  cells_measurable : ∀ i, Measurable (X i)
  marks_measurable : ∀ i, Measurable (B i)
  cells_uniform : ∀ i a, μ {ω | X i ω = a} = (K : ℝ≥0∞)⁻¹
  marks_bernoulli : ∀ i b, μ {ω | B i ω = b} =
    ENNReal.ofReal (if b = true then ε else 1 - ε)
  cells_independent : iIndepFun X μ
  marks_independent : iIndepFun B μ
  blocks_independent : IndepFun (fun ω i => X i ω) (fun ω i => B i ω) μ

/-- [The marked cardinality](goal) of [a labelled subset](hyp:s) under
[a Boolean marking](hyp:b) is its number of true marks. -/
noncomputable def markCount {n : ℕ} (s : Finset (Fin n)) (b : Fin n → Bool) : ℕ :=
  (s.filter (fun i => b i = true)).card

/-- In [the uniform marked model](hyp:h), [any specified assignments on a
fixed labelled subset](hyp:s,a) have [exact reciprocal-power probability](goal).

Use iIndepFun.measure_inter_preimage_eq_mul with singleton targets, then the
constant-product identity. No constraint is imposed on unsampled labels.
-/
theorem fixed_subset_assignment_probability {n K : ℕ} {μ : Measure Ω}
    {X : Fin n → Ω → Fin K} {B : Fin n → Ω → Bool} {ε : ℝ}
    (h : UniformMarkedSample μ X B ε) (s : Finset (Fin n)) (a : s → Fin K) :
    μ {ω | ∀ i : s, X i ω = a i} = (K : ℝ≥0∞)⁻¹ ^ s.card := by
  classical
  have hi := h.cells_independent.precomp (g := fun i : s => (i : Fin n))
    Subtype.val_injective
  have hp := hi.measure_inter_preimage_eq_mul Finset.univ
    (sets := fun i => {a i}) (fun _ _ => MeasurableSet.singleton _)
  have he : (⋂ i ∈ (Finset.univ : Finset s), X (i : Fin n) ⁻¹' {a i}) =
      {ω | ∀ i : s, X i ω = a i} := by ext ω; simp
  rw [he] at hp
  simp only [Set.preimage, Set.mem_singleton_iff] at hp
  simpa only [h.cells_uniform, Finset.prod_const, Finset.card_univ,
    Fintype.card_coe] using hp

/-- In [the uniform marked model](hyp:h), [cell assignments on a fixed
subset](hyp:s,a) and [mark assignments on any fixed subset](hyp:t,b) hold
jointly with [probability exactly 1/K to the power of the size of the first subset,
times the product over the second subset of ε for each label prescribed a true
mark and 1 − ε for each label prescribed a false mark](goal).
The two subsets may overlap or be different.
-/
theorem fixed_subset_assignment_mark_probability {n K : ℕ} {μ : Measure Ω}
    {X : Fin n → Ω → Fin K} {B : Fin n → Ω → Bool} {ε : ℝ}
    (h : UniformMarkedSample μ X B ε)
    (s t : Finset (Fin n)) (a : s → Fin K) (b : t → Bool) :
    μ {ω | (∀ i : s, X i ω = a i) ∧ (∀ i : t, B i ω = b i)} =
      (K : ℝ≥0∞)⁻¹ ^ s.card *
        ∏ i : t, ENNReal.ofReal (if b i = true then ε else 1 - ε) := by
  classical
  have hi := h.marks_independent.precomp (g := fun i : t => (i : Fin n))
    Subtype.val_injective
  have hp := hi.measure_inter_preimage_eq_mul Finset.univ
    (sets := fun i => {b i}) (fun _ _ => MeasurableSet.singleton _)
  have hm : μ {ω | ∀ i : t, B i ω = b i} =
      ∏ i : t, ENNReal.ofReal (if b i = true then ε else 1 - ε) := by
    have he : (⋂ i ∈ (Finset.univ : Finset t), B (i : Fin n) ⁻¹' {b i}) =
        {ω | ∀ i : t, B i ω = b i} := by ext ω; simp
    rw [he] at hp
    simp only [Set.preimage, Set.mem_singleton_iff] at hp
    exact hp.trans (Finset.prod_congr rfl (fun i _ => h.marks_bernoulli i (b i)))
  have hb := h.blocks_independent.measure_inter_preimage_eq_mul
    {x | ∀ i : s, x i = a i} {y | ∀ i : t, y i = b i}
    (by simpa only [Set.preimage, Set.mem_singleton_iff, Set.iInter_ofPred] using
      (MeasurableSet.iInter fun i : s =>
        (measurable_pi_apply (i : Fin n) :
          Measurable (fun x : Fin n → Fin K => x i)) (MeasurableSet.singleton (a i))))
    (by simpa only [Set.preimage, Set.mem_singleton_iff, Set.iInter_ofPred] using
      (MeasurableSet.iInter fun i : t =>
        (measurable_pi_apply (i : Fin n) :
          Measurable (fun x : Fin n → Bool => x i)) (MeasurableSet.singleton (b i))))
  change μ {ω | (∀ i : s, X i ω = a i) ∧ (∀ i : t, B i ω = b i)} = _ at hb
  rw [hb]
  change μ {ω | ∀ i : s, X i ω = a i} * μ {ω | ∀ i : t, B i ω = b i} = _
  rw [fixed_subset_assignment_probability h, hm]

/-- [A fixed cell assignment](hyp:s,a) and [two distinct successful marks](hyp:i,j,hij)
under [the uniform marked model](hyp:h) have [the exact product probability](goal). -/
theorem assignment_two_specified_marks_probability {n K : ℕ} {μ : Measure Ω}
    {X : Fin n → Ω → Fin K} {B : Fin n → Ω → Bool} {ε : ℝ}
    (h : UniformMarkedSample μ X B ε) (s : Finset (Fin n)) (a : s → Fin K)
    (i j : Fin n) (hij : i ≠ j) :
    (μ {ω | (∀ k : s, X k ω = a k) ∧ B i ω = true ∧ B j ω = true}).toReal =
      ε ^ 2 / (K : ℝ) ^ s.card := by
  classical
  have hp := fixed_subset_assignment_mark_probability h s {i, j} a (fun _ => true)
  have he : {ω | (∀ k : s, X k ω = a k) ∧
      ∀ k : (↑({i, j} : Finset (Fin n))), B k ω = true} =
      {ω | (∀ k : s, X k ω = a k) ∧ B i ω = true ∧ B j ω = true} := by
    ext ω
    simp
  rw [he] at hp
  simp only [ite_true, Finset.prod_const, Finset.card_univ, Fintype.card_coe,
    Finset.card_pair hij] at hp
  rw [hp]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, ENNReal.toReal_ofReal h.epsilon_nonneg]
  simp [div_eq_mul_inv, mul_comm]

/-- In [the independent uniform model](hyp:h), [a fixed assignment](hyp:s,a)
with [at least two marks](goal) has probability at most the reciprocal-power
cell probability times the quadratic Bernoulli union factor.

Union over pairs of distinct marked labels. The deliberately looser s.card²
factor is convenient for subsequent weighted occupancy bounds.
-/
theorem assignment_two_marks_probability_le {n K : ℕ} {μ : Measure Ω}
    {X : Fin n → Ω → Fin K} {B : Fin n → Ω → Bool} {ε : ℝ}
    (h : UniformMarkedSample μ X B ε) (s : Finset (Fin n)) (a : s → Fin K) :
    (μ {ω | (∀ i : s, X i ω = a i) ∧
      2 ≤ markCount s (fun i => B i ω)}).toReal ≤
      ε ^ 2 * (s.card : ℝ) ^ 2 / (K : ℝ) ^ s.card := by
  classical
  have : IsProbabilityMeasure μ := h.probability
  let E : s × s → Set Ω := fun p =>
    if (p.1 : Fin n) = p.2 then ∅ else
      {ω | (∀ i : s, X i ω = a i) ∧ B p.1 ω = true ∧ B p.2 ω = true}
  have hsub : {ω | (∀ i : s, X i ω = a i) ∧
      2 ≤ markCount s (fun i => B i ω)} ⊆ ⋃ p, E p := by
    intro ω hω
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hω.2
    obtain ⟨his, hib⟩ := Finset.mem_filter.mp hi
    obtain ⟨hjs, hjb⟩ := Finset.mem_filter.mp hj
    refine Set.mem_iUnion.mpr ⟨(⟨i, his⟩, ⟨j, hjs⟩), ?_⟩
    simpa [E, hij] using And.intro hω.1 (And.intro hib hjb)
  have hbound : ∀ p : s × s, μ.real (E p) ≤ ε ^ 2 / (K : ℝ) ^ s.card := by
    intro p
    by_cases hij : (p.1 : Fin n) = p.2
    · simp only [E, if_pos hij, measureReal_empty]
      exact div_nonneg (sq_nonneg ε) (pow_nonneg (Nat.cast_nonneg K) _)
    · exact le_of_eq (by
        simpa only [E, if_neg hij, Measure.real] using
          assignment_two_specified_marks_probability h s a p.1 p.2 hij)
  calc
    _ ≤ μ.real (⋃ p, E p) := measureReal_mono hsub
    _ ≤ ∑ p : s × s, μ.real (E p) := measureReal_iUnion_fintype_le E
    _ ≤ ∑ _p : s × s, ε ^ 2 / (K : ℝ) ^ s.card :=
      Finset.sum_le_sum (fun p _ => hbound p)
    _ = _ := by simp [Fintype.card_prod, Fintype.card_coe]; ring

/-- In [the independent uniform model](hyp:h), [assignments on two disjoint
labelled subsets](hyp:s,t,a,b,hdisj) with [one mark in each](goal) have probability
at most the reciprocal-power cell probability times ε² times the two sizes.
-/
theorem assignment_pair_marks_probability_le {n K : ℕ} {μ : Measure Ω}
    {X : Fin n → Ω → Fin K} {B : Fin n → Ω → Bool} {ε : ℝ}
    (h : UniformMarkedSample μ X B ε) (s t : Finset (Fin n))
    (hdisj : Disjoint s t) (a : s → Fin K) (b : t → Fin K) :
    (μ {ω | (∀ i : s, X i ω = a i) ∧ (∀ i : t, X i ω = b i) ∧
      1 ≤ markCount s (fun i => B i ω) ∧
      1 ≤ markCount t (fun i => B i ω)}).toReal ≤
      ε ^ 2 * (s.card : ℝ) * (t.card : ℝ) / (K : ℝ) ^ (s.card + t.card) := by
  classical
  have : IsProbabilityMeasure μ := h.probability
  let c : (↑(s ∪ t) : Type) → Fin K := fun i =>
    if hi : (i : Fin n) ∈ s then a ⟨i, hi⟩ else
      b ⟨i, (Finset.mem_union.mp i.property).resolve_left hi⟩
  have hc : ∀ ω, (∀ i : (↑(s ∪ t) : Type), X i ω = c i) ↔
      (∀ i : s, X i ω = a i) ∧ (∀ i : t, X i ω = b i) := by
    intro ω
    constructor
    · intro hw
      constructor
      · intro i
        simpa only [c, dif_pos i.property] using
          hw ⟨i, Finset.mem_union_left t i.property⟩
      · intro i
        have hi : (i : Fin n) ∉ s := fun hs =>
          Finset.disjoint_left.mp hdisj hs i.property
        simpa only [c, dif_neg hi] using
          hw ⟨i, Finset.mem_union_right s i.property⟩
    · rintro ⟨hs, ht⟩ i
      by_cases hi : (i : Fin n) ∈ s
      · simpa only [c, dif_pos hi] using hs ⟨i, hi⟩
      · simpa only [c, dif_neg hi] using
          ht ⟨i, (Finset.mem_union.mp i.property).resolve_left hi⟩
  let E : s × t → Set Ω := fun p =>
    {ω | (∀ i : (↑(s ∪ t) : Type), X i ω = c i) ∧
      B p.1 ω = true ∧ B p.2 ω = true}
  have hsub : {ω | (∀ i : s, X i ω = a i) ∧ (∀ i : t, X i ω = b i) ∧
      1 ≤ markCount s (fun i => B i ω) ∧
      1 ≤ markCount t (fun i => B i ω)} ⊆ ⋃ p, E p := by
    rintro ω ⟨hs, ht, hms, hmt⟩
    obtain ⟨i, hi⟩ := Finset.one_le_card.mp hms
    obtain ⟨j, hj⟩ := Finset.one_le_card.mp hmt
    obtain ⟨his, hib⟩ := Finset.mem_filter.mp hi
    obtain ⟨hjt, hjb⟩ := Finset.mem_filter.mp hj
    exact Set.mem_iUnion.mpr ⟨(⟨i, his⟩, ⟨j, hjt⟩),
      (hc ω).mpr ⟨hs, ht⟩, hib, hjb⟩
  have hbound : ∀ p : s × t,
      μ.real (E p) = ε ^ 2 / (K : ℝ) ^ (s.card + t.card) := by
    intro p
    have hij : (p.1 : Fin n) ≠ p.2 := by
      intro he
      exact Finset.disjoint_left.mp hdisj p.1.property (he ▸ p.2.property)
    simpa only [E, Measure.real, Finset.card_union_of_disjoint hdisj] using
      assignment_two_specified_marks_probability h (s ∪ t) c p.1 p.2 hij
  calc
    _ ≤ μ.real (⋃ p, E p) := measureReal_mono hsub
    _ ≤ ∑ p : s × t, μ.real (E p) := measureReal_iUnion_fintype_le E
    _ = ∑ _p : s × t, ε ^ 2 / (K : ℝ) ^ (s.card + t.card) :=
      Finset.sum_congr rfl (fun p _ => hbound p)
    _ = _ := by simp [Fintype.card_prod, Fintype.card_coe]; ring

end Causalean.Stat.RandomGraph.PathOccupancy
