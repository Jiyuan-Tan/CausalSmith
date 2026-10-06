module
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.Law

/-!
# Ordered labeled Poisson stream laws

This module identifies the ordered label streams of a marked Poisson sample
with independent finite Poisson samples and transports that law to the
nonoverflow part of a single capped iid pool.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.FiniteMeasurablePartition

variable {X I : Type*} [MeasurableSpace X] [MeasurableSpace I]
  [Fintype I] [MeasurableSingletonClass I]

/-- Given [an iid observation law](hyp:P), [label masses](hyp:p) [summing to
one](hyp:hp), [a pool size](hyp:n), and [an admissible prefix length](hyp:h),
[unshuffling the labeled fixed-pool prefix has the same law as unshuffling an
iid marked tuple of that length](goal). -/
theorem map_labeledPrefix_joint_eq
    (P : Measure X) [IsProbabilityMeasure P]
    (p : I → ℝ≥0) (hp : ∑ i, p i = 1)
    {n m : ℕ} (h : m ≤ n) :
    Measure.map
      (fun z : (Fin n → X) × (Fin n → I) =>
        labeledPrefix z.1 m h
          (fun k => z.2 ⟨k.val, lt_of_lt_of_le k.isLt h⟩))
      ((fixedPoolLaw P n).prod (Measure.pi (fun _ : Fin n => labelLaw p hp))) =
    Measure.map (fun z : Fin m → X × I => unshuffle (⟨m, z⟩ : FiniteSample (X × I)))
      (Measure.pi (fun _ : Fin m => P.prod (labelLaw p hp))) := by
  rw [← map_joint_prefix_pi P p hp h]
  rw [Measure.map_map]
  · rfl
  · exact measurable_unshuffle.comp (measurable_fixedSizeEmbed m)
  · fun_prop

/-- Given [an observation probability law](hyp:P), [label masses](hyp:p)
[summing to one](hyp:hp), [a Poisson mean](hyp:lambda), and [a count](hyp:m),
[the uncapped labeled-stream law on its total-count fibre is Poisson mass times
the law of an unshuffled iid marked tuple](goal). -/
theorem labeledStreamLaw_restrict_totalCount_eq
    (P : Measure X) [IsProbabilityMeasure P]
    (p : I → ℝ≥0) (hp : ∑ i, p i = 1) (lambda : ℝ≥0) (m : ℕ) :
    (labeledStreamLaw P p hp lambda).restrict
      {s | ∑ i, (s i).count = m} =
    (poissonMeasure lambda) {m} •
      Measure.map (fun z : Fin m → X × I => unshuffle (⟨m, z⟩ : FiniteSample (X × I)))
        (Measure.pi (fun _ : Fin m => P.prod (labelLaw p hp))) := by
  letI := labelLaw_isProbabilityMeasure p hp
  let Q := P.prod (labelLaw p hp)
  have hset : MeasurableSet {s : I → FiniteSample X | ∑ i, (s i).count = m} := by
    have hc : Measurable (fun s : I → FiniteSample X => ∑ i, (s i).count) := by
      fun_prop
    exact hc (measurableSet_singleton m)
  have hpre : unshuffle (X := X) (I := I) ⁻¹'
      {s | ∑ i, (s i).count = m} =
      FiniteSample.count ⁻¹' ({m} : Set ℕ) := by
    ext s
    simp [unshuffle_total_count]
  unfold labeledStreamLaw
  rw [Measure.restrict_map measurable_unshuffle hset, hpre,
    finitePoissonSampleLaw_restrict_count_eq Q lambda m,
    Measure.map_smul, Measure.map_map]
  · rfl
  · exact measurable_unshuffle
  · exact measurable_fixedSizeEmbed m

/-- Given [an iid observation law](hyp:P), [label masses](hyp:p) [summing to one](hyp:hp),
[a Poisson mean](hyp:lambda), and [a label-count vector](hyp:c), [restricting the
unshuffled Poisson law to that count vector](goal) equals the Poisson mass of
its total length times the unshuffled fixed-length marked law restricted to
the corresponding word histogram. -/
theorem labeledStreamLaw_restrict_countVector_eq_histogramMap
    (P : Measure X) [IsProbabilityMeasure P]
    (p : I → ℝ≥0) (hp : ∑ i, p i = 1) (lambda : ℝ≥0) (c : I → ℕ) :
    (labeledStreamLaw P p hp lambda).restrict
        {s | ∀ i, (s i).count = c i} =
      (poissonMeasure lambda) ({∑ i, c i} : Set ℕ) •
        Measure.map
          (fun z : Fin (∑ i, c i) → X × I =>
            unshuffle (⟨∑ i, c i, z⟩ : FiniteSample (X × I)))
          ((Measure.pi (fun _ : Fin (∑ i, c i) => P.prod (labelLaw p hp))).restrict
            {z | ∀ i, wordHistogram (fun k => (z k).2) i = c i}) := by
  -- Restrict the fixed-total-count identity once more. The inverse image of
  -- the count-vector event under `unshuffle` is the word-histogram event,
  -- since each stream length is its label's word histogram.
  let A : Set (I → FiniteSample X) := {s | ∀ i, (s i).count = c i}
  let B : Set (I → FiniteSample X) := {s | ∑ i, (s i).count = ∑ i, c i}
  let H : Set (Fin (∑ i, c i) → X × I) :=
    {z | ∀ i, wordHistogram (fun k => (z k).2) i = c i}
  let f : (Fin (∑ i, c i) → X × I) → I → FiniteSample X :=
    fun z => unshuffle (⟨∑ i, c i, z⟩ : FiniteSample (X × I))
  have hAB : A ⊆ B := by
    intro s hs
    exact Finset.sum_congr rfl (fun i _ => hs i)
  have hA : MeasurableSet A := by
    have hset : A = ⋂ i : I, {s : I → FiniteSample X | (s i).count = c i} := by
      ext s
      simp [A]
    rw [hset]
    apply MeasurableSet.iInter
    intro i
    have hm : Measurable (fun s : I → FiniteSample X => (s i).count) := by fun_prop
    exact hm (measurableSet_singleton (c i))
  have hf : Measurable f :=
    measurable_unshuffle.comp (measurable_fixedSizeEmbed (∑ i, c i))
  have hpre : f ⁻¹' A = H := by
    ext z
    change (∀ i, ((unshuffle (⟨∑ i, c i, z⟩ : FiniteSample (X × I))) i).count =
      c i) ↔ (∀ i, wordHistogram (fun k => (z k).2) i = c i)
    rfl
  change (labeledStreamLaw P p hp lambda).restrict A =
    (poissonMeasure lambda) {∑ i, c i} •
      Measure.map f
        ((Measure.pi (fun _ : Fin (∑ i, c i) => P.prod (labelLaw p hp))).restrict H)
  calc
    (labeledStreamLaw P p hp lambda).restrict A =
        ((labeledStreamLaw P p hp lambda).restrict B).restrict A :=
      (Measure.restrict_restrict_of_subset hAB).symm
    _ = ((poissonMeasure lambda) {∑ i, c i} •
          Measure.map f
            (Measure.pi (fun _ : Fin (∑ i, c i) => P.prod (labelLaw p hp)))).restrict A := by
      rw [show B = {s : I → FiniteSample X | ∑ i, (s i).count = ∑ i, c i} from rfl,
        labeledStreamLaw_restrict_totalCount_eq]
    _ = _ := by
      rw [Measure.restrict_smul, Measure.restrict_map hf hA, hpre]

/-- Given [an iid observation law](hyp:P), [label masses](hyp:p) [summing to one](hyp:hp),
[a Poisson mean](hyp:lambda), and [a prescribed label-count vector](hyp:c), [the
uncapped unshuffled law on that count-vector fibre is the product of the count
probabilities times independent fixed-length iid streams](goal). -/
theorem labeledStreamLaw_restrict_countVector_eq
    (P : Measure X) [IsProbabilityMeasure P]
    (p : I → ℝ≥0) (hp : ∑ i, p i = 1) (lambda : ℝ≥0) (c : I → ℕ) :
    (labeledStreamLaw P p hp lambda).restrict
        {s | ∀ i, (s i).count = c i} =
      (∏ i, (poissonMeasure (lambda * p i)) ({c i} : Set ℕ)) •
        Measure.pi (fun i : I =>
          Measure.map (fixedSizeEmbed (c i))
            (Measure.pi (fun _ : Fin (c i) => P))) := by
  -- Restrict first to total count `∑ i, c i`, then partition the iid label
  -- words by their histogram. On each word, `map_gatherWord_iid_pi` gives
  -- the same product of fixed-length iid observation laws. Sum the word
  -- coefficients with `poisson_label_word_coefficient_eq`.
  rw [labeledStreamLaw_restrict_countVector_eq_histogramMap P p hp lambda c,
    map_unshuffle_restrict_histogram_eq P p hp c, smul_smul,
    poisson_label_word_coefficient_eq p hp lambda c]

/-- Given [an observation probability law](hyp:P), [label masses](hyp:p) [summing to
one](hyp:hp), and [a Poisson mean](hyp:lambda), [the unshuffled streams are independent
finite Poisson samples](goal), with label-specific mean `lambda * p i`. -/
theorem labeledStreamLaw_eq_independent
    (P : Measure X) [IsProbabilityMeasure P]
    (p : I → ℝ≥0) (hp : ∑ i, p i = 1) (lambda : ℝ≥0) :
    labeledStreamLaw P p hp lambda =
      Measure.pi (fun i : I => finitePoissonSampleLaw P (lambda * p i)) := by
  -- Partition both measures by the complete label-count vector. On every
  -- fibre, use the two fixed-count identities above; then sum the pairwise
  -- disjoint restrictions. This keeps arbitrary measurable observation spaces.
  classical
  have hcover :
      (⋃ c : I → ℕ, {s : I → FiniteSample X | ∀ i, (s i).count = c i}) =
        Set.univ := by
    ext s
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact ⟨fun i => (s i).count, fun i => rfl⟩
  apply Measure.ext_of_iUnion_eq_univ hcover
  intro c
  exact (labeledStreamLaw_restrict_countVector_eq P p hp lambda c).trans
    (independentStreamLaw_restrict_countVector_eq P p hp lambda c).symm

/-- On [a Poisson mean](hyp:lambda) and [label masses summing to one](hyp:p,hp), [an observation law](hyp:P), and [an exact admissible Poisson count](hyp:m,h), [the labeled fixed-pool
experiment](goal) has Poisson mass at that count times the law of an unshuffled iid
marked tuple of that length. -/
theorem map_labeledPrefix_restrict_count_eq
    (P : Measure X) [IsProbabilityMeasure P]
    (p : I → ℝ≥0) (hp : ∑ i, p i = 1) (lambda : ℝ≥0)
    {n m : ℕ} (h : m ≤ n) :
    Measure.map
      (fun z : (Fin n → X) × (ℕ × (Fin n → I)) =>
        labeledPrefix z.1 m h
          (fun k => z.2.2 ⟨k.val, lt_of_lt_of_le k.isLt h⟩))
      (((fixedPoolLaw P n).prod (auxiliaryLaw p hp lambda n)).restrict
        {z | z.2.1 = m}) =
      (poissonMeasure lambda) {m} •
        Measure.map
          (fun z : Fin m → X × I => unshuffle (⟨m, z⟩ : FiniteSample (X × I)))
          (Measure.pi (fun _ : Fin m => P.prod (labelLaw p hp))) := by
  classical
  haveI := labelLaw_isProbabilityMeasure p hp
  haveI : IsProbabilityMeasure (fixedPoolLaw P n) := by
    unfold fixedPoolLaw
    infer_instance
  let L : Measure (Fin n → I) := Measure.pi (fun _ => labelLaw p hp)
  let c : ℝ≥0∞ := (poissonMeasure lambda) {m}
  have hs : {z : (Fin n → X) × (ℕ × (Fin n → I)) | z.2.1 = m} =
      Set.univ ×ˢ (({m} : Set ℕ) ×ˢ Set.univ) := by
    ext z
    simp
  have haux : (auxiliaryLaw p hp lambda n).restrict
      (({m} : Set ℕ) ×ˢ Set.univ) =
      c • Measure.map (Prod.mk m) L := by
    unfold auxiliaryLaw
    rw [← Measure.prod_restrict, Measure.restrict_univ,
      Measure.restrict_singleton, Measure.prod_smul_left, Measure.dirac_prod]
  let f : (Fin n → X) × (ℕ × (Fin n → I)) → I → FiniteSample X :=
    fun z => labeledPrefix z.1 m h
      (fun k => z.2.2 ⟨k.val, lt_of_lt_of_le k.isLt h⟩)
  let g : (Fin n → X) × (Fin n → I) → I → FiniteSample X :=
    fun z => labeledPrefix z.1 m h
      (fun k => z.2 ⟨k.val, lt_of_lt_of_le k.isLt h⟩)
  have hf : Measurable f := by
    exact measurable_unshuffle.comp (measurable_fixedSizeEmbed m |>.comp
      (measurable_pi_lambda _ fun k =>
        ((measurable_pi_apply _).comp measurable_fst).prodMk
          ((measurable_pi_apply _).comp measurable_snd.snd)))
  have hprod : (fixedPoolLaw P n).prod (Measure.map (Prod.mk m) L) =
      Measure.map (Prod.map id (Prod.mk m)) ((fixedPoolLaw P n).prod L) := by
    simpa only [Measure.map_id] using
      (Measure.map_prod_map (fixedPoolLaw P n) L measurable_id measurable_prodMk_left)
  calc
    Measure.map f (((fixedPoolLaw P n).prod (auxiliaryLaw p hp lambda n)).restrict
        {z | z.2.1 = m}) =
        Measure.map f ((fixedPoolLaw P n).prod
          ((auxiliaryLaw p hp lambda n).restrict (({m} : Set ℕ) ×ˢ Set.univ))) := by
            rw [hs, ← Measure.prod_restrict, Measure.restrict_univ]
    _ = c • Measure.map g ((fixedPoolLaw P n).prod L) := by
      rw [haux, Measure.prod_smul_right, Measure.map_smul, hprod,
        Measure.map_map]
      · rfl
      · exact hf
      · fun_prop
    _ = _ := by rw [map_labeledPrefix_joint_eq P p hp h]

/-- Given [an observation probability law](hyp:P), [label masses](hyp:p) [summing to
one](hyp:hp), [a Poisson mean](hyp:lambda), and [a pool size](hyp:n), [the capped fixed-pool
experiment on nonoverflow has the same ordered-stream law as the uncapped labeled Poisson
experiment restricted to total count at most the pool size](goal). -/
theorem map_capped_restrict_nonoverflow
    (P : Measure X) [IsProbabilityMeasure P]
    (p : I → ℝ≥0) (hp : ∑ i, p i = 1) (lambda : ℝ≥0) (n : ℕ) :
    Measure.map
      (fun z : (Fin n → X) × (ℕ × (Fin n → I)) =>
        if h : z.2.1 ≤ n then
          labeledPrefix z.1 z.2.1 h
            (fun k => z.2.2 ⟨k.val, lt_of_lt_of_le k.isLt h⟩)
        else fun _ => (⟨0, Fin.elim0⟩ : FiniteSample X))
      (((fixedPoolLaw P n).prod (auxiliaryLaw p hp lambda n)).restrict
        {z | z.2.1 ≤ n}) =
      (labeledStreamLaw P p hp lambda).restrict
        {s | ∑ i, (s i).count ≤ n} := by
  classical
  let μ := (fixedPoolLaw P n).prod (auxiliaryLaw p hp lambda n)
  let ν := labeledStreamLaw P p hp lambda
  let f : (Fin n → X) × (ℕ × (Fin n → I)) → I → FiniteSample X := fun z =>
    if h : z.2.1 ≤ n then
      labeledPrefix z.1 z.2.1 h
        (fun k => z.2.2 ⟨k.val, lt_of_lt_of_le k.isLt h⟩)
    else fun _ => (⟨0, Fin.elim0⟩ : FiniteSample X)
  have hf : Measurable f := by
    let g : ℕ × ((Fin n → X) × (Fin n → I)) → I → FiniteSample X := fun z =>
      if h : z.1 ≤ n then
        labeledPrefix z.2.1 z.1 h
          (fun k => z.2.2 ⟨k.val, lt_of_lt_of_le k.isLt h⟩)
      else fun _ => (⟨0, Fin.elim0⟩ : FiniteSample X)
    have hg : Measurable g := by
      apply measurable_from_prod_countable_right
      intro m
      by_cases hm : m ≤ n
      · have hprefix : Measurable (fun z : (Fin n → X) × (Fin n → I) =>
            labeledPrefix z.1 m hm
              (fun k => z.2 ⟨k.val, lt_of_lt_of_le k.isLt hm⟩)) := by
          exact measurable_unshuffle.comp (measurable_fixedSizeEmbed m |>.comp
            (measurable_pi_lambda _ fun k =>
              ((measurable_pi_apply _).comp measurable_fst).prodMk
                ((measurable_pi_apply _).comp measurable_snd)))
        simpa only [g, hm, dite_true] using hprefix
      · simpa only [g, hm, dite_false] using
          (measurable_const : Measurable (fun _ : (Fin n → X) × (Fin n → I) =>
            (fun _ => (⟨0, Fin.elim0⟩ : FiniteSample X))))
    exact hg.comp (by fun_prop : Measurable
      (fun z : (Fin n → X) × (ℕ × (Fin n → I)) => (z.2.1, (z.1, z.2.2))))
  have hfiber (m : Fin (n + 1)) :
      Measure.map f (μ.restrict {z | z.2.1 = m.val}) =
        ν.restrict {s | ∑ i, (s i).count = m.val} := by
    have hm : m.val ≤ n := Nat.le_of_lt_succ m.isLt
    have hmap : Measure.map f (μ.restrict {z | z.2.1 = m.val}) =
        Measure.map (fun z : (Fin n → X) × (ℕ × (Fin n → I)) =>
          labeledPrefix z.1 m.val hm
            (fun k => z.2.2 ⟨k.val, lt_of_lt_of_le k.isLt hm⟩))
          (μ.restrict {z | z.2.1 = m.val}) := by
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem (by
        exact (measurable_fst.comp measurable_snd) (measurableSet_singleton m.val) :
          MeasurableSet {z : (Fin n → X) × (ℕ × (Fin n → I)) | z.2.1 = m.val})]
        with z hz
      rcases z with ⟨x, ⟨k, w⟩⟩
      change k = m.val at hz
      subst k
      simp [f, hm]
    rw [hmap, map_labeledPrefix_restrict_count_eq P p hp lambda hm,
      ← labeledStreamLaw_restrict_totalCount_eq P p hp lambda m.val]
  have hsource : {z : (Fin n → X) × (ℕ × (Fin n → I)) | z.2.1 ≤ n} =
      ⋃ m : Fin (n + 1), {z | z.2.1 = m.val} := by
    ext z
    simp only [Set.mem_iUnion]
    constructor
    · intro hz
      exact ⟨⟨z.2.1, Nat.lt_succ_of_le hz⟩, rfl⟩
    · rintro ⟨m, hm⟩
      change z.2.1 = m.val at hm
      change z.2.1 ≤ n
      rw [hm]
      exact Nat.le_of_lt_succ m.isLt
  have htarget : {s : I → FiniteSample X | ∑ i, (s i).count ≤ n} =
      ⋃ m : Fin (n + 1), {s | ∑ i, (s i).count = m.val} := by
    ext s
    simp only [Set.mem_iUnion]
    constructor
    · intro hs
      exact ⟨⟨∑ i, (s i).count, Nat.lt_succ_of_le hs⟩, rfl⟩
    · rintro ⟨m, hm⟩
      change (∑ i, (s i).count) = m.val at hm
      change (∑ i, (s i).count) ≤ n
      rw [hm]
      exact Nat.le_of_lt_succ m.isLt
  have hsource_disjoint : Pairwise (Function.onFun Disjoint
      (fun m : Fin (n + 1) =>
        {z : (Fin n → X) × (ℕ × (Fin n → I)) | z.2.1 = m.val})) := by
    intro a b hab
    change Disjoint
      {z : (Fin n → X) × (ℕ × (Fin n → I)) | z.2.1 = a.val}
      {z : (Fin n → X) × (ℕ × (Fin n → I)) | z.2.1 = b.val}
    rw [Set.disjoint_left]
    intro z hza hzb
    apply hab
    apply Fin.ext
    exact hza.symm.trans hzb
  have htarget_disjoint : Pairwise (Function.onFun Disjoint
      (fun m : Fin (n + 1) =>
        {s : I → FiniteSample X | ∑ i, (s i).count = m.val})) := by
    intro a b hab
    change Disjoint
      {s : I → FiniteSample X | ∑ i, (s i).count = a.val}
      {s : I → FiniteSample X | ∑ i, (s i).count = b.val}
    rw [Set.disjoint_left]
    intro s hsa hsb
    apply hab
    apply Fin.ext
    exact hsa.symm.trans hsb
  change Measure.map f (μ.restrict {z | z.2.1 ≤ n}) =
    ν.restrict {s | ∑ i, (s i).count ≤ n}
  rw [hsource, Measure.restrict_iUnion hsource_disjoint
    (fun m => (measurable_fst.comp measurable_snd) (measurableSet_singleton m.val)),
    Measure.map_sum hf.aemeasurable, htarget,
    Measure.restrict_iUnion htarget_disjoint (fun m => by
      have hc : Measurable (fun s : I → FiniteSample X => ∑ i, (s i).count) := by
        fun_prop
      exact hc (measurableSet_singleton m.val))]
  congr 1
  funext m
  exact hfiber m

end Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition

