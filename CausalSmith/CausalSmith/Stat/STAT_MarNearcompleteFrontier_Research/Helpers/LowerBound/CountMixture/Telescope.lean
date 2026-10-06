module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.LowerBound.CountMixture.PairMarks
public import Causalean.Mathlib.Algebra.BigOperators.Ring.ProductDifference
public import Causalean.Stat.Concentration.Poisson.CountVectorSeries

/-! # Telescope for the paired count-mixture comparison -/

@[expose] public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open Causalean.Stat.Concentration.Poisson

open Causalean.Mathlib.Algebra.BigOperators.Ring

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal



-- @node: labelPoissonFactor
/-- Product-Poisson likelihood factor restricted to one baseline label. Given [the specified input `rate`](hyp:rate), [the specified input `x`](hyp:x), [the specified input `counts`](hyp:counts), [the stated mathematical conclusion holds](goal). -/
noncomputable def labelPoissonFactor (rate : Obs d → ℝ≥0) (x : Fin d)
    (counts : Obs d → ℕ) : ℝ :=
  ∏ o : Obs d, if o.X = x then
    Real.exp (-(rate o : ℝ)) * (rate o : ℝ) ^ counts o /
      (counts o).factorial else 1

-- @node: prod_labelPoissonFactor
/-- Multiplying all baseline-label-local Poisson factors recovers the full
observed-coordinate product likelihood. Given [the specified input `rate`](hyp:rate), [the specified input `counts`](hyp:counts), [the stated mathematical conclusion holds](goal). -/
lemma prod_labelPoissonFactor (rate : Obs d → ℝ≥0)
    (counts : Obs d → ℕ) :
    (∏ x : Fin d, labelPoissonFactor rate x counts) =
      ∏ o : Obs d, Real.exp (-(rate o : ℝ)) *
        (rate o : ℝ) ^ counts o / (counts o).factorial := by
  unfold labelPoissonFactor
  exact (prod_by_observed_label fun o : Obs d =>
    Real.exp (-(rate o : ℝ)) * (rate o : ℝ) ^ counts o /
      (counts o).factorial).symm

-- @node: labelPoissonFactor_countVector_tsum_one
/-- The product of all local baseline-label Poisson factors sums to one over
the full observed count-vector space. Given [the specified input `rate`](hyp:rate), [the stated mathematical conclusion holds](goal). -/
lemma labelPoissonFactor_countVector_tsum_one (rate : Obs d → ℝ≥0) :
    (∑' counts : Obs d → ℕ,
      ∏ x : Fin d, labelPoissonFactor rate x counts) = 1 := by
  rw [show (∑' counts : Obs d → ℕ,
      ∏ x : Fin d, labelPoissonFactor rate x counts) =
      ∑' counts : Obs d → ℕ, ∏ o : Obs d,
        Real.exp (-(rate o : ℝ)) * (rate o : ℝ) ^ counts o /
          (counts o).factorial by
    apply tsum_congr
    exact prod_labelPoissonFactor rate]
  exact poissonFactorial_countVector_tsum_one rate

-- @node: assembledLabelRate
/-- Global observed-coordinate rate assembled from one local rate family per
baseline label. Given [the specified input `localRate`](hyp:localRate), [the specified input `o`](hyp:o), [the stated mathematical conclusion holds](goal). -/
noncomputable def assembledLabelRate (localRate : Fin d → Obs d → ℝ≥0)
    (o : Obs d) : ℝ≥0 := localRate o.X o

-- @node: localLabelPoissonFactor
/-- Poisson factor at one baseline label using that label's member of a local
rate family. Given [the specified input `localRate`](hyp:localRate), [the specified input `x`](hyp:x), [the specified input `counts`](hyp:counts), [the stated mathematical conclusion holds](goal). -/
noncomputable def localLabelPoissonFactor
    (localRate : Fin d → Obs d → ℝ≥0) (x : Fin d)
    (counts : Obs d → ℕ) : ℝ :=
  ∏ o : Obs d, if o.X = x then
    Real.exp (-(localRate x o : ℝ)) * (localRate x o : ℝ) ^ counts o /
      (counts o).factorial else 1

-- @node: localLabelPoissonFactor_eq_assembled
/-- At each label, the local-family factor agrees with the corresponding
factor of the globally assembled rate. Given [the specified input `localRate`](hyp:localRate), [the specified input `x`](hyp:x), [the specified input `counts`](hyp:counts), [the stated mathematical conclusion holds](goal). -/
lemma localLabelPoissonFactor_eq_assembled
    (localRate : Fin d → Obs d → ℝ≥0) (x : Fin d)
    (counts : Obs d → ℕ) :
    localLabelPoissonFactor localRate x counts =
      labelPoissonFactor (assembledLabelRate localRate) x counts := by
  unfold localLabelPoissonFactor labelPoissonFactor assembledLabelRate
  apply Finset.prod_congr rfl
  intro o _
  by_cases ho : o.X = x
  · subst x
    simp
  · simp [ho]

-- @node: localLabelPoissonFactor_countVector_tsum_one
/-- Arbitrary nonnegative local rate families normalize jointly after their
disjoint baseline-label supports are assembled. Given [the specified input `localRate`](hyp:localRate), [the stated mathematical conclusion holds](goal). -/
lemma localLabelPoissonFactor_countVector_tsum_one
    (localRate : Fin d → Obs d → ℝ≥0) :
    (∑' counts : Obs d → ℕ,
      ∏ x : Fin d, localLabelPoissonFactor localRate x counts) = 1 := by
  simp_rw [localLabelPoissonFactor_eq_assembled]
  exact labelPoissonFactor_countVector_tsum_one (assembledLabelRate localRate)









-- @node: half_pairBlockMarkAverage_mem_unit
/-- The fair-orientation average of a legal pair-block mark likelihood lies in
the unit interval, as required by the product telescoping bound. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `z`](hyp:z), [the specified input `hd`](hyp:hd), [the specified input `counts`](hyp:counts), [the specified input `hz`](hyp:hz), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ), [the specified input `hσ`](hyp:hσ). Given [the specified input `j`](hyp:j), [the specified input `hq`](hyp:hq). -/
lemma half_pairBlockMarkAverage_mem_unit (n d : ℕ) (q σ z : ℝ)
    (hd : 1 ≤ d) (j : Fin (pairCount n d)) (counts : Obs d → ℕ)
    (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (hσ : σ = -1 ∨ σ = 1) (hz : z = -1 ∨ z = 1) :
    (1 / 2 : ℝ) * pairBlockMarkAverage n d q σ z hd j counts ∈
      Set.Icc 0 1 := by
  have hterm (base : Bool) :
      (∏ side : Bool,
        pairObservedMonomial q σ z (if base == side then 1 else -1)
          (pairLabel n d hd j side) counts) ∈ Set.Icc (0 : ℝ) 1 := by
    have hmono (side : Bool) := pairObservedMonomial_mem_unit q σ z
      (if base == side then 1 else -1) (pairLabel n d hd j side) counts
      hq hσ hz (by split_ifs <;> simp)
    exact ⟨Finset.prod_nonneg fun side _ => (hmono side).1,
      Finset.prod_le_one (fun side _ => (hmono side).1)
        (fun side _ => (hmono side).2)⟩
  unfold pairBlockMarkAverage
  constructor
  · exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun base _ => (hterm base).1)
  · calc
      (1 / 2 : ℝ) * ∑ base : Bool, ∏ side : Bool,
          pairObservedMonomial q σ z (if base == side then 1 else -1)
            (pairLabel n d hd j side) counts ≤
          (1 / 2 : ℝ) * ∑ _base : Bool, (1 : ℝ) := by
        gcongr with base
        exact (hterm base).2
      _ = 1 := by norm_num

-- @node: activeBaselineLabels
/-- Baseline labels carrying nonzero construction mass: the filler and the two
labels of every active latent pair. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hd`](hyp:hd), [the stated mathematical conclusion holds](goal). -/
noncomputable def activeBaselineLabels (n d : ℕ) (hd : 1 ≤ d) : Finset (Fin d) :=
  insert (fillerLabel d hd)
    (Finset.univ.image fun js : Fin (pairCount n d) × Bool =>
      pairLabel n d hd js.1 js.2)

-- @node: countAtomMass_eq_zero_of_unused
/-- Every baseline label outside the filler and paired-label image has exactly
zero conditional atom mass for all observed marks. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hd`](hyp:hd), [the specified input `o`](hyp:o), [the specified input `hf`](hyp:hf), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ), [the specified input `θ`](hyp:θ). Given [the specified input `hp`](hyp:hp). -/
lemma countAtomMass_eq_zero_of_unused (n d : ℕ) (q σ : ℝ) (hd : 1 ≤ d)
    (θ : Theta n d) (o : Obs d)
    (hf : o.X ≠ fillerLabel d hd)
    (hp : ∀ j : Fin (pairCount n d), ∀ side : Bool,
      o.X ≠ pairLabel n d hd j side) :
    countAtomMass n d q σ hd θ o = 0 := by
  unfold countAtomMass
  rw [if_neg hf]
  simp only [zero_add]
  apply Finset.sum_eq_zero
  intro j _
  apply Finset.sum_eq_zero
  intro side _
  rw [if_neg (hp j side)]

-- @node: partitionedLocalRate
/-- Local rate family assembled from one filler rate, one rate for every pair
side, and zero on unused baseline labels. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hd`](hyp:hd), [the specified input `fillerRate`](hyp:fillerRate), [the specified input `x`](hyp:x), [the specified input `o`](hyp:o), [the stated mathematical conclusion holds](goal). Given [the specified input `pairRate`](hyp:pairRate). -/
noncomputable def partitionedLocalRate (n d : ℕ) (hd : 1 ≤ d)
    (fillerRate : Obs d → ℝ≥0)
    (pairRate : Fin (pairCount n d) → Bool → Obs d → ℝ≥0)
    (x : Fin d) (o : Obs d) : ℝ≥0 :=
  if x = fillerLabel d hd then fillerRate o else
    ∑ j : Fin (pairCount n d), ∑ side : Bool,
      if x = pairLabel n d hd j side then pairRate j side o else 0

-- @node: partitionedLocalRate_filler
/-- At the filler label, the partitioned local family selects the filler
rate. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hd`](hyp:hd), [the specified input `fillerRate`](hyp:fillerRate), [the specified input `o`](hyp:o), [the stated mathematical conclusion holds](goal). Given [the specified input `pairRate`](hyp:pairRate). -/
lemma partitionedLocalRate_filler (n d : ℕ) (hd : 1 ≤ d)
    (fillerRate : Obs d → ℝ≥0)
    (pairRate : Fin (pairCount n d) → Bool → Obs d → ℝ≥0) (o : Obs d) :
    partitionedLocalRate n d hd fillerRate pairRate (fillerLabel d hd) o =
      fillerRate o := by
  simp [partitionedLocalRate]

-- @node: partitionedLocalRate_pair
/-- At an active pair label, the partitioned local family selects exactly its
corresponding pair-side rate. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hd`](hyp:hd), [the specified input `fillerRate`](hyp:fillerRate), [the specified input `side`](hyp:side), [the specified input `o`](hyp:o), [the stated mathematical conclusion holds](goal). Given [the specified input `pairRate`](hyp:pairRate), [the specified input `j`](hyp:j). -/
lemma partitionedLocalRate_pair (n d : ℕ) (hd : 1 ≤ d)
    (fillerRate : Obs d → ℝ≥0)
    (pairRate : Fin (pairCount n d) → Bool → Obs d → ℝ≥0)
    (j : Fin (pairCount n d)) (side : Bool) (o : Obs d) :
    partitionedLocalRate n d hd fillerRate pairRate
        (pairLabel n d hd j side) o = pairRate j side o := by
  unfold partitionedLocalRate
  rw [if_neg (fillerLabel_ne_pairLabel n d hd j side).symm]
  rw [Finset.sum_eq_single j]
  · rw [Finset.sum_eq_single side]
    · simp
    · intro side' _ hne
      rw [if_neg]
      intro hlabel
      exact hne (pairLabel_injective n d hd j j side' side hlabel.symm).2
    · simp
  · intro k _ hne
    apply Finset.sum_eq_zero
    intro side' _
    rw [if_neg]
    intro hlabel
    exact hne (pairLabel_injective n d hd k j side' side hlabel.symm).1
  · simp

-- @node: partitionedLocalRate_unused
/-- The partitioned local family vanishes at every unused baseline label. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hd`](hyp:hd), [the specified input `fillerRate`](hyp:fillerRate), [the specified input `x`](hyp:x), [the specified input `hx`](hyp:hx), [the specified input `o`](hyp:o), [the stated mathematical conclusion holds](goal). Given [the specified input `pairRate`](hyp:pairRate). -/
lemma partitionedLocalRate_unused (n d : ℕ) (hd : 1 ≤ d)
    (fillerRate : Obs d → ℝ≥0)
    (pairRate : Fin (pairCount n d) → Bool → Obs d → ℝ≥0)
    (x : Fin d) (hx : x ∈ Finset.univ \ activeBaselineLabels n d hd)
    (o : Obs d) :
    partitionedLocalRate n d hd fillerRate pairRate x o = 0 := by
  have hxnot := (Finset.mem_sdiff.mp hx).2
  have hfill : x ≠ fillerLabel d hd := by
    intro h
    apply hxnot
    rw [h]
    exact Finset.mem_insert_self _ _
  unfold partitionedLocalRate
  rw [if_neg hfill]
  apply Finset.sum_eq_zero
  intro j _
  apply Finset.sum_eq_zero
  intro side _
  rw [if_neg]
  intro h
  apply hxnot
  rw [h]
  apply Finset.mem_insert_of_mem
  exact Finset.mem_image.mpr ⟨(j, side), Finset.mem_univ _, rfl⟩

-- @node: prod_activeBaselineLabels
/-- A product over active baseline labels reindexes exactly into the filler
factor followed by one factor for each pair and side. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hd`](hyp:hd), [the specified input `f`](hyp:f), [the stated mathematical conclusion holds](goal). -/
lemma prod_activeBaselineLabels (n d : ℕ) (hd : 1 ≤ d) (f : Fin d → ℝ) :
    (∏ x ∈ activeBaselineLabels n d hd, f x) =
      f (fillerLabel d hd) *
        ∏ js : Fin (pairCount n d) × Bool, f (pairLabel n d hd js.1 js.2) := by
  unfold activeBaselineLabels
  rw [Finset.prod_insert]
  · congr 1
    apply Finset.prod_image
    intro a _ b _ hab
    rcases pairLabel_injective n d hd a.1 b.1 a.2 b.2 hab with ⟨h₁, h₂⟩
    exact Prod.ext h₁ h₂
  · simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro js
    exact (fillerLabel_ne_pairLabel n d hd js.1 js.2).symm

-- @node: prod_split_active_unused_labels
/-- Every baseline-label product splits exactly into filler, active pair labels,
and the complement of unused zero-rate labels. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hd`](hyp:hd), [the specified input `f`](hyp:f), [the stated mathematical conclusion holds](goal). -/
lemma prod_split_active_unused_labels (n d : ℕ) (hd : 1 ≤ d) (f : Fin d → ℝ) :
    (∏ x : Fin d, f x) =
      f (fillerLabel d hd) *
        (∏ js : Fin (pairCount n d) × Bool,
          f (pairLabel n d hd js.1 js.2)) *
        ∏ x ∈ (Finset.univ \ activeBaselineLabels n d hd), f x := by
  have hs : activeBaselineLabels n d hd ⊆ (Finset.univ : Finset (Fin d)) :=
    Finset.subset_univ _
  have hsplit := Finset.prod_sdiff (f := f) hs
  rw [prod_activeBaselineLabels n d hd f] at hsplit
  calc
    (∏ x : Fin d, f x) = ∏ x ∈ (Finset.univ : Finset (Fin d)), f x := by rfl
    _ = _ := by rw [← hsplit]; ring


end CausalSmith.Stat.MarNearcompleteFrontier
