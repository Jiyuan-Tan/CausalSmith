module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.LowerBound.CountMixture.Telescope

/-! # MarkedRates for the paired count-mixture comparison -/

@[expose] public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory ProbabilityTheory
open Causalean.Stat.Concentration.Poisson
open scoped ENNReal NNReal

-- @node: localLabelPoissonFactor_partitioned_filler
/-- The filler-label local Poisson factor of a partitioned family uses only
the supplied filler rate. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hd`](hyp:hd), [the specified input `fillerRate`](hyp:fillerRate), [the specified input `counts`](hyp:counts), [the stated mathematical conclusion holds](goal). Given [the specified input `pairRate`](hyp:pairRate). -/
lemma localLabelPoissonFactor_partitioned_filler (n d : ℕ) (hd : 1 ≤ d)
    (fillerRate : Obs d → ℝ≥0)
    (pairRate : Fin (pairCount n d) → Bool → Obs d → ℝ≥0)
    (counts : Obs d → ℕ) :
    localLabelPoissonFactor (partitionedLocalRate n d hd fillerRate pairRate)
        (fillerLabel d hd) counts =
      ∏ o : Obs d, if o.X = fillerLabel d hd then
        Real.exp (-(fillerRate o : ℝ)) * (fillerRate o : ℝ) ^ counts o /
          (counts o).factorial else 1 := by
  unfold localLabelPoissonFactor
  apply Finset.prod_congr rfl
  intro o _
  by_cases ho : o.X = fillerLabel d hd
  · simp only [ho, ↓reduceIte,
      partitionedLocalRate_filler n d hd fillerRate pairRate o]
  · simp [ho]

-- @node: localLabelPoissonFactor_partitioned_pair
/-- Each active pair-label local Poisson factor of a partitioned family uses
only its supplied pair-side rate. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hd`](hyp:hd), [the specified input `fillerRate`](hyp:fillerRate), [the specified input `side`](hyp:side), [the specified input `counts`](hyp:counts), [the stated mathematical conclusion holds](goal). Given [the specified input `pairRate`](hyp:pairRate), [the specified input `j`](hyp:j). -/
lemma localLabelPoissonFactor_partitioned_pair (n d : ℕ) (hd : 1 ≤ d)
    (fillerRate : Obs d → ℝ≥0)
    (pairRate : Fin (pairCount n d) → Bool → Obs d → ℝ≥0)
    (j : Fin (pairCount n d)) (side : Bool) (counts : Obs d → ℕ) :
    localLabelPoissonFactor (partitionedLocalRate n d hd fillerRate pairRate)
        (pairLabel n d hd j side) counts =
      ∏ o : Obs d, if o.X = pairLabel n d hd j side then
        Real.exp (-(pairRate j side o : ℝ)) *
          (pairRate j side o : ℝ) ^ counts o /
            (counts o).factorial else 1 := by
  unfold localLabelPoissonFactor
  apply Finset.prod_congr rfl
  intro o _
  by_cases ho : o.X = pairLabel n d hd j side
  · simp only [ho, ↓reduceIte,
      partitionedLocalRate_pair n d hd fillerRate pairRate j side o]
  · simp [ho]

-- @node: localLabelPoissonFactor_partitioned_unused
/-- At an unused label, the local Poisson factor is exactly the indicator that
all counts at that label vanish. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hd`](hyp:hd), [the specified input `fillerRate`](hyp:fillerRate), [the specified input `x`](hyp:x), [the specified input `hx`](hyp:hx), [the specified input `counts`](hyp:counts), [the stated mathematical conclusion holds](goal). Given [the specified input `pairRate`](hyp:pairRate). -/
lemma localLabelPoissonFactor_partitioned_unused (n d : ℕ) (hd : 1 ≤ d)
    (fillerRate : Obs d → ℝ≥0)
    (pairRate : Fin (pairCount n d) → Bool → Obs d → ℝ≥0)
    (x : Fin d) (hx : x ∈ Finset.univ \ activeBaselineLabels n d hd)
    (counts : Obs d → ℕ) :
    localLabelPoissonFactor (partitionedLocalRate n d hd fillerRate pairRate)
        x counts =
      ∏ o : Obs d, if o.X = x then (if counts o = 0 then 1 else 0) else 1 := by
  unfold localLabelPoissonFactor
  apply Finset.prod_congr rfl
  intro o _
  by_cases ho : o.X = x
  · rw [if_pos ho,
      partitionedLocalRate_unused n d hd fillerRate pairRate x hx o]
    by_cases hc : counts o = 0 <;> simp [ho, hc]
  · simp [ho]

-- @node: partitionedLocalPoisson_countVector_tsum_one
/-- Filler, pair-side, and unused-zero local factors jointly normalize over
the full observed count-vector space. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hd`](hyp:hd), [the specified input `fillerRate`](hyp:fillerRate), [the stated mathematical conclusion holds](goal). Given [the specified input `pairRate`](hyp:pairRate). -/
lemma partitionedLocalPoisson_countVector_tsum_one (n d : ℕ) (hd : 1 ≤ d)
    (fillerRate : Obs d → ℝ≥0)
    (pairRate : Fin (pairCount n d) → Bool → Obs d → ℝ≥0) :
    (∑' counts : Obs d → ℕ,
      (∏ o : Obs d, if o.X = fillerLabel d hd then
        Real.exp (-(fillerRate o : ℝ)) * (fillerRate o : ℝ) ^ counts o /
          (counts o).factorial else 1) *
      (∏ js : Fin (pairCount n d) × Bool, ∏ o : Obs d,
        if o.X = pairLabel n d hd js.1 js.2 then
          Real.exp (-(pairRate js.1 js.2 o : ℝ)) *
            (pairRate js.1 js.2 o : ℝ) ^ counts o /
              (counts o).factorial else 1) *
      ∏ x ∈ (Finset.univ \ activeBaselineLabels n d hd),
        ∏ o : Obs d, if o.X = x then
          (if counts o = 0 then 1 else 0) else 1) = 1 := by
  rw [show (∑' counts : Obs d → ℕ, _) =
      ∑' counts : Obs d → ℕ,
        ∏ x : Fin d, localLabelPoissonFactor
          (partitionedLocalRate n d hd fillerRate pairRate) x counts by
    apply tsum_congr
    intro counts
    rw [prod_split_active_unused_labels n d hd]
    rw [localLabelPoissonFactor_partitioned_filler]
    simp_rw [localLabelPoissonFactor_partitioned_pair]
    apply congrArg₂ (· * ·) rfl
    apply Finset.prod_congr rfl
    intro x hx
    exact (localLabelPoissonFactor_partitioned_unused
      n d hd fillerRate pairRate x hx counts).symm]
  exact localLabelPoissonFactor_countVector_tsum_one
    (partitionedLocalRate n d hd fillerRate pairRate)

-- @node: zero_rate_factor_eq_indicator
/-- A zero-rate Poisson factorial factor forces its count coordinate to zero. Given [the specified input `k`](hyp:k), [the stated mathematical conclusion holds](goal). -/
lemma zero_rate_factor_eq_indicator (k : ℕ) :
    (0 : ℝ) ^ k / (k.factorial : ℝ) = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · simp [hk]
  · simp [hk]

-- @node: obsProd_split_filler_pairs_unused
/-- Any product over observed atoms splits exactly into the filler block, one
block for every pair and side, and blocks over unused baseline labels. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hd`](hyp:hd), [the specified input `g`](hyp:g), [the stated mathematical conclusion holds](goal). -/
lemma obsProd_split_filler_pairs_unused (n d : ℕ) (hd : 1 ≤ d)
    (g : Obs d → ℝ) :
    (∏ o : Obs d, g o) =
      (∏ o : Obs d, if o.X = fillerLabel d hd then g o else 1) *
        (∏ js : Fin (pairCount n d) × Bool,
          ∏ o : Obs d,
            if o.X = pairLabel n d hd js.1 js.2 then g o else 1) *
        ∏ x ∈ (Finset.univ \ activeBaselineLabels n d hd),
          ∏ o : Obs d, if o.X = x then g o else 1 := by
  rw [prod_by_observed_label]
  exact prod_split_active_unused_labels n d hd
    (fun x => ∏ o : Obs d, if o.X = x then g o else 1)

-- @node: pairMarkedIntensity
/-- Marked count intensity for one pair at a fixed base orientation. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `z`](hyp:z), [the specified input `p`](hyp:p), [the specified input `hd`](hyp:hd), [the specified input `base`](hyp:base), [the specified input `o`](hyp:o), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ). Given [the specified input `j`](hyp:j). -/
noncomputable def pairMarkedIntensity (n d : ℕ) (q σ z p : ℝ)
    (hd : 1 ≤ d) (j : Fin (pairCount n d)) (base : Bool)
    (o : Obs d) : ℝ :=
  ∑ side : Bool, if o.X = pairLabel n d hd j side then
    4 * (n : ℝ) * p *
      pairObservedCoeff q σ z (if base == side then 1 else -1) o else 0

-- @node: pairMarkedIntensity_nonneg
/-- Legal pair marked intensities are nonnegative. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `z`](hyp:z), [the specified input `p`](hyp:p), [the specified input `hd`](hyp:hd), [the specified input `hz`](hyp:hz), [the specified input `hp`](hyp:hp), [the specified input `base`](hyp:base), [the specified input `o`](hyp:o), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ), [the specified input `hσ`](hyp:hσ). Given [the specified input `hq`](hyp:hq), [the specified input `j`](hyp:j). -/
lemma pairMarkedIntensity_nonneg (n d : ℕ) (q σ z p : ℝ)
    (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (hσ : σ = -1 ∨ σ = 1) (hz : z = -1 ∨ z = 1) (hp : 0 ≤ p)
    (j : Fin (pairCount n d)) (base : Bool) (o : Obs d) :
    0 ≤ pairMarkedIntensity n d q σ z p hd j base o := by
  unfold pairMarkedIntensity
  apply Finset.sum_nonneg
  intro side _
  by_cases ho : o.X = pairLabel n d hd j side
  · rw [if_pos ho]
    have hu : (if base == side then (1 : ℝ) else -1) = -1 ∨
        (if base == side then (1 : ℝ) else -1) = 1 := by
      by_cases h : base == side <;> simp [h]
    have hscale : 0 ≤ 4 * (n : ℝ) * p :=
      mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) hp
    exact mul_nonneg hscale
      (pairObservedCoeff_nonneg q σ z
        (if base == side then 1 else -1) o hq hσ hz hu)
  · rw [if_neg ho]

-- @node: pairMarkedIntensity_at_label
/-- At one of the pair's two labels, the marked intensity is its scalar mass
times the corresponding observed-mark coefficient. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `z`](hyp:z), [the specified input `p`](hyp:p), [the specified input `hd`](hyp:hd), [the specified input `base`](hyp:base), [the specified input `side`](hyp:side), [the specified input `o`](hyp:o), [the specified input `ho`](hyp:ho), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ). Given [the specified input `j`](hyp:j). -/
lemma pairMarkedIntensity_at_label (n d : ℕ) (q σ z p : ℝ)
    (hd : 1 ≤ d) (j : Fin (pairCount n d)) (base side : Bool)
    (o : Obs d) (ho : o.X = pairLabel n d hd j side) :
    pairMarkedIntensity n d q σ z p hd j base o =
      4 * (n : ℝ) * p *
        pairObservedCoeff q σ z (if base == side then 1 else -1) o := by
  unfold pairMarkedIntensity
  rw [Finset.sum_eq_single side]
  · rw [if_pos ho]
  · intro side' _ hne
    rw [if_neg]
    intro hlabel
    exact hne (pairLabel_injective n d hd j j side' side
      (hlabel.symm.trans ho)).2
  · simp

-- @node: pairMarkedIntensity_sum
/-- The marked intensities of one pair have total rate `8 * n * p`. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `z`](hyp:z), [the specified input `p`](hyp:p), [the specified input `hd`](hyp:hd), [the specified input `base`](hyp:base), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ). Given [the specified input `j`](hyp:j). -/
lemma pairMarkedIntensity_sum (n d : ℕ) (q σ z p : ℝ)
    (hd : 1 ≤ d) (j : Fin (pairCount n d)) (base : Bool) :
    (∑ o : Obs d, pairMarkedIntensity n d q σ z p hd j base o) =
      8 * (n : ℝ) * p := by
  unfold pairMarkedIntensity
  rw [Finset.sum_comm]
  have hside (side : Bool) :
      (∑ o : Obs d, if o.X = pairLabel n d hd j side then
        4 * (n : ℝ) * p *
          pairObservedCoeff q σ z (if base == side then 1 else -1) o else 0) =
        4 * (n : ℝ) * p := by
    calc
      _ = 4 * (n : ℝ) * p *
          (∑ o : Obs d, if o.X = pairLabel n d hd j side then
            pairObservedCoeff q σ z (if base == side then 1 else -1) o else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro o _
        split_ifs <;> ring
      _ = _ := by
        rw [sum_pairObservedCoeff_at_label]
        ring
  simp_rw [hside]
  norm_num
  ring

-- @node: pairMarkedRate
/-- Nonnegative-real packaging of one pair's marked intensity. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `z`](hyp:z), [the specified input `p`](hyp:p), [the specified input `hd`](hyp:hd), [the specified input `base`](hyp:base), [the specified input `o`](hyp:o), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ). Given [the specified input `j`](hyp:j). -/
noncomputable def pairMarkedRate (n d : ℕ) (q σ z p : ℝ)
    (hd : 1 ≤ d) (j : Fin (pairCount n d)) (base : Bool)
    (o : Obs d) : ℝ≥0 :=
  Real.toNNReal (pairMarkedIntensity n d q σ z p hd j base o)

-- @node: pairMarkedRate_coe
/-- Under the legal parameter restrictions, coercing `pairMarkedRate` back to
the reals recovers the marked intensity. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `z`](hyp:z), [the specified input `p`](hyp:p), [the specified input `hd`](hyp:hd), [the specified input `hz`](hyp:hz), [the specified input `hp`](hyp:hp), [the specified input `base`](hyp:base), [the specified input `o`](hyp:o), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ), [the specified input `hσ`](hyp:hσ). Given [the specified input `hq`](hyp:hq), [the specified input `j`](hyp:j). -/
lemma pairMarkedRate_coe (n d : ℕ) (q σ z p : ℝ)
    (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (hσ : σ = -1 ∨ σ = 1) (hz : z = -1 ∨ z = 1) (hp : 0 ≤ p)
    (j : Fin (pairCount n d)) (base : Bool) (o : Obs d) :
    (pairMarkedRate n d q σ z p hd j base o : ℝ) =
      pairMarkedIntensity n d q σ z p hd j base o := by
  exact Real.coe_toNNReal _
    (pairMarkedIntensity_nonneg n d q σ z p hd hq hσ hz hp j base o)

-- @node: pairMarkedRate_sum
/-- The packaged pair marked rate also has total mass `8 * n * p`. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `z`](hyp:z), [the specified input `p`](hyp:p), [the specified input `hd`](hyp:hd), [the specified input `hz`](hyp:hz), [the specified input `hp`](hyp:hp), [the specified input `base`](hyp:base), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ), [the specified input `hσ`](hyp:hσ). Given [the specified input `hq`](hyp:hq), [the specified input `j`](hyp:j). -/
lemma pairMarkedRate_sum (n d : ℕ) (q σ z p : ℝ)
    (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (hσ : σ = -1 ∨ σ = 1) (hz : z = -1 ∨ z = 1) (hp : 0 ≤ p)
    (j : Fin (pairCount n d)) (base : Bool) :
    (∑ o : Obs d, (pairMarkedRate n d q σ z p hd j base o : ℝ)) =
      8 * (n : ℝ) * p := by
  simp_rw [pairMarkedRate_coe n d q σ z p hd hq hσ hz hp j base]
  exact pairMarkedIntensity_sum n d q σ z p hd j base

-- @node: pairMarkedRate_factorial_tsum
/-- The raw factorial count series for one oriented marked pair sums to the
exponential of its total rate. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `z`](hyp:z), [the specified input `p`](hyp:p), [the specified input `hd`](hyp:hd), [the specified input `hz`](hyp:hz), [the specified input `hp`](hyp:hp), [the specified input `base`](hyp:base), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ), [the specified input `hσ`](hyp:hσ). Given [the specified input `hq`](hyp:hq), [the specified input `j`](hyp:j). -/
lemma pairMarkedRate_factorial_tsum (n d : ℕ) (q σ z p : ℝ)
    (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (hσ : σ = -1 ∨ σ = 1) (hz : z = -1 ∨ z = 1) (hp : 0 ≤ p)
    (j : Fin (pairCount n d)) (base : Bool) :
    (∑' counts : Obs d → ℕ, ∏ o : Obs d,
      (pairMarkedRate n d q σ z p hd j base o : ℝ) ^ counts o /
        (counts o).factorial) = Real.exp (8 * (n : ℝ) * p) := by
  rw [factorial_countVector_tsum_eq_exp_sum,
    pairMarkedRate_sum n d q σ z p hd hq hσ hz hp j base]

-- @node: pairSideMarkedRate
/-- Nonnegative marked rate carried by one side label of a pair. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `z`](hyp:z), [the specified input `p`](hyp:p), [the specified input `hd`](hyp:hd), [the specified input `base`](hyp:base), [the specified input `side`](hyp:side), [the specified input `o`](hyp:o), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ). Given [the specified input `j`](hyp:j). -/
noncomputable def pairSideMarkedRate (n d : ℕ) (q σ z p : ℝ)
    (hd : 1 ≤ d) (j : Fin (pairCount n d)) (base side : Bool)
    (o : Obs d) : ℝ≥0 :=
  Real.toNNReal (if o.X = pairLabel n d hd j side then
    4 * (n : ℝ) * p *
      pairObservedCoeff q σ z (if base == side then 1 else -1) o else 0)

-- @node: pairSideMarkedRate_coe
/-- A legal pair-side marked rate coerces to its explicit real intensity. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `z`](hyp:z), [the specified input `p`](hyp:p), [the specified input `hd`](hyp:hd), [the specified input `hz`](hyp:hz), [the specified input `hp`](hyp:hp), [the specified input `base`](hyp:base), [the specified input `side`](hyp:side), [the specified input `o`](hyp:o), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ), [the specified input `hσ`](hyp:hσ). Given [the specified input `hq`](hyp:hq), [the specified input `j`](hyp:j). -/
lemma pairSideMarkedRate_coe (n d : ℕ) (q σ z p : ℝ)
    (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (hσ : σ = -1 ∨ σ = 1) (hz : z = -1 ∨ z = 1) (hp : 0 ≤ p)
    (j : Fin (pairCount n d)) (base side : Bool) (o : Obs d) :
    (pairSideMarkedRate n d q σ z p hd j base side o : ℝ) =
      if o.X = pairLabel n d hd j side then
        4 * (n : ℝ) * p *
          pairObservedCoeff q σ z (if base == side then 1 else -1) o else 0 := by
  apply Real.coe_toNNReal
  by_cases ho : o.X = pairLabel n d hd j side
  · rw [if_pos ho]
    have hu : (if base == side then (1 : ℝ) else -1) = -1 ∨
        (if base == side then (1 : ℝ) else -1) = 1 := by
      by_cases h : base == side <;> simp [h]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) hp)
      (pairObservedCoeff_nonneg q σ z
        (if base == side then 1 else -1) o hq hσ hz hu)
  · rw [if_neg ho]

-- @node: pairSideMarkedRate_sum
/-- One pair-side marked rate has total mass `4 * n * p`. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `z`](hyp:z), [the specified input `p`](hyp:p), [the specified input `hd`](hyp:hd), [the specified input `hz`](hyp:hz), [the specified input `hp`](hyp:hp), [the specified input `base`](hyp:base), [the specified input `side`](hyp:side), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ), [the specified input `hσ`](hyp:hσ). Given [the specified input `hq`](hyp:hq), [the specified input `j`](hyp:j). -/
lemma pairSideMarkedRate_sum (n d : ℕ) (q σ z p : ℝ)
    (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (hσ : σ = -1 ∨ σ = 1) (hz : z = -1 ∨ z = 1) (hp : 0 ≤ p)
    (j : Fin (pairCount n d)) (base side : Bool) :
    (∑ o : Obs d,
      (pairSideMarkedRate n d q σ z p hd j base side o : ℝ)) =
      4 * (n : ℝ) * p := by
  simp_rw [pairSideMarkedRate_coe n d q σ z p hd hq hσ hz hp j base side]
  calc
    _ = 4 * (n : ℝ) * p *
        (∑ o : Obs d, if o.X = pairLabel n d hd j side then
          pairObservedCoeff q σ z (if base == side then 1 else -1) o else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro o _
      split_ifs <;> ring
    _ = _ := by rw [sum_pairObservedCoeff_at_label]; ring

-- @node: poissonFactor_extract_exponential
/-- A finite Poisson product separates into its common exponential and raw
power/factorial factors, even when restricted to a decidable subset. Given [the specified input `rate`](hyp:rate), [the specified input `counts`](hyp:counts), [the specified input `keep`](hyp:keep), [the stated mathematical conclusion holds](goal). Given [the specified input `α`](hyp:α). -/
lemma poissonFactor_extract_exponential {α : Type*} [Fintype α]
    (rate : α → ℝ) (counts : α → ℕ) (keep : α → Prop) [DecidablePred keep] :
    (∏ a : α, if keep a then
        Real.exp (-rate a) * rate a ^ counts a / (counts a).factorial else 1) =
      Real.exp (-(∑ a : α, if keep a then rate a else 0)) *
        ∏ a : α, if keep a then
          rate a ^ counts a / (counts a).factorial else 1 := by
  rw [show (∏ a : α, if keep a then
      Real.exp (-rate a) * rate a ^ counts a / (counts a).factorial else 1) =
      (∏ a : α, Real.exp (-(if keep a then rate a else 0))) *
        ∏ a : α, if keep a then
          rate a ^ counts a / (counts a).factorial else 1 by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro a _
    by_cases h : keep a <;> simp [h]
    ring]
  rw [← Real.exp_sum]
  congr 2
  rw [← Finset.sum_neg_distrib]

-- @node: fillerMass_nonneg
/-- The filler mass is nonnegative at every positive sample size. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hn`](hyp:hn), [the stated mathematical conclusion holds](goal). -/
lemma fillerMass_nonneg (n d : ℕ) (hn : 1 ≤ n) : 0 ≤ fillerMass n d := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hL := ell_pos_for_normalization n
  have hK := priorK_lower_for_normalization n
  have hKpos : (0 : ℝ) < priorK n := by linarith
  have hM : (pairCount n d : ℝ) ≤ (n : ℝ) * ell n := by
    have hm : pairCount n d ≤ Nat.floor ((n : ℝ) * ell n) := by
      unfold pairCount
      exact min_le_right _ _
    have hf : ((Nat.floor ((n : ℝ) * ell n) : ℕ) : ℝ) ≤ (n : ℝ) * ell n :=
      Nat.floor_le (le_of_lt (mul_pos hnpos hL))
    exact (Nat.cast_le.mpr hm).trans hf
  have hbound : 8 * (pairCount n d : ℝ) ≤ (n : ℝ) * priorK n := by
    nlinarith [mul_nonneg (le_of_lt hnpos) (sub_nonneg.mpr hK)]
  have hsmall : (pairCount n d : ℝ) / (512 * n * priorK n) < 1 := by
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith
  have hrewrite :
      2 * (pairCount n d : ℝ) * priorH n * priorB n =
        (pairCount n d : ℝ) / (512 * n * priorK n) := by
    unfold priorH priorB
    field_simp
    <;> ring
  unfold fillerMass
  rw [hrewrite]
  linarith

-- @node: fillerObservedCoeff_nonneg
/-- Every legal filler observed-mark coefficient is nonnegative. Given [the specified input `q`](hyp:q), [the specified input `o`](hyp:o), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
lemma fillerObservedCoeff_nonneg (q : ℝ) (o : Obs d)
    (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) :
    0 ≤ fillerObservedCoeff q o := by
  have hb := baseMean_mem_unit q hq
  rcases hb with ⟨hb0, hb1⟩
  unfold fillerObservedCoeff
  split_ifs <;> nlinarith

-- @node: fillerMarkedRate
/-- Nonnegative-real packaging of the filler-label marked rate. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hd`](hyp:hd), [the specified input `o`](hyp:o), [the stated mathematical conclusion holds](goal). -/
noncomputable def fillerMarkedRate (n d : ℕ) (q : ℝ) (hd : 1 ≤ d)
    (o : Obs d) : ℝ≥0 :=
  Real.toNNReal (if o.X = fillerLabel d hd then
    4 * (n : ℝ) * (fillerMass n d * fillerObservedCoeff q o) else 0)

-- @node: fillerMarkedRate_coe
/-- A legal filler marked rate coerces to its explicit real intensity. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hd`](hyp:hd), [the specified input `o`](hyp:o), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
lemma fillerMarkedRate_coe (n d : ℕ) (q : ℝ) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) (o : Obs d) :
    (fillerMarkedRate n d q hd o : ℝ) =
      if o.X = fillerLabel d hd then
        4 * (n : ℝ) * (fillerMass n d * fillerObservedCoeff q o) else 0 := by
  apply Real.coe_toNNReal
  by_cases ho : o.X = fillerLabel d hd
  · rw [if_pos ho]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (Nat.cast_nonneg n))
      (mul_nonneg (fillerMass_nonneg n d hn)
        (fillerObservedCoeff_nonneg q o hq))
  · rw [if_neg ho]

-- @node: fillerMarkedRate_sum
/-- Filler marked rates have total mass `4 * n * fillerMass`. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hd`](hyp:hd), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
lemma fillerMarkedRate_sum (n d : ℕ) (q : ℝ) (hn : 1 ≤ n) (hd : 1 ≤ d)
    (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) :
    (∑ o : Obs d, (fillerMarkedRate n d q hd o : ℝ)) =
      4 * (n : ℝ) * fillerMass n d := by
  simp_rw [fillerMarkedRate_coe n d q hn hd hq]
  calc
    _ = 4 * (n : ℝ) * fillerMass n d *
        (∑ o : Obs d, if o.X = fillerLabel d hd then
          fillerObservedCoeff q o else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro o _
      split_ifs <;> ring
    _ = _ := by rw [sum_fillerObservedCoeff_at_label]; ring

-- @node: fillerMarkedPoissonFactor_eq
/-- The normalized local filler Poisson factor equals its raw likelihood times
the exponential of the negative filler rate. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hd`](hyp:hd), [the specified input `counts`](hyp:counts), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
lemma fillerMarkedPoissonFactor_eq (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d)
    (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) (counts : Obs d → ℕ) :
    (∏ o : Obs d, if o.X = fillerLabel d hd then
      Real.exp (-(fillerMarkedRate n d q hd o : ℝ)) *
        (fillerMarkedRate n d q hd o : ℝ) ^ counts o /
          (counts o).factorial else 1) =
      Real.exp (-4 * (n : ℝ) * fillerMass n d) *
        ∏ o : Obs d, if o.X = fillerLabel d hd then
          (4 * (n : ℝ) * (fillerMass n d * fillerObservedCoeff q o)) ^ counts o /
            (counts o).factorial else 1 := by
  rw [poissonFactor_extract_exponential
    (fun o => (fillerMarkedRate n d q hd o : ℝ)) counts
    (fun o => o.X = fillerLabel d hd)]
  congr 1
  · apply congrArg Real.exp
    have hsum := fillerMarkedRate_sum n d q hn hd hq
    have hrestricted :
        (∑ o : Obs d, if o.X = fillerLabel d hd then
          (fillerMarkedRate n d q hd o : ℝ) else 0) =
          ∑ o : Obs d, (fillerMarkedRate n d q hd o : ℝ) := by
      apply Finset.sum_congr rfl
      intro o _
      by_cases ho : o.X = fillerLabel d hd
      · simp [ho]
      · rw [fillerMarkedRate_coe n d q hn hd hq o]
        simp [ho]
    rw [hrestricted, hsum]
    ring
  · apply Finset.prod_congr rfl
    intro o _
    by_cases ho : o.X = fillerLabel d hd
    · simp only [ho, ↓reduceIte]
      rw [fillerMarkedRate_coe n d q hn hd hq o, if_pos ho]
    · simp [ho]


end CausalSmith.Stat.MarNearcompleteFrontier
