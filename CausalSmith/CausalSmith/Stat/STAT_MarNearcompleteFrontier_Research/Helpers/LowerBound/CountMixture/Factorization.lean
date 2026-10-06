module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.LowerBound.CountMixture.MarkedRates

/-! # Factorization for the paired count-mixture comparison -/

@[expose] public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

-- @node: pairLabelFactorial
/-- Product of count factorials at one paired baseline label. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hd`](hyp:hd), [the specified input `side`](hyp:side), [the specified input `counts`](hyp:counts), [the stated mathematical conclusion holds](goal). Given [the specified input `j`](hyp:j). -/
noncomputable def pairLabelFactorial (n d : ℕ) (hd : 1 ≤ d)
    (j : Fin (pairCount n d)) (side : Bool) (counts : Obs d → ℕ) : ℝ :=
  ∏ o : Obs d,
    if o.X = pairLabel n d hd j side then ((counts o).factorial : ℝ) else 1

-- @node: pair_label_poisson_power_factorization
/-- The full power/factorial contribution at one paired label separates into
its scalar pair mass, observed-mark monomial, and count factorials. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hd`](hyp:hd), [the specified input `counts`](hyp:counts), [the specified input `side`](hyp:side), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ), [the specified input `θ`](hyp:θ). Given [the specified input `j`](hyp:j). -/
lemma pair_label_poisson_power_factorization (n d : ℕ) (q σ : ℝ)
    (hd : 1 ≤ d) (θ : Theta n d) (counts : Obs d → ℕ)
    (j : Fin (pairCount n d)) (side : Bool) :
    (∏ o : Obs d, if o.X = pairLabel n d hd j side then
      (4 * (n : ℝ) * countAtomMass n d q σ hd θ o) ^ counts o /
        (counts o).factorial else 1) =
      (4 * (n : ℝ) * latentP n (θ.1 j)) ^
          (∑ o : Obs d,
            if o.X = pairLabel n d hd j side then counts o else 0) *
        pairObservedMonomial q σ (latentZ n (θ.1 j))
          (orientation θ j side) (pairLabel n d hd j side) counts /
        pairLabelFactorial n d hd j side counts := by
  unfold pairLabelFactorial pairObservedMonomial
  rw [show (∏ o : Obs d, if o.X = pairLabel n d hd j side then
      (4 * (n : ℝ) * countAtomMass n d q σ hd θ o) ^ counts o /
        (counts o).factorial else 1) =
      (∏ o : Obs d, if o.X = pairLabel n d hd j side then
        (4 * (n : ℝ) * countAtomMass n d q σ hd θ o) ^ counts o else 1) /
      ∏ o : Obs d, if o.X = pairLabel n d hd j side then
        ((counts o).factorial : ℝ) else 1 by
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro o _
    by_cases ho : o.X = pairLabel n d hd j side <;> simp [ho]]
  congr 1
  rw [← Finset.prod_pow_eq_pow_sum (Finset.univ : Finset (Obs d))
    (fun o => if o.X = pairLabel n d hd j side then counts o else 0)
    (4 * (n : ℝ) * latentP n (θ.1 j)), ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro o _
  by_cases ho : o.X = pairLabel n d hd j side
  · simp only [ho, ↓reduceIte,
      countAtomMass_at_pair_label n d q σ hd θ o j side ho, mul_pow]
    ring
  · simp [ho]

-- @node: pairBlockFactorial
/-- Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hd`](hyp:hd), [the specified input `counts`](hyp:counts), [the stated mathematical conclusion holds](goal). Given [the specified input `j`](hyp:j). -/
noncomputable def pairBlockFactorial (n d : ℕ) (hd : 1 ≤ d)
    (j : Fin (pairCount n d)) (counts : Obs d → ℕ) : ℝ :=
  ∏ side : Bool, pairLabelFactorial n d hd j side counts

-- @node: pair_block_poisson_power_factorization
/-- Multiplying the two labels of one pair combines their scalar mass powers
to `pairBlockCount` and their marks to the pair-block monomial. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hd`](hyp:hd), [the specified input `counts`](hyp:counts), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ), [the specified input `θ`](hyp:θ). Given [the specified input `j`](hyp:j). -/
lemma pair_block_poisson_power_factorization (n d : ℕ) (q σ : ℝ)
    (hd : 1 ≤ d) (θ : Theta n d) (counts : Obs d → ℕ)
    (j : Fin (pairCount n d)) :
    (∏ side : Bool, ∏ o : Obs d,
      if o.X = pairLabel n d hd j side then
        (4 * (n : ℝ) * countAtomMass n d q σ hd θ o) ^ counts o /
          (counts o).factorial else 1) =
      (4 * (n : ℝ) * latentP n (θ.1 j)) ^
          pairBlockCount n d hd counts j *
        (∏ side : Bool,
          pairObservedMonomial q σ (latentZ n (θ.1 j))
            (orientation θ j side) (pairLabel n d hd j side) counts) /
        pairBlockFactorial n d hd j counts := by
  simp_rw [pair_label_poisson_power_factorization n d q σ hd θ counts j]
  unfold pairBlockFactorial pairBlockCount
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]

-- @node: pairMarkedLocalFactor
/-- Factorial likelihood contribution restricted to the two labels of one
marked pair. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `z`](hyp:z), [the specified input `p`](hyp:p), [the specified input `hd`](hyp:hd), [the specified input `base`](hyp:base), [the specified input `counts`](hyp:counts), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ). Given [the specified input `j`](hyp:j). -/
noncomputable def pairMarkedLocalFactor (n d : ℕ) (q σ z p : ℝ)
    (hd : 1 ≤ d) (j : Fin (pairCount n d)) (base : Bool)
    (counts : Obs d → ℕ) : ℝ :=
  ∏ side : Bool, ∏ o : Obs d,
    if o.X = pairLabel n d hd j side then
      pairMarkedIntensity n d q σ z p hd j base o ^ counts o /
        (counts o).factorial else 1

-- @node: pairMarkedLocalFactor_eq
/-- The local marked-pair factorial likelihood is the scalar pair-count power
times its observed-mark monomial divided by the block factorial. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `z`](hyp:z), [the specified input `p`](hyp:p), [the specified input `hd`](hyp:hd), [the specified input `base`](hyp:base), [the specified input `counts`](hyp:counts), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ). Given [the specified input `j`](hyp:j). -/
lemma pairMarkedLocalFactor_eq (n d : ℕ) (q σ z p : ℝ)
    (hd : 1 ≤ d) (j : Fin (pairCount n d)) (base : Bool)
    (counts : Obs d → ℕ) :
    pairMarkedLocalFactor n d q σ z p hd j base counts =
      (4 * (n : ℝ) * p) ^ pairBlockCount n d hd counts j *
        (∏ side : Bool,
          pairObservedMonomial q σ z (if base == side then 1 else -1)
            (pairLabel n d hd j side) counts) /
        pairBlockFactorial n d hd j counts := by
  unfold pairMarkedLocalFactor pairBlockFactorial pairBlockCount
  have hlabel (side : Bool) :
      (∏ o : Obs d, if o.X = pairLabel n d hd j side then
        pairMarkedIntensity n d q σ z p hd j base o ^ counts o /
          (counts o).factorial else 1) =
      (4 * (n : ℝ) * p) ^
          (∑ o : Obs d,
            if o.X = pairLabel n d hd j side then counts o else 0) *
        pairObservedMonomial q σ z (if base == side then 1 else -1)
          (pairLabel n d hd j side) counts /
        pairLabelFactorial n d hd j side counts := by
    unfold pairObservedMonomial pairLabelFactorial
    rw [show (∏ o : Obs d, if o.X = pairLabel n d hd j side then
        pairMarkedIntensity n d q σ z p hd j base o ^ counts o /
          (counts o).factorial else 1) =
      (∏ o : Obs d, if o.X = pairLabel n d hd j side then
        pairMarkedIntensity n d q σ z p hd j base o ^ counts o else 1) /
      ∏ o : Obs d, if o.X = pairLabel n d hd j side then
        ((counts o).factorial : ℝ) else 1 by
      rw [← Finset.prod_div_distrib]
      apply Finset.prod_congr rfl
      intro o _
      by_cases ho : o.X = pairLabel n d hd j side <;> simp [ho]]
    congr 1
    rw [← Finset.prod_pow_eq_pow_sum (Finset.univ : Finset (Obs d))
      (fun o => if o.X = pairLabel n d hd j side then counts o else 0)
      (4 * (n : ℝ) * p), ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro o _
    by_cases ho : o.X = pairLabel n d hd j side
    · simp only [ho, ↓reduceIte,
        pairMarkedIntensity_at_label n d q σ z p hd j base side o ho, mul_pow]
    · simp [ho]
  simp_rw [hlabel]
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]

-- @node: half_pairBlockMarkAverage_eq_average_localFactor
/-- The fair orientation-averaged raw block likelihood is exactly the fair
average of the two fixed-base marked local factors. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `z`](hyp:z), [the specified input `p`](hyp:p), [the specified input `hd`](hyp:hd), [the specified input `counts`](hyp:counts), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ). Given [the specified input `j`](hyp:j). -/
lemma half_pairBlockMarkAverage_eq_average_localFactor
    (n d : ℕ) (q σ z p : ℝ) (hd : 1 ≤ d)
    (j : Fin (pairCount n d)) (counts : Obs d → ℕ) :
    (4 * (n : ℝ) * p) ^ pairBlockCount n d hd counts j /
        pairBlockFactorial n d hd j counts *
      ((1 / 2 : ℝ) * pairBlockMarkAverage n d q σ z hd j counts) =
      ∑ base : Bool, (1 / 2 : ℝ) *
        pairMarkedLocalFactor n d q σ z p hd j base counts := by
  simp_rw [pairMarkedLocalFactor_eq n d q σ z p hd j]
  unfold pairBlockMarkAverage
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro base _
  ring

-- @node: pairSidePoissonFactor_eq
/-- The normalized Poisson factor on one side of a marked pair is its raw
marked likelihood times the exponential of the side's total rate. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `z`](hyp:z), [the specified input `p`](hyp:p), [the specified input `hd`](hyp:hd), [the specified input `hz`](hyp:hz), [the specified input `hp`](hyp:hp), [the specified input `base`](hyp:base), [the specified input `side`](hyp:side), [the specified input `counts`](hyp:counts), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ), [the specified input `hσ`](hyp:hσ). Given [the specified input `hq`](hyp:hq), [the specified input `j`](hyp:j). -/
lemma pairSidePoissonFactor_eq (n d : ℕ) (q σ z p : ℝ)
    (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (hσ : σ = -1 ∨ σ = 1) (hz : z = -1 ∨ z = 1) (hp : 0 ≤ p)
    (j : Fin (pairCount n d)) (base side : Bool) (counts : Obs d → ℕ) :
    (∏ o : Obs d, if o.X = pairLabel n d hd j side then
      Real.exp (-(pairSideMarkedRate n d q σ z p hd j base side o : ℝ)) *
        (pairSideMarkedRate n d q σ z p hd j base side o : ℝ) ^ counts o /
          (counts o).factorial else 1) =
      Real.exp (-4 * (n : ℝ) * p) *
        ∏ o : Obs d, if o.X = pairLabel n d hd j side then
          pairMarkedIntensity n d q σ z p hd j base o ^ counts o /
            (counts o).factorial else 1 := by
  rw [poissonFactor_extract_exponential
    (fun o => (pairSideMarkedRate n d q σ z p hd j base side o : ℝ))
    counts (fun o => o.X = pairLabel n d hd j side)]
  congr 1
  · apply congrArg Real.exp
    have hsum := pairSideMarkedRate_sum n d q σ z p hd hq hσ hz hp j base side
    have hrestricted :
        (∑ o : Obs d, if o.X = pairLabel n d hd j side then
          (pairSideMarkedRate n d q σ z p hd j base side o : ℝ) else 0) =
          ∑ o : Obs d,
            (pairSideMarkedRate n d q σ z p hd j base side o : ℝ) := by
      apply Finset.sum_congr rfl
      intro o _
      by_cases ho : o.X = pairLabel n d hd j side
      · simp [ho]
      · rw [pairSideMarkedRate_coe n d q σ z p hd hq hσ hz hp j base side o]
        simp [ho]
    rw [hrestricted, hsum]
    ring
  · apply Finset.prod_congr rfl
    intro o _
    by_cases ho : o.X = pairLabel n d hd j side
    · simp only [ho, beq_self_eq_true, ↓reduceIte]
      rw [pairSideMarkedRate_coe n d q σ z p hd hq hσ hz hp j base side o,
        if_pos ho,
        pairMarkedIntensity_at_label n d q σ z p hd j base side o ho]
    · simp [ho]

-- @node: pairMarkedPoissonFactor_eq
/-- Multiplying the two normalized side factors yields the normalized marked
pair likelihood with total exponential rate `8 * n * p`. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `z`](hyp:z), [the specified input `p`](hyp:p), [the specified input `hd`](hyp:hd), [the specified input `hz`](hyp:hz), [the specified input `hp`](hyp:hp), [the specified input `base`](hyp:base), [the specified input `counts`](hyp:counts), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ), [the specified input `hσ`](hyp:hσ). Given [the specified input `hq`](hyp:hq), [the specified input `j`](hyp:j). -/
lemma pairMarkedPoissonFactor_eq (n d : ℕ) (q σ z p : ℝ)
    (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (hσ : σ = -1 ∨ σ = 1) (hz : z = -1 ∨ z = 1) (hp : 0 ≤ p)
    (j : Fin (pairCount n d)) (base : Bool) (counts : Obs d → ℕ) :
    (∏ side : Bool, ∏ o : Obs d,
      if o.X = pairLabel n d hd j side then
        Real.exp (-(pairSideMarkedRate n d q σ z p hd j base side o : ℝ)) *
          (pairSideMarkedRate n d q σ z p hd j base side o : ℝ) ^ counts o /
            (counts o).factorial else 1) =
      Real.exp (-8 * (n : ℝ) * p) *
        pairMarkedLocalFactor n d q σ z p hd j base counts := by
  simp_rw [pairSidePoissonFactor_eq n d q σ z p hd hq hσ hz hp j base]
  unfold pairMarkedLocalFactor
  rw [Finset.prod_mul_distrib, ← Real.exp_sum]
  congr 2
  norm_num
  ring

-- @node: pairMixtureFactor
/-- One pair's latent-and-orientation averaged marked-Poisson likelihood factor. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hd`](hyp:hd), [the specified input `counts`](hyp:counts), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ). Given [the specified input `j`](hyp:j). -/
noncomputable def pairMixtureFactor (n d : ℕ) (q σ : ℝ) (hd : 1 ≤ d)
    (j : Fin (pairCount n d)) (counts : Obs d → ℕ) : ℝ :=
  ∑ z : Latent n, latentWeight n z *
    (Real.exp (-8 * (n : ℝ) * latentP n z) *
      (4 * (n : ℝ) * latentP n z) ^ pairBlockCount n d hd counts j /
        pairBlockFactorial n d hd j counts *
      ((1 / 2 : ℝ) *
        pairBlockMarkAverage n d q σ (latentZ n z) hd j counts))

-- @node: pairMixtureFactor_nonneg
/-- Every legal one-pair averaged marked-Poisson likelihood factor is
nonnegative. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hd`](hyp:hd), [the specified input `counts`](hyp:counts), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ), [the specified input `hσ`](hyp:hσ). Given [the specified input `hq`](hyp:hq), [the specified input `j`](hyp:j). -/
lemma pairMixtureFactor_nonneg (n d : ℕ) (q σ : ℝ) (hd : 1 ≤ d)
    (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) (hσ : σ = -1 ∨ σ = 1)
    (j : Fin (pairCount n d)) (counts : Obs d → ℕ) :
    0 ≤ pairMixtureFactor n d q σ hd j counts := by
  unfold pairMixtureFactor
  apply Finset.sum_nonneg
  intro z _
  have hw := latentWeight_nonneg_count n z
  have hp := latentP_nonneg n z
  have hz : latentZ n z = -1 ∨ latentZ n z = 1 := by
    have h := latentZ_abs_one n z
    rw [abs_eq (by norm_num : (0 : ℝ) ≤ 1)] at h
    exact h.elim Or.inr Or.inl
  have hm := (half_pairBlockMarkAverage_mem_unit n d q σ (latentZ n z)
    hd j counts hq hσ hz).1
  have hbase : 0 ≤ 4 * (n : ℝ) * latentP n z := by positivity
  have hpow : 0 ≤ (4 * (n : ℝ) * latentP n z) ^
      pairBlockCount n d hd counts j := pow_nonneg hbase _
  have hfac : 0 ≤ pairBlockFactorial n d hd j counts := by
    unfold pairBlockFactorial pairLabelFactorial
    positivity
  exact mul_nonneg hw (mul_nonneg
    (div_nonneg (mul_nonneg (Real.exp_pos _).le hpow) hfac) hm)

-- @node: theta_pair_likelihood_factorization
/-- Averaging the product of conditional pair-block likelihoods under
`thetaLaw` gives the product of the one-pair mixture factors. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hd`](hyp:hd), [the specified input `counts`](hyp:counts), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ). Given [the specified input `hq`](hyp:hq). -/
lemma theta_pair_likelihood_factorization (n d : ℕ) (q σ : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (counts : Obs d → ℕ) :
    (∑ θ : Theta n d, (thetaLaw n d q hn hd hq θ).toReal *
      ∏ j : Fin (pairCount n d),
        (Real.exp (-8 * (n : ℝ) * latentP n (θ.1 j)) *
          (4 * (n : ℝ) * latentP n (θ.1 j)) ^
              pairBlockCount n d hd counts j /
            pairBlockFactorial n d hd j counts *
          ∏ side : Bool,
            pairObservedMonomial q σ (latentZ n (θ.1 j))
              (orientation θ j side) (pairLabel n d hd j side) counts)) =
      ∏ j : Fin (pairCount n d), pairMixtureFactor n d q σ hd j counts := by
  simp only [orientation]
  rw [thetaLaw_product_factorization n d q hn hd hq
    (fun j z base =>
      Real.exp (-8 * (n : ℝ) * latentP n z) *
        (4 * (n : ℝ) * latentP n z) ^ pairBlockCount n d hd counts j /
          pairBlockFactorial n d hd j counts *
        ∏ side : Bool,
          pairObservedMonomial q σ (latentZ n z)
            (if base == side then 1 else -1)
            (pairLabel n d hd j side) counts)]
  apply Finset.prod_congr rfl
  intro j _
  unfold pairMixtureFactor pairBlockMarkAverage
  apply Finset.sum_congr rfl
  intro z _
  let A : ℝ := Real.exp (-8 * (n : ℝ) * latentP n z) *
    (4 * (n : ℝ) * latentP n z) ^ pairBlockCount n d hd counts j /
      pairBlockFactorial n d hd j counts
  let M : Bool → ℝ := fun base => ∏ side : Bool,
    pairObservedMonomial q σ (latentZ n z)
      (if base == side then 1 else -1) (pairLabel n d hd j side) counts
  change latentWeight n z * (∑ base : Bool, (1 / 2 : ℝ) * (A * M base)) =
    latentWeight n z * (A * ((1 / 2 : ℝ) * ∑ base : Bool, M base))
  congr 1
  calc
    _ = ∑ base : Bool, ((1 / 2 : ℝ) * A) * M base := by
      apply Finset.sum_congr rfl
      intro base _
      ring
    _ = ((1 / 2 : ℝ) * A) * ∑ base : Bool, M base := by
      rw [Finset.mul_sum]
    _ = _ := by ring

-- @node: commonCountFactor
/-- The sign-independent filler and forced-zero contribution to a count-vector
likelihood. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hd`](hyp:hd), [the specified input `counts`](hyp:counts), [the stated mathematical conclusion holds](goal). -/
noncomputable def commonCountFactor (n d : ℕ) (q : ℝ) (hd : 1 ≤ d)
    (counts : Obs d → ℕ) : ℝ :=
  Real.exp (-4 * (n : ℝ) * fillerMass n d) *
    (∏ o : Obs d, if o.X = fillerLabel d hd then
      (4 * (n : ℝ) * (fillerMass n d * fillerObservedCoeff q o)) ^ counts o /
        (counts o).factorial else 1) *
    ∏ x ∈ (Finset.univ \ activeBaselineLabels n d hd),
      ∏ o : Obs d, if o.X = x then (if counts o = 0 then 1 else 0) else 1

-- @node: markedComponent_countVector_tsum_one
/-- Every fixed choice of pair masses, signs, and base orientations gives a
normalized full observed count-vector likelihood. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hd`](hyp:hd), [the specified input `hp`](hyp:hp), [the specified input `hz`](hyp:hz), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ), [the specified input `hσ`](hyp:hσ). Given [the specified input `hq`](hyp:hq), [the specified input `p`](hyp:p), [the specified input `z`](hyp:z), [the specified input `base`](hyp:base). -/
lemma markedComponent_countVector_tsum_one (n d : ℕ) (q σ : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (hσ : σ = -1 ∨ σ = 1)
    (p : Fin (pairCount n d) → ℝ) (z : Fin (pairCount n d) → ℝ)
    (base : Fin (pairCount n d) → Bool)
    (hp : ∀ j, 0 ≤ p j) (hz : ∀ j, z j = -1 ∨ z j = 1) :
    (∑' counts : Obs d → ℕ,
      commonCountFactor n d q hd counts *
        ∏ j : Fin (pairCount n d),
          Real.exp (-8 * (n : ℝ) * p j) *
            pairMarkedLocalFactor n d q σ (z j) (p j) hd j (base j) counts) = 1 := by
  rw [show (∑' counts : Obs d → ℕ, _) =
      ∑' counts : Obs d → ℕ,
        (∏ o : Obs d, if o.X = fillerLabel d hd then
          Real.exp (-(fillerMarkedRate n d q hd o : ℝ)) *
            (fillerMarkedRate n d q hd o : ℝ) ^ counts o /
              (counts o).factorial else 1) *
        (∏ js : Fin (pairCount n d) × Bool, ∏ o : Obs d,
          if o.X = pairLabel n d hd js.1 js.2 then
            Real.exp (-(pairSideMarkedRate n d q σ (z js.1) (p js.1)
              hd js.1 (base js.1) js.2 o : ℝ)) *
              (pairSideMarkedRate n d q σ (z js.1) (p js.1)
                hd js.1 (base js.1) js.2 o : ℝ) ^ counts o /
                (counts o).factorial else 1) *
        ∏ x ∈ (Finset.univ \ activeBaselineLabels n d hd),
          ∏ o : Obs d, if o.X = x then
            (if counts o = 0 then 1 else 0) else 1 by
    apply tsum_congr
    intro counts
    rw [fillerMarkedPoissonFactor_eq n d q hn hd hq counts]
    simp_rw [Fintype.prod_prod_type,
      pairMarkedPoissonFactor_eq n d q σ _ _ hd hq hσ (hz _) (hp _)]
    unfold commonCountFactor
    ring]
  exact partitionedLocalPoisson_countVector_tsum_one n d hd
    (fillerMarkedRate n d q hd)
    (fun j side => pairSideMarkedRate n d q σ (z j) (p j) hd j (base j) side)

-- @node: thetaMarkedComponent_countVector_tsum_one
/-- The fixed latent component used by the paired prior is a normalized full
count-vector likelihood. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hd`](hyp:hd), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ), [the specified input `hσ`](hyp:hσ), [the specified input `θ`](hyp:θ). Given [the specified input `hq`](hyp:hq). -/
lemma thetaMarkedComponent_countVector_tsum_one (n d : ℕ) (q σ : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (hσ : σ = -1 ∨ σ = 1) (θ : Theta n d) :
    (∑' counts : Obs d → ℕ,
      commonCountFactor n d q hd counts *
        ∏ j : Fin (pairCount n d),
          Real.exp (-8 * (n : ℝ) * latentP n (θ.1 j)) *
            pairMarkedLocalFactor n d q σ (latentZ n (θ.1 j))
              (latentP n (θ.1 j)) hd j (θ.2 j) counts) = 1 := by
  apply markedComponent_countVector_tsum_one n d q σ hn hd hq hσ
  · intro j
    exact latentP_nonneg n (θ.1 j)
  · intro j
    have h := latentZ_abs_one n (θ.1 j)
    rw [abs_eq (by norm_num : (0 : ℝ) ≤ 1)] at h
    exact h.elim Or.inr Or.inl

-- @node: conditional_count_likelihood_block_split
/-- A conditional likelihood splits into a common filler/zero-rate factor and
one marked-Poisson factor for each active pair. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hd`](hyp:hd), [the specified input `counts`](hyp:counts), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ), [the specified input `θ`](hyp:θ). -/
lemma conditional_count_likelihood_block_split (n d : ℕ) (q σ : ℝ)
    (hd : 1 ≤ d) (θ : Theta n d) (counts : Obs d → ℕ) :
    Real.exp (-4 * (n : ℝ) * normalizationJ n d θ) *
        (∏ o : Obs d,
          (4 * (n : ℝ) * countAtomMass n d q σ hd θ o) ^ counts o /
            (counts o).factorial) =
      commonCountFactor n d q hd counts *
        ∏ j : Fin (pairCount n d),
          (Real.exp (-8 * (n : ℝ) * latentP n (θ.1 j)) *
            (4 * (n : ℝ) * latentP n (θ.1 j)) ^
                pairBlockCount n d hd counts j /
              pairBlockFactorial n d hd j counts *
            ∏ side : Bool,
              pairObservedMonomial q σ (latentZ n (θ.1 j))
                (orientation θ j side) (pairLabel n d hd j side) counts) := by
  let g : Obs d → ℝ := fun o =>
    (4 * (n : ℝ) * countAtomMass n d q σ hd θ o) ^ counts o /
      (counts o).factorial
  have hfiller :
      (∏ o : Obs d, if o.X = fillerLabel d hd then g o else 1) =
        ∏ o : Obs d, if o.X = fillerLabel d hd then
          (4 * (n : ℝ) * (fillerMass n d * fillerObservedCoeff q o)) ^ counts o /
            (counts o).factorial else 1 := by
    apply Finset.prod_congr rfl
    intro o _
    by_cases ho : o.X = fillerLabel d hd
    · simp only [ho, ↓reduceIte, g]
      rw [countAtomMass_at_filler_label n d q σ hd θ o ho]
    · simp [ho]
  have hunused (x : Fin d)
      (hx : x ∈ (Finset.univ \ activeBaselineLabels n d hd)) :
      (∏ o : Obs d, if o.X = x then g o else 1) =
        ∏ o : Obs d, if o.X = x then (if counts o = 0 then 1 else 0) else 1 := by
    apply Finset.prod_congr rfl
    intro o _
    by_cases ho : o.X = x
    · simp only [ho, ↓reduceIte, g]
      have hxnot : x ∉ activeBaselineLabels n d hd :=
        (Finset.mem_sdiff.mp hx).2
      have hfill : o.X ≠ fillerLabel d hd := by
        intro h
        apply hxnot
        rw [← ho, h]
        exact Finset.mem_insert_self _ _
      have hp (j : Fin (pairCount n d)) (side : Bool) :
          o.X ≠ pairLabel n d hd j side := by
        intro h
        apply hxnot
        rw [← ho, h]
        apply Finset.mem_insert_of_mem
        exact Finset.mem_image.mpr ⟨(j, side), Finset.mem_univ _, rfl⟩
      rw [countAtomMass_eq_zero_of_unused n d q σ hd θ o hfill hp,
        mul_zero, zero_rate_factor_eq_indicator]
    · simp [ho]
  have hunusedProd :
      (∏ x ∈ (Finset.univ \ activeBaselineLabels n d hd),
        ∏ o : Obs d, if o.X = x then g o else 1) =
      ∏ x ∈ (Finset.univ \ activeBaselineLabels n d hd),
        ∏ o : Obs d, if o.X = x then (if counts o = 0 then 1 else 0) else 1 := by
    apply Finset.prod_congr rfl
    intro x hx
    exact hunused x hx
  have hexp :
      Real.exp (-4 * (n : ℝ) * normalizationJ n d θ) =
        Real.exp (-4 * (n : ℝ) * fillerMass n d) *
          ∏ j : Fin (pairCount n d),
            Real.exp (-8 * (n : ℝ) * latentP n (θ.1 j)) := by
    unfold normalizationJ
    rw [show -4 * (n : ℝ) *
          (fillerMass n d + 2 * ∑ j : Fin (pairCount n d), latentP n (θ.1 j)) =
        -4 * (n : ℝ) * fillerMass n d +
          ∑ j : Fin (pairCount n d), -8 * (n : ℝ) * latentP n (θ.1 j) by
      rw [← Finset.mul_sum]
      ring,
      Real.exp_add, Real.exp_sum]
  change Real.exp (-4 * (n : ℝ) * normalizationJ n d θ) *
      (∏ o : Obs d, g o) = _
  rw [obsProd_split_filler_pairs_unused n d hd g, hfiller]
  rw [hunusedProd]
  rw [Fintype.prod_prod_type]
  simp only [g]
  simp_rw [pair_block_poisson_power_factorization n d q σ hd θ counts]
  have hreorder (j : Fin (pairCount n d)) :
      (4 * (n : ℝ) * latentP n (θ.1 j)) ^ pairBlockCount n d hd counts j *
            (∏ side : Bool,
              pairObservedMonomial q σ (latentZ n (θ.1 j))
                (orientation θ j side) (pairLabel n d hd j side) counts) /
          pairBlockFactorial n d hd j counts =
        ((4 * (n : ℝ) * latentP n (θ.1 j)) ^ pairBlockCount n d hd counts j /
          pairBlockFactorial n d hd j counts) *
            ∏ side : Bool,
              pairObservedMonomial q σ (latentZ n (θ.1 j))
                (orientation θ j side) (pairLabel n d hd j side) counts := by
    ring
  simp_rw [hreorder]
  rw [Finset.prod_mul_distrib]
  rw [hexp]
  unfold commonCountFactor
  rw [Finset.prod_mul_distrib]
  have hreorderExp (j : Fin (pairCount n d)) :
      Real.exp (-8 * (n : ℝ) * latentP n (θ.1 j)) *
            (4 * (n : ℝ) * latentP n (θ.1 j)) ^ pairBlockCount n d hd counts j /
          pairBlockFactorial n d hd j counts =
        Real.exp (-8 * (n : ℝ) * latentP n (θ.1 j)) *
          ((4 * (n : ℝ) * latentP n (θ.1 j)) ^ pairBlockCount n d hd counts j /
            pairBlockFactorial n d hd j counts) := by
    ring
  simp_rw [hreorderExp]
  rw [Finset.prod_mul_distrib]
  ring


end CausalSmith.Stat.MarNearcompleteFrontier
