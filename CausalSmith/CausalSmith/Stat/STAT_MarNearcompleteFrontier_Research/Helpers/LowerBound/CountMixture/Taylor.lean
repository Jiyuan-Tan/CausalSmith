module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.LowerBound.CountMixture.Factorization

/-! # Taylor for the paired count-mixture comparison -/

public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory ProbabilityTheory
open Causalean.Stat
open Causalean.Mathlib.Algebra.BigOperators.Ring
open scoped ENNReal NNReal

-- @node: mixedCountLaw_singleton_factorization
/-- The full mixed singleton likelihood is the common filler/zero-rate factor
times the product of the independently averaged pair factors. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hd`](hyp:hd), [the specified input `counts`](hyp:counts), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ), [the specified input `hσ`](hyp:hσ). Given [the specified input `hq`](hyp:hq). -/
lemma mixedCountLaw_singleton_factorization (n d : ℕ) (q σ : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (hσ : σ = -1 ∨ σ = 1) (counts : Obs d → ℕ) :
    (mixedCountLaw n d q σ hn hd hq).real {counts} =
      commonCountFactor n d q hd counts *
        ∏ j : Fin (pairCount n d), pairMixtureFactor n d q σ hd j counts := by
  rw [mixedCountLaw_singleton_likelihood n d q σ hn hd hq hσ counts]
  simp_rw [conditional_count_likelihood_block_split n d q σ hd]
  have hreorder (θ : Theta n d) :
      (thetaLaw n d q hn hd hq θ).toReal *
          (commonCountFactor n d q hd counts *
            ∏ j : Fin (pairCount n d),
              (Real.exp (-8 * (n : ℝ) * latentP n (θ.1 j)) *
                (4 * (n : ℝ) * latentP n (θ.1 j)) ^
                    pairBlockCount n d hd counts j /
                  pairBlockFactorial n d hd j counts *
                ∏ side : Bool,
                  pairObservedMonomial q σ (latentZ n (θ.1 j))
                    (orientation θ j side) (pairLabel n d hd j side) counts)) =
        commonCountFactor n d q hd counts *
          ((thetaLaw n d q hn hd hq θ).toReal *
            ∏ j : Fin (pairCount n d),
              (Real.exp (-8 * (n : ℝ) * latentP n (θ.1 j)) *
                (4 * (n : ℝ) * latentP n (θ.1 j)) ^
                    pairBlockCount n d hd counts j /
                  pairBlockFactorial n d hd j counts *
                ∏ side : Bool,
                  pairObservedMonomial q σ (latentZ n (θ.1 j))
                    (orientation θ j side) (pairLabel n d hd j side) counts)) := by
    ring
  simp_rw [hreorder]
  rw [← Finset.mul_sum]
  congr 1
  exact theta_pair_likelihood_factorization n d q σ hn hd hq counts

-- @node: mixedFactorizedLikelihood_countVector_tsum_one
/-- The factorized mixed likelihood normalizes over every observed count
vector; this is the aggregate Tonelli target for the later Taylor envelope. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hd`](hyp:hd), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ), [the specified input `hσ`](hyp:hσ). Given [the specified input `hq`](hyp:hq). -/
lemma mixedFactorizedLikelihood_countVector_tsum_one (n d : ℕ) (q σ : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (hσ : σ = -1 ∨ σ = 1) :
    (∑' counts : Obs d → ℕ,
      commonCountFactor n d q hd counts *
        ∏ j : Fin (pairCount n d), pairMixtureFactor n d q σ hd j counts) = 1 := by
  letI : IsProbabilityMeasure (mixedCountLaw n d q σ hn hd hq) := by
    constructor
    unfold mixedCountLaw
    rw [Measure.coe_finsetSum, Finset.sum_apply]
    have hc (θ : Theta n d) :
        conditionalCountLaw n d q σ hd θ Set.univ = 1 := by
      letI : IsProbabilityMeasure (conditionalCountLaw n d q σ hd θ) := by
        unfold conditionalCountLaw
        infer_instance
      exact measure_univ
    simp_rw [Measure.smul_apply, hc, smul_eq_mul, mul_one]
    simpa using (thetaLaw n d q hn hd hq).tsum_coe
  simp_rw [← mixedCountLaw_singleton_factorization n d q σ hn hd hq hσ]
  exact probability_real_singleton_tsum (mixedCountLaw n d q σ hn hd hq)

-- @node: pairMixture_product_gap_le_weighted
/-- The product gap between the two experiment signs is bounded by the
weighted pair telescope, retaining all non-target pair likelihood factors. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hd`](hyp:hd), [the specified input `counts`](hyp:counts), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
lemma pairMixture_product_gap_le_weighted (n d : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (counts : Obs d → ℕ) :
    |(∏ j : Fin (pairCount n d), pairMixtureFactor n d q (-1) hd j counts) -
        ∏ j : Fin (pairCount n d), pairMixtureFactor n d q 1 hd j counts| ≤
      weightedProductTelescopeAbs
        (fun j : Fin (pairCount n d) =>
          pairMixtureFactor n d q (-1) hd j counts)
        (fun j : Fin (pairCount n d) =>
          pairMixtureFactor n d q 1 hd j counts)
        Finset.univ.toList := by
  apply abs_fintype_prod_sub_prod_le_weighted
  · intro j
    exact pairMixtureFactor_nonneg n d q (-1) hd hq (Or.inl rfl) j counts
  · intro j
    exact pairMixtureFactor_nonneg n d q 1 hd hq (Or.inr rfl) j counts

-- @node: latent_signed_power_moment_zero
/-- The signed latent mass cancels every power from degree two through the
interpolation-node count. The nonzero first moment is the target signal. Given [the specified input `n`](hyp:n), [the specified input `t`](hyp:t), [the specified input `ht`](hyp:ht), [the specified input `hK`](hyp:hK), [the stated mathematical conclusion holds](goal). -/
lemma latent_signed_power_moment_zero (n t : ℕ)
    (ht : 2 ≤ t) (hK : t ≤ priorK n) :
    (∑ z : Latent n,
      latentWeight n z * latentZ n z * latentP n z ^ t) = 0 := by
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_unique, latentWeight, latentZ, latentP,
    mul_zero, zero_pow (by omega : t ≠ 0), add_zero]
  calc
    (∑ i : Fin (priorK n),
      (priorH n * |signedNodeWeight n i| / interpolationNode n i) *
        (if 0 ≤ signedNodeWeight n i then 1 else -1) *
          (priorB n * interpolationNode n i) ^ t) =
      priorH n * priorB n ^ t *
        (∑ i : Fin (priorK n),
          signedNodeWeight n i * interpolationNode n i ^ (t - 1)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      have hx : interpolationNode n i ≠ 0 :=
        ne_of_gt (latentWeight_node_pos n i)
      have hpow : interpolationNode n i ^ t =
          interpolationNode n i * interpolationNode n i ^ (t - 1) := by
        conv_lhs => rw [show t = (t - 1) + 1 by omega, pow_succ]
        ring
      by_cases hw : 0 ≤ signedNodeWeight n i
      · simp only [if_pos hw, abs_of_nonneg hw]
        rw [mul_pow, hpow]
        field_simp [hx]
      · have hw' : signedNodeWeight n i ≤ 0 := le_of_not_ge hw
        simp only [if_neg hw, abs_of_nonpos hw']
        rw [mul_pow, hpow]
        field_simp [hx]
    _ = 0 := by
      rw [signedNodeWeight_moment_zero n (t - 1) (by omega) (by omega)]
      ring

-- @node: latentZ_eq_neg_one_or_one
/-- Given [the specified input `n`](hyp:n), [the specified input `z`](hyp:z), [the stated mathematical conclusion holds](goal). -/
lemma latentZ_eq_neg_one_or_one (n : ℕ) (z : Latent n) :
    latentZ n z = -1 ∨ latentZ n z = 1 := by
  have h := latentZ_abs_one n z
  rw [abs_eq (by norm_num : (0 : ℝ) ≤ 1)] at h
  exact h.elim Or.inr Or.inl

-- @node: pairBlock_taylor_coefficient_cancel
/-- A one-pair signed likelihood coefficient vanishes whenever its observed
degree plus exponential Taylor degree lies in the matched-moment range. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `r`](hyp:r), [the specified input `t`](hyp:t), [the specified input `q`](hyp:q), [the specified input `hd`](hyp:hd), [the specified input `counts`](hyp:counts), [the specified input `hlo`](hyp:hlo), [the specified input `hhi`](hyp:hhi), [the stated mathematical conclusion holds](goal). Given [the specified input `j`](hyp:j). -/
lemma pairBlock_taylor_coefficient_cancel (n d r t : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (j : Fin (pairCount n d)) (counts : Obs d → ℕ)
    (hlo : 2 ≤ r + t) (hhi : r + t ≤ priorK n) :
    (∑ z : Latent n, latentWeight n z *
      ((-8 * (n : ℝ) * latentP n z) ^ t *
        (4 * (n : ℝ) * latentP n z) ^ r *
        (pairBlockMarkAverage n d q (-1) (latentZ n z) hd j counts -
          pairBlockMarkAverage n d q 1 (latentZ n z) hd j counts))) = 0 := by
  let C : ℝ := pairBlockMarkAverage n d q (-1) 1 hd j counts -
    pairBlockMarkAverage n d q 1 1 hd j counts
  have hgap (z : Latent n) :
      pairBlockMarkAverage n d q (-1) (latentZ n z) hd j counts -
          pairBlockMarkAverage n d q 1 (latentZ n z) hd j counts =
        latentZ n z * C := by
    exact pairBlockMarkAverage_gap_factor n d q (latentZ n z) hd j counts
      (latentZ_eq_neg_one_or_one n z)
  simp_rw [hgap]
  calc
    _ = ((-8 * (n : ℝ)) ^ t * (4 * (n : ℝ)) ^ r * C) *
        ∑ z : Latent n,
          latentWeight n z * latentZ n z * latentP n z ^ (r + t) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      rw [mul_pow, mul_pow, show latentP n z ^ (r + t) =
        latentP n z ^ r * latentP n z ^ t by rw [pow_add]]
      ring
    _ = 0 := by
      rw [latent_signed_power_moment_zero n (r + t) hlo hhi]
      ring

-- @node: pairBlock_low_total_coefficient_cancel
/-- Every Taylor/observed coefficient through the matched degree vanishes:
degrees zero and one use direct mark cancellation, while higher degrees use
the signed latent moments. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `r`](hyp:r), [the specified input `t`](hyp:t), [the specified input `q`](hyp:q), [the specified input `hd`](hyp:hd), [the specified input `counts`](hyp:counts), [the specified input `hr`](hyp:hr), [the specified input `hhi`](hyp:hhi), [the stated mathematical conclusion holds](goal). Given [the specified input `j`](hyp:j). -/
lemma pairBlock_low_total_coefficient_cancel (n d r t : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (j : Fin (pairCount n d)) (counts : Obs d → ℕ)
    (hr : pairBlockCount n d hd counts j = r)
    (hhi : r + t ≤ priorK n) :
    (∑ z : Latent n, latentWeight n z *
      ((-8 * (n : ℝ) * latentP n z) ^ t *
        (4 * (n : ℝ) * latentP n z) ^ r *
        (pairBlockMarkAverage n d q (-1) (latentZ n z) hd j counts -
          pairBlockMarkAverage n d q 1 (latentZ n z) hd j counts))) = 0 := by
  by_cases hlo : 2 ≤ r + t
  · exact pairBlock_taylor_coefficient_cancel n d r t q hd j counts hlo hhi
  · have hsmall : r + t = 0 ∨ r + t = 1 := by omega
    rcases hsmall with hzero | hone
    · have hr0 : r = 0 := by omega
      have hblock : pairBlockCount n d hd counts j = 0 := hr.trans hr0
      have hgap (z : Latent n) :
          pairBlockMarkAverage n d q (-1) (latentZ n z) hd j counts -
            pairBlockMarkAverage n d q 1 (latentZ n z) hd j counts = 0 := by
        rw [pairBlockMarkAverage_degree_zero n d q (latentZ n z) hd j counts hblock]
        ring
      simp_rw [hgap, mul_zero, Finset.sum_const_zero]
    · by_cases hr0 : r = 0
      · have hblock : pairBlockCount n d hd counts j = 0 := hr.trans hr0
        have hgap (z : Latent n) :
            pairBlockMarkAverage n d q (-1) (latentZ n z) hd j counts -
              pairBlockMarkAverage n d q 1 (latentZ n z) hd j counts = 0 := by
          rw [pairBlockMarkAverage_degree_zero n d q (latentZ n z) hd j counts hblock]
          ring
        simp_rw [hgap, mul_zero, Finset.sum_const_zero]
      · have hr1 : r = 1 := by omega
        have hblock : pairBlockCount n d hd counts j = 1 := hr.trans hr1
        have hgap (z : Latent n) :
            pairBlockMarkAverage n d q (-1) (latentZ n z) hd j counts -
              pairBlockMarkAverage n d q 1 (latentZ n z) hd j counts = 0 := by
          rw [pairBlockMarkAverage_degree_one n d q (latentZ n z) hd j counts hblock]
          ring
        simp_rw [hgap, mul_zero, Finset.sum_const_zero]

-- @node: interpolationNode_le_one_count
/-- Given [the specified input `n`](hyp:n), [the stated mathematical conclusion holds](goal). Given [the specified input `i`](hyp:i). -/
lemma interpolationNode_le_one_count (n : ℕ) (i : Fin (priorK n)) :
    interpolationNode n i ≤ 1 := by
  have hh := priorH_le_one_for_normalization n
  have hc := Real.cos_le_one
    ((i : ℝ) * Real.pi / ((priorK n - 1 : ℕ) : ℝ))
  unfold interpolationNode
  nlinarith

-- @node: latentP_le_priorB_count
/-- Given [the specified input `n`](hyp:n), [the specified input `z`](hyp:z), [the stated mathematical conclusion holds](goal). -/
lemma latentP_le_priorB_count (n : ℕ) (z : Latent n) :
    latentP n z ≤ priorB n := by
  cases z with
  | inl i =>
      simp only [latentP]
      exact mul_le_of_le_one_right (by unfold priorB; positivity)
        (interpolationNode_le_one_count n i)
  | inr u =>
      simp only [latentP]
      unfold priorB
      positivity

-- @node: latentWeight_sum_real_count
/-- Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hd`](hyp:hd), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
lemma latentWeight_sum_real_count (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) :
    ∑ z : Latent n, latentWeight n z = 1 := by
  have h := congrArg ENNReal.toReal (latentWeight_sum n d q hn hd hq)
  rw [ENNReal.toReal_sum (fun _ _ => ENNReal.ofReal_ne_top)] at h
  simpa only [ENNReal.toReal_one,
    ENNReal.toReal_ofReal (latentWeight_nonneg_count n _)] using h

-- @node: pairBlock_taylor_coefficient_abs_le
/-- Every one-pair Taylor coefficient has the uniform absolute envelope used
for the unmatched factorial tail. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `r`](hyp:r), [the specified input `t`](hyp:t), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hd`](hyp:hd), [the specified input `counts`](hyp:counts), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq), [the specified input `j`](hyp:j). -/
lemma pairBlock_taylor_coefficient_abs_le (n d r t : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (j : Fin (pairCount n d)) (counts : Obs d → ℕ) :
    |∑ z : Latent n, latentWeight n z *
      ((-8 * (n : ℝ) * latentP n z) ^ t *
        (4 * (n : ℝ) * latentP n z) ^ r *
        (pairBlockMarkAverage n d q (-1) (latentZ n z) hd j counts -
          pairBlockMarkAverage n d q 1 (latentZ n z) hd j counts))| ≤
      2 * (8 * (n : ℝ) * priorB n) ^ t *
        (4 * (n : ℝ) * priorB n) ^ r := by
  calc
    _ ≤ ∑ z : Latent n, |latentWeight n z *
      ((-8 * (n : ℝ) * latentP n z) ^ t *
        (4 * (n : ℝ) * latentP n z) ^ r *
        (pairBlockMarkAverage n d q (-1) (latentZ n z) hd j counts -
          pairBlockMarkAverage n d q 1 (latentZ n z) hd j counts))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _z : Latent n, latentWeight n _z *
        ((8 * (n : ℝ) * priorB n) ^ t *
          (4 * (n : ℝ) * priorB n) ^ r * 2) := by
      apply Finset.sum_le_sum
      intro z _
      have hw := latentWeight_nonneg_count n z
      have hp0 := latentP_nonneg n z
      have hpB := latentP_le_priorB_count n z
      have hgap := pairBlockMarkAverage_gap_le_two n d q (latentZ n z)
        hd j counts hq (latentZ_eq_neg_one_or_one n z)
      rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_pow,
        abs_of_nonneg hw]
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hB0 : 0 ≤ priorB n := by unfold priorB; positivity
      have habsneg : |-8 * (n : ℝ) * latentP n z| =
          8 * (n : ℝ) * latentP n z := by
        rw [abs_of_nonpos]
        · ring
        · exact mul_nonpos_of_nonpos_of_nonneg
            (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hn0) hp0
      have habspos : |4 * (n : ℝ) * latentP n z| =
          4 * (n : ℝ) * latentP n z := by
        rw [abs_of_nonneg]
        exact mul_nonneg (mul_nonneg (by norm_num) hn0) hp0
      rw [habsneg, habspos]
      gcongr
    _ = _ := by
      rw [← Finset.sum_mul, latentWeight_sum_real_count n d q hn hd hq]
      ring

-- @node: pairBlock_taylor_coefficient_marked_envelope
/-- The absolute Taylor coefficient is dominated by a positive envelope that
retains both legal marked likelihoods.  This form can be summed by the marked
component normalization without paying for the number of observed marks. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `r`](hyp:r), [the specified input `t`](hyp:t), [the specified input `q`](hyp:q), [the specified input `hd`](hyp:hd), [the specified input `counts`](hyp:counts), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq), [the specified input `j`](hyp:j). -/
lemma pairBlock_taylor_coefficient_marked_envelope (n d r t : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (j : Fin (pairCount n d)) (counts : Obs d → ℕ) :
    |∑ z : Latent n, latentWeight n z *
      ((-8 * (n : ℝ) * latentP n z) ^ t *
        (4 * (n : ℝ) * latentP n z) ^ r *
        (pairBlockMarkAverage n d q (-1) (latentZ n z) hd j counts -
          pairBlockMarkAverage n d q 1 (latentZ n z) hd j counts))| ≤
      ∑ z : Latent n, latentWeight n z *
        ((8 * (n : ℝ) * latentP n z) ^ t *
          (4 * (n : ℝ) * latentP n z) ^ r *
          (pairBlockMarkAverage n d q (-1) (latentZ n z) hd j counts +
            pairBlockMarkAverage n d q 1 (latentZ n z) hd j counts)) := by
  calc
    _ ≤ ∑ z : Latent n, |latentWeight n z *
        ((-8 * (n : ℝ) * latentP n z) ^ t *
          (4 * (n : ℝ) * latentP n z) ^ r *
          (pairBlockMarkAverage n d q (-1) (latentZ n z) hd j counts -
            pairBlockMarkAverage n d q 1 (latentZ n z) hd j counts))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro z _
      have hw := latentWeight_nonneg_count n z
      have hp := latentP_nonneg n z
      have hz := latentZ_eq_neg_one_or_one n z
      have hmneg := (half_pairBlockMarkAverage_mem_unit n d q (-1)
        (latentZ n z) hd j counts hq (Or.inl rfl) hz).1
      have hmpos := (half_pairBlockMarkAverage_mem_unit n d q 1
        (latentZ n z) hd j counts hq (Or.inr rfl) hz).1
      have hmneg0 : 0 ≤ pairBlockMarkAverage n d q (-1)
          (latentZ n z) hd j counts := by linarith
      have hmpos0 : 0 ≤ pairBlockMarkAverage n d q 1
          (latentZ n z) hd j counts := by linarith
      rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_pow,
        abs_of_nonneg hw]
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have habsneg : |-8 * (n : ℝ) * latentP n z| =
          8 * (n : ℝ) * latentP n z := by
        rw [abs_of_nonpos]
        · ring
        · exact mul_nonpos_of_nonpos_of_nonneg
            (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hn0) hp
      have habspos : |4 * (n : ℝ) * latentP n z| =
          4 * (n : ℝ) * latentP n z := by
        rw [abs_of_nonneg]
        positivity
      rw [habsneg, habspos]
      gcongr
      calc
        |pairBlockMarkAverage n d q (-1) (latentZ n z) hd j counts -
            pairBlockMarkAverage n d q 1 (latentZ n z) hd j counts| =
          |pairBlockMarkAverage n d q (-1) (latentZ n z) hd j counts +
            -pairBlockMarkAverage n d q 1 (latentZ n z) hd j counts| := by ring_nf
        _ ≤ |pairBlockMarkAverage n d q (-1) (latentZ n z) hd j counts| +
            |-pairBlockMarkAverage n d q 1 (latentZ n z) hd j counts| :=
          abs_add_le _ _
        _ = _ := by rw [abs_of_nonneg hmneg0, abs_neg, abs_of_nonneg hmpos0]

-- @node: pairBlock_normalized_taylor_coefficient_marked_envelope
/-- After factorial normalization, a pair Taylor coefficient is dominated by
positive normalized marked-pair factors times the compensating positive
Taylor weight. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `t`](hyp:t), [the specified input `q`](hyp:q), [the specified input `hd`](hyp:hd), [the specified input `counts`](hyp:counts), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq), [the specified input `j`](hyp:j). -/
lemma pairBlock_normalized_taylor_coefficient_marked_envelope
    (n d t : ℕ) (q : ℝ) (hd : 1 ≤ d)
    (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (j : Fin (pairCount n d)) (counts : Obs d → ℕ) :
    |(∑ z : Latent n, latentWeight n z *
      ((-8 * (n : ℝ) * latentP n z) ^ t *
        (4 * (n : ℝ) * latentP n z) ^ pairBlockCount n d hd counts j *
        (pairBlockMarkAverage n d q (-1) (latentZ n z) hd j counts -
          pairBlockMarkAverage n d q 1 (latentZ n z) hd j counts))) /
        (2 * (t.factorial : ℝ) * pairBlockFactorial n d hd j counts)| ≤
      ∑ z : Latent n, latentWeight n z *
        (Real.exp (8 * (n : ℝ) * latentP n z) *
          (8 * (n : ℝ) * latentP n z) ^ t / (t.factorial : ℝ)) *
        (Real.exp (-8 * (n : ℝ) * latentP n z) *
            (∑ base : Bool, (1 / 2 : ℝ) *
              pairMarkedLocalFactor n d q (-1) (latentZ n z) (latentP n z)
                hd j base counts) +
          Real.exp (-8 * (n : ℝ) * latentP n z) *
            (∑ base : Bool, (1 / 2 : ℝ) *
              pairMarkedLocalFactor n d q 1 (latentZ n z) (latentP n z)
                hd j base counts)) := by
  have hfac : 0 < pairBlockFactorial n d hd j counts := by
    unfold pairBlockFactorial pairLabelFactorial
    positivity
  have hden : 0 < 2 * (t.factorial : ℝ) *
      pairBlockFactorial n d hd j counts := by positivity
  rw [abs_div, abs_of_pos hden]
  calc
    _ ≤ (∑ z : Latent n, latentWeight n z *
        ((8 * (n : ℝ) * latentP n z) ^ t *
          (4 * (n : ℝ) * latentP n z) ^ pairBlockCount n d hd counts j *
          (pairBlockMarkAverage n d q (-1) (latentZ n z) hd j counts +
            pairBlockMarkAverage n d q 1 (latentZ n z) hd j counts))) /
        (2 * (t.factorial : ℝ) * pairBlockFactorial n d hd j counts) := by
      apply div_le_div_of_nonneg_right
        (pairBlock_taylor_coefficient_marked_envelope n d
          (pairBlockCount n d hd counts j) t q hd hq j counts)
        hden.le
    _ = _ := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro z _
      rw [← half_pairBlockMarkAverage_eq_average_localFactor
          n d q (-1) (latentZ n z) (latentP n z) hd j counts,
        ← half_pairBlockMarkAverage_eq_average_localFactor
          n d q 1 (latentZ n z) (latentP n z) hd j counts]
      rw [show -8 * (n : ℝ) * latentP n z =
          -(8 * (n : ℝ) * latentP n z) by ring, Real.exp_neg]
      field_simp


end CausalSmith.Stat.MarNearcompleteFrontier
