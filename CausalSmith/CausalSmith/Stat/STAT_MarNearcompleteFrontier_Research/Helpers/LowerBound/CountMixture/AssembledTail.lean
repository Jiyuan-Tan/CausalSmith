module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.LowerBound.CountMixture.ProductSummation

/-! # Assembly of independent count blocks

Split a count vector into its disjoint pair blocks and its common residual
block. This injection transfers the normalized product L1 bound to the
original count alphabet without counting any atom twice.
-/

@[expose] public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory ProbabilityTheory
open Causalean.Stat
open Causalean.Stat.Concentration.Poisson
open Causalean.Mathlib.Analysis.Normed.Ring.InfiniteSum
open scoped ENNReal NNReal

-- @node: pairCountRestriction
/-- Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hd`](hyp:hd), [the specified input `counts`](hyp:counts), [the specified input `o`](hyp:o), [the stated mathematical conclusion holds](goal). Given [the specified input `j`](hyp:j). -/
noncomputable def pairCountRestriction (n d : ℕ) (hd : 1 ≤ d)
    (counts : Obs d → ℕ) (j : Fin (pairCount n d)) (o : Obs d) : ℕ := by
  classical
  exact if ∃ side : Bool, o.X = pairLabel n d hd j side then counts o else 0

-- @node: residualCountRestriction
/-- Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hd`](hyp:hd), [the specified input `counts`](hyp:counts), [the specified input `o`](hyp:o), [the stated mathematical conclusion holds](goal). -/
noncomputable def residualCountRestriction (n d : ℕ) (hd : 1 ≤ d)
    (counts : Obs d → ℕ) (o : Obs d) : ℕ := by
  classical
  exact if ∃ j : Fin (pairCount n d), ∃ side : Bool, o.X = pairLabel n d hd j side
    then 0 else counts o

-- @node: splitCountBlocks_injective
/-- Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hd`](hyp:hd), [the stated mathematical conclusion holds](goal). -/
lemma splitCountBlocks_injective (n d : ℕ) (hd : 1 ≤ d) :
    Function.Injective (fun counts : Obs d → ℕ =>
      (residualCountRestriction n d hd counts, pairCountRestriction n d hd counts)) := by
  classical
  intro a b h
  funext o
  by_cases hp : ∃ j : Fin (pairCount n d), ∃ side : Bool, o.X = pairLabel n d hd j side
  · obtain ⟨j, side, hs⟩ := hp
    have hj := congrFun (congrFun (congrArg Prod.snd h) j) o
    simpa [pairCountRestriction, show ∃ side : Bool, o.X = pairLabel n d hd j side from ⟨side, hs⟩] using hj
  · have hr := congrFun (congrArg Prod.fst h) o
    simpa only [residualCountRestriction, if_neg hp] using hr

/-- Restricting the count vector to its pair does not alter the local factor. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hd`](hyp:hd), [the specified input `counts`](hyp:counts), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ). Given [the specified input `j`](hyp:j). -/
-- @node: pairMixtureFactor_restrict
lemma pairMixtureFactor_restrict (n d : ℕ) (q σ : ℝ) (hd : 1 ≤ d)
    (j : Fin (pairCount n d)) (counts : Obs d → ℕ) :
    pairMixtureFactor n d q σ hd j (pairCountRestriction n d hd counts j) =
      pairMixtureFactor n d q σ hd j counts := by
  classical
  have he (side : Bool) (o : Obs d) (ho : o.X = pairLabel n d hd j side) :
      pairCountRestriction n d hd counts j o = counts o := by
    simp [pairCountRestriction, show ∃ side : Bool, o.X = pairLabel n d hd j side from ⟨side, ho⟩]
  have hc : pairBlockCount n d hd (pairCountRestriction n d hd counts j) j =
      pairBlockCount n d hd counts j := by
    unfold pairBlockCount
    apply Finset.sum_congr rfl
    intro side _
    apply Finset.sum_congr rfl
    intro o _
    by_cases ho : o.X = pairLabel n d hd j side <;> simp [ho, he side o]
  have hf : pairBlockFactorial n d hd j (pairCountRestriction n d hd counts j) =
      pairBlockFactorial n d hd j counts := by
    unfold pairBlockFactorial pairLabelFactorial
    apply Finset.prod_congr rfl
    intro side _
    apply Finset.prod_congr rfl
    intro o _
    by_cases ho : o.X = pairLabel n d hd j side <;> simp [ho, he side o]
  have hm (z : ℝ) : pairBlockMarkAverage n d q σ z hd j (pairCountRestriction n d hd counts j) =
      pairBlockMarkAverage n d q σ z hd j counts := by
    unfold pairBlockMarkAverage pairObservedMonomial
    apply Finset.sum_congr rfl
    intro base _
    apply Finset.prod_congr rfl
    intro side _
    apply Finset.prod_congr rfl
    intro o _
    by_cases ho : o.X = pairLabel n d hd j side <;> simp [ho, he side o]
  unfold pairMixtureFactor
  simp_rw [hc, hf, hm]

-- @node: pairMarkedMixtureFactor_restrict
/-- Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hd`](hyp:hd), [the specified input `counts`](hyp:counts), [the stated mathematical conclusion holds](goal). Given [the specified input `σ`](hyp:σ). Given [the specified input `j`](hyp:j). -/
lemma pairMarkedMixtureFactor_restrict (n d : ℕ) (q σ : ℝ) (hd : 1 ≤ d)
    (j : Fin (pairCount n d)) (counts : Obs d → ℕ) :
    pairMarkedMixtureFactor n d q σ hd j (pairCountRestriction n d hd counts j) =
      pairMixtureFactor n d q σ hd j counts := by
  classical
  rw [pairMarkedMixtureFactor_eq_local_of_supported]
  · exact pairMixtureFactor_restrict n d q σ hd j counts
  · intro o ho
    simp [pairCountRestriction, not_exists.mpr ho]

/-- The residual restriction carries the filler likelihood and all forced
zeros on unused labels, exactly the common factor in the full experiment. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hd`](hyp:hd), [the specified input `counts`](hyp:counts), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
-- @node: residualPoissonFactor_eq_common
lemma residualPoissonFactor_eq_common (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (counts : Obs d → ℕ) :
    (∏ o : Obs d, Real.exp (-(fillerMarkedRate n d q hd o : ℝ)) *
      (fillerMarkedRate n d q hd o : ℝ) ^ residualCountRestriction n d hd counts o /
        (residualCountRestriction n d hd counts o).factorial) =
      commonCountFactor n d q hd counts := by
  classical
  have hfill (o : Obs d) (ho : o.X = fillerLabel d hd) :
      residualCountRestriction n d hd counts o = counts o := by
    have hp : ¬ ∃ j : Fin (pairCount n d), ∃ side : Bool, o.X = pairLabel n d hd j side := by
      rintro ⟨j, side, h⟩
      exact fillerLabel_ne_pairLabel n d hd j side (ho.symm.trans h)
    simp only [residualCountRestriction, if_neg hp]
  have hpair (j : Fin (pairCount n d)) (side : Bool) (o : Obs d)
      (ho : o.X = pairLabel n d hd j side) :
      residualCountRestriction n d hd counts o = 0 := by
    simp only [residualCountRestriction, if_pos (show ∃ j : Fin (pairCount n d), ∃ side : Bool,
      o.X = pairLabel n d hd j side from ⟨j, side, ho⟩)]
  have hunused (x : Fin d) (hx : x ∈ Finset.univ \ activeBaselineLabels n d hd)
      (o : Obs d) (ho : o.X = x) :
      residualCountRestriction n d hd counts o = counts o ∧ o.X ≠ fillerLabel d hd := by
    have hxnot := (Finset.mem_sdiff.mp hx).2
    have hp : ¬ ∃ j : Fin (pairCount n d), ∃ side : Bool, o.X = pairLabel n d hd j side := by
      rintro ⟨j, side, hs⟩
      apply hxnot
      unfold activeBaselineLabels
      apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr ⟨(j, side), Finset.mem_univ _, (ho.symm.trans hs).symm⟩
    constructor
    · simp only [residualCountRestriction, if_neg hp]
    · intro hf
      apply hxnot
      rw [← ho, hf]
      exact Finset.mem_insert_self _ _
  rw [obsProd_split_filler_pairs_unused n d hd]
  have hf : (∏ o : Obs d, if o.X = fillerLabel d hd then
      Real.exp (-(fillerMarkedRate n d q hd o : ℝ)) *
        (fillerMarkedRate n d q hd o : ℝ) ^ residualCountRestriction n d hd counts o /
          (residualCountRestriction n d hd counts o).factorial else 1) =
      Real.exp (-4 * (n : ℝ) * fillerMass n d) *
        ∏ o : Obs d, if o.X = fillerLabel d hd then
          (4 * (n : ℝ) * (fillerMass n d * fillerObservedCoeff q o)) ^ counts o /
            (counts o).factorial else 1 := by
    rw [← fillerMarkedPoissonFactor_eq n d q hn hd hq counts]
    apply Finset.prod_congr rfl
    intro o _
    by_cases ho : o.X = fillerLabel d hd <;> simp [ho, hfill o]
  rw [hf]
  have hp : (∏ js : Fin (pairCount n d) × Bool, ∏ o : Obs d,
      if o.X = pairLabel n d hd js.1 js.2 then
        Real.exp (-(fillerMarkedRate n d q hd o : ℝ)) *
          (fillerMarkedRate n d q hd o : ℝ) ^ residualCountRestriction n d hd counts o /
            (residualCountRestriction n d hd counts o).factorial else 1) = 1 := by
    apply Finset.prod_eq_one
    intro js _
    apply Finset.prod_eq_one
    intro o _
    by_cases ho : o.X = pairLabel n d hd js.1 js.2
    · have hne : o.X ≠ fillerLabel d hd := by
        rw [ho]; exact (fillerLabel_ne_pairLabel n d hd js.1 js.2).symm
      simp only [if_pos ho, hpair js.1 js.2 o ho, fillerMarkedRate_coe n d q hn hd hq o, if_neg hne]
      norm_num
    · simp [ho]
  rw [hp, mul_one]
  unfold commonCountFactor
  congr 1
  apply Finset.prod_congr rfl
  intro x hx
  apply Finset.prod_congr rfl
  intro o _
  by_cases ho : o.X = x
  · obtain ⟨hc, hne⟩ := hunused x hx o ho
    simp only [if_pos ho, hc, fillerMarkedRate_coe n d q hn hd hq o, if_neg hne]
    simp [zero_rate_factor_eq_indicator]
  · simp [ho]

/-- The singleton-mass `ℓ¹` discrepancy of the two count mixtures is bounded
by twice the pair count times the unmatched factorial-series tail. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hd`](hyp:hd), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
-- @node: mixedCountLaw_singleton_l1_le_factorial_tail
lemma mixedCountLaw_singleton_l1_le_factorial_tail (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) :
    (∑' counts : Obs d → ℕ,
      |(mixedCountLaw n d q (-1) hn hd hq).real {counts} -
        (mixedCountLaw n d q 1 hn hd hq).real {counts}|) ≤
      2 * (pairCount n d : ℝ) *
        Causalean.Stat.Minimax.MomentMatchedMixture.exponentialSeriesTail
          (priorK n) (16 * (n : ℝ) * priorB n) := by
  classical
  let F : (Obs d → ℕ) → ℝ := fun counts => ∏ o : Obs d,
    Real.exp (-(fillerMarkedRate n d q hd o : ℝ)) *
      (fillerMarkedRate n d q hd o : ℝ) ^ counts o / (counts o).factorial
  let A : (Fin (pairCount n d) → (Obs d → ℕ)) → ℝ := fun counts =>
    ∏ j : Fin (pairCount n d), pairMarkedMixtureFactor n d q (-1) hd j (counts j)
  let B : (Fin (pairCount n d) → (Obs d → ℕ)) → ℝ := fun counts =>
    ∏ j : Fin (pairCount n d), pairMarkedMixtureFactor n d q 1 hd j (counts j)
  have hF := summable_poissonFactorial_countVector (fillerMarkedRate n d q hd)
  have hF0 : ∀ counts, 0 ≤ F counts := by
    intro counts
    exact Finset.prod_nonneg (fun o _ => by positivity)
  have hA := normalized_likelihood_fin_product_hasSum_one (pairCount n d)
    (fun j => pairMarkedMixtureFactor n d q (-1) hd j)
    (fun j => pairMarkedMixtureFactor_hasSum_one n d q (-1) hn hd hq (Or.inl rfl) j)
    (fun j counts => pairMarkedMixtureFactor_nonneg n d q (-1) hd hq (Or.inl rfl) j counts)
  have hB := normalized_likelihood_fin_product_hasSum_one (pairCount n d)
    (fun j => pairMarkedMixtureFactor n d q 1 hd j)
    (fun j => pairMarkedMixtureFactor_hasSum_one n d q 1 hn hd hq (Or.inr rfl) j)
    (fun j counts => pairMarkedMixtureFactor_nonneg n d q 1 hd hq (Or.inr rfl) j counts)
  have hA0 : ∀ counts, 0 ≤ A counts := fun counts => Finset.prod_nonneg
    (fun j _ => pairMarkedMixtureFactor_nonneg n d q (-1) hd hq (Or.inl rfl) j (counts j))
  have hB0 : ∀ counts, 0 ≤ B counts := fun counts => Finset.prod_nonneg
    (fun j _ => pairMarkedMixtureFactor_nonneg n d q 1 hd hq (Or.inr rfl) j (counts j))
  have hgap := normalized_likelihood_abs_gap_summable A B hA.summable hB.summable hA0 hB0
  let G : (Obs d → ℕ) × (Fin (pairCount n d) → (Obs d → ℕ)) → ℝ :=
    fun x => F x.1 * |A x.2 - B x.2|
  have hG : Summable G := hF.mul_of_nonneg hgap hF0 (fun _ => abs_nonneg _)
  have hG0 : ∀ x, 0 ≤ G x := fun x => mul_nonneg (hF0 x.1) (abs_nonneg _)
  calc
    _ = ∑' counts : Obs d → ℕ,
        G (residualCountRestriction n d hd counts, pairCountRestriction n d hd counts) := by
      apply tsum_congr
      intro counts
      rw [mixedCountLaw_singleton_factorization n d q (-1) hn hd hq (Or.inl rfl),
        mixedCountLaw_singleton_factorization n d q 1 hn hd hq (Or.inr rfl)]
      change |commonCountFactor n d q hd counts * _ - commonCountFactor n d q hd counts * _| =
        F (residualCountRestriction n d hd counts) *
          |A (pairCountRestriction n d hd counts) - B (pairCountRestriction n d hd counts)|
      dsimp only [F, A, B]
      rw [residualPoissonFactor_eq_common n d q hn hd hq]
      simp_rw [pairMarkedMixtureFactor_restrict]
      rw [← mul_sub, abs_mul, abs_of_nonneg]
      rw [← residualPoissonFactor_eq_common n d q hn hd hq]
      exact hF0 _
    _ ≤ ∑' x, G x := tsum_comp_le_tsum_of_inj hG hG0 (splitCountBlocks_injective n d hd)
    _ = ∑' counts : Fin (pairCount n d) → (Obs d → ℕ), |A counts - B counts| := by
      rw [← hF.tsum_mul_tsum hgap hG, poissonFactorial_countVector_tsum_one,
        one_mul]
    _ ≤ _ := pairMarkedMixture_product_l1_le_factorial_tail n d q hn hd hq

/-- The two count mixtures differ only through unmatched pair-block degrees;
their total variation is bounded by the pair count times the exponential
series tail from paper equation (35). Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `hd`](hyp:hd), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq). -/
-- @node: mixedCountLaw_tv_le_factorial_tail
lemma mixedCountLaw_tv_le_factorial_tail (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1) :
    Causalean.Stat.tvDist
        (mixedCountLaw n d q (-1) hn hd hq)
        (mixedCountLaw n d q 1 hn hd hq) ≤
      (pairCount n d : ℝ) *
        Causalean.Stat.Minimax.MomentMatchedMixture.exponentialSeriesTail
          (priorK n) (16 * (n : ℝ) * priorB n) := by
  letI : IsProbabilityMeasure (mixedCountLaw n d q (-1) hn hd hq) := by
    constructor
    unfold mixedCountLaw
    rw [Measure.coe_finsetSum, Finset.sum_apply]
    have hc (θ : Theta n d) :
        conditionalCountLaw n d q (-1) hd θ Set.univ = 1 := by
      letI : IsProbabilityMeasure (conditionalCountLaw n d q (-1) hd θ) := by
        unfold conditionalCountLaw
        infer_instance
      exact measure_univ
    simp_rw [Measure.smul_apply, hc, smul_eq_mul, mul_one]
    simpa using (thetaLaw n d q hn hd hq).tsum_coe
  letI : IsProbabilityMeasure (mixedCountLaw n d q 1 hn hd hq) := by
    constructor
    unfold mixedCountLaw
    rw [Measure.coe_finsetSum, Finset.sum_apply]
    have hc (θ : Theta n d) :
        conditionalCountLaw n d q 1 hd θ Set.univ = 1 := by
      letI : IsProbabilityMeasure (conditionalCountLaw n d q 1 hd θ) := by
        unfold conditionalCountLaw
        infer_instance
      exact measure_univ
    simp_rw [Measure.smul_apply, hc, smul_eq_mul, mul_one]
    simpa using (thetaLaw n d q hn hd hq).tsum_coe
  calc
    _ ≤ (1 / 2 : ℝ) * ∑' counts : Obs d → ℕ,
        |(mixedCountLaw n d q (-1) hn hd hq).real {counts} -
          (mixedCountLaw n d q 1 hn hd hq).real {counts}| :=
      tvDist_le_half_tsum_singleton_abs _ _
    _ ≤ (1 / 2 : ℝ) *
        (2 * (pairCount n d : ℝ) *
          Causalean.Stat.Minimax.MomentMatchedMixture.exponentialSeriesTail
            (priorK n) (16 * (n : ℝ) * priorB n)) :=
      mul_le_mul_of_nonneg_left
        (mixedCountLaw_singleton_l1_le_factorial_tail n d q hn hd hq)
        (by norm_num)
    _ = _ := by ring


end CausalSmith.Stat.MarNearcompleteFrontier
