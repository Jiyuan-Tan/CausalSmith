module
public import CausalSmith.Stat.STAT_DiscreteBudgetvalueCurve_Research.Helpers.JacksonPolynomial
public import Mathlib.Probability.Distributions.Poisson.Basic

/-! The deterministic, auxiliary-randomization-averaged curve estimator. -/

@[expose] public section

namespace CausalSmith.Stat.DiscreteBudgetvalueCurve

open scoped BigOperators NNReal

/-- The empirical observed four-mass vector. -/
noncomputable def empiricalCellVector {n d : ℕ}
    (sample : Fin n → Obs d) (j : Fin d) : Cell → ℝ :=
  fun zeta => (∑ i : Fin n,
    if (sample i).1 = j ∧ (sample i).2.1 = finTwoEquiv zeta.1 ∧
       (sample i).2.2 = finTwoEquiv zeta.2 then (1 : ℝ) else 0) / n

/-- The plug-in threshold process used below the alphabet cutoff. -/
noncomputable def empiricalThresholdProcess {n d : ℕ} (epsilon : ℝ)
    (sample : Fin n → Obs d) (lambda : ℝ) : ℝ :=
  ∑ j, thresholdFunReal epsilon lambda (empiricalCellVector sample j)

/-- The uncapped pilot/evaluation threshold process for one auxiliary draw. -/
noncomputable def auxiliaryThresholdProcess {n d : ℕ} (epsilon : ℝ)
    (sample : Fin n → Obs d) (perm : Equiv.Perm (Fin n))
    (M : ℕ) (marks : Fin n → Bool) (lambda : ℝ) : ℝ :=
  ∑ j : Fin d,
    jacksonCellStatistic epsilon lambda ((n : ℝ) / 8) d
      (fun zeta => markedCellCount sample perm M marks false j zeta)
      (fun zeta => markedCellCount sample perm M marks true j zeta)

/-- The cap event contributes the zero threshold process. -/
noncomputable def cappedThresholdProcess {n d : ℕ} (epsilon : ℝ)
    (sample : Fin n → Obs d) (perm : Equiv.Perm (Fin n))
    (M : ℕ) (marks : Fin n → Bool) (lambda : ℝ) : ℝ :=
  if M ≤ n then auxiliaryThresholdProcess epsilon sample perm M marks lambda else 0

/-- Exact finite average over Poisson count, permutation, and fair marks. -/
noncomputable def averagedThresholdProcess {n d : ℕ} (epsilon : ℝ)
    (sample : Fin n → Obs d) (lambda : ℝ) : ℝ :=
  ∑ M ∈ Finset.range (n + 1),
    ((ProbabilityTheory.poissonMeasure ((n : ℝ≥0) / 4)) {M}).toReal *
      ((∑ perm : Equiv.Perm (Fin n), ∑ marks : Fin n → Bool,
          cappedThresholdProcess epsilon sample perm M marks lambda) /
        ((Fintype.card (Equiv.Perm (Fin n)) : ℝ) *
         (Fintype.card (Fin n → Bool) : ℝ)))

/-- The process used by the two nonconstant estimator branches. -/
noncomputable def estimatedThresholdProcess {n d : ℕ} (epsilon : ℝ)
    (sample : Fin n → Obs d) (lambda : ℝ) : ℝ :=
  if d < boundedAlphabetCutoff then
    empiricalThresholdProcess epsilon sample lambda
  else averagedThresholdProcess epsilon sample lambda

/-- The projected dual minimum, with no optimizer choice. -/
noncomputable def estimatedBudgetValue {n d : ℕ} (epsilon : ℝ)
    (sample : Fin n → Obs d) (b : ℝ) : ℝ :=
  min 1 (max 0 (sInf ((fun lambda : ℝ =>
    b * lambda + estimatedThresholdProcess epsilon sample lambda) '' Set.Icc 0 1)))

-- @node: def:jf-estimator
/-- For [n](hyp:n), [epsilon](hyp:epsilon), [sample](hyp:sample), the jf estimator definition specifies [the stated object](goal). -/
noncomputable def jfEstimator (n d : ℕ) (epsilon b0 : ℝ)
    (sample : Fin n → Obs d) : Set.Icc b0 (1 - b0) → ℝ :=
  fun b => if d ≥ boundedAlphabetCutoff ∧ n < (d : ℝ) / logAlphabet d then
    1 / 2
  else estimatedBudgetValue epsilon sample b.1
  -- @realizes \widehat V^{\mathrm{JF}}(total deterministic curve estimator)

/-- Measurability and global boundedness of the clipped curve estimator. With [the specified inputs and conditions](hyp:n,d,epsilon,b0), [the stated relationship holds](goal). -/
lemma jfEstimator_admissible (n d : ℕ) (epsilon b0 : ℝ) :
    Measurable (jfEstimator n d epsilon b0) ∧
      ∃ B : ℝ, ∀ z b, |jfEstimator n d epsilon b0 z b| ≤ B := by
  constructor
  · exact measurable_of_finite _
  · refine ⟨1, ?_⟩
    intro z b
    unfold jfEstimator
    split_ifs
    · norm_num
    · unfold estimatedBudgetValue
      apply abs_le.mpr
      constructor
      · exact le_trans (by norm_num : (-1 : ℝ) ≤ 0)
          (le_min (by norm_num : (0 : ℝ) ≤ 1) (le_max_left _ _))
      · exact min_le_left _ _

/-- The estimator packaged for the minimax infimum. -/
noncomputable def jfCurveEstimator (n d : ℕ) (epsilon b0 : ℝ)
    (hb0 : b0 ∈ Set.Icc (0 : ℝ) (1 / 2)) : CurveEstimator n d b0 :=
  ⟨jfEstimator n d epsilon b0, hb0, jfEstimator_admissible n d epsilon b0⟩

end CausalSmith.Stat.DiscreteBudgetvalueCurve
