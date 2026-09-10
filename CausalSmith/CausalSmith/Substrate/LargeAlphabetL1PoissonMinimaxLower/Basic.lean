import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The two-sample Poisson experiment and its minimax risk

This module defines probability vectors, the two independent coordinatewise
Poisson samples, extended squared risk for an arbitrary measurable estimator,
and the real-valued minimax risk.  Extended nonnegative integrals are used at
the estimator level so a non-integrable estimator cannot acquire Lean's
zero-by-convention real integral.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace CausalSmith.Substrate.LargeAlphabetL1PoissonMinimaxLower

/-- A probability vector on `d` symbols is a nonnegative vector whose
coordinates sum to one. -/
abbrev ProbabilityVector (d : ℕ) :=
  {p : Fin d → ℝ≥0 // ∑ i, p i = 1}

/-- A parameter of the two-unknown-distribution problem is an ordered pair of
probability vectors on the same alphabet. -/
abbrev TwoUnknownParameter (d : ℕ) := ProbabilityVector d × ProbabilityVector d

/-- The observation space contains one count vector from each of the two
independent Poisson samples. -/
abbrev TwoSampleCounts (d : ℕ) := (Fin d → ℕ) × (Fin d → ℕ)

/-- The `L₁` distance between two finite probability vectors is the sum of the
absolute coordinate differences. -/
noncomputable def probabilityVectorL1 {d : ℕ}
    (p q : ProbabilityVector d) : ℝ :=
  ∑ i, |(p.1 i : ℝ) - (q.1 i : ℝ)|

/-- The `L₁` distance between probability vectors lies between zero and two. -/
theorem probabilityVectorL1_mem_Icc {d : ℕ} (p q : ProbabilityVector d) :
    probabilityVectorL1 p q ∈ Set.Icc (0 : ℝ) 2 := by
  constructor
  · exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  · calc
      probabilityVectorL1 p q ≤
          ∑ i, ((p.1 i : ℝ) + (q.1 i : ℝ)) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_le]
        constructor <;> have hp := NNReal.coe_nonneg (p.1 i) <;>
          have hq := NNReal.coe_nonneg (q.1 i) <;> linarith
      _ = 2 := by
        rw [Finset.sum_add_distrib]
        norm_cast
        rw [p.2, q.2]
        norm_num

/-- At nonnegative intensity `t`, the two-sample law consists of mutually
independent counts with means `t pᵢ` and `t qᵢ`. -/
noncomputable def poissonizedTwoSampleLawAt {d : ℕ} (t : ℝ≥0)
    (p q : ProbabilityVector d) : Measure (TwoSampleCounts d) :=
  (Measure.pi fun i : Fin d => poissonMeasure (t * p.1 i)).prod
    (Measure.pi fun i : Fin d => poissonMeasure (t * q.1 i))

/-- The coordinatewise two-sample Poisson law is a probability measure. -/
instance poissonizedTwoSampleLawAt_isProbabilityMeasure {d : ℕ} (t : ℝ≥0)
    (p q : ProbabilityVector d) :
    IsProbabilityMeasure (poissonizedTwoSampleLawAt t p q) := by
  unfold poissonizedTwoSampleLawAt
  infer_instance

/-- The main experiment uses Poisson means `2 n pᵢ` and `2 n qᵢ`, matching the
intensity convention in the substrate requirement. -/
noncomputable def poissonizedTwoSampleLaw (n : ℕ) {d : ℕ}
    (p q : ProbabilityVector d) : Measure (TwoSampleCounts d) :=
  poissonizedTwoSampleLawAt (2 * (n : ℝ≥0)) p q

/-- A measurable estimator is an arbitrary measurable real-valued function of
the pair of count vectors. -/
abbrev MeasurableEstimator (d : ℕ) :=
  {est : TwoSampleCounts d → ℝ // Measurable est}

/-- At arbitrary common intensity `t`, the squared-error risk of a measurable
estimator is its extended expected squared error. -/
noncomputable def poissonizedTwoSampleL1RiskAt (t : ℝ≥0) {d : ℕ}
    (p q : ProbabilityVector d) (est : MeasurableEstimator d) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal ((est.1 z - probabilityVectorL1 p q) ^ 2)
    ∂poissonizedTwoSampleLawAt t p q

/-- The squared-error risk of an arbitrary measurable estimator of
`‖p-q‖₁` when coordinate means are `2npᵢ` and `2nqᵢ`. -/
noncomputable def poissonizedTwoSampleL1Risk (n : ℕ) {d : ℕ}
    (p q : ProbabilityVector d) (est : MeasurableEstimator d) : ℝ≥0∞ :=
  poissonizedTwoSampleL1RiskAt (2 * (n : ℝ≥0)) p q est

/-- The worst-case squared risk of an estimator is the supremum over both
unknown probability vectors. -/
noncomputable def poissonizedTwoUnknownL1WorstRisk (n d : ℕ)
    (est : MeasurableEstimator d) : ℝ≥0∞ :=
  ⨆ θ : TwoUnknownParameter d,
    poissonizedTwoSampleL1Risk n θ.1 θ.2 est

/-- The extended minimax risk is the infimum, over all measurable estimators,
of their worst-case extended squared risks. -/
noncomputable def poissonizedTwoUnknownL1MinimaxRiskENNReal (n d : ℕ) : ℝ≥0∞ :=
  ⨅ est : MeasurableEstimator d,
    poissonizedTwoUnknownL1WorstRisk n d est

/-- The real-valued minimax risk is the finite extended minimax risk converted
to a real number.  Finiteness follows from the constant estimator bound. -/
noncomputable def poissonizedTwoUnknownL1MinimaxRisk (n d : ℕ) : ℝ :=
  (poissonizedTwoUnknownL1MinimaxRiskENNReal n d).toReal

/-- The real minimax risk at an arbitrary common Poisson intensity `t`. -/
noncomputable def poissonizedTwoUnknownL1MinimaxRiskAt (t : ℝ≥0) (d : ℕ) : ℝ :=
  (⨅ est : MeasurableEstimator d,
    ⨆ θ : TwoUnknownParameter d,
      poissonizedTwoSampleL1RiskAt t θ.1 θ.2 est).toReal

/-- The large-alphabet squared-error scale is
`min(1, d / (n log(e n)))`. -/
noncomputable def largeAlphabetL1Rate (n d : ℕ) : ℝ :=
  min 1 ((d : ℝ) /
    ((n : ℝ) * Real.log (Real.exp 1 * (n : ℝ))))

/-- The large-alphabet rate is strictly positive when both the sample size and
alphabet size are nonzero. -/
theorem largeAlphabetL1Rate_pos {n d : ℕ} (hn : 0 < n) (hd : 0 < d) :
    0 < largeAlphabetL1Rate n d := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by omega))
  have hexp : (1 : ℝ) < Real.exp 1 :=
    Real.one_lt_exp_iff.mpr (by norm_num)
  have harg : 1 < Real.exp 1 * (n : ℝ) :=
    lt_of_lt_of_le hexp
      (by simpa using mul_le_mul_of_nonneg_left hnR (Real.exp_pos 1).le)
  rw [largeAlphabetL1Rate, lt_min_iff]
  exact ⟨by norm_num, div_pos (by exact_mod_cast hd)
    (mul_pos (by exact_mod_cast hn) (Real.log_pos harg))⟩

/-- Clipping a measurable estimator to the feasible target interval `[0,2]`
produces another measurable estimator. -/
noncomputable def projectL1Estimator {d : ℕ} (est : MeasurableEstimator d) :
    MeasurableEstimator d :=
  ⟨fun z => max 0 (min 2 (est.1 z)), by
    fun_prop⟩

/-- Projection to `[0,2]` cannot increase squared risk at any pair of
probability vectors. -/
theorem poissonizedTwoSampleL1Risk_project_le (n : ℕ) {d : ℕ}
    (p q : ProbabilityVector d) (est : MeasurableEstimator d) :
    poissonizedTwoSampleL1Risk n p q (projectL1Estimator est) ≤
      poissonizedTwoSampleL1Risk n p q est := by
  unfold poissonizedTwoSampleL1Risk poissonizedTwoSampleL1RiskAt
  apply lintegral_mono
  intro z
  apply ENNReal.ofReal_le_ofReal
  have ht := probabilityVectorL1_mem_Icc p q
  change (max 0 (min 2 (est.1 z)) - probabilityVectorL1 p q) ^ 2 ≤
    (est.1 z - probabilityVectorL1 p q) ^ 2
  by_cases h0 : est.1 z ≤ 0
  · rw [min_eq_right (le_trans h0 (by norm_num)), max_eq_left h0]
    nlinarith [ht.1]
  · have h0' : 0 ≤ est.1 z := le_of_not_ge h0
    by_cases h2 : 2 ≤ est.1 z
    · rw [min_eq_left h2, max_eq_right (by norm_num)]
      nlinarith [ht.2]
    · rw [min_eq_right (le_of_not_ge h2), max_eq_right h0']

/-- The extended minimax risk is finite, since the zero estimator has risk at
most four for every parameter. -/
theorem poissonizedTwoUnknownL1MinimaxRiskENNReal_ne_top (n d : ℕ) :
    poissonizedTwoUnknownL1MinimaxRiskENNReal n d ≠ ∞ := by
  let est0 : MeasurableEstimator d := ⟨fun _ => 0, measurable_const⟩
  apply ne_of_lt
  have hzero : poissonizedTwoUnknownL1WorstRisk n d est0 ≤ 4 := by
    apply iSup_le
    intro θ
    unfold poissonizedTwoSampleL1Risk poissonizedTwoSampleL1RiskAt
    calc
      ∫⁻ z, ENNReal.ofReal ((est0.1 z - probabilityVectorL1 θ.1 θ.2) ^ 2)
          ∂poissonizedTwoSampleLawAt (2 * (n : ℝ≥0)) θ.1 θ.2 ≤
          ∫⁻ _z, ENNReal.ofReal (4 : ℝ)
            ∂poissonizedTwoSampleLawAt (2 * (n : ℝ≥0)) θ.1 θ.2 := by
        apply lintegral_mono
        intro z
        apply ENNReal.ofReal_le_ofReal
        have ht := probabilityVectorL1_mem_Icc θ.1 θ.2
        have hprod : 0 ≤ probabilityVectorL1 θ.1 θ.2 *
            (2 - probabilityVectorL1 θ.1 θ.2) :=
          mul_nonneg ht.1 (sub_nonneg.mpr ht.2)
        have hsq : probabilityVectorL1 θ.1 θ.2 ^ 2 ≤ 4 := by nlinarith
        simpa [est0] using hsq
      _ = 4 := by simp
  exact lt_of_le_of_lt (iInf_le _ est0)
    (lt_of_le_of_lt hzero (show (4 : ℝ≥0∞) < ∞ from ENNReal.ofNat_lt_top))

/-- The real minimax risk is nonnegative. -/
theorem poissonizedTwoUnknownL1MinimaxRisk_nonneg (n d : ℕ) :
    0 ≤ poissonizedTwoUnknownL1MinimaxRisk n d := by
  exact ENNReal.toReal_nonneg

/-- Using intensity `n` rather than `2n` at sample size `2n` gives exactly the
same observation law as the main convention at sample size `n`. -/
theorem poissonizedTwoSampleLaw_two_mul_eq (n : ℕ) {d : ℕ}
    (p q : ProbabilityVector d) :
    poissonizedTwoSampleLaw n p q =
      poissonizedTwoSampleLawAt ((2 * n : ℕ) : ℝ≥0) p q := by
  simp [poissonizedTwoSampleLaw]

/-- The main risk at sample-size parameter `n` is exactly the arbitrary-intensity
risk at intensity `2n`. -/
theorem poissonizedTwoSampleL1Risk_eq_at_two_mul (n : ℕ) {d : ℕ}
    (p q : ProbabilityVector d) (est : MeasurableEstimator d) :
    poissonizedTwoSampleL1Risk n p q est =
      poissonizedTwoSampleL1RiskAt (2 * (n : ℝ≥0)) p q est := by
  rfl

/-- Changing from the `2n` convention to a unit-intensity convention merely
relabels the integer sample-size parameter from `n` to `2n`. -/
theorem poissonizedTwoUnknownL1MinimaxRisk_eq_at_two_mul (n d : ℕ) :
    poissonizedTwoUnknownL1MinimaxRisk n d =
      poissonizedTwoUnknownL1MinimaxRiskAt (2 * (n : ℝ≥0)) d := by
  rfl

end CausalSmith.Substrate.LargeAlphabetL1PoissonMinimaxLower
