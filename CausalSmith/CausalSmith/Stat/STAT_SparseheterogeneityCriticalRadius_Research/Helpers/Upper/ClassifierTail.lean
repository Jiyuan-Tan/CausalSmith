module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.HeavyWeightBound
public import Causalean.Stat.Concentration.Poisson.Threshold

/-! Poisson classifier tails for the light/heavy audit split. -/

public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal MeasureTheory

/-- The classifier probability is a probability. -/
lemma classificationProbability_mem_Icc {n : ℕ} (rho : ℝ) (P : Law n)
    (k : Fin n) : classificationProbability n rho P k ∈ Set.Icc 0 1 := by
  constructor
  · exact ENNReal.toReal_nonneg
  · calc
      _ ≤ (poissonMeasure
          (Real.toNNReal (blockMean n * P.cellMass k))).real Set.univ :=
        measureReal_mono (Set.subset_univ _)
      _ = 1 := probReal_univ

/-- The complement of the light-classification probability is the strict upper tail. -/
lemma one_sub_classificationProbability {n : ℕ} (rho : ℝ) (P : Law n)
    (k : Fin n) :
    1 - classificationProbability n rho P k =
      (poissonMeasure (Real.toNNReal (blockMean n * P.cellMass k))).real
        {q : ℕ | 256 * degree n rho < q} := by
  let A : Set ℕ := {q : ℕ | q ≤ 256 * degree n rho}
  have hA : MeasurableSet A := MeasurableSet.of_discrete
  have hcompl : Aᶜ = {q : ℕ | 256 * degree n rho < q} := by
    ext q
    simp [A]
  change 1 - (poissonMeasure
      (Real.toNNReal (blockMean n * P.cellMass k))).real A = _
  rw [← hcompl, measureReal_compl hA, probReal_univ]

/-- Equation (25) at the audit cutoff: cells of mass at most `B/64` are
misclassified as heavy with exponentially small probability. -/
lemma light_classification_error_bound {n : ℕ} (rho : ℝ) (P : Law n)
    (k : Fin n) (hn : 0 < n)
    (hlight : P.cellMass k ≤ lightScale n rho / 64) :
    1 - classificationProbability n rho P k ≤
      Real.exp ((1 - Real.log 4) * (256 * degree n rho : ℕ)) := by
  let K := degree n rho
  let T := 256 * K
  let lambda : ℝ := blockMean n * P.cellMass k
  let lam : ℝ≥0 := Real.toNNReal lambda
  have hm : 0 < blockMean n := by
    simp only [blockMean, postPilotSize, pilotSize]
    have : 0 < n - n / 2 := by omega
    positivity
  have hp0 : 0 ≤ P.cellMass k := (P.cellMass_range k).1
  have hlambda0 : 0 ≤ lambda := by dsimp [lambda]; positivity
  have hlam : (lam : ℝ) = lambda := by
    simp [lam, Real.coe_toNNReal lambda hlambda0]
  have hlambdaT : 4 * lambda ≤ (T : ℝ) := by
    have hB : lightScale n rho = 4096 * (K : ℝ) / blockMean n := rfl
    have hp := hlight
    rw [hB] at hp
    dsimp [lambda, T, K]
    rw [div_div] at hp
    have hm64 : 0 < blockMean n * 64 := by positivity
    have := (le_div_iff₀ hm64).mp hp
    norm_num at this ⊢
    nlinarith
  have hchernoff :=
    Causalean.Stat.Concentration.Poisson.poisson_upper_tail_mul_exp_le
      lam T (r := 3) (by norm_num)
  have hexp : 0 < Real.exp (-3 * lambda) := Real.exp_pos _
  rw [one_sub_classificationProbability rho P k]
  change (poissonMeasure lam).real {q : ℕ | T < q} ≤ _
  apply le_of_mul_le_mul_right _ hexp
  calc
    (poissonMeasure lam).real {q : ℕ | T < q} * Real.exp (-3 * lambda) ≤
        Real.exp (-Real.log (1 + 3) * (T : ℝ)) := by
      simpa [hlam] using hchernoff
    _ ≤ Real.exp ((1 - Real.log 4) * (T : ℝ)) * Real.exp (-3 * lambda) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      norm_num
      nlinarith [hlambdaT]

/-- Equation (26), in the stronger range needed by the audit: cells above `B`
are classified as light with probability at most `exp (-m p / 8)`. -/
lemma heavy_classification_error_bound {n : ℕ} (rho : ℝ) (P : Law n)
    (k : Fin n) (hn : 0 < n)
    (hheavy : lightScale n rho < P.cellMass k) :
    classificationProbability n rho P k ≤
      Real.exp (-blockMean n * P.cellMass k / 8) := by
  let K := degree n rho
  let T := 256 * K
  let lambda : ℝ := blockMean n * P.cellMass k
  let lam : ℝ≥0 := Real.toNNReal lambda
  have hm : 0 < blockMean n := by
    simp only [blockMean, postPilotSize, pilotSize]
    have : 0 < n - n / 2 := by omega
    positivity
  have hp0 : 0 ≤ P.cellMass k := (P.cellMass_range k).1
  have hlambda0 : 0 ≤ lambda := by dsimp [lambda]; positivity
  have hlam : (lam : ℝ) = lambda := by
    simp [lam, Real.coe_toNNReal lambda hlambda0]
  have hcutoff : (T : ℝ) < (lam : ℝ) / 4 := by
    have hp := hheavy
    change 4096 * (K : ℝ) / blockMean n < P.cellMass k at hp
    have hmul := (div_lt_iff₀ hm).mp hp
    rw [hlam]
    dsimp [lambda, T]
    norm_num at hmul ⊢
    nlinarith
  have htail :=
    Causalean.Stat.Concentration.Poisson.poisson_le_cutoff_of_cutoff_lt_quarter
      lam T hcutoff
  have htailReal :
      (poissonMeasure lam).real {q : ℕ | q ≤ T} ≤
        Real.exp (-(lam : ℝ) / 4) := by
    exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _)
      (Real.exp_nonneg _)).mp htail
  change (poissonMeasure lam).real {q : ℕ | q ≤ T} ≤ _
  calc
    _ ≤ Real.exp (-(lam : ℝ) / 4) := htailReal
    _ ≤ Real.exp (-blockMean n * P.cellMass k / 8) := by
      rw [hlam]
      apply Real.exp_le_exp.mpr
      dsimp [lambda]
      have : 0 ≤ blockMean n * P.cellMass k := mul_nonneg hm.le hp0
      linarith

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
