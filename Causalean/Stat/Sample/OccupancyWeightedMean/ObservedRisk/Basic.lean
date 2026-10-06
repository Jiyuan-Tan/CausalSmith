module
public import Causalean.Stat.Sample.OccupancyWeightedMean.Variance

/-!
# Observed finite-cell collision statistics

The statistics and assumptions in this module depend only on one observed
probability law and the measurable cell, arm, and real-outcome maps. All sample
ratios are guarded at zero. No potential-outcome variables occur here.
-/

@[expose] public section

namespace Causalean.Stat.Sample.OccupancyWeightedMean.ObservedRisk

open MeasureTheory Causalean.Stat
open scoped BigOperators

variable {Ω κ : Type*} [MeasurableSpace Ω] [Fintype κ] [DecidableEq κ]
  [MeasurableSpace κ] [MeasurableSingletonClass κ]

/-- The observed mass of a cell is the probability that the measured cell label equals it. -/
noncomputable def cellMass (μ : Measure Ω) (X : Ω → κ) (k : κ) : ℝ :=
  (μ (groupEvent X k)).toReal

/-- The observed mass of an arm-cell pair is its joint probability under the observed law. -/
noncomputable def armCellMass (μ : Measure Ω) (X : Ω → κ) (A : Ω → Bool)
    (a : Bool) (k : κ) : ℝ :=
  (μ (armGroupEvent X A a k)).toReal

/-- The guarded arm-cell count is the number of sample observations in that arm and cell. -/
abbrev armCount {n : ℕ} (X : Ω → κ) (A : Ω → Bool)
    (z : Fin n → Ω) (a : Bool) (k : κ) : ℕ :=
  groupArmCount X A z a k

/-- The guarded arm-cell sum adds real outcomes in the requested arm and cell. -/
noncomputable def armSum {n : ℕ} (X : Ω → κ) (A : Ω → Bool) (Y : Ω → ℝ)
    (z : Fin n → Ω) (a : Bool) (k : κ) : ℝ :=
  armResidualSum X A Y (fun _ _ => 0) z a k

/-- The guarded arm-cell mean is the arm-cell outcome sum divided by its positive count,
and is zero when the count vanishes. -/
noncomputable def armMean {n : ℕ} (X : Ω → κ) (A : Ω → Bool) (Y : Ω → ℝ)
    (z : Fin n → Ω) (a : Bool) (k : κ) : ℝ :=
  armResidualMean X A Y (fun _ _ => 0) z a k

/-- A cell is matched when both observed treatment arms appear in it. -/
abbrev matchedCell {n : ℕ} (X : Ω → κ) (A : Ω → Bool)
    (z : Fin n → Ω) (k : κ) : Prop :=
  usableGroup X A z k

/-- The usable total counts all observations in matched cells, and is zero if none match. -/
noncomputable abbrev usableTotal {n : ℕ} (X : Ω → κ) (A : Ω → Bool)
    (z : Fin n → Ω) : ℕ :=
  usableGroupTotal X A z

/-- The cell-count-weighted collision estimator averages matched-cell arm contrasts,
with value zero when no cell is matched. -/
noncomputable def collisionEstimator {n : ℕ} (X : Ω → κ) (A : Ω → Bool)
    (Y : Ω → ℝ) (z : Fin n → Ω) : ℝ := by
  classical
  exact if 0 < usableTotal X A z then
    (∑ k : κ, if matchedCell X A z k then
      (groupCount X A z k : ℝ) *
        (armMean X A Y z true k - armMean X A Y z false k) else 0) /
        usableTotal X A z
    else 0

/-- The population contrast averages the observed arm-cell centers using observed cell masses. -/
noncomputable def populationContrast (μ : Measure Ω) (X : Ω → κ)
    (center : Bool → κ → ℝ) : ℝ :=
  ∑ k : κ, cellMass μ X k * (center true k - center false k)

/-- The design center replaces empirical arm means by their observed arm-cell centers,
retaining the same matched-cell weights and zero-denominator guard. -/
noncomputable def designCenter {n : ℕ} (X : Ω → κ) (A : Ω → Bool)
    (center : Bool → κ → ℝ) (z : Fin n → Ω) : ℝ := by
  classical
  exact if 0 < usableTotal X A z then
    (∑ k : κ, if matchedCell X A z k then
      (groupCount X A z k : ℝ) *
        (center true k - center false k) else 0) / usableTotal X A z
    else 0

/-- An observed-law model has arm-cell overlap, bounded observed centers, centered
square-integrable residuals with a cellwise second-moment envelope, and approximate
homogeneity of observed cell contrasts. -/
structure ObservedAssumptions (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → κ) (A : Ω → Bool) (Y : Ω → ℝ)
    (center : Bool → κ → ℝ) (epsilon M rho : ℝ) : Prop where
  epsilon_pos : 0 < epsilon
  epsilon_lt_half : epsilon < 1 / 2
  X_measurable : Measurable X
  A_measurable : Measurable A
  Y_measurable : Measurable Y
  overlap : ∀ a k, 0 < cellMass μ X k →
    epsilon * cellMass μ X k ≤ armCellMass μ X A a k
  center_envelope : ∀ a k, |center a k| ≤ M
  residual_L2 : ∀ a k,
    MemLp (supportedArmGroupResidual X A Y center a k) 2 μ
  residual_centered : ∀ a k,
    ∫ ω in armGroupEvent X A a k,
      armGroupResidual Y center a k ω ∂μ = 0
  residual_second_moment : ∀ a k,
    ∫ ω in armGroupEvent X A a k,
      (armGroupResidual Y center a k ω) ^ 2 ∂μ ≤
        armCellMass μ X A a k * M ^ 2
  homogeneity : ∀ k, 0 < cellMass μ X k →
    |(center true k - center false k) - populationContrast μ X center| ≤ M * rho

end Causalean.Stat.Sample.OccupancyWeightedMean.ObservedRisk
