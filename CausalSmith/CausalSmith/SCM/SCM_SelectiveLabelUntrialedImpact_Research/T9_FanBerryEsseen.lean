import CausalSmith.SCM.SCM_SelectiveLabelUntrialedImpact_Research.Helpers.CitedGates
import CausalSmith.SCM.SCM_SelectiveLabelUntrialedImpact_Research.Helpers.Inference
import Causalean.Mathlib.OperatorSqrt
import Causalean.Mathlib.SemiInnerProjection
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.PosDef

set_option linter.style.openClassical false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-! # Finite-alphabet fan Berry--Esseen bound -/

namespace CausalSmith.SCM.SelectiveLabelUntrialedImpact

open scoped BigOperators ENNReal NNReal Classical
open MeasureTheory Set Filter Asymptotics

variable {O T OBlind K R : Type*} [Fintype O] [Fintype T] [Fintype OBlind]
  [Fintype K] [Fintype R] [DecidableEq O] [DecidableEq T]
  [DecidableEq OBlind] [DecidableEq K] [DecidableEq R]

/-- The centered empirical categorical fluctuation based on the first `m`
observations. -/
noncomputable def categoricalFluctuation
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace O]
    {μ : Measure Ω} {P : Measure O}
    (S : Causalean.Stat.IIDSample Ω O μ P) (p : O → ℝ)
    (m : ℕ) (ω : Ω) (o : O) : ℝ :=
  (Real.sqrt m)⁻¹ * ∑ i ∈ Finset.range m,
    ((if S.Z i ω = o then 1 else 0) - p o)

/-- A lower orthant in finite Euclidean coordinates. -/
def lowerOrthant (x : R → ℝ) : Set (R → ℝ) := {y | ∀ r, y r ≤ x r}

/-- The transformed covariance `M Sigma_p Mᵀ`. -/
def transformedCovariance (p : O → ℝ) (M : Matrix R O ℝ) : Matrix R R ℝ :=
  M * multinomialCovariance p * M.transpose

/-- The lower-orthant approximation error, maximized over the finite fan
matrix family. -/
noncomputable def fanApproximationError
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace O]
    {μ : Measure Ω} {P : Measure O}
    (S : Causalean.Stat.IIDSample Ω O μ P) (p : O → ℝ)
    (Q : Measure (O → ℝ)) (M : K → Matrix R O ℝ) (m : ℕ) : ℝ :=
  sSup {a | ∃ k x, a =
    |ENNReal.toReal (μ {ω | (M k).mulVec (categoricalFluctuation S p m ω) ∈
        lowerOrthant x}) -
      ENNReal.toReal (Q {g | (M k).mulVec g ∈ lowerOrthant x})|}

/-- The fixed-law explicit constant after an effective-range whitening `W`.
Rank-zero matrices contribute zero. -/
noncomputable def fanBerryEsseenConstant
    (p : O → ℝ) (M : K → Matrix R O ℝ) (W : K → Matrix R R ℝ) : ℝ :=
  max 0 (sSup {c | ∃ k, c =
    (42 * Real.sqrt (Real.sqrt (Matrix.rank (transformedCovariance p (M k)) : ℝ)) + 16) *
      ∑ o, p o * (Real.sqrt (∑ r,
        (W k).mulVec ((M k).mulVec
          (fun o' => (if o' = o then 1 else 0) - p o')) r ^ 2)) ^ 3})

/-- Raič's identity-covariance theorem, applied only after restriction and
whitening on each covariance range, gives the pointwise fan bound and the
paper's explicit cube-root schedules.  The cited input is deliberately an
explicit `_of_gate` hypothesis. -/
-- @node: lem:finite-alphabet-fan-berry-esseen-explicit-schedule
lemma finite_alphabet_fan_berry_esseen_explicit_schedule
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace O]
    [MeasurableSingletonClass O] {μ : Measure Ω} {P : Measure O}
    (S : Causalean.Stat.IIDSample Ω O μ P) (G : SLCCIncidence O T OBlind)
    (p : O → ℝ) (hIID : IidFiniteSampling μ P S G p)
    (M : K → Matrix R O ℝ) (alpha : ℝ) (hAlpha : 0 < alpha ∧ alpha < 1)
    (raic_of_gate : RaicMultivariateBerryEsseenConvexSets) :
    ∃ W : K → Matrix R R ℝ,
      0 ≤ fanBerryEsseenConstant p M W ∧
      (∀ m : ℕ, 1 ≤ m →
        fanApproximationError S p (multinomialGaussianLaw p) M m ≤
          fanBerryEsseenConstant p M W * (Real.sqrt m)⁻¹) ∧
      (fun n : ℕ => fanApproximationError S p (multinomialGaussianLaw p) M
          (subsampleSize n)) =O[atTop]
        (fun n : ℕ => Real.rpow n (-(1 / 6 : ℝ))) ∧
      (fun n : ℕ => (subsampleSize n : ℝ) / Real.sqrt n) =O[atTop]
        (fun n : ℕ => Real.rpow n (-(1 / 6 : ℝ))) ∧
      (fun n : ℕ => (subsampleSize n : ℝ) ^ 2 / n) =O[atTop]
        (fun n : ℕ => Real.rpow n (-(1 / 3 : ℝ))) ∧
      (fun n : ℕ => Real.rpow n (-(1 / 6 : ℝ))) =o[atTop]
        (fun n : ℕ => quantileSlack n alpha) := by
  sorry

end CausalSmith.SCM.SelectiveLabelUntrialedImpact
