module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Estimator
public import Causalean.Stat.Concentration.Poisson.FactorialPolynomial
public import Mathlib.Probability.Distributions.Poisson.Basic

/-! Exact quantities in the radius-indexed Poisson audit.  The bounds on these
quantities belong to the upper-bound proof. -/

@[expose] public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

def AdmissiblePilotValue (M t : ℝ) : Prop :=
  t ∈ Icc (-M) M -- @realizes t(clipped pilot-conditioning value)

noncomputable def armMass {n : ℕ} (P : Law n) (a : Bool) (k : Fin n) : ℝ :=
  P.cellMass k * (if a then P.propensity k else 1 - P.propensity k)

noncomputable def GK (K : ℕ) (x : ℝ) : ℝ :=
  ∑ ell ∈ Finset.range (K - 1), gCoeff K ell * x ^ ell

noncomputable def FK (K : ℕ) (R : ℝ) (N : ℕ) : ℝ :=
  ∑ ell ∈ Finset.range (K - 1),
    gCoeff K ell * (falling (N - 1) ell : ℝ) / R ^ ell

noncomputable def lightAuditWeight (n : ℕ) (rho : ℝ)
    (P : Law n) (k : Fin n) : ℝ :=
  let B := lightScale n rho
  let x0 := armMass P false k / B
  let x1 := armMass P true k / B
  B * x0 * x1 * (GK (degree n rho) x0 + GK (degree n rho) x1)

noncomputable def heavyAuditWeight (n : ℕ) (P : Law n) (k : Fin n) : ℝ :=
  P.cellMass k * (1 - P.propensity k *
      Real.exp (-blockMean n * armMass P false k) -
      (1 - P.propensity k) *
      Real.exp (-blockMean n * armMass P true k))

noncomputable def classificationProbability (n : ℕ) (rho : ℝ)
    (P : Law n) (k : Fin n) : ℝ :=
  ((poissonMeasure (Real.toNNReal (blockMean n * P.cellMass k)))
    {q : ℕ | q ≤ 256 * degree n rho}).toReal

noncomputable def upperAuditWeights (n : ℕ) (rho : ℝ)
    (P : Law n) : Fin n → ℝ :=
  fun k => classificationProbability n rho P k * lightAuditWeight n rho P k +
    (1 - classificationProbability n rho P k) * heavyAuditWeight n P k

noncomputable def factorialOverlap (N j q : ℕ) : ℝ :=
  ∑ b ∈ Finset.range (min (j + 1) (q + 1) + 1),
    ((Nat.choose (j + 1) b * Nat.choose (q + 1) b * Nat.factorial b : ℕ) : ℝ) *
      (falling N (j + q + 2 - b) : ℝ)

noncomputable def conditionalNumeratorSecond {n : ℕ} (P : Law n)
    (k : Fin n) (t : ℝ) (N0 N1 : ℕ) : ℝ :=
  let V0 := ∫ y, (y - P.outcomeMean false k) ^ 2 ∂P.outcomeLaw false k
  let V1 := ∫ y, (y - P.outcomeMean true k) ^ 2 ∂P.outcomeLaw true k
  (N0 : ℝ) ^ 2 * N1 * V1 + (N1 : ℝ) ^ 2 * N0 * V0 +
    (N0 : ℝ) ^ 2 * (N1 : ℝ) ^ 2 *
      (DiscreteAteHeterogeneityFrontier.cellEffect P k - t) ^ 2

noncomputable def factorialCorrectionSquare (n : ℕ) (rho : ℝ)
    (N0 N1 : ℕ) : ℝ :=
  let K := degree n rho
  let B := lightScale n rho
  let m := blockMean n
  if N0 = 0 ∨ N1 = 0 then 0 else
    ∑ j ∈ Finset.range (K - 1), ∑ q ∈ Finset.range (K - 1),
      gCoeff K j * gCoeff K q /
        (B ^ (j + 1) * m ^ (j + 2) * B ^ (q + 1) * m ^ (q + 2)) *
        (factorialOverlap N0 j q / (N0 : ℝ) ^ 2 +
         factorialOverlap N1 j q / (N1 : ℝ) ^ 2 +
         2 * (falling (N0 - 1) j : ℝ) * (falling (N1 - 1) q : ℝ))

noncomputable def lightFactorialCoefficient (n : ℕ) (rho : ℝ)
    (N0 N1 : ℕ) : ℝ :=
  if N0 = 0 ∨ N1 = 0 then 0 else
    ∑ j ∈ Finset.range (degree n rho - 1),
      gCoeff (degree n rho) j *
        ((falling (N0 - 1) j : ℝ) + (falling (N1 - 1) j : ℝ)) /
        (lightScale n rho ^ (j + 1) * blockMean n ^ (j + 2))

noncomputable def heavyCoefficient (n N0 N1 : ℕ) : ℝ :=
  if N0 = 0 ∨ N1 = 0 then 0 else
    ((N0 + N1 : ℕ) : ℝ) / (blockMean n * N0 * N1)

noncomputable def lightConditionalAudit (n : ℕ) (rho : ℝ)
    (P : Law n) (t : ℝ) : ℝ :=
  ∑ k : Fin n, classificationProbability n rho P k *
    ∫ N0 : ℕ, ∫ N1 : ℕ,
      conditionalNumeratorSecond P k t N0 N1 *
        factorialCorrectionSquare n rho N0 N1
      ∂poissonMeasure (Real.toNNReal (blockMean n * armMass P true k))
      ∂poissonMeasure (Real.toNNReal (blockMean n * armMass P false k))

noncomputable def heavyConditionalAudit (n : ℕ) (rho : ℝ)
    (P : Law n) (t : ℝ) : ℝ :=
  ∑ k : Fin n, (1 - classificationProbability n rho P k) *
    ∫ N0 : ℕ, ∫ N1 : ℕ,
      conditionalNumeratorSecond P k t N0 N1 *
        heavyCoefficient n N0 N1 ^ 2
      ∂poissonMeasure (Real.toNNReal (blockMean n * armMass P true k))
      ∂poissonMeasure (Real.toNNReal (blockMean n * armMass P false k))

noncomputable def misclassifiedConditionalAudit (n : ℕ) (rho : ℝ)
    (P : Law n) (t : ℝ) : ℝ :=
  ∑ k : Fin n,
    (if blockMean n * P.cellMass k ≤ 256 * degree n rho then
      1 - classificationProbability n rho P k
    else classificationProbability n rho P k) *
    (∫ N0 : ℕ, ∫ N1 : ℕ,
      conditionalNumeratorSecond P k t N0 N1 *
        (lightFactorialCoefficient n rho N0 N1 -
          heavyCoefficient n N0 N1) ^ 2
      ∂poissonMeasure (Real.toNNReal (blockMean n * armMass P true k))
      ∂poissonMeasure (Real.toNNReal (blockMean n * armMass P false k)))

-- @node: def:upper-audit-handle
noncomputable def upperConditionalAudit (n : ℕ) (M rho : ℝ)
    (P : Law n) (t : ℝ) (_ht : AdmissiblePilotValue M t) : ℝ × ℝ × ℝ :=
  (lightConditionalAudit n rho P t,
    heavyConditionalAudit n rho P t,
    misclassifiedConditionalAudit n rho P t)

-- @node: audit_descFactorial_overlap
lemma audit_descFactorial_overlap (N j q : ℕ) :
    (falling N (j + 1) : ℝ) * (falling N (q + 1) : ℝ) =
      ∑ b ∈ Finset.range (min (j + 1) (q + 1) + 1),
        (Nat.choose (j + 1) b * Nat.choose (q + 1) b * Nat.factorial b : ℝ) *
          (falling N (j + q + 2 - b) : ℝ) := by
  simpa only [falling, Nat.cast_mul,
    show (j + 1) + (q + 1) = j + q + 2 by omega] using
    (Causalean.Stat.Concentration.Poisson.descFactorial_mul N (j + 1) (q + 1))

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
