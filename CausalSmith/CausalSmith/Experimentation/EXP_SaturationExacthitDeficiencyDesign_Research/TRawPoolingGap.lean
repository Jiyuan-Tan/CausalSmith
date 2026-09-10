import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.Helpers.Estimators
import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.Helpers.ScheduleLawBridge
import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.TEfficientExactHitBernoulli

/-! # Raw pooling inefficiency -/

open scoped BigOperators
open MeasureTheory Filter

namespace CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign

noncomputable section

/-- Scalar characteristic-function limit for the raw pooled estimator. -/
def RawPooledAsymptotic (P : Measure (Schedule n)) (p : Fin K → ℝ)
    (m : Fin K → ℕ) (k : Fin K) (psi : Record K n → ℝ) (variance : ℝ) : Prop :=
  (∃ remainder : ∀ C, (Fin C → Record K n) → ℝ,
    (∀ eps > 0, Tendsto (fun C => (Measure.pi fun _ : Fin C => bernoulliObservedLaw P p m)
      {O | eps < |remainder C O|}) atTop (nhds 0)) ∧
    ∀ (C : ℕ) O, Real.sqrt C *
      (rawPooledEstimator O m k - exactSliceWelfare P m k) =
        (Real.sqrt C)⁻¹ * ∑ c, psi (O c) + remainder C O) ∧
  ∀ t : ℝ,
    Tendsto (fun C => ∫ O : Fin C → Record K n,
      Real.cos (t * Real.sqrt C *
        (rawPooledEstimator O m k - exactSliceWelfare P m k))
        ∂(Measure.pi fun _ : Fin C => bernoulliObservedLaw P p m)) Filter.atTop
      (nhds (Real.exp (-(t ^ 2 * variance) / 2))) ∧
    Tendsto (fun C => ∫ O : Fin C → Record K n,
      Real.sin (t * Real.sqrt C *
        (rawPooledEstimator O m k - exactSliceWelfare P m k))
        ∂(Measure.pi fun _ : Fin C => bernoulliObservedLaw P p m)) Filter.atTop (nhds 0)

/-- Ordered slice means for the actual four-unit count-one witness law. -/
def fourUnitCountOneMeans : Fin 4 → ℝ := ![4 / 5, 4 / 5, 1 / 5, 1 / 5]

-- @node: prop:raw-pooling-gap
/-- Raw pooling has variance `(tau²+b²)/q`, is efficient exactly when `b²=0`,
and the displayed four-unit witness has excess `9/100` before division by `q`. -/
theorem raw_pooling_gap {n K : ℕ} [NeZero n] [NeZero K]
    (P : Measure (Schedule n)) (p : Fin K → ℝ) (m : Fin K → ℕ) (k : Fin K)
    (hP : WellFormedScheduleLaw P) (hmenu : WellFormedMenu n K m)
    (hp : (∀ l, 0 ≤ p l) ∧ ∑ l, p l = 1) :
    let q := (hitMatrix n m p).2 k
    let tau2 := sliceVariance P (m k)
    let b2 := betweenAssignmentVariance P m k
    let psi := rawInfluence m (hitMatrix n m p).2 (exactSliceWelfare P m) k
    InL2Zero (bernoulliObservedLaw P p m) psi ∧
    (∫ o, (psi o) ^ 2 ∂(bernoulliObservedLaw P p m)) = (tau2 + b2) / q ∧
    RawPooledAsymptotic P p m k psi ((tau2 + b2) / q) ∧
    (((tau2 + b2) / q = tau2 / q) ↔ b2 = 0) ∧
    ∃ P4 : Measure (Schedule 4), ∃ bijection :
        {z // z ∈ exactSlice 4 1} ≃ Fin 4,
      WellFormedScheduleLaw P4 ∧
      (∀ z : {z // z ∈ exactSlice 4 1},
        assignmentMean P4 z.1 = fourUnitCountOneMeans (bijection z)) ∧
      ((sliceCard 4 1 : ℝ)⁻¹ * ∑ z ∈ exactSlice 4 1, assignmentMean P4 z) = 1 / 2 ∧
      sliceVariance P4 1 = 4 / 25 ∧
      ((sliceCard 4 1 : ℝ)⁻¹ *
        ∑ z ∈ exactSlice 4 1, (assignmentMean P4 z - 1 / 2) ^ 2) = 9 / 100 ∧
      sliceVariance P4 1 + ((sliceCard 4 1 : ℝ)⁻¹ *
        ∑ z ∈ exactSlice 4 1, (assignmentMean P4 z - 1 / 2) ^ 2) = 1 / 4 := by sorry

end

end CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign
