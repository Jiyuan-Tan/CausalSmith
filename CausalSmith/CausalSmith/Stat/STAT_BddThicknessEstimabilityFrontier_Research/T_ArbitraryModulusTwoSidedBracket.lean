-- The severe-modulus clause imports its domain-restricted consistency result.
import CausalSmith.Stat.STAT_BddThicknessEstimabilityFrontier_Research.T_ExponentialHornConsistency
import CausalSmith.Stat.STAT_BddThicknessEstimabilityFrontier_Research.T_ThicknessEntropySeparation
import CausalSmith.Stat.STAT_BddThicknessEstimabilityFrontier_Research.Helpers.DiskPattern

/-! # Arbitrary-modulus two-sided bracket -/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace CausalSmith.Stat.BddThicknessEstimabilityFrontier

/-- The upper bias-stochastic objective at a declared modulus. -/
noncomputable def modulusObjective (n : ℕ) (m : ℝ → ℝ≥0∞)
    (L σ h : ℝ) : ℝ :=
  L * h + σ * Real.sqrt (Real.log (Real.exp 1 + n / h) / (n * (m h).toReal))

/-- Extended-real upper benchmark; an empty feasible grid has value `⊤`. -/
noncomputable def modulusUpperBenchmark (n : ℕ) (m : ℝ → ℝ≥0∞)
    (L σ h0 A : ℝ) : ℝ≥0∞ :=
  ⨅ h : ℝ, ⨅ (_hh : h ∈ dyadicGrid n h0),
    ⨅ (_h2h : 2 * h ∈ dyadicGrid n h0),
    ⨅ (_hcount : A * Real.log (Real.exp 1 + n / h) ≤ n * (m h).toReal),
      ENNReal.ofReal (modulusObjective n m L σ h)

/-- Radii at which either the two-law or many-law information budget is feasible. -/
def LowerInformationFeasible (n : ℕ) (Jminus : ℝ → ℝ≥0∞ → ℕ∞)
    (L σ h0 a h : ℝ) : Prop :=
  ∃ u : ℝ, 0 < h ∧ h ≤ h0 / 3 ∧ 0 < u ∧ u ≤ 1 ∧
    let M := Jminus h (ENNReal.ofReal u)
    M ≠ ∞ ∧ ((1 ≤ M ∧ n * L ^ 2 * h ^ 2 * u / σ ^ 2 ≤ a) ∨
      (2 ≤ M ∧ n * L ^ 2 * h ^ 2 * u / σ ^ 2 ≤
        a * Real.log (M.toNat + 1)))

/-- Supremum of all lower-bound-feasible radii, including both testing branches. -/
noncomputable def modulusLowerFeasibleRadius (n : ℕ)
    (Jminus : ℝ → ℝ≥0∞ → ℕ∞) (L σ h0 a : ℝ) : ℝ≥0∞ :=
  ⨆ h : ℝ, ⨆ (_hh : LowerInformationFeasible n Jminus L σ h0 a h),
    ENNReal.ofReal h

/-- The deliberately slack declaration exposing only one polynomially thin site. -/
noncomputable def oneSiteLowerProfile (Cm κ : ℝ) : ℝ → ℝ≥0∞ → ℕ∞ :=
  fun h u => if ENNReal.ofReal (Cm * h ^ κ) ≤ u then 1 else 0

-- @node: thm:arbitrary-modulus-two-sided-bracket
/-- The clipped count-adaptive estimator has the global-modulus upper bound,
while separated thin sites give the stated one- or many-hypothesis lower
bound.  The signature also records the sufficient and necessary consistency
conditions and the polynomial and exponential specializations. -/
theorem arbitrary_modulus_two_sided_bracket (κbar L σ cm Cm h0 : ℝ)
    (A0 A1 B : Set Score)
    (hparams : 2 < κbar ∧ 0 < L ∧ 0 < σ ∧ 0 < cm ∧ cm < Cm ∧
      0 < h0 ∧ h0 < 1)
    (hgeometry : FixedAssignmentGeometry A0 A1 B) :
    ∃ A C c a : ℝ, 0 < A ∧ 0 < C ∧ 0 < c ∧ 0 < a ∧
    ∀ (m : ℕ → ℝ → ℝ≥0∞) (Jminus : ℕ → ℝ → ℝ≥0∞ → ℕ∞)
    (hpos : ∀ n h, 0 < h → h ≤ h0 → 0 < m n h)
    (hJfinite : ∀ n h u, 0 < h → h ≤ h0 → u ≤ 1 → Jminus n h u ≠ ∞)
    (hnonempty : ∀ n,
      (lawsOnGeometry (modulusProfileLaws L σ h0 (m n) (Jminus n)) A0 A1 B).Nonempty)
    (hiid : ∀ n P,
      P ∈ lawsOnGeometry (modulusProfileLaws L σ h0 (m n) (Jminus n)) A0 A1 B →
      IidSampling n P (observedSampleLaw P n)),
    (∀ n, MeasurableBoundaryEstimator
      (clippedGeometryMassAdaptiveEstimator n A0 A1 L σ h0)) ∧
      (∀ n,
        (⨆ P : BoundaryLaw,
          ⨆ (_hP : P ∈ lawsOnGeometry
            (modulusProfileLaws L σ h0 (m n) (Jminus n)) A0 A1 B),
          estimatorExpectedSupLoss
            (clippedGeometryMassAdaptiveEstimator n A0 A1 L σ h0) P) ≤
          min (ENNReal.ofReal (C * L))
            (ENNReal.ofReal C * modulusUpperBenchmark n (m n) L σ h0 A)) ∧
      (∀ (n : ℕ) (h u : ℝ), 0 < h → h ≤ h0 / 3 → 0 < u → u ≤ 1 →
        let M := Jminus n h (ENNReal.ofReal u)
        M ≠ ∞ →
        ((1 ≤ M ∧ n * L ^ 2 * h ^ 2 * u / σ ^ 2 ≤ a) ∨
          (2 ≤ M ∧ n * L ^ 2 * h ^ 2 * u / σ ^ 2 ≤
            a * Real.log (M.toNat + 1))) →
        ENNReal.ofReal (c * L * h) ≤
          expectedSupMinimaxRisk n (lawsOnGeometry
            (modulusProfileLaws L σ h0 (m n) (Jminus n)) A0 A1 B)) ∧
      ((∃ hseq : ℕ → ℝ, Tendsto hseq atTop (𝓝 0) ∧
          (∀ᶠ n in atTop,
            hseq n ∈ dyadicGrid n h0 ∧ 2 * hseq n ∈ dyadicGrid n h0) ∧
          Tendsto (fun n => n * (m n (hseq n)).toReal /
            Real.log (Real.exp 1 + n / hseq n)) atTop atTop) →
        Tendsto (fun n => expectedSupMinimaxRisk n
          (lawsOnGeometry (modulusProfileLaws L σ h0 (m n) (Jminus n)) A0 A1 B))
            atTop (𝓝 0)) ∧
      (Tendsto (fun n => expectedSupMinimaxRisk n
          (lawsOnGeometry (modulusProfileLaws L σ h0 (m n) (Jminus n)) A0 A1 B))
            atTop (𝓝 0) →
        Tendsto (fun n => modulusLowerFeasibleRadius n (Jminus n) L σ h0 a)
          atTop (𝓝 0)) ∧
      (∀ α, AdmissibleSeverityExponent α → ∃ hseq : ℕ → ℝ,
        Tendsto hseq atTop (𝓝 0) ∧ (∀ n, 0 < hseq n ∧ hseq n ≤ h0) ∧
        (∀ᶠ n in atTop,
          hseq n ∈ dyadicGrid n h0 ∧ 2 * hseq n ∈ dyadicGrid n h0) ∧
        Tendsto (fun n : ℕ => n * exponentialModulus α h0 (hseq n) /
          Real.log (Real.exp 1 + n / hseq n)) atTop atTop) ∧
      ∀ κ, 2 < κ → κ ≤ κbar →
        (lawsOnGeometry (isolatedLaws L σ cm Cm κ h0) A0 A1 B).Nonempty →
        (lawsOnGeometry (pervasiveLaws L σ cm Cm κ h0) A0 A1 B).Nonempty →
        (∀ n P, P ∈ lawsOnGeometry (isolatedLaws L σ cm Cm κ h0) A0 A1 B ∪
          lawsOnGeometry (pervasiveLaws L σ cm Cm κ h0) A0 A1 B →
            IidSampling n P (observedSampleLaw P n)) →
        (∃ ciso Ciso cperv Cperv : ℝ, 0 < ciso ∧ ciso ≤ Ciso ∧
          0 < cperv ∧ cperv ≤ Cperv ∧
          ∀ᶠ n in atTop,
            ENNReal.ofReal (ciso * isolatedRate n κ) ≤
              expectedSupMinimaxRisk n
                (lawsOnGeometry (isolatedLaws L σ cm Cm κ h0) A0 A1 B) ∧
            expectedSupMinimaxRisk n
                (lawsOnGeometry (isolatedLaws L σ cm Cm κ h0) A0 A1 B) ≤
              ENNReal.ofReal (Ciso * isolatedRate n κ) ∧
            ENNReal.ofReal (cperv * pervasiveRate n κ) ≤
              expectedSupMinimaxRisk n
                (lawsOnGeometry (pervasiveLaws L σ cm Cm κ h0) A0 A1 B) ∧
            expectedSupMinimaxRisk n
                (lawsOnGeometry (pervasiveLaws L σ cm Cm κ h0) A0 A1 B) ≤
              ENNReal.ofReal (Cperv * pervasiveRate n κ)) ∧
        lawsOnGeometry (isolatedLaws L σ cm Cm κ h0) A0 A1 B ∪
            lawsOnGeometry (pervasiveLaws L σ cm Cm κ h0) A0 A1 B ⊆
          lawsOnGeometry (modulusProfileLaws L σ h0
            (fun h => ENNReal.ofReal (cm * h ^ κ)) (oneSiteLowerProfile Cm κ))
            A0 A1 B ∧
        Tendsto (fun n : ℕ => pervasiveRate n κ / isolatedRate n κ) atTop atTop := by sorry

end CausalSmith.Stat.BddThicknessEstimabilityFrontier
