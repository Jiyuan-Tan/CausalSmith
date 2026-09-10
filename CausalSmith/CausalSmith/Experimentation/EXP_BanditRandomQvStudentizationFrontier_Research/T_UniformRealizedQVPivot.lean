/- Uniform contrastwise inference from early-measurable predictable QV. -/

import CausalSmith.Experimentation.EXP_BanditRandomQvStudentizationFrontier_Research.T_BasinStableIPWZ
import CausalSmith.Experimentation.EXP_BanditRandomQvStudentizationFrontier_Research.Helpers.SelfNormalizedCLT

/-! # Uniform realized-QV pivot -/

open Filter MeasureTheory Set Topology

namespace CausalSmith.Experimentation.BanditRandomQV

noncomputable section

def UniformCDFConvergesPositive {I Ω : Type*} [MeasurableSpace Ω]
    (μ : PositiveHorizon → I → Measure Ω)
    (X : PositiveHorizon → I → Ω → ℝ) (F : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ T : PositiveHorizon in atTop, ∀ i z,
    |(μ T i {ω | X T i ω ≤ z}).toReal - F z| ≤ ε

def earlyCutoff (r : ℕ → ℝ) (T : ℕ) : ℕ :=
  min (T - 1) (sInf {n : ℕ | (T : ℝ) * max ((T : ℝ)⁻¹.sqrt) (Real.sqrt (r T)) ≤ n})
  -- @realizes k_T(canonical horizon-relative early cutoff)

def uniformRealizedQVPivotConclusion
    {Ω 𝒳 I : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳]
    {K d q : ℕ} (E : PositiveHorizon → I → AdaptiveCausalExperiment Ω 𝒳 K d q)
    (rho : ℝ) (C : ∀ T i, IPWZContract Ω 𝒳 (E T i) T rho) (c : Vec d)
  (hc : c ≠ 0) (hmin : ℝ) (hhmin : 0 < hmin)
  (omega : ℕ → ℝ) (homega : ∀ T : PositiveHorizon, 0 < omega T) : Prop :=
  (∀ eps > 0, ∀ᶠ T in atTop, ∀ i,
    ((E T i).law {ω' | ¬ (localRootSet (E T i).parameterSet
      (empiricalMoment (E T i) T ω') ((C T i).tilde ω') rho).Nonempty}).toReal ≤ eps) ∧
  UniformBigOInProbability (fun T i => (E T i).law)
    (fun T i ω' => ‖Real.sqrt T • (ipwZEstimator (C T i) ω' - (E T i).thetaStar) +
      matVec ((E T i).jacobian)⁻¹ ((T : ℝ)⁻¹.sqrt • (E T i).scoreSum T ω')‖)
    (fun T => (T : ℝ)⁻¹.sqrt) ∧
  UniformBigOInProbability (fun T i => (E T i).law)
    (fun T i ω' => matrixOperatorNorm ((T : ℝ)⁻¹ •
      ((E T i).realizedQV T ω' - (E T i).predictableQV T ω')))
    (fun T => (T : ℝ)⁻¹.sqrt) ∧
  UniformBigOInProbability (fun T i => (E T i).law)
    (fun T i ω' => matrixOperatorNorm
      (empiricalOmega T (feasibleScore (C T i)) ω' -
        (T : ℝ)⁻¹ • (E T i).realizedQV T ω'))
    (fun T => (T : ℝ)⁻¹.sqrt) ∧
  UniformBigOInProbability (fun T i => (E T i).law)
    (fun T i ω' => matrixOperatorNorm ((C T i).Hhat ω' - (E T i).jacobian))
    (fun T => (T : ℝ)⁻¹.sqrt) ∧
  (∀ eps > 0, ∀ᶠ T in atTop, ∀ i,
    ((E T i).law ((contrastTruncationEvent T (feasibleScore (C T i))
      (C T i).Hhat hmin (omega T) c)ᶜ)).toReal ≤ eps) ∧
  UniformCDFConvergesPositive (fun T i => (E T i).law)
    (fun T i => realizedQVPivot T (C T i).T_pos c (E T i).thetaStar
      hc (ipwZEstimator (C T i))
      (feasibleScore (C T i)) (C T i).Hhat hmin (omega T) hhmin (homega T))
    Causalean.Mathlib.stdNormalCDF ∧
  (∀ alpha, ∀ halpha : 0 < alpha ∧ alpha < 1, ∀ eps > 0, ∀ᶠ T in atTop, ∀ i,
    |((E T i).law {ω' | dot c (E T i).thetaStar ∈
      realizedQVWaldInterval T (C T i).T_pos
        (fun ω'' => dot c (ipwZEstimator (C T i) ω''))
        (feasibleScore (C T i)) (C T i).Hhat hmin (omega T) hhmin (homega T)
        c hc alpha halpha ω'}).toReal -
      (1 - alpha)| ≤ eps)

-- @node: thm:uniform-realized-qv-pivot
theorem uniform_realized_qv_pivot
    {Ω 𝒳 I : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳]
    {K d q : ℕ} [MeasurableSpace (Mat d)]
    (E : PositiveHorizon → I → AdaptiveCausalExperiment Ω 𝒳 K d q)
    [Nonempty I] (rho : ℝ) (C : ∀ T i, IPWZContract Ω 𝒳 (E T i) T rho) (c : Vec d)
    (ε B D1 D2 hmin sTheta : ℝ) (κ : ℝ → ℝ)
    (r delta omega : ℕ → ℝ) (k : ℕ → ℕ)
    (Lambda : PositiveHorizon → I → Ω → ℝ) (Theta : Set (Vec d))
    (hClass : ProjectedQVGrowthIPWZClass E Theta c ε B rho
      D1 D2 hmin sTheta κ r delta omega k Lambda)
    (contract_moduli : ∀ T i, (C T i).r = r T ∧ (C T i).failure = delta T)
    (jacobian_derivative : ∀ T i, (E T i).jacobianMap =
      fderiv ℝ (E T i).populationMoment (E T i).thetaStar)
    {m : ℕ}
    (EF : PositiveHorizon → I → AdaptiveCausalExperiment Ω 𝒳 K d q)
    (etaBar : Fin m → Vec q) (J : PositiveHorizon → I → Ω → Fin m)
    (etaInf : PositiveHorizon → I → Ω → Vec q)
    (CF : ∀ T i, IPWZContract Ω 𝒳 (EF T i) T rho)
    (LPi omegaMin sEta pmin : ℝ)
    (hFinite : ∀ T i, FiniteAttractorClass (EF T i) etaBar (J T i) (etaInf T i)
      ε B rho D1 D2 hmin LPi omegaMin sEta pmin sTheta κ r delta) :
    uniformRealizedQVPivotConclusion E rho C c hClass.contrast_ne hmin
      (hClass.nonsingular ⟨1, by omega⟩ (Classical.choice inferInstance)).1
      omega hClass.floor_pos ∧
    ∃ (kFinite : ℕ → ℕ) (Jearly : PositiveHorizon → I → Ω → Fin m)
      (LambdaFinite : PositiveHorizon → I → Ω → ℝ),
      kFinite = earlyCutoff r ∧
      (∀ T : PositiveHorizon, kFinite T < T) ∧
      (∀ T i, Measurable[(EF T i).filtration (kFinite T)] (Jearly T i)) ∧
      (∀ T i ω', LambdaFinite T i ω' =
        qform (basinOmega (EF T i) etaBar (hFinite T i).etaBar_mem (Jearly T i ω'))
          (matVec (transpose ((EF T i).jacobian)⁻¹) c)) ∧
      UniformProjectedPredictableQVGrowth EF c
        (fun T i => (EF T i).law) (fun T i => (EF T i).filtration)
        (fun T i t ω' => dot c
          (matVec ((EF T i).jacobian)⁻¹ ((EF T i).ipwScore t ω')))
        kFinite (fun _ => omegaMin * ‖c‖ ^ 2 / (K * D1) ^ 2) LambdaFinite ∧
      ∃ hfloor : ∀ T : PositiveHorizon,
        0 < omegaMin * ‖c‖ ^ 2 / (K * D1) ^ 2,
        uniformRealizedQVPivotConclusion EF rho CF c hClass.contrast_ne hmin
          (hFinite ⟨1, by omega⟩ (Classical.choice inferInstance)).nonsingular.1
          (fun _ => omegaMin * ‖c‖ ^ 2 / (K * D1) ^ 2) hfloor := by sorry

/-- The finite-attractor specialization is a separate implication and does
not require membership in the projected class as an additional premise. -/
theorem finite_attractor_implies_early_stabilized
    {Ω 𝒳 I : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳] [Nonempty I]
    {K d q m : ℕ} [MeasurableSpace (Mat d)]
    (E : PositiveHorizon → I → AdaptiveCausalExperiment Ω 𝒳 K d q)
    (etaBar : Fin m → Vec q) (J : PositiveHorizon → I → Ω → Fin m)
    (etaInf : PositiveHorizon → I → Ω → Vec q) (default : Fin m)
    (ε B rho D1 D2 hmin LPi omegaMin sEta pmin sTheta : ℝ)
    (κ : ℝ → ℝ) (r delta : ℕ → ℝ) (c : Vec d) (hc : c ≠ 0)
    (hFinite : ∀ T i, FiniteAttractorClass (E T i) etaBar (J T i) (etaInf T i)
      ε B rho D1 D2 hmin LPi omegaMin sEta pmin sTheta κ r delta) :
    ∃ kFinite : ℕ → ℕ, kFinite = earlyCutoff r ∧
      ∃ Jearly : PositiveHorizon → I → Ω → Fin m,
      ∃ LambdaFinite : PositiveHorizon → I → Ω → ℝ,
      (∀ T : PositiveHorizon, kFinite T < T) ∧
      (∀ T : PositiveHorizon, ∀ i,
        Measurable[(E T i).filtration (kFinite T)] (Jearly T i)) ∧
      (∀ T : PositiveHorizon, ∀ i ω', kFinite T = 0 → Jearly T i ω' = default) ∧
      (∀ T : PositiveHorizon, ∀ i ω', 0 < kFinite T → ∀ j,
        dist ((kFinite T : ℝ)⁻¹ • ∑ t ∈ Finset.Icc 1 (kFinite T),
          (E T i).state (t - 1) ω') (etaBar (Jearly T i ω')) ≤
        dist ((kFinite T : ℝ)⁻¹ • ∑ t ∈ Finset.Icc 1 (kFinite T),
          (E T i).state (t - 1) ω') (etaBar j)) ∧
      (∀ T : PositiveHorizon, ∀ i ω', LambdaFinite T i ω' =
        qform (basinOmega (E T i) etaBar (hFinite T i).etaBar_mem (Jearly T i ω'))
          (matVec (transpose ((E T i).jacobian)⁻¹) c)) ∧
      UniformProjectedPredictableQVGrowth E c
        (fun T i => (E T i).law) (fun T i => (E T i).filtration)
        (fun T i t ω' => dot c
          (matVec ((E T i).jacobian)⁻¹ ((E T i).ipwScore t ω')))
        kFinite (fun _ => omegaMin * ‖c‖ ^ 2 / (K * D1) ^ 2) LambdaFinite := by sorry

end

end CausalSmith.Experimentation.BanditRandomQV
