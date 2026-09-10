/- Basin-stable adaptive IPW-Z limit theorem. -/

import CausalSmith.Experimentation.EXP_BanditRandomQvStudentizationFrontier_Research.Helpers.Classes
import CausalSmith.Experimentation.EXP_BanditRandomQvStudentizationFrontier_Research.Helpers.CovarianceLaws
import CausalSmith.Experimentation.EXP_BanditRandomQvStudentizationFrontier_Research.Helpers.MartingaleCLT

/-! # Basin-stable IPW-Z asymptotics -/

open Filter MeasureTheory Set Topology

namespace CausalSmith.Experimentation.BanditRandomQV

noncomputable section

def UniformBigOInProbability {Ω I : Type*} [MeasurableSpace Ω]
    (law : PositiveHorizon → I → Measure Ω)
    (X : PositiveHorizon → I → Ω → ℝ) (rate : PositiveHorizon → ℝ) : Prop :=
  ∀ eps > 0, ∃ M ≥ 0, ∀ᶠ T : PositiveHorizon in atTop, ∀ i,
    (law T i {ω | M * rate T < |X T i ω|}).toReal ≤ eps

def WeakMatrixLawConvergence {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    [MeasurableSpace (Mat d)] (law : ℕ → Measure Ω) (V : ℕ → Ω → Mat d)
    (mu : Measure (Mat d)) : Prop :=
  ∀ f : Mat d → ℝ, Continuous f → (∃ C, ∀ A, |f A| ≤ C) →
    Tendsto (fun n => ∫ ω, f (V n ω) ∂law n) atTop (𝓝 (∫ A, f A ∂mu))

def basinStableIPWZConclusion
    {Ω 𝒳 I : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳]
    {K d q m : ℕ} [MeasurableSpace (Mat d)]
    (E : PositiveHorizon → I → AdaptiveCausalExperiment Ω 𝒳 K d q)
    (etaBar : Fin m → Vec q) (hetaBar : ∀ T i j, etaBar j ∈ (E T i).stateSpace)
    (J : ℕ → I → Ω → Fin m)
    (etaInf : ℕ → I → Ω → Vec q)
    (hetaInf : ∀ T i ω, etaInf T i ω ∈ (E T i).stateSpace)
    (rho : ℝ) (C : ∀ T i, IPWZContract Ω 𝒳 (E T i) T rho)
    (ε B D1 hmin omegaMin : ℝ) (r delta : ℕ → ℝ) : Prop :=
  (∀ T i, opNormLE (E T i).jacobian (K * D1)) ∧
  (∀ T i j, psdLE (omegaMin • identMat d)
      (basinOmega (E T i) etaBar (hetaBar T i) j) ∧
    psdLE (basinOmega (E T i) etaBar (hetaBar T i) j)
      ((K * B ^ 2 / ε) • identMat d)) ∧
  (∀ T i, terminalOmega (E T i) (etaInf T i) (hetaInf T i) =ᵐ[(E T i).law]
    selectedOmega (E T i) etaBar (hetaBar T i) (J T i)) ∧
  (∀ T i, terminalV (E T i) (etaInf T i) (hetaInf T i) =ᵐ[(E T i).law]
    selectedV (E T i) etaBar (hetaBar T i) (J T i)) ∧
  (∃ C0 ≥ 0, ∀ T i,
    ∫ ω, matrixOperatorNorm ((T : ℝ)⁻¹ • (E T i).predictableQV T ω -
      selectedOmega (E T i) etaBar (hetaBar T i) (J T i) ω) ∂(E T i).law ≤
        C0 * (r T + delta T)) ∧
  (∀ u > 0, ∀ eps > 0, ∀ᶠ T in atTop, ∀ i,
    ((E T i).law {ω | u < ‖(C T i).tilde ω - (E T i).thetaStar‖}).toReal ≤ eps) ∧
  UniformBigOInProbability (fun T i => (E T i).law)
    (fun T i ω => ‖empiricalMoment (E T i) T ω (E T i).thetaStar‖)
    (fun T => (T : ℝ)⁻¹.sqrt) ∧
  UniformBigOInProbability (fun T i => (E T i).law)
    (fun T i ω => ‖fderiv ℝ (empiricalMoment (E T i) T ω) (E T i).thetaStar -
      (E T i).jacobianMap‖)
    (fun T => (T : ℝ)⁻¹.sqrt) ∧
  (∀ eps > 0, ∀ᶠ T in atTop, ∀ i,
    ((E T i).law {ω | ¬ (∃! θ : Vec d,
      θ ∈ Metric.closedBall (E T i).thetaStar rho ∧
      empiricalMoment (E T i) T ω θ = 0)}).toReal ≤ eps) ∧
  (∀ eps > 0, ∀ᶠ T in atTop, ∀ i,
    ((E T i).law {ω | ¬ (∃! θ : Vec d, θ ∈ localRootSet (E T i).parameterSet
      (empiricalMoment (E T i) T ω) ((C T i).tilde ω) rho)}).toReal ≤ eps) ∧
  (∀ eps > 0, ∀ᶠ T in atTop, ∀ i,
    ((E T i).law (exactRootEvent (fun ω => localRootSet (E T i).parameterSet
      (empiricalMoment (E T i) T ω) ((C T i).tilde ω) rho))ᶜ).toReal ≤ eps) ∧
  UniformBigOInProbability (fun T i => (E T i).law)
    (fun T i ω => ‖Real.sqrt T • (ipwZEstimator (C T i) ω - (E T i).thetaStar) +
      matVec ((E T i).jacobian)⁻¹ ((T : ℝ)⁻¹.sqrt • (E T i).scoreSum T ω)‖)
    (fun T => (T : ℝ)⁻¹.sqrt + r T + delta T) ∧
  (∀ eps > 0, ∀ᶠ T in atTop, ∀ i j c z, ‖c‖ = 1 →
    |conditionalEventProb (E T i).law
      {ω | dot c (Real.sqrt T • (ipwZEstimator (C T i) ω - (E T i).thetaStar)) ≤ z}
      {ω | J T i ω = j} -
      Causalean.Mathlib.stdNormalCDF
        (z / Real.sqrt (qform (basinV (E T i) etaBar (hetaBar T i) j) c))| ≤ eps) ∧
  (∀ eps > 0, ∀ᶠ T in atTop, ∀ i c z, ‖c‖ = 1 →
    ∀ psi : Fin m → ℝ, (∀ j, psi j ∈ Icc (-1 : ℝ) 1) →
    |(∫ ω, psi (J T i ω) * (if dot c (Real.sqrt T •
        (ipwZEstimator (C T i) ω - (E T i).thetaStar)) ≤ z then 1 else 0)
        ∂(E T i).law) -
      ∑ j, ((E T i).law {ω | J T i ω = j}).toReal * psi j *
        Causalean.Mathlib.stdNormalCDF
          (z / Real.sqrt (qform (basinV (E T i) etaBar (hetaBar T i) j) c))| ≤ eps) ∧
  (∀ T i j, psdLE ((omegaMin / (K * D1) ^ 2) • identMat d)
      (basinV (E T i) etaBar (hetaBar T i) j) ∧
    psdLE (basinV (E T i) etaBar (hetaBar T i) j)
      ((K * B ^ 2 / (ε * hmin ^ 2)) • identMat d)) ∧
  ∀ path : PositiveHorizon → I,
    ∃ (nk : ℕ → PositiveHorizon) (mu : Measure (Mat d)),
    StrictMono nk ∧ mu univ = 1 ∧
    mu {V | psdLE ((omegaMin / (K * D1) ^ 2) • identMat d) V ∧
      psdLE V ((K * B ^ 2 / (ε * hmin ^ 2)) • identMat d)} = 1 ∧
    WeakMatrixLawConvergence
      (fun n => (E (nk n) (path (nk n))).law)
      (fun n => selectedV (E (nk n) (path (nk n))) etaBar
        (hetaBar (nk n) (path (nk n))) (J (nk n) (path (nk n)))) mu ∧
    ∀ c, c ≠ 0 →
      (∀ z, Tendsto (fun n => ((E (nk n) (path (nk n))).law
        {ω | dot c (Real.sqrt (nk n) •
          (ipwZEstimator (C (nk n) (path (nk n))) ω -
            (E (nk n) (path (nk n))).thetaStar)) ≤ z}).toReal) atTop
        (𝓝 (∫ V, Causalean.Mathlib.stdNormalCDF
          (z / Real.sqrt (qform V c)) ∂mu))) ∧
      ((∃ variance > 0, ∀ z, (∫ V, Causalean.Mathlib.stdNormalCDF
          (z / Real.sqrt (qform V c)) ∂mu) =
          Causalean.Mathlib.stdNormalCDF (z / Real.sqrt variance)) ↔
        ∃ variance > 0, ∀ᵐ V ∂mu, qform V c = variance)

-- @node: thm:basin-stable-ipwz
theorem basin_stable_ipwz
    {Ω 𝒳 I : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳]
    {K d q m : ℕ} [MeasurableSpace (Mat d)]
    (E : PositiveHorizon → I → AdaptiveCausalExperiment Ω 𝒳 K d q)
    (etaBar : Fin m → Vec q) (J : ℕ → I → Ω → Fin m)
    (etaInf : ℕ → I → Ω → Vec q)
    (rho : ℝ) (C : ∀ T i, IPWZContract Ω 𝒳 (E T i) T rho)
    (ε B D1 D2 hmin LPi omegaMin sEta pmin sTheta : ℝ)
    (κ : ℝ → ℝ) (r delta : ℕ → ℝ)
    (hClass : ∀ T i, FiniteAttractorClass (E T i) etaBar (J T i) (etaInf T i)
      ε B rho D1 D2 hmin LPi omegaMin sEta pmin sTheta κ r delta)
    (horizon_eq : ∀ T i, (E T i).horizon = T)
    (contract_moduli : ∀ T i, (C T i).r = r T ∧ (C T i).failure = delta T)
    (jacobian_derivative : ∀ T i, (E T i).jacobianMap =
      fderiv ℝ (E T i).populationMoment (E T i).thetaStar) :
    basinStableIPWZConclusion E etaBar (fun T i => (hClass T i).etaBar_mem)
      J etaInf (fun T i => (hClass T i).etaInf_mem) rho C ε B D1 hmin omegaMin r delta := by sorry

end

end CausalSmith.Experimentation.BanditRandomQV
