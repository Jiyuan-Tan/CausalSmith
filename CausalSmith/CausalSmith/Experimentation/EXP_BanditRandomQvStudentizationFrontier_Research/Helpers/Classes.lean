/- Shared law-class structures for the random-QV frontier. -/

import CausalSmith.Experimentation.EXP_BanditRandomQvStudentizationFrontier_Research.Helpers.BasinCovariance

/-! # Finite-attractor and projected-QV law classes -/

open Filter MeasureTheory Topology

namespace CausalSmith.Experimentation.BanditRandomQV

noncomputable section

variable {Ω 𝒳 ι : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳]
  {K d q m : ℕ}

-- @node: def:finite-attractor-class
structure FiniteAttractorClass
    (E : AdaptiveCausalExperiment Ω 𝒳 K d q) (etaBar : Fin m → Vec q)
    (J : Ω → Fin m) (etaInf : Ω → Vec q)
    (ε B ρ D1 D2 hmin LPi omegaMin sEta pmin sTheta : ℝ)
    (κ : ℝ → ℝ) (r δ : ℕ → ℝ) : Prop where
  iid : IIDFullData E
  randomized : SequentialRandomization E
  overlap : UniformOverlap E ε
  bounded : BoundedScore E B
  smooth : SmoothZMap E ρ D1 D2
  separatedRoot : UniformRootSeparation E κ
  interiorRoot : RootInterior E sTheta
  nonsingular : JacobianNonsingular E hmin
  lipschitzPolicy : PolicyLipschitz E LPi
  etaBar_mem : ∀ j, etaBar j ∈ E.stateSpace
  etaInf_mem : ∀ ω, etaInf ω ∈ E.stateSpace
  separatedAttractors : FiniteAttractorSeparation etaBar sEta
  terminalLabel_spec :
    Measurable[⨆ t, E.filtration t] J ∧ etaInf =ᵐ[E.law] fun ω => etaBar (J ω)
  tailSelection : FiniteTailSelection E m etaBar etaInf := ⟨J, terminalLabel_spec⟩
  basinMass : BasinMassFloor E.law J pmin
  attraction : UniformAttractionModulus E etaBar J r δ
  vanishing : VanishingModulus r δ
  radius_range : ρ < sTheta ∧ D2 * ρ / ε < hmin / 4
    -- @realizes \rho(radius below interior and curvature thresholds)
  nondegenerate : BasinNondegeneracy (terminalOmega E etaInf etaInf_mem) E.law omegaMin
  -- @realizes \mathfrak P_T(finite-tail-attractor law membership)

-- @node: def:projected-qv-growth-ipwz-class
structure ProjectedQVGrowthIPWZClass
    (E : PositiveHorizon → ι → AdaptiveCausalExperiment Ω 𝒳 K d q)
    (Theta : Set (Vec d))
    (c : Vec d) (ε B ρ D1 D2 hmin sTheta : ℝ) (κ : ℝ → ℝ)
    (r δ omega : ℕ → ℝ) (k : ℕ → ℕ)
    (Lambda : PositiveHorizon → ι → Ω → ℝ) : Prop where
  contrast_ne : c ≠ 0 -- @realizes c(nonzero prespecified contrast)
  horizon_eq : ∀ T i, (E T i).horizon = T
  parameter_set : ∀ T i, (E T i).parameterSet = Theta
    -- @realizes \Theta(fixed parameter set across all positive horizons and members)
  iid : ∀ T i, IIDFullData (E T i)
  randomized : ∀ T i, SequentialRandomization (E T i)
  overlap : ∀ T i, UniformOverlap (E T i) ε
  bounded : ∀ T i, BoundedScore (E T i) B
  smooth : ∀ T i, SmoothZMap (E T i) ρ D1 D2
  separatedRoot : ∀ T i, UniformRootSeparation (E T i) κ
  interiorRoot : ∀ T i, RootInterior (E T i) sTheta
  nonsingular : ∀ T i, JacobianNonsingular (E T i) hmin
  vanishing : VanishingModulus r δ
  radius_range : ρ < sTheta ∧ D2 * ρ / ε < hmin / 4
    -- @realizes \rho(radius below interior and curvature thresholds)
  cutoff : ∀ T : PositiveHorizon, k T < T
  floor_pos : ∀ T : PositiveHorizon, 0 < omega T -- @realizes \omega_{c,T}(positive deterministic scale floor)
  scale_measurable : ∀ T : PositiveHorizon, ∀ i,
    Measurable[(E T i).filtration (k T)] (Lambda T i)
  scale_floor : ∀ T : PositiveHorizon, ∀ i,
    ∀ᵐ ω' ∂(E T i).law, omega T ≤ Lambda T i ω'
  information_growth : Tendsto (fun (T : ℕ) => (T : ℝ) * omega T) atTop atTop
  prefix_negligible : Tendsto (fun (T : ℕ) => (k T : ℝ) / ((T : ℝ) * omega T)) atTop (𝓝 0)
  projected_qv : UniformProjectedPredictableQVGrowth
    E c
    (fun T i => (E T i).law) (fun T i => (E T i).filtration)
    (fun T i t ω' => dot c (matVec ((E T i).jacobian)⁻¹ ((E T i).ipwScore t ω')))
    k omega Lambda
  -- @realizes \mathfrak Q_T^{\mathrm{proj}}(c)(early-stabilized projected law class)

end

end CausalSmith.Experimentation.BanditRandomQV
