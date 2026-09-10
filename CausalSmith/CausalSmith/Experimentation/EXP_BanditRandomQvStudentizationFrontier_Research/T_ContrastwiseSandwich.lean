/- Identification of a scale mixture from all nominal coverage levels. -/

import CausalSmith.Experimentation.EXP_BanditRandomQvStudentizationFrontier_Research.T_BasinStableIPWZ

/-! # Contrastwise deterministic-sandwich boundary -/

open Filter MeasureTheory Set Topology

namespace CausalSmith.Experimentation.BanditRandomQV

noncomputable section

def scaleMixtureCoverage {d : ℕ} [MeasurableSpace (Mat d)]
    (mu : Measure (Mat d)) (Sigma : Mat d) (c : Vec d) (alpha : ℝ) : ℝ :=
  ∫ V, 2 * Causalean.Mathlib.stdNormalCDF
    (Causalean.Mathlib.probit (1 - alpha / 2) *
      Real.sqrt (qform Sigma c / qform V c)) - 1 ∂mu

/-- A concrete horizon-asymptotic sequence inside the finite-attractor class,
together with the weak covariance-law limit used in Theorems 3 and 4. -/
structure FiniteAttractorSandwichSequence
    (Ω 𝒳 : Type*) [MeasurableSpace Ω] [MeasurableSpace 𝒳]
    (K d q m : ℕ) [MeasurableSpace (Mat d)] where
  T : ℕ → ℕ
  T_pos : ∀ l, 0 < T l
  T_tendsto : Tendsto T atTop atTop
  E : ℕ → AdaptiveCausalExperiment Ω 𝒳 K d q
  horizon_eq : ∀ l, (E l).horizon = T l
  etaBar : Fin m → Vec q
  J : ℕ → Ω → Fin m
  etaInf : ℕ → Ω → Vec q
  rho : ℝ
  ε : ℝ
  B : ℝ
  D1 : ℝ
  D2 : ℝ
  hmin : ℝ
  LPi : ℝ
  omegaMin : ℝ
  sEta : ℝ
  pmin : ℝ
  sTheta : ℝ
  kappa : ℝ → ℝ
  r : ℕ → ℝ
  delta : ℕ → ℝ
  estimator : ∀ l, IPWZContract Ω 𝒳 (E l) (T l) rho
  estimator_r : ∀ l, (estimator l).r = r (T l)
  estimator_failure : ∀ l, (estimator l).failure = delta (T l)
  member : ∀ l, FiniteAttractorClass (E l) etaBar (J l) (etaInf l)
    ε B rho D1 D2 hmin LPi omegaMin sEta pmin sTheta kappa r delta
  mu : Measure (Mat d)
  mu_probability : mu univ = 1
  mu_compact_covariance_support : mu {V |
    psdLE ((omegaMin / (K * D1) ^ 2) • identMat d) V ∧
    psdLE V ((K * B ^ 2 / (ε * hmin ^ 2)) • identMat d)} = 1
  terminalV_aemeasurable : ∀ l,
    AEMeasurable (terminalV (E l) (etaInf l) (member l).etaInf_mem) (E l).law
  covariance_weak_limit : WeakMatrixLawConvergence
    (fun l => (E l).law)
    (fun l => terminalV (E l) (etaInf l) (member l).etaInf_mem) mu
  jacobian_derivative : ∀ l, (E l).jacobianMap =
    fderiv ℝ (E l).populationMoment (E l).thetaStar

-- @node: thm:contrastwise-deterministic-sandwich-iff
theorem contrastwise_deterministic_sandwich_iff
    {Ω 𝒳 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳]
    {K d q m : ℕ} [MeasurableSpace (Mat d)] [BorelSpace (Mat d)]
    (S : FiniteAttractorSandwichSequence Ω 𝒳 K d q m)
    (Sigma : Mat d) (hSigma : PositiveDefinite Sigma)
    (c : Vec d) (hc : c ≠ 0) :
    (∀ alpha, ∀ halpha : 0 < alpha ∧ alpha < 1,
      Tendsto (fun l => ((S.E l).law {ω |
        dot c (S.E l).thetaStar ∈ deterministicWaldInterval (S.T l)
          (ipwZEstimator (S.estimator l)) (S.T_pos l) Sigma hSigma c hc alpha halpha ω}).toReal)
        atTop (𝓝 (1 - alpha))) ↔
      (∀ᵐ V ∂S.mu, qform V c = qform Sigma c) := by sorry

end

end CausalSmith.Experimentation.BanditRandomQV
