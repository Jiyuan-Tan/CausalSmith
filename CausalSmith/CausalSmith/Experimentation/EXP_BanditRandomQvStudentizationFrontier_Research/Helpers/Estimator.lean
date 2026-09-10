/- Total IPW-Z estimators and their deterministic and random-QV Wald reports. -/

import CausalSmith.Experimentation.EXP_BanditRandomQvStudentizationFrontier_Research.Basic
import Causalean.Mathlib.Probability.StdNormalCDF
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Estimator constructions -/

open Set

namespace CausalSmith.Experimentation.BanditRandomQV

noncomputable section
set_option linter.style.openClassical false
open Classical

def localRootSet {d : ℕ} (Theta : Set (Vec d)) (G : Vec d → Vec d)
    (tilde : Vec d) (ρ : ℝ) : Set (Vec d) :=
  {θ | θ ∈ Theta ∧ G θ = 0 ∧ ‖θ - tilde‖ ≤ ρ / 2}
  -- @realizes \mathcal Z_T(local exact-root correspondence)

def exactRootEvent {Ω : Type*} {d : ℕ} (Z : Ω → Set (Vec d)) : Set Ω :=
  {ω | (Z ω).Nonempty}
  -- @realizes E_T(nonempty-root event)

def LexLE {d : ℕ} (x y : Vec d) : Prop :=
  x = y ∨ ∃ j : Fin d, (∀ i : Fin d, i < j → x i = y i) ∧ x j < y j

/-- The exact preliminary-estimator and measurable lexicographic-selection
contract used by the paper, for one positive horizon. -/
def empiricalMoment {Ω 𝒳 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳]
    {K d q : ℕ} (E : AdaptiveCausalExperiment Ω 𝒳 K d q) (T : ℕ)
    (ω : Ω) (θ : Vec d) : Vec d :=
  (T : ℝ)⁻¹ • ∑ t ∈ Finset.Icc 1 T,
    (E.loggedPropensity t (E.action t ω) ω)⁻¹ •
      E.score (E.action t ω) (E.context t ω) (E.observedOutcome t ω) θ
  -- @realizes G_T(canonical empirical IPW moment)

structure IPWZContract (Ω 𝒳 : Type*) [MeasurableSpace Ω] [MeasurableSpace 𝒳]
    {K d q : ℕ} (E : AdaptiveCausalExperiment Ω 𝒳 K d q) (T : ℕ) (rho : ℝ) where
  T_pos : 0 < T
  rho_pos : 0 < rho
  G_continuous : ∀ ω, ContinuousOn (empiricalMoment E T ω) E.parameterSet
  G_joint_measurable : Measurable (fun p : Ω × Vec d => empiricalMoment E T p.1 p.2)
  tilde : Ω → Vec d
  tilde_measurable : Measurable tilde
  tilde_mem : ∀ ω, tilde ω ∈ E.parameterSet
  r : ℝ
  failure : ℝ
  r_nonneg : 0 ≤ r
  failure_nonneg : 0 ≤ failure
  approximate_minimizer : ∀ ω,
    ‖empiricalMoment E T ω (tilde ω)‖ ≤
      sInf (norm '' empiricalMoment E T ω '' E.parameterSet) +
      (T : ℝ)⁻¹.sqrt * (r + failure)
  select : Ω → Vec d
  select_measurable : Measurable select
  root_event_measurable : MeasurableSet {ω |
    (localRootSet E.parameterSet (empiricalMoment E T ω) (tilde ω) rho).Nonempty}
  select_mem : ∀ ω, (localRootSet E.parameterSet (empiricalMoment E T ω) (tilde ω) rho).Nonempty →
    select ω ∈ localRootSet E.parameterSet (empiricalMoment E T ω) (tilde ω) rho
  select_lexicographic : ∀ ω θ,
    θ ∈ localRootSet E.parameterSet (empiricalMoment E T ω) (tilde ω) rho →
      LexLE (select ω) θ
  Hhat : Ω → Mat d
  Hhat_derivative : ∀ ω v, matVec (Hhat ω) v =
    fderiv ℝ (empiricalMoment E T ω) (if
      (localRootSet E.parameterSet (empiricalMoment E T ω) (tilde ω) rho).Nonempty
      then select ω else tilde ω) v

-- @node: def:ipw-z-estimator
def ipwZEstimator {Ω 𝒳 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳]
    {K d q T : ℕ} {rho : ℝ} {E : AdaptiveCausalExperiment Ω 𝒳 K d q}
    (C : IPWZContract Ω 𝒳 E T rho) : Ω → Vec d :=
  fun ω => if (localRootSet E.parameterSet (empiricalMoment E T ω) (C.tilde ω) rho).Nonempty then
    C.select ω else C.tilde ω
  -- @realizes G_T(random empirical moment map)
  -- @realizes \widetilde\theta_T(preliminary approximate minimizer)
  -- @realizes \widehat\theta_T(exact root with fallback)

def feasibleScore {Ω 𝒳 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳]
    {K d q T : ℕ} {rho : ℝ} {E : AdaptiveCausalExperiment Ω 𝒳 K d q}
    (C : IPWZContract Ω 𝒳 E T rho) (t : ℕ) : Ω → Vec d :=
  fun ω => (E.loggedPropensity t (E.action t ω) ω)⁻¹ •
    E.score (E.action t ω) (E.context t ω) (E.observedOutcome t ω) (ipwZEstimator C ω)
  -- @realizes \widehat\xi_t(feasible score at estimated root)

def empiricalOmega {Ω : Type*} {d : ℕ} (T : ℕ)
    (xiHat : ℕ → Ω → Vec d) : Ω → Mat d :=
  fun ω => (T : ℝ)⁻¹ • ∑ t ∈ Finset.Icc 1 T, outer (xiHat t ω) (xiHat t ω)
  -- @realizes \widehat\xi_t(feasible score at estimated root)
  -- @realizes \widehat\Omega_T(realized feasible score covariance)

def invertibilityEvent {Ω : Type*} {d : ℕ} (Hhat : Ω → Mat d) (hmin : ℝ) : Set Ω :=
  {ω | ∀ v, hmin / 2 * ‖v‖ ≤ ‖matVec (Hhat ω) v‖}
  -- @realizes \mathcal H_T(empirical Jacobian invertibility event)
  -- @realizes \widehat H_T(empirical Jacobian)

def sandwich {d : ℕ} (H Omega : Mat d) : Mat d :=
  H⁻¹ * Omega * transpose H⁻¹

def totalContrastVariance {Ω : Type*} {d : ℕ} (T : ℕ)
    (xiHat : ℕ → Ω → Vec d) (Hhat : Ω → Mat d)
    (hmin : ℝ) (c : Vec d) : Ω → ℝ :=
  fun ω => if ω ∈ invertibilityEvent Hhat hmin then
    qform (sandwich (Hhat ω) (empiricalOmega T xiHat ω)) c else 0
  -- @realizes \widehat q_T(c)(zero off invertibility event)
  -- @realizes \widehat\Omega_T(empirical positive-semidefinite score covariance input)

def contrastTruncationEvent {Ω : Type*} {d : ℕ} (T : ℕ)
    (xiHat : ℕ → Ω → Vec d) (Hhat : Ω → Mat d)
    (hmin omega : ℝ) (c : Vec d) : Set Ω :=
  invertibilityEvent Hhat hmin ∩
    {ω | omega / 2 ≤ totalContrastVariance T xiHat Hhat hmin c ω}
  -- @realizes \mathcal E_T(joint invertibility and information event)

-- @node: def:event-truncated-rqv-sandwich
def eventTruncatedRQVSandwich {Ω : Type*} {d : ℕ} (T : ℕ)
    (xiHat : ℕ → Ω → Vec d) (Hhat : Ω → Mat d)
    (_hT : 0 < T) (hmin omega : ℝ) (_hhmin : 0 < hmin) (_homega : 0 < omega)
    (c : Vec d) (_hc : c ≠ 0) : Ω → Mat d :=
  fun ω' => if ω' ∈ contrastTruncationEvent T xiHat Hhat hmin omega c then
    sandwich (Hhat ω') (empiricalOmega T xiHat ω') else identMat d
  -- @realizes \widehat V_T(contrast-specific event-truncated sandwich)

-- @node: def:realized-qv-pivot
def realizedQVPivot {Ω : Type*} {d : ℕ} (T : ℕ) (hT : 0 < T)
    (c thetaStar : Vec d) (hc : c ≠ 0) (thetaHat : Ω → Vec d)
    (xiHat : ℕ → Ω → Vec d) (Hhat : Ω → Mat d) (hmin omega : ℝ)
    (hhmin : 0 < hmin) (homega : 0 < omega) : Ω → ℝ :=
  fun ω' => Real.sqrt T * dot c (thetaHat ω' - thetaStar) /
    Real.sqrt (qform (eventTruncatedRQVSandwich T xiHat Hhat hT hmin omega hhmin homega c hc ω') c)
  -- @realizes T_T^{\mathrm{rqv}}(c)(realized-QV studentized statistic)
  -- @realizes \tau(c-transpose theta-star target contrast)

-- @node: def:deterministic-wald-interval
def deterministicWaldInterval {Ω : Type*} {d : ℕ} (T : ℕ) (thetaHat : Ω → Vec d)
    (_hT : 0 < T) (Sigma : Mat d) (_hSigma : PositiveDefinite Sigma)
    (c : Vec d) (_hc : c ≠ 0) (alpha : ℝ)
    (_halpha : 0 < alpha ∧ alpha < 1) : Ω → Set ℝ :=
  fun ω => let z := Causalean.Mathlib.probit (1 - alpha / 2)
    Icc (dot c (thetaHat ω) - z * Real.sqrt (qform Sigma c / T))
      (dot c (thetaHat ω) + z * Real.sqrt (qform Sigma c / T))
  -- @realizes \Sigma(deterministic positive-definite comparator matrix)
  -- @realizes \alpha(nominal noncoverage level)
  -- @realizes \Phi(standard normal CDF via Causalean.Mathlib.stdNormalCDF)
  -- @realizes z_{1-\alpha/2}(probit critical value)
  -- @realizes C_T^{\Sigma}(c,\alpha)(deterministic-sandwich Wald interval)

-- @node: def:realized-qv-wald-interval
def realizedQVWaldInterval {Ω : Type*} {d : ℕ} (T : ℕ) (_hT : 0 < T)
    (tauHat : Ω → ℝ) (xiHat : ℕ → Ω → Vec d) (Hhat : Ω → Mat d)
    (hmin omega : ℝ) (hhmin : 0 < hmin) (homega : 0 < omega)
    (c : Vec d) (hc : c ≠ 0)
    (alpha : ℝ) (_halpha : 0 < alpha ∧ alpha < 1) : Ω → Set ℝ :=
  fun ω => let z := Causalean.Mathlib.probit (1 - alpha / 2)
    let Vhat := eventTruncatedRQVSandwich T xiHat Hhat _hT hmin omega hhmin homega c hc
    Icc (tauHat ω - z * Real.sqrt (qform (Vhat ω) c / T))
      (tauHat ω + z * Real.sqrt (qform (Vhat ω) c / T))
  -- @realizes \widehat\tau_T(estimated causal contrast)
  -- @realizes I_T^{\mathrm{rqv}}(c,\alpha)(realized-QV Wald interval)

end

end CausalSmith.Experimentation.BanditRandomQV
