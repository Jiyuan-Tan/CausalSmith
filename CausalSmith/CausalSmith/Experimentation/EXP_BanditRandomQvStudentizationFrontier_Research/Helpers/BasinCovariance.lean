/- Covariance objects associated with finite policy-state attractors. -/

import CausalSmith.Experimentation.EXP_BanditRandomQvStudentizationFrontier_Research.Helpers.Estimator
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Basin covariance construction -/

open scoped BigOperators
open MeasureTheory

namespace CausalSmith.Experimentation.BanditRandomQV

noncomputable section

variable {Ω 𝒳 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳]

def stateCovariance {K d q : ℕ} (E : AdaptiveCausalExperiment Ω 𝒳 K d q)
    (η : Vec q) (_hη : η ∈ E.stateSpace) : Mat d :=
  fun i j => ∫ ω, ∑ a,
    (E.policy a (E.context 1 ω) η)⁻¹ *
      E.score a (E.context 1 ω) (E.potentialOutcome 1 a ω) E.thetaStar i *
      E.score a (E.context 1 ω) (E.potentialOutcome 1 a ω) E.thetaStar j ∂E.law
  -- @realizes \Gamma_P(state-indexed IPW score covariance)

def basinOmega {K d q m : ℕ} (E : AdaptiveCausalExperiment Ω 𝒳 K d q)
    (etaBar : Fin m → Vec q) (hetaBar : ∀ j, etaBar j ∈ E.stateSpace)
    (j : Fin m) : Mat d := stateCovariance E (etaBar j) (hetaBar j)
  -- @realizes \Omega_j(Gamma_P at attractor j)

def basinV {K d q m : ℕ} (E : AdaptiveCausalExperiment Ω 𝒳 K d q)
    (etaBar : Fin m → Vec q) (hetaBar : ∀ j, etaBar j ∈ E.stateSpace)
    (j : Fin m) : Mat d := sandwich E.jacobian (basinOmega E etaBar hetaBar j)
  -- @realizes V_j(H-inverse basin sandwich)

def selectedOmega {K d q m : ℕ} (E : AdaptiveCausalExperiment Ω 𝒳 K d q)
    (etaBar : Fin m → Vec q) (hetaBar : ∀ j, etaBar j ∈ E.stateSpace)
    (J : Ω → Fin m) : Ω → Mat d :=
  fun ω => basinOmega E etaBar hetaBar (J ω)
  -- @realizes \Omega_J(selected basin score covariance)

def selectedV {K d q m : ℕ} (E : AdaptiveCausalExperiment Ω 𝒳 K d q)
    (etaBar : Fin m → Vec q) (hetaBar : ∀ j, etaBar j ∈ E.stateSpace)
    (J : Ω → Fin m) : Ω → Mat d :=
  fun ω => basinV E etaBar hetaBar (J ω)
  -- @realizes V_J(selected basin estimator covariance)

def terminalOmega {K d q : ℕ} (E : AdaptiveCausalExperiment Ω 𝒳 K d q)
    (etaInf : Ω → Vec q) (hetaInf : ∀ ω, etaInf ω ∈ E.stateSpace) : Ω → Mat d :=
  fun ω => stateCovariance E (etaInf ω) (hetaInf ω)
  -- @realizes \Omega_\infty(covariance at terminal random state)

def terminalV {K d q : ℕ} (E : AdaptiveCausalExperiment Ω 𝒳 K d q)
    (etaInf : Ω → Vec q) (hetaInf : ∀ ω, etaInf ω ∈ E.stateSpace) : Ω → Mat d :=
  fun ω => sandwich E.jacobian (terminalOmega E etaInf hetaInf ω)
  -- @realizes V_\infty(terminal random sandwich covariance)

def basinMass {m : ℕ} (μ : Measure Ω) (J : Ω → Fin m) (j : Fin m) : ℝ :=
  (μ {ω | J ω = j}).toReal
  -- @realizes p_j(P(J=j) basin mass)

lemma terminalOmega_eq_selectedOmega {K d q m : ℕ}
    (E : AdaptiveCausalExperiment Ω 𝒳 K d q)
    (etaBar : Fin m → Vec q) (hetaBar : ∀ j, etaBar j ∈ E.stateSpace)
    (J : Ω → Fin m) (etaInf : Ω → Vec q)
    (hetaInf : ∀ ω, etaInf ω ∈ E.stateSpace)
    (hselect : etaInf =ᵐ[E.law] fun ω => etaBar (J ω)) :
    terminalOmega E etaInf hetaInf =ᵐ[E.law] selectedOmega E etaBar hetaBar J := by sorry

lemma terminalV_eq_selectedV {K d q m : ℕ}
    (E : AdaptiveCausalExperiment Ω 𝒳 K d q)
    (etaBar : Fin m → Vec q) (hetaBar : ∀ j, etaBar j ∈ E.stateSpace)
    (J : Ω → Fin m) (etaInf : Ω → Vec q)
    (hetaInf : ∀ ω, etaInf ω ∈ E.stateSpace)
    (hselect : etaInf =ᵐ[E.law] fun ω => etaBar (J ω)) :
    terminalV E etaInf hetaInf =ᵐ[E.law] selectedV E etaBar hetaBar J := by sorry

/-- The complete terminal-representative covariance construction.  This
bundle keeps the basin masses, basin and selected covariances, terminal
covariances, and both finite-tail substitution identities attached to the
same experiment and label. -/
structure BasinCovarianceBundle {K d q m : ℕ}
    (E : AdaptiveCausalExperiment Ω 𝒳 K d q)
    (etaBar : Fin m → Vec q) (hetaBar : ∀ j, etaBar j ∈ E.stateSpace)
    (J : Ω → Fin m) (etaInf : Ω → Vec q)
    (hetaInf : ∀ ω, etaInf ω ∈ E.stateSpace) where
  gamma : {η : Vec q // η ∈ E.stateSpace} → Mat d
  gamma_eq : ∀ η, gamma η = stateCovariance E η.1 η.2
  p : Fin m → ℝ -- @realizes p_j(basin probability mass)
  p_eq : ∀ j, p j = basinMass E.law J j
  omega : Fin m → Mat d -- @realizes \Omega_j(state covariance at attractor j)
  omega_eq : ∀ j, omega j = basinOmega E etaBar hetaBar j
  v : Fin m → Mat d -- @realizes V_j(basin sandwich covariance)
  v_eq : ∀ j, v j = basinV E etaBar hetaBar j
  omegaJ : Ω → Mat d -- @realizes \Omega_J(label-selected basin covariance)
  omegaJ_eq : omegaJ = selectedOmega E etaBar hetaBar J
  vJ : Ω → Mat d -- @realizes V_J(label-selected basin sandwich)
  vJ_eq : vJ = selectedV E etaBar hetaBar J
  omegaInf : Ω → Mat d -- @realizes \Omega_\infty(covariance at terminal state)
  omegaInf_eq : omegaInf = terminalOmega E etaInf hetaInf
  vInf : Ω → Mat d -- @realizes V_\infty(terminal sandwich covariance)
  vInf_eq : vInf = terminalV E etaInf hetaInf
  omega_substitution : omegaInf =ᵐ[E.law] omegaJ
  v_substitution : vInf =ᵐ[E.law] vJ

-- @node: def:basin-covariance
noncomputable def basinCovarianceBundle {K d q m : ℕ}
    (E : AdaptiveCausalExperiment Ω 𝒳 K d q)
    (etaBar : Fin m → Vec q) (hetaBar : ∀ j, etaBar j ∈ E.stateSpace)
    (J : Ω → Fin m) (etaInf : Ω → Vec q)
    (hetaInf : ∀ ω, etaInf ω ∈ E.stateSpace)
    (hselect : etaInf =ᵐ[E.law] fun ω => etaBar (J ω)) :
    BasinCovarianceBundle E etaBar hetaBar J etaInf hetaInf where
  gamma := fun η => stateCovariance E η.1 η.2
  gamma_eq := by intro; rfl
  p := basinMass E.law J
  p_eq := by intro; rfl
  omega := basinOmega E etaBar hetaBar
  omega_eq := by intro; rfl
  v := basinV E etaBar hetaBar
  v_eq := by intro; rfl
  omegaJ := selectedOmega E etaBar hetaBar J
  omegaJ_eq := rfl
  vJ := selectedV E etaBar hetaBar J
  vJ_eq := rfl
  omegaInf := terminalOmega E etaInf hetaInf
  omegaInf_eq := rfl
  vInf := terminalV E etaInf hetaInf
  vInf_eq := rfl
  omega_substitution := terminalOmega_eq_selectedOmega E etaBar hetaBar J etaInf hetaInf hselect
  v_substitution := terminalV_eq_selectedV E etaBar hetaBar J etaInf hetaInf hselect

/-- Early fixed-tie-broken nearest-attractor decoder.  The `nearest` argument
is the fixed measurable nearest-point rule chosen by the construction. -/
def earlyBasinLabel {q m : ℕ} (default : Fin m) (nearest : Vec q → Fin m)
    (k : ℕ) (stateAverage : Vec q) : Fin m :=
  if k = 0 then default else nearest stateAverage
  -- @realizes J_T(early nearest-attractor label with fixed tie breaking)

end

end CausalSmith.Experimentation.BanditRandomQV
