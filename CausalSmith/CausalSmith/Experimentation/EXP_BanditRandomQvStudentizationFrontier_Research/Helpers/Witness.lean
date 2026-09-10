/- Full product-law construction for the directional-versus-matrix witness. -/

import CausalSmith.Experimentation.EXP_BanditRandomQvStudentizationFrontier_Research.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProductMeasure

/-! # Directional matrix witness -/

namespace CausalSmith.Experimentation.BanditRandomQV

noncomputable section
open MeasureTheory

/-- One occasion's independent assignment randomizer and three potential-outcome signs. -/
abbrev DirectionalNoise := Fin 120 × (Fin 3 → Bool)

/-- The full infinite product sample; a horizon uses its first `T` coordinates. -/
abbrev DirectionalPath := ℕ → DirectionalNoise

def directionalNoiseLaw : Measure DirectionalNoise :=
  (PMF.uniformOfFintype DirectionalNoise).toMeasure

def directionalProductLaw : Measure DirectionalPath :=
  Measure.infinitePi (fun _ : ℕ => directionalNoiseLaw)
  -- @realizes P^{\dagger}(independent time-indexed product law)

def directionalPolicy (a : Fin 3) (η : ℝ) : ℝ :=
  (1 - η) * (![2 / 5, 1 / 4, 7 / 20] : Fin 3 → ℝ) a +
    η * (![2 / 5, 1 / 6, 13 / 30] : Fin 3 → ℝ) a

def directionalDrawArm (η : ℝ) (u : Fin 120) : Fin 3 :=
  if u.1 < 48 then 0
  else if η = 0 ∧ u.1 < 78 then 1
  else if η = 1 ∧ u.1 < 68 then 1
  else if η ≠ 0 ∧ η ≠ 1 ∧ u.1 < 73 then 1
  else 2

def directionalFirstArm (ω : DirectionalPath) : Fin 3 :=
  directionalDrawArm (1 / 2) (ω 1).1

def directionalLabel (ω : DirectionalPath) : Fin 2 :=
  if directionalFirstArm ω = 0 then 0 else 1

def directionalState (t : ℕ) (ω : DirectionalPath) : ℝ :=
  if t = 0 then 1 / 2 else if directionalLabel ω = 0 then 0 else 1

def directionalAssignment (t : ℕ) (ω : DirectionalPath) : Fin 3 :=
  directionalDrawArm (directionalState (t - 1) ω) (ω t).1

def directionalTerminalState (ω : DirectionalPath) : ℝ :=
  if directionalLabel ω = 0 then 0 else 1

def directionalSign (b : Bool) : ℝ := if b then 1 else -1

def directionalPotentialOutcome (t : ℕ) (a : Fin 3) (ω : DirectionalPath) : ℝ :=
  if a = 0 then directionalSign ((ω t).2 a) * Real.sqrt (2 / 5)
  else if a = 1 then directionalSign ((ω t).2 a) * Real.sqrt (1 / 2)
  else 0

/-- The complete horizon-indexed witness, including all time-indexed variables
and the independent product law from which they are generated. -/
structure DirectionalWitnessData where
  horizon : ℕ
  horizon_ge : 2 ≤ horizon
  law : Measure DirectionalPath
  context : ℕ → DirectionalPath → Unit
  assignment : ℕ → DirectionalPath → Fin 3
  potentialOutcome : ℕ → Fin 3 → DirectionalPath → ℝ
  stateSpace : Set ℝ -- @realizes \mathsf H(explicit scalar carrier)
  state : ℕ → DirectionalPath → ℝ
  policy0 : Fin 3 → ℝ
  policy1 : Fin 3 → ℝ
  eta0 : ℝ
  thetaStar : Vec 2
  covariance : Fin 2 → Mat 2
  basinMass : Fin 2 → ℝ
  parameterSet : Set (Vec 2)
  score : Fin 3 → ℝ → Vec 2 → Vec 2
  policy : Fin 3 → ℝ → ℝ
  attractor : Fin 2 → ℝ
  firstArm : DirectionalPath → Fin 3
  label : DirectionalPath → Fin 2
  terminalState : DirectionalPath → ℝ
  assignment_one : ∀ ω, assignment 1 ω = firstArm ω
  label_zero_iff : ∀ ω, label ω = 0 ↔ assignment 1 ω = 0
  state_eq_terminal : ∀ t ω, 1 ≤ t → t ≤ horizon → state t ω = terminalState ω

-- @node: def:directional-matrix-witness
def directionalMatrixWitness (T : ℕ) (hT : 2 ≤ T) : DirectionalWitnessData where
  horizon := T
  horizon_ge := hT
  law := directionalProductLaw
  context := fun _ _ => ()
  assignment := directionalAssignment
  potentialOutcome := directionalPotentialOutcome
  stateSpace := Set.Icc (0 : ℝ) 1
  state := directionalState
  policy0 := ![2 / 5, 1 / 4, 7 / 20]
  policy1 := ![2 / 5, 1 / 6, 13 / 30]
  eta0 := 1 / 2
  thetaStar := 0
  covariance := fun j => if j = 0 then !![1, 0; 0, 2] else !![1, 0; 0, 3]
  basinMass := ![2 / 5, 3 / 5]
  parameterSet := {θ | ∀ i, θ i ∈ Set.Icc (-1 : ℝ) 1}
  score := fun a y θ => if a = 0 then WithLp.toLp 2 ![y - θ 0, 0]
    else if a = 1 then WithLp.toLp 2 ![0, y - θ 1] else 0
  policy := directionalPolicy
  attractor := ![0, 1]
  firstArm := directionalFirstArm
  label := directionalLabel
  terminalState := directionalTerminalState
  assignment_one := by
    intro ω
    rfl
  label_zero_iff := by
    intro ω
    simp [directionalLabel, directionalAssignment, directionalFirstArm, directionalState]
  state_eq_terminal := by
    intro t ω ht _
    simp [directionalState, directionalTerminalState, Nat.ne_of_gt ht]
  -- @realizes T(full positive horizon)
  -- @realizes W_t(independent time-indexed full-data process)
  -- @realizes \eta_t(eta_t equals etaInf at every t at least one)

/-- Field-by-field realization relation tying an adaptive experiment to the
explicit product-law witness rather than merely equating its measure. -/
def DirectionalWitnessRealizes
  (E : AdaptiveCausalExperiment DirectionalPath Unit 3 2 1)
    (W : DirectionalWitnessData) (etaBar : Fin 2 → Vec 1)
    (J : DirectionalPath → Fin 2) (etaInf : DirectionalPath → Vec 1) : Prop :=
  E.horizon = W.horizon ∧ E.law = W.law ∧
  (∀ t, E.context t = W.context t) ∧
  (∀ t, E.action t = W.assignment t) ∧
  (∀ t a, E.potentialOutcome t a = W.potentialOutcome t a) ∧
  E.stateSpace = {η | η 0 ∈ W.stateSpace} ∧
  E.initialState 0 = W.eta0 ∧
  (∀ t ω, E.state t ω 0 = W.state t ω) ∧
  E.parameterSet = W.parameterSet ∧ E.thetaStar = W.thetaStar ∧
  (∀ a x y θ, E.score a x y θ = W.score a y θ) ∧
  (∀ a x η, E.policy a x η = W.policy a (η 0)) ∧
  (∀ j, etaBar j 0 = W.attractor j) ∧ J = W.label ∧
  (∀ ω, etaInf ω 0 = W.terminalState ω) ∧
  (∀ t ω, 1 ≤ t → t ≤ W.horizon → E.state t ω = etaInf ω)
  -- @realizes P^{\dagger}(fieldwise experiment realization)

end

end CausalSmith.Experimentation.BanditRandomQV
