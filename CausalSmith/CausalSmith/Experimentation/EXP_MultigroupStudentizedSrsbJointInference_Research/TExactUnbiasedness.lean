import CausalSmith.Experimentation.EXP_MultigroupStudentizedSrsbJointInference_Research.Basic
import Causalean.Experimentation.DesignBased.HT.Unbiased
import Causalean.Experimentation.DesignBased.Designs.CompleteRandomization

/-! Exact conditional exposure probabilities and finite-design unbiasedness. -/

namespace CausalSmith.Experimentation.MultigroupStudentizedSRSB

noncomputable section

open Causalean.Experimentation.DesignBased

def rawConditionalEvent {Omega : Type*} {G B n : ℕ}
    (x : Omega → Fin B → Fin G → Bool)
    (A : Omega → Fin B → Fin G → Fin n → Bool)
    (b : Fin B) (w z : Omega) : Prop :=
  ∀ k : Fin B, k.val < b.val → x z k = x w k ∧ A z k = A w k

noncomputable def rawConditionalE {Omega : Type*} [Fintype Omega] {G B n : ℕ}
    (D : FiniteDesign Omega)
    (x : Omega → Fin B → Fin G → Bool)
    (A : Omega → Fin B → Fin G → Fin n → Bool)
    (b : Fin B) (w : Omega) (X : Omega → ℝ) : ℝ := by
  classical
  let p := D.Pr (rawConditionalEvent x A b w)
  exact if p = 0 then 0 else
    D.E (fun z ↦ FiniteDesign.ind (rawConditionalEvent x A b w) z * X z) / p

def rawCanonicalHistory {G B n : ℕ} (d q : Bool) : GlobalHistory G B n :=
  fun _ _ ↦ (fun _ ↦ d, q)

def rawSustainedEndpoint {G B n : ℕ} (_hB : 0 < B) (Y : PotentialSchedule G B n)
    (g : Fin G) (b : Fin B) (i : Fin n) (d q : Bool) : ℝ :=
  Y g ⟨2 * b.val + 1, by omega⟩ i (rawCanonicalHistory d q)

def rawJointEstimand {G B n : ℕ} (hB : 0 < B) (Y : PotentialSchedule G B n) : Vec2 :=
  fun j ↦ ((G * B * n : ℕ) : ℝ)⁻¹ *
    ∑ b, ∑ g, ∑ i, ∑ d : Bool, ∑ q : Bool,
      contrast d q j * rawSustainedEndpoint hB Y g b i d q

def rawCellIndicator {Omega : Type*} {G B n : ℕ}
    (x : Omega → Fin B → Fin G → Bool)
    (A : Omega → Fin B → Fin G → Fin n → Bool)
    (w : Omega) (b : Fin B) (k : CellIndex G n) : ℝ :=
  if x w b k.1 = k.2.2.2 ∧ A w b k.1 k.2.1 = k.2.2.1 then 1 else 0

def rawJointHTEstimator {Omega : Type*} {G B n : ℕ}
    (x : Omega → Fin B → Fin G → Bool)
    (A : Omega → Fin B → Fin G → Fin n → Bool)
    (observed : ObservedEndpoints Omega G B n)
    (pi : InclusionProbabilities Omega G B n) (w : Omega) : Vec2 := fun j ↦
  ((G * B * n : ℕ) : ℝ)⁻¹ *
    ∑ b, ∑ g, ∑ i, ∑ d : Bool, ∑ q : Bool,
      let k : CellIndex G n := (g, i, d, q)
      contrast d q j * rawCellIndicator x A w b k * observed w g b i / pi w b k

-- @node: prop:exact-unbiasedness
theorem exact_unbiasedness {Omega : Type*} [Fintype Omega] {G B n : ℕ}
    (hB : 0 < B) (D : FiniteDesign Omega)
    (x : Omega → Fin B → Fin G → Bool)
    (A : Omega → Fin B → Fin G → Fin n → Bool)
    (Y : PotentialSchedule G B n)
    (history : Omega → GlobalHistory G B n)
    (observed : ObservedEndpoints Omega G B n)
    (pi : InclusionProbabilities Omega G B n)
    (P0 : Omega → Fin B → FiniteDesign Omega)
    (V : Omega → Fin B → Fin G → ℝ) (sigmaSq : Omega → Fin B → ℝ)
    (eta kappa : ℝ)
    (hLaw : PredictableSoftTwoStageLaw D P0 x A V sigmaSq eta kappa)
    (hLogged : LoggedProbabilityCoherence D x A pi
      (fun w b k l ↦ rawConditionalE D x A b w (fun z ↦
        rawCellIndicator x A z b k * rawCellIndicator x A z b l)))
    (hDesign : DesignBasedFiniteness (_hB := hB) x A Y history observed)
    (hPartial : PartialInterference Y)
    (hStratified : StratifiedInterference Y)
    (hNonanticipation : Nonanticipation Y)
    (hLagOne : FiniteMemoryLagOne Y) :
    (∀ w b, 0 < rawConditionalE D x A b w (fun _ ↦ 1) → ∀ g,
      rawConditionalE D x A b w (fun z ↦ if x z b g then 1 else 0) = 1 / 2) ∧
    (∀ w b, 0 < rawConditionalE D x A b w (fun _ ↦ 1) → ∀ g,
      rawConditionalE D x A b w (fun z ↦ if x z b g then 0 else 1) = 1 / 2) ∧
    (∀ w b, 0 < rawConditionalE D x A b w (fun _ ↦ 1) → ∀ k,
      pi w b k = treatmentProbability k.2.2.1 k.2.2.2 / 2 ∧ 1 / 8 ≤ pi w b k) ∧
    (∀ j, D.E (fun w ↦ rawJointHTEstimator x A observed pi w j) =
      rawJointEstimand hB Y j) := by sorry

end

end CausalSmith.Experimentation.MultigroupStudentizedSRSB
