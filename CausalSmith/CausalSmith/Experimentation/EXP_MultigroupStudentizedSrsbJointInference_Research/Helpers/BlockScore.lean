import CausalSmith.Experimentation.EXP_MultigroupStudentizedSrsbJointInference_Research.Basic
import Causalean.Experimentation.DesignBased.ProductVariance
import Causalean.Experimentation.DesignBased.CompoundVariance

/-! Block-score definitions, decomposition, and conditional centering. -/

open scoped BigOperators Matrix
open Finset

namespace CausalSmith.Experimentation.MultigroupStudentizedSRSB

noncomputable section

open Causalean.Experimentation.DesignBased
open BoundedLagOnePartialInterferenceClass

variable {Omega : Type*} [Fintype Omega]

-- @node: def:score-splitting
def blockScoreSplit (Mdl : BoundedLagOnePartialInterferenceClass Omega)
    (w : Omega) (b : Fin Mdl.B) : Prop :=
  blockR Mdl w b = blockA Mdl w b + blockU Mdl w b

noncomputable def conditionalEGivenSign (Mdl : BoundedLagOnePartialInterferenceClass Omega)
    (b : Fin Mdl.B) (w : Omega) (X : Omega → ℝ) : ℝ := by
  classical
  let event := fun z ↦ conditionalEvent Mdl b w z ∧ Mdl.x z b = Mdl.x w b
  let p := Mdl.design.Pr event
  exact if p = 0 then 0 else Mdl.design.E (fun z ↦ FiniteDesign.ind event z * X z) / p

noncomputable def referenceConditionalE
    (Mdl : BoundedLagOnePartialInterferenceClass Omega)
    (b : Fin Mdl.B) (w : Omega) (X : Omega → ℝ) : ℝ :=
  pathConditionalE (Mdl.referenceDesign w b) Mdl.x Mdl.Aassign b w X

def referenceConditionalCovVec (Mdl : BoundedLagOnePartialInterferenceClass Omega)
    (b : Fin Mdl.B) (w : Omega) (X : Omega → Vec2) : Mat2 := fun i j ↦
  referenceConditionalE Mdl b w (fun z ↦
    (X z i - referenceConditionalE Mdl b w (fun u ↦ X u i)) *
    (X z j - referenceConditionalE Mdl b w (fun u ↦ X u j)))

-- @node: lem:score-decomposition
lemma score_decomposition (Mdl : BoundedLagOnePartialInterferenceClass Omega)
    (hDesign : DesignBasedFiniteness (_hB := Mdl.B_pos) Mdl.x Mdl.Aassign
      Mdl.Y Mdl.realizedHistory Mdl.observed)
    (hPartial : PartialInterference Mdl.Y)
    (hStratified : StratifiedInterference Mdl.Y) :
    (∀ w b, blockScoreSplit Mdl w b) ∧
    (∀ w b i, conditionalEGivenSign Mdl b w (fun z ↦ blockU Mdl z b i) = 0) ∧
    (∀ w b (g h : Fin Mdl.G), g ≠ h → ∀ f k : Vec2 → ℝ,
      conditionalEGivenSign Mdl b w (fun z ↦
        f (groupSamplingError Mdl z g b (groupSaturation Mdl z b g)) *
        k (groupSamplingError Mdl z h b (groupSaturation Mdl z b h))) =
      conditionalEGivenSign Mdl b w (fun z ↦
        f (groupSamplingError Mdl z g b (groupSaturation Mdl z b g))) *
      conditionalEGivenSign Mdl b w (fun z ↦
        k (groupSamplingError Mdl z h b (groupSaturation Mdl z b h)))) ∧
    (∀ w b, rrCovariance Mdl w b =
      conditionalCovVec Mdl b w (fun z ↦ blockA Mdl z b) +
        withinCovarianceComponent Mdl w b) ∧
    (∀ w b i j, conditionalE Mdl b w (fun z ↦ blockA Mdl z b i * blockU Mdl z b j) = 0) ∧
    (∀ w b, referenceConditionalCovVec Mdl b w (fun z ↦ blockR Mdl z b) =
      completeRandomizationCovariance Mdl w b ∧ completeRandomizationCovariance Mdl w b =
      ((Mdl.G - 1 : ℕ) : ℝ)⁻¹ •
          (∑ g, let abar := (Mdl.G : ℝ)⁻¹ • ∑ h, scoreDifference Mdl h b
            outer (scoreDifference Mdl g b - abar) (scoreDifference Mdl g b - abar)) +
        withinCovarianceComponent Mdl w b) := by sorry

-- @node: lem:martingale-centering
lemma martingale_centering (Mdl : BoundedLagOnePartialInterferenceClass Omega)
    (hNonanticipation : Nonanticipation Mdl.Y)
    (hLagOne : FiniteMemoryLagOne Mdl.Y) :
    (∀ w b i, conditionalE Mdl b w (fun z ↦ blockR Mdl z b i) = 0) ∧
    (∀ w, Real.sqrt (Mdl.G * Mdl.B) •
        (jointHTEstimator Mdl w - jointEstimand Mdl) =
      (Real.sqrt Mdl.B)⁻¹ • ∑ b, blockR Mdl w b) := by sorry

end

end CausalSmith.Experimentation.MultigroupStudentizedSRSB
