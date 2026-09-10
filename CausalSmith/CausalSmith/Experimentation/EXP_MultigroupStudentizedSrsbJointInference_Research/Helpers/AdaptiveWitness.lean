import CausalSmith.Experimentation.EXP_MultigroupStudentizedSrsbJointInference_Research.Helpers.BlockScore
import Causalean.Experimentation.DesignBased.Designs.CompleteRandomization
import Causalean.Mathlib.OperatorSqrt

/-! The alternating type-A/type-B finite-population witness and its local transport step. -/

namespace CausalSmith.Experimentation.MultigroupStudentizedSRSB

noncomputable section

open MeasureTheory
open BoundedLagOnePartialInterferenceClass

def witnessEndpoint (blockType d q : Bool) (H J : ℝ) : ℝ :=
  let aD := if blockType then J else H
  let aS := if blockType then H else J
  let L : ℝ := if blockType then 4 else 0
  let theta := 4 * aD
  let delta := L - theta
  let h := aS / 2 + aD - L / 2
  h + (if d then 1 else 0) * (delta + theta * saturationValue q)

def witnessH {G : ℕ} (g : Fin G) : ℝ :=
  if g.val % 4 < 2 then 1 else -1

def witnessJ {G : ℕ} (g : Fin G) : ℝ :=
  if g.val % 2 = 0 then 1 else -1

def witnessLoading : ℝ := 1
-- @realizes \lambda(the alternating witness fixes lambda=1)

-- @node: def:adaptive-witness
def alternatingBlockWitness (G B n : ℕ) :
    Fin G → Fin B → Fin n → Bool → Bool → ℝ :=
  fun g b _ d q ↦ witnessEndpoint (b.val % 2 = 1) d q (witnessH g) (witnessJ g)
-- @realizes \mathcal W^{AB}(alternating-block explicit potential-outcome family)

def witnessProjectionMatrix : Mat2 :=
  (1 / 2 : ℝ) •
    ((1 / 53 : ℝ) • !![(36 : ℝ), 6; 6, 1] +
      (1 / 29 : ℝ) • !![(4 : ℝ), 10; 10, 25])

abbrev WitnessSignAssignment (G : ℕ) := BalancedSignAssignment G

def witnessSign {G : ℕ} (S : WitnessSignAssignment G) (g : Fin G) : ℝ :=
  if g ∈ S.1 then 1 else -1

def witnessSaturation {G : ℕ} (S : WitnessSignAssignment G) (g : Fin G) : Bool :=
  g ∈ S.1

noncomputable def witnessReferenceDesign (G : ℕ) :
    Causalean.Experimentation.DesignBased.FiniteDesign (WitnessSignAssignment G) :=
  Causalean.Experimentation.DesignBased.completeRandomization (G / 2)
    (by simpa using Nat.div_le_self G 2)

def witnessGroupScore (G B n : ℕ) (g : Fin G) (b : Fin B) (q : Bool) : Vec2 := fun j ↦
  ∑ d : Bool, contrast d q j * ((n : ℝ)⁻¹ *
    ∑ i : Fin n, alternatingBlockWitness G B n g b i d q)

def witnessScoreDifference (G B n : ℕ) (g : Fin G) (b : Fin B) : Vec2 :=
  witnessGroupScore G B n g b true - witnessGroupScore G B n g b false

def witnessBlockA (G B n : ℕ) (S : WitnessSignAssignment G) (b : Fin B) : Vec2 :=
  (Real.sqrt G)⁻¹ • ∑ g, witnessSign S g • witnessScoreDifference G B n g b

def witnessObservedGroupMean (G B n : ℕ) (g : Fin G) (b : Fin B) (q : Bool) : ℝ :=
  ∑ d : Bool, treatmentProbability d q *
    ((n : ℝ)⁻¹ * ∑ i : Fin n,
      alternatingBlockWitness G B n g b i d q)

def witnessBalanceScore (G B n : ℕ)
    (path : Fin B → WitnessSignAssignment G) (b : Fin B) (g : Fin G) : ℝ :=
  if hb : b.val = 0 then witnessH g else
    let previous : Fin B := ⟨b.val - 1, by omega⟩
    let groupMean := witnessObservedGroupMean G B n g previous
      (witnessSaturation (path previous) g)
    let grandMean := (G : ℝ)⁻¹ * ∑ h,
      witnessObservedGroupMean G B n h previous (witnessSaturation (path previous) h)
    witnessH g + (groupMean - grandMean)

def witnessSigmaSq (G B n : ℕ)
    (path : Fin B → WitnessSignAssignment G) (b : Fin B) : ℝ :=
  ((G - 1 : ℕ) : ℝ)⁻¹ * ∑ g, (witnessBalanceScore G B n path b g) ^ 2

def witnessStandardizedBalance (G B n : ℕ)
    (path : Fin B → WitnessSignAssignment G) (b : Fin B)
    (S : WitnessSignAssignment G) : ℝ :=
  (Real.sqrt G)⁻¹ * (∑ g, witnessSign S g * witnessBalanceScore G B n path b g) /
    Real.sqrt (witnessSigmaSq G B n path b)

def witnessSoftExpectation {G : ℕ}
    (D : Causalean.Experimentation.DesignBased.FiniteDesign (WitnessSignAssignment G))
    (eta kappa : ℝ) (W X : WitnessSignAssignment G → ℝ) : ℝ :=
  D.E (fun S ↦ radialWeight eta kappa (W S) * X S) /
    D.E (fun S ↦ radialWeight eta kappa (W S))

def witnessSoftCovariance {G : ℕ}
    (D : Causalean.Experimentation.DesignBased.FiniteDesign (WitnessSignAssignment G))
    (eta kappa : ℝ) (A : WitnessSignAssignment G → Vec2)
    (W : WitnessSignAssignment G → ℝ) : Mat2 := fun i j ↦
  let mi := witnessSoftExpectation D eta kappa W (fun S ↦ A S i)
  let mj := witnessSoftExpectation D eta kappa W (fun S ↦ A S j)
  witnessSoftExpectation D eta kappa W (fun S ↦ (A S i - mi) * (A S j - mj))
-- @realizes \Sigma_{b,\mathrm{RR}}(exact tilted first-stage covariance for the witness)

def witnessReferenceCovariance {G : ℕ}
    (D : Causalean.Experimentation.DesignBased.FiniteDesign (WitnessSignAssignment G))
    (A : WitnessSignAssignment G → Vec2) : Mat2 := fun i j ↦
  D.Cov (fun S ↦ A S i) (fun S ↦ A S j)
-- @realizes \Sigma_{b,0}(exact uniform balanced-sign covariance for the witness)

def witnessProjectionLoading {G : ℕ}
    (D : Causalean.Experimentation.DesignBased.FiniteDesign (WitnessSignAssignment G))
    (A : WitnessSignAssignment G → Vec2) (W : WitnessSignAssignment G → ℝ) : Vec2 := fun i ↦
  D.Cov (fun S ↦ A S i) W
-- @realizes \beta_b(exact witness score-on-imbalance covariance)

-- @node: lem:adaptive-witness-pre-membership-transport
lemma adaptive_witness_pre_membership_transport :
    ∀ (G B n : ℕ → ℕ) (eta kappa : ℝ),
      (∀ N, 4 ∣ G N ∧ 0 < G N ∧ 4 ∣ n N ∧ 0 < n N ∧ 0 < B N) →
      0 < eta → eta < 1 → 0 < kappa →
      Filter.Tendsto G Filter.atTop Filter.atTop →
      ∃ epsilon_G : ℕ → ℝ, Filter.Tendsto epsilon_G Filter.atTop (nhds 0) ∧
        ∀ N (path : Fin (B N) → WitnessSignAssignment (G N)) (b : Fin (B N)),
          let D := witnessReferenceDesign (G N)
          let A := fun S ↦ witnessBlockA (G N) (B N) (n N) S b
          let W := witnessStandardizedBalance (G N) (B N) (n N) path b
          ∃ QA : Measure Vec3,
            IsCenteredGaussianWithCovariance QA
              (scoreBalanceCovariance D A W) ∧
            |rawSoftScalarMoment D eta kappa W - gaussianSoftScalarMoment QA eta kappa| +
              matMaxAbs (rawSoftMatrixMoment D eta kappa A W -
                gaussianSoftMatrixMoment QA eta kappa) ≤ epsilon_G N ∧
            matMaxAbs (witnessSoftCovariance D eta kappa A W - witnessReferenceCovariance D A +
              projectionGain eta kappa
                (outer (witnessProjectionLoading D A W) (witnessProjectionLoading D A W))) ≤
              epsilon_G N := by sorry

end

end CausalSmith.Experimentation.MultigroupStudentizedSRSB
