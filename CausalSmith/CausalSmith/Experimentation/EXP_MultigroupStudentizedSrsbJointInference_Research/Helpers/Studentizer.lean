import CausalSmith.Experimentation.EXP_MultigroupStudentizedSrsbJointInference_Research.Helpers.PairProbability
import Causalean.Experimentation.ExposureMappingInterference.Variance.Conservative

/-! The observable pairwise covariance estimator, Young completion, and clipping. -/

open scoped BigOperators Matrix
open Finset

namespace CausalSmith.Experimentation.MultigroupStudentizedSRSB

noncomputable section

open BoundedLagOnePartialInterferenceClass

variable {Omega : Type*} [Fintype Omega]

def blockCellOutcome (Mdl : BoundedLagOnePartialInterferenceClass Omega)
    (b : Fin Mdl.B) (k : CellIndex Mdl.G Mdl.n) : Vec2 :=
  contrast k.2.2.1 k.2.2.2 •
    (fun _ ↦ sustainedEndpoint Mdl k.1 b k.2.1 k.2.2.1 k.2.2.2)

noncomputable def completedBlockEstimator
    (Mdl : BoundedLagOnePartialInterferenceClass Omega) (w : Omega) (b : Fin Mdl.B) : Mat2 := by
  classical
  let feasible := Finset.univ.filter fun kl : CellIndex Mdl.G Mdl.n × CellIndex Mdl.G Mdl.n ↦
    0 < Mdl.piPair w b kl.1 kl.2
  let pairTerm : Mat2 := ∑ kl ∈ feasible,
    let k := kl.1
    let l := kl.2
    let coeff := cellIndicator Mdl w b k * cellIndicator Mdl w b l *
      (Mdl.piPair w b k l - Mdl.pi w b k * Mdl.pi w b l) /
      (Mdl.piPair w b k l * Mdl.pi w b k * Mdl.pi w b l)
    coeff • outer (blockCellOutcome Mdl b k) (blockCellOutcome Mdl b l)
  let completion : Mat2 := ∑ kl ∈ impossiblePairs (Mdl.piPair w b),
    ((cellIndicator Mdl w b kl.1 / Mdl.pi w b kl.1 : ℝ) •
        outer (blockCellOutcome Mdl b kl.1) (blockCellOutcome Mdl b kl.1) +
      (cellIndicator Mdl w b kl.2 / Mdl.pi w b kl.2 : ℝ) •
        outer (blockCellOutcome Mdl b kl.2) (blockCellOutcome Mdl b kl.2))
  exact (((Mdl.G * Mdl.n * Mdl.n : ℕ) : ℝ)⁻¹) • (pairTerm + completion)
-- @realizes \widehat\Gamma_b(pairwise HT covariance plus observable Young completion)

noncomputable def completionBias
    (Mdl : BoundedLagOnePartialInterferenceClass Omega) (w : Omega) (b : Fin Mdl.B) : Mat2 := by
  classical
  exact (((Mdl.G * Mdl.n * Mdl.n : ℕ) : ℝ)⁻¹) •
    ∑ kl ∈ impossiblePairs (Mdl.piPair w b),
      outer (blockCellOutcome Mdl b kl.1 + blockCellOutcome Mdl b kl.2)
        (blockCellOutcome Mdl b kl.1 + blockCellOutcome Mdl b kl.2)
-- @realizes D_b(positive-semidefinite impossible-pair completion bias)

-- @node: def:completed-studentizer
noncomputable def completedStudentizer
    (Mdl : BoundedLagOnePartialInterferenceClass Omega) (w : Omega) :
    (Fin Mdl.B → Mat2) × Mat2 × Mat2 :=
  let blocks := fun b ↦ completedBlockEstimator Mdl w b
  let average := (Mdl.B : ℝ)⁻¹ • ∑ b, blocks b
  (blocks, average, spectralClip2 (Mdl.rClip Mdl.B) average)
-- @realizes \widehat\Gamma_b(first component: completed block covariance estimates)
-- @realizes \widehat\Gamma(second component: block average)
-- @realizes \widehat\Gamma_+(third component: eigenvalues clipped at r_B)

end

end CausalSmith.Experimentation.MultigroupStudentizedSRSB
