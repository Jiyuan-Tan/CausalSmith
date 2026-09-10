/- Explicit separation of contrastwise and matrixwise variance invariance. -/

import CausalSmith.Experimentation.EXP_BanditRandomQvStudentizationFrontier_Research.Helpers.Witness
import CausalSmith.Experimentation.EXP_BanditRandomQvStudentizationFrontier_Research.T_MatrixwiseSandwich

/-! # Directional/matrix separation -/

open Filter MeasureTheory Set Topology

namespace CausalSmith.Experimentation.BanditRandomQV

noncomputable section

/-- The advertised horizon-asymptotic validity/separation assertion for the
explicit witness family. -/
def DirectionalWitnessAsymptoticSeparation (epsilon : ℝ) : Prop :=
  let Sigma : Mat 2 := !![1, 0; 0, 2]
  let c : Vec 2 := WithLp.toLp 2 ![1, 0]
  ∃ (E : ℕ → AdaptiveCausalExperiment DirectionalPath Unit 3 2 1)
    (C : ∀ T, 2 ≤ T → IPWZContract DirectionalPath Unit (E T) T (epsilon / 8))
    (etaBar : Fin 2 → Vec 1) (J : DirectionalPath → Fin 2)
    (etaInf : DirectionalPath → Vec 1)
    (hSigma : PositiveDefinite Sigma) (hc : c ≠ 0),
    (∀ T, ∀ hT : 2 ≤ T,
      ∃ hClass : FiniteAttractorClass (E T) etaBar J etaInf
        epsilon 2 (epsilon / 8) 1 1 1 (1 / 12) 1 1 (2 / 5) 1
        (fun u => u) (fun n => 1 / (2 * n)) (fun _ => 0),
      DirectionalWitnessRealizes (E T) (directionalMatrixWitness T hT)
        etaBar J etaInf ∧
      (E T).horizon = T ∧ (E T).jacobian = -identMat 2 ∧
      ((E T).law {ω | J ω = 0}).toReal = 2 / 5 ∧
      ((E T).law {ω | J ω = 1}).toReal = 3 / 5 ∧
      basinOmega (E T) etaBar hClass.etaBar_mem 0 = !![1, 0; 0, 2] ∧
      basinV (E T) etaBar hClass.etaBar_mem 0 = !![1, 0; 0, 2] ∧
      basinOmega (E T) etaBar hClass.etaBar_mem 1 = !![1, 0; 0, 3] ∧
      basinV (E T) etaBar hClass.etaBar_mem 1 = !![1, 0; 0, 3] ∧
      qform (basinV (E T) etaBar hClass.etaBar_mem 0) c = qform Sigma c ∧
      qform (basinV (E T) etaBar hClass.etaBar_mem 1) c = qform Sigma c) ∧
    (∀ alpha, ∀ halpha : 0 < alpha ∧ alpha < 1,
      Tendsto (fun n => ((E (n + 2)).law {ω |
        dot c (E (n + 2)).thetaStar ∈ deterministicWaldInterval (n + 2)
          (ipwZEstimator (C (n + 2) (by omega))) (by omega)
          Sigma hSigma c hc alpha halpha ω}).toReal)
        atTop (𝓝 (1 - alpha))) ∧
    !![1, 0; 0, 2] ≠ (!![1, 0; 0, 3] : Mat 2)

-- @node: prop:directional-matrix-separation
theorem directional_matrix_separation :
    ∀ epsilon : ℝ, ∀ _hepsilon_pos : 0 < epsilon,
    ∀ _hepsilon_lt : epsilon < 1 / 6,
      DirectionalWitnessAsymptoticSeparation epsilon := by sorry

end

end CausalSmith.Experimentation.BanditRandomQV
