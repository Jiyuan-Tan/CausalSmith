import CausalSmith.Experimentation.EXP_MultigroupStudentizedSrsbJointInference_Research.Helpers.AdaptiveWitness
import Causalean.Mathlib.Analysis.TwoByTwoSpectralRoots

/-! Nonvacuity: an explicit genuinely adaptive witness with full-rank gain. -/

namespace CausalSmith.Experimentation.MultigroupStudentizedSRSB

open BoundedLagOnePartialInterferenceClass
open Filter

-- @node: prop:adaptive-full-rank-witness
theorem adaptive_full_rank_witness :
    ∃ (O : ℕ → Type) (inst : ∀ N, Fintype (O N))
      (Mdl : ∀ N, @BoundedLagOnePartialInterferenceClass (O N) (inst N))
      (OmegaRR OmegaCR : Mat2),
      Tendsto (fun N ↦ (Mdl N).G) Filter.atTop Filter.atTop ∧
      Tendsto (fun N ↦ (Mdl N).B) Filter.atTop Filter.atTop ∧
      (∀ N, 4 ∣ (Mdl N).G ∧ 4 ∣ (Mdl N).n ∧ 0 < (Mdl N).B) ∧
      (∀ N, (Mdl N).H = witnessH ∧ (Mdl N).lambda = witnessLoading) ∧
      (∀ N g b i d q,
        sustainedEndpoint (Mdl N) g b i d q =
          alternatingBlockWitness (Mdl N).G (Mdl N).B (Mdl N).n g b i d q) ∧
      (∀ ε : ℝ, 0 < ε → ∃ N0, ∀ N, N0 ≤ N → ∀ (w : O N) b,
        (b.val % 2 = 0 → |(Mdl N).sigmaSq w b - (53 : ℝ) / 16| < ε) ∧
        (b.val % 2 = 1 → |(Mdl N).sigmaSq w b - (29 : ℝ) / 16| < ε)) ∧
      witnessProjectionMatrix =
        (1 / 2 : ℝ) •
          ((1 / 53 : ℝ) • !![(36 : ℝ), 6; 6, 1] +
            (1 / 29 : ℝ) • !![(4 : ℝ), 10; 10, 25]) ∧
      Matrix.det witnessProjectionMatrix = (196 : ℝ) / 1537 ∧
      Matrix.PosDef witnessProjectionMatrix ∧
      (∀ ε : ℝ, 0 < ε → ∃ N0, ∀ N, N0 ≤ N → ∀ w : O N,
        matMaxAbs (avgSigmaRR (Mdl N) w - OmegaRR) < ε ∧
        matMaxAbs (avgSigmaCR (Mdl N) w - OmegaCR) < ε ∧
        matMaxAbs (avgProjection (Mdl N) w - witnessProjectionMatrix) < ε) ∧
      OmegaRR = OmegaCR - projectionGain (Mdl 0).eta (Mdl 0).kappa witnessProjectionMatrix ∧
      ∃ N : ℕ, ∃ w w' : O N, ∃ b : Fin (Mdl N).B,
        (∀ k : Fin (Mdl N).B, k.val < b.val →
          (Mdl N).x w k = (Mdl N).x w' k ∧ (Mdl N).Aassign w k = (Mdl N).Aassign w' k) ∧
        (∃ g, (Mdl N).observed w g ≠ (Mdl N).observed w' g) ∧
        ∃ z a,
          softBlockKernelMass (Mdl N).G (Mdl N).n (Mdl N).eta (Mdl N).kappa
              ((Mdl N).sigmaSq w b) ((Mdl N).V w b) z a ≠
            softBlockKernelMass (Mdl N).G (Mdl N).n (Mdl N).eta (Mdl N).kappa
              ((Mdl N).sigmaSq w' b) ((Mdl N).V w' b) z a := by sorry

end CausalSmith.Experimentation.MultigroupStudentizedSRSB
