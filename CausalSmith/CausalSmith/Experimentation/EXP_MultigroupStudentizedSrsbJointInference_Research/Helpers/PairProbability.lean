import CausalSmith.Experimentation.EXP_MultigroupStudentizedSrsbJointInference_Research.Helpers.PerfectMatching
import Causalean.Experimentation.DesignBased.Exposure

/-! Uniform first- and second-stage exposure-probability control. -/

namespace CausalSmith.Experimentation.MultigroupStudentizedSRSB

open BoundedLagOnePartialInterferenceClass

variable {Omega : Type*} [Fintype Omega]

-- @node: lem:pair-probability-control
lemma pair_probability_control :
    ∀ (M KH cSigma CSigma eta kappa lambda : ℝ),
    0 < M → 0 < KH → 0 < cSigma → 0 < CSigma →
    eta ∈ Set.Ioo (0 : ℝ) 1 → 0 < kappa → 0 < lambda →
    ∃ C_pi c_pair : ℝ, 0 ≤ C_pi ∧ 0 < c_pair ∧
    ∀ (Omega : Type*) [Fintype Omega]
      (Mdl : BoundedLagOnePartialInterferenceClass Omega),
      Mdl.M = M → Mdl.KH = KH → Mdl.cSigma = cSigma → Mdl.CSigma = CSigma →
      Mdl.eta = eta → Mdl.kappa = kappa → Mdl.lambda = lambda →
      ImbalanceVarianceWindow Mdl.cSigma Mdl.CSigma Mdl.sigmaSq →
      (∀ w b (g h : Fin Mdl.G), g ≠ h →
        |conditionalE Mdl b w (fun z ↦ signValue (Mdl.x z b g) * signValue (Mdl.x z b h))| ≤
          C_pi / Mdl.G) ∧
      (∀ w b k l, k.1 ≠ l.1 →
        |Mdl.piPair w b k l - Mdl.pi w b k * Mdl.pi w b l| ≤ C_pi / Mdl.G) ∧
      (∀ w b k l, k.1 = l.1 → Mdl.piPair w b k l > 0 → c_pair ≤ Mdl.piPair w b k l) := by sorry

end CausalSmith.Experimentation.MultigroupStudentizedSRSB
