module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Basic

/-! # Folded-score branch density -/

public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

variable {d m N : ℕ} {β L cX CX cg Cg h c0 c1 C1 C2 κ ε A Bconst : ℝ}

open MeasureTheory

-- @node: folded_family_score_envelope
lemma folded_family_score_envelope
    (hfam : HypercubeFamily d β L cX CX cg Cg h c0 c1 C1 C2 κ ε A Bconst) :
    ∃ K : ℕ, ∃ g : (Fin K → Bool) → XSpace d → ℝ,
      ∀ θ, RegularScorePushforward (bernoulliUnitLaw (g θ)) (g θ) cg Cg := by
  rcases hfam with ⟨K, Q, ψ, B, g, base, amplitude, hKlow, hKhi, hQ,
    hdisj, hB, hψ, hamp, hrep, hloc, hfold, hmodel, hX, hKL⟩
  exact ⟨K, g, fun θ => (hmodel θ).regular_score_pushforward⟩

end CausalSmith.Experimentation.PilotscorePairingFrontier
