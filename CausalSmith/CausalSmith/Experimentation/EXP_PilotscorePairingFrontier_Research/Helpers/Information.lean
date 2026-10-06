module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Basic
public import Causalean.Stat.Minimax.TotalVariation
public import Causalean.Stat.Minimax.CoordinatewiseOverlap

/-! # Likelihood and posterior-overlap inequalities -/

public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

variable {d m N : ℕ} {β L cX CX cg Cg h c0 c1 C1 C2 κ ε A Bconst : ℝ}

open MeasureTheory

-- @node: local_flip_pilot_kl
lemma local_flip_pilot_kl
    (hfam : HypercubeFamily d β L cX CX cg Cg h c0 c1 C1 C2 κ ε A Bconst)
    (hm : 1 ≤ m) :
    ∃ K : ℕ, ∃ P : (Fin K → Bool) → Measure (PilotSample m d),
      ∀ θ j, InformationTheory.klDiv (P θ) (P (flipCoordinate θ j)) ≤
        ENNReal.ofReal (C2 * m * h ^ ((d : ℝ) + 2 * β)) := by
  obtain ⟨K, Q, ψ, B, g, base, amplitude, hKlo, hKhi, hQ, hdisj,
    hB, hψ, hamp, hg, hflip, hfold, hmodel, hcov, hkl⟩ := hfam
  refine ⟨K, (fun θ => Measure.pi fun _ : Fin m =>
    pilotUnitLaw (bernoulliUnitLaw (g θ))), ?_⟩
  intro θ j
  exact hkl m hm θ j

end CausalSmith.Experimentation.PilotscorePairingFrontier
