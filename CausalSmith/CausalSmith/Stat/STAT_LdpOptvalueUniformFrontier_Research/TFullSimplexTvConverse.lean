module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.TPairedUniformTvFrontier

/-!
# TFullSimplexTvConverse

Finite original-record private value frontiers: TFullSimplexTvConverse.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

namespace CausalSmith.Stat.LdpOptvalueUniformFrontier


-- @node: thm:full-simplex-tv-converse
/-- Under the [Bernstein absolute-approximation limit](hyp:hBernstein_of_gate), the full simplex obeys
the [private minimax-risk and globally honest connected-length lower
bounds](goal). -/
theorem full_simplex_tv_converse (hBernstein_of_gate : BernsteinAbsoluteApproximationLimit) :
    ∃ c : ℝ, 0 < c ∧ -- @realizes c(universal positive lower constant)
      ∀ (n d : ℕ) (eps : ℝ), Allowed n d eps →
      ∀ C : ProtocolClassLabel,
        ENNReal.ofReal (c*rateR C n d eps) ≤ tvMinimaxRisk C (simplexModel d) n eps ∧
        ENNReal.ofReal (c*rateH C n d eps) ≤ tvHonestLength C (simplexModel d) n eps  := by
  obtain ⟨c, hc, hconverse⟩ := paired_converse_of_gate
    measurableKernelRadonNikodym_proved caiLowMomentDuality_proved hBernstein_of_gate
  refine ⟨c, hc, ?_⟩
  intro n d eps hAllowed C
  have hsub := pairedFamily_subset_simplex (d := d) (by have := hAllowed.2.1; omega)
  have hsequential : ∀ K : LocalProtocol n (PairedSymbol d),
      protocolClass C K eps → SequentialClass K eps := by
    intro K hK
    cases C with
    | NI => exact ⟨hK.privacy⟩
    | SI => exact hK
  constructor
  · change _ ≤ Causalean.Stat.minimaxValueENNReal _
    apply Causalean.Stat.le_minimaxValueENNReal
    rintro ⟨⟨K, hK⟩, T⟩
    apply le_trans ((hconverse n d eps hAllowed K (hsequential K hK)).1 T)
    apply iSup_le
    intro p
    exact le_iSup_of_le ⟨p.1, hsub p.2⟩ le_rfl
  · change _ ≤ Causalean.Stat.minimaxValueENNReal _
    apply Causalean.Stat.le_minimaxValueENNReal
    rintro ⟨⟨K, hK⟩, J, hJ⟩
    have hpaired : ∀ p ∈ pairedFamily d,
        (0.90 : ℝ) ≤ coverage (canonicalDecisionLaw K p) J (tvFromUniform p) :=
      fun p hp => hJ p (hsub hp)
    apply le_trans ((hconverse n d eps hAllowed K (hsequential K hK)).2 J hpaired)
    apply iSup_le
    intro p
    exact le_iSup_of_le ⟨p.1, hsub p.2⟩ le_rfl


end CausalSmith.Stat.LdpOptvalueUniformFrontier
