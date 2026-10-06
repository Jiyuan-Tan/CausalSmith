module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotAdaptiveTransfer

/-!
# Sequential uniformization over shrinking pilot neighborhoods

This module turns convergence along every selected bad subsequence of finite pilot
prefixes into eventual uniform control over all prefixes whose selected parameter lies
in a shrinking neighborhood of the base point.
-/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open Filter
open scoped Topology

/-- If every subsequence of finite pilot prefixes whose selected parameters converge to the base point has the same scalar limit, then the scalar errors are eventually uniform over all pilot prefixes selected inside any shrinking radius. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hρ,hseq), [the adaptive Pilot Selector uniform of subsequential tendsto](goal).

Under the stated assumptions, the adaptive Pilot Selector uniform of subsequential tendsto. -/
-- keep: reusable finite-pilot construction, law, localization, or limit API for related adaptive procedures
lemma adaptivePilotSelector_uniform_of_subsequential_tendsto
    (θ : TrialParameter) (p ε : ℝ) (m : ℕ → ℕ)
    (ρ : ℕ → ℝ)
    (E : (n : ℕ) → AdaptivePilotSample m n → ℝ) (L : ℝ)
    (hρ : Tendsto ρ atTop (nhds 0))
    (hseq : ∀ (φ : ℕ → ℕ), StrictMono φ →
      ∀ u : (k : ℕ) → AdaptivePilotSample m (φ k),
        Tendsto (fun k => adaptivePilotSelector p ε m (φ k) (u k))
            atTop (nhds θ) →
          Tendsto (fun k => E (φ k) (u k)) atTop (nhds L)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      ∀ u : AdaptivePilotSample m n,
        dist (adaptivePilotSelector p ε m n u) θ ≤ ρ n →
          |E n u - L| < δ := by
  intro δ hδ
  by_contra huniform
  have hfrequent : ∃ᶠ n in atTop,
      ¬(∀ u : AdaptivePilotSample m n,
        dist (adaptivePilotSelector p ε m n u) θ ≤ ρ n →
          |E n u - L| < δ) := not_eventually.mp huniform
  have hbad : ∃ᶠ n in atTop, ∃ u : AdaptivePilotSample m n,
      dist (adaptivePilotSelector p ε m n u) θ ≤ ρ n ∧
        δ ≤ |E n u - L| := by
    apply hfrequent.mono
    intro n hn
    push Not at hn
    exact hn
  obtain ⟨φ, hφ, hφbad⟩ := extraction_of_frequently_atTop hbad
  choose u hu using hφbad
  have hselector : Tendsto
      (fun k => adaptivePilotSelector p ε m (φ k) (u k))
      atTop (nhds θ) := by
    rw [Metric.tendsto_atTop]
    intro η hη
    have hρsub : Tendsto (fun k => ρ (φ k)) atTop (nhds 0) :=
      hρ.comp hφ.tendsto_atTop
    have hρlt : ∀ᶠ k in atTop, ρ (φ k) < η :=
      (tendsto_order.1 hρsub).2 η hη
    rcases eventually_atTop.1 hρlt with ⟨N, hN⟩
    exact ⟨N, fun k hk => lt_of_le_of_lt (hu k).1 (hN k hk)⟩
  have hE := hseq φ hφ u hselector
  have hclose : ∀ᶠ k in atTop, |E (φ k) (u k) - L| < δ := by
    rcases (Metric.tendsto_atTop.1 hE) δ hδ with ⟨N, hN⟩
    exact eventually_atTop.2 ⟨N, fun k hk => by
      simpa [Real.dist_eq] using hN k hk⟩
  rcases eventually_atTop.1 hclose with ⟨N, hN⟩
  exact (not_lt_of_ge (hu N).2 (hN N le_rfl)).elim

end CausalSmith.Stat.LdpAteEfficiencySurface
