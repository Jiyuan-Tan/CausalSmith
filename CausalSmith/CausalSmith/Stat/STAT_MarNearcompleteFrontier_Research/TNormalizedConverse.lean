module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.LowerBound.NormalizedGlue
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.LowerBound.NormalizedLargeN
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.LowerBound.NormalizedTargetConcentration
public import Causalean.Stat.Minimax.ChiSquared
public import Causalean.Stat.Minimax.TotalVariation
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.IndependentPrefix.RandomScaleTransfer.Basic

/-!
# Normalized same-experiment converse

Both priors are on the legal full-data class. Their predictive laws retain the
entire observed record, including membership on nonarrival.
-/

@[expose] public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory

-- @node: thm:normalized-converse
/-- Paired legal priors have close complete-sample mixtures and separated ATEs. [the stated mathematical conclusion holds](goal). Given [the specified input `β`](hyp:β). Given [the specified input `hβ`](hyp:hβ). -/
-- @realizes beta(fixed fuzzy-hypothesis tolerance in (0,1/4))
theorem normalized_converse (β : ℝ) (hβ : β ∈ Set.Ioo 0 ((1 : ℝ) / 4)) :
    ∃ cβ : ℝ, 0 < cβ ∧
      ∀ (n d : ℕ) (q : ℝ), 1 ≤ n → 1 ≤ d →
        q ∈ Set.Icc ((1 : ℝ) / 2) 1 →
        gScale n d q ^ 2 ≥ 1 / (n : ℝ) →
        ∃ πminus πplus : PMF (ClassLaw d q),
          Causalean.Stat.tvDist
            (priorPredictive n d q πminus)
            (priorPredictive n d q πplus) ≤ β ∧
          ∃ m0 : ℝ,
            1 - β ≤ priorEventMass d q πminus
              (fun P => tau P.val ≤ m0 - cβ * gScale n d q) ∧
            1 - β ≤ priorEventMass d q πplus
              (fun P => m0 + cβ * gScale n d q ≤ tau P.val) := by
  apply normalized_converse_of_eventual_certificate β hβ
  obtain ⟨NTV, hNTV, htv⟩ := paired_predictive_tv_eventual β hβ.1
  obtain ⟨NTarget, hNTarget, c, hc, htarget⟩ :=
    pairedPrior_target_events_eventual β hβ.1
  refine ⟨max NTV NTarget, le_max_of_le_left hNTV, c, hc, ?_⟩
  intro n d q hnN hd hq hreg
  have hnTV : NTV ≤ n := (le_max_left _ _).trans hnN
  have hnTarget : NTarget ≤ n := (le_max_right _ _).trans hnN
  have hn : 1 ≤ n := le_trans (by omega : 1 ≤ NTV) hnTV
  refine ⟨(pairedPrior n d q hn hd hq).1,
    (pairedPrior n d q hn hd hq).2,
    htv n d q hnTV hn hd hq hreg, ?_⟩
  exact htarget n d q hnTarget hn hd hq hreg

/-- Separation constant extracted from the proved converse at a fixed tolerance. -/
noncomputable def converseConstant (β : ℝ)
    (hβ : β ∈ Set.Ioo 0 ((1 : ℝ) / 4)) : ℝ :=
  Classical.choose (normalized_converse β hβ)
  -- @realizes c_beta(positive universal separation constant at beta)

-- @node: converseConstant_spec
/-- The selected separation constant retains the complete paired-prior certificate. [the stated mathematical conclusion holds](goal). Given [the specified input `β`](hyp:β). Given [the specified input `hβ`](hyp:hβ). -/
lemma converseConstant_spec (β : ℝ)
    (hβ : β ∈ Set.Ioo 0 ((1 : ℝ) / 4)) :
    0 < converseConstant β hβ ∧
      ∀ (n d : ℕ) (q : ℝ), 1 ≤ n → 1 ≤ d →
        q ∈ Set.Icc ((1 : ℝ) / 2) 1 →
        gScale n d q ^ 2 ≥ 1 / (n : ℝ) →
        ∃ πminus πplus : PMF (ClassLaw d q),
          Causalean.Stat.tvDist
            (priorPredictive n d q πminus)
            (priorPredictive n d q πplus) ≤ β ∧
          ∃ m0 : ℝ,
            1 - β ≤ priorEventMass d q πminus
              (fun P => tau P.val ≤ m0 - converseConstant β hβ * gScale n d q) ∧
            1 - β ≤ priorEventMass d q πplus
              (fun P => m0 + converseConstant β hβ * gScale n d q ≤ tau P.val) := by
  exact Classical.choose_spec (normalized_converse β hβ)

end CausalSmith.Stat.MarNearcompleteFrontier
