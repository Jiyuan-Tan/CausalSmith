module
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.LowerWitness

/-!
# True-side Gaussian measurement-error endpoint frontier

Helpers/Law-level constructions and the obligations specified by the typed core.
Cited logical facts are explicit inputs; bibliographic records have no logical consumers.
-/

@[expose] public section

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology

namespace CausalSmith.Stat.RdTruesideNoiseFrontier


/-- The endpoint handle records objects only; it carries no comparability or legality premises. -/
structure FrontierHandleData (β : ℝ) (n : ℕ) (σ : ℝ) where
  target : LatentLaw → ℝ
  variance : ℕ → ℝ
  certificate : ℝ
  cancellation : (m : ℕ) → 2 ≤ m → σ ∈ Ioc (0 : ℝ) 1 → Bool → LatentLaw
  direct : (h : ℝ) → h ∈ Ioc (0 : ℝ) 1 → Bool → LatentLaw
  frontier : ℝ
  estimate : Estimator n
  interval : IntervalProc n
/-- Endpoint precision handle over the constructed objects in Definitions 3--10. Given [the displayed inputs and assumptions](hyp:hleg,β,n,σ,hβ), [this definition specifies the stated object](goal). -/
-- @node: def:frontier-handle
def frontierHandle (hleg : ClassicalLegendreFacts) (β : ℝ) (n : ℕ) (σ : ℝ) (hβ : β ∈ Ioc (0 : ℝ) 1) :
    FrontierHandleData β n σ where
  target := theta
  variance := fun L => kernelVariance L σ
  certificate := certificate β n σ
  cancellation := fun m hm hσ s => altLaw hleg β (noiseSupport σ m) m s hβ (noiseSupport_mem σ m hσ hm) hm
  direct := fun h hh s => directAltLaw β h s hβ hh
  frontier := frontierRate β n σ
  estimate := attainer β n σ
  interval := honestAttainer β n σ

end CausalSmith.Stat.RdTruesideNoiseFrontier
