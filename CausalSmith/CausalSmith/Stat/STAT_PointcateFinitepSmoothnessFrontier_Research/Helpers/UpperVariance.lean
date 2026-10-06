module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.DegenerateVariance
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.UpperBias
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.TObservableHeavyProjections

/-! Finite-moment point-CATE frontier: Helpers/UpperVariance. -/
public section
set_option linter.style.longLine false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier


/-- The actual two-block procedure satisfies the numerator and denominator deviation certificates. -/
-- @node: upper_variance
lemma upper_variance (κ : Params) (hκ : κ.Valid) (n : ℕ) (hn : 2 ≤ n)
    (law : ObservedLaw) (hm : InModel κ law) :
  (∫ o, |numeratorHat κ n o-(∫ z, numeratorHat κ n z ∂Measure.pi (fun _ : Fin n => law.P))|
    ∂Measure.pi (fun _ : Fin n => law.P)) ≤ cNoise κ*rate κ n ∧
  (∫ o, |denominatorHat κ n o-localDenominator law (upperH κ n) (upperJ κ n)|
    ∂Measure.pi (fun _ : Fin n => law.P)) ≤ 20*rate κ n := by
  constructor
  · obtain ⟨j0, hcap⟩ := upper_cap_certificate κ hκ n hn
    apply (upper_numerator_deviation_projection_rates κ hκ n hn law hm j0.val
      (by omega) (fun j hj => (hcap j).1 hj) (fun j hj => (hcap j).2 hj)).trans
    apply (add_le_add le_rfl (upper_numerator_degenerate_sd_rate κ hκ n hn)).trans
    exact le_of_eq (by unfold cNoise; ring)
  · exact upper_denominator_deviation κ hκ n hn law hm

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
