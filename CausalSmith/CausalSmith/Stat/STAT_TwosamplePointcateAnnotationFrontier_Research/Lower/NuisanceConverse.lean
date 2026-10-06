module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.CitedGates
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.RateAlgebra
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Lower.FuzzyBlockTesting
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Lower.NuisanceScales
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Lower.TargetIdentification

/-!
# Lower/NuisanceConverse

Two-channel point-CATE annotation frontier: Lower/NuisanceConverse
constructions and obligations.
-/

public section

attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
noncomputable section
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.whitespace false
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier


-- @node: lem:nuisance-frontier-converse
/-- Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input hdom](hyp:hdom), [the specified input hS](hyp:hS), [the nuisance frontier converse conclusion](goal) holds. -/
lemma nuisance_frontier_converse
    (d : ℕ) (alpha beta gamma L eps : ℝ) (hdom : PublicDomain d alpha beta gamma L eps)
    (hS : alpha+beta < sCrit d gamma) :
    ∃ c : ℝ, 0 < c ∧ -- @realizes c(positive claim-local constant)
       ∀ (n m : ℕ), 2 ≤ n →
      (n:ℝ)+m ≤ (n:ℝ)^qStar d alpha beta gamma →
      ENNReal.ofReal (c*(((n:ℝ)*((n:ℝ)+m))^(-(gamma/bigDelta d alpha beta gamma)))) ≤
        minimaxRisk d alpha beta gamma L eps n m := by
  obtain ⟨kappa, hkappa, hpriors⟩ :=
    nuisance_scaled_marked_priors d alpha beta gamma L eps hdom hS
  refine ⟨(3/4:ℝ)*kappa, by positivity, ?_⟩
  intro n m hn hboundary
  obtain ⟨h, delta, a, b, hd, hdh, hh, ha, hb, hab, hMembers, hTargets, hhell⟩ :=
    hpriors n m hn hboundary
  obtain ⟨Ψ, hΨ⟩ := marked_experiment_target_exists (by omega : 0 < n) hMembers
  have htest := marked_fuzzy_testing_minimax d n m alpha beta gamma L eps
    h delta a b ha hb hMembers hTargets Ψ hΨ hhell
  have hscale : (3/4:ℝ)*a*b =
      ((3/4:ℝ)*kappa)*(((n:ℝ)*((n:ℝ)+m))^(-(gamma/bigDelta d alpha beta gamma))) := by
    calc
      _ = (3/4:ℝ)*(a*b) := by ring
      _ = _ := by rw [hab]; ring
  rw [hscale] at htest
  exact htest


end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
