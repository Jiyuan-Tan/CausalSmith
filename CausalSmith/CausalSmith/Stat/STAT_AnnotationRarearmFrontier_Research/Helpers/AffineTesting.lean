module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.AtomHistogram
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.AtomLaw
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.CellTV
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.Concentration
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.ControlSplit
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.FixedRisk
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.Histogram
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.HistogramCoordinates
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.Membership
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.NumericalConcentration
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.NumericalSeparation
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.NumericalTV
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.NumericalTransfer
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.OrderedExperiment
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.ProductExperiment
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.ProductTV
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.RawBayes
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.Testing
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.Transfer
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.ShrinkingConeDual
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.IndependentPrefix.RandomScaleTransfer.Main
public import Causalean.Stat.Minimax.Mixture.MomentMatched.MarkedPoisson.Product
public import Causalean.Stat.Minimax.Mixture.MomentMatched.MarkedPoisson.TVBound

/-!
Support, common normalized marginal, and original-experiment affine-prior testing bound.
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable


/-- [Under the stated inputs and conditions](hyp:d), The auxiliary marginal is Borel in the complete-record mass coordinates.  This gives [the stated result](goal).-/
-- @node: affine_auxMarginal_measurable
@[fun_prop]
lemma affine_auxMarginal_measurable (d : Nat) :
    Measurable (auxMarginal (d := d)) := by
  apply measurable_comap_iff.mpr
  apply measurable_pi_lambda
  intro z
  change Measurable (fun P : DiscreteLaw d => (auxMarginal P z).toReal)
  simp_rw [show ∀ P : DiscreteLaw d, (auxMarginal P z).toReal = armMass P z.1 z.2 from
    fun P => auxMarginal_toReal_armMass P z.1 z.2]
  unfold armMass jointMass
  apply Finset.measurable_sum
  intro y _
  exact (measurable_pi_apply (z.1, z.2, y)).comp
    (comap_measurable (fun P : DiscreteLaw d => fun o => (P.pmf o).toReal))

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',sigma,n,m,d), Coupling the same finite latent vector gives identical normalized marginal laws.  This gives [the stated result](goal).-/
-- @node: affine_productPrior_common_marginal
lemma affine_productPrior_common_marginal (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps) :
    (affineProductPrior true n m d eps hd sigma).map auxMarginal =
      (affineProductPrior false n m d eps hd sigma).map auxMarginal := by
  have hm (hyp : Bool) : Measurable (normalizedLaw hyp n m d eps hd sigma) := by
    fun_prop
  unfold affineProductPrior
  rw [Measure.map_map (affine_auxMarginal_measurable d) (hm true),
    Measure.map_map (affine_auxMarginal_measurable d) (hm false)]
  congr 1
  funext lat
  exact (affine_support_and_normalizer n m d eps hn hd heps heps' sigma).2 lat |>.2.2

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',sigma,n,m,d), Both affine hypotheses have legal support and the same marginal under the latent coupling.  This gives [the stated result](goal).-/
-- @node: affine_prior_support_and_common_marginal
lemma affine_prior_support_and_common_marginal (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps) :
    (∀ hyp lat, ModelClass d eps (normalizedLaw hyp n m d eps hd sigma lat)) ∧
    (∀ lat, auxMarginal (normalizedLaw true n m d eps hd sigma lat) =
      auxMarginal (normalizedLaw false n m d eps hd sigma lat)) ∧
    (affineProductPrior true n m d eps hd sigma).map auxMarginal =
      (affineProductPrior false n m d eps hd sigma).map auxMarginal := by
  have hs := (affine_support_and_normalizer n m d eps hn hd heps heps' sigma).2
  exact ⟨fun hyp lat => (hs lat).2.1 hyp, fun lat => (hs lat).2.2,
    affine_productPrior_common_marginal n m d eps hn hd heps heps' sigma⟩

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',hS,n,hx,d,m), In the affine regime the selected prior handle preserves the common marginal law.  This gives [the stated result](goal).-/
-- @node: affine_selectedPrior_common_marginal
lemma affine_selectedPrior_common_marginal (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (hS : Real.exp 4096 ≤ (n : Real) * eps)
    (hx : 1 / ((n : Real) * eps) <
      ((d : Real) / (((n : Real) + m) * eps * logScale n eps)) ^ 2) :
    (affinePrior true n m d eps hn hd heps heps').map auxMarginal =
      (affinePrior false n m d eps hn hd heps heps').map auxMarginal := by
  have hbranch : ¬ (labelScale n eps < Real.exp 4096 ∨
      ((d : Real) / (((n : Real) + m) * eps * logScale n eps)) ^ 2 ≤
        1 / labelScale n eps) := by
    exact not_or.mpr ⟨not_lt.mpr hS, not_le.mpr hx⟩
  simp only [affinePrior, hbranch, if_false]
  exact affine_productPrior_common_marginal n m d eps hn hd heps heps' _

-- @node: lem:normalized-affine-testing
/-- Under the stated inputs and conditions, The normalized affine priors have legal support and a common auxiliary-table distribution, and
prove the all-rule lower bound. This gives [the stated conclusion](goal). -/
lemma normalized_affine_testing :
    ∃ c : Real, 0 < c ∧ ∀ (n m d : Nat) (eps : Real),
      ∀ hn : 1 ≤ n, ∀ hd : 2 ≤ d, ∀ heps : 0 < eps, ∀ heps' : eps ≤ 1 / 4,
      Real.exp 4096 ≤ (n : Real) * eps →
      let x := (d : Real) / (((n : Real) + m) * eps * logScale n eps)
      1 / ((n : Real) * eps) < x ^ 2 →
      (∀ sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps,
        (∀ hyp lat, ModelClass d eps (normalizedLaw hyp n m d eps hd sigma lat)) ∧
        (∀ lat, auxMarginal (normalizedLaw true n m d eps hd sigma lat) =
          auxMarginal (normalizedLaw false n m d eps hd sigma lat)) ∧
        (affineProductPrior true n m d eps hd sigma).map auxMarginal =
          (affineProductPrior false n m d eps hd sigma).map auxMarginal) ∧
      (affinePrior true n m d eps hn hd heps heps').map auxMarginal =
        (affinePrior false n m d eps hn hd heps heps').map auxMarginal ∧
      c * min 1 (x ^ 2) ≤ minimaxRisk n m d eps := by
  refine ⟨10 ^ (-20 : Int) / 128, by positivity, ?_⟩
  intro n m d eps hn hd heps heps' hS x hx
  refine ⟨fun sigma => affine_prior_support_and_common_marginal n m d eps hn hd heps heps' sigma,
    affine_selectedPrior_common_marginal n m d eps hn hd heps heps' hS hx, ?_⟩
  obtain ⟨sigma⟩ := affine_schedule_dual n m d eps hn heps heps'
  exact affine_fixed_minimax_rate_lower n m d eps hn hd heps heps' hS hx sigma

end CausalSmith.Stat.AnnotationRarearmFrontier
