module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.NumericalConcentration
public import Causalean.Stat.Minimax.FuzzyHypotheses

/-!
Normalized affine-prior concentration and the two-prior testing step in equation (11).
The experiment-distance estimate is a separate input, to be proved for the raw experiment.
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
open Causalean.Stat.Minimax.FuzzyHypotheses
open Causalean.Stat.Minimax.MomentMatchedMixture

/-- [Under the stated inputs and conditions](hyp:d), The ATE is Borel measurable in the finite table of observable atom probabilities.  This gives [the stated result](goal).-/
-- @node: affine_ateFunctional_measurable
@[fun_prop]
lemma affine_ateFunctional_measurable (d : Nat) :
    Measurable (ateFunctional (d := d)) := by
  have hj (j : Fin d) (a y : Bool) :
      Measurable (fun P : DiscreteLaw d => jointMass P j a y) := by
    exact (measurable_pi_apply (j, a, y)).comp
      (comap_measurable (fun P : DiscreteLaw d => fun o => (P.pmf o).toReal))
  unfold ateFunctional cellMass outcomeMean markedMass armMass
  fun_prop

/-- [Under the stated inputs and conditions](hyp:hyp,eps,hd,sigma,n,m,d), Each normalized affine prior is a probability measure, including its zero filler.  This gives [the stated result](goal).-/
-- @node: affine_productPrior_isProbabilityMeasure
lemma affine_productPrior_isProbabilityMeasure (hyp : Bool) (n m d : Nat)
    (eps : Real) (hd : 2 ≤ d)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps) :
    IsProbabilityMeasure (affineProductPrior hyp n m d eps hd sigma) := by
  unfold affineProductPrior
  apply Measure.isProbabilityMeasure_map
  fun_prop

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',hS,n,hx,d,sigma,hyp,m), Pushing forward the latent tail bound gives concentration for the actual law prior.  This gives [the stated result](goal).-/
-- @node: affine_productPrior_target_tail_small
lemma affine_productPrior_target_tail_small (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (hS : Real.exp 4096 ≤ (n : Real) * eps)
    (hx : 1 / ((n : Real) * eps) <
      ((d : Real) / (((n : Real) + m) * eps * logScale n eps)) ^ 2)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool) :
    let nu := Measure.pi (fun _ : Fin (affineTuning n m d eps).Kstar => (latentPMF sigma).toMeasure)
    let t := fun i => ∫ lat, affineRawTarget n m d eps sigma i lat ∂nu
    let gap := t true - t false
    (affineProductPrior hyp n m d eps hd sigma).real
      {P | gap / 8 < |ateFunctional P - t hyp|} ≤ 1 / 128 := by
  intro nu t gap
  have hmap : Measurable (normalizedLaw hyp n m d eps hd sigma) := by fun_prop
  have hset : MeasurableSet {P : DiscreteLaw d | gap / 8 < |ateFunctional P - t hyp|} := by
    exact measurableSet_lt measurable_const
      (continuous_abs.measurable.comp
        ((affine_ateFunctional_measurable d).sub measurable_const))
  change ((nu.map (normalizedLaw hyp n m d eps hd sigma))
    {P | gap / 8 < |ateFunctional P - t hyp|}).toReal ≤ _
  rw [Measure.map_apply hmap hset]
  have htail := affine_normalized_target_tail_small n m d eps hn hd heps heps' hS hx sigma hyp
  change nu.real _ ≤ _ at htail
  apply le_trans (measureReal_mono ?_) htail
  intro lat hlat
  change gap / 8 < |ateFunctional (normalizedLaw hyp n m d eps hd sigma lat) - t hyp| at hlat
  exact hlat.le

/-- [Under the stated inputs and conditions](hyp:X,eps,hn,hd,heps,heps',hS,n,hx,d,sigma,K,hK,estimator,hestimator,htv,m), With the raw-mixture distance budget, every measurable rule has Bayes risk at least
one sixty-fourth of the squared affine target gap. This is equation (11).  This gives [the stated result](goal).-/
-- @node: affine_two_prior_bayes_lower
lemma affine_two_prior_bayes_lower {X : Type*} [MeasurableSpace X]
    (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (hS : Real.exp 4096 ≤ (n : Real) * eps)
    (hx : 1 / ((n : Real) * eps) <
      ((d : Real) / (((n : Real) + m) * eps * logScale n eps)) ^ 2)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (K : Kernel (DiscreteLaw d) X) (hK : ∀ P, IsProbabilityMeasure (K P))
    (estimator : X → Real) (hestimator : Measurable estimator)
    (htv : Causalean.Stat.tvDist
      (priorPredictive (affineProductPrior false n m d eps hd sigma) K)
      (priorPredictive (affineProductPrior true n m d eps hd sigma) K) ≤ 1 / 64) :
    let nu := Measure.pi (fun _ : Fin (affineTuning n m d eps).Kstar => (latentPMF sigma).toMeasure)
    let t := fun i => ∫ lat, affineRawTarget n m d eps sigma i lat ∂nu
    let gap := t true - t false
    ENNReal.ofReal (gap ^ 2 / 64) ≤
      max (bayesSquaredRisk (affineProductPrior false n m d eps hd sigma) K ateFunctional estimator)
        (bayesSquaredRisk (affineProductPrior true n m d eps hd sigma)
          K ateFunctional estimator) := by
  intro nu t gap
  let := affine_productPrior_isProbabilityMeasure false n m d eps hd sigma
  let := affine_productPrior_isProbabilityMeasure true n m d eps hd sigma
  have hS1 : 1 ≤ (n : Real) * eps := by
    linarith [Real.add_one_le_exp (4096 : Real)]
  have hKpos : (0 : Real) < (affineTuning n m d eps).Kstar := by
    exact_mod_cast affine_tuning_Kstar_pos n m d eps hn hd heps heps' hS1
  have hb := (affine_tuning_bounds n m d eps hn hd heps heps').2.2.2.2.2.2.1
  have hgapbound := affine_raw_target_mean_gap n m d eps hn hd heps heps' sigma
  have hgap : 0 < gap := lt_of_lt_of_le (by positivity) hgapbound
  have hlower := twoFuzzyHypotheses_bayesRisk_lower
    (affineProductPrior false n m d eps hd sigma)
    (affineProductPrior true n m d eps hd sigma) K ateFunctional hK
    estimator hestimator (affine_ateFunctional_measurable d)
    (t false) (t true) gap (gap / 8) (1 / 128) (1 / 128) (1 / 64)
    hgap.le (by positivity) (by linarith) (le_refl _)
    (by norm_num) (by norm_num) (by norm_num)
    (affine_productPrior_target_tail_small n m d eps hn hd heps heps' hS hx sigma false)
    (affine_productPrior_target_tail_small n m d eps hn hd heps heps' hS hx sigma true) htv
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) hlower
  nlinarith [sq_nonneg gap]

end CausalSmith.Stat.AnnotationRarearmFrontier
