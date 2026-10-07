module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.OrderedExperiment
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.Testing

/-!
Two-prior testing for the actual ordered raw experiment. A hypothesis tag retains
its raw scale together with the latent vector, so the same parameter space can
also be used by the random-scale fixed-size transfer.
-/

@[expose] public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
open Causalean.Stat.Minimax.FuzzyHypotheses
open Causalean.Stat.Minimax.MomentMatchedMixture
open Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix.RandomScaleMinimaxTransfer

/-- The raw parameter retains the hypothesis and its finite latent draw. -/
-- @node: AffineRawParameter
abbrev AffineRawParameter (n m d : Nat) (eps : Real) :=
  Bool × (Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L)

variable (n m d : Nat) (eps : Real) (hd : 2 ≤ d)
  (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)

/-- The tagged prior draws the common latent vector with a fixed hypothesis. -/
-- @node: affineRawTaggedPrior
noncomputable def affineRawTaggedPrior (hyp : Bool) : Measure (AffineRawParameter n m d eps) :=
  (Measure.pi fun _ : Fin (affineTuning n m d eps).Kstar =>
    (latentPMF sigma).toMeasure).map (fun lat => (hyp, lat))

/-- Both tagged priors are probability measures. -/
-- @node: affineRawTaggedPrior_isProbabilityMeasure
instance affineRawTaggedPrior_isProbabilityMeasure (hyp : Bool) :
    IsProbabilityMeasure (affineRawTaggedPrior n m d eps sigma hyp) := by
  unfold affineRawTaggedPrior
  apply Measure.isProbabilityMeasure_map
  fun_prop

/-- The tagged experiment keeps both ordered channels and the independent seed. -/
-- @node: affineRawTaggedKernel
noncomputable def affineRawTaggedKernel :
    Kernel (AffineRawParameter n m d eps) (RawTwoPool (Obs d) (AuxObs d) × Real) :=
  Kernel.ofFunOfCountable fun theta =>
    (affineOrderedRawKernel n m d eps hd sigma theta.1 theta.2).prod seedLaw

/-- Each tagged conditional law is a probability law. -/
-- @node: affineRawTaggedKernel_isMarkovKernel
instance affineRawTaggedKernel_isMarkovKernel :
    IsMarkovKernel (affineRawTaggedKernel n m d eps hd sigma) where
  isProbabilityMeasure theta := by
    let : IsProbabilityMeasure seedLaw := ⟨by norm_num [seedLaw, Real.volume_Icc]⟩
    change IsProbabilityMeasure ((_ : Measure (RawTwoPool (Obs d) (AuxObs d))).prod seedLaw)
    infer_instance

/-- [Under the stated inputs and conditions](hyp:hyp), Mixing the tagged experiment reads back to the seeded ordered raw mixture.  This gives [the stated result](goal).-/
-- @node: affineRawTaggedKernel_predictive
lemma affineRawTaggedKernel_predictive (hyp : Bool) :
    priorPredictive (affineRawTaggedPrior n m d eps sigma hyp)
      (affineRawTaggedKernel n m d eps hd sigma) =
    (priorPredictive
      (Measure.pi fun _ : Fin (affineTuning n m d eps).Kstar => (latentPMF sigma).toMeasure)
      (affineOrderedRawKernel n m d eps hd sigma hyp)).prod seedLaw := by
  let : IsProbabilityMeasure seedLaw := ⟨by norm_num [seedLaw, Real.volume_Icc]⟩
  ext A hA : 1
  rw [priorPredictive_apply _ _ hA]
  unfold affineRawTaggedPrior
  rw [lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
  change (∫⁻ lat, ((affineOrderedRawKernel n m d eps hd sigma hyp lat).prod seedLaw) A
    ∂Measure.pi _) = _
  rw [Measure.prod_apply hA]
  rw [lintegral_priorPredictive _ _ _]
  · apply lintegral_congr
    intro lat
    rw [Measure.prod_apply hA]
  · exact measurable_measure_prodMk_left hA

/-- [Under the stated hypotheses](hyp:hn,heps,heps',hS,hx,hyp), The tagged normalized target has the paper's concentration budget.  This gives [the stated result](goal). -/
-- @node: affineRawTaggedPrior_target_tail
lemma affineRawTaggedPrior_target_tail
    (hn : 1 ≤ n) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (hS : Real.exp 4096 ≤ (n : Real) * eps)
    (hx : 1 / ((n : Real) * eps) <
      ((d : Real) / (((n : Real) + m) * eps * logScale n eps)) ^ 2) (hyp : Bool) :
    let nu := Measure.pi fun _ : Fin (affineTuning n m d eps).Kstar => (latentPMF sigma).toMeasure
    let t := fun i => ∫ lat, affineRawTarget n m d eps sigma i lat ∂nu
    let target := fun theta : AffineRawParameter n m d eps =>
      ateFunctional (normalizedLaw theta.1 n m d eps hd sigma theta.2)
    (affineRawTaggedPrior n m d eps sigma hyp).real
      {theta | (t true - t false) / 8 < |target theta - t hyp|} ≤ 1 / 128 := by
  intro nu t target
  unfold affineRawTaggedPrior Measure.real
  rw [Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet]
  have ht := affine_normalized_target_tail_small n m d eps hn hd heps heps' hS hx sigma hyp
  apply le_trans (measureReal_mono ?_) ht
  intro lat hlat
  change (t true - t false) / 8 <
    |ateFunctional (normalizedLaw hyp n m d eps hd sigma lat) - t hyp| at hlat
  exact hlat.le

/-- [Under the stated inputs and conditions](hyp:hyp,estimator), The tagged Bayes risk is exactly the latent average of the actual seeded
conditional squared risk; tagging changes no observation or loss.  This gives [the stated result](goal).-/
-- @node: affineRawTaggedKernel_bayes_readback
lemma affineRawTaggedKernel_bayes_readback (hyp : Bool)
    (estimator : RawTwoPool (Obs d) (AuxObs d) × Real → Real) :
    bayesSquaredRisk (affineRawTaggedPrior n m d eps sigma hyp)
      (affineRawTaggedKernel n m d eps hd sigma)
      (fun theta => ateFunctional (normalizedLaw theta.1 n m d eps hd sigma theta.2)) estimator =
    ∫⁻ lat, ∫⁻ z,
      ENNReal.ofReal ((estimator z -
        ateFunctional (normalizedLaw hyp n m d eps hd sigma lat)) ^ 2)
      ∂((affineOrderedRawKernel n m d eps hd sigma hyp lat).prod seedLaw)
      ∂(Measure.pi fun _ : Fin (affineTuning n m d eps).Kstar => (latentPMF sigma).toMeasure) := by
  unfold bayesSquaredRisk affineRawTaggedPrior
  rw [lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
  rfl

/-- [Under the stated hypotheses](hyp:hn,heps,heps',hS,hx,hestimator), Every randomized measurable rule in the actual raw experiment has a Bayes
risk at least one sixty-fourth of the squared raw target gap.  This gives [the stated result](goal). -/
-- @node: affineRawTaggedKernel_bayes_lower
lemma affineRawTaggedKernel_bayes_lower
    (hn : 1 ≤ n) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (hS : Real.exp 4096 ≤ (n : Real) * eps)
    (hx : 1 / ((n : Real) * eps) <
      ((d : Real) / (((n : Real) + m) * eps * logScale n eps)) ^ 2)
    (estimator : RawTwoPool (Obs d) (AuxObs d) × Real → Real)
    (hestimator : Measurable estimator) :
    let nu := Measure.pi fun _ : Fin (affineTuning n m d eps).Kstar => (latentPMF sigma).toMeasure
    let t := fun i => ∫ lat, affineRawTarget n m d eps sigma i lat ∂nu
    let gap := t true - t false
    let target := fun theta : AffineRawParameter n m d eps =>
      ateFunctional (normalizedLaw theta.1 n m d eps hd sigma theta.2)
    ENNReal.ofReal (gap ^ 2 / 64) ≤
      max (bayesSquaredRisk (affineRawTaggedPrior n m d eps sigma false)
        (affineRawTaggedKernel n m d eps hd sigma) target estimator)
        (bayesSquaredRisk (affineRawTaggedPrior n m d eps sigma true)
          (affineRawTaggedKernel n m d eps hd sigma) target estimator) := by
  intro nu t gap target
  have hS1 : 1 ≤ (n : Real) * eps := by
    linarith [Real.add_one_le_exp (4096 : Real)]
  have hKpos : (0 : Real) < (affineTuning n m d eps).Kstar := by
    exact_mod_cast affine_tuning_Kstar_pos n m d eps hn hd heps heps' hS1
  have hb := (affine_tuning_bounds n m d eps hn hd heps heps').2.2.2.2.2.2.1
  have hgapbound := affine_raw_target_mean_gap n m d eps hn hd heps heps' sigma
  have hgap : 0 < gap := lt_of_lt_of_le (by positivity) hgapbound
  have htv : Causalean.Stat.tvDist
      (priorPredictive (affineRawTaggedPrior n m d eps sigma false)
        (affineRawTaggedKernel n m d eps hd sigma))
      (priorPredictive (affineRawTaggedPrior n m d eps sigma true)
        (affineRawTaggedKernel n m d eps hd sigma)) ≤ 1 / 64 := by
    rw [affineRawTaggedKernel_predictive, affineRawTaggedKernel_predictive]
    exact (affineOrderedRawKernel_randomized_tv_small n m d eps hn hd heps heps' sigma).le
  have hlower := twoFuzzyHypotheses_bayesRisk_lower
    (affineRawTaggedPrior n m d eps sigma false)
    (affineRawTaggedPrior n m d eps sigma true)
    (affineRawTaggedKernel n m d eps hd sigma) target (fun _ => inferInstance)
    estimator hestimator (measurable_of_countable _)
    (t false) (t true) gap (gap / 8) (1 / 128) (1 / 128) (1 / 64)
    (by linarith) (le_refl _)
    (affineRawTaggedPrior_target_tail n m d eps hd sigma hn heps heps' hS hx false)
    (affineRawTaggedPrior_target_tail n m d eps hd sigma hn heps heps' hS hx true) htv
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) hlower
  nlinarith [sq_nonneg gap]

end CausalSmith.Stat.AnnotationRarearmFrontier
