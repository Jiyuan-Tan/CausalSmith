module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.AtomHistogram

/-!
The actual ordered random-scale experiment and its two-channel mixture distance,
including the independent uniform seed used by randomized rules.
-/

@[expose] public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.Minimax.MomentMatchedMixture
open Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram
open Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix.RandomScaleMinimaxTransfer

/-- Conditional on the latent table, both ordered channels have their normalized
mark laws and independent Poisson totals at the shared raw scale. -/
-- @node: affineOrderedRawKernel
noncomputable def affineOrderedRawKernel (n m d : Nat) (eps : Real) (hd : 2 ≤ d)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool) :
    Kernel (Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L)
      (RawTwoPool (Obs d) (AuxObs d)) :=
  Kernel.ofFunOfCountable fun lat =>
    let t := affineTuning n m d eps
    let P := normalizedLaw hyp n m d eps hd sigma lat
    let Q := rawNormalizer n m d eps sigma lat
    (finitePoissonSampleLaw P.pmf.toMeasure (Real.toNNReal (t.u * Q))).prod
      (finitePoissonSampleLaw (auxMarginal P).toMeasure (Real.toNNReal (t.w * Q)))

/-- The actual ordered experiment is a probability kernel. -/
-- @node: affineOrderedRawKernel_isMarkovKernel
instance affineOrderedRawKernel_isMarkovKernel (n m d : Nat) (eps : Real) (hd : 2 ≤ d)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool) : IsMarkovKernel (affineOrderedRawKernel n m d eps hd sigma hyp) where
  isProbabilityMeasure lat := by
    change IsProbabilityMeasure ((finitePoissonSampleLaw _ _).prod (finitePoissonSampleLaw _ _))
    infer_instance

/-- [Under the stated inputs and conditions](hyp:eps,hd,sigma,hyp,n,m,d), The exact normalized mark laws and raw normalizer instantiate the shared-scale
experiment property required by the fixed-size transfer theorem.  This gives [the stated result](goal).-/
-- @node: affineOrderedRawKernel_isRandomScale
lemma affineOrderedRawKernel_isRandomScale (n m d : Nat) (eps : Real) (hd : 2 ≤ d)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool) :
    let P := Kernel.ofFunOfCountable fun lat =>
      (normalizedLaw hyp n m d eps hd sigma lat).pmf.toMeasure
    let Q := Kernel.ofFunOfCountable fun lat =>
      (auxMarginal (normalizedLaw hyp n m d eps hd sigma lat)).toMeasure
    letI : ∀ lat, IsProbabilityMeasure (P lat) := by
      intro lat
      change IsProbabilityMeasure (normalizedLaw hyp n m d eps hd sigma lat).pmf.toMeasure
      infer_instance
    letI : ∀ lat, IsProbabilityMeasure (Q lat) := by
      intro lat
      change IsProbabilityMeasure (auxMarginal (normalizedLaw hyp n m d eps hd sigma lat)).toMeasure
      infer_instance
    let S := fun lat => Real.toNNReal (rawNormalizer n m d eps sigma lat)
    IsRandomScaleTwoPoolExperiment (affineOrderedRawKernel n m d eps hd sigma hyp)
      P Q S (Real.toNNReal (affineTuning n m d eps).u)
        (Real.toNNReal (affineTuning n m d eps).w) := by
  intro P Q S lat
  change (finitePoissonSampleLaw (normalizedLaw hyp n m d eps hd sigma lat).pmf.toMeasure
      (Real.toNNReal (_ * _))).prod
      (finitePoissonSampleLaw (auxMarginal (normalizedLaw hyp n m d eps hd sigma lat)).toMeasure
        (Real.toNNReal (_ * _))) =
    (finitePoissonSampleLaw (normalizedLaw hyp n m d eps hd sigma lat).pmf.toMeasure
      (Real.toNNReal _ * Real.toNNReal _)).prod
      (finitePoissonSampleLaw (auxMarginal (normalizedLaw hyp n m d eps hd sigma lat)).toMeasure
        (Real.toNNReal _ * Real.toNNReal _))
  rw [Real.toNNReal_mul (by change 0 ≤ 128 * (n : Real); positivity),
    Real.toNNReal_mul (by change 0 ≤ 128 * ((n : Real) + m); positivity)]

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',sigma,hyp,n,m,d), The atom-histogram reconstruction equals the actual ordered conditional law.  This gives [the stated result](goal).-/
-- @node: affineOrderedRawKernel_eq_reconstruction
lemma affineOrderedRawKernel_eq_reconstruction (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool) :
    affineOrderedRawKernel n m d eps hd sigma hyp =
      pairedHistogramReconstructionKernel (Obs d) (AuxObs d) ∘ₖ
        affineHistogramKernel n m d eps sigma hyp := by
  ext lat : 1
  exact (affineHistogramKernel_ordered_apply n m d eps hn hd heps heps' sigma hyp lat).symm

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',sigma,n,m,d), The distance budget holds for the actual normalized ordered random-scale
experiment, retaining both original observation channels.  This gives [the stated result](goal).-/
-- @node: affineOrderedRawKernel_predictive_tv_small
lemma affineOrderedRawKernel_predictive_tv_small (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps) :
    let nu := Measure.pi fun _ : Fin (affineTuning n m d eps).Kstar => (latentPMF sigma).toMeasure
    Causalean.Stat.tvDist
      (priorPredictive nu (affineOrderedRawKernel n m d eps hd sigma false))
      (priorPredictive nu (affineOrderedRawKernel n m d eps hd sigma true)) < 1 / 64 := by
  intro nu
  rw [affineOrderedRawKernel_eq_reconstruction n m d eps hn hd heps heps' sigma false,
    affineOrderedRawKernel_eq_reconstruction n m d eps hn hd heps heps' sigma true]
  exact affineHistogramKernel_ordered_predictive_tv_small n m d eps hn hd heps heps' sigma

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',sigma,n,m,d), A common independent uniform seed preserves the ordered mixture TV budget.  This gives [the stated result](goal).-/
-- @node: affineOrderedRawKernel_randomized_tv_small
lemma affineOrderedRawKernel_randomized_tv_small (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps) :
    let nu := Measure.pi fun _ : Fin (affineTuning n m d eps).Kstar => (latentPMF sigma).toMeasure
    Causalean.Stat.tvDist
      ((priorPredictive nu (affineOrderedRawKernel n m d eps hd sigma false)).prod seedLaw)
      ((priorPredictive nu (affineOrderedRawKernel n m d eps hd sigma true)).prod seedLaw) <
      1 / 64 := by
  intro nu
  let : IsProbabilityMeasure seedLaw := ⟨by norm_num [seedLaw, Real.volume_Icc]⟩
  let hp (hyp : Bool) : IsProbabilityMeasure
      (priorPredictive nu (affineOrderedRawKernel n m d eps hd sigma hyp)) :=
    priorPredictive_isProbability nu _ (fun _ => inferInstance)
  let := hp false
  let := hp true
  have hprod := tvDist_prod_le_add
    (priorPredictive nu (affineOrderedRawKernel n m d eps hd sigma false))
    (priorPredictive nu (affineOrderedRawKernel n m d eps hd sigma true)) seedLaw seedLaw
  have hself : Causalean.Stat.tvDist seedLaw seedLaw = 0 := by
    simp [Causalean.Stat.tvDist]
  rw [hself, add_zero] at hprod
  exact hprod.trans_lt
    (affineOrderedRawKernel_predictive_tv_small n m d eps hn hd heps heps' sigma)

end CausalSmith.Stat.AnnotationRarearmFrontier
