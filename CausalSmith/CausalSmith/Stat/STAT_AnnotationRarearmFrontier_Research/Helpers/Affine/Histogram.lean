module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.ControlSplit
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.PairedHistogram.HistogramReconstruction.PairedTransport

/-!
Embedding the five rare-cell count coordinates and the four common reservoir
counts into both original atom histograms, followed by uniform channel ordering.
-/

@[expose] public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
open Causalean.Stat.Minimax.MomentMatchedMixture
open Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram

/-- Place rare-cell counts at their original labels, reservoir counts at label k,
and zeros at unused labels. Complete control outcomes are always zero. -/
-- @node: affineFullCountHistograms
def affineFullCountHistograms (d k : Nat)
    (counts : (Fin k → ((Nat × Nat) × (Nat × (Nat × Nat)))) ×
      ((Nat × Nat) × (Nat × Nat))) : (Obs d → Nat) × (AuxObs d → Nat) :=
  (fun z => if hj : z.1.val < k then
      let c := counts.1 ⟨z.1.val, hj⟩
      if z.2.1 then (if z.2.2 then c.1.1 else c.1.2)
      else (if z.2.2 then 0 else c.2.2.1)
    else if z.1.val = k then
      if z.2.2 then 0 else if z.2.1 then counts.2.1.1 else counts.2.1.2
    else 0,
   fun z => if hj : z.1.val < k then
      let c := counts.1 ⟨z.1.val, hj⟩
      if z.2 then c.2.1 else c.2.2.2
    else if z.1.val = k then
      if z.2 then counts.2.2.1 else counts.2.2.2
    else 0)

/-- [Both histogram channels are measurable functions of the finite count coordinates. ](goal)-/
-- @node: affineFullCountHistograms_measurable
@[fun_prop]
lemma affineFullCountHistograms_measurable (d k : Nat) :
    Measurable (affineFullCountHistograms d k) := by
  exact measurable_of_countable _

/-- [Under the stated inputs and conditions](hyp:counts,j,hj,d,k), The five rare-cell coordinates occupy exactly their original complete and
auxiliary atoms, with no positive complete control outcomes.  This gives [the stated result](goal).-/
-- @node: affineFullCountHistograms_rare
lemma affineFullCountHistograms_rare (d k : Nat)
    (counts : (Fin k → ((Nat × Nat) × (Nat × (Nat × Nat)))) ×
      ((Nat × Nat) × (Nat × Nat))) (j : Fin d) (hj : j.val < k) :
    let c := counts.1 ⟨j.val, hj⟩
    (affineFullCountHistograms d k counts).1 (j, true, true) = c.1.1 ∧
    (affineFullCountHistograms d k counts).1 (j, true, false) = c.1.2 ∧
    (affineFullCountHistograms d k counts).1 (j, false, false) = c.2.2.1 ∧
    (affineFullCountHistograms d k counts).1 (j, false, true) = 0 ∧
    (affineFullCountHistograms d k counts).2 (j, true) = c.2.1 ∧
    (affineFullCountHistograms d k counts).2 (j, false) = c.2.2.2 := by
  simp [affineFullCountHistograms, hj]

/-- [Under the stated inputs and conditions](hyp:counts,j,hj,d,k), All four reservoir coordinates are retained, and its complete outcomes are zero.  This gives [the stated result](goal).-/
-- @node: affineFullCountHistograms_reservoir
lemma affineFullCountHistograms_reservoir (d k : Nat)
    (counts : (Fin k → ((Nat × Nat) × (Nat × (Nat × Nat)))) ×
      ((Nat × Nat) × (Nat × Nat))) (j : Fin d) (hj : j.val = k) :
    (affineFullCountHistograms d k counts).1 (j, true, false) = counts.2.1.1 ∧
    (affineFullCountHistograms d k counts).1 (j, false, false) = counts.2.1.2 ∧
    (affineFullCountHistograms d k counts).1 (j, true, true) = 0 ∧
    (affineFullCountHistograms d k counts).1 (j, false, true) = 0 ∧
    (affineFullCountHistograms d k counts).2 (j, true) = counts.2.2.1 ∧
    (affineFullCountHistograms d k counts).2 (j, false) = counts.2.2.2 := by
  simp [affineFullCountHistograms, hj]

/-- [Under the stated inputs and conditions](hyp:counts,j,hj,d,k,a,y), Labels beyond the reservoir contribute no counts in either channel.  This gives [the stated result](goal).-/
-- @node: affineFullCountHistograms_null
lemma affineFullCountHistograms_null (d k : Nat)
    (counts : (Fin k → ((Nat × Nat) × (Nat × (Nat × Nat)))) ×
      ((Nat × Nat) × (Nat × Nat))) (j : Fin d) (hj : k < j.val) (a y : Bool) :
    (affineFullCountHistograms d k counts).1 (j, a, y) = 0 ∧
    (affineFullCountHistograms d k counts).2 (j, a) = 0 := by
  simp [affineFullCountHistograms, not_lt.mpr hj.le, ne_of_gt hj]

/-- The reservoir has independent zero-outcome complete and auxiliary counts
in both arms, each with half the common reservoir mass. -/
-- @node: affineReservoirCountLaw
noncomputable def affineReservoirCountLaw (n m d : Nat) (eps : Real)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps) :
    Measure ((Nat × Nat) × (Nat × Nat)) :=
  let t := affineTuning n m d eps
  let pstar := 1 - (t.Kstar : Real) * latentMeanMass sigma
  let complete := poissonMeasure (Real.toNNReal (t.u * (pstar / 2)))
  let auxiliary := poissonMeasure (Real.toNNReal (t.w * (pstar / 2)))
  (complete.prod complete).prod (auxiliary.prod auxiliary)

/-- The common reservoir count law has total mass one. -/
-- @node: affineReservoirCountLaw_isProbabilityMeasure
instance affineReservoirCountLaw_isProbabilityMeasure (n m d : Nat) (eps : Real)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps) :
    IsProbabilityMeasure (affineReservoirCountLaw n m d eps sigma) := by
  unfold affineReservoirCountLaw
  infer_instance

/-- Embed the independent full rare-cell mixtures and the construction's common
reservoir into the two complete atom histograms. -/
-- @node: affineHistogramPredictive
noncomputable def affineHistogramPredictive (n m d : Nat) (eps : Real)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool) : Measure ((Obs d → Nat) × (AuxObs d → Nat)) :=
  let t := affineTuning n m d eps
  Kernel.deterministic (affineFullCountHistograms d t.Kstar)
    (affineFullCountHistograms_measurable d t.Kstar) ∘ₘ
      ((Measure.pi fun _ : Fin t.Kstar =>
        affineCellFullPoissonPredictive sigma t.u t.w hyp).prod
          (affineReservoirCountLaw n m d eps sigma))

/-- The embedded histogram mixture is a probability law in both channels. -/
-- @node: affineHistogramPredictive_isProbabilityMeasure
instance affineHistogramPredictive_isProbabilityMeasure (n m d : Nat) (eps : Real)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool) : IsProbabilityMeasure (affineHistogramPredictive n m d eps sigma hyp) := by
  unfold affineHistogramPredictive
  infer_instance

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',sigma,n,m,d), The embedded paired histogram experiment satisfies the full joint TV budget.  This gives [the stated result](goal).-/
-- @node: affineHistogramPredictive_tv_small
lemma affineHistogramPredictive_tv_small (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps) :
    Causalean.Stat.tvDist (affineHistogramPredictive n m d eps sigma true)
      (affineHistogramPredictive n m d eps sigma false) < 1 / 64 := by
  let t := affineTuning n m d eps
  have hprod := tvDist_prod_le_add
    (Measure.pi fun _ : Fin t.Kstar => affineCellFullPoissonPredictive sigma t.u t.w true)
    (Measure.pi fun _ : Fin t.Kstar => affineCellFullPoissonPredictive sigma t.u t.w false)
    (affineReservoirCountLaw n m d eps sigma) (affineReservoirCountLaw n m d eps sigma)
  have hself : Causalean.Stat.tvDist (affineReservoirCountLaw n m d eps sigma)
      (affineReservoirCountLaw n m d eps sigma) = 0 := by
    simp [Causalean.Stat.tvDist]
  rw [hself, add_zero] at hprod
  exact (Causalean.Stat.tvDist_bind_le _ _
    (Kernel.deterministic (affineFullCountHistograms d t.Kstar)
      (affineFullCountHistograms_measurable d t.Kstar))).trans_lt
    (hprod.trans_lt
      (affineCellFullPoissonPredictive_product_tv_small n m d eps hn hd heps heps' sigma))

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',sigma,n,m,d), Uniform ordering independently restores both channels without increasing
the distance of the embedded full count mixtures.  This gives [the stated result](goal).-/
-- @node: affineHistogramPredictive_ordered_tv_small
lemma affineHistogramPredictive_ordered_tv_small (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps) :
    Causalean.Stat.tvDist
      (pairedHistogramReconstructionKernel (Obs d) (AuxObs d) ∘ₘ
        affineHistogramPredictive n m d eps sigma true)
      (pairedHistogramReconstructionKernel (Obs d) (AuxObs d) ∘ₘ
        affineHistogramPredictive n m d eps sigma false) < 1 / 64 := by
  exact (Causalean.Stat.tvDist_bind_le _ _
    (pairedHistogramReconstructionKernel (Obs d) (AuxObs d))).trans_lt
    (affineHistogramPredictive_tv_small n m d eps hn hd heps heps' sigma)

/-- The conditional product of the five full cell coordinates over the actual
latent vector, before adding the common reservoir. -/
-- @node: affineFullCellProductKernel
noncomputable def affineFullCellProductKernel {L : Nat} {B eps : Real}
    (sigma : ConeDual L B eps) (k : Nat) (u w : Real) (hyp : Bool) :
    Kernel (Fin k → Latent L) (Fin k → ((Nat × Nat) × (Nat × (Nat × Nat)))) :=
  Kernel.ofFunOfCountable fun lat =>
    Measure.pi fun i : Fin k => affineCellFullPoissonLaw sigma u w hyp (lat i)

/-- Each full conditional product is a probability kernel. -/
-- @node: affineFullCellProductKernel_isMarkovKernel
instance affineFullCellProductKernel_isMarkovKernel {L : Nat} {B eps : Real}
    (sigma : ConeDual L B eps) (k : Nat) (u w : Real) (hyp : Bool) :
    IsMarkovKernel (affineFullCellProductKernel sigma k u w hyp) where
  isProbabilityMeasure lat := by
    change IsProbabilityMeasure
      (Measure.pi fun i : Fin k => affineCellFullPoissonLaw sigma u w hyp (lat i))
    infer_instance

/-- [Under the stated inputs and conditions](hyp:L,sigma,k,hyp,B,eps,u,w), Mixing the full conditional cell products over independent core/filler
latent draws gives exactly the product used by the histogram experiment.  This gives [the stated result](goal).-/
-- @node: affineFullCellProductKernel_predictive_eq
lemma affineFullCellProductKernel_predictive_eq {L : Nat} {B eps : Real}
    (sigma : ConeDual L B eps) (k : Nat) (u w : Real) (hyp : Bool) :
    priorPredictive (Measure.pi fun _ : Fin k => (latentPMF sigma).toMeasure)
      (affineFullCellProductKernel sigma k u w hyp) =
    Measure.pi fun _ : Fin k => affineCellFullPoissonPredictive sigma u w hyp := by
  classical
  apply Measure.ext_of_singleton
  intro o
  rw [priorPredictive_apply _ _ (measurableSet_singleton o), lintegral_fintype]
  change (∑ lat : Fin k → Latent L,
    (Measure.pi fun i : Fin k => affineCellFullPoissonLaw sigma u w hyp (lat i)) {o} *
      (Measure.pi fun _ : Fin k => (latentPMF sigma).toMeasure) {lat}) = _
  simp only [Measure.pi_singleton,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp only [affineCellFullPoissonPredictive, Measure.finsetSum_apply, Measure.smul_apply,
    smul_eq_mul]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro lat _
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact mul_comm _ _

/-- Attach the actual common reservoir to the full conditional cell experiment. -/
-- @node: affineFullCountKernel
noncomputable def affineFullCountKernel (n m d : Nat) (eps : Real)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool) :
    Kernel (Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L)
      ((Fin (affineTuning n m d eps).Kstar → ((Nat × Nat) × (Nat × (Nat × Nat)))) ×
        ((Nat × Nat) × (Nat × Nat))) :=
  let t := affineTuning n m d eps
  (affineFullCellProductKernel sigma t.Kstar t.u t.w hyp).prod
    (Kernel.const _ (affineReservoirCountLaw n m d eps sigma))

/-- The conditional full count law is a probability kernel. -/
-- @node: affineFullCountKernel_isMarkovKernel
instance affineFullCountKernel_isMarkovKernel (n m d : Nat) (eps : Real)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool) : IsMarkovKernel (affineFullCountKernel n m d eps sigma hyp) := by
  unfold affineFullCountKernel
  infer_instance

/-- [Under the stated inputs and conditions](hyp:eps,sigma,hyp,n,m,d), The independent reservoir factors out of the actual full latent mixture.  This gives [the stated result](goal).-/
-- @node: affineFullCountKernel_predictive_eq
lemma affineFullCountKernel_predictive_eq (n m d : Nat) (eps : Real)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool) :
    let t := affineTuning n m d eps
    priorPredictive (Measure.pi fun _ : Fin t.Kstar => (latentPMF sigma).toMeasure)
      (affineFullCountKernel n m d eps sigma hyp) =
      (Measure.pi fun _ : Fin t.Kstar =>
        affineCellFullPoissonPredictive sigma t.u t.w hyp).prod
          (affineReservoirCountLaw n m d eps sigma) := by
  intro t
  refine (Measure.prod_eq ?_).symm
  intro s r hs hr
  rw [priorPredictive_apply _ _ (hs.prod hr)]
  simp only [affineFullCountKernel, Kernel.prod_apply_prod, Kernel.const_apply]
  change (∫⁻ lat, (affineFullCellProductKernel sigma t.Kstar t.u t.w hyp lat) s *
    (affineReservoirCountLaw n m d eps sigma) r
      ∂Measure.pi fun _ : Fin t.Kstar => (latentPMF sigma).toMeasure) = _
  rw [lintegral_mul_const _ ((affineFullCellProductKernel sigma t.Kstar t.u t.w hyp).measurable_coe hs),
    ← priorPredictive_apply _ _ hs, affineFullCellProductKernel_predictive_eq]

/-- The concrete histogram embedding of the actual conditional full count law. -/
-- @node: affineHistogramKernel
noncomputable def affineHistogramKernel (n m d : Nat) (eps : Real)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool) :
    Kernel (Fin (affineTuning n m d eps).Kstar → Latent (affineTuning n m d eps).L)
      ((Obs d → Nat) × (AuxObs d → Nat)) :=
  Kernel.deterministic (affineFullCountHistograms d (affineTuning n m d eps).Kstar)
    (affineFullCountHistograms_measurable d (affineTuning n m d eps).Kstar) ∘ₖ
      affineFullCountKernel n m d eps sigma hyp

/-- The conditional histogram embedding is a probability kernel. -/
-- @node: affineHistogramKernel_isMarkovKernel
instance affineHistogramKernel_isMarkovKernel (n m d : Nat) (eps : Real)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool) : IsMarkovKernel (affineHistogramKernel n m d eps sigma hyp) := by
  unfold affineHistogramKernel
  infer_instance

/-- [Under the stated inputs and conditions](hyp:eps,sigma,hyp,n,m,d), The histogram predictive law is the mixture of the actual conditional
core/filler count embeddings, rather than an assumed identification.  This gives [the stated result](goal).-/
-- @node: affineHistogramKernel_predictive_eq
lemma affineHistogramKernel_predictive_eq (n m d : Nat) (eps : Real)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (hyp : Bool) :
    priorPredictive
      (Measure.pi fun _ : Fin (affineTuning n m d eps).Kstar => (latentPMF sigma).toMeasure)
      (affineHistogramKernel n m d eps sigma hyp) =
      affineHistogramPredictive n m d eps sigma hyp := by
  rw [affineHistogramKernel, kernel_comp_priorPredictive, affineFullCountKernel_predictive_eq]
  rfl

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',sigma,n,m,d), The ordered, mixed conditional histogram experiment obeys the joint TV
budget in the orientation used by the two-prior testing inequality.  This gives [the stated result](goal).-/
-- @node: affineHistogramKernel_ordered_predictive_tv_small
lemma affineHistogramKernel_ordered_predictive_tv_small (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps) :
    let nu := Measure.pi fun _ : Fin (affineTuning n m d eps).Kstar => (latentPMF sigma).toMeasure
    let order := pairedHistogramReconstructionKernel (Obs d) (AuxObs d)
    Causalean.Stat.tvDist
      (priorPredictive nu (order ∘ₖ affineHistogramKernel n m d eps sigma false))
      (priorPredictive nu (order ∘ₖ affineHistogramKernel n m d eps sigma true)) < 1 / 64 := by
  intro nu order
  rw [kernel_comp_priorPredictive, kernel_comp_priorPredictive,
    affineHistogramKernel_predictive_eq, affineHistogramKernel_predictive_eq,
    Causalean.Stat.tvDist_symm]
  exact affineHistogramPredictive_ordered_tv_small n m d eps hn hd heps heps' sigma

end CausalSmith.Stat.AnnotationRarearmFrontier
