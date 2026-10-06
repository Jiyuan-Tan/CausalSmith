module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.ProductTV

/-!
Identification of the independent rare-cell predictive law with the mixture of
conditional raw cell products over the construction's independent latent draws.
-/

@[expose] public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
open Causalean.Stat.Minimax.MomentMatchedMixture
open Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture

/-- Conditional independent raw count laws of the rare cells, before restoring
control-channel splits and ordering the records. -/
-- @node: affineRareCellProductKernel
noncomputable def affineRareCellProductKernel {L : Nat} {B eps : Real}
    (sigma : ConeDual L B eps) (k : Nat) (u w : Real) (hyp : Bool) :
    Kernel (Fin k → Latent L) (Fin k → MarkedPoissonObservation) :=
  Kernel.ofFunOfCountable fun lat =>
    Measure.pi fun i : Fin k => affineCellPoissonLaw sigma u w hyp (lat i)

/-- Every conditional rare-cell product is a probability law. -/
-- @node: affineRareCellProductKernel_isMarkovKernel
instance affineRareCellProductKernel_isMarkovKernel {L : Nat} {B eps : Real}
    (sigma : ConeDual L B eps) (k : Nat) (u w : Real) (hyp : Bool) :
    IsMarkovKernel (affineRareCellProductKernel sigma k u w hyp) where
  isProbabilityMeasure lat := by
    change IsProbabilityMeasure
      (Measure.pi fun i : Fin k => affineCellPoissonLaw sigma u w hyp (lat i))
    infer_instance

/-- [Under the stated inputs and conditions](hyp:L,sigma,k,hyp,B,eps,u,w), Mixing independent conditional raw cells over the actual latent product
prior gives exactly the product of the actual core/filler predictive measures.  This gives [the stated result](goal).-/
-- @node: affineRareCellProductKernel_predictive_eq
lemma affineRareCellProductKernel_predictive_eq {L : Nat} {B eps : Real}
    (sigma : ConeDual L B eps) (k : Nat) (u w : Real) (hyp : Bool) :
    priorPredictive
      (Measure.pi fun _ : Fin k => (latentPMF sigma).toMeasure)
      (affineRareCellProductKernel sigma k u w hyp) =
    Measure.pi fun _ : Fin k => affineCellPoissonPredictive sigma u w hyp := by
  classical
  apply Measure.ext_of_singleton
  intro o
  rw [priorPredictive_apply _ _ (measurableSet_singleton o), lintegral_fintype]
  change (∑ lat : Fin k → Latent L,
    (Measure.pi fun i : Fin k => affineCellPoissonLaw sigma u w hyp (lat i)) {o} *
      (Measure.pi fun _ : Fin k => (latentPMF sigma).toMeasure) {lat}) = _
  simp only [Measure.pi_singleton,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp only [affineCellPoissonPredictive, Measure.finsetSum_apply, Measure.smul_apply,
    smul_eq_mul]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro lat _
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact mul_comm _ _

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',sigma,n,m,d), The raw rare-cell mixture itself inherits the joint one-sixty-fourth TV
budget; the product identity eliminates any identification hypothesis.  This gives [the stated result](goal).-/
-- @node: affineRareCellProductKernel_predictive_tv_small
lemma affineRareCellProductKernel_predictive_tv_small (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps) :
    let t := affineTuning n m d eps
    let nu := Measure.pi fun _ : Fin t.Kstar => (latentPMF sigma).toMeasure
    Causalean.Stat.tvDist
      (priorPredictive nu (affineRareCellProductKernel sigma t.Kstar t.u t.w true))
      (priorPredictive nu (affineRareCellProductKernel sigma t.Kstar t.u t.w false)) <
      1 / 64 := by
  intro t nu
  rw [affineRareCellProductKernel_predictive_eq, affineRareCellProductKernel_predictive_eq]
  exact affineCellPoissonPredictive_product_tv_small n m d eps hn hd heps heps' sigma

/-- Attach a common independent reservoir to the conditional rare-cell counts. -/
-- @node: affineRareCellReservoirKernel
noncomputable def affineRareCellReservoirKernel {R : Type*} [MeasurableSpace R]
    (rho : Measure R) {L : Nat} {B eps : Real}
    (sigma : ConeDual L B eps) (k : Nat) (u w : Real) (hyp : Bool) :
    Kernel (Fin k → Latent L) ((Fin k → MarkedPoissonObservation) × R) :=
  (affineRareCellProductKernel sigma k u w hyp).prod
    (Kernel.const (Fin k → Latent L) rho)

/-- A probability reservoir preserves the conditional probability law. -/
-- @node: affineRareCellReservoirKernel_isMarkovKernel
instance affineRareCellReservoirKernel_isMarkovKernel {R : Type*} [MeasurableSpace R]
    (rho : Measure R) [IsProbabilityMeasure rho] {L : Nat} {B eps : Real}
    (sigma : ConeDual L B eps) (k : Nat) (u w : Real) (hyp : Bool) :
    IsMarkovKernel (affineRareCellReservoirKernel rho sigma k u w hyp) := by
  unfold affineRareCellReservoirKernel
  infer_instance

/-- [Under the stated inputs and conditions](hyp:R,rho,L,sigma,k,hyp,B,eps,u,w), The common reservoir factors out of the actual finite latent mixture.  This gives [the stated result](goal).-/
-- @node: affineRareCellReservoirKernel_predictive_eq
lemma affineRareCellReservoirKernel_predictive_eq {R : Type*} [MeasurableSpace R]
    (rho : Measure R) [IsProbabilityMeasure rho] {L : Nat} {B eps : Real}
    (sigma : ConeDual L B eps) (k : Nat) (u w : Real) (hyp : Bool) :
    priorPredictive
      (Measure.pi fun _ : Fin k => (latentPMF sigma).toMeasure)
      (affineRareCellReservoirKernel rho sigma k u w hyp) =
    (Measure.pi fun _ : Fin k => affineCellPoissonPredictive sigma u w hyp).prod rho := by
  refine (Measure.prod_eq ?_).symm
  intro s r hs hr
  rw [priorPredictive_apply _ _ (hs.prod hr)]
  simp only [affineRareCellReservoirKernel, Kernel.prod_apply_prod, Kernel.const_apply]
  rw [lintegral_mul_const _ ((affineRareCellProductKernel sigma k u w hyp).measurable_coe hs),
    ← priorPredictive_apply _ _ hs, affineRareCellProductKernel_predictive_eq]

/-- [Under the stated inputs and conditions](hyp:rho,eps,hn,hd,heps,heps',sigma,reconstruct,R,X,n,m,d), A common reconstruction channel, including control splits, ordering and a
common random seed, preserves the TV budget of the mixed raw cells and reservoir.  This gives [the stated result](goal).-/
-- @node: affineRareCellReservoirKernel_reconstruction_tv_small
lemma affineRareCellReservoirKernel_reconstruction_tv_small
    {R X : Type*} [MeasurableSpace R] [MeasurableSpace X]
    (rho : Measure R) [IsProbabilityMeasure rho]
    (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps)
    (reconstruct : Kernel
      ((Fin (affineTuning n m d eps).Kstar → MarkedPoissonObservation) × R) X)
    [IsMarkovKernel reconstruct] :
    let t := affineTuning n m d eps
    let nu := Measure.pi fun _ : Fin t.Kstar => (latentPMF sigma).toMeasure
    Causalean.Stat.tvDist
      (priorPredictive nu
        (reconstruct ∘ₖ affineRareCellReservoirKernel rho sigma t.Kstar t.u t.w true))
      (priorPredictive nu
        (reconstruct ∘ₖ affineRareCellReservoirKernel rho sigma t.Kstar t.u t.w false)) <
      1 / 64 := by
  intro t nu
  rw [kernel_comp_priorPredictive, kernel_comp_priorPredictive,
    affineRareCellReservoirKernel_predictive_eq,
    affineRareCellReservoirKernel_predictive_eq]
  exact (Causalean.Stat.tvDist_bind_le _ _ reconstruct).trans_lt
    (affineCellPoissonPredictive_reservoir_tv_small rho n m d eps hn hd heps heps' sigma)

end CausalSmith.Stat.AnnotationRarearmFrontier
