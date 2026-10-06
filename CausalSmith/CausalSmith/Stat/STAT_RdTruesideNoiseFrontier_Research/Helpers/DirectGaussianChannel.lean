module

public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.DirectWitness
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.TwoPoint
public import Causalean.Mathlib.Probability.Kernel.GraphMapProd

/-!
# Gaussian channel for the direct lower bound
-/

@[expose] public section

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology

namespace CausalSmith.Stat.RdTruesideNoiseFrontier

/-- Add independent Gaussian score noise while retaining the true-side arm
and observed outcome. Given [the displayed inputs and assumptions](hyp:sigma,z), [this definition specifies the stated object](goal). -/
@[no_expose]
def observedNoiseMechanism (sigma : ℝ) (z : Obs × ℝ) : Obs :=
  (z.1.1 + sigma * z.2, z.1.2)

/-- The common Gaussian channel from the error-free observation to an
observation at noise scale `sigma`. -/
@[no_expose]
noncomputable def observedNoiseKernel (sigma : ℝ) : Kernel Obs Obs :=
  Causalean.Mathlib.GraphMapProd.mechanismKernel
    (gaussianReal 0 1) (observedNoiseMechanism sigma)

/-- Given [the displayed inputs and assumptions](hyp:sigma), [this definition specifies the stated object](goal). -/
instance observedNoiseKernel_markov (sigma : ℝ) :
    IsMarkovKernel (observedNoiseKernel sigma) := by
  unfold observedNoiseKernel
  exact Causalean.Mathlib.GraphMapProd.instIsMarkovKernelMechanismKernel _ (by
    unfold observedNoiseMechanism
    fun_prop)

/-- Given [the displayed inputs and assumptions](hyp:mu,sigma), [the stated mathematical conclusion holds](goal). -/
lemma observedNoiseKernel_comp_eq_prod_map (mu : Measure Obs) [SFinite mu]
    (sigma : ℝ) :
    observedNoiseKernel sigma ∘ₘ mu =
      (mu.prod (gaussianReal 0 1)).map (observedNoiseMechanism sigma) := by
  have hm : Measurable (observedNoiseMechanism sigma) := by
    unfold observedNoiseMechanism
    fun_prop
  rw [← Measure.snd_compProd]
  unfold observedNoiseKernel
  rw [← Causalean.Mathlib.GraphMapProd.map_graph_prod_eq_compProd
    mu (gaussianReal 0 1) hm]
  rw [Measure.snd, Measure.map_map measurable_snd (measurable_fst.prodMk hm)]
  rfl

/-- Gaussian error independence makes every noisy observed law a common
Markov garbling of its error-free observed law. Given [the displayed inputs and assumptions](hyp:L,sigma,hgauss,hind), [the stated mathematical conclusion holds](goal). -/
lemma observedNoiseKernel_comp_Pobs_zero (L : LatentLaw) (sigma : ℝ)
    (hgauss : GaussianError L) (hind : ErrorIndependence L) :
    observedNoiseKernel sigma ∘ₘ Pobs L 0 = Pobs L sigma := by
  letI := L.prob
  letI : IsProbabilityMeasure (Pobs L 0) :=
    Measure.isProbabilityMeasure_map (obs_measurable 0).aemeasurable
  let schedule : Latent → ℝ × Bool × Bool :=
    fun omega => (score omega, omega.2.1, omega.2.2.1)
  let cleanObs : ℝ × Bool × Bool → Obs := fun z =>
    (z.1, decide (0 ≤ z.1), if decide (0 ≤ z.1) then z.2.2 else z.2.1)
  have hclean : cleanObs ∘ schedule = obs 0 := by
    funext omega
    by_cases hs : 0 ≤ omega.1 <;>
      simp [cleanObs, schedule, obs, proxy, side, outcome, score, hs]
  have hcleanMeas : Measurable cleanObs := by
    dsimp [cleanObs]
    have hs : MeasurableSet {z : ℝ × Bool × Bool | 0 ≤ z.1} :=
      measurableSet_le measurable_const measurable_fst
    have hd : Measurable (fun z : ℝ × Bool × Bool => decide (0 ≤ z.1)) := by
      change Measurable (fun z : ℝ × Bool × Bool =>
        if 0 ≤ z.1 then true else false)
      exact measurable_const.ite hs measurable_const
    have hs' : MeasurableSet {z : ℝ × Bool × Bool |
        decide (0 ≤ z.1) = true} := by simpa using hs
    exact measurable_fst.prodMk
      (hd.prodMk (measurable_snd.snd.ite hs' measurable_snd.fst))
  have herrorMeas : Measurable errorCoord := by
    unfold errorCoord
    fun_prop
  have hindClean : IndepFun (obs 0) errorCoord L.P := by
    have h := hind.symm.comp hcleanMeas measurable_id
    rw [hclean, Function.id_comp] at h
    exact h
  have hjoint : L.P.map (fun omega => (obs 0 omega, errorCoord omega)) =
      (Pobs L 0).prod (gaussianReal 0 1) := by
    have h := (indepFun_iff_map_prod_eq_prod_map_map
      (obs_measurable 0).aemeasurable herrorMeas.aemeasurable).mp hindClean
    unfold GaussianError at hgauss
    rw [hgauss] at h
    simpa [Pobs] using h
  have hmechanism : Measurable (observedNoiseMechanism sigma) := by
    unfold observedNoiseMechanism
    fun_prop
  have hpair : Measurable (fun omega : Latent => (obs 0 omega, errorCoord omega)) :=
    (obs_measurable 0).prodMk herrorMeas
  have hobs : observedNoiseMechanism sigma ∘
      (fun omega : Latent => (obs 0 omega, errorCoord omega)) = obs sigma := by
    funext omega
    simp [observedNoiseMechanism, obs, proxy, errorCoord]
  rw [observedNoiseKernel_comp_eq_prod_map]
  rw [← hjoint, Measure.map_map hmechanism hpair]
  exact congrArg (fun f => L.P.map f) hobs

/-- Coordinatewise Gaussian randomization of an error-free sample. Given [the displayed inputs and assumptions](hyp:n,sigma,z), [this definition specifies the stated object](goal). -/
@[no_expose]
def sampleObservedNoiseMechanism (n : ℕ) (sigma : ℝ)
    (z : (Fin n → Obs) × (Fin n → ℝ)) : Fin n → Obs :=
  fun i => observedNoiseMechanism sigma (z.1 i, z.2 i)

/-- Given the [sample size and noise scale](hyp:n,sigma), this definition specifies the [coordinatewise Gaussian observation kernel](goal). -/
@[no_expose]
noncomputable def sampleObservedNoiseKernel (n : ℕ) (sigma : ℝ) :
    Kernel (Fin n → Obs) (Fin n → Obs) :=
  Causalean.Mathlib.GraphMapProd.mechanismKernel
    (Measure.pi (fun _ : Fin n => gaussianReal 0 1))
    (sampleObservedNoiseMechanism n sigma)

/-- Given [the displayed inputs and assumptions](hyp:n,sigma), [this definition specifies the stated object](goal). -/
instance sampleObservedNoiseKernel_markov (n : ℕ) (sigma : ℝ) :
    IsMarkovKernel (sampleObservedNoiseKernel n sigma) := by
  unfold sampleObservedNoiseKernel
  exact Causalean.Mathlib.GraphMapProd.instIsMarkovKernelMechanismKernel _ (by
    unfold sampleObservedNoiseMechanism observedNoiseMechanism
    fun_prop)

/-- Given [the displayed inputs and assumptions](hyp:L,sigma,n,hgauss,hind), [the stated mathematical conclusion holds](goal). -/
lemma sampleObservedNoiseKernel_comp_sampleLaw (L : LatentLaw) (sigma : ℝ)
    (n : ℕ) (hgauss : GaussianError L) (hind : ErrorIndependence L) :
    sampleObservedNoiseKernel n sigma ∘ₘ sampleLaw L 0 n =
      sampleLaw L sigma n := by
  letI := L.prob
  let mu := Pobs L 0
  let nu := gaussianReal 0 1
  letI : IsProbabilityMeasure mu :=
    Measure.isProbabilityMeasure_map (obs_measurable 0).aemeasurable
  let e := MeasurableEquiv.arrowProdEquivProdArrow Obs ℝ (Fin n)
  have hmech : Measurable (sampleObservedNoiseMechanism n sigma) := by
    unfold sampleObservedNoiseMechanism observedNoiseMechanism
    fun_prop
  have hpair :
      ((Measure.pi (fun _ : Fin n => mu)).prod
        (Measure.pi (fun _ : Fin n => nu))).map e.symm =
        Measure.pi (fun _ : Fin n => mu.prod nu) := by
    exact (measurePreserving_arrowProdEquivProdArrow
      Obs ℝ (Fin n) (fun _ => mu) (fun _ => nu)).symm.map_eq
  rw [show sampleObservedNoiseKernel n sigma ∘ₘ sampleLaw L 0 n =
      ((sampleLaw L 0 n).prod (Measure.pi (fun _ : Fin n => nu))).map
        (sampleObservedNoiseMechanism n sigma) by
    have hsfinite : SFinite (sampleLaw L 0 n) := by
      unfold sampleLaw
      infer_instance
    letI : IsSFiniteKernel (sampleObservedNoiseKernel n sigma) := inferInstance
    rw [← Measure.snd_compProd]
    unfold sampleObservedNoiseKernel
    rw [← Causalean.Mathlib.GraphMapProd.map_graph_prod_eq_compProd
      (sampleLaw L 0 n) (Measure.pi (fun _ : Fin n => nu)) hmech]
    rw [Measure.snd, Measure.map_map measurable_snd (measurable_fst.prodMk hmech)]
    rfl]
  change ((Measure.pi (fun _ : Fin n => mu)).prod
      (Measure.pi (fun _ : Fin n => nu))).map
        (sampleObservedNoiseMechanism n sigma) = sampleLaw L sigma n
  calc
    _ = (((Measure.pi (fun _ : Fin n => mu)).prod
          (Measure.pi (fun _ : Fin n => nu))).map e.symm).map
          (fun z : Fin n → Obs × ℝ =>
            fun i => observedNoiseMechanism sigma (z i)) := by
      rw [Measure.map_map (by
        unfold observedNoiseMechanism
        fun_prop) e.symm.measurable]
      rfl
    _ = (Measure.pi (fun _ : Fin n => mu.prod nu)).map
          (fun z : Fin n → Obs × ℝ =>
            fun i => observedNoiseMechanism sigma (z i)) := by rw [hpair]
    _ = Measure.pi (fun _ : Fin n =>
          (mu.prod nu).map (observedNoiseMechanism sigma)) := by
      exact Measure.pi_map_pi (fun _ => (by
        unfold observedNoiseMechanism
        fun_prop : AEMeasurable (observedNoiseMechanism sigma) (mu.prod nu)))
    _ = sampleLaw L sigma n := by
      unfold sampleLaw
      congr 1
      funext i
      rw [← observedNoiseKernel_comp_eq_prod_map mu sigma,
        observedNoiseKernel_comp_Pobs_zero L sigma hgauss hind]

/-- Adding the same independent Gaussian noise coordinatewise cannot increase
sample total variation. Given [the displayed inputs and assumptions](hyp:beta,sigma,n,P,Q,hP,hQ), [the stated mathematical conclusion holds](goal). -/
lemma sampleLaw_tv_le_zero_of_model (beta sigma : ℝ) (n : ℕ)
    (P Q : LatentLaw) (hP : Model beta sigma P) (hQ : Model beta sigma Q) :
    tvDist (sampleLaw P sigma n) (sampleLaw Q sigma n) ≤
      tvDist (sampleLaw P 0 n) (sampleLaw Q 0 n) := by
  letI := P.prob
  letI := Q.prob
  letI : IsProbabilityMeasure (Pobs P 0) :=
    Measure.isProbabilityMeasure_map (obs_measurable 0).aemeasurable
  letI : IsProbabilityMeasure (Pobs Q 0) :=
    Measure.isProbabilityMeasure_map (obs_measurable 0).aemeasurable
  letI : IsProbabilityMeasure (sampleLaw P 0 n) := by
    unfold sampleLaw
    infer_instance
  letI : IsProbabilityMeasure (sampleLaw Q 0 n) := by
    unfold sampleLaw
    infer_instance
  rw [← sampleObservedNoiseKernel_comp_sampleLaw P sigma n hP.gaussian hP.independent,
    ← sampleObservedNoiseKernel_comp_sampleLaw Q sigma n hQ.gaussian hQ.independent]
  exact Causalean.Stat.tvDist_bind_le
    (sampleLaw P 0 n) (sampleLaw Q 0 n) (sampleObservedNoiseKernel n sigma)

end CausalSmith.Stat.RdTruesideNoiseFrontier
