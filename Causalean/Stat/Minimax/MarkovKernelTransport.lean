/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Mathlib.MeasureTheory.IntegralBind
import Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.Basic
import Causalean.Mathlib.Probability.Kernel.GraphMapProd


import Causalean.Stat.Minimax.MinimaxRisk
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.ParallelComp
import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# Squared-risk transport through Markov kernels

This module packages the Blackwell comparison for squared loss: randomizing an experiment
through a Markov kernel cannot improve the best attainable squared-error risk. It constructs
the Rao--Blackwell pullback of a bounded estimator, proves its risk comparison under an affine
change of target, and exports the resulting minimax-hardness transport for both one observation
and finite independent samples, including the empty sample.

## Main results

* `forall_estimator_exists_sqRisk_ge_of_kernel_affine_transport` transfers a quantified
  squared-risk lower bound through a randomized experiment and an affine target change.
* `finProductKernel_comp_pi` identifies the image of an independent product experiment under
  the coordinatewise product kernel.
* `forall_estimator_exists_sqRisk_ge_of_kernel_affine_transport_pi` gives the finite-product
  form of the randomized transport theorem.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace Causalean.Stat

universe uX uY uI

variable {X : Type uX} {Y : Type uY} {Iota : Type uI}
  [MeasurableSpace X] [MeasurableSpace Y]

/-! ## Kernel means and affine pullbacks -/

/-- For [an arbitrary domain](hyp:A) and [a real-valued function on that domain](hyp:f), the [uniform boundedness
property](goal) holds exactly when there exists [a nonnegative real constant](step:1) that
bounds the function's absolute value at every input. -/
def UniformlyBounded {A : Type*} (f : A → ℝ) : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |f x| ≤ M

/-- For [an input measurable space](hyp:X), [an output measurable space](hyp:Y), and [a Markov
kernel from the input space to the output space](hyp:K)
and [a real-valued function on the output space](hyp:T), the [kernel mean](goal) assigns to each
input the expectation of that function under the output distribution selected by the kernel. -/
noncomputable def kernelMean (K : Kernel X Y) (T : Y → ℝ) : X → ℝ :=
  fun x => ∫ y, T y ∂K x

/-- [Measurability of a real-valued estimator](hyp:hT) ensures that [its expectation under each
kernel output distribution varies measurably with the kernel input](goal). -/
@[fun_prop]
theorem measurable_kernelMean (K : Kernel X Y) {T : Y → ℝ} (hT : Measurable T) :
    Measurable (kernelMean K T) := by
  exact hT.stronglyMeasurable.integral_kernel.measurable

/-- If [a proposed bound is nonnegative](hyp:hM) and [bounds the estimator in absolute value at
every output](hyp:hT), then [the kernel mean obeys the same absolute bound at every input](goal)
when each kernel output is a probability distribution. -/
theorem abs_kernelMean_le (K : Kernel X Y) [IsMarkovKernel K]
    {T : Y → ℝ} {M : ℝ} (hM : 0 ≤ M) (hT : ∀ y, |T y| ≤ M) :
    ∀ x, |kernelMean K T x| ≤ M := by
  intro x
  haveI : IsProbabilityMeasure (K x) := inferInstance
  simpa [kernelMean, Real.norm_eq_abs] using
    (norm_integral_le_of_norm_le_const
      (μ := K x) (f := T) (C := M) (Filter.Eventually.of_forall hT))

/-- [Uniform boundedness of an estimator](hyp:hT) implies that [averaging it against a Markov
kernel is uniformly bounded by the same witness](goal). -/
theorem uniformlyBounded_kernelMean (K : Kernel X Y) [IsMarkovKernel K]
    {T : Y → ℝ} (hT : UniformlyBounded T) :
    UniformlyBounded (kernelMean K T) := by
  obtain ⟨M, hM, hT⟩ := hT
  exact ⟨M, hM, abs_kernelMean_le K hM hT⟩

/-- For [an input measurable space](hyp:X), [an output measurable space](hyp:Y), and [a Markov
kernel from the input space to the output space](hyp:K),
[a real slope](hyp:a), [a real offset](hyp:b), and [a real-valued estimator on the output
space](hyp:targetEst), the [affine kernel pullback](goal) assigns to each input the kernel mean
of the estimator, minus the offset, divided by the slope. -/
noncomputable def kernelAffinePullback (K : Kernel X Y) (a b : ℝ)
    (targetEst : Y → ℝ) : X → ℝ :=
  fun x => (kernelMean K targetEst x - b) / a

/-- [Measurability of a target estimator](hyp:htarget) ensures that [its affine kernel
pullback is measurable on the source experiment](goal). -/
@[fun_prop]
theorem measurable_kernelAffinePullback (K : Kernel X Y) {a b : ℝ}
    {targetEst : Y → ℝ} (htarget : Measurable targetEst) :
    Measurable (kernelAffinePullback K a b targetEst) := by
  exact ((measurable_kernelMean K htarget).sub measurable_const).div measurable_const

/-- If [the affine slope is nonzero](hyp:ha) and [the target estimator is uniformly
bounded](hyp:htarget), then [the affine kernel pullback is uniformly bounded on the source
experiment](goal). -/
theorem uniformlyBounded_kernelAffinePullback (K : Kernel X Y) [IsMarkovKernel K]
    {a b : ℝ} (ha : a ≠ 0) {targetEst : Y → ℝ}
    (htarget : UniformlyBounded targetEst) :
    UniformlyBounded (kernelAffinePullback K a b targetEst) := by
  obtain ⟨M, hM, htarget⟩ := htarget
  refine ⟨(M + |b|) / |a|, div_nonneg (add_nonneg hM (abs_nonneg b)) (abs_nonneg a), ?_⟩
  intro x
  rw [kernelAffinePullback, abs_div]
  exact div_le_div_of_nonneg_right
    ((abs_sub _ _).trans (add_le_add (abs_kernelMean_le K hM htarget x) le_rfl))
    (abs_nonneg a)

/-! ## Tower identity and squared-risk comparison -/

/-- If [the target estimator is measurable](hyp:hTmeas) and [uniformly bounded](hyp:hTbound),
then [its expectation after taking the kernel mean under a source probability law equals its
expectation under the garbled law](goal). -/
theorem integral_kernelMean_eq_integral_comp (P : Measure X) [IsProbabilityMeasure P]
    (K : Kernel X Y) [IsMarkovKernel K] {T : Y → ℝ}
    (hTmeas : Measurable T) (hTbound : UniformlyBounded T) :
    ∫ x, kernelMean K T x ∂P = ∫ y, T y ∂(K ∘ₘ P) := by
  obtain ⟨M, _hM, hT⟩ := hTbound
  have hTint : Integrable T (K ∘ₘ P) :=
    (integrable_const M).mono' hTmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hT y)
  simpa [kernelMean] using
    (Causalean.Mathlib.MeasureTheory.integral_bind K.measurable hTint).symm

/-- If [the target estimator is measurable](hyp:hTmeas) and [uniformly bounded](hyp:hTbound),
then [the squared error of its kernel mean is no greater than the kernel average of its squared
error at each source observation](goal). -/
theorem sqLoss_kernelMean_le (K : Kernel X Y) [IsMarkovKernel K]
    {T : Y → ℝ} (hTmeas : Measurable T) (hTbound : UniformlyBounded T)
    (c : ℝ) (x : X) :
    (kernelMean K T x - c) ^ 2 ≤ ∫ y, (T y - c) ^ 2 ∂K x := by
  haveI : IsProbabilityMeasure (K x) := inferInstance
  obtain ⟨M, hM, hT⟩ := hTbound
  have hTint : Integrable T (K x) :=
    (integrable_const M).mono' hTmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hT y)
  have hdiffint : Integrable (fun y => T y - c) (K x) :=
    hTint.sub (integrable_const c)
  have hlossint : Integrable (fun y => (T y - c) ^ 2) (K x) := by
    refine (integrable_const ((M + |c|) ^ 2)).mono'
      ((hTmeas.sub measurable_const).pow_const 2).aestronglyMeasurable ?_
    filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq_le_sq,
      abs_of_nonneg (add_nonneg hM (abs_nonneg c))]
    exact (abs_sub _ _).trans (add_le_add (hT y) le_rfl)
  have hjensen := ((show Even 2 by norm_num).convexOn_pow :
      ConvexOn ℝ Set.univ (fun z : ℝ => z ^ 2)).map_integral_le
        (continuousOn_pow 2) isClosed_univ
        (Filter.Eventually.of_forall fun _ => Set.mem_univ _)
        hdiffint hlossint
  simpa [kernelMean, integral_sub hTint (integrable_const c), integral_const] using hjensen

/-- If [the target estimator is measurable](hyp:hTmeas) and [uniformly bounded](hyp:hTbound),
then [Rao--Blackwellizing it through a Markov kernel cannot increase squared risk](goal): the
source-law risk of the kernel mean is at most the target-law risk after garbling. -/
theorem sqRisk_kernelMean_le_comp (P : Measure X) [IsProbabilityMeasure P]
    (K : Kernel X Y) [IsMarkovKernel K] {T : Y → ℝ}
    (hTmeas : Measurable T) (hTbound : UniformlyBounded T) (c : ℝ) :
    sqRisk P (kernelMean K T) c ≤ sqRisk (K ∘ₘ P) T c := by
  obtain ⟨M, hM, hT⟩ := hTbound
  have hlossMeas : Measurable (fun y => (T y - c) ^ 2) :=
    (hTmeas.sub measurable_const).pow_const 2
  have hlossBound : UniformlyBounded (fun y => (T y - c) ^ 2) := by
    refine ⟨(M + |c|) ^ 2, sq_nonneg _, ?_⟩
    intro y
    rw [abs_of_nonneg (sq_nonneg _), sq_le_sq,
      abs_of_nonneg (add_nonneg hM (abs_nonneg c))]
    exact (abs_sub _ _).trans (add_le_add (hT y) le_rfl)
  obtain ⟨N, _hN, hmeanLoss⟩ := uniformlyBounded_kernelMean K hlossBound
  have hmeanLossInt : Integrable (kernelMean K fun y => (T y - c) ^ 2) P :=
    (integrable_const N).mono' (measurable_kernelMean K hlossMeas).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs] using hmeanLoss x)
  unfold sqRisk
  calc
    (∫ x, (kernelMean K T x - c) ^ 2 ∂P) ≤
        ∫ x, kernelMean K (fun y => (T y - c) ^ 2) x ∂P :=
      integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun _ => sq_nonneg _)
        hmeanLossInt
        (Filter.Eventually.of_forall fun x =>
          sqLoss_kernelMean_le K hTmeas ⟨M, hM, hT⟩ c x)
    _ = ∫ y, (T y - c) ^ 2 ∂(K ∘ₘ P) :=
      integral_kernelMean_eq_integral_comp P K hlossMeas hlossBound

/-- If [the affine slope is nonzero](hyp:ha), [the target estimator is
measurable](hyp:htargetMeas), and [the target estimator is uniformly
bounded](hyp:htargetBound), then [the source risk of the affine kernel pullback, multiplied by
the squared slope, is at most the target risk under the garbled law](goal). -/
theorem sqRisk_kernelAffinePullback_le_comp (P : Measure X) [IsProbabilityMeasure P]
    (K : Kernel X Y) [IsMarkovKernel K] {a b theta : ℝ} (ha : a ≠ 0)
    {targetEst : Y → ℝ} (htargetMeas : Measurable targetEst)
    (htargetBound : UniformlyBounded targetEst) :
    a ^ 2 * sqRisk P (kernelAffinePullback K a b targetEst) theta ≤
      sqRisk (K ∘ₘ P) targetEst (a * theta + b) := by
  have hpull : ∀ x,
      a ^ 2 * (kernelAffinePullback K a b targetEst x - theta) ^ 2 =
        (kernelMean K targetEst x - (a * theta + b)) ^ 2 := by
    intro x
    unfold kernelAffinePullback
    field_simp
    ring
  calc
    a ^ 2 * sqRisk P (kernelAffinePullback K a b targetEst) theta =
        ∫ x, a ^ 2 * (kernelAffinePullback K a b targetEst x - theta) ^ 2 ∂P := by
      exact (integral_const_mul (a ^ 2) _).symm
    _ = sqRisk P (kernelMean K targetEst) (a * theta + b) := by
      unfold sqRisk
      exact integral_congr_ae (Filter.Eventually.of_forall hpull)
    _ ≤ sqRisk (K ∘ₘ P) targetEst (a * theta + b) :=
      sqRisk_kernelMean_le_comp P K htargetMeas htargetBound _

/-- Suppose [the affine slope is nonzero](hyp:ha), [each target law is obtained by passing its
source law through the common Markov kernel](hyp:hQ), and [every measurable uniformly bounded
source estimator incurs squared risk at least a fixed level for some parameter
index](hyp:hsource). Then [every measurable uniformly bounded target estimator incurs at least
the source level multiplied by the squared slope for some parameter index](goal), with the
target parameter transformed by the same affine map. -/
theorem forall_estimator_exists_sqRisk_ge_of_kernel_affine_transport
    (P : Iota → Measure X) (Q : Iota → Measure Y)
    [∀ j, IsProbabilityMeasure (P j)]
    (K : Kernel X Y) [IsMarkovKernel K]
    (theta : Iota → ℝ) (a b L : ℝ) (ha : a ≠ 0)
    (hQ : ∀ j, Q j = K ∘ₘ P j)
    (hsource : ∀ sourceEst : X → ℝ, Measurable sourceEst →
      UniformlyBounded sourceEst → ∃ j, L ≤ sqRisk (P j) sourceEst (theta j)) :
    ∀ targetEst : Y → ℝ, Measurable targetEst → UniformlyBounded targetEst →
      ∃ j, a ^ 2 * L ≤ sqRisk (Q j) targetEst (a * theta j + b) := by
  intro targetEst htargetMeas htargetBound
  obtain ⟨j, hj⟩ := hsource (kernelAffinePullback K a b targetEst)
    (measurable_kernelAffinePullback K htargetMeas)
    (uniformlyBounded_kernelAffinePullback K ha htargetBound)
  refine ⟨j, ?_⟩
  calc
    a ^ 2 * L ≤ a ^ 2 * sqRisk (P j)
        (kernelAffinePullback K a b targetEst) (theta j) :=
      mul_le_mul_of_nonneg_left hj (sq_nonneg a)
    _ ≤ sqRisk (K ∘ₘ P j) targetEst (a * theta j + b) :=
      sqRisk_kernelAffinePullback_le_comp (P j) K ha htargetMeas htargetBound
    _ = sqRisk (Q j) targetEst (a * theta j + b) := by
      rw [hQ j]

/-! ## Independent finite products -/

/-- For [an input measurable space](hyp:X), [an output measurable space](hyp:Y), [a nonnegative
integer number of coordinates](hyp:n), and [a Markov kernel from the input space to the output
space](hyp:K), the [finite product kernel](goal) maps
an input vector to [the unique point-mass kernel at zero coordinates](step:1), and otherwise to
independent kernel outputs coordinate by coordinate. -/
noncomputable def finProductKernel (n : ℕ) (K : Kernel X Y) :
    Kernel (Fin n → X) (Fin n → Y) :=
  match n with
  | 0 => Kernel.deterministic (fun _ => fun i => Fin.elim0 i) measurable_const
  | n + 1 =>
      let eX := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0
      let eY := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Y) 0
      ((K ∥ₖ finProductKernel n K).comap eX eX.measurable).map eY.symm

/-- [Each fibre of the finite product kernel equals the independent product of its coordinate
output laws](goal), including the unique empty product fibre. -/
theorem finProductKernel_apply (n : ℕ) (K : Kernel X Y) [IsMarkovKernel K]
    (x : Fin n → X) :
    finProductKernel n K x = Measure.pi (fun i : Fin n => K (x i)) := by
  induction n with
  | zero =>
      rw [finProductKernel, Kernel.deterministic_apply]
      exact (Measure.pi_of_empty _ _).symm
  | succ n ih =>
      let _ : IsMarkovKernel (finProductKernel n K) :=
        ⟨fun z => ⟨by rw [ih z]; exact measure_univ⟩⟩
      let eX := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0
      let eY := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Y) 0
      rw [finProductKernel, Kernel.map_apply _ eY.symm.measurable,
        Kernel.comap_apply, Kernel.parallelComp_apply, ih]
      exact (MeasureTheory.measurePreserving_piFinSuccAbove
        (fun i : Fin (n + 1) => K (x i)) 0).symm.map_eq

/-- For every [nonnegative integer number of coordinates](hyp:n) and every [Markov kernel
between measurable input and output spaces](hyp:K), the [independent product kernel over that
many coordinates is a Markov kernel](goal), including when there are zero coordinates. -/
instance instIsMarkovKernelFinProductKernel (n : ℕ) (K : Kernel X Y)
    [IsMarkovKernel K] : IsMarkovKernel (finProductKernel n K) := by
  refine ⟨fun x => ?_⟩
  rw [finProductKernel_apply]
  infer_instance

/-- [Passing an independent finite product law through the coordinatewise product kernel
produces the product of the one-coordinate garbled law](goal), including when there are no
coordinates. -/
theorem finProductKernel_comp_pi (n : ℕ) (P : Measure X) [IsProbabilityMeasure P]
    (K : Kernel X Y) [IsMarkovKernel K] :
    finProductKernel n K ∘ₘ Measure.pi (fun _ : Fin n => P) =
      Measure.pi (fun _ : Fin n => K ∘ₘ P) := by
  induction n with
  | zero =>
      rw [finProductKernel, Measure.deterministic_comp_eq_map,
        Measure.pi_of_empty, Measure.map_dirac]
      exact (Measure.pi_of_empty _ _).symm
  | succ n ih =>
      let eX := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0
      let eY := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Y) 0
      have hsource :
          (Measure.pi (fun _ : Fin (n + 1) => P)).map eX =
            P.prod (Measure.pi (fun _ : Fin n => P)) :=
        (MeasureTheory.measurePreserving_piFinSuccAbove
          (fun _ : Fin (n + 1) => P) 0).map_eq
      have hparallel :
          (K ∥ₖ finProductKernel n K) ∘ₘ
              (P.prod (Measure.pi (fun _ : Fin n => P))) =
            (K ∘ₘ P).prod
              (finProductKernel n K ∘ₘ Measure.pi (fun _ : Fin n => P)) := by
        calc
          (K ∥ₖ finProductKernel n K) ∘ₘ
                (P.prod (Measure.pi (fun _ : Fin n => P))) =
              (K ∥ₖ Kernel.id) ∘ₘ
                ((Kernel.id ∥ₖ finProductKernel n K) ∘ₘ
                  (P.prod (Measure.pi (fun _ : Fin n => P)))) := by
            rw [Measure.comp_assoc, Kernel.parallelComp_comp_parallelComp,
              Kernel.comp_id, Kernel.id_comp]
          _ = (K ∥ₖ Kernel.id) ∘ₘ
                (P.prod (finProductKernel n K ∘ₘ
                  Measure.pi (fun _ : Fin n => P))) := by
            rw [← Measure.prod_comp_right]
          _ = (K ∘ₘ P).prod
                (finProductKernel n K ∘ₘ Measure.pi (fun _ : Fin n => P)) := by
            rw [Measure.prod_comp_left]
      calc
        finProductKernel (n + 1) K ∘ₘ
              Measure.pi (fun _ : Fin (n + 1) => P) =
            (((K ∥ₖ finProductKernel n K) ∘ₘ
              (Measure.pi (fun _ : Fin (n + 1) => P)).map eX).map eY.symm) := by
          rw [finProductKernel, ← Kernel.deterministic_comp_eq_map eY.symm.measurable,
            ← Measure.comp_assoc, ← Kernel.comp_deterministic_eq_comap,
            ← Measure.comp_assoc, Measure.deterministic_comp_eq_map,
            Measure.deterministic_comp_eq_map]
        _ = ((K ∘ₘ P).prod (Measure.pi (fun _ : Fin n => K ∘ₘ P))).map eY.symm := by
          rw [hsource, hparallel, ih]
        _ = Measure.pi (fun _ : Fin (n + 1) => K ∘ₘ P) :=
          (MeasureTheory.measurePreserving_piFinSuccAbove
            (fun _ : Fin (n + 1) => K ∘ₘ P) 0).symm.map_eq

/-- If [the affine slope is nonzero](hyp:ha), [a finite-sample target estimator is
measurable](hyp:htargetMeas), and [that estimator is uniformly bounded](hyp:htargetBound), then
[the source-product risk of its affine product-kernel pullback, multiplied by the squared
slope, is at most its target-product risk](goal). -/
theorem sqRisk_finProductKernel_affinePullback_le (n : ℕ)
    (P : Measure X) [IsProbabilityMeasure P]
    (K : Kernel X Y) [IsMarkovKernel K] {a b theta : ℝ} (ha : a ≠ 0)
    {targetEst : (Fin n → Y) → ℝ} (htargetMeas : Measurable targetEst)
    (htargetBound : UniformlyBounded targetEst) :
    a ^ 2 * sqRisk (Measure.pi (fun _ : Fin n => P))
        (kernelAffinePullback (finProductKernel n K) a b targetEst) theta ≤
      sqRisk (Measure.pi (fun _ : Fin n => K ∘ₘ P))
        targetEst (a * theta + b) := by
  calc
    a ^ 2 * sqRisk (Measure.pi (fun _ : Fin n => P))
        (kernelAffinePullback (finProductKernel n K) a b targetEst) theta ≤
      sqRisk (finProductKernel n K ∘ₘ Measure.pi (fun _ : Fin n => P))
        targetEst (a * theta + b) :=
      sqRisk_kernelAffinePullback_le_comp
        (Measure.pi (fun _ : Fin n => P)) (finProductKernel n K)
        ha htargetMeas htargetBound
    _ = sqRisk (Measure.pi (fun _ : Fin n => K ∘ₘ P))
        targetEst (a * theta + b) := by
      rw [finProductKernel_comp_pi]

/-- Suppose [the affine slope is nonzero](hyp:ha), [each one-coordinate target law is obtained
by applying the common Markov kernel to its source law](hyp:hQ), and [every measurable uniformly
bounded estimator on the finite source product incurs squared risk at least a fixed level for
some parameter index](hyp:hsource). Then [every measurable uniformly bounded estimator on the
target product incurs at least the source level multiplied by the squared slope for some
parameter index](goal), including when the sample has no coordinates. -/
theorem forall_estimator_exists_sqRisk_ge_of_kernel_affine_transport_pi
    (n : ℕ) (P : Iota → Measure X) (Q : Iota → Measure Y)
    [∀ j, IsProbabilityMeasure (P j)]
    (K : Kernel X Y) [IsMarkovKernel K]
    (theta : Iota → ℝ) (a b L : ℝ) (ha : a ≠ 0)
    (hQ : ∀ j, Q j = K ∘ₘ P j)
    (hsource : ∀ sourceEst : (Fin n → X) → ℝ, Measurable sourceEst →
      UniformlyBounded sourceEst →
      ∃ j, L ≤ sqRisk (Measure.pi (fun _ : Fin n => P j)) sourceEst (theta j)) :
    ∀ targetEst : (Fin n → Y) → ℝ, Measurable targetEst →
      UniformlyBounded targetEst →
      ∃ j, a ^ 2 * L ≤ sqRisk (Measure.pi (fun _ : Fin n => Q j))
        targetEst (a * theta j + b) := by
  apply forall_estimator_exists_sqRisk_ge_of_kernel_affine_transport
    (P := fun j => Measure.pi (fun _ : Fin n => P j))
    (Q := fun j => Measure.pi (fun _ : Fin n => Q j))
    (K := finProductKernel n K) theta a b L ha
  · intro j
    rw [finProductKernel_comp_pi, hQ j]
  · exact hsource

end Causalean.Stat

/-! ## Capped-Poisson Rao--Blackwell risk transfer -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace Causalean.Stat

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Mathlib.GraphMapProd
open Causalean.Stat

variable {X : Type*} [MeasurableSpace X]

/-- Given [a statistic on finite samples](hyp:T), [an overflow value](hyp:zOver),
[a fixed array](hyp:x), and [an auxiliary count](hyp:m), the [randomized capped
statistic](goal) evaluates `T` on the requested prefix off overflow and equals
the specified value on overflow. -/
def cappedStatistic {n : ℕ} (T : FiniteSample X → ℝ) (zOver : ℝ)
    (x : Fin n → X) (m : ℕ) : ℝ :=
  if h : m ≤ n then T (prefixOfLE x m h) else zOver

/-- If [the finite-sample statistic is measurable](hyp:hT), then [the capped
statistic is jointly measurable in the fixed array and auxiliary count](goal). -/
@[fun_prop]
theorem measurable_cappedStatistic {n : ℕ} {T : FiniteSample X → ℝ}
    (hT : Measurable T) (zOver : ℝ) :
    Measurable (fun z : (Fin n → X) × ℕ ↦
      cappedStatistic T zOver z.1 z.2) := by
  apply measurable_from_prod_countable_left
  intro m
  unfold cappedStatistic
  change Measurable (fun x : Fin n → X ↦
    if h : m ≤ n then T (prefixOfLE x m h) else zOver)
  split
  · exact hT.comp (measurable_prefixOfLE (X := X) ‹m ≤ n›)
  · exact measurable_const

/-- Given [a Poisson mean](hyp:lambda), the [auxiliary-count Markov kernel](goal)
sends each fixed array to that same array paired with an independent Poisson
count. -/
noncomputable def auxPoissonCountKernel {n : ℕ} (lambda : ℝ≥0) :
    Kernel (Fin n → X) ((Fin n → X) × ℕ) :=
  mechanismKernel (poissonMeasure lambda)
    (fun z : (Fin n → X) × ℕ ↦ z)

/-- The [auxiliary-count kernel](hyp:lambda) is [a Markov kernel](goal). -/
instance auxPoissonCountKernel.isMarkovKernel {n : ℕ} (lambda : ℝ≥0) :
    IsMarkovKernel (auxPoissonCountKernel (X := X) (n := n) lambda) := by
  unfold auxPoissonCountKernel
  exact instIsMarkovKernelMechanismKernel _ measurable_id

/-- For [an observation probability law](hyp:P), [a Poisson mean](hyp:lambda),
and [a fixed sample size](hyp:n),
[mixing the auxiliary-count kernel over the fixed iid sample law gives exactly
the product of that iid law and the Poisson count law](goal). -/
theorem auxPoissonCountKernel_comp_pi
    (P : Measure X) [IsProbabilityMeasure P] (lambda : ℝ≥0) (n : ℕ) :
    auxPoissonCountKernel (X := X) (n := n) lambda ∘ₘ
        Measure.pi (fun _ : Fin n ↦ P) =
      (Measure.pi (fun _ : Fin n ↦ P)).prod (poissonMeasure lambda) := by
  -- Use `map_graph_prod_eq_compProd` with the identity mechanism, then take
  -- the second marginal (`Measure.snd_compProd`).
  have hgraph :
      Measure.map
          (fun p : (Fin n → X) × ℕ => (p.1, p))
          ((Measure.pi (fun _ : Fin n ↦ P)).prod (poissonMeasure lambda)) =
        (Measure.pi (fun _ : Fin n ↦ P)).compProd
          (auxPoissonCountKernel lambda) := by
    simpa [auxPoissonCountKernel] using
      (map_graph_prod_eq_compProd
        (Measure.pi (fun _ : Fin n ↦ P)) (poissonMeasure lambda)
          (show Measurable (fun z : (Fin n → X) × ℕ ↦ z) from measurable_id))
  have hsnd := congrArg (Measure.map Prod.snd) hgraph
  rw [Measure.map_map measurable_snd
      (show Measurable (fun p : (Fin n → X) × ℕ => (p.1, p)) from
        measurable_fst.prodMk measurable_id)] at hsnd
  change _ = ((Measure.pi (fun _ : Fin n ↦ P)) ⊗ₘ
    auxPoissonCountKernel lambda).snd at hsnd
  rw [Measure.snd_compProd] at hsnd
  simpa [Function.comp_def] using hsnd.symm

/-- Given [a Poisson mean](hyp:lambda), [a statistic](hyp:T), and
[an overflow value](hyp:zOver), the [fixed-sample Rao--Blackwell statistic](goal)
is the mean of the capped statistic under the auxiliary-count kernel. -/
noncomputable def raoBlackwellStatistic {n : ℕ} (lambda : ℝ≥0)
    (T : FiniteSample X → ℝ) (zOver : ℝ) :
    (Fin n → X) → ℝ :=
  kernelMean (auxPoissonCountKernel lambda)
    (fun z ↦ cappedStatistic T zOver z.1 z.2)

/-- Given [a Poisson mean](hyp:lambda), [a finite-sample statistic](hyp:T),
[its measurability](hyp:hT), [an overflow value](hyp:zOver), and [a fixed
array](hyp:x), [the Rao--Blackwell statistic equals the Poisson integral of the
capped prefix statistic](goal). -/
theorem raoBlackwellStatistic_eq_integral {n : ℕ} (lambda : ℝ≥0)
    (T : FiniteSample X → ℝ) (hT : Measurable T) (zOver : ℝ)
    (x : Fin n → X) :
    raoBlackwellStatistic lambda T zOver x =
      ∫ m : ℕ, cappedStatistic T zOver x m ∂poissonMeasure lambda := by
  -- Unfold the kernel mean, rewrite with `mechanismKernel_apply`, and use
  -- `integral_map` with `measurable_cappedStatistic hT zOver`.
  unfold raoBlackwellStatistic kernelMean auxPoissonCountKernel
  rw [mechanismKernel_apply _
    (show Measurable (fun z : (Fin n → X) × ℕ ↦ z) from measurable_id) x]
  exact integral_map measurable_prodMk_left.aemeasurable
    (measurable_cappedStatistic hT zOver).aestronglyMeasurable

/-! ## Restricted-risk bridge lemmas

These three statements isolate the measure-theoretic pieces of the headline
transfer theorem: transport on the nonoverflow restriction, evaluation on the
overflow restriction, and monotonicity when the count restriction is removed.
-/

/-- For [an observation probability law](hyp:P), [a Poisson mean](hyp:lambda),
[a fixed sample size](hyp:n), [a measurable finite-sample statistic](hyp:hT),
[an overflow value](hyp:zOver), and [a target](hyp:theta), [the squared risk of
the capped statistic on the nonoverflow restriction equals the squared risk of
the original statistic under the correspondingly restricted finite-Poisson
law](goal). -/
theorem sqRisk_cappedStatistic_restrict_nonoverflow_eq
    (P : Measure X) [IsProbabilityMeasure P] (lambda : ℝ≥0) (n : ℕ)
    {T : FiniteSample X → ℝ} (hT : Measurable T) (zOver theta : ℝ) :
    sqRisk
        (((Measure.pi (fun _ : Fin n ↦ P)).prod (poissonMeasure lambda)).restrict
          (Prod.snd ⁻¹' Set.Iic n))
        (fun z ↦ cappedStatistic T zOver z.1 z.2) theta =
      sqRisk
        ((finitePoissonSampleLaw P lambda).restrict
          (FiniteSample.count ⁻¹' Set.Iic n)) T theta := by
  -- On the restricted source, `cappedStatistic` is the squared loss pulled
  -- back along `totalizedPrefix`; use `integral_map` and
  -- `map_totalizedPrefix_restrict_nonoverflow`.
  let overflow : FiniteSample X := ⟨0, fun i => Fin.elim0 i⟩
  unfold sqRisk
  rw [← map_totalizedPrefix_restrict_nonoverflow P lambda n overflow]
  rw [integral_map
    (μ := ((Measure.pi (fun _ : Fin n ↦ P)).prod (poissonMeasure lambda)).restrict
      (Prod.snd ⁻¹' Set.Iic n))
    (φ := fun z : (Fin n → X) × ℕ ↦ totalizedPrefix overflow z.1 z.2)
    (f := fun s : FiniteSample X ↦ (T s - theta) ^ 2)
    (measurable_totalizedPrefix overflow).aemeasurable
    ((hT.sub measurable_const).pow_const 2).aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (measurable_snd measurableSet_Iic)] with z hz
  have hzn : z.2 ≤ n := hz
  simp [cappedStatistic, totalizedPrefix, cappedPrefix, hzn]

/-- For [an observation probability law](hyp:P), [a Poisson mean](hyp:lambda),
[a fixed sample size](hyp:n), [a statistic](hyp:T), [an overflow value](hyp:zOver),
and [a target](hyp:theta), [the squared risk of the capped statistic on the
overflow restriction is its constant overflow loss times the Poisson overflow
probability](goal). -/
theorem sqRisk_cappedStatistic_restrict_overflow_eq
    (P : Measure X) [IsProbabilityMeasure P] (lambda : ℝ≥0) (n : ℕ)
    (T : FiniteSample X → ℝ) (zOver theta : ℝ) :
    sqRisk
        (((Measure.pi (fun _ : Fin n ↦ P)).prod (poissonMeasure lambda)).restrict
          (Prod.snd ⁻¹' Set.Ioi n))
        (fun z ↦ cappedStatistic T zOver z.1 z.2) theta =
      (zOver - theta) ^ 2 * (poissonMeasure lambda).real (Set.Ioi n) := by
  -- The capped statistic is constant on `m > n`; evaluate the restricted
  -- integral and the product-event mass using that the iid law has mass one.
  unfold sqRisk
  have hae : ∀ᵐ z ∂
      ((Measure.pi (fun _ : Fin n ↦ P)).prod (poissonMeasure lambda)).restrict
        (Prod.snd ⁻¹' Set.Ioi n),
      (cappedStatistic T zOver z.1 z.2 - theta) ^ 2 =
        (zOver - theta) ^ 2 := by
    filter_upwards [ae_restrict_mem (measurable_snd measurableSet_Ioi)] with z hz
    change n < z.2 at hz
    simp [cappedStatistic, not_le_of_gt hz]
  have hset : (Prod.snd : ((Fin n → X) × ℕ) → ℕ) ⁻¹' Set.Ioi n =
      (Set.univ : Set (Fin n → X)) ×ˢ Set.Ioi n := by
    ext z
    simp
  rw [integral_congr_ae hae, integral_const]
  simp only [smul_eq_mul, measureReal_def]
  rw [Measure.restrict_apply_univ, hset,
    Measure.prod_apply (MeasurableSet.univ.prod measurableSet_Ioi)]
  simp [mul_comm]

/-- For [an observation probability law](hyp:P), [a Poisson mean](hyp:lambda),
[a fixed sample size](hyp:n), [a measurable uniformly bounded statistic](hyp:hT,hTb),
and [a target](hyp:theta), [restricting the finite-Poisson law to counts at most
the fixed sample size cannot increase squared risk](goal). -/
theorem sqRisk_finitePoisson_restrict_nonoverflow_le
    (P : Measure X) [IsProbabilityMeasure P] (lambda : ℝ≥0) (n : ℕ)
    {T : FiniteSample X → ℝ} (hT : Measurable T)
    (hTb : UniformlyBounded T) (theta : ℝ) :
    sqRisk
        ((finitePoissonSampleLaw P lambda).restrict
          (FiniteSample.count ⁻¹' Set.Iic n)) T theta ≤
      sqRisk (finitePoissonSampleLaw P lambda) T theta := by
  -- Split the full integral over the measurable count event and its
  -- complement, then discard the nonnegative complementary squared loss.
  obtain ⟨M, hM, hTb⟩ := hTb
  let μ : Measure (FiniteSample X) := finitePoissonSampleLaw P lambda
  let s : Set (FiniteSample X) := FiniteSample.count ⁻¹' Set.Iic n
  have hs : MeasurableSet s := by
    exact measurable_finiteSample_count measurableSet_Iic
  have hlossInt : Integrable (fun z => (T z - theta) ^ 2) μ := by
    refine (integrable_const ((M + |theta|) ^ 2)).mono'
      ((hT.sub measurable_const).pow_const 2).aestronglyMeasurable ?_
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq_le_sq,
      abs_of_nonneg (add_nonneg hM (abs_nonneg theta))]
    exact (abs_sub _ _).trans (add_le_add (hTb z) le_rfl)
  have hsInt : Integrable (fun z => (T z - theta) ^ 2) (μ.restrict s) :=
    hlossInt.restrict
  have hscInt : Integrable (fun z => (T z - theta) ^ 2) (μ.restrict sᶜ) :=
    hlossInt.restrict
  unfold sqRisk
  change (∫ z, (T z - theta) ^ 2 ∂μ.restrict s) ≤
    ∫ z, (T z - theta) ^ 2 ∂μ
  conv_rhs => rw [← Measure.restrict_add_restrict_compl (μ := μ) hs,
    integral_add_measure hsInt hscInt]
  exact le_add_of_nonneg_right
    (integral_nonneg fun z => sq_nonneg (T z - theta))

/-- For [an observation probability law](hyp:P), [a Poisson mean](hyp:lambda),
and [a fixed sample size](hyp:n), if [the statistic is measurable](hyp:hT),
[the interval is ordered](hyp:hab),
[the statistic stays in the interval](hyp:hTmem), [the target is in the
interval](hyp:htheta), and [the overflow value is in the interval](hyp:hzOver),
then [the fixed-iid squared risk of the Rao--Blackwell statistic is at most the
uncapped finite-Poisson risk plus the squared interval diameter times the
Poisson overflow probability](goal). -/
theorem sqRisk_raoBlackwellStatistic_le
    (P : Measure X) [IsProbabilityMeasure P] (lambda : ℝ≥0) (n : ℕ)
    {T : FiniteSample X → ℝ} (hT : Measurable T)
    {a b theta zOver : ℝ} (hab : a ≤ b)
    (hTmem : ∀ s, T s ∈ Set.Icc a b) (htheta : theta ∈ Set.Icc a b)
    (hzOver : zOver ∈ Set.Icc a b) :
    sqRisk (Measure.pi (fun _ : Fin n ↦ P))
        (raoBlackwellStatistic lambda T zOver) theta ≤
      sqRisk (finitePoissonSampleLaw P lambda) T theta +
        (b - a) ^ 2 * (poissonMeasure lambda).real (Set.Ioi n) := by
  -- Apply `sqRisk_kernelMean_le_comp` to the bounded capped statistic, rewrite
  -- the composed law with `auxPoissonCountKernel_comp_pi`, and split its risk
  -- integral over `m ≤ n` and `m > n`.  Rewrite the first restriction with
  -- `map_totalizedPrefix_restrict_nonoverflow`; bound the overflow loss by
  -- the squared interval diameter before integrating its indicator.
  have hTb : UniformlyBounded T := by
    refine ⟨max |a| |b|, ?_, ?_⟩
    · exact (abs_nonneg a).trans (le_max_left _ _)
    · intro s
      exact abs_le_max_abs_abs (hTmem s).1 (hTmem s).2
  have hCappedBound : UniformlyBounded
      (fun z : (Fin n → X) × ℕ ↦ cappedStatistic T zOver z.1 z.2) := by
    refine ⟨max |a| |b|, ?_, ?_⟩
    · exact (abs_nonneg a).trans (le_max_left _ _)
    · intro z
      by_cases h : z.2 ≤ n
      · simp only [cappedStatistic, h, ↓reduceDIte]
        exact abs_le_max_abs_abs (hTmem _).1 (hTmem _).2
      · simp only [cappedStatistic, h, ↓reduceDIte]
        exact abs_le_max_abs_abs hzOver.1 hzOver.2
  let μ : Measure ((Fin n → X) × ℕ) :=
    (Measure.pi (fun _ : Fin n ↦ P)).prod (poissonMeasure lambda)
  let s : Set ((Fin n → X) × ℕ) := Prod.snd ⁻¹' Set.Iic n
  have hs : MeasurableSet s := measurable_snd measurableSet_Iic
  obtain ⟨M, hM, hCappedBoundM⟩ := hCappedBound
  have hlossInt : Integrable
      (fun z : (Fin n → X) × ℕ =>
        (cappedStatistic T zOver z.1 z.2 - theta) ^ 2) μ := by
    refine (integrable_const ((M + |theta|) ^ 2)).mono'
      (((measurable_cappedStatistic hT zOver).sub measurable_const).pow_const 2
        ).aestronglyMeasurable ?_
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq_le_sq,
      abs_of_nonneg (add_nonneg hM (abs_nonneg theta))]
    exact (abs_sub _ _).trans (add_le_add (hCappedBoundM z) le_rfl)
  have hsplit :
      sqRisk μ (fun z : (Fin n → X) × ℕ ↦
          cappedStatistic T zOver z.1 z.2) theta =
        sqRisk (μ.restrict s) (fun z : (Fin n → X) × ℕ ↦
            cappedStatistic T zOver z.1 z.2) theta +
          sqRisk (μ.restrict sᶜ) (fun z : (Fin n → X) × ℕ ↦
            cappedStatistic T zOver z.1 z.2) theta := by
    unfold sqRisk
    conv_lhs => rw [← Measure.restrict_add_restrict_compl (μ := μ) hs,
      integral_add_measure hlossInt.restrict hlossInt.restrict]
  have hsc : sᶜ = Prod.snd ⁻¹' Set.Ioi n := by
    rw [← Set.preimage_compl, Set.compl_Iic]
  have hoverflowSq : (zOver - theta) ^ 2 ≤ (b - a) ^ 2 := by
    have hdist : |zOver - theta| ≤ b - a := by
      simpa [Real.dist_eq] using Real.dist_le_of_mem_Icc hzOver htheta
    rw [← sq_abs (zOver - theta)]
    exact (sq_le_sq₀ (abs_nonneg _) (sub_nonneg.mpr hab)).2 hdist
  have hoverflowProb : 0 ≤ (poissonMeasure lambda).real (Set.Ioi n) := by
    positivity
  calc
    sqRisk (Measure.pi (fun _ : Fin n ↦ P))
          (raoBlackwellStatistic lambda T zOver) theta ≤
        sqRisk (auxPoissonCountKernel lambda ∘ₘ
            Measure.pi (fun _ : Fin n ↦ P))
          (fun z : (Fin n → X) × ℕ ↦ cappedStatistic T zOver z.1 z.2) theta := by
      exact sqRisk_kernelMean_le_comp
        (Measure.pi (fun _ : Fin n ↦ P)) (auxPoissonCountKernel lambda)
          (measurable_cappedStatistic hT zOver)
          ⟨M, hM, hCappedBoundM⟩ theta
    _ = sqRisk μ (fun z : (Fin n → X) × ℕ ↦
          cappedStatistic T zOver z.1 z.2) theta := by
      rw [auxPoissonCountKernel_comp_pi]
    _ = sqRisk (μ.restrict s) (fun z : (Fin n → X) × ℕ ↦
            cappedStatistic T zOver z.1 z.2) theta +
          sqRisk (μ.restrict sᶜ) (fun z : (Fin n → X) × ℕ ↦
            cappedStatistic T zOver z.1 z.2) theta := hsplit
    _ = sqRisk
          ((finitePoissonSampleLaw P lambda).restrict
            (FiniteSample.count ⁻¹' Set.Iic n)) T theta +
        (zOver - theta) ^ 2 * (poissonMeasure lambda).real (Set.Ioi n) := by
      rw [show μ.restrict s =
          ((Measure.pi (fun _ : Fin n ↦ P)).prod
            (poissonMeasure lambda)).restrict (Prod.snd ⁻¹' Set.Iic n) from rfl,
        sqRisk_cappedStatistic_restrict_nonoverflow_eq P lambda n hT zOver theta,
        hsc]
      exact congrArg
        (fun r => sqRisk
          ((finitePoissonSampleLaw P lambda).restrict
            (FiniteSample.count ⁻¹' Set.Iic n)) T theta + r)
        (sqRisk_cappedStatistic_restrict_overflow_eq
          P lambda n T zOver theta)
    _ ≤ sqRisk (finitePoissonSampleLaw P lambda) T theta +
        (b - a) ^ 2 * (poissonMeasure lambda).real (Set.Ioi n) :=
      add_le_add
        (sqRisk_finitePoisson_restrict_nonoverflow_le
          P lambda n hT hTb theta)
        (mul_le_mul_of_nonneg_right hoverflowSq hoverflowProb)

/-- For [an observation probability law](hyp:P), [a Poisson mean](hyp:lambda),
and [a fixed sample size](hyp:n), under
[measurability of the statistic](hyp:hT),
[unit-interval bounds on the statistic](hyp:hTmem), [target](hyp:htheta),
and [overflow value](hyp:hzOver), [the fixed-iid Rao--Blackwell risk is at most
the uncapped finite-Poisson risk plus exactly the overflow probability](goal). -/
theorem sqRisk_raoBlackwellStatistic_unitInterval_le
    (P : Measure X) [IsProbabilityMeasure P] (lambda : ℝ≥0) (n : ℕ)
    {T : FiniteSample X → ℝ} (hT : Measurable T)
    {theta zOver : ℝ} (hTmem : ∀ s, T s ∈ Set.Icc (0 : ℝ) 1)
    (htheta : theta ∈ Set.Icc (0 : ℝ) 1)
    (hzOver : zOver ∈ Set.Icc (0 : ℝ) 1) :
    sqRisk (Measure.pi (fun _ : Fin n ↦ P))
        (raoBlackwellStatistic lambda T zOver) theta ≤
      sqRisk (finitePoissonSampleLaw P lambda) T theta +
        (poissonMeasure lambda).real (Set.Ioi n) := by
  -- Specialize the interval theorem to `[0,1]` and normalize `(1 - 0)^2`.
  simpa using
    (sqRisk_raoBlackwellStatistic_le P lambda n hT
      (a := (0 : ℝ)) (b := 1) (theta := theta) (zOver := zOver)
      (by norm_num) hTmem htheta hzOver)

end Causalean.Stat
