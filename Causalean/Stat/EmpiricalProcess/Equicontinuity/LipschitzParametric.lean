/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.EmpiricalProcess.Equicontinuity.LipschitzParametric.Scalar
public import Causalean.Stat.EmpiricalProcess.Equicontinuity.Modulus
public import Causalean.Stat.Sample.PiTransport

/-! # Stochastic equicontinuity for Lipschitz parameter classes

This module proves a measurable vector-valued maximal inequality for finite-dimensional
Lipschitz score classes and derives stochastic equicontinuity for consistent estimators.
-/

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped BigOperators ENNReal

namespace Causalean.Stat

open Causalean.Stat.Concentration

@[expose] public section

/-- The [centered root-sample-size empirical process](goal) compares the mean
of [a vector-valued function](hyp:f) on [a finite sample](hyp:S) of [size
`n`](hyp:n) with its mean under [the population law](hyp:P). -/
noncomputable def sampleEmpProc
    {X V : Type*} [MeasurableSpace X] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (P : Measure X) (f : X → V) (n : ℕ) (S : Fin n → X) : V :=
  Real.sqrt (n : ℝ) •
    ((n : ℝ)⁻¹ • (∑ i, f (S i)) - ∫ x, f x ∂P)

/-- The [measurable local empirical-process supremum](goal) takes the largest
process norm along a canonical dense sequence in the ball with [center](hyp:θ₀)
and [nonnegative radius](hyp:hδ).  It evaluates [the score family](hyp:ψ)
under [the population law](hyp:P) on [a finite sample](hyp:S) of [size
`n`](hyp:n). -/
noncomputable def parametricEmpProcSup
    {X E V : Type*} [MeasurableSpace X]
    [PseudoMetricSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (P : Measure X) (ψ : E → X → V) (θ₀ : E) {δ : ℝ} (hδ : 0 ≤ δ)
    (n : ℕ) (S : Fin n → X) : ℝ :=
  ⨆ k : ℕ, ‖sampleEmpProc P
    (fun x => ψ (closedBallDenseSeq θ₀ hδ k) x - ψ θ₀ x) n S‖

/-- The [dimension-only constant in the Lipschitz parametric maximal
inequality](goal) is 192 times the dimension of [the output space](hyp:V) times
one plus the dimension of [the parameter space](hyp:E). -/
noncomputable def lipschitzParametricConstant
    (E V : Type*) [AddCommGroup E] [Module ℝ E]
    [AddCommGroup V] [Module ℝ V] : ℝ :=
  192 * Module.finrank ℝ V * (Module.finrank ℝ E + 1)

/-- [The dense-sequence empirical-process supremum is measurable](goal) when
[every score is measurable](hyp:hψmeas).  The supremum is formed from [a score
family](hyp:ψ), [population law](hyp:P), [center](hyp:θ₀), [nonnegative
radius](hyp:hδ), and [sample size](hyp:n). -/
@[fun_prop]
theorem parametricEmpProcSup_measurable
    {X E V : Type*} [MeasurableSpace X]
    [PseudoMetricSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (P : Measure X) (ψ : E → X → V) (θ₀ : E) {δ : ℝ} (hδ : 0 ≤ δ)
    (n : ℕ) (hψmeas : ∀ θ, Measurable (ψ θ)) :
    Measurable (fun S : Fin n → X => parametricEmpProcSup P ψ θ₀ hδ n S) := by
  unfold parametricEmpProcSup
  apply Measurable.iSup
  intro k
  have hf : Measurable (fun x =>
      ψ (closedBallDenseSeq θ₀ hδ k) x - ψ θ₀ x) :=
    (hψmeas _).sub (hψmeas θ₀)
  have hp : Measurable (fun S : Fin n → X => sampleEmpProc P
      (fun x => ψ (closedBallDenseSeq θ₀ hδ k) x - ψ θ₀ x) n S) := by
    unfold sampleEmpProc
    fun_prop
  exact hp.norm

/-- [The uniform empirical deviation of a countable scalar class is
integrable](goal) under [a population probability law](hyp:P) for [positive
sample size](hyp:hn), provided [the class](hyp:F) and [its envelope](hyp:G) are
[respectively measurable and integrable](hyp:hFmeas,hGint), and the envelope
[dominates the class pointwise](hyp:henv). -/
@[fun_prop]
lemma uniformDeviation_integrable_of_envelope
    {X ι : Type*} [MeasurableSpace X] [Nonempty ι] [Countable ι]
    (P : Measure X) [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n)
    (F : ι → X → ℝ) (G : X → ℝ)
    (hFmeas : ∀ i, Measurable (F i)) (hGint : Integrable G P)
    (henv : ∀ i x, |F i x| ≤ G x) :
    Integrable (fun S : Fin n → X => uniformDeviation n F P id S)
      (Measure.pi (fun _ : Fin n => P)) := by
  have hFint (i : ι) : Integrable (F i) P :=
    Integrable.mono' hGint (hFmeas i).aestronglyMeasurable
      (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using henv i x)
  have hcoord (k : Fin n) : Integrable (fun S : Fin n → X => G (S k))
      (Measure.pi (fun _ : Fin n => P)) := by
    change Integrable (G ∘ (fun S : Fin n → X => S k)) _
    exact ((measurePreserving_eval (fun _ : Fin n => P) k).integrable_comp
      hGint.aestronglyMeasurable).2 hGint
  have hdomInt : Integrable (fun S : Fin n → X =>
      (n : ℝ)⁻¹ * ∑ k : Fin n, G (S k) + ∫ x, G x ∂P)
      (Measure.pi (fun _ : Fin n => P)) :=
    ((integrable_finsetSum Finset.univ fun k _ => hcoord k).const_mul _).add
      (integrable_const _)
  have hmeas : Measurable (fun S : Fin n → X => uniformDeviation n F P id S) :=
    uniformDeviation_measurable id hFmeas
  apply Integrable.mono' hdomInt hmeas.aestronglyMeasurable
  filter_upwards with S
  rw [Real.norm_eq_abs, abs_of_nonneg (by
    unfold uniformDeviation
    exact Real.iSup_nonneg fun i => abs_nonneg _)]
  unfold uniformDeviation
  simp only [id_eq]
  apply ciSup_le
  intro i
  have havg : |(n : ℝ)⁻¹ * ∑ k : Fin n, F i (S k)| ≤
      (n : ℝ)⁻¹ * ∑ k : Fin n, G (S k) := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr (by exact_mod_cast hn))]
    gcongr
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun k _ => henv i (S k))
  have hint : |∫ x, F i x ∂P| ≤ ∫ x, G x ∂P := by
    calc
      _ ≤ ∫ x, |F i x| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ x, G x ∂P := integral_mono (hFint i).abs hGint (henv i)
  exact (abs_sub _ _).trans (add_le_add havg hint)

/-- [A finite-dimensional vector's norm is at most the sum of its absolute
coordinates in the standard orthonormal basis](goal), for [the given
vector](hyp:v). -/
lemma norm_le_sum_abs_inner_basis
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (v : V) :
    ‖v‖ ≤ ∑ j : Fin (Module.finrank ℝ V),
      |inner ℝ ((stdOrthonormalBasis ℝ V) j) v| := by
  let b := stdOrthonormalBasis ℝ V
  calc
    ‖v‖ = ‖∑ j, (b.repr v).ofLp j • b j‖ := congrArg norm (b.sum_repr v).symm
    _ ≤ ∑ j, ‖(b.repr v).ofLp j • b j‖ :=
      norm_sum_le _ _
    _ = ∑ j, |inner ℝ (b j) v| := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [norm_smul, Real.norm_eq_abs, b.repr_apply_apply,
        b.orthonormal.norm_eq_one, mul_one]

/-- [The measurable local empirical-process supremum is integrable and its
expectation is bounded by the dimension constant times the radius and envelope
norm](goal).  This holds under [a population probability law](hyp:P) at
[positive sample size](hyp:hn) for [a measurable vector score](hyp:ψ,hψmeas)
with [a measurable, nonnegative, square-integrable
envelope](hyp:L,hLmeas,hL,hL2), assuming [Lipschitz control](hyp:hLip) on the
ball with [center](hyp:θ₀) and [positive radius](hyp:hδ). -/
theorem parametricEmpProcSup_integrable_and_expected_le
    {X E V : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (P : Measure X) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) (ψ : E → X → V) (L : X → ℝ)
    (hψmeas : ∀ θ, Measurable (ψ θ)) (hLmeas : Measurable L)
    (hL : ∀ x, 0 ≤ L x)
    (hL2 : Integrable (fun x => L x ^ 2) P)
    (θ₀ : E) {δ : ℝ}
    (hLip : ∀ θ ∈ Metric.closedBall θ₀ δ, ∀ η ∈ Metric.closedBall θ₀ δ, ∀ z,
      ‖ψ θ z - ψ η z‖ ≤ L z * ‖θ - η‖)
    (hδ : 0 < δ) :
    Integrable (fun S : Fin n → X => parametricEmpProcSup P ψ θ₀ hδ.le n S)
        (Measure.pi (fun _ : Fin n => P)) ∧
      ∫ S : Fin n → X, parametricEmpProcSup P ψ θ₀ hδ.le n S
          ∂Measure.pi (fun _ : Fin n => P) ≤
        lipschitzParametricConstant E V * δ *
          Real.sqrt (∫ x, L x ^ 2 ∂P) := by
  classical
  let b := stdOrthonormalBasis ℝ V
  let θseq := closedBallDenseSeq θ₀ hδ.le
  let Fv : ℕ → X → V := fun k x => ψ (θseq k) x - ψ θ₀ x
  let Fc : Fin (Module.finrank ℝ V) → ℕ → X → ℝ :=
    fun j k x => inner ℝ (b j) (Fv k x)
  have hLint : Integrable L P := by
    apply Integrable.mono' ((integrable_const (1 : ℝ)).add hL2)
      hLmeas.aestronglyMeasurable
    filter_upwards with x
    change |L x| ≤ 1 + L x ^ 2
    rw [abs_of_nonneg (hL x)]
    nlinarith [sq_nonneg (L x - 1 / 2)]
  have hθ (k : ℕ) : ‖(θseq k).1 - θ₀‖ ≤ δ := by
    have hp := (θseq k).2
    rw [Metric.mem_closedBall, dist_eq_norm] at hp
    exact hp
  have hFvmeas : ∀ k, Measurable (Fv k) := fun k => (hψmeas _).sub (hψmeas θ₀)
  have hFvenv : ∀ k x, ‖Fv k x‖ ≤ δ * L x := by
    intro k x
    calc
      ‖Fv k x‖ ≤ L x * ‖(θseq k).1 - θ₀‖ := by
        simpa [Fv] using
          hLip (θseq k).1 (θseq k).2 θ₀ (Metric.mem_closedBall_self hδ.le) x
      _ ≤ L x * δ := mul_le_mul_of_nonneg_left (hθ k) (hL x)
      _ = δ * L x := by ring
  have hFcmeas : ∀ j k, Measurable (Fc j k) := by
    intro j k
    fun_prop
  have hFcenv : ∀ j k x, |Fc j k x| ≤ δ * L x := by
    intro j k x
    calc
      |Fc j k x| ≤ ‖b j‖ * ‖Fv k x‖ := by
        simpa [Fc, Real.norm_eq_abs] using
          norm_inner_le_norm (𝕜 := ℝ) (b j) (Fv k x)
      _ = ‖Fv k x‖ := by rw [b.orthonormal.norm_eq_one, one_mul]
      _ ≤ δ * L x := hFvenv k x
  have hFcInt (j) : Integrable (fun S : Fin n → X => uniformDeviation n (Fc j) P id S)
      (Measure.pi (fun _ : Fin n => P)) :=
    uniformDeviation_integrable_of_envelope P hn (Fc j) (fun x => δ * L x)
      (hFcmeas j) (hLint.const_mul δ) (hFcenv j)
  have hscalar (j : Fin (Module.finrank ℝ V)) :
      ∫ S : Fin n → X, uniformDeviation n (Fc j) P id S
          ∂Measure.pi (fun _ : Fin n => P) ≤
        192 * (Module.finrank ℝ E + 1) * δ *
          Real.sqrt (∫ x, L x ^ 2 ∂P) / Real.sqrt (n : ℝ) := by
    let Fj : E → X → ℝ := fun θ x => inner ℝ (b j) (ψ θ x - ψ θ₀ x)
    have hFjmeas : ∀ θ, Measurable (Fj θ) := by intro θ; fun_prop
    have hFjLip : ∀ θ ∈ Metric.closedBall θ₀ δ, ∀ η ∈ Metric.closedBall θ₀ δ, ∀ x,
        |Fj θ x - Fj η x| ≤ L x * ‖θ - η‖ := by
      intro θ hθ η hη x
      calc
        |Fj θ x - Fj η x| = |inner ℝ (b j) (ψ θ x - ψ η x)| := by
          simp [Fj, inner_sub_right]
        _ ≤ ‖b j‖ * ‖ψ θ x - ψ η x‖ := by
          simpa [Real.norm_eq_abs] using
            norm_inner_le_norm (𝕜 := ℝ) (b j) (ψ θ x - ψ η x)
        _ = ‖ψ θ x - ψ η x‖ := by rw [b.orthonormal.norm_eq_one, one_mul]
        _ ≤ L x * ‖θ - η‖ := hLip θ hθ η hη x
    have hs := scalar_parametric_expected_average_le P hn Fj L hFjmeas hLmeas hL hL2
      θ₀ hFjLip (by simp [Fj]) hδ
    change ∫ S : Fin n → X,
        uniformDeviation n
          ((fun θ : Metric.closedBall θ₀ δ => Fj θ.1) ∘
            closedBallDenseSeq θ₀ hδ.le) P id S
          ∂Measure.pi (fun _ : Fin n => P) ≤ _
    exact hs
  have hprocMeas (k : ℕ) : Measurable (fun S : Fin n → X =>
      sampleEmpProc P (Fv k) n S) := by
    unfold sampleEmpProc
    fun_prop
  have hsupMeas : Measurable (fun S : Fin n → X => parametricEmpProcSup P ψ θ₀ hδ.le n S) := by
    unfold parametricEmpProcSup
    apply Measurable.iSup
    intro k
    fun_prop
  have hpoint (S : Fin n → X) : parametricEmpProcSup P ψ θ₀ hδ.le n S ≤
      Real.sqrt (n : ℝ) * ∑ j, uniformDeviation n (Fc j) P id S := by
    unfold parametricEmpProcSup
    apply ciSup_le
    intro k
    calc
      ‖sampleEmpProc P (Fv k) n S‖ ≤
          ∑ j, |inner ℝ (b j) (sampleEmpProc P (Fv k) n S)| :=
        norm_le_sum_abs_inner_basis _
      _ ≤ ∑ j, Real.sqrt (n : ℝ) * uniformDeviation n (Fc j) P id S := by
        apply Finset.sum_le_sum
        intro j hj
        have hFvint : Integrable (Fv k) P := Integrable.mono' (hLint.const_mul δ)
          (hFvmeas k).aestronglyMeasurable
          (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hFvenv k x)
        have hcoord : inner ℝ (b j) (sampleEmpProc P (Fv k) n S) =
            Real.sqrt (n : ℝ) * ((n : ℝ)⁻¹ * ∑ i, Fc j k (S i) -
              ∫ x, Fc j k x ∂P) := by
          unfold sampleEmpProc
          simp only [inner_sub_right, real_inner_smul_right, inner_sum]
          rw [integral_inner hFvint (b j)]
        rw [hcoord, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
        gcongr
        unfold uniformDeviation
        exact le_ciSup (by
          refine ⟨δ * ((n : ℝ)⁻¹ * ∑ i, L (S i) + ∫ x, L x ∂P), ?_⟩
          rintro _ ⟨q, rfl⟩
          calc
            |(n : ℝ)⁻¹ * ∑ i, Fc j q (S i) - ∫ x, Fc j q x ∂P| ≤
                (n : ℝ)⁻¹ * ∑ i, |Fc j q (S i)| + ∫ x, |Fc j q x| ∂P := by
                  refine (abs_sub _ _).trans (add_le_add ?_ abs_integral_le_integral_abs)
                  rw [abs_mul, abs_of_pos (inv_pos.mpr (by exact_mod_cast hn))]
                  gcongr
                  exact Finset.abs_sum_le_sum_abs _ _
            _ ≤ δ * ((n : ℝ)⁻¹ * ∑ i, L (S i) + ∫ x, L x ∂P) := by
              have hFcqInt : Integrable (Fc j q) P := Integrable.mono' (hLint.const_mul δ)
                (hFcmeas j q).aestronglyMeasurable
                (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hFcenv j q x)
              have hi := integral_mono hFcqInt.abs (hLint.const_mul δ)
                (fun x => hFcenv j q x)
              rw [integral_const_mul] at hi
              calc
                _ ≤ (n : ℝ)⁻¹ * ∑ i, δ * L (S i) + δ * ∫ x, L x ∂P := by
                  gcongr with i
                  exact hFcenv j q (S i)
                _ = _ := by rw [← Finset.mul_sum]; ring) k
      _ = Real.sqrt (n : ℝ) * ∑ j, uniformDeviation n (Fc j) P id S := by
        rw [Finset.mul_sum]
  have hdomInt : Integrable (fun S : Fin n → X =>
      Real.sqrt (n : ℝ) * ∑ j, uniformDeviation n (Fc j) P id S)
      (Measure.pi (fun _ : Fin n => P)) :=
    (integrable_finsetSum Finset.univ fun j _ => hFcInt j).const_mul _
  have hsupInt : Integrable (fun S : Fin n → X => parametricEmpProcSup P ψ θ₀ hδ.le n S)
      (Measure.pi (fun _ : Fin n => P)) := by
    apply Integrable.mono' hdomInt hsupMeas.aestronglyMeasurable
    filter_upwards with S
    rw [Real.norm_eq_abs, abs_of_nonneg (by
      unfold parametricEmpProcSup
      exact Real.iSup_nonneg fun k => norm_nonneg _)]
    exact hpoint S
  refine ⟨hsupInt, ?_⟩
  calc
    _ ≤ ∫ S : Fin n → X,
        Real.sqrt (n : ℝ) * ∑ j, uniformDeviation n (Fc j) P id S
        ∂Measure.pi (fun _ : Fin n => P) := integral_mono hsupInt hdomInt hpoint
    _ = Real.sqrt (n : ℝ) * ∑ j,
        ∫ S : Fin n → X, uniformDeviation n (Fc j) P id S
          ∂Measure.pi (fun _ : Fin n => P) := by
      rw [integral_const_mul, integral_finsetSum Finset.univ (fun j _ => hFcInt j)]
    _ ≤ Real.sqrt (n : ℝ) * ∑ _j : Fin (Module.finrank ℝ V),
        (192 * (Module.finrank ℝ E + 1) * δ *
          Real.sqrt (∫ x, L x ^ 2 ∂P) / Real.sqrt (n : ℝ)) := by
      gcongr with j
      exact hscalar j
    _ = lipschitzParametricConstant E V * δ * Real.sqrt (∫ x, L x ^ 2 ∂P) := by
      simp [lipschitzParametricConstant]
      have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
      field_simp

/-- [The dense local empirical-process supremum is integrable](goal) under [a
population probability law](hyp:P) at [positive sample size](hyp:hn) for [a
measurable vector score](hyp:ψ,hψmeas) with [a measurable, nonnegative,
square-integrable envelope](hyp:L,hLmeas,hL,hL2), assuming [Lipschitz
control](hyp:hLip) on the ball with [center](hyp:θ₀) and [positive
radius](hyp:hδ). -/
@[fun_prop]
theorem parametricEmpProcSup_integrable
    {X E V : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (P : Measure X) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) (ψ : E → X → V) (L : X → ℝ)
    (hψmeas : ∀ θ, Measurable (ψ θ)) (hLmeas : Measurable L)
    (hL : ∀ x, 0 ≤ L x)
    (hL2 : Integrable (fun x => L x ^ 2) P)
    (θ₀ : E) {δ : ℝ}
    (hLip : ∀ θ ∈ Metric.closedBall θ₀ δ, ∀ η ∈ Metric.closedBall θ₀ δ, ∀ z,
      ‖ψ θ z - ψ η z‖ ≤ L z * ‖θ - η‖)
    (hδ : 0 < δ) :
    Integrable (fun S : Fin n → X => parametricEmpProcSup P ψ θ₀ hδ.le n S)
      (Measure.pi (fun _ : Fin n => P)) :=
  (parametricEmpProcSup_integrable_and_expected_le P hn ψ L hψmeas hLmeas hL hL2
    θ₀ hLip hδ).1

/-- **Quantitative finite-dimensional Lipschitz maximal inequality.** For
[a population law](hyp:P), [positive sample size](hyp:hn),
[vector score](hyp:ψ), [nonnegative envelope](hyp:L), [score and envelope
measurability](hyp:hψmeas,hLmeas), [envelope nonnegativity and square
integrability](hyp:hL,hL2), [global Lipschitz control](hyp:hLip), [center](hyp:θ₀),
and [positive radius](hyp:hδ), [the expected local empirical-process supremum
is at most a dimension constant times the radius and envelope L² norm](goal).

This library-specific finite-sample refinement is assembled from scalar entropy and
Rademacher bounds and is used below to derive the asymptotic equicontinuity consequence
associated with van der Vaart (1998), Example 19.7. -/
theorem parametricEmpProcSup_expected_le
    {X E V : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (P : Measure X) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) (ψ : E → X → V) (L : X → ℝ)
    (hψmeas : ∀ θ, Measurable (ψ θ)) (hLmeas : Measurable L)
    (hL : ∀ x, 0 ≤ L x)
    (hL2 : Integrable (fun x => L x ^ 2) P)
    (θ₀ : E) {δ : ℝ}
    (hLip : ∀ θ ∈ Metric.closedBall θ₀ δ, ∀ η ∈ Metric.closedBall θ₀ δ, ∀ z,
      ‖ψ θ z - ψ η z‖ ≤ L z * ‖θ - η‖)
    (hδ : 0 < δ) :
    ∫ S : Fin n → X, parametricEmpProcSup P ψ θ₀ hδ.le n S
        ∂Measure.pi (fun _ : Fin n => P) ≤
      lipschitzParametricConstant E V * δ *
        Real.sqrt (∫ x, L x ^ 2 ∂P) :=
  (parametricEmpProcSup_integrable_and_expected_le P hn ψ L hψmeas hLmeas hL hL2
    θ₀ hLip hδ).2

/-- [The finite-product empirical process equals the sample-indexed empirical
process vector](goal) for [a vector-valued function](hyp:f) evaluated on [an
i.i.d. sample](hyp:S) at [an outcome](hyp:ω), provided the [sample size is
positive](hyp:hn). -/
lemma sampleEmpProc_eq_empProcVec
    {Ω X V : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {μ : Measure Ω} {P : Measure X} (S : IIDSample Ω X μ P)
    (f : X → V) {n : ℕ} (hn : 0 < n) (ω : Ω) :
    sampleEmpProc P f n (fun k : Fin n => S.Z k ω) = S.empProcVec f n ω := by
  unfold sampleEmpProc IIDSample.empProcVec
  change Real.sqrt (n : ℝ) •
      ((n : ℝ)⁻¹ • (∑ i : Fin n, f (S.Z (i : ℕ) ω)) - ∫ x, f x ∂P) = _
  rw [← Fin.sum_univ_eq_sum_range]
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
    Real.mul_self_sqrt (by positivity)
  have hcoef : Real.sqrt (n : ℝ) * (n : ℝ)⁻¹ = (Real.sqrt (n : ℝ))⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    calc
      (Real.sqrt (n : ℝ) * (n : ℝ)⁻¹) * Real.sqrt (n : ℝ) =
          (n : ℝ)⁻¹ * (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) := by ring
      _ = (n : ℝ)⁻¹ * (n : ℝ) := by rw [hsq]
      _ = 1 := inv_mul_cancel₀ (by exact_mod_cast hn.ne')
  rw [smul_sub, smul_smul, hcoef]

/-- [The empirical-process norm at a parameter in the ball is bounded by the
measurable dense supremum](goal).  The bound applies under [a population
probability law](hyp:P) to [a measurable vector score](hyp:ψ,hψmeas) with [a
measurable, nonnegative, square-integrable envelope](hyp:L,hLmeas,hL,hL2) and
[Lipschitz control](hyp:hLip), on the ball with [center](hyp:θ₀) and
[positive radius](hyp:hδ), for [sample](hyp:S) and [parameter in that
ball](hyp:θ,hθ). -/
lemma sampleEmpProc_norm_le_parametricSup
    {X E V : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (P : Measure X) [IsProbabilityMeasure P]
    (ψ : E → X → V) (L : X → ℝ)
    (hψmeas : ∀ θ, Measurable (ψ θ)) (hLmeas : Measurable L)
    (hL : ∀ x, 0 ≤ L x) (hL2 : Integrable (fun x => L x ^ 2) P)
    (θ₀ : E) {δ : ℝ}
    (hLip : ∀ θ ∈ Metric.closedBall θ₀ δ, ∀ η ∈ Metric.closedBall θ₀ δ, ∀ z,
      ‖ψ θ z - ψ η z‖ ≤ L z * ‖θ - η‖)
    (hδ : 0 < δ) {n : ℕ}
    (S : Fin n → X) (θ : E) (hθ : ‖θ - θ₀‖ ≤ δ) :
    ‖sampleEmpProc P (fun x => ψ θ x - ψ θ₀ x) n S‖ ≤
      parametricEmpProcSup P ψ θ₀ hδ.le n S := by
  classical
  let B := Metric.closedBall θ₀ δ
  let θsub : B := ⟨θ, by
    change θ ∈ Metric.closedBall θ₀ δ
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact hθ⟩
  letI : Nonempty B := ⟨⟨θ₀, by
    change dist θ₀ θ₀ ≤ δ
    simpa using hδ.le⟩⟩
  letI : CompactSpace B := isCompact_iff_compactSpace.mp (by
    simpa [B] using (isCompact_closedBall θ₀ δ))
  have hLint : Integrable L P := by
    apply Integrable.mono' ((integrable_const (1 : ℝ)).add hL2)
      hLmeas.aestronglyMeasurable
    filter_upwards with x
    change |L x| ≤ 1 + L x ^ 2
    rw [abs_of_nonneg (hL x)]
    nlinarith [sq_nonneg (L x - 1 / 2)]
  let F : B → X → V := fun q x => ψ q.1 x - ψ θ₀ x
  have hFmeas (q : B) : Measurable (F q) := (hψmeas q.1).sub (hψmeas θ₀)
  have hFint (q : B) : Integrable (F q) P := by
    apply Integrable.mono' (hLint.const_mul ‖q.1 - θ₀‖) (hFmeas q).aestronglyMeasurable
    filter_upwards with x
    simpa [F, mul_comm] using hLip q.1 q.2 θ₀ (Metric.mem_closedBall_self hδ.le) x
  have hpointCont (x : X) : Continuous (fun q : B => F q x) := by
    let K : NNReal := ⟨L x, hL x⟩
    apply (LipschitzWith.of_dist_le_mul (K := K) fun q r => ?_).continuous
    change dist (F q x) (F r x) ≤ L x * dist (q.1 : E) r.1
    have hp := hLip q.1 q.2 r.1 r.2 x
    simpa [F, dist_eq_norm] using hp
  have hIntLip (q r : B) :
      dist (∫ x, F q x ∂P) (∫ x, F r x ∂P) ≤
        (∫ x, L x ∂P) * dist q r := by
    have hDint : Integrable (fun x => F q x - F r x) P := (hFint q).sub (hFint r)
    rw [dist_eq_norm, ← integral_sub (hFint q) (hFint r)]
    calc
      ‖∫ x, F q x - F r x ∂P‖ ≤ ∫ x, ‖F q x - F r x‖ ∂P :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ x, L x * dist q r ∂P := by
        apply integral_mono hDint.norm (hLint.mul_const _)
        intro x
        have hp := hLip q.1 q.2 r.1 r.2 x
        have hd : dist q r = ‖q.1 - r.1‖ := by
          change dist (q.1 : E) r.1 = _
          rw [dist_eq_norm]
        rw [hd]
        simpa [F] using hp
      _ = (∫ x, L x ∂P) * dist q r := by rw [integral_mul_const]
  have hLintNonneg : 0 ≤ ∫ x, L x ∂P := integral_nonneg hL
  have hIntCont : Continuous (fun q : B => ∫ x, F q x ∂P) := by
    let K : NNReal := ⟨∫ x, L x ∂P, hLintNonneg⟩
    exact (LipschitzWith.of_dist_le_mul (K := K) hIntLip).continuous
  have hprocCont : Continuous (fun q : B => sampleEmpProc P (F q) n S) := by
    unfold sampleEmpProc
    fun_prop
  have hnormCont : Continuous (fun q : B => ‖sampleEmpProc P (F q) n S‖) :=
    continuous_norm.comp hprocCont
  have hbdd : BddAbove (Set.range fun q : B => ‖sampleEmpProc P (F q) n S‖) :=
    (isCompact_range hnormCont).bddAbove
  have hsupEq := separableSpaceSup_eq_real hnormCont
  have hseq : closedBallDenseSeq θ₀ hδ.le = denseSeq B := by rfl
  calc
    ‖sampleEmpProc P (fun x => ψ θ x - ψ θ₀ x) n S‖ =
        ‖sampleEmpProc P (F θsub) n S‖ := rfl
    _ ≤ ⨆ q : B, ‖sampleEmpProc P (F q) n S‖ := le_ciSup hbdd θsub
    _ = ⨆ k : ℕ, ‖sampleEmpProc P (F (denseSeq B k)) n S‖ := hsupEq
    _ = parametricEmpProcSup P ψ θ₀ hδ.le n S := by
      unfold parametricEmpProcSup
      rw [hseq]

/-- [The measurable dense supremum equals the supremum over the entire closed
parameter ball](goal).  Continuity follows under [a population probability
law](hyp:P) from [a measurable vector score](hyp:ψ,hψmeas) with [a measurable,
nonnegative, square-integrable envelope](hyp:L,hLmeas,hL,hL2) and [Lipschitz
control](hyp:hLip), on the ball with [center](hyp:θ₀) and [positive
radius](hyp:hδ), for [the finite sample](hyp:S). -/
theorem parametricEmpProcSup_eq_iSup_closedBall
    {X E V : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (P : Measure X) [IsProbabilityMeasure P]
    (ψ : E → X → V) (L : X → ℝ)
    (hψmeas : ∀ θ, Measurable (ψ θ)) (hLmeas : Measurable L)
    (hL : ∀ x, 0 ≤ L x) (hL2 : Integrable (fun x => L x ^ 2) P)
    (θ₀ : E) {δ : ℝ}
    (hLip : ∀ θ ∈ Metric.closedBall θ₀ δ, ∀ η ∈ Metric.closedBall θ₀ δ, ∀ z,
      ‖ψ θ z - ψ η z‖ ≤ L z * ‖θ - η‖)
    (hδ : 0 < δ) {n : ℕ}
    (S : Fin n → X) :
    parametricEmpProcSup P ψ θ₀ hδ.le n S =
      ⨆ θ : Metric.closedBall θ₀ δ,
        ‖sampleEmpProc P (fun x => ψ θ.1 x - ψ θ₀ x) n S‖ := by
  let U : ℝ := parametricEmpProcSup P ψ θ₀ hδ.le n S
  have hfull (θ : Metric.closedBall θ₀ δ) :
      ‖sampleEmpProc P (fun x => ψ θ.1 x - ψ θ₀ x) n S‖ ≤ U := by
    apply sampleEmpProc_norm_le_parametricSup P ψ L hψmeas hLmeas hL hL2 θ₀ hLip
      hδ S θ.1
    have hp := θ.2
    rw [Metric.mem_closedBall, dist_eq_norm] at hp
    exact hp
  have hbdd : BddAbove (Set.range fun θ : Metric.closedBall θ₀ δ =>
      ‖sampleEmpProc P (fun x => ψ θ.1 x - ψ θ₀ x) n S‖) :=
    ⟨U, by rintro _ ⟨θ, rfl⟩; exact hfull θ⟩
  letI : Nonempty (Metric.closedBall θ₀ δ) :=
    ⟨⟨θ₀, by simp [hδ.le]⟩⟩
  apply le_antisymm
  · unfold parametricEmpProcSup
    apply ciSup_le
    intro k
    exact le_ciSup hbdd (closedBallDenseSeq θ₀ hδ.le k)
  · apply ciSup_le
    exact hfull

namespace AsymptoticEquicont

/-- **Lipschitz asymptotic equicontinuity (van der Vaart 1998, Example 19.7).**
For [a population law](hyp:P), [iid sample](hyp:S), [vector score](hyp:ψ),
[nonnegative envelope](hyp:L), [score and envelope measurability](hyp:hψmeas,hLmeas),
[envelope nonnegativity and square integrability](hyp:hL,hL2), [target](hyp:θ₀), [a positive
radius](hyp:hδ₀), and [Lipschitz control on the ball of that radius](hyp:hLip), [the local
empirical-process modulus vanishes in probability](goal).

The Lipschitz hypothesis is only required on a ball around the target, not on the whole
parameter space: asymptotic equicontinuity chooses its own radius and its event is monotone
in that radius, so the proof simply shrinks to `min δ δ₀`. This is what admits scores such as
the Poisson score `exp (θᵀx)`, which is locally but not globally Lipschitz with an integrable
envelope. -/
theorem of_lipschitz
    {Ω X E V : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    {μ : Measure Ω} (P : Measure X)
    (S : IIDSample Ω X μ P) (ψ : E → X → V) (L : X → ℝ)
    (hψmeas : ∀ θ, Measurable (ψ θ)) (hLmeas : Measurable L)
    (hL : ∀ x, 0 ≤ L x) (hL2 : Integrable (fun x => L x ^ 2) P)
    (θ₀ : E) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hLip : ∀ θ ∈ Metric.closedBall θ₀ δ₀, ∀ η ∈ Metric.closedBall θ₀ δ₀, ∀ z,
      ‖ψ θ z - ψ η z‖ ≤ L z * ‖θ - η‖) :
    AsymptoticEquicont ψ θ₀ P μ S := by
  classical
  haveI : IsProbabilityMeasure μ := S.indep.isProbabilityMeasure
  letI : IsProbabilityMeasure P := by
    rw [← S.law]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  intro ε hε η hη
  let M : ℝ := lipschitzParametricConstant E V *
    Real.sqrt (∫ x, L x ^ 2 ∂P)
  have hmoment : 0 ≤ ∫ x, L x ^ 2 ∂P := integral_nonneg fun x => sq_nonneg (L x)
  have hM : 0 ≤ M := by
    dsimp [M, lipschitzParametricConstant]
    positivity
  let δ : ℝ := min (ε * η / (2 * (M + 1))) δ₀
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (by positivity) hδ₀
  have hδsmall : δ ≤ ε * η / (2 * (M + 1)) := min_le_left _ _
  have hδball : δ ≤ δ₀ := min_le_right _ _
  -- Restrict the ball-Lipschitz hypothesis from radius `δ₀` inward to the chosen `δ`.
  have hLipδ : ∀ θ ∈ Metric.closedBall θ₀ δ, ∀ η ∈ Metric.closedBall θ₀ δ, ∀ z,
      ‖ψ θ z - ψ η z‖ ≤ L z * ‖θ - η‖ := fun θ hθ η hη z =>
    hLip θ (Metric.closedBall_subset_closedBall hδball hθ) η
      (Metric.closedBall_subset_closedBall hδball hη) z
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  let Q : Measure (Fin n → X) := Measure.pi (fun _ : Fin n => P)
  let U : (Fin n → X) → ℝ :=
    fun T => parametricEmpProcSup P ψ θ₀ hδ.le n T
  have hUInt : Integrable U Q := by
    simpa [U, Q] using parametricEmpProcSup_integrable P hn ψ L hψmeas hLmeas
      hL hL2 θ₀ hLipδ hδ
  have hUmeas : Measurable U := by
    simpa [U] using parametricEmpProcSup_measurable P ψ θ₀ hδ.le n hψmeas
  have hUnonneg : ∀ T, 0 ≤ U T := by
    intro T
    dsimp [U, parametricEmpProcSup]
    exact Real.iSup_nonneg fun k => norm_nonneg _
  have hUint : ∫ T, U T ∂Q ≤ M * δ := by
    have hb :=
      parametricEmpProcSup_expected_le P hn ψ L hψmeas hLmeas hL hL2 θ₀ hLipδ hδ
    dsimp [U, Q, M]
    calc
      _ ≤ lipschitzParametricConstant E V * δ *
          Real.sqrt (∫ x, L x ^ 2 ∂P) := hb
      _ = _ := by ring
  have hratio : (∫ T, U T ∂Q) / ε ≤ η := by
    calc
      (∫ T, U T ∂Q) / ε ≤ (M * δ) / ε :=
        div_le_div_of_nonneg_right hUint hε.le
      _ ≤ (M * (ε * η / (2 * (M + 1)))) / ε := by gcongr
      _ ≤ η := by
        have hMone : 0 < M + 1 := by linarith
        field_simp
        nlinarith [mul_nonneg hM hη.le]
  let A : Set (Fin n → X) := {T | ε < U T}
  have hAmeas : MeasurableSet A := measurableSet_Ioi.preimage hUmeas
  have hmarkov : Q A ≤ ENNReal.ofReal η := by
    have hsub : A ⊆ {T | ENNReal.ofReal ε ≤ ENNReal.ofReal (U T)} := by
      intro T hT
      exact ENNReal.ofReal_le_ofReal hT.le
    have hεne : ENNReal.ofReal ε ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hε)
    have hεtop : ENNReal.ofReal ε ≠ ⊤ := ENNReal.ofReal_ne_top
    calc
      Q A ≤ Q {T | ENNReal.ofReal ε ≤ ENNReal.ofReal (U T)} := measure_mono hsub
      _ ≤ (∫⁻ T, ENNReal.ofReal (U T) ∂Q) / ENNReal.ofReal ε :=
        MeasureTheory.meas_ge_le_lintegral_div hUmeas.ennreal_ofReal.aemeasurable
          hεne hεtop
      _ = ENNReal.ofReal (∫ T, U T ∂Q) / ENNReal.ofReal ε := by
        rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hUInt
          (ae_of_all _ hUnonneg)]
      _ = ENNReal.ofReal ((∫ T, U T ∂Q) / ε) := by
        rw [ENNReal.ofReal_div_of_pos hε]
      _ ≤ ENNReal.ofReal η := ENNReal.ofReal_le_ofReal hratio
  let W : Ω → (Fin n → X) := fun ω k => S.Z k ω
  have hWmeas : Measurable W := iidSample_finN_measurable S n
  have htransport : μ (W ⁻¹' A) = Q A := by
    rw [← Measure.map_apply hWmeas hAmeas, iidSample_finN_pushforward S n]
  calc
    μ {ω | ∃ θ : E, ‖θ - θ₀‖ < δ ∧
        ε < ‖S.empProcVec (fun z => ψ θ z - ψ θ₀ z) n ω‖}
        ≤ μ (W ⁻¹' A) := by
          apply measure_mono
          rintro ω ⟨θ, hθ, hproc⟩
          have hle := sampleEmpProc_norm_le_parametricSup P ψ L hψmeas hLmeas hL hL2
            θ₀ hLipδ hδ (W ω) θ hθ.le
          have heq := sampleEmpProc_eq_empProcVec S
            (fun z => ψ θ z - ψ θ₀ z) hn ω
          exact hproc.trans_le (by simpa [W, U, A, heq] using hle)
    _ = Q A := htransport
    _ ≤ ENNReal.ofReal η := hmarkov

end AsymptoticEquicont

namespace StochEquicontAt

/-- **Estimator-indexed Lipschitz equicontinuity (van der Vaart 1998,
Lemma 19.24).** For [a population law](hyp:P), [iid sample](hyp:S), [vector
score](hyp:ψ), [nonnegative envelope](hyp:L), [score and envelope
measurability](hyp:hψmeas,hLmeas), [envelope nonnegativity and square
integrability](hyp:hL,hL2), [target](hyp:θ₀), [a positive radius](hyp:hδ₀), [Lipschitz
control on the ball of that radius](hyp:hLip), [estimator sequence](hyp:θn), and
[consistency](hyp:hConsistent), [the empirical score increment at the estimator is
`o_P(1)`](goal).

As with the class-level statement, the Lipschitz bound is needed only near the target, which
is what lets locally-Lipschitz scores such as the Poisson score be used here. -/
theorem of_lipschitz
    {Ω X E V : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    {μ : Measure Ω} (P : Measure X)
    (S : IIDSample Ω X μ P) (ψ : E → X → V) (L : X → ℝ)
    (hψmeas : ∀ θ, Measurable (ψ θ)) (hLmeas : Measurable L)
    (hL : ∀ x, 0 ≤ L x) (hL2 : Integrable (fun x => L x ^ 2) P)
    (θ₀ : E) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hLip : ∀ θ ∈ Metric.closedBall θ₀ δ₀, ∀ η ∈ Metric.closedBall θ₀ δ₀, ∀ z,
      ‖ψ θ z - ψ η z‖ ≤ L z * ‖θ - η‖)
    (θn : ℕ → Ω → E)
    (hConsistent : ∀ ε > 0,
      Tendsto (fun n => μ {ω | ε < ‖θn n ω - θ₀‖}) atTop (𝓝 0)) :
    StochEquicontAt ψ θ₀ P μ S θn :=
  stochEquicontAt_of_asymptoticEquicont ψ θ₀ S θn
    (AsymptoticEquicont.of_lipschitz P S ψ L hψmeas hLmeas hL hL2 θ₀ hδ₀ hLip)
    hConsistent

end StochEquicontAt

end
end Causalean.Stat
