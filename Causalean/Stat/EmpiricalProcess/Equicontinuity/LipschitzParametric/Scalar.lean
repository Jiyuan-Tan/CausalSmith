/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.Concentration.Hilbert.EmpiricalMean.Tail
public import Causalean.Stat.EmpiricalProcess.Equicontinuity.LipschitzParametric.Rademacher

/-! # Expected scalar deviations for Lipschitz parameter classes

This module combines symmetrization, conditional chaining, and envelope truncation to
obtain an expected uniform-deviation inequality under only a square-integrable envelope.
-/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped BigOperators ENNReal

namespace Causalean.Stat

open Causalean.Stat.Concentration

/-- [The expected empirical envelope norm is at most its population root
second moment](goal) under [a population probability law](hyp:P), for [positive
sample size](hyp:hn) and [a measurable, square-integrable
envelope](hyp:L,hLmeas,hL2). -/
lemma expected_empiricalNorm_le
    {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) (L : X → ℝ) (hLmeas : Measurable L)
    (hL2 : Integrable (fun x => L x ^ 2) P) :
    ∫ S : Fin n → X, Concentration.empiricalNorm S L
        ∂Measure.pi (fun _ : Fin n => P) ≤
      Real.sqrt (∫ x, L x ^ 2 ∂P) := by
  let Q : Measure (Fin n → X) := Measure.pi (fun _ : Fin n => P)
  let g : (Fin n → X) → ℝ := fun S => Concentration.empiricalNorm S L
  have hgmeas : Measurable g := by
    dsimp [g, Concentration.empiricalNorm]
    fun_prop
  have hgsq_eq : (fun S => g S ^ 2) =
      fun S => 1 / (n : ℝ) * ∑ i : Fin n, L (S i) ^ 2 := by
    funext S
    dsimp [g, Concentration.empiricalNorm]
    rw [Real.sq_sqrt (by positivity)]
  have hcoord (i : Fin n) : Integrable (fun S : Fin n → X => L (S i) ^ 2) Q := by
    change Integrable ((fun x => L x ^ 2) ∘ (Function.eval i)) Q
    exact ((measurePreserving_eval (fun _ : Fin n => P) i).integrable_comp
      hL2.aestronglyMeasurable).2 hL2
  have hgsq : Integrable (fun S => g S ^ 2) Q := by
    rw [hgsq_eq]
    exact (integrable_finsetSum Finset.univ fun i _ => hcoord i).const_mul _
  have hnonneg : ∀ S, 0 ≤ g S := by
    intro S
    dsimp [g, Concentration.empiricalNorm]
    positivity
  have hgsqnorm : Integrable (fun S => ‖g S‖ ^ 2) Q := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hnonneg _)] using hgsq
  have hcs :=
    Concentration.HilbertEmpiricalMean.integral_norm_le_sqrt_integral_norm_sq
      Q g hgmeas.stronglyMeasurable hgsqnorm
  have hleft : (∫ S, ‖g S‖ ∂Q) = ∫ S, g S ∂Q := by
    apply integral_congr_ae
    filter_upwards with S
    simp [Real.norm_eq_abs, abs_of_nonneg (hnonneg S)]
  have hcoord_int (i : Fin n) :
      (∫ S : Fin n → X, L (S i) ^ 2 ∂Q) = ∫ x, L x ^ 2 ∂P := by
    exact integral_comp_eval (μ := fun _ : Fin n => P) (i := i) hL2.aestronglyMeasurable
  have hright : (∫ S, ‖g S‖ ^ 2 ∂Q) = ∫ x, L x ^ 2 ∂P := by
    simp_rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg _)]
    rw [hgsq_eq, integral_const_mul,
      integral_finsetSum Finset.univ (fun i _ => hcoord i)]
    simp_rw [hcoord_int]
    simp [hn.ne']
  rw [hleft, hright] at hcs
  simpa [Q, g] using hcs

/-- [The empirical envelope norm is integrable under the product law](goal)
for [positive sample size](hyp:hn) when [the envelope is measurable and
square-integrable](hyp:L,hLmeas,hL2) under [the population probability
law](hyp:P). -/
@[fun_prop]
lemma empiricalNorm_integrable
    {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) (L : X → ℝ) (hLmeas : Measurable L)
    (hL2 : Integrable (fun x => L x ^ 2) P) :
    Integrable (fun S : Fin n → X => Concentration.empiricalNorm S L)
      (Measure.pi (fun _ : Fin n => P)) := by
  let Q : Measure (Fin n → X) := Measure.pi (fun _ : Fin n => P)
  let g : (Fin n → X) → ℝ := fun S => Concentration.empiricalNorm S L
  have hgmeas : Measurable g := by
    dsimp [g, Concentration.empiricalNorm]
    fun_prop
  have hcoord (i : Fin n) : Integrable (fun S : Fin n → X => L (S i) ^ 2) Q := by
    change Integrable ((fun x => L x ^ 2) ∘ (Function.eval i)) Q
    exact ((measurePreserving_eval (fun _ : Fin n => P) i).integrable_comp
      hL2.aestronglyMeasurable).2 hL2
  have hsq : Integrable (fun S : Fin n → X =>
      1 / (n : ℝ) * ∑ i : Fin n, L (S i) ^ 2) Q :=
    (integrable_finsetSum Finset.univ fun i _ => hcoord i).const_mul _
  have hdom : ∀ S, ‖g S‖ ≤ 1 +
      1 / (n : ℝ) * ∑ i : Fin n, L (S i) ^ 2 := by
    intro S
    have hu : 0 ≤ 1 / (n : ℝ) * ∑ i : Fin n, L (S i) ^ 2 := by positivity
    have hsqrt : Real.sqrt (1 / (n : ℝ) * ∑ i : Fin n, L (S i) ^ 2) ≤
        1 + 1 / (n : ℝ) * ∑ i : Fin n, L (S i) ^ 2 := by
      nlinarith [Real.sq_sqrt hu, Real.sqrt_nonneg
        (1 / (n : ℝ) * ∑ i : Fin n, L (S i) ^ 2)]
    simpa [g, Concentration.empiricalNorm, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)] using hsqrt
  exact Integrable.mono' ((integrable_const (1 : ℝ)).add hsq)
    hgmeas.aestronglyMeasurable (ae_of_all _ hdom)

/-- [The expected uniform empirical-average deviation of a bounded Lipschitz
class satisfies the finite-dimensional maximal inequality](goal) under [a
population probability law](hyp:P) at [positive sample size](hyp:hn).  The
[measurable class](hyp:F,hFmeas) is [centered](hyp:hzero) and [Lipschitz on the
parameter ball](hyp:θ₀,hLip,hδ), with [a measurable, nonnegative,
square-integrable envelope](hyp:L,hLmeas,hL,hL2) that is [bounded by a
nonnegative constant](hyp:hM,hLM). -/
theorem scalar_parametric_expected_average_le_of_bounded
    {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (P : Measure X) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) (F : E → X → ℝ) (L : X → ℝ)
    (hFmeas : ∀ θ, Measurable (F θ)) (hLmeas : Measurable L)
    (hL : ∀ x, 0 ≤ L x)
    (hL2 : Integrable (fun x => L x ^ 2) P)
    (θ₀ : E) {δ : ℝ}
    (hLip : ∀ θ ∈ Metric.closedBall θ₀ δ, ∀ η ∈ Metric.closedBall θ₀ δ, ∀ z,
      |F θ z - F η z| ≤ L z * ‖θ - η‖)
    (hzero : ∀ x, F θ₀ x = 0)
    {M : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M) (hLM : ∀ x, L x ≤ M) :
    ∫ S : Fin n → X,
        uniformDeviation n
          ((fun θ : Metric.closedBall θ₀ δ => F θ.1) ∘
            closedBallDenseSeq θ₀ hδ.le) P id S
        ∂Measure.pi (fun _ : Fin n => P) ≤
      192 * (Module.finrank ℝ E + 1) * δ *
        Real.sqrt (∫ x, L x ^ 2 ∂P) / Real.sqrt (n : ℝ) := by
  classical
  let B := Metric.closedBall θ₀ δ
  let FB : B → X → ℝ := fun θ => F θ.1
  let θc : B := ⟨θ₀, by
    change dist θ₀ θ₀ ≤ δ
    simpa using hδ.le⟩
  letI : Nonempty B := ⟨θc⟩
  let FD : ℕ → X → ℝ := FB ∘ denseSeq B
  have hcont : ∀ x, Continuous (fun θ : B => FB θ x) := by
    intro x
    apply continuous_iff_continuousAt.2
    intro θ
    rw [Metric.continuousAt_iff]
    intro ε hε
    refine ⟨ε / (L x + 1), div_pos hε (by linarith [hL x]), ?_⟩
    intro η hη
    have hb := hLip η.1 η.2 θ.1 θ.2 x
    have hdist : ‖η.1 - θ.1‖ < ε / (L x + 1) := by
      change dist (η.1 : E) θ.1 < ε / (L x + 1) at hη
      simpa [dist_eq_norm] using hη
    rw [Real.dist_eq]
    calc
      |FB η x - FB θ x| ≤ L x * ‖η.1 - θ.1‖ := by simpa [FB] using hb
      _ ≤ (L x + 1) * ‖η.1 - θ.1‖ := by
        gcongr
        linarith
      _ < (L x + 1) * (ε / (L x + 1)) :=
        mul_lt_mul_of_pos_left hdist (by linarith [hL x])
      _ = ε := by
        have hx : 0 < L x + 1 := by linarith [hL x]
        field_simp
  have hFDmeas : ∀ k, Measurable (FD k) := fun k => hFmeas _
  have henv : ∀ k x, |FD k x| ≤ δ * M := by
    intro k x
    let θ : B := denseSeq B k
    have hp := θ.2
    rw [Metric.mem_closedBall, dist_eq_norm] at hp
    calc
      |FD k x| ≤ L x * ‖θ.1 - θ₀‖ := by
        simpa [FD, FB, θ, hzero] using hLip θ.1 θ.2 θ₀ (Metric.mem_closedBall_self hδ.le) x
      _ ≤ L x * δ := mul_le_mul_of_nonneg_left hp (hL x)
      _ ≤ M * δ := mul_le_mul_of_nonneg_right (hLM x) hδ.le
      _ = δ * M := by ring
  have hsymm := uniform_deviation_expectation_le_two_smul_rademacher_complexity
    (μ := P) (f := FD) hn id (fun k => by simpa [Function.comp_def] using hFDmeas k)
    (mul_nonneg hδ.le hM) henv
  have hpoint (S : Fin n → X) : empiricalRademacherComplexity n FD S ≤
      96 * (Module.finrank ℝ E + 1) * δ *
        Concentration.empiricalNorm S L / Real.sqrt (n : ℝ) := by
    dsimp [FD]
    rw [← _root_.empiricalRademacherComplexity_eq n hcont S]
    simpa [FB] using parametric_empiricalRademacher_le hn S F L hL θ₀ hLip hzero hδ
  have hradInt : Integrable (fun S : Fin n → X =>
      empiricalRademacherComplexity n FD S) (Measure.pi (fun _ : Fin n => P)) := by
    have hm := Concentration.empiricalRademacherComplexity_measurable_countable
      FD hFDmeas n
    apply Integrable.of_bound hm.aestronglyMeasurable (δ * M)
    filter_upwards with S
    have hrange := Concentration.empiricalRademacherComplexity_mem_Icc
      FD (mul_nonneg hδ.le hM) henv n S
    rw [Real.norm_eq_abs, abs_of_nonneg hrange.1]
    exact hrange.2
  have hrhsInt : Integrable (fun S : Fin n → X =>
      96 * (Module.finrank ℝ E + 1) * δ *
        Concentration.empiricalNorm S L / Real.sqrt (n : ℝ))
      (Measure.pi (fun _ : Fin n => P)) := by
    convert (empiricalNorm_integrable P hn L hLmeas hL2).const_mul
      (96 * (Module.finrank ℝ E + 1) * δ / Real.sqrt (n : ℝ)) using 1
    funext S
    ring
  have hrad : rademacherComplexity n FD P id ≤
      96 * (Module.finrank ℝ E + 1) * δ *
        Real.sqrt (∫ x, L x ^ 2 ∂P) / Real.sqrt (n : ℝ) := by
    rw [Concentration.rademacherComplexity_eq]
    have hi := integral_mono hradInt hrhsInt hpoint
    let c : ℝ := 96 * (Module.finrank ℝ E + 1) * δ / Real.sqrt (n : ℝ)
    have hc : 0 ≤ c := by
      dsimp [c]
      positivity
    have hfun : (fun S : Fin n → X =>
        96 * (Module.finrank ℝ E + 1) * δ *
          Concentration.empiricalNorm S L / Real.sqrt (n : ℝ)) =
        fun S => c * Concentration.empiricalNorm S L := by
      funext S
      dsimp [c]
      ring
    have hE := expected_empiricalNorm_le P hn L hLmeas hL2
    calc
      _ ≤ ∫ S : Fin n → X,
          96 * (Module.finrank ℝ E + 1) * δ *
            Concentration.empiricalNorm S L / Real.sqrt (n : ℝ)
          ∂Measure.pi (fun _ : Fin n => P) := by
            simpa [Function.comp_def] using hi
      _ = c * ∫ S : Fin n → X, Concentration.empiricalNorm S L
          ∂Measure.pi (fun _ : Fin n => P) := by rw [hfun, integral_const_mul]
      _ ≤ c * Real.sqrt (∫ x, L x ^ 2 ∂P) := mul_le_mul_of_nonneg_left hE hc
      _ = _ := by dsimp [c]; ring
  have hseq : closedBallDenseSeq θ₀ hδ.le = denseSeq B := by
    rfl
  calc
    _ ≤ 2 • rademacherComplexity n FD P id := by
      rw [hseq]
      simpa [FD, FB, B] using hsymm
    _ ≤ 2 • (96 * (Module.finrank ℝ E + 1) * δ *
        Real.sqrt (∫ x, L x ^ 2 ∂P) / Real.sqrt (n : ℝ)) := by
      simpa [nsmul_eq_mul] using mul_le_mul_of_nonneg_left hrad (by norm_num : (0 : ℝ) ≤ 2)
    _ = _ := by simp [nsmul_eq_mul]; ring

/-- [The uniform deviation of a class is bounded by the deviation of an
approximating class plus empirical and population means of the error
envelope](goal) under [a population law](hyp:P), at [positive sample
size](hyp:hn), on [a sample](hyp:S).  The [main and approximating
classes](hyp:F,H) are [measurable](hyp:hFmeas,hHmeas), the [error
envelope](hyp:T) is [integrable](hyp:hTint), and the approximation obeys
[boundedness](hyp:hHbound) and [the pointwise error bound](hyp:hDiff). -/
lemma uniformDeviation_le_add_envelope
    {X ι : Type*} [MeasurableSpace X] [Nonempty ι]
    (P : Measure X) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) (F H : ι → X → ℝ) (T : X → ℝ)
    (hFmeas : ∀ i, Measurable (F i)) (hHmeas : ∀ i, Measurable (H i))
    (hTint : Integrable T P) {B : ℝ} (hHbound : ∀ i x, |H i x| ≤ B)
    (hDiff : ∀ i x, |F i x - H i x| ≤ T x)
    (S : Fin n → X) :
    uniformDeviation n F P id S ≤ uniformDeviation n H P id S +
      ((n : ℝ)⁻¹ * ∑ k : Fin n, T (S k) + ∫ x, T x ∂P) := by
  have hHint (i : ι) : Integrable (H i) P :=
    Integrable.of_bound (hHmeas i).aestronglyMeasurable B
      (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hHbound i x)
  have hDint (i : ι) : Integrable (fun x => F i x - H i x) P :=
    Integrable.mono' hTint (hFmeas i |>.sub (hHmeas i)).aestronglyMeasurable
      (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hDiff i x)
  have hFint (i : ι) : Integrable (F i) P := by
    have hs := (hDint i).add (hHint i)
    exact hs.congr (ae_of_all _ fun x => by simp)
  have hbddH : BddAbove (Set.range fun i =>
      |(n : ℝ)⁻¹ * ∑ k : Fin n, H i (S k) - ∫ x, H i x ∂P|) := by
    refine ⟨2 * B, ?_⟩
    rintro _ ⟨i, rfl⟩
    have havg : |(n : ℝ)⁻¹ * ∑ k : Fin n, H i (S k)| ≤ B := by
      rw [abs_mul, abs_of_pos (inv_pos.mpr (by exact_mod_cast hn))]
      calc
        (n : ℝ)⁻¹ * |∑ k : Fin n, H i (S k)|
            ≤ (n : ℝ)⁻¹ * ∑ k : Fin n, |H i (S k)| := by
              gcongr
              exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ (n : ℝ)⁻¹ * ∑ _k : Fin n, B := by
              gcongr with k
              exact hHbound i (S k)
        _ = B := by simp [hn.ne']
    have hint : |∫ x, H i x ∂P| ≤ B := by
      calc
        |∫ x, H i x ∂P| ≤ ∫ x, |H i x| ∂P := abs_integral_le_integral_abs
        _ ≤ ∫ _x, B ∂P := integral_mono (hHint i).abs (integrable_const B) (hHbound i)
        _ = B := by simp
    exact (abs_sub _ _).trans (by linarith)
  unfold uniformDeviation
  simp only [id_eq]
  refine ciSup_le fun i => ?_
  have hcenterDiff :
      |((n : ℝ)⁻¹ * ∑ k : Fin n, F i (S k) - ∫ x, F i x ∂P) -
        ((n : ℝ)⁻¹ * ∑ k : Fin n, H i (S k) - ∫ x, H i x ∂P)| ≤
      (n : ℝ)⁻¹ * ∑ k : Fin n, T (S k) + ∫ x, T x ∂P := by
    have hsample : |∑ k : Fin n, (F i (S k) - H i (S k))| ≤ ∑ k : Fin n, T (S k) :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun k _ => hDiff i (S k))
    have hint : |∫ x, F i x - H i x ∂P| ≤ ∫ x, T x ∂P := by
      calc
        |∫ x, F i x - H i x ∂P| ≤ ∫ x, |F i x - H i x| ∂P :=
          abs_integral_le_integral_abs
        _ ≤ ∫ x, T x ∂P := integral_mono (hDint i).abs hTint (hDiff i)
    rw [integral_sub (hFint i) (hHint i)] at hint
    calc
      _ = |(n : ℝ)⁻¹ * ∑ k : Fin n, (F i (S k) - H i (S k)) -
          (∫ x, F i x ∂P - ∫ x, H i x ∂P)| := by
            rw [Finset.sum_sub_distrib]
            congr 1 <;> ring
      _ ≤ |(n : ℝ)⁻¹ * ∑ k : Fin n, (F i (S k) - H i (S k))| +
          |∫ x, F i x ∂P - ∫ x, H i x ∂P| := abs_sub _ _
      _ ≤ (n : ℝ)⁻¹ * ∑ k : Fin n, T (S k) + ∫ x, T x ∂P := by
        rw [abs_mul, abs_of_pos (inv_pos.mpr (by exact_mod_cast hn))]
        gcongr
  let a := (n : ℝ)⁻¹ * ∑ k : Fin n, F i (S k) - ∫ x, F i x ∂P
  let b := (n : ℝ)⁻¹ * ∑ k : Fin n, H i (S k) - ∫ x, H i x ∂P
  let e := (n : ℝ)⁻¹ * ∑ k : Fin n, T (S k) + ∫ x, T x ∂P
  have hab : |a - b| ≤ e := by simpa [a, b, e] using hcenterDiff
  calc
    |a| = |b + (a - b)| := by congr 1 <;> ring
    _ ≤ |b| + |a - b| := abs_add_le _ _
    _ ≤ |b| + e := by gcongr
    _ ≤ (⨆ j, |(n : ℝ)⁻¹ * ∑ k : Fin n, H j (S k) - ∫ x, H j x ∂P|) + e := by
      gcongr
      exact le_ciSup hbddH i

/-- [The expected uniform empirical-average deviation of a Lipschitz scalar
class is bounded by dimension times radius and the population envelope
norm](goal) under [a population probability law](hyp:P) at [positive sample
size](hyp:hn).  The [measurable score class](hyp:F,hFmeas) is
[centered](hyp:hzero) and [Lipschitz on the parameter
ball](hyp:θ₀,hLip,hδ), with [a measurable, nonnegative, square-integrable
envelope](hyp:L,hLmeas,hL,hL2). -/
theorem scalar_parametric_expected_average_le
    {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (P : Measure X) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) (F : E → X → ℝ) (L : X → ℝ)
    (hFmeas : ∀ θ, Measurable (F θ)) (hLmeas : Measurable L)
    (hL : ∀ x, 0 ≤ L x)
    (hL2 : Integrable (fun x => L x ^ 2) P)
    (θ₀ : E) {δ : ℝ}
    (hLip : ∀ θ ∈ Metric.closedBall θ₀ δ, ∀ η ∈ Metric.closedBall θ₀ δ, ∀ z,
      |F θ z - F η z| ≤ L z * ‖θ - η‖)
    (hzero : ∀ x, F θ₀ x = 0)
    (hδ : 0 < δ) :
    ∫ S : Fin n → X,
        uniformDeviation n
          ((fun θ : Metric.closedBall θ₀ δ => F θ.1) ∘
            closedBallDenseSeq θ₀ hδ.le) P id S
        ∂Measure.pi (fun _ : Fin n => P) ≤
      192 * (Module.finrank ℝ E + 1) * δ *
        Real.sqrt (∫ x, L x ^ 2 ∂P) / Real.sqrt (n : ℝ) := by
  classical
  let B := Metric.closedBall θ₀ δ
  let θseq : ℕ → B := closedBallDenseSeq θ₀ hδ.le
  let F0 : ℕ → X → ℝ := (fun θ : B => F θ.1) ∘ θseq
  let moment := ∫ x, L x ^ 2 ∂P
  have hmoment : 0 ≤ moment := integral_nonneg fun x => sq_nonneg (L x)
  have hLint : Integrable L P := by
    apply Integrable.mono' ((integrable_const (1 : ℝ)).add hL2)
      hLmeas.aestronglyMeasurable
    filter_upwards with x
    change |L x| ≤ 1 + L x ^ 2
    rw [abs_of_nonneg (hL x)]
    nlinarith [sq_nonneg (L x - 1 / 2)]
  apply le_of_forall_pos_le_add
  intro ζ hζ
  let M := 1 + 2 * δ * moment / ζ
  have hM : 0 < M := by dsimp [M]; positivity
  let keep : Set X := {x | L x ≤ M}
  have hkeep : MeasurableSet keep := measurableSet_le hLmeas measurable_const
  let LT : X → ℝ := fun x => if x ∈ keep then L x else 0
  let T : X → ℝ := fun x => if x ∈ keep then 0 else L x
  let FT : E → X → ℝ := fun θ x => if x ∈ keep then F θ x else 0
  let H0 : ℕ → X → ℝ := (fun θ : B => FT θ.1) ∘ θseq
  have hLTmeas : Measurable LT := Measurable.ite hkeep hLmeas measurable_const
  have hTmeas : Measurable T := Measurable.ite hkeep measurable_const hLmeas
  have hFTmeas : ∀ θ, Measurable (FT θ) := fun θ =>
    Measurable.ite hkeep (hFmeas θ) measurable_const
  have hLT : ∀ x, 0 ≤ LT x := by intro x; simp only [LT]; split <;> simp [hL]
  have hT : ∀ x, 0 ≤ T x := by intro x; simp only [T]; split <;> simp [hL]
  have hLTle : ∀ x, LT x ≤ M := by
    intro x
    simp only [LT]
    split
    · simpa [keep] using ‹x ∈ keep›
    · exact hM.le
  have hLTsq : Integrable (fun x => LT x ^ 2) P := by
    apply Integrable.mono' hL2 (hLTmeas.pow_const 2).aestronglyMeasurable
    filter_upwards with x
    simp only [LT]
    split <;> simp [sq_nonneg]
  have hTint : Integrable T P := by
    apply Integrable.mono' hLint hTmeas.aestronglyMeasurable
    filter_upwards with x
    simp only [T]
    split <;> simp [hL, abs_of_nonneg]
  have hLipT : ∀ θ ∈ Metric.closedBall θ₀ δ, ∀ η ∈ Metric.closedBall θ₀ δ, ∀ z,
      |FT θ z - FT η z| ≤ LT z * ‖θ - η‖ := by
    intro θ hθ η hη z
    simp only [FT, LT]
    split
    · exact hLip θ hθ η hη z
    · simp
  have hzeroT : ∀ x, FT θ₀ x = 0 := by
    intro x
    simp [FT, hzero]
  have htrunc := scalar_parametric_expected_average_le_of_bounded
    P hn FT LT hFTmeas hLTmeas hLT hLTsq θ₀ hLipT hzeroT hδ hM.le hLTle
  have hmomentT : (∫ x, LT x ^ 2 ∂P) ≤ moment := by
    apply integral_mono hLTsq hL2
    intro x
    simp only [LT]
    split <;> simp [sq_nonneg]
  have htrunc' :
      ∫ S : Fin n → X, uniformDeviation n H0 P id S
          ∂Measure.pi (fun _ : Fin n => P) ≤
        192 * (Module.finrank ℝ E + 1) * δ *
          Real.sqrt moment / Real.sqrt (n : ℝ) := by
    calc
      _ ≤ 192 * (Module.finrank ℝ E + 1) * δ *
          Real.sqrt (∫ x, LT x ^ 2 ∂P) / Real.sqrt (n : ℝ) := by
            simpa [H0, θseq, B] using htrunc
      _ ≤ _ := by
        gcongr
  have htail : (∫ x, T x ∂P) ≤ moment / M := by
    have hdom : ∀ x, T x ≤ L x ^ 2 / M := by
      intro x
      simp only [T]
      split
      · positivity
      · have hx : M < L x := lt_of_not_ge (by simpa [keep] using ‹x ∉ keep›)
        apply (le_div_iff₀ hM).2
        nlinarith [hL x]
    have hright : Integrable (fun x => L x ^ 2 / M) P := hL2.div_const M
    calc
      _ ≤ ∫ x, L x ^ 2 / M ∂P := integral_mono hTint hright hdom
      _ = moment / M := by rw [integral_div]
  have htailSmall : 2 * δ * (∫ x, T x ∂P) < ζ := by
    have hfrac : 2 * δ * (moment / M) < ζ := by
      rw [show 2 * δ * (moment / M) = (2 * δ * moment) / M by ring]
      apply (div_lt_iff₀ hM).2
      dsimp [M]
      field_simp [ne_of_gt hζ]
      nlinarith [hζ]
    exact (mul_le_mul_of_nonneg_left htail
      (mul_nonneg (by norm_num) hδ.le)).trans_lt hfrac
  let Td : X → ℝ := fun x => δ * T x
  have hTdmeas : Measurable Td := hTmeas.const_mul δ
  have hTdint : Integrable Td P := hTint.const_mul δ
  have hTd : ∀ x, 0 ≤ Td x := fun x => mul_nonneg hδ.le (hT x)
  have hH0meas : ∀ k, Measurable (H0 k) := fun k => hFTmeas _
  have hF0meas : ∀ k, Measurable (F0 k) := fun k => hFmeas _
  have hH0bound : ∀ k x, |H0 k x| ≤ δ * M := by
    intro k x
    simp only [H0, Function.comp_apply, FT]
    split
    · let θ : B := θseq k
      have hp := θ.2
      rw [Metric.mem_closedBall, dist_eq_norm] at hp
      calc
        |F θ.1 x| ≤ L x * ‖θ.1 - θ₀‖ := by
          simpa [hzero] using hLip θ.1 θ.2 θ₀ (Metric.mem_closedBall_self hδ.le) x
        _ ≤ M * δ := mul_le_mul (by simpa [keep] using ‹x ∈ keep›) hp (norm_nonneg _) hM.le
        _ = δ * M := by ring
    · simp [mul_nonneg hδ.le hM.le]
  have hdiff : ∀ k x, |F0 k x - H0 k x| ≤ Td x := by
    intro k x
    simp only [F0, H0, Function.comp_apply, FT, Td, T]
    split
    · simp
    · let θ : B := θseq k
      have hp := θ.2
      rw [Metric.mem_closedBall, dist_eq_norm] at hp
      calc
        |F θ.1 x - 0| ≤ L x * ‖θ.1 - θ₀‖ := by
          simpa [hzero] using hLip θ.1 θ.2 θ₀ (Metric.mem_closedBall_self hδ.le) x
        _ ≤ L x * δ := mul_le_mul_of_nonneg_left hp (hL x)
        _ = δ * L x := by ring
  have hcomp (S : Fin n → X) : uniformDeviation n F0 P id S ≤
      uniformDeviation n H0 P id S +
        ((n : ℝ)⁻¹ * ∑ k : Fin n, Td (S k) + ∫ x, Td x ∂P) :=
    uniformDeviation_le_add_envelope P hn F0 H0 Td hF0meas hH0meas
      hTdint hH0bound hdiff S
  have hHdevMeas : Measurable (fun S : Fin n → X => uniformDeviation n H0 P id S) :=
    uniformDeviation_measurable id hH0meas
  have hHdevInt : Integrable (fun S : Fin n → X => uniformDeviation n H0 P id S)
      (Measure.pi (fun _ : Fin n => P)) := by
    apply Integrable.of_bound hHdevMeas.aestronglyMeasurable (2 * (δ * M))
    filter_upwards with S
    rw [Real.norm_eq_abs, abs_of_nonneg (by
      unfold uniformDeviation
      exact Real.iSup_nonneg fun k => abs_nonneg _)]
    unfold uniformDeviation
    simp only [id_eq]
    apply ciSup_le
    intro k
    have hkint : Integrable (H0 k) P := Integrable.of_bound
      (hH0meas k).aestronglyMeasurable (δ * M)
      (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hH0bound k x)
    have havg : |(n : ℝ)⁻¹ * ∑ i : Fin n, H0 k (S i)| ≤ δ * M := by
      rw [abs_mul, abs_of_pos (inv_pos.mpr (by exact_mod_cast hn))]
      calc
        _ ≤ (n : ℝ)⁻¹ * ∑ i : Fin n, |H0 k (S i)| := by
          gcongr; exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ (n : ℝ)⁻¹ * ∑ _i : Fin n, (δ * M) := by gcongr with i; exact hH0bound k (S i)
        _ = δ * M := by simp [hn.ne']
    have hint : |∫ x, H0 k x ∂P| ≤ δ * M := by
      calc
        _ ≤ ∫ x, |H0 k x| ∂P := abs_integral_le_integral_abs
        _ ≤ ∫ _x, δ * M ∂P := integral_mono hkint.abs (integrable_const _) (hH0bound k)
        _ = δ * M := by simp
    exact (abs_sub _ _).trans (by linarith)
  have hTdcoord (k : Fin n) : Integrable (fun S : Fin n → X => Td (S k))
      (Measure.pi (fun _ : Fin n => P)) := by
    change Integrable (Td ∘ (fun S : Fin n → X => S k)) _
    exact ((measurePreserving_eval (fun _ : Fin n => P) k).integrable_comp
      hTdint.aestronglyMeasurable).2 hTdint
  have hTdavgInt : Integrable (fun S : Fin n → X =>
      (n : ℝ)⁻¹ * ∑ k : Fin n, Td (S k)) (Measure.pi (fun _ : Fin n => P)) :=
    (integrable_finsetSum Finset.univ fun k _ => hTdcoord k).const_mul _
  have hTdconstInt : Integrable (fun _S : Fin n → X => ∫ x, Td x ∂P)
      (Measure.pi (fun _ : Fin n => P)) := integrable_const _
  have herrInt : Integrable (fun S : Fin n → X =>
      (n : ℝ)⁻¹ * ∑ k : Fin n, Td (S k) + ∫ x, Td x ∂P)
      (Measure.pi (fun _ : Fin n => P)) := hTdavgInt.add hTdconstInt
  have hFdevMeas : Measurable (fun S : Fin n → X => uniformDeviation n F0 P id S) :=
    uniformDeviation_measurable id hF0meas
  have hFdevInt : Integrable (fun S : Fin n → X => uniformDeviation n F0 P id S)
      (Measure.pi (fun _ : Fin n => P)) := by
    apply Integrable.mono' (hHdevInt.add herrInt) hFdevMeas.aestronglyMeasurable
    filter_upwards with S
    rw [Real.norm_eq_abs, abs_of_nonneg (by
      unfold uniformDeviation
      exact Real.iSup_nonneg fun k => abs_nonneg _)]
    exact hcomp S
  have hIntComp := integral_mono hFdevInt (hHdevInt.add herrInt) hcomp
  have herrEval :
      (∫ S : Fin n → X,
        ((n : ℝ)⁻¹ * ∑ k : Fin n, Td (S k) + ∫ x, Td x ∂P)
        ∂Measure.pi (fun _ : Fin n => P)) = 2 * δ * ∫ x, T x ∂P := by
    rw [integral_add hTdavgInt hTdconstInt, integral_const, integral_const_mul,
      integral_finsetSum Finset.univ (fun k _ => hTdcoord k)]
    simp_rw [integral_comp_eval (μ := fun _ : Fin n => P) (i := _) hTdint.aestronglyMeasurable]
    rw [show (∫ x, Td x ∂P) = δ * ∫ x, T x ∂P by
      simp [Td, integral_const_mul]]
    simp [hn.ne']
    ring
  calc
    ∫ S : Fin n → X, uniformDeviation n F0 P id S
        ∂Measure.pi (fun _ : Fin n => P)
        ≤ (∫ S : Fin n → X, uniformDeviation n H0 P id S
            ∂Measure.pi (fun _ : Fin n => P)) +
          ∫ S : Fin n → X,
            ((n : ℝ)⁻¹ * ∑ k : Fin n, Td (S k) + ∫ x, Td x ∂P)
            ∂Measure.pi (fun _ : Fin n => P) := by
              simpa [integral_add hHdevInt herrInt] using hIntComp
    _ ≤ 192 * (Module.finrank ℝ E + 1) * δ * Real.sqrt moment /
          Real.sqrt (n : ℝ) + 2 * δ * ∫ x, T x ∂P := by
            rw [herrEval]
            gcongr
    _ ≤ 192 * (Module.finrank ℝ E + 1) * δ * Real.sqrt moment /
          Real.sqrt (n : ℝ) + ζ := by linarith
    _ = _ := by rfl


end Causalean.Stat
