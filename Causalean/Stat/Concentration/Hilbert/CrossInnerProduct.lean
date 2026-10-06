/-
Copyright (c) 2026 CausalSmith contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module
public import Causalean.Stat.Concentration.Chebyshev
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
public import Mathlib.Probability.Independence.Integration

/-!
# Independent finite-dimensional cross-inner-product bounds

This module bounds cross-inner products and low-rank orthogonal projections from uniform
directional second-moment envelopes. The results combine independence with elementary
second-moment tail bounds and are reusable in finite-dimensional calibration arguments.
-/
public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace Causalean.Stat.Concentration

/-- Two independent centered finite-dimensional vectors whose directional second moments are bounded by `Λ` have cross-inner-product second moment at most `M * Λ²`. This statement assumes [the hX condition](hyp:hX), [the hY condition](hyp:hY), [the hXL2 condition](hyp:hXL2), [the hYL2 condition](hyp:hYL2), [the hind condition](hyp:hind), [the hXmom condition](hyp:hXmom), [the hYmom condition](hyp:hYmom). [This is the stated conclusion](goal). -/
lemma indep_inner_sq_integral_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {M : ℕ} [MeasurableSpace (EuclideanSpace ℝ (Fin M))]
    [BorelSpace (EuclideanSpace ℝ (Fin M))]
    (X Y : Ω → EuclideanSpace ℝ (Fin M)) (Λ : ℝ)
    (hX : Measurable X) (hY : Measurable Y) (hXL2 : MemLp X 2 μ) (hYL2 : MemLp Y 2 μ)
    (hind : IndepFun X Y μ)
    (hXmom : ∀ u, (∫ ω, inner ℝ u (X ω) ^ 2 ∂μ) ≤ Λ * ‖u‖ ^ 2)
    (hYmom : ∀ u, (∫ ω, inner ℝ u (Y ω) ^ 2 ∂μ) ≤ Λ * ‖u‖ ^ 2) :
    (∫ ω, inner ℝ (X ω) (Y ω) ^ 2 ∂μ) ≤ M * Λ ^ 2 := by
  by_cases hM : M = 0
  · subst M
    have hzeroX : X = 0 := funext fun _ => Subsingleton.elim _ _
    have hzeroY : Y = 0 := funext fun _ => Subsingleton.elim _ _
    simp [hzeroX, hzeroY]
  have i0 : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin M))) :=
    ⟨0, by simpa using Nat.pos_of_ne_zero hM⟩
  have hΛ : 0 ≤ Λ := by
    have hi := hXmom ((stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin M))) i0)
    have hnonneg : 0 ≤ ∫ ω, inner ℝ
        ((stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin M))) i0) (X ω) ^ 2 ∂μ :=
      integral_nonneg (fun _ => sq_nonneg _)
    simp only [OrthonormalBasis.norm_eq_one, one_pow, mul_one] at hi
    exact hnonneg.trans hi
  let νX := Measure.map X μ
  let νY := Measure.map Y μ
  have hXnorm : Integrable (fun x : EuclideanSpace ℝ (Fin M) => ‖x‖ ^ 2) νX := by
    dsimp [νX]
    apply (integrable_map_measure (continuous_norm.pow 2 |>.aestronglyMeasurable)
      hX.aemeasurable).2
    simpa [Function.comp_def] using hXL2.norm.integrable_sq
  have hYnorm : Integrable (fun y : EuclideanSpace ℝ (Fin M) => ‖y‖ ^ 2) νY := by
    dsimp [νY]
    apply (integrable_map_measure (continuous_norm.pow 2 |>.aestronglyMeasurable)
      hY.aemeasurable).2
    simpa [Function.comp_def] using hYL2.norm.integrable_sq
  have hcross : Integrable
      (fun z : EuclideanSpace ℝ (Fin M) × EuclideanSpace ℝ (Fin M) =>
        inner ℝ z.1 z.2 ^ 2) (νX.prod νY) := by
    apply (hXnorm.mul_prod hYnorm).mono' (by fun_prop)
    filter_upwards [] with z
    have habs : |inner ℝ z.1 z.2| ≤ ‖z.1‖ * ‖z.2‖ := by
      simpa only [Real.norm_eq_abs] using (norm_inner_le_norm (𝕜 := ℝ) z.1 z.2)
    have hs := (sq_le_sq₀ (abs_nonneg (inner ℝ z.1 z.2))
      (mul_nonneg (norm_nonneg z.1) (norm_nonneg z.2))).2 habs
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs, mul_pow] using hs
  have hjoint : Measure.map (fun ω => (X ω, Y ω)) μ = νX.prod νY := by
    exact hind.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable
  calc
    (∫ ω, inner ℝ (X ω) (Y ω) ^ 2 ∂μ) =
        ∫ z, inner ℝ z.1 z.2 ^ 2 ∂(νX.prod νY) := by
      rw [← hjoint, integral_map (hX.prodMk hY).aemeasurable (by fun_prop)]
    _ = ∫ x, ∫ y, inner ℝ x y ^ 2 ∂νY ∂νX := integral_prod _ hcross
    _ ≤ ∫ x, Λ * ‖x‖ ^ 2 ∂νX := by
      apply integral_mono_ae
      · exact hcross.integral_prod_left
      · exact hXnorm.const_mul Λ
      · filter_upwards [] with x
        rw [integral_map hY.aemeasurable (by fun_prop)]
        exact hYmom x
    _ = Λ * ∫ x, ‖x‖ ^ 2 ∂νX := integral_const_mul _ _
    _ ≤ Λ * (M * Λ) := by
      gcongr
      rw [integral_map hX.aemeasurable (by fun_prop)]
      have hparse : (fun ω => ‖X ω‖ ^ 2) = fun ω => ∑ i,
          inner ℝ ((stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin M))) i) (X ω) ^ 2 := by
        funext ω
        exact (stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin M))).sum_sq_inner_right (X ω) |>.symm
      rw [hparse]
      rw [integral_finsetSum _ (fun i _ => (hXL2.const_inner _).integrable_sq)]
      calc
        (∑ i : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin M))), ∫ ω, inner ℝ
            ((stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin M))) i) (X ω) ^ 2 ∂μ) ≤
            ∑ _ : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin M))), Λ := by
          gcongr with i
          simpa using hXmom ((stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin M))) i)
        _ = M * Λ := by simp
    _ = M * Λ ^ 2 := by ring

/-- The squared inner product of two independent square-integrable finite-dimensional vectors is integrable. This statement assumes [the hX condition](hyp:hX), [the hY condition](hyp:hY), [the hXL2 condition](hyp:hXL2), [the hYL2 condition](hyp:hYL2), [the hind condition](hyp:hind). [This is the stated conclusion](goal). -/
lemma integrable_indep_inner_sq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {M : ℕ} [MeasurableSpace (EuclideanSpace ℝ (Fin M))]
    [BorelSpace (EuclideanSpace ℝ (Fin M))]
    (X Y : Ω → EuclideanSpace ℝ (Fin M)) (hX : Measurable X) (hY : Measurable Y)
    (hXL2 : MemLp X 2 μ) (hYL2 : MemLp Y 2 μ) (hind : IndepFun X Y μ) :
    Integrable (fun ω => inner ℝ (X ω) (Y ω) ^ 2) μ := by
  let νX := Measure.map X μ
  let νY := Measure.map Y μ
  have hXnorm : Integrable (fun x : EuclideanSpace ℝ (Fin M) => ‖x‖ ^ 2) νX := by
    dsimp [νX]
    apply (integrable_map_measure (continuous_norm.pow 2 |>.aestronglyMeasurable)
      hX.aemeasurable).2
    simpa [Function.comp_def] using hXL2.norm.integrable_sq
  have hYnorm : Integrable (fun y : EuclideanSpace ℝ (Fin M) => ‖y‖ ^ 2) νY := by
    dsimp [νY]
    apply (integrable_map_measure (continuous_norm.pow 2 |>.aestronglyMeasurable)
      hY.aemeasurable).2
    simpa [Function.comp_def] using hYL2.norm.integrable_sq
  have hcross : Integrable
      (fun z : EuclideanSpace ℝ (Fin M) × EuclideanSpace ℝ (Fin M) =>
        inner ℝ z.1 z.2 ^ 2) (νX.prod νY) := by
    apply (hXnorm.mul_prod hYnorm).mono' (by fun_prop)
    filter_upwards [] with z
    have habs : |inner ℝ z.1 z.2| ≤ ‖z.1‖ * ‖z.2‖ := by
      simpa only [Real.norm_eq_abs] using (norm_inner_le_norm (𝕜 := ℝ) z.1 z.2)
    have hs := (sq_le_sq₀ (abs_nonneg (inner ℝ z.1 z.2))
      (mul_nonneg (norm_nonneg z.1) (norm_nonneg z.2))).2 habs
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs, mul_pow] using hs
  have hjoint : Measure.map (fun ω => (X ω, Y ω)) μ = νX.prod νY :=
    hind.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable
  rw [← hjoint] at hcross
  apply (integrable_map_measure (by fun_prop) (hX.prodMk hY).aemeasurable).1 at hcross
  simpa [Function.comp_def] using hcross

/-- Markov's inequality converts an independent cross-inner-product second-moment envelope into an absolute tail bound. This statement assumes [the hX condition](hyp:hX), [the hY condition](hyp:hY), [the hXL2 condition](hyp:hXL2), [the hYL2 condition](hyp:hYL2), [the hind condition](hyp:hind), [the ha condition](hyp:ha), [the hmom condition](hyp:hmom). [This is the stated conclusion](goal). -/
lemma indep_inner_tail_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {M : ℕ} [MeasurableSpace (EuclideanSpace ℝ (Fin M))]
    [BorelSpace (EuclideanSpace ℝ (Fin M))]
    (X Y : Ω → EuclideanSpace ℝ (Fin M)) (Λ a : ℝ)
    (hX : Measurable X) (hY : Measurable Y) (hXL2 : MemLp X 2 μ) (hYL2 : MemLp Y 2 μ)
    (hind : IndepFun X Y μ) (ha : 0 < a)
    (hmom : (∫ ω, inner ℝ (X ω) (Y ω) ^ 2 ∂μ) ≤ M * Λ ^ 2) :
    μ.real {ω | a < |inner ℝ (X ω) (Y ω)|} ≤ M * Λ ^ 2 / a ^ 2 := by
  exact (Causalean.Stat.Concentration.absolute_error_tail_le_second_moment μ
    (fun ω => inner ℝ (X ω) (Y ω)) a ha
    (integrable_indep_inner_sq μ X Y hX hY hXL2 hYL2 hind)).trans
      (div_le_div_of_nonneg_right hmom (sq_nonneg a))

/-- Projection onto a subspace of dimension at most two has expected squared norm at most twice the common directional second-moment envelope. This statement assumes [the hS condition](hyp:hS), [the hΛ condition](hyp:hΛ), [the hXL2 condition](hyp:hXL2), [the hmom condition](hyp:hmom). [This is the stated conclusion](goal). -/
lemma projection_second_moment_le_two {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {M : ℕ} [MeasurableSpace (EuclideanSpace ℝ (Fin M))]
    [BorelSpace (EuclideanSpace ℝ (Fin M))]
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin M))) (hS : Module.finrank ℝ S ≤ 2)
    (X : Ω → EuclideanSpace ℝ (Fin M)) (Λ : ℝ) (hΛ : 0 ≤ Λ) (hXL2 : MemLp X 2 μ)
    (hmom : ∀ u, (∫ ω, inner ℝ u (X ω) ^ 2 ∂μ) ≤ Λ * ‖u‖ ^ 2) :
    (∫ ω, ‖S.orthogonalProjection (X ω)‖ ^ 2 ∂μ) ≤ 2 * Λ := by
  let b := stdOrthonormalBasis ℝ S
  have heq : (fun ω => ‖S.orthogonalProjection (X ω)‖ ^ 2) = fun ω =>
      ∑ i, inner ℝ ((b i : S)) (S.orthogonalProjection (X ω)) ^ 2 := by
    funext ω
    exact (b.sum_sq_inner_right (S.orthogonalProjection (X ω))).symm
  rw [heq]
  have hi (i : Fin (Module.finrank ℝ S)) : Integrable
      (fun ω => inner ℝ ((b i : S)) (S.orthogonalProjection (X ω)) ^ 2) μ := by
    have he : (fun ω => inner ℝ ((b i : S)) (S.orthogonalProjection (X ω)) ^ 2) =
        fun ω => inner ℝ (b i : EuclideanSpace ℝ (Fin M)) (X ω) ^ 2 := by
      funext ω
      rw [S.inner_orthogonalProjection_eq_of_mem_left]
    rw [he]
    exact (hXL2.const_inner _).integrable_sq
  rw [integral_finsetSum _ (fun i _ => hi i)]
  calc
    (∑ i : Fin (Module.finrank ℝ S), ∫ ω,
        inner ℝ ((b i : S)) (S.orthogonalProjection (X ω)) ^ 2 ∂μ) ≤
        ∑ _ : Fin (Module.finrank ℝ S), Λ := by
      gcongr with i
      rw [show (fun ω => inner ℝ ((b i : S)) (S.orthogonalProjection (X ω)) ^ 2) =
          fun ω => inner ℝ (b i : EuclideanSpace ℝ (Fin M)) (X ω) ^ 2 by
        funext ω
        rw [S.inner_orthogonalProjection_eq_of_mem_left]]
      have h := hmom (b i : EuclideanSpace ℝ (Fin M))
      rw [show ‖(b i : EuclideanSpace ℝ (Fin M))‖ = ‖b i‖ from rfl,
        OrthonormalBasis.norm_eq_one, one_pow, mul_one] at h
      exact h
    _ = Module.finrank ℝ S * Λ := by simp
    _ ≤ 2 * Λ := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hS) hΛ

/-- The squared norm of a finite-dimensional orthogonal projection is integrable whenever the original vector is square integrable. This statement assumes [the hXL2 condition](hyp:hXL2). [This is the stated conclusion](goal). -/
lemma integrable_projection_norm_sq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {M : ℕ} [MeasurableSpace (EuclideanSpace ℝ (Fin M))]
    [BorelSpace (EuclideanSpace ℝ (Fin M))]
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin M)))
    (X : Ω → EuclideanSpace ℝ (Fin M)) (hXL2 : MemLp X 2 μ) :
    Integrable (fun ω => ‖S.orthogonalProjection (X ω)‖ ^ 2) μ := by
  let b := stdOrthonormalBasis ℝ S
  have heq : (fun ω => ‖S.orthogonalProjection (X ω)‖ ^ 2) = fun ω =>
      ∑ i, inner ℝ ((b i : S)) (S.orthogonalProjection (X ω)) ^ 2 := by
    funext ω
    exact (b.sum_sq_inner_right (S.orthogonalProjection (X ω))).symm
  rw [heq]
  apply integrable_finsetSum
  intro i hi
  have he : (fun ω => inner ℝ ((b i : S)) (S.orthogonalProjection (X ω)) ^ 2) =
      fun ω => inner ℝ (b i : EuclideanSpace ℝ (Fin M)) (X ω) ^ 2 := by
    funext ω
    rw [S.inner_orthogonalProjection_eq_of_mem_left]
  rw [he]
  exact (hXL2.const_inner _).integrable_sq

/-- A rank-at-most-two projection obeys the Markov tail bound obtained from its directional second-moment envelope. This statement assumes [the hS condition](hyp:hS), [the hΛ condition](hyp:hΛ), [the ha condition](hyp:ha), [the hXL2 condition](hyp:hXL2), [the hmom condition](hyp:hmom). [This is the stated conclusion](goal). -/
lemma projection_norm_tail_le_two {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {M : ℕ} [MeasurableSpace (EuclideanSpace ℝ (Fin M))]
    [BorelSpace (EuclideanSpace ℝ (Fin M))]
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin M))) (hS : Module.finrank ℝ S ≤ 2)
    (X : Ω → EuclideanSpace ℝ (Fin M)) (Λ a : ℝ) (hΛ : 0 ≤ Λ) (ha : 0 < a)
    (hXL2 : MemLp X 2 μ)
    (hmom : ∀ u, (∫ ω, inner ℝ u (X ω) ^ 2 ∂μ) ≤ Λ * ‖u‖ ^ 2) :
    μ.real {ω | a < ‖S.orthogonalProjection (X ω)‖} ≤ 2 * Λ / a ^ 2 := by
  have ht := Causalean.Stat.Concentration.absolute_error_tail_le_second_moment μ
    (fun ω => ‖S.orthogonalProjection (X ω)‖) a ha
    (integrable_projection_norm_sq μ S X hXL2)
  change (μ {ω | a < ‖S.orthogonalProjection (X ω)‖}).toReal ≤ 2 * Λ / a ^ 2
  simpa only [abs_norm] using ht.trans (div_le_div_of_nonneg_right
    (projection_second_moment_le_two μ S hS X Λ hΛ hXL2 hmom) (sq_nonneg a))

end Causalean.Stat.Concentration
