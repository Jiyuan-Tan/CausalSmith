/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-!
# Bounded centered functions are dense in mean-zero L²

For a probability measure `μ`, this file realizes `L²₀(μ)` as the orthogonal
complement of the constant-one function. It centers the dense subspace of L²
simple functions and proves that the resulting bounded, measurable, mean-zero
functions are dense in `L²₀(μ)`.

This is the functional-analytic density step used to generate nonparametric
tangent spaces from bounded exponential tilts.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped InnerProductSpace RealInnerProductSpace

namespace Causalean.Mathlib.MeasureTheory

variable {α : Type*} [MeasurableSpace α]

/-- For [a probability measure `μ`](hyp:μ), the [constant-one vector in `L²(μ)`](goal) is the
L² equivalence class of the function equal to one everywhere. -/
noncomputable def lpOne (μ : Measure α) [IsProbabilityMeasure μ] : Lp ℝ 2 μ :=
  (memLp_const (1 : ℝ)).toLp _

/-- For [a probability measure `μ`](hyp:μ), the [mean-zero subspace of `L²(μ)`](goal) is the
orthogonal complement of the span of the constant-one vector. -/
noncomputable def meanZeroLp (μ : Measure α) [IsProbabilityMeasure μ] :
    Submodule ℝ (Lp ℝ 2 μ) :=
  (ℝ ∙ lpOne μ)ᗮ

/-- For [a measure `μ`](hyp:μ), the [real linear subspace of `L²(μ)` represented by measurable
simple functions](goal) consists exactly of Mathlib's L² simple-function classes. -/
def lpSimpleFuncSubmodule (μ : Measure α) : Submodule ℝ (Lp ℝ 2 μ) where
  carrier := Lp.simpleFunc ℝ 2 μ
  zero_mem' := (Lp.simpleFunc ℝ 2 μ).zero_mem
  add_mem' := (Lp.simpleFunc ℝ 2 μ).add_mem
  smul_mem' := by
    rintro c f ⟨s, hs⟩
    refine ⟨c • s, ?_⟩
    change AEEqFun.mk (c • (s : α → ℝ)) _ = c • (f : α →ₘ[μ] ℝ)
    rw [← hs]
    exact (AEEqFun.smul_mk c s s.aestronglyMeasurable).symm

/-- For [a probability measure `μ`](hyp:μ), the [continuous L² centering operator](goal)
subtracts the constant component of a square-integrable function. -/
noncomputable def lpCenter (μ : Measure α) [IsProbabilityMeasure μ] :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  ContinuousLinearMap.id ℝ _ -
    InnerProductSpace.rankOne ℝ (lpOne μ) (lpOne μ)

/-- For [a probability measure `μ`](hyp:μ), the [bounded centered L² subspace](goal) is the image
of the simple-function subspace under the continuous centering operator. -/
noncomputable def boundedCenteredLp (μ : Measure α) [IsProbabilityMeasure μ] :
    Submodule ℝ (Lp ℝ 2 μ) :=
  (lpSimpleFuncSubmodule μ).map (lpCenter μ : Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 μ)

private theorem lpSimpleFuncSubmodule_dense (μ : Measure α) :
    (lpSimpleFuncSubmodule μ).topologicalClosure = ⊤ := by
  rw [← Submodule.dense_iff_topologicalClosure_eq_top]
  simpa [lpSimpleFuncSubmodule] using
    (Lp.simpleFunc.dense (E := ℝ) (μ := μ) (p := 2) (by norm_num))

private theorem inner_lpOne_self (μ : Measure α) [IsProbabilityMeasure μ] :
    ⟪lpOne μ, lpOne μ⟫_ℝ = 1 := by
  rw [L2.inner_def]
  calc
    (∫ a : α, ⟪(lpOne μ) a, (lpOne μ) a⟫_ℝ ∂μ)
        = ∫ _a : α, (1 : ℝ) ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [(memLp_const (1 : ℝ)).coeFn_toLp (p := 2) (μ := μ)]
            with x hx
          rw [show lpOne μ x = (1 : ℝ) from hx]
          simp
    _ = 1 := by simp

/-- Under [a probability measure `μ`](hyp:μ), [inner product with the constant-one L² vector
equals integration](goal): `⟪f, 1⟫ = ∫ f dμ`. -/
theorem inner_lpOne_eq_integral (μ : Measure α) [IsProbabilityMeasure μ]
    (f : Lp ℝ 2 μ) :
    ⟪f, lpOne μ⟫_ℝ = ∫ z, f z ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_const (1 : ℝ)).coeFn_toLp (p := 2) (μ := μ)] with z hz
  rw [show lpOne μ z = (1 : ℝ) from hz]
  simp

private theorem lpCenter_mem_meanZeroLp (μ : Measure α) [IsProbabilityMeasure μ]
    (f : Lp ℝ 2 μ) : lpCenter μ f ∈ meanZeroLp μ := by
  rw [meanZeroLp, Submodule.mem_orthogonal_singleton_iff_inner_left]
  rw [lpCenter, sub_apply, ContinuousLinearMap.id_apply,
    InnerProductSpace.rankOne_apply]
  rw [inner_sub_left, inner_smul_left, inner_lpOne_self]
  simp [real_inner_comm]

private theorem lpCenter_eq_self_of_mem (μ : Measure α) [IsProbabilityMeasure μ]
    (f : Lp ℝ 2 μ) (hf : f ∈ meanZeroLp μ) : lpCenter μ f = f := by
  rw [meanZeroLp, Submodule.mem_orthogonal_singleton_iff_inner_left] at hf
  simp [lpCenter, InnerProductSpace.rankOne_apply, real_inner_comm, hf]

private theorem range_lpCenter (μ : Measure α) [IsProbabilityMeasure μ] :
    LinearMap.range (lpCenter μ : Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 μ) = meanZeroLp μ := by
  ext f
  constructor
  · rintro ⟨x, rfl⟩
    exact lpCenter_mem_meanZeroLp μ x
  · intro hf
    exact ⟨f, lpCenter_eq_self_of_mem μ f hf⟩

private theorem lpOne_mem_simple (μ : Measure α) [IsProbabilityMeasure μ] :
    lpOne μ ∈ lpSimpleFuncSubmodule μ := by
  change ∃ s : SimpleFunc α ℝ,
    AEEqFun.mk s s.aestronglyMeasurable = (lpOne μ : α →ₘ[μ] ℝ)
  refine ⟨SimpleFunc.const α (1 : ℝ), ?_⟩
  rfl

private theorem lpCenter_mem_simple (μ : Measure α) [IsProbabilityMeasure μ]
    (f : Lp ℝ 2 μ) (hf : f ∈ lpSimpleFuncSubmodule μ) :
    lpCenter μ f ∈ lpSimpleFuncSubmodule μ := by
  change f - ⟪lpOne μ, f⟫_ℝ • lpOne μ ∈ lpSimpleFuncSubmodule μ
  exact (lpSimpleFuncSubmodule μ).sub_mem hf
    ((lpSimpleFuncSubmodule μ).smul_mem _ (lpOne_mem_simple μ))

/-- For [a probability measure `μ`](hyp:μ), [centered bounded measurable functions are dense in
the mean-zero subspace of `L²(μ)`](goal): the topological closure of centered L² simple functions
is exactly the orthogonal complement of the constants.

This density result supplies an ingredient for the construction in van der Vaart (1998),
Example 25.16, which builds differentiable parametric submodels with prescribed L²₀ scores to
identify the full-model tangent set; it is not itself that example's full statement. -/
theorem boundedCenteredLp_topologicalClosure (μ : Measure α) [IsProbabilityMeasure μ] :
    (boundedCenteredLp μ).topologicalClosure = meanZeroLp μ := by
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · rintro f ⟨x, _hx, rfl⟩
      exact lpCenter_mem_meanZeroLp μ x
    · exact Submodule.isClosed_orthogonal (ℝ ∙ lpOne μ)
  · have hmap := (lpSimpleFuncSubmodule μ).topologicalClosure_map (lpCenter μ)
    rw [lpSimpleFuncSubmodule_dense, Submodule.map_top, range_lpCenter] at hmap
    exact hmap

/-- If [an L² vector belongs to the centered-simple subspace](hyp:hf) under [a probability
measure `μ`](hyp:μ), then [it has an everywhere measurable, everywhere bounded, mean-zero
representative](goal) whose L² class is that vector. -/
theorem mem_boundedCenteredLp_exists (μ : Measure α) [IsProbabilityMeasure μ]
    (f : Lp ℝ 2 μ) (hf : f ∈ boundedCenteredLp μ) :
    ∃ (g : α → ℝ) (M : ℝ) (hg : MemLp g 2 μ), Measurable g ∧
      (∀ z, |g z| ≤ M) ∧ (∫ z, g z ∂μ) = 0 ∧ hg.toLp g = f := by
  rcases hf with ⟨x, hx, rfl⟩
  let sf : Lp.simpleFunc ℝ 2 μ := ⟨lpCenter μ x, lpCenter_mem_simple μ x hx⟩
  let g : α → ℝ := Lp.simpleFunc.toSimpleFunc sf
  obtain ⟨M, hM⟩ :=
    SimpleFunc.exists_forall_norm_le (Lp.simpleFunc.toSimpleFunc sf)
  have hg : MemLp g 2 μ := Lp.simpleFunc.memLp sf
  refine ⟨g, M, hg, Lp.simpleFunc.measurable sf, ?_, ?_, ?_⟩
  · intro z
    simpa [g, Real.norm_eq_abs] using hM z
  · have hzero : ∫ z, (sf : Lp ℝ 2 μ) z ∂μ = 0 := by
      rw [← inner_lpOne_eq_integral]
      exact Submodule.mem_orthogonal_singleton_iff_inner_left.mp
        (show (sf : Lp ℝ 2 μ) ∈ meanZeroLp μ from lpCenter_mem_meanZeroLp μ x)
    exact (integral_congr_ae (Lp.simpleFunc.toSimpleFunc_eq_toFun sf)).trans hzero
  · exact congrArg Subtype.val (Lp.simpleFunc.toLp_toSimpleFunc sf)

end Causalean.Mathlib.MeasureTheory
