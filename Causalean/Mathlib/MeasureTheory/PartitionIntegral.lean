/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Finite-partition integral algebra

This file decomposes integrals over the measurable fibres of a finite-valued map and proves that
weights constant on each fibre can be pulled outside the corresponding fibre integral.

The public lemmas are `integral_eq_sum_setIntegral_fiber`, `integral_cellConst_mul`, and
`integral_cellConst`, which turn a finite partition into finite sums of set integrals or fibre
weights.
-/

public section

-- `open` BEFORE the namespace: inside `namespace Causalean.Mathlib.MeasureTheory`
-- the token `MeasureTheory` would resolve to this local namespace and shadow the
-- real one, so open the root MeasureTheory here at top level (cf. IntegralBind).
open MeasureTheory

namespace Causalean.Mathlib.MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Fiber partition of `univ` -/

/-- The fibers of `H` are measurable. -/
private theorem measurableSet_fiber {ι : Type*} [MeasurableSpace ι]
    [MeasurableSingletonClass ι] {H : Ω → ι} (hH : Measurable H) (h : ι) :
    MeasurableSet (H ⁻¹' {h}) :=
  hH (measurableSet_singleton h)

omit [MeasurableSpace Ω] in
/-- The fibers of `H` are pairwise disjoint. -/
private theorem pairwise_disjoint_fiber {ι : Type*} (H : Ω → ι) :
    Pairwise (Function.onFun Disjoint (fun h => H ⁻¹' {h})) := by
  intro a b hab
  simp only [Function.onFun]
  rw [Set.disjoint_left]
  intro ω ha hb
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at ha hb
  exact hab (ha.symm.trans hb)

omit [MeasurableSpace Ω] in
/-- The fibers of `H` cover the whole space. -/
private theorem iUnion_fiber {ι : Type*} (H : Ω → ι) : (⋃ h, H ⁻¹' {h}) = Set.univ := by
  ext ω
  simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  exact ⟨H ω, rfl⟩

/-! ## Integral decomposition over fibers -/

/-- [The integral of a function is the sum of its integrals over the fibres of a finite-valued
map](goal) when [every fibre is measurable](hyp:hfiber) and [the function is
integrable](hyp:hf). -/
theorem integral_eq_sum_setIntegral_fiber {ι : Type*} [Fintype ι]
    {H : Ω → ι} (hfiber : ∀ h, MeasurableSet (H ⁻¹' {h}))
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Ω → E} (hf : Integrable f μ) :
    ∫ ω, f ω ∂μ = ∑ h : ι, ∫ ω in H ⁻¹' {h}, f ω ∂μ := by
  have hsplit :
      ∫ ω in ⋃ h, H ⁻¹' {h}, f ω ∂μ = ∑ h : ι, ∫ ω in H ⁻¹' {h}, f ω ∂μ :=
    MeasureTheory.integral_iUnion_fintype hfiber
      (pairwise_disjoint_fiber H) (fun _ => hf.integrableOn)
  calc
    ∫ ω, f ω ∂μ = ∫ ω in (Set.univ : Set Ω), f ω ∂μ := by rw [setIntegral_univ]
    _ = ∫ ω in ⋃ h, H ⁻¹' {h}, f ω ∂μ := by rw [iUnion_fiber]
    _ = ∑ h : ι, ∫ ω in H ⁻¹' {h}, f ω ∂μ := hsplit

/-- [A function weighted by a constant on each fibre integrates as the sum of the fibre
integrals with their corresponding weights](goal) when [every fibre is
measurable](hyp:hfiber), [the weighting assigns a real number to each fibre](hyp:c), and [the
function is integrable](hyp:hf).

The identity requires no measurability of `c`, because it is constant on each fiber. -/
theorem integral_cellConst_mul {ι : Type*} [Fintype ι]
    {H : Ω → ι} (hfiber : ∀ h, MeasurableSet (H ⁻¹' {h})) (c : ι → ℝ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Ω → E} (hf : Integrable f μ) :
    ∫ ω, c (H ω) • f ω ∂μ = ∑ h : ι, c h • ∫ ω in H ⁻¹' {h}, f ω ∂μ := by
  -- On each fiber the integrand equals the constant-multiple `c h • f`.
  have hgint : ∀ h : ι, IntegrableOn (fun ω => c (H ω) • f ω) (H ⁻¹' {h}) μ := by
    intro h
    refine ((hf.smul (c h)).integrableOn).congr_fun ?_ (hfiber h)
    intro ω hω
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hω
    simp [hω]
  have hsplit :
      ∫ ω in ⋃ h, H ⁻¹' {h}, c (H ω) • f ω ∂μ
        = ∑ h : ι, ∫ ω in H ⁻¹' {h}, c (H ω) • f ω ∂μ :=
    MeasureTheory.integral_iUnion_fintype hfiber
      (pairwise_disjoint_fiber H) hgint
  calc
    ∫ ω, c (H ω) • f ω ∂μ
        = ∫ ω in (Set.univ : Set Ω), c (H ω) • f ω ∂μ := by rw [setIntegral_univ]
    _ = ∫ ω in ⋃ h, H ⁻¹' {h}, c (H ω) • f ω ∂μ := by rw [iUnion_fiber]
    _ = ∑ h : ι, ∫ ω in H ⁻¹' {h}, c (H ω) • f ω ∂μ := hsplit
    _ = ∑ h : ι, c h • ∫ ω in H ⁻¹' {h}, f ω ∂μ := by
        refine Finset.sum_congr rfl fun h _ => ?_
        have hcell :
            ∫ ω in H ⁻¹' {h}, c (H ω) • f ω ∂μ = ∫ ω in H ⁻¹' {h}, c h • f ω ∂μ := by
          refine setIntegral_congr_fun (hfiber h) ?_
          intro ω hω
          simp only [Set.mem_preimage, Set.mem_singleton_iff] at hω
          simp [hω]
        rw [hcell, integral_smul]

/-- [The integral of a function constant on each fibre is the sum of each constant times the
measure of its fibre](goal) for a finite measure, provided [every fibre is
measurable](hyp:hfiber) and [a real weight is assigned to each fibre](hyp:c). This is the
constant-function case of `integral_cellConst_mul`. -/
theorem integral_cellConst {ι : Type*} [Fintype ι]
    [IsFiniteMeasure μ] {H : Ω → ι}
    (hfiber : ∀ h, MeasurableSet (H ⁻¹' {h})) (c : ι → ℝ) :
    ∫ ω, c (H ω) ∂μ = ∑ h : ι, c h * (μ (H ⁻¹' {h})).toReal := by
  have h := integral_cellConst_mul hfiber c
    (f := fun _ => (1 : ℝ)) (hf := (integrable_const (1 : ℝ) : Integrable (fun _ : Ω => (1 : ℝ)) μ))
  simpa [mul_one, setIntegral_const, smul_eq_mul, measureReal_def] using h

end Causalean.Mathlib.MeasureTheory
