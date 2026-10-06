/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-! # Absolute continuity of finite product measures

This file provides product-measure Radon--Nikodym factorization and the
absolute-continuity side condition for finite i.i.d. product measures. These
results are independent of statistical divergence constructions and can
therefore be reused by Mathlib-adjacent probability developments.
-/

public section

namespace Causalean.Mathlib.Probability.ProductAbsolutelyContinuous

open MeasureTheory

section ProductDensity

variable {α : Type*} {mα : MeasurableSpace α} {β : Type*} {mβ : MeasurableSpace β}

/-- **Product density factorization.** For `μ₁ ≪ ν₁` and `μ₂ ≪ ν₂`, the Radon–Nikodym
density of the product is (a.e.) the product of the marginal densities. -/
theorem rnDeriv_prod_eq (μ₁ ν₁ : Measure α) (μ₂ ν₂ : Measure β)
    [SigmaFinite ν₁] [SigmaFinite ν₂] [SFinite ν₂]
    [μ₁.HaveLebesgueDecomposition ν₁] [μ₂.HaveLebesgueDecomposition ν₂]
    (h₁ : μ₁ ≪ ν₁) (h₂ : μ₂ ≪ ν₂) :
    (μ₁.prod μ₂).rnDeriv (ν₁.prod ν₂)
      =ᵐ[ν₁.prod ν₂]
        fun z => μ₁.rnDeriv ν₁ z.1 * μ₂.rnDeriv ν₂ z.2 := by
  -- Rewrite `μᵢ = νᵢ.withDensity (rnDeriv μᵢ νᵢ)` and use `prod_withDensity₀`.
  have hfac : μ₁.prod μ₂
      = (ν₁.prod ν₂).withDensity (fun z => μ₁.rnDeriv ν₁ z.1 * μ₂.rnDeriv ν₂ z.2) := by
    conv_lhs =>
      rw [← Measure.withDensity_rnDeriv_eq _ _ h₁, ← Measure.withDensity_rnDeriv_eq _ _ h₂]
    exact prod_withDensity₀ (Measure.measurable_rnDeriv _ _).aemeasurable
      (Measure.measurable_rnDeriv _ _).aemeasurable
  calc (μ₁.prod μ₂).rnDeriv (ν₁.prod ν₂)
      =ᵐ[ν₁.prod ν₂]
        ((ν₁.prod ν₂).withDensity
          (fun z => μ₁.rnDeriv ν₁ z.1 * μ₂.rnDeriv ν₂ z.2)).rnDeriv (ν₁.prod ν₂) := by
        rw [hfac]
    _ =ᵐ[ν₁.prod ν₂] fun z => μ₁.rnDeriv ν₁ z.1 * μ₂.rnDeriv ν₂ z.2 :=
        Measure.rnDeriv_withDensity₀ _
          (((Measure.measurable_rnDeriv _ _).comp measurable_fst).mul
            ((Measure.measurable_rnDeriv _ _).comp measurable_snd)).aemeasurable

end ProductDensity

/-- For [two σ-finite measures μ and ν on the same space](hyp:μ,ν) with
[μ absolutely continuous with respect to ν](hyp:hac), [the n-fold product of μ is
absolutely continuous with respect to the n-fold product of ν](goal), [for every
number of factors n](hyp:n).

Proved by induction via the `piFinSuccAbove` equivalence and the binary
`AbsolutelyContinuous.prod`. -/
theorem pi_iid_absolutelyContinuous {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [SigmaFinite μ] [SigmaFinite ν] (hac : μ ≪ ν) (n : ℕ) :
    Measure.pi (fun _ : Fin n => μ) ≪ Measure.pi (fun _ : Fin n => ν) := by
  induction n with
  | zero =>
    rw [Measure.pi_of_empty (fun _ : Fin 0 => μ), Measure.pi_of_empty (fun _ : Fin 0 => ν)]
  | succ n ih =>
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Ω) 0 with he
    have hμ := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).map_eq
    have hν := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) 0).map_eq
    have hprod : μ.prod (Measure.pi (fun _ : Fin n => μ))
        ≪ ν.prod (Measure.pi (fun _ : Fin n => ν)) := hac.prod ih
    have hmap : (Measure.pi (fun _ : Fin (n + 1) => μ)).map e
        ≪ (Measure.pi (fun _ : Fin (n + 1) => ν)).map e := by
      rw [hμ, hν]; exact hprod
    have hmapped := hmap.map (f := e.symm) e.symm.measurable
    rwa [Measure.map_map e.symm.measurable e.measurable,
      MeasurableEquiv.symm_comp_self, Measure.map_id,
      Measure.map_map e.symm.measurable e.measurable,
      MeasurableEquiv.symm_comp_self, Measure.map_id] at hmapped

end Causalean.Mathlib.Probability.ProductAbsolutelyContinuous
