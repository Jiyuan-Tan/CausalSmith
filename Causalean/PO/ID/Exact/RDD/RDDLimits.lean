/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.PO.Analysis.Regression
public import Mathlib.Topology.Order.Basic

/-! # RDD One-Sided Limits

This file provides the one-sided limit engine used by sharp and fuzzy
regression-discontinuity identification. If two real-valued functions agree
almost everywhere on the relevant side of a cutoff and the reference function
is continuous at the cutoff, then any corresponding one-sided limit of the
other function equals the reference value at the cutoff, provided the running
variable law has positive mass arbitrarily close to that side.

Theorems `oneSidedLimit_eq_right` and `oneSidedLimit_eq_left` identify
right- and left-hand limits from one-sided a.e. agreement. The pointwise
versions `value_eq_of_aeEq_right` and `value_eq_of_aeEq_left` identify the
cutoff values of two continuous representatives. These results isolate the
topological and measure-theoretic argument from the causal RDD files. -/

public section

namespace Causalean
namespace PO
namespace RDDLimits

open Filter MeasureTheory
open scoped Topology

variable {π : Measure ℝ} {f g : ℝ → ℝ} {c : ℝ}

/-- [Almost-everywhere agreement on the right half-line](hyp:h_aeEq) and [positive
running-variable mass in every right neighborhood](hyp:h_support) ensure that [each
positive-width neighborhood](hyp:hε) [contains a point where the two regression
representatives agree](goal); this supplies the sequence of agreement points needed for
cutoff-limit identification. -/
private lemma exists_eq_in_Ioo_right
    (h_aeEq : f =ᵐ[π.restrict (Set.Ici c)] g)
    (h_support : ∀ ε > (0 : ℝ), π (Set.Ioo c (c + ε)) ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ Set.Ioo c (c + ε), f x = g x := by
  have hsubset : Set.Ioo c (c + ε) ⊆ Set.Ici c := fun x hx => le_of_lt hx.1
  have h_le : π.restrict (Set.Ioo c (c + ε)) ≤ π.restrict (Set.Ici c) :=
    Measure.restrict_mono hsubset le_rfl
  have h_ae_Ioo : f =ᵐ[π.restrict (Set.Ioo c (c + ε))] g :=
    h_aeEq.filter_mono (ae_mono h_le)
  exact Measure.exists_mem_of_measure_ne_zero_of_ae (h_support ε hε) h_ae_Ioo

private lemma exists_eq_in_Ioo_left
    (h_aeEq : f =ᵐ[π.restrict (Set.Iio c)] g)
    (h_support : ∀ ε > (0 : ℝ), π (Set.Ioo (c - ε) c) ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ Set.Ioo (c - ε) c, f x = g x := by
  have hsubset : Set.Ioo (c - ε) c ⊆ Set.Iio c := fun x hx => hx.2
  have h_le : π.restrict (Set.Ioo (c - ε) c) ≤ π.restrict (Set.Iio c) :=
    Measure.restrict_mono hsubset le_rfl
  have h_ae_Ioo : f =ᵐ[π.restrict (Set.Ioo (c - ε) c)] g :=
    h_aeEq.filter_mono (ae_mono h_le)
  exact Measure.exists_mem_of_measure_ne_zero_of_ae (h_support ε hε) h_ae_Ioo

private lemma neBot_right
    (h_aeEq : f =ᵐ[π.restrict (Set.Ici c)] g)
    (h_support : ∀ ε > (0 : ℝ), π (Set.Ioo c (c + ε)) ≠ 0) :
    (𝓝[>] c ⊓ Filter.principal {x | f x = g x}).NeBot := by
  rw [Filter.neBot_iff, Ne, Filter.inf_principal_eq_bot]
  intro hbot
  rcases mem_nhdsGT_iff_exists_Ioo_subset.1 hbot with ⟨b, hcb, hsub⟩
  set ε : ℝ := b - c
  have hε : 0 < ε := sub_pos.mpr hcb
  have hbeq : c + ε = b := by simp [ε]
  rcases exists_eq_in_Ioo_right h_aeEq h_support hε with ⟨x, hx_mem, hx_eq⟩
  rw [hbeq] at hx_mem
  exact hsub hx_mem hx_eq

private lemma neBot_left
    (h_aeEq : f =ᵐ[π.restrict (Set.Iio c)] g)
    (h_support : ∀ ε > (0 : ℝ), π (Set.Ioo (c - ε) c) ≠ 0) :
    (𝓝[<] c ⊓ Filter.principal {x | f x = g x}).NeBot := by
  rw [Filter.neBot_iff, Ne, Filter.inf_principal_eq_bot]
  intro hbot
  rcases mem_nhdsLT_iff_exists_Ioo_subset.1 hbot with ⟨a, hac, hsub⟩
  set ε : ℝ := c - a
  have hε : 0 < ε := sub_pos.mpr hac
  have haeq : c - ε = a := by simp [ε]
  rcases exists_eq_in_Ioo_left h_aeEq h_support hε with ⟨x, hx_mem, hx_eq⟩
  rw [haeq] at hx_mem
  exact hsub hx_mem hx_eq

/-- **Right-side limit identification.** If [the observable regression agrees almost
everywhere with a reference regression to the right of the cutoff](hyp:h_aeEq), [the
reference is continuous at the cutoff](hyp:hg_cont), and [the running-variable law has
positive mass arbitrarily close on the right](hyp:h_support), then [any right-hand limit
of the observable regression](hyp:hL) [must equal the reference value at the
cutoff](goal). This turns one-sided a.e. regression agreement into an identified cutoff
limit. -/
theorem oneSidedLimit_eq_right
    (h_aeEq : f =ᵐ[π.restrict (Set.Ici c)] g)
    (hg_cont : ContinuousAt g c)
    (h_support : ∀ ε > (0 : ℝ), π (Set.Ioo c (c + ε)) ≠ 0)
    {L : ℝ} (hL : Tendsto f (𝓝[>] c) (𝓝 L)) :
    L = g c := by
  haveI : (𝓝[>] c ⊓ Filter.principal {x | f x = g x}).NeBot :=
    neBot_right h_aeEq h_support
  have h_f :
      Tendsto f
        (𝓝[>] c ⊓ Filter.principal {x | f x = g x})
        (𝓝 L) := hL.mono_left inf_le_left
  have h_g_full :
      Tendsto g (𝓝[>] c) (𝓝 (g c)) :=
    hg_cont.tendsto.mono_left inf_le_left
  have h_g :
      Tendsto g
        (𝓝[>] c ⊓ Filter.principal {x | f x = g x})
        (𝓝 (g c)) := h_g_full.mono_left inf_le_left
  have h_eq :
      f =ᶠ[𝓝[>] c ⊓ Filter.principal {x | f x = g x}] g := by
    refine Filter.eventually_iff_exists_mem.mpr ?_
    refine ⟨{x | f x = g x}, ?_, fun x hx => hx⟩
    exact mem_inf_of_right (mem_principal_self _)
  have h_f' :
      Tendsto g
        (𝓝[>] c ⊓ Filter.principal {x | f x = g x})
        (𝓝 L) := h_f.congr' h_eq
  exact tendsto_nhds_unique h_f' h_g

/-- **Left-side limit identification.** Symmetric form of `oneSidedLimit_eq_right`. If
[a real-valued function `f` agrees with a reference function `g` almost everywhere, with
respect to a measure `π`, on the half-line to the left of the cutoff `c`](hyp:h_aeEq),
[`g` is continuous at `c`](hyp:hg_cont), and [every open interval immediately to the left
of `c` has positive `π`-measure](hyp:h_support), then [any left-hand limit `L` of `f`
at `c`](hyp:hL) [must equal `g` evaluated at `c`](goal). -/
theorem oneSidedLimit_eq_left
    (h_aeEq : f =ᵐ[π.restrict (Set.Iio c)] g)
    (hg_cont : ContinuousAt g c)
    (h_support : ∀ ε > (0 : ℝ), π (Set.Ioo (c - ε) c) ≠ 0)
    {L : ℝ} (hL : Tendsto f (𝓝[<] c) (𝓝 L)) :
    L = g c := by
  haveI : (𝓝[<] c ⊓ Filter.principal {x | f x = g x}).NeBot :=
    neBot_left h_aeEq h_support
  have h_f :
      Tendsto f
        (𝓝[<] c ⊓ Filter.principal {x | f x = g x})
        (𝓝 L) := hL.mono_left inf_le_left
  have h_g_full :
      Tendsto g (𝓝[<] c) (𝓝 (g c)) :=
    hg_cont.tendsto.mono_left inf_le_left
  have h_g :
      Tendsto g
        (𝓝[<] c ⊓ Filter.principal {x | f x = g x})
        (𝓝 (g c)) := h_g_full.mono_left inf_le_left
  have h_eq :
      f =ᶠ[𝓝[<] c ⊓ Filter.principal {x | f x = g x}] g := by
    refine Filter.eventually_iff_exists_mem.mpr ?_
    refine ⟨{x | f x = g x}, ?_, fun x hx => hx⟩
    exact mem_inf_of_right (mem_principal_self _)
  have h_f' :
      Tendsto g
        (𝓝[<] c ⊓ Filter.principal {x | f x = g x})
        (𝓝 L) := h_f.congr' h_eq
  exact tendsto_nhds_unique h_f' h_g

/-- **Pointwise equality from right-side agreement.** If [two regression
representatives agree almost everywhere to the right of the cutoff](hyp:h_aeEq), [the
first is continuous there](hyp:hf_cont), [the second is continuous there](hyp:hg_cont),
and [the running-variable law has positive mass arbitrarily close on the
right](hyp:h_support), then [their cutoff values coincide](goal). -/
theorem value_eq_of_aeEq_right
    (h_aeEq : f =ᵐ[π.restrict (Set.Ici c)] g)
    (hf_cont : ContinuousAt f c) (hg_cont : ContinuousAt g c)
    (h_support : ∀ ε > (0 : ℝ), π (Set.Ioo c (c + ε)) ≠ 0) :
    f c = g c := by
  have hL : Tendsto f (𝓝[>] c) (𝓝 (f c)) :=
    hf_cont.tendsto.mono_left nhdsWithin_le_nhds
  exact oneSidedLimit_eq_right h_aeEq hg_cont h_support hL

/-- **Pointwise equality from left-side agreement.** If [two regression
representatives agree almost everywhere to the left of the cutoff](hyp:h_aeEq), [the
first is continuous there](hyp:hf_cont), [the second is continuous there](hyp:hg_cont),
and [the running-variable law has positive mass arbitrarily close on the
left](hyp:h_support), then [their cutoff values coincide](goal). -/
theorem value_eq_of_aeEq_left
    (h_aeEq : f =ᵐ[π.restrict (Set.Iio c)] g)
    (hf_cont : ContinuousAt f c) (hg_cont : ContinuousAt g c)
    (h_support : ∀ ε > (0 : ℝ), π (Set.Ioo (c - ε) c) ≠ 0) :
    f c = g c := by
  have hL : Tendsto f (𝓝[<] c) (𝓝 (f c)) :=
    hf_cont.tendsto.mono_left nhdsWithin_le_nhds
  exact oneSidedLimit_eq_left h_aeEq hg_cont h_support hL

end RDDLimits
end PO
end Causalean
