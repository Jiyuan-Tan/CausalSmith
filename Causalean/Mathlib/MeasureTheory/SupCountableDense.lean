/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Integrability of suprema over a countable-dense-skeletoned index class

This file proves measurability and integrability of pointwise suprema over arbitrary index sets by
reducing them to uniformly bounded families on countable dense skeletons.

The API works on an arbitrary measurable space and reduces measurability and
Bochner-integrability side conditions to countable suprema.

Main results:
* `sSup_image_eq_of_dense_tendsto` — for a real functional `F` bounded above on `S`, if
  every `x ∈ S` is reached by a `D`-valued sequence along which `F` converges to `F x`,
  then the supremum over `S` equals the supremum over the countable skeleton `D`.
* `measurable_sSup_image_of_countable_dense` — the pointwise supremum `ω ↦ sSup (F ω '' S)`
  is measurable, given a countable `D`, per-index measurability on `D`, and the skeleton
  supremum-equality for every `ω`.
* `integrable_sSup_image_of_countable_dense` — on a finite measure, the same supremum is
  integrable, given in addition a uniform bound `|F ω π| ≤ C` over `S`; the accompanying
  `bddAbove_image_of_bound` supplies the pointwise `BddAbove` fact for free.
-/

public section

open MeasureTheory
open scoped BigOperators

namespace Causalean.Mathlib.MeasureTheory

/-- [A supremum over an index set equals the supremum over a dense skeleton](goal) when [the
real functional](hyp:F) is [bounded above on the full set](hyp:S,hbdd), [the skeleton lies
inside that set](hyp:D,hDS), and [every full-set value is approached along a skeleton-valued
sequence](hyp:hdense). -/
theorem sSup_image_eq_of_dense_tendsto {ι : Type*} (F : ι → ℝ) (S D : Set ι)
    (hDS : D ⊆ S) (hbdd : BddAbove (F '' S))
    (hdense : ∀ x ∈ S, ∃ seq : ℕ → ι, (∀ j, seq j ∈ D) ∧
      Filter.Tendsto (fun j => F (seq j)) Filter.atTop (nhds (F x))) :
    sSup (F '' S) = sSup (F '' D) := by
  classical
  by_cases hS : S = ∅
  · have hD : D = ∅ := Set.eq_empty_of_subset_empty (by simpa [hS] using hDS)
    simp [hS, hD]
  · obtain ⟨x0, hx0⟩ := Set.nonempty_iff_ne_empty.mpr hS
    obtain ⟨seq, hseqD, _⟩ := hdense x0 hx0
    have hDne : D.Nonempty := ⟨seq 0, hseqD 0⟩
    have himageDne : (F '' D).Nonempty := hDne.image F
    have hbddD : BddAbove (F '' D) := hbdd.mono (Set.image_mono hDS)
    apply le_antisymm
    · refine csSup_le (Set.image_nonempty.mpr ⟨x0, hx0⟩) ?_
      rintro y ⟨x, hx, rfl⟩
      obtain ⟨seq, hseqD, htendsto⟩ := hdense x hx
      refine le_of_tendsto htendsto (Filter.Eventually.of_forall fun j => ?_)
      exact le_csSup hbddD ⟨seq j, hseqD j, rfl⟩
    · exact csSup_le_csSup hbdd himageDne (Set.image_mono hDS)

/-- [The pointwise supremum of a real-valued family over an index set is measurable](goal) when
[the family and its full and skeleton index sets](hyp:F,S,D) satisfy [countability of the
skeleton](hyp:hD), [measurability at each skeleton index](hyp:hF), and [pointwise equality of
the full and skeleton suprema](hyp:heq). -/
theorem measurable_sSup_image_of_countable_dense {Ω ι : Type*} [MeasurableSpace Ω]
    (S D : Set ι) (F : Ω → ι → ℝ)
    (hD : D.Countable)
    (hF : ∀ π ∈ D, Measurable (fun ω => F ω π))
    (heq : ∀ ω, sSup ((fun π => F ω π) '' S) = sSup ((fun π => F ω π) '' D)) :
    Measurable (fun ω => sSup ((fun π => F ω π) '' S)) := by
  classical
  let _ : Countable D := hD.to_subtype
  have hsup :
      Measurable (fun ω : Ω => ⨆ π : D, F ω π.1) :=
    Measurable.iSup (fun π => hF π.1 π.2)
  convert hsup using 1
  ext ω
  rw [heq ω]
  have himage :
      ((fun π : ι => F ω π) '' D) =
        ((fun π : D => F ω π.1) '' Set.univ) := by
    ext y
    constructor
    · rintro ⟨π, hπ, rfl⟩
      exact ⟨⟨π, hπ⟩, Set.mem_univ _, rfl⟩
    · rintro ⟨π, _hπ, rfl⟩
      exact ⟨π.1, π.2, rfl⟩
  rw [himage]
  have huniv :
      ((fun π : D => F ω π.1) '' Set.univ) =
        Set.range (fun π : D => F ω π.1) := by
    ext y
    constructor
    · rintro ⟨π, _hπ, rfl⟩
      exact ⟨π, rfl⟩
    · rintro ⟨π, rfl⟩
      exact ⟨π, Set.mem_univ _, rfl⟩
  rw [huniv, sSup_range]

/-- A uniform upper bound `F ω π ≤ C` over the index class `S` makes the image `(F ω) '' S`
bounded above (for every `ω`).  Companion `BddAbove` fact accompanying the integrability lemma. -/
theorem bddAbove_image_of_bound {Ω ι : Type*} (S : Set ι) (F : Ω → ι → ℝ) (C : ℝ)
    (hbound : ∀ ω, ∀ π ∈ S, F ω π ≤ C) (ω : Ω) :
    BddAbove ((fun π => F ω π) '' S) := by
  exact bddAbove_def.mpr ⟨C, by
    rintro _ ⟨π, hπ, rfl⟩
    exact hbound ω π hπ⟩

/-- [The pointwise supremum of a real-valued family is integrable under a finite
measure](goal) when [the family and its full and skeleton index sets](hyp:F,S,D) have [a
nonnegative uniform bound](hyp:C,hC), [the skeleton is countable](hyp:hD), [each skeleton
coordinate is measurable](hyp:hF), [the full and skeleton suprema agree pointwise](hyp:heq),
and [the family is uniformly bounded in absolute value](hyp:hbound), with integration against
[the given measure](hyp:μ). -/
theorem integrable_sSup_image_of_countable_dense {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (S D : Set ι) (F : Ω → ι → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hD : D.Countable)
    (hF : ∀ π ∈ D, Measurable (fun ω => F ω π))
    (heq : ∀ ω, sSup ((fun π => F ω π) '' S) = sSup ((fun π => F ω π) '' D))
    (hbound : ∀ ω, ∀ π ∈ S, |F ω π| ≤ C) :
    Integrable (fun ω => sSup ((fun π => F ω π) '' S)) μ := by
  have hmeas := measurable_sSup_image_of_countable_dense S D F hD hF heq
  refine Integrable.of_bound hmeas.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  by_cases hne : ((fun π => F ω π) '' S).Nonempty
  · apply abs_le.mpr
    constructor
    · obtain ⟨y, hy⟩ := hne
      rcases hy with ⟨π, hπ, rfl⟩
      exact (abs_le.mp (hbound ω π hπ)).1.trans
        (le_csSup (bddAbove_image_of_bound S F C
          (fun ω π hπ => (le_abs_self _).trans (hbound ω π hπ)) ω) ⟨π, hπ, rfl⟩)
    · refine csSup_le hne fun y hy => ?_
      rcases hy with ⟨π, hπ, rfl⟩
      exact (abs_le.mp (hbound ω π hπ)).2
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sSup_empty]
    simpa using hC

end Causalean.Mathlib.MeasureTheory
