/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.Minimax.TotalVariation
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Max
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-!
# Honest confidence sets and frontier risk

This module provides model-free measure and order lemmas for honest random
confidence sets. It relates expected restricted volume to pointwise inclusion
probabilities, transfers coverage through total variation, and packages
uniform asymptotic coverage and frontier-risk bounds over arbitrary model
classes. It also fixes the worst-case coverage convention for empty model
classes.
-/

@[expose] public section

namespace Causalean.Stat

open Filter MeasureTheory
open scoped Topology

/-- For [a parameter region on the real line](hyp:region) and [a set on the
real line](hyp:set), the [restricted set volume](goal) is the real-valued
Lebesgue volume of their intersection, with infinite volume represented by
zero. -/
noncomputable def restrictedSetVolume (region set : Set ℝ) : ℝ :=
  (volume (set ∩ region)).toReal

/-- The expected restricted volume of a jointly measurable random set equals
the integral, over the parameter region, of its pointwise inclusion
probabilities. -/
theorem expected_restrictedSetVolume_eq_integral_inclusion
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsFiniteMeasure Q] (C : Ω → Set ℝ)
    (region : Set ℝ)
    (hgraph : MeasurableSet {p : Ω × ℝ | p.2 ∈ C p.1})
    (hregion : MeasurableSet region) (hregionFinite : volume region ≠ ⊤) :
    (∫ ω, restrictedSetVolume region (C ω) ∂Q) =
      ∫ u in region, (Q {ω | u ∈ C ω}).toReal := by
  let S : Set (Ω × ℝ) := {p | p.2 ∈ C p.1 ∧ p.2 ∈ region}
  let f : Ω × ℝ → ℝ := S.indicator (fun _ => 1)
  have hS : MeasurableSet S := hgraph.inter (hregion.preimage measurable_snd)
  have hSsub : S ⊆ Set.univ ×ˢ region := by
    intro p hp
    exact ⟨Set.mem_univ _, hp.2⟩
  have hSfinite : (Q.prod volume) S ≠ ⊤ := by
    apply ne_of_lt
    calc
      (Q.prod volume) S ≤ (Q.prod volume) (Set.univ ×ˢ region) :=
        measure_mono hSsub
      _ = Q Set.univ * volume region := by rw [Measure.prod_prod]
      _ < ⊤ := ENNReal.mul_lt_top (measure_lt_top Q Set.univ)
        (lt_top_iff_ne_top.mpr hregionFinite)
  have hfint : Integrable f (Q.prod volume) := by
    rw [show f = S.indicator (fun _ => (1 : ℝ)) from rfl]
    exact (integrableOn_const hSfinite).integrable_indicator hS
  calc
    (∫ ω, restrictedSetVolume region (C ω) ∂Q) =
        ∫ ω, (∫ u, f (ω, u) ∂volume) ∂Q := by
      apply integral_congr_ae
      filter_upwards with ω
      rw [show restrictedSetVolume region (C ω) =
        (volume (C ω ∩ region)).toReal from rfl]
      rw [show (fun u => f (ω, u)) =
        (C ω ∩ region).indicator (fun _ => (1 : ℝ)) by
          funext u
          simp only [f, S, Set.indicator]
          split_ifs <;> simp_all]
      exact (integral_indicator_one
        (hgraph.preimage (measurable_const.prodMk measurable_id) |>.inter
          hregion)).symm
    _ = ∫ u, (∫ ω, f (ω, u) ∂Q) ∂volume := by
      calc
        _ = ∫ z, f z ∂Q.prod volume :=
          (integral_prod (μ := Q) (ν := volume) f hfint).symm
        _ = _ := integral_prod_symm (μ := Q) (ν := volume) f hfint
    _ = ∫ u in region, (Q {ω | u ∈ C ω}).toReal := by
      rw [← MeasureTheory.integral_indicator hregion]
      apply integral_congr_ae
      filter_upwards with u
      by_cases hu : u ∈ region
      · rw [show (fun ω => f (ω, u)) =
          {ω | u ∈ C ω}.indicator (fun _ => (1 : ℝ)) by
            funext ω
            simp only [f, S, Set.indicator]
            split_ifs <;> simp_all]
        rw [Set.indicator_of_mem hu]
        exact integral_indicator_one (μ := Q)
          (hgraph.preimage (measurable_id.prodMk measurable_const))
      · simp [f, S, hu]

/-- **Coverage-to-expected-restricted-volume bound.**  For a family of laws `Q u` indexed by
`u : ℝ`, a random set `C`, a subset `I` of a parameter region `region`, and a reference point
`reference`, suppose [every `Q u` is a probability measure](hyp:hQ), [`C` covers `u` with
probability at least `coverage`, for every `u` in `I`](hyp:hcover), [`Q u` is within total
variation `tv` of the reference law `Q reference`, for every `u` in `I`](hyp:htv), [the graph
`{(ω, u) | u ∈ C ω}` is measurable](hyp:hgraph), [`region` is measurable](hyp:hregion), [`region`
has finite Lebesgue volume](hyp:hregionFinite), [`I` is measurable](hyp:hI), and [`I` is
contained in `region`](hyp:hI_sub). Then [the expected restricted volume of `C` under the
reference law `Q reference` is at least `(volume I) · (coverage − tv)`](goal). -/
theorem coverage_tv_expectedRestrictedVolume_lower
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : ℝ → Measure Ω) (C : Ω → Set ℝ) (region I : Set ℝ)
    (reference coverage tv : ℝ)
    (hQ : ∀ u, IsProbabilityMeasure (Q u))
    (hcover : ∀ u ∈ I, coverage ≤ (Q u {ω | u ∈ C ω}).toReal)
    (htv : ∀ u ∈ I, tvDist (Q u) (Q reference) ≤ tv)
    (hgraph : MeasurableSet {p : Ω × ℝ | p.2 ∈ C p.1})
    (hregion : MeasurableSet region) (hregionFinite : volume region ≠ ⊤)
    (hI : MeasurableSet I) (hI_sub : I ⊆ region) :
    (volume I).toReal * (coverage - tv) ≤
      ∫ ω, restrictedSetVolume region (C ω) ∂Q reference := by
  letI : IsProbabilityMeasure (Q reference) := hQ reference
  have hpoint : ∀ u ∈ I,
      coverage - tv ≤ (Q reference {ω | u ∈ C ω}).toReal := by
    intro u hu
    letI : IsProbabilityMeasure (Q u) := hQ u
    have hE : MeasurableSet {ω | u ∈ C ω} :=
      hgraph.preimage (measurable_id.prodMk measurable_const)
    have hgap := measureReal_sub_le_tvDist
      (μ := Q reference) (ν := Q u) hE
    change (Q u {ω | u ∈ C ω}).toReal -
      (Q reference {ω | u ∈ C ω}).toReal ≤
        tvDist (Q reference) (Q u) at hgap
    rw [tvDist_symm] at hgap
    linarith [hcover u hu, htv u hu]
  rw [expected_restrictedSetVolume_eq_integral_inclusion
    (Q := Q reference) C region hgraph hregion hregionFinite]
  have hmeas : Measurable fun u =>
      (Q reference {ω | u ∈ C ω}).toReal :=
    Measurable.ennreal_toReal (measurable_measure_prodMk_right hgraph)
  have hIfinite : volume I ≠ ⊤ := ne_top_of_le_ne_top hregionFinite
    (measure_mono hI_sub)
  have hrhsint : IntegrableOn
      (fun u => (Q reference {ω | u ∈ C ω}).toReal) I := by
    letI : IsFiniteMeasure (volume.restrict I) :=
      isFiniteMeasure_restrict.mpr hIfinite
    exact Integrable.of_bound
      hmeas.aestronglyMeasurable.restrict 1
      (Filter.Eventually.of_forall fun u => by
        rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
        simpa only [← measureReal_def] using
          (measureReal_le_one (μ := Q reference)
            (s := {ω | u ∈ C ω})))
  have hrhsRegion : IntegrableOn
      (fun u => (Q reference {ω | u ∈ C ω}).toReal) region := by
    letI : IsFiniteMeasure (volume.restrict region) :=
      isFiniteMeasure_restrict.mpr hregionFinite
    exact Integrable.of_bound hmeas.aestronglyMeasurable.restrict 1
      (Filter.Eventually.of_forall fun u => by
        rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
        simpa only [← measureReal_def] using
          (measureReal_le_one (μ := Q reference)
            (s := {ω | u ∈ C ω})))
  calc
    (volume I).toReal * (coverage - tv) =
        ∫ _u in I, coverage - tv := by
      rw [setIntegral_const]
      simp [measureReal_def]
    _ ≤ ∫ u in I, (Q reference {ω | u ∈ C ω}).toReal :=
      setIntegral_mono_on (integrableOn_const hIfinite) hrhsint hI hpoint
    _ ≤ ∫ u in region, (Q reference {ω | u ∈ C ω}).toReal :=
      setIntegral_mono_set hrhsRegion
        (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
        (Filter.Eventually.of_forall hI_sub)

/-- Pointwise coverage rows with a vanishing uniform error imply asymptotic
uniform coverage over any eventually inhabited sequence of model classes. -/
theorem classCoverage_liminf
    {Model : Type*} (cls : ℕ → Model → Prop)
    (coverage : ℕ → Model → ℝ) (alpha : ℝ) (delta : ℕ → ℝ)
    (hdelta : Tendsto delta atTop (𝓝 0))
    (hInhab : ∀ᶠ n in atTop, ∃ P, cls n P)
    (hcoverage : ∀ n P, cls n P →
      0 ≤ coverage n P ∧ coverage n P ≤ 1)
    (hrow : ∀ n P, cls n P → 1 - alpha - delta n ≤ coverage n P) :
    1 - alpha ≤ Filter.liminf
      (fun n => ⨅ P : {P : Model // cls n P}, coverage n P) atTop := by
  let row : ℕ → ℝ := fun n =>
    ⨅ P : {P : Model // cls n P}, coverage n P
  have hrows : ∀ᶠ n in atTop, 1 - alpha - delta n ≤ row n := by
    filter_upwards [hInhab] with n hn
    letI : Nonempty {P : Model // cls n P} :=
      ⟨⟨Classical.choose hn, Classical.choose_spec hn⟩⟩
    apply le_ciInf
    intro P
    exact hrow n P P.2
  have hrowUpper : ∀ᶠ n in atTop, row n ≤ 1 := by
    filter_upwards [hInhab] with n hn
    obtain ⟨P₀, hP₀⟩ := hn
    have hbdd : BddBelow
        (Set.range fun P : {P : Model // cls n P} => coverage n P) := by
      refine ⟨0, ?_⟩
      rintro y ⟨P, rfl⟩
      exact (hcoverage n P P.2).1
    exact (ciInf_le hbdd ⟨P₀, hP₀⟩).trans (hcoverage n P₀ hP₀).2
  have hlowerBounded :
      IsBoundedUnder (· ≥ ·) atTop (fun n => 1 - alpha - delta n) := by
    change ∃ b, ∀ᶠ n in atTop, b ≤ 1 - alpha - delta n
    have hdeltalt : ∀ᶠ n in atTop, delta n < 1 :=
      (tendsto_order.1 hdelta).2 1 zero_lt_one
    exact ⟨-alpha, hdeltalt.mono fun _ hn => by linarith⟩
  have hrowCobounded : IsCoboundedUnder (· ≥ ·) atTop row := by
    change ∃ b, ∀ a, (∀ᶠ n in atTop, a ≤ row n) → a ≤ b
    refine ⟨1, fun a ha => ?_⟩
    obtain ⟨n, han, hn1⟩ := (ha.and hrowUpper).exists
    exact han.trans hn1
  have hlowerTendsto :
      Tendsto (fun n => 1 - alpha - delta n) atTop (𝓝 (1 - alpha)) := by
    simpa using ((tendsto_const_nhds.sub tendsto_const_nhds).sub hdelta)
  change 1 - alpha ≤ Filter.liminf row atTop
  rw [← hlowerTendsto.liminf_eq]
  exact Filter.liminf_le_liminf hrows hlowerBounded hrowCobounded

/-- The capped inverse-square-root rate is antitone on positive strengths. -/
theorem inverseSqrtCap_anti {t0 t : ℝ} (ht0 : 0 < t0) (htt : t0 ≤ t) :
    min 1 (t ^ (-1 / 2 : ℝ)) ≤ min 1 (t0 ^ (-1 / 2 : ℝ)) := by
  apply min_le_min_left
  exact Real.rpow_le_rpow_of_nonpos ht0 htt (by norm_num)

/-- For [a sequence of model classes](hyp:cls), [a real-valued strength and a
real-valued expected-length criterion for each sample size and model](hyp:strength,expectedLength),
and [a real strength threshold](hyp:t0), the [class frontier risk](goal) is the
limit superior, across sample sizes, of the supremum expected length over the
models in that class whose strength is at least the threshold. -/
noncomputable def classFrontierRisk
    {Model : Type*} (cls : ℕ → Model → Prop)
    (strength expectedLength : ℕ → Model → ℝ) (t0 : ℝ) : ℝ :=
  Filter.limsup
    (fun n => ⨆ P : {P : Model // cls n P ∧ t0 ≤ strength n P},
      expectedLength n P) atTop

/-- A pointwise capped inverse-square-root expected-length bound passes through
both the class supremum and asymptotic limsup at the threshold value. -/
theorem classFrontierRisk_le
    {Model : Type*} (cls : ℕ → Model → Prop)
    (strength expectedLength : ℕ → Model → ℝ)
    (C0 t0 : ℝ) (hC0 : 0 ≤ C0) (ht0 : 0 < t0)
    (hLengthNonneg : ∀ n P, cls n P → 0 ≤ expectedLength n P)
    (hpoint : ∀ n P, cls n P →
      expectedLength n P ≤ C0 * min 1 (strength n P ^ (-1 / 2 : ℝ))) :
    classFrontierRisk cls strength expectedLength t0 ≤
      C0 * min 1 (t0 ^ (-1 / 2 : ℝ)) := by
  let bound : ℝ := C0 * min 1 (t0 ^ (-1 / 2 : ℝ))
  have hmin0 : 0 ≤ min 1 (t0 ^ (-1 / 2 : ℝ)) :=
    le_min (by norm_num) (Real.rpow_nonneg ht0.le _)
  have hbound0 : 0 ≤ bound := mul_nonneg hC0 hmin0
  let row : ℕ → ℝ := fun n =>
    ⨆ P : {P : Model // cls n P ∧ t0 ≤ strength n P}, expectedLength n P
  have hrowUpper : ∀ n, row n ≤ bound := by
    intro n
    let I := {P : Model // cls n P ∧ t0 ≤ strength n P}
    cases isEmpty_or_nonempty I with
    | inl hEmpty =>
        letI : IsEmpty I := hEmpty
        change (⨆ P : I, expectedLength n P) ≤ bound
        simpa using hbound0
    | inr hNonempty =>
        letI : Nonempty I := hNonempty
        apply ciSup_le
        intro P
        exact (hpoint n P P.2.1).trans
          (mul_le_mul_of_nonneg_left (inverseSqrtCap_anti ht0 P.2.2) hC0)
  have hrowLower : ∀ n, 0 ≤ row n := by
    intro n
    let I := {P : Model // cls n P ∧ t0 ≤ strength n P}
    cases isEmpty_or_nonempty I with
    | inl hEmpty =>
        letI : IsEmpty I := hEmpty
        change 0 ≤ ⨆ P : I, expectedLength n P
        simp
    | inr hNonempty =>
        letI : Nonempty I := hNonempty
        obtain ⟨P⟩ := hNonempty
        have hbdd : BddAbove (Set.range fun Q : I => expectedLength n Q) := by
          refine ⟨bound, ?_⟩
          rintro y ⟨Q, rfl⟩
          exact (hpoint n Q Q.2.1).trans
            (mul_le_mul_of_nonneg_left (inverseSqrtCap_anti ht0 Q.2.2) hC0)
        exact (hLengthNonneg n P P.2.1).trans (le_ciSup hbdd P)
  have hcob : IsCoboundedUnder (· ≤ ·) atTop row :=
    Filter.isCoboundedUnder_le_of_le atTop hrowLower
  change Filter.limsup row atTop ≤ bound
  exact Filter.limsup_le_of_le hcob (Filter.Eventually.of_forall hrowUpper)

/-- For [a real-valued criterion indexed by an arbitrary collection](hyp:f),
the [worst-case criterion with the empty-collection convention](goal) is its
infimum when the collection is nonempty and is one when it is empty.

Worst-case coverage is the ordinary infimum when the model class is nonempty, but is
defined as one when the class is empty. A real-valued infimum over an empty index would
otherwise equal zero and misleadingly signal coverage failure for a vacuous model class.

The related `classCoverage_liminf` theorem avoids this issue by assuming that its model
classes are eventually inhabited; this definition instead makes the empty-class convention
explicit. -/
noncomputable def coverageInfOrOne {ι : Sort*} (f : ι → ℝ) : ℝ := by
  classical
  exact if Nonempty ι then ⨅ i, f i else 1

/-- On a nonempty model class, worst-case coverage with the empty-class convention is the
ordinary infimum of coverage across the class. -/
theorem coverageInfOrOne_of_nonempty {ι : Sort*} [Nonempty ι] (f : ι → ℝ) :
    coverageInfOrOne f = ⨅ i, f i := by
  have hne : Nonempty ι := inferInstance
  simp [coverageInfOrOne, hne]

/-- On an empty model class, worst-case coverage with the empty-class convention is one,
expressing that the coverage requirement is vacuously satisfied. -/
theorem coverageInfOrOne_of_isEmpty {ι : Sort*} [IsEmpty ι] (f : ι → ℝ) :
    coverageInfOrOne f = 1 := by
  simp [coverageInfOrOne, not_nonempty_iff.mpr inferInstance]

end Causalean.Stat


namespace Causalean.Stat

open MeasureTheory
open scoped BigOperators ENNReal

/-- The [grid point](goal) indexed by [j](hyp:j) is obtained from [the origin and spacing](hyp:t,δ) by taking that many equally spaced steps. -/
def gridPoint {M : ℕ} (t δ : ℝ) (j : Fin (M + 1)) : ℝ := t + (j.val : ℝ) * δ

/-- The [covered grid count](goal) is the number of points in [the grid with M gaps, origin t, and spacing δ](hyp:M,t,δ) that lie in [the closed interval with endpoints l and u](hyp:l,u). -/
noncomputable def gridCount (M : ℕ) (t δ l u : ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun j : Fin (M + 1) => gridPoint t δ j ∈ Set.Icc l u)).card

/-- The [coverage event](goal) for [a target value](hyp:θ) is the collection of sample outcomes where the closed interval with [random lower and upper endpoints](hyp:L,U) contains that target. -/
def coverageEvent {Ω : Type*} (L U : Ω → ℝ) (θ : ℝ) : Set Ω :=
  {x | θ ∈ Set.Icc (L x) (U x)}

/-- The [nonnegative interval length](goal) associated with [a lower endpoint](hyp:l) and [an upper endpoint](hyp:u) is the upper endpoint minus the lower endpoint when that difference is nonnegative, and zero when the endpoints are reversed. -/
def intervalLength (l u : ℝ) : ℝ := max 0 (u - l)

/-- [Measurable random lower and upper endpoints](hyp:hL,hU) make [each fixed-target coverage event measurable](goal). -/
theorem measurableSet_coverageEvent {Ω : Type*} [MeasurableSpace Ω]
    {L U : Ω → ℝ} {θ : ℝ} (hL : Measurable L) (hU : Measurable U) :
    MeasurableSet (coverageEvent L U θ) := by
  exact (measurableSet_le hL measurable_const).inter
    (measurableSet_le measurable_const hU)

/-- [Measurable random lower and upper endpoints](hyp:hL,hU) give [a measurable nonnegative interval length](goal). -/
@[fun_prop] theorem measurable_intervalLength {Ω : Type*} [MeasurableSpace Ω]
    {L U : Ω → ℝ} (hL : Measurable L) (hU : Measurable U) :
    Measurable (fun x => intervalLength (L x) (U x)) := by
  exact measurable_const.max (hU.sub hL)

/-- The [covered grid count](hyp:M,t,δ,L,U) is [the finite sum of the corresponding coverage-event indicators, viewed as a real-valued statistic](goal). -/
theorem gridCount_eq_sum_indicator {Ω : Type*} (M : ℕ) (t δ : ℝ)
    (L U : Ω → ℝ) :
    (fun x => (gridCount M t δ (L x) (U x) : ℝ)) =
      fun x => ∑ j : Fin (M + 1),
        (coverageEvent L U (gridPoint t δ j)).indicator (fun _ => (1 : ℝ)) x := by
  classical
  funext x
  simp only [gridCount, Set.indicator_apply, coverageEvent, Set.mem_ofPred_eq]
  exact (Finset.sum_boole _ _).symm

/-- Under [a finite sample law](hyp:μ), [measurable random endpoints](hyp:hL,hU) make [the covered grid count an integrable statistic](goal). -/
@[fun_prop] theorem integrable_gridCount {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (M : ℕ) (t δ : ℝ)
    {L U : Ω → ℝ} (hL : Measurable L) (hU : Measurable U) :
    Integrable (fun x => (gridCount M t δ (L x) (U x) : ℝ)) μ := by
  classical
  rw [gridCount_eq_sum_indicator]
  exact integrable_finsetSum _ (fun j _ =>
    (integrable_const (1 : ℝ)).indicator (measurableSet_coverageEvent hL hU))

/-- Under [a finite sample law](hyp:μ), [a grid with M gaps, origin t, and spacing δ](hyp:M,t,δ), and [measurable random endpoints](hyp:hL,hU), [the expected covered grid count equals the sum of its coverage probabilities](goal). -/
theorem integral_gridCount {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (M : ℕ) (t δ : ℝ)
    {L U : Ω → ℝ} (hL : Measurable L) (hU : Measurable U) :
    (∫ x, (gridCount M t δ (L x) (U x) : ℝ) ∂μ) =
      ∑ j : Fin (M + 1), μ.real (coverageEvent L U (gridPoint t δ j)) := by
  classical
  rw [gridCount_eq_sum_indicator, integral_finsetSum]
  · exact Finset.sum_congr rfl (fun j _ =>
      integral_indicator_one (measurableSet_coverageEvent hL hU))
  · intro j _
    exact (integrable_const (1 : ℝ)).indicator (measurableSet_coverageEvent hL hU)

/-- If [an integrable real-valued statistic](hyp:hf) is [pointwise no larger than a second statistic](hyp:hle), then [the positive part of its expectation is no larger than the nonnegative integral of the second statistic](goal). -/
theorem ofReal_integral_le_lintegral_ofReal_of_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f g : Ω → ℝ} (hf : Integrable f μ) (hle : ∀ x, f x ≤ g x) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (g x) ∂μ := by
  calc
    ENNReal.ofReal (∫ x, f x ∂μ) ≤
        ENNReal.ofReal (∫ x, max (f x) 0 ∂μ) :=
      ENNReal.ofReal_le_ofReal (integral_mono hf hf.pos_part (fun x => le_max_left _ _))
    _ = ∫⁻ x, ENNReal.ofReal (max (f x) 0) ∂μ :=
      ofReal_integral_eq_lintegral_ofReal hf.pos_part
        (Filter.Eventually.of_forall (fun x => le_max_right _ _))
    _ ≤ ∫⁻ x, ENNReal.ofReal (g x) ∂μ := by
      apply lintegral_mono
      intro x
      simpa only [ENNReal.ofReal_max, ENNReal.ofReal_zero,
        max_eq_left (zero_le : (0 : ℝ≥0∞) ≤ _)] using ENNReal.ofReal_le_ofReal (hle x)

/-- For [a grid with M gaps, origin t, and strictly positive spacing δ](hyp:M,t,δ,hδ), the [nonnegative length of any closed interval with endpoints l and u](hyp:l,u) is [at least δ times one less than its number of covered grid points](goal). -/
theorem intervalLength_ge_gridCount (M : ℕ) (t δ l u : ℝ) (hδ : 0 < δ) :
    δ * ((gridCount M t δ l u : ℝ) - 1) ≤ intervalLength l u := by
  classical
  let S := Finset.univ.filter (fun j : Fin (M + 1) => gridPoint t δ j ∈ Set.Icc l u)
  change δ * ((S.card : ℝ) - 1) ≤ max 0 (u - l)
  by_cases hS : S.Nonempty
  · let a := S.min' hS
    let b := S.max' hS
    have ha : gridPoint t δ a ∈ Set.Icc l u :=
      (Finset.mem_filter.mp (S.min'_mem hS)).2
    have hb : gridPoint t δ b ∈ Set.Icc l u :=
      (Finset.mem_filter.mp (S.max'_mem hS)).2
    have hab : a.val ≤ b.val := S.min'_le_max' hS
    have hcard : S.card ≤ b.val + 1 - a.val := by
      calc
        S.card = (S.image Fin.val).card :=
          (Finset.card_image_of_injective S Fin.val_injective).symm
        _ ≤ (Finset.Icc a.val b.val).card := by
          apply Finset.card_le_card
          intro k hk
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
          exact Finset.mem_Icc.mpr ⟨S.min'_le j hj, S.le_max' j hj⟩
        _ = b.val + 1 - a.val := Nat.card_Icc _ _
    have hcast : (S.card : ℝ) ≤ (b.val : ℝ) + 1 - (a.val : ℝ) := by
      have hsub : a.val ≤ b.val + 1 := hab.trans (Nat.le_succ _)
      have := (Nat.cast_le (α := ℝ)).mpr hcard
      simpa only [Nat.cast_sub hsub, Nat.cast_add, Nat.cast_one] using this
    have hspan : δ * ((S.card : ℝ) - 1) ≤ δ * ((b.val : ℝ) - (a.val : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith) hδ.le
    have hlo : l ≤ t + (a.val : ℝ) * δ := ha.1
    have hhi : t + (b.val : ℝ) * δ ≤ u := hb.2
    nlinarith [le_max_right (0 : ℝ) (u - l)]
  · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero, zero_sub, mul_neg, mul_one]
    exact (neg_nonpos.mpr hδ.le).trans (le_max_left _ _)

/-- Under [a reference probability law](hyp:μ₀), [a grid with M gaps, origin t, and positive spacing δ](hyp:M,t,δ,hδ), [a coverage floor p at every grid target](hyp:p,hcoverage), and [measurable random interval endpoints](hyp:hL,hU), [the expected nonnegative interval length is at least δ times ((M + 1) times p minus one)](goal). -/
theorem expected_interval_length_lower_of_grid {Ω : Type*} [MeasurableSpace Ω]
    (μ₀ : Measure Ω) [IsProbabilityMeasure μ₀] (M : ℕ) (t δ p : ℝ)
    {L U : Ω → ℝ} (hL : Measurable L) (hU : Measurable U) (hδ : 0 < δ)
    (hcoverage : ∀ j : Fin (M + 1),
      p ≤ μ₀.real (coverageEvent L U (gridPoint t δ j))) :
    ENNReal.ofReal (δ * (((M + 1 : ℕ) : ℝ) * p - 1)) ≤
      ∫⁻ x, ENNReal.ofReal (intervalLength (L x) (U x)) ∂μ₀ := by
  have hc := integrable_gridCount μ₀ M t δ hL hU
  have hsum : ((M + 1 : ℕ) : ℝ) * p ≤
      ∫ x, (gridCount M t δ (L x) (U x) : ℝ) ∂μ₀ := by
    rw [integral_gridCount μ₀ M t δ hL hU]
    simpa using (Finset.sum_le_sum (s := Finset.univ) (fun j _ => hcoverage j))
  have hf : Integrable (fun x => δ * ((gridCount M t δ (L x) (U x) : ℝ) - 1)) μ₀ :=
    (hc.sub (integrable_const 1)).const_mul δ
  have heq : (∫ x, δ * ((gridCount M t δ (L x) (U x) : ℝ) - 1) ∂μ₀) =
      δ * ((∫ x, (gridCount M t δ (L x) (U x) : ℝ) ∂μ₀) - 1) := by
    rw [integral_const_mul, integral_sub hc (integrable_const 1)]
    simp
  calc
    ENNReal.ofReal (δ * (((M + 1 : ℕ) : ℝ) * p - 1)) ≤
        ENNReal.ofReal (∫ x, δ * ((gridCount M t δ (L x) (U x) : ℝ) - 1) ∂μ₀) := by
      apply ENNReal.ofReal_le_ofReal
      rw [heq]
      exact mul_le_mul_of_nonneg_left (sub_le_sub_right hsum 1) hδ.le
    _ ≤ _ := ofReal_integral_le_lintegral_ofReal_of_le hf
      (fun x => intervalLength_ge_gridCount M t δ (L x) (U x) hδ)

/-- [Honest coverage under each experiment law](hyp:μ,α,hhonest), [an event-wise gap of at most η from each experiment law to the reference law](hyp:μ₀,η,hclose), [a grid with M gaps, origin t, and positive spacing δ](hyp:M,t,δ,hδ), and [measurable random endpoints](hyp:hL,hU) give [the finite-grid expected-length lower bound with transferred coverage 1 minus α minus η](goal). -/
theorem honest_interval_length_lower_of_grid_eventwise {Ω : Type*} [MeasurableSpace Ω]
    (μ₀ : Measure Ω) [IsProbabilityMeasure μ₀] (M : ℕ)
    (μ : Fin (M + 1) → Measure Ω) [∀ j, IsProbabilityMeasure (μ j)]
    (t δ α η : ℝ) {L U : Ω → ℝ}
    (hL : Measurable L) (hU : Measurable U) (hδ : 0 < δ)
    (hhonest : ∀ j, 1 - α ≤ (μ j).real (coverageEvent L U (gridPoint t δ j)))
    (hclose : ∀ j, (μ j).real (coverageEvent L U (gridPoint t δ j)) -
      μ₀.real (coverageEvent L U (gridPoint t δ j)) ≤ η) :
    ENNReal.ofReal (δ * (((M + 1 : ℕ) : ℝ) * (1 - α - η) - 1)) ≤
      ∫⁻ x, ENNReal.ofReal (intervalLength (L x) (U x)) ∂μ₀ := by
  apply expected_interval_length_lower_of_grid μ₀ M t δ (1 - α - η) hL hU hδ
  intro j
  linarith [hhonest j, hclose j]

/-- [Honest coverage under each experiment law](hyp:μ,α,hhonest), [total variation at most η from each experiment law to a reference law](hyp:μ₀,η,htv), [a grid with M gaps, origin t, and positive spacing δ](hyp:M,t,δ,hδ), and [measurable random endpoints](hyp:hL,hU) imply [the finite-grid expected-length lower bound with transferred coverage 1 minus α minus η](goal). -/
theorem honest_interval_length_lower_of_grid_tv {Ω : Type*} [MeasurableSpace Ω]
    (μ₀ : Measure Ω) [IsProbabilityMeasure μ₀] (M : ℕ)
    (μ : Fin (M + 1) → Measure Ω) [∀ j, IsProbabilityMeasure (μ j)]
    (t δ α η : ℝ) {L U : Ω → ℝ}
    (hL : Measurable L) (hU : Measurable U) (hδ : 0 < δ)
    (hhonest : ∀ j, 1 - α ≤ (μ j).real (coverageEvent L U (gridPoint t δ j)))
    (htv : ∀ j, tvDist μ₀ (μ j) ≤ η) :
    ENNReal.ofReal (δ * (((M + 1 : ℕ) : ℝ) * (1 - α - η) - 1)) ≤
      ∫⁻ x, ENNReal.ofReal (intervalLength (L x) (U x)) ∂μ₀ := by
  apply honest_interval_length_lower_of_grid_eventwise μ₀ M μ t δ α η hL hU hδ hhonest
  intro j
  exact (measureReal_sub_le_tvDist (μ := μ₀) (ν := μ j)
    (measurableSet_coverageEvent hL hU)).trans (htv j)

/-- For [a reference law and experiment laws](hyp:μ₀,μ), [a miscoverage level strictly between zero and one](hyp:α,hα0,hα1), [a grid with at least 8 divided by one minus α gaps and positive spacing δ](hyp:M,t,hM,δ,hδ), [a TV error at most one eighth of one minus α](hyp:η,hη,htv), [honest coverage under each experiment law](hyp:hhonest), and [measurable random endpoints](hyp:hL,hU), [the expected length is at least three quarters of one minus α times the grid width and is strictly positive](goal). -/
theorem honest_interval_length_lower_of_grid_tv_positive {Ω : Type*} [MeasurableSpace Ω]
    (μ₀ : Measure Ω) [IsProbabilityMeasure μ₀] (M : ℕ)
    (μ : Fin (M + 1) → Measure Ω) [∀ j, IsProbabilityMeasure (μ j)]
    (t δ α η : ℝ) {L U : Ω → ℝ}
    (hL : Measurable L) (hU : Measurable U) (hδ : 0 < δ)
    (hα0 : 0 < α) (hα1 : α < 1) (hM : 8 / (1 - α) ≤ (M : ℝ))
    (hη : η ≤ (1 - α) / 8)
    (hhonest : ∀ j, 1 - α ≤ (μ j).real (coverageEvent L U (gridPoint t δ j)))
    (htv : ∀ j, tvDist μ₀ (μ j) ≤ η) :
    0 < 3 * (1 - α) / 4 ∧
      ENNReal.ofReal ((3 * (1 - α) / 4) * ((M : ℝ) * δ)) ≤
        (∫⁻ x, ENNReal.ofReal (intervalLength (L x) (U x)) ∂μ₀) ∧
      0 < (∫⁻ x, ENNReal.ofReal (intervalLength (L x) (U x)) ∂μ₀) := by
  have hu : 0 < 1 - α := by linarith
  have hMu : 8 ≤ (M : ℝ) * (1 - α) := (div_le_iff₀ hu).mp hM
  have hMpos : 0 < (M : ℝ) := by nlinarith
  have hcoeff : 0 < 3 * (1 - α) / 4 := by positivity
  have hbase := honest_interval_length_lower_of_grid_tv μ₀ M μ t δ α η hL hU hδ hhonest htv
  have harith : (3 * (1 - α) / 4) * ((M : ℝ) * δ) ≤
      δ * (((M + 1 : ℕ) : ℝ) * (1 - α - η) - 1) := by
    have hinner : (3 * (1 - α) / 4) * (M : ℝ) ≤
        ((M + 1 : ℕ) : ℝ) * (1 - α - η) - 1 := by
      push_cast
      nlinarith [mul_nonneg (show 0 ≤ (M : ℝ) + 1 by positivity)
        (show 0 ≤ (1 - α) / 8 - η by linarith)]
    nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hinner)]
  have hbound := (ENNReal.ofReal_le_ofReal harith).trans hbase
  refine ⟨hcoeff, hbound, ?_⟩
  exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (mul_pos hcoeff (mul_pos hMpos hδ))) hbound

end Causalean.Stat
