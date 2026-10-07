module
public import Causalean.Stat.Concentration.Poisson.ConditionalProduct

/-!
# Joint pilot-cell and evaluation-cell statistics

A statistic may depend on all four pilot counts in a cell and all four evaluation
counts in the same cell. This module derives joint measurability and product-law
disintegration from measurable compositions and an integrable envelope.
-/

public section

open MeasureTheory MeasureTheory.Measure ProbabilityTheory
open scoped NNReal

namespace Causalean.Stat.Concentration.Poisson

/-- Given [a cell](hyp:j), [a measurable pilot-cell indicator](hyp:good,hgood), and [a jointly measurable cell statistic](hyp:φ,hφ), [the indicator-weighted pilot/evaluation statistic is jointly measurable](goal). -/
theorem poissonTable_cell_indicator_measurable
    {J : Type*} (j : J)
    (good : (Fin 4 → ℕ) → Bool) (hgood : Measurable good)
    (φ : (Fin 4 → ℕ) → (Fin 4 → ℕ) → ℝ)
    (hφ : Measurable (Function.uncurry φ)) :
    Measurable (fun pe : ((J × Fin 4) → ℕ) × ((J × Fin 4) → ℕ) =>
      if good (poissonTableCell j pe.1) then
        φ (poissonTableCell j pe.1) (poissonTableCell j pe.2)
      else 0) := by
  have hcell : Measurable (poissonTableCell j : ((J × Fin 4) → ℕ) → Fin 4 → ℕ) :=
    measurable_pi_iff.mpr (fun z => measurable_pi_apply (j, z))
  have hp : Measurable (fun pe : ((J × Fin 4) → ℕ) × ((J × Fin 4) → ℕ) =>
      poissonTableCell j pe.1) := hcell.comp measurable_fst
  have he : Measurable (fun pe : ((J × Fin 4) → ℕ) × ((J × Fin 4) → ℕ) =>
      poissonTableCell j pe.2) := hcell.comp measurable_snd
  exact Measurable.ite ((hgood.comp hp) (measurableSet_singleton true))
    (hφ.comp (hp.prodMk he)) measurable_const

/-- Given [pilot-cell rates](hyp:pilotRate), [evaluation-cell rates](hyp:evalRate), [a cell](hyp:j), [a measurable pilot indicator](hyp:good,hgood), [a jointly measurable statistic](hyp:φ,hφ), and [an integrable dominating envelope](hyp:envelope,henvelope,hdom), [the joint integral disintegrates into pilot and evaluation integrals](goal). -/
theorem poissonTable_cell_indicator_integral_prod
    {J : Type*} [Fintype J]
    (pilotRate evalRate : J → Fin 4 → ℝ≥0) (j : J)
    (good : (Fin 4 → ℕ) → Bool) (hgood : Measurable good)
    (φ : (Fin 4 → ℕ) → (Fin 4 → ℕ) → ℝ)
    (hφ : Measurable (Function.uncurry φ))
    (envelope : ((J × Fin 4) → ℕ) × ((J × Fin 4) → ℕ) → ℝ)
    (henvelope : Integrable envelope
      ((poissonTableLaw (fun iz : J × Fin 4 => pilotRate iz.1 iz.2)).prod
        (poissonTableLaw (fun iz : J × Fin 4 => evalRate iz.1 iz.2))))
    (hdom : ∀ pe,
      |(if good (poissonTableCell j pe.1) then
          φ (poissonTableCell j pe.1) (poissonTableCell j pe.2) else 0)| ≤
        envelope pe) :
    (∫ pe,
      (if good (poissonTableCell j pe.1) then
        φ (poissonTableCell j pe.1) (poissonTableCell j pe.2) else 0)
      ∂(poissonTableLaw (fun iz : J × Fin 4 => pilotRate iz.1 iz.2)).prod
        (poissonTableLaw (fun iz : J × Fin 4 => evalRate iz.1 iz.2))) =
    ∫ p, ∫ e,
      (if good (poissonTableCell j p) then
        φ (poissonTableCell j p) (poissonTableCell j e) else 0)
      ∂poissonTableLaw (fun iz : J × Fin 4 => evalRate iz.1 iz.2)
      ∂poissonTableLaw (fun iz : J × Fin 4 => pilotRate iz.1 iz.2) := by
  have hm := poissonTable_cell_indicator_measurable j good hgood φ hφ
  have hi : Integrable (fun pe : ((J × Fin 4) → ℕ) × ((J × Fin 4) → ℕ) =>
      if good (poissonTableCell j pe.1) then
        φ (poissonTableCell j pe.1) (poissonTableCell j pe.2) else 0)
      ((poissonTableLaw (fun iz : J × Fin 4 => pilotRate iz.1 iz.2)).prod
        (poissonTableLaw (fun iz : J × Fin 4 => evalRate iz.1 iz.2))) :=
    henvelope.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall
      (fun pe => by simpa only [Real.norm_eq_abs] using hdom pe))
  exact integral_prod _ hi

/-- Given [pilot-cell rates](hyp:pilotRate), [evaluation-cell rates](hyp:evalRate), [a cell](hyp:j), [a measurable pilot indicator](hyp:good,hgood), [a jointly measurable statistic](hyp:φ,hφ), [an integrable dominating envelope](hyp:envelope,henvelope,hdom), and [an integrable pilot bound on every evaluation section](hyp:bound,hbound,hsection), [the joint integral is bounded by the pilot integral of that bound](goal). -/
theorem poissonTable_cell_indicator_integral_le
    {J : Type*} [Fintype J]
    (pilotRate evalRate : J → Fin 4 → ℝ≥0) (j : J)
    (good : (Fin 4 → ℕ) → Bool) (hgood : Measurable good)
    (φ : (Fin 4 → ℕ) → (Fin 4 → ℕ) → ℝ)
    (hφ : Measurable (Function.uncurry φ))
    (envelope : ((J × Fin 4) → ℕ) × ((J × Fin 4) → ℕ) → ℝ)
    (henvelope : Integrable envelope
      ((poissonTableLaw (fun iz : J × Fin 4 => pilotRate iz.1 iz.2)).prod
        (poissonTableLaw (fun iz : J × Fin 4 => evalRate iz.1 iz.2))))
    (hdom : ∀ pe,
      |(if good (poissonTableCell j pe.1) then
          φ (poissonTableCell j pe.1) (poissonTableCell j pe.2) else 0)| ≤
        envelope pe)
    (bound : ((J × Fin 4) → ℕ) → ℝ)
    (hbound : Integrable bound
      (poissonTableLaw (fun iz : J × Fin 4 => pilotRate iz.1 iz.2)))
    (hsection : ∀ p,
      (∫ e,
        (if good (poissonTableCell j p) then
          φ (poissonTableCell j p) (poissonTableCell j e) else 0)
        ∂poissonTableLaw (fun iz : J × Fin 4 => evalRate iz.1 iz.2)) ≤
      bound p) :
    (∫ pe,
      (if good (poissonTableCell j pe.1) then
        φ (poissonTableCell j pe.1) (poissonTableCell j pe.2) else 0)
      ∂(poissonTableLaw (fun iz : J × Fin 4 => pilotRate iz.1 iz.2)).prod
        (poissonTableLaw (fun iz : J × Fin 4 => evalRate iz.1 iz.2))) ≤
    ∫ p, bound p
      ∂poissonTableLaw (fun iz : J × Fin 4 => pilotRate iz.1 iz.2) := by
  rw [poissonTable_cell_indicator_integral_prod pilotRate evalRate j good hgood φ hφ
    envelope henvelope hdom]
  have hi := (poissonTable_cell_indicator_measurable j good hgood φ hφ)
  have hprod : Integrable (fun pe : ((J × Fin 4) → ℕ) × ((J × Fin 4) → ℕ) =>
      if good (poissonTableCell j pe.1) then
        φ (poissonTableCell j pe.1) (poissonTableCell j pe.2) else 0)
      ((poissonTableLaw (fun iz : J × Fin 4 => pilotRate iz.1 iz.2)).prod
        (poissonTableLaw (fun iz : J × Fin 4 => evalRate iz.1 iz.2))) :=
    henvelope.mono' hi.aestronglyMeasurable (Filter.Eventually.of_forall
      (fun pe => by simpa only [Real.norm_eq_abs] using hdom pe))
  exact integral_mono hprod.integral_prod_left hbound hsection

/-- Let a pilot table and an evaluation table of independent Poisson counts, four per cell, have [pilot-cell rates](hyp:pilotRate) and [evaluation-cell rates](hyp:evalRate), and be independent of each other. Fix [a cell](hyp:j), [a measurable yes/no indicator of that cell's four pilot counts](hyp:good,hgood), and [a jointly measurable nonnegative statistic of that cell's four pilot counts and four evaluation counts](hyp:φ,hφ,hφ_nonneg), and consider the statistic set to zero when the indicator fails. If, [for every fixed pilot table, this gated statistic is integrable over the evaluation table](hyp:hsection_int), and [its evaluation-table expectation is at most a function of the pilot table that is integrable under the pilot law](hyp:bound,hbound,hsection_bound), then [the joint expectation of the gated statistic over both tables is at most the pilot-table expectation of that bounding function](goal). -/
-- Use `integrable_prod_iff` after proving the outer integral of the absolute
-- value is dominated by `bound`; nonnegativity identifies that absolute value
-- with the conditional integral already bounded by `hsection_bound`.
theorem poissonTable_cell_nonneg_integral_le_of_sections
    {J : Type*} [Fintype J]
    (pilotRate evalRate : J → Fin 4 → ℝ≥0) (j : J)
    (good : (Fin 4 → ℕ) → Bool) (hgood : Measurable good)
    (φ : (Fin 4 → ℕ) → (Fin 4 → ℕ) → ℝ)
    (hφ : Measurable (Function.uncurry φ))
    (hφ_nonneg : ∀ u v, 0 ≤ φ u v)
    (hsection_int : ∀ p : (J × Fin 4) → ℕ,
      Integrable (fun e : (J × Fin 4) → ℕ =>
        if good (poissonTableCell j p) then
          φ (poissonTableCell j p) (poissonTableCell j e) else 0)
        (poissonTableLaw (fun iz : J × Fin 4 => evalRate iz.1 iz.2)))
    (bound : ((J × Fin 4) → ℕ) → ℝ)
    (hbound : Integrable bound
      (poissonTableLaw (fun iz : J × Fin 4 => pilotRate iz.1 iz.2)))
    (hsection_bound : ∀ p : (J × Fin 4) → ℕ,
      (∫ e : (J × Fin 4) → ℕ,
        (if good (poissonTableCell j p) then
          φ (poissonTableCell j p) (poissonTableCell j e) else 0)
        ∂poissonTableLaw (fun iz : J × Fin 4 => evalRate iz.1 iz.2)) ≤
      bound p) :
    (∫ pe,
      (if good (poissonTableCell j pe.1) then
        φ (poissonTableCell j pe.1) (poissonTableCell j pe.2) else 0)
      ∂(poissonTableLaw (fun iz : J × Fin 4 => pilotRate iz.1 iz.2)).prod
        (poissonTableLaw (fun iz : J × Fin 4 => evalRate iz.1 iz.2))) ≤
    ∫ p, bound p
      ∂poissonTableLaw (fun iz : J × Fin 4 => pilotRate iz.1 iz.2) := by
  let f : (((J × Fin 4) → ℕ) × ((J × Fin 4) → ℕ)) → ℝ := fun pe =>
    if good (poissonTableCell j pe.1) then
      φ (poissonTableCell j pe.1) (poissonTableCell j pe.2) else 0
  have hf_meas : Measurable f := poissonTable_cell_indicator_measurable j good hgood φ hφ
  have hf_nonneg : ∀ pe, 0 ≤ f pe := by
    intro pe
    dsimp [f]
    split_ifs <;> simp [hφ_nonneg]
  have hnorm : (fun p => ∫ e, ‖f (p, e)‖
      ∂poissonTableLaw (fun iz : J × Fin 4 => evalRate iz.1 iz.2)) =
      (fun p => ∫ e, f (p, e)
      ∂poissonTableLaw (fun iz : J × Fin 4 => evalRate iz.1 iz.2)) := by
    funext p
    congr 1
    funext e
    exact Real.norm_eq_abs (f (p, e)) ▸ abs_of_nonneg (hf_nonneg (p, e))
  have houter : Integrable (fun p => ∫ e, ‖f (p, e)‖
      ∂poissonTableLaw (fun iz : J × Fin 4 => evalRate iz.1 iz.2))
      (poissonTableLaw (fun iz : J × Fin 4 => pilotRate iz.1 iz.2)) := by
    haveI : IsProbabilityMeasure
        (poissonTableLaw (fun iz : J × Fin 4 => pilotRate iz.1 iz.2)) := by
      unfold poissonTableLaw
      infer_instance
    rw [hnorm]
    apply integrable_of_le_of_le
      (g₁ := fun _ => (0 : ℝ)) (g₂ := bound)
    · exact hf_meas.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    · filter_upwards [] with p
      exact integral_nonneg (fun e => hf_nonneg (p, e))
    · exact Filter.Eventually.of_forall hsection_bound
    · exact integrable_const 0
    · exact hbound
  have hf_int : Integrable f
      ((poissonTableLaw (fun iz : J × Fin 4 => pilotRate iz.1 iz.2)).prod
        (poissonTableLaw (fun iz : J × Fin 4 => evalRate iz.1 iz.2))) :=
    (integrable_prod_iff hf_meas.aestronglyMeasurable).mpr
      ⟨Filter.Eventually.of_forall hsection_int, houter⟩
  change (∫ pe, f pe ∂(poissonTableLaw
      (fun iz : J × Fin 4 => pilotRate iz.1 iz.2)).prod
      (poissonTableLaw (fun iz : J × Fin 4 => evalRate iz.1 iz.2))) ≤ _
  rw [integral_prod f hf_int]
  exact integral_mono hf_int.integral_prod_left hbound hsection_bound

end Causalean.Stat.Concentration.Poisson
