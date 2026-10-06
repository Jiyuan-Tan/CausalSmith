module
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.Independence.InfinitePi

/-!
# Conditioning a finite product of pilot and evaluation Poisson counts

The two count tables have separate product laws. Their product has an outer
pilot integral and an inner evaluation integral. For each fixed pilot table,
evaluation coordinates retain their Poisson marginals and independence, including
after measurable coordinatewise transformations selected by that pilot table.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure ProbabilityTheory
open scoped NNReal

namespace Causalean.Stat.Concentration.Poisson

/-- [Coordinate Poisson rates](hyp:rate) determine [the joint law of a finite table of independent Poisson counts](goal), [given by the finite product of the coordinate laws](step:1). -/
noncomputable def poissonTableLaw {ι : Type*} [Fintype ι]
    (rate : ι → ℝ≥0) : Measure (ι → ℕ) :=
  infinitePi (fun i => poissonMeasure (rate i))

/-- Independent [pilot-table rates](hyp:pilotRate) and [evaluation-table rates](hyp:evalRate) give [the pilot-then-evaluation integral identity](goal) for [an integrable table statistic](hyp:f,hf). -/
theorem poissonTable_integral_prod {ι : Type*} [Fintype ι]
    (pilotRate evalRate : ι → ℝ≥0)
    (f : (ι → ℕ) × (ι → ℕ) → ℝ)
    (hf : Integrable f ((poissonTableLaw pilotRate).prod (poissonTableLaw evalRate))) :
    (∫ z, f z ∂(poissonTableLaw pilotRate).prod (poissonTableLaw evalRate)) =
      ∫ p, ∫ e, f (p, e) ∂poissonTableLaw evalRate ∂poissonTableLaw pilotRate := by
  exact integral_prod f hf

/-- Independent [pilot-table rates](hyp:pilotRate) and [evaluation-table rates](hyp:evalRate) ensure that [an integrable joint statistic](hyp:f,hf) has [integrable evaluation sections for almost every pilot table](goal). -/
theorem poissonTable_eval_integrable_ae {ι : Type*} [Fintype ι]
    (pilotRate evalRate : ι → ℝ≥0)
    (f : (ι → ℕ) × (ι → ℕ) → ℝ)
    (hf : Integrable f ((poissonTableLaw pilotRate).prod (poissonTableLaw evalRate))) :
    ∀ᵐ p ∂poissonTableLaw pilotRate,
      Integrable (fun e => f (p, e)) (poissonTableLaw evalRate) := by
  exact hf.prod_right_ae

/-- Given [pilot-table rates](hyp:pilotRate), [evaluation-table rates](hyp:evalRate), [a fixed pilot table](hyp:p), and [a coordinate](hyp:i), [that evaluation coordinate retains its stated Poisson law](goal). -/
theorem poissonTable_eval_coordinate_law {ι : Type*} [Fintype ι]
    (pilotRate evalRate : ι → ℝ≥0) (p : ι → ℕ) (i : ι) :
    HasLaw (fun e : ι → ℕ => e i) (poissonMeasure (evalRate i))
      (poissonTableLaw evalRate) := by
  refine ⟨(measurable_pi_apply i).aemeasurable, ?_⟩
  exact infinitePi_map_eval (fun j => poissonMeasure (evalRate j)) i

/-- Given [pilot-table rates](hyp:pilotRate), [evaluation-table rates](hyp:evalRate), and [a fixed pilot table](hyp:p), [the evaluation coordinates are mutually independent](goal). -/
theorem poissonTable_eval_independent {ι : Type*} [Fintype ι]
    (pilotRate evalRate : ι → ℝ≥0) (p : ι → ℕ) :
    iIndepFun (fun i (e : ι → ℕ) => e i) (poissonTableLaw evalRate) := by
  simpa only [poissonTableLaw] using
    (iIndepFun_infinitePi (P := fun i => poissonMeasure (evalRate i))
      (X := fun _ n => n) (by fun_prop))

/-- Given [pilot-table rates](hyp:pilotRate), [evaluation-table rates](hyp:evalRate), [a fixed pilot table](hyp:p), and [cellwise maps measurable after fixing that table](hyp:φ,hφ), [the transformed evaluation coordinates are mutually independent](goal). -/
theorem poissonTable_cellwise_independent
    {ι β : Type*} [Fintype ι] [MeasurableSpace β]
    (pilotRate evalRate : ι → ℝ≥0) (p : ι → ℕ)
    (φ : ι → ℕ → ℕ → β)
    (hφ : ∀ i, Measurable (φ i (p i))) :
    iIndepFun (fun i (e : ι → ℕ) => φ i (p i) (e i))
      (poissonTableLaw evalRate) := by
  simpa only [Function.comp_def] using
    (poissonTable_eval_independent pilotRate evalRate p).comp
      (fun i => φ i (p i)) hφ

/-- Given [pilot-table rates](hyp:pilotRate), [evaluation-table rates](hyp:evalRate), [a fixed pilot table](hyp:p), [pilot-selected Boolean indicators](hyp:good), and [measurable evaluation statistics](hyp:φ,hφ), [the indicator-weighted statistics remain mutually independent](goal). -/
theorem poissonTable_pilot_indicator_independent
    {ι : Type*} [Fintype ι]
    (pilotRate evalRate : ι → ℝ≥0) (p : ι → ℕ)
    (good : ι → ℕ → Bool) (φ : ι → ℕ → ℕ → ℝ)
    (hφ : ∀ i, Measurable (φ i (p i))) :
    iIndepFun (fun i (e : ι → ℕ) =>
      if good i (p i) then φ i (p i) (e i) else 0)
      (poissonTableLaw evalRate) := by
  apply poissonTable_cellwise_independent pilotRate evalRate p
    (fun i k w => if good i k then φ i k w else 0)
  intro i
  by_cases h : good i (p i) <;> simp [h, hφ i]

/-- [Four-coordinate rates in each finite cell](hyp:rate) yield [mutually independent four-count evaluation-cell tables](goal). -/
-- Group the `J × Fin 4` product law by `J`. Prove the regrouping map sends
-- `infinitePi` to `infinitePi` using `infinitePi_map_eval` on cylinder sets,
-- then use `iIndepFun_iff_map_fun_eq_infinitePi_map`. An alternative is the
-- finite-set criterion for independence of disjoint coordinate subfamilies.
theorem poissonTable_cell_blocks_independent
    {J : Type*} [Fintype J] (rate : J → Fin 4 → ℝ≥0) :
    iIndepFun (fun j (e : (J × Fin 4) → ℕ) => fun z => e (j, z))
      (poissonTableLaw (fun iz : J × Fin 4 => rate iz.1 iz.2)) := by
  unfold poissonTableLaw
  have : IsProbabilityMeasure
      (infinitePi (fun iz : J × Fin 4 => poissonMeasure (rate iz.1 iz.2))) := inferInstance
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)]
  convert (Measure.infinitePi_map_curry
    (μ := fun j z => poissonMeasure (rate j z))) using 1
  · rfl
  · congr 1
    funext j
    exact Measure.map_infinitePi_infinitePi_of_inj
      (f := fun z : Fin 4 => (j, z)) (by intro a b h; exact (Prod.mk.inj h).2)

/-- [A cell label](hyp:j) and [a flattened count table](hyp:table) determine [the four-count subtable for that cell](goal), [given by selecting its four coordinates](step:1). -/
def poissonTableCell {J : Type*} (j : J)
    (table : (J × Fin 4) → ℕ) : Fin 4 → ℕ :=
  fun z => table (j, z)

/-- Given [pilot-cell rates](hyp:pilotRate), [evaluation-cell rates](hyp:evalRate), [a fixed pilot table](hyp:p), and [a cell](hyp:j), [the evaluation cell retains its four-coordinate product Poisson law](goal). -/
theorem poissonTable_eval_cell_law
    {J : Type*} [Fintype J] (pilotRate evalRate : J → Fin 4 → ℝ≥0)
    (p : (J × Fin 4) → ℕ) (j : J) :
    HasLaw (poissonTableCell j) (poissonTableLaw (evalRate j))
      (poissonTableLaw (fun iz : J × Fin 4 => evalRate iz.1 iz.2)) := by
  refine ⟨(measurable_pi_iff.mpr (fun z => measurable_pi_apply (j, z))).aemeasurable, ?_⟩
  exact Measure.map_infinitePi_infinitePi_of_inj
    (f := fun z : Fin 4 => (j, z)) (by intro a b h; exact (Prod.mk.inj h).2)

/-- Given [pilot-cell rates](hyp:pilotRate), [evaluation-cell rates](hyp:evalRate), [a fixed pilot table](hyp:p), and [whole-cell maps measurable after fixing each pilot cell](hyp:φ,hφ), [the transformed evaluation cells are mutually independent](goal). -/
theorem poissonTable_pilot_cell_maps_independent
    {J β : Type*} [Fintype J] [MeasurableSpace β]
    (pilotRate evalRate : J → Fin 4 → ℝ≥0)
    (p : (J × Fin 4) → ℕ)
    (φ : J → (Fin 4 → ℕ) → (Fin 4 → ℕ) → β)
    (hφ : ∀ j, Measurable (φ j (poissonTableCell j p))) :
    iIndepFun (fun j (e : (J × Fin 4) → ℕ) =>
      φ j (poissonTableCell j p) (poissonTableCell j e))
      (poissonTableLaw (fun iz : J × Fin 4 => evalRate iz.1 iz.2)) := by
  exact (poissonTable_cell_blocks_independent evalRate).comp
    (fun j => φ j (poissonTableCell j p)) hφ

/-- Given [pilot-cell rates](hyp:pilotRate), [evaluation-cell rates](hyp:evalRate), [a fixed pilot table](hyp:p), [whole-cell pilot indicators](hyp:good), and [measurable evaluation-cell statistics](hyp:φ,hφ), [the indicator-weighted cell statistics are mutually independent](goal). -/
theorem poissonTable_pilot_cell_indicators_independent
    {J : Type*} [Fintype J]
    (pilotRate evalRate : J → Fin 4 → ℝ≥0)
    (p : (J × Fin 4) → ℕ)
    (good : J → (Fin 4 → ℕ) → Bool)
    (φ : J → (Fin 4 → ℕ) → (Fin 4 → ℕ) → ℝ)
    (hφ : ∀ j, Measurable (φ j (poissonTableCell j p))) :
    iIndepFun (fun j (e : (J × Fin 4) → ℕ) =>
      if good j (poissonTableCell j p) then
        φ j (poissonTableCell j p) (poissonTableCell j e) else 0)
      (poissonTableLaw (fun iz : J × Fin 4 => evalRate iz.1 iz.2)) := by
  apply poissonTable_pilot_cell_maps_independent pilotRate evalRate p
    (fun j q w => if good j q then φ j q w else 0)
  intro j
  by_cases h : good j (poissonTableCell j p) <;> simp [h, hφ j]


end Causalean.Stat.Concentration.Poisson
