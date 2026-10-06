module
public import CausalSmith.Stat.STAT_DiscreteBudgetvalueCurve_Research.Helpers.JacksonBias
public import Causalean.Stat.Concentration.Poisson.ConditionalProduct

/-! Transport between flattened Poisson tables and the paper's curried count tables. -/

@[expose] public section

namespace CausalSmith.Stat.DiscreteBudgetvalueCurve

open MeasureTheory ProbabilityTheory
open Causalean.Stat.Concentration.Poisson
open scoped NNReal

/-- Flatten a paper count table using the fixed four-cell equivalence. -/
-- @node: flattenCountTable
noncomputable def flattenCountTable {d : ℕ} (t : Fin d → Cell → ℕ) :
    (Fin d × Fin 4) → ℕ := fun iz => t iz.1 (CellFourEquiv.symm iz.2)

/-- Curry a flattened four-coordinate table back into the paper representation. -/
-- @node: curryCountTable
noncomputable def curryCountTable {d : ℕ} (t : (Fin d × Fin 4) → ℕ) :
    Fin d → Cell → ℕ := fun j z => t (j, CellFourEquiv z)

/-- Flattening and currying are inverse table representations. -/
-- @node: countTableEquiv
noncomputable def countTableEquiv (d : ℕ) :
    ((Fin d × Fin 4) → ℕ) ≃ (Fin d → Cell → ℕ) where
  toFun := curryCountTable
  invFun := flattenCountTable
  left_inv t := by funext iz; simp [curryCountTable, flattenCountTable]
  right_inv t := by funext j z; simp [curryCountTable, flattenCountTable]

/-- The flattened rate corresponding to one pool in `idealCountLaw`. -/
-- @node: idealFlatRate
noncomputable def idealFlatRate {n d : ℕ} (P : DiscreteLaw d) :
    Fin d → Fin 4 → ℝ≥0 := fun j z =>
  Real.toNNReal (((n : ℝ) / 8) * cellVector P j (CellFourEquiv.symm z))

/-- One flattened ideal Poisson pool pushes forward to the paper's curried pool. With [the specified inputs and conditions](hyp:n,d,P), [the stated relationship holds](goal). -/
-- @node: map_poissonTableLaw_curryCountTable
lemma map_poissonTableLaw_curryCountTable {n d : ℕ} (P : DiscreteLaw d) :
    Measure.map curryCountTable
      (poissonTableLaw (fun iz : Fin d × Fin 4 => idealFlatRate (n := n) P iz.1 iz.2)) =
    Measure.pi (fun j : Fin d => Measure.pi (fun z : Cell =>
      poissonMeasure ⟨max 0 (((n : ℝ) / 8) * cellVector P j z),
        le_max_left 0 _⟩)) := by
  let e : (Fin d × Fin 4) ≃ (Fin d × Cell) :=
    Equiv.prodCongr (Equiv.refl _) CellFourEquiv.symm
  let μ : Fin d → Cell → Measure ℕ := fun j z =>
    poissonMeasure (idealFlatRate (n := n) P j (CellFourEquiv z))
  letI : ∀ j z, IsProbabilityMeasure (μ j z) := fun j z => by
    dsimp [μ]
    infer_instance
  letI : ∀ j, IsProbabilityMeasure (Measure.infinitePi (μ j)) := fun j => by
    infer_instance
  have hreindex :
      Measure.map (MeasurableEquiv.piCongrLeft (fun _ : Fin d × Cell => ℕ) e)
        (Measure.infinitePi (fun iz : Fin d × Fin 4 =>
          poissonMeasure (idealFlatRate (n := n) P iz.1 iz.2))) =
      Measure.infinitePi (fun iz : Fin d × Cell => μ iz.1 iz.2) := by
    convert Measure.infinitePi_map_piCongrLeft
      (fun iz : Fin d × Cell => μ iz.1 iz.2) e using 1 <;>
      simp [e, μ]
  have hcurry := Measure.infinitePi_map_curry μ
  unfold poissonTableLaw
  rw [show curryCountTable = (MeasurableEquiv.curry (Fin d) Cell ℕ) ∘
      (MeasurableEquiv.piCongrLeft (fun _ : Fin d × Cell => ℕ) e) by
    funext t j z
    simp [curryCountTable, e, Function.comp_def, MeasurableEquiv.piCongrLeft,
      Equiv.piCongrLeft]]
  rw [← Measure.map_map (by fun_prop) (by fun_prop)]
  rw [hreindex, hcurry]
  rw [Measure.infinitePi_eq_pi]
  congr 2
  funext j
  rw [Measure.infinitePi_eq_pi]
  congr 1
  funext z
  apply congrArg poissonMeasure
  apply NNReal.eq
  simp only [μ, idealFlatRate, Equiv.symm_apply_apply, Real.coe_toNNReal,
    NNReal.coe_mk]
  exact max_comm _ _

/-- Both flattened ideal pools push forward to `idealCountLaw`. With [the specified inputs and conditions](hyp:n,d,P), [the stated relationship holds](goal). -/
-- @node: map_flatIdealCountLaw
lemma map_flatIdealCountLaw {n d : ℕ} (P : DiscreteLaw d) :
    Measure.map (fun pe => (curryCountTable pe.1, curryCountTable pe.2))
      ((poissonTableLaw (fun iz : Fin d × Fin 4 =>
        idealFlatRate (n := n) P iz.1 iz.2)).prod
       (poissonTableLaw (fun iz : Fin d × Fin 4 =>
        idealFlatRate (n := n) P iz.1 iz.2))) =
      idealCountLaw (n := n) P := by
  change Measure.map (Prod.map curryCountTable curryCountTable) _ = _
  rw [← MeasureTheory.Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)]
  rw [map_poissonTableLaw_curryCountTable]
  rfl

/-- Selecting a cell after currying a flat table returns its four-count block. With [the specified inputs and conditions](hyp:d,j,t), [the stated relationship holds](goal). -/
-- @node: curryCountTable_cell
lemma curryCountTable_cell {d : ℕ} (j : Fin d) (t : (Fin d × Fin 4) → ℕ) :
    (fun z => curryCountTable t j (CellFourEquiv.symm z)) =
      poissonTableCell j t := by
  funext z
  simp [curryCountTable, poissonTableCell]

end CausalSmith.Stat.DiscreteBudgetvalueCurve
