/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Goodman-Bacon (2021) Layer B: panel class, cell statistics, and projections

Holds the saturated cohort + period nuisance class `panelClass`, the
cohort/period/cell statistics extracted from the joint law, the in-class
projections `panelPropensity` / `panelMeanReg`, the elementary cell-mass
positivity bounds, and the membership lemmas
`panelPropensity_mem_panelClass` / `panelMeanReg_mem_panelClass`.

Intended to be a pure-definitions + light-bound layer; integral identities
go in `Support/Integrals.lean`, per-cell orthogonality in
`Support/Orthogonality.lean`, residualization witnesses in
`Support/Partition.lean`, and per-cell denominator/numerator identities in
`Support/PerCell.lean`.

NL artifact:
`doc/basic_concepts/po/estimand_characterization/goodman_bacon_twfe_timing.md`
("Layer B" section).
-/

import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Causalean.Panel.Analysis.Residualization
import Causalean.Panel.CellBridge
import Causalean.Panel.EstimandCharacterization.StaggeredTWFEDecomposition.FinitePanel

/-!
Defines basic bridge objects for the staggered-TWFE decomposition. The module
packages saturated cohort-period classes and finite panel support used to
connect algebraic weighted panels to population integrals.
-/

namespace Causalean.Panel.EstimandCharacterization.StaggeredTWFEDecomposition

open MeasureTheory Finset Causalean.Panel
open scoped BigOperators

variable {Ω 𝒢 : Type*} [MeasurableSpace Ω] [Fintype 𝒢] [DecidableEq 𝒢]
  [MeasurableSpace 𝒢] [MeasurableSingletonClass 𝒢] {T : ℕ}

/-! ### B1. Saturated cohort + period class -/

/-- Given [a finite measure](hyp:μ), [a cohort classifier](hyp:G), [a period classifier](hyp:T_rv), [a measurable cohort classifier](hyp:G_meas), and [a measurable period classifier](hyp:T_meas), [the saturated cohort-and-period function class](goal) consists of functions that agree almost everywhere with a linear combination of cohort and period indicator functions.

Membership predicate (predicate-style, residualization_core D1 option (b)):

    f ∈ panelClass μ G T_rv  ↔  ∃ (cG : 𝒢 → ℝ) (cT : Fin T → ℝ),
        f =ᵐ[μ] (fun ω => ∑ g, cG g · 𝟙{G ω = g}
                        + ∑ t, cT t · 𝟙{T_rv ω = t}). -/
noncomputable def panelClass
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (G : Ω → 𝒢) (T_rv : Ω → Fin T)
    (G_meas : Measurable G) (T_meas : Measurable T_rv) : LinearL2Class μ :=
  CellBridge.twoAxisIndicatorSpan μ G T_rv G_meas T_meas

/-! ### B2. Cell statistics -/

/-- For [a measure](hyp:μ), [a cohort classifier](hyp:G), [a period classifier](hyp:T_rv), [a cohort](hyp:g), and [a period](hyp:t), [the cohort-period cell mass](goal) is the real-valued mass of observations classified in that cohort-period cell. -/
def cellMass (μ : Measure Ω) (G : Ω → 𝒢) (T_rv : Ω → Fin T)
    (g : 𝒢) (t : Fin T) : ℝ :=
  CellBridge.jointCellMass μ G T_rv g t

/-- For [a measure](hyp:μ), [a cohort classifier](hyp:G), and [a cohort](hyp:g), [the cohort mass](goal) is the real-valued mass of observations classified in that cohort. -/
def cohortMass (μ : Measure Ω) (G : Ω → 𝒢) (g : 𝒢) : ℝ :=
  CellBridge.cellMass μ G g

/-- For [a measure](hyp:μ), [a period classifier](hyp:T_rv), and [a period](hyp:t), [the period mass](goal) is the real-valued mass of observations classified in that period. -/
def periodMass (μ : Measure Ω) (T_rv : Ω → Fin T) (t : Fin T) : ℝ :=
  CellBridge.cellMass μ T_rv t

/-- For [a measure](hyp:μ), [an outcome variable](hyp:Y), [a cohort classifier](hyp:G), [a period classifier](hyp:T_rv), [a cohort](hyp:g), and [a period](hyp:t), [the cohort-period cell mean](goal) is the outcome integral over that cell divided by its mass, and is zero when the cell has zero mass. -/
noncomputable def cellMean (μ : Measure Ω) (Y : Ω → ℝ) (G : Ω → 𝒢)
    (T_rv : Ω → Fin T) (g : 𝒢) (t : Fin T) : ℝ :=
  (∫ ω, Y ω
    * Set.indicator {ω' | G ω' = g ∧ T_rv ω' = t} (fun _ => (1 : ℝ)) ω ∂μ)
    / cellMass μ G T_rv g t

omit [Fintype 𝒢] [DecidableEq 𝒢] [MeasurableSpace 𝒢] [MeasurableSingletonClass 𝒢] in
/-- The panel cell mean for a cohort and period equals the generic cell-mean operator applied to
the joint cohort-period cell. -/
theorem cellMean_eq_cellBridge (μ : Measure Ω) (Y : Ω → ℝ) (G : Ω → 𝒢)
    (T_rv : Ω → Fin T) (g : 𝒢) (t : Fin T) :
    cellMean μ Y G T_rv g t =
      CellBridge.cellMean μ Y (fun ω => (G ω, T_rv ω)) (g, t) := by
  classical
  unfold cellMean CellBridge.cellMean cellMass CellBridge.jointCellMass CellBridge.cellMass
  congr 2
  · ext ω
    simp
  · congr 1
    ext ω
    simp

/-- For [a measure](hyp:μ), [a treatment variable](hyp:D), [a cohort classifier](hyp:G), and [a cohort](hyp:g), [the cohort mean treatment share](goal) is the treatment integral over that cohort's cell divided by its mass, and is zero when the cell has zero mass. -/
noncomputable def cohortBarD (μ : Measure Ω) (D : Ω → ℝ) (G : Ω → 𝒢)
    (g : 𝒢) : ℝ :=
  (∫ ω, D ω * Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω ∂μ)
    / cohortMass μ G g

/-! ### B2. `panelOf` — Layer A panel built from the law -/

/-- Given [a measure](hyp:μ), [an outcome variable](hyp:Y), [a cohort classifier](hyp:G), [a period classifier](hyp:T_rv), [an adoption-date schedule](hyp:A), [a positive number of periods](hyp:hT_pos), [strictly positive cohort masses](hyp:hp_pos), and [cohort masses summing to one](hyp:hp_sum), [the cohort panel constructed from the law](goal) has those cohort masses as shares, the supplied adoption dates, and cohort-period outcome means. -/
noncomputable def panelOf
    (μ : Measure Ω)
    (Y : Ω → ℝ) (G : Ω → 𝒢) (T_rv : Ω → Fin T)
    (A : 𝒢 → WithTop (Fin T))
    (hT_pos : 0 < T)
    (hp_pos : ∀ g, 0 < cohortMass μ G g)
    (hp_sum : ∑ g, cohortMass μ G g = 1) :
    CohortPanel 𝒢 T :=
  { p := cohortMass μ G
  , A := A
  , Y := cellMean μ Y G T_rv
  , T_pos := hT_pos
  , p_pos := hp_pos
  , p_sum_one := hp_sum }

/-! ### B3. In-class projections for `D` and `Y` -/

/-- For [a measure](hyp:μ), [a treatment variable](hyp:D), [a cohort classifier](hyp:G), and [a period classifier](hyp:T_rv), [the saturated cohort-and-period propensity regression](goal) assigns each observation its cohort mean treatment plus its period mean treatment minus the overall mean treatment.

The pointwise representative

    panelPropensity μ D G T_rv ω
      := \overline{D}_{G ω} + (E[D | T = T_rv ω] - E[D])

decomposes the projection of `D` on `H_gt` as the sum of a cohort-indicator
expansion and a period-indicator expansion (centred to ensure
identifiability). Lies in `panelClass μ G T_rv G_meas T_meas`. -/
noncomputable def panelPropensity
    (μ : Measure Ω) (D : Ω → ℝ) (G : Ω → 𝒢) (T_rv : Ω → Fin T) : Ω → ℝ :=
  fun ω =>
    (∑ g, cohortBarD μ D G g
      * Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω)
    + (∑ t, ((∫ ω', D ω'
        * Set.indicator {ω' | T_rv ω' = t} (fun _ => (1 : ℝ)) ω' ∂μ)
        / periodMass μ T_rv t
        - ∫ ω', D ω' ∂μ)
      * Set.indicator {ω' | T_rv ω' = t} (fun _ => (1 : ℝ)) ω)

/-- For [a measure](hyp:μ), [an outcome variable](hyp:Y), [a cohort classifier](hyp:G), and [a period classifier](hyp:T_rv), [the saturated cohort-and-period outcome regression](goal) assigns each observation its cohort mean outcome plus its period mean outcome minus the overall mean outcome. -/
noncomputable def panelMeanReg
    (μ : Measure Ω) (Y : Ω → ℝ) (G : Ω → 𝒢) (T_rv : Ω → Fin T) : Ω → ℝ :=
  fun ω =>
    (∑ g, ((∫ ω', Y ω'
        * Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω' ∂μ)
        / cohortMass μ G g)
      * Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω)
    + (∑ t, ((∫ ω', Y ω'
        * Set.indicator {ω' | T_rv ω' = t} (fun _ => (1 : ℝ)) ω' ∂μ)
        / periodMass μ T_rv t
        - ∫ ω', Y ω' ∂μ)
      * Set.indicator {ω' | T_rv ω' = t} (fun _ => (1 : ℝ)) ω)

/-! ### B3. Membership lemmas -/

/-- For [a finite measure `μ`](hyp:μ), [a treatment variable `D`](hyp:D), [a measurable cohort
map `G`](hyp:G,G_meas), and [a measurable period map `T_rv`](hyp:T_rv,T_meas), [the pointwise
saturated cohort-and-period propensity regression of `D` belongs to the two-axis additive
(cohort-plus-period) function class](goal).

Coefficient maps: `cG g := cohortBarD μ D G g`,
`cT t := (∫ D · 𝟙{T=t} dμ) / periodMass t - ∫ D dμ`. -/
theorem panelPropensity_mem_panelClass
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (D : Ω → ℝ) (G : Ω → 𝒢) (T_rv : Ω → Fin T)
    (G_meas : Measurable G) (T_meas : Measurable T_rv) :
    (panelClass μ G T_rv G_meas T_meas).mem (panelPropensity μ D G T_rv) := by
  unfold panelClass CellBridge.twoAxisIndicatorSpan
  refine ⟨fun g => cohortBarD μ D G g,
    fun t => (∫ ω', D ω'
      * Set.indicator {ω' | T_rv ω' = t} (fun _ => (1 : ℝ)) ω' ∂μ)
      / periodMass μ T_rv t
      - ∫ ω', D ω' ∂μ, ?_⟩
  filter_upwards [] with ω
  rfl

/-- For [a finite measure `μ`](hyp:μ), [an outcome variable `Y`](hyp:Y), [a measurable cohort
map `G`](hyp:G,G_meas), and [a measurable period map `T_rv`](hyp:T_rv,T_meas), [the pointwise
saturated cohort-and-period mean regression of `Y` belongs to the two-axis additive
(cohort-plus-period) function class](goal). -/
theorem panelMeanReg_mem_panelClass
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (Y : Ω → ℝ) (G : Ω → 𝒢) (T_rv : Ω → Fin T)
    (G_meas : Measurable G) (T_meas : Measurable T_rv) :
    (panelClass μ G T_rv G_meas T_meas).mem (panelMeanReg μ Y G T_rv) := by
  unfold panelClass CellBridge.twoAxisIndicatorSpan
  refine ⟨fun g => (∫ ω', Y ω'
      * Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω' ∂μ)
      / cohortMass μ G g,
    fun t => (∫ ω', Y ω'
      * Set.indicator {ω' | T_rv ω' = t} (fun _ => (1 : ℝ)) ω' ∂μ)
      / periodMass μ T_rv t
      - ∫ ω', Y ω' ∂μ, ?_⟩
  filter_upwards [] with ω
  rfl

/-! ### B2. Elementary cell-mass bounds -/

omit [Fintype 𝒢] [DecidableEq 𝒢] [MeasurableSpace 𝒢] [MeasurableSingletonClass 𝒢] in
/-- Cell mass is nonnegative. -/
theorem cellMass_nonneg (μ : Measure Ω) (G : Ω → 𝒢) (T_rv : Ω → Fin T)
    (g : 𝒢) (t : Fin T) : 0 ≤ cellMass μ G T_rv g t := ENNReal.toReal_nonneg

omit [Fintype 𝒢] [DecidableEq 𝒢] [MeasurableSpace 𝒢] [MeasurableSingletonClass 𝒢] in
/-- Cohort mass is nonnegative. -/
theorem cohortMass_nonneg (μ : Measure Ω) (G : Ω → 𝒢) (g : 𝒢) :
    0 ≤ cohortMass μ G g := ENNReal.toReal_nonneg

/-- Period mass is nonnegative. -/
theorem periodMass_nonneg (μ : Measure Ω) (T_rv : Ω → Fin T) (t : Fin T) :
    0 ≤ periodMass μ T_rv t := ENNReal.toReal_nonneg

end Causalean.Panel.EstimandCharacterization.StaggeredTWFEDecomposition
