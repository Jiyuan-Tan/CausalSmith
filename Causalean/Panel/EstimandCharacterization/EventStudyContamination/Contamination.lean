/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Listed-cohort cell-grid contamination representation

Public entry points for the listed-cohort cell-grid contamination theorem.
Each takes a `CellGridResidualization` input, derives the
`ConventionalResidualization` orthogonality conditions and the identity
`D.mu = conventionalMuRatio` via the weighted cell-grid projection in
`CellGrid.lean`, then applies the finite-cell contamination algebra from
`Conventional.lean`.
-/

module
public import Causalean.Panel.EstimandCharacterization.EventStudyContamination.CellGrid

/-! # Listed-Cohort Cell-Grid Contamination Representation

This file provides public contamination theorems for an event-study coefficient
defined by a weighted projection on the listed finite cohorts and declared
event-support cells. It derives the needed residualization identities and
applies the finite-cell algebra to obtain the displayed contamination formulas.
These results do not identify that restricted projection with a full-population
TWFE regression. -/

public section

namespace Causalean
namespace Panel.EstimandCharacterization
namespace EventStudyContamination

namespace EventStudySystem

open Finset

variable {T : ℕ} {P : EventStudySystem T} {D : P.ConventionalDesign}

/-- **Cell-grid contamination representation.** For the coefficient `D.mu` of a cell-grid
design, if [observed outcomes equal the own-path potential-outcome means](hyp:hConsistency),
[never-treated means obey additive parallel trends](hyp:hMeanParallelUntreated),
[the relevant event times have finite support](hyp:hSupport), and
[the weighted cell-grid projection input is supplied](hyp:hCell), then
[`D.mu` equals the contamination-weighted sum of CATTs over admissible cells](goal). -/
theorem contamination_representation_of_cellGrid
    (hConsistency : P.Consistency) (hMeanParallelUntreated : P.MeanParallelUntreated)
    (hSupport : P.ConventionalFiniteSupport D)
    (hCell : P.CellGridResidualization D) :
    D.mu =
      ∑ ge ∈ P.admissibleCells D.eventSupport,
        P.omega D ge.1 ge.2 * P.CATT ge.1 ge.2 :=
  P.contamination_representation D hConsistency hMeanParallelUntreated
    (cellGrid_provides_residualization hCell.hCellMassPos hCell.hCellNonempty
      hCell.hRdotResidual).hResidualization
    hCell.hDenomPos (cellGrid_mu_eq_conventionalMuRatio hCell) hSupport

/-- **Cell-grid contamination split.** For the coefficient `D.mu` of a cell-grid design, if
[the consistency, parallel-trends, and no-anticipation restrictions hold](hyp:hCausal),
[the relevant event times have finite support](hyp:hSupport), and
[the weighted cell-grid projection input is supplied](hyp:hCell), then
[`D.mu` splits into its displayed-event term and all other admissible-cell terms](goal). -/
theorem contamination_representation_split_of_cellGrid
    (hCausal : P.EventStudyCausalRestrictions)
    (hSupport : P.ConventionalFiniteSupport D)
    (hCell : P.CellGridResidualization D) :
    D.mu =
      (∑ g ∈ P.cohortsAtEvent D.eventSupport D.displayedEvent,
        P.omega D g D.displayedEvent * P.CATT g D.displayedEvent) +
      (∑ ge ∈ (P.admissibleCells D.eventSupport).filter
          (fun ge => ge.2 ≠ D.displayedEvent),
        P.omega D ge.1 ge.2 * P.CATT ge.1 ge.2) :=
  P.contamination_representation_split D hCausal.hConsistency hCausal.hMeanParallelUntreated
    (cellGrid_provides_residualization hCell.hCellMassPos hCell.hCellNonempty hCell.hRdotResidual)
    hCell.hDenomPos (cellGrid_mu_eq_conventionalMuRatio hCell) hSupport

/-- **Cell-grid apparent pretrends.** For the coefficient `D.mu` of a cell-grid design, if
[the displayed event is a lead](hyp:hLead),
[the consistency, parallel-trends, and no-anticipation restrictions hold](hyp:hCausal),
[the relevant event times have finite support](hyp:hSupport), and
[the weighted cell-grid projection input is supplied](hyp:hCell), then
[`D.mu` is a generally signed contamination-weighted sum of nonnegative-event-time CATTs](goal).
-/
theorem apparent_pretrends_from_post_treatment_of_cellGrid
    (hLead : D.displayedEvent < 0)
    (hCausal : P.EventStudyCausalRestrictions)
    (hSupport : P.ConventionalFiniteSupport D)
    (hCell : P.CellGridResidualization D) :
    D.mu =
      ∑ ge ∈ (P.admissibleCells D.eventSupport).filter (fun ge => 0 ≤ ge.2),
        P.omega D ge.1 ge.2 * P.CATT ge.1 ge.2 :=
  P.apparent_pretrends_from_post_treatment D hLead hCausal
    (cellGrid_provides_residualization hCell.hCellMassPos hCell.hCellNonempty
      hCell.hRdotResidual).hResidualization
    hCell.hDenomPos (cellGrid_mu_eq_conventionalMuRatio hCell) hSupport

end EventStudySystem

end EventStudyContamination
end Panel.EstimandCharacterization
end Causalean
