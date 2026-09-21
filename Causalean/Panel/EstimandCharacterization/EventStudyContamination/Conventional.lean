/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Listed cohort cell-grid event-study contamination

Finite-cell contamination algebra for a coefficient defined by a projection on
listed cohort-by-relative-time cells. The orthogonality conditions
(`ConventionalResidualization`) and
the FWL ratio (`D.mu = conventionalMuRatio`) are consumed here as hypotheses.
Both are derived from a weighted cell-grid projection in `CellGrid.lean`, with
public entry points in `Contamination.lean`.
-/

module
public import Causalean.Panel.EstimandCharacterization.EventStudyContamination.Setup

/-! # Listed-Cohort Cell-Grid Event Study

This file formalizes finite-cell algebra for an event-study coefficient defined
by a projection on the listed finite cohorts and declared relative-time cells.
It expresses that coefficient as a generally signed weighted sum of
cohort-relative-time treatment effects under supplied residualization and
support conditions. The projection does not include the never-treated path and
is not asserted to equal a full-population two-way fixed-effects regression. -/

@[expose] public section

namespace Causalean
namespace Panel.EstimandCharacterization
namespace EventStudyContamination

open Finset

namespace EventStudySystem

variable {T : ℕ}

/-- For [two relative times](hyp:k,e), the [event-time indicator](goal) equals
one when they are equal and zero otherwise. -/
noncomputable def eventIndicator (k e : ℤ) : ℝ :=
  if e = k then 1 else 0

/-- An event-study cell-grid design on [a finite system](hyp:P) records
[the relative-time support used in its cell expansion](hyp:eventSupport),
[the included event-time regressors](hyp:includedEvents),
[an omitted-event metadata label](hyp:omittedEvent),
[the displayed event time](hyp:displayedEvent),
[the displayed indicator's cellwise residual](hyp:Rdot), and
[the displayed cell-grid coefficient](hyp:mu).

No current validity condition constrains the omitted-event label, and no theorem in this
development reads it; the included-event set itself determines the post-omission regressors.
The structure's legacy name does not assert that this coefficient equals a full-population
TWFE coefficient. -/
structure ConventionalDesign (P : EventStudySystem T) where
  /-- Finite support of relative times used in the cell expansion. -/
  eventSupport : Finset ℤ
  /-- Included relative-time indicators in the cell-grid projection. -/
  includedEvents : Finset ℤ
  /-- Source-facing omitted-reference label; currently unconstrained and computationally inert. -/
  omittedEvent : ℤ
  /-- Displayed event time `l` whose coefficient is characterized. -/
  displayedEvent : ℤ
  /-- Residualized relative-time indicator `Rdot^l`, constant on cells. -/
  Rdot : Fin T → ℤ → ℝ
  /-- Coefficient on the displayed indicator in the cell-grid projection. -/
  mu : ℝ

/-- For a [finite time horizon](hyp:T), [an event-study system](hyp:P),
[a cell-grid design](hyp:D), and [a cohort-period function](hyp:h), the
[event-study nuisance condition](goal) holds exactly when the function is the
sum of a cohort-and-period additive component and a linear combination of the
included relative-time indicators other than the displayed indicator, for every
cohort in the system and every period. -/
def IsEventStudyNuisance (P : EventStudySystem T) (D : P.ConventionalDesign)
    (h : Fin T → Fin T → ℝ) : Prop :=
  ∃ hAdd : Fin T → Fin T → ℝ, Causalean.Stat.Weighted.IsUnitTimeAdditive hAdd ∧
    ∃ gamma : ℤ → ℝ,
      ∀ g ∈ P.cohorts, ∀ t,
        h g t = hAdd g t +
          ∑ k ∈ D.includedEvents.filter (fun k => k ≠ D.displayedEvent),
            gamma k * eventIndicator k (P.relTime g t)

/-- For a [finite time horizon](hyp:T), [an event-study system](hyp:P), [a
cohort-period function](hyp:h), [a cohort](hyp:g), and [a relative time](hyp:e),
the [cell average](goal) is the average of that function over the periods in
which the cohort has the given relative time. -/
noncomputable def cellAverage (P : EventStudySystem T)
    (h : Fin T → Fin T → ℝ) (g : Fin T) (e : ℤ) : ℝ :=
  ((P.targetPeriods g e).card : ℝ)⁻¹ *
    ∑ t ∈ P.targetPeriods g e, h g t

/-- Finite-cell residualization record for the cell-grid coefficient.

The fields are the finite-cell consequences of `Rdot^l` being the residual of
the displayed relative-time indicator `R^l` against the event-study nuisance
class: orthogonality to nuisance functions, the displayed-event expansion of
the denominator, and zero weights for other included event-time indicators.
This file consumes the record as a hypothesis for the algebraic contamination
proofs; `CellGrid.lean` derives the record from a weighted projection on the
admissible cohort-relative-time grid. -/
structure ConventionalResidualization (P : EventStudySystem T)
    (D : P.ConventionalDesign) : Prop where
  hResidualization :
    ∀ h : Fin T → Fin T → ℝ, P.IsEventStudyNuisance D h →
      ∑ ge ∈ P.admissibleCells D.eventSupport,
        P.cellMassAtEvent ge.1 ge.2 * D.Rdot ge.1 ge.2 *
          P.cellAverage h ge.1 ge.2 = 0
  hDisplayedExpansion :
    ∑ ge ∈ P.admissibleCells D.eventSupport,
      P.cellMassAtEvent ge.1 ge.2 * D.Rdot ge.1 ge.2 *
        eventIndicator D.displayedEvent ge.2 =
      ∑ g ∈ P.cohortsAtEvent D.eventSupport D.displayedEvent,
        P.cellMassAtEvent g D.displayedEvent * D.Rdot g D.displayedEvent
  hOtherIncludedOrthogonal :
    ∀ e ∈ D.includedEvents, e ≠ D.displayedEvent →
      ∑ g ∈ P.cohortsAtEvent D.eventSupport e,
        P.cellMassAtEvent g e * D.Rdot g e = 0

/-- For a [finite time horizon](hyp:T), [an event-study system](hyp:P), and
[a cell-grid design](hyp:D), the [residualized denominator](goal) is the sum
over admissible cells of cell mass times the design residual times the
indicator for the displayed event time. -/
noncomputable def residualDenom (P : EventStudySystem T)
    (D : P.ConventionalDesign) : ℝ :=
  ∑ ge ∈ P.admissibleCells D.eventSupport,
    P.cellMassAtEvent ge.1 ge.2 * D.Rdot ge.1 ge.2 *
      eventIndicator D.displayedEvent ge.2

/-- For a [finite time horizon](hyp:T), [an event-study system](hyp:P), and
[a cell-grid design](hyp:D), the [residualized numerator](goal) is the sum over
admissible cells of cell mass times the design residual times the observed cell
mean. -/
noncomputable def residualNumerator (P : EventStudySystem T)
    (D : P.ConventionalDesign) : ℝ :=
  ∑ ge ∈ P.admissibleCells D.eventSupport,
    P.cellMassAtEvent ge.1 ge.2 * D.Rdot ge.1 ge.2 *
      P.observedCellMean ge.1 ge.2

/-- For a [finite time horizon](hyp:T), [an event-study system](hyp:P), and
[an event-study design](hyp:D), the [cell-grid coefficient ratio](goal) is the
residualized numerator divided by the residualized denominator. -/
noncomputable def conventionalMuRatio (P : EventStudySystem T)
    (D : P.ConventionalDesign) : ℝ :=
  P.residualNumerator D / P.residualDenom D

/-- Transparent finite support bookkeeping for the conventional cell expansion.
It records that the explicit event-time support is the finite universe over
which the displayed theorem is expanded, without asserting the headline
contamination formula itself. -/
structure ConventionalFiniteSupport (P : EventStudySystem T)
    (D : P.ConventionalDesign) : Prop where
  hIncludedInSupport : ∀ e ∈ D.includedEvents, e ∈ D.eventSupport
  hDisplayedInSupport : D.displayedEvent ∈ D.eventSupport
  hCellsSupported :
    ∀ ge ∈ P.admissibleCells D.eventSupport, ge.1 ∈ P.cohorts ∧ ge.2 ∈ D.eventSupport

/-- For a [finite time horizon](hyp:T), [an event-study system](hyp:P),
[a cell-grid design](hyp:D), [a cohort](hyp:g), and [a relative time](hyp:e),
the [cell-grid contamination weight](goal) is that cell's mass times its
design residual, divided by the residualized denominator. -/
noncomputable def omega (P : EventStudySystem T) (D : P.ConventionalDesign)
    (g : Fin T) (e : ℤ) : ℝ :=
  (P.cellMassAtEvent g e * D.Rdot g e) / P.residualDenom D

/-- Desired-event-time weights sum to one. -/
theorem desired_event_weights_sum_one (P : EventStudySystem T)
    (D : P.ConventionalDesign)
    (hDisplayedExpansion :
      ∑ ge ∈ P.admissibleCells D.eventSupport,
        P.cellMassAtEvent ge.1 ge.2 * D.Rdot ge.1 ge.2 *
          eventIndicator D.displayedEvent ge.2 =
        ∑ g ∈ P.cohortsAtEvent D.eventSupport D.displayedEvent,
          P.cellMassAtEvent g D.displayedEvent * D.Rdot g D.displayedEvent)
    (hDenomPos : 0 < P.residualDenom D) :
    ∑ g ∈ P.cohortsAtEvent D.eventSupport D.displayedEvent,
      P.omega D g D.displayedEvent = 1 := by
  have hDenom_ne : P.residualDenom D ≠ 0 := ne_of_gt hDenomPos
  calc
    ∑ g ∈ P.cohortsAtEvent D.eventSupport D.displayedEvent,
        P.omega D g D.displayedEvent =
        (∑ g ∈ P.cohortsAtEvent D.eventSupport D.displayedEvent,
          P.cellMassAtEvent g D.displayedEvent * D.Rdot g D.displayedEvent) /
          P.residualDenom D := by
      simp [omega, Finset.sum_div]
    _ = P.residualDenom D / P.residualDenom D := by
      rw [← hDisplayedExpansion]
      rfl
    _ = 1 := div_self hDenom_ne

/-- Other included-event-time weights sum to zero. -/
theorem other_included_event_weights_sum_zero (P : EventStudySystem T)
    (D : P.ConventionalDesign) {e : ℤ}
    (hOtherZero :
      ∑ g ∈ P.cohortsAtEvent D.eventSupport e,
        P.cellMassAtEvent g e * D.Rdot g e = 0)
    (hDenomPos : 0 < P.residualDenom D) :
    ∑ g ∈ P.cohortsAtEvent D.eventSupport e, P.omega D g e = 0 := by
  have _ : P.residualDenom D ≠ 0 := ne_of_gt hDenomPos
  calc
    ∑ g ∈ P.cohortsAtEvent D.eventSupport e, P.omega D g e =
        (∑ g ∈ P.cohortsAtEvent D.eventSupport e,
          P.cellMassAtEvent g e * D.Rdot g e) / P.residualDenom D := by
      simp [omega, Finset.sum_div]
    _ = 0 / P.residualDenom D := by
      rw [hOtherZero]
    _ = 0 := zero_div _

/-- **Finite-cell contamination representation.**
[For an event-study system and cell-grid design](hyp:P,D), if
[observed outcomes equal the own-path potential-outcome means](hyp:hConsistency),
[never-treated means obey additive parallel trends](hyp:hMeanParallelUntreated),
[`Rdot` is orthogonal to every event-study nuisance function](hyp:hNuisanceOrthogonal),
[the residualized denominator is strictly positive](hyp:hDenomPos),
[`D.mu` equals its FWL residualized ratio](hyp:hMuRatio), and
[the included, displayed, and admissible event times have finite support](hyp:hSupport), then
[`D.mu` equals the contamination-weighted sum of CATTs over admissible cells](goal).

Takes the FWL ratio identity `D.mu = conventionalMuRatio D` and the finite-cell
orthogonality conditions `ConventionalResidualization` as hypotheses. See
`cellGrid_mu_eq_conventionalMuRatio`, `cellGrid_provides_residualization`, and
the public wrappers in `Contamination.lean` for the projection-derived entry
points. -/
theorem contamination_representation (P : EventStudySystem T)
    (D : P.ConventionalDesign)
    (hConsistency : P.Consistency)
    (hMeanParallelUntreated : P.MeanParallelUntreated)
    (hNuisanceOrthogonal :
      ∀ h : Fin T → Fin T → ℝ, P.IsEventStudyNuisance D h →
        ∑ ge ∈ P.admissibleCells D.eventSupport,
          P.cellMassAtEvent ge.1 ge.2 * D.Rdot ge.1 ge.2 *
            P.cellAverage h ge.1 ge.2 = 0)
    (hDenomPos : 0 < P.residualDenom D)
    (hMuRatio : D.mu = P.conventionalMuRatio D)
    (hSupport : P.ConventionalFiniteSupport D) :
    D.mu =
      ∑ ge ∈ P.admissibleCells D.eventSupport,
        P.omega D ge.1 ge.2 * P.CATT ge.1 ge.2 := by
  have _ : P.residualDenom D ≠ 0 := ne_of_gt hDenomPos
  rcases hMeanParallelUntreated with ⟨hAdd, ⟨alpha, lambda, hAdd_eq⟩, hUntreated⟩
  let hFE : Fin T → Fin T → ℝ := fun g t => alpha g + lambda t
  have hNuisance : P.IsEventStudyNuisance D hFE := by
    refine ⟨hFE, ⟨alpha, lambda, ?_⟩, fun _ => 0, ?_⟩
    · intro g t
      rfl
    intro g hg t
    simp [hFE]
  have hFE_zero :
      ∑ ge ∈ P.admissibleCells D.eventSupport,
        P.cellMassAtEvent ge.1 ge.2 * D.Rdot ge.1 ge.2 *
          P.cellAverage hFE ge.1 ge.2 = 0 :=
    hNuisanceOrthogonal hFE hNuisance
  have hObs :
      ∀ ge ∈ P.admissibleCells D.eventSupport,
        P.observedCellMean ge.1 ge.2 =
          P.cellAverage hFE ge.1 ge.2 + P.CATT ge.1 ge.2 := by
    intro ge hge
    have hg : ge.1 ∈ P.cohorts := (hSupport.hCellsSupported ge hge).1
    unfold observedCellMean cellAverage hFE
    change
      ((P.targetPeriods ge.1 ge.2).card : ℝ)⁻¹ *
          ∑ t ∈ P.targetPeriods ge.1 ge.2, P.observedMean ge.1 t =
        ((P.targetPeriods ge.1 ge.2).card : ℝ)⁻¹ *
            ∑ t ∈ P.targetPeriods ge.1 ge.2, (alpha ge.1 + lambda t) +
          ((P.targetPeriods ge.1 ge.2).card : ℝ)⁻¹ *
            ∑ t ∈ P.targetPeriods ge.1 ge.2,
              (P.treatedMean ge.1 t - P.untreatedMean ge.1 t)
    have hsum :
        (∑ t ∈ P.targetPeriods ge.1 ge.2, P.observedMean ge.1 t) =
          (∑ t ∈ P.targetPeriods ge.1 ge.2, (alpha ge.1 + lambda t)) +
            ∑ t ∈ P.targetPeriods ge.1 ge.2,
              (P.treatedMean ge.1 t - P.untreatedMean ge.1 t) := by
      calc
        (∑ t ∈ P.targetPeriods ge.1 ge.2, P.observedMean ge.1 t) =
            ∑ t ∈ P.targetPeriods ge.1 ge.2,
              ((alpha ge.1 + lambda t) +
                (P.treatedMean ge.1 t - P.untreatedMean ge.1 t)) := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [hConsistency ge.1 hg t, hUntreated ge.1 hg t, hAdd_eq ge.1 t]
          ring
        _ = (∑ t ∈ P.targetPeriods ge.1 ge.2, (alpha ge.1 + lambda t)) +
            ∑ t ∈ P.targetPeriods ge.1 ge.2,
              (P.treatedMean ge.1 t - P.untreatedMean ge.1 t) := by
          rw [Finset.sum_add_distrib]
    rw [hsum, mul_add]
  have hNumerator :
      P.residualNumerator D =
        ∑ ge ∈ P.admissibleCells D.eventSupport,
          P.cellMassAtEvent ge.1 ge.2 * D.Rdot ge.1 ge.2 *
            P.CATT ge.1 ge.2 := by
    unfold residualNumerator
    calc
      ∑ ge ∈ P.admissibleCells D.eventSupport,
          P.cellMassAtEvent ge.1 ge.2 * D.Rdot ge.1 ge.2 *
            P.observedCellMean ge.1 ge.2 =
          ∑ ge ∈ P.admissibleCells D.eventSupport,
            P.cellMassAtEvent ge.1 ge.2 * D.Rdot ge.1 ge.2 *
              (P.cellAverage hFE ge.1 ge.2 + P.CATT ge.1 ge.2) := by
        apply Finset.sum_congr rfl
        intro ge hge
        rw [hObs ge hge]
      _ =
          (∑ ge ∈ P.admissibleCells D.eventSupport,
            P.cellMassAtEvent ge.1 ge.2 * D.Rdot ge.1 ge.2 *
              P.cellAverage hFE ge.1 ge.2) +
          ∑ ge ∈ P.admissibleCells D.eventSupport,
            P.cellMassAtEvent ge.1 ge.2 * D.Rdot ge.1 ge.2 *
              P.CATT ge.1 ge.2 := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib]
      _ =
          ∑ ge ∈ P.admissibleCells D.eventSupport,
            P.cellMassAtEvent ge.1 ge.2 * D.Rdot ge.1 ge.2 *
              P.CATT ge.1 ge.2 := by
        rw [hFE_zero, zero_add]
  calc
    D.mu = P.residualNumerator D / P.residualDenom D := hMuRatio
    _ =
        (∑ ge ∈ P.admissibleCells D.eventSupport,
          P.cellMassAtEvent ge.1 ge.2 * D.Rdot ge.1 ge.2 *
            P.CATT ge.1 ge.2) / P.residualDenom D := by
      rw [hNumerator]
    _ =
        ∑ ge ∈ P.admissibleCells D.eventSupport,
          P.omega D ge.1 ge.2 * P.CATT ge.1 ge.2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro ge hge
      simp [omega]
      ring

set_option linter.flexible false in
/-- [For an event-study system and cell-grid design](hyp:P,D), if
[observed outcomes equal the own-path potential-outcome means](hyp:hConsistency),
[never-treated means obey additive parallel trends](hyp:hMeanParallelUntreated),
[the design satisfies the finite-cell orthogonality conditions](hyp:hResidualization),
[the residualized denominator is strictly positive](hyp:hDenomPos),
[`D.mu` equals its FWL residualized ratio](hyp:hMuRatio), and
[the included, displayed, and admissible event times have finite support](hyp:hSupport), then
[`D.mu` splits into its displayed-event term and all other admissible-cell terms](goal). -/
theorem contamination_representation_split (P : EventStudySystem T)
    (D : P.ConventionalDesign)
    (hConsistency : P.Consistency)
    (hMeanParallelUntreated : P.MeanParallelUntreated)
    (hResidualization : P.ConventionalResidualization D)
    (hDenomPos : 0 < P.residualDenom D)
    (hMuRatio : D.mu = P.conventionalMuRatio D)
    (hSupport : P.ConventionalFiniteSupport D) :
    D.mu =
      (∑ g ∈ P.cohortsAtEvent D.eventSupport D.displayedEvent,
        P.omega D g D.displayedEvent * P.CATT g D.displayedEvent) +
      (∑ ge ∈ (P.admissibleCells D.eventSupport).filter
          (fun ge => ge.2 ≠ D.displayedEvent),
        P.omega D ge.1 ge.2 * P.CATT ge.1 ge.2) := by
  let F : Fin T × ℤ → ℝ := fun ge => P.omega D ge.1 ge.2 * P.CATT ge.1 ge.2
  have hMain :
      D.mu = ∑ ge ∈ P.admissibleCells D.eventSupport, F ge := by
    simpa [F] using
      contamination_representation P D hConsistency
        hMeanParallelUntreated hResidualization.hResidualization hDenomPos
        hMuRatio hSupport
  have hDisplayedCells :
      (P.admissibleCells D.eventSupport).filter
          (fun ge => ge.2 = D.displayedEvent) =
        (P.cohortsAtEvent D.eventSupport D.displayedEvent).map
          ⟨fun g => (g, D.displayedEvent),
            by
              intro a b h
              exact congrArg Prod.fst h⟩ := by
    ext ge
    rcases ge with ⟨g, e⟩
    simp [admissibleCells, cohortsAtEvent]
    constructor
    · rintro ⟨⟨⟨hg, heSupport⟩, hAdm⟩, rfl⟩
      exact ⟨g, ⟨hg, heSupport, hAdm⟩, rfl⟩
    · rintro ⟨a, ⟨hg, hDisplayedSupport, hAdm⟩, hEq⟩
      -- `simp` no longer reduces the `Function.Embedding` structure-literal application,
      -- so restate the pair equation in reduced form (definitionally equal).
      have hEq' : (a, D.displayedEvent) = (g, e) := hEq
      have ha : a = g := congrArg Prod.fst hEq'
      have he : D.displayedEvent = e := congrArg Prod.snd hEq'
      subst ha
      subst he
      exact ⟨⟨⟨hg, hDisplayedSupport⟩, hAdm⟩, rfl⟩
  calc
    D.mu = ∑ ge ∈ P.admissibleCells D.eventSupport, F ge := hMain
    _ =
        (∑ ge ∈ (P.admissibleCells D.eventSupport).filter
          (fun ge => ge.2 = D.displayedEvent), F ge) +
        (∑ ge ∈ (P.admissibleCells D.eventSupport).filter
          (fun ge => ge.2 ≠ D.displayedEvent), F ge) := by
      exact (Finset.sum_filter_add_sum_filter_not
        (P.admissibleCells D.eventSupport)
        (fun ge : Fin T × ℤ => ge.2 = D.displayedEvent) F).symm
    _ =
        (∑ g ∈ P.cohortsAtEvent D.eventSupport D.displayedEvent,
          P.omega D g D.displayedEvent * P.CATT g D.displayedEvent) +
        (∑ ge ∈ (P.admissibleCells D.eventSupport).filter
          (fun ge => ge.2 ≠ D.displayedEvent),
          P.omega D ge.1 ge.2 * P.CATT ge.1 ge.2) := by
      rw [hDisplayedCells, Finset.sum_map]
      rfl

set_option linter.unusedVariables false in
/-- [For an event-study system and cell-grid design](hyp:P,D), if
[the displayed event is a lead](hyp:hLead),
[the consistency, parallel-trends, and no-anticipation restrictions hold](hyp:hCausal),
[`Rdot` is orthogonal to every event-study nuisance function](hyp:hNuisanceOrthogonal),
[the residualized denominator is strictly positive](hyp:hDenomPos),
[`D.mu` equals its FWL residualized ratio](hyp:hMuRatio), and
[the included, displayed, and admissible event times have finite support](hyp:hSupport), then
[`D.mu` is a generally signed contamination-weighted sum of nonnegative-event-time CATTs](goal).
-/
theorem apparent_pretrends_from_post_treatment (P : EventStudySystem T)
    (D : P.ConventionalDesign)
    (hLead : D.displayedEvent < 0)
    (hCausal : P.EventStudyCausalRestrictions)
    (hNuisanceOrthogonal :
      ∀ h : Fin T → Fin T → ℝ, P.IsEventStudyNuisance D h →
        ∑ ge ∈ P.admissibleCells D.eventSupport,
          P.cellMassAtEvent ge.1 ge.2 * D.Rdot ge.1 ge.2 *
            P.cellAverage h ge.1 ge.2 = 0)
    (hDenomPos : 0 < P.residualDenom D)
    (hMuRatio : D.mu = P.conventionalMuRatio D)
    (hSupport : P.ConventionalFiniteSupport D) :
    D.mu =
      ∑ ge ∈ (P.admissibleCells D.eventSupport).filter (fun ge => 0 ≤ ge.2),
        P.omega D ge.1 ge.2 * P.CATT ge.1 ge.2 := by
  let F : Fin T × ℤ → ℝ := fun ge => P.omega D ge.1 ge.2 * P.CATT ge.1 ge.2
  have hMain :
      D.mu = ∑ ge ∈ P.admissibleCells D.eventSupport, F ge := by
    simpa [F] using
      contamination_representation P D hCausal.hConsistency
        hCausal.hMeanParallelUntreated hNuisanceOrthogonal hDenomPos
        hMuRatio hSupport
  have hNegZero :
      ∑ ge ∈ (P.admissibleCells D.eventSupport).filter
          (fun ge => ¬ 0 ≤ ge.2), F ge = 0 := by
    apply Finset.sum_eq_zero
    intro ge hge
    have hmem : ge ∈ P.admissibleCells D.eventSupport := (Finset.mem_filter.mp hge).1
    have hneg : ¬ 0 ≤ ge.2 := (Finset.mem_filter.mp hge).2
    have hlt : ge.2 < 0 := not_le.mp hneg
    have hg : ge.1 ∈ P.cohorts := (hSupport.hCellsSupported ge hmem).1
    simp [F, P.CATT_eq_zero_of_noAnticipation hCausal.hNoAnticipation hg hlt]
  calc
    D.mu = ∑ ge ∈ P.admissibleCells D.eventSupport, F ge := hMain
    _ =
        (∑ ge ∈ (P.admissibleCells D.eventSupport).filter
          (fun ge => 0 ≤ ge.2), F ge) +
        (∑ ge ∈ (P.admissibleCells D.eventSupport).filter
          (fun ge => ¬ 0 ≤ ge.2), F ge) := by
      exact (Finset.sum_filter_add_sum_filter_not
        (P.admissibleCells D.eventSupport)
        (fun ge : Fin T × ℤ => 0 ≤ ge.2) F).symm
    _ = ∑ ge ∈ (P.admissibleCells D.eventSupport).filter
          (fun ge => 0 ≤ ge.2), F ge := by
      rw [hNegZero, add_zero]

end EventStudySystem

end EventStudyContamination
end Panel.EstimandCharacterization
end Causalean
