/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Listed-cohort cell-grid weighted residualization

Derives the finite-cell orthogonality conditions recorded by
`ConventionalResidualization` and the coefficient identity `D.mu =
conventionalMuRatio` from a weighted projection on the cohort-relative-time
cell grid.

The cell grid is the finite empirical population `↥(admissibleCells)` carrying
the normalized cell masses `cellMassAtEvent / Z`.  Its weighted inner product
reproduces the finite-cell sums verbatim, so:

* `residualize_in_orthogonal` (the residual `Rdot = tildeX H R` is `⟨·,·⟩_ω`-
  orthogonal to the nuisance span `H`) gives `hResidualization` and
  `hOtherIncludedOrthogonal`;
* `hDisplayedExpansion` is a pure finite-sum filtering identity;
* `scalar_fwl_of_normalEqs` gives `D.mu = conventionalMuRatio`.

The inputs are: (i) `Rdot` is the weighted residual of the displayed-event
indicator against the cell-nuisance span, and (ii) `D.mu` solves the weighted
normal equations, i.e. is the projection coefficient. Cell-mass positivity on
admissible cells is a population-regularity hypothesis. This grid contains only
the cohorts listed in `P.cohorts` and relative times in `D.eventSupport`; it does
not include the never-treated path.
-/

module
public import Causalean.Panel.EstimandCharacterization.EventStudyContamination.Conventional
public import Causalean.Stat.Weighted.ScalarFWL

/-! # Listed-Cohort Cell-Grid Projection

This file derives finite-cell residualization and ratio identities from a
weighted projection on the listed-cohort-by-relative-time cell grid. The grid
omits the never-treated path and every cell outside the declared event support,
so it is not identified here with a full-population TWFE regression. The
resulting bridge supplies the orthogonality and normal-equation inputs used by
the contamination representation. -/

@[expose] public section

namespace Causalean
namespace Panel.EstimandCharacterization
namespace EventStudyContamination

open Finset Causalean.Stat.Weighted

namespace EventStudySystem

variable {T : ℕ}

/-- For a [finite time horizon](hyp:T), [an event-study system](hyp:P), and
[a cell-grid design](hyp:D), the [cell index](goal) is the collection of
admissible cohort--relative-time cells in that design. -/
abbrev CellIndex (P : EventStudySystem T) (D : P.ConventionalDesign) : Type :=
  {ge : Fin T × ℤ // ge ∈ P.admissibleCells D.eventSupport}

/-- For a [finite time horizon](hyp:T), [an event-study system](hyp:P), and
[a cell-grid design](hyp:D), the [total admissible cell mass](goal) is the sum
of the population masses of all admissible cohort--relative-time cells. -/
noncomputable def cellTotalMass (P : EventStudySystem T) (D : P.ConventionalDesign) : ℝ :=
  ∑ ge ∈ P.admissibleCells D.eventSupport, P.cellMassAtEvent ge.1 ge.2

/-- For a [finite time horizon](hyp:T), [an event-study system](hyp:P), and
[a cell-grid design](hyp:D), if
[every admissible cohort--relative-time cell has strictly positive population mass](hyp:hpos)
and [at least one admissible cell exists](hyp:hne), the [cell-grid weighted support](goal) is the
finite
population of admissible cells, weighted by each cell's mass divided by total
admissible cell mass.

The cell-grid weighted support: the empirical population over admissible
cells with weight `cellMassAtEvent / Z`. -/
noncomputable def cellSupport (P : EventStudySystem T) (D : P.ConventionalDesign)
    (hpos : ∀ ge ∈ P.admissibleCells D.eventSupport, 0 < P.cellMassAtEvent ge.1 ge.2)
    (hne : (P.admissibleCells D.eventSupport).Nonempty) :
    WeightedSupport (P.CellIndex D) where
  observed := Finset.univ
  observed_nonempty := by
    classical
    rw [Finset.univ_nonempty_iff]
    obtain ⟨ge, hge⟩ := hne
    exact ⟨⟨ge, hge⟩⟩
  weight := fun cell => P.cellMassAtEvent cell.val.1 cell.val.2 / P.cellTotalMass D
  weight_pos := by
    intro cell _
    have hZ : 0 < P.cellTotalMass D :=
      Finset.sum_pos (fun ge hge => hpos ge hge) hne
    exact div_pos (hpos cell.val cell.property) hZ
  weight_zero_off := by
    intro cell hcell
    exact absurd (Finset.mem_univ cell) hcell
  weight_sum_one := by
    classical
    have hZ : 0 < P.cellTotalMass D :=
      Finset.sum_pos (fun ge hge => hpos ge hge) hne
    have hsum :
        ∑ cell : P.CellIndex D,
            P.cellMassAtEvent cell.val.1 cell.val.2 / P.cellTotalMass D =
          (∑ cell : P.CellIndex D,
            P.cellMassAtEvent cell.val.1 cell.val.2) / P.cellTotalMass D := by
      rw [← Finset.sum_div]
    rw [show (Finset.univ : Finset (P.CellIndex D)) = Finset.univ from rfl, hsum]
    rw [Finset.sum_coe_sort (P.admissibleCells D.eventSupport)
        (fun ge => P.cellMassAtEvent ge.1 ge.2)]
    rw [← cellTotalMass]
    exact div_self hZ.ne'

/-- **ip → cell-sum.** The cell-grid weighted inner product of two cell
functions reproduces the finite-cell sum (divided by the total mass `Z`).
This is the bridge that turns weighted-projection facts into the finite-cell
orthogonality conditions. -/
lemma ip_cellSupport (P : EventStudySystem T) (D : P.ConventionalDesign)
    (hpos : ∀ ge ∈ P.admissibleCells D.eventSupport, 0 < P.cellMassAtEvent ge.1 ge.2)
    (hne : (P.admissibleCells D.eventSupport).Nonempty)
    (A B : Fin T × ℤ → ℝ) :
    (P.cellSupport D hpos hne).ip (fun cell => A cell.val) (fun cell => B cell.val)
      = (∑ ge ∈ P.admissibleCells D.eventSupport,
          P.cellMassAtEvent ge.1 ge.2 * A ge * B ge) / P.cellTotalMass D := by
  classical
  rw [WeightedSupport.ip_def]
  have hobs : (P.cellSupport D hpos hne).observed
      = (Finset.univ : Finset (P.CellIndex D)) := rfl
  rw [hobs]
  rw [show (∑ cell : P.CellIndex D,
        (P.cellSupport D hpos hne).weight cell * A cell.val * B cell.val)
      = ∑ cell : P.CellIndex D,
          (fun ge : Fin T × ℤ =>
            P.cellMassAtEvent ge.1 ge.2 / P.cellTotalMass D * A ge * B ge) cell.val
        from rfl]
  rw [Finset.sum_coe_sort (P.admissibleCells D.eventSupport)
      (fun ge => P.cellMassAtEvent ge.1 ge.2 / P.cellTotalMass D * A ge * B ge)]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun ge _ => ?_)
  ring

/-! ### Cell-nuisance subspace on the cell grid -/

/-- For a [finite time horizon](hyp:T), [an event-study system](hyp:P), and
[a cell-grid design](hyp:D), the [generators of the cell-nuisance space](goal)
are precisely the functions on admissible cells obtained by averaging an
event-study nuisance function within each cohort--relative-time cell. -/
def cellNuisanceGen (P : EventStudySystem T) (D : P.ConventionalDesign) :
    Set (P.CellIndex D → ℝ) :=
  {f | ∃ hCell : Fin T → Fin T → ℝ, P.IsEventStudyNuisance D hCell ∧
        f = fun cell => P.cellAverage hCell cell.val.1 cell.val.2}

/-- For a [finite time horizon](hyp:T), [an event-study system](hyp:P), and
[a cell-grid design](hyp:D), the [cell-nuisance space](goal) is the linear span
of all cell-level averages of event-study nuisance functions. -/
noncomputable def cellNuisance (P : EventStudySystem T) (D : P.ConventionalDesign) :
    Submodule ℝ (P.CellIndex D → ℝ) :=
  Submodule.span ℝ (P.cellNuisanceGen D)

/-- Every cell-evaluated nuisance function lies in the cell-nuisance subspace. -/
lemma cellAverage_mem_cellNuisance (P : EventStudySystem T) (D : P.ConventionalDesign)
    {hCell : Fin T → Fin T → ℝ} (hN : P.IsEventStudyNuisance D hCell) :
    (fun cell : P.CellIndex D => P.cellAverage hCell cell.val.1 cell.val.2)
      ∈ P.cellNuisance D :=
  Submodule.subset_span ⟨hCell, hN, rfl⟩

/-- The cell average of the relative-time indicator `1{relTime = e}`, evaluated
on a nonempty cell `(g, e')`, is the cell-level indicator `1{e' = e}`. -/
lemma cellAverage_eventIndicator (P : EventStudySystem T) {e : ℤ} {g : Fin T} {e' : ℤ}
    (hne : (P.targetPeriods g e').Nonempty) :
    P.cellAverage (fun g t => eventIndicator e (P.relTime g t)) g e'
      = eventIndicator e e' := by
  classical
  have hcard : ((P.targetPeriods g e').card : ℝ) ≠ 0 := by
    have : 0 < (P.targetPeriods g e').card := Finset.card_pos.mpr hne
    exact_mod_cast this.ne'
  unfold EventStudySystem.cellAverage
  have hconst : ∀ t ∈ P.targetPeriods g e',
      eventIndicator e (P.relTime g t) = eventIndicator e e' := by
    intro t ht
    have hrel : P.relTime g t = e' := by simpa [EventStudySystem.targetPeriods] using ht
    rw [hrel]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ hcard, one_mul]

/-- A non-displayed included relative-time indicator lies in the cell-nuisance
subspace (it is the cell average of the corresponding event-study nuisance). -/
lemma eventIndicator_mem_cellNuisance (P : EventStudySystem T) (D : P.ConventionalDesign)
    {e : ℤ} (he_inc : e ∈ D.includedEvents) (he_ne : e ≠ D.displayedEvent) :
    (fun cell : P.CellIndex D => eventIndicator e cell.val.2) ∈ P.cellNuisance D := by
  classical
  have hN : P.IsEventStudyNuisance D (fun g t => eventIndicator e (P.relTime g t)) := by
    refine ⟨fun _ _ => 0, ⟨fun _ => 0, fun _ => 0, fun g t => by simp⟩,
      fun k => if k = e then 1 else 0, ?_⟩
    intro g _ t
    simp only [zero_add]
    rw [Finset.sum_eq_single e]
    · simp
    · intro k _ hkne; simp [hkne]
    · intro hnot
      exact absurd (Finset.mem_filter.mpr ⟨he_inc, he_ne⟩) hnot
  have heq :
      (fun cell : P.CellIndex D =>
          P.cellAverage (fun g t => eventIndicator e (P.relTime g t))
            cell.val.1 cell.val.2)
        = fun cell : P.CellIndex D => eventIndicator e cell.val.2 := by
    funext cell
    have hmem : cell.val ∈ (P.cohorts.product D.eventSupport).filter
        (fun ge => P.AdmissibleCell ge.1 ge.2) := cell.property
    obtain ⟨_, hnonempty⟩ := (Finset.mem_filter.mp hmem).2
    exact P.cellAverage_eventIndicator (e := e) hnonempty
  rw [← heq]
  exact P.cellAverage_mem_cellNuisance D hN

/-- **Cell-grid filtering identity.** Weighting an admissible-cell sum by the
relative-time indicator `1{e = e'}` collapses it to a sum over the cohorts
observed at relative time `e'`. Pure finite algebra; no residualization needed.
This is the engine behind `hDisplayedExpansion` and `hOtherIncludedOrthogonal`. -/
lemma sum_admissible_mul_eventIndicator (P : EventStudySystem T) (D : P.ConventionalDesign)
    (e' : ℤ) (f : Fin T → ℤ → ℝ) :
    ∑ ge ∈ P.admissibleCells D.eventSupport, f ge.1 ge.2 * eventIndicator e' ge.2
      = ∑ g ∈ P.cohortsAtEvent D.eventSupport e', f g e' := by
  classical
  have hfilter :
      (P.admissibleCells D.eventSupport).filter (fun ge => ge.2 = e') =
        (P.cohortsAtEvent D.eventSupport e').map
          ⟨fun g => (g, e'), fun a b h => congrArg Prod.fst h⟩ := by
    ext ge
    rcases ge with ⟨g, e⟩
    simp only [admissibleCells, product_eq_sprod, mem_filter, mem_product, cohortsAtEvent,
      mem_map]
    constructor
    · rintro ⟨⟨⟨hg, heSupport⟩, hAdm⟩, rfl⟩
      exact ⟨g, ⟨hg, heSupport, hAdm⟩, rfl⟩
    · rintro ⟨a, ⟨ha, hSupport, hAdm⟩, hEq⟩
      have hEq' : (a, e') = (g, e) := hEq
      injection hEq' with h1 h2
      subst h1
      subst h2
      exact ⟨⟨⟨ha, hSupport⟩, hAdm⟩, rfl⟩
  calc
    ∑ ge ∈ P.admissibleCells D.eventSupport, f ge.1 ge.2 * eventIndicator e' ge.2
        = ∑ ge ∈ P.admissibleCells D.eventSupport,
            if ge.2 = e' then f ge.1 e' else 0 := by
          refine Finset.sum_congr rfl (fun ge _ => ?_)
          unfold EventStudySystem.eventIndicator
          by_cases h : ge.2 = e'
          · rw [h]; simp
          · simp [h]
    _ = ∑ ge ∈ (P.admissibleCells D.eventSupport).filter (fun ge => ge.2 = e'),
            f ge.1 e' := by
          rw [Finset.sum_filter]
    _ = ∑ g ∈ P.cohortsAtEvent D.eventSupport e', f g e' := by
          rw [hfilter, Finset.sum_map]
          rfl

/-! ### Genuine cell-grid residualization input -/

/-- For a [finite time horizon](hyp:T), [an event-study system](hyp:P), and
[a cell-grid design](hyp:D), the [cell-grid regressor](goal) assigns one to an
admissible cell exactly when its relative time is the displayed event time, and
zero otherwise. -/
noncomputable def cellRegressor (P : EventStudySystem T) (D : P.ConventionalDesign) :
    P.CellIndex D → ℝ :=
  fun cell => eventIndicator D.displayedEvent cell.val.2

/-- For a [finite time horizon](hyp:T), [an event-study system](hyp:P), and
[a cell-grid design](hyp:D), the [cell-grid outcome](goal) assigns to each
admissible cohort--relative-time cell its observed mean outcome. -/
noncomputable def cellOutcome (P : EventStudySystem T) (D : P.ConventionalDesign) :
    P.CellIndex D → ℝ :=
  fun cell => P.observedCellMean cell.val.1 cell.val.2

/-- **Cell-grid residualization input.**
[An event-study design on a finite system](hyp:P,D) is backed by a well-posed weighted
cell-grid projection when [every admissible cell has positive mass](hyp:hCellMassPos),
[the grid is nonempty](hyp:hCellNonempty),
[the residualized regressor has positive energy](hyp:hDenomPos),
[the recorded residual is the projected displayed indicator](hyp:hRdotResidual),
and
[a nuisance fit satisfies both normal equations](hyp:hMuNormalEqs).

From these fields, the finite-cell orthogonality conditions and the identity
`D.mu = conventionalMuRatio` are derived. -/
structure CellGridResidualization (P : EventStudySystem T)
    (D : P.ConventionalDesign) : Prop where
  hCellMassPos : ∀ ge ∈ P.admissibleCells D.eventSupport,
    0 < P.cellMassAtEvent ge.1 ge.2
  hCellNonempty : (P.admissibleCells D.eventSupport).Nonempty
  hDenomPos : 0 < P.residualDenom D
  hRdotResidual : ∀ cell : P.CellIndex D,
    D.Rdot cell.val.1 cell.val.2
      = (P.cellSupport D hCellMassPos hCellNonempty).tildeX (P.cellNuisance D)
          (P.cellRegressor D) cell
  hMuNormalEqs : ∃ α : P.CellIndex D → ℝ, α ∈ P.cellNuisance D ∧
    (P.cellSupport D hCellMassPos hCellNonempty).ip
        (P.cellOutcome D - D.mu • P.cellRegressor D - α) (P.cellRegressor D) = 0 ∧
    (∀ h ∈ P.cellNuisance D,
      (P.cellSupport D hCellMassPos hCellNonempty).ip
        (P.cellOutcome D - D.mu • P.cellRegressor D - α) h = 0)

variable {P : EventStudySystem T} {D : P.ConventionalDesign}

/-- Under cell-grid residualization, the residualized displayed-event regressor equals the
design residual at every admissible cohort--relative-time cell. -/
lemma tildeX_eq_Rdot (h : P.CellGridResidualization D) :
    (P.cellSupport D h.hCellMassPos h.hCellNonempty).tildeX (P.cellNuisance D)
        (P.cellRegressor D)
      = fun cell => D.Rdot cell.val.1 cell.val.2 := by
  funext cell; exact (h.hRdotResidual cell).symm

/-- **Cell-grid FWL bridge.**
[Under cell-grid residualization of the event-study design](hyp:h),
[the recorded coefficient equals the FWL residualized ratio on the cell grid](goal).

This is derived from the weighted normal equations via `scalar_fwl_of_normalEqs`. -/
theorem cellGrid_mu_eq_conventionalMuRatio (h : P.CellGridResidualization D) :
    D.mu = P.conventionalMuRatio D := by
  classical
  have hZpos : 0 < P.cellTotalMass D :=
    Finset.sum_pos (fun ge hge => h.hCellMassPos ge hge) h.hCellNonempty
  have hZ : P.cellTotalMass D ≠ 0 := hZpos.ne'
  have hRdot := tildeX_eq_Rdot h
  have hnum :
      (P.cellSupport D h.hCellMassPos h.hCellNonempty).ip
          ((P.cellSupport D h.hCellMassPos h.hCellNonempty).tildeX (P.cellNuisance D)
            (P.cellRegressor D))
          (P.cellOutcome D)
        = P.residualNumerator D / P.cellTotalMass D := by
    rw [hRdot]
    exact P.ip_cellSupport D h.hCellMassPos h.hCellNonempty
      (fun ge => D.Rdot ge.1 ge.2) (fun ge => P.observedCellMean ge.1 ge.2)
  have hden :
      (P.cellSupport D h.hCellMassPos h.hCellNonempty).ip
          ((P.cellSupport D h.hCellMassPos h.hCellNonempty).tildeX (P.cellNuisance D)
            (P.cellRegressor D))
          ((P.cellSupport D h.hCellMassPos h.hCellNonempty).tildeX (P.cellNuisance D)
            (P.cellRegressor D))
        = P.residualDenom D / P.cellTotalMass D := by
    rw [← (P.cellSupport D h.hCellMassPos h.hCellNonempty).ip_tildeX_self
        (P.cellNuisance D) (P.cellRegressor D), hRdot]
    exact P.ip_cellSupport D h.hCellMassPos h.hCellNonempty
      (fun ge => D.Rdot ge.1 ge.2) (fun ge => eventIndicator D.displayedEvent ge.2)
  have hpos_ip :
      0 < (P.cellSupport D h.hCellMassPos h.hCellNonempty).ip
        ((P.cellSupport D h.hCellMassPos h.hCellNonempty).tildeX (P.cellNuisance D)
          (P.cellRegressor D))
        ((P.cellSupport D h.hCellMassPos h.hCellNonempty).tildeX (P.cellNuisance D)
          (P.cellRegressor D)) := by
    rw [hden]; exact div_pos h.hDenomPos hZpos
  obtain ⟨α, hα_mem, hNR, hNH⟩ := h.hMuNormalEqs
  have hmu := (P.cellSupport D h.hCellMassPos h.hCellNonempty).scalar_fwl_of_normalEqs
    (P.cellNuisance D) (P.cellRegressor D) (P.cellOutcome D) D.mu α
    hα_mem hpos_ip.ne' hNR hNH
  rw [hmu, hnum, hden, EventStudySystem.conventionalMuRatio]
  have hDen : P.residualDenom D ≠ 0 := h.hDenomPos.ne'
  field_simp

/-- For an event-study design `D` over an event-study system `P`, if
[every admissible cell has strictly positive population mass](hyp:hCellMassPos),
[the collection of admissible cells is nonempty](hyp:hCellNonempty), and
[`Rdot` agrees cellwise with the weighted cell-grid projection residual](hyp:hRdotResidual),
then
[the three finite-cell orthogonality conditions hold for `D` as projection consequences](goal).
-/
theorem cellGrid_provides_residualization
    (hCellMassPos : ∀ ge ∈ P.admissibleCells D.eventSupport,
      0 < P.cellMassAtEvent ge.1 ge.2)
    (hCellNonempty : (P.admissibleCells D.eventSupport).Nonempty)
    (hRdotResidual : ∀ cell : P.CellIndex D,
      D.Rdot cell.val.1 cell.val.2
        = (P.cellSupport D hCellMassPos hCellNonempty).tildeX (P.cellNuisance D)
            (P.cellRegressor D) cell) :
    P.ConventionalResidualization D := by
  classical
  have hZpos : 0 < P.cellTotalMass D :=
    Finset.sum_pos (fun ge hge => hCellMassPos ge hge) hCellNonempty
  have hZ : P.cellTotalMass D ≠ 0 := hZpos.ne'
  have hRdot :
      (P.cellSupport D hCellMassPos hCellNonempty).tildeX (P.cellNuisance D)
          (P.cellRegressor D) = fun cell => D.Rdot cell.val.1 cell.val.2 := by
    funext cell
    exact (hRdotResidual cell).symm
  refine ⟨?_, ?_, ?_⟩
  · -- hResidualization
    intro hCell hN
    have hmem := P.cellAverage_mem_cellNuisance D hN
    have hortho := (P.cellSupport D hCellMassPos hCellNonempty).residualize_in_orthogonal
      (P.cellNuisance D) (P.cellRegressor D) hmem
    rw [hRdot] at hortho
    have hip :
        (P.cellSupport D hCellMassPos hCellNonempty).ip
            (fun cell => D.Rdot cell.val.1 cell.val.2)
            (fun cell => P.cellAverage hCell cell.val.1 cell.val.2)
          = (∑ ge ∈ P.admissibleCells D.eventSupport,
              P.cellMassAtEvent ge.1 ge.2 * D.Rdot ge.1 ge.2
                * P.cellAverage hCell ge.1 ge.2) / P.cellTotalMass D :=
      P.ip_cellSupport D hCellMassPos hCellNonempty
        (fun ge => D.Rdot ge.1 ge.2) (fun ge => P.cellAverage hCell ge.1 ge.2)
    rw [hip] at hortho
    exact (div_eq_zero_iff.mp hortho).resolve_right hZ
  · -- hDisplayedExpansion
    exact P.sum_admissible_mul_eventIndicator D D.displayedEvent
      (fun g e => P.cellMassAtEvent g e * D.Rdot g e)
  · -- hOtherIncludedOrthogonal
    intro e he_inc he_ne
    have hmem := P.eventIndicator_mem_cellNuisance D he_inc he_ne
    have hortho := (P.cellSupport D hCellMassPos hCellNonempty).residualize_in_orthogonal
      (P.cellNuisance D) (P.cellRegressor D) hmem
    rw [hRdot] at hortho
    have hip :
        (P.cellSupport D hCellMassPos hCellNonempty).ip
            (fun cell => D.Rdot cell.val.1 cell.val.2)
            (fun cell => eventIndicator e cell.val.2)
          = (∑ ge ∈ P.admissibleCells D.eventSupport,
              P.cellMassAtEvent ge.1 ge.2 * D.Rdot ge.1 ge.2
                * eventIndicator e ge.2) / P.cellTotalMass D :=
      P.ip_cellSupport D hCellMassPos hCellNonempty
        (fun ge => D.Rdot ge.1 ge.2) (fun ge => eventIndicator e ge.2)
    rw [hip] at hortho
    have hsum0 :
        ∑ ge ∈ P.admissibleCells D.eventSupport,
          P.cellMassAtEvent ge.1 ge.2 * D.Rdot ge.1 ge.2 * eventIndicator e ge.2 = 0 :=
      (div_eq_zero_iff.mp hortho).resolve_right hZ
    rw [← P.sum_admissible_mul_eventIndicator D e
      (fun g e0 => P.cellMassAtEvent g e0 * D.Rdot g e0)]
    exact hsum0

end EventStudySystem

end EventStudyContamination
end Panel.EstimandCharacterization
end Causalean
