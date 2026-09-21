/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Flexible imputation / POLS / ETWFE finite-cell scaffold

Finite-cell primitives for a flexible-DID algebraic scaffold: primitive cohort
shares, covariate weights, conditional means, treated/untreated cell predicates,
support assumptions, finite-cell normal equations, and cell/aggregate equality
theorems. Adoption timing and estimator-specific regression designs are not
constructed here.
-/

module
public import Causalean.Panel.EstimandCharacterization.FlexibleDIDMundlak.TWFE

/-! # Wooldridge Flexible DID Cells

This file provides finite-cell primitives for Wooldridge-style flexible
imputation, pooled least squares, and extended two-way fixed effects
difference-in-differences calculations. It takes the treated and untreated
cohort-period cells as arbitrary predicates, rather than deriving them from an
adoption process. It defines cell means, support conditions, untreated-outcome
regressions, normal-equation-based POLS/ETWFE coefficient candidates, and
weighted linear aggregates of cell effects. The main
public theorem is `flexible_did_scaffold_consequences`, which records the
algebraic consequences of supplying the estimator-specific normal equations;
the file does not construct POLS or ETWFE regressions from design matrices. -/

@[expose] public section

namespace Causalean
namespace Panel.EstimandCharacterization
namespace FlexibleDIDMundlak

open Finset

variable {Cohort Time Covar : Type*}
  [Fintype Cohort] [Fintype Time] [Fintype Covar]

/-- Finite cohort-period cell scaffold: [cohort shares](hyp:cohortShare) and
[within-cohort covariate weights](hyp:covarWeight) over [treated](hyp:treatedCell) and
[untreated](hyp:untreatedCell) cohort-time cells, with cell-level means of the
[untreated](hyp:Y0Mean) and [cohort-specific treated](hyp:YgMean) potential outcomes. It
requires that [every treated cell's cohort has positive share](hyp:cohortShare_pos_on_treated),
that [the covariate weights are nonnegative](hyp:covarWeight_nonneg) and [sum to one within
each cohort](hyp:covarWeight_sum_one), and that [the observed cell mean coincides with the
treated mean on treated cells](hyp:consistency_treated) and [with the untreated mean on
untreated cells](hyp:consistency_untreated).

Conditional expectations are encoded as primitive finite-cell means. The treated and
untreated predicates are independent inputs: the structure imposes no adoption-time order,
absorbing-treatment law, disjointness, or coverage condition. -/
structure StaggeredATTCells (Cohort Time Covar : Type*)
    [Fintype Cohort] [Fintype Time] [Fintype Covar] where
  cohortShare : Cohort → ℝ
  covarWeight : Cohort → Covar → ℝ
  treatedCell : Cohort → Time → Prop
  untreatedCell : Cohort → Time → Prop
  Y0Mean : Cohort → Time → Covar → ℝ
  YgMean : Cohort → Time → Covar → ℝ
  observedMean : Cohort → Time → Covar → ℝ
  cohortShare_pos_on_treated :
    ∀ ⦃g : Cohort⦄ ⦃t : Time⦄, treatedCell g t → 0 < cohortShare g
  covarWeight_nonneg : ∀ g c, 0 ≤ covarWeight g c
  covarWeight_sum_one : ∀ g, ∑ c, covarWeight g c = 1
  consistency_treated :
    ∀ ⦃g : Cohort⦄ ⦃t : Time⦄, treatedCell g t →
      ∀ c, observedMean g t c = YgMean g t c
  consistency_untreated :
    ∀ ⦃g : Cohort⦄ ⦃t : Time⦄, untreatedCell g t →
      ∀ c, observedMean g t c = Y0Mean g t c

namespace StaggeredATTCells

open Classical in
/-- For [finite sets of cohorts, periods, and covariate cells](hyp:Cohort,Time,Covar)
and [a finite cell system](hyp:P), the [treated-cell set](goal) is
the finite set of all cohort--period pairs designated as treated by that system. -/
noncomputable def treatedCells (P : StaggeredATTCells Cohort Time Covar) :
    Finset (Cohort × Time) :=
  (Finset.univ : Finset (Cohort × Time)).filter (fun gt => P.treatedCell gt.1 gt.2)

open Classical in
/-- For [finite sets of cohorts, periods, and covariate cells](hyp:Cohort,Time,Covar)
and [a finite cell system](hyp:P), the [untreated-cell set](goal) is
the finite set of all cohort--period pairs designated as untreated and used to
fit the untreated-outcome regression. -/
noncomputable def untreatedCells (P : StaggeredATTCells Cohort Time Covar) :
    Finset (Cohort × Time) :=
  (Finset.univ : Finset (Cohort × Time)).filter (fun gt => P.untreatedCell gt.1 gt.2)

/-- For [finite sets of cohorts, periods, and covariate cells](hyp:Cohort,Time,Covar),
[a finite cell system](hyp:P), [a cohort](hyp:g), and [a period](hyp:t), the
[cell treatment-effect contrast](goal) is the covariate-weighted average, within
that cohort, of the cohort-specific potential outcome minus the untreated
potential outcome in that period. Its treatment interpretation requires the
system's supplied treated-cell predicate to represent an actual treatment design. -/
noncomputable def tauCell (P : StaggeredATTCells Cohort Time Covar)
    (g : Cohort) (t : Time) : ℝ :=
  ∑ c, P.covarWeight g c * (P.YgMean g t c - P.Y0Mean g t c)

/-- The [weighted linear aggregate of treated-cell effects](goal) for [a finite cell
system](hyp:P) uses [an arbitrary cohort-period coefficient function](hyp:a) over
[finite cohort, period, and covariate sets](hyp:Cohort,Time,Covar). The coefficients
need not be nonnegative or sum to one, so this definition alone carries no average-effect
interpretation. -/
noncomputable def tauAgg (P : StaggeredATTCells Cohort Time Covar)
    (a : Cohort → Time → ℝ) : ℝ :=
  ∑ gt ∈ P.treatedCells, a gt.1 gt.2 * P.tauCell gt.1 gt.2

end StaggeredATTCells

/-- An aggregate-weight specification for [a finite cell system](hyp:P) over
[finite cohort, period, and covariate sets](hyp:Cohort,Time,Covar) consists of
[cohort-period weights](hyp:weight) that are [nonnegative](hyp:nonneg_on_treated)
on treated cells and [sum to one across those cells](hyp:sum_treated). -/
structure AggregateWeights (P : StaggeredATTCells Cohort Time Covar) where
  weight : Cohort → Time → ℝ
  nonneg_on_treated :
    ∀ ⦃g : Cohort⦄ ⦃t : Time⦄, P.treatedCell g t → 0 ≤ weight g t
  sum_treated : ∑ gt ∈ P.treatedCells, weight gt.1 gt.2 = 1

/-- For [finite sets of cohorts, periods, and covariate cells](hyp:Cohort,Time,Covar)
and [a finite cell system](hyp:P), [the condition called no anticipation](goal) means
that, for every cohort, every period designated untreated, and every covariate
cell, that cohort's potential outcome equals its untreated potential outcome. -/
def NoAnticipation (P : StaggeredATTCells Cohort Time Covar) : Prop :=
  ∀ ⦃g : Cohort⦄ ⦃t : Time⦄, P.untreatedCell g t →
    ∀ c, P.YgMean g t c = P.Y0Mean g t c

/-- For [finite sets of cohorts, periods, and covariate cells](hyp:Cohort,Time,Covar)
and [a finite cell system](hyp:P), [conditional parallel trends in
additive form](goal) means that there exist cohort-by-covariate and period-by-
covariate functions whose sum equals the untreated potential-outcome mean for
every cohort, period, and covariate cell. -/
def ConditionalParallelTrendsAdditive
    (P : StaggeredATTCells Cohort Time Covar) : Prop :=
  ∃ α : Cohort → Covar → ℝ, ∃ lam : Time → Covar → ℝ,
    ∀ g t c, P.Y0Mean g t c = α g c + lam t c

/-- For [finite sets of cohorts, periods, and covariate cells](hyp:Cohort,Time,Covar)
and [a cohort-period-covariate function](hyp:d), the [cell-additivity
condition](goal) means that there exist cohort-by-covariate and period-by-
covariate functions whose sum equals that function at every cell. -/
def IsCellAdditive (d : Cohort → Time → Covar → ℝ) : Prop :=
  ∃ γ : Cohort → Covar → ℝ, ∃ δ : Time → Covar → ℝ,
    ∀ g t c, d g t c = γ g c + δ t c

/-- For [finite sets of cohorts, periods, and covariate cells](hyp:Cohort,Time,Covar)
and [a finite cell system](hyp:P), the [untreated-design
identification condition](goal) means that every additive cohort-period-
covariate function which vanishes at every untreated cell also vanishes at
every treated cell.

Connected untreated design and full-rank identification condition.

Saturating the untreated design with enough connected cells to pin down the
target values of the additive `α_{g,c} + λ_{t,c}` functions is represented by the
statement that an additive cell function vanishing on every untreated cell must
also vanish on every treated cell. The condition says nothing about cells marked
neither untreated nor treated. -/
def UntreatedDesignIdentifies (P : StaggeredATTCells Cohort Time Covar) : Prop :=
  ∀ d : Cohort → Time → Covar → ℝ, IsCellAdditive (Cohort := Cohort) d →
    (∀ ⦃g : Cohort⦄ ⦃t : Time⦄, P.untreatedCell g t → ∀ c, d g t c = 0) →
    ∀ ⦃g : Cohort⦄ ⦃t : Time⦄, P.treatedCell g t → ∀ c, d g t c = 0

/-- A finite-cell weighted least-squares fit of the untreated-outcome mean for a cell
design `P`, restricted to the untreated observations. It bundles [a fitted untreated-outcome
mean](hyp:m0) that [is additive in cohort and time given the covariate cell](hyp:additive),
[projection weights that are strictly positive on the untreated
design](hyp:untreatedWeight,untreatedWeight_pos), the requirement that [the fit solves the
covariate/cell-weighted normal equations against every additive test function, summed over the
untreated design](hyp:untreatedNormalEq), [full-rank identification of the additive class from
vanishing on the untreated design alone](hyp:design_identifies), and [a positive cohort share on
every treated cell](hyp:target_cell_support).

The fitted untreated mean `m0(g,t,c)` is additive in cohort/time conditional on
covariates. The field `untreatedNormalEq` states the weighted least-squares
normal equations for projecting the observed outcome onto this additive class
using untreated observations only: against every additive test function, the
covariate/cell-weighted residual `observedMean - m0` sums to zero on the
untreated design.

The exact-fit facts are proved below rather than stored as fields:
`untreatedFit` derives agreement on untreated cells from the normal equations,
no anticipation, and conditional parallel trends, while `recovers_target_Y0`
uses `UntreatedDesignIdentifies` to extend the untreated-outcome fit to target
treated cells. The companion population bridge relates these finite-cell means
to conditional expectations. -/
structure SaturatedUntreatedRegression
    (P : StaggeredATTCells Cohort Time Covar) where
  m0 : Cohort → Time → Covar → ℝ
  additive :
    ∃ α : Cohort → Covar → ℝ, ∃ lam : Time → Covar → ℝ,
      ∀ g t c, m0 g t c = α g c + lam t c
  /-- Nonnegative covariate/cell weights of the untreated-only projection. -/
  untreatedWeight : Cohort → Time → Covar → ℝ
  /-- The projection weights are strictly positive on the untreated design
  (positive probability of each untreated observation cell). -/
  untreatedWeight_pos :
    ∀ ⦃g : Cohort⦄ ⦃t : Time⦄, P.untreatedCell g t →
      ∀ c, 0 < untreatedWeight g t c
  /-- Finite-cell projection origin of `m0`: `m0` solves the weighted
  least-squares normal equations for the observed outcome on the additive class
  `H0`, using only untreated observations: against every additive test function
  the covariate/cell-weighted residual `observedMean − m0` over the untreated
  design vanishes. -/
  untreatedNormalEq :
    ∀ d : Cohort → Time → Covar → ℝ, IsCellAdditive (Cohort := Cohort) d →
      ∑ gt ∈ P.untreatedCells, ∑ c,
          untreatedWeight gt.1 gt.2 c *
            (P.observedMean gt.1 gt.2 c - m0 gt.1 gt.2 c) * d gt.1 gt.2 c = 0
  design_identifies : UntreatedDesignIdentifies P
  target_cell_support :
    ∀ ⦃g : Cohort⦄ ⦃t : Time⦄, P.treatedCell g t → 0 < P.cohortShare g

/-- An untreated-fit witness for [a finite cohort-period cell system](hyp:P)
over [finite cohort, period, and covariate sets](hyp:Cohort,Time,Covar) consists of
[an additive fitted mean](hyp:m0,additive), [untreated-cell
weights](hyp:untreatedWeight) that are [strictly positive](hyp:untreatedWeight_pos)
on the untreated design, and [weighted normal equations against every additive
test function](hyp:untreatedNormalEq). -/
structure UntreatedFitWitness
    (P : StaggeredATTCells Cohort Time Covar) where
  m0 : Cohort → Time → Covar → ℝ
  additive : IsCellAdditive (Cohort := Cohort) m0
  untreatedWeight : Cohort → Time → Covar → ℝ
  untreatedWeight_pos :
    ∀ ⦃g : Cohort⦄ ⦃t : Time⦄, P.untreatedCell g t →
      ∀ c, 0 < untreatedWeight g t c
  untreatedNormalEq :
    ∀ d : Cohort → Time → Covar → ℝ, IsCellAdditive (Cohort := Cohort) d →
      ∑ gt ∈ P.untreatedCells, ∑ c,
          untreatedWeight gt.1 gt.2 c *
            (P.observedMean gt.1 gt.2 c - m0 gt.1 gt.2 c) * d gt.1 gt.2 c = 0

/-- For [finite sets of cohorts, periods, and covariate cells](hyp:Cohort,Time,Covar),
[the finite cell system underlying the regression](hyp:P), and [a
saturated untreated-outcome regression](hyp:S), the [untreated-fit
witness](goal) retains its fitted untreated mean, additivity, untreated-cell
weights, positivity condition, and untreated normal equations, while omitting
its target-support and design-identification conditions. -/
def SaturatedUntreatedRegression.toUntreatedFitWitness
    {P : StaggeredATTCells Cohort Time Covar}
    (S : SaturatedUntreatedRegression P) : UntreatedFitWitness P where
  m0 := S.m0
  additive := S.additive
  untreatedWeight := S.untreatedWeight
  untreatedWeight_pos := S.untreatedWeight_pos
  untreatedNormalEq := S.untreatedNormalEq

namespace SaturatedUntreatedRegression

/-- The [additive fitted mean equals the cohort-specific outcome mean](goal) at
[an untreated cell and covariate value](hyp:hgt,c) when [an untreated-fit
witness](hyp:S) is combined with [no anticipation](hyp:hNA) and [additive
conditional parallel trends](hyp:hCPT) for [a finite cell system](hyp:P) over
[finite cohort, period, and covariate sets](hyp:Cohort,Time,Covar).

Proof: under no anticipation the untreated observed mean equals the cohort-`g`
mean, and under conditional parallel trends it is additive (lies in `H0`).  The
residual `m0 − Y0Mean` is then itself additive (`additive` + `hCPT`); plugging it
into the weighted untreated normal equations (`untreatedNormalEq`) shows the
positively-weighted sum of its squares over the untreated design vanishes, so the
residual is zero on every untreated cell — the projection is exact there. -/
theorem untreatedFit
    {P : StaggeredATTCells Cohort Time Covar}
    (S : UntreatedFitWitness P)
    (hNA : NoAnticipation P) (hCPT : ConditionalParallelTrendsAdditive P)
    ⦃g : Cohort⦄ ⦃t : Time⦄ (hgt : P.untreatedCell g t) (c : Covar) :
    S.m0 g t c = P.YgMean g t c := by
  classical
  obtain ⟨αy, lamy, hy⟩ := hCPT
  obtain ⟨αm, lamm, hm⟩ := S.additive
  set d : Cohort → Time → Covar → ℝ :=
    fun g t c => S.m0 g t c - P.Y0Mean g t c with hd
  have hd_add : IsCellAdditive (Cohort := Cohort) d := by
    refine ⟨fun g c => αm g c - αy g c, fun t c => lamm t c - lamy t c, ?_⟩
    intro g t c
    simp only [hd, hm, hy]; ring
  have hne := S.untreatedNormalEq d hd_add
  -- The positively-weighted squared residual over the untreated design vanishes.
  have hsq :
      (∑ gt ∈ P.untreatedCells, ∑ c,
          S.untreatedWeight gt.1 gt.2 c * (d gt.1 gt.2 c) ^ 2) = 0 := by
    have hQR :
        (∑ gt ∈ P.untreatedCells, ∑ c,
            S.untreatedWeight gt.1 gt.2 c * (d gt.1 gt.2 c) ^ 2)
          + (∑ gt ∈ P.untreatedCells, ∑ c,
              S.untreatedWeight gt.1 gt.2 c *
                (P.observedMean gt.1 gt.2 c - S.m0 gt.1 gt.2 c) * d gt.1 gt.2 c)
          = 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero ?_
      intro gt hgt_mem
      have hut : P.untreatedCell gt.1 gt.2 := by
        simpa [StaggeredATTCells.untreatedCells] using hgt_mem
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero ?_
      intro c _
      have hobs : P.observedMean gt.1 gt.2 c = P.Y0Mean gt.1 gt.2 c :=
        P.consistency_untreated hut c
      simp only [hd]
      rw [hobs]; ring
    linarith [hQR, hne]
  -- Extract the single untreated cell `(g,t)` and covariate `c`.
  have hmem : (g, t) ∈ P.untreatedCells := by
    simp only [StaggeredATTCells.untreatedCells, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact hgt
  have hrow_nonneg :
      ∀ gt ∈ P.untreatedCells,
        0 ≤ ∑ c, S.untreatedWeight gt.1 gt.2 c * (d gt.1 gt.2 c) ^ 2 := by
    intro gt hgt_mem
    have hut : P.untreatedCell gt.1 gt.2 := by
      simpa [StaggeredATTCells.untreatedCells] using hgt_mem
    exact Finset.sum_nonneg fun c _ =>
      mul_nonneg (le_of_lt (S.untreatedWeight_pos hut c)) (sq_nonneg _)
  have hrow := (Finset.sum_eq_zero_iff_of_nonneg hrow_nonneg).mp hsq (g, t) hmem
  have hcell_nonneg :
      ∀ c' ∈ (Finset.univ : Finset Covar),
        0 ≤ S.untreatedWeight g t c' * (d g t c') ^ 2 :=
    fun c' _ => mul_nonneg (le_of_lt (S.untreatedWeight_pos hgt c')) (sq_nonneg _)
  have hcell :=
    (Finset.sum_eq_zero_iff_of_nonneg hcell_nonneg).mp hrow c (Finset.mem_univ c)
  have hw := S.untreatedWeight_pos hgt c
  have hd0 : d g t c = 0 := by
    have hsq0 : (d g t c) ^ 2 = 0 :=
      (mul_eq_zero.mp hcell).resolve_left (ne_of_gt hw)
    exact pow_eq_zero_iff (by norm_num) |>.mp hsq0
  have hm0 : S.m0 g t c = P.Y0Mean g t c := by
    have hh := hd0; simp only [hd] at hh; linarith
  rw [hm0]; exact (hNA hgt c).symm

/-- **Saturated untreated regression recovers the untreated potential outcome on
treated cells.** If [no anticipation holds: the treated and untreated
potential-outcome means agree on every cell in the untreated-outcome regression's
design](hyp:hNA) and [conditional parallel trends holds — the mean untreated
potential outcome admits an additive cohort/time fixed-effects representation
given covariates](hyp:hCPT), then on [any treated cohort-time cell `(g,t)`
covered by the saturated untreated regression `S`](hyp:hgt), [the fitted value
`S.m0 g t c` equals the mean untreated potential outcome `Y0Mean g t c`, for
every covariate cell `c`](goal).

Proof: on the untreated design, `m0` reproduces the factual cohort-`g` mean
(`untreatedFit`), which no anticipation turns into the untreated-outcome mean
(`hNA`).  Both `m0` and `Y0Mean` are additive (`additive`, `hCPT`), so their
difference is an additive cell function vanishing on every untreated cell; the
connected/full-rank identifiability condition (`design_identifies`) extends that
vanishing to every treated cell, giving `m0 = Y0Mean` there. -/
theorem recovers_target_Y0
    {P : StaggeredATTCells Cohort Time Covar}
    (S : SaturatedUntreatedRegression P)
    (hNA : NoAnticipation P) (hCPT : ConditionalParallelTrendsAdditive P)
    ⦃g : Cohort⦄ ⦃t : Time⦄ (hgt : P.treatedCell g t) (c : Covar) :
    S.m0 g t c = P.Y0Mean g t c := by
  classical
  obtain ⟨αm, lamm, hm⟩ := S.additive
  obtain ⟨αy, lamy, hy⟩ := id hCPT
  -- The difference of the two additive representations.
  set d : Cohort → Time → Covar → ℝ :=
    fun g t c => S.m0 g t c - P.Y0Mean g t c with hd
  have hd_add : IsCellAdditive (Cohort := Cohort) d := by
    refine ⟨fun g c => αm g c - αy g c, fun t c => lamm t c - lamy t c, ?_⟩
    intro g t c
    simp only [hd, hm, hy]; ring
  have hd_untreated :
      ∀ ⦃g : Cohort⦄ ⦃t : Time⦄, P.untreatedCell g t → ∀ c, d g t c = 0 := by
    intro g t hut c
    have h1 : S.m0 g t c = P.Y0Mean g t c := by
      have hfit := SaturatedUntreatedRegression.untreatedFit
        S.toUntreatedFitWitness hNA hCPT hut c
      rw [show S.m0 g t c = P.YgMean g t c by
        simpa [SaturatedUntreatedRegression.toUntreatedFitWitness] using hfit, hNA hut c]
    simp [hd, h1]
  have hzero : d g t c = 0 := S.design_identifies d hd_add hd_untreated hgt c
  have := sub_eq_zero.mp (by simpa [hd] using hzero)
  exact this

end SaturatedUntreatedRegression

/-- For [finite sets of cohorts, periods, and covariate cells](hyp:Cohort,Time,Covar),
[a finite cell system](hyp:P), [a saturated untreated-outcome
regression](hyp:S), [a cohort](hyp:g), and [a period](hyp:t), the [imputation
residual mean](goal) is the within-cohort covariate-weighted average of the
observed cell mean minus the fitted untreated mean.

Imputation residual mean for a treated cohort-time cell.

The companion file `FlexibleDIDMundlak/PopulationBridge.lean` connects this
finite covariate-weighted average of cell residuals to the corresponding
population conditional expectation when the cell weights are conditional
probabilities and the residuals are within-cell conditional means. -/
noncomputable def imputationTheta (P : StaggeredATTCells Cohort Time Covar)
    (S : SaturatedUntreatedRegression P) (g : Cohort) (t : Time) : ℝ :=
  ∑ c, P.covarWeight g c * (P.observedMean g t c - S.m0 g t c)

/-- For [finite sets of cohorts, periods, and covariate cells](hyp:Cohort,Time,Covar),
[a finite cell system](hyp:P), [a saturated untreated-outcome
regression](hyp:S), [a proposed cell coefficient](hyp:theta), [a cohort](hyp:g),
and [a period](hyp:t), the [cell residual normal equation](goal) states that
the within-cohort covariate-weighted mean of observed outcome minus fitted
untreated outcome minus that coefficient is zero. -/
def cellResidualNormalEq (P : StaggeredATTCells Cohort Time Covar)
    (S : SaturatedUntreatedRegression P) (theta : ℝ) (g : Cohort) (t : Time) :
    Prop :=
  ∑ c, P.covarWeight g c * (P.observedMean g t c - S.m0 g t c - theta) = 0

omit [Fintype Cohort] [Fintype Time] in
/-- For [outcome and fitted-mean arrays](hyp:outcome,fitted) over [cohort, period,
and finite covariate sets](hyp:Cohort,Time,Covar), [within-cohort covariate
weights](hyp:covarWeight) that [sum to one](hyp:covarWeight_sum_one) make [a
coefficient satisfying the weighted residual normal equation](hyp:hθ) [equal the
corresponding weighted residual mean](goal). -/
theorem cellResidualNormalEq_eq_imputationTheta
    (outcome fitted : Cohort → Time → Covar → ℝ)
    (covarWeight : Cohort → Covar → ℝ)
    (covarWeight_sum_one : ∀ g, ∑ c, covarWeight g c = 1)
    {theta : ℝ} {g : Cohort} {t : Time}
    (hθ : ∑ c, covarWeight g c * (outcome g t c - fitted g t c - theta) = 0) :
    theta = ∑ c, covarWeight g c * (outcome g t c - fitted g t c) := by
  have hsum :
      (∑ c, covarWeight g c *
          (outcome g t c - fitted g t c - theta)) =
        (∑ c, covarWeight g c * (outcome g t c - fitted g t c)) -
          (∑ c, covarWeight g c) * theta := by
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
  have hnormal :
      (∑ c, covarWeight g c * (outcome g t c - fitted g t c)) -
          theta = 0 := by
    calc
      (∑ c, covarWeight g c * (outcome g t c - fitted g t c)) - theta
          = (∑ c, covarWeight g c * (outcome g t c - fitted g t c)) -
              (∑ c, covarWeight g c) * theta := by
                rw [covarWeight_sum_one g]
                ring
      _ = ∑ c, covarWeight g c *
            (outcome g t c - fitted g t c - theta) := by
              rw [hsum]
      _ = 0 := hθ
  exact (sub_eq_zero.mp hnormal).symm

/-- For [finite sets of cohorts and periods](hyp:Cohort,Time), [a cohort](hyp:g),
and [a period](hyp:t), the [saturated treated-cell indicator](goal) is one at
that cohort--period pair and zero at every other pair. -/
noncomputable def cellIndicator [DecidableEq Cohort] [DecidableEq Time]
    (g : Cohort) (t : Time) : Cohort → Time → ℝ :=
  fun g' t' => if g' = g ∧ t' = t then 1 else 0

/-- For [finite cohort and period sets](hyp:Cohort,Time), [outcome and fitted-mean
arrays](hyp:outcome,fitted), [within-cohort covariate weights](hyp:covarWeight),
[a coefficient](hyp:theta), and [a selected cohort-period cell](hyp:g,t), [the
full normal equation against that cell's indicator is equivalent to its single-cell
residual equation](goal).

Because the treated-cell indicators are saturated — one indicator per cell — the
*full* POLS/ETWFE
normal equation for the indicator of cell `(g,t)`, namely the covariate-weighted
residual summed against `cellIndicator g t` over the entire cohort×time design,
collapses to that single cell's residual sum.  Hence the per-cell residual
normal equation `cellResidualNormalEq` *is* the full saturated normal equation
for cell `(g,t)`, not an extra simplification: the cross-cell terms vanish by
orthogonality of the saturated indicators.  This is the concrete content behind
the `pols_cell_normalEq` / `etwfe_cell_normalEq` fields below. -/
theorem cellIndicator_normalEq_eq_cellResidual
    [DecidableEq Cohort] [DecidableEq Time]
    (outcome fitted : Cohort → Time → Covar → ℝ)
    (covarWeight : Cohort → Covar → ℝ)
    (theta : ℝ) (g : Cohort) (t : Time) :
    (∑ g', ∑ t', ∑ c, cellIndicator g t g' t' *
        covarWeight g' c * (outcome g' t' c - fitted g' t' c
          - cellIndicator g t g' t' * theta) = 0)
      ↔ ∑ c, covarWeight g c * (outcome g t c - fitted g t c - theta) = 0 := by
  classical
  unfold cellIndicator
  -- The full saturated sum collapses to the single-cell residual sum, because
  -- the saturated indicator vanishes off cell `(g,t)`.
  have hcollapse :
      (∑ g', ∑ t', ∑ c, (if g' = g ∧ t' = t then (1 : ℝ) else 0) *
          covarWeight g' c * (outcome g' t' c - fitted g' t' c
            - (if g' = g ∧ t' = t then (1 : ℝ) else 0) * theta))
        = ∑ c, covarWeight g c * (outcome g t c - fitted g t c - theta) := by
    rw [Finset.sum_eq_single g, Finset.sum_eq_single t]
    · refine Finset.sum_congr rfl ?_
      intro c _
      simp
    · intro t' _ ht'
      refine Finset.sum_eq_zero ?_
      intro c _
      simp [ht']
    · intro hg; simp at hg
    · intro g' _ hg'
      refine Finset.sum_eq_zero ?_
      intro t' _
      refine Finset.sum_eq_zero ?_
      intro c _
      simp [hg']
    · intro hg; simp at hg
  rw [hcollapse]

/-- On top of a finite cell design `P` and its saturated untreated-outcome regression `S`,
this structure packages three families of treated-cell coefficients — [an imputation
coefficient](hyp:thetaImp), [a pooled-least-squares (POLS) coefficient](hyp:thetaPOLS), and [an
extended two-way-fixed-effects (ETWFE) coefficient](hyp:thetaETWFE) — together with the
conditions pinning them down: [on every treated cell the imputation coefficient equals the
covariate-weighted imputation residual mean](hyp:thetaImp_eq_imputation), and [the POLS and
ETWFE coefficients each solve the finite-cell covariate-weighted residual normal
equation](hyp:pols_cell_normalEq,etwfe_cell_normalEq).

The two normal-equation fields are supplied inputs. By
`cellIndicator_normalEq_eq_cellResidual`, each per-cell equation is equivalent
to the full saturated normal equation for that cell's indicator. An external
POLS or ETWFE construction would still have to prove that its regression design
reduces to these equations; this structure does not provide that bridge. -/
structure FlexibleDIDEstimands (P : StaggeredATTCells Cohort Time Covar)
    (S : SaturatedUntreatedRegression P) where
  thetaImp : Cohort → Time → ℝ
  thetaPOLS : Cohort → Time → ℝ
  thetaETWFE : Cohort → Time → ℝ
  thetaImp_eq_imputation :
    ∀ ⦃g : Cohort⦄ ⦃t : Time⦄, P.treatedCell g t →
      thetaImp g t = imputationTheta P S g t
  pols_cell_normalEq :
    ∀ ⦃g : Cohort⦄ ⦃t : Time⦄, P.treatedCell g t →
      cellResidualNormalEq P S (thetaPOLS g t) g t
  etwfe_cell_normalEq :
    ∀ ⦃g : Cohort⦄ ⦃t : Time⦄, P.treatedCell g t →
      cellResidualNormalEq P S (thetaETWFE g t) g t

namespace FlexibleDIDEstimands

/-- **POLS candidate satisfying the supplied cell normal equation.** On [any treated
cohort-time cell `(g,t)`](hyp:hgt), [the supplied POLS coefficient candidate equals the
imputation residual mean at that cell](goal).

Proof idea: both coefficients solve the same finite-cell residual normal
equation, so they identify the same covariate-weighted residual mean. -/
theorem thetaPOLS_eq_imputationTheta_of_normalEq
    (P : StaggeredATTCells Cohort Time Covar)
    (S : SaturatedUntreatedRegression P)
    (E : FlexibleDIDEstimands P S)
    {g : Cohort} {t : Time} (hgt : P.treatedCell g t) :
    E.thetaPOLS g t = imputationTheta P S g t :=
  cellResidualNormalEq_eq_imputationTheta P.observedMean S.m0 P.covarWeight
    P.covarWeight_sum_one (E.pols_cell_normalEq hgt)

/-- **ETWFE candidate satisfying the supplied cell normal equation.** On [any treated
cohort-time cell `(g,t)`](hyp:hgt), [the supplied extended two-way-fixed-effects (ETWFE)
coefficient candidate equals the imputation residual mean at that cell](goal).

The supplied ETWFE field asserts the same finite-cell residual normal equation
as imputation, so the two coefficients solve the identical equation. -/
theorem thetaETWFE_eq_imputationTheta_of_normalEq
    (P : StaggeredATTCells Cohort Time Covar)
    (S : SaturatedUntreatedRegression P)
    (E : FlexibleDIDEstimands P S)
    {g : Cohort} {t : Time} (hgt : P.treatedCell g t) :
    E.thetaETWFE g t = imputationTheta P S g t :=
  cellResidualNormalEq_eq_imputationTheta P.observedMean S.m0 P.covarWeight
    P.covarWeight_sum_one (E.etwfe_cell_normalEq hgt)

/-- On [a treated cell](hyp:hgt), [the supplied POLS candidate equals the supplied imputation
candidate](goal), as an algebraic consequence of their scaffold identities. -/
theorem pols_cell_eq_imputation_of_normalEq
    (P : StaggeredATTCells Cohort Time Covar)
    (S : SaturatedUntreatedRegression P)
    (E : FlexibleDIDEstimands P S)
    {g : Cohort} {t : Time} (hgt : P.treatedCell g t) :
    E.thetaPOLS g t = E.thetaImp g t := by
  rw [E.thetaPOLS_eq_imputationTheta_of_normalEq P S hgt, E.thetaImp_eq_imputation hgt]

/-- On [a treated cell](hyp:hgt), [the supplied ETWFE candidate equals the supplied POLS
candidate](goal), because both satisfy the scaffold's finite-cell normal equations. -/
theorem etwfe_cell_eq_pols_of_normalEq
    (P : StaggeredATTCells Cohort Time Covar)
    (S : SaturatedUntreatedRegression P)
    (E : FlexibleDIDEstimands P S)
    {g : Cohort} {t : Time} (hgt : P.treatedCell g t) :
    E.thetaETWFE g t = E.thetaPOLS g t := by
  rw [E.thetaETWFE_eq_imputationTheta_of_normalEq P S hgt,
    E.thetaPOLS_eq_imputationTheta_of_normalEq P S hgt]

end FlexibleDIDEstimands

/-- The [weighted linear aggregate of supplied imputation coefficients](goal) for
[a finite cell system, untreated regression, and coefficient scaffold](hyp:P,S,E)
uses [an arbitrary cohort-period coefficient function](hyp:a) over [finite cohort,
period, and covariate sets](hyp:Cohort,Time,Covar). -/
noncomputable def psiImp (P : StaggeredATTCells Cohort Time Covar)
    {S : SaturatedUntreatedRegression P} (E : FlexibleDIDEstimands P S)
    (a : Cohort → Time → ℝ) : ℝ :=
  ∑ gt ∈ P.treatedCells, a gt.1 gt.2 * E.thetaImp gt.1 gt.2

/-- The [weighted linear aggregate of supplied pooled-least-squares coefficient
candidates](goal) for [a finite cell system, untreated regression, and coefficient
scaffold](hyp:P,S,E) uses [an arbitrary cohort-period coefficient function](hyp:a)
over [finite cohort, period, and covariate sets](hyp:Cohort,Time,Covar). -/
noncomputable def psiPOLS (P : StaggeredATTCells Cohort Time Covar)
    {S : SaturatedUntreatedRegression P} (E : FlexibleDIDEstimands P S)
    (a : Cohort → Time → ℝ) : ℝ :=
  ∑ gt ∈ P.treatedCells, a gt.1 gt.2 * E.thetaPOLS gt.1 gt.2

/-- The [weighted linear aggregate of supplied extended two-way-fixed-effects
coefficient candidates](goal) for [a finite cell system, untreated regression, and
coefficient scaffold](hyp:P,S,E) uses [an arbitrary cohort-period coefficient
function](hyp:a) over [finite cohort, period, and covariate
sets](hyp:Cohort,Time,Covar). -/
noncomputable def psiETWFE (P : StaggeredATTCells Cohort Time Covar)
    {S : SaturatedUntreatedRegression P} (E : FlexibleDIDEstimands P S)
    (a : Cohort → Time → ℝ) : ℝ :=
  ∑ gt ∈ P.treatedCells, a gt.1 gt.2 * E.thetaETWFE gt.1 gt.2

/-- Under [no anticipation](hyp:hNA), [additive conditional parallel
trends](hyp:hCPT), and [membership in the treated-cell predicate](hyp:hgt), [the supplied
imputation coefficient equals the cell treatment-effect contrast](goal) for [a finite
cell system, untreated regression, and coefficient scaffold](hyp:P,S,E) over
[finite cohort, period, and covariate sets](hyp:Cohort,Time,Covar). -/
theorem imputationTheta_eq_tauCell
    (P : StaggeredATTCells Cohort Time Covar)
    (S : SaturatedUntreatedRegression P)
    (E : FlexibleDIDEstimands P S)
    (hNA : NoAnticipation P) (hCPT : ConditionalParallelTrendsAdditive P)
    {g : Cohort} {t : Time} (hgt : P.treatedCell g t) :
    E.thetaImp g t = P.tauCell g t := by
  rw [E.thetaImp_eq_imputation hgt]
  unfold imputationTheta StaggeredATTCells.tauCell
  refine Finset.sum_congr rfl ?_
  intro c _hc
  rw [P.consistency_treated hgt c, S.recovers_target_Y0 hNA hCPT hgt c]

/-- **Cell-level consequences of supplied POLS and ETWFE normal equations.** If [no
anticipation holds](hyp:hNA), [conditional parallel trends holds
— the mean untreated potential outcome admits an additive cohort/time
fixed-effects representation given covariates](hyp:hCPT), and [`(g,t)` is a
treated cohort-time cell covered by the untreated-regression witness `S` and the scaffold
`E`, which supplies the imputation identity and POLS/ETWFE cell normal equations](hyp:hgt),
then [the three supplied coefficient candidates at `(g,t)` all equal the cell
treatment-effect contrast](goal). -/
theorem flexible_did_cell_consequences_of_scaffold
    (P : StaggeredATTCells Cohort Time Covar)
    (S : SaturatedUntreatedRegression P)
    (E : FlexibleDIDEstimands P S)
    (hNA : NoAnticipation P) (hCPT : ConditionalParallelTrendsAdditive P)
    {g : Cohort} {t : Time} (hgt : P.treatedCell g t) :
    E.thetaImp g t = P.tauCell g t ∧
      E.thetaPOLS g t = P.tauCell g t ∧
      E.thetaETWFE g t = P.tauCell g t := by
  have himp : E.thetaImp g t = P.tauCell g t :=
    imputationTheta_eq_tauCell P S E hNA hCPT hgt
  have hpols : E.thetaPOLS g t = P.tauCell g t := by
    rw [E.pols_cell_eq_imputation_of_normalEq P S hgt, himp]
  have hetwfe : E.thetaETWFE g t = P.tauCell g t := by
    rw [E.etwfe_cell_eq_pols_of_normalEq P S hgt, hpols]
  exact ⟨himp, hpols, hetwfe⟩

/-- **Aggregate consequences of supplied POLS and ETWFE normal equations.** If [no
anticipation holds](hyp:hNA) and
[conditional parallel trends holds — the mean untreated potential outcome
admits an additive cohort/time fixed-effects representation given
covariates](hyp:hCPT), then for any treated-cell coefficient function `a`, [the
`a`-weighted linear aggregates of the three supplied coefficient candidates all
equal the same linear aggregate of cell treatment-effect contrasts](goal). No
nonnegativity or normalization of `a` is assumed. -/
theorem flexible_did_aggregate_consequences_of_scaffold
    (P : StaggeredATTCells Cohort Time Covar)
    (S : SaturatedUntreatedRegression P)
    (E : FlexibleDIDEstimands P S)
    (hNA : NoAnticipation P) (hCPT : ConditionalParallelTrendsAdditive P)
    (a : Cohort → Time → ℝ) :
    psiImp P E a = P.tauAgg a ∧
      psiPOLS P E a = P.tauAgg a ∧
      psiETWFE P E a = P.tauAgg a := by
  classical
  have hcell :
      ∀ gt ∈ P.treatedCells,
        E.thetaImp gt.1 gt.2 = P.tauCell gt.1 gt.2 ∧
          E.thetaPOLS gt.1 gt.2 = P.tauCell gt.1 gt.2 ∧
          E.thetaETWFE gt.1 gt.2 = P.tauCell gt.1 gt.2 := by
    intro gt hgt_mem
    have hgt : P.treatedCell gt.1 gt.2 := by
      simpa [StaggeredATTCells.treatedCells] using hgt_mem
    exact flexible_did_cell_consequences_of_scaffold P S E hNA hCPT hgt
  constructor
  · unfold psiImp StaggeredATTCells.tauAgg
    refine Finset.sum_congr rfl ?_
    intro gt hgt
    rw [(hcell gt hgt).1]
  constructor
  · unfold psiPOLS StaggeredATTCells.tauAgg
    refine Finset.sum_congr rfl ?_
    intro gt hgt
    rw [(hcell gt hgt).2.1]
  · unfold psiETWFE StaggeredATTCells.tauAgg
    refine Finset.sum_congr rfl ?_
    intro gt hgt
    rw [(hcell gt hgt).2.2]

/-- **Finite-cell normal-equation scaffold consequences.** If [no
anticipation holds: the treated and untreated potential-outcome means agree on
every cell in the untreated-outcome regression's design](hyp:hNA) and
[conditional parallel trends holds — the mean untreated potential outcome
admits an additive cohort/time fixed-effects representation given
covariates](hyp:hCPT), then, given the saturated untreated regression `S` and
the POLS/ETWFE finite-cell residual normal equations carried by `E`, [on every
treated cohort-time cell the flexible imputation, POLS, and ETWFE coefficient
candidates all equal the cell treatment-effect contrast, and consequently every
treated-cell weighted linear aggregate of the three candidates equals the
correspondingly weighted linear aggregate of those contrasts](goal).

This theorem does not construct POLS or ETWFE estimators from regression design
matrices and therefore is not a formalization of Wooldridge's estimator-equivalence
theorem. The assumptions `hNA` and `hCPT` drive
`SaturatedUntreatedRegression.recovers_target_Y0`, which feeds
`imputationTheta_eq_tauCell`. The POLS/ETWFE legs are pinned to the imputation
residual through the cell residual normal equations carried by `E`; see
`FlexibleDIDEstimands` for the saturated-regression interface. -/
theorem flexible_did_scaffold_consequences
    (P : StaggeredATTCells Cohort Time Covar)
    (S : SaturatedUntreatedRegression P)
    (E : FlexibleDIDEstimands P S)
    (hNA : NoAnticipation P) (hCPT : ConditionalParallelTrendsAdditive P) :
    (∀ ⦃g : Cohort⦄ ⦃t : Time⦄, P.treatedCell g t →
      E.thetaImp g t = P.tauCell g t ∧
        E.thetaPOLS g t = P.tauCell g t ∧
        E.thetaETWFE g t = P.tauCell g t) ∧
      (∀ a : Cohort → Time → ℝ,
        psiImp P E a = P.tauAgg a ∧
          psiPOLS P E a = P.tauAgg a ∧
          psiETWFE P E a = P.tauAgg a) := by
  constructor
  · intro g t hgt
    exact flexible_did_cell_consequences_of_scaffold P S E hNA hCPT hgt
  · intro a
    exact flexible_did_aggregate_consequences_of_scaffold P S E hNA hCPT a

end FlexibleDIDMundlak
end Panel.EstimandCharacterization
end Causalean
