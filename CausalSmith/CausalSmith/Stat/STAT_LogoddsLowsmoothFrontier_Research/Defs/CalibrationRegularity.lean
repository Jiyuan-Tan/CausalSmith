module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Defs.Calibration
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! # Calibration regularity specifications

Fully substituted local cells and the closed parameter regions used for smoothness
and bounds of all fixed derivative orders.
-/
@[expose] public section
noncomputable section
open scoped ContDiff
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- Actual local four-cell formulas, with the root fully substituted. -/
def localMixedCell (b : Bool) (s : Bool × Bool) (a y : Bool) (v : Fin 3 → ℝ) : ℝ :=
  let η := v 0
  let ζ := v 1
  let Z := localSignField (v 2) s
  let q := mixedRoot η ζ (v 2)
  let e := if b then 1/2-η*q*Z else 1/2+η*q*Z
  let m := 1/2+ζ*Z
  tableCell e m (if b then covarianceBranch (32*η*ζ) e m else 0) a y
/-- Actual local fair-cell formulas, including spatial centering and comparator effect. -/
def localFairCell (random : Bool) (s : Bool × Bool) (a y : Bool) (v : Fin 3 → ℝ) : ℝ :=
  let t := v 0
  let δ := v 1
  let p := fairRoot t δ (v 2)
  let μ0 := if random then p+δ*localSignField (v 2) s else p
  let μ1 := riskShift (if random then t else comparatorEffect t δ) μ0
  (1/2)*(if y then (if a then μ1 else μ0) else 1-(if a then μ1 else μ0))
/-- Closed mixed-amplitude neighbourhood, including the full spatial coordinate range. -/
def mixedParameterRegion (ε : ℝ) : Set (Fin 3 → ℝ) :=
  {v | |v 0| ≤ ε ∧ |v 1| ≤ ε ∧ v 2 ∈ Set.Icc (0 : ℝ) 1}
/-- Closed fair-amplitude neighbourhood, including zero effect and zero amplitude. -/
def fairParameterRegion (ε : ℝ) : Set (Fin 3 → ℝ) :=
  {v | v 0 ∈ Set.Icc (0 : ℝ) (1/4) ∧ |v 1| ≤ ε ∧ v 2 ∈ Set.Icc (0 : ℝ) 1}
/-- Both roots and all fully substituted local cell formulas are smooth. -/
def CalibrationSmooth (ε : ℝ) : Prop :=
  ContDiffOn ℝ ∞ (fun v : Fin 3 → ℝ => mixedRoot (v 0) (v 1) (v 2)) (mixedParameterRegion ε) ∧
  ContDiffOn ℝ ∞ (fun v : Fin 3 → ℝ => fairRoot (v 0) (v 1) (v 2)) (fairParameterRegion ε) ∧
  (∀ b s a y, ContDiffOn ℝ ∞ (localMixedCell b s a y) (mixedParameterRegion ε)) ∧
  (∀ b s a y, ContDiffOn ℝ ∞ (localFairCell b s a y) (fairParameterRegion ε))
/-- Every fixed derivative order is uniformly bounded; the order is not truncated at two. -/
def CalibrationDerivativeBounds (ε : ℝ) : Prop :=
  ∀ m : ℕ, ∃ B : ℝ, 0 < B ∧
    (∀ v ∈ mixedParameterRegion ε,
      ‖iteratedFDeriv ℝ m (fun w : Fin 3 → ℝ => mixedRoot (w 0) (w 1) (w 2)) v‖ ≤ B ∧
      ∀ b s a y, ‖iteratedFDeriv ℝ m (localMixedCell b s a y) v‖ ≤ B) ∧
    (∀ v ∈ fairParameterRegion ε,
      ‖iteratedFDeriv ℝ m (fun w : Fin 3 → ℝ => fairRoot (w 0) (w 1) (w 2)) v‖ ≤ B ∧
      ∀ b s a y, ‖iteratedFDeriv ℝ m (localFairCell b s a y) v‖ ≤ B)

/-- The literal mixed selector is the unique zero in its prescribed open bracket. -/
def MixedCalibrationZero (v : Fin 3 → ℝ) : Prop :=
  mixedRoot (v 0) (v 1) (v 2) ∈ Set.Ioo (3/4 : ℝ) (5/4) ∧
  mixedEquation (v 0) (v 1) (v 2) (mixedRoot (v 0) (v 1) (v 2)) = 0 ∧
  ∀ q ∈ Set.Ioo (3/4 : ℝ) (5/4),
    mixedEquation (v 0) (v 1) (v 2) q = 0 → q = mixedRoot (v 0) (v 1) (v 2)
/-- The literal fair selector lies in one fixed narrow bracket and is its unique zero;
it also lies in the existing selector bracket. -/
def FairCalibrationZero (b : ℝ) (v : Fin 3 → ℝ) : Prop :=
  fairRoot (v 0) (v 1) (v 2) ∈ Set.Ioo ((2/5 : ℝ)-b) (2/5+b) ∧
  fairRoot (v 0) (v 1) (v 2) ∈ Set.Ioo (3/10 : ℝ) (1/2) ∧
  fairEquation (v 0) (v 1) (fairRoot (v 0) (v 1) (v 2)) (v 2) = 0 ∧
  ∀ p ∈ Set.Ioo ((2/5 : ℝ)-b) (2/5+b),
    fairEquation (v 0) (v 1) p (v 2) = 0 → p = fairRoot (v 0) (v 1) (v 2)
/-- Absolute signed branch radii larger than the derivative-bound radius, one fixed
fair bracket, and open neighborhoods of the full closed parameter regions.
The ambient open sets include signed effects across zero and neighborhoods of
both spatial endpoints; all cells have their selectors fully substituted.
The fair equation itself is smooth on an ambient open set containing the entire
fair core and centered margin bracket, and agrees with the normalized numerator
off the axes throughout that core, for every margin in the bracket. -/
def CalibrationBranchNeighbourhood (ε : ℝ) : Prop :=
  ∃ εmix εfair b : ℝ, ∃ U V : Set (Fin 3 → ℝ),
    0 < εmix ∧ ε < εmix ∧ 0 < εfair ∧ ε < εfair ∧
    0 < b ∧ b < 1/10 ∧ IsOpen U ∧ IsOpen V ∧
    mixedParameterRegion εmix ⊆ U ∧ fairParameterRegion εfair ⊆ V ∧
    (∀ v ∈ U, MixedCalibrationZero v) ∧
    (∀ v ∈ V, FairCalibrationZero b v) ∧
    ContDiffOn ℝ ∞ (fun v : Fin 3 → ℝ => mixedRoot (v 0) (v 1) (v 2)) U ∧
    ContDiffOn ℝ ∞ (fun v : Fin 3 → ℝ => fairRoot (v 0) (v 1) (v 2)) V ∧
    (∀ b s a y, ContDiffOn ℝ ∞ (localMixedCell b s a y) U) ∧
    (∀ b s a y, ContDiffOn ℝ ∞ (localFairCell b s a y) V) ∧
    ∃ W : Set (Fin 4 → ℝ), IsOpen W ∧
      {w | w 0 ∈ Set.Icc (0 : ℝ) (1/4) ∧ |w 1| ≤ εfair ∧
        w 2 ∈ Set.Ioo ((2/5 : ℝ)-b) (2/5+b) ∧ w 3 ∈ Set.Icc (0 : ℝ) 1} ⊆ W ∧
      ContDiffOn ℝ ∞ (fun w : Fin 4 → ℝ =>
        fairEquation (w 0) (w 1) (w 2) (w 3)) W ∧
      (∀ t δ ξ u : ℝ, t ∈ Set.Icc (0 : ℝ) (1/4) → |δ| ≤ εfair →
        ξ ∈ Set.Ioo ((2/5 : ℝ)-b) (2/5+b) → u ∈ Set.Icc (0 : ℝ) 1 →
        t*δ ≠ 0 → fairEquation t δ ξ u = fairNumerator t δ ξ u/(t*δ^2))

end CausalSmith.Stat.LogoddsLowsmoothFrontier
