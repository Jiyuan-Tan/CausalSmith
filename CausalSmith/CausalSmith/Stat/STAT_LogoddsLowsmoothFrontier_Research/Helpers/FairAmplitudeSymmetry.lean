module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FairRootSelection
public import Mathlib.Analysis.Calculus.Deriv.Shift

/-! # Signed fair-calibration symmetry

Sign symmetry transports through the numerator, its Taylor extension, and the
literal selected root, including both amplitude axes.
-/
public section
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [Symmetry of the two independent signs makes every transformed sign average even.](goal) Under [the stated assumptions](hyp:F). -/
-- @node: signAverage_neg_field
lemma signAverage_neg_field (F : ℝ → ℝ) (u : ℝ) :
    signAverage (fun s => F (-localSignField u s)) =
      signAverage (fun s => F (localSignField u s)) := by
  simp only [signAverage, Fintype.sum_prod_type, Fintype.sum_bool,
    localSignField, signValue, Bool.false_eq_true, ↓reduceIte]
  simp only [neg_add_rev, neg_mul, neg_neg, one_mul]
  simp only [add_comm, add_left_comm]

/-- [The deterministic fair comparator is even in the signed amplitude. [the stated conclusion](goal) holds. -/
-- @node: comparatorEffect_even
lemma comparatorEffect_even (t δ : ℝ) : comparatorEffect t (-δ) = comparatorEffect t δ := by
  simp only [comparatorEffect, neg_sq]

/-- Reversing the amplitude reindexes the symmetric sign law in the fair numerator. [the stated conclusion](goal) holds. -/
-- @node: fairNumerator_even
lemma fairNumerator_even (t δ ξ u : ℝ) : fairNumerator t (-δ) ξ u = fairNumerator t δ ξ u := by
  unfold fairNumerator
  rw [comparatorEffect_even]
  have he : (fun s => riskShift t (ξ+(-δ)*localSignField u s)) =
      (fun s => riskShift t (ξ+δ*(-localSignField u s))) := by
    funext s
    congr 1
    ring
  rw [he, signAverage_neg_field (fun z => riskShift t (ξ+δ*z)) u]

/-- Two derivatives preserve evenness, including where the totalized derivative is zero. Under the stated assumptions. Under the stated assumptions. [The stated hypotheses](hyp:hf) hold, and [the stated conclusion follows](goal). -/
-- @node: calibration_second_deriv_even
lemma calibration_second_deriv_even (f : ℝ → ℝ) (hf : ∀ x, f (-x) = f x) (x : ℝ) :
    deriv (deriv f) (-x) = deriv (deriv f) x := by
  have he : (fun x => f (-x)) = f := funext hf
  have ho (y : ℝ) : deriv f (-y) = -deriv f y := by
    have h := deriv_comp_neg f y
    rw [he] at h
    linarith
  have he' : (fun y => deriv f (-y)) = (fun y => -deriv f y) := funext ho
  have h := congrArg (fun g : ℝ → ℝ => deriv g x) he'
  rw [deriv_comp_neg, deriv.fun_neg] at h
  linarith

/-- The literal integral Taylor extension retains amplitude evenness on both axes. [the stated conclusion](goal) holds. -/
-- @node: fairEquation_even
lemma fairEquation_even (t δ ξ u : ℝ) : fairEquation t (-δ) ξ u = fairEquation t δ ξ u := by
  unfold fairEquation
  congr 1
  funext s
  congr 1
  funext v
  congr 1
  have he : (fun T => deriv (deriv (fun D => fairNumerator T D ξ u)) (v*(-δ))) =
      (fun T => deriv (deriv (fun D => fairNumerator T D ξ u)) (v*δ)) := by
    funext T
    rw [mul_neg]
    exact calibration_second_deriv_even _ (fun D => fairNumerator_even T D ξ u) _
  rw [he]

/-- Equal normalized equations give equal literal fair-root selectors. [the stated conclusion](goal) holds. -/
-- @node: fairRoot_even
lemma fairRoot_even (t δ u : ℝ) : fairRoot t (-δ) u = fairRoot t δ u := by
  have he : fairEquation t (-δ) = fairEquation t δ := by
    funext ξ u
    exact fairEquation_even t δ ξ u
  unfold fairRoot
  rw [he]
end CausalSmith.Stat.LogoddsLowsmoothFrontier
