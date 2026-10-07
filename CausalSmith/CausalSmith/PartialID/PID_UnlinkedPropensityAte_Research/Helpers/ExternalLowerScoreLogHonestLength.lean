module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.ExternalLowerTrialTesting

/-! Honest two-point lower bounds for excess interval length. -/

public section

open MeasureTheory Set
namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- Given [the stated mathematical inputs and assumptions](hyp:epsilon,J,n,m,C,Q0,Q1,theta0,theta1,W0,Delta,alpha,_htheta,hsep,hDelta,hcover0,hcover1), this result [establishes the stated mathematical conclusion](goal). -/
lemma externalInterval_twoPoint_expectedExcessLength {epsilon : ℝ} {J n m : ℕ}
    (C : ExternalIntervalProcedure epsilon J n m)
    (Q0 Q1 : Measure (ExternalSample epsilon J n m))
    [IsProbabilityMeasure Q0] [IsProbabilityMeasure Q1]
    (theta0 theta1 W0 Delta alpha : ℝ)
    (_htheta : theta0 ≤ theta1)
    (hsep : theta1 - theta0 = W0 + Delta)
    (hDelta : 0 ≤ Delta)
    (hcover0 : 1 - alpha ≤ Q0.real {x | C.contains x theta0})
    (hcover1 : 1 - alpha ≤ Q1.real {x | C.contains x theta1}) :
    Delta * (1 - 2 * alpha - Causalean.Stat.tvDist Q0 Q1) ≤
      ∫ x, max 0 (C.length x - W0) ∂Q0 := by
  let A0 : Set (ExternalSample epsilon J n m) := {x | C.contains x theta0}
  let A1 : Set (ExternalSample epsilon J n m) := {x | C.contains x theta1}
  let I := A0 ∩ A1
  have hA (theta : ℝ) : MeasurableSet {x | C.contains x theta} := by
    change MeasurableSet {x | C.lo x ≤ theta ∧ theta ≤ C.hi x}
    exact (measurableSet_le C.measurable_lo measurable_const).inter
      (measurableSet_le measurable_const C.measurable_hi)
  have hA0 : MeasurableSet A0 := hA theta0
  have hA1 : MeasurableSet A1 := hA theta1
  have hI : MeasurableSet I := hA0.inter hA1
  have htransfer :
      1 - alpha - Causalean.Stat.tvDist Q0 Q1 ≤ Q0.real A1 := by
    have htv := Causalean.Stat.measureReal_sub_le_tvDist
      (μ := Q0) (ν := Q1) hA1
    dsimp [A1] at htv
    linarith
  have hmass :
      1 - 2 * alpha - Causalean.Stat.tvDist Q0 Q1 ≤ Q0.real I := by
    have hu : Q0.real (A0 ∪ A1) ≤ 1 := measureReal_le_one
    have hsum := measureReal_union_add_inter (μ := Q0) (s := A0) (t := A1)
      hA1 (measure_ne_top Q0 A0) (measure_ne_top Q0 A1)
    change Q0.real (A0 ∪ A1) + Q0.real I =
      Q0.real A0 + Q0.real A1 at hsum
    linarith
  have hlengthInt : Integrable C.length Q0 := by
    have hlengthMeas : Measurable C.length :=
      C.measurable_hi.sub C.measurable_lo
    apply Integrable.of_bound hlengthMeas.aestronglyMeasurable 2
    filter_upwards with x
    dsimp [ExternalIntervalProcedure.length]
    rw [abs_of_nonneg (sub_nonneg.mpr (C.ordered x))]
    linarith [C.lower_bound x, C.upper_bound x]
  have hexcessInt : Integrable (fun x => max 0 (C.length x - W0)) Q0 := by
    have hsub : Integrable (fun x => C.length x - W0) Q0 := by
      fun_prop
    simpa only [max_comm] using hsub.pos_part
  have hindInt : Integrable (I.indicator (fun _ => Delta)) Q0 :=
    (integrable_const _).indicator hI
  have hpoint (x : ExternalSample epsilon J n m) :
      I.indicator (fun _ => Delta) x ≤ max 0 (C.length x - W0) := by
    by_cases hx : x ∈ I
    · rw [Set.indicator_of_mem hx]
      have hx0 : C.lo x ≤ theta0 ∧ theta0 ≤ C.hi x := hx.1
      have hx1 : C.lo x ≤ theta1 ∧ theta1 ≤ C.hi x := hx.2
      apply le_max_of_le_right
      dsimp [ExternalIntervalProcedure.length]
      linarith
    · rw [Set.indicator_of_notMem hx]
      exact le_max_left _ _
  have hmono := integral_mono hindInt hexcessInt hpoint
  rw [integral_indicator_const Delta hI] at hmono
  simp only [smul_eq_mul] at hmono
  rw [mul_comm (Q0.real I) Delta] at hmono
  exact (mul_le_mul_of_nonneg_left hmass hDelta).trans hmono

/-- Given [the stated mathematical inputs and assumptions](hyp:epsilon,J,n,m,C,Q0,Q1,theta0,theta1,W0,Delta,alpha,htheta,hsep,hDelta,hcover0,hcover1,htv), this result [establishes the stated mathematical conclusion](goal). -/
lemma externalInterval_twoPoint_expectedExcessLength_of_tv {epsilon : ℝ}
    {J n m : ℕ}
    (C : ExternalIntervalProcedure epsilon J n m)
    (Q0 Q1 : Measure (ExternalSample epsilon J n m))
    [IsProbabilityMeasure Q0] [IsProbabilityMeasure Q1]
    (theta0 theta1 W0 Delta alpha : ℝ)
    (htheta : theta0 ≤ theta1)
    (hsep : theta1 - theta0 = W0 + Delta)
    (hDelta : 0 < Delta)
    (hcover0 : 1 - alpha ≤ Q0.real {x | C.contains x theta0})
    (hcover1 : 1 - alpha ≤ Q1.real {x | C.contains x theta1})
    (htv : Causalean.Stat.tvDist Q0 Q1 ≤ (1 - 2 * alpha) / 2) :
    Delta * ((1 - 2 * alpha) / 2) ≤
      ∫ x, max 0 (C.length x - W0) ∂Q0 := by
  have hexact := externalInterval_twoPoint_expectedExcessLength
    C Q0 Q1 theta0 theta1 W0 Delta alpha htheta hsep hDelta.le
    hcover0 hcover1
  have hcoefficient :
      (1 - 2 * alpha) / 2 ≤
        1 - 2 * alpha - Causalean.Stat.tvDist Q0 Q1 := by
    linarith
  exact (mul_le_mul_of_nonneg_left hcoefficient hDelta.le).trans hexact

end
end CausalSmith.PartialID.UnlinkedPropensityAte
