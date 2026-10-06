module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.Inference
public import Causalean.Stat.Minimax.TotalVariation

/-! Two-point testing lower bounds for ordinary released-trial confidence intervals. -/

public section

open MeasureTheory Set

namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- Given [the stated mathematical inputs and assumptions](hyp:K,n,C,Q0,Q1,θ0,θ1,α,hθ,hcover0,hcover1), this result [establishes the stated mathematical conclusion](goal). -/
lemma intervalProcedure_twoPoint_expectedLength {K n : ℕ}
    (C : IntervalProcedure n K)
    (Q0 Q1 : Measure (TrialSample n K))
    [IsProbabilityMeasure Q0] [IsProbabilityMeasure Q1]
    (θ0 θ1 α : ℝ) (hθ : θ0 ≤ θ1)
    (hcover0 : 1 - α ≤ Q0.real {x | C.contains x θ0})
    (hcover1 : 1 - α ≤ Q1.real {x | C.contains x θ1}) :
    (θ1 - θ0) * (1 - 2 * α - Causalean.Stat.tvDist Q0 Q1) ≤
      ∫ x, C.length x ∂Q0 := by
  let A0 : Set (TrialSample n K) := {x | C.contains x θ0}
  let A1 : Set (TrialSample n K) := {x | C.contains x θ1}
  let I := A0 ∩ A1
  have hA (θ : ℝ) : MeasurableSet {x | C.contains x θ} := by
    change MeasurableSet {x | C.lo x ≤ θ ∧ θ ≤ C.hi x}
    exact (measurableSet_le C.measurable_lo measurable_const).inter
      (measurableSet_le measurable_const C.measurable_hi)
  have hA0 : MeasurableSet A0 := hA θ0
  have hA1 : MeasurableSet A1 := hA θ1
  have hI : MeasurableSet I := hA0.inter hA1
  have htransfer : 1 - α - Causalean.Stat.tvDist Q0 Q1 ≤ Q0.real A1 := by
    have htv := Causalean.Stat.measureReal_sub_le_tvDist
      (μ := Q0) (ν := Q1) hA1
    dsimp [A1] at htv
    linarith
  have hmass : 1 - 2 * α - Causalean.Stat.tvDist Q0 Q1 ≤ Q0.real I := by
    have hu : Q0.real (A0 ∪ A1) ≤ 1 := measureReal_le_one
    have hsum := measureReal_union_add_inter (μ := Q0) (s := A0) (t := A1)
      hA1 (measure_ne_top Q0 A0) (measure_ne_top Q0 A1)
    change Q0.real (A0 ∪ A1) + Q0.real I = Q0.real A0 + Q0.real A1 at hsum
    linarith
  have hlenMeas : Measurable C.length := C.measurable_hi.sub C.measurable_lo
  have hlenNonneg (x : TrialSample n K) : 0 ≤ C.length x :=
    sub_nonneg.mpr (C.ordered x)
  have hlenBound (x : TrialSample n K) : C.length x ≤ 2 := by
    dsimp [IntervalProcedure.length]
    linarith [C.lower_bound x, C.upper_bound x]
  have hlenInt : Integrable C.length Q0 := by
    apply Integrable.of_bound hlenMeas.aestronglyMeasurable 2
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hlenNonneg x)]
    exact hlenBound x
  have hindInt : Integrable (I.indicator (fun _ => θ1 - θ0)) Q0 :=
    (integrable_const _).indicator hI
  have hpoint (x : TrialSample n K) :
      I.indicator (fun _ => θ1 - θ0) x ≤ C.length x := by
    by_cases hx : x ∈ I
    · rw [Set.indicator_of_mem hx]
      have hx0 : C.lo x ≤ θ0 ∧ θ0 ≤ C.hi x := hx.1
      have hx1 : C.lo x ≤ θ1 ∧ θ1 ≤ C.hi x := hx.2
      dsimp [IntervalProcedure.length]
      linarith
    · rw [Set.indicator_of_notMem hx]
      exact hlenNonneg x
  have hmono := integral_mono hindInt hlenInt hpoint
  rw [integral_indicator_const (θ1 - θ0) hI] at hmono
  simp only [smul_eq_mul] at hmono
  rw [mul_comm (Q0.real I) (θ1 - θ0)] at hmono
  exact (mul_le_mul_of_nonneg_left hmass (sub_nonneg.mpr hθ)).trans hmono

end
end CausalSmith.PartialID.UnlinkedPropensityAte
