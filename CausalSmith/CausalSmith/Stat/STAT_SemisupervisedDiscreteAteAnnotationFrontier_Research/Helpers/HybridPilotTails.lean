module
public import Causalean.Stat.Concentration.Poisson.Threshold
public import Causalean.Stat.Concentration.Poisson.SelfNormalized.Chernoff
public import Mathlib.MeasureTheory.Group.Convolution

/-! Poisson lower-tail leaves for the independent pilot branch. -/

public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal MeasureTheory
open Causalean.Stat.Concentration.Poisson

/-- Adding the two arm counts in a pilot cell produces the Poisson law with
the summed rate.  [the stated conclusion](goal). -/
lemma map_add_prod_poisson (lambda0 lambda1 : NNReal) :
    Measure.map (fun z : Nat × Nat ↦ z.1 + z.2)
        ((poissonMeasure lambda0).prod (poissonMeasure lambda1)) =
      poissonMeasure (lambda0 + lambda1) := by
  simpa [Measure.conv] using
    poissonMeasure_conv_poissonMeasure lambda0 lambda1

/-- Product-law form of the light-selection error bound, at the two arm rates
appearing in one pilot cell.  [the stated conditions](hyp:htp,hs0,hs1,hk) [the stated conclusion](goal). -/
lemma pilot_light_probability_le {tp s0 s1 : Real} (k : Nat)
    (htp : 0 ≤ tp) (hs0 : 0 ≤ s0) (hs1 : 0 ≤ s1)
    (hk : (k : Real) < tp * (s0 + s1) / 4) :
    ((poissonMeasure (Real.toNNReal (tp * s0))).prod
      (poissonMeasure (Real.toNNReal (tp * s1))))
        {z : Nat × Nat | z.1 + z.2 ≤ k} ≤
      ENNReal.ofReal (Real.exp (-(tp * (s0 + s1)) / 4)) := by
  let lambda0 := Real.toNNReal (tp * s0)
  let lambda1 := Real.toNNReal (tp * s1)
  have hr0 : (lambda0 : Real) = tp * s0 := by
    simp [lambda0, mul_nonneg htp hs0]
  have hr1 : (lambda1 : Real) = tp * s1 := by
    simp [lambda1, mul_nonneg htp hs1]
  have hsum : ((lambda0 + lambda1 : NNReal) : Real) = tp * (s0 + s1) := by
    rw [NNReal.coe_add, hr0, hr1]
    ring
  let S : Set Nat := {w : Nat | w ≤ k}
  have hS : MeasurableSet S := measurableSet_Iic
  calc
    ((poissonMeasure lambda0).prod (poissonMeasure lambda1))
        {z : Nat × Nat | z.1 + z.2 ≤ k} =
        (Measure.map (fun z : Nat × Nat ↦ z.1 + z.2)
          ((poissonMeasure lambda0).prod (poissonMeasure lambda1))) S := by
          rw [Measure.map_apply (by fun_prop) hS]
          rfl
    _ = poissonMeasure (lambda0 + lambda1) S := by
      rw [map_add_prod_poisson]
    _ ≤ ENNReal.ofReal (Real.exp (-((lambda0 + lambda1 : NNReal) : Real) / 4)) :=
      poisson_le_cutoff_of_cutoff_lt_quarter (lambda0 + lambda1) k (by
        rw [hsum]
        exact hk)
    _ = ENNReal.ofReal (Real.exp (-(tp * (s0 + s1)) / 4)) := by rw [hsum]

/-- Two-arm pilot-product form of the wrong-heavy-branch estimate.  [the stated conditions](hyp:htp,hs0,hs1,hr) [the stated conclusion](goal). -/
lemma pilot_heavy_probability_mul_exp_le {tp s0 s1 r : Real} (k : Nat)
    (htp : 0 ≤ tp) (hs0 : 0 ≤ s0) (hs1 : 0 ≤ s1) (hr : 0 ≤ r) :
    ((poissonMeasure (Real.toNNReal (tp * s0))).prod
      (poissonMeasure (Real.toNNReal (tp * s1)))).real
        {z : Nat × Nat | k < z.1 + z.2} *
        Real.exp (-r * (tp * (s0 + s1))) ≤
      Real.exp (-Real.log (1 + r) * (k : Real)) := by
  let lambda0 := Real.toNNReal (tp * s0)
  let lambda1 := Real.toNNReal (tp * s1)
  have hr0 : (lambda0 : Real) = tp * s0 := by
    simp [lambda0, mul_nonneg htp hs0]
  have hr1 : (lambda1 : Real) = tp * s1 := by
    simp [lambda1, mul_nonneg htp hs1]
  have hsum : ((lambda0 + lambda1 : NNReal) : Real) = tp * (s0 + s1) := by
    rw [NNReal.coe_add, hr0, hr1]
    ring
  have hprob :
      ((poissonMeasure lambda0).prod (poissonMeasure lambda1)).real
          {z : Nat × Nat | k < z.1 + z.2} =
        (poissonMeasure (lambda0 + lambda1)).real {w : Nat | k < w} := by
    simp only [MeasureTheory.measureReal_def]
    congr 1
    calc
      ((poissonMeasure lambda0).prod (poissonMeasure lambda1))
          {z : Nat × Nat | k < z.1 + z.2} =
          (Measure.map (fun z : Nat × Nat ↦ z.1 + z.2)
            ((poissonMeasure lambda0).prod (poissonMeasure lambda1)))
              {w : Nat | k < w} := by
            symm
            convert (Measure.map_apply (μ :=
                (poissonMeasure lambda0).prod (poissonMeasure lambda1))
                (f := fun z : Nat × Nat ↦ z.1 + z.2) (by fun_prop)
                (measurableSet_Ioi : MeasurableSet {w : Nat | k < w})) using 1
            · congr 1
            · congr 1
      _ = poissonMeasure (lambda0 + lambda1) {w : Nat | k < w} := by
        rw [map_add_prod_poisson]
  rw [hprob, ← hsum]
  exact poisson_upper_tail_mul_exp_le (lambda0 + lambda1) k hr

/-- Reciprocal-power statement of the wrong-heavy-branch estimate (C24).  [the stated conditions](hyp:htp,hs0,hs1,hr) [the stated conclusion](goal). -/
lemma pilot_heavy_probability_mul_exp_le_inv_pow
    {tp s0 s1 r : Real} (k : Nat)
    (htp : 0 ≤ tp) (hs0 : 0 ≤ s0) (hs1 : 0 ≤ s1) (hr : 0 ≤ r) :
    ((poissonMeasure (Real.toNNReal (tp * s0))).prod
      (poissonMeasure (Real.toNNReal (tp * s1)))).real
        {z : Nat × Nat | k < z.1 + z.2} *
        Real.exp (-r * (tp * (s0 + s1))) ≤ ((1 + r) ^ k)⁻¹ := by
  rw [← exp_neg_log_mul_nat_eq_inv_pow hr]
  exact pilot_heavy_probability_mul_exp_le k htp hs0 hs1 hr

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
