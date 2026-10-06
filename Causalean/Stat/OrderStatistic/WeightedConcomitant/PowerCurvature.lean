module
public import Causalean.Stat.OrderStatistic.WeightedConcomitant.PowerApproximation

/-!
# Curvature and hinge cells for real power weights

The curvature representation of a real power supplies the integrable
threshold weight and the hinge-cell increment used in the finite Bernstein
L1 estimate.
-/

@[expose] public section

namespace Causalean.Stat.OrderStatistic.WeightedConcomitant

open MeasureTheory
open Causalean.Stat.OrderStatistic

noncomputable section

/-- For a [sample size](hyp:N), [threshold](hyp:t), and [cell](hyp:j), the
 [cell increment of the positive-part hinge at that threshold](goal) is the
 difference between its values at the cell endpoints. -/
def hingeCell (N : ℕ) (t : ℝ) (j : Fin N) : ℝ :=
  max (((((j : ℕ) : ℝ) + 1) / N) - t) 0 -
    max ((((j : ℕ) : ℝ) / N) - t) 0

/-- For a [real power](hyp:s) and [threshold](hyp:t), the
 [curvature density](goal) of the power CDF is `s(s-1)(1-t)^(s-2)`. -/
def powerCurvature (s t : ℝ) : ℝ :=
  s * (s - 1) * (1 - t) ^ (s - 2)

/-- For a positive sample size, a hinge-cell increment is its full width below
the cell, the remaining width inside it, and zero above it. -/
theorem hingeCell_eq_piecewise {N : ℕ} (hN : 0 < N) (t : ℝ)
    (j : Fin N) :
    hingeCell N t j =
      if t ≤ ((j : ℕ) : ℝ) / (N : ℝ) then (1 : ℝ) / (N : ℝ)
      else if t ≤ (((j : ℕ) : ℝ) + 1) / N then
        (((j : ℕ) : ℝ) + 1) / N - t
      else (0 : ℝ) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : (((j : ℕ) : ℝ) / N) ≤
      (((j : ℕ) : ℝ) + 1) / N := by
    apply (div_le_div_iff_of_pos_right hNr).2
    linarith
  unfold hingeCell
  split_ifs with hleft hmid
  · rw [max_eq_left (by linarith : 0 ≤ ((((j : ℕ) : ℝ) + 1) / N) - t),
      max_eq_left (by linarith : 0 ≤ (((j : ℕ) : ℝ) / N) - t)]
    field_simp
    ring
  · rw [max_eq_left (by linarith : 0 ≤ ((((j : ℕ) : ℝ) + 1) / N) - t),
      max_eq_right (by linarith : (((j : ℕ) : ℝ) / N) - t ≤ 0)]
    ring
  · rw [max_eq_right (by linarith : ((((j : ℕ) : ℝ) + 1) / N) - t ≤ 0),
      max_eq_right (by linarith : (((j : ℕ) : ℝ) / N) - t ≤ 0)]
    ring

/-- For a power above one, integrating its curvature from zero to a point in
the unit interval gives the drop of the power density from its initial value. -/
theorem integral_powerCurvature_Icc {s u : ℝ} (hs : 1 < s)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    (∫ t in Set.Icc (0 : ℝ) u, powerCurvature s t ∂volume) =
      s - powerDensity s u := by
  have hpow : -1 < s - 2 := by linarith
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hu.1]
  simp only [powerCurvature, powerDensity]
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ (s - 2)) 1]
  simp only [sub_zero]
  rw [integral_rpow (a := 1 - u) (b := 1) (r := s - 2) (Or.inl hpow)]
  simp only [Real.one_rpow]
  have hs0 : s - 1 ≠ 0 := by linarith
  have he : s - 2 + 1 = s - 1 := by ring
  rw [he]
  field_simp

/-- For a real power above one, the curvature density has total mass `s` on
the unit interval. -/
theorem integral_powerCurvature_unit {s : ℝ} (hs : 1 < s) :
    (∫ t in Set.Icc (0 : ℝ) 1, powerCurvature s t ∂volume) = s := by
  rw [integral_powerCurvature_Icc hs (by norm_num)]
  simp [powerDensity, Real.zero_rpow (by linarith : s - 1 ≠ 0)]

/-- For a real power above one, the first moment of its curvature density
on the unit interval is one. -/
theorem integral_mul_powerCurvature_unit {s : ℝ} (hs : 1 < s) :
    (∫ t in Set.Icc (0 : ℝ) 1, t * powerCurvature s t ∂volume) = 1 := by
  have hp : -1 < s - 2 := by linarith
  have hq : -1 < s - 1 := by linarith
  have hp0 : s - 1 ≠ 0 := by linarith
  have hq0 : s ≠ 0 := by linarith
  calc
    (∫ t in Set.Icc (0 : ℝ) 1, t * powerCurvature s t ∂volume) =
        ∫ t in (0 : ℝ)..1, t * (s * (s - 1) * (1 - t) ^ (s - 2)) := by
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      rfl
    _ = ∫ x in (0 : ℝ)..1, (1 - x) * (s * (s - 1) * x ^ (s - 2)) := by
      convert intervalIntegral.integral_comp_sub_left
        (fun x : ℝ => (1 - x) * (s * (s - 1) * x ^ (s - 2))) 1
        (a := 0) (b := 1) using 1 <;> simp
    _ = ∫ x in (0 : ℝ)..1,
          (s * (s - 1)) * (x ^ (s - 2) - x ^ (s - 1)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx0 : 0 ≤ x := by
        have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by
          simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
        exact hx'.1
      have hpow : x ^ (s - 1) = x ^ (s - 2) * x := by
        rw [show s - 1 = s - 2 + 1 by ring,
          Real.rpow_add_one' hx0 (by linarith : s - 2 + 1 ≠ 0)]
      change (1 - x) * (s * (s - 1) * x ^ (s - 2)) =
        (s * (s - 1)) * (x ^ (s - 2) - x ^ (s - 1))
      rw [hpow]
      ring
    _ = (s * (s - 1)) *
          ((∫ x in (0 : ℝ)..1, x ^ (s - 2)) -
            (∫ x in (0 : ℝ)..1, x ^ (s - 1))) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_sub
          (intervalIntegral.intervalIntegrable_rpow' hp)
          (intervalIntegral.intervalIntegrable_rpow' hq)]
    _ = 1 := by
      rw [integral_rpow (a := 0) (b := 1) (r := s - 2) (Or.inl hp),
        integral_rpow (a := 0) (b := 1) (r := s - 1) (Or.inl hq)]
      have he : s - 2 + 1 = s - 1 := by ring
      have he' : s - 1 + 1 = s := by ring
      rw [he, he']
      simp [Real.zero_rpow hp0, Real.zero_rpow hq0]
      field_simp
      ring

/-- A [real power above one](hyp:hs) has [a curvature-weighted square-root
integral bounded by the square root of that power](goal). -/
theorem integral_powerCurvature_mul_sqrt_le {s : ℝ} (hs : 1 < s) :
    (∫ t in Set.Icc (0 : ℝ) 1,
      powerCurvature s t * Real.sqrt t ∂volume) ≤ Real.sqrt s := by
  have hr : IntervalIntegrable (fun x : ℝ => x ^ (s - 2)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hr' : IntervalIntegrable (fun t : ℝ => (1 - t) ^ (s - 2)) volume 0 1 := by
    convert (hr.comp_sub_left 1).symm using 1 <;> norm_num
  have hq : Integrable (powerCurvature s) (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
    change IntervalIntegrable (fun t : ℝ => s * (s - 1) * (1 - t) ^ (s - 2)) volume 0 1
    exact hr'.const_mul (s * (s - 1))
  have hpos : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ powerCurvature s t := by
    intro t ht
    unfold powerCurvature
    exact mul_nonneg (mul_nonneg (by linarith) (by linarith))
      (Real.rpow_nonneg (by linarith [ht.2]) _)
  have hsm : AEStronglyMeasurable (fun t : ℝ => Real.sqrt t)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    fun_prop
  have hsqrt : Integrable (fun t : ℝ => powerCurvature s t * Real.sqrt t)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    apply hq.mul_bdd (c := 1) hsm
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg t)]
    exact Real.sqrt_le_one.mpr ht.2
  have htint : Integrable (fun t : ℝ => t * powerCurvature s t)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    apply hq.bdd_mul (by fun_prop)
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact ht.2
  have hroot : 0 < Real.sqrt s := Real.sqrt_pos.2 (by linarith)
  have hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      powerCurvature s t * Real.sqrt t ≤
        (Real.sqrt s / 2) * (t * powerCurvature s t) +
          (1 / (2 * Real.sqrt s)) * powerCurvature s t := by
    intro t ht
    have hsq := sq_nonneg (Real.sqrt s * Real.sqrt t - 1)
    have htsq : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht.1
    have hssq : (Real.sqrt s) ^ 2 = s := Real.sq_sqrt (by linarith)
    have hp := hpos t ht
    have hroot_ne : Real.sqrt s ≠ 0 := ne_of_gt hroot
    have hscalar : Real.sqrt t ≤ Real.sqrt s / 2 * t + 1 / (2 * Real.sqrt s) := by
      calc
        Real.sqrt t ≤ (s * t + 1) / (2 * Real.sqrt s) := by
          apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.sqrt s)).mpr
          nlinarith [hsq]
        _ = Real.sqrt s / 2 * t + 1 / (2 * Real.sqrt s) := by
          field_simp
          nlinarith [hssq]
    calc
      powerCurvature s t * Real.sqrt t = Real.sqrt t * powerCurvature s t := by ring
      _ ≤ (Real.sqrt s / 2 * t + 1 / (2 * Real.sqrt s)) * powerCurvature s t :=
        mul_le_mul_of_nonneg_right hscalar hp
      _ = _ := by ring
  calc
    (∫ t in Set.Icc (0 : ℝ) 1, powerCurvature s t * Real.sqrt t ∂volume)
        ≤ ∫ t in Set.Icc (0 : ℝ) 1,
            (Real.sqrt s / 2) * (t * powerCurvature s t) +
              (1 / (2 * Real.sqrt s)) * powerCurvature s t ∂volume := by
          apply integral_mono_ae hsqrt ((htint.const_mul _).add (hq.const_mul _))
          filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
          exact hbound t ht
    _ = Real.sqrt s := by
      rw [integral_add (htint.const_mul _) (hq.const_mul _), integral_const_mul,
        integral_const_mul, integral_mul_powerCurvature_unit hs,
        integral_powerCurvature_unit hs]
      have hsq : (Real.sqrt s) ^ 2 = s := Real.sq_sqrt (by linarith)
      field_simp
      nlinarith

end
end Causalean.Stat.OrderStatistic.WeightedConcomitant
