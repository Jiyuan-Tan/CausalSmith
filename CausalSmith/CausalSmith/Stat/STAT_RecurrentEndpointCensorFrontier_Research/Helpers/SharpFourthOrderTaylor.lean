module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SharpThirdOrderTaylor

/-! # Sharp quartic Taylor remainders

Integrating the cubic remainder of the derivative gives the exact quartic
Hölder coefficient, retaining all four integration factors for interpolation.
-/

public section

open MeasureTheory Set
namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Differentiation retains the top Hölder modulus at quartic order. -/
-- @node: fourthOrder_derivative_holder
lemma fourthOrder_derivative_holder (f : ℝ → ℝ) {α L : ℝ}
    (hf : HolderSeminormLe 4 α L f) :
    HolderSeminormLe 3 α L (derivWithin f (Icc (0 : ℝ) 1)) := by
  refine ⟨hf.1.derivWithin (uniqueDiffOn_Icc (by norm_num)) (by norm_num), ?_⟩
  intro x hx y hy
  simpa only [show 4 = 3 + 1 from rfl, iteratedDerivWithin_succ'] using hf.2 x hx y hy

/-- The quartic remainder integrates the derivative's cubic remainder. -/
-- @node: fourthOrder_remainder_integral
lemma fourthOrder_remainder_integral (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Icc (0 : ℝ) 1))
    {x y b : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1)
    (hxy : x ≤ y) :
    (∫ u in x..y, derivWithin f (Icc (0 : ℝ) 1) u -
      derivWithin f (Icc (0 : ℝ) 1) b -
      iteratedDerivWithin 2 f (Icc (0 : ℝ) 1) b * (u - b) -
      iteratedDerivWithin 3 f (Icc (0 : ℝ) 1) b * (u - b) ^ 2 / 2 -
      iteratedDerivWithin 4 f (Icc (0 : ℝ) 1) b * (u - b) ^ 3 / 6) =
      f y - f x - derivWithin f (Icc (0 : ℝ) 1) b * (y - x) -
      iteratedDerivWithin 2 f (Icc (0 : ℝ) 1) b *
        ((y - b) ^ 2 - (x - b) ^ 2) / 2 -
      iteratedDerivWithin 3 f (Icc (0 : ℝ) 1) b *
        ((y - b) ^ 3 - (x - b) ^ 3) / 6 -
      iteratedDerivWithin 4 f (Icc (0 : ℝ) 1) b *
        ((y - b) ^ 4 - (x - b) ^ 4) / 24 := by
  have hc := hf.continuousOn_derivWithin (uniqueDiffOn_Icc (by norm_num)) (by norm_num)
  have hsub : Icc x y ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc hx.1 hy.2
  have hi : IntervalIntegrable (fun u => derivWithin f (Icc (0 : ℝ) 1) u -
      derivWithin f (Icc (0 : ℝ) 1) b -
      iteratedDerivWithin 2 f (Icc (0 : ℝ) 1) b * (u - b) -
      iteratedDerivWithin 3 f (Icc (0 : ℝ) 1) b * (u - b) ^ 2 / 2) volume x y :=
    ((((hc.mono hsub).sub continuousOn_const).sub
      (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))).sub
        ((continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).pow 2)).div_const 2)).intervalIntegrable_of_Icc hxy
  have hp : IntervalIntegrable (fun u : ℝ =>
      iteratedDerivWithin 4 f (Icc (0 : ℝ) 1) b * (u - b) ^ 3 / 6) volume x y := by
    exact ((continuous_const.mul ((continuous_id.sub continuous_const).pow 3)).div_const 6).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hi hp, thirdOrder_remainder_integral f hf hx hy hxy,
    intervalIntegral.integral_div, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_right (f := fun u : ℝ => u ^ 3)]
  have hid : (∫ u in (x - b)..(y - b), u ^ 3) =
      ((y - b) ^ 4 - (x - b) ^ 4) / 4 := by
    rw [integral_pow]
    norm_num
  rw [hid]
  ring

/-- Integrating the derivative remainder to the right gives the sharp
fourth-order coefficient, without replacing the power by a supremum. -/
-- @node: fourthOrder_forward_remainder_bound
lemma fourthOrder_forward_remainder_bound (f : ℝ → ℝ) {α L : ℝ}
    (hα : 0 < α) (hf : HolderSeminormLe 4 α L f)
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1)
    (hxy : x ≤ y) :
    |f y - f x - derivWithin f (Icc (0 : ℝ) 1) x * (y - x) -
      iteratedDerivWithin 2 f (Icc (0 : ℝ) 1) x * (y - x) ^ 2 / 2 -
      iteratedDerivWithin 3 f (Icc (0 : ℝ) 1) x * (y - x) ^ 3 / 6 -
      iteratedDerivWithin 4 f (Icc (0 : ℝ) 1) x * (y - x) ^ 4 / 24| ≤
      L / ((α + 1) * (α + 2) * (α + 3) * (α + 4)) * (y - x) ^ (α + 4) := by
  have hdf := fourthOrder_derivative_holder f hf
  have hid := fourthOrder_remainder_integral f (hf.1.of_le (by norm_num))
    (b := x) hx hy hxy
  simp only [sub_self, zero_pow (by norm_num : 2 ≠ 0), zero_pow (by norm_num : 3 ≠ 0), zero_pow (by norm_num : 4 ≠ 0), sub_zero] at hid
  rw [← hid]
  have hc := hdf.1.continuousOn
  have hsub : Icc x y ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc hx.1 hy.2
  have hr : ContinuousOn (fun u => derivWithin f (Icc (0 : ℝ) 1) u -
      derivWithin f (Icc (0 : ℝ) 1) x -
      iteratedDerivWithin 2 f (Icc (0 : ℝ) 1) x * (u - x) -
        iteratedDerivWithin 3 f (Icc (0 : ℝ) 1) x * (u - x) ^ 2 / 2 -
      iteratedDerivWithin 4 f (Icc (0 : ℝ) 1) x * (u - x) ^ 3 / 6) (Icc x y) :=
    ((((hc.mono hsub).sub continuousOn_const).sub
      (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))).sub
        ((continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).pow 2)).div_const 2)).sub
          ((continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).pow 3)).div_const 6)
  have hp : Continuous (fun u : ℝ => (u - x) ^ (α + 3)) :=
    (continuous_id.sub continuous_const).rpow_const (fun _ => Or.inr (by linarith))
  calc
    _ ≤ ∫ u in x..y, |derivWithin f (Icc (0 : ℝ) 1) u -
        derivWithin f (Icc (0 : ℝ) 1) x -
        iteratedDerivWithin 2 f (Icc (0 : ℝ) 1) x * (u - x) -
        iteratedDerivWithin 3 f (Icc (0 : ℝ) 1) x * (u - x) ^ 2 / 2 -
      iteratedDerivWithin 4 f (Icc (0 : ℝ) 1) x * (u - x) ^ 3 / 6| :=
      intervalIntegral.abs_integral_le_integral_abs hxy
    _ ≤ ∫ u in x..y, L / ((α + 1) * (α + 2) * (α + 3)) * (u - x) ^ (α + 3) := by
      apply intervalIntegral.integral_mono_on hxy
        (hr.abs.intervalIntegrable_of_Icc hxy)
        ((continuous_const.mul hp).intervalIntegrable _ _)
      intro u hu
      simpa only [iteratedDerivWithin_succ', iteratedDerivWithin_one,
        iteratedDerivWithin_zero, Pi.mul_apply] using
        thirdOrder_forward_remainder_bound (derivWithin f (Icc (0 : ℝ) 1)) hα hdf
          hx (hsub hu) hu.1
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,
        firstOrder_forward_power_integral (by linarith : 0 < α + 3)]
      simp only [show α + 3 + 1 = α + 4 by ring]
      field_simp
      <;> ring

/-- Integrating to a right-hand expansion base gives the same sharp
fourth-order constant on the backward interpolation grid. -/
-- @node: fourthOrder_backward_remainder_bound
lemma fourthOrder_backward_remainder_bound (f : ℝ → ℝ) {α L : ℝ}
    (hα : 0 < α) (hf : HolderSeminormLe 4 α L f)
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1)
    (hxy : x ≤ y) :
    |f x - f y - derivWithin f (Icc (0 : ℝ) 1) y * (x - y) -
      iteratedDerivWithin 2 f (Icc (0 : ℝ) 1) y * (x - y) ^ 2 / 2 -
      iteratedDerivWithin 3 f (Icc (0 : ℝ) 1) y * (x - y) ^ 3 / 6 -
      iteratedDerivWithin 4 f (Icc (0 : ℝ) 1) y * (x - y) ^ 4 / 24| ≤
      L / ((α + 1) * (α + 2) * (α + 3) * (α + 4)) * (y - x) ^ (α + 4) := by
  have hdf := fourthOrder_derivative_holder f hf
  have hid := fourthOrder_remainder_integral f (hf.1.of_le (by norm_num))
    (b := y) hx hy hxy
  have heq : |f x - f y - derivWithin f (Icc (0 : ℝ) 1) y * (x - y) -
      iteratedDerivWithin 2 f (Icc (0 : ℝ) 1) y * (x - y) ^ 2 / 2 -
      iteratedDerivWithin 3 f (Icc (0 : ℝ) 1) y * (x - y) ^ 3 / 6 -
      iteratedDerivWithin 4 f (Icc (0 : ℝ) 1) y * (x - y) ^ 4 / 24| =
      |∫ u in x..y, derivWithin f (Icc (0 : ℝ) 1) u -
        derivWithin f (Icc (0 : ℝ) 1) y -
        iteratedDerivWithin 2 f (Icc (0 : ℝ) 1) y * (u - y) -
        iteratedDerivWithin 3 f (Icc (0 : ℝ) 1) y * (u - y) ^ 2 / 2 -
      iteratedDerivWithin 4 f (Icc (0 : ℝ) 1) y * (u - y) ^ 3 / 6| := by
    rw [hid, ← abs_neg]
    congr 1
    ring
  rw [heq]
  have hc := hdf.1.continuousOn
  have hsub : Icc x y ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc hx.1 hy.2
  have hr : ContinuousOn (fun u => derivWithin f (Icc (0 : ℝ) 1) u -
      derivWithin f (Icc (0 : ℝ) 1) y -
      iteratedDerivWithin 2 f (Icc (0 : ℝ) 1) y * (u - y) -
        iteratedDerivWithin 3 f (Icc (0 : ℝ) 1) y * (u - y) ^ 2 / 2 -
      iteratedDerivWithin 4 f (Icc (0 : ℝ) 1) y * (u - y) ^ 3 / 6) (Icc x y) :=
    ((((hc.mono hsub).sub continuousOn_const).sub
      (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))).sub
        ((continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).pow 2)).div_const 2)).sub
          ((continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).pow 3)).div_const 6)
  have hp : Continuous (fun u : ℝ => (y - u) ^ (α + 3)) :=
    (continuous_const.sub continuous_id).rpow_const (fun _ => Or.inr (by linarith))
  calc
    _ ≤ ∫ u in x..y, |derivWithin f (Icc (0 : ℝ) 1) u -
        derivWithin f (Icc (0 : ℝ) 1) y -
        iteratedDerivWithin 2 f (Icc (0 : ℝ) 1) y * (u - y) -
        iteratedDerivWithin 3 f (Icc (0 : ℝ) 1) y * (u - y) ^ 2 / 2 -
      iteratedDerivWithin 4 f (Icc (0 : ℝ) 1) y * (u - y) ^ 3 / 6| :=
      intervalIntegral.abs_integral_le_integral_abs hxy
    _ ≤ ∫ u in x..y, L / ((α + 1) * (α + 2) * (α + 3)) * (y - u) ^ (α + 3) := by
      apply intervalIntegral.integral_mono_on hxy
        (hr.abs.intervalIntegrable_of_Icc hxy)
        ((continuous_const.mul hp).intervalIntegrable _ _)
      intro u hu
      simpa only [iteratedDerivWithin_succ', iteratedDerivWithin_one,
        iteratedDerivWithin_zero, Pi.mul_apply] using
        thirdOrder_backward_remainder_bound (derivWithin f (Icc (0 : ℝ) 1)) hα hdf
          (hsub hu) hy hu.2
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,
        firstOrder_backward_power_integral (by linarith : 0 < α + 3)]
      simp only [show α + 3 + 1 = α + 4 by ring]
      field_simp
      <;> ring

/-- The cubic Taylor remainder has its exact integrated Hölder coefficient
at every base in the closed horizon, including both endpoints. -/
-- @node: fourthOrder_remainder_bound
lemma fourthOrder_remainder_bound (f : ℝ → ℝ) {α L : ℝ}
    (hα : 0 < α) (hf : HolderSeminormLe 4 α L f)
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    |f y - f x - derivWithin f (Icc (0 : ℝ) 1) x * (y - x) -
      iteratedDerivWithin 2 f (Icc (0 : ℝ) 1) x * (y - x) ^ 2 / 2 -
      iteratedDerivWithin 3 f (Icc (0 : ℝ) 1) x * (y - x) ^ 3 / 6 -
      iteratedDerivWithin 4 f (Icc (0 : ℝ) 1) x * (y - x) ^ 4 / 24| ≤
      L / ((α + 1) * (α + 2) * (α + 3) * (α + 4)) * |y - x| ^ (α + 4) := by
  by_cases hxy : x ≤ y
  · simpa only [abs_of_nonneg (sub_nonneg.mpr hxy)] using
      fourthOrder_forward_remainder_bound f hα hf hx hy hxy
  · have hyx := le_of_not_ge hxy
    simpa only [abs_of_nonpos (sub_nonpos.mpr hyx), neg_sub] using
      fourthOrder_backward_remainder_bound f hα hf hy hx hyx

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
