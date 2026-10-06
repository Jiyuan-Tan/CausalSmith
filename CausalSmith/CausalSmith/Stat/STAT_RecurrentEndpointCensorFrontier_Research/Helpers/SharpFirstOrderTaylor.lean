module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ContinuationBias
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ExplicitInterpolation
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Sharp first-order Taylor interpolation

Integrating the derivative Hölder modulus gives the exact first-order
Taylor coefficient. Forward and backward two-point grids then bound both
within-interval jets by the declared finite inverse norm.
-/

public section

open MeasureTheory Set
namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Integrating a Hölder power to the right of its base retains its exact coefficient. -/
-- @node: firstOrder_forward_power_integral
lemma firstOrder_forward_power_integral {α x y : ℝ} (hα : 0 < α) :
    (∫ u in x..y, (u - x) ^ α) = (y - x) ^ (α + 1) / (α + 1) := by
  rw [intervalIntegral.integral_comp_sub_right (f := fun u : ℝ => u ^ α)]
  rw [integral_rpow (Or.inl (by linarith : -1 < α))]
  simp [Real.zero_rpow (by linarith : α + 1 ≠ 0)]

/-- Integrating a Hölder power to the left of its base retains its exact coefficient. -/
-- @node: firstOrder_backward_power_integral
lemma firstOrder_backward_power_integral {α x y : ℝ} (hα : 0 < α) :
    (∫ u in x..y, (y - u) ^ α) = (y - x) ^ (α + 1) / (α + 1) := by
  rw [intervalIntegral.integral_comp_sub_left (f := fun u : ℝ => u ^ α) y]
  rw [integral_rpow (Or.inl (by linarith : -1 < α))]
  simp [Real.zero_rpow (by linarith : α + 1 ≠ 0)]

/-- The first-order remainder is the integral of the derivative increment,
including endpoint bases where only within-interval derivatives are available. -/
-- @node: firstOrder_remainder_integral
lemma firstOrder_remainder_integral (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Icc (0 : ℝ) 1))
    {x y b : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1)
    (hxy : x ≤ y) :
    (∫ u in x..y, derivWithin f (Icc (0 : ℝ) 1) u -
      derivWithin f (Icc (0 : ℝ) 1) b) =
      f y - f x - derivWithin f (Icc (0 : ℝ) 1) b * (y - x) := by
  have hc := hf.continuousOn_derivWithin (uniqueDiffOn_Icc (by norm_num)) (by norm_num)
  have hsub : Icc x y ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc hx.1 hy.2
  have hi : IntervalIntegrable (derivWithin f (Icc (0 : ℝ) 1)) volume x y :=
    (hc.mono hsub).intervalIntegrable_of_Icc hxy
  rw [intervalIntegral.integral_sub hi intervalIntegrable_const]
  have hFTC : (∫ u in x..y, derivWithin f (Icc (0 : ℝ) 1) u) = f y - f x := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hxy
      (hf.continuousOn.mono hsub) _ hi
    intro u hu
    have hu' : u ∈ Ioo (0 : ℝ) 1 := ⟨hx.1.trans_lt hu.1, hu.2.trans_le hy.2⟩
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds hu'.1 hu'.2)]
    exact ((hf.mono Ioo_subset_Icc_self).contDiffAt
      (isOpen_Ioo.mem_nhds hu')).differentiableAt (by norm_num) |>.hasDerivAt
  rw [hFTC, intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- Integrating the derivative's Hölder modulus proves the sharp first-order
Taylor bound at a left base, rather than a supremum bound losing the denominator. -/
-- @node: firstOrder_forward_remainder_bound
lemma firstOrder_forward_remainder_bound (f : ℝ → ℝ) {α L : ℝ}
    (hα : 0 < α) (hf : HolderSeminormLe 1 α L f)
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1)
    (hxy : x ≤ y) :
    |f y - f x - derivWithin f (Icc (0 : ℝ) 1) x * (y - x)| ≤
      L / (α + 1) * (y - x) ^ (α + 1) := by
  rw [← firstOrder_remainder_integral f hf.1 hx hy hxy]
  have hc := hf.1.continuousOn_derivWithin (uniqueDiffOn_Icc (by norm_num)) (by norm_num)
  have hsub : Icc x y ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc hx.1 hy.2
  have hp : Continuous (fun u : ℝ => (u - x) ^ α) :=
    (by fun_prop : Continuous (fun u : ℝ => u - x)).rpow_const (fun _ => Or.inr hα.le)
  calc
    _ ≤ ∫ u in x..y, |derivWithin f (Icc (0 : ℝ) 1) u -
        derivWithin f (Icc (0 : ℝ) 1) x| := intervalIntegral.abs_integral_le_integral_abs hxy
    _ ≤ ∫ u in x..y, L * (u - x) ^ α := by
      apply intervalIntegral.integral_mono_on hxy
        (((hc.mono hsub).sub continuousOn_const).abs.intervalIntegrable_of_Icc hxy)
        ((continuous_const.mul hp).intervalIntegrable _ _)
      intro u hu
      simpa only [Pi.sub_apply, Pi.mul_apply, iteratedDerivWithin_one, abs_of_nonneg (sub_nonneg.mpr hu.1)] using
        hf.2 u (hsub hu) x hx
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, firstOrder_forward_power_integral hα]
      ring

/-- The same sharp bound holds for the backward grid at a right base. -/
-- @node: firstOrder_backward_remainder_bound
lemma firstOrder_backward_remainder_bound (f : ℝ → ℝ) {α L : ℝ}
    (hα : 0 < α) (hf : HolderSeminormLe 1 α L f)
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1)
    (hxy : x ≤ y) :
    |f x - f y - derivWithin f (Icc (0 : ℝ) 1) y * (x - y)| ≤
      L / (α + 1) * (y - x) ^ (α + 1) := by
  have hid := firstOrder_remainder_integral f hf.1 (b := y) hx hy hxy
  have heq : |f x - f y - derivWithin f (Icc (0 : ℝ) 1) y * (x - y)| =
      |∫ u in x..y, derivWithin f (Icc (0 : ℝ) 1) u -
        derivWithin f (Icc (0 : ℝ) 1) y| := by
    rw [hid, ← abs_neg]
    congr 1
    ring
  rw [heq]
  have hc := hf.1.continuousOn_derivWithin (uniqueDiffOn_Icc (by norm_num)) (by norm_num)
  have hsub : Icc x y ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc hx.1 hy.2
  have hp : Continuous (fun u : ℝ => (y - u) ^ α) :=
    (by fun_prop : Continuous (fun u : ℝ => y - u)).rpow_const (fun _ => Or.inr hα.le)
  calc
    _ ≤ ∫ u in x..y, |derivWithin f (Icc (0 : ℝ) 1) u -
        derivWithin f (Icc (0 : ℝ) 1) y| := intervalIntegral.abs_integral_le_integral_abs hxy
    _ ≤ ∫ u in x..y, L * (y - u) ^ α := by
      apply intervalIntegral.integral_mono_on hxy
        (((hc.mono hsub).sub continuousOn_const).abs.intervalIntegrable_of_Icc hxy)
        ((continuous_const.mul hp).intervalIntegrable _ _)
      intro u hu
      simpa only [Pi.sub_apply, Pi.mul_apply, iteratedDerivWithin_one, abs_of_nonpos (sub_nonpos.mpr hu.2),
        neg_sub] using hf.2 u (hsub hu) y hy
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, firstOrder_backward_power_integral hα]
      ring
/-- The forward and backward integral bounds give a sharp remainder at either base. -/
-- @node: firstOrder_remainder_bound
lemma firstOrder_remainder_bound (f : ℝ → ℝ) {α L : ℝ}
    (hα : 0 < α) (hf : HolderSeminormLe 1 α L f)
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    |f y - f x - derivWithin f (Icc (0 : ℝ) 1) x * (y - x)| ≤
      L / (α + 1) * |y - x| ^ (α + 1) := by
  by_cases hxy : x ≤ y
  · simpa only [abs_of_nonneg (sub_nonneg.mpr hxy)] using
      firstOrder_forward_remainder_bound f hα hf hx hy hxy
  · have hyx := le_of_not_ge hxy
    simpa only [abs_of_nonpos (sub_nonpos.mpr hyx), neg_sub] using
      firstOrder_backward_remainder_bound f hα hf hy hx hyx

/-- On the two-point grid, the inverse matrix yields the declared jet envelope
from the sharp Taylor remainder. The direction is chosen to stay within the horizon. -/
-- @node: firstOrder_interpolation_jet_bound
lemma firstOrder_interpolation_jet_bound (f : ℝ → ℝ) {β M L : ℝ}
    (hβ : 1 < β) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hf : HolderSeminormLe 1 (β - 1) L f)
    (hv : ∀ t ∈ Icc (0 : ℝ) 1, |f t| ≤ M)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (j : Fin (1 + 1)) :
    |iteratedDerivWithin j.val f (Icc (0 : ℝ) 1) x| ≤
      interpolationInverseNorm 1 * (M + L / β * (2 : ℝ) ^ (-β)) := by
  let v : Fin (1 + 1) → ℝ := fun j => iteratedDerivWithin j.val f (Icc (0 : ℝ) 1) x
  let R := L / β * (2 : ℝ) ^ (-β)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hα : 0 < β - 1 := by linarith
  have he : β - 1 + 1 = β := by ring
  have hpow : (1 / 2 : ℝ) ^ β = (2 : ℝ) ^ (-β) := by
    rw [one_div, Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num)]
  have hr {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (htx : |t - x| ≤ 1 / 2) :
      |f t - f x - derivWithin f (Icc (0 : ℝ) 1) x * (t - x)| ≤ R := by
    have hb := firstOrder_remainder_bound f hα hf hx ht
    rw [he] at hb
    refine hb.trans ?_
    dsimp [R]
    rw [← hpow]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (abs_nonneg _) htx (by linarith)) (div_nonneg hL (by linarith))
  have hcalc (r : Fin (1 + 1)) :
      (interpolationMatrix 1).mulVec v r =
        f x + derivWithin f (Icc (0 : ℝ) 1) x * ((r.val : ℝ) / 2) := by
    simp [interpolationMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, v,
      iteratedDerivWithin_one]
    ring
  by_cases hleft : x ≤ 1 / 2
  · let y : Fin (1 + 1) → ℝ := fun r => f (x + (r.val : ℝ) / 2)
    have ht (r : Fin (1 + 1)) : x + (r.val : ℝ) / 2 ∈ Icc (0 : ℝ) 1 := by
      have hr1 : (r.val : ℝ) ≤ 1 := by exact_mod_cast (show r.val ≤ 1 by omega)
      have hr0 : (0 : ℝ) ≤ r.val := by positivity
      constructor <;> linarith [hx.1]
    apply interpolationMatrix_jet_bound_of_remainder 1 (by omega) v y hM hR
      (fun r => hv _ (ht r)) _ j
    intro r
    rw [hcalc]
    have hr1 : (r.val : ℝ) ≤ 1 := by exact_mod_cast (show r.val ≤ 1 by omega)
    have hd : |x + (r.val : ℝ) / 2 - x| ≤ 1 / 2 := by
      rw [show x + (r.val : ℝ) / 2 - x = (r.val : ℝ) / 2 by ring,
        abs_of_nonneg (by positivity)]
      linarith
    simpa only [y, show x + (r.val : ℝ) / 2 - x = (r.val : ℝ) / 2 by ring,
      sub_sub] using hr (ht r) hd
  · let y : Fin (1 + 1) → ℝ := fun r => f (x - (r.val : ℝ) / 2)
    have ht (r : Fin (1 + 1)) : x - (r.val : ℝ) / 2 ∈ Icc (0 : ℝ) 1 := by
      have hr1 : (r.val : ℝ) ≤ 1 := by exact_mod_cast (show r.val ≤ 1 by omega)
      have hr0 : (0 : ℝ) ≤ r.val := by positivity
      constructor <;> linarith [hx.2]
    apply interpolationMatrix_backward_jet_bound_of_remainder 1 (by omega) v y hM hR
      (fun r => hv _ (ht r)) _ j
    intro r
    have hr1 : (r.val : ℝ) ≤ 1 := by exact_mod_cast (show r.val ≤ 1 by omega)
    have hd : |x - (r.val : ℝ) / 2 - x| ≤ 1 / 2 := by
      rw [show x - (r.val : ℝ) / 2 - x = -((r.val : ℝ) / 2) by ring,
        abs_neg, abs_of_nonneg (by positivity)]
      linarith
    have hc : (interpolationMatrix 1).mulVec (fun j => (-1 : ℝ) ^ j.val * v j) r =
        f x - derivWithin f (Icc (0 : ℝ) 1) x * ((r.val : ℝ) / 2) := by
      simp [interpolationMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, v,
        iteratedDerivWithin_one]
      ring
    rw [hc]
    convert hr (ht r) hd using 1 <;> dsimp [y] <;> congr 1 <;> ring

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
