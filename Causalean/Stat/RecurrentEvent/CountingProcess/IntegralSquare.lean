module
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
The deterministic square identity and absolute mixed-product bound for an
indefinite Lebesgue integral on a finite interval. These are the pathwise
calculus inputs to counting-process second-moment calculations.
-/

public section

open MeasureTheory

namespace Causalean.Stat.RecurrentEvent.CountingProcess

/-- For [a nonnegative horizon u](hyp:hu) and [a real rate integrable on the interval from 0 to
u](hyp:hf), [the square of the rate's integral over that interval equals the integral of twice
its running integral times the rate](goal). -/
theorem integral_prefix_square (f : ℝ → ℝ) (u : ℝ) (hu : 0 ≤ u)
    (hf : Integrable f (volume.restrict (Set.Icc 0 u))) :
    (∫ s in Set.Icc 0 u, f s ∂volume) ^ 2 =
      ∫ s in Set.Icc 0 u,
        2 * (∫ t in Set.Icc 0 s, f t ∂volume) * f s ∂volume := by
  let F : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, f t
  have hfi : IntervalIntegrable f volume 0 u :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hu).2 hf
  have hF : AbsolutelyContinuousOnInterval F 0 u :=
    hfi.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hderiv := hfi.ae_hasDerivAt_integral
  have hprod := hF.integral_deriv_mul_eq_sub hF
  have heq : (∫ s in (0 : ℝ)..u, deriv F s * F s + F s * deriv F s) =
      ∫ s in (0 : ℝ)..u, 2 * (∫ t in Set.Icc 0 s, f t ∂volume) * f s := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hderiv] with s hs hsmem
    have hsIcc : s ∈ Set.Icc (0 : ℝ) u := by
      simpa [Set.uIcc_of_le hu] using (Set.uIoc_subset_uIcc hsmem)
    have hds : deriv F s = f s :=
      (hs (by simpa [Set.uIcc_of_le hu] using hsIcc) 0 (by simp)).deriv
    have hprefix : F s = ∫ t in Set.Icc 0 s, f t ∂volume := by
      dsimp [F]
      rw [intervalIntegral.integral_of_le hsIcc.1, ← integral_Icc_eq_integral_Ioc]
    rw [hds, hprefix]
    ring
  rw [heq] at hprod
  have hzero : F 0 = 0 := by simp [F]
  have hfinal : F u = ∫ s in Set.Icc 0 u, f s ∂volume := by
    dsimp [F]
    rw [intervalIntegral.integral_of_le hu, ← integral_Icc_eq_integral_Ioc]
  rw [hfinal, hzero] at hprod
  simpa [pow_two, intervalIntegral.integral_of_le hu,
    ← integral_Icc_eq_integral_Ioc] using hprod.symm

/-- For [a nonnegative horizon u](hyp:hu) and [a real rate integrable on the interval from 0 to
u](hyp:hf), [the integral of the absolute value of the running integral times the rate is at most
the square of the integral of the rate's absolute value](goal). -/
theorem integral_prefix_mul_abs_le_square (f : ℝ → ℝ) (u : ℝ) (hu : 0 ≤ u)
    (hf : Integrable f (volume.restrict (Set.Icc 0 u))) :
    (∫ s in Set.Icc 0 u,
      |(∫ t in Set.Icc 0 s, f t ∂volume) * f s| ∂volume) ≤
      (∫ s in Set.Icc 0 u, |f s| ∂volume) ^ 2 := by
  /- On 0 ≤ s ≤ u, the absolute prefix is bounded by the prefix integral
     of |f|. Apply `integral_prefix_square` to |f|, use positivity, and
     compare the two integrands. The factor of two leaves slack. -/
  let g : ℝ → ℝ := fun s => |f s|
  let F : ℝ → ℝ := fun s => ∫ t in (0 : ℝ)..s, g t
  have hg : Integrable g (volume.restrict (Set.Icc 0 u)) := hf.abs
  have hgi : IntervalIntegrable g volume 0 u :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hu).2 hg
  have hF : ContinuousOn F (Set.Icc 0 u) := by
    simpa [Set.uIcc_of_le hu] using
      (hgi.absolutelyContinuousOnInterval_intervalIntegral (by simp)).continuousOn
  have hprod : Integrable (fun s => F s * g s)
      (volume.restrict (Set.Icc 0 u)) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hu).1
      (hgi.continuousOn_mul (by simpa [Set.uIcc_of_le hu] using hF))
  have hprefix (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) u) :
      F s = ∫ t in Set.Icc 0 s, g t ∂volume := by
    dsimp [F]
    rw [intervalIntegral.integral_of_le hs.1, ← integral_Icc_eq_integral_Ioc]
  have hright : Integrable
      (fun s => 2 * (∫ t in Set.Icc 0 s, g t ∂volume) * g s)
      (volume.restrict (Set.Icc 0 u)) := by
    have hae : (fun s => 2 * (F s * g s)) =ᵐ[volume.restrict (Set.Icc 0 u)]
        (fun s => 2 * (∫ t in Set.Icc 0 s, g t ∂volume) * g s) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      rw [hprefix s hs]
      ring
    have h := (hprod.const_mul (2 : ℝ)).congr hae
    exact h
  have hle : (∫ s in Set.Icc 0 u,
      |(∫ t in Set.Icc 0 s, f t ∂volume) * f s| ∂volume) ≤
      ∫ s in Set.Icc 0 u,
        2 * (∫ t in Set.Icc 0 s, g t ∂volume) * g s ∂volume := by
    apply integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall (fun s => abs_nonneg _)
    · exact hright
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      have hpre := abs_integral_le_integral_abs
        (μ := volume.restrict (Set.Icc 0 s)) (f := f)
      have hnonneg : 0 ≤ ∫ t in Set.Icc 0 s, g t ∂volume :=
        integral_nonneg (fun t => abs_nonneg (f t))
      rw [abs_mul]
      dsimp [g]
      change 0 ≤ ∫ t in Set.Icc 0 s, |f t| ∂volume at hnonneg
      nlinarith [mul_nonneg (sub_nonneg.mpr hpre) (abs_nonneg (f s)),
        mul_nonneg hnonneg (abs_nonneg (f s))]
  rw [← integral_prefix_square g u hu hg] at hle
  exact hle

end Causalean.Stat.RecurrentEvent.CountingProcess
