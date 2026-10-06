module
public import Causalean.Stat.CLT.BerryEsseen.SincSquaredFourier

/-! # Real integrals of the squared-sinc Fourier triangle

The squared-sinc transform is a compactly supported triangle. These two
real-variable integrals isolate the compact-support and normalization
calculations used in the fourth-power smoothing kernel.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory

/-- The squared-sinc Fourier triangle has squared integral `4π²/3` over the
real line. The triangle is `π max (1 - |u|/2) 0`. -/
theorem sincTriangle_square_integral :
    (∫ u : ℝ, (Real.pi * max (1 - |u| / 2) 0) ^ 2) =
      4 * Real.pi ^ 2 / 3 := by
  /- Split at -2, 0, and 2. Outside [-2,2] the integrand vanishes;
  on each half it is the square of an affine function. -/
  let f : ℝ → ℝ := fun u => (Real.pi * max (1 - |u| / 2) 0) ^ 2
  have hcont : Continuous f := by
    dsimp [f]
    fun_prop
  have hzero (u : ℝ) (hu : 2 ≤ |u|) : f u = 0 := by
    dsimp [f]
    rw [max_eq_right (by linarith : 1 - |u| / 2 ≤ 0)]
    ring
  have hsupp : Function.support f ⊆ Set.Ioc (-2) 2 := by
    intro u hu
    simp only [Function.mem_support] at hu
    constructor
    · by_contra hn
      have hle : u ≤ -2 := le_of_not_gt hn
      exact hu (hzero u (by rw [abs_of_nonpos (by linarith)]; linarith))
    · by_contra hn
      have hge : 2 ≤ u := le_of_lt (lt_of_not_ge hn)
      exact hu (hzero u (by rw [abs_of_nonneg (by linarith)]; linarith))
  have hleft : (∫ u in (-2 : ℝ)..0, f u) = 2 * Real.pi ^ 2 / 3 := by
    have heq : ∀ u ∈ Set.uIcc (-2 : ℝ) 0,
        f u = (Real.pi * (1 + u / 2)) ^ 2 := by
      intro u hu
      have hle : u ≤ 0 := by simpa using hu.2
      have hge : -2 ≤ u := by simpa using hu.1
      dsimp [f]
      rw [abs_of_nonpos hle, max_eq_left (by linarith : 0 ≤ 1 - -u / 2)]
      ring
    have hderiv (u : ℝ) :
        HasDerivAt (fun v : ℝ => Real.pi ^ 2 * (v + 2) ^ 3 / 12)
          ((Real.pi * (1 + u / 2)) ^ 2) u := by
      have h := ((hasDerivAt_id u).add_const 2 |>.pow 3 |>.const_mul (Real.pi ^ 2) |>.div_const 12)
      change HasDerivAt (fun v : ℝ => Real.pi ^ 2 * (v + 2) ^ 3 / 12)
        (Real.pi ^ 2 * (3 * (u + 2) ^ 2 * 1) / 12) u at h
      convert h using 1; ring
    calc
      _ = ∫ u in (-2 : ℝ)..0, (Real.pi * (1 + u / 2)) ^ 2 := by
        apply intervalIntegral.integral_congr
        exact heq
      _ = (Real.pi ^ 2 * (0 + 2) ^ 3 / 12) -
          (Real.pi ^ 2 * (-2 + 2) ^ 3 / 12) := by
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt
          (f := fun v : ℝ => Real.pi ^ 2 * (v + 2) ^ 3 / 12)
          (f' := fun v : ℝ => (Real.pi * (1 + v / 2)) ^ 2)
        · intro u _
          exact hderiv u
        · have hc : Continuous (fun v : ℝ => (Real.pi * (1 + v / 2)) ^ 2) := by
            fun_prop
          exact hc.intervalIntegrable _ _
      _ = _ := by ring
  have hright : (∫ u in (0 : ℝ)..2, f u) = 2 * Real.pi ^ 2 / 3 := by
    have heq : ∀ u ∈ Set.uIcc (0 : ℝ) 2,
        f u = (Real.pi * (1 - u / 2)) ^ 2 := by
      intro u hu
      have hge : 0 ≤ u := by simpa using hu.1
      have hle : u ≤ 2 := by simpa using hu.2
      dsimp [f]
      rw [abs_of_nonneg hge, max_eq_left (by linarith : 0 ≤ 1 - u / 2)]
    have hderiv (u : ℝ) :
        HasDerivAt (fun v : ℝ => -(Real.pi ^ 2 * (2 - v) ^ 3 / 12))
          ((Real.pi * (1 - u / 2)) ^ 2) u := by
      have h := (((hasDerivAt_const u (2 : ℝ)).sub (hasDerivAt_id u)).pow 3
        |>.const_mul (Real.pi ^ 2) |>.div_const 12 |>.neg)
      change HasDerivAt (fun v : ℝ => -(Real.pi ^ 2 * (2 - v) ^ 3 / 12))
        (-(Real.pi ^ 2 * (3 * (2 - u) ^ 2 * (0 - 1)) / 12)) u at h
      convert h using 1; ring
    calc
      _ = ∫ u in (0 : ℝ)..2, (Real.pi * (1 - u / 2)) ^ 2 := by
        apply intervalIntegral.integral_congr
        exact heq
      _ = -(Real.pi ^ 2 * (2 - 2) ^ 3 / 12) -
          -(Real.pi ^ 2 * (2 - 0) ^ 3 / 12) := by
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt
          (f := fun v : ℝ => -(Real.pi ^ 2 * (2 - v) ^ 3 / 12))
          (f' := fun v : ℝ => (Real.pi * (1 - v / 2)) ^ 2)
        · intro u _
          exact hderiv u
        · have hc : Continuous (fun v : ℝ => (Real.pi * (1 - v / 2)) ^ 2) := by
            fun_prop
          exact hc.intervalIntegrable _ _
      _ = _ := by ring
  change (∫ u : ℝ, f u) = _
  rw [← intervalIntegral.integral_eq_integral_of_support_subset hsupp,
    ← intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable (-2) 0) (hcont.intervalIntegrable 0 2),
    hleft, hright]
  ring

/-- [The self-convolution of the squared-sinc Fourier triangle
u ↦ π·max(1 − |u|/2, 0) vanishes](goal) at [every frequency t of absolute
value at least four](hyp:ht), including the endpoints. -/
theorem sincTriangle_convolution_outside (t : ℝ) (ht : 4 ≤ |t|) :
    (∫ u : ℝ,
      (Real.pi * max (1 - |u| / 2) 0) *
        (Real.pi * max (1 - |t - u| / 2) 0)) = 0 := by
  /- At each u, nonzero factors would imply |u| < 2 and |t-u| < 2,
  contradicting 4 ≤ |t| by the triangle inequality. Thus the
  integrand is pointwise zero, even when |t| = 4. -/
  apply integral_eq_zero_of_ae
  filter_upwards with u
  by_cases hu : 2 ≤ |u|
  · have hzero : max (1 - |u| / 2) 0 = 0 := by
      apply max_eq_right
      linarith
    simp [hzero]
  · have hu' : |u| < 2 := lt_of_not_ge hu
    have htri : |t| ≤ |t - u| + |u| := by
      calc
        |t| = |(t - u) + u| := by ring_nf
        _ ≤ |t - u| + |u| := abs_add_le _ _
    have hfar : 2 ≤ |t - u| := by linarith
    have hzero : max (1 - |t - u| / 2) 0 = 0 := by
      apply max_eq_right
      linarith
    simp [hzero]

end Causalean.Stat.CLT.BerryEsseen
