module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.Basic
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Smooth compactly supported product bumps on cubes

This module defines a normalized smooth product bump and proves bandwidth-uniform
intrinsic Hölder-ball bounds for its translated, rescaled copies on the unit cube.
-/

@[expose] public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

open Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- At [a real input](hyp:x), [the normalized bump profile](goal) is given by
[the smooth-transition formula](step:1). -/
noncomputable def bumpProfile (x : ℝ) : ℝ :=
  Real.exp 1 * expNegInvGlue (1 - x ^ 2)

/-- In [a finite dimension](hyp:d), [the product bump at the given point](hyp:x)
is [the finite coordinate product](goal) given by
[multiplying the normalized profiles](step:1). -/
noncomputable def productBump {d : ℕ} (x : Fin d → ℝ) : ℝ :=
  ∏ i : Fin d, bumpProfile (x i)

/-- [The normalized bump profile](goal) is smooth to every finite order. -/
theorem bumpProfile_contDiff :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) bumpProfile := by
  unfold bumpProfile
  have hinner : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ => 1 - x ^ 2) := by fun_prop
  exact contDiff_const.mul (expNegInvGlue.contDiff.comp hinner)

/-- [The normalized bump profile](goal) takes value one at zero. -/
theorem bumpProfile_zero : bumpProfile 0 = 1 := by
  simp [bumpProfile, expNegInvGlue, Real.exp_neg, Real.exp_ne_zero]

/-- When [the real input](hyp:x) [has absolute value at least one](hyp:hx),
[the normalized bump profile vanishes](goal). -/
theorem bumpProfile_eq_zero_of_one_le_abs {x : ℝ} (hx : 1 ≤ |x|) :
    bumpProfile x = 0 := by
  have hx2 : 1 ≤ x ^ 2 := by nlinarith [sq_nonneg (|x|), sq_abs x]
  simp [bumpProfile, expNegInvGlue.zero_of_nonpos (show 1 - x ^ 2 ≤ 0 by linarith)]

/-- In [a finite dimension](hyp:d), [the product bump](goal) is smooth to every finite order. -/
theorem productBump_contDiff {d : ℕ} :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (productBump (d := d)) := by
  change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun x : Fin d → ℝ => ∏ i : Fin d, bumpProfile (x i))
  apply contDiff_prod
  intro i _
  have hcoord : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : Fin d → ℝ => x i) := by fun_prop
  exact bumpProfile_contDiff.comp hcoord

/-- In [a finite dimension](hyp:d), [the product bump](goal) takes value one at the origin. -/
theorem productBump_zero {d : ℕ} : productBump (d := d) 0 = 1 := by
  simp [productBump, bumpProfile_zero]

/-- In [a finite dimension](hyp:d), when [a point](hyp:x) has
[a coordinate](hyp:i) [whose absolute value is at least one](hyp:hi),
[the product bump vanishes](goal). -/
theorem productBump_eq_zero_of_coordinate {d : ℕ} (x : Fin d → ℝ)
    {i : Fin d} (hi : 1 ≤ |x i|) : productBump x = 0 := by
  exact Finset.prod_eq_zero (Finset.mem_univ i) (bumpProfile_eq_zero_of_one_le_abs hi)

/-- In [a finite dimension](hyp:d), [the product bump](goal) has compact support. -/
theorem productBump_hasCompactSupport {d : ℕ} :
    HasCompactSupport (productBump (d := d)) := by
  apply HasCompactSupport.intro (K := {x : Fin d → ℝ | ∀ i, x i ∈ Set.Icc (-1) 1})
    (isCompact_pi_infinite (fun _ => isCompact_Icc))
  intro x hx
  have hcoord : ∃ i : Fin d, 1 ≤ |x i| := by
    simp only [Set.mem_ofPred_eq, Set.mem_Icc, not_forall] at hx
    obtain ⟨i, hi⟩ := hx
    refine ⟨i, ?_⟩
    rcases not_and_or.mp hi with hi | hi
    · have h : x i ≤ -1 := le_of_lt (lt_of_not_ge hi)
      simpa [abs_of_nonpos (by linarith : x i ≤ 0)] using (neg_le_neg h)
    · have h : 1 ≤ x i := le_of_lt (lt_of_not_ge hi)
      simpa [abs_of_nonneg (by linarith : 0 ≤ x i)] using h
  obtain ⟨i, hi⟩ := hcoord
  exact productBump_eq_zero_of_coordinate x hi

/-- In [a finite dimension](hyp:d), at [a derivative order](hyp:j),
[the product bump has a finite global derivative bound](goal). -/
theorem productBump_iteratedFDeriv_bounded {d : ℕ} (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Fin d → ℝ,
      ‖iteratedFDeriv ℝ j (productBump (d := d)) x‖ ≤ C := by
  have hprofile : ContDiff ℝ (j + 1 : ℕ) bumpProfile := by
    unfold bumpProfile
    have hinner : ContDiff ℝ (j + 1 : ℕ) (fun x : ℝ => 1 - x ^ 2) := by fun_prop
    exact contDiff_const.mul (expNegInvGlue.contDiff.comp hinner)
  have hproduct : ContDiff ℝ (j + 1 : ℕ) (productBump (d := d)) := by
    change ContDiff ℝ (j + 1 : ℕ) (fun x : Fin d → ℝ => ∏ i : Fin d, bumpProfile (x i))
    apply contDiff_prod
    intro i _
    have hcoord : ContDiff ℝ (j + 1 : ℕ) (fun x : Fin d → ℝ => x i) := by fun_prop
    exact hprofile.comp hcoord
  have hcontinuous : Continuous (iteratedFDeriv ℝ j (productBump (d := d))) :=
    hproduct.continuous_iteratedFDeriv (by exact_mod_cast Nat.le_succ j)
  obtain ⟨C, hC⟩ := hcontinuous.bounded_above_of_compact_support
    (productBump_hasCompactSupport.iteratedFDeriv j)
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x
  exact (hC x).trans (le_max_left _ _)

/-- In [a finite dimension](hyp:d), with [smoothness exponent and bandwidth](hyp:β,h)
and [a center](hyp:x₀) at [an evaluation point](hyp:x), [the scaled product bump](goal) is given by
[amplitude scaling followed by translation and dilation](step:1). -/
noncomputable def scaledProductBump {d : ℕ} (β h : ℝ)
    (x₀ : Fin d → ℝ) (x : Fin d → ℝ) : ℝ :=
  h ^ β * productBump (h⁻¹ • (x - x₀))

/-- In [a finite dimension](hyp:d), with [a smoothness exponent](hyp:β),
[a nonzero bandwidth](hyp:_hh), [a center](hyp:x₀), and
[an evaluation point](hyp:x), [the scaled bump has
the coordinatewise-division representation](goal). -/
theorem scaledProductBump_eq_coordinate_div {d : ℕ} (β : ℝ)
    {h : ℝ} (_hh : h ≠ 0) (x₀ x : Fin d → ℝ) :
    scaledProductBump β h x₀ x =
      h ^ β * productBump (fun i => (x i - x₀ i) / h) := by
  simp only [scaledProductBump]
  have harg : h⁻¹ • (x - x₀) = (fun i => (x i - x₀ i) / h) := by
    funext i
    simp [Pi.smul_apply, Pi.sub_apply, div_eq_mul_inv, mul_comm]
  rw [harg]

/-- In [a finite dimension](hyp:d), for
[a smoothness exponent and bandwidth](hyp:β,h) and [a center](hyp:x₀),
[the scaled product bump is smooth to every finite order](goal). -/
theorem scaledProductBump_contDiff {d : ℕ} (β h : ℝ)
    (x₀ : Fin d → ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (scaledProductBump β h x₀) := by
  unfold scaledProductBump
  have hinner : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : Fin d → ℝ => h⁻¹ • (x - x₀)) := by fun_prop
  exact contDiff_const.mul (productBump_contDiff.comp hinner)

/-- In [a finite dimension](hyp:d), at [a derivative order](hyp:j), with
[a smoothness exponent and bandwidth](hyp:β,h), [a center](hyp:x₀), and
[an evaluation point](hyp:x), [the scaled bump derivative has
the exact dilation formula](goal). -/
theorem scaledProductBump_iteratedFDeriv {d : ℕ} (j : ℕ)
    (β h : ℝ) (x₀ x : Fin d → ℝ) :
    iteratedFDeriv ℝ j (scaledProductBump β h x₀) x =
      (h ^ β) • ((h⁻¹) ^ j •
        iteratedFDeriv ℝ j (productBump (d := d)) (h⁻¹ • (x - x₀))) := by
  have hg : ContDiff ℝ (j : WithTop ℕ∞)
      (fun z : Fin d → ℝ => productBump (h⁻¹ • z)) :=
    ((productBump_contDiff (d := d)).of_le (WithTop.coe_le_coe.mpr le_top)).comp
      (by fun_prop)
  have htrans : ContDiff ℝ (j : WithTop ℕ∞)
      (fun z : Fin d → ℝ => productBump (h⁻¹ • (z - x₀))) :=
    hg.comp (by fun_prop)
  change iteratedFDeriv ℝ j
    (fun z : Fin d → ℝ => (h ^ β) • productBump (h⁻¹ • (z - x₀))) x = _
  rw [iteratedFDeriv_const_smul_apply' htrans.contDiffAt]
  have ht := iteratedFDeriv_comp_sub (𝕜 := ℝ)
    (f := fun z : Fin d → ℝ => productBump (h⁻¹ • z)) j x₀ x
  rw [ht]
  rw [show iteratedFDeriv ℝ j
      (fun z : Fin d → ℝ => productBump (h⁻¹ • z)) =
      fun z => (h⁻¹) ^ j •
        iteratedFDeriv ℝ j (productBump (d := d)) (h⁻¹ • z) from
    iteratedFDeriv_comp_const_smul h⁻¹
      ((productBump_contDiff (d := d)).of_le (WithTop.coe_le_coe.mpr le_top))]

/-- In [a finite dimension](hyp:d), for
[a positive smoothness exponent](hyp:β,hβ), [a nonnegative global Hölder
coefficient for the normalized top derivative exists](goal). -/
theorem exists_productBump_top_modulus {d : ℕ} (β : ℝ) (hβ : 0 < β) :
    let m := ⌈β⌉₊ - 1
    let s := β - (m : ℝ)
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : Fin d → ℝ,
      ‖iteratedFDeriv ℝ m (productBump (d := d)) x -
        iteratedFDeriv ℝ m (productBump (d := d)) y‖ ≤
        C * ‖x - y‖ ^ s := by
  let m := ⌈β⌉₊ - 1
  let s := β - (m : ℝ)
  have hmpos : 0 < ⌈β⌉₊ := Nat.ceil_pos.mpr hβ
  have hmadd : m + 1 = ⌈β⌉₊ := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (by omega))
  have hmlt : (m : ℝ) < β := Nat.lt_ceil.mp (by omega : m < ⌈β⌉₊)
  have hs : 0 < s := by dsimp [s]; linarith
  have hs1 : s ≤ 1 := by
    have hceil := Nat.le_ceil β
    have hcast : (m : ℝ) + 1 = (⌈β⌉₊ : ℝ) := by exact_mod_cast hmadd
    dsimp [s]
    linarith
  obtain ⟨B, hB0, hB⟩ := productBump_iteratedFDeriv_bounded (d := d) m
  obtain ⟨L, hL0, hL⟩ := productBump_iteratedFDeriv_bounded (d := d) (m + 1)
  let A := max B L
  have hA0 : 0 ≤ A := le_trans hB0 (le_max_left B L)
  refine ⟨2 * A, by positivity, ?_⟩
  intro x y
  let f := iteratedFDeriv ℝ m (productBump (d := d))
  have hdiff : ∀ z : Fin d → ℝ, DifferentiableAt ℝ f z := by
    intro z
    exact (productBump_contDiff (d := d)).contDiffAt.differentiableAt_iteratedFDeriv
      (by exact_mod_cast (show (m : ℕ∞) < ⊤ from by simp))
  have hlip : ‖f x - f y‖ ≤ A * ‖x - y‖ := by
    have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le
      (s := Set.univ) (x := y) (y := x) (f := f) (C := A)
      (fun z _ => hdiff z) (by
        intro z _
        rw [norm_fderiv_iteratedFDeriv]
        exact (hL z).trans (le_max_right B L)) convex_univ (Set.mem_univ _) (Set.mem_univ _)
    simpa using hmv
  by_cases hsmall : ‖x - y‖ ≤ 1
  · have hpow : ‖x - y‖ ≤ ‖x - y‖ ^ s :=
      Real.self_le_rpow_of_le_one (norm_nonneg _) hsmall hs1
    calc
      ‖f x - f y‖ ≤ A * ‖x - y‖ := hlip
      _ ≤ A * ‖x - y‖ ^ s := mul_le_mul_of_nonneg_left hpow hA0
      _ ≤ (2 * A) * ‖x - y‖ ^ s := by
        have := Real.rpow_nonneg (norm_nonneg (x - y)) s
        nlinarith
  · have hpow : 1 ≤ ‖x - y‖ ^ s :=
      Real.one_le_rpow (le_of_lt (lt_of_not_ge hsmall)) hs.le
    calc
      ‖f x - f y‖ ≤ ‖f x‖ + ‖f y‖ := norm_sub_le _ _
      _ ≤ 2 * A := by
        have hx := (hB x).trans (le_max_left B L)
        have hy := (hB y).trans (le_max_left B L)
        dsimp [f] at *
        linarith
      _ ≤ (2 * A) * ‖x - y‖ ^ s := by nlinarith

/-- In [a finite dimension](hyp:d), for
[a positive smoothness exponent](hyp:β,hβ), [a nonnegative derivative bound
uniform over admissible scaled bumps exists](goal). -/
theorem exists_scaledProductBump_deriv_bound {d : ℕ} (β : ℝ) (hβ : 0 < β) :
    let m := ⌈β⌉₊ - 1
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : ℝ), 0 < h → h ≤ 1 →
      ∀ (x₀ : Fin d → ℝ) (j : ℕ), j ≤ m → ∀ x : Fin d → ℝ,
      ‖iteratedFDeriv ℝ j (scaledProductBump β h x₀) x‖ ≤ C := by
  let m := ⌈β⌉₊ - 1
  have hmpos : 0 < ⌈β⌉₊ := Nat.ceil_pos.mpr hβ
  have hmlt : (m : ℝ) < β := Nat.lt_ceil.mp (by omega : m < ⌈β⌉₊)
  let D : ℕ → ℝ := fun j => (productBump_iteratedFDeriv_bounded (d := d) j).choose
  have hD0 : ∀ j, 0 ≤ D j := fun j =>
    (productBump_iteratedFDeriv_bounded (d := d) j).choose_spec.1
  have hD : ∀ j x, ‖iteratedFDeriv ℝ j (productBump (d := d)) x‖ ≤ D j :=
    fun j x => (productBump_iteratedFDeriv_bounded (d := d) j).choose_spec.2 x
  let C := ∑ j ∈ Finset.range (m + 1), D j
  have hC0 : 0 ≤ C := Finset.sum_nonneg (fun j _ => hD0 j)
  refine ⟨C, hC0, ?_⟩
  intro h hh hh1 x₀ j hj x
  have hh0 : h ≠ 0 := ne_of_gt hh
  have hjβ : (j : ℝ) ≤ β := by
    have hjm : (j : ℝ) ≤ m := Nat.cast_le.mpr hj
    linarith
  have hscale : h ^ β * (h⁻¹) ^ j ≤ 1 := by
    have hp : h ^ β ≤ h ^ (j : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge' hh.le hh1 (Nat.cast_nonneg j) hjβ
    calc
      h ^ β * (h⁻¹) ^ j ≤ h ^ (j : ℝ) * (h⁻¹) ^ j :=
        mul_le_mul_of_nonneg_right hp (pow_nonneg (inv_nonneg.mpr hh.le) j)
      _ = 1 := by rw [Real.rpow_natCast, ← mul_pow, mul_inv_cancel₀ hh0, one_pow]
  have hjC : D j ≤ C := Finset.single_le_sum (fun i _ => hD0 i)
    (by simpa only [Finset.mem_range] using (Nat.lt_succ_of_le (show j ≤ m from hj)))
  rw [scaledProductBump_iteratedFDeriv]
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_pow, abs_inv, abs_of_pos hh, abs_of_nonneg (Real.rpow_nonneg hh.le β)]
  calc
    h ^ β * ((h⁻¹) ^ j * ‖iteratedFDeriv ℝ j (productBump (d := d)) _‖)
        ≤ (h ^ β * (h⁻¹) ^ j) * D j := by
          calc
            _ ≤ h ^ β * ((h⁻¹) ^ j * D j) := by
              gcongr
              exact hD j _
            _ = _ := by ring
    _ ≤ D j := by nlinarith [hD0 j]
    _ ≤ C := hjC

/-- In [a finite dimension](hyp:d), for
[a positive smoothness exponent](hyp:β,hβ), [a nonnegative global Hölder
coefficient uniform over admissible scaled bumps exists](goal). -/
theorem exists_scaledProductBump_top_modulus {d : ℕ} (β : ℝ) (hβ : 0 < β) :
    let m := ⌈β⌉₊ - 1
    let s := β - (m : ℝ)
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : ℝ), 0 < h → h ≤ 1 →
      ∀ (x₀ x y : Fin d → ℝ),
      ‖iteratedFDeriv ℝ m (scaledProductBump β h x₀) x -
        iteratedFDeriv ℝ m (scaledProductBump β h x₀) y‖ ≤
        C * ‖x - y‖ ^ s := by
  let m := ⌈β⌉₊ - 1
  let s := β - (m : ℝ)
  obtain ⟨C, hC0, hC⟩ := exists_productBump_top_modulus (d := d) β hβ
  refine ⟨C, hC0, ?_⟩
  intro h hh hh1 x₀ x y
  have hh0 : h ≠ 0 := ne_of_gt hh
  let u : Fin d → ℝ := h⁻¹ • (x - x₀)
  let v : Fin d → ℝ := h⁻¹ • (y - x₀)
  have hdist : ‖u - v‖ = ‖x - y‖ / h := by
    have heq : u - v = h⁻¹ • (x - y) := by
      dsimp [u, v]
      rw [← smul_sub]
      congr 1
      abel
    rw [heq, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hh]
    exact inv_mul_eq_div _ _
  have hcancel : h ^ β * (h⁻¹) ^ m * (‖x - y‖ / h) ^ s = ‖x - y‖ ^ s := by
    rw [Real.div_rpow (norm_nonneg _) hh.le, div_eq_mul_inv]
    have hp : h ^ β * (h⁻¹) ^ m * (h ^ s)⁻¹ = 1 := by
      rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg hh.le,
        ← Real.rpow_neg hh.le, ← Real.rpow_add hh, ← Real.rpow_add hh]
      have hexp : β + -(m : ℝ) + -s = 0 := by dsimp [s]; ring
      rw [hexp, Real.rpow_zero]
    calc
      h ^ β * (h⁻¹) ^ m * (‖x - y‖ ^ s * (h ^ s)⁻¹) =
          (h ^ β * (h⁻¹) ^ m * (h ^ s)⁻¹) * ‖x - y‖ ^ s := by ring
      _ = ‖x - y‖ ^ s := by rw [hp, one_mul]
  rw [scaledProductBump_iteratedFDeriv, scaledProductBump_iteratedFDeriv]
  rw [← smul_sub, ← smul_sub, norm_smul, norm_smul, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_pow, abs_inv, abs_of_pos hh,
    abs_of_nonneg (Real.rpow_nonneg hh.le β)]
  have htop := hC u v
  change ‖iteratedFDeriv ℝ m (productBump (d := d)) u -
    iteratedFDeriv ℝ m (productBump (d := d)) v‖ ≤ C * ‖u - v‖ ^ s at htop
  change h ^ β * ((h⁻¹) ^ m *
    ‖iteratedFDeriv ℝ m (productBump (d := d)) u -
      iteratedFDeriv ℝ m (productBump (d := d)) v‖) ≤ C * ‖x - y‖ ^ s
  calc
    _ ≤ h ^ β * ((h⁻¹) ^ m * (C * ‖u - v‖ ^ s)) := by
      gcongr
    _ = C * ‖x - y‖ ^ s := by rw [hdist]; rw [← hcancel]; ring


/-- In [a finite dimension and derivative order](hyp:d,j), when [a response](hyp:u)
[is globally smooth](hyp:hu), [a requested coordinate direction list](hyp:f) at
[a point in the unit cube](hyp:x,hx) has [an intrinsic coordinate jet equal to
the ambient iterated derivative](goal). -/
theorem coordJetOn_unitCube_eq_ambient {d j : ℕ}
    {u : (Fin d → ℝ) → ℝ}
    (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u)
    (f : Fin j → Fin d) (x : Fin d → ℝ) (hx : x ∈ unitCube d) :
    coordJetOn (unitCube d) j u f x =
      iteratedFDeriv ℝ j u x (fun k => Pi.single (f k) (1 : ℝ)) := by
  have huniq : UniqueDiffOn ℝ (unitCube d) := by
    unfold unitCube
    exact UniqueDiffOn.pi (fun _ _ => uniqueDiffOn_Icc (by norm_num))
  unfold coordJetOn
  rw [iteratedFDerivWithin_eq_iteratedFDeriv huniq
    (hu.contDiffAt.of_le (by exact_mod_cast le_top)) hx]

/-- In [a finite dimension, derivative order, exponent, and radius](hyp:d,m,s,R),
when [a response](hyp:u) is [globally smooth](hyp:hu), has
[uniform derivative bounds](hyp:hbound), and has
[a top-derivative Hölder modulus](hyp:hmod), [it belongs to the same-radius
intrinsic Hölder ball on the unit cube](goal). -/
theorem holderBallOn_unitCube_of_ambient_bounds {d m : ℕ} {s R : ℝ}
    {u : (Fin d → ℝ) → ℝ}
    (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u)
    (hbound : ∀ j ≤ m, ∀ x : Fin d → ℝ,
      ‖iteratedFDeriv ℝ j u x‖ ≤ R)
    (hmod : ∀ x y : Fin d → ℝ,
      ‖iteratedFDeriv ℝ m u x - iteratedFDeriv ℝ m u y‖ ≤
        R * ‖x - y‖ ^ s) :
    HolderBallOn (unitCube d) m s R u := by
  have hcoord (j : ℕ) (f : Fin j → Fin d) :
      ‖(fun k => Pi.single (f k) (1 : ℝ) : Fin j → (Fin d → ℝ))‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num)).2
    intro k
    simp [Pi.norm_single]
  refine ⟨hu.contDiffOn.of_le (by exact_mod_cast le_top), ?_, ?_⟩
  · intro j hj f x hx
    rw [coordJetOn_unitCube_eq_ambient hu f x hx, ← Real.norm_eq_abs]
    exact (ContinuousMultilinearMap.unit_le_opNorm _ (hcoord j f)).trans
      (hbound j hj x)
  · intro f x hx y hy
    rw [coordJetOn_unitCube_eq_ambient hu f x hx,
      coordJetOn_unitCube_eq_ambient hu f y hy, ← Real.norm_eq_abs]
    have heval :
        iteratedFDeriv ℝ m u x (fun k => Pi.single (f k) (1 : ℝ)) -
          iteratedFDeriv ℝ m u y (fun k => Pi.single (f k) (1 : ℝ)) =
          (iteratedFDeriv ℝ m u x - iteratedFDeriv ℝ m u y)
            (fun k => Pi.single (f k) (1 : ℝ)) := rfl
    rw [heval]
    exact (ContinuousMultilinearMap.unit_le_opNorm _ (hcoord m f)).trans
      (hmod x y)

/-- In [a finite dimension, derivative order, exponent, and nonnegative radius]
(hyp:d,m,s,R), [the radius is nonnegative](hyp:_hR), and [a response](hyp:u) [belongs](hyp:hu) to the intrinsic unit-cube
Hölder ball with that radius and [a baseline and amplitude](hyp:b,amp) are
chosen, [the affine response belongs to the stated enlarged Hölder ball](goal). -/
theorem holderBallOn_unitCube_add_const_mul {d m : ℕ} {s R : ℝ}
    {u : (Fin d → ℝ) → ℝ} (_hR : 0 ≤ R)
    (hu : HolderBallOn (unitCube d) m s R u) (b amp : ℝ) :
    HolderBallOn (unitCube d) m s (|b| + |amp| * R)
      (fun x => b + amp * u x) := by
  have huniq : UniqueDiffOn ℝ (unitCube d) := by
    unfold unitCube
    exact UniqueDiffOn.pi (fun _ _ => uniqueDiffOn_Icc (by norm_num))
  have hjet (j : ℕ) (hj : j ≤ m) (f : Fin j → Fin d)
      (x : Fin d → ℝ) (hx : x ∈ unitCube d) :
      coordJetOn (unitCube d) j (fun z => b + amp * u z) f x =
        (if j = 0 then b else 0) + amp * coordJetOn (unitCube d) j u f x := by
    have hreg : ContDiffWithinAt ℝ j u (unitCube d) x :=
      (hu.regularity x hx).of_le (by exact_mod_cast hj)
    unfold coordJetOn
    change iteratedFDerivWithin ℝ j
      ((fun _ : Fin d → ℝ => b) + (fun y => amp • u y)) (unitCube d) x _ = _
    rw [iteratedFDerivWithin_add_apply contDiffWithinAt_const
      (hreg.const_smul amp) huniq hx]
    change ((iteratedFDerivWithin ℝ j (fun _ : Fin d → ℝ => b) (unitCube d) x +
      iteratedFDerivWithin ℝ j (amp • u) (unitCube d) x) _) = _
    rw [iteratedFDerivWithin_const_smul_apply hreg huniq hx]
    simp only [add_apply, smul_apply, smul_eq_mul]
    by_cases hj0 : j = 0
    · subst j
      simp [iteratedFDerivWithin_zero_apply]
    · rw [iteratedFDerivWithin_const_of_ne hj0]
      simp [hj0]
  have hregularity : ContDiffOn ℝ m (fun x => b + amp * u x) (unitCube d) := by
    have hc : ContDiffOn ℝ m (fun _ : Fin d → ℝ => b) (unitCube d) := contDiffOn_const
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
      hc.add (ContDiffOn.const_smul amp hu.regularity)
  refine ⟨hregularity, ?_, ?_⟩
  · intro j hj f x hx
    rw [hjet j hj f x hx]
    have hc : |if j = 0 then b else 0| ≤ |b| := by
      split_ifs <;> simp
    calc
      |(if j = 0 then b else 0) + amp * coordJetOn (unitCube d) j u f x| ≤
          |if j = 0 then b else 0| + |amp * coordJetOn (unitCube d) j u f x| :=
        abs_add_le _ _
      _ ≤ |b| + |amp| * R := by
        rw [abs_mul]
        gcongr
        exact hu.derivBound j hj f x hx
  · intro f x hx y hy
    rw [hjet m le_rfl f x hx, hjet m le_rfl f y hy]
    have heq : (if m = 0 then b else 0) + amp * coordJetOn (unitCube d) m u f x -
        ((if m = 0 then b else 0) + amp * coordJetOn (unitCube d) m u f y) =
        amp * (coordJetOn (unitCube d) m u f x - coordJetOn (unitCube d) m u f y) := by
      ring
    rw [heq, abs_mul]
    calc
      |amp| * |coordJetOn (unitCube d) m u f x - coordJetOn (unitCube d) m u f y| ≤
          |amp| * (R * ‖x - y‖ ^ s) :=
        mul_le_mul_of_nonneg_left (hu.modulus f x hx y hy) (abs_nonneg amp)
      _ = (|amp| * R) * ‖x - y‖ ^ s := by ring
      _ ≤ (|b| + |amp| * R) * ‖x - y‖ ^ s :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (abs_nonneg b))
          (Real.rpow_nonneg (norm_nonneg _) _)

/-- In [a finite dimension](hyp:d), for
[a positive smoothness exponent](hyp:β,hβ), [a positive Hölder radius
independent of bandwidth and center controls every admissible scaled product
bump on the unit cube](goal). -/
theorem exists_uniform_scaledProductBump_holderBallOn {d : ℕ}
    (β : ℝ) (hβ : 0 < β) :
    let m := ⌈β⌉₊ - 1
    let s := β - (m : ℝ)
    ∃ A : ℝ, 0 < A ∧ ∀ (h : ℝ), 0 < h → h ≤ 1 →
      ∀ x₀ : Fin d → ℝ,
      HolderBallOn (unitCube d) m s A (scaledProductBump β h x₀) := by
  obtain ⟨D, _hD0, hD⟩ := exists_scaledProductBump_deriv_bound (d := d) β hβ
  obtain ⟨M, _hM0, hM⟩ := exists_scaledProductBump_top_modulus (d := d) β hβ
  let A := max 1 (max D M)
  have hDA : D ≤ A := (le_max_left D M).trans (le_max_right 1 (max D M))
  have hMA : M ≤ A := (le_max_right D M).trans (le_max_right 1 (max D M))
  refine ⟨A, lt_of_lt_of_le (by norm_num) (le_max_left 1 (max D M)), ?_⟩
  intro h hh hh1 x₀
  apply holderBallOn_unitCube_of_ambient_bounds (scaledProductBump_contDiff β h x₀)
  · intro j hj x
    exact (hD h hh hh1 x₀ j hj x).trans hDA
  · intro x y
    exact (hM h hh hh1 x₀ x y).trans
      (mul_le_mul_of_nonneg_right hMA (Real.rpow_nonneg (norm_nonneg _) _))

/-- In [a finite dimension](hyp:d), for
[a positive smoothness exponent](hyp:β,hβ), [a positive radius constant yields
the stated intrinsic unit-cube Hölder-ball guarantee for every baseline,
amplitude, bandwidth, and center](goal). -/
theorem exists_scaledProductBump_holderBallOn {d : ℕ}
    (β : ℝ) (hβ : 0 < β) :
    let m := ⌈β⌉₊ - 1
    let s := β - (m : ℝ)
    ∃ A : ℝ, 0 < A ∧ ∀ (b amp h : ℝ), 0 < h → h ≤ 1 →
      ∀ x₀ : Fin d → ℝ,
      HolderBallOn (unitCube d) m s (|b| + |amp| * A)
        (fun x => b + amp * h ^ β *
          productBump (fun i => (x i - x₀ i) / h)) := by
  obtain ⟨A, hA, hball⟩ := exists_uniform_scaledProductBump_holderBallOn (d := d) β hβ
  refine ⟨A, hA, ?_⟩
  intro b amp h hh hh1 x₀
  have hscaled := holderBallOn_unitCube_add_const_mul hA.le
    (hball h hh hh1 x₀) b amp
  simpa only [scaledProductBump_eq_coordinate_div β (ne_of_gt hh), mul_assoc] using hscaled

end Causalean.Mathlib.Analysis.Calculus.CubeExtension
