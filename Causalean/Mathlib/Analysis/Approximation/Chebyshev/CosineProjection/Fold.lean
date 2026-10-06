module
public import Mathlib.Algebra.Order.ToIntervalMod
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# The even periodic extension of a unit-interval function

The fold `arccos(cos(t))/π` maps the line continuously into `[0,1]`, agrees
with `t/π` on `[0,π]`, and is even and 2π-periodic. Its global Lipschitz bound
is the independent geometric obligation behind Hölder extension; differentiating
arccos at ±1 would incorrectly exclude the endpoints.
-/

@[expose] public section

noncomputable section
namespace Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection

/-- [The folded unit-interval position](goal) of an [angle](hyp:t) is its
cosine's principal arccosine divided by π. -/
def fold (t : ℝ) : ℝ := Real.arccos (Real.cos t) / Real.pi

/-- [The even periodic extension](goal) of an [interval function](hyp:f)
at an [angle](hyp:t) evaluates that function at the folded position. -/
def evenExtension (f : ℝ → ℝ) (t : ℝ) : ℝ := f (fold t)

/-- The folded position at [every angle](hyp:t) [lies in the unit interval](goal). -/
theorem fold_mem (t : ℝ) : fold t ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact div_nonneg (Real.arccos_nonneg _) Real.pi_pos.le
  · exact (div_le_one Real.pi_pos).mpr (Real.arccos_le_pi _)

/-- [The angular fold is continuous](goal). -/
@[fun_prop]
theorem continuous_fold : Continuous fold := by
  exact (Real.continuous_arccos.comp Real.continuous_cos).div_const Real.pi

/-- The fold [recovers each unit-interval point](goal) after scaling by π,
for a [point in that interval](hyp:hx). -/
theorem fold_pi_mul {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    fold (Real.pi * x) = x := by
  unfold fold
  rw [Real.arccos_cos (mul_nonneg Real.pi_pos.le hx.1)
    (by nlinarith [Real.pi_pos, hx.2])]
  exact mul_div_cancel_left₀ x Real.pi_ne_zero

/-- [The angular fold is even](goal). -/
theorem fold_even : Function.Even fold := by
  intro t
  simp [fold]

/-- [The angular fold has period 2π](goal). -/
theorem fold_periodic : Function.Periodic fold (2 * Real.pi) := by
  intro t
  simp [fold, Real.cos_add_two_pi]

/-- On the centered principal interval, the angular fold before scaling is absolute value. -/
private theorem arccos_cos_eq_abs {x : ℝ} (hx : |x| ≤ Real.pi) :
    Real.arccos (Real.cos x) = |x| := by
  rw [← Real.cos_abs x]
  exact Real.arccos_cos (abs_nonneg x) hx

/-- The principal arccosine of a cosine never exceeds the absolute angle. -/
private theorem arccos_cos_le_abs (x : ℝ) : Real.arccos (Real.cos x) ≤ |x| := by
  by_cases hx : |x| ≤ Real.pi
  · exact (arccos_cos_eq_abs hx).le
  · exact (Real.arccos_le_pi _).trans (le_of_not_ge hx)

/-- Periodic reduction and the triangle inequality bound a one-sided angular increment. -/
private theorem arccos_cos_le_add (s t : ℝ) :
    Real.arccos (Real.cos s) ≤ Real.arccos (Real.cos t) + |s - t| := by
  let k : ℤ := toIcoDiv (show 0 < 2 * Real.pi by positivity) (-Real.pi) t
  have hk := sub_toIcoDiv_zsmul_mem_Ico
    (show 0 < 2 * Real.pi by positivity) (-Real.pi) t
  rw [zsmul_eq_mul] at hk
  change t - (k : ℝ) * (2 * Real.pi) ∈
    Set.Ico (-Real.pi) (-Real.pi + 2 * Real.pi) at hk
  have habs : |t - (k : ℝ) * (2 * Real.pi)| ≤ Real.pi := by
    rw [abs_le]
    constructor
    · exact hk.1
    · linarith [hk.2]
  calc
    Real.arccos (Real.cos s) =
        Real.arccos (Real.cos (s - (k : ℝ) * (2 * Real.pi))) := by
          rw [Real.cos_sub_int_mul_two_pi]
    _ ≤ |s - (k : ℝ) * (2 * Real.pi)| := arccos_cos_le_abs _
    _ = |(t - (k : ℝ) * (2 * Real.pi)) + (s - t)| := by congr 1; ring
    _ ≤ |t - (k : ℝ) * (2 * Real.pi)| + |s - t| := abs_add_le _ _
    _ = Real.arccos (Real.cos t) + |s - t| := by
      rw [← arccos_cos_eq_abs habs, Real.cos_sub_int_mul_two_pi]

/-- Folded positions at [two angles](hyp:s,t) have [distance at most angular
distance divided by π](goal).

Prove that `arccos ∘ cos` is the triangular wave with slopes ±1. One route
uses reduction modulo 2π followed by cases at π and at the wrap point. A route
through distance to the lattice 2πℤ uses the 1-Lipschitz distance-to-set lemma.
This is a genuine global inequality, including every cusp.
-/
theorem fold_lipschitz (s t : ℝ) : |fold s - fold t| ≤ |s - t| / Real.pi := by
  have h : |Real.arccos (Real.cos s) - Real.arccos (Real.cos t)| ≤ |s - t| := by
    rw [abs_le]
    have hst := arccos_cos_le_add s t
    have hts := arccos_cos_le_add t s
    rw [abs_sub_comm t s] at hts
    constructor <;> linarith
  simpa only [fold, ← sub_div, abs_div, abs_of_pos Real.pi_pos] using
    (div_le_div_of_nonneg_right h Real.pi_pos.le)

/-- A [function continuous on the closed unit interval](hyp:hf) has
[continuous even periodic extension on the real line](goal). -/
@[fun_prop]
theorem continuous_evenExtension {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1)) : Continuous (evenExtension f) := by
  exact hf.comp_continuous continuous_fold fold_mem

/-- [The folded extension of an interval function](hyp:f) is [even](goal). -/
theorem evenExtension_even (f : ℝ → ℝ) : Function.Even (evenExtension f) := by
  intro t
  exact congrArg f (fold_even t)

/-- [The folded extension of an interval function](hyp:f) has [period 2π](goal). -/
theorem evenExtension_periodic (f : ℝ → ℝ) :
    Function.Periodic (evenExtension f) (2 * Real.pi) := by
  intro t
  exact congrArg f (fold_periodic t)

/-- The even extension [recovers the original function](goal) at a π-scaled
[unit-interval point](hyp:hx), for an [interval function](hyp:f). -/
theorem evenExtension_pi_mul (f : ℝ → ℝ) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) : evenExtension f (Real.pi * x) = f x := by
  simp only [evenExtension, fold_pi_mul hx]

/-- A [unit-interval Hölder increment bound](hyp:hf) at a [positive
exponent](hyp:hγ) with a [nonnegative constant](hyp:hH) gives [the angular
increment bound, with distance divided by π, for its even extension](goal). -/
theorem evenExtension_holder {f : ℝ → ℝ} {γ H : ℝ}
    (hγ : 0 < γ) (hH : 0 ≤ H)
    (hf : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ z ∈ Set.Icc (0 : ℝ) 1,
      |f x - f z| ≤ H * |x - z| ^ γ) (s t : ℝ) :
    |evenExtension f s - evenExtension f t| ≤ H * (|s - t| / Real.pi) ^ γ := by
  exact (hf (fold s) (fold_mem s) (fold t) (fold_mem t)).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (abs_nonneg _) (fold_lipschitz s t) hγ.le) hH)

end Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection

