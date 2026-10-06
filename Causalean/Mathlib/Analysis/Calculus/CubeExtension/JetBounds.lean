module
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Real bounds for scalar jets through order two

This independent module packages ordinary ambient value, derivative, and Hessian
bounds. Compact support and order-two regularity imply such bounds. Mean-value
and elementary power interpolation yield single-function Hölder estimates.
-/

@[expose] public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- At [a point](hyp:x) where [a scalar function is zero on a neighborhood](hyp:hf),
[its value and both ambient jets vanish](goal), without a differentiability hypothesis. -/
theorem jets_zero_of_eventually_zero {f : E → ℝ} (x : E)
    (hf : ∀ᶠ y in nhds x, f y = 0) :
    f x = 0 ∧ fderiv ℝ f x = 0 ∧ fderiv ℝ (fderiv ℝ f) x = 0 := by
  have h0 : f =ᶠ[nhds x] (fun _ => (0 : ℝ)) := hf
  refine ⟨h0.eq_of_nhds, ?_, ?_⟩
  · simpa using h0.fderiv_eq (𝕜 := ℝ)
  · simpa using (h0.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)

/-- [Uniform order-two jet data for a scalar function with a common bound](hyp:f,C)
consist of [a nonnegative bound](hyp:nonneg),
[global order-two regularity](hyp:regularity), and [bounds for its value,
first derivative, and second derivative](hyp:value,first,second). -/
structure JetBounds (f : E → ℝ) (C : ℝ) : Prop where
  nonneg : 0 ≤ C
  regularity : ContDiff ℝ 2 f
  value : ∀ x, |f x| ≤ C
  first : ∀ x, ‖fderiv ℝ f x‖ ≤ C
  second : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C

/-- [Bandwidth-weighted jet data for an exponent, bandwidth, function, and constant](hyp:β,h,f,C)
consist of [a nonnegative bound](hyp:nonneg),
[global order-two regularity](hyp:regularity), and [bounds with powers
β, β-1, and β-2](hyp:value,first,second). -/
structure ScaledJetBounds (β h : ℝ) (f : E → ℝ) (C : ℝ) : Prop where
  nonneg : 0 ≤ C
  regularity : ContDiff ℝ 2 f
  value : ∀ x, |f x| ≤ C * h ^ β
  first : ∀ x, ‖fderiv ℝ f x‖ ≤ C * h ^ (β - 1)
  second : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C * h ^ (β - 2)

/-- [A globally twice continuously differentiable function](hyp:hf)
with [compact support](hyp:hc) admits [a finite common bound on all three jets](goal).

Continuity of the second derivative needs only C², not C³. Use compact
support of derivatives and `bounded_above_of_compact_support`, or use
`norm_iteratedFDeriv_fderiv` to translate the order-two multilinear bound. -/
theorem exists_jetBounds_of_compactSupport {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    ∃ C : ℝ, 1 ≤ C ∧ JetBounds f C := by
  have hdf : ContDiff ℝ 1 (fderiv ℝ f) :=
    (contDiff_succ_iff_fderiv.mp hf).2.2
  obtain ⟨C₀, h₀⟩ := hf.continuous.bounded_above_of_compact_support hc
  obtain ⟨C₁, h₁⟩ := hdf.continuous.bounded_above_of_compact_support (hc.fderiv ℝ)
  obtain ⟨C₂, h₂⟩ := (hdf.continuous_fderiv (by norm_num)).bounded_above_of_compact_support
    ((hc.fderiv ℝ).fderiv ℝ)
  refine ⟨max 1 (max C₀ (max C₁ C₂)), le_max_left _ _, ?_⟩
  have hC₀ : C₀ ≤ max 1 (max C₀ (max C₁ C₂)) :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hC₁ : C₁ ≤ max 1 (max C₀ (max C₁ C₂)) :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hC₂ : C₂ ≤ max 1 (max C₀ (max C₁ C₂)) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨(by positivity), hf, ?_, fun x => (h₁ x).trans hC₁,
    fun x => (h₂ x).trans hC₂⟩
  intro x
  simpa only [Real.norm_eq_abs] using (h₀ x).trans hC₀

/-- [Scaled first-jet bounds](hyp:hf) imply [a global scalar Lipschitz estimate](goal)
for [the exponent and bandwidth](hyp:β,h) at [any two points](hyp:x,y). -/
theorem ScaledJetBounds.value_lipschitz {β h C : ℝ} {f : E → ℝ}
    (hf : ScaledJetBounds β h f C) (x y : E) :
    |f x - f y| ≤ C * h ^ (β - 1) * ‖x - y‖ := by
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z (_ : z ∈ Set.univ) => (hf.regularity.differentiable (by norm_num)) z)
      (fun z _ => hf.first z) convex_univ (Set.mem_univ y) (Set.mem_univ x)

/-- [Scaled second-jet bounds](hyp:hf) imply [a global derivative Lipschitz estimate](goal)
for [the exponent and bandwidth](hyp:β,h) at [any two points](hyp:x,y). -/
theorem ScaledJetBounds.first_lipschitz {β h C : ℝ} {f : E → ℝ}
    (hf : ScaledJetBounds β h f C) (x y : E) :
    ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ C * h ^ (β - 2) * ‖x - y‖ := by
  have hdf : ContDiff ℝ 1 (fderiv ℝ f) :=
    (contDiff_succ_iff_fderiv.mp hf.regularity).2.2
  exact Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z (_ : z ∈ Set.univ) => (hdf.differentiable (by norm_num)) z)
    (fun z _ => hf.second z) convex_univ (Set.mem_univ y) (Set.mem_univ x)

/-- [A nonnegative quantity](hyp:ha) bounded both by [a scaled supremum](hyp:hsup)
and [a scaled Lipschitz bound](hyp:hlip) has [the interpolated Hölder bound](goal)
when [the exponent s lies in `(0,1]`](hyp:hs,hs1), [the bandwidth is positive](hyp:hh),
and [the constant and distance are nonnegative](hyp:hC,hr).

Split at `r ≤ h`, use monotonicity of the nonpositive power `s - 1`,
and combine the powers of r.
This helper is valid at s=1 and r=0. -/
theorem scaled_min_holder {a C h r s : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hh : 0 < h) (hr : 0 ≤ r) (hs : 0 < s) (hs1 : s ≤ 1)
    (hsup : a ≤ 2 * C * h ^ s) (hlip : a ≤ C * h ^ (s - 1) * r) :
    a ≤ 2 * C * r ^ s := by
  by_cases hr0 : r = 0
  · subst r
    have ha0 : a = 0 := le_antisymm (by simpa only [mul_zero] using hlip) ha
    simp only [ha0, Real.zero_rpow hs.ne', mul_zero, le_refl]
  have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  by_cases hrh : r ≤ h
  · have hp : h ^ (s - 1) ≤ r ^ (s - 1) :=
      Real.rpow_le_rpow_of_nonpos hrpos hrh (by linarith)
    have heq : r ^ (s - 1) * r = r ^ s := by
      calc
        r ^ (s - 1) * r = r ^ (s - 1) * r ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = r ^ (s - 1 + 1) := (Real.rpow_add hrpos _ _).symm
        _ = r ^ s := by congr 1; ring
    calc
      a ≤ C * h ^ (s - 1) * r := hlip
      _ ≤ C * r ^ (s - 1) * r :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hC) hr
      _ = C * r ^ s := by rw [mul_assoc, heq]
      _ ≤ 2 * C * r ^ s := by
        have := Real.rpow_nonneg hr s
        nlinarith [mul_nonneg hC this]
  · exact hsup.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hh.le (le_of_not_ge hrh) hs.le) (by positivity))

/-- [Scaled jet bounds](hyp:hf) give [a bandwidth-independent scalar Hölder modulus](goal)
when [the exponent β lies in `(0,1]`](hyp:hβ,hβ1) and [the bandwidth is positive](hyp:hh). -/
theorem ScaledJetBounds.value_holder {β h C : ℝ} {f : E → ℝ}
    (hf : ScaledJetBounds β h f C) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hh : 0 < h) (x y : E) :
    |f x - f y| ≤ 2 * C * ‖x - y‖ ^ β := by
  apply scaled_min_holder (abs_nonneg _) hf.nonneg hh (norm_nonneg _) hβ hβ1
  · calc
      |f x - f y| ≤ |f x| + |f y| := by simpa only [Real.norm_eq_abs] using norm_sub_le (f x) (f y)
      _ ≤ 2 * C * h ^ β := by linarith [hf.value x, hf.value y]
  · exact hf.value_lipschitz x y

/-- [Scaled jet bounds](hyp:hf) give [a bandwidth-independent derivative Hölder modulus](goal)
when [the exponent β lies in `(1,2]`](hyp:hβ,hβ2) and [the bandwidth is positive](hyp:hh). -/
theorem ScaledJetBounds.first_holder {β h C : ℝ} {f : E → ℝ}
    (hf : ScaledJetBounds β h f C) (hβ : 1 < β) (hβ2 : β ≤ 2)
    (hh : 0 < h) (x y : E) :
    ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ 2 * C * ‖x - y‖ ^ (β - 1) := by
  apply scaled_min_holder (norm_nonneg _) hf.nonneg hh (norm_nonneg _)
    (by linarith : 0 < β - 1) (by linarith : β - 1 ≤ 1)
  · calc
      ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ ‖fderiv ℝ f x‖ + ‖fderiv ℝ f y‖ :=
        norm_sub_le _ _
      _ ≤ 2 * C * h ^ (β - 1) := by linarith [hf.first x, hf.first y]
  · simpa only [show β - 1 - 1 = β - 2 by ring] using hf.first_lipschitz x y

end Causalean.Mathlib.Analysis.Calculus.CubeExtension
