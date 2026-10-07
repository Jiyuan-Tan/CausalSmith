module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.JetBounds
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Generic translated and dilated order-two scalar jets

Amplitude scaling by a real bandwidth power, inverse dilation, and translation
have exact first, second, and iterated derivative identities. These identities
transfer uniform normalized jet bounds and off-support vanishing to scaled
copies without depending on a particular cutoff, plateau, or coordinate profile.
-/

@[expose] public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- For [a profile](hyp:f), [exponent and bandwidth](hyp:β,h), and
[a center](hyp:z), [the scaled copy](goal) at [a point](hyp:x) is
[the translated, inversely dilated profile multiplied by h to the exponent](step:1). -/
noncomputable def scaledCopy (β h : ℝ) (z : E) (f : E → ℝ) (x : E) : ℝ :=
  h ^ β * f (h⁻¹ • (x - z))

/-- [The scaled support](goal) of [a set](hyp:K) at [a bandwidth and center](hyp:h,z)
is [its inverse image under translation and inverse dilation](step:1). -/
def scaledSupport (h : ℝ) (z : E) (K : Set E) : Set E :=
  {x | h⁻¹ • (x - z) ∈ K}

/-- [A globally order-two profile](hyp:hf) has [globally order-two scaled copies](goal)
for [any exponent, bandwidth, and center](hyp:β,h,z). -/
theorem scaledCopy_contDiff (β h : ℝ) (z : E) {f : E → ℝ} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 2 (scaledCopy β h z f) := by
  unfold scaledCopy
  exact contDiff_const.mul (hf.comp (by fun_prop))

/-- For [an order-two profile](hyp:hf), [a jet order at most two](hyp:j,hj),
[an exponent, bandwidth, center, and point](hyp:β,h,z,x), [the iterated jet
scales by the amplitude and the inverse bandwidth to the jet order](goal).

Reuse `iteratedFDeriv_comp_sub`, `iteratedFDeriv_comp_const_smul`, and
`iteratedFDeriv_const_smul_apply'`, as in CubeExtension.ScaledProductBump.
Unlike that module, regularity is assumed only through order two. -/
-- Restrict hf to the finite natural order j using hj (casts into WithTop ℕ∞).
-- These Mathlib identities include j=0 and h=0; this theorem deliberately
-- imposes neither a positive bandwidth nor an infinite-order smoothness premise.
theorem scaledCopy_iteratedFDeriv (β h : ℝ) (z x : E) {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (j : ℕ) (hj : j ≤ 2) :
    iteratedFDeriv ℝ j (scaledCopy β h z f) x =
      (h ^ β) • ((h⁻¹) ^ j • iteratedFDeriv ℝ j f (h⁻¹ • (x - z))) := by
  have hfj : ContDiff ℝ (j : WithTop ℕ∞) f := hf.of_le (by exact_mod_cast hj)
  have hg : ContDiff ℝ (j : WithTop ℕ∞) (fun y : E => f (h⁻¹ • y)) :=
    hfj.comp (by fun_prop)
  have ht : ContDiff ℝ (j : WithTop ℕ∞) (fun y : E => f (h⁻¹ • (y - z))) :=
    hg.comp (by fun_prop)
  change iteratedFDeriv ℝ j (fun y : E => (h ^ β) • f (h⁻¹ • (y - z))) x = _
  rw [iteratedFDeriv_const_smul_apply' ht.contDiffAt]
  rw [iteratedFDeriv_comp_sub (f := fun y : E => f (h⁻¹ • y)) j z x]
  rw [iteratedFDeriv_comp_const_smul h⁻¹ hfj]

/-- For [a globally order-two profile](hyp:hf)
and [an exponent, bandwidth, center, and point](hyp:β,h,z,x), [the ambient first derivative
has the expected amplitude and inverse-bandwidth factor](goal). -/
theorem scaledCopy_fderiv (β h : ℝ) (z x : E) {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) :
    fderiv ℝ (scaledCopy β h z f) x =
      (h ^ β * h⁻¹) • fderiv ℝ f (h⁻¹ • (x - z)) := by
  have ht : ContDiff ℝ 2 (fun y : E => f (h⁻¹ • (y - z))) :=
    hf.comp (by fun_prop)
  change fderiv ℝ (fun y : E => (h ^ β) • f (h⁻¹ • (y - z))) x = _
  rw [fderiv_fun_const_smul (ht.differentiable (by norm_num) x)]
  rw [fderiv_comp_sub (f := fun y : E => f (h⁻¹ • y)) z, fderiv_comp_smul]
  rw [smul_smul]

/-- For [a globally order-two profile](hyp:hf)
and [an exponent, bandwidth, center, and point](hyp:β,h,z,x), [the ambient second derivative
has the expected amplitude and squared inverse-bandwidth factor](goal). -/
-- First prove scaledCopy_fderiv as an equality of functions (funext).
-- Differentiate that identity using C¹ regularity of fderiv f from hf.
-- Constant scalar dilation contributes another h⁻¹; no third derivative is needed.
theorem scaledCopy_second_fderiv (β h : ℝ) (z x : E) {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) :
    fderiv ℝ (fderiv ℝ (scaledCopy β h z f)) x =
      (h ^ β * (h⁻¹) ^ 2) • fderiv ℝ (fderiv ℝ f) (h⁻¹ • (x - z)) := by
  have heq : fderiv ℝ (scaledCopy β h z f) =
      fun y => (h ^ β * h⁻¹) • fderiv ℝ f (h⁻¹ • (y - z)) := by
    funext y
    exact scaledCopy_fderiv β h z y hf
  have hdf : ContDiff ℝ 1 (fderiv ℝ f) :=
    (contDiff_succ_iff_fderiv.mp hf).2.2
  have ht : ContDiff ℝ 1 (fun y : E => fderiv ℝ f (h⁻¹ • (y - z))) :=
    hdf.comp (by fun_prop)
  rw [heq, fderiv_fun_const_smul (ht.differentiable (by norm_num) x)]
  rw [fderiv_comp_sub (f := fun y : E => fderiv ℝ f (h⁻¹ • y)) z,
    fderiv_comp_smul, smul_smul]
  congr 1
  ring

/-- If [a profile is twice continuously differentiable on the whole space with its values, first
derivative, and second derivative all bounded in norm by a nonnegative constant C](hyp:hf), then
for [a positive bandwidth](hyp:hh) and [any exponent β, bandwidth h, and center](hyp:β,h,z), [the
scaled copy is twice continuously differentiable and its values, first derivative, and second
derivative are bounded everywhere by C times h to the powers β, β − 1, and β − 2
respectively](goal). -/
-- Use the two exact ambient derivative identities and norm_smul. Positivity
-- removes absolute values; `Real.rpow_sub hh`, `Real.rpow_one`, and
-- `Real.rpow_natCast` identify powers β-1 and β-2. Keep all real exponents.
theorem scaledCopy_jetBounds (β h : ℝ) (z : E) {f : E → ℝ} {C : ℝ}
    (hf : JetBounds f C) (hh : 0 < h) : ScaledJetBounds β h (scaledCopy β h z f) C := by
  have hp : 0 ≤ h ^ β := Real.rpow_nonneg hh.le β
  have h₁ : h ^ β * h⁻¹ = h ^ (β - 1) := by
    rw [Real.rpow_sub hh, Real.rpow_one, div_eq_mul_inv]
  have h₂ : h ^ β * (h⁻¹) ^ 2 = h ^ (β - 2) := by
    rw [Real.rpow_sub hh, Real.rpow_two, div_eq_mul_inv, inv_pow]
  refine ⟨hf.nonneg, scaledCopy_contDiff β h z hf.regularity, ?_, ?_, ?_⟩
  · intro x
    calc
      |scaledCopy β h z f x| = h ^ β * |f (h⁻¹ • (x - z))| := by
        rw [scaledCopy, abs_mul, abs_of_nonneg hp]
      _ ≤ h ^ β * C := mul_le_mul_of_nonneg_left (hf.value _) hp
      _ = C * h ^ β := mul_comm _ _
  · intro x
    rw [scaledCopy_fderiv β h z x hf.regularity, norm_smul, h₁,
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hh.le _)]
    calc
      h ^ (β - 1) * ‖fderiv ℝ f (h⁻¹ • (x - z))‖ ≤ h ^ (β - 1) * C :=
        mul_le_mul_of_nonneg_left (hf.first _) (Real.rpow_nonneg hh.le _)
      _ = C * h ^ (β - 1) := mul_comm _ _
  · intro x
    rw [scaledCopy_second_fderiv β h z x hf.regularity, norm_smul, h₂,
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hh.le _)]
    calc
      h ^ (β - 2) * ‖fderiv ℝ (fderiv ℝ f) (h⁻¹ • (x - z))‖ ≤ h ^ (β - 2) * C :=
        mul_le_mul_of_nonneg_left (hf.second _) (Real.rpow_nonneg hh.le _)
      _ = C * h ^ (β - 2) := mul_comm _ _

/-- If [a twice continuously differentiable profile](hyp:hf) has [value and
first two derivatives vanishing off a set K](hyp:hzero), then for [any exponent, bandwidth and
center](hyp:β,h,z), and [a point](hyp:x)
[outside the scaled support of K](hyp:hx), [the scaled copy and its first two
derivatives vanish at that point](goal). -/
theorem scaledCopy_jets_zero (β h : ℝ) (z : E) {f : E → ℝ} {K : Set E}
    (hf : ContDiff ℝ 2 f)
    (hzero : ∀ x ∉ K, f x = 0 ∧ fderiv ℝ f x = 0 ∧ fderiv ℝ (fderiv ℝ f) x = 0)
    (x : E) (hx : x ∉ scaledSupport h z K) :
    scaledCopy β h z f x = 0 ∧ fderiv ℝ (scaledCopy β h z f) x = 0 ∧
      fderiv ℝ (fderiv ℝ (scaledCopy β h z f)) x = 0 := by
  obtain ⟨hv, h₁, h₂⟩ := hzero (h⁻¹ • (x - z)) hx
  refine ⟨?_, ?_, ?_⟩
  · simp only [scaledCopy, hv, mul_zero]
  · rw [scaledCopy_fderiv β h z x hf, h₁, smul_zero]
  · rw [scaledCopy_second_fderiv β h z x hf, h₂, smul_zero]

end Causalean.Mathlib.Analysis.Calculus.CubeExtension
