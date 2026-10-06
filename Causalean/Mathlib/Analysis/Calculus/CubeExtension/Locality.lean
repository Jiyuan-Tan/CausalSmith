module
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Normed.Operator.NNNorm

/-!
# Separated supports and finite signed-sum locality

The separation interface uses arbitrary closed support sets at a positive scale.
The jet interface explicitly requires value, first-jet, and second-jet vanishing
off those sets. Finite signed sums reduce to one summand at each point; constants
never count the number of indices. This module is independent of the profiles.
-/

@[expose] public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]

/-- [Scale separation for a family of supports, bandwidth, and separation factor](hyp:K,h,δ)
requires [closed supports](hyp:closed)
and [distance at least δh between points in distinct supports](hyp:separated). -/
structure SupportSeparation (K : ι → Set E) (h δ : ℝ) : Prop where
  closed : ∀ i, IsClosed (K i)
  separated : ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j, δ * h ≤ ‖x - y‖

/-- [Jet locality for a function family and its supports](hyp:f,K) means
[values, first jets, and second jets vanish off each support](hyp:value,first,second). -/
structure JetLocality (f : ι → E → ℝ) (K : ι → Set E) : Prop where
  value : ∀ i x, x ∉ K i → f i x = 0
  first : ∀ i x, x ∉ K i → fderiv ℝ (f i) x = 0
  second : ∀ i x, x ∉ K i → fderiv ℝ (fderiv ℝ (f i)) x = 0

/-- For [coefficients](hyp:σ) and [a finite scalar family](hyp:f), [the signed sum](goal)
at [a point](hyp:x) is [the finite sum of coefficient times function values](step:1). -/
noncomputable def signedSum (σ : ι → ℝ) (f : ι → E → ℝ) (x : E) : ℝ :=
  ∑ i, σ i * f i x

omit [Fintype ι] in
/-- Under [scale separation](hyp:hsep) with [positive scale and factor](hyp:hh,hδ),
if [a point x lies in the support K_i](hyp:hi) and [in the support
K_j](hyp:hj), then [i = j](goal): a point lies in at most one support. -/
theorem SupportSeparation.unique {K : ι → Set E} {h δ : ℝ}
    (hsep : SupportSeparation K h δ) (hh : 0 < h) (hδ : 0 < δ)
    {i j : ι} {x : E} (hi : x ∈ K i) (hj : x ∈ K j) : i = j := by
  by_contra hij
  have h := hsep.separated i j hij x hi x hj
  have hp := mul_pos hδ hh
  simp only [sub_self, norm_zero] at h
  exact (not_le_of_gt hp) h

/-- [A finite signed sum is globally twice continuously differentiable](goal)
when [each summand is globally twice continuously differentiable](hyp:hf),
for [any coefficients](hyp:σ) and [family](hyp:f). -/
theorem signedSum_contDiff (σ : ι → ℝ) (f : ι → E → ℝ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) : ContDiff ℝ 2 (signedSum σ f) := by
  classical
  unfold signedSum
  exact ContDiff.sum fun i _ => by
    simpa only [smul_eq_mul] using (hf i).const_smul (σ i)

/-- For [globally order-two summands](hyp:hf) and [any coefficients](hyp:σ),
[the first derivative of the signed sum is the signed sum of derivatives](goal)
at [every point](hyp:x). -/
theorem signedSum_fderiv (σ : ι → ℝ) (f : ι → E → ℝ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (x : E) :
    fderiv ℝ (signedSum σ f) x = ∑ i, σ i • fderiv ℝ (f i) x := by
  classical
  unfold signedSum
  rw [fderiv_fun_sum (fun i _ =>
    ((hf i).differentiable (by norm_num) x).const_mul (σ i))]
  exact Finset.sum_congr rfl fun i _ =>
    fderiv_const_mul ((hf i).differentiable (by norm_num) x) (σ i)

/-- For [globally order-two summands](hyp:hf) and [any coefficients](hyp:σ),
[the second derivative of the signed sum is the signed sum of second derivatives](goal)
at [every point](hyp:x). -/
theorem signedSum_second_fderiv (σ : ι → ℝ) (f : ι → E → ℝ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (x : E) :
    fderiv ℝ (fderiv ℝ (signedSum σ f)) x =
      ∑ i, σ i • fderiv ℝ (fderiv ℝ (f i)) x := by
  classical
  have hd : ∀ i, Differentiable ℝ (fderiv ℝ (f i)) := fun i =>
    ((hf i).fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable_one
  have heq : fderiv ℝ (signedSum σ f) =
      fun y => ∑ i, σ i • fderiv ℝ (f i) y :=
    funext (signedSum_fderiv σ f hf)
  rw [heq, fderiv_fun_sum (u := Finset.univ)
    (A := fun i y => σ i • fderiv ℝ (f i) y)
    (fun i _ => (hd i x).const_smul (σ i))]
  exact Finset.sum_congr rfl fun i _ => fderiv_fun_const_smul (hd i x) (σ i)

/-- For [a separated family](hyp:hsep) at [positive scale and factor](hyp:hh,hδ)
with [jet locality](hyp:hloc), [all signed-sum jets reduce to the unique contributing
summand](goal) at [a point in a support](hyp:hx), assuming [global order-two
regularity](hyp:hf) and [any coefficients](hyp:σ). -/
theorem signedSum_jets_eq {K : ι → Set E} {h δ : ℝ} {f : ι → E → ℝ}
    (hsep : SupportSeparation K h δ) (hh : 0 < h) (hδ : 0 < δ)
    (hloc : JetLocality f K) (hf : ∀ i, ContDiff ℝ 2 (f i))
    (σ : ι → ℝ) (i : ι) (x : E) (hx : x ∈ K i) :
    signedSum σ f x = σ i * f i x ∧
      fderiv ℝ (signedSum σ f) x = σ i • fderiv ℝ (f i) x ∧
      fderiv ℝ (fderiv ℝ (signedSum σ f)) x =
        σ i • fderiv ℝ (fderiv ℝ (f i)) x := by
  classical
  have hoff : ∀ j, j ≠ i → x ∉ K j := by
    intro j hji hj
    exact hji (hsep.unique hh hδ hj hx)
  refine ⟨?_, ?_, ?_⟩
  · unfold signedSum
    exact Finset.sum_eq_single i
      (fun j _ hji => by rw [hloc.value j x (hoff j hji), mul_zero])
      (fun hi => (hi (Finset.mem_univ i)).elim)
  · rw [signedSum_fderiv σ f hf x]
    exact Finset.sum_eq_single i
      (fun j _ hji => by rw [hloc.first j x (hoff j hji), smul_zero])
      (fun hi => (hi (Finset.mem_univ i)).elim)
  · rw [signedSum_second_fderiv σ f hf x]
    exact Finset.sum_eq_single i
      (fun j _ hji => by rw [hloc.second j x (hoff j hji), smul_zero])
      (fun hi => (hi (Finset.mem_univ i)).elim)

/-- For [a family with jet locality](hyp:hloc) and [global order-two regularity](hyp:hf),
[all signed-sum jets vanish](goal) at [a point outside every support](hyp:hx)
for [any coefficients](hyp:σ). -/
theorem signedSum_jets_zero {K : ι → Set E} {f : ι → E → ℝ}
    (hloc : JetLocality f K) (hf : ∀ i, ContDiff ℝ 2 (f i))
    (σ : ι → ℝ) (x : E) (hx : ∀ i, x ∉ K i) :
    signedSum σ f x = 0 ∧ fderiv ℝ (signedSum σ f) x = 0 ∧
      fderiv ℝ (fderiv ℝ (signedSum σ f)) x = 0 := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · simp only [signedSum, hloc.value _ _ (hx _), mul_zero, Finset.sum_const_zero]
  · rw [signedSum_fderiv σ f hf x]
    simp only [hloc.first _ _ (hx _), smul_zero, Finset.sum_const_zero]
  · rw [signedSum_second_fderiv σ f hf x]
    simp only [hloc.second _ _ (hx _), smul_zero, Finset.sum_const_zero]

/-- At [a point in one support](hyp:hx) and [a point outside that support](hyp:hy),
[subtracting signed sums splits into that summand's difference and the remaining
signed sum at the second point](goal), under [separation](hyp:hsep),
[positive scale and factor](hyp:hh,hδ), [jet locality](hyp:hloc), and
[global order-two regularity](hyp:hf).

This identity is useful for two-point proofs: if y is outside every support the
remaining sum is zero; if y is in another support scale separation applies. -/
theorem signedSum_sub_outside {K : ι → Set E} {h δ : ℝ} {f : ι → E → ℝ}
    (hsep : SupportSeparation K h δ) (hh : 0 < h) (hδ : 0 < δ)
    (hloc : JetLocality f K) (hf : ∀ i, ContDiff ℝ 2 (f i))
    (σ : ι → ℝ) (i : ι) (x y : E) (hx : x ∈ K i) (hy : y ∉ K i) :
    signedSum σ f x - signedSum σ f y =
      σ i * (f i x - f i y) - signedSum σ f y := by
  rw [(signedSum_jets_eq hsep hh hδ hloc hf σ i x hx).1,
    hloc.value i y hy, sub_zero]

end Causalean.Mathlib.Analysis.Calculus.CubeExtension
