module
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Interior line segments in a fixed cube

The segment from an interior cube point to a closed cube point remains interior
before its final endpoint. Along that open part, ordinary line derivatives agree
with diagonal Fréchet derivatives of the original function.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- Every point before the final endpoint of a segment from an interior cube
point to a closed cube point remains in the open cube. -/
theorem segment_mem_openCube {d : ℕ} {x y : Fin d → ℝ}
    (hx : x ∈ openCube d) (hy : y ∈ cube d)
    {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    x + t • (y - x) ∈ openCube d := by
  rcases ht with ⟨ht0, ht1⟩
  intro i hi
  have hxi := hx i (Set.mem_univ i)
  have hyi := hy i
  dsimp [openCube] at hxi
  dsimp at hxi hyi ⊢
  constructor
  · have h₁ : 0 < (1 - t) * (x i + 1) := mul_pos (by linarith) (by linarith [hxi.1])
    have h₂ : 0 ≤ t * (y i + 1) := mul_nonneg ht0 (by linarith [hyi.1])
    nlinarith
  · have h₁ : 0 < (1 - t) * (1 - x i) := mul_pos (by linarith) (by linarith [hxi.2])
    have h₂ : 0 ≤ t * (1 - y i) := mul_nonneg ht0 (by linarith [hyi.2])
    nlinarith

/-- For [a function that is m times continuously differentiable on the closed normalized
cube](hyp:hu), [a starting point x in the open cube](hyp:hx), [an end point y in the closed
cube](hyp:hy), [a time t in the half-open unit interval](hyp:ht), and [an order k](hyp:k) [at most
m](hyp:hk), [the k-th derivative at time t of the function restricted to the segment from x to y
equals the order-k derivative of the function at the point x + t (y − x), taken k times in the
direction y − x](goal). -/
theorem segment_iteratedDeriv_eq_diagonal {d m : ℕ}
    {u : (Fin d → ℝ) → ℝ} (hu : ContDiffOn ℝ m u (cube d))
    {x y : Fin d → ℝ} (hx : x ∈ openCube d) (hy : y ∈ cube d)
    {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1)
    (k : ℕ) (hk : k ≤ m) :
    iteratedDeriv k (fun r : ℝ => u (x + r • (y - x))) t =
      iteratedFDeriv ℝ k u (x + t • (y - x)) (fun _ => y - x) := by
  let v : ℝ →L[ℝ] (Fin d → ℝ) :=
    (1 : ℝ →L[ℝ] ℝ).smulRight (y - x)
  let S : Set (Fin d → ℝ) := {z | x + z ∈ openCube d}
  have ho : IsOpen (openCube d) :=
    isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)
  have hsub : openCube d ⊆ cube d := by
    intro z hz i
    exact ⟨le_of_lt (hz i (Set.mem_univ i)).1,
      le_of_lt (hz i (Set.mem_univ i)).2⟩
  have hS : IsOpen S := ho.preimage (continuous_const.add continuous_id)
  have hf : ContDiffOn ℝ m (fun z : Fin d → ℝ => u (x + z)) S := by
    apply hS.contDiffOn_iff.mpr
    intro z hz
    exact ((hu.mono hsub).contDiffAt (ho.mem_nhds hz)).comp z
      ((contDiff_const.add contDiff_id).contDiffAt)
  have hvt : v t ∈ S := by
    simpa [S, v, ContinuousLinearMap.smulRight_apply] using
      (segment_mem_openCube hx hy ht)
  have hpre : IsOpen (v ⁻¹' S) := hS.preimage v.continuous
  have hcomp := v.iteratedFDerivWithin_comp_right hf hS.uniqueDiffOn
    hpre.uniqueDiffOn hvt (show (k : WithTop ℕ∞) ≤ m from mod_cast hk)
  have hfun : (fun r : ℝ => u (x + r • (y - x))) =
      (fun z : Fin d → ℝ => u (x + z)) ∘ v := by
    funext r
    simp [v, ContinuousLinearMap.smulRight_apply]
  rw [hfun]
  rw [iteratedDeriv_eq_iteratedFDeriv]
  rw [← iteratedFDerivWithin_of_isOpen k hpre hvt,
    hcomp, iteratedFDerivWithin_of_isOpen k hS hvt]
  rw [iteratedFDeriv_comp_add_left]
  simp [v, ContinuousMultilinearMap.compContinuousLinearMap_apply]

end Causalean.Mathlib.Analysis.Calculus.CubeInterpolation
