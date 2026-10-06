module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ReflectionFaceLimit
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ReflectionInterior
public import Mathlib.Analysis.Calculus.FDeriv.Extend

/-!
# First derivative at a reflected cube face

This module isolates the first differentiability step in gluing a finite
reflection sum to the original response. The derivative is taken within the
closed collar, so its value does not depend on the original response outside
the normalized cube.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

open Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- If [m ≥ 1](hyp:hm), [the reflection weights a satisfy the moment conditions
Σ_q a_q·(−(q + 1))^k = 1 for every k ≤ m](hyp:ha), [a response u is m times
continuously differentiable within the closed cube](hyp:hu), and [x is a cube
point](hyp:hx) [on the left face in coordinate i](hyp:hxi), then [the one-face
reflection of u has, within the closed left collar at x, derivative equal to the
within-cube derivative of u at x](goal). -/
theorem leftFaceReflection_hasFDerivWithinAt_face (d m : ℕ) (hm : 1 ≤ m)
    (i : Fin d) (a : Fin (m + 1) → ℝ)
    (ha : ∀ k : Fin (m + 1),
      (∑ q : Fin (m + 1),
        a q * (-((q.val : ℝ) + 1)) ^ (k.val : ℕ)) = 1)
    (u : (Fin d → ℝ) → ℝ) (hu : ContDiffOn ℝ m u (cube d))
    (x : Fin d → ℝ) (hx : x ∈ cube d) (hxi : x i = -1) :
    HasFDerivWithinAt (leftFaceReflection d m i a u)
      (fderivWithin ℝ u (cube d) x) (leftCubeCollar d m i) x := by
  classical
  let s := leftOpenCubeCollar d m i
  let c := leftCubeCollar d m i
  have hwidth : -1 - (1 : ℝ) / ((m : ℝ) + 1) < -1 := by
    have : 0 < (1 : ℝ) / ((m : ℝ) + 1) := by positivity
    linarith
  have hclosure : closure s =
      {z : Fin d → ℝ | ∀ j : Fin d,
        if j = i then z j ∈ Set.Icc (-1 - (1 : ℝ) / ((m : ℝ) + 1)) (-1)
        else z j ∈ Set.Icc (-1 : ℝ) 1} := by
    have hs : s = Set.univ.pi (fun j : Fin d =>
        if j = i then Set.Ioo (-1 - (1 : ℝ) / ((m : ℝ) + 1)) (-1)
        else Set.Ioo (-1 : ℝ) 1) := by
      ext z
      simp only [s, leftOpenCubeCollar, Set.mem_pi, Set.mem_univ, forall_true_left,
        Set.mem_ofPred_eq]
      constructor <;> intro hz j
      · specialize hz j
        split_ifs at hz ⊢ <;> exact hz
      · specialize hz j
        split_ifs at hz ⊢ <;> exact hz
    rw [hs, closure_pi_set]
    ext z
    simp only [Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_ofPred_eq]
    constructor <;> intro hz j
    · specialize hz j
      split_ifs at hz ⊢ with h
      · rw [closure_Ioo hwidth.ne] at hz
        exact hz
      · simpa [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)] using hz
    · specialize hz j
      split_ifs at hz ⊢ with h
      · rw [closure_Ioo hwidth.ne]
        exact hz
      · simpa [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)] using hz
  have hsopen : IsOpen s := by
    rw [show s = Set.univ.pi (fun j : Fin d =>
        if j = i then Set.Ioo (-1 - (1 : ℝ) / ((m : ℝ) + 1)) (-1)
        else Set.Ioo (-1 : ℝ) 1) from by
      ext z
      simp only [s, leftOpenCubeCollar, Set.mem_pi, Set.mem_univ, forall_true_left,
        Set.mem_ofPred_eq]
      constructor <;> intro hz j <;> specialize hz j <;>
        split_ifs at hz ⊢ <;> exact hz]
    apply isOpen_set_pi Set.finite_univ
    intro j hj
    split_ifs <;> exact isOpen_Ioo
  have hsconv : Convex ℝ s := by
    rw [show s = Set.univ.pi (fun j : Fin d =>
        if j = i then Set.Ioo (-1 - (1 : ℝ) / ((m : ℝ) + 1)) (-1)
        else Set.Ioo (-1 : ℝ) 1) from by
      ext z
      simp only [s, leftOpenCubeCollar, Set.mem_pi, Set.mem_univ, forall_true_left,
        Set.mem_ofPred_eq]
      constructor <;> intro hz j <;> specialize hz j <;>
        split_ifs at hz ⊢ <;> exact hz]
    apply convex_pi
    intro j hj
    split_ifs <;> exact convex_Ioo _ _
  have hclosedsub : closure s ⊆ c := by
    rw [hclosure]
    intro z hz j
    by_cases h : j = i
    · simp only [h, ↓reduceIte]
      have hj := hz j
      simp only [h, ↓reduceIte] at hj
      exact ⟨hj.1, hj.2.trans (by norm_num)⟩
    · simpa [h] using hz j
  have hcubeSub : cube d ⊆ c := by
    intro z hz j
    by_cases h : j = i
    · subst j
      simp only [↓reduceIte]
      have hnonneg : 0 ≤ (1 : ℝ) / ((m : ℝ) + 1) := by positivity
      exact ⟨by linarith [(hz i).1], (hz i).2⟩
    · simpa [h] using hz j
  have hcont : ContinuousOn (leftFaceReflection d m i a u) c := by
    apply leftFaceReflection_continuousOn d m i a
    · have hzero := ha (0 : Fin (m + 1))
      simpa using hzero
    · exact hu.continuousOn
  have hdiff : DifferentiableOn ℝ (leftFaceReflection d m i a u) s :=
    (leftFaceReflection_contDiffOn_openCollar d m i a u hu).differentiableOn
      (by exact_mod_cast (Nat.ne_of_gt hm))
  have hcubeUnique : UniqueDiffWithinAt ℝ (cube d) x := by
    have hpi : cube d = Set.univ.pi (fun _ : Fin d => Set.Icc (-1 : ℝ) 1) := by
      ext z
      simp [cube, Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube,
        Pi.le_def, forall_and]
    have hunique : UniqueDiffOn ℝ (cube d) := by
      rw [hpi]
      exact UniqueDiffOn.pi (fun _ _ => uniqueDiffOn_Icc (by norm_num))
    exact hunique x hx
  have hjet := leftFaceReflection_jet_tendsto_face d m i a ha u hu 1 hm x hx hxi
  have htend : Filter.Tendsto
      (fun z => fderiv ℝ (leftFaceReflection d m i a u) z)
      (nhdsWithin x s) (nhds (fderivWithin ℝ u (cube d) x)) := by
    let e := continuousMultilinearCurryFin1 ℝ (Fin d → ℝ) ℝ
    have he : e (iteratedFDerivWithin ℝ 1 u (cube d) x) =
        fderivWithin ℝ u (cube d) x := by
      ext v
      simpa [e, continuousMultilinearCurryFin1_apply] using
        (iteratedFDerivWithin_one_apply hcubeUnique (Fin.snoc 0 v))
    have h' := (e.continuous.tendsto _).comp hjet
    rw [he] at h'
    convert h' using 1
    funext z
    ext v
    simpa [e, continuousMultilinearCurryFin1_apply] using
      (iteratedFDeriv_one_apply (f := leftFaceReflection d m i a u) (x := z)
        (Fin.snoc 0 v))
  have hexterior : HasFDerivWithinAt (leftFaceReflection d m i a u)
      (fderivWithin ℝ u (cube d) x) (closure s) x := by
    apply hasFDerivWithinAt_closure_of_tendsto_fderiv hdiff hsconv hsopen
    · intro z hz
      exact (hcont z (hclosedsub hz)).mono (subset_closure.trans hclosedsub)
    · exact htend
  have hcube : HasFDerivWithinAt (leftFaceReflection d m i a u)
      (fderivWithin ℝ u (cube d) x) (cube d) x := by
    exact (hu.differentiableOn (by exact_mod_cast (Nat.ne_of_gt hm)) x hx).hasFDerivWithinAt.congr
      (leftFaceReflection_eqOn_cube d m i a u)
      (leftFaceReflection_eqOn_cube d m i a u hx)
  have hunion := hexterior.union hcube
  have hcEq : closure s ∪ cube d = c := by
    ext z
    constructor
    · rintro (hz | hz)
      · exact hclosedsub hz
      · exact hcubeSub hz
    · intro hz
      by_cases h : z i ≤ -1
      · left
        rw [hclosure]
        intro j
        by_cases hji : j = i
        · subst j
          have hj := hz i
          change (if i = i then z i ∈ Set.Icc (-1 - (1 : ℝ) / ((m : ℝ) + 1)) 1
            else z i ∈ Set.Icc (-1 : ℝ) 1) at hj
          simp only [↓reduceIte] at hj ⊢
          exact ⟨hj.1, h⟩
        · simpa [c, leftCubeCollar, hji] using hz j
      · right
        intro j
        by_cases hji : j = i
        · subst j
          have hj := hz i
          change (if i = i then z i ∈ Set.Icc (-1 - (1 : ℝ) / ((m : ℝ) + 1)) 1
            else z i ∈ Set.Icc (-1 : ℝ) 1) at hj
          simp only [↓reduceIte] at hj
          exact ⟨le_of_not_ge h, hj.2⟩
        · simpa [c, leftCubeCollar, hji] using hz j
  simpa only [hcEq, c] using hunion

end Causalean.Mathlib.Analysis.Calculus.CubeExtension
