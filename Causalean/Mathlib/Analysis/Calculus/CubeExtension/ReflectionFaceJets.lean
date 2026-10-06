module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ReflectionClosedExterior
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ReflectionFaceLimit

/-!
# Intrinsic jets of the reflected exterior at a face

The within-set jets of the closed exterior reflection agree with the
original cube jets on their common face, including edges and corners.
This is the trace identity needed before gluing the two closed pieces.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

open Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- If [the reflection weights a satisfy the moment conditions
Σ_q a_q·(−(q + 1))^k = 1 for every k ≤ m](hyp:ha), [a response u is m times
continuously differentiable within the closed cube](hyp:hu), [j ≤ m](hyp:hj),
and [x is a cube point](hyp:hx) [on the left face in coordinate i](hyp:hxi),
then [the order-j derivative of the one-face reflection of u within the closed
exterior slab at x equals the order-j within-cube derivative of u at x](goal).
This holds at edges and corners of the face as well as in its relative interior. -/
theorem leftFaceReflection_closedExterior_jet_eq_face (d m : ℕ) (i : Fin d)
    (a : Fin (m + 1) → ℝ)
    (ha : ∀ k : Fin (m + 1),
      (∑ q : Fin (m + 1),
        a q * (-((q.val : ℝ) + 1)) ^ (k.val : ℕ)) = 1)
    (u : (Fin d → ℝ) → ℝ) (hu : ContDiffOn ℝ m u (cube d))
    (j : ℕ) (hj : j ≤ m) (x : Fin d → ℝ)
    (hx : x ∈ cube d) (hxi : x i = -1) :
    iteratedFDerivWithin ℝ j (leftFaceReflection d m i a u)
      (leftClosedExteriorCollar d m i) x =
      iteratedFDerivWithin ℝ j u (cube d) x := by
  classical
  let s := leftOpenCubeCollar d m i
  let c := leftClosedExteriorCollar d m i
  have hwidth : -1 - (1 : ℝ) / ((m : ℝ) + 1) < -1 := by
    have : 0 < (1 : ℝ) / ((m : ℝ) + 1) := by positivity
    linarith
  have hs : s = Set.univ.pi (fun k : Fin d =>
      if k = i then Set.Ioo (-1 - (1 : ℝ) / ((m : ℝ) + 1)) (-1)
      else Set.Ioo (-1 : ℝ) 1) := by
    ext z
    simp only [s, leftOpenCubeCollar, Set.mem_pi, Set.mem_univ, forall_true_left,
      Set.mem_ofPred_eq]
    constructor <;> intro hz k <;> by_cases h : k = i <;>
      simpa [h] using hz k
  have hc : c = Set.univ.pi (fun k : Fin d =>
      if k = i then Set.Icc (-1 - (1 : ℝ) / ((m : ℝ) + 1)) (-1)
      else Set.Icc (-1 : ℝ) 1) := by
    ext z
    simp only [c, leftClosedExteriorCollar, leftCubeCollar, Set.mem_inter_iff,
      Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_true_left]
    constructor
    · rintro ⟨hz, hzi⟩ k
      by_cases h : k = i
      · subst k
        have hki := hz i
        simp only at hki ⊢
        exact ⟨hki.1, hzi⟩
      · simpa [h] using hz k
    · intro hz
      constructor
      · intro k
        by_cases h : k = i
        · subst k
          have hki := hz i
          simp only at hki ⊢
          exact ⟨hki.1, hki.2.trans (by norm_num)⟩
        · simpa [h] using hz k
      · have hki := hz i
        simp only at hki
        simpa using hki.2
  have hclosure : closure s = c := by
    rw [hs, closure_pi_set, hc]
    ext z
    simp only [Set.mem_pi, Set.mem_univ, forall_true_left]
    constructor <;> intro hz k <;> specialize hz k <;>
      split_ifs at hz ⊢ with h
    · rw [closure_Ioo hwidth.ne] at hz
      exact hz
    · rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)] at hz
      exact hz
    · rw [closure_Ioo hwidth.ne]
      exact hz
    · rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]
      exact hz
  have hsopen : IsOpen s := by
    rw [hs]
    apply isOpen_set_pi Set.finite_univ
    intro k hk
    split_ifs <;> exact isOpen_Ioo
  have hcunique : UniqueDiffOn ℝ c := by
    rw [hc]
    apply UniqueDiffOn.pi
    intro k hk
    split_ifs
    · exact uniqueDiffOn_Icc hwidth
    · exact uniqueDiffOn_Icc (by norm_num : (-1 : ℝ) < 1)
  have hxc : x ∈ c := by
    rw [hc]
    intro k hk
    by_cases h : k = i
    · subst k
      simp only [↓reduceIte]
      have hnonneg : 0 ≤ (1 : ℝ) / ((m : ℝ) + 1) := by positivity
      exact ⟨by linarith [hxi], le_of_eq hxi⟩
    · simpa [h] using hx k
  letI : (nhdsWithin x s).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp (by rw [hclosure]; exact hxc)
  have hs_sub : s ⊆ c := by
    rw [← hclosure]
    exact subset_closure
  have hzero : (∑ q : Fin (m + 1), a q) = 1 := by
    simpa using ha (0 : Fin (m + 1))
  have hreg := leftFaceReflection_contDiffOn_closedExterior d m i a hzero u hu
  have hcont : ContinuousWithinAt
      (iteratedFDerivWithin ℝ j (leftFaceReflection d m i a u) c) c x :=
    (hreg.continuousOn_iteratedFDerivWithin (by exact_mod_cast hj) hcunique) x hxc
  have hwithin : Filter.Tendsto
      (fun z => iteratedFDerivWithin ℝ j (leftFaceReflection d m i a u) c z)
      (nhdsWithin x s)
      (nhds (iteratedFDerivWithin ℝ j (leftFaceReflection d m i a u) c x)) :=
    hcont.mono_left (nhdsWithin_mono x hs_sub)
  have hopenreg := leftFaceReflection_contDiffOn_openCollar d m i a u hu
  have hface := leftFaceReflection_jet_tendsto_face d m i a ha u hu j hj x hx hxi
  have hface' : Filter.Tendsto
      (fun z => iteratedFDerivWithin ℝ j (leftFaceReflection d m i a u) c z)
      (nhdsWithin x s) (nhds (iteratedFDerivWithin ℝ j u (cube d) x)) := by
    apply hface.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    symm
    exact iteratedFDerivWithin_eq_iteratedFDeriv hcunique
      ((hopenreg.contDiffAt (hsopen.mem_nhds hz)).of_le (by exact_mod_cast hj))
      (hs_sub hz)
  exact tendsto_nhds_unique hwithin hface'

end Causalean.Mathlib.Analysis.Calculus.CubeExtension
