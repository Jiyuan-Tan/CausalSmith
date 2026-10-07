module
public import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Differentiability across two closed pieces

These lemmas isolate the local gluing argument needed when a cube face joins
two regions carrying the same response and matching intrinsic jets.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

open Filter

/-- If [two sets s and t are closed](hyp:hs,ht), [a function f is
differentiable within s and within t](hyp:hfs,hft), and [the within-s and
within-t derivatives of f agree at every point of s ∩ t](hyp:hmatch), then [f is
differentiable within s ∪ t](goal). -/
theorem differentiableOn_closed_union_of_matching_fderiv (d : ℕ)
    (s t : Set (Fin d → ℝ)) (hs : IsClosed s) (ht : IsClosed t)
    (f : (Fin d → ℝ) → ℝ)
    (hfs : DifferentiableOn ℝ f s) (hft : DifferentiableOn ℝ f t)
    (hmatch : ∀ x ∈ s ∩ t,
      fderivWithin ℝ f s x = fderivWithin ℝ f t x) :
    DifferentiableOn ℝ f (s ∪ t) := by
  intro x hx
  rcases hx with hx | hx
  · by_cases hxt : x ∈ t
    · have hds := (hfs x hx).hasFDerivWithinAt
      have hdt := (hft x hxt).hasFDerivWithinAt
      rw [hmatch x ⟨hx, hxt⟩] at hds
      exact (hds.union hdt).differentiableWithinAt
    · have hnear : s ∈ nhdsWithin x (s ∪ t) := by
        filter_upwards [self_mem_nhdsWithin,
          mem_nhdsWithin_of_mem_nhds (ht.isOpen_compl.mem_nhds hxt)]
          with y hy hyt
        exact hy.resolve_right hyt
      exact ((hfs x hx).hasFDerivWithinAt.mono_of_mem_nhdsWithin hnear).differentiableWithinAt
  · by_cases hxs : x ∈ s
    · have hds := (hfs x hxs).hasFDerivWithinAt
      have hdt := (hft x hx).hasFDerivWithinAt
      rw [hmatch x ⟨hxs, hx⟩] at hds
      exact (hds.union hdt).differentiableWithinAt
    · have hnear : t ∈ nhdsWithin x (s ∪ t) := by
        filter_upwards [self_mem_nhdsWithin,
          mem_nhdsWithin_of_mem_nhds (hs.isOpen_compl.mem_nhds hxs)]
          with y hy hys
        exact hy.resolve_left hys
      exact ((hft x hx).hasFDerivWithinAt.mono_of_mem_nhdsWithin hnear).differentiableWithinAt

/-- If [two sets s and t are closed](hyp:hs,ht), [each has unique within-set
derivatives](hyp:hus,hut), [a function f is m
times continuously differentiable within s and within t](hyp:hfs,hft), and [for
every order j ≤ m the j-th within-s and within-t derivatives of f agree on
s ∩ t](hyp:hmatch), then [f is m times continuously differentiable within
s ∪ t](goal). -/
theorem contDiffOn_closed_union_of_matching_jets (d m : ℕ)
    (s t : Set (Fin d → ℝ))
    (hs : IsClosed s) (ht : IsClosed t)
    (hus : UniqueDiffOn ℝ s) (hut : UniqueDiffOn ℝ t)
    (f : (Fin d → ℝ) → ℝ)
    (hfs : ContDiffOn ℝ m f s) (hft : ContDiffOn ℝ m f t)
    (hmatch : ∀ j ≤ m, ∀ x ∈ s ∩ t,
      iteratedFDerivWithin ℝ j f s x =
        iteratedFDerivWithin ℝ j f t x) :
    ContDiffOn ℝ m f (s ∪ t) := by
  classical
  let p : (Fin d → ℝ) → FormalMultilinearSeries ℝ (Fin d → ℝ) ℝ :=
    fun x => if x ∈ s then ftaylorSeriesWithin ℝ f s x else ftaylorSeriesWithin ℝ f t x
  have hps : HasFTaylorSeriesUpToOn m f p s := by
    apply (hfs.ftaylorSeriesWithin hus).congr_series
    intro j hj x hx
    simp [p, hx]
  have hpt : HasFTaylorSeriesUpToOn m f p t := by
    apply (hft.ftaylorSeriesWithin hut).congr_series
    intro j hj x hx
    by_cases hxs : x ∈ s
    · have hj' : j ≤ m := by exact_mod_cast hj
      simpa [p, hxs, ftaylorSeriesWithin] using (hmatch j hj' x ⟨hxs, hx⟩).symm
    · simp [p, hxs]
  refine (show HasFTaylorSeriesUpToOn (m : ℕ∞) f p (s ∪ t) from ?_).contDiffOn
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rcases hx with hx | hx
    · exact hps.zero_eq x hx
    · exact hpt.zero_eq x hx
  · intro j hj x hx
    by_cases hxs : x ∈ s
    · by_cases hxt : x ∈ t
      · exact (hps.fderivWithin j hj x hxs).union (hpt.fderivWithin j hj x hxt)
      · have hnear : s ∈ nhdsWithin x (s ∪ t) := by
          filter_upwards [self_mem_nhdsWithin,
            mem_nhdsWithin_of_mem_nhds (ht.isOpen_compl.mem_nhds hxt)]
            with y hy hyt
          exact hy.resolve_right hyt
        exact (hps.fderivWithin j hj x hxs).mono_of_mem_nhdsWithin hnear
    · have hxt : x ∈ t := hx.resolve_left hxs
      have hnear : t ∈ nhdsWithin x (s ∪ t) := by
        filter_upwards [self_mem_nhdsWithin,
          mem_nhdsWithin_of_mem_nhds (hs.isOpen_compl.mem_nhds hxs)]
          with y hy hys
        exact hy.resolve_left hys
      exact (hpt.fderivWithin j hj x hxt).mono_of_mem_nhdsWithin hnear
  · intro j hj
    exact (hps.cont j hj).union_of_isClosed (hpt.cont j hj) hs ht

end Causalean.Mathlib.Analysis.Calculus.CubeExtension
