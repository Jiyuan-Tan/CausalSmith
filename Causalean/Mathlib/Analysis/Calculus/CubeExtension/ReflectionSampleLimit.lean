module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.ReflectionSampleJets

/-!
# Boundary limits of inward sample jets

At a cube face, an affine inward sample has a boundary jet determined by the
intrinsic jet of the original response and the sample's diagonal linear part.
This isolates the chain-rule and continuity step used to glue reflections.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

open Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- If [a response u is m times continuously differentiable within the closed
cube](hyp:hu), [j ≤ m](hyp:hj), and [x is a cube point](hyp:hx) [on the left face
in coordinate i](hyp:hxi), then [as z approaches x from within the open exterior
collar, the order-j ambient derivative at z of the composite
y ↦ u(inward sample of y with dilation index q), evaluated on the standard basis
vectors in directions f, converges to the order-j within-cube derivative of u at
x evaluated on the same basis vectors, those in direction i scaled by
−(q + 1)](goal). -/
theorem leftFaceSample_coordinate_jet_tendsto_face (d m : ℕ) (i : Fin d)
    (q : Fin (m + 1)) (u : (Fin d → ℝ) → ℝ)
    (hu : ContDiffOn ℝ m u (cube d)) (j : ℕ) (hj : j ≤ m)
    (f : Fin j → Fin d) (x : Fin d → ℝ)
    (hx : x ∈ cube d) (hxi : x i = -1) :
    Filter.Tendsto
      (fun z =>
        iteratedFDeriv ℝ j (fun y => u (leftFaceSample d i q y)) z
          (fun k => Pi.single (f k) (1 : ℝ)))
      (nhdsWithin x (leftOpenCubeCollar d m i))
      (nhds
        (iteratedFDerivWithin ℝ j u (cube d) x
          (fun k =>
            (if f k = i then -((q.val : ℝ) + 1) else 1) •
              Pi.single (f k) (1 : ℝ)))) := by
  /- Express the sample as an affine map with diagonal linear part. On the
  open collar, the ordinary chain rule for an affine map gives the stated
  coordinate jet at the inward sample point. Those sample points lie in the
  cube and tend to `x` by `leftFaceSample_fixed`; apply continuity of the
  within-cube iterated derivative, then evaluate the resulting multilinear
  map on the fixed scaled coordinate tuple. -/
  classical
  let a : Fin d → ℝ := leftFaceSample d i q 0
  let g : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) := {
    toFun := fun y k => if k = i then -((q : ℝ) + 1) * y k else y k
    map_add' := by
      intro y z
      ext k
      by_cases hk : k = i <;> simp [hk, mul_add]
    map_smul' := by
      intro c y
      ext k
      by_cases hk : k = i <;> simp [hk]
      ring
    cont := by
      apply continuous_pi
      intro k
      by_cases hk : k = i
      · subst k
        simp only
        exact (continuous_const.mul (continuous_apply i) :
          Continuous (fun y : Fin d → ℝ => -((q : ℝ) + 1) * y i))
      · simpa [hk] using (continuous_apply k)
  }
  have hsamp (y : Fin d → ℝ) : leftFaceSample d i q y = g y + a := by
    ext k
    by_cases hk : k = i
    · subst k
      simp [g, a, leftFaceSample]
      ring
    · simp [g, a, leftFaceSample, hk]
  let S : Set (Fin d → ℝ) := {y | y + a ∈ openCube d}
  let F : (Fin d → ℝ) → ℝ := fun y => u (y + a)
  have hopen : IsOpen (openCube d) :=
    isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)
  have hsub : openCube d ⊆ cube d := by
    intro y hy k
    exact ⟨(hy k trivial).1.le, (hy k trivial).2.le⟩
  have hSopen : IsOpen S := hopen.preimage (continuous_id.add continuous_const)
  have hSf : ContDiffOn ℝ m F S := by
    have htrans : ContDiff ℝ m (fun y : Fin d → ℝ => y + a) :=
      contDiff_id.add contDiff_const
    exact (hu.mono hsub).comp htrans.contDiffOn (fun y hy => hy)
  let v : Fin j → Fin d → ℝ := fun k =>
    (if f k = i then -((q.val : ℝ) + 1) else 1) • Pi.single (f k) (1 : ℝ)
  have hgv (k : Fin j) : g (Pi.single (f k) (1 : ℝ)) = v k := by
    ext l
    by_cases hl : l = i <;> by_cases hf : f k = i <;>
      simp [g, v, hl, hf, Pi.single_apply]
  have hcube : UniqueDiffOn ℝ (cube d) := by
    have hc : cube d = Set.univ.pi (fun _ : Fin d => Set.Icc (-1 : ℝ) 1) := by
      ext y
      simp [cube, Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube,
        Pi.le_def, forall_and]
    rw [hc]
    exact UniqueDiffOn.pi (fun _ _ => uniqueDiffOn_Icc (by norm_num))
  have hjet (z : Fin d → ℝ) (hz : z ∈ leftOpenCubeCollar d m i) :
      iteratedFDeriv ℝ j (fun y => u (leftFaceSample d i q y)) z
        (fun k => Pi.single (f k) (1 : ℝ)) =
      iteratedFDerivWithin ℝ j u (cube d) (leftFaceSample d i q z) v := by
    have hsrc : g z ∈ S := by
      change g z + a ∈ openCube d
      rw [← hsamp]
      exact leftFaceSample_mem_openCube i q z hz
    have htarget : ContDiffAt ℝ j (F ∘ g) z :=
      (hSf.comp_continuousLinearMap g).contDiffAt
        ((hSopen.preimage g.continuous).mem_nhds hsrc) |>.of_le
          (by exact_mod_cast hj)
    have hsource : ContDiffAt ℝ j F (g z) :=
      hSf.contDiffAt (hSopen.mem_nhds hsrc) |>.of_le
        (by exact_mod_cast hj)
    have hchain := g.iteratedFDerivWithin_comp_right hSf hSopen.uniqueDiffOn
      (hSopen.preimage g.continuous).uniqueDiffOn hsrc
      (show j ≤ (m : WithTop ℕ∞) by exact_mod_cast hj)
    have hfun : (fun y => u (leftFaceSample d i q y)) = F ∘ g := by
      funext y
      simp [F, hsamp]
    have hreg : ContDiffAt ℝ j u (leftFaceSample d i q z) :=
      (hu.mono hsub).contDiffAt
        (hopen.mem_nhds (leftFaceSample_mem_openCube i q z hz)) |>.of_le
          (by exact_mod_cast hj)
    have hfull : iteratedFDeriv ℝ j (fun y => u (leftFaceSample d i q y)) z =
        (iteratedFDeriv ℝ j u (leftFaceSample d i q z)).compContinuousLinearMap
          (fun _ => g) := by
      rw [hfun, ← iteratedFDerivWithin_eq_iteratedFDeriv
        (hSopen.preimage g.continuous).uniqueDiffOn htarget hsrc]
      rw [hchain]
      rw [iteratedFDerivWithin_eq_iteratedFDeriv hSopen.uniqueDiffOn hsource hsrc]
      rw [iteratedFDeriv_comp_add_right j a (g z)]
      rw [hsamp]
    rw [hfull, ← iteratedFDerivWithin_eq_iteratedFDeriv hcube hreg
      (hsub (leftFaceSample_mem_openCube i q z hz))]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, hgv]
  have hsample_cont : Continuous (leftFaceSample d i q) := by
    change Continuous (fun y => leftFaceSample d i q y)
    simp_rw [hsamp]
    exact g.continuous.add continuous_const
  have hsample_tendsto : Filter.Tendsto (leftFaceSample d i q)
      (nhdsWithin x (leftOpenCubeCollar d m i)) (nhdsWithin x (cube d)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have ht := hsample_cont.continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : nhdsWithin x (leftOpenCubeCollar d m i) ≤ nhds x)
      rw [leftFaceSample_fixed i q x hxi] at ht
      exact ht
    · exact Filter.Eventually.mono (self_mem_nhdsWithin) (fun z hz =>
        hsub (leftFaceSample_mem_openCube i q z hz))
  have hcont : ContinuousOn
      (fun y => iteratedFDerivWithin ℝ j u (cube d) y v) (cube d) := by
    have heval : Continuous
        (fun L : ContinuousMultilinearMap ℝ (fun _ : Fin j => Fin d → ℝ) ℝ => L v) := by
      fun_prop
    exact heval.comp_continuousOn
      (hu.continuousOn_iteratedFDerivWithin (by exact_mod_cast hj) hcube)
  have hlimit := (hcont x hx).tendsto.comp hsample_tendsto
  change Filter.Tendsto
    (fun z => iteratedFDerivWithin ℝ j u (cube d) (leftFaceSample d i q z) v)
    (nhdsWithin x (leftOpenCubeCollar d m i))
    (nhds (iteratedFDerivWithin ℝ j u (cube d) x v)) at hlimit
  apply Filter.Tendsto.congr' ?_ hlimit
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (hjet z hz).symm

end Causalean.Mathlib.Analysis.Calculus.CubeExtension
