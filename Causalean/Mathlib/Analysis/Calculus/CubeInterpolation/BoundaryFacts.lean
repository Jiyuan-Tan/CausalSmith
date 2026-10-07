module
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.Basic
public import Mathlib.Analysis.Calculus.TangentCone.Pi

/-!
# Cube closure and boundary jets

The open cube is dense in the closed cube. Within derivatives therefore inherit
interior bounds. An ambient iterated derivative at a face either agrees with
the corresponding within derivative or has Lean's fallback value zero.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- Every point of the closed coordinate cube is a limit of points in the open
coordinate cube. -/
theorem cube_subset_closure_openCube (d : ℕ) :
    cube d ⊆ closure (openCube d) := by
  intro x hx
  rw [openCube, mem_closure_pi]
  intro i _
  rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]
  exact hx i

private theorem cube_eq_pi (d : ℕ) :
    cube d = Set.univ.pi (fun _ : Fin d => Set.Icc (-1 : ℝ) 1) := by
  ext x
  simp [cube, Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube,
    Pi.le_def, forall_and]

private theorem cube_uniqueDiffOn (d : ℕ) : UniqueDiffOn ℝ (cube d) := by
  rw [cube_eq_pi]
  exact UniqueDiffOn.pi (fun _ _ => uniqueDiffOn_Icc (by norm_num))

private theorem closure_openCube_eq_cube (d : ℕ) : closure (openCube d) = cube d := by
  rw [cube_eq_pi]
  simp only [openCube, closure_pi_set, closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]

private theorem isOpen_openCube (d : ℕ) : IsOpen (openCube d) := by
  exact isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)

private theorem openCube_subset_cube (d : ℕ) : openCube d ⊆ cube d := by
  intro x hx i
  exact ⟨(hx i trivial).1.le, (hx i trivial).2.le⟩

/-- An interior bound on a coordinate partial extends to the corresponding
within derivative throughout the closed cube. -/
theorem within_coordPartial_bound_extends {d m j : ℕ}
    {u : (Fin d → ℝ) → ℝ} {B : ℝ}
    (hu : ContDiffOn ℝ m u (cube d)) (hj : j ≤ m)
    (f : Fin j → Fin d)
    (hinterior : ∀ x ∈ openCube d, |coordPartial j u f x| ≤ B) :
    ∀ x ∈ cube d,
      |iteratedFDerivWithin ℝ j u (cube d) x
        (fun a => Pi.single (f a) (1 : ℝ))| ≤ B := by
  let v : Fin j → Fin d → ℝ := fun a => Pi.single (f a) (1 : ℝ)
  have hcont : ContinuousOn
      (fun x => |iteratedFDerivWithin ℝ j u (cube d) x v|) (cube d) := by
    have heval : Continuous
        (fun L : ContinuousMultilinearMap ℝ (fun _ : Fin j => Fin d → ℝ) ℝ => |L v|) := by
      fun_prop
    exact heval.comp_continuousOn
      (hu.continuousOn_iteratedFDerivWithin (by exact_mod_cast hj) (cube_uniqueDiffOn d))
  have hbound : ∀ x ∈ openCube d,
      |iteratedFDerivWithin ℝ j u (cube d) x v| ≤ B := by
    intro x hx
    have hreg : ContDiffAt ℝ j u x :=
      (hu.mono (openCube_subset_cube d)).contDiffAt
        ((isOpen_openCube d).mem_nhds hx) |>.of_le (by exact_mod_cast hj)
    rw [iteratedFDerivWithin_eq_iteratedFDeriv (cube_uniqueDiffOn d) hreg
      (openCube_subset_cube d hx)]
    exact hinterior x hx
  intro x hx
  change |iteratedFDerivWithin ℝ j u (cube d) x v| ≤ B
  exact le_on_closure hbound (by simpa [closure_openCube_eq_cube] using hcont)
    continuousOn_const (by simpa [closure_openCube_eq_cube] using hx)

/-- For [a function that is m times continuously differentiable on the closed normalized
cube](hyp:hu), [an order j at most m](hyp:hj), and [a point](hyp:x) [of that cube](hyp:hx), [the
order-j iterated derivative taken in the whole space is either zero or equal to the order-j
iterated derivative taken within the cube](goal). -/
theorem ambient_jet_zero_or_within {d m j : ℕ}
    {u : (Fin d → ℝ) → ℝ}
    (hu : ContDiffOn ℝ m u (cube d)) (hj : j ≤ m)
    (x : Fin d → ℝ) (hx : x ∈ cube d) :
    iteratedFDeriv ℝ j u x = 0 ∨
      iteratedFDeriv ℝ j u x = iteratedFDerivWithin ℝ j u (cube d) x := by
  cases j with
  | zero =>
      exact Or.inr rfl
  | succ n =>
      let g := iteratedFDeriv ℝ n u
      let w := iteratedFDerivWithin ℝ n u (cube d)
      by_cases hd : DifferentiableAt ℝ g x
      · right
        have hnm : (n : WithTop ℕ∞) < m := by exact_mod_cast (Nat.lt_of_succ_le hj)
        have hwcont : ContinuousOn w (cube d) :=
          hu.continuousOn_iteratedFDerivWithin (by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_succ_le hj)))
            (cube_uniqueDiffOn d)
        have heq : Set.EqOn g w (openCube d) := by
          intro y hy
          have hreg : ContDiffAt ℝ n u y :=
            (hu.mono (openCube_subset_cube d)).contDiffAt
              ((isOpen_openCube d).mem_nhds hy) |>.of_le
                (by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_succ_le hj)))
          exact (iteratedFDerivWithin_eq_iteratedFDeriv
            (cube_uniqueDiffOn d) hreg (openCube_subset_cube d hy)).symm
        have hxeq : g x = w x := by
          haveI : (nhdsWithin x (openCube d)).NeBot :=
            mem_closure_iff_clusterPt.mp (by simpa [closure_openCube_eq_cube] using hx)
          exact tendsto_nhds_unique_of_eventuallyEq
            (hd.continuousAt.mono_left nhdsWithin_le_nhds)
            ((hwcont x hx).mono_left (nhdsWithin_mono _ (openCube_subset_cube d)))
            (heq.eventuallyEq_of_mem self_mem_nhdsWithin)
        have hwdiff := hu.differentiableOn_iteratedFDerivWithin hnm
          (cube_uniqueDiffOn d) x hx
        have hgderiv : HasFDerivWithinAt g (fderiv ℝ g x) (openCube d) x :=
          hd.hasFDerivAt.hasFDerivWithinAt
        have hwderiv : HasFDerivWithinAt w
            (fderivWithin ℝ w (cube d) x) (openCube d) x :=
          hwdiff.hasFDerivWithinAt.mono (openCube_subset_cube d)
        have huniq : UniqueDiffWithinAt ℝ (openCube d) x := by
          have hc : UniqueDiffWithinAt ℝ (closure (openCube d)) x := by
            simpa [closure_openCube_eq_cube] using cube_uniqueDiffOn d x hx
          exact hc.of_closure
        have hderiv : fderiv ℝ g x = fderivWithin ℝ w (cube d) x :=
          huniq.eq hgderiv (hwderiv.congr heq hxeq)
        simpa only [iteratedFDeriv_succ_eq_comp_left,
          iteratedFDerivWithin_succ_eq_comp_left, Function.comp_apply, g, w] using
          congrArg (continuousMultilinearCurryLeftEquiv ℝ
            (fun _ : Fin (n + 1) => Fin d → ℝ) ℝ).symm hderiv
      · left
        simp [iteratedFDeriv_succ_eq_comp_left,
          fderiv_zero_of_not_differentiableAt hd, g]

end Causalean.Mathlib.Analysis.Calculus.CubeInterpolation
