module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.Clamping

/-!
# Global Hölder extension from the cube at derivative order zero

A function on the cube [−1,1]^d that is bounded and s-Hölder with exponent s ∈ (0, 1] and radius L
extends to a continuous function on all of ℝ^d that agrees with it on the cube, is bounded by A·L
and is s-Hölder with constant A·L, where A depends only on d and s. The extension is the function
composed with the coordinatewise clamping of a point to the cube.

## Main results

* `exists_global_holder_extension_order_zero` — the order-zero extension with controlled sup norm
  and Hölder constant.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

open Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- In [dimension d](hyp:d), for [a Hölder exponent s](hyp:s) with [0 < s](hyp:hs),
[there is a positive constant A such that every response u
in the intrinsic order-zero Hölder ball of exponent s and radius L ≥ 0 on the
normalized cube has a continuous global representative U that agrees with u on
the cube, is bounded in absolute value by A·L everywhere, and is s-Hölder with
coefficient A·L on the whole space](goal). -/
theorem exists_global_holder_extension_order_zero (d : ℕ) (s : ℝ)
    (hs : 0 < s) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (u : (Fin d → ℝ) → ℝ) (L : ℝ), 0 ≤ L →
        CubeHolderBall d 0 s L u →
        ∃ U : (Fin d → ℝ) → ℝ,
          Set.EqOn U u (cube d) ∧
          ContDiff ℝ 0 U ∧
          (∀ j ≤ 0, ∀ x, ‖iteratedFDeriv ℝ j U x‖ ≤ A * L) ∧
          (∀ x y,
            ‖iteratedFDeriv ℝ 0 U x - iteratedFDeriv ℝ 0 U y‖
              ≤ A * L * ‖x - y‖ ^ s) := by
  refine ⟨1, by norm_num, ?_⟩
  intro u L hL hu
  let U : (Fin d → ℝ) → ℝ := fun x => u (cubeClamp d x)
  have hbound (x : Fin d → ℝ) : ‖U x‖ ≤ L := by
    have h := hu.derivBound 0 (Nat.le_refl 0) (Fin.elim0)
      (cubeClamp d x) (cubeClamp_mem_cube d x)
    simpa [U, coordJetOn, iteratedFDerivWithin_zero_apply,
      Real.norm_eq_abs] using h
  have hmod (x y : Fin d → ℝ) : ‖U x - U y‖ ≤ L * ‖x - y‖ ^ s := by
    have h := hu.modulus (Fin.elim0)
      (cubeClamp d x) (cubeClamp_mem_cube d x)
      (cubeClamp d y) (cubeClamp_mem_cube d y)
    have h' : ‖U x - U y‖ ≤
        L * ‖cubeClamp d x - cubeClamp d y‖ ^ s := by
      simpa [U, coordJetOn, iteratedFDerivWithin_zero_apply,
        Real.norm_eq_abs] using h
    calc
      ‖U x - U y‖ ≤ L * ‖cubeClamp d x - cubeClamp d y‖ ^ s := h'
      _ ≤ L * ‖x - y‖ ^ s := by
        gcongr
        exact cubeClamp_nonexpansive d x y
  have hcont : Continuous U := by
    refine continuous_iff_continuousAt.mpr fun x =>
      tendsto_iff_norm_sub_tendsto_zero.mpr ?_
    refine squeeze_zero (fun y => norm_nonneg _) (fun y => hmod y x) ?_
    have hn : ContinuousAt (fun y : Fin d → ℝ => ‖y - x‖) x :=
      (continuousAt_id.sub continuousAt_const).norm
    have hp : ContinuousAt (fun y : Fin d → ℝ => ‖y - x‖ ^ s) x :=
      hn.rpow_const (Or.inr hs.le)
    have hc : ContinuousAt (fun _ : Fin d → ℝ => L) x := continuousAt_const
    have ht := (hc.mul hp).tendsto
    change Filter.Tendsto (fun y : Fin d → ℝ => L * ‖y - x‖ ^ s)
      (nhds x) (nhds (L * ‖x - x‖ ^ s)) at ht
    simpa [Real.zero_rpow hs.ne'] using ht
  refine ⟨U, ?_, contDiff_zero.mpr hcont, ?_, ?_⟩
  · intro x hx
    simp [U, cubeClamp_fixed hx]
  · intro j hj x
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    simpa only [norm_iteratedFDeriv_zero, one_mul] using hbound x
  · intro x y
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_apply,
      ← map_sub, LinearIsometryEquiv.norm_map, one_mul] using hmod x y

end Causalean.Mathlib.Analysis.Calculus.CubeExtension
