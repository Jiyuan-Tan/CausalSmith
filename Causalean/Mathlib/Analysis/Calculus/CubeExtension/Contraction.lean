module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.Basic
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.Interpolation

/-!
# Contracting intrinsic cube data to ambient cube data

A strict contraction sends the closed cube into its interior. Pulling an
intrinsic response back by this contraction gives ambient coordinate jets on
the entire closed cube, with the original supremum and Hölder bounds.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

open Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- If [0 < t](hyp:ht0) and [t < 1](hyp:ht1), [s > 0](hyp:hs), and [a response
u](hyp:u) is [m times continuously differentiable within the closed
cube](hyp:hu), [bounded in absolute value by M on the cube](hyp:hM), and [has a
top-order intrinsic s-Hölder modulus with coefficient L on the cube](hyp:hL),
then [the contracted response x ↦ u(t·x) is m times continuously
differentiable within the cube, is still bounded by M on the cube, and its
top-order ambient coordinate partial derivatives have an s-Hölder modulus with
coefficient L on the cube](goal). -/
theorem contracted_cube_ambient_data {d m : ℕ} {s t M L : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (hs : 0 < s)
    (u : (Fin d → ℝ) → ℝ) (hu : ContDiffOn ℝ m u (cube d))
    (hM : ∀ x ∈ cube d, |u x| ≤ M)
    (hL : TopHolderOn (cube d) m s L u) :
    ContDiffOn ℝ m (fun x => u (t • x)) (cube d) ∧
      (∀ x ∈ cube d, |u (t • x)| ≤ M) ∧
      TopHolder d m s L (fun x => u (t • x)) := by
  /-
  Use that `t • cube d` lies in `openCube d`. On this open region the
  within jet is the ambient jet; the scalar chain rule contributes `t ^ m`.
  Both `t ^ m` and `t ^ s` are at most one. The `m = 0` case uses the
  ordinary response modulus directly.
  -/
  have hsub : openCube d ⊆ cube d := by
    intro z hz i
    exact ⟨(hz i trivial).1.le, (hz i trivial).2.le⟩
  have hopen : IsOpen (openCube d) :=
    isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)
  have hscaled (x : Fin d → ℝ) (hx : x ∈ cube d) : t • x ∈ openCube d := by
    intro i _
    have hi := hx i
    change -1 ≤ x i ∧ x i ≤ 1 at hi
    change -1 < t * x i ∧ t * x i < 1
    constructor <;> nlinarith [mul_nonneg ht0.le (sub_nonneg.mpr hi.1),
      mul_nonneg ht0.le (sub_nonneg.mpr hi.2)]
  let g : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ) :=
    ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := Fin d → ℝ)
      (Units.mk0 t (ne_of_gt ht0))
  have hg (x : Fin d → ℝ) : g x = t • x := by
    ext i
    simp [g]
  have hfun : (fun x => u (t • x)) = u ∘ g := by
    funext x
    simp [hg x]
  have hpreopen : IsOpen (g ⁻¹' openCube d) := hopen.preimage g.continuous
  have hreg : ContDiffOn ℝ m (fun x => u (t • x)) (cube d) := by
    have hcomp := hu.comp g.contDiff.contDiffOn (fun x hx => hsub (hscaled x hx))
    rw [hfun]
    exact hcomp
  have hjet (j : ℕ) (hj : j ≤ m) (f : Fin j → Fin d)
      (x : Fin d → ℝ) (hx : x ∈ cube d) :
      coordPartial j (fun z => u (t • z)) f x =
        t ^ j * coordJetOn (cube d) j u f (t • x) := by
    have hsource : ContDiffAt ℝ j u (g x) :=
      (hu.mono hsub).contDiffAt (hopen.mem_nhds (by simpa [hg] using hscaled x hx))
        |>.of_le (by exact_mod_cast hj)
    have htarget : ContDiffAt ℝ j (u ∘ g) x :=
      ((hu.mono hsub).comp g.contDiff.contDiffOn (fun _ hz => hz)).contDiffAt
        (hpreopen.mem_nhds (by simpa [hg] using hscaled x hx))
        |>.of_le (by exact_mod_cast hj)
    have hchain := g.iteratedFDerivWithin_comp_right u hopen.uniqueDiffOn
      (by simpa [hg] using hscaled x hx) j
    rw [coordJetOn_cube_eq_ambient hu hj (hscaled x hx)]
    unfold coordPartial
    rw [hfun]
    rw [← iteratedFDerivWithin_eq_iteratedFDeriv hpreopen.uniqueDiffOn htarget
      (by simpa [hg] using hscaled x hx)]
    rw [hchain]
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hopen.uniqueDiffOn hsource
      (by simpa [hg] using hscaled x hx)]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousLinearEquiv.coe_coe]
    have hb (k : Fin j) : g (Pi.single (f k) (1 : ℝ)) =
        t • Pi.single (f k) (1 : ℝ) := hg _
    simp only [hb]
    rw [ContinuousMultilinearMap.map_smul_univ]
    simp [Finset.prod_const, smul_eq_mul, hg]
  refine ⟨hreg, ?_, ?_⟩
  · intro x hx
    exact hM (t • x) (hsub (hscaled x hx))
  · intro f x hx y hy
    rw [hjet m le_rfl f x hx, hjet m le_rfl f y hy]
    have hmod := hL f (t • x) (hsub (hscaled x hx))
      (t • y) (hsub (hscaled y hy))
    have hnorm : ‖t • x - t • y‖ = t * ‖x - y‖ := by
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
    have htpow : t ^ m ≤ 1 := pow_le_one₀ ht0.le ht1.le
    have hspow : t ^ s ≤ 1 := Real.rpow_le_one ht0.le ht1.le hs.le
    have hfactor : t ^ m * t ^ s ≤ 1 := by
      nlinarith [pow_nonneg ht0.le m, Real.rpow_nonneg ht0.le s]
    have hbase : 0 ≤ L * ‖t • x - t • y‖ ^ s :=
      (abs_nonneg _).trans hmod
    calc
      |t ^ m * coordJetOn (cube d) m u f (t • x) -
          t ^ m * coordJetOn (cube d) m u f (t • y)| =
          t ^ m * |coordJetOn (cube d) m u f (t • x) -
            coordJetOn (cube d) m u f (t • y)| := by
              rw [← mul_sub, abs_mul, abs_of_nonneg (pow_nonneg ht0.le _)]
      _ ≤ t ^ m * (L * ‖t • x - t • y‖ ^ s) :=
        mul_le_mul_of_nonneg_left hmod (pow_nonneg ht0.le _)
      _ = (t ^ m * t ^ s) * (L * ‖x - y‖ ^ s) := by
        rw [hnorm, Real.mul_rpow ht0.le (norm_nonneg _)]
        ring
      _ ≤ L * ‖x - y‖ ^ s := by
        have hnonneg : 0 ≤ L * ‖x - y‖ ^ s := by
          rw [hnorm, Real.mul_rpow ht0.le (norm_nonneg _)] at hbase
          have htp : 0 < t ^ s := Real.rpow_pos_of_pos ht0 _
          nlinarith
        nlinarith

end Causalean.Mathlib.Analysis.Calculus.CubeExtension
