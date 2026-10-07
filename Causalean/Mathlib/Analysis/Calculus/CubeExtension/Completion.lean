module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.Basic
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.Contraction
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.Interpolation

/-!
# Intrinsic fixed-cube Hölder completion

Interior interpolation is stated for within-cube jets. Continuous traces pass
its derivative bounds to every face of the closed cube.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.CubeExtension

open Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- If [a response u is m times continuously differentiable
within the closed normalized cube](hyp:hu), [j ≤ m](hyp:hj), and [the order-j
intrinsic coordinate jet of u in a fixed choice of coordinate directions is
bounded in absolute value by B at every interior point of the cube](hyp:hinterior),
then [the same bound B holds at every point of the closed cube](goal). -/
theorem interior_coordJet_bound_extends {d m j : ℕ}
    {u : (Fin d → ℝ) → ℝ} {B : ℝ}
    (hu : ContDiffOn ℝ m u (cube d)) (hj : j ≤ m)
    (f : Fin j → Fin d)
    (hinterior : ∀ x ∈ openCube d, |coordJetOn (cube d) j u f x| ≤ B) :
    ∀ x ∈ cube d, |coordJetOn (cube d) j u f x| ≤ B := by
  apply within_coordPartial_bound_extends hu hj f
  intro x hx
  have h := hinterior x hx
  rw [coordJetOn_cube_eq_ambient hu hj hx] at h
  exact h

/-- In [any dimension d](hyp:d), for [derivative order m](hyp:m) and [an
exponent s](hyp:s) with [0 < s](hyp:hs), [there is a
positive constant K such that, for every response u that is m times
continuously differentiable within the closed cube, bounded in absolute value by
M ≥ 0 there, and whose top-order intrinsic jets have an s-Hölder modulus with
coefficient L ≥ 0, every intrinsic coordinate jet of order at most m is bounded
in absolute value by K·(M + L) at every interior point of the cube](goal). The
constant depends only on d, m and s. -/
theorem interior_fixed_cube_interpolation_within (d m : ℕ)
    (s : ℝ) (hs : 0 < s) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (u : (Fin d → ℝ) → ℝ) (M L : ℝ),
        0 ≤ M → 0 ≤ L → ContDiffOn ℝ m u (cube d) →
        (∀ x ∈ cube d, |u x| ≤ M) → TopHolderOn (cube d) m s L u →
        ∀ j ≤ m, ∀ f : Fin j → Fin d,
          ∀ x ∈ openCube d, |coordJetOn (cube d) j u f x| ≤ K * (M + L) := by
  obtain ⟨K, hK, hinterp⟩ := interior_fixed_cube_interpolation d m s hs
  refine ⟨K, hK, ?_⟩
  intro u M L hM hL hu hbound hholder j hj f x hx
  have hsub : openCube d ⊆ cube d := by
    intro z hz i
    exact ⟨(hz i trivial).1.le, (hz i trivial).2.le⟩
  have hopen : IsOpen (openCube d) :=
    isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)
  have hscaled (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
      (z : Fin d → ℝ) (hz : z ∈ cube d) : t • z ∈ openCube d := by
    intro i _
    have hi := hz i
    change -1 ≤ z i ∧ z i ≤ 1 at hi
    change -1 < t * z i ∧ t * z i < 1
    constructor <;> nlinarith [mul_nonneg ht0.le (sub_nonneg.mpr hi.1),
      mul_nonneg ht0.le (sub_nonneg.mpr hi.2)]
  have hjet (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
      coordPartial j (fun z => u (t • z)) f x =
        t ^ j * coordJetOn (cube d) j u f (t • x) := by
    let g : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ) :=
      ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := Fin d → ℝ)
        (Units.mk0 t (ne_of_gt ht0))
    have hg (z : Fin d → ℝ) : g z = t • z := by
      ext i
      simp [g]
    have hfun : (fun z => u (t • z)) = u ∘ g := by
      funext z
      simp [hg z]
    have hpreopen : IsOpen (g ⁻¹' openCube d) := hopen.preimage g.continuous
    have hsource : ContDiffAt ℝ j u (g x) :=
      (hu.mono hsub).contDiffAt
        (hopen.mem_nhds (by simpa [hg] using hscaled t ht0 ht1 x (hsub hx)))
        |>.of_le (by exact_mod_cast hj)
    have htarget : ContDiffAt ℝ j (u ∘ g) x :=
      ((hu.mono hsub).comp g.contDiff.contDiffOn (fun _ hz => hz)).contDiffAt
        (hpreopen.mem_nhds (by simpa [hg] using hscaled t ht0 ht1 x (hsub hx)))
        |>.of_le (by exact_mod_cast hj)
    have hchain := g.iteratedFDerivWithin_comp_right u hopen.uniqueDiffOn
      (by simpa [hg] using hscaled t ht0 ht1 x (hsub hx)) j
    rw [coordJetOn_cube_eq_ambient hu hj (hscaled t ht0 ht1 x (hsub hx))]
    unfold coordPartial
    rw [hfun]
    rw [← iteratedFDerivWithin_eq_iteratedFDeriv hpreopen.uniqueDiffOn htarget
      (by simpa [hg] using hscaled t ht0 ht1 x (hsub hx))]
    rw [hchain]
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hopen.uniqueDiffOn hsource
      (by simpa [hg] using hscaled t ht0 ht1 x (hsub hx))]
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousLinearEquiv.coe_coe]
    have hb (k : Fin j) : g (Pi.single (f k) (1 : ℝ)) =
        t • Pi.single (f k) (1 : ℝ) := hg _
    simp only [hb]
    rw [ContinuousMultilinearMap.map_smul_univ]
    simp [Finset.prod_const, smul_eq_mul, hg]
  have hbound_t (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
      |t ^ j * coordJetOn (cube d) j u f (t • x)| ≤ K * (M + L) := by
    obtain ⟨hreg, hsup, htop⟩ := contracted_cube_ambient_data
      ht.1 ht.2 hs u hu hbound hholder
    rw [← hjet t ht.1 ht.2]
    exact hinterp (fun z => u (t • z)) M L hM hL hreg hsup htop
      j hj f x hx
  have hmap : Set.MapsTo (fun t : ℝ => t • x) (Set.Icc (0 : ℝ) 1) (cube d) := by
    intro t ht i
    rcases ht with ⟨ht0, ht1⟩
    have hi := (hsub hx) i
    change -1 ≤ x i ∧ x i ≤ 1 at hi
    change -1 ≤ t * x i ∧ t * x i ≤ 1
    constructor <;> nlinarith [mul_nonneg ht0 (by linarith : 0 ≤ x i + 1),
      mul_nonneg ht0 (by linarith : 0 ≤ 1 - x i)]
  have hcontsmul : Continuous (fun t : ℝ => t • x) := by fun_prop
  have hcontjet : ContinuousOn
      (fun t : ℝ => coordJetOn (cube d) j u f (t • x)) (Set.Icc (0 : ℝ) 1) :=
    (continuousOn_coordJetOn_cube hu hj f).comp hcontsmul.continuousOn hmap
  have hcont : ContinuousOn
      (fun t : ℝ => |t ^ j * coordJetOn (cube d) j u f (t • x)|)
      (Set.Icc (0 : ℝ) 1) := by
    fun_prop
  have hclosure : closure (Set.Ioo (0 : ℝ) 1) = Set.Icc 0 1 := by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
  have hfinal := le_on_closure hbound_t
    (by simpa [hclosure] using hcont)
    (by fun_prop : ContinuousOn (fun _ : ℝ => K * (M + L))
      (closure (Set.Ioo (0 : ℝ) 1)))
    (by simp [hclosure] : (1 : ℝ) ∈ closure (Set.Ioo (0 : ℝ) 1))
  simpa using hfinal

/-- In [any dimension d](hyp:d), for [derivative order m](hyp:m) and [an
exponent s](hyp:s) with [0 < s](hyp:hs), [there is a
positive constant K such that, for every response u that is m times
continuously differentiable within the closed cube, bounded in absolute value by
M ≥ 0 there, and whose top-order intrinsic jets have an s-Hölder modulus with
coefficient L ≥ 0, every intrinsic coordinate jet of order at most m is bounded
in absolute value by K·(M + L) on the whole closed cube](goal). The constant
depends only on d, m and s. -/
theorem fixed_cube_interpolation_within (d m : ℕ)
    (s : ℝ) (hs : 0 < s) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (u : (Fin d → ℝ) → ℝ) (M L : ℝ),
        0 ≤ M → 0 ≤ L → ContDiffOn ℝ m u (cube d) →
        (∀ x ∈ cube d, |u x| ≤ M) → TopHolderOn (cube d) m s L u →
        DerivBoundOn (cube d) m (K * (M + L)) u := by
  obtain ⟨K, hK, hinterior⟩ :=
    interior_fixed_cube_interpolation_within d m s hs
  refine ⟨K, hK, ?_⟩
  intro u M L hM hL hu hbound hholder j hj f x hx
  exact interior_coordJet_bound_extends
    hu hj f
    (hinterior u M L hM hL hu hbound hholder j hj f) x hx

/-- In [dimension d](hyp:d), for [derivative order m](hyp:m) and [an
exponent s](hyp:s) with [0 < s](hyp:hs), [there is a
positive constant K such that every response u that is m times continuously
differentiable within the closed cube, bounded in absolute value by M ≥ 0
there, and whose top-order intrinsic jets have an s-Hölder modulus with
coefficient L ≥ 0, lies in the intrinsic Hölder ball of order m, exponent s and
radius K·(M + L) on the closed cube](goal). The constant depends only on d, m
and s. -/
theorem cube_holder_completion (d m : ℕ)
    (s : ℝ) (hs : 0 < s) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (u : (Fin d → ℝ) → ℝ) (M L : ℝ),
        0 ≤ M → 0 ≤ L → ContDiffOn ℝ m u (cube d) →
        (∀ x ∈ cube d, |u x| ≤ M) → TopHolderOn (cube d) m s L u →
        CubeHolderBall d m s (K * (M + L)) u := by
  obtain ⟨K, hK, hinterp⟩ := fixed_cube_interpolation_within d m s hs
  refine ⟨K + 1, by linarith, ?_⟩
  intro u M L hM hL hu hbound hholder
  refine ⟨hu, ?_, ?_⟩
  · intro j hj f x hx
    exact (hinterp u M L hM hL hu hbound hholder j hj f x hx).trans
      (mul_le_mul_of_nonneg_right (by linarith : K ≤ K + 1) (add_nonneg hM hL))
  · intro f x hx y hy
    exact (hholder f x hx y hy).trans
      (mul_le_mul_of_nonneg_right
        (by nlinarith [add_nonneg hM hL] : L ≤ (K + 1) * (M + L))
        (by positivity))

end Causalean.Mathlib.Analysis.Calculus.CubeExtension
