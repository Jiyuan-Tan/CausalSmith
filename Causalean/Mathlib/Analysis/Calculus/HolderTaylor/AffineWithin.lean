module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Affine transfer of intrinsic interval jets

These lemmas transport within-set derivatives from a translated real interval
to the normalized one-dimensional cube. They are the geometric adapter for
fixed-cube Hölder interpolation, including the interval endpoints.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.HolderTaylor

open Causalean.Mathlib.Analysis.Calculus.CubeInterpolation
open Causalean.Mathlib.Analysis.Calculus.CubeExtension
open scoped Pointwise

/-- If [a function f](hyp:f) is [k times continuously differentiable](hyp:k,hf) on [the closed
interval from a to a + d](hyp:a,d) of [positive length](hyp:hd), then [its pullback by the affine
map sending the closed one-dimensional unit cube onto that interval is k times continuously
differentiable on the cube](goal). -/
theorem affine_cube_contDiffOn
    (k : ℕ) (a d : ℝ) (hd : 0 < d) (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ k f (Set.Icc a (a + d))) :
    ContDiffOn ℝ k
      (fun z : Fin 1 → ℝ => f (a + d / 2 + (d / 2) * z 0))
      (cube 1) := by
  have hmap (z : Fin 1 → ℝ) (hz : z ∈ cube 1) :
      a + d / 2 + (d / 2) * z 0 ∈ Set.Icc a (a + d) := by
    have hz0 : z 0 ∈ Set.Icc (-1 : ℝ) 1 := hz 0
    rcases hz0 with ⟨hzlo, hzhi⟩
    constructor <;> nlinarith
  have hinner : ContDiff ℝ k (fun z : Fin 1 → ℝ => a + d / 2 + (d / 2) * z 0) := by
    fun_prop
  exact hf.comp hinner.contDiffOn (fun z hz => hmap z hz)

/-- If [a function f](hyp:f) is [j times continuously differentiable](hyp:j,hf) on [the closed
interval from a to a + d](hyp:a,d) of [positive length](hyp:hd), then at [every point z of the
closed one-dimensional unit cube](hyp:z,hz) and for [every choice of j coordinate
directions](hyp:q), [the order-j within-cube coordinate derivative of the affine pullback of f
equals (d/2)^j times the order-j within-interval derivative of f at the image point](goal). This
includes both endpoints and order zero. -/
theorem affine_cube_coordJetOn
    (j : ℕ) (a d : ℝ) (hd : 0 < d) (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ j f (Set.Icc a (a + d)))
    (q : Fin j → Fin 1) (z : Fin 1 → ℝ) (hz : z ∈ cube 1) :
    coordJetOn (cube 1) j
      (fun w : Fin 1 → ℝ => f (a + d / 2 + (d / 2) * w 0)) q z =
      (d / 2) ^ j *
        iteratedDerivWithin j f (Set.Icc a (a + d))
          (a + d / 2 + (d / 2) * z 0) := by
  let c : ℝ := d / 2
  have hc : 0 < c := by dsimp [c]; linarith
  have hdc : d = 2 * c := by dsimp [c]; ring
  let e₁ := ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ
  let e₂ := (LinearEquiv.smulOfNeZero ℝ ℝ c (ne_of_gt hc)).toContinuousLinearEquiv
  let e := e₁.trans e₂
  let S : Set ℝ := Set.Icc (-c) c
  have he (w : Fin 1 → ℝ) : e w = c * w 0 := by
    simp [e, e₁, e₂, LinearEquiv.smulOfNeZero_apply, smul_eq_mul]
  have hpre : e ⁻¹' S = cube 1 := by
    ext w
    simp only [Set.mem_preimage, he]
    constructor
    · intro hw i
      have hi : i = 0 := Fin.fin_one_eq_zero i
      subst i
      constructor <;> nlinarith [hw.1, hw.2]
    · intro hw
      have hw0 := hw 0
      constructor <;> nlinarith [hw0.1, hw0.2]
  have hshift : (a + c) +ᵥ S = Set.Icc a (a + d) := by
    ext x
    simp only [Set.mem_vadd_set, Set.mem_Icc]
    constructor
    · rintro ⟨y, hy, rfl⟩
      change -c ≤ y ∧ y ≤ c at hy
      simp only [vadd_eq_add]
      constructor <;> nlinarith [hy.1, hy.2, hdc]
    · intro hx
      refine ⟨x - (a + c), ?_, ?_⟩
      · change -c ≤ x - (a + c) ∧ x - (a + c) ≤ c
        constructor <;> nlinarith [hx.1, hx.2, hdc]
      · simp only [vadd_eq_add]
        ring
  have huniq : UniqueDiffOn ℝ S := uniqueDiffOn_Icc (by linarith)
  have hmap : e z ∈ S := by change z ∈ e ⁻¹' S; rw [hpre]; exact hz
  have h₁ := e.iteratedFDerivWithin_comp_right
    (fun x : ℝ => f ((a + c) + x)) huniq hmap j
  have h₂ := iteratedFDerivWithin_comp_add_left (𝕜 := ℝ)
    (f := f) (s := S) j (a + c) (e z)
  have h₃ := congrArg (fun T : (Fin 1 → ℝ) [×j]→L[ℝ] ℝ =>
    T (fun i => Pi.single (q i) (1 : ℝ))) h₁
  rw [h₂] at h₃
  have hedir (i : Fin j) : e (Pi.single (q i) (1 : ℝ)) = c := by
    rw [he]
    simp [Fin.fin_one_eq_zero]
  simpa [coordJetOn, hpre, hshift, Function.comp_def, he, hedir,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    iteratedFDerivWithin_apply_eq_iteratedDerivWithin_mul_prod,
    Finset.prod_const, Fin.fin_one_eq_zero] using h₃

end Causalean.Mathlib.Analysis.Calculus.HolderTaylor
