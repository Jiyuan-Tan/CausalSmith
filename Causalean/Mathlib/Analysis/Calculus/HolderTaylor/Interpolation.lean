module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.Completion
public import Causalean.Mathlib.Analysis.Calculus.HolderTaylor.AffineHolder
public import Causalean.Mathlib.Analysis.Calculus.HolderTaylor.AmbientGrid
public import Causalean.Mathlib.Analysis.Calculus.HolderTaylor.BoundaryTransfer
public import Causalean.Mathlib.Analysis.Calculus.HolderTaylor.BoundedTopGrid
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.Taylor

/-!
# Uniform derivative bounds from a top Hölder modulus

Finite-interval interpolation for scalar functions, stated directly in terms of
`ContDiffOn` and `iteratedDerivWithin`. The constant is uniform under translation
of an interval of fixed positive length.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.HolderTaylor

open Causalean.Mathlib.Analysis.Calculus.CubeInterpolation
open Causalean.Mathlib.Analysis.Calculus.CubeExtension

/-- Fix [a derivative order k](hyp:k), [a Hölder exponent α](hyp:α) with [α positive](hyp:hα),
[an interval length d](hyp:d) that is [positive](hyp:hd), and
[a nonnegative value envelope M](hyp:M,hM) and [a nonnegative Hölder constant L](hyp:L,hL). Then
[there is one nonnegative constant B such that, for every interval from a to a + d and every
function f that is k times continuously differentiable on it, bounded by M there, and whose k-th
within-interval derivative is Hölder with constant L and exponent α there, that k-th derivative
is bounded by B on the whole interval](goal). The bound is independent of the interval location
and the function. -/
theorem uniform_top_iteratedDerivWithin_bound
    (k : ℕ) (α d M L : ℝ) (hα : 0 < α)
    (hd : 0 < d) (hM : 0 ≤ M) (hL : 0 ≤ L) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (a : ℝ) (f : ℝ → ℝ),
        ContDiffOn ℝ k f (Set.Icc a (a + d)) →
        (∀ x ∈ Set.Icc a (a + d), |f x| ≤ M) →
        (∀ x ∈ Set.Icc a (a + d), ∀ y ∈ Set.Icc a (a + d),
          |iteratedDerivWithin k f (Set.Icc a (a + d)) x -
            iteratedDerivWithin k f (Set.Icc a (a + d)) y| ≤
              L * |x - y| ^ α) →
        ∀ x ∈ Set.Icc a (a + d),
          |iteratedDerivWithin k f (Set.Icc a (a + d)) x| ≤ B := by
  obtain ⟨K, hK, hfixed⟩ := fixed_cube_interpolation_within
    1 k α hα
  let c : ℝ := d / 2
  have hc : 0 < c := by dsimp [c]; linarith
  let R : ℝ := K * (M + L * c ^ k * c ^ α)
  let B : ℝ := R / c ^ k
  have hR : 0 ≤ R := by dsimp [R]; positivity
  refine ⟨B, div_nonneg hR (pow_nonneg hc.le _), ?_⟩
  intro a f hf hval hholder x hx
  let u : (Fin 1 → ℝ) → ℝ := fun z => f (a + c + c * z 0)
  have hmap (z : Fin 1 → ℝ) (hz : z ∈ cube 1) :
      a + c + c * z 0 ∈ Set.Icc a (a + d) := by
    have hz0 := hz 0
    dsimp [c] at *
    constructor <;> nlinarith [hz0.1, hz0.2]
  have hu : ContDiffOn ℝ k u (cube 1) := by
    simpa [u, c] using affine_cube_contDiffOn k a d hd f hf
  have hval' : ∀ z ∈ cube 1, |u z| ≤ M := by
    intro z hz
    exact hval _ (hmap z hz)
  have hL' : 0 ≤ L * c ^ k * c ^ α := by positivity
  have hholder' : TopHolderOn (cube 1) k α (L * c ^ k * c ^ α) u := by
    simpa [u, c] using affine_cube_topHolderOn k α a d L hd f hholder
  let z : Fin 1 → ℝ := fun _ => (x - a - c) / c
  have hz : z ∈ cube 1 := by
    intro i
    have hi : i = 0 := Fin.fin_one_eq_zero i
    subst i
    change -1 ≤ (x - a - c) / c ∧ (x - a - c) / c ≤ 1
    constructor
    · apply (le_div_iff₀ hc).2
      dsimp [c]
      nlinarith [hx.1]
    · apply (div_le_iff₀ hc).2
      dsimp [c]
      nlinarith [hx.2]
  have heq : a + c + c * z 0 = x := by
    dsimp [z]
    field_simp
    ring
  have hbound := hfixed u M (L * c ^ k * c ^ α) hM hL' hu hval' hholder'
    k (le_refl k) (fun _ => (0 : Fin 1)) z hz
  rw [affine_cube_coordJetOn k a d hd f (fun _ => (0 : Fin 1)) z hz] at hbound
  change |c ^ k * iteratedDerivWithin k f (Set.Icc a (a + d))
    (a + c + c * z 0)| ≤ R at hbound
  rw [heq, abs_mul, abs_of_pos (pow_pos hc _)] at hbound
  change |iteratedDerivWithin k f (Set.Icc a (a + d)) x| ≤
    R / c ^ k
  apply (le_div_iff₀ (pow_pos hc _)).2
  nlinarith [hbound]

/-- Fix [a derivative order k](hyp:k), [an interval length d](hyp:d) that is [positive](hyp:hd),
[a nonnegative value envelope M](hyp:M,hM) and [a nonnegative top-derivative envelope
T](hyp:T,hT). Then [there is one nonnegative constant B such that, for every interval from a to
a + d and every function f that is k times continuously differentiable on it, bounded by M there,
and whose k-th within-interval derivative is bounded by T there, every within-interval derivative
of f of order at most k is bounded by B on the whole interval](goal), endpoints included. -/
theorem uniform_lower_iteratedDerivWithin_of_top_bound
    (k : ℕ) (d M T : ℝ) (hd : 0 < d) (hM : 0 ≤ M) (hT : 0 ≤ T) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (a : ℝ) (f : ℝ → ℝ),
        ContDiffOn ℝ k f (Set.Icc a (a + d)) →
        (∀ x ∈ Set.Icc a (a + d), |f x| ≤ M) →
        (∀ x ∈ Set.Icc a (a + d),
          |iteratedDerivWithin k f (Set.Icc a (a + d)) x| ≤ T) →
    ∀ j ≤ k, ∀ x ∈ Set.Icc a (a + d),
          |iteratedDerivWithin j f (Set.Icc a (a + d)) x| ≤ B := by
  obtain ⟨B, hB, hinterior⟩ :=
    uniform_interior_ambient_jet_bound_of_top_bound k d M T hd hM hT
  refine ⟨B, hB, ?_⟩
  intro a f hf hval htop
  exact within_jet_bound_of_interior_ambient_bound k a (a + d) B
    (by linarith) f hf (hinterior a f hf hval htop)

/-- Fix [a derivative order k](hyp:k), [a Hölder exponent α](hyp:α) with [α positive](hyp:hα),
[an interval length d](hyp:d) that is [positive](hyp:hd), and
[a nonnegative value envelope M](hyp:M,hM) and [a nonnegative Hölder constant L](hyp:L,hL). Then
[there is one nonnegative constant B such that, for every interval from a to a + d and every
function f that is k times continuously differentiable on it, bounded by M there, and whose k-th
within-interval derivative is Hölder with constant L and exponent α there, every within-interval
derivative of f of order at most k is bounded by B on the whole interval](goal). -/
theorem uniform_iteratedDerivWithin_bound
    (k : ℕ) (α d M L : ℝ) (hα : 0 < α)
    (hd : 0 < d) (hM : 0 ≤ M) (hL : 0 ≤ L) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (a : ℝ) (f : ℝ → ℝ),
        ContDiffOn ℝ k f (Set.Icc a (a + d)) →
        (∀ x ∈ Set.Icc a (a + d), |f x| ≤ M) →
        (∀ x ∈ Set.Icc a (a + d), ∀ y ∈ Set.Icc a (a + d),
          |iteratedDerivWithin k f (Set.Icc a (a + d)) x -
            iteratedDerivWithin k f (Set.Icc a (a + d)) y| ≤
              L * |x - y| ^ α) →
        ∀ j ≤ k, ∀ x ∈ Set.Icc a (a + d),
          |iteratedDerivWithin j f (Set.Icc a (a + d)) x| ≤ B := by
  obtain ⟨T, hT, htop⟩ :=
    uniform_top_iteratedDerivWithin_bound k α d M L hα hd hM hL
  obtain ⟨B, hB, hbound⟩ :=
    uniform_lower_iteratedDerivWithin_of_top_bound k d M T hd hM hT
  exact ⟨B, hB, fun a f hf hM' hL' =>
    hbound a f hf hM' (htop a f hf hM' hL')⟩

end Causalean.Mathlib.Analysis.Calculus.HolderTaylor
