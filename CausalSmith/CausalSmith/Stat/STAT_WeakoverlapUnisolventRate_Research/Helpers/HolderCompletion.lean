module
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.Completion
public import Causalean.Mathlib.Analysis.Calculus.CubeExtension.Affine
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.Counts
public import Causalean.Stat.Nonparametric.Approximation.Holder.CubeExtension
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.Witnesses

/-! # Fixed-cube completion of Dorn's Hölder seminorm

The source class supplies only an intrinsic top-order seminorm. The completion
and affine transport are performed on the closed cubes using within-cube jets.
-/
public section
namespace CausalSmith.Stat.WeakOverlap

open Causalean.Mathlib.Analysis.Calculus.CubeExtension
open Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

-- @node: lem:fixed-cube-holder-completion
/-- A response sup bound and Dorn's top-derivative seminorm control the full
intrinsic Hölder radius after affine scaling. The constant depends on dimension
and smoothness alone. [For the stated inputs and conditions](hyp:d,hd,β,hβ), [the asserted conclusion holds](goal). -/
lemma fixedCube_holder_completion (d : ℕ) (hd : 1 ≤ d) (β : ℝ) (hβ : 1 < β) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (M₀ L₀ : ℝ) (u : (Fin d → ℝ) → ℝ),
        0 ≤ M₀ → 0 ≤ L₀ →
        DornTopDerivativeSeminorm β L₀ u →
        (∀ x ∈ dornCube d, |u x| ≤ M₀) →
        HolderBall β (K * (M₀ + L₀))
          (fun x : Fin d → ℝ => u (fun i => 2 * x i - 1)) := by
  let m : ℕ := polynomialDegree β
  let s : ℝ := β - (m : ℝ)
  have hs : 0 < s := by
    dsimp [s, m, polynomialDegree]
    have hceil : 1 ≤ ⌈β⌉₊ := Nat.one_le_ceil_iff.mpr (by linarith)
    rw [Nat.cast_sub hceil, Nat.cast_one]
    linarith [Nat.ceil_lt_add_one (by linarith : 0 ≤ β)]
  have hs1 : s ≤ 1 := by
    dsimp [s, m, polynomialDegree]
    have hceil : 1 ≤ ⌈β⌉₊ := Nat.one_le_ceil_iff.mpr (by linarith)
    rw [Nat.cast_sub hceil, Nat.cast_one]
    linarith [Nat.le_ceil β]
  obtain ⟨K₀, hK₀, hcomplete⟩ := cube_holder_completion d m s hs
  obtain ⟨K₁, hK₁, haffine⟩ := cube_holder_affine_transport d m s hs1
  let C : ℝ := (Real.sqrt d) ^ s
  have hC : 0 < C := by
    dsimp [C]
    exact Real.rpow_pos_of_pos (Real.sqrt_pos.2 (by exact_mod_cast hd)) _
  let K : ℝ := K₁ * K₀ * (C + 1)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro M₀ L₀ u hM hL hu hbound
  have hcube : Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.cube d =
      dornCube d := by
    ext x
    change (∀ i, x i ∈ Set.Icc (-1 : ℝ) 1) ↔
      x ∈ Set.univ.pi (fun _ => Set.Icc (-1 : ℝ) 1)
    exact ⟨fun hx => Set.mem_univ_pi.mpr hx, fun hx => Set.mem_univ_pi.mp hx⟩
  have hunit : unitCube d = cube d := rfl
  have htop : TopHolderOn (Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.cube d)
      m s (C * L₀) u := by
    intro f x hx y hy
    rw [hcube]
    let α : Fin d → ℕ := fun i => coordCount f i
    have hsum : (∑ i, α i) = m := sum_coordCount f
    let P : ℕ → Prop := fun j =>
      ∀ g : Fin j → Fin d,
        (∀ i, (Finset.univ.filter (fun k => g k = i)).card = α i) →
        |coordJetOn (dornCube d) j u g x -
          coordJetOn (dornCube d) j u g y| ≤
          L₀ * (Real.sqrt (∑ i, (x i - y i) ^ 2)) ^ s
    have hP : P (∑ i, α i) := by
      intro g hg
      have hm : (∑ i, α i) = polynomialDegree β := hsum
      have h := hu.2 α hm g hg x (hcube ▸ hx) y (hcube ▸ hy)
      simpa only [s, m] using h
    have hsource : |coordJetOn (dornCube d) m u f x -
        coordJetOn (dornCube d) m u f y| ≤
        L₀ * (Real.sqrt (∑ i, (x i - y i) ^ 2)) ^ s :=
      (hsum ▸ hP) f (by intro i; rfl)
    have hsq : (∑ i : Fin d, (x i - y i) ^ 2) ≤
        (d : ℝ) * ‖x - y‖ ^ 2 := by
      calc
        _ ≤ ∑ _i : Fin d, ‖x - y‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          have hi := norm_le_pi_norm (x - y) i
          simpa only [Pi.sub_apply, Real.norm_eq_abs, sq_abs] using
            ((sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).2 hi)
        _ = (d : ℝ) * ‖x - y‖ ^ 2 := by simp
    have hdist : Real.sqrt (∑ i : Fin d, (x i - y i) ^ 2) ≤
        Real.sqrt d * ‖x - y‖ := by
      calc
        _ ≤ Real.sqrt ((d : ℝ) * ‖x - y‖ ^ 2) := Real.sqrt_le_sqrt hsq
        _ = Real.sqrt d * ‖x - y‖ := by
          rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ d), Real.sqrt_sq_eq_abs]
          simp
    have hpow : (Real.sqrt (∑ i : Fin d, (x i - y i) ^ 2)) ^ s ≤
        C * ‖x - y‖ ^ s := by
      calc
        _ ≤ (Real.sqrt d * ‖x - y‖) ^ s :=
          Real.rpow_le_rpow (Real.sqrt_nonneg _) hdist hs.le
        _ = _ := by rw [Real.mul_rpow (Real.sqrt_nonneg _) (norm_nonneg _)]
    exact hsource.trans (by
      calc
        L₀ * (Real.sqrt (∑ i : Fin d, (x i - y i) ^ 2)) ^ s ≤
            L₀ * (C * ‖x - y‖ ^ s) := mul_le_mul_of_nonneg_left hpow hL
        _ = C * L₀ * ‖x - y‖ ^ s := by ring)
  have hball : CubeHolderBall d m s (K₀ * (M₀ + C * L₀)) u := by
    apply hcomplete u M₀ (C * L₀) hM (mul_nonneg hC.le hL)
    · simpa only [m, hcube] using hu.1
    · simpa only [hcube] using hbound
    · exact htop
  have htransport := haffine u (K₀ * (M₀ + C * L₀))
    (mul_nonneg hK₀.le (add_nonneg hM (mul_nonneg hC.le hL))) hball
  have hscale : M₀ + C * L₀ ≤ (C + 1) * (M₀ + L₀) := by
    nlinarith [mul_nonneg hC.le hM]
  have hR : K₁ * (K₀ * (M₀ + C * L₀)) ≤ K * (M₀ + L₀) := by
    dsimp [K]
    nlinarith [mul_nonneg hK₀.le (sub_nonneg.mpr hscale),
      mul_nonneg hK₁.le (mul_nonneg hK₀.le (sub_nonneg.mpr hscale))]
  have horder : ((polynomialDegree β : ℕ) : WithTop ℕ∞) =
      (⌈β⌉₊ : WithTop ℕ∞) - 1 := by
    simp only [polynomialDegree]
    norm_cast
  refine ⟨?_, ?_, ?_⟩
  · rw [← horder]
    have hreg : ContDiffOn ℝ (polynomialDegree β)
        (fun x => u (Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.cubeAffine x))
        (cube d) := htransport.regularity
    have hfun : (fun x : Fin d → ℝ =>
        u (Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.cubeAffine x)) =
        (fun x : Fin d → ℝ => u (fun i => 2 * x i - 1)) := by
      rfl
    rw [hfun] at hreg
    exact hreg
  · intro j hj f x hx
    exact (htransport.derivBound j hj f x (hunit.symm ▸ hx)).trans hR
  · intro f x hx y hy
    exact (htransport.modulus f x (hunit.symm ▸ hx) y (hunit.symm ▸ hy)).trans
      (mul_le_mul_of_nonneg_right hR (Real.rpow_nonneg (norm_nonneg _) _))

end CausalSmith.Stat.WeakOverlap
