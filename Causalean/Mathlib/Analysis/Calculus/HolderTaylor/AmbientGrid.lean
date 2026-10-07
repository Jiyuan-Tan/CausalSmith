module
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.Interpolation
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Interior interpolation from ambient Hölder data

This one-dimensional adapter isolates the finite-grid estimate behind interval
interpolation. It uses ambient derivatives only at points where the function is
smooth in a neighborhood. The later local-window bridge applies it to within
derivative data without imposing ambient regularity at the original endpoints.
-/

public section

namespace Causalean.Mathlib.Analysis.Calculus.HolderTaylor

private lemma coordPartial_finOne_eq_iteratedDeriv
    (j : ℕ) (f : ℝ → ℝ) (x : Fin 1 → ℝ) (q : Fin j → Fin 1) :
    Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.coordPartial j
      (fun z : Fin 1 → ℝ => f (z 0)) q x = iteratedDeriv j f (x 0) := by
  let e := ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ
  have h := e.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ
    (Set.mem_univ (e x)) j
  simp only [iteratedFDerivWithin_univ, Set.preimage_univ] at h
  have h' := congrArg (fun T : (Fin 1 → ℝ) [×j]→L[ℝ] ℝ =>
    T (fun i => Pi.single (q i) (1 : ℝ))) h
  simpa [Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.coordPartial,
    e, Function.comp_def, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    Pi.single_apply, Fin.fin_one_eq_zero,
    iteratedDeriv_eq_iteratedFDeriv] using h'

private lemma iteratedDeriv_comp_mul_nonzero
    (n : ℕ) (f : ℝ → ℝ) (c : ℝ) (hc : c ≠ 0) (x : ℝ) :
    iteratedDeriv n (fun t => f (c * t)) x =
      c ^ n * iteratedDeriv n f (c * x) := by
  let e := (LinearEquiv.smulOfNeZero ℝ ℝ c hc).toContinuousLinearEquiv
  have h := e.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ
    (Set.mem_univ (e x)) n
  simp only [iteratedFDerivWithin_univ, Set.preimage_univ] at h
  have h' := congrArg (fun T : ℝ [×n]→L[ℝ] ℝ => T (fun _ => 1)) h
  simpa [e, Function.comp_def, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, Finset.prod_const,
    LinearEquiv.smulOfNeZero_apply, smul_eq_mul] using h'

private lemma iteratedDeriv_comp_affine_nonzero
    (n : ℕ) (f : ℝ → ℝ) (a c : ℝ) (hc : c ≠ 0) (x : ℝ) :
    iteratedDeriv n (fun t => f (a + c * t)) x =
      c ^ n * iteratedDeriv n f (a + c * x) := by
  have h := iteratedDeriv_comp_mul_nonzero n (fun t => f (a + t)) c hc x
  rw [iteratedDeriv_comp_const_add] at h
  exact h

/-- Fix [a derivative order k](hyp:k), [a Hölder exponent α](hyp:α) with [α positive](hyp:hα),
[an interval length d](hyp:d) that is [positive](hyp:hd), and
[a nonnegative value envelope M](hyp:M,hM) and [a nonnegative Hölder constant L](hyp:L,hL). Then
[there is one nonnegative constant B such that, for every interval from a to a + d and every
function f that is k times continuously differentiable on it, bounded by M there, and whose
ambient k-th derivative is Hölder with constant L and exponent α there, every ambient derivative
of f of order at most k is bounded by B at the interior points](goal). This includes order zero.
-/
theorem uniform_interior_ambient_jet_bound
    (k : ℕ) (α d M L : ℝ) (hα : 0 < α)
    (hd : 0 < d) (hM : 0 ≤ M) (hL : 0 ≤ L) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (a : ℝ) (f : ℝ → ℝ),
        ContDiffOn ℝ k f (Set.Icc a (a + d)) →
        (∀ x ∈ Set.Icc a (a + d), |f x| ≤ M) →
        (∀ x ∈ Set.Icc a (a + d), ∀ y ∈ Set.Icc a (a + d),
          |iteratedDeriv k f x - iteratedDeriv k f y| ≤
            L * |x - y| ^ α) →
        ∀ j ≤ k, ∀ x ∈ Set.Ioo a (a + d),
          |iteratedDeriv j f x| ≤ B := by
  let c : ℝ := d / 2
  have hc : 0 < c := by dsimp [c]; linarith
  have hdc : d = 2 * c := by dsimp [c]; ring
  obtain ⟨K, hK, hfixed⟩ :=
    Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.fixed_cube_interpolation
      1 k α hα
  let R : ℝ := K * (M + L * c ^ k * c ^ α)
  let B : ℝ := ∑ j ∈ Finset.range (k + 1), R / c ^ j
  have hR : 0 ≤ R := by dsimp [R]; positivity
  refine ⟨B, Finset.sum_nonneg (fun j hj => div_nonneg hR (pow_nonneg hc.le _)), ?_⟩
  intro a f hf hval hholder j hj x hx
  let u : (Fin 1 → ℝ) → ℝ := fun z => f (a + c + c * z 0)
  have hmap (z : Fin 1 → ℝ)
      (hz : z ∈ Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.cube 1) :
      a + c + c * z 0 ∈ Set.Icc a (a + d) := by
    have hz0 : z 0 ∈ Set.Icc (-1 : ℝ) 1 := hz 0
    rcases hz0 with ⟨hzlo, hzhi⟩
    constructor <;> nlinarith [hdc]
  have hreg : ContDiffOn ℝ k u
      (Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.cube 1) := by
    have hinner : ContDiff ℝ k (fun z : Fin 1 → ℝ => a + c + c * z 0) := by fun_prop
    exact hf.comp hinner.contDiffOn (fun z hz => hmap z hz)
  have hjet (i : ℕ) (q : Fin i → Fin 1) (z : Fin 1 → ℝ) :
      Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.coordPartial i u q z =
        c ^ i * iteratedDeriv i f (a + c + c * z 0) := by
    exact (coordPartial_finOne_eq_iteratedDeriv i
      (fun t => f (a + c + c * t)) z q).trans
        (iteratedDeriv_comp_affine_nonzero i f (a + c) c (ne_of_gt hc) (z 0))
  have hval' : ∀ z ∈ Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.cube 1,
      |u z| ≤ M := by
    intro z hz
    exact hval _ (hmap z hz)
  have hholder' :
      Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.TopHolder
        1 k α (L * c ^ k * c ^ α) u := by
    intro q z hz w hw
    have hdist : |(a + c + c * z 0) - (a + c + c * w 0)| ≤ c * ‖z - w‖ := by
      calc
        _ = c * |z 0 - w 0| := by
          rw [show (a + c + c * z 0) - (a + c + c * w 0) =
            c * (z 0 - w 0) by ring, abs_mul, abs_of_pos hc]
        _ ≤ c * ‖z - w‖ := by
          apply mul_le_mul_of_nonneg_left _ hc.le
          simpa [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (z - w) 0
    have hpow : |(a + c + c * z 0) - (a + c + c * w 0)| ^ α ≤
        c ^ α * ‖z - w‖ ^ α := by
      calc
        _ ≤ (c * ‖z - w‖) ^ α :=
          Real.rpow_le_rpow (abs_nonneg _) hdist hα.le
        _ = c ^ α * ‖z - w‖ ^ α := Real.mul_rpow hc.le (norm_nonneg _)
    rw [hjet k q z, hjet k q w, ← mul_sub, abs_mul, abs_of_nonneg (pow_nonneg hc.le _)]
    calc
      c ^ k * |iteratedDeriv k f (a + c + c * z 0) -
          iteratedDeriv k f (a + c + c * w 0)| ≤
          c ^ k * (L * |(a + c + c * z 0) - (a + c + c * w 0)| ^ α) :=
        mul_le_mul_of_nonneg_left
          (hholder _ (hmap z hz) _ (hmap w hw)) (pow_nonneg hc.le _)
      _ ≤ c ^ k * (L * (c ^ α * ‖z - w‖ ^ α)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hpow hL) (pow_nonneg hc.le _)
      _ = (L * c ^ k * c ^ α) * ‖z - w‖ ^ α := by ring
  have hbound := hfixed u M (L * c ^ k * c ^ α) hM (by positivity)
    hreg hval' hholder'
  let z : Fin 1 → ℝ := fun _ => (x - (a + c)) / c
  have hz : z ∈ Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.cube 1 := by
    intro i
    have hi : i = 0 := Subsingleton.elim i 0
    subst i
    change -1 ≤ (x - (a + c)) / c ∧ (x - (a + c)) / c ≤ 1
    constructor
    · apply (le_div_iff₀ hc).2
      nlinarith [hx.1, hx.2]
    · apply (div_le_iff₀ hc).2
      nlinarith [hx.1, hx.2]
  have hzx : a + c + c * z 0 = x := by
    dsimp [z]
    field_simp
    ring
  have hjbound := hbound j hj (fun _ => 0) z hz
  rw [hjet j (fun _ => 0) z, hzx] at hjbound
  have hsmall : |iteratedDeriv j f x| ≤ R / c ^ j := by
    apply (le_div_iff₀ (pow_pos hc j)).2
    simpa [abs_mul, abs_of_nonneg (pow_nonneg hc.le _), R, mul_comm] using hjbound
  exact hsmall.trans (Finset.single_le_sum
    (fun i _ => div_nonneg hR (pow_nonneg hc.le i)) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)))

end Causalean.Mathlib.Analysis.Calculus.HolderTaylor
