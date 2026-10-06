module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SharpGammaTaylor

/-! # Arbitrary-order sharp interpolation jet envelopes

One-sided interpolation on the closed horizon bounds all hazard and intensity
jets with the exact Gamma remainder and the declared finite inverse norm.
-/

public section

open MeasureTheory Set
open scoped BigOperators

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The forward grid response is the within-Taylor polynomial. -/
-- @node: interpolationMatrix_mulVec_withinTaylor
lemma interpolationMatrix_mulVec_withinTaylor (k : ℕ) (f : ℝ → ℝ) (x : ℝ)
    (r : Fin (k + 1)) :
    (interpolationMatrix k).mulVec
      (fun j => iteratedDerivWithin j.val f (Icc (0 : ℝ) 1) x) r =
      taylorWithinEval f k (Icc (0 : ℝ) 1) x (x + (r.val : ℝ) / (2 * k)) := by
  rw [taylor_within_apply, ← Fin.sum_univ_eq_sum_range]
  unfold Matrix.mulVec dotProduct interpolationMatrix
  apply Finset.sum_congr rfl
  intro j _
  simp only [smul_eq_mul]
  rw [show x + (r.val : ℝ) / (2 * k) - x = (r.val : ℝ) / (2 * k) by ring]
  ring

/-- Reversing the grid changes only the signs of its Taylor columns. -/
-- @node: interpolationMatrix_backward_mulVec_withinTaylor
lemma interpolationMatrix_backward_mulVec_withinTaylor (k : ℕ) (f : ℝ → ℝ)
    (x : ℝ) (r : Fin (k + 1)) :
    (interpolationMatrix k).mulVec
      (fun j => (-1 : ℝ) ^ j.val *
        iteratedDerivWithin j.val f (Icc (0 : ℝ) 1) x) r =
      taylorWithinEval f k (Icc (0 : ℝ) 1) x (x - (r.val : ℝ) / (2 * k)) := by
  rw [taylor_within_apply, ← Fin.sum_univ_eq_sum_range]
  unfold Matrix.mulVec dotProduct interpolationMatrix
  apply Finset.sum_congr rfl
  intro j _
  simp only [smul_eq_mul]
  rw [show x - (r.val : ℝ) / (2 * k) - x =
    (-1 : ℝ) * ((r.val : ℝ) / (2 * k)) by ring, mul_pow]
  ring

/-- At every order, sharp one-sided Taylor remainders give the paper's exact
inverse-matrix envelope for all within jets. -/
-- @node: sharp_interpolation_jet_bound
lemma sharp_interpolation_jet_bound (k : ℕ) (hk : 0 < k) (f : ℝ → ℝ)
    {α M L : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hf : HolderSeminormLe k α L f)
    (hv : ∀ t ∈ Icc (0 : ℝ) 1, |f t| ≤ M)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (j : Fin (k + 1)) :
    |iteratedDerivWithin j.val f (Icc (0 : ℝ) 1) x| ≤
      interpolationInverseNorm k *
        (M + sharpTaylorRatio α k * L * (2 : ℝ) ^ (-((k : ℝ) + α))) := by
  let v : Fin (k + 1) → ℝ := fun j => iteratedDerivWithin j.val f (Icc (0 : ℝ) 1) x
  let R := sharpTaylorRatio α k * L * (2 : ℝ) ^ (-((k : ℝ) + α))
  have hC : 0 ≤ sharpTaylorRatio α k * L := by
    unfold sharpTaylorRatio
    positivity
  have hR : 0 ≤ R := mul_nonneg hC (Real.rpow_nonneg (by norm_num) _)
  have hpow : (1 / 2 : ℝ) ^ ((k : ℝ) + α) =
      (2 : ℝ) ^ (-((k : ℝ) + α)) := by
    rw [one_div, Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num)]
  have hr {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hd : |t - x| ≤ 1 / 2) :
      |f t - taylorWithinEval f k (Icc (0 : ℝ) 1) x t| ≤ R := by
    refine (sharp_holder_taylor_remainder k f hα hα1 hL hf hx ht).trans ?_
    dsimp [R]
    rw [← hpow]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (abs_nonneg _) hd (by positivity)) hC
  have hgrid (r : Fin (k + 1)) :
      0 ≤ (r.val : ℝ) / (2 * k) ∧ (r.val : ℝ) / (2 * k) ≤ 1 / 2 := by
    have hrk : (r.val : ℝ) ≤ k := by exact_mod_cast (show r.val ≤ k by omega)
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    constructor
    · positivity
    · apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * k)).mpr
      nlinarith
  by_cases hleft : x ≤ 1 / 2
  · let y : Fin (k + 1) → ℝ := fun r => f (x + (r.val : ℝ) / (2 * k))
    have ht (r : Fin (k + 1)) : x + (r.val : ℝ) / (2 * k) ∈ Icc (0 : ℝ) 1 := by
      have := hgrid r
      constructor <;> linarith [hx.1]
    apply interpolationMatrix_jet_bound_of_remainder k hk v y hM hR
      (fun r => hv _ (ht r)) _ j
    intro r
    dsimp only [y, v]
    rw [interpolationMatrix_mulVec_withinTaylor]
    apply hr (ht r)
    rw [show x + (r.val : ℝ) / (2 * k) - x = (r.val : ℝ) / (2 * k) by ring,
      abs_of_nonneg (hgrid r).1]
    exact (hgrid r).2
  · let y : Fin (k + 1) → ℝ := fun r => f (x - (r.val : ℝ) / (2 * k))
    have ht (r : Fin (k + 1)) : x - (r.val : ℝ) / (2 * k) ∈ Icc (0 : ℝ) 1 := by
      have := hgrid r
      constructor <;> linarith [hx.2]
    apply interpolationMatrix_backward_jet_bound_of_remainder k hk v y hM hR
      (fun r => hv _ (ht r)) _ j
    intro r
    dsimp only [y, v]
    rw [interpolationMatrix_backward_mulVec_withinTaylor]
    apply hr (ht r)
    rw [show x - (r.val : ℝ) / (2 * k) - x = -((r.val : ℝ) / (2 * k)) by ring,
      abs_neg, abs_of_nonneg (hgrid r).1]
    exact (hgrid r).2

/-- The sharp interpolation envelope bounds jets uniformly for arbitrary beta. -/
-- @node: derivativeEnvelope_jet_bound
lemma derivativeEnvelope_jet_bound (c : ClassConstants) (f : ℝ → ℝ) {M L : ℝ}
    (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hf : HolderSeminormLe (holderOrder c) (c.beta - holderOrder c) L f)
    (hv : ∀ t ∈ Icc (0 : ℝ) 1, |f t| ≤ M)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (j : Fin (holderOrder c + 1)) :
    |iteratedDerivWithin j.val f (Icc (0 : ℝ) 1) x| ≤ derivativeEnvelope c M L := by
  by_cases hk : holderOrder c = 0
  · have hj : j.val = 0 := by have := j.isLt; omega
    simpa only [derivativeEnvelope, hk, ↓reduceIte, hj, iteratedDerivWithin_zero]
      using hv x hx
  · have hα := holderOrder_remainder_exponent c
    have hb := sharp_interpolation_jet_bound (holderOrder c) (Nat.pos_of_ne_zero hk)
      f hα.1 hα.2 hM hL hf hv hx j
    simpa only [derivativeEnvelope, hk, ↓reduceIte, taylorRatio_eq_sharpTaylorRatio,
      show (holderOrder c : ℝ) + (c.beta - holderOrder c) = c.beta by ring] using hb

/-- Nonnegative value and modulus bounds give a nonnegative jet envelope. -/
-- @node: derivativeEnvelope_nonneg
lemma derivativeEnvelope_nonneg (c : ClassConstants) {M L : ℝ}
    (hM : 0 ≤ M) (hL : 0 ≤ L) : 0 ≤ derivativeEnvelope c M L := by
  unfold derivativeEnvelope
  split
  · exact hM
  · rw [taylorRatio_eq_sharpTaylorRatio]
    have hα := (holderOrder_remainder_exponent c).1
    have hRatio : 0 ≤ sharpTaylorRatio (c.beta - holderOrder c) (holderOrder c) := by
      unfold sharpTaylorRatio
      apply div_nonneg
      · exact (Real.Gamma_pos_of_pos (by linarith)).le
      · exact (Real.Gamma_pos_of_pos (by linarith)).le
    have hInv : 0 ≤ interpolationInverseNorm (holderOrder c) := by
      unfold interpolationInverseNorm
      positivity
    exact mul_nonneg hInv (add_nonneg hM
      (mul_nonneg (mul_nonneg hRatio hL) (Real.rpow_nonneg (by norm_num) _)))

/-- All recurrence intensity jets obey the exact declared envelope. -/
-- @node: recurrence_jet_bound
lemma recurrence_jet_bound (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (j : Fin (holderOrder c + 1)) :
    |iteratedDerivWithin j.val (P.lam a) (Icc (0 : ℝ) 1) x| ≤
      derivativeEnvelope c c.lambdaMax c.Llambda := by
  apply derivativeEnvelope_jet_bound c (P.lam a)
    (c.lambdaMin_pos.le.trans c.lambdaMin_lt.le) c.Llambda_pos.le
    (hP.recurrenceHolder a) _ hx j
  intro t ht
  rw [abs_of_nonneg (c.lambdaMin_pos.le.trans (hP.recurrenceBounds a t ht).1)]
  exact (hP.recurrenceBounds a t ht).2

/-- All death-hazard jets obey the exact declared envelope. -/
-- @node: death_jet_bound
lemma death_jet_bound (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (j : Fin (holderOrder c + 1)) :
    |iteratedDerivWithin j.val (P.hazard a) (Icc (0 : ℝ) 1) x| ≤
      derivativeEnvelope c c.dMax c.Ld := by
  apply derivativeEnvelope_jet_bound c (P.hazard a)
    (c.dMin_pos.le.trans c.dMin_lt.le) c.Ld_pos.le
    (hP.deathHolder a) _ hx j
  intro t ht
  rw [abs_of_nonneg (c.dMin_pos.le.trans (hP.deathBounds a t ht).1)]
  exact (hP.deathBounds a t ht).2

/-- Lower jets inherit a Holder modulus from the next bounded jet, while
 the top jet retains the model's stated modulus. -/
-- @node: derivativeHolderEnvelope_modulus
lemma derivativeHolderEnvelope_modulus (c : ClassConstants) (f : ℝ → ℝ) {M L : ℝ}
    (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hf : HolderSeminormLe (holderOrder c) (c.beta - holderOrder c) L f)
    (hv : ∀ t ∈ Icc (0 : ℝ) 1, |f t| ≤ M)
    (j : Fin (holderOrder c + 1)) {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    |iteratedDerivWithin j.val f (Icc (0 : ℝ) 1) x -
      iteratedDerivWithin j.val f (Icc (0 : ℝ) 1) y| ≤
      derivativeHolderEnvelope c M L j.val * |x - y| ^ (c.beta - holderOrder c) := by
  by_cases hj : j.val < holderOrder c
  · have hα := holderOrder_remainder_exponent c
    have hc : ContDiffOn ℝ (j.val + 1 : ℕ) f (Icc (0 : ℝ) 1) :=
      hf.1.of_le (by exact_mod_cast (show j.val + 1 ≤ holderOrder c by omega))
    have h := Causalean.Mathlib.Analysis.Calculus.HolderTaylor.lower_jet_holder_of_next_bound
      j.val (c.beta - holderOrder c) 0 1 (derivativeEnvelope c M L) hα.1 hα.2
      (by norm_num) (derivativeEnvelope_nonneg c hM hL) f
      (by simpa using hc)
      (by
        intro t ht
        simpa using derivativeEnvelope_jet_bound c f hM hL hf hv
          (by simpa using ht) ⟨j.val + 1, by omega⟩)
      x (by simpa using hx) y (by simpa using hy)
    simpa only [derivativeHolderEnvelope, hj, ↓reduceIte,
      zero_add, Real.one_rpow, mul_one] using h
  · have he : j.val = holderOrder c := by have := j.isLt; omega
    simpa only [derivativeHolderEnvelope, he, lt_self_iff_false, ↓reduceIte]
      using hf.2 x hx y hy

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
