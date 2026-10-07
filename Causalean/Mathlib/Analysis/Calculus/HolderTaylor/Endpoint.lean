module
public import Mathlib.Analysis.Calculus.Taylor

/-!
# Endpoint Taylor remainder from a top Hölder modulus

The endpoint result needs only within-interval regularity; its coefficients
are chosen separately for each function and its constant is uniform over all
translated intervals of the same length.
-/

public section

open scoped BigOperators Topology
open Filter

namespace Causalean.Mathlib.Analysis.Calculus.HolderTaylor

/-- Fix [a derivative order k](hyp:k), [a Hölder exponent α](hyp:α) with [α positive](hyp:hα),
[an interval length d](hyp:d) that is [positive](hyp:hd), and
[a nonnegative Hölder constant L](hyp:L,hL). Then [there is one nonnegative constant C such
that every function f that is k times continuously differentiable on an interval from a to a + d,
with k-th within-interval derivative Hölder with constant L and exponent α there, has a polynomial
of degree at most k in the distance a + d − t to the right endpoint whose error at every point t
of the interval is at most C times that distance to the power k + α](goal). The polynomial
coefficients may depend on f; this includes k = 0. -/
theorem endpoint_holder_taylor
    (k : ℕ) (α d L : ℝ) (hα : 0 < α)
    (hd : 0 < d) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (a : ℝ) (f : ℝ → ℝ),
        ContDiffOn ℝ k f (Set.Icc a (a + d)) →
        (∀ x ∈ Set.Icc a (a + d), ∀ y ∈ Set.Icc a (a + d),
          |iteratedDerivWithin k f (Set.Icc a (a + d)) x -
            iteratedDerivWithin k f (Set.Icc a (a + d)) y| ≤
              L * |x - y| ^ α) →
        ∃ coeff : Fin (k + 1) → ℝ,
          ∀ t ∈ Set.Icc a (a + d),
            |f t - ∑ j : Fin (k + 1), coeff j * (a + d - t) ^ j.val| ≤
              C * (a + d - t) ^ ((k : ℝ) + α) := by
  refine ⟨L, hL, ?_⟩
  intro a f hf hholder
  let b := a + d
  let s := Set.Icc a b
  let coeff : Fin (k + 1) → ℝ := fun j =>
    (Nat.factorial j.val : ℝ)⁻¹ * iteratedDerivWithin j.val f s b * (-1 : ℝ) ^ j.val
  refine ⟨coeff, ?_⟩
  intro t ht
  have hab : a < b := by dsimp [b]; linarith
  have htb : t ≤ b := ht.2
  have hpow (j : ℕ) : (t - b) ^ j = (-1 : ℝ) ^ j * (b - t) ^ j := by
    rw [show t - b = (-1 : ℝ) * (b - t) by ring, mul_pow]
  have hpoly :
      (∑ j : Fin (k + 1), coeff j * (b - t) ^ j.val) =
        ∑ j ∈ Finset.range (k + 1),
          (Nat.factorial j : ℝ)⁻¹ * iteratedDerivWithin j f s b * (t - b) ^ j := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [coeff]
    rw [hpow]
    ring
  rw [hpoly]
  by_cases hzero : k = 0
  · subst k
    simp only [Finset.range_one, Finset.sum_singleton, Nat.factorial_zero,
      Nat.cast_one, inv_one, iteratedDerivWithin_zero, pow_zero, mul_one,
      one_mul, Nat.cast_zero, zero_add]
    have h := hholder t ht b (Set.right_mem_Icc.mpr hab.le)
    simpa [abs_of_nonpos (sub_nonpos.mpr htb), s, b] using h
  have hk : 0 < k := Nat.pos_of_ne_zero hzero
  have hexp : 0 < (k : ℝ) + α := by positivity
  by_cases hteq : t = b
  · subst t
    have hsum :
        (∑ j ∈ Finset.range (k + 1),
          (Nat.factorial j : ℝ)⁻¹ * iteratedDerivWithin j f s b * (b - b) ^ j) = f b := by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro j hj hj0
        simp [hj0]
      · simp
    rw [hsum]
    simpa [b] using (mul_nonneg hL (Real.rpow_nonneg (sub_nonneg.mpr htb) _))
  have hlt : t < b := lt_of_le_of_ne htb hteq
  have hseg : Set.Icc t b ⊆ s := by
    intro z hz
    exact ⟨ht.1.trans hz.1, hz.2⟩
  have hlocal : s =ᶠ[𝓝 b] Set.Icc t b := by
    filter_upwards [Ioi_mem_nhds hlt] with z hz
    change (a ≤ z ∧ z ≤ b) = (t ≤ z ∧ z ≤ b)
    change t < z at hz
    exact propext (by
      constructor
      · intro h
        exact ⟨hz.le, h.2⟩
      · intro h
        exact ⟨ht.1.trans h.1, h.2⟩)
  have hbase (j : ℕ) :
      iteratedDerivWithin j f (Set.Icc t b) b = iteratedDerivWithin j f s b := by
    rw [iteratedDerivWithin_eq_iteratedFDerivWithin,
      iteratedDerivWithin_eq_iteratedFDerivWithin,
      iteratedFDerivWithin_congr_set (f := f) hlocal.symm]
  let n := k - 1
  have hn : n + 1 = k := Nat.succ_pred_eq_of_pos hk
  have hcont : ContDiffOn ℝ (n + 1) f (Set.uIcc b t) := by
    change ContDiffOn ℝ (↑(n + 1 : ℕ)) f (Set.uIcc b t)
    rw [Set.uIcc_of_ge htb, hn]
    exact hf.mono hseg
  obtain ⟨ξ, hξ, hrem⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (f := f) (x := t) (x₀ := b)
      (n := n) (Ne.symm hteq) hcont
  have hξmem : ξ ∈ s := by
    apply hseg
    rw [Set.uIoo_of_ge htb] at hξ
    exact ⟨hξ.1.le, hξ.2.le⟩
  have hξderiv : iteratedDeriv k f ξ = iteratedDerivWithin k f s ξ := by
    have hξint : ξ ∈ Set.Ioo a b := by
      rw [Set.uIoo_of_ge htb] at hξ
      exact ⟨ht.1.trans_lt hξ.1, hξ.2⟩
    exact (iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab)
      (hf.contDiffAt (Icc_mem_nhds hξint.1 hξint.2)) hξmem).symm
  have hξdist : |ξ - b| ≤ |t - b| := by
    rw [Set.uIoo_of_ge htb] at hξ
    rw [abs_of_nonpos (sub_nonpos.mpr hξ.2.le),
      abs_of_nonpos (sub_nonpos.mpr htb)]
    linarith [hξ.1]
  have htop : |iteratedDeriv k f ξ - iteratedDerivWithin k f s b| ≤
      L * |t - b| ^ α := by
    rw [hξderiv]
    exact (hholder ξ hξmem b (Set.right_mem_Icc.mpr hab.le)).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (abs_nonneg _) hξdist hα.le) hL)
  have hpolyN : taylorWithinEval f n (Set.uIcc b t) b t =
      ∑ j ∈ Finset.range (n + 1),
        (Nat.factorial j : ℝ)⁻¹ * iteratedDerivWithin j f s b * (t - b) ^ j := by
    rw [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Set.uIcc_of_ge htb, hbase]
    simp only [smul_eq_mul]
    ring
  have hdiff :
      f t - (∑ j ∈ Finset.range (k + 1),
        (Nat.factorial j : ℝ)⁻¹ * iteratedDerivWithin j f s b * (t - b) ^ j) =
      (iteratedDeriv k f ξ - iteratedDerivWithin k f s b) /
        (Nat.factorial k : ℝ) * (t - b) ^ k := by
    rw [← hn, Finset.sum_range_succ, ← hpolyN, sub_add_eq_sub_sub, hrem, hn]
    ring
  rw [hdiff]
  have hfac : 1 ≤ (Nat.factorial k : ℝ) := by
    exact_mod_cast Nat.factorial_pos k
  have hdistpos : 0 < |t - b| := abs_pos.mpr (sub_ne_zero.mpr hteq)
  calc
    |(iteratedDeriv k f ξ - iteratedDerivWithin k f s b) /
        (Nat.factorial k : ℝ) * (t - b) ^ k| =
      |iteratedDeriv k f ξ - iteratedDerivWithin k f s b| /
        (Nat.factorial k : ℝ) * |t - b| ^ k := by
          rw [abs_mul, abs_div, abs_pow, abs_of_nonneg (by linarith : (0 : ℝ) ≤ k.factorial)]
    _ ≤ L * |t - b| ^ α / (Nat.factorial k : ℝ) * |t - b| ^ k := by
      gcongr
    _ ≤ L * |t - b| ^ α * |t - b| ^ k := by
      gcongr
      exact div_le_self (mul_nonneg hL (Real.rpow_nonneg (abs_nonneg _) _)) hfac
    _ = L * (b - t) ^ ((k : ℝ) + α) := by
      rw [abs_of_nonpos (sub_nonpos.mpr htb)]
      have hp : (b - t) ^ α * (b - t) ^ k = (b - t) ^ ((k : ℝ) + α) := by
        rw [← Real.rpow_natCast, ← Real.rpow_add (by linarith : 0 < b - t)]
        congr 1
        ring
      rw [neg_sub, mul_assoc, hp]

/-- Fix [a derivative order k](hyp:k), [a Hölder exponent α](hyp:α) with [α positive](hyp:hα),
[endpoints a and b](hyp:a,b) with [a < b](hyp:hab), and
[a nonnegative Hölder constant L](hyp:L,hL). Then [there is one nonnegative constant C such
that every function f that is k times continuously differentiable on the interval from a to b,
with k-th within-interval derivative Hölder with constant L and exponent α there, has a polynomial
of degree at most k in b − t whose error at every point t of the interval is at most
C·(b − t)^(k + α)](goal). The coefficients may depend on the function, while the remainder
constant depends only on the order, exponent, length, and Hölder constant. -/
theorem endpoint_holder_taylor_Icc
    (k : ℕ) (α a b L : ℝ) (hα : 0 < α)
    (hab : a < b) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (f : ℝ → ℝ),
        ContDiffOn ℝ k f (Set.Icc a b) →
        (∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
          |iteratedDerivWithin k f (Set.Icc a b) x -
            iteratedDerivWithin k f (Set.Icc a b) y| ≤
              L * |x - y| ^ α) →
        ∃ coeff : Fin (k + 1) → ℝ,
          ∀ t ∈ Set.Icc a b,
            |f t - ∑ j : Fin (k + 1), coeff j * (b - t) ^ j.val| ≤
              C * (b - t) ^ ((k : ℝ) + α) := by
  obtain ⟨C, hC, hbound⟩ :=
    endpoint_holder_taylor k α (b - a) L hα (sub_pos.mpr hab) hL
  refine ⟨C, hC, ?_⟩
  intro f hf hholder
  have heq : a + (b - a) = b := by ring
  simpa [heq] using
    (hbound a f (by simpa [heq] using hf) (by simpa [heq] using hholder))

end Causalean.Mathlib.Analysis.Calculus.HolderTaylor
