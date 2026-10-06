module
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.Basic
public import Mathlib.Analysis.Calculus.Taylor

/-!
# One-dimensional Taylor remainder with a top Hölder modulus

This is the line-segment calculus step used by the multivariate remainder.
-/

public section

open scoped BigOperators

namespace Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- For [a derivative order m and an exponent s](hyp:m,s) with [s positive](hyp:hs) and [s at most
one](hyp:hs1), [there is a positive constant C such that, for every function of one real variable
that is m times continuously differentiable on a nondegenerate closed interval and whose m-th
derivative changes between any two points of the interval by at most a nonnegative L times their
distance to the power s, the function at any point y of the interval differs from its order-m
Taylor polynomial centred at any interior point x by at most C times L times the distance from x to
y raised to the power m + s](goal). -/
theorem line_holder_taylor (m : ℕ) (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (v : ℝ → ℝ) (a b L : ℝ),
        a < b → 0 ≤ L → ContDiffOn ℝ m v (Set.Icc a b) →
        (∀ z ∈ Set.Icc a b, ∀ w ∈ Set.Icc a b,
          |iteratedDeriv m v z - iteratedDeriv m v w| ≤ L * |z - w| ^ s) →
        ∀ x ∈ Set.Ioo a b, ∀ y ∈ Set.Icc a b,
          |v y - ∑ k ∈ Finset.range (m + 1),
              (Nat.factorial k : ℝ)⁻¹ * iteratedDeriv k v x * (y - x) ^ k| ≤
            C * L * |y - x| ^ ((m : ℝ) + s) := by
  refine ⟨1, by norm_num, ?_⟩
  intro v a b L hab hL hv hholder x hx y hy
  have hxmem : x ∈ Set.Icc a b := ⟨hx.1.le, hx.2.le⟩
  have hbase : ∀ n ≤ m, ∀ z, x ∈ Set.uIcc x z → x ≠ z →
      iteratedDerivWithin n v (Set.uIcc x z) x = iteratedDeriv n v x := by
    intro n hn z hxz hne
    exact iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hne)
      ((hv.contDiffAt (Icc_mem_nhds hx.1 hx.2)).of_le (by exact_mod_cast hn)) hxz
  by_cases hxy : x = y
  · subst y
    have he : 0 < (m : ℝ) + s := by positivity
    have hsum : (∑ k ∈ Finset.range (m + 1),
        (Nat.factorial k : ℝ)⁻¹ * iteratedDeriv k v x * (x - x) ^ k) = v x := by
      calc
        _ = (Nat.factorial 0 : ℝ)⁻¹ * iteratedDeriv 0 v x * (x - x) ^ 0 := by
          apply Finset.sum_eq_single 0
          · intro k hk hk0
            simp [hk0]
          · simp
        _ = v x := by simp [iteratedDeriv_zero]
    rw [hsum]
    simp [Real.zero_rpow (ne_of_gt he)]
  have hpos : 0 < |y - x| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hxy))
  have hseg : Set.uIcc x y ⊆ Set.Icc a b := by
    intro z hz
    rcases le_total x y with h | h
    · rw [Set.uIcc_of_le h] at hz
      exact ⟨hxmem.1.trans hz.1, hz.2.trans hy.2⟩
    · rw [Set.uIcc_of_ge h] at hz
      exact ⟨hy.1.trans hz.1, hz.2.trans hxmem.2⟩
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst m
    simpa [iteratedDeriv_zero] using hholder y hy x hxmem
  let n := m - 1
  have hm : n + 1 = m := Nat.succ_pred_eq_of_pos hmpos
  have hcont : ContDiffOn ℝ (n + 1) v (Set.uIcc x y) := by
    change ContDiffOn ℝ (↑(n + 1 : ℕ)) v (Set.uIcc x y)
    rw [hm]
    exact hv.mono hseg
  obtain ⟨ξ, hξ, hrem⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (f := v) (x := y) (x₀ := x)
      (n := n) hxy hcont
  have hξmem : ξ ∈ Set.Icc a b := hseg (Set.uIoo_subset_uIcc_self hξ)
  have hξdist : |ξ - x| ≤ |y - x| := by
    rcases le_total x y with h | h
    · rw [Set.uIoo_of_le h] at hξ
      rw [abs_of_nonneg (sub_nonneg.mpr hξ.1.le),
        abs_of_nonneg (sub_nonneg.mpr h)]
      linarith [hξ.2]
    · rw [Set.uIoo_of_ge h] at hξ
      rw [abs_of_nonpos (sub_nonpos.mpr hξ.2.le),
        abs_of_nonpos (sub_nonpos.mpr h)]
      linarith [hξ.1]
  have hpow : |ξ - x| ^ s ≤ |y - x| ^ s :=
    Real.rpow_le_rpow (abs_nonneg _) hξdist hs.le
  have htop : |iteratedDeriv m v ξ - iteratedDeriv m v x| ≤
      L * |y - x| ^ s :=
    (hholder ξ hξmem x hxmem).trans (mul_le_mul_of_nonneg_left hpow hL)
  have hpolyM :
      (∑ k ∈ Finset.range (m + 1),
          (Nat.factorial k : ℝ)⁻¹ * iteratedDeriv k v x * (y - x) ^ k) =
      (∑ k ∈ Finset.range (n + 1),
          (Nat.factorial k : ℝ)⁻¹ * iteratedDeriv k v x * (y - x) ^ k) +
        (Nat.factorial m : ℝ)⁻¹ * iteratedDeriv m v x * (y - x) ^ m := by
    rw [hm, Finset.sum_range_succ]
  have hpolyN' : taylorWithinEval v n (Set.uIcc x y) x y =
      ∑ k ∈ Finset.range (n + 1),
        (Nat.factorial k : ℝ)⁻¹ * iteratedDeriv k v x * (y - x) ^ k := by
    rw [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ m := by
      have hk'' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      omega
    rw [hbase k hk' y Set.left_mem_uIcc hxy]
    simp only [smul_eq_mul]
    ring
  have hdiff :
      v y - (∑ k ∈ Finset.range (m + 1),
          (Nat.factorial k : ℝ)⁻¹ * iteratedDeriv k v x * (y - x) ^ k) =
        (iteratedDeriv m v ξ - iteratedDeriv m v x) /
          (Nat.factorial m : ℝ) * (y - x) ^ m := by
    rw [hpolyM, ← hpolyN', sub_add_eq_sub_sub, hrem]
    simp only [hm]
    ring
  rw [hdiff]
  have hfac : 1 ≤ (Nat.factorial m : ℝ) := by exact_mod_cast Nat.factorial_pos m
  calc
    |(iteratedDeriv m v ξ - iteratedDeriv m v x) / (Nat.factorial m : ℝ) *
        (y - x) ^ m| =
        |iteratedDeriv m v ξ - iteratedDeriv m v x| /
          (Nat.factorial m : ℝ) * |y - x| ^ m := by
      rw [abs_mul, abs_div, abs_pow, abs_of_nonneg (by linarith : (0 : ℝ) ≤ m.factorial)]
    _ ≤ L * |y - x| ^ s / (Nat.factorial m : ℝ) * |y - x| ^ m := by
      gcongr
    _ ≤ L * |y - x| ^ s * |y - x| ^ m := by
      gcongr
      exact div_le_self (mul_nonneg hL (Real.rpow_nonneg (abs_nonneg _) _)) hfac
    _ = 1 * L * |y - x| ^ ((m : ℝ) + s) := by
      have hp : |y - x| ^ s * |y - x| ^ m =
          |y - x| ^ ((m : ℝ) + s) := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hpos]
        congr 1
        ring
      calc
        _ = L * (|y - x| ^ s * |y - x| ^ m) := by ring
        _ = L * |y - x| ^ ((m : ℝ) + s) := by rw [hp]
        _ = _ := by ring

end Causalean.Mathlib.Analysis.Calculus.CubeInterpolation
