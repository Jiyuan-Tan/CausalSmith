module
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.Directional
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.LineInterior
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.LineTaylor
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.Segment

/-!
# Taylor remainder from the top coordinate seminorm

The Taylor remainder uses only the Hölder differences of order-`m` coordinate partials.
The expansion point is interior, where `ContDiffOn` agrees with ambient derivatives.
-/

public section

open scoped BigOperators

namespace Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- For [a dimension, a derivative order m, and an exponent s](hyp:d,m,s) with [s positive](hyp:hs)
and [s at most one](hyp:hs1), [there is a positive constant C such that, for every function that is
m times continuously differentiable on the closed normalized cube and satisfies the top-order
Hölder condition with exponent s and a nonnegative constant L, the function at any point y of the
closed cube differs from its order-m Taylor polynomial centred at any point x of the open cube by
at most C times L times the distance from x to y raised to the power m + s](goal). -/
theorem top_holder_taylor_remainder (d m : ℕ) (s : ℝ)
    (hs : 0 < s) (hs1 : s ≤ 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : (Fin d → ℝ) → ℝ) (L : ℝ),
        0 ≤ L → ContDiffOn ℝ m u (cube d) → TopHolder d m s L u →
        ∀ x ∈ openCube d, ∀ y ∈ cube d,
          |u y - ∑ k ∈ Finset.range (m + 1),
              (Nat.factorial k : ℝ)⁻¹ *
                iteratedFDeriv ℝ k u x (fun _ => y - x)| ≤
            C * L * ‖y - x‖ ^ ((m : ℝ) + s) := by
  refine ⟨((d : ℝ) + 1) ^ m, by positivity, ?_⟩
  intro u L hL hu hholder x hx y hy
  let v : ℝ → ℝ := fun r => u (x + r • (y - x))
  have hline : ContDiff ℝ m (fun r : ℝ => x + r • (y - x)) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  have hmaps : Set.MapsTo (fun r : ℝ => x + r • (y - x))
      (Set.Icc (0 : ℝ) 1) (cube d) := by
    intro r hr
    by_cases hr1 : r < 1
    · have h := segment_mem_openCube hx hy (show r ∈ Set.Ico (0 : ℝ) 1 from ⟨hr.1, hr1⟩)
      intro i
      exact ⟨le_of_lt (h i (Set.mem_univ i)).1,
        le_of_lt (h i (Set.mem_univ i)).2⟩
    · have hr' : r = 1 := by linarith [hr.2]
      subst r
      simpa using hy
  have hv : ContDiffOn ℝ m v (Set.Icc (0 : ℝ) 1) :=
    hu.comp hline.contDiffOn hmaps
  have hzero : (0 : ℝ) ∈ Set.Ico (0 : ℝ) 1 := by norm_num
  have hderiv (k : ℕ) (hk : k ≤ m) :
      iteratedDeriv k v 0 = iteratedFDeriv ℝ k u x (fun _ => y - x) := by
    simpa [v] using segment_iteratedDeriv_eq_diagonal hu hx hy hzero k hk
  have hpoly :
      (∑ k ∈ Finset.range (m + 1),
          (Nat.factorial k : ℝ)⁻¹ * iteratedFDeriv ℝ k u x (fun _ => y - x)) =
      ∑ k ∈ Finset.range (m + 1),
          (Nat.factorial k : ℝ)⁻¹ * iteratedDeriv k v 0 * (1 - 0) ^ k := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hderiv k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
    norm_num
  have hvone : v 1 = u y := by simp [v]
  have hbase : ∀ k ≤ m,
      iteratedDerivWithin k v (Set.uIcc (0 : ℝ) 1) 0 = iteratedDeriv k v 0 := by
    intro k hk
    have hcont : ContDiffAt ℝ k v 0 := by
      have ho : IsOpen (openCube d) :=
        isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)
      have hsub : openCube d ⊆ cube d := by
        intro z hz i
        exact ⟨le_of_lt (hz i (Set.mem_univ i)).1,
          le_of_lt (hz i (Set.mem_univ i)).2⟩
      have hux : ContDiffAt ℝ k u x :=
        ((hu.mono hsub).contDiffAt (ho.mem_nhds hx)).of_le (by exact_mod_cast hk)
      have hlinek : ContDiffAt ℝ k (fun r : ℝ => x + r • (y - x)) 0 :=
        (hline.of_le (by exact_mod_cast hk)).contDiffAt
      have hux' : ContDiffAt ℝ k u (x + (0 : ℝ) • (y - x)) := by simpa using hux
      change ContDiffAt ℝ k (u ∘ fun r : ℝ => x + r • (y - x)) 0
      exact hux'.comp 0 hlinek
    exact iteratedDerivWithin_eq_iteratedDeriv
      (uniqueDiffOn_uIcc (by norm_num : (0 : ℝ) ≠ 1)) hcont Set.left_mem_uIcc
  by_cases hm0 : m = 0
  · subst m
    have htop := topHolder_diagonal_derivative u hs hL hholder y x (y - x) hy
      (by
        intro i
        exact ⟨le_of_lt (hx i (Set.mem_univ i)).1,
          le_of_lt (hx i (Set.mem_univ i)).2⟩)
    simp only [Finset.range_one, Finset.sum_singleton] at *
    simp [iteratedFDeriv_zero] at htop ⊢
    simpa [abs_sub_comm, norm_sub_rev] using htop
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
    let n := m - 1
    have hn : n + 1 = m := Nat.succ_pred_eq_of_pos hmpos
    have hcont : ContDiffOn ℝ (n + 1) v (Set.uIcc (0 : ℝ) 1) := by
      change ContDiffOn ℝ (↑(n + 1 : ℕ)) v (Set.uIcc (0 : ℝ) 1)
      rw [hn, Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact hv
    obtain ⟨ξ, hξ, hrem⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv
        (f := v) (x := (1 : ℝ)) (x₀ := (0 : ℝ)) (n := n)
        (by norm_num) hcont
    have hξ' : ξ ∈ Set.Ioo (0 : ℝ) 1 := by
      simpa [Set.uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hξ
    have htop : |iteratedDeriv m v ξ - iteratedDeriv m v 0| ≤
        ((d : ℝ) + 1) ^ m * L * ‖y - x‖ ^ ((m : ℝ) + s) := by
      have ht : 0 ≤ (ξ + 1) / 2 ∧ (ξ + 1) / 2 < 1 := by constructor <;> linarith [hξ'.1, hξ'.2]
      have hξmem : ξ ∈ Set.Icc (0 : ℝ) ((ξ + 1) / 2) := ⟨hξ'.1.le, by linarith [hξ'.2]⟩
      have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) ((ξ + 1) / 2) := ⟨le_refl _, ht.1⟩
      have h := segment_line_topHolder_before_endpoint hu hs hL hholder hx hy
        ht.1 ht.2 hξmem h0mem
      have hp : |ξ - 0| ^ s ≤ (1 : ℝ) := by
        rw [sub_zero, abs_of_pos hξ'.1]
        simpa using Real.rpow_le_rpow (le_of_lt hξ'.1) hξ'.2.le hs.le
      calc
        _ ≤ ((d : ℝ) + 1) ^ m * L * ‖y - x‖ ^ ((m : ℝ) + s) * |ξ - 0| ^ s := h
        _ ≤ ((d : ℝ) + 1) ^ m * L * ‖y - x‖ ^ ((m : ℝ) + s) * 1 :=
          mul_le_mul_of_nonneg_left hp (by positivity)
        _ = _ := by ring
    have hpolyM :
        (∑ k ∈ Finset.range (m + 1),
            (Nat.factorial k : ℝ)⁻¹ * iteratedDeriv k v 0 * (1 - 0) ^ k) =
        (∑ k ∈ Finset.range (n + 1),
            (Nat.factorial k : ℝ)⁻¹ * iteratedDeriv k v 0 * (1 - 0) ^ k) +
          (Nat.factorial m : ℝ)⁻¹ * iteratedDeriv m v 0 * (1 - 0) ^ m := by
      rw [hn, Finset.sum_range_succ]
    have hpolyN : taylorWithinEval v n (Set.uIcc (0 : ℝ) 1) 0 1 =
        ∑ k ∈ Finset.range (n + 1),
          (Nat.factorial k : ℝ)⁻¹ * iteratedDeriv k v 0 * (1 - 0) ^ k := by
      rw [taylor_within_apply]
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k ≤ m := by
        have hk'' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        omega
      rw [hbase k hk']
      simp only [smul_eq_mul]
      ring
    have hdiff : v 1 - (∑ k ∈ Finset.range (m + 1),
        (Nat.factorial k : ℝ)⁻¹ * iteratedDeriv k v 0 * (1 - 0) ^ k) =
        (iteratedDeriv m v ξ - iteratedDeriv m v 0) /
          (Nat.factorial m : ℝ) := by
      rw [hpolyM, ← hpolyN, sub_add_eq_sub_sub, hrem]
      simp only [hn]
      norm_num
      ring
    rw [← hvone, hpoly, hdiff]
    have hfac : 1 ≤ (Nat.factorial m : ℝ) := by exact_mod_cast Nat.factorial_pos m
    calc
      |(iteratedDeriv m v ξ - iteratedDeriv m v 0) / (Nat.factorial m : ℝ)| =
          |iteratedDeriv m v ξ - iteratedDeriv m v 0| / (Nat.factorial m : ℝ) := by
            rw [abs_div, abs_of_nonneg (by linarith : (0 : ℝ) ≤ m.factorial)]
      _ ≤ ((d : ℝ) + 1) ^ m * L * ‖y - x‖ ^ ((m : ℝ) + s) /
          (Nat.factorial m : ℝ) := div_le_div_of_nonneg_right htop (by linarith)
      _ ≤ ((d : ℝ) + 1) ^ m * L * ‖y - x‖ ^ ((m : ℝ) + s) :=
          div_le_self (by positivity) hfac

end Causalean.Mathlib.Analysis.Calculus.CubeInterpolation
