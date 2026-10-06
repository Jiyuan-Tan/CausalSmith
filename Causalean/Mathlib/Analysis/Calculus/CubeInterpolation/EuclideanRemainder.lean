module
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.Euclidean
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.EuclideanSegment
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.Holder
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.MultiindexTaylor
public import Causalean.Mathlib.Analysis.Calculus.CubeInterpolation.Taylor

/-!
# Euclidean top-Hölder Taylor remainders on arbitrary cubes

Sorted within-cube coordinate Hölder data controls the Taylor remainder from
any interior point, including evaluation at a boundary point. The constants
are uniform in the exponent 0 < s ≤ 1 as well as center and side length.

The existing top_holder_taylor_remainder and euclidean_to_topHolder live on
the normalized Pi cube and ambient jets. Here their segment argument is
transported to Euclidean within jets; no ambient differentiability at the
boundary is required. Segment.lean isolates the line-jet transport and Holder.lean isolates the
sorted-to-diagonal modulus before the final remainder argument.
-/

public section

open scoped BigOperators Topology
noncomputable section
namespace Causalean.Mathlib.Analysis.Calculus.CubeInterpolation

/-- Take [a cube centre b and two points a and y](hyp:b,a,y), [a side length H](hyp:H) that is
[positive](hyp:hH), [a real function u](hyp:u), and [constants L and s](hyp:L,s) with [L
nonnegative](hyp:hL) and [s positive](hyp:hs). Suppose [u is m times continuously differentiable on
the cube](hyp:hu), [every sorted coordinate partial of total order m, taken within the cube,
changes between any two cube points by at most L times their distance to the power s](hyp:hmod), [a
is interior to the cube](hyp:ha), and [y lies in the cube](hyp:hy). Then for [any two times r and
q](hyp:r,q) [in the half-open unit interval](hyp:hr,hq), [the m-th derivative of the function
restricted to the segment from a to y changes between those times by at most (d + 1)^m times L
times the segment length to the power m + s times the time difference to the power s](goal). -/
theorem segment_topHolder_from_sorted {d m : ℕ}
    (b a y : EuclideanSpace ℝ (Fin d)) (H : ℝ) (hH : 0 < H)
    (u : EuclideanSpace ℝ (Fin d) → ℝ) (L s : ℝ) (hL : 0 ≤ L) (hs : 0 < s)
    (hu : ContDiffOn ℝ m u (centeredCube b H))
    (hmod : ∀ κ : ExactIndex d m, ∀ x ∈ centeredCube b H,
      ∀ z ∈ centeredCube b H,
      |coordinatePartial (centeredCube b H) u κ.1 x -
        coordinatePartial (centeredCube b H) u κ.1 z| ≤ L * ‖x - z‖ ^ s)
    (ha : a ∈ interior (centeredCube b H)) (hy : y ∈ centeredCube b H)
    (r q : ℝ) (hr : r ∈ Set.Ico (0 : ℝ) 1) (hq : q ∈ Set.Ico (0 : ℝ) 1) :
    |iteratedDeriv m (fun t : ℝ => u (a + t • (y - a))) r -
      iteratedDeriv m (fun t : ℝ => u (a + t • (y - a))) q| ≤
      ((d : ℝ) + 1) ^ m * L * ‖y - a‖ ^ ((m : ℝ) + s) * |r - q| ^ s := by
  rw [segment_iteratedDeriv_eq_within_diagonal b a y H hH u hu ha hy r hr m le_rfl,
    segment_iteratedDeriv_eq_within_diagonal b a y H hH u hu ha hy q hq m le_rfl]
  have hrc := interior_subset (segment_mem_interior_centeredCube b a y H ha hy r hr)
  have hqc := interior_subset (segment_mem_interior_centeredCube b a y H ha hy q hq)
  have hbound := within_diagonal_topHolder_from_sorted b H hH u L s hL hs hu hmod
    (a + r • (y - a)) (a + q • (y - a)) (y - a) hrc hqc
  have hdiff : (a + r • (y - a)) - (a + q • (y - a)) =
      (r - q) • (y - a) := by
    rw [sub_smul]
    abel
  rw [hdiff, norm_smul, Real.norm_eq_abs] at hbound
  calc
    _ ≤ ((d : ℝ) + 1) ^ m * L *
        (|r - q| * ‖y - a‖) ^ s * ‖y - a‖ ^ m := hbound
    _ = _ := by
      rw [Real.mul_rpow (abs_nonneg _) (norm_nonneg _),
        Real.rpow_add_of_nonneg (norm_nonneg _) (Nat.cast_nonneg _) hs.le,
        Real.rpow_natCast]
      ring

/-- In [a finite Euclidean dimension](hyp:d) at [a derivative order](hyp:m), [there is a positive
constant C such that the following holds for every cube of positive side length, every nonnegative
L, and every positive exponent s at most one: if a function is m times continuously differentiable
on the cube and each of its sorted coordinate partials of total order m changes between any two
cube points by at most L times their distance to the power s, then at every cube point y the
function differs from its order-m diagonal Taylor polynomial centred at an interior point a by at
most C times L times the distance from a to y raised to the power m + s](goal). -/
theorem cube_euclidean_taylor_remainder (d m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (b a y : EuclideanSpace ℝ (Fin d))
      (H L s : ℝ) (u : EuclideanSpace ℝ (Fin d) → ℝ),
      0 < H → 0 ≤ L → 0 < s → s ≤ 1 →
      ContDiffOn ℝ m u (centeredCube b H) →
      (∀ κ : ExactIndex d m, ∀ x ∈ centeredCube b H, ∀ z ∈ centeredCube b H,
        |coordinatePartial (centeredCube b H) u κ.1 x -
          coordinatePartial (centeredCube b H) u κ.1 z| ≤ L * ‖x - z‖ ^ s) →
      a ∈ interior (centeredCube b H) → y ∈ centeredCube b H →
      |u y - diagonalTaylor (centeredCube b H) u m a y| ≤
        C * L * ‖y - a‖ ^ ((m : ℝ) + s) := by
  refine ⟨((d : ℝ) + 1) ^ m, by positivity, ?_⟩
  intro b a y H L s u hH hL hs _hs1 hu hmod ha hy
  let v : ℝ → ℝ := fun r => u (a + r • (y - a))
  have hline : ContDiff ℝ m (fun r : ℝ => a + r • (y - a)) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  have hmaps : Set.MapsTo (fun r : ℝ => a + r • (y - a))
      (Set.Icc (0 : ℝ) 1) (centeredCube b H) := by
    intro r hr
    by_cases hr1 : r < 1
    · exact interior_subset (segment_mem_interior_centeredCube b a y H ha hy r
        ⟨hr.1, hr1⟩)
    · have hr' : r = 1 := by linarith [hr.2]
      subst r
      simpa using hy
  have hv : ContDiffOn ℝ m v (Set.Icc (0 : ℝ) 1) :=
    hu.comp hline.contDiffOn hmaps
  have hzero : (0 : ℝ) ∈ Set.Ico (0 : ℝ) 1 := by norm_num
  have hderiv (k : ℕ) (hk : k ≤ m) :
      iteratedDeriv k v 0 =
        iteratedFDerivWithin ℝ k u (centeredCube b H) a (fun _ => y - a) := by
    simpa [v] using
      segment_iteratedDeriv_eq_within_diagonal b a y H hH u hu ha hy 0 hzero k hk
  have hpoly :
      (∑ k ∈ Finset.range (m + 1),
          (Nat.factorial k : ℝ)⁻¹ *
            iteratedFDerivWithin ℝ k u (centeredCube b H) a (fun _ => y - a)) =
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
      have hua : ContDiffAt ℝ k u a :=
        ((hu.mono interior_subset).contDiffAt
          (isOpen_interior.mem_nhds ha)).of_le (by exact_mod_cast hk)
      have hlinek : ContDiffAt ℝ k (fun r : ℝ => a + r • (y - a)) 0 :=
        (hline.of_le (by exact_mod_cast hk)).contDiffAt
      have hua' : ContDiffAt ℝ k u (a + (0 : ℝ) • (y - a)) := by simpa using hua
      change ContDiffAt ℝ k (u ∘ fun r : ℝ => a + r • (y - a)) 0
      exact hua'.comp 0 hlinek
    exact iteratedDerivWithin_eq_iteratedDeriv
      (uniqueDiffOn_uIcc (by norm_num : (0 : ℝ) ≠ 1)) hcont Set.left_mem_uIcc
  by_cases hm0 : m = 0
  · subst m
    have htop := within_diagonal_topHolder_from_sorted b H hH u L s hL hs hu
      hmod y a (y - a) hy (interior_subset ha)
    simpa [diagonalTaylor, iteratedFDerivWithin_zero_apply] using htop
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
        ((d : ℝ) + 1) ^ m * L * ‖y - a‖ ^ ((m : ℝ) + s) := by
      have h := segment_topHolder_from_sorted b a y H hH u L s hL hs hu hmod
        ha hy ξ 0 ⟨hξ'.1.le, hξ'.2⟩ hzero
      change |iteratedDeriv m v ξ - iteratedDeriv m v 0| ≤ _ at h
      have hp : |ξ - 0| ^ s ≤ (1 : ℝ) := by
        rw [sub_zero, abs_of_pos hξ'.1]
        simpa using Real.rpow_le_rpow (le_of_lt hξ'.1) hξ'.2.le hs.le
      calc
        _ ≤ ((d : ℝ) + 1) ^ m * L * ‖y - a‖ ^ ((m : ℝ) + s) * |ξ - 0| ^ s := h
        _ ≤ ((d : ℝ) + 1) ^ m * L * ‖y - a‖ ^ ((m : ℝ) + s) * 1 :=
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
    change |u y - (∑ k ∈ Finset.range (m + 1),
      (Nat.factorial k : ℝ)⁻¹ *
        iteratedFDerivWithin ℝ k u (centeredCube b H) a (fun _ => y - a))| ≤ _
    rw [← hvone, hpoly, hdiff]
    have hfac : 1 ≤ (Nat.factorial m : ℝ) := by exact_mod_cast Nat.factorial_pos m
    calc
      |(iteratedDeriv m v ξ - iteratedDeriv m v 0) / (Nat.factorial m : ℝ)| =
          |iteratedDeriv m v ξ - iteratedDeriv m v 0| / (Nat.factorial m : ℝ) := by
            rw [abs_div, abs_of_nonneg (by linarith : (0 : ℝ) ≤ m.factorial)]
      _ ≤ ((d : ℝ) + 1) ^ m * L * ‖y - a‖ ^ ((m : ℝ) + s) /
          (Nat.factorial m : ℝ) := div_le_div_of_nonneg_right htop (by linarith)
      _ ≤ ((d : ℝ) + 1) ^ m * L * ‖y - a‖ ^ ((m : ℝ) + s) :=
          div_le_self (by positivity) hfac

/-- In [a finite Euclidean dimension](hyp:d) at [a derivative order](hyp:m), [there is a positive
constant C such that the following holds for every cube of positive side length, every nonnegative
L, and every positive exponent s at most one: if a function is m times continuously differentiable
on the cube and each of its sorted coordinate partials of total order m changes between any two
cube points by at most L times their distance to the power s, then on every smaller cube of
positive side length h contained in the big cube and centred at one of its interior points, the
function differs from its order-m multi-index Taylor polynomial at that centre by at most C times L
times h to the power m + s](goal). -/
theorem local_cube_multiindex_remainder (d m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (b a : EuclideanSpace ℝ (Fin d))
      (H h L s : ℝ) (u : EuclideanSpace ℝ (Fin d) → ℝ),
      0 < H → 0 < h → 0 ≤ L → 0 < s → s ≤ 1 →
      ContDiffOn ℝ m u (centeredCube b H) →
      (∀ κ : ExactIndex d m, ∀ x ∈ centeredCube b H, ∀ z ∈ centeredCube b H,
        |coordinatePartial (centeredCube b H) u κ.1 x -
          coordinatePartial (centeredCube b H) u κ.1 z| ≤ L * ‖x - z‖ ^ s) →
      a ∈ interior (centeredCube b H) → centeredCube a h ⊆ centeredCube b H →
      ∀ x ∈ centeredCube a h,
        |u x - multiindexTaylor (centeredCube b H) u m a x| ≤
          C * L * h ^ ((m : ℝ) + s) := by
  obtain ⟨Cr, hCr, hr⟩ := cube_euclidean_taylor_remainder d m
  let D : ℝ := (d : ℝ) + 1
  have hD : 1 ≤ D := by
    dsimp [D]
    linarith [Nat.cast_nonneg (α := ℝ) d]
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  refine ⟨Cr * D ^ (m + 1), mul_pos hCr (pow_pos hDpos _), ?_⟩
  intro b a H h L s u hH hh hL hs hs1 hu hmod ha hsub x hx
  have he : 0 ≤ (m : ℝ) + s := by positivity
  have hsqrt : Real.sqrt d ≤ D := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · exact hDpos.le
    · dsimp [D]
      nlinarith [Nat.cast_nonneg (α := ℝ) d, sq_nonneg (d : ℝ)]
  have hdist : ‖x - a‖ ≤ D * h := by
    calc
      _ ≤ Real.sqrt d * (h / 2) := centeredCube_norm_sub_le a h hh.le hx
      _ ≤ D * (h / 2) := mul_le_mul_of_nonneg_right hsqrt (by positivity)
      _ ≤ D * h := mul_le_mul_of_nonneg_left (by linarith) hDpos.le
  have hpow : ‖x - a‖ ^ ((m : ℝ) + s) ≤
      D ^ (m + 1) * h ^ ((m : ℝ) + s) := by
    calc
      _ ≤ (D * h) ^ ((m : ℝ) + s) :=
        Real.rpow_le_rpow (norm_nonneg _) hdist he
      _ = D ^ ((m : ℝ) + s) * h ^ ((m : ℝ) + s) :=
        Real.mul_rpow hDpos.le hh.le
      _ ≤ D ^ ((m : ℝ) + 1) * h ^ ((m : ℝ) + s) :=
        mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le hD (by linarith))
          (Real.rpow_nonneg hh.le _)
      _ = D ^ (m + 1) * h ^ ((m : ℝ) + s) := by
        rw [show (m : ℝ) + 1 = ((m + 1 : ℕ) : ℝ) by norm_cast,
          Real.rpow_natCast]
  rw [← cube_diagonal_taylor_eq_multiindex b a x H hH u hu (interior_subset ha)]
  calc
    _ ≤ Cr * L * ‖x - a‖ ^ ((m : ℝ) + s) :=
      hr b a x H L s u hH hL hs hs1 hu hmod ha (hsub hx)
    _ ≤ Cr * L * (D ^ (m + 1) * h ^ ((m : ℝ) + s)) :=
      mul_le_mul_of_nonneg_left hpow (mul_nonneg hCr.le hL)
    _ = Cr * D ^ (m + 1) * L * h ^ ((m : ℝ) + s) := by ring

end Causalean.Mathlib.Analysis.Calculus.CubeInterpolation
