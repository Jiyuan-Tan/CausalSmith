module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.Coefficients

/-!
# Zero-extended discrete variation of Jackson coefficients

All sums are over the full integer line. This retains the endpoint terms that
arise when a finite sequence is extended by zero.
-/

@[expose] public section

namespace Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson

open scoped BigOperators

/-- The [forward first difference](goal) of [a real sequence indexed by the integers](hyp:a) at [an
index j](hyp:j) is [the term at j + 1 minus the term at j](step:1). -/
def delta (a : ℤ → ℝ) (j : ℤ) : ℝ := a (j + 1) - a j

/-- The [forward second difference](goal) of [a real sequence indexed by the integers](hyp:a) at
[an index j](hyp:j) is [the first difference of the first-difference sequence](step:1), that is,
the term at j + 2 minus twice the term at j + 1 plus the term at j. -/
def delta2 (a : ℤ → ℝ) (j : ℤ) : ℝ := delta (delta a) j

/-- For [any order N](hyp:N) and [any integer frequency j](hyp:j), [the first difference of the raw
Jackson Fourier coefficients at j equals the sum, over integers k between −N − 1 and N, of the
first difference of the triangular sequence at k times the triangular sequence at j − k](goal). -/
theorem delta_convolution (N : ℕ) (j : ℤ) :
    delta (convolution N) j =
      ∑ k ∈ Finset.Icc (-(N : ℤ) - 1) (N : ℤ),
        delta (triangle N) k * triangle N (j - k) := by
  let S := Finset.Icc (-(N : ℤ) - 1) (N : ℤ)
  have hleft : (∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      triangle N k * triangle N (j + 1 - k)) =
      ∑ k ∈ S, triangle N (k + 1) * triangle N (j - k) := by
    have hext : (∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        triangle N k * triangle N (j + 1 - k)) =
        ∑ k ∈ Finset.Icc (-(N : ℤ)) ((N : ℤ) + 1),
          triangle N k * triangle N (j + 1 - k) := by
      apply Finset.sum_subset (by intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega)
      intro k hk hk'
      have hkN : k = (N : ℤ) + 1 := by
        simp only [Finset.mem_Icc] at hk hk'
        omega
      subst k
      have hz : triangle N ((N : ℤ) + 1) = 0 :=
        triangle_support N _ (by
          rw [abs_of_nonneg (by omega : 0 ≤ (N : ℤ) + 1)]
          omega)
      simp [hz]
    rw [hext]
    have hmap := Finset.map_add_right_Icc (-(N : ℤ) - 1) (N : ℤ) (1 : ℤ)
    have hshift : S.map (addRightEmbedding (1 : ℤ)) =
        Finset.Icc (-(N : ℤ)) ((N : ℤ) + 1) := by
      simpa [S, sub_eq_add_neg, add_assoc] using hmap
    rw [← hshift, Finset.sum_map]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [addRightEmbedding_apply]
    have harg : j + 1 - (k + 1) = j - k := by omega
    rw [harg]
  have hright : (∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      triangle N k * triangle N (j - k)) =
      ∑ k ∈ S, triangle N k * triangle N (j - k) := by
    apply Finset.sum_subset (by intro k hk; simp only [Finset.mem_Icc, S] at hk ⊢; omega)
    intro k hk hk'
    have hkN : k = -(N : ℤ) - 1 := by
      simp only [Finset.mem_Icc, S] at hk hk'
      omega
    subst k
    have hz : triangle N (-(N : ℤ) - 1) = 0 :=
      triangle_support N _ (by
        rw [abs_of_nonpos (by omega : -(N : ℤ) - 1 ≤ 0)]
        omega)
    simp [hz]
  change (∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      triangle N k * triangle N (j + 1 - k)) -
      (∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        triangle N k * triangle N (j - k)) = _
  rw [hleft, hright, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [delta]
  ring

/-- For [any order N](hyp:N) and [any integer frequency j](hyp:j), [the second difference of the
raw Jackson Fourier coefficients at j equals the sum, over integers k between −N − 1 and N, of the
first difference of the triangular sequence at k times its first difference at j − k](goal). -/
theorem delta2_convolution (N : ℕ) (j : ℤ) :
    delta2 (convolution N) j =
      ∑ k ∈ Finset.Icc (-(N : ℤ) - 1) (N : ℤ),
        delta (triangle N) k * delta (triangle N) (j - k) := by
  rw [delta2, delta, delta_convolution N (j + 1), delta_convolution N j]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [delta]
  congr 1
  ring

/-- For [any order N](hyp:N), [the sum over all integers of the absolute values of the triangular
sequence equals N²](goal). -/
theorem triangle_l1 (N : ℕ) :
    (∑' j : ℤ, |triangle N j|) = (N : ℝ) ^ 2 := by
  have hsupport : ∀ j : ℤ, j ∉ Finset.Icc (-(N : ℤ)) (N : ℤ) →
      |triangle N j| = 0 := by
    intro j hj
    have hj' : (N : ℤ) ≤ |j| := by
      by_contra h
      have habs : |j| < (N : ℤ) := by omega
      have hbounds := abs_lt.mp habs
      simp only [Finset.mem_Icc] at hj
      omega
    simp [triangle_support N j hj']
  rw [tsum_eq_sum hsupport]
  have heven : Function.Even (fun j : ℤ => |triangle N j|) := by
    intro j
    simp [triangle, Int.natAbs_neg]
  rw [Finset.sum_Icc_of_even_eq_range heven N]
  have hterm : ∀ m ∈ Finset.range (N + 1),
      |triangle N (m : ℤ)| = (N : ℝ) - m := by
    intro m hm
    have hmN : m ≤ N := by
      have := Finset.mem_range.mp hm
      omega
    simp [triangle, Nat.cast_sub hmN, hmN]
  rw [Finset.sum_congr rfl hterm]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  have hsum : (∑ m ∈ Finset.range (N + 1), (m : ℝ)) * 2 =
      ((N + 1 : ℕ) : ℝ) * N := by
    have hnat : (∑ m ∈ Finset.range (N + 1), m) * 2 = (N + 1) * N := by
      simpa using Finset.sum_range_id_mul_two (N + 1)
    have hreal := congrArg (fun x : ℕ => (x : ℝ)) hnat
    simpa only [Nat.cast_mul, Nat.cast_sum, Nat.cast_add, Nat.cast_one,
      Nat.cast_ofNat] using hreal
  simp only [triangle, Int.natAbs_zero, Nat.sub_zero]
  rw [abs_of_nonneg (show (0 : ℝ) ≤ N by positivity)]
  push_cast at hsum ⊢
  nlinarith

/-- For [any order N](hyp:N), [the sum over all integers of the absolute first differences of the
triangular sequence equals 2N](goal). -/
theorem triangle_delta_l1 (N : ℕ) :
    (∑' j : ℤ, |delta (triangle N) j|) = 2 * (N : ℝ) := by
  have hneg (j : ℤ) (hlo : -(N : ℤ) ≤ j) (hhi : j ≤ 0) :
      triangle N j = (N : ℝ) + j := by
    have hnat : j.natAbs ≤ N := by
      have h : (j.natAbs : ℤ) ≤ N := by
        rw [Int.natCast_natAbs, abs_of_nonpos hhi]
        omega
      exact_mod_cast h
    have hcast : ((j.natAbs : ℕ) : ℝ) = -(j : ℝ) := by
      have hh : (j.natAbs : ℤ) = -j := by
        rw [Int.natCast_natAbs, abs_of_nonpos hhi]
      have hr := congrArg (fun x : ℤ => (x : ℝ)) hh
      simpa only [Int.cast_natCast, Int.cast_neg] using hr
    simp only [triangle, Nat.cast_sub hnat, hcast]
    ring
  have hpos (j : ℤ) (hlo : 0 ≤ j) (hhi : j ≤ (N : ℤ)) :
      triangle N j = (N : ℝ) - j := by
    have hnat : j.natAbs ≤ N := by
      have h : (j.natAbs : ℤ) ≤ N := by
        rw [Int.natCast_natAbs, abs_of_nonneg hlo]
        omega
      exact_mod_cast h
    have hcast : ((j.natAbs : ℕ) : ℝ) = (j : ℝ) := by
      have hr := congrArg (fun x : ℤ => (x : ℝ)) (Int.natAbs_of_nonneg hlo)
      simpa only [Int.cast_natCast] using hr
    simp only [triangle, Nat.cast_sub hnat, hcast]
  have hpoint (j : ℤ) : |delta (triangle N) j| =
      if j ∈ Finset.Ico (-(N : ℤ)) (N : ℤ) then 1 else 0 := by
    by_cases hmem : j ∈ Finset.Ico (-(N : ℤ)) (N : ℤ)
    · simp only [Finset.mem_Ico] at hmem
      rw [if_pos (Finset.mem_Ico.mpr hmem)]
      by_cases hj : j < 0
      · have hj1 : j + 1 ≤ 0 := by omega
        rw [delta, hneg j hmem.1 (by omega), hneg (j + 1) (by omega) hj1]
        push_cast
        norm_num
      · have hj0 : 0 ≤ j := by omega
        rw [delta, hpos j hj0 (by omega), hpos (j + 1) (by omega) (by omega)]
        push_cast
        norm_num
    · rw [if_neg hmem]
      have hout : j < -(N : ℤ) ∨ (N : ℤ) ≤ j := by
        simp only [Finset.mem_Ico, not_and_or, not_le, not_lt] at hmem
        exact hmem
      rcases hout with hj | hj
      · have hj1 : j + 1 ≤ -(N : ℤ) := by omega
        have hz0 : triangle N j = 0 := triangle_support N j (by
          rw [abs_of_nonpos (by omega : j ≤ 0)]; omega)
        have hz1 : triangle N (j + 1) = 0 := triangle_support N (j + 1) (by
          rw [abs_of_nonpos (by omega : j + 1 ≤ 0)]; omega)
        simp [delta, hz0, hz1]
      · have hz0 : triangle N j = 0 := triangle_support N j (by
          rw [abs_of_nonneg (by omega : 0 ≤ j)]; omega)
        have hz1 : triangle N (j + 1) = 0 := triangle_support N (j + 1) (by
          rw [abs_of_nonneg (by omega : 0 ≤ j + 1)]; omega)
        simp [delta, hz0, hz1]
  have hsum : (∑' j : ℤ, |delta (triangle N) j|) =
      ∑ j ∈ Finset.Ico (-(N : ℤ)) (N : ℤ), (1 : ℝ) := by
    rw [tsum_eq_sum (s := Finset.Ico (-(N : ℤ)) (N : ℤ)) (by
      intro j hj
      rw [hpoint j, if_neg hj])]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hpoint j, if_pos hj]
  rw [hsum]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Int.card_Ico]
  have hnat : ((N : ℤ) - -(N : ℤ)).toNat = 2 * N := by omega
  rw [hnat]
  push_cast
  ring

/-- For [two real sequences a and b indexed by the integers](hyp:a,b) and [a finite set of
integers](hyp:s) [outside which a vanishes](hyp:ha), [the convolution sum of a and b at any
index](hyp:j) [equals the same sum restricted to that finite set](goal). -/
theorem finite_convolution_tsum_eq_sum (a b : ℤ → ℝ) (s : Finset ℤ)
    (ha : ∀ k ∉ s, a k = 0) (j : ℤ) :
    (∑' k : ℤ, a k * b (j - k)) = ∑ k ∈ s, a k * b (j - k) := by
  apply tsum_eq_sum
  intro k hk
  simp [ha k hk]

/-- For [two real sequences indexed by the integers](hyp:a,b) [each with finite
support](hyp:ha,hb), [the sum over all integers of the absolute value of their discrete convolution
is at most the product of the sums of their absolute values](goal). -/
theorem finite_convolution_l1 (a b : ℤ → ℝ)
    (ha : Function.HasFiniteSupport a) (hb : Function.HasFiniteSupport b) :
    (∑' j : ℤ, |∑' k : ℤ, a k * b (j - k)|) ≤
      (∑' k : ℤ, |a k|) * (∑' l : ℤ, |b l|) := by
  let s : Finset ℤ := ha.toFinset
  let t : Finset ℤ := hb.toFinset
  have ha0 (k : ℤ) (hk : k ∉ s) : a k = 0 := by
    by_contra h
    exact hk ((Set.Finite.mem_toFinset ha).2 (Function.mem_support.mpr h))
  have hb0 (l : ℤ) (hl : l ∉ t) : b l = 0 := by
    by_contra h
    exact hl ((Set.Finite.mem_toFinset hb).2 (Function.mem_support.mpr h))
  let u : Finset ℤ := s.biUnion (fun k => t.image (fun l => k + l))
  have hu (j : ℤ) (hj : j ∉ u) :
      (∑' k : ℤ, a k * b (j - k)) = 0 := by
    rw [finite_convolution_tsum_eq_sum a b s ha0]
    apply Finset.sum_eq_zero
    intro k hk
    have hnot : j - k ∉ t := by
      intro hmem
      apply hj
      simp only [u, Finset.mem_biUnion, Finset.mem_image]
      exact ⟨k, hk, j - k, hmem, by ring⟩
    simp [hb0 (j - k) hnot]
  have houter : (∑' j : ℤ, |∑' k : ℤ, a k * b (j - k)|) =
      ∑ j ∈ u, |∑' k : ℤ, a k * b (j - k)| := by
    apply tsum_eq_sum
    intro j hj
    simp [hu j hj]
  have hbound (j : ℤ) :
      |∑' k : ℤ, a k * b (j - k)| ≤
        ∑ k ∈ s, |a k| * |b (j - k)| := by
    rw [finite_convolution_tsum_eq_sum a b s ha0]
    calc
      |∑ k ∈ s, a k * b (j - k)| ≤
          ∑ k ∈ s, |a k * b (j - k)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k ∈ s, |a k| * |b (j - k)| := by simp only [abs_mul]
  have hbmass : (∑' l : ℤ, |b l|) = ∑ l ∈ t, |b l| := by
    apply tsum_eq_sum
    intro l hl
    simp [hb0 l hl]
  have hamass : (∑' k : ℤ, |a k|) = ∑ k ∈ s, |a k| := by
    apply tsum_eq_sum
    intro k hk
    simp [ha0 k hk]
  have hshift (k : ℤ) (hk : k ∈ s) :
      (∑ j ∈ u, |b (j - k)|) = ∑ l ∈ t, |b l| := by
    have hsub : t.image (fun l => k + l) ⊆ u := by
      intro j hj
      exact Finset.mem_biUnion.mpr ⟨k, hk, hj⟩
    calc
      (∑ j ∈ u, |b (j - k)|) =
          ∑ j ∈ t.image (fun l => k + l), |b (j - k)| := by
            symm
            apply Finset.sum_subset hsub
            intro j hj hj'
            have hnot : j - k ∉ t := by
              intro hmem
              apply hj'
              exact Finset.mem_image.mpr ⟨j - k, hmem, by ring⟩
            simp [hb0 (j - k) hnot]
      _ = ∑ l ∈ t, |b l| := by
          rw [Finset.sum_image (by intro l hl m hm h; exact add_left_cancel h)]
          simp only [add_sub_cancel_left]
  rw [houter, hamass, hbmass]
  calc
    (∑ j ∈ u, |∑' k : ℤ, a k * b (j - k)|) ≤
        ∑ j ∈ u, ∑ k ∈ s, |a k| * |b (j - k)| :=
          Finset.sum_le_sum (by intro j hj; exact hbound j)
    _ = ∑ k ∈ s, |a k| * ∑ l ∈ t, |b l| := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro k hk
          rw [← Finset.mul_sum, hshift k hk]
    _ = (∑ k ∈ s, |a k|) * ∑ l ∈ t, |b l| := by rw [Finset.sum_mul]

private theorem triangle_finite (N : ℕ) :
    Function.HasFiniteSupport (triangle N) := by
  apply (Finset.finite_toSet (Finset.Icc (-(N : ℤ)) (N : ℤ))).subset
  intro j hj
  simp only [Finset.mem_coe, Finset.mem_Icc]
  have hnonzero : triangle N j ≠ 0 := Function.mem_support.mp hj
  have hlt : |j| < (N : ℤ) := by
    by_contra h
    exact hnonzero (triangle_support N j (by omega))
  have hb := abs_lt.mp hlt
  omega

private theorem triangle_outside (N : ℕ) (k : ℤ)
    (hk : k ∉ Finset.Icc (-(N : ℤ)) (N : ℤ)) : triangle N k = 0 := by
  apply triangle_support
  simp only [Finset.mem_Icc, not_and_or, not_le] at hk
  rcases hk with hk | hk
  · rw [abs_of_nonpos (by omega : k ≤ 0)]; omega
  · rw [abs_of_nonneg (by omega : 0 ≤ k)]; omega

/-- For [an order N](hyp:N) that is [positive](hyp:hN), [the sum over all integers of the absolute
values of the normalized Jackson coefficients is at most 2N](goal). -/
theorem normalizedCoeff_l1 (N : ℕ) (hN : 0 < N) :
    (∑' j : ℤ, |normalizedCoeff N j|) ≤ 2 * (N : ℝ) := by
  have htri := triangle_finite N
  have hconv (j : ℤ) :
      convolution N j = ∑' k : ℤ, triangle N k * triangle N (j - k) := by
    exact (finite_convolution_tsum_eq_sum _ _ _ (triangle_outside N) j).symm
  have hmass : (∑' j : ℤ, |convolution N j|) ≤ (N : ℝ) ^ 4 := by
    have h := finite_convolution_l1 (triangle N) (triangle N) htri htri
    simp_rw [← hconv] at h
    rw [triangle_l1] at h
    nlinarith
  have hpos := convolution_zero_pos N hN
  have hscale : (∑' j : ℤ, |normalizedCoeff N j|) =
      (∑' j : ℤ, |convolution N j|) / convolution N 0 := by
    simp_rw [normalizedCoeff, abs_div, abs_of_pos hpos, div_eq_mul_inv]
    rw [tsum_mul_right]
  rw [hscale]
  have hn : (0 : ℝ) ≤ N := by positivity
  rw [convolution_zero N] at hpos ⊢
  apply (div_le_iff₀ hpos).2
  nlinarith [sq_nonneg ((N : ℝ) ^ 2), sq_nonneg (N : ℝ)]

private theorem delta_triangle_outside (N : ℕ) (j : ℤ)
    (hj : j ∉ Finset.Icc (-(N : ℤ) - 1) (N : ℤ)) :
    delta (triangle N) j = 0 := by
  simp only [Finset.mem_Icc, not_and_or, not_le] at hj
  rcases hj with hj | hj
  · have hz0 : triangle N j = 0 := triangle_support N j (by
      rw [abs_of_nonpos (by omega : j ≤ 0)]; omega)
    have hz1 : triangle N (j + 1) = 0 := triangle_support N (j + 1) (by
      rw [abs_of_nonpos (by omega : j + 1 ≤ 0)]; omega)
    simp [delta, hz0, hz1]
  · have hz0 : triangle N j = 0 := triangle_support N j (by
      rw [abs_of_nonneg (by omega : 0 ≤ j)]; omega)
    have hz1 : triangle N (j + 1) = 0 := triangle_support N (j + 1) (by
      rw [abs_of_nonneg (by omega : 0 ≤ j + 1)]; omega)
    simp [delta, hz0, hz1]

private theorem delta_triangle_finite (N : ℕ) :
    Function.HasFiniteSupport (delta (triangle N)) := by
  apply (Finset.finite_toSet (Finset.Icc (-(N : ℤ) - 1) (N : ℤ))).subset
  intro j hj
  by_contra h
  exact (Function.mem_support.mp hj) (delta_triangle_outside N j (by simpa using h))

/-- For [an order N](hyp:N) that is [positive](hyp:hN), [the sum over all integers of the absolute
first differences of the normalized Jackson coefficients is at most four](goal). -/
theorem normalizedCoeff_delta_l1 (N : ℕ) (hN : 0 < N) :
    (∑' j : ℤ, |delta (normalizedCoeff N) j|) ≤ 4 := by
  have hraw (j : ℤ) : delta (convolution N) j =
      ∑' k : ℤ, delta (triangle N) k * triangle N (j - k) := by
    rw [delta_convolution]
    exact (finite_convolution_tsum_eq_sum _ _ _ (delta_triangle_outside N) j).symm
  have hmass : (∑' j : ℤ, |delta (convolution N) j|) ≤
      2 * (N : ℝ) ^ 3 := by
    have h := finite_convolution_l1 (delta (triangle N)) (triangle N)
      (delta_triangle_finite N) (triangle_finite N)
    simp_rw [← hraw] at h
    rw [triangle_delta_l1, triangle_l1] at h
    nlinarith
  have hpos := convolution_zero_pos N hN
  have hdiff (j : ℤ) : delta (normalizedCoeff N) j =
      delta (convolution N) j / convolution N 0 := by
    unfold delta normalizedCoeff
    ring
  have hscale : (∑' j : ℤ, |delta (normalizedCoeff N) j|) =
      (∑' j : ℤ, |delta (convolution N) j|) / convolution N 0 := by
    simp_rw [hdiff, abs_div, abs_of_pos hpos, div_eq_mul_inv]
    rw [tsum_mul_right]
  rw [hscale]
  rw [convolution_zero N] at hpos ⊢
  apply (div_le_iff₀ hpos).2
  have hn : (0 : ℝ) ≤ N := by positivity
  nlinarith [sq_nonneg (N : ℝ)]

/-- For [an order N](hyp:N) that is [positive](hyp:hN), [the sum over all integers of the absolute
second differences of the normalized Jackson coefficients is at most 6 / N](goal). -/
theorem normalizedCoeff_delta2_l1 (N : ℕ) (hN : 0 < N) :
    (∑' j : ℤ, |delta2 (normalizedCoeff N) j|) ≤ 6 / (N : ℝ) := by
  have hraw (j : ℤ) : delta2 (convolution N) j =
      ∑' k : ℤ, delta (triangle N) k * delta (triangle N) (j - k) := by
    rw [delta2_convolution]
    exact (finite_convolution_tsum_eq_sum _ _ _ (delta_triangle_outside N) j).symm
  have hmass : (∑' j : ℤ, |delta2 (convolution N) j|) ≤
      4 * (N : ℝ) ^ 2 := by
    have h := finite_convolution_l1 (delta (triangle N)) (delta (triangle N))
      (delta_triangle_finite N) (delta_triangle_finite N)
    simp_rw [← hraw] at h
    rw [triangle_delta_l1] at h
    nlinarith
  have hpos := convolution_zero_pos N hN
  have hdiff (j : ℤ) : delta2 (normalizedCoeff N) j =
      delta2 (convolution N) j / convolution N 0 := by
    unfold delta2 delta normalizedCoeff
    ring
  have hscale : (∑' j : ℤ, |delta2 (normalizedCoeff N) j|) =
      (∑' j : ℤ, |delta2 (convolution N) j|) / convolution N 0 := by
    simp_rw [hdiff, abs_div, abs_of_pos hpos, div_eq_mul_inv]
    rw [tsum_mul_right]
  rw [hscale]
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  rw [convolution_zero N] at hpos ⊢
  apply (div_le_iff₀ hpos).2
  rw [show 6 / (N : ℝ) * ((2 * (N : ℝ) ^ 3 + N) / 3) =
      (6 * ((2 * (N : ℝ) ^ 3 + N) / 3)) / N by ring]
  apply (le_div_iff₀ hn).2
  have hmul := mul_le_mul_of_nonneg_right hmass hn.le
  nlinarith [sq_nonneg (N : ℝ)]

end Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson

