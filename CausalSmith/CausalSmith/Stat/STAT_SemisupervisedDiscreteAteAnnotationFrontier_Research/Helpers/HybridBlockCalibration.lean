module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.HybridLogSchedule

/-! Exact arithmetic for the deterministic labeled/auxiliary block split. -/

public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

/-- Integer form of the uniform quarter/three-quarter block bounds.  [the stated conditions](hyp:hn) [the stated conclusion](goal). -/
lemma blockSizes_nat_bounds (n m : Nat) (hn : 24 ≤ n) :
    n ≤ 4 * (blockSizes n m).M0 ∧
    3 * (blockSizes n m).M0 ≤ n ∧
    n + m ≤ 4 * ((blockSizes n m).np + (blockSizes n m).mp) ∧
    4 * ((blockSizes n m).np + (blockSizes n m).mp) ≤ 3 * (n + m) ∧
    n + m ≤ 4 * ((blockSizes n m).nf + (blockSizes n m).mf) ∧
    4 * ((blockSizes n m).nf + (blockSizes n m).mf) ≤ 3 * (n + m) := by
  simp only [blockSizes]
  omega

/-- The deterministic intensities satisfy all ratio bounds in C15.  [the stated conditions](hyp:hn) [the stated conclusion](goal). -/
lemma blockSizes_intensity_ratios (n m : Nat) (hn : 24 ≤ n) :
    let bs := blockSizes n m
    let N : Nat := n + m
    let u : Real := bs.M0 / 8
    let tp : Real := (bs.np + bs.mp : Nat) / 8
    let t : Real := (bs.nf + bs.mf : Nat) / 8
    1 / 32 ≤ u / n ∧ u / n ≤ 1 / 24 ∧
    1 / 32 ≤ tp / N ∧ tp / N ≤ 3 / 32 ∧
    1 / 32 ≤ t / N ∧ t / N ≤ 3 / 32 ∧
    1 / 3 ≤ t / tp ∧ t / tp ≤ 3 := by
  dsimp only
  rcases blockSizes_nat_bounds n m hn with ⟨hu0, hu1, hp0, hp1, hf0, hf1⟩
  have hnR : (0 : Real) < n := by positivity
  have hNR : (0 : Real) < n + m := by positivity
  have hpR : (0 : Real) < (blockSizes n m).np + (blockSizes n m).mp := by
    have : (0 : Nat) < (blockSizes n m).np + (blockSizes n m).mp := by omega
    exact_mod_cast this
  have hfR : (0 : Real) < (blockSizes n m).nf + (blockSizes n m).mf := by
    have : (0 : Nat) < (blockSizes n m).nf + (blockSizes n m).mf := by omega
    exact_mod_cast this
  have hu0R : (n : Real) ≤ 4 * (blockSizes n m).M0 := by exact_mod_cast hu0
  have hu1R : 3 * ((blockSizes n m).M0 : Real) ≤ n := by exact_mod_cast hu1
  have hp0R : (n + m : Real) ≤
      4 * ((blockSizes n m).np + (blockSizes n m).mp : Nat) := by exact_mod_cast hp0
  have hp1R : 4 * ((blockSizes n m).np + (blockSizes n m).mp : Nat) ≤
      3 * (n + m : Real) := by exact_mod_cast hp1
  have hf0R : (n + m : Real) ≤
      4 * ((blockSizes n m).nf + (blockSizes n m).mf : Nat) := by exact_mod_cast hf0
  have hf1R : 4 * ((blockSizes n m).nf + (blockSizes n m).mf : Nat) ≤
      3 * (n + m : Real) := by exact_mod_cast hf1
  norm_num [Nat.cast_add] at *
  constructor
  · field_simp
    nlinarith
  constructor
  · field_simp
    nlinarith
  constructor
  · field_simp
    nlinarith
  constructor
  · field_simp
    nlinarith
  constructor
  · field_simp
    nlinarith
  constructor
  · field_simp
    nlinarith
  constructor <;> field_simp [hpR.ne'] <;> nlinarith

/-- Multiplication by the calibrated bandwidth cancels its positive minimum
denominator.  This form is convenient for all three tail tests.  [the stated conditions](hyp:hn) [the stated conclusion](goal). -/
lemma blockSizes_mul_Bscale_lower (n m : Nat) (eps : Real) (hn : 24 ≤ n) :
    let bs := blockSizes n m
    let tp : Real := (bs.np + bs.mp : Nat) / 8
    let t : Real := (bs.nf + bs.mf : Nat) / 8
    let L : Real := Ldeg n
    let H : Real := Hconst eps
    H * L ≤ tp * Bscale n m eps ∧ H * L ≤ t * Bscale n m eps := by
  dsimp only
  have hr := blockSizes_intensity_ratios n m hn
  dsimp only at hr
  rcases hr with ⟨_, _, htpN, _, htN, _, _, _⟩
  have hN : (0 : Real) < n + m := by positivity
  have htp : 0 < (((blockSizes n m).np + (blockSizes n m).mp : Nat) : Real) / 8 := by
    have : 0 < ((((blockSizes n m).np + (blockSizes n m).mp : Nat) : Real) / 8) /
        (n + m : Nat) := lt_of_lt_of_le (by norm_num : (0 : Real) < 1 / 32) htpN
    rcases div_pos_iff.mp this with h | h
    · exact h.1
    · linarith
  have ht : 0 < (((blockSizes n m).nf + (blockSizes n m).mf : Nat) : Real) / 8 := by
    have : 0 < ((((blockSizes n m).nf + (blockSizes n m).mf : Nat) : Real) / 8) /
        (n + m : Nat) := lt_of_lt_of_le (by norm_num : (0 : Real) < 1 / 32) htN
    rcases div_pos_iff.mp this with h | h
    · exact h.1
    · linarith
  have hHL : 0 ≤ (Hconst eps : Real) * Ldeg n := by positivity
  have hmin : 0 < min
      ((((blockSizes n m).np + (blockSizes n m).mp : Nat) : Real) / 8)
      ((((blockSizes n m).nf + (blockSizes n m).mf : Nat) : Real) / 8) :=
    lt_min htp ht
  simp only [Bscale]
  constructor
  · calc
      (Hconst eps : Real) * Ldeg n ≤
          ((Hconst eps : Real) * Ldeg n) /
            min ((((blockSizes n m).np + (blockSizes n m).mp : Nat) : Real) / 8)
              ((((blockSizes n m).nf + (blockSizes n m).mf : Nat) : Real) / 8) *
            ((((blockSizes n m).np + (blockSizes n m).mp : Nat) : Real) / 8) := by
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ hmin).2
        exact mul_le_mul_of_nonneg_left (min_le_left _ _) hHL
      _ = _ := by ring
  · calc
      (Hconst eps : Real) * Ldeg n ≤
          ((Hconst eps : Real) * Ldeg n) /
            min ((((blockSizes n m).np + (blockSizes n m).mp : Nat) : Real) / 8)
              ((((blockSizes n m).nf + (blockSizes n m).mf : Nat) : Real) / 8) *
            ((((blockSizes n m).nf + (blockSizes n m).mf : Nat) : Real) / 8) := by
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ hmin).2
        exact mul_le_mul_of_nonneg_left (min_le_right _ _) hHL
      _ = _ := by ring

/-- When [the unrounded pilot scale is at least eight](hyp:h), [the floored pilot threshold retains at least one eighth of that scale](goal). -/
lemma k0_lower_eighth (n m : Nat) (eps : Real) (h :
    let bs := blockSizes n m
    let tp : Real := (bs.np + bs.mp : Nat) / 8
    8 ≤ tp * Bscale n m eps) :
    let bs := blockSizes n m
    let tp : Real := (bs.np + bs.mp : Nat) / 8
    tp * Bscale n m eps / 8 ≤ (k0 n m eps : Real) := by
  dsimp only at h ⊢
  let x : Real :=
    (((blockSizes n m).np + (blockSizes n m).mp : Nat) : Real) / 8 *
      Bscale n m eps / 4
  have hx2 : 2 ≤ x := by dsimp [x]; linarith
  have hfloor0 : (0 : Int) ≤ ⌊x⌋ := by rw [Int.floor_nonneg]; linarith
  have hcast : ((Int.toNat ⌊x⌋ : Nat) : Real) = (⌊x⌋ : Int) := by
    exact_mod_cast Int.toNat_of_nonneg hfloor0
  have hfloor := Int.lt_floor_add_one x
  simp only [k0]
  change (((blockSizes n m).np + (blockSizes n m).mp : Nat) : Real) / 8 *
      Bscale n m eps / 8 ≤ ((Int.toNat ⌊x⌋ : Nat) : Real)
  rw [show ((((blockSizes n m).np + (blockSizes n m).mp : Nat) : Real) / 8 *
      Bscale n m eps / 8) = x / 2 by dsimp [x]; ring]
  rw [hcast]
  have hfloorR : x < ((⌊x⌋ : Int) : Real) + 1 := by exact_mod_cast hfloor
  linarith

/-- When [the pilot scale is nonnegative](hyp:h), [the floored pilot threshold is at most one quarter of that scale](goal). -/
lemma k0_upper_quarter (n m : Nat) (eps : Real) (h :
    let bs := blockSizes n m
    let tp : Real := (bs.np + bs.mp : Nat) / 8
    0 ≤ tp * Bscale n m eps) :
    let bs := blockSizes n m
    let tp : Real := (bs.np + bs.mp : Nat) / 8
    (k0 n m eps : Real) ≤ tp * Bscale n m eps / 4 := by
  dsimp only at h ⊢
  let x : Real :=
    (((blockSizes n m).np + (blockSizes n m).mp : Nat) : Real) / 8 *
      Bscale n m eps / 4
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hfloor0 : (0 : Int) ≤ ⌊x⌋ := by rw [Int.floor_nonneg]; exact hx
  have hcast : ((Int.toNat ⌊x⌋ : Nat) : Real) = (⌊x⌋ : Int) := by
    exact_mod_cast Int.toNat_of_nonneg hfloor0
  simp only [k0]
  change ((Int.toNat ⌊x⌋ : Nat) : Real) ≤ x
  rw [hcast]
  exact Int.floor_le x

/-- Turning the logarithmic tail exponent into the exact rational-power test
used in the finite calibration predicate.  [the stated conditions](hyp:hn,hb,hlog) [the stated conclusion](goal). -/
lemma pow_tail_test_of_log {n k : Nat} {b : Real} (hn : 1 ≤ n)
    (hb : 0 < b) (hlog : 12 * binLen n ≤ (k : Real) * Real.log b) :
    (n : Real) ^ 12 ≤ b ^ k := by
  have hnR : (0 : Real) < n := by positivity
  have hlogn : Real.log (n : Real) ≤ binLen n := by
    have h := logEN_le_binLen n hn
    have hs : logEN n = 1 + Real.log (n : Real) := by
      rw [logEN, Real.log_mul (by positivity : Real.exp 1 ≠ 0) hnR.ne']
      simp
    rw [hs] at h
    linarith
  rw [← Real.log_le_log_iff (pow_pos hnR _) (pow_pos hb _)]
  rw [Real.log_pow, Real.log_pow]
  push_cast
  nlinarith

/-- Exact two-sided bandwidth comparison (C33).  [the stated conditions](hyp:hn) [the stated conclusion](goal). -/
lemma Bscale_bounds (n m : Nat) (eps : Real) (hn : 24 ≤ n) :
    32 * Hconst eps * Ldeg n / (3 * (n + m : Nat)) ≤ Bscale n m eps ∧
      Bscale n m eps ≤ 32 * Hconst eps * Ldeg n / (n + m : Nat) := by
  have hr := blockSizes_intensity_ratios n m hn
  dsimp only at hr
  rcases hr with ⟨_, _, hp0, hp1, hf0, hf1, _, _⟩
  let N : Real := n + m
  let tp : Real := ((blockSizes n m).np + (blockSizes n m).mp : Nat) / 8
  let t : Real := ((blockSizes n m).nf + (blockSizes n m).mf : Nat) / 8
  have hN : 0 < N := by dsimp [N]; positivity
  have hp0' : 1 / 32 ≤ tp / N := by
    simpa [tp, N, Nat.cast_add] using hp0
  have hp1' : tp / N ≤ 3 / 32 := by
    simpa [tp, N, Nat.cast_add] using hp1
  have hf0' : 1 / 32 ≤ t / N := by
    simpa [t, N, Nat.cast_add] using hf0
  have hf1' : t / N ≤ 3 / 32 := by
    simpa [t, N, Nat.cast_add] using hf1
  have htp0 : N / 32 ≤ tp := by
    have hx := (le_div_iff₀ hN).1 hp0'
    nlinarith
  have htp1 : tp ≤ 3 * N / 32 := by
    apply (div_le_iff₀ hN).mp at hp1'
    nlinarith
  have ht0 : N / 32 ≤ t := by
    have hx := (le_div_iff₀ hN).1 hf0'
    nlinarith
  have ht1 : t ≤ 3 * N / 32 := by
    apply (div_le_iff₀ hN).mp at hf1'
    nlinarith
  have hmin0 : 0 < min tp t := lt_of_lt_of_le (by positivity : 0 < N / 32)
    (le_min htp0 ht0)
  have hHL : 0 ≤ (Hconst eps : Real) * Ldeg n := by positivity
  have hminlo : N / 32 ≤ min tp t := le_min htp0 ht0
  have hminhi : min tp t ≤ 3 * N / 32 := (min_le_left _ _).trans htp1
  simp only [Bscale, Nat.cast_add]
  dsimp [N, tp, t] at hN hmin0 hminlo hminhi ⊢
  norm_num [Nat.cast_add] at hmin0 hminlo hminhi ⊢
  let q : Real := min
    ((((blockSizes n m).np : Real) + (blockSizes n m).mp) / 8)
    ((((blockSizes n m).nf : Real) + (blockSizes n m).mf) / 8)
  have hq0 : 0 < q := by
    dsimp [q]
    exact lt_min (div_pos hmin0.1 (by norm_num))
      (div_pos hmin0.2 (by norm_num))
  have hqlo : (n + m : Real) / 32 ≤ q := by
    dsimp [q]
    exact le_min hminlo.1 hminlo.2
  have hqhi : q ≤ 3 * (n + m : Real) / 32 := by
    dsimp [q]
    rcases hminhi with h | h
    · exact (min_le_left _ _).trans h
    · exact (min_le_right _ _).trans h
  change 32 * (Hconst eps : Real) * Ldeg n / (3 * (n + m : Real)) ≤
      (Hconst eps : Real) * Ldeg n / q ∧
    (Hconst eps : Real) * Ldeg n / q ≤
      32 * (Hconst eps : Real) * Ldeg n / (n + m : Real)
  constructor
  · field_simp [hN.ne', hq0.ne']
    have := mul_nonneg (sub_nonneg.mpr hqhi) hHL
    nlinarith
  · field_simp [hN.ne', hq0.ne']
    have := mul_nonneg (sub_nonneg.mpr hqlo) hHL
    nlinarith

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
