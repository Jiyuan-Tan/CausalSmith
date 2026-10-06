module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.LowerBound.NormalizedLagrange

/-! # Scale arithmetic for normalized paired concentration -/

public section

open scoped ENNReal
namespace CausalSmith.Stat.MarNearcompleteFrontier

-- @node: one_le_ell_scale
/-- Given [the specified input `n`](hyp:n), [the stated mathematical conclusion holds](goal). -/
lemma one_le_ell_scale (n : ℕ) : 1 ≤ ell n := by
  unfold ell
  calc
    1 = Real.log (Real.exp 1) := (Real.log_exp _).symm
    _ ≤ Real.log (Real.exp 1 + n) :=
      Real.log_le_log (Real.exp_pos _) (le_add_of_nonneg_right (Nat.cast_nonneg _))

-- @node: priorK_le_nine_ell
/-- Given [the specified input `n`](hyp:n), [the stated mathematical conclusion holds](goal). -/
lemma priorK_le_nine_ell (n : ℕ) : (priorK n : ℝ) ≤ 9 * ell n := by
  have hell := one_le_ell_scale n
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ 8 * ell n by positivity)
  change (priorK n : ℝ) < 8 * ell n + 1 at hceil
  linarith [one_le_ell_scale n]

-- @node: nat_half_sub_one_lower
/-- Given [the specified input `d`](hyp:d), [the specified input `hd`](hyp:hd), [the stated mathematical conclusion holds](goal). -/
lemma nat_half_sub_one_lower {d : ℕ} (hd : 3 ≤ d) :
    (d : ℝ) / 4 ≤ (((d - 1) / 2 : ℕ) : ℝ) := by
  have hnat : d ≤ 4 * ((d - 1) / 2) := by omega
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).2
  exact_mod_cast (show d ≤ ((d - 1) / 2) * 4 by simpa [mul_comm] using hnat)

-- @node: floor_half_lower
/-- Given [the specified input `x`](hyp:x), [the specified input `hx`](hyp:hx), [the stated mathematical conclusion holds](goal). -/
lemma floor_half_lower {x : ℝ} (hx : 2 ≤ x) : x / 2 ≤ (Nat.floor x : ℝ) := by
  have hfloor := Nat.sub_one_lt_floor x
  linarith

-- @node: pairCount_lower_quarter
/-- Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hd`](hyp:hd), [the specified input `n`](hyp:n), [the stated mathematical conclusion holds](goal). Given [the specified input `hnell`](hyp:hnell). -/
lemma pairCount_lower_quarter (n d : ℕ) (hd : 3 ≤ d)
    (hnell : 2 ≤ (n : ℝ) * ell n) :
    (1 / 4 : ℝ) * min (d : ℝ) ((n : ℝ) * ell n) ≤ pairCount n d := by
  have hA := nat_half_sub_one_lower hd
  have hB := floor_half_lower hnell
  unfold pairCount
  push_cast
  apply le_min
  · calc
      (1 / 4 : ℝ) * min (d : ℝ) ((n : ℝ) * ell n) ≤ (d : ℝ) / 4 := by
        have := min_le_left (d : ℝ) ((n : ℝ) * ell n)
        linarith
      _ ≤ _ := hA
  · calc
      (1 / 4 : ℝ) * min (d : ℝ) ((n : ℝ) * ell n) ≤
          ((n : ℝ) * ell n) / 4 := by
        have := min_le_right (d : ℝ) ((n : ℝ) * ell n)
        linarith
      _ ≤ ((n : ℝ) * ell n) / 2 := by nlinarith
      _ ≤ _ := hB

-- @node: regime_dimension_ge_three
/-- Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `n`](hyp:n), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq), [the specified input `hreg`](hyp:hreg). -/
lemma regime_dimension_ge_three (n d : ℕ) (q : ℝ)
    (hn : 2 ≤ n) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (hreg : gScale n d q ^ 2 ≥ 1 / (n : ℝ)) : 3 ≤ d := by
  by_contra hd
  have hd2 : d ≤ 2 := by omega
  have hnpos : (0 : ℝ) < n := by positivity
  have hell := one_le_ell_scale n
  have hden : 0 < (n : ℝ) * ell n := mul_pos hnpos (lt_of_lt_of_le zero_lt_one hell)
  have hfrac0 : 0 ≤ (d : ℝ) / ((n : ℝ) * ell n) := div_nonneg (Nat.cast_nonneg _) hden.le
  have hr0 : 0 ≤ min 1 ((d : ℝ) / ((n : ℝ) * ell n)) := le_min (by norm_num) hfrac0
  have hrle : min 1 ((d : ℝ) / ((n : ℝ) * ell n)) ≤
      2 / ((n : ℝ) * ell n) := by
    calc
      _ ≤ (d : ℝ) / ((n : ℝ) * ell n) := min_le_right _ _
      _ ≤ 2 / ((n : ℝ) * ell n) := by gcongr; exact_mod_cast hd2
  have hδ0 : 0 ≤ delta q := by unfold delta; linarith [hq.2]
  have hδle : delta q ≤ 1 / 2 := by unfold delta; linarith [hq.1]
  have hg0 : 0 ≤ gScale n d q := mul_nonneg hδ0 hr0
  have hgle : gScale n d q ≤ 1 / (n : ℝ) := by
    unfold gScale
    calc
      delta q * min 1 ((d : ℝ) / ((n : ℝ) * ell n)) ≤
          (1 / 2 : ℝ) * (2 / ((n : ℝ) * ell n)) :=
        by
          have h1 := mul_nonneg (sub_nonneg.mpr hδle) hr0
          have h2 := mul_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num)
            (sub_nonneg.mpr hrle)
          nlinarith
      _ ≤ 1 / (n : ℝ) := by
        rw [show (1 / 2 : ℝ) * (2 / ((n : ℝ) * ell n)) =
          1 / ((n : ℝ) * ell n) by ring]
        exact one_div_le_one_div_of_le hnpos (by nlinarith)
  have hsquare : gScale n d q ^ 2 ≤ (1 / (n : ℝ)) ^ 2 := by nlinarith
  have hstrict : (1 / (n : ℝ)) ^ 2 < 1 / (n : ℝ) := by
    have : (1 : ℝ) < n := by exact_mod_cast hn
    have hinv : 0 < 1 / (n : ℝ) := by positivity
    have hinv1 : 1 / (n : ℝ) < 1 := (div_lt_one hnpos).2 this
    nlinarith
  linarith

-- @node: pairCount_scale_lower
/-- Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `n`](hyp:n), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq), [the specified input `hreg`](hyp:hreg). -/
lemma pairCount_scale_lower (n d : ℕ) (q : ℝ)
    (hn : 2 ≤ n) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (hreg : gScale n d q ^ 2 ≥ 1 / (n : ℝ)) :
    (1 / 36 : ℝ) * min 1 ((d : ℝ) / ((n : ℝ) * ell n)) ≤
      (pairCount n d : ℝ) / ((n : ℝ) * (priorK n : ℝ)) := by
  have hd := regime_dimension_ge_three n d q hn hq hreg
  have hell := one_le_ell_scale n
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnell : 2 ≤ (n : ℝ) * ell n := by nlinarith
  have hm := pairCount_lower_quarter n d hd hnell
  have hk := priorK_le_nine_ell n
  have hnpos : (0 : ℝ) < n := by positivity
  have hellpos : 0 < ell n := lt_of_lt_of_le zero_lt_one hell
  have hK := priorK_ge_two n
  have hkpos : (0 : ℝ) < priorK n := by
    exact_mod_cast (show 0 < priorK n by omega)
  have hidentity : min (d : ℝ) ((n : ℝ) * ell n) =
      (n : ℝ) * ell n * min 1 ((d : ℝ) / ((n : ℝ) * ell n)) := by
    rw [mul_min_of_nonneg _ _ (mul_nonneg hnpos.le hellpos.le)]
    field_simp [hnpos.ne', hellpos.ne']
    rw [min_comm]
  rw [hidentity] at hm
  apply (le_div_iff₀ (mul_pos hnpos hkpos)).2
  have hr0 : 0 ≤ min 1 ((d : ℝ) / ((n : ℝ) * ell n)) := by positivity
  calc
    (1 / 36 : ℝ) * min 1 ((d : ℝ) / ((n : ℝ) * ell n)) *
        ((n : ℝ) * (priorK n : ℝ)) ≤
      (1 / 4 : ℝ) * ((n : ℝ) * ell n *
        min 1 ((d : ℝ) / ((n : ℝ) * ell n))) := by
      nlinarith [mul_le_mul_of_nonneg_left hk (mul_nonneg hnpos.le hr0)]
    _ ≤ _ := hm

-- @node: eventually_ell_sq_le
/-- [the stated mathematical conclusion holds](goal). Given [the specified input `ε`](hyp:ε), [the specified input `hε`](hyp:hε). -/
lemma eventually_ell_sq_le (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ell n ^ 2 ≤ ε * (n : ℝ) := by
  open Filter in
  let C : ℝ := Real.exp 1 + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hsmall : 0 < ε / C := div_pos hε hC
  have hbound := (Real.isLittleO_pow_log_id_atTop (n := 2)).bound hsmall
  have ht : Tendsto (fun n : ℕ => Real.exp 1 + (n : ℝ)) atTop atTop := by
    exact tendsto_const_nhds.add_atTop tendsto_natCast_atTop_atTop
  have he : ∀ᶠ n : ℕ in atTop,
      ell n ^ 2 ≤ (ε / C) * (Real.exp 1 + (n : ℝ)) := by
    filter_upwards [hbound.filter_mono ht] with n hn
    have hx0 : 0 ≤ Real.exp 1 + (n : ℝ) := by positivity
    have hlog0 : 0 ≤ Real.log (Real.exp 1 + (n : ℝ)) :=
      Real.log_nonneg (by
        have := Real.one_lt_exp_iff.mpr (show (0 : ℝ) < 1 by norm_num)
        have hnnon : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith)
    simpa [ell, Real.norm_eq_abs, abs_of_nonneg hlog0, abs_of_nonneg hx0,
      div_eq_mul_inv] using hn
  rw [eventually_atTop] at he
  obtain ⟨N0, hN0⟩ := he
  refine ⟨max N0 1, ?_⟩
  intro n hn
  have hn0 : N0 ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hn1 : 1 ≤ n := le_trans (Nat.le_max_right _ _) hn
  have hxn : Real.exp 1 + (n : ℝ) ≤ C * (n : ℝ) := by
    dsimp [C]
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    nlinarith [mul_nonneg (Real.exp_pos 1).le (sub_nonneg.mpr (sub_nonneg.mpr hnR))]
  calc
    ell n ^ 2 ≤ (ε / C) * (Real.exp 1 + (n : ℝ)) := hN0 n hn0
    _ ≤ (ε / C) * (C * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hxn (div_nonneg hε.le hC.le)
    _ = ε * (n : ℝ) := by field_simp [hC.ne']

-- @node: regime_min_scale_sq_lower
/-- Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `q`](hyp:q), [the specified input `hn`](hyp:hn), [the specified input `n`](hyp:n), [the stated mathematical conclusion holds](goal). Given [the specified input `hq`](hyp:hq), [the specified input `hreg`](hyp:hreg). -/
lemma regime_min_scale_sq_lower (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hq : q ∈ Set.Icc ((1 : ℝ) / 2) 1)
    (hreg : gScale n d q ^ 2 ≥ 1 / (n : ℝ)) :
    4 / (n : ℝ) ≤ (min 1 ((d : ℝ) / ((n : ℝ) * ell n))) ^ 2 := by
  let r := min 1 ((d : ℝ) / ((n : ℝ) * ell n))
  have hnpos : (0 : ℝ) < n := by positivity
  have hellpos : 0 < ell n := lt_of_lt_of_le zero_lt_one (one_le_ell_scale n)
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hδ0 : 0 ≤ delta q := by unfold delta; linarith [hq.2]
  have hδle : delta q ≤ 1 / 2 := by unfold delta; linarith [hq.1]
  have hδsq : delta q ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by nlinarith
  have hgsq : gScale n d q ^ 2 = delta q ^ 2 * r ^ 2 := by
    simp [gScale, r]
    ring
  have hr_sq0 : 0 ≤ r ^ 2 := sq_nonneg _
  rw [hgsq] at hreg
  have hchain : 1 / (n : ℝ) ≤ (1 / 2 : ℝ) ^ 2 * r ^ 2 :=
    le_trans hreg (mul_le_mul_of_nonneg_right hδsq hr_sq0)
  calc
    4 / (n : ℝ) = 4 * (1 / (n : ℝ)) := by ring
    _ ≤ 4 * ((1 / 2 : ℝ) ^ 2 * r ^ 2) :=
      mul_le_mul_of_nonneg_left hchain (by norm_num)
    _ = r ^ 2 := by ring

-- @node: eventually_priorK_sq_div_pairCount_le
/-- [the stated mathematical conclusion holds](goal). Given [the specified input `η`](hyp:η), [the specified input `hη`](hyp:hη). -/
lemma eventually_priorK_sq_div_pairCount_le (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ (n d : ℕ) (q : ℝ), N ≤ n →
      q ∈ Set.Icc ((1 : ℝ) / 2) 1 →
      gScale n d q ^ 2 ≥ 1 / (n : ℝ) →
      (priorK n : ℝ) ^ 2 / (pairCount n d : ℝ) ≤ η := by
  obtain ⟨N0, hN0⟩ := eventually_ell_sq_le (η ^ 2 / 26244) (by positivity)
  refine ⟨max N0 2, le_max_right _ _, ?_⟩
  intro n d q hn hq hreg
  have hn0 : N0 ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hnpos : (0 : ℝ) < n := by positivity
  have hell := one_le_ell_scale n
  have hell0 : 0 ≤ ell n := le_trans (by norm_num) hell
  have hr0 : 0 ≤ min 1 ((d : ℝ) / ((n : ℝ) * ell n)) := by positivity
  have hr2 := regime_min_scale_sq_lower n d q (by omega) hq hreg
  have hd := regime_dimension_ge_three n d q hn2 hq hreg
  have hnell : 2 ≤ (n : ℝ) * ell n := by
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    nlinarith
  have hm := pairCount_lower_quarter n d hd hnell
  have hidentity : min (d : ℝ) ((n : ℝ) * ell n) =
      (n : ℝ) * ell n * min 1 ((d : ℝ) / ((n : ℝ) * ell n)) := by
    rw [mul_min_of_nonneg _ _ (mul_nonneg hnpos.le hell0)]
    field_simp [hnpos.ne', (lt_of_lt_of_le zero_lt_one hell).ne']
    rw [min_comm]
  rw [hidentity] at hm
  have hm0 : 0 ≤ (pairCount n d : ℝ) := Nat.cast_nonneg _
  have hbase0 : 0 ≤ (1 / 4 : ℝ) *
      ((n : ℝ) * ell n * min 1 ((d : ℝ) / ((n : ℝ) * ell n))) := by positivity
  have hm_sq := (sq_le_sq₀ hbase0 hm0).2 hm
  have hm_sq_lower : (n : ℝ) * ell n ^ 2 / 4 ≤ (pairCount n d : ℝ) ^ 2 := by
    have hr2' : (4 : ℝ) ≤ (n : ℝ) *
        min 1 ((d : ℝ) / ((n : ℝ) * ell n)) ^ 2 := by
      simpa [mul_comm] using (div_le_iff₀ hnpos).mp hr2
    calc
      (n : ℝ) * ell n ^ 2 / 4 ≤
          ((1 / 4 : ℝ) * ((n : ℝ) * ell n *
            min 1 ((d : ℝ) / ((n : ℝ) * ell n)))) ^ 2 := by
        nlinarith [mul_nonneg (sq_nonneg (ell n))
          (sub_nonneg.mpr hr2')]
      _ ≤ _ := hm_sq
  have hk := priorK_le_nine_ell n
  have hk0 : 0 ≤ (priorK n : ℝ) := Nat.cast_nonneg _
  have hk_sq : (priorK n : ℝ) ^ 2 ≤ 81 * ell n ^ 2 := by nlinarith
  have hk_four : ((priorK n : ℝ) ^ 2) ^ 2 ≤
      6561 * (ell n ^ 2) ^ 2 := by
    have hs := (sq_le_sq₀ (sq_nonneg (priorK n : ℝ))
      (mul_nonneg (by norm_num) (sq_nonneg (ell n)))).2 hk_sq
    nlinarith
  have heps := hN0 n hn0
  have htarget_sq : ((priorK n : ℝ) ^ 2) ^ 2 ≤
      η ^ 2 * (pairCount n d : ℝ) ^ 2 := by
    have hη2 : 0 ≤ η ^ 2 := sq_nonneg _
    have hmul := mul_le_mul_of_nonneg_left hm_sq_lower hη2
    nlinarith [hk_four, mul_nonneg (sq_nonneg (ell n))
      (sub_nonneg.mpr heps)]
  have hmpos : 0 < (pairCount n d : ℝ) := by
    have hrpos : 0 < min 1 ((d : ℝ) / ((n : ℝ) * ell n)) := by
      have hfour : 0 < (4 : ℝ) / (n : ℝ) := div_pos (by norm_num) hnpos
      have hspos : 0 < min 1 ((d : ℝ) / ((n : ℝ) * ell n)) ^ 2 :=
        lt_of_lt_of_le hfour hr2
      nlinarith
    exact lt_of_lt_of_le (mul_pos (by positivity)
      (mul_pos (mul_pos hnpos (lt_of_lt_of_le zero_lt_one hell)) hrpos)) hm
  apply (div_le_iff₀ hmpos).2
  nlinarith [mul_nonneg (sub_nonneg.mpr (show (0 : ℝ) ≤ η by linarith)) hm0]

end CausalSmith.Stat.MarNearcompleteFrontier
