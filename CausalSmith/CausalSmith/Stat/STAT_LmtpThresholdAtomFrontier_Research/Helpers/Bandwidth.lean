/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Basic

/-!
# Information-balance bandwidth regimes

`AsympSeq` records the explicit eventual two-sided constant sandwich used by
the paper. The theorem keeps the threshold sequence arbitrary.
-/

namespace CausalSmith.Stat.LmtpThresholdAtomFrontier

open Filter Set

noncomputable section

/-- Two positive constants eventually sandwich one nonnegative sequence by another. -/
def AsympSeq (f g : ℕ → ℝ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
    ∀ᶠ n in atTop, c * g n ≤ f n ∧ f n ≤ C * g n

/-- Eventually the infimum in `infoBandwidth` is the unique positive
information-balance root. The result uses [the `hbeta` condition](hyp:hbeta), [the `hkappa` condition](hyp:hkappa), [the `hdeltaBar` condition](hyp:hdeltaBar), [the `hdelta` condition](hyp:hdelta). [This is the stated conclusion](goal).
-/
-- @node: infoBandwidth_eventually_balance
lemma infoBandwidth_eventually_balance
    (beta kappa deltaBar : ℝ) (hbeta : 0 < beta) (hkappa : 0 ≤ kappa)
    (hdeltaBar : 0 < deltaBar ∧ deltaBar < 1)
    (deltaSeq : ℕ → ℝ) (hdelta : ThresholdSequence deltaBar deltaSeq) :
    ∀ᶠ n in atTop,
      0 < infoBandwidth n (deltaSeq n) beta kappa deltaBar ∧
      infoBandwidth n (deltaSeq n) beta kappa deltaBar ≤ 1 - deltaBar ∧
      (n : ℝ) * infoBandwidth n (deltaSeq n) beta kappa deltaBar ^
          (2 * beta + 1) *
        (deltaSeq n + infoBandwidth n (deltaSeq n) beta kappa deltaBar) ^ kappa = 1 := by
  let H : ℝ := 1 - deltaBar
  have hH : 0 < H := sub_pos.mpr hdeltaBar.2
  have hp : 0 < 2 * beta + 1 := by linarith
  have hK : 0 < H ^ (2 * beta + 1) * H ^ kappa :=
    mul_pos (Real.rpow_pos_of_pos hH _) (Real.rpow_pos_of_pos hH _)
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / (H ^ (2 * beta + 1) * H ^ kappa))
  filter_upwards [eventually_ge_atTop N] with n hn
  have hnpos : 0 < n := by
    by_contra hn0
    have hnz : n = 0 := Nat.eq_zero_of_not_pos hn0
    have hNz : N = 0 := Nat.le_zero.mp (hnz ▸ hn)
    subst N
    norm_num at hN
    have : 0 < (H ^ kappa)⁻¹ * (H ^ (2 * beta + 1))⁻¹ := by positivity
    linarith
  let F : ℝ → ℝ := fun h => (n : ℝ) * h ^ (2 * beta + 1) *
    (deltaSeq n + h) ^ kappa
  have hd := hdelta n
  have hFH : 1 ≤ F H := by
    have hbase : H ≤ deltaSeq n + H := by linarith [hd.1]
    have hrpow : H ^ kappa ≤ (deltaSeq n + H) ^ kappa :=
      Real.rpow_le_rpow (le_of_lt hH) hbase hkappa
    have hnK : 1 < (n : ℝ) * (H ^ (2 * beta + 1) * H ^ kappa) := by
      have hnR : 1 / (H ^ (2 * beta + 1) * H ^ kappa) < (n : ℝ) :=
        lt_of_lt_of_le hN (by exact_mod_cast hn)
      calc
        1 = (1 / (H ^ (2 * beta + 1) * H ^ kappa)) *
            (H ^ (2 * beta + 1) * H ^ kappa) := by field_simp
        _ < (n : ℝ) * (H ^ (2 * beta + 1) * H ^ kappa) :=
          mul_lt_mul_of_pos_right hnR hK
    dsimp [F]
    calc
      1 ≤ (n : ℝ) * (H ^ (2 * beta + 1) * H ^ kappa) := hnK.le
      _ = (n : ℝ) * H ^ (2 * beta + 1) * H ^ kappa := by ring
      _ ≤ (n : ℝ) * H ^ (2 * beta + 1) * (deltaSeq n + H) ^ kappa := by
        gcongr
  have hFcont : ContinuousOn F (Set.Icc 0 H) := by
    unfold F
    by_cases hkzero : kappa = 0
    · simp [hkzero]
      exact continuousOn_const.mul
        (continuousOn_id.rpow continuousOn_const (fun _ _ => Or.inr hp))
    · exact (continuousOn_const.mul
          (continuousOn_id.rpow continuousOn_const (fun _ _ => Or.inr hp))).mul
        ((continuousOn_const.add continuousOn_id).rpow continuousOn_const
          (fun _ _ => Or.inr (lt_of_le_of_ne hkappa (Ne.symm hkzero))))
  have hF0 : F 0 = 0 := by
    simp [F, Real.zero_rpow hp.ne']
  obtain ⟨r, hrI, hr⟩ : ∃ r ∈ Set.Icc (0 : ℝ) H, F r = 1 := by
    have hone : (1 : ℝ) ∈ Set.Icc (F 0) (F H) := by simpa [hF0] using hFH
    rcases intermediate_value_Icc hH.le hFcont hone with ⟨r, hrI, hr⟩
    exact ⟨r, hrI, hr⟩
  have hrpos : 0 < r := by
    rcases hrI with ⟨hr0, _⟩
    exact lt_of_le_of_ne hr0 (fun hre => by subst r; simp [hF0] at hr)
  have hFstrict : StrictMonoOn F (Set.Icc 0 H) := by
    intro a ha b hb hab
    have haPow : a ^ (2 * beta + 1) < b ^ (2 * beta + 1) :=
      Real.rpow_lt_rpow ha.1 hab hp
    have hbpos : 0 < b := lt_of_le_of_lt ha.1 hab
    have hdb : 0 < deltaSeq n + b := by linarith [hd.1]
    have hfac : 0 < (n : ℝ) * (deltaSeq n + b) ^ kappa :=
      mul_pos (by exact_mod_cast hnpos) (Real.rpow_pos_of_pos hdb _)
    have hmono : (deltaSeq n + a) ^ kappa ≤ (deltaSeq n + b) ^ kappa := by
      apply Real.rpow_le_rpow
      · linarith [hd.1, ha.1]
      · linarith
      · exact hkappa
    dsimp [F]
    calc
      (n : ℝ) * a ^ (2 * beta + 1) * (deltaSeq n + a) ^ kappa ≤
          (n : ℝ) * a ^ (2 * beta + 1) * (deltaSeq n + b) ^ kappa := by
            exact mul_le_mul_of_nonneg_left hmono
              (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg ha.1 _))
      _ < (n : ℝ) * b ^ (2 * beta + 1) * (deltaSeq n + b) ^ kappa := by
        exact mul_lt_mul_of_pos_right
          (mul_lt_mul_of_pos_left haPow (Nat.cast_pos.mpr hnpos))
          (Real.rpow_pos_of_pos hdb _)
  have hset : bandwidthCrossingSet n (deltaSeq n) beta kappa deltaBar =
      Set.Icc r H := by
    ext h
    simp only [bandwidthCrossingSet, Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · rintro ⟨hh0, hhH, hhF⟩
      refine ⟨?_, hhH⟩
      by_contra hnot
      have hlt : h < r := lt_of_not_ge hnot
      have := hFstrict ⟨hh0.le, hhH⟩ hrI hlt
      dsimp [F] at this
      linarith
    · rintro ⟨hrh, hhH⟩
      have hh0 : 0 < h := hrpos.trans_le hrh
      refine ⟨hh0, hhH, ?_⟩
      have := hFstrict.monotoneOn hrI ⟨hh0.le, hhH⟩ hrh
      dsimp [F] at this
      linarith
  have hnonempty : (bandwidthCrossingSet n (deltaSeq n) beta kappa deltaBar).Nonempty := by
    rw [hset]
    exact Set.nonempty_Icc.2 hrI.2
  have hbw : infoBandwidth n (deltaSeq n) beta kappa deltaBar = r := by
    simp [infoBandwidth, hnonempty, hset, hrI.2]
  rw [hbw]
  exact ⟨hrpos, hrI.2, by simpa [F] using hr⟩

/-- The balance equation bounds its positive root above by the interior-scale
closed form. The result uses [the `hn` condition](hyp:hn), [the `hd` condition](hyp:hd), [the `hh` condition](hyp:hh), [the `hp` condition](hyp:hp), [the `hk` condition](hyp:hk), [the `heq` condition](hyp:heq). [This is the stated conclusion](goal).
-/
-- @node: balance_root_le_interior_scale
lemma balance_root_le_interior_scale (n d h p k : ℝ)
    (hn : 0 < n) (hd : 0 < d) (hh : 0 < h) (hp : 0 < p) (hk : 0 ≤ k)
    (heq : n * h ^ p * (d + h) ^ k = 1) :
    h ≤ (n * d ^ k) ^ (-1 / p) := by
  have hX : 0 < n * d ^ k := mul_pos hn (Real.rpow_pos_of_pos hd _)
  rw [← Real.rpow_le_rpow_iff hh.le (Real.rpow_nonneg hX.le _) hp]
  rw [← Real.rpow_mul hX.le]
  have hexp : (-1 / p) * p = -1 := by field_simp
  rw [hexp, Real.rpow_neg_one]
  have hdk : d ^ k ≤ (d + h) ^ k :=
    Real.rpow_le_rpow hd.le (by linarith) hk
  have hmul : n * h ^ p * d ^ k ≤ n * h ^ p * (d + h) ^ k :=
    mul_le_mul_of_nonneg_left hdk
      (mul_nonneg hn.le (Real.rpow_nonneg hh.le p))
  rw [heq] at hmul
  rw [inv_eq_one_div]
  apply (le_div_iff₀ hX).2
  calc
    h ^ p * (n * d ^ k) = n * h ^ p * d ^ k := by ring
    _ ≤ 1 := hmul

/-- When the root lies below the threshold, it is also bounded below by a
fixed multiple of the interior scale. The result uses [the `hn` condition](hyp:hn), [the `hd` condition](hyp:hd), [the `hh` condition](hyp:hh), [the `hp` condition](hyp:hp), [the `hk` condition](hyp:hk), [the `hhd` condition](hyp:hhd), [the `heq` condition](hyp:heq). [This is the stated conclusion](goal).
-/
-- @node: interior_scale_le_balance_root
lemma interior_scale_le_balance_root (n d h p k : ℝ)
    (hn : 0 < n) (hd : 0 < d) (hh : 0 < h) (hp : 0 < p) (hk : 0 ≤ k)
    (hhd : h ≤ d) (heq : n * h ^ p * (d + h) ^ k = 1) :
    2 ^ (-k / p) * (n * d ^ k) ^ (-1 / p) ≤ h := by
  have htwo : 0 < (2 : ℝ) := by norm_num
  have hX : 0 < n * d ^ k := mul_pos hn (Real.rpow_pos_of_pos hd _)
  have hc : 0 < (2 : ℝ) ^ (-k / p) := Real.rpow_pos_of_pos htwo _
  rw [← Real.rpow_le_rpow_iff
    (mul_nonneg hc.le (Real.rpow_nonneg hX.le _)) hh.le hp]
  rw [Real.mul_rpow hc.le (Real.rpow_nonneg hX.le _)]
  rw [← Real.rpow_mul htwo.le, ← Real.rpow_mul hX.le]
  have hcExp : (-k / p) * p = -k := by field_simp
  have hXExp : (-1 / p) * p = -1 := by field_simp
  rw [hcExp, hXExp, Real.rpow_neg_one]
  have hadd : d + h ≤ 2 * d := by linarith
  have hpowadd : (d + h) ^ k ≤ (2 * d) ^ k :=
    Real.rpow_le_rpow (by linarith) hadd hk
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hd.le] at hpowadd
  have hmul : n * h ^ p * (d + h) ^ k ≤ n * h ^ p * (2 ^ k * d ^ k) :=
    mul_le_mul_of_nonneg_left hpowadd
      (mul_nonneg hn.le (Real.rpow_nonneg hh.le p))
  rw [heq] at hmul
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  have hden : 0 < 2 ^ k * (n * d ^ k) :=
    mul_pos (Real.rpow_pos_of_pos htwo _) hX
  have hmain : 1 / (2 ^ k * (n * d ^ k)) ≤ h ^ p := by
    apply (div_le_iff₀ hden).2
    calc
      1 ≤ n * h ^ p * (2 ^ k * d ^ k) := hmul
      _ = h ^ p * (2 ^ k * (n * d ^ k)) := by ring
  calc
    (2 ^ k)⁻¹ * (n * d ^ k)⁻¹ = 1 / (2 ^ k * (n * d ^ k)) := by field_simp
    _ ≤ h ^ p := hmain

/-- Above the edge scale, the interior closed-form scale is no larger than
the threshold. The result uses [the `hn` condition](hyp:hn), [the `hd` condition](hyp:hd), [the `hp` condition](hyp:hp), [the `hk` condition](hyp:hk), [the `hed` condition](hyp:hed). [This is the stated conclusion](goal).
-/
-- @node: interior_scale_le_threshold_of_edge_le
lemma interior_scale_le_threshold_of_edge_le (n d p k : ℝ)
    (hn : 0 < n) (hd : 0 < d) (hp : 0 < p) (hk : 0 ≤ k)
    (hed : n ^ (-1 / (p + k)) ≤ d) :
    (n * d ^ k) ^ (-1 / p) ≤ d := by
  have hpk : 0 < p + k := by linarith
  have hepos : 0 < n ^ (-1 / (p + k)) := Real.rpow_pos_of_pos hn _
  have hnpk : n * (n ^ (-1 / (p + k))) ^ (p + k) = 1 := by
    rw [← Real.rpow_mul hn.le]
    have : (-1 / (p + k)) * (p + k) = -1 := by field_simp
    rw [this, Real.rpow_neg_one]
    field_simp
  have hdpow : (n ^ (-1 / (p + k))) ^ (p + k) ≤ d ^ (p + k) :=
    Real.rpow_le_rpow hepos.le hed hpk.le
  have hone : 1 ≤ n * d ^ (p + k) := by
    rw [← hnpk]
    exact mul_le_mul_of_nonneg_left hdpow hn.le
  have hX : 0 < n * d ^ k := mul_pos hn (Real.rpow_pos_of_pos hd _)
  rw [← Real.rpow_le_rpow_iff (Real.rpow_nonneg hX.le _) hd.le hp]
  rw [← Real.rpow_mul hX.le]
  have hxexp : (-1 / p) * p = -1 := by field_simp
  rw [hxexp, Real.rpow_neg_one, inv_eq_one_div]
  apply (div_le_iff₀ hX).2
  calc
    1 ≤ n * d ^ (p + k) := hone
    _ = d ^ p * (n * d ^ k) := by rw [Real.rpow_add hd]; ring

/-- Every positive balance root is at most the edge scale. The result uses [the `hn` condition](hyp:hn), [the `hd` condition](hyp:hd), [the `hh` condition](hyp:hh), [the `hp` condition](hyp:hp), [the `hk` condition](hyp:hk), [the `heq` condition](hyp:heq). [This is the stated conclusion](goal).
-/
-- @node: balance_root_le_edge_scale
lemma balance_root_le_edge_scale (n d h p k : ℝ)
    (hn : 0 < n) (hd : 0 ≤ d) (hh : 0 < h) (hp : 0 < p) (hk : 0 ≤ k)
    (heq : n * h ^ p * (d + h) ^ k = 1) :
    h ≤ n ^ (-1 / (p + k)) := by
  have hpk : 0 < p + k := by linarith
  have hpow : h ^ k ≤ (d + h) ^ k :=
    Real.rpow_le_rpow hh.le (by linarith) hk
  have hmul : n * h ^ p * h ^ k ≤ n * h ^ p * (d + h) ^ k :=
    mul_le_mul_of_nonneg_left hpow
      (mul_nonneg hn.le (Real.rpow_nonneg hh.le p))
  rw [heq] at hmul
  rw [← Real.rpow_le_rpow_iff hh.le (Real.rpow_nonneg hn.le _) hpk]
  rw [← Real.rpow_mul hn.le]
  have hexp : (-1 / (p + k)) * (p + k) = -1 := by field_simp
  rw [hexp, Real.rpow_neg_one, inv_eq_one_div]
  apply (le_div_iff₀ hn).2
  calc
    h ^ (p + k) * n = n * (h ^ p * h ^ k) := by rw [Real.rpow_add hh]; ring
    _ ≤ 1 := by simpa [mul_assoc] using hmul

/-- Under an edge-scale upper bound on the threshold, a positive balance root
is bounded below by a fixed multiple of that edge scale. The result uses [the `hn` condition](hyp:hn), [the `hd` condition](hyp:hd), [the `hh` condition](hyp:hh), [the `hp` condition](hyp:hp), [the `hk` condition](hyp:hk), [the `hD` condition](hyp:hD), [the `heq` condition](hyp:heq), [the `hde` condition](hyp:hde), [the `hhe` condition](hyp:hhe). [This is the stated conclusion](goal).
-/
-- @node: edge_scale_le_balance_root
lemma edge_scale_le_balance_root (n d h p k D : ℝ)
    (hn : 0 < n) (hd : 0 ≤ d) (hh : 0 < h) (hp : 0 < p) (hk : 0 ≤ k)
    (hD : 0 < D) (heq : n * h ^ p * (d + h) ^ k = 1)
    (hde : d ≤ D * n ^ (-1 / (p + k)))
    (hhe : h ≤ n ^ (-1 / (p + k))) :
    (D + 1) ^ (-k / p) * n ^ (-1 / (p + k)) ≤ h := by
  have hpk : 0 < p + k := by linarith
  let e := n ^ (-1 / (p + k))
  have hepos : 0 < e := Real.rpow_pos_of_pos hn _
  have hDp : 0 < D + 1 := by linarith
  have hcpos : 0 < (D + 1) ^ (-k / p) := Real.rpow_pos_of_pos hDp _
  rw [← Real.rpow_le_rpow_iff (mul_nonneg hcpos.le hepos.le) hh.le hp]
  rw [Real.mul_rpow hcpos.le hepos.le]
  rw [← Real.rpow_mul hDp.le, ← Real.rpow_mul hn.le]
  have hcExp : (-k / p) * p = -k := by field_simp
  have heExp : (-1 / (p + k)) * p = -p / (p + k) := by ring
  rw [hcExp, heExp]
  have hsum : d + h ≤ (D + 1) * e := by dsimp [e] at *; linarith
  have hpow : (d + h) ^ k ≤ ((D + 1) * e) ^ k :=
    Real.rpow_le_rpow (by linarith) hsum hk
  rw [Real.mul_rpow hDp.le hepos.le] at hpow
  have hmul : n * h ^ p * (d + h) ^ k ≤ n * h ^ p * ((D + 1) ^ k * e ^ k) :=
    mul_le_mul_of_nonneg_left hpow
      (mul_nonneg hn.le (Real.rpow_nonneg hh.le p))
  rw [heq] at hmul
  have hne : n * e ^ (p + k) = 1 := by
    dsimp [e]
    rw [← Real.rpow_mul hn.le]
    have : (-1 / (p + k)) * (p + k) = -1 := by field_simp
    rw [this, Real.rpow_neg_one]
    field_simp
  rw [Real.rpow_neg hDp.le]
  have hnpart : n ^ (-p / (p + k)) = e ^ p := by
    dsimp [e]
    rw [← Real.rpow_mul hn.le]
    congr 1
    ring
  rw [hnpart]
  have htarget : ((D + 1) ^ k)⁻¹ * e ^ p =
      1 / (n * (D + 1) ^ k * e ^ k) := by
    have hene : n * (e ^ p * e ^ k) = 1 := by
      rw [← Real.rpow_add hepos]
      exact hne
    field_simp
    nlinarith
  rw [htarget]
  have hden : 0 < n * (D + 1) ^ k * e ^ k := by positivity
  apply (div_le_iff₀ hden).2
  calc
    1 ≤ n * h ^ p * ((D + 1) ^ k * e ^ k) := hmul
    _ = h ^ p * (n * (D + 1) ^ k * e ^ k) := by ring

/-- The crossing bandwidth has the stated balance, effective count, and the
two regimes separated by `deltaEdge`. [This is the stated conclusion](goal).
-/
-- @node: lem:bandwidth-phases
lemma bandwidth_phases
    (beta kappa deltaBar : ℝ) :
    ∃ cBalance CBalance cFar CFar : ℝ,
      0 < cBalance ∧ cBalance ≤ CBalance ∧ 0 < cFar ∧ cFar ≤ CFar ∧
      (∀ (J : ℕ) (P : ClampLaw J) (L cminus cplus pmin alpha : ℝ),
        RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha →
        PolynomialThinning P kappa cminus cplus →
        ∀ (deltaSeq : ℕ → ℝ), ThresholdSequence deltaBar deltaSeq →
        let hSeq := fun n => infoBandwidth n (deltaSeq n) beta kappa deltaBar
        (∀ᶠ n : ℕ in atTop,
          cBalance ≤ (n : ℝ) * (hSeq n) ^ (2 * beta + 1) *
            (deltaSeq n + hSeq n) ^ kappa ∧
          (n : ℝ) * (hSeq n) ^ (2 * beta + 1) *
            (deltaSeq n + hSeq n) ^ kappa ≤ CBalance) ∧
        (∀ᶠ n : ℕ in atTop,
          cBalance * (hSeq n) ^ (-2 * beta) ≤
            (n : ℝ) * hSeq n * (deltaSeq n + hSeq n) ^ kappa ∧
          (n : ℝ) * hSeq n * (deltaSeq n + hSeq n) ^ kappa ≤
            CBalance * (hSeq n) ^ (-2 * beta)) ∧
        (Tendsto (fun n => deltaSeq n / deltaEdge n beta kappa) atTop atTop →
          ∀ᶠ n : ℕ in atTop,
            cFar * (((n : ℝ) * (deltaSeq n) ^ kappa) ^
                (-(1 : ℝ) / (2 * beta + 1))) ≤ hSeq n ∧
            hSeq n ≤ CFar * (((n : ℝ) * (deltaSeq n) ^ kappa) ^
                (-(1 : ℝ) / (2 * beta + 1))))) ∧
      ∀ D : ℝ, 0 < D →
        ∃ cNear CNear : ℝ, 0 < cNear ∧ cNear ≤ CNear ∧
          ∀ (J : ℕ) (P : ClampLaw J) (L cminus cplus pmin alpha : ℝ),
            RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha →
            PolynomialThinning P kappa cminus cplus →
            ∀ (deltaSeq : ℕ → ℝ), ThresholdSequence deltaBar deltaSeq →
            (∀ᶠ n : ℕ in atTop,
              |deltaSeq n| ≤ D * |deltaEdge n beta kappa|) →
            let hSeq := fun n => infoBandwidth n (deltaSeq n) beta kappa deltaBar
            ∀ᶠ n : ℕ in atTop,
              cNear * (n : ℝ) ^ (-(1 : ℝ) / (2 * beta + kappa + 1)) ≤ hSeq n ∧
              hSeq n ≤ CNear * (n : ℝ) ^
                (-(1 : ℝ) / (2 * beta + kappa + 1)) := by
  let p : ℝ := 2 * beta + 1
  let rawFar : ℝ := 2 ^ (-kappa / p)
  let cFar : ℝ := min 1 rawFar
  have hrawFar : 0 < rawFar := Real.rpow_pos_of_pos (by norm_num) _
  have hcFar : 0 < cFar := lt_min (by norm_num) hrawFar
  have hcFarOne : cFar ≤ 1 := min_le_left _ _
  refine ⟨1, 1, cFar, 1, by norm_num, le_rfl, hcFar, hcFarOne, ?_, ?_⟩
  · intro J P L cminus cplus pmin alpha hreg hthin deltaSeq hdelta
    rcases hreg with ⟨hJ, hbeta, hkappa, hL, hcminus, hcm, hcp, hpmin,
      hpminJ, hdeltaBar_pos, hdeltaBar_lt, halpha, halpha_lt⟩
    have hp : 0 < p := by dsimp [p]; linarith
    have hrawFarOne : rawFar ≤ 1 := by
      rw [show (1 : ℝ) = 2 ^ (0 : ℝ) by norm_num]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hkappa) hp.le
    have hcFarEq : cFar = rawFar := min_eq_right hrawFarOne
    dsimp
    have hbalance := infoBandwidth_eventually_balance beta kappa deltaBar hbeta hkappa
      ⟨hdeltaBar_pos, hdeltaBar_lt⟩ deltaSeq hdelta
    refine ⟨?_, ?_, ?_⟩
    · filter_upwards [hbalance] with n hn
      simpa using ⟨hn.2.2.ge, hn.2.2.le⟩
    · filter_upwards [hbalance] with n hn
      have hh := hn.1
      have heq := hn.2.2
      have hsplit : infoBandwidth n (deltaSeq n) beta kappa deltaBar ^
            (2 * beta + 1) =
          infoBandwidth n (deltaSeq n) beta kappa deltaBar ^ (2 * beta) *
            infoBandwidth n (deltaSeq n) beta kappa deltaBar := by
        simpa using Real.rpow_add hh (2 * beta) 1
      have hneg : infoBandwidth n (deltaSeq n) beta kappa deltaBar ^ (-2 * beta) =
          (infoBandwidth n (deltaSeq n) beta kappa deltaBar ^ (2 * beta))⁻¹ := by
        rw [show -2 * beta = -(2 * beta) by ring, Real.rpow_neg hh.le]
      rw [hsplit] at heq
      rw [hneg]
      have hpowpos :
          0 < infoBandwidth n (deltaSeq n) beta kappa deltaBar ^ (2 * beta) :=
        Real.rpow_pos_of_pos hh _
      constructor <;> field_simp <;> nlinarith
    · intro hfar
      have hratio := (Filter.tendsto_atTop.1 hfar) 1
      filter_upwards [hbalance, hratio] with n hn hratioN
      have hnpos : 0 < (n : ℝ) := by
        by_contra hn0
        have hnzero : (n : ℝ) = 0 :=
          le_antisymm (le_of_not_gt hn0) (Nat.cast_nonneg n)
        rw [hnzero, zero_mul] at hn
        norm_num at hn
      have hedgePos : 0 < deltaEdge n beta kappa :=
        Real.rpow_pos_of_pos hnpos _
      have hdeltaPos : 0 < deltaSeq n := by
        have : deltaEdge n beta kappa ≤ deltaSeq n := by
          have := (le_div_iff₀ hedgePos).mp hratioN
          simpa using this
        exact hedgePos.trans_le this
      have hedge : (n : ℝ) ^ (-1 / (p + kappa)) ≤ deltaSeq n := by
        have hle : deltaEdge n beta kappa ≤ deltaSeq n := by
          have := (le_div_iff₀ hedgePos).mp hratioN
          simpa using this
        simpa [deltaEdge, p, show 2 * beta + kappa + 1 =
          (2 * beta + 1) + kappa by ring] using hle
      let h := infoBandwidth n (deltaSeq n) beta kappa deltaBar
      let w := ((n : ℝ) * (deltaSeq n) ^ kappa) ^ (-1 / p)
      have hwUpper : h ≤ w := by
        exact balance_root_le_interior_scale (n : ℝ) (deltaSeq n) h p kappa hnpos
          hdeltaPos hn.1 hp hkappa (by simpa [h, p] using hn.2.2)
      have hwDelta : w ≤ deltaSeq n := by
        exact interior_scale_le_threshold_of_edge_le (n : ℝ) (deltaSeq n) p kappa
          hnpos hdeltaPos hp hkappa hedge
      have hwLower : rawFar * w ≤ h := by
        exact interior_scale_le_balance_root (n : ℝ) (deltaSeq n) h p kappa hnpos
          hdeltaPos hn.1 hp hkappa (hwUpper.trans hwDelta)
          (by simpa [h, p] using hn.2.2)
      simpa [h, w, hcFarEq, rawFar, p] using ⟨hwLower, hwUpper⟩
  · intro D hD
    let rawNear : ℝ := (D + 1) ^ (-kappa / p)
    let cNear : ℝ := min 1 rawNear
    have hDp : 0 < D + 1 := by linarith
    have hrawNear : 0 < rawNear := Real.rpow_pos_of_pos hDp _
    have hcNear : 0 < cNear := lt_min (by norm_num) hrawNear
    have hcNearOne : cNear ≤ 1 := min_le_left _ _
    refine ⟨cNear, 1, hcNear, hcNearOne, ?_⟩
    intro J P L cminus cplus pmin alpha hreg hthin deltaSeq hdelta hnear
    rcases hreg with ⟨hJ, hbeta, hkappa, hL, hcminus, hcm, hcp, hpmin,
      hpminJ, hdeltaBar_pos, hdeltaBar_lt, halpha, halpha_lt⟩
    have hp : 0 < p := by dsimp [p]; linarith
    have hrawNearOne : rawNear ≤ 1 := by
      rw [show (1 : ℝ) = (D + 1) ^ (0 : ℝ) by simp]
      apply Real.rpow_le_rpow_of_exponent_le (by linarith)
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hkappa) hp.le
    have hcNearEq : cNear = rawNear := min_eq_right hrawNearOne
    dsimp
    have hbalance := infoBandwidth_eventually_balance beta kappa deltaBar hbeta hkappa
      ⟨hdeltaBar_pos, hdeltaBar_lt⟩ deltaSeq hdelta
    filter_upwards [hbalance, hnear] with n hn hnearN
    have hnpos : 0 < (n : ℝ) := by
      by_contra hn0
      have hnzero : (n : ℝ) = 0 := le_antisymm (le_of_not_gt hn0) (Nat.cast_nonneg n)
      rw [hnzero, zero_mul] at hn
      norm_num at hn
    have hedgePos : 0 < deltaEdge n beta kappa := Real.rpow_pos_of_pos hnpos _
    have hdeltaNonneg : 0 ≤ deltaSeq n := (hdelta n).1
    have hdeltaEdge : deltaSeq n ≤ D * deltaEdge n beta kappa := by
      simpa [abs_of_nonneg hdeltaNonneg, abs_of_pos hedgePos] using hnearN
    let h := infoBandwidth n (deltaSeq n) beta kappa deltaBar
    let e := (n : ℝ) ^ (-1 / (p + kappa))
    have hedgeEq : deltaEdge n beta kappa = e := by
      simp [deltaEdge, e, p, show 2 * beta + kappa + 1 =
        (2 * beta + 1) + kappa by ring]
    have hde : deltaSeq n ≤ D * e := by simpa [hedgeEq] using hdeltaEdge
    have hhe : h ≤ e := by
      exact balance_root_le_edge_scale (n : ℝ) (deltaSeq n) h p kappa hnpos
        hdeltaNonneg hn.1 hp hkappa (by simpa [h, p] using hn.2.2)
    have hlow : rawNear * e ≤ h := by
      exact edge_scale_le_balance_root (n : ℝ) (deltaSeq n) h p kappa D hnpos
        hdeltaNonneg hn.1 hp hkappa hD (by simpa [h, p] using hn.2.2) hde hhe
    simpa [h, e, hcNearEq, rawNear, p, show 2 * beta + kappa + 1 =
      (2 * beta + 1) + kappa by ring] using ⟨hlow, hhe⟩

/-- If the threshold is asymptotically above the design edge, the information
bandwidth has the interior closed-form order.  Unlike `bandwidth_phases`, this
purely analytic projection does not require an otherwise unused model law. The result uses [the `hreg` condition](hyp:hreg), [the `hdelta` condition](hyp:hdelta), [the `hfar` condition](hyp:hfar). [This is the stated conclusion](goal).
-/
-- @node: infoBandwidth_interior_asymp
lemma infoBandwidth_interior_asymp
    (J : ℕ) (beta kappa L cminus cplus pmin deltaBar alpha : ℝ)
    (hreg : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha)
    (deltaSeq : ℕ → ℝ) (hdelta : ThresholdSequence deltaBar deltaSeq)
    (hfar : Tendsto (fun n => deltaSeq n / deltaEdge n beta kappa) atTop atTop) :
    AsympSeq (fun n => infoBandwidth n (deltaSeq n) beta kappa deltaBar)
      (fun n => ((n : ℝ) * (deltaSeq n) ^ kappa) ^
        (-(1 : ℝ) / (2 * beta + 1))) := by
  rcases hreg with ⟨hJ, hbeta, hkappa, hL, hcminus, hcm, hcp, hpmin,
    hpminJ, hdeltaBar_pos, hdeltaBar_lt, halpha, halpha_lt⟩
  have hbalance := infoBandwidth_eventually_balance beta kappa deltaBar hbeta hkappa
    ⟨hdeltaBar_pos, hdeltaBar_lt⟩ deltaSeq hdelta
  let p : ℝ := 2 * beta + 1
  let c : ℝ := 2 ^ (-kappa / p)
  have hp : 0 < p := by dsimp [p]; linarith
  have hc : 0 < c := Real.rpow_pos_of_pos (by norm_num) _
  have hcOne : c ≤ 1 := by
    rw [show (1 : ℝ) = 2 ^ (0 : ℝ) by norm_num]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hkappa) hp.le
  refine ⟨c, 1, hc, hcOne, ?_⟩
  have hratio := (Filter.tendsto_atTop.1 hfar) 1
  filter_upwards [hbalance, hratio] with n hn hratioN
  have hnpos : 0 < (n : ℝ) := by
    by_contra hn0
    have hnzero : (n : ℝ) = 0 :=
      le_antisymm (le_of_not_gt hn0) (Nat.cast_nonneg n)
    rw [hnzero, zero_mul] at hn
    norm_num at hn
  have hedgePos : 0 < deltaEdge n beta kappa :=
    Real.rpow_pos_of_pos hnpos _
  have hdeltaPos : 0 < deltaSeq n := by
    have hle : deltaEdge n beta kappa ≤ deltaSeq n := by
      have := (le_div_iff₀ hedgePos).mp hratioN
      simpa using this
    exact hedgePos.trans_le hle
  have hedge : (n : ℝ) ^ (-1 / (p + kappa)) ≤ deltaSeq n := by
    have hle : deltaEdge n beta kappa ≤ deltaSeq n := by
      have := (le_div_iff₀ hedgePos).mp hratioN
      simpa using this
    simpa [deltaEdge, p, show 2 * beta + kappa + 1 =
      (2 * beta + 1) + kappa by ring] using hle
  let h := infoBandwidth n (deltaSeq n) beta kappa deltaBar
  let w := ((n : ℝ) * (deltaSeq n) ^ kappa) ^ (-1 / p)
  have hwUpper : h ≤ w := by
    exact balance_root_le_interior_scale (n : ℝ) (deltaSeq n) h p kappa hnpos
      hdeltaPos hn.1 hp hkappa (by simpa [h, p] using hn.2.2)
  have hwDelta : w ≤ deltaSeq n := by
    exact interior_scale_le_threshold_of_edge_le (n : ℝ) (deltaSeq n) p kappa
      hnpos hdeltaPos hp hkappa hedge
  have hwLower : c * w ≤ h := by
    exact interior_scale_le_balance_root (n : ℝ) (deltaSeq n) h p kappa hnpos
      hdeltaPos hn.1 hp hkappa (hwUpper.trans hwDelta)
      (by simpa [h, p] using hn.2.2)
  simpa [h, w, c, p] using ⟨hwLower, hwUpper⟩

end


end CausalSmith.Stat.LmtpThresholdAtomFrontier
