module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.HybridBlockCalibration

/-! Uniform eventual validity of the finite hybrid calibration predicate. -/

public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

/-- The elementary logarithmic lower bound used for the rational pilot tail.  [the stated conditions](hyp:heps,heps2) [the stated conclusion](goal). -/
lemma log_one_add_barEps_div_three_lower {eps : Real}
    (heps : 0 < eps) (heps2 : eps < 1 / 2) :
    2 * barEps eps / 7 ≤ Real.log (1 + barEps eps / 3) := by
  have hb : 0 < barEps eps := barEps_pos eps
  have hbe : barEps eps ≤ eps := (dyadicIndex_spec heps heps2).2
  have hhalf : barEps eps < 1 / 2 := hbe.trans_lt heps2
  have hlog := Real.le_log_one_add_of_nonneg (show 0 ≤ barEps eps / 3 by positivity)
  calc
    2 * barEps eps / 7 ≤ 2 * (barEps eps / 3) / (barEps eps / 3 + 2) := by
      field_simp
      nlinarith
    _ ≤ Real.log (1 + barEps eps / 3) := hlog

/-- Every deterministic calibration test holds for all auxiliary sizes once
the labeled size is sufficiently large.  [the stated conditions](hyp:heps,heps2) [the stated conclusion](goal). -/
lemma calibrationPredicate_eventually_uniform {eps : Real}
    (heps : 0 < eps) (heps2 : eps < 1 / 2) :
    ∀ᶠ n : Nat in Filter.atTop, ∀ m : Nat, calibrationPredicate n m eps := by
  filter_upwards [Filter.eventually_ge_atTop 24,
    eventually_two_le_cCirc_binLen,
    eventually_factorial_moment_tests] with n hn hdeg hmom
  intro m
  let bs := blockSizes n m
  let N : Nat := n + m
  let u : Real := bs.M0 / 8
  let tp : Real := (bs.np + bs.mp : Nat) / 8
  let t : Real := (bs.nf + bs.mf : Nat) / 8
  let L : Nat := Ldeg n
  let B : Real := Bscale n m eps
  have hr := blockSizes_intensity_ratios n m hn
  change 1 / 32 ≤ u / n ∧ u / n ≤ 1 / 24 ∧
      1 / 32 ≤ tp / N ∧ tp / N ≤ 3 / 32 ∧
      1 / 32 ≤ t / N ∧ t / N ≤ 3 / 32 ∧
      1 / 3 ≤ t / tp ∧ t / tp ≤ 3 at hr
  rcases hr with ⟨hu0, hu1, hp0, hp1, hf0, hf1, hratio0, hratio1⟩
  have hLbounds := Ldeg_bounds hdeg
  change cCirc * binLen n / 2 ≤ (L : Real) ∧ (L : Real) ≤ cCirc * binLen n at hLbounds
  have hBL := blockSizes_mul_Bscale_lower n m eps hn
  change (Hconst eps : Real) * L ≤ tp * B ∧
      (Hconst eps : Real) * L ≤ t * B at hBL
  rcases hBL with ⟨htpBL, htBL⟩
  rcases Hconst_spec heps with ⟨hH4, hHtail, hH672, hH24⟩
  have hLR : (2 : Real) ≤ L := by exact_mod_cast Ldeg_ge_two n
  have hH4R : (4 : Real) ≤ Hconst eps := by exact_mod_cast hH4
  have htpB8 : 8 ≤ tp * B := by nlinarith
  have htBL' : (L : Real) ≤ t * B := by nlinarith
  have htail1 : 15 * (L : Real) + 12 * binLen n ≤ tp * B / 4 := by
    have hc : 0 < cCirc := by norm_num [cCirc]
    have hbin : (12 : Real) * binLen n ≤ 24 / cCirc * L := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hc).2
      nlinarith [hLbounds.1]
    have : (15 + 24 / cCirc) * L ≤ tp * B / 4 := by
      calc
        (15 + 24 / cCirc) * L ≤ ((Hconst eps : Real) / 4) * L :=
          mul_le_mul_of_nonneg_right hHtail (by positivity)
        _ ≤ tp * B / 4 := by linarith
    nlinarith
  have htail3 : 12 * binLen n ≤ barEps eps * t * B := by
    have hnonneg : 0 ≤ (binLen n : Real) := by positivity
    have hscaled : 12 * binLen n ≤
        ((Hconst eps : Real) * cCirc * barEps eps / 2) * binLen n := by
      have : (12 : Real) ≤ (Hconst eps : Real) * cCirc * barEps eps / 2 := by
        linarith
      exact mul_le_mul_of_nonneg_right this hnonneg
    calc
      12 * binLen n ≤ ((Hconst eps : Real) * cCirc * barEps eps / 2) *
          binLen n := hscaled
      _ ≤ barEps eps * ((Hconst eps : Real) * L) := by
        have hb := (barEps_pos eps).le
        have h := mul_le_mul_of_nonneg_left hLbounds.1
          (mul_nonneg (by positivity : 0 ≤ (Hconst eps : Real)) hb)
        nlinarith
      _ ≤ barEps eps * (t * B) :=
        mul_le_mul_of_nonneg_left htBL (barEps_pos eps).le
      _ = barEps eps * t * B := by ring
  have hk : (Hconst eps : Real) * L / 8 ≤ (k0 n m eps : Real) := by
    calc
      (Hconst eps : Real) * L / 8 ≤ tp * B / 8 := by
        exact div_le_div_of_nonneg_right htpBL (by norm_num)
      _ ≤ (k0 n m eps : Real) := k0_lower_eighth n m eps htpB8
  have hb := barEps_pos eps
  have hlog0 := log_one_add_barEps_div_three_lower heps heps2
  have hbase : 1 + barEps eps / 3 ≤ 1 + barEps eps * t / tp := by
    have := mul_le_mul_of_nonneg_left hratio0 hb.le
    simpa [div_eq_mul_inv, mul_assoc] using add_le_add_left this 1
  have hbase0 : 0 < 1 + barEps eps / 3 := by positivity
  have hbase1 : 0 < 1 + barEps eps * t / tp := hbase0.trans_le hbase
  have hlogmono : Real.log (1 + barEps eps / 3) ≤
      Real.log (1 + barEps eps * t / tp) :=
    Real.strictMonoOn_log.monotoneOn hbase0 hbase1 hbase
  have hklog : 12 * binLen n ≤ (k0 n m eps : Real) *
      Real.log (1 + barEps eps * t / tp) := by
    have hbin0 : 0 ≤ (binLen n : Real) := by positivity
    have hstart : 12 * binLen n ≤
        ((Hconst eps : Real) * cCirc * barEps eps / 56) * binLen n := by
      have : (12 : Real) ≤ (Hconst eps : Real) * cCirc * barEps eps / 56 := by
        nlinarith
      exact mul_le_mul_of_nonneg_right this hbin0
    have hmid : ((Hconst eps : Real) * cCirc * barEps eps / 56) * binLen n ≤
        ((Hconst eps : Real) * L / 8) * (2 * barEps eps / 7) := by
      have h := mul_le_mul_of_nonneg_left hLbounds.1
        (mul_nonneg (by positivity : 0 ≤ (Hconst eps : Real)) hb.le)
      nlinarith
    calc
      12 * binLen n ≤ ((Hconst eps : Real) * cCirc * barEps eps / 56) *
          binLen n := hstart
      _ ≤ ((Hconst eps : Real) * L / 8) * (2 * barEps eps / 7) := hmid
      _ ≤ (k0 n m eps : Real) * (2 * barEps eps / 7) :=
        mul_le_mul_of_nonneg_right hk (by positivity)
      _ ≤ (k0 n m eps : Real) * Real.log (1 + barEps eps / 3) :=
        mul_le_mul_of_nonneg_left hlog0 (by positivity)
      _ ≤ (k0 n m eps : Real) * Real.log (1 + barEps eps * t / tp) :=
        mul_le_mul_of_nonneg_left hlogmono (by positivity)
  have htail2 : (n : Real) ^ 12 ≤
      (1 + barEps eps * t / tp) ^ k0 n m eps :=
    pow_tail_test_of_log (by omega) hbase1 hklog
  change calibrationPredicate n m eps
  simp only [calibrationPredicate]
  change 24 ≤ n ∧ 1 / 32 ≤ u / n ∧ u / n ≤ 1 / 24 ∧
    1 / 32 ≤ tp / N ∧ tp / N ≤ 3 / 32 ∧
    1 / 32 ≤ t / N ∧ t / N ≤ 3 / 32 ∧
    1 / 3 ≤ t / tp ∧ t / tp ≤ 3 ∧
    cCirc * binLen n / 2 ≤ L ∧ 8 ≤ tp * B ∧ (L : Real) ≤ t * B ∧
    (L : Real) ^ 4 * starA ^ (2 * L) ≤ n ∧
    (L : Real) ^ 6 * starA ^ (2 * L) ≤ n ∧
    15 * L + 12 * binLen n ≤ tp * B / 4 ∧
    (n : Real) ^ 12 ≤ (1 + barEps eps * t / tp) ^ k0 n m eps ∧
    12 * binLen n ≤ barEps eps * t * B
  exact ⟨hn, hu0, hu1, hp0, hp1, hf0, hf1, hratio0, hratio1,
    hLbounds.1, htpB8, htBL', hmom.1, hmom.2, htail1, htail2, htail3⟩

/-- A single finite labeled-size threshold contains every possible calibration
failure, uniformly over the auxiliary sample size.  [the stated conditions](hyp:heps,heps2) [the stated conclusion](goal). -/
lemma calibrationPredicate_failure_bounded {eps : Real}
    (heps : 0 < eps) (heps2 : eps < 1 / 2) :
    ∃ n0 : Nat, 1 ≤ n0 ∧ ∀ n m : Nat,
      ¬ calibrationPredicate n m eps → n < n0 := by
  have hev := calibrationPredicate_eventually_uniform heps heps2
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  refine ⟨max 1 N, by simp, ?_⟩
  intro n m hfail
  by_contra hn
  have hNn : N ≤ n := le_trans (le_max_right 1 N) (le_of_not_gt hn)
  exact hfail (hN n hNn m)

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
