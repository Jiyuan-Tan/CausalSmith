module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.HybridVarianceAssembly

/-! Deterministic C33--C36 absorption of the calibrated hybrid envelope. -/

public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

private lemma normalized_young {R nr dr N q : Real}
    (hn : 0 < nr) (hN : 0 < N) (hq : 0 < q) (hR : R ^ 2 ≤ nr) :
    R * dr / (N * nr * q) ≤
      (1 / nr + dr ^ 2 / (N ^ 2 * q ^ 2)) / 2 := by
  have ha : (R / nr) ^ 2 ≤ 1 / nr := by
    rw [div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos hn)).2
    field_simp [hn.ne']
    nlinarith
  have hs := sq_nonneg (R / nr - dr / (N * q))
  have hid : R * dr / (N * nr * q) = (R / nr) * (dr / (N * q)) := by
    field_simp [hn.ne', hN.ne', hq.ne']
  have hb : (dr / (N * q)) ^ 2 = dr ^ 2 / (N ^ 2 * q ^ 2) := by
    field_simp [hN.ne', hq.ne']
  rw [hid, ← hb]
  nlinarith

private lemma inverse_square_schedule {q L : Real} (hq : 0 < q)
    (hL : 0 < L) (h : q ≤ 512 * L) :
    1 / L ^ 2 ≤ 512 ^ 2 / q ^ 2 := by
  apply (div_le_div_iff₀ (sq_pos_of_pos hL) (sq_pos_of_pos hq)).2
  nlinarith [sq_nonneg (512 * L - q)]

private lemma inverse_schedule {q L : Real} (hq : 0 < q)
    (hL : 0 < L) (h : q ≤ 512 * L) :
    1 / L ≤ 512 / q := by
  exact (div_le_div_iff₀ hL hq).2 (by nlinarith)

private lemma sq_add_le_two (a b : Real) :
    (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

set_option maxHeartbeats 400000 in
-- The expanded rational envelope requires sustained nonlinear normalization.
/-- A purely real-variable version of the final calibrated envelope bound.  [the stated conditions](hyp:heps,hC0,hH,hn,hN,hd,hq,hL,hA,hB,hu,ht,hBup,hqL,hR,hinv12,hinv120) [the stated conclusion](goal). -/
lemma hybrid_deterministic_envelope_le
    {eps C0 H nr N dr q L A B u t inv12 : Real}
    (heps : 0 < eps) (hC0 : 0 ≤ C0) (hH : 0 ≤ H)
    (hn : 1 ≤ nr) (hN : nr ≤ N) (hd : 1 ≤ dr) (hq : 1 ≤ q)
    (hL : 0 < L) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hu : nr / 32 ≤ u) (ht : N / 32 ≤ t)
    (hBup : B ≤ 32 * H * L / N) (hqL : q ≤ 512 * L)
    (hR : (L ^ 3 * A) ^ 2 ≤ nr) (hinv12 : inv12 ≤ 1 / nr)
    (hinv120 : 0 ≤ inv12) :
    4 * A * (min 1 (dr * B) / u + dr * B ^ 2) +
        C0 * (u⁻¹ + t⁻¹) +
        8 * dr * B ^ 2 / (eps ^ 2 * L ^ 4) + 4 / (eps * t) +
        414 * inv12 +
        (2 * dr * B / (eps * L ^ 2) + 6 * inv12) ^ 2 ≤
      (4096 * H * 512 ^ 2 + 4096 * H ^ 2 * 512 +
          64 * C0 + 8192 * H ^ 2 * 512 ^ 2 / eps ^ 2 +
          128 / eps + 414 + 2 * (64 * H * 512 / eps) ^ 2 + 72) *
        (1 / nr + dr ^ 2 / (N ^ 2 * q ^ 2)) := by
  have hnr : 0 < nr := lt_of_lt_of_le zero_lt_one hn
  have hNp : 0 < N := hnr.trans_le hN
  have hdr : 0 ≤ dr := zero_le_one.trans hd
  have hqp : 0 < q := zero_lt_one.trans_le hq
  have hup : 0 < u := lt_of_lt_of_le (div_pos hnr (by norm_num)) hu
  have htp : 0 < t := lt_of_lt_of_le (div_pos hNp (by norm_num)) ht
  let R := L ^ 3 * A
  let rate := 1 / nr + dr ^ 2 / (N ^ 2 * q ^ 2)
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hR2 : R ^ 2 ≤ nr := by simpa [R] using hR
  have hyr : R * dr / (N * nr * q) ≤ rate / 2 := by
    simpa [rate] using normalized_young hnr hNp hqp hR2 (dr := dr)
  have hr0 : 0 ≤ rate := by dsimp [rate]; positivity
  have hq2 := inverse_square_schedule hqp hL hqL
  have hq1 := inverse_schedule hqp hL hqL
  have hinvu : u⁻¹ ≤ 32 / nr := by
    rw [inv_eq_one_div]
    apply (div_le_div_iff₀ hup hnr).2
    linarith
  have hinvt : t⁻¹ ≤ 32 / nr := by
    have hnt : nr / 32 ≤ t :=
      (div_le_div_of_nonneg_right hN (by norm_num : (0 : Real) ≤ 32)).trans ht
    rw [inv_eq_one_div]
    apply (div_le_div_iff₀ htp hnr).2
    nlinarith
  have hsimple : C0 * (u⁻¹ + t⁻¹) + 4 / (eps * t) + 414 * inv12 ≤
      (64 * C0 + 128 / eps + 414) * rate := by
    have h1 : C0 * (u⁻¹ + t⁻¹) ≤ 64 * C0 * (1 / nr) := by
      have := mul_le_mul_of_nonneg_left (add_le_add hinvu hinvt) hC0
      calc
        _ ≤ C0 * (32 / nr + 32 / nr) := this
        _ = _ := by ring
    have h2 : 4 / (eps * t) ≤ (128 / eps) * (1 / nr) := by
      calc
        _ = (4 / eps) * t⁻¹ := by field_simp [heps.ne', htp.ne']
        _ ≤ (4 / eps) * (32 / nr) :=
          mul_le_mul_of_nonneg_left hinvt (by positivity)
        _ = _ := by ring
    have h3 : 414 * inv12 ≤ 414 * (1 / nr) :=
      mul_le_mul_of_nonneg_left hinv12 (by norm_num)
    have hir : 1 / nr ≤ rate := by
      dsimp [rate]
      exact le_add_of_nonneg_right (by positivity)
    have := mul_le_mul_of_nonneg_left hir
      (show 0 ≤ 64 * C0 + 128 / eps + 414 by positivity)
    nlinarith
  have hcoreL2 : R * dr / (N * nr * L ^ 2) ≤ 512 ^ 2 * (rate / 2) := by
    calc
      _ = (R * dr / (N * nr)) * (1 / L ^ 2) := by
        field_simp [hnr.ne', hNp.ne', hL.ne']
      _ ≤ (R * dr / (N * nr)) * (512 ^ 2 / q ^ 2) :=
        mul_le_mul_of_nonneg_left hq2 (by positivity)
      _ ≤ (R * dr / (N * nr)) * (512 ^ 2 / q) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        simpa [one_div] using one_div_le_one_div_of_le hqp
          (by nlinarith [mul_nonneg hqp.le (sub_nonneg.mpr hq)] : q ≤ q ^ 2)
      _ = 512 ^ 2 * (R * dr / (N * nr * q)) := by
        field_simp [hnr.ne', hNp.ne', hqp.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left hyr (by positivity)
  have hcoreL1 : R * dr / (N ^ 2 * L) ≤ 512 * (rate / 2) := by
    calc
      _ = (R * dr / N ^ 2) * (1 / L) := by
        field_simp [hNp.ne', hL.ne']
      _ ≤ (R * dr / N ^ 2) * (512 / q) :=
        mul_le_mul_of_nonneg_left hq1 (by positivity)
      _ ≤ (R * dr / (N * nr)) * (512 / q) := by
        gcongr
        simpa [pow_two] using mul_le_mul_of_nonneg_left hN hNp.le
      _ = 512 * (R * dr / (N * nr * q)) := by
        field_simp [hnr.ne', hNp.ne', hqp.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left hyr (by norm_num)
  have hlight1 : 4 * A * (min 1 (dr * B) / u) ≤
      (4096 * H * 512 ^ 2) * (rate / 2) := by
    calc
      _ ≤ 4 * A * ((dr * B) / u) := by
        gcongr
        exact min_le_right _ _
      _ ≤ 4 * A * ((dr * (32 * H * L / N)) / (nr / 32)) := by
        gcongr
      _ = 4096 * H * (R * dr / (N * nr * L ^ 2)) := by
        dsimp [R]
        field_simp [hnr.ne', hNp.ne', hL.ne']
        ring
      _ ≤ _ := by
        simpa [mul_assoc] using
          mul_le_mul_of_nonneg_left hcoreL2 (show 0 ≤ 4096 * H by positivity)
  have hlight2 : 4 * A * (dr * B ^ 2) ≤
      (4096 * H ^ 2 * 512) * (rate / 2) := by
    calc
      _ ≤ 4 * A * (dr * (32 * H * L / N) ^ 2) := by gcongr
      _ = 4096 * H ^ 2 * (R * dr / (N ^ 2 * L)) := by
        dsimp [R]
        field_simp [hNp.ne', hL.ne']
        ring
      _ ≤ _ := by
        simpa [mul_assoc] using
          mul_le_mul_of_nonneg_left hcoreL1 (show 0 ≤ 4096 * H ^ 2 by positivity)
  have hdim : dr ^ 2 / (N ^ 2 * q ^ 2) ≤ rate := by
    dsimp [rate]
    exact le_add_of_nonneg_left (by positivity)
  have hvpoly : 8 * dr * B ^ 2 / (eps ^ 2 * L ^ 4) ≤
      (8192 * H ^ 2 * 512 ^ 2 / eps ^ 2) * rate := by
    have hdr2 : dr ≤ dr ^ 2 := by
      calc
        dr = dr * 1 := by ring
        _ ≤ dr * dr := mul_le_mul_of_nonneg_left hd hdr
        _ = dr ^ 2 := by ring
    have hfrac : dr / (N ^ 2 * L ^ 2) ≤
        dr ^ 2 * (512 ^ 2 / q ^ 2) / N ^ 2 := by
      calc
        _ = (dr / N ^ 2) * (1 / L ^ 2) := by
          field_simp [hNp.ne', hL.ne']
        _ ≤ (dr / N ^ 2) * (512 ^ 2 / q ^ 2) :=
          mul_le_mul_of_nonneg_left hq2 (by positivity)
        _ ≤ (dr ^ 2 / N ^ 2) * (512 ^ 2 / q ^ 2) := by
          gcongr
        _ = _ := by ring
    calc
      _ ≤ 8 * dr * (32 * H * L / N) ^ 2 / (eps ^ 2 * L ^ 4) := by gcongr
      _ = (8192 * H ^ 2 / eps ^ 2) * (dr / (N ^ 2 * L ^ 2)) := by
        field_simp [heps.ne', hNp.ne', hL.ne']
        ring
      _ ≤ (8192 * H ^ 2 / eps ^ 2) *
          (dr ^ 2 * (512 ^ 2 / q ^ 2) / N ^ 2) :=
        mul_le_mul_of_nonneg_left hfrac (by positivity)
      _ = (8192 * H ^ 2 * 512 ^ 2 / eps ^ 2) *
          (dr ^ 2 / (N ^ 2 * q ^ 2)) := by
        field_simp [heps.ne', hNp.ne', hqp.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left hdim (by positivity)
  have hbmain : 2 * dr * B / (eps * L ^ 2) ≤
      (64 * H * 512 / eps) * (dr / (N * q)) := by
    calc
      _ ≤ 2 * dr * (32 * H * L / N) / (eps * L ^ 2) := by gcongr
      _ = (64 * H / eps) * (dr / (N * L)) := by
        field_simp [heps.ne', hNp.ne', hL.ne']
        ring
      _ ≤ (64 * H / eps) * (dr * (512 / q) / N) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc
          dr / (N * L) = (dr / N) * (1 / L) := by
            field_simp [hNp.ne', hL.ne']
          _ ≤ (dr / N) * (512 / q) :=
            mul_le_mul_of_nonneg_left hq1 (by positivity)
          _ = dr * (512 / q) / N := by ring
      _ = _ := by ring
  have hbmainSq : (2 * dr * B / (eps * L ^ 2)) ^ 2 ≤
      (64 * H * 512 / eps) ^ 2 * rate := by
    have hs := mul_self_le_mul_self (by positivity) hbmain
    have : (dr / (N * q)) ^ 2 = dr ^ 2 / (N ^ 2 * q ^ 2) := by
      field_simp [hNp.ne', hqp.ne']
    calc
      _ ≤ ((64 * H * 512 / eps) * (dr / (N * q))) ^ 2 := by
        simpa [pow_two] using hs
      _ = (64 * H * 512 / eps) ^ 2 *
          (dr ^ 2 / (N ^ 2 * q ^ 2)) := by rw [mul_pow, this]
      _ ≤ _ := mul_le_mul_of_nonneg_left hdim (sq_nonneg _)
  have htailSq : (6 * inv12) ^ 2 ≤ 36 * (1 / nr) := by
    have hi1 : inv12 ≤ 1 := hinv12.trans (by
      rw [div_le_one hnr]
      exact hn)
    nlinarith [mul_nonneg hinv120 (sub_nonneg.mpr hi1),
      mul_le_mul_of_nonneg_left hinv12 (by norm_num : (0 : Real) ≤ 36)]
  have hbias : (2 * dr * B / (eps * L ^ 2) + 6 * inv12) ^ 2 ≤
      (2 * (64 * H * 512 / eps) ^ 2 + 72) * rate := by
    have hs : (2 * dr * B / (eps * L ^ 2) + 6 * inv12) ^ 2 ≤
        2 * (2 * dr * B / (eps * L ^ 2)) ^ 2 + 2 * (6 * inv12) ^ 2 :=
      sq_add_le_two _ _
    have hir : 1 / nr ≤ rate := by
      dsimp [rate]
      exact le_add_of_nonneg_right (by positivity)
    have ht' := htailSq.trans
      (mul_le_mul_of_nonneg_left hir (by norm_num : (0 : Real) ≤ 36))
    linarith [mul_le_mul_of_nonneg_left hbmainSq (by norm_num : (0 : Real) ≤ 2),
      mul_le_mul_of_nonneg_left ht' (by norm_num : (0 : Real) ≤ 2)]
  have hlight : 4 * A * (min 1 (dr * B) / u + dr * B ^ 2) ≤
      (4096 * H * 512 ^ 2 + 4096 * H ^ 2 * 512) * rate := by
    have hc1 : 0 ≤ 4096 * H * 512 ^ 2 := by positivity
    have hc2 : 0 ≤ 4096 * H ^ 2 * 512 := by positivity
    calc
      _ = 4 * A * (min 1 (dr * B) / u) + 4 * A * (dr * B ^ 2) := by ring
      _ ≤ (4096 * H * 512 ^ 2) * (rate / 2) +
          (4096 * H ^ 2 * 512) * (rate / 2) := add_le_add hlight1 hlight2
      _ = (4096 * H * 512 ^ 2 + 4096 * H ^ 2 * 512) * (rate / 2) := by ring
      _ ≤ (4096 * H * 512 ^ 2 + 4096 * H ^ 2 * 512) * rate :=
        mul_le_mul_of_nonneg_left (half_le_self hr0) (add_nonneg hc1 hc2)
  let cL := 4096 * H * 512 ^ 2 + 4096 * H ^ 2 * 512
  let cS := 64 * C0 + 128 / eps + 414
  let cV := 8192 * H ^ 2 * 512 ^ 2 / eps ^ 2
  let cB := 2 * (64 * H * 512 / eps) ^ 2 + 72
  calc
    _ = (4 * A * (min 1 (dr * B) / u + dr * B ^ 2)) +
        (C0 * (u⁻¹ + t⁻¹) + 4 / (eps * t) + 414 * inv12) +
        (8 * dr * B ^ 2 / (eps ^ 2 * L ^ 4)) +
        ((2 * dr * B / (eps * L ^ 2) + 6 * inv12) ^ 2) := by ring
    _ ≤ cL * rate + cS * rate + cV * rate + cB * rate :=
      add_le_add (add_le_add (add_le_add hlight (by simpa [cS] using hsimple))
        (by simpa [cV] using hvpoly)) (by simpa [cB] using hbias)
    _ = _ := by dsimp [cL, cS, cV, cB]; ring

/-- Concrete calibrated C33--C36 absorption.  [the stated conditions](hyp:heps,hC0) [the stated conclusion](goal). -/
lemma calibrated_envelope_absorption_exists {eps C0 : Real}
    (heps : 0 < eps) (hC0 : 0 < C0) :
    ∃ C : Real, 0 < C ∧ ∀ (n m d : Nat), 1 ≤ n → 2 ≤ d →
      calibrationPredicate n m eps →
      let bs := blockSizes n m
      let u : Real := bs.M0 / 8
      let t : Real := (bs.nf + bs.mf : Nat) / 8
      4 * starA ^ Ldeg n *
          (min 1 ((d : Real) * Bscale n m eps) / u +
            (d : Real) * Bscale n m eps ^ 2) +
        C0 * (u⁻¹ + t⁻¹) +
        8 * d * Bscale n m eps ^ 2 /
          (eps ^ 2 * (Ldeg n : Real) ^ 4) + 4 / (eps * t) +
        414 * ((n : Real) ^ 12)⁻¹ +
        (2 * d * Bscale n m eps / (eps * (Ldeg n : Real) ^ 2) +
          6 * ((n : Real) ^ 12)⁻¹) ^ 2 ≤
      C * (1 / (n : Real) + (d : Real) ^ 2 /
        (((n + m : Nat) : Real) ^ 2 * logEN n ^ 2)) := by
  let H : Real := Hconst eps
  let C : Real := 1 + (4096 * H * 512 ^ 2 + 4096 * H ^ 2 * 512 +
    64 * C0 + 8192 * H ^ 2 * 512 ^ 2 / eps ^ 2 +
    128 / eps + 414 + 2 * (64 * H * 512 / eps) ^ 2 + 72)
  have hC : 0 < C := by dsimp [C, H]; positivity
  refine ⟨C, hC, ?_⟩
  intro n m d hn hd hcal
  dsimp only
  let nr : Real := n
  let N : Real := n + m
  let dr : Real := d
  let q := logEN n
  let L : Real := Ldeg n
  let A : Real := starA ^ Ldeg n
  let B := Bscale n m eps
  let u : Real := (blockSizes n m).M0 / 8
  let t : Real := ((blockSizes n m).nf + (blockSizes n m).mf : Nat) / 8
  have hnr : 1 ≤ nr := by dsimp [nr]; exact_mod_cast hn
  have hN : nr ≤ N := by dsimp [nr, N]; exact_mod_cast Nat.le_add_right n m
  have hdr : 1 ≤ dr := by dsimp [dr]; exact_mod_cast (by omega : 1 ≤ d)
  have hq : 1 ≤ q := by
    have hnp : (0 : Real) < n := by positivity
    dsimp [q, logEN]
    rw [Real.log_mul (Real.exp_ne_zero 1) hnp.ne', Real.log_exp]
    exact le_add_of_nonneg_right (Real.log_nonneg (by exact_mod_cast hn))
  have hL : 0 < L := by
    dsimp [L]
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) (Ldeg_ge_two n))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  obtain ⟨_hu, _htp, _ht, hBp⟩ := calibrationPredicate_positive_parameters hcal
  have hB : 0 ≤ B := by simpa [B] using hBp.le
  have hcal' := hcal
  simp only [calibrationPredicate] at hcal'
  rcases hcal' with ⟨hn24, hu0, _hu1, _hp0, _hp1, ht0, _ht1,
    _hr0, _hr1, hLbin, _htpB, _htB, hm4, hm6, _tail1, _tail2, _tail3⟩
  have hu : nr / 32 ≤ u := by
    have hnp : (0 : Real) < nr := lt_of_lt_of_le zero_lt_one hnr
    have := (le_div_iff₀ hnp).1 hu0
    dsimp [nr, u]
    nlinarith
  have ht : N / 32 ≤ t := by
    have hNp : (0 : Real) < N := lt_of_lt_of_le zero_lt_one (hnr.trans hN)
    have ht0' : 1 / 32 ≤ t / N := by simpa [t, N] using ht0
    have := (le_div_iff₀ hNp).1 ht0'
    simpa [div_eq_mul_inv, mul_comm] using this
  have hBup : B ≤ 32 * H * L / N := by
    simpa [B, H, L, N] using (Bscale_bounds n m eps hn24).2
  have hqL : q ≤ 512 * L := by
    have hlog := logEN_le_binLen n hn
    norm_num [cCirc] at hLbin
    dsimp [q, L]
    nlinarith
  have hR : (L ^ 3 * A) ^ 2 ≤ nr := by
    have hm := (moment_tests_square_forms hm4 hm6).2
    simpa [L, A, nr] using hm
  have hinv0 : 0 ≤ ((n : Real) ^ 12)⁻¹ := by positivity
  have hinv : ((n : Real) ^ 12)⁻¹ ≤ 1 / nr := by
    have hnp : (0 : Real) < n := by positivity
    have hp : (n : Real) ≤ (n : Real) ^ 12 := by
      calc
        (n : Real) = (n : Real) ^ 1 := by ring
        _ ≤ _ := pow_le_pow_right₀ (by exact_mod_cast hn) (by omega)
    dsimp [nr]
    simpa [one_div] using inv_anti₀ hnp hp
  have hmain := hybrid_deterministic_envelope_le heps hC0.le
    (show 0 ≤ H by dsimp [H]; positivity) hnr hN hdr hq hL hA hB hu ht
    hBup hqL hR hinv hinv0
  have hr0 : 0 ≤ 1 / nr + dr ^ 2 / (N ^ 2 * q ^ 2) := by positivity
  have hcoef :
      4096 * H * 512 ^ 2 + 4096 * H ^ 2 * 512 + 64 * C0 +
          8192 * H ^ 2 * 512 ^ 2 / eps ^ 2 + 128 / eps + 414 +
          2 * (64 * H * 512 / eps) ^ 2 + 72 ≤ C := by
    dsimp [C]
    linarith
  have hout := hmain.trans
    (mul_le_mul_of_nonneg_right hcoef hr0)
  simpa only [nr, N, dr, q, L, A, B, u, t, Nat.cast_add] using hout

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
