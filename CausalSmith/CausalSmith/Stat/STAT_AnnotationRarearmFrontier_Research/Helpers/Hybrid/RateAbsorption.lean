module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Hybrid.Calibration

/-!
Bandwidth rescaling and absorption of the intermediate hybrid variance terms in
roadmap equations (14)--(15). All degree calibration uses S = n epsilon.
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

/-- [Under the stated inputs and conditions](hyp:L,hN,htp,ht,N,tp,t), The lower bounds on both factorial intensities give the public bandwidth bound.  This gives [the stated result](goal).-/
-- @node: hybrid_bandwidth_public_bound
lemma hybrid_bandwidth_public_bound (N tp t : Real) (L : Nat)
    (hN : 0 < N) (htp : N / 64 ≤ tp) (ht : N / 64 ≤ t) :
    (2 : Real) ^ 20 * L / min tp t ≤ (64 * (2 : Real) ^ 20) * L / N := by
  have hm : N / 64 ≤ min tp t := le_min htp ht
  have hmpos : 0 < min tp t := lt_of_lt_of_le (by positivity) hm
  calc
    _ ≤ (2 : Real) ^ 20 * L / (N / 64) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hm
    _ = _ := by ring

/-- [Under the stated inputs and conditions](hyp:_hA,hB,hd,hN,heps,hL,hband,hmass,A,B,d,N,eps,L,M), Equation (15): a bandwidth bound controls the light mass, the variance bandwidth,
and the squared total bias at the common public scale d / (N epsilon L).  This gives [the stated result](goal).-/
-- @node: hybrid_bandwidth_rate_monomials
lemma hybrid_bandwidth_rate_monomials (A B d N eps L M : Real)
    (_hA : 0 ≤ A) (hB : 0 ≤ B) (hd : 0 ≤ d) (hN : 0 < N)
    (heps : 0 < eps) (hL : 0 < L) (hband : B ≤ A * L / N)
    (hmass : M ≤ d * B / eps) :
    M ≤ A * (d / (N * eps * L)) * L ^ 2 ∧
      d * B ^ 2 / eps ^ 2 ≤
        A ^ 2 * (d / (N * eps * L)) * L ^ 3 / (N * eps) ∧
      d ^ 2 * B ^ 2 / (eps ^ 2 * L ^ 4) ≤
        A ^ 2 * (d / (N * eps * L)) ^ 2 := by
  have hB2 := pow_le_pow_left₀ hB hband 2
  refine ⟨?_, ?_, ?_⟩
  · calc
      M ≤ d * B / eps := hmass
      _ ≤ d * (A * L / N) / eps :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hband hd) heps.le
      _ = _ := by field_simp
  · calc
      _ ≤ d * (A * L / N) ^ 2 / eps ^ 2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hB2 hd) (sq_nonneg eps)
      _ = _ := by field_simp
  · calc
      _ ≤ d ^ 2 * (A * L / N) ^ 2 / (eps ^ 2 * L ^ 4) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hB2 (sq_nonneg d))
          (by positivity)
      _ = _ := by field_simp

/-- [Under the stated inputs and conditions](hyp:hA,hF,hS,hL,hM,hz,_ht,hcal,hmass,hband,htinv,A,F,S,L,M,H,z,t), The calibrated factorial growth absorbs both light-mass terms and the bandwidth
variance term into z / sqrt S, retaining the factorial-intensity constant.  This gives [the stated result](goal).-/
-- @node: hybrid_light_variance_rate_absorption
lemma hybrid_light_variance_rate_absorption (A F S L M H z t : Real)
    (hA : 0 ≤ A) (hF : 0 ≤ F) (hS : 0 < S) (hL : 1 ≤ L)
    (hM : 0 ≤ M) (hz : 0 ≤ z) (_ht : 0 < t)
    (hcal : F * L ^ 3 ≤ Real.sqrt S)
    (hmass : M ≤ A * z * L ^ 2)
    (hband : H ≤ A ^ 2 * z * L ^ 3 / S)
    (htinv : 1 / t ≤ 64 / S) :
    F * (M / S + M / t + H) ≤ (65 * A + A ^ 2) * z / Real.sqrt S := by
  have hroot : 0 < Real.sqrt S := Real.sqrt_pos.mpr hS
  have hroot2 : (Real.sqrt S) ^ 2 = S := Real.sq_sqrt hS.le
  have hLpos : 0 ≤ L := by linarith
  have hL23 : L ^ 2 ≤ L ^ 3 := by nlinarith [sq_nonneg L]
  have hcal2 : F * L ^ 2 ≤ Real.sqrt S :=
    (mul_le_mul_of_nonneg_left hL23 hF).trans hcal
  have hFM : F * M ≤ A * z * Real.sqrt S := by
    calc
      _ ≤ F * (A * z * L ^ 2) := mul_le_mul_of_nonneg_left hmass hF
      _ = (A * z) * (F * L ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcal2 (mul_nonneg hA hz)
  have hFH : F * H ≤ A ^ 2 * z * Real.sqrt S / S := by
    calc
      _ ≤ F * (A ^ 2 * z * L ^ 3 / S) := mul_le_mul_of_nonneg_left hband hF
      _ = (A ^ 2 * z) * (F * L ^ 3) / S := by ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcal (mul_nonneg (sq_nonneg A) hz)) hS.le
  have hT : F * M / t ≤ 64 * (A * z * Real.sqrt S / S) := by
    calc
      _ = (F * M) * (1 / t) := by ring
      _ ≤ (F * M) * (64 / S) := mul_le_mul_of_nonneg_left htinv (mul_nonneg hF hM)
      _ ≤ (A * z * Real.sqrt S) * (64 / S) :=
        mul_le_mul_of_nonneg_right hFM (by positivity)
      _ = _ := by ring
  calc
    _ = F * M / S + F * M / t + F * H := by ring
    _ ≤ A * z * Real.sqrt S / S +
        64 * (A * z * Real.sqrt S / S) + A ^ 2 * z * Real.sqrt S / S :=
      add_le_add (add_le_add (div_le_div_of_nonneg_right hFM hS.le) hT) hFH
    _ = (65 * A + A ^ 2) * z / Real.sqrt S := by
      field_simp
      rw [hroot2]
      ring

/-- [Under the stated inputs and conditions](hyp:hS,S,z), Young's inequality at the public scale converts the mixed rate to the two
terms of the arm risk, with no restriction on the cell-budget scale z.  This gives [the stated result](goal).-/
-- @node: hybrid_mixed_rate_le
lemma hybrid_mixed_rate_le (S z : Real) (hS : 0 < S) :
    2 * z / Real.sqrt S ≤ z ^ 2 + 1 / S := by
  have hroot : 0 < Real.sqrt S := Real.sqrt_pos.mpr hS
  have hroot2 : (Real.sqrt S) ^ 2 = S := Real.sq_sqrt hS.le
  have hinv : (1 / Real.sqrt S) ^ 2 = 1 / S := by
    rw [div_pow, hroot2]
    norm_num
  have hh := sq_nonneg (z - 1 / Real.sqrt S)
  rw [show 2 * z / Real.sqrt S = 2 * z * (1 / Real.sqrt S) by ring]
  nlinarith only [hh, hinv]

/-- [Under the stated inputs and conditions](hyp:S,hS), The pilot's inverse twentieth power remainder is smaller than the leading rate.  This gives [the stated result](goal).-/
-- @node: hybrid_pilot_remainder_le
lemma hybrid_pilot_remainder_le (S : Real) (hS : 1 ≤ S) :
    (S ^ 20)⁻¹ ≤ 1 / S := by
  have hpos : 0 < S := by linarith
  have hp : S ≤ S ^ 20 := by
    calc
      S = S ^ 1 := by ring
      _ ≤ S ^ 20 := pow_le_pow_right₀ hS (by norm_num)
  simpa only [one_div] using one_div_le_one_div_of_le hpos hp

/-- [Under the stated inputs and conditions](hyp:hS,hd,heps,heps1,hNS,htp,ht,S,N,d,eps,tp,t,M), Applying the actual degree calibration and pool-size assumptions absorbs the
entire equation (5) light-variance envelope into the target arm rate.  This gives [the stated result](goal).-/
-- @node: hybrid_calibrated_light_variance_rate
lemma hybrid_calibrated_light_variance_rate (S N d eps tp t M : Real)
    (hS : Real.exp 4096 ≤ S) (hd : 0 ≤ d) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hNS : S ≤ N * eps) (htp : N / 64 ≤ tp) (ht : N / 64 ≤ t) :
    let L := Nat.floor (Real.log S / 1024)
    let B : Real := (2 : Real) ^ 20 * L / min tp t
    let A : Real := 64 * (2 : Real) ^ 20
    0 ≤ M → M ≤ d * B / eps →
    ((2 : Real) ^ 24) ^ L * (M / S + M / t + d * B ^ 2 / eps ^ 2) ≤
      ((65 * A + A ^ 2) / 2) * (1 / S + (d / (N * eps * L)) ^ 2) := by
  dsimp only
  intro hM hmass
  let L := Nat.floor (Real.log S / 1024)
  let B : Real := (2 : Real) ^ 20 * L / min tp t
  let A : Real := 64 * (2 : Real) ^ 20
  let z := d / (N * eps * L)
  have hSpos : 0 < S := (Real.exp_pos _).trans_le hS
  have hN : 0 < N := by nlinarith
  have htpos : 0 < t := (show 0 < N / 64 by positivity).trans_le ht
  have htpPos : 0 < tp := (show 0 < N / 64 by positivity).trans_le htp
  have hcal := hybrid_degree_calibration S hS
  have hL4 : (4 : Real) ≤ L := by exact_mod_cast hcal.1
  have hL : 0 < (L : Real) := by linarith
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hA : 0 ≤ A := by norm_num [A]
  have hband : B ≤ A * L / N := hybrid_bandwidth_public_bound N tp t L hN htp ht
  obtain ⟨hm, hb, _⟩ := hybrid_bandwidth_rate_monomials A B d N eps L M
    hA hB hd hN heps hL hband hmass
  have hbS : d * B ^ 2 / eps ^ 2 ≤ A ^ 2 * z * (L : Real) ^ 3 / S := by
    exact hb.trans (div_le_div_of_nonneg_left (by positivity) hSpos hNS)
  have hNle : N * eps ≤ N := mul_le_of_le_one_right hN.le heps1
  have htinv : 1 / t ≤ 64 / S := by
    apply (div_le_div_iff₀ htpos hSpos).2
    nlinarith only [hNS, hNle, ht]
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have habs := hybrid_light_variance_rate_absorption A (((2 : Real) ^ 24) ^ L)
    S L M (d * B ^ 2 / eps ^ 2) z t hA (by positivity) hSpos (by linarith)
    hM hz htpos hcal.2.2.1 hm hbS htinv
  calc
    _ ≤ (65 * A + A ^ 2) * z / Real.sqrt S := habs
    _ = ((65 * A + A ^ 2) / 2) * (2 * z / Real.sqrt S) := by ring
    _ ≤ ((65 * A + A ^ 2) / 2) * (z ^ 2 + 1 / S) :=
      mul_le_mul_of_nonneg_left (hybrid_mixed_rate_le S z hSpos) (by positivity)
    _ = _ := by ring

/-- [Every retained term of equation (14), including the single-cell squared-bias
sum and the false-pilot remainder, is bounded by a universal multiple of the arm rate.
This is deterministic absorption; the probabilistic MSE assembly is separate. ](goal)-/
-- @node: hybrid_intermediate_envelope_rate
lemma hybrid_intermediate_envelope_rate :
    ∃ C : Real, 0 < C ∧ ∀ (S N d eps tp t M : Real),
      Real.exp 4096 ≤ S → 1 ≤ d → 0 < eps → eps ≤ 1 →
      S ≤ N * eps → N / 64 ≤ tp → N / 64 ≤ t →
      let L := Nat.floor (Real.log S / 1024)
      let B : Real := (2 : Real) ^ 20 * L / min tp t
      0 ≤ M → M ≤ d * B / eps →
      1 / S + d ^ 2 * B ^ 2 / (eps ^ 2 * (L : Real) ^ 4) +
        ((2 : Real) ^ 24) ^ L * (M / S + M / t + d * B ^ 2 / eps ^ 2) +
        d * B ^ 2 / (eps ^ 2 * (L : Real) ^ 4) + (S ^ 20)⁻¹ ≤
        C * (1 / S + (d / (N * eps * L)) ^ 2) := by
  let A : Real := 64 * (2 : Real) ^ 20
  let K : Real := (65 * A + A ^ 2) / 2
  refine ⟨2 + 2 * A ^ 2 + K, by dsimp [K, A]; positivity, ?_⟩
  intro S N d eps tp t M hS hd heps heps1 hNS htp ht
  dsimp only
  intro hM hmass
  let L := Nat.floor (Real.log S / 1024)
  let B : Real := (2 : Real) ^ 20 * L / min tp t
  let z := d / (N * eps * L)
  have hSpos : 0 < S := (Real.exp_pos _).trans_le hS
  have hS1 : 1 ≤ S := (Real.one_le_exp (by norm_num : (0 : Real) ≤ 4096)).trans hS
  have hN : 0 < N := by nlinarith
  have hL4 : (4 : Real) ≤ L := by exact_mod_cast (hybrid_degree_calibration S hS).1
  have hL : 0 < (L : Real) := by linarith
  have htpos : 0 < t := (show 0 < N / 64 by positivity).trans_le ht
  have htpPos : 0 < tp := (show 0 < N / 64 by positivity).trans_le htp
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hA : 0 ≤ A := by norm_num [A]
  have hband : B ≤ A * L / N := hybrid_bandwidth_public_bound N tp t L hN htp ht
  have hbig := (hybrid_bandwidth_rate_monomials A B d N eps L M
    hA hB (by linarith) hN heps hL hband hmass).2.2
  have hsmall : d * B ^ 2 / (eps ^ 2 * (L : Real) ^ 4) ≤ A ^ 2 * z ^ 2 := by
    apply le_trans _ hbig
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg B)
    nlinarith only [hd]
  have hlight := hybrid_calibrated_light_variance_rate S N d eps tp t M
    hS (by linarith) heps heps1 hNS htp ht hM hmass
  have htail := hybrid_pilot_remainder_le S hS1
  have hR : 0 ≤ 1 / S := by positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  change 1 / S + d ^ 2 * B ^ 2 / (eps ^ 2 * (L : Real) ^ 4) +
    ((2 : Real) ^ 24) ^ L * (M / S + M / t + d * B ^ 2 / eps ^ 2) +
    d * B ^ 2 / (eps ^ 2 * (L : Real) ^ 4) + (S ^ 20)⁻¹ ≤
    (2 + 2 * A ^ 2 + K) * (1 / S + z ^ 2)
  change ((2 : Real) ^ 24) ^ L * (M / S + M / t + d * B ^ 2 / eps ^ 2) ≤
    K * (1 / S + z ^ 2) at hlight
  change d ^ 2 * B ^ 2 / (eps ^ 2 * (L : Real) ^ 4) ≤ A ^ 2 * z ^ 2 at hbig
  nlinarith only [hbig, hsmall, hlight, htail, hR, sq_nonneg z,
    mul_nonneg (sq_nonneg A) hR]

/-- [Under the stated hypotheses](hyp:hC0,hCP,hCH), The actual canonical MSE envelope, with its branch constants and pool intensities,
absorbs into the public arm rate. The inverse-count variance is supplied by its
separate proved overlap bound; no retained pilot term is discarded.  This gives [the stated result](goal). -/
-- @node: hybrid_canonical_envelope_rate
lemma hybrid_canonical_envelope_rate (C0 CP CH : Real)
    (hC0 : 0 < C0) (hCP : 0 < CP) (hCH : 0 < CH) :
    ∃ C : Real, 0 < C ∧ ∀ (S N d eps u tp t M c H : Real),
      Real.exp 4096 ≤ S → 1 ≤ d → 0 < eps → eps ≤ 1 →
      S ≤ N * eps → S / 32 ≤ u * eps → N / 64 ≤ tp → N / 64 ≤ t →
      let L := Nat.floor (Real.log S / 1024)
      let B : Real := (2 : Real) ^ 20 * L / min tp t
      0 ≤ M → M ≤ d * B / eps → 0 ≤ c → c ≤ d →
      H ≤ C0 * (1 / (u * eps) + 1 / (t * eps)) →
      H + CP * ((2 : Real) ^ 24) ^ L * (M / (u * eps) + M / t + c * B ^ 2 / eps ^ 2) +
        2 * c * (B / (eps * (L : Real) ^ 2)) ^ 2 +
        1 / (Real.exp 1 * t * eps) +
        CH * (S ^ 20)⁻¹ * (1 / (u * eps) + 1 + 1 / t) +
        2 * d ^ 2 * B ^ 2 / (eps ^ 2 * (L : Real) ^ 4) + 18 * (S ^ 20)⁻¹ ≤
      C * (1 / S + (d / (N * eps * L)) ^ 2) := by
  obtain ⟨CE, hCE, habs⟩ := hybrid_intermediate_envelope_rate
  let K := 96 * C0 + 32 * CP + 97 * CH + 86
  refine ⟨K * CE, mul_pos (by dsimp [K]; positivity) hCE, ?_⟩
  intro S N d eps u tp t M c H hS hd heps heps1 hNS hu htp ht
  dsimp only
  intro hM hmass hc hcd hH
  let L := Nat.floor (Real.log S / 1024)
  let B : Real := (2 : Real) ^ 20 * L / min tp t
  let F := ((2 : Real) ^ 24) ^ L
  let Q := d ^ 2 * B ^ 2 / (eps ^ 2 * (L : Real) ^ 4)
  let W := F * (M / S + M / t + d * B ^ 2 / eps ^ 2)
  let R := d * B ^ 2 / (eps ^ 2 * (L : Real) ^ 4)
  let r := (S ^ 20)⁻¹
  let E := 1 / S + Q + W + R + r
  have hS1 : 1 ≤ S := (Real.one_le_exp (by norm_num : (0 : Real) ≤ 4096)).trans hS
  have hSp : 0 < S := by linarith
  have hN : 0 < N := by nlinarith
  have htpP : 0 < tp := (show 0 < N / 64 by positivity).trans_le htp
  have htP : 0 < t := (show 0 < N / 64 by positivity).trans_le ht
  have hue : 0 < u * eps := (show 0 < S / 32 by positivity).trans_le hu
  have hL : 0 < (L : Real) := by
    exact_mod_cast (show 0 < L from by have := (hybrid_degree_calibration S hS).1; omega)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hF : 0 ≤ F := by positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hEinv : 1 / S ≤ E := by dsimp [E]; linarith
  have hEQ : Q ≤ E := by dsimp [E]; linarith [show 0 ≤ 1 / S by positivity]
  have hEW : W ≤ E := by dsimp [E]; linarith [show 0 ≤ 1 / S by positivity]
  have hER : R ≤ E := by dsimp [E]; linarith [show 0 ≤ 1 / S by positivity]
  have hEr : r ≤ E := by dsimp [E]; linarith [show 0 ≤ 1 / S by positivity]
  have hui : 1 / (u * eps) ≤ 32 / S := by
    apply (div_le_div_iff₀ hue hSp).2
    linarith
  have hti : 1 / (t * eps) ≤ 64 / S := by
    apply (div_le_div_iff₀ (mul_pos htP heps) hSp).2
    have hh := mul_le_mul_of_nonneg_right ht heps.le
    nlinarith only [hh, hNS]
  have htplain : 1 / t ≤ 64 / S := by
    apply (div_le_div_iff₀ htP hSp).2
    have hne : N * eps ≤ N := mul_le_of_le_one_right hN.le heps1
    linarith
  have hi1 : 1 / S ≤ 1 := (div_le_one hSp).2 hS1
  have hheavy : H ≤ 96 * C0 * E := by
    calc
      H ≤ C0 * (1 / (u * eps) + 1 / (t * eps)) := hH
      _ ≤ C0 * (32 / S + 64 / S) := mul_le_mul_of_nonneg_left (add_le_add hui hti) hC0.le
      _ = 96 * C0 * (1 / S) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hEinv (by positivity)
  have hpoly : CP * F * (M / (u * eps) + M / t + c * B ^ 2 / eps ^ 2) ≤ 32 * CP * E := by
    have hm : M / (u * eps) ≤ 32 * (M / S) := by
      convert mul_le_mul_of_nonneg_left hui hM using 1 <;> first | rfl | ring
    have hcB : c * B ^ 2 / eps ^ 2 ≤ d * B ^ 2 / eps ^ 2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcd (sq_nonneg B)) (sq_nonneg eps)
    have hsum : M / (u * eps) + M / t + c * B ^ 2 / eps ^ 2 ≤
        32 * (M / S + M / t + d * B ^ 2 / eps ^ 2) := by
      have hmt : 0 ≤ M / t := by positivity
      have hdb : 0 ≤ d * B ^ 2 / eps ^ 2 := by positivity
      linarith
    calc
      _ ≤ CP * F * (32 * (M / S + M / t + d * B ^ 2 / eps ^ 2)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 32 * CP * W := by dsimp [W]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hEW (by positivity)
  have hsep : 2 * c * (B / (eps * (L : Real) ^ 2)) ^ 2 ≤ 2 * E := by
    calc
      _ ≤ 2 * d * (B / (eps * (L : Real) ^ 2)) ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith : 2 * c ≤ 2 * d) (sq_nonneg _)
      _ = 2 * R := by dsimp [R]; ring
      _ ≤ _ := by linarith
  have hexp : 1 / (Real.exp 1 * t * eps) ≤ 64 * E := by
    have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    calc
      _ ≤ 1 / (t * eps) := one_div_le_one_div_of_le (by positivity) (by
        have hh := mul_le_mul_of_nonneg_right he (mul_nonneg htP.le heps.le)
        nlinarith only [hh])
      _ ≤ 64 / S := hti
      _ = 64 * (1 / S) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hEinv (by norm_num)
  have htail : CH * r * (1 / (u * eps) + 1 + 1 / t) ≤ 97 * CH * E := by
    have hsum : 1 / (u * eps) + 1 + 1 / t ≤ 97 := by
      have hu1 : 32 / S ≤ 32 := by
        convert mul_le_mul_of_nonneg_left hi1 (by norm_num : (0 : Real) ≤ 32) using 1 <;>
          first | rfl | ring
      have ht1 : 64 / S ≤ 64 := by
        convert mul_le_mul_of_nonneg_left hi1 (by norm_num : (0 : Real) ≤ 64) using 1 <;>
          first | rfl | ring
      linarith
    calc
      _ ≤ CH * r * 97 := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 97 * CH * r := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hEr (by positivity)
  have henv : E ≤ CE * (1 / S + (d / (N * eps * L)) ^ 2) :=
    habs S N d eps tp t M hS hd heps heps1 hNS htp ht hM hmass
  have hbias : 2 * d ^ 2 * B ^ 2 / (eps ^ 2 * (L : Real) ^ 4) ≤ 2 * E := by
    calc
      _ = 2 * Q := by dsimp [Q]; ring
      _ ≤ _ := by linarith only [hEQ]
  calc
    _ ≤ K * E := by
      change H + CP * F * (M / (u * eps) + M / t + c * B ^ 2 / eps ^ 2) +
        2 * c * (B / (eps * (L : Real) ^ 2)) ^ 2 +
        1 / (Real.exp 1 * t * eps) + CH * r * (1 / (u * eps) + 1 + 1 / t) +
        2 * d ^ 2 * B ^ 2 / (eps ^ 2 * (L : Real) ^ 4) + 18 * r ≤ K * E
      dsimp only [K]
      linarith only [hheavy, hpoly, hsep, hexp, htail, hbias, hEr]
    _ ≤ K * (CE * (1 / S + (d / (N * eps * L)) ^ 2)) :=
      mul_le_mul_of_nonneg_left henv (by dsimp [K]; positivity)
    _ = _ := by ring

end CausalSmith.Stat.AnnotationRarearmFrontier
