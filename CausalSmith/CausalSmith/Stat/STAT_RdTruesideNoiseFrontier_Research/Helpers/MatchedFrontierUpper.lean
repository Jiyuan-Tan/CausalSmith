module
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.FrontierRoot
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.TFiniteCertificate

/-!
# Uniform upper tuning for the matched frontier

The public finite selector is compared with the scalar frontier using a rounded
degree whose squared reciprocal is a fixed dilation of the scalar resolution.
-/

public section

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology

namespace CausalSmith.Stat.RdTruesideNoiseFrontier

/-- Exponentiating the scalar root equation gives the exact balance identity. Given [the displayed inputs and assumptions](hyp:β,n,σ,hβ,hn,hσ), [the stated mathematical conclusion holds](goal). -/
lemma rateRoot_exp_balance (β : ℝ) (n : ℕ) (σ : ℝ)
    (hβ : β ∈ Ioc (0 : ℝ) 1) (hn : 2 ≤ n) (hσ : σ ∈ Icc (0 : ℝ) 1) :
    Real.exp (noiseCost (rateResolution β n σ) σ) =
      (n : ℝ) * rateResolution β n σ ^ (2 * β + 1) := by
  have hr := unique_rate_root β n σ hβ hn hσ
  have hd := directResolution_pos_le_one β n hβ hn
  have hH : 0 < rateResolution β n σ := hd.1.trans_le hr.1.1
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  rw [← hr.2.1, Real.exp_add, Real.exp_log hnpos,
    Real.rpow_def_of_pos hH, mul_comm (Real.log _) _]

/-- Ceiling a number above one loses at most a factor two. Given [the displayed inputs and assumptions](hyp:x,hx), [the stated mathematical conclusion holds](goal). -/
lemma ceil_one_two_bounds (x : ℝ) (hx : 1 < x) :
    1 ≤ ⌈x⌉₊ ∧ x ≤ (⌈x⌉₊ : ℝ) ∧ (⌈x⌉₊ : ℝ) ≤ 2 * x := by
  have hx0 : 0 ≤ x := hx.le.trans' (by norm_num)
  have hceil := Nat.le_ceil x
  have hlt := Nat.ceil_lt_add_one hx0
  have hone : 1 ≤ ⌈x⌉₊ := by
    apply Nat.one_le_iff_ne_zero.mpr
    intro hz
    rw [hz] at hceil
    norm_num at hceil
    linarith
  exact ⟨hone, hceil, by
    have hxone : 1 ≤ x := hx.le
    linarith⟩

/-- The rounded upper degree has a width between one quarter and one times
the requested dilated resolution. Given [the displayed inputs and assumptions](hyp:A,H,hA,hH,hsmall), [the stated mathematical conclusion holds](goal). -/
lemma upperDegree_width_bounds (A H : ℝ) (hA : 0 < A) (hH : 0 < H)
    (hsmall : A * H < 1) :
    let x := (A * H) ^ (-1 / 2 : ℝ)
    let J := ⌈x⌉₊
    1 ≤ J ∧ A * H / 4 ≤ (J : ℝ) ^ (-2 : ℝ) ∧
      (J : ℝ) ^ (-2 : ℝ) ≤ A * H := by
  dsimp only
  let x := (A * H) ^ (-1 / 2 : ℝ)
  have hAH : 0 < A * H := mul_pos hA hH
  have hx : 1 < x := by
    dsimp [x]
    exact Real.one_lt_rpow_of_pos_of_lt_one_of_neg hAH hsmall (by norm_num)
  obtain ⟨hJ, hxJ, hJx⟩ := ceil_one_two_bounds x hx
  have hJpos : (0 : ℝ) < ⌈x⌉₊ := by exact_mod_cast (show 0 < ⌈x⌉₊ by omega)
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hupper := Real.rpow_le_rpow_of_nonpos hxpos hxJ (by norm_num : (-2 : ℝ) ≤ 0)
  have hlower := Real.rpow_le_rpow_of_nonpos hJpos hJx (by norm_num : (-2 : ℝ) ≤ 0)
  have hxpow : x ^ (-2 : ℝ) = A * H := by
    dsimp [x]
    rw [← Real.rpow_mul hAH.le]
    norm_num
  have h2xpow : (2 * x) ^ (-2 : ℝ) = A * H / 4 := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hxpos.le, hxpow]
    norm_num [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    ring_nf
  change 1 ≤ ⌈x⌉₊ ∧ A * H / 4 ≤ (⌈x⌉₊ : ℝ) ^ (-2 : ℝ) ∧
    (⌈x⌉₊ : ℝ) ^ (-2 : ℝ) ≤ A * H
  exact ⟨hJ, by rw [← h2xpow]; exact hlower,
    hupper.trans_eq hxpow⟩

/-- The rounded dilated degree remains in the public finite candidate set. Given [the displayed inputs and assumptions](hyp:β,A,H,n,hβ,hn,hA,hH), [the stated mathematical conclusion holds](goal). -/
lemma upperDegree_le_Lmax (β A H : ℝ) (n : ℕ)
    (hβ : β ∈ Ioc (0 : ℝ) 1) (hn : 2 ≤ n) (hA : 1 ≤ A)
    (hH : directResolution β n ≤ H) :
    ⌈(A * H) ^ (-1 / 2 : ℝ)⌉₊ ≤ Lmax β n := by
  have hν : 0 < 2 * β + 1 := by linarith [hβ.1]
  have hd := directResolution_pos_le_one β n hβ hn
  have hHpos : 0 < H := hd.1.trans_le hH
  have hAH : H ≤ A * H := by nlinarith
  have hpowAH := Real.rpow_le_rpow_of_nonpos hHpos hAH (by norm_num : (-1 / 2 : ℝ) ≤ 0)
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hdirect : (directResolution β n) ^ (-1 / 2 : ℝ) =
      (n : ℝ) ^ (1 / (4 * β + 2)) := by
    unfold directResolution
    rw [← Real.rpow_mul hnpos.le]
    congr 1
    have hden : 2 + β * 4 ≠ 0 := by nlinarith [hβ.1]
    rw [div_eq_mul_inv]
    apply (eq_div_iff (by nlinarith [hβ.1] : 4 * β + 2 ≠ 0)).2
    field_simp [hden]
    ring
  have hHdirect := Real.rpow_le_rpow_of_nonpos hd.1 hH (by norm_num : (-1 / 2 : ℝ) ≤ 0)
  unfold Lmax
  exact Nat.ceil_mono (hpowAH.trans (hHdirect.trans_eq hdirect))

/-- A dilation by at least `(D+1)^2` absorbs the variance-envelope
constant in the square-root cost scaling. Given [the displayed inputs and assumptions](hyp:D,a,c,hD,ha,hc), [the stated mathematical conclusion holds](goal). -/
lemma dilation_cost_absorption (D a c : ℝ) (hD : 0 < D)
    (ha : (D + 1)^2 ≤ a) (hc : 0 ≤ c) :
    D * max 1 (a ^ (-1 / 2 : ℝ) * (1 + c)) ≤ D + (1 + c) := by
  have ha0 : 0 < a := lt_of_lt_of_le (sq_pos_of_pos (by linarith : 0 < D + 1)) ha
  have hDsqrt : D ≤ Real.sqrt a := by
    apply (Real.le_sqrt hD.le ha0.le).2
    nlinarith
  have hinv : D * a ^ (-1 / 2 : ℝ) ≤ 1 := by
    have hsqrt : 0 < Real.sqrt a := Real.sqrt_pos.2 ha0
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by norm_num,
      Real.rpow_neg ha0.le, ← Real.sqrt_eq_rpow]
    rw [mul_inv_le_iff₀ hsqrt]
    simpa only [one_mul] using hDsqrt
  rw [mul_max_of_nonneg 1 (a ^ (-1 / 2 : ℝ) * (1 + c)) hD.le]
  apply max_le
  · linarith
  · calc
      D * (a ^ (-1 / 2 : ℝ) * (1 + c)) =
          (D * a ^ (-1 / 2 : ℝ)) * (1 + c) := by ring
      _ ≤ 1 * (1 + c) := mul_le_mul_of_nonneg_right hinv (by linarith)
      _ ≤ D + (1 + c) := by linarith

/-- The public finite certificate is uniformly bounded by the scalar frontier.
The constant depends only on the smoothness exponent (and on the two classical
polynomial identities packaged by the cited gates). Given [the displayed inputs and assumptions](hyp:legendre_of_gate,hermite_of_gate,β,hβ), [the stated mathematical conclusion holds](goal). -/
theorem certificate_le_frontierRate
    (legendre_of_gate : ClassicalLegendreFacts)
    (hermite_of_gate : ClassicalHermiteFacts)
    (β : ℝ) (hβ : β ∈ Ioc (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ σ ∈ Icc (0 : ℝ) 1,
      certificate β n σ ≤ C * frontierRate β n σ := by
  obtain ⟨K, hK, hmoment⟩ := positive_endpoint β hβ
  obtain ⟨D, hD, hvariance⟩ :=
    variance_cost_envelope
  let A : ℝ := 4 * (D + 1)^2
  let Q : ℝ := Real.sqrt (160 * D * Real.exp (D + 1))
  let C : ℝ := max ((1 / 2 : ℝ) * A ^ β)
    (12 * K * A ^ β + 28 * Q)
  have hA : 4 ≤ A := by
    dsimp [A]
    nlinarith [sq_nonneg D]
  have hApos : 0 < A := by linarith
  have hQ : 0 < Q := by
    dsimp [Q]
    positivity
  have hC : 0 < C := by
    exact lt_of_lt_of_le (by positivity : 0 < 12 * K * A ^ β + 28 * Q)
      (le_max_right _ _)
  refine ⟨C, hC, ?_⟩
  intro n hn σ hσ
  let H := rateResolution β n σ
  have hr := unique_rate_root β n σ hβ hn hσ
  have hd := directResolution_pos_le_one β n hβ hn
  have hHpos : 0 < H := hd.1.trans_le hr.1.1
  have hHle : H ≤ 1 := hr.1.2
  have hHmem : H ∈ Ioc (0 : ℝ) 1 := ⟨hHpos, hHle⟩
  have hHβpos : 0 < H ^ β := Real.rpow_pos_of_pos hHpos β
  have hfrontier : frontierRate β n σ = H ^ β := rfl
  by_cases hlarge : 1 ≤ A * H
  · have hAβpos : 0 < A ^ β := Real.rpow_pos_of_pos hApos β
    have hAHβ : 1 ≤ (A * H) ^ β :=
      Real.one_le_rpow hlarge (le_of_lt hβ.1)
    have hmul : A ^ β * H ^ β = (A * H) ^ β := by
      rw [Real.mul_rpow hApos.le hHpos.le]
    have hfallback : (1 / 2 : ℝ) ≤ ((1 / 2 : ℝ) * A ^ β) * H ^ β := by
      rw [mul_assoc, hmul]
      nlinarith
    rw [hfrontier]
    exact (certificate_le_half β n σ).trans
      (hfallback.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hHβpos.le))
  · have hsmall : A * H < 1 := lt_of_not_ge hlarge
    let x : ℝ := (A * H) ^ (-1 / 2 : ℝ)
    let J : ℕ := ⌈x⌉₊
    obtain ⟨hJ, hwidth_lower, hwidth_upper⟩ :=
      upperDegree_width_bounds A H hApos hHpos hsmall
    have hJnat : 1 ≤ J := by exact hJ
    have hJcap : J ≤ Lmax β n :=
      upperDegree_le_Lmax β A H n hβ hn (by linarith) hr.1.1
    have hJpos : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
    let width : ℝ := (J : ℝ) ^ (-2 : ℝ)
    let a : ℝ := width / H
    have hwidth_pos : 0 < width := Real.rpow_pos_of_pos hJpos _
    have haH : a * H = width := by
      dsimp [a]
      field_simp
    have ha_lower : (D + 1)^2 ≤ a := by
      dsimp [a]
      apply (le_div_iff₀ hHpos).2
      calc
        (D + 1)^2 * H = A * H / 4 := by dsimp [A]; ring
        _ ≤ width := hwidth_lower
    have ha_one : 1 ≤ a := by nlinarith [sq_nonneg D]
    have ha_pos : 0 < a := lt_of_lt_of_le zero_lt_one ha_one
    have ha_upper : a ≤ A := by
      dsimp [a]
      rw [div_le_iff₀ hHpos]
      simpa only using hwidth_upper
    have hawidth_le : a * H ≤ 1 := by rw [haH]; exact hwidth_upper.trans hsmall.le
    have hcost_nonneg : 0 ≤ noiseCost H σ := noiseCost_nonneg H σ hHmem hσ
    have hcostscale := noise_cost_scaling.2.2 H σ a hHmem hσ ha_one hawidth_le
    rw [haH] at hcostscale
    have hcostabs :
        D * (1 + noiseCost width σ) ≤ D + (1 + noiseCost H σ) :=
      (mul_le_mul_of_nonneg_left hcostscale hD.le).trans
        (dilation_cost_absorption D a (noiseCost H σ) hD ha_lower hcost_nonneg)
    have hmomentJ := (hmoment J hJ).2.2.1
    have hpow_width : (J : ℝ) ^ (-2 * β) = width ^ β := by
      dsimp [width]
      rw [← Real.rpow_mul hJpos.le]
    have hwidthβ : width ^ β ≤ (A * H) ^ β :=
      Real.rpow_le_rpow hwidth_pos.le hwidth_upper hβ.1.le
    have hAHpow : (A * H) ^ β = A ^ β * H ^ β :=
      Real.mul_rpow hApos.le hHpos.le
    have hbias : kernelMoment J β ≤ K * A ^ β * H ^ β := by
      calc
        kernelMoment J β ≤ K * (J : ℝ) ^ (-2 * β) := hmomentJ
        _ = K * width ^ β := by rw [hpow_width]
        _ ≤ K * (A * H) ^ β := mul_le_mul_of_nonneg_left hwidthβ hK.le
        _ = K * A ^ β * H ^ β := by rw [hAHpow]; ring
    have hvar0 := hvariance J hJ σ hσ
    have hexp :
        Real.exp (D * (1 + noiseCost width σ)) ≤
          Real.exp (D + 1) * Real.exp (noiseCost H σ) := by
      calc
        _ ≤ Real.exp (D + (1 + noiseCost H σ)) := Real.exp_le_exp.mpr hcostabs
        _ = _ := by rw [show D + (1 + noiseCost H σ) =
          (D + 1) + noiseCost H σ by ring, Real.exp_add]
    have hvar1 : kernelVariance J σ ≤
        D * (J : ℝ)^2 * (Real.exp (D + 1) * Real.exp (noiseCost H σ)) :=
      hvar0.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
    have hxgt : 1 < x := by
      dsimp [x]
      exact Real.one_lt_rpow_of_pos_of_lt_one_of_neg (mul_pos hApos hHpos)
        hsmall (by norm_num)
    have hJx : (J : ℝ) ≤ 2 * x := (ceil_one_two_bounds x hxgt).2.2
    have hx_sq : x^2 = (A * H)⁻¹ := by
      dsimp [x]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (mul_pos hApos hHpos).le]
      norm_num [Real.rpow_neg_one]
    have hJ_sq : (J : ℝ)^2 ≤ 4 / H := by
      have hsquare := (sq_le_sq₀ (by positivity : (0 : ℝ) ≤ J)
        (by positivity : 0 ≤ 2 * x)).2 hJx
      rw [mul_pow, hx_sq] at hsquare
      have hAHne : A * H ≠ 0 := ne_of_gt (mul_pos hApos hHpos)
      rw [inv_eq_one_div] at hsquare
      calc
        (J : ℝ)^2 ≤ 2^2 * (1 / (A * H)) := hsquare
        _ ≤ 4 / H := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          have hAinv : (A * H)⁻¹ ≤ H⁻¹ := by
            apply (inv_le_inv₀ (a := A * H) (b := H)
              (mul_pos hApos hHpos) hHpos).2
            nlinarith [hA]
          norm_num at hAinv ⊢
          linarith
    have hbalance := rateRoot_exp_balance β n σ hβ hn hσ
    change Real.exp (noiseCost H σ) = (n : ℝ) * H ^ (2 * β + 1) at hbalance
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    have hHsplit : H ^ (2 * β + 1) = H ^ (2 * β) * H := by
      rw [show 2 * β + 1 = 2 * β + 1 by ring, Real.rpow_add hHpos]
      simp
    have hvar2 : 40 * kernelVariance J σ / (n : ℝ) ≤
        160 * D * Real.exp (D + 1) * H ^ (2 * β) := by
      rw [hbalance, hHsplit] at hvar1
      apply (div_le_iff₀ hnpos).2
      have hJH : (J : ℝ)^2 * H ≤ 4 := by
        have ht := mul_le_mul_of_nonneg_right hJ_sq hHpos.le
        calc
          (J : ℝ)^2 * H ≤ (4 / H) * H := ht
          _ = 4 := by field_simp
      have hfac : 0 ≤ 40 * D * Real.exp (D + 1) * (n : ℝ) * H ^ (2 * β) := by
        positivity
      calc
        40 * kernelVariance J σ ≤
            40 * (D * (J : ℝ)^2 *
              (Real.exp (D + 1) * ((n : ℝ) * (H ^ (2 * β) * H)))) :=
          mul_le_mul_of_nonneg_left hvar1 (by norm_num)
        _ = (40 * D * Real.exp (D + 1) * (n : ℝ) * H ^ (2 * β)) *
              ((J : ℝ)^2 * H) := by ring
        _ ≤ (40 * D * Real.exp (D + 1) * (n : ℝ) * H ^ (2 * β)) * 4 :=
          mul_le_mul_of_nonneg_left hJH hfac
        _ = (160 * D * Real.exp (D + 1) * H ^ (2 * β)) * (n : ℝ) := by ring
    have hsqrt : Real.sqrt (40 * kernelVariance J σ / (n : ℝ)) ≤ Q * H ^ β := by
      have hsqrt_mono := Real.sqrt_le_sqrt hvar2
      have hconst : 0 ≤ 160 * D * Real.exp (D + 1) := by positivity
      have hpowsq : H ^ (2 * β) = (H ^ β)^2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hHpos.le]
        congr 1
        ring
      rw [hpowsq, Real.sqrt_mul hconst, Real.sqrt_sq_eq_abs,
        abs_of_pos hHβpos] at hsqrt_mono
      exact hsqrt_mono
    have hradius : radius β n σ J ≤
        (12 * K * A ^ β + 28 * Q) * H ^ β := by
      simp only [radius, if_neg (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hJnat))]
      calc
        12 * kernelMoment J β + 28 * Real.sqrt (40 * kernelVariance J σ / ↑n) ≤
            12 * (K * A ^ β * H ^ β) + 28 * (Q * H ^ β) :=
          add_le_add (mul_le_mul_of_nonneg_left hbias (by norm_num))
            (mul_le_mul_of_nonneg_left hsqrt (by norm_num))
        _ = (12 * K * A ^ β + 28 * Q) * H ^ β := by ring
    rw [hfrontier]
    exact (selectedDegree_radius_le β n σ J hJcap).trans
      (hradius.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hHβpos.le))

end CausalSmith.Stat.RdTruesideNoiseFrontier
