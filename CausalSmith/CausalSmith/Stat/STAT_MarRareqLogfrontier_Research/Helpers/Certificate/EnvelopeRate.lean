module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.PrefixTransfer
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! Uniform comparison of the explicit envelope with the frontier rate. -/

public section

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

attribute [local instance] Classical.propDecidable

private lemma exp_neg_le_inv (x : ℝ) (hx : 0 < x) :
    Real.exp (-x) ≤ x⁻¹ := by
  have hxe : x ≤ Real.exp x :=
    (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp x)
  rw [Real.exp_neg]
  exact inv_anti₀ hx hxe

private lemma half_le_natFloor {x : ℝ} (hx : 1 ≤ x) :
    x / 2 ≤ (Nat.floor x : ℝ) := by
  by_cases h : x < 2
  · have hf : 1 ≤ Nat.floor x := Nat.le_floor (by simpa using hx)
    have hf' : (1 : ℝ) ≤ Nat.floor x := by exact_mod_cast hf
    linarith
  · have hfloor := Nat.lt_floor_add_one x
    have h : 2 ≤ x := le_of_not_gt h
    linarith

private lemma min_four_le_const_min_one {E R C : ℝ}
    (hE : E ≤ C * R) (_hR : 0 ≤ R) (hC : 4 ≤ C) :
    min 4 E ≤ C * min 1 R := by
  by_cases hR1 : R ≤ 1
  · rw [min_eq_right hR1]
    exact (min_le_right 4 E).trans hE
  · rw [min_eq_left (le_of_not_ge hR1)]
    calc
      min 4 E ≤ 4 := min_le_left _ _
      _ ≤ C := hC
      _ = C * 1 := by ring

private lemma logscale_basic (N ell : ℝ) (hN : 1 < N)
    (hell : ell = Real.log (Real.exp 1 + N)) :
    1 < ell ∧ Real.exp ell = Real.exp 1 + N ∧
      Real.exp (-ell) ≤ N⁻¹ := by
  have he1 : Real.exp 1 < Real.exp 1 + N := by linarith
  have hepos : 0 < Real.exp 1 + N := by positivity
  have hl : 1 < ell := by
    have h := Real.strictMonoOn_log (Real.exp_pos 1) hepos he1
    simpa [hell] using h
  have hexp : Real.exp ell = Real.exp 1 + N := by
    rw [hell, Real.exp_log hepos]
  have hNe : N < Real.exp ell := by rw [hexp]; linarith [Real.exp_pos 1]
  refine ⟨hl, hexp, ?_⟩
  rw [Real.exp_neg]
  exact inv_anti₀ (by linarith) hNe.le

private lemma poisson_tail_rate (n : ℕ) (N : ℝ) (hn : 1 ≤ n)
    (hNpos : 0 < N) (hNn : N ≤ n) :
    Real.exp (-(n : ℝ) * (Real.log 2 - 1 / 2)) ≤ 8 * N⁻¹ := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hgamma : (1 / 8 : ℝ) ≤ Real.log 2 - 1 / 2 := by
    nlinarith [Real.log_two_gt_d9]
  have ht : 0 < (n : ℝ) * (Real.log 2 - 1 / 2) := by positivity
  have hdecay := exp_neg_le_inv ((n : ℝ) * (Real.log 2 - 1 / 2)) ht
  have hinv : ((n : ℝ) * (Real.log 2 - 1 / 2))⁻¹ ≤ 8 * ((n : ℝ)⁻¹) := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ ht).2
    have : 1 ≤ 8 * (Real.log 2 - 1 / 2) := by nlinarith
    have heq : (n : ℝ)⁻¹ * ((n : ℝ) * (Real.log 2 - 1 / 2)) =
        Real.log 2 - 1 / 2 := by
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hnR), one_mul]
    rw [mul_assoc, heq]
    exact this
  have hinvN : (n : ℝ)⁻¹ ≤ N⁻¹ := by
    rw [inv_eq_one_div, inv_eq_one_div]
    exact one_div_le_one_div_of_le hNpos hNn
  calc
    Real.exp (-(n : ℝ) * (Real.log 2 - 1 / 2)) =
        Real.exp (-((n : ℝ) * (Real.log 2 - 1 / 2))) := by ring_nf
    _ ≤ ((n : ℝ) * (Real.log 2 - 1 / 2))⁻¹ := hdecay
    _ ≤ 8 * (n : ℝ)⁻¹ := hinv
    _ ≤ 8 * N⁻¹ := mul_le_mul_of_nonneg_left hinvN (by norm_num)

private lemma needle_growth (N ell d : ℝ) (hN : 1 < N) (hell : 128 ≤ ell)
    (hexp : Real.exp ell = Real.exp 1 + N) (hd : Real.sqrt N ≤ d)
    (hd0 : 0 ≤ d) :
    (Real.exp (ell / 8) + 1) * ell ^ 4 ≤ 262144 * d ∧ ell ≤ 2 * d := by
  have hell0 : 0 ≤ ell := by linarith
  have hlin0 := Real.two_mul_le_exp (x := ell / 32)
  have hlin : ell ≤ 16 * Real.exp (ell / 32) := by nlinarith
  have hpow := pow_le_pow_left₀ hell0 hlin 4
  have hpow' : ell ^ 4 ≤ 65536 * Real.exp (ell / 8) := by
    calc
      ell ^ 4 ≤ (16 * Real.exp (ell / 32)) ^ 4 := hpow
      _ = 65536 * Real.exp (ell / 8) := by
        rw [mul_pow, ← Real.exp_nat_mul]
        congr 1 <;> norm_num <;> ring
  have hy1 : 1 ≤ Real.exp (ell / 8) := Real.one_le_exp (by positivity)
  have hquarter : Real.exp (ell / 4) ≤ Real.exp (ell / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  have hexpone : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
  have hexp_upper : Real.exp ell ≤ 4 * N := by rw [hexp]; nlinarith
  have hdsq : N ≤ d ^ 2 := by
    have hsqrt := Real.sq_sqrt (by linarith : 0 ≤ N)
    have hs := pow_le_pow_left₀ (Real.sqrt_nonneg N) hd 2
    simpa [hsqrt] using hs
  have hhalf_sq : (Real.exp (ell / 2)) ^ 2 = Real.exp ell := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hhalf : Real.exp (ell / 2) ≤ 2 * d := by
    have hs : (Real.exp (ell / 2)) ^ 2 ≤ (2 * d) ^ 2 := by
      rw [hhalf_sq]
      nlinarith
    nlinarith [Real.exp_pos (ell / 2), sq_nonneg (Real.exp (ell / 2) + 2 * d)]
  constructor
  · calc
      (Real.exp (ell / 8) + 1) * ell ^ 4 ≤
          (2 * Real.exp (ell / 8)) * (65536 * Real.exp (ell / 8)) :=
        mul_le_mul (by nlinarith) hpow' (by positivity) (by positivity)
      _ = 131072 * Real.exp (ell / 4) := by
        rw [show 2 * Real.exp (ell / 8) * (65536 * Real.exp (ell / 8)) =
          131072 * (Real.exp (ell / 8) * Real.exp (ell / 8)) by ring,
          ← Real.exp_add]
        congr 2
        ring
      _ ≤ 131072 * Real.exp (ell / 2) :=
        mul_le_mul_of_nonneg_left hquarter (by norm_num)
      _ ≤ 262144 * d := by nlinarith
  · have hell_exp : ell ≤ Real.exp (ell / 2) := by
      convert Real.two_mul_le_exp (x := ell / 2) using 1 <;> ring
    exact hell_exp.trans hhalf

set_option maxHeartbeats 2000000 in
-- The explicit three-branch normalization requires substantial nonlinear arithmetic.
/-- [the stated mathematical conclusion holds](goal). -/
lemma riskEnvelope_le_frontierRate :
    ∃ C : ℝ, 0 < C ∧ ∀ (n d : ℕ) (q : ℝ),
      1 ≤ n → 1 ≤ d → 0 < q → q ≤ 1 →
        riskEnvelope n d q ≤ C * frontierRate n d q := by
  refine ⟨10 ^ 30, by norm_num, ?_⟩
  intro n d q hn hd hq hq1
  let N := effectiveSize n q
  let m := streamSize n
  let N₀ := streamEffectiveSize n q
  let ell := logScale n q
  let k := needleDegree n q
  let B := needleRadius n q
  let gamma := Real.log 2 - 1 / 2
  change (if N ≤ 1 then 1 else if ¬ needleBranch n d q then
    min 4 (((8 * d / (Real.exp 1 * N₀)) ^ 2) +
      4 * (4 / N₀ + 1 / m) + 4 * Real.exp (-(n : ℝ) * gamma))
    else
      let b := 2 * (4 * d * B / (N₀ * (k : ℝ) ^ 2) + 3 * Real.exp (-16 * ell))
      let v := 8 * (4 / N₀ + 1 / m) +
        64 * d * (Real.exp (ell / 8) + 1) *
          (B ^ 2 / N₀ ^ 2 + B / (m * N₀)) +
          32 * Real.exp (-32 * ell) * (1 + 1 / m)
      min 4 (b ^ 2 + v + 4 * Real.exp (-(n : ℝ) * gamma))) ≤
    10 ^ 30 * min 1 (N⁻¹ + ((d : ℝ) / (N * ell)) ^ 2)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hNpos : 0 < N := by
    dsimp [N, effectiveSize]
    positivity
  have hNn : N ≤ (n : ℝ) := by
    dsimp [N, effectiveSize]
    nlinarith [mul_nonneg hnR.le hq.le]
  have hm : m = (n : ℝ) / 6 := rfl
  have hN₀ : N₀ = N / 6 := by
    dsimp [N₀, streamEffectiveSize, streamSize, N, effectiveSize]
    ring
  have hell : ell = Real.log (Real.exp 1 + N) := rfl
  have hR0 : 0 ≤ N⁻¹ + ((d : ℝ) / (N * ell)) ^ 2 :=
    add_nonneg (inv_nonneg.mpr hNpos.le) (sq_nonneg _)
  by_cases hsmall : N ≤ 1
  · rw [if_pos hsmall]
    have hInv : 1 ≤ N⁻¹ := (one_le_inv₀ hNpos).2 hsmall
    have hR1 : 1 ≤ N⁻¹ + ((d : ℝ) / (N * ell)) ^ 2 := by
      nlinarith [sq_nonneg ((d : ℝ) / (N * ell))]
    rw [min_eq_left hR1]
    norm_num
  · rw [if_neg hsmall]
    have hN1 : 1 < N := lt_of_not_ge hsmall
    obtain ⟨hell1, hexpell, hexpneg⟩ := logscale_basic N ell hN1 hell
    have hellpos : 0 < ell := lt_trans (by norm_num) hell1
    have htail := poisson_tail_rate n N hn hNpos hNn
    have hmpos : 0 < m := by rw [hm]; positivity
    have hN₀pos : 0 < N₀ := by rw [hN₀]; positivity
    have hN₀inv : 1 / N₀ = 6 * N⁻¹ := by
      rw [hN₀]
      field_simp
    have hminv : 1 / m ≤ 6 * N⁻¹ := by
      have hmN : N / 6 ≤ m := by rw [hm]; linarith
      calc
        1 / m ≤ 1 / (N / 6) := one_div_le_one_div_of_le (by positivity) hmN
        _ = 6 * N⁻¹ := by field_simp
    by_cases hbranch : needleBranch n d q
    · rw [if_neg (not_not_intro hbranch)]
      rcases hbranch with ⟨hell128, hdsqrt⟩
      have hB : B = 256 * ell := rfl
      have hxfloor : 1 ≤ ell / 64 := by linarith
      have hk : ell / 128 ≤ (k : ℝ) := by
        have hf := half_le_natFloor hxfloor
        dsimp [k, needleDegree]
        convert hf using 1 <;> ring
      have hkpos : 0 < (k : ℝ) := lt_of_lt_of_le (by positivity) hk
      have hkSq : (ell / 128) ^ 2 ≤ (k : ℝ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hk 2
      obtain ⟨hgrowth, hell_d⟩ :=
        needle_growth N ell d hN1 hell128 hexpell hdsqrt hdR.le
      have hexp16 : Real.exp (-16 * ell) ≤ N⁻¹ := by
        exact (Real.exp_le_exp.mpr (by nlinarith)).trans hexpneg
      have hexp32 : Real.exp (-32 * ell) ≤ N⁻¹ := by
        exact (Real.exp_le_exp.mpr (by nlinarith)).trans hexpneg
      have hinv_ratio : N⁻¹ ≤ 2 * (d : ℝ) / (N * ell) := by
        rw [inv_eq_one_div]
        apply (div_le_div_iff₀ hNpos (mul_pos hNpos hellpos)).2
        have hp : 0 ≤ N * (2 * (d : ℝ) - ell) :=
          mul_nonneg hNpos.le (sub_nonneg.mpr hell_d)
        nlinarith
      have hmain : 4 * (d : ℝ) * B / (N₀ * (k : ℝ) ^ 2) ≤
          100663296 * ((d : ℝ) / (N * ell)) := by
        rw [hB, hN₀]
        calc
          4 * (d : ℝ) * (256 * ell) / (N / 6 * (k : ℝ) ^ 2) =
              6144 * (d : ℝ) * ell / (N * (k : ℝ) ^ 2) := by field_simp; ring
          _ ≤ 6144 * (d : ℝ) * ell / (N * (ell / 128) ^ 2) := by
            have hnumer : 0 ≤ 6144 * (d : ℝ) * ell := by positivity
            have hden := mul_le_mul_of_nonneg_left hkSq hNpos.le
            exact div_le_div_of_nonneg_left hnumer
              (mul_pos hNpos (sq_pos_of_pos (by positivity : 0 < ell / 128))) hden
          _ = 100663296 * ((d : ℝ) / (N * ell)) := by field_simp; ring
      have hbias_inside :
          4 * (d : ℝ) * B / (N₀ * (k : ℝ) ^ 2) +
              3 * Real.exp (-16 * ell) ≤
            100663302 * ((d : ℝ) / (N * ell)) := by
        have htail_ratio : 3 * Real.exp (-16 * ell) ≤
            6 * ((d : ℝ) / (N * ell)) := by
          calc
            3 * Real.exp (-16 * ell) ≤ 3 * N⁻¹ :=
              mul_le_mul_of_nonneg_left hexp16 (by norm_num)
            _ ≤ 3 * (2 * (d : ℝ) / (N * ell)) :=
              mul_le_mul_of_nonneg_left hinv_ratio (by norm_num)
            _ = 6 * ((d : ℝ) / (N * ell)) := by ring
        linarith
      have hbias_sq :
          (2 * (4 * (d : ℝ) * B / (N₀ * (k : ℝ) ^ 2) +
            3 * Real.exp (-16 * ell))) ^ 2 ≤
          40532401478172816 * ((d : ℝ) / (N * ell)) ^ 2 := by
        have hins0 : 0 ≤ 4 * (d : ℝ) * B / (N₀ * (k : ℝ) ^ 2) +
            3 * Real.exp (-16 * ell) := by rw [hB]; positivity
        have hs := pow_le_pow_left₀ hins0 hbias_inside 2
        calc
          (2 * (4 * (d : ℝ) * B / (N₀ * (k : ℝ) ^ 2) +
            3 * Real.exp (-16 * ell))) ^ 2 ≤
              (2 * (100663302 * ((d : ℝ) / (N * ell)))) ^ 2 := by
            exact pow_le_pow_left₀ (mul_nonneg (by norm_num) hins0)
              (mul_le_mul_of_nonneg_left hbias_inside (by norm_num)) 2
          _ = 40532401478172816 * ((d : ℝ) / (N * ell)) ^ 2 := by ring
      have hN₀m : N₀ ≤ m := by
        rw [hN₀, hm]
        linarith
      have hB1 : 1 ≤ B := by rw [hB]; nlinarith
      have hBterms : B ^ 2 / N₀ ^ 2 + B / (m * N₀) ≤
          4718592 * ell ^ 2 / N ^ 2 := by
        have hden : N₀ ^ 2 ≤ m * N₀ := by
          rw [sq]
          exact mul_le_mul_of_nonneg_right hN₀m hN₀pos.le
        have hsecond : B / (m * N₀) ≤ B ^ 2 / N₀ ^ 2 := by
          calc
            B / (m * N₀) ≤ B / N₀ ^ 2 :=
              div_le_div_of_nonneg_left (zero_le_one.trans hB1) (sq_pos_of_pos hN₀pos) hden
            _ ≤ B ^ 2 / N₀ ^ 2 :=
              div_le_div_of_nonneg_right (by nlinarith [sq_nonneg (B - 1)])
                (sq_nonneg N₀)
        calc
          B ^ 2 / N₀ ^ 2 + B / (m * N₀) ≤ 2 * (B ^ 2 / N₀ ^ 2) := by linarith
          _ = 4718592 * ell ^ 2 / N ^ 2 := by rw [hB, hN₀]; field_simp; ring
      have hscale : (d : ℝ) * (Real.exp (ell / 8) + 1) * ell ^ 2 / N ^ 2 ≤
          262144 * ((d : ℝ) / (N * ell)) ^ 2 := by
        calc
          (d : ℝ) * (Real.exp (ell / 8) + 1) * ell ^ 2 / N ^ 2 =
              (d : ℝ) * ((Real.exp (ell / 8) + 1) * ell ^ 4) /
                (N ^ 2 * ell ^ 2) := by field_simp
          _ ≤ (d : ℝ) * (262144 * d) / (N ^ 2 * ell ^ 2) := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hgrowth hdR.le) (by positivity)
          _ = 262144 * ((d : ℝ) / (N * ell)) ^ 2 := by field_simp
      have hcomplex :
          64 * (d : ℝ) * (Real.exp (ell / 8) + 1) *
              (B ^ 2 / N₀ ^ 2 + B / (m * N₀)) ≤
            79164837199872 * ((d : ℝ) / (N * ell)) ^ 2 := by
        calc
          64 * (d : ℝ) * (Real.exp (ell / 8) + 1) *
              (B ^ 2 / N₀ ^ 2 + B / (m * N₀)) ≤
              64 * (d : ℝ) * (Real.exp (ell / 8) + 1) *
                (4718592 * ell ^ 2 / N ^ 2) :=
            mul_le_mul_of_nonneg_left hBterms (by positivity)
          _ = 301989888 *
              ((d : ℝ) * (Real.exp (ell / 8) + 1) * ell ^ 2 / N ^ 2) := by ring
          _ ≤ 301989888 * (262144 * ((d : ℝ) / (N * ell)) ^ 2) :=
            mul_le_mul_of_nonneg_left hscale (by norm_num)
          _ = 79164837199872 * ((d : ℝ) / (N * ell)) ^ 2 := by ring
      have hbase : 8 * (4 / N₀ + 1 / m) ≤ 240 * N⁻¹ := by
        have hfour : 4 / N₀ = 24 * N⁻¹ := by
          rw [show 4 / N₀ = 4 * (1 / N₀) by ring, hN₀inv]
          ring
        rw [hfour]
        nlinarith
      have hinv1 : N⁻¹ ≤ 1 := (inv_le_one₀ hNpos).2 hN1.le
      have hmInv6 : 1 / m ≤ 6 := hminv.trans (by nlinarith)
      have hvtail : 32 * Real.exp (-32 * ell) * (1 + 1 / m) ≤
          224 * N⁻¹ := by
        calc
          32 * Real.exp (-32 * ell) * (1 + 1 / m) ≤
              32 * N⁻¹ * 7 :=
            mul_le_mul (mul_le_mul_of_nonneg_left hexp32 (by norm_num))
              (by linarith) (by positivity) (by positivity)
          _ = 224 * N⁻¹ := by ring
      refine min_four_le_const_min_one ?_ hR0 (by norm_num : (4 : ℝ) ≤ 10 ^ 30)
      have htail' : 4 * Real.exp (-(n : ℝ) * gamma) ≤ 32 * N⁻¹ := by
        dsimp [gamma]
        nlinarith
      calc
        (2 * (4 * (d : ℝ) * B / (N₀ * (k : ℝ) ^ 2) +
              3 * Real.exp (-16 * ell))) ^ 2 +
            (8 * (4 / N₀ + 1 / m) +
              64 * (d : ℝ) * (Real.exp (ell / 8) + 1) *
                (B ^ 2 / N₀ ^ 2 + B / (m * N₀)) +
              32 * Real.exp (-32 * ell) * (1 + 1 / m)) +
            4 * Real.exp (-(n : ℝ) * gamma) ≤
            (40532401478172816 + 79164837199872) *
                ((d : ℝ) / (N * ell)) ^ 2 + 496 * N⁻¹ := by
          linarith
        _ ≤ 10 ^ 30 * (N⁻¹ + ((d : ℝ) / (N * ell)) ^ 2) := by
          nlinarith [inv_nonneg.mpr hNpos.le,
            sq_nonneg ((d : ℝ) / (N * ell))]
    · rw [if_pos hbranch]
      have hfrac0 : 0 ≤ 8 * (d : ℝ) / (Real.exp 1 * N₀) := by positivity
      have hfrac : 8 * (d : ℝ) / (Real.exp 1 * N₀) ≤
          48 * (d : ℝ) / N := by
        calc
          8 * (d : ℝ) / (Real.exp 1 * N₀) ≤ 8 * (d : ℝ) / N₀ := by
            apply (div_le_div_iff₀ (mul_pos (Real.exp_pos 1) hN₀pos) hN₀pos).2
            have he := Real.one_le_exp (show (0 : ℝ) ≤ 1 by norm_num)
            nlinarith [mul_nonneg (show (0 : ℝ) ≤ 8 * d by positivity)
              (sub_nonneg.mpr he)]
          _ = 48 * (d : ℝ) / N := by rw [hN₀]; field_simp; norm_num
      have hfrac_sq : (8 * (d : ℝ) / (Real.exp 1 * N₀)) ^ 2 ≤
          2304 * ((d : ℝ) / N) ^ 2 := by
        have := pow_le_pow_left₀ hfrac0 hfrac 2
        calc
          (8 * (d : ℝ) / (Real.exp 1 * N₀)) ^ 2 ≤
              (48 * (d : ℝ) / N) ^ 2 := this
          _ = 2304 * ((d : ℝ) / N) ^ 2 := by ring
      have hnbranch : ell < 128 ∨ (d : ℝ) < Real.sqrt N := by
        simp only [needleBranch, not_and_or, not_le] at hbranch
        exact hbranch
      have hdratio : ((d : ℝ) / N) ^ 2 ≤
          N⁻¹ + 16384 * ((d : ℝ) / (N * ell)) ^ 2 := by
        rcases hnbranch with hell128 | hdsqrt
        · have heq : (d : ℝ) / N = ell * ((d : ℝ) / (N * ell)) := by
            field_simp
          rw [heq]
          have hs := sq_nonneg ((d : ℝ) / (N * ell))
          have hellsq : ell ^ 2 ≤ 16384 := by nlinarith [sq_nonneg (128 - ell)]
          calc
            (ell * ((d : ℝ) / (N * ell))) ^ 2 =
                ell ^ 2 * ((d : ℝ) / (N * ell)) ^ 2 := by ring
            _ ≤ 16384 * ((d : ℝ) / (N * ell)) ^ 2 :=
              mul_le_mul_of_nonneg_right hellsq hs
            _ ≤ N⁻¹ + 16384 * ((d : ℝ) / (N * ell)) ^ 2 :=
              le_add_of_nonneg_left (inv_nonneg.mpr hNpos.le)
        · have hsqrt : (Real.sqrt N) ^ 2 = N := Real.sq_sqrt hNpos.le
          have hdsq : (d : ℝ) ^ 2 ≤ N := by
            nlinarith [sq_nonneg (Real.sqrt N - d)]
          have hratioN : ((d : ℝ) / N) ^ 2 ≤ N⁻¹ := by
            calc
              ((d : ℝ) / N) ^ 2 = (d : ℝ) ^ 2 / N ^ 2 := by ring
              _ ≤ N / N ^ 2 := div_le_div_of_nonneg_right hdsq (sq_nonneg N)
              _ = N⁻¹ := by field_simp
          exact hratioN.trans (le_add_of_nonneg_right (by positivity))
      have hvar : 4 * (4 / N₀ + 1 / m) ≤ 120 * N⁻¹ := by
        have hfour : 4 / N₀ = 24 * N⁻¹ := by
          rw [show 4 / N₀ = 4 * (1 / N₀) by ring, hN₀inv]
          ring
        rw [hfour]
        nlinarith
      refine min_four_le_const_min_one ?_ hR0 (by norm_num : (4 : ℝ) ≤ 10 ^ 30)
      have hfracR := mul_le_mul_of_nonneg_left hdratio (by norm_num : (0 : ℝ) ≤ 2304)
      have htail' : 4 * Real.exp (-(n : ℝ) * gamma) ≤ 32 * N⁻¹ := by
        dsimp [gamma]
        nlinarith
      calc
        (8 * (d : ℝ) / (Real.exp 1 * N₀)) ^ 2 +
            4 * (4 / N₀ + 1 / m) + 4 * Real.exp (-(n : ℝ) * gamma) ≤
            2304 * ((d : ℝ) / N) ^ 2 + 120 * N⁻¹ + 32 * N⁻¹ := by
          linarith
        _ ≤ 10 ^ 30 * (N⁻¹ + ((d : ℝ) / (N * ell)) ^ 2) := by
          nlinarith [inv_nonneg.mpr hNpos.le,
            sq_nonneg ((d : ℝ) / (N * ell))]

end CausalSmith.Stat.MarRareqLogfrontier
