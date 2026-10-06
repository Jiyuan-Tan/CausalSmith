module
public import Causalean.Stat.CLT.BerryEsseen.PrawitzCompactKernelCells
public import Causalean.Stat.CLT.BerryEsseen.PrawitzCutoffRationalCertificate
public import Causalean.Stat.CLT.BerryEsseen.PrawitzRescaledCells

/-! # Analytic adapters for the rational high-frequency cells

The lower-half Taylor kernel and upper-half reflected polynomial use the
actual real pi here. The first adapter compares their squared enclosures
with the rational pi interval; the second compares the rescaled cubic
exponential with the reciprocal Taylor entry. These are pointwise scalar
inequalities, not integral allocations. They import no open budget or real
cutoff adapter. At the outer kernel endpoint the later integral comparison
must still be made only almost everywhere, as in PrawitzRescaledCells.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open Finset

/-- On [every positive high grid cell](hyp:i,hi), [the squared analytic
kernel enclosure with real pi is bounded by the rational pi enclosure
used by the kernel magnitude certificate](goal). -/
theorem prawitz_high_real_kernel_square_enclosure
    (i : ℕ) (hi : i ∈ Ico 1 1000) :
    let a := (i : ℝ) / 1000
    let b := ((i + 1 : ℕ) : ℝ) / 1000
    let Q := if i < 500 then
      (1 - a) ^ 2 / 4 +
        (((1 - a) * (1 - (Real.pi * a) ^ 2 / 2 + (Real.pi * b) ^ 4 / 24) /
          (Real.pi * a * (1 - (Real.pi * b) ^ 2 / 6)) + 1 / Real.pi) / 2) ^ 2
      else (1 - a) ^ 2 / 4 + Real.pi ^ 2 * (1 - a) ^ 4 / 16
    Q ≤ (prawitzRationalKernelSq i : ℝ) := by
  /- Round 8 lowest analytic kernel layer. Let p=314159/100000 and
  q=314160/100000; use the CLOSED rational pi bounds. If i<500,
  0<a<=b<=1/2. Compare 1-(pi*a)²/2+(pi*b)^4/24 with
  1-(p*a)²/2+(q*b)^4/24, and pi*a*(1-(pi*b)²/6) with
  p*a*(1-(q*b)²/6)>0. The denominator factor is positive since
  q<4 and b<=1/2. Establish numerator nonnegativity before division
  and squaring (the proved cosine quartic estimate at pi*a supplies
  it, since b>=a and cos(pi*a)>=0). Use 1/pi<=1/p. In the upper
  branch only pi²<=q² and (1-a)^4>=0 are needed. After push_cast,
  the result is exactly prawitzRationalKernelSq. This is NOT a bound
  on the assigned kernel value at u=1, which remains excluded a.e. -/
  dsimp only
  let a : ℝ := i / 1000
  let b : ℝ := (i + 1 : ℕ) / 1000
  let p : ℝ := 314159 / 100000
  let q : ℝ := 314160 / 100000
  have hpi := prawitz_rational_pi_bounds
  have hp : 0 < p := by norm_num [p]
  have hq : q < 4 := by norm_num [q]
  have hpaPi : p ≤ Real.pi := hpi.1
  have hpiq : Real.pi ≤ q := hpi.2
  have ha : 0 < a := by
    dsimp [a]
    exact div_pos (by exact_mod_cast (mem_Ico.mp hi).1) (by norm_num)
  have hab : a ≤ b := by dsimp [a, b]; push_cast; linarith
  have haOne : 0 ≤ 1 - a := by
    have h := (mem_Ico.mp hi).2
    have h' : (i : ℝ) < 1000 := by exact_mod_cast h
    dsimp [a]
    linarith
  unfold prawitzRationalKernelSq
  split_ifs with h
  · have hb : b ≤ 1 / 2 := by
      have h' : (i : ℝ) + 1 ≤ 500 := by exact_mod_cast (by omega : i + 1 ≤ 500)
      dsimp [b]
      push_cast
      linarith
    have hpb : 0 ≤ Real.pi * b := mul_nonneg Real.pi_pos.le (ha.le.trans hab)
    have hqb : 0 ≤ q * b := mul_nonneg (by norm_num [q]) (ha.le.trans hab)
    have hqbTwo : q * b < 2 := by nlinarith [ha.le.trans hab]
    have hqbSq : (q * b) ^ 2 < 4 := by nlinarith
    have hfactor : 0 < 1 - (q * b) ^ 2 / 6 := by
      apply sub_pos.mpr
      exact (div_lt_one (by norm_num)).2 (hqbSq.trans (by norm_num))
    have hpbqb : Real.pi * b ≤ q * b :=
      mul_le_mul_of_nonneg_right hpiq (ha.le.trans hab)
    have hsqb := pow_le_pow_left₀ hpb hpbqb 2
    have hfourb := pow_le_pow_left₀ hpb hpbqb 4
    have hsqa := pow_le_pow_left₀ (mul_nonneg hp.le ha.le)
      (mul_le_mul_of_nonneg_right hpaPi ha.le) 2
    let c := 1 - (Real.pi * a) ^ 2 / 2 + (Real.pi * b) ^ 4 / 24
    let C := 1 - (p * a) ^ 2 / 2 + (q * b) ^ 4 / 24
    let d := Real.pi * a * (1 - (Real.pi * b) ^ 2 / 6)
    let D := p * a * (1 - (q * b) ^ 2 / 6)
    have hc : 0 ≤ c := by
      have hcos : 0 ≤ Real.cos (Real.pi * a) :=
        Real.cos_nonneg_of_mem_Icc
          ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
      have ht := cos_le_quadratic_add_quartic (Real.pi * a)
      have hfour := pow_le_pow_left₀ (mul_nonneg Real.pi_pos.le ha.le)
        (mul_le_mul_of_nonneg_left hab Real.pi_pos.le) 4
      dsimp [c]
      linarith
    have hcC : c ≤ C :=
      add_le_add (sub_le_sub_left
        (div_le_div_of_nonneg_right hsqa (by norm_num)) 1)
        (div_le_div_of_nonneg_right hfourb (by norm_num))
    have hD : 0 < D := mul_pos (mul_pos hp ha) hfactor
    have hDd : D ≤ d := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right hpaPi ha.le)
        (sub_le_sub_left (div_le_div_of_nonneg_right hsqb (by norm_num)) 1)
        hfactor.le (mul_nonneg Real.pi_pos.le ha.le)
    have hfrac : (1 - a) * c / d ≤ (1 - a) * C / D := by
      calc
        _ ≤ (1 - a) * c / D :=
          div_le_div_of_nonneg_left (mul_nonneg haOne hc) hD hDd
        _ ≤ _ := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcC haOne) hD.le
    have hinv : 1 / Real.pi ≤ 1 / p := one_div_le_one_div_of_le hp hpaPi
    have hnonneg : 0 ≤ ((1 - a) * c / d + 1 / Real.pi) / 2 := by
      have hd := hD.trans_le hDd
      positivity
    have hsq := pow_le_pow_left₀ hnonneg
      (show ((1 - a) * c / d + 1 / Real.pi) / 2 ≤
        ((1 - a) * C / D + 1 / p) / 2 by linarith) 2
    push_cast
    simpa only [a, b, p, q, c, C, d, D, Nat.cast_add, Nat.cast_one] using
      add_le_add (le_refl ((1 - a) ^ 2 / 4)) hsq
  · have hsq := pow_le_pow_left₀ Real.pi_pos.le hpiq 2
    have hmul := mul_le_mul_of_nonneg_right hsq (pow_nonneg haOne 4)
    push_cast
    change (1 - a) ^ 2 / 4 + Real.pi ^ 2 * (1 - a) ^ 4 / 16 ≤
      (1 - a) ^ 2 / 4 + q ^ 2 * (1 - a) ^ 4 / 16
    exact add_le_add le_rfl (div_le_div_of_nonneg_right hmul (by norm_num))

/-- On [the j-th certified compact parameter cell and the i-th positive
high-frequency grid cell [i/1000, (i+1)/1000], for i from 1 to
999](hyp:j,i,hi), [the exponential of the rescaled cubic endpoint exponent
is at most the reciprocal of the rational Taylor polynomial evaluated at the
matching rational exponent from the high table](goal). -/
theorem prawitz_high_real_exponential_enclosure
    (j : Fin 270) (i : ℕ) (hi : i ∈ Ico 1 1000) :
    let s := (prawitzCompactRight j.val : ℝ)
    let a := (i : ℝ) / 1000
    let b := ((i + 1 : ℕ) : ℝ) / 1000
    let E := max ((-72 * a ^ 2 / 25 + 1728 * a ^ 3 / 625) / s ^ 2)
      ((-72 * b ^ 2 / 25 + 1728 * b ^ 3 / 625) / s ^ 2)
    let aq := (i : ℚ) / 1000
    let bq := ((i + 1 : ℕ) : ℚ) / 1000
    let e := min (72 * aq ^ 2 / 25 - 1728 * aq ^ 3 / 625)
      (72 * bq ^ 2 / 25 - 1728 * bq ^ 3 / 625) /
        (prawitzCompactRight j.val) ^ 2
    Real.exp E ≤ ((1 / prawitzTaylor16 e : ℚ) : ℝ) := by
  /- Round 8 independent exponent leaf. The CLOSED cutoff certificate
  gives s>0, and hi gives 0<=a<=b<=1. For z in [0,1],
  72*z²/25-1728*z³/625 = (72/625)*z²*(25-24*z)>=0.
  Thus e>=0; after casting, e=-E (min/max and division by s²>0).
  Apply prawitz_exp_neg_le_reciprocal_taylor16. This preserves the
  cubic damping rather than the rejected exp(-t²/50) majorant.
  Later assembly combines this and the kernel square adapter with
  the CLOSED square certificate to bound each existing rescaled
  cell integral by prawitzRationalHighCell, then outward rounds it. -/
  dsimp only
  let s := prawitzCompactRight j.val
  let a : ℚ := i / 1000
  let b : ℚ := (i + 1 : ℕ) / 1000
  let e := min (72 * a ^ 2 / 25 - 1728 * a ^ 3 / 625)
    (72 * b ^ 2 / 25 - 1728 * b ^ 3 / 625) / s ^ 2
  have hc := prawitz_compact_cutoff_rational_certificate j
  dsimp only at hc
  have hs : 0 < s := hc.1.trans hc.2.1
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hab : a ≤ b := by dsimp [a, b]; push_cast; linarith
  have hbOne : b ≤ 1 := by
    have h : (i + 1 : ℕ) ≤ 1000 := by have := (mem_Ico.mp hi).2; omega
    have h' : ((i + 1 : ℕ) : ℚ) ≤ 1000 := by exact_mod_cast h
    dsimp [b]
    linarith
  have damping : ∀ z : ℚ, 0 ≤ z → z ≤ 1 →
      0 ≤ 72 * z ^ 2 / 25 - 1728 * z ^ 3 / 625 := by
    intro z hz hzOne
    have h : 0 ≤ (72 / 625 : ℚ) * z ^ 2 * (25 - 24 * z) :=
      mul_nonneg (by positivity) (by linarith)
    nlinarith only [h]
  have he : 0 ≤ e := div_nonneg
    (le_min (damping a ha (hab.trans hbOne)) (damping b hb hbOne)) (sq_nonneg s)
  have hE : max ((-72 * (a : ℝ) ^ 2 / 25 + 1728 * (a : ℝ) ^ 3 / 625) /
      (s : ℝ) ^ 2)
      ((-72 * (b : ℝ) ^ 2 / 25 + 1728 * (b : ℝ) ^ 3 / 625) / (s : ℝ) ^ 2) =
      -(e : ℝ) := by
    dsimp [e]
    push_cast
    rw [← min_div_div_right (sq_nonneg (s : ℝ))]
    have hneg (z : ℝ) :
        -((72 * z ^ 2 / 25 - 1728 * z ^ 3 / 625) / (s : ℝ) ^ 2) =
        (-72 * z ^ 2 / 25 + 1728 * z ^ 3 / 625) / (s : ℝ) ^ 2 := by ring
    rw [neg_inf, hneg, hneg]
  have hbound := prawitz_exp_neg_le_reciprocal_taylor16 e he
  rw [← hE] at hbound
  simpa only [a, b, s, e, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hbound

end Causalean.Stat.CLT.BerryEsseen
