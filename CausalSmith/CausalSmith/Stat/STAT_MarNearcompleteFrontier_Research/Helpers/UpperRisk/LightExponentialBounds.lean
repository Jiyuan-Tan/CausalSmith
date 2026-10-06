module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.StreamBiasAlgebra
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.StreamLightSecondMoment
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.PilotTails

/-!
# Exponential bounds for the light correction

The numerical degree and threshold choices turn equation (8) into the
small-cell bound (9) and pilot-weighted large-cell decay (11).
-/

public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory

/-- Above the fallback cutoff, the degree is at most the logarithmic scale
 divided by sixty-four. Given [the specified input `n`](hyp:n), [the specified input `hL`](hyp:hL), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_polyDegree_log_upper
lemma upper_polyDegree_log_upper {n : ℕ} (hL : 128 ≤ ell n) :
    (polyDegree n : ℝ) ≤ ell n / 64 := by
  have h0 : 0 ≤ ell n / 64 := by linarith
  have hf := Nat.floor_le h0
  unfold polyDegree
  rw [Nat.cast_max]
  exact max_le (by norm_num; linarith) hf

/-- The logarithms of the two fixed numerical bases have simple rational
upper bounds. [the stated mathematical conclusion holds](goal). -/
-- @node: upper_log_bases_le
lemma upper_log_bases_le : Real.log 64 ≤ 6 ∧ Real.log 4 ≤ 2 := by
  have h2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have h64 : Real.log (64 : ℝ) = 6 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 6
    norm_num at h
    exact h
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 2
    norm_num at h
    exact h
  rw [h64, h4]
  constructor <;> linarith

/-- The exponential degree factor in equation (8) is at most exp(6k). Given [the specified input `k`](hyp:k), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_sixtyfour_pow_le_exp
lemma upper_sixtyfour_pow_le_exp (k : ℕ) :
    (64 : ℝ) ^ k ≤ Real.exp (6 * (k : ℝ)) := by
  have h64 : (64 : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log 64) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 64)]
  rw [h64]
  apply Real.exp_le_exp.mpr
  nlinarith [upper_log_bases_le.1, Nat.cast_nonneg (α := ℝ) k]

/-- In a small cell, the power-growth factor in equation (8) costs at most
exp(k); the numerical threshold is much larger than the degree. Given [the specified input `n`](hyp:n), [the specified input `hL`](hyp:hL), [the specified input `z`](hyp:z), [the specified input `hz`](hyp:hz), [the specified input `hzB`](hyp:hzB), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_small_light_growth_le
lemma upper_small_light_growth_le {n : ℕ} (hL : 128 ≤ ell n)
    {z : ℝ} (hz : 0 ≤ z) (hzB : z ≤ polyThreshold n) :
    max 1 (((z + (2 * polyDegree n : ℕ)) / polyThreshold n) ^
      (2 * polyDegree n)) ≤ Real.exp (polyDegree n : ℝ) := by
  have hk := upper_polyDegree_log_upper hL
  have hB : 0 < polyThreshold n := by unfold polyThreshold; linarith
  have hr0 : 0 ≤ (z + (2 * polyDegree n : ℕ)) / polyThreshold n := by positivity
  have hr : (z + (2 * polyDegree n : ℕ)) / polyThreshold n ≤ (1 / 2 : ℝ) + 1 := by
    apply (div_le_iff₀ hB).mpr
    push_cast
    unfold polyThreshold at hzB ⊢
    linarith
  have hre : (z + (2 * polyDegree n : ℕ)) / polyThreshold n ≤ Real.exp (1 / 2) :=
    hr.trans (Real.add_one_le_exp _)
  have hp := pow_le_pow_left₀ hr0 hre (2 * polyDegree n)
  rw [← Real.exp_nat_mul] at hp
  have he : ((2 * polyDegree n : ℕ) : ℝ) * (1 / 2 : ℝ) = (polyDegree n : ℝ) := by
    push_cast
    ring
  rw [he] at hp
  exact max_le (Real.one_le_exp (Nat.cast_nonneg _)) hp

/-- Equation (9), with universal constant one, for the actual fourth-stream
light correction. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hL`](hyp:hL), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the specified input `hzB`](hyp:hzB), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_streamH_small_second_moment_le
lemma upper_streamH_small_second_moment_le {n d : ℕ} (hL : 128 ≤ ell n)
    (P : FullLaw d) (x : Fin d) (a s : Bool)
    (hzB : streamZ n P x a s ≤ polyThreshold n) :
    (∫ streams, (streamH n d streams x a s) ^ 2 ∂fourStreamLaw n P) ≤
      Real.exp (ell n / 8) := by
  have hz : 0 ≤ streamZ n P x a s := by
    unfold streamZ
    exact mul_nonneg (by positivity) (arrivedCellMass_nonneg P x a s)
  have hg := upper_small_light_growth_le hL hz hzB
  have hk := upper_polyDegree_log_upper hL
  calc
    _ ≤ (64 : ℝ) ^ polyDegree n / 2 *
        max 1 (((streamZ n P x a s + (2 * polyDegree n : ℕ)) /
          polyThreshold n) ^ (2 * polyDegree n)) :=
      upper_streamH_second_moment_le P x a s
    _ ≤ (64 : ℝ) ^ polyDegree n * Real.exp (polyDegree n : ℝ) := by
      have hh := mul_le_mul_of_nonneg_left hg
        (show 0 ≤ (64 : ℝ) ^ polyDegree n / 2 by positivity)
      have he := Real.exp_pos (polyDegree n : ℝ)
      nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 64) (polyDegree n)]
    _ ≤ Real.exp (6 * (polyDegree n : ℝ)) * Real.exp (polyDegree n : ℝ) :=
      mul_le_mul_of_nonneg_right (upper_sixtyfour_pow_le_exp _) (Real.exp_pos _).le
    _ = Real.exp (7 * (polyDegree n : ℝ)) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (ell n / 8) := Real.exp_le_exp.mpr (by linarith)

/-- The large-cell polynomial growth is dominated by exp(z/8). This leaves
ample decay after multiplying by the pilot lower-tail probability. Given [the specified input `n`](hyp:n), [the specified input `hL`](hyp:hL), [the specified input `z`](hyp:z), [the specified input `hzB`](hyp:hzB), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_large_light_envelope_le
lemma upper_large_light_envelope_le {n : ℕ} (hL : 128 ≤ ell n)
    {z : ℝ} (hzB : polyThreshold n ≤ z) :
    (64 : ℝ) ^ polyDegree n *
      max 1 (((z + (2 * polyDegree n : ℕ)) / polyThreshold n) ^
        (2 * polyDegree n)) ≤ Real.exp (z / 8) := by
  let k : ℝ := polyDegree n
  let B : ℝ := polyThreshold n
  let r : ℝ := (z + 2 * k) / B
  have hk0 : 0 ≤ k := Nat.cast_nonneg _
  have hB : 0 < B := by dsimp [B]; unfold polyThreshold; linarith
  have hk : k ≤ B / 16384 := by
    have := upper_polyDegree_log_upper hL
    dsimp [k, B]
    unfold polyThreshold
    linarith
  have hz : 0 ≤ z := hB.le.trans hzB
  have h2k : 2 * k ≤ z := by dsimp [B] at hk; nlinarith
  have hr0 : 0 ≤ r := div_nonneg (by positivity) hB.le
  have hrB : r * B = z + 2 * k := by
    dsimp [r]
    exact div_mul_cancel₀ _ (ne_of_gt hB)
  have hkr : k * r ≤ z / 8192 := by
    have hm1 := mul_le_mul_of_nonneg_left h2k hk0
    have hm2 := mul_le_mul_of_nonneg_right hk hz
    have hprod : (k * r - z / 8192) * B ≤ 0 := by
      nlinarith [mul_nonneg hk0 (show 0 ≤ B from hB.le)]
    have : k * r - z / 8192 ≤ 0 := nonpos_of_mul_nonpos_left hprod hB
    linarith
  have hexponent : 6 * k + 2 * k * r ≤ z / 8 := by
    have hkz : k ≤ z / 16384 := hk.trans (div_le_div_of_nonneg_right hzB (by norm_num))
    linarith
  have hre : r ≤ Real.exp r := by linarith [Real.add_one_le_exp r]
  have hp := pow_le_pow_left₀ hr0 hre (2 * polyDegree n)
  rw [← Real.exp_nat_mul] at hp
  have heq : ((2 * polyDegree n : ℕ) : ℝ) * r = 2 * k * r := by dsimp [k]; push_cast; ring
  rw [heq] at hp
  have hmax : max 1 (r ^ (2 * polyDegree n)) ≤ Real.exp (2 * k * r) :=
    max_le (Real.one_le_exp (by positivity)) hp
  have hcast : ((2 * polyDegree n : ℕ) : ℝ) = 2 * k := by dsimp [k]; push_cast; rfl
  simp only [hcast]
  change (64 : ℝ) ^ polyDegree n * max 1 (r ^ (2 * polyDegree n)) ≤ _
  calc
    _ ≤ (64 : ℝ) ^ polyDegree n * Real.exp (2 * k * r) :=
      mul_le_mul_of_nonneg_left hmax (by positivity)
    _ ≤ Real.exp (6 * k) * Real.exp (2 * k * r) :=
      mul_le_mul_of_nonneg_right (upper_sixtyfour_pow_le_exp _) (Real.exp_pos _).le
    _ = Real.exp (6 * k + 2 * k * r) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (z / 8) := Real.exp_le_exp.mpr hexponent

/-- The actual light correction's second moment grows slowly enough beyond
the threshold to be suppressed by the pilot selection probability. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hL`](hyp:hL), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the specified input `hzB`](hyp:hzB), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_streamH_large_second_moment_le
lemma upper_streamH_large_second_moment_le {n d : ℕ} (hL : 128 ≤ ell n)
    (P : FullLaw d) (x : Fin d) (a s : Bool)
    (hzB : polyThreshold n ≤ streamZ n P x a s) :
    (∫ streams, (streamH n d streams x a s) ^ 2 ∂fourStreamLaw n P) ≤
      Real.exp (streamZ n P x a s / 8) := by
  apply (upper_streamH_second_moment_le P x a s).trans
  apply le_trans _ (upper_large_light_envelope_le hL hzB)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have hp : 0 ≤ (64 : ℝ) ^ polyDegree n := by positivity
  linarith

/-- Equation (11) for the actual light statistic: pilot weighting changes
large-cell polynomial growth into exponential decay. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `hL`](hyp:hL), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the specified input `hzB`](hyp:hzB), [the stated mathematical conclusion holds](goal). -/
-- @node: upper_streamH_pilot_large_second_moment_le
lemma upper_streamH_pilot_large_second_moment_le {n d : ℕ} (hL : 128 ≤ ell n)
    (P : FullLaw d) (x : Fin d) (a s : Bool)
    (hzB : polyThreshold n ≤ streamZ n P x a s) :
    streamPilotLightProb n P x a s *
      (∫ streams, (streamH n d streams x a s) ^ 2 ∂fourStreamLaw n P) ≤
      Real.exp (-streamZ n P x a s / 8) := by
  have hp0 := (upper_streamPilotLightProb_bounds (n := n) P x a s).1
  have hh := upper_streamH_large_second_moment_le hL P x a s hzB
  have htail := upper_stream_pilot_light_tail (n := n) P x a s
  have hB : 0 ≤ polyThreshold n := by unfold polyThreshold; linarith
  calc
    _ ≤ streamPilotLightProb n P x a s * Real.exp (streamZ n P x a s / 8) :=
      mul_le_mul_of_nonneg_left hh hp0
    _ ≤ Real.exp (polyThreshold n * Real.log 4 / 4 - 3 * streamZ n P x a s / 4) *
        Real.exp (streamZ n P x a s / 8) :=
      mul_le_mul_of_nonneg_right htail (Real.exp_pos _).le
    _ = Real.exp (polyThreshold n * Real.log 4 / 4 - 3 * streamZ n P x a s / 4 +
        streamZ n P x a s / 8) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (-streamZ n P x a s / 8) := by
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_left upper_log_bases_le.2 hB
      linarith

end CausalSmith.Stat.MarNearcompleteFrontier
