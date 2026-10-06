module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.LowerSparseRisk

/-!
# Universal sparse alphabet calibration

The even logarithmic degree from (32) makes the target concentration condition
(39) hold above a universal alphabet cutoff. This removes the numerical
concentration premise from the explicit packet Bayes lower bound.
-/

@[expose] public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory Filter
open Causalean.Stat.Minimax.MomentMatchedMixture
open Causalean.Stat.Minimax.FuzzyHypotheses
open scoped BigOperators Topology

-- @node: lowerLogDegree
/-- For [the displayed parameters](hyp:C,d), [lowerLogDegree](goal) is the object specified by this definition. -/
noncomputable def lowerLogDegree (C : ℝ) (d : ℕ) : ℕ :=
  2 * ⌈C * logAlphabet d / 2⌉₊

-- @node: lowerLogDegree_bounds
/-- Rounding the degree preserves its logarithmic lower bound and costs at most two logarithmic units, uniformly for every legal alphabet. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hC,hd), the [stated conclusion](goal) holds. -/
lemma lowerLogDegree_bounds {C : ℝ} (hC : 2 ≤ C) {d : ℕ} (hd : 2 ≤ d) :
    2 ≤ lowerLogDegree C d ∧
      C * logAlphabet d ≤ (lowerLogDegree C d : ℝ) ∧
      (lowerLogDegree C d : ℝ) ≤ (C + 2) * logAlphabet d := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hdpos : (0 : ℝ) < d := by linarith
  have hL : 1 ≤ logAlphabet d := by
    rw [logAlphabet, Real.log_mul (Real.exp_pos _).ne' hdpos.ne', Real.log_exp]
    linarith [Real.log_nonneg hdR]
  have hnonneg : 0 ≤ C * logAlphabet d / 2 := by positivity
  have hlo := Nat.le_ceil (C * logAlphabet d / 2)
  have hhi := Nat.ceil_lt_add_one hnonneg
  have hcast : (lowerLogDegree C d : ℝ) = 2 * (⌈C * logAlphabet d / 2⌉₊ : ℝ) := by
    simp [lowerLogDegree]
  have hdeg : (2 : ℝ) ≤ lowerLogDegree C d := by
    rw [hcast]
    nlinarith
  refine ⟨by exact_mod_cast hdeg, ?_, ?_⟩ <;> rw [hcast] <;> nlinarith

-- @node: logAlphabet_sq_div_tendsto_zero
/-- Logarithmic degree squared is negligible relative to alphabet size. In the econometric construction, no additional assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma logAlphabet_sq_div_tendsto_zero :
    Tendsto (fun d : ℕ => logAlphabet d ^ 2 / (d : ℝ)) atTop (𝓝 0) := by
  have ht := (Real.tendsto_pow_log_div_mul_add_atTop
    (Real.exp 1)⁻¹ 0 2 (inv_ne_zero (Real.exp_ne_zero 1))).comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop (Real.exp_pos 1))
  simpa only [Function.comp_def, logAlphabet, add_zero,
    ← mul_assoc, inv_mul_cancel₀ (Real.exp_ne_zero 1), one_mul] using ht

-- @node: sparse_packet_alphabet_cutoff
/-- A single alphabet cutoff enforces the target-deviation bound (39) for all endpoints and overlap floors in the theorem's range. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hcp,hC), the [stated conclusion](goal) holds. -/
lemma sparse_packet_alphabet_cutoff {cp C : ℝ} (hcp : 0 < cp) (hC : 2 ≤ C) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ d : ℕ, D ≤ d → ∀ M ε : ℝ,
      2 ≤ M → 0 ≤ ε → ε ≤ 1 / 2 →
      256 * (2 + 3 * ε ^ 2 * M) * (lowerLogDegree C d : ℝ) ^ 2 ≤
        cp ^ 2 * M * d := by
  have hδ : 0 < cp ^ 2 / (448 * (C + 2) ^ 2) := by positivity
  obtain ⟨D, hD⟩ := eventually_atTop.mp
    (logAlphabet_sq_div_tendsto_zero.eventually_lt_const hδ)
  refine ⟨max D 2, le_max_right _ _, ?_⟩
  intro d hd M ε hM hε hεhalf
  have hd2 : 2 ≤ d := (le_max_right _ _).trans hd
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hsmall := hD d ((le_max_left _ _).trans hd)
  have hL := (lowerLogDegree_bounds hC hd2).2.2
  have hLpos : 0 ≤ (C + 2) * logAlphabet d := by
    exact (Nat.cast_nonneg (lowerLogDegree C d)).trans hL
  have hsq := pow_le_pow_left₀ (Nat.cast_nonneg (lowerLogDegree C d)) hL 2
  have hbound : 448 * (lowerLogDegree C d : ℝ) ^ 2 ≤ cp ^ 2 * d := by
    have hscaled := (div_lt_div_iff₀ hdpos
      (by positivity : 0 < 448 * (C + 2) ^ 2)).mp hsmall
    rw [mul_pow] at hsq
    nlinarith
  have hεsq : ε ^ 2 ≤ 1 / 4 := by nlinarith
  have hfactor : 256 * (2 + 3 * ε ^ 2 * M) ≤ 448 * M := by
    have hm := mul_le_mul_of_nonneg_right hεsq (by linarith : 0 ≤ M)
    nlinarith
  calc
    _ ≤ (448 * M) * (lowerLogDegree C d : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hfactor (sq_nonneg _)
    _ = M * (448 * (lowerLogDegree C d : ℝ) ^ 2) := by ring
    _ ≤ M * (cp ^ 2 * d) := mul_le_mul_of_nonneg_left hbound (by linarith)
    _ = _ := by ring

/-- Above a universal alphabet cutoff the explicit packet yields the sparse Bayes lower order without any assumed concentration or testing bound. All numerical side conditions are derived from the logarithmic degree. In the econometric construction, no additional assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma sparse_packet_bayesRisk_lower_largeAlphabet :
    ∃ (c η C : ℝ) (A D : ℕ),
      0 < c ∧ 0 < η ∧ 2 ≤ C ∧ 1 ≤ A ∧ 2 ≤ D ∧
      ∀ (n d : ℕ) (ε M B : ℝ),
        1 ≤ n → D ≤ d → 0 < ε → ε ≤ 1 / 2 →
        ∀ hM : 2 ≤ M, M ≤ (lowerLogDegree C d : ℝ) ^ 2 → 2 < B →
        M ≤ η * d * lowerLogDegree C d / (B * n * ε) →
        ∃ (P : ConstrainedPriorPair (lowerLogDegree C d) M),
          ∃ hdom : CommonAtomDomain
            (packetPositive A (lowerLogDegree C d) M)
            (packetNegative A (lowerLogDegree C d) M),
            commonAtomCompletion
              (packetPositive A (lowerLogDegree C d) M)
              (packetNegative A (lowerLogDegree C d) M) hdom = (P.ν₀, P.ν₁) ∧
            ∀ est : (Fin d → (Fin 4 → ℕ)) → ℝ, Measurable est →
              ENNReal.ofReal (c * M / (lowerLogDegree C d : ℝ) ^ 2) ≤
                max
                  (bayesSquaredRisk
                    (productPrior d (Measure.map (fun z => z - sparseReference (_hMpaper := hM) M) P.ν₀))
                    (sparseProductPoissonKernel (hMpaper := hM) B n d ε M) (sparsePriorTarget (hMpaper := hM) d ε M) est)
                  (bayesSquaredRisk
                    (productPrior d (Measure.map (fun z => z - sparseReference (_hMpaper := hM) M) P.ν₁))
                    (sparseProductPoissonKernel (hMpaper := hM) B n d ε M) (sparsePriorTarget (hMpaper := hM) d ε M) est) := by
  obtain ⟨c, cp, η, C₀, A, hc, hcp, hη, _, hA, hrisk⟩ := sparse_packet_bayesRisk_lower
  let C := max C₀ 2
  have hC : 2 ≤ C := le_max_right _ _
  obtain ⟨D, hD, hcut⟩ := sparse_packet_alphabet_cutoff hcp hC
  refine ⟨c, η, C, A, D, hc, hη, hC, hA, hD, ?_⟩
  intro n d ε M B hn hd hε hεhalf hM hMhi hB hband
  have hd2 : 2 ≤ d := hD.trans hd
  obtain ⟨hK, hlog, _⟩ := lowerLogDegree_bounds hC hd2
  have hL : 0 ≤ logAlphabet d := by
    rw [logAlphabet, Real.log_mul (Real.exp_pos _).ne'
      (show (d : ℝ) ≠ 0 by exact_mod_cast (by omega : d ≠ 0)), Real.log_exp]
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
    linarith [Real.log_nonneg hdR]
  exact hrisk (lowerLogDegree C d) n d ε M B hK hn hd2 hε hεhalf hM hMhi hB
    ((mul_le_mul_of_nonneg_right (le_max_left C₀ 2) hL).trans hlog)
    hband (hcut d hd M ε hM hε.le hεhalf)

end CausalSmith.Stat.OptvalueVanishingoverlapRate
