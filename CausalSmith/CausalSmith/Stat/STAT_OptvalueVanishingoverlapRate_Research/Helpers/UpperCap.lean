module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperRaoBlackwell
public import Causalean.Stat.Concentration.Poisson.UpperTail
public import Mathlib.Analysis.SpecialFunctions.Exp

/-! # Restoring the Poisson cap

Roadmap equations (35)–(36) compare coupled unit-range scalar statistics,
transfer the quarter-mean Poisson tail, and absorb its penalty into the
observable rate. These estimates do not impose a relation between log n and d.
-/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory ProbabilityTheory
open scoped NNReal


-- @node: logAlphabet_le_card
/-- The alphabet logarithm is bounded by the alphabet size. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hd), the [stated conclusion](goal) holds. -/
lemma logAlphabet_le_card {d : ℕ} (hd : 1 ≤ d) : logAlphabet d ≤ d := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hlog := Real.log_le_sub_one_of_pos hd0
  unfold logAlphabet
  rw [Real.log_mul (Real.exp_ne_zero _) hd0.ne', Real.log_exp]
  linarith


-- @node: capExponential_le_inverse_sample
/-- The cap's exponential penalty is at most twice the inverse sample size. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hn), the [stated conclusion](goal) holds. -/
lemma capExponential_le_inverse_sample {n : ℕ} (hn : 1 ≤ n) :
    Real.exp (-(n : ℝ) / 2) ≤ 2 / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h := Real.mul_exp_neg_le_exp_neg_one ((n : ℝ) / 2)
  have he : Real.exp (-1) ≤ (1 : ℝ) := by
    exact Real.exp_le_one_iff.mpr (by norm_num)
  apply (le_div_iff₀ hn0).2
  have h' : (n : ℝ) / 2 * Real.exp (-(n : ℝ) / 2) ≤ 1 := by
    simpa only [neg_div] using h.trans he
  nlinarith


-- @node: capExponential_le_observable_rate
/-- Equation (36): the cap penalty has the unsaturated observable rate scale. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hn,hd,hε,hε1), the [stated conclusion](goal) holds. -/
lemma capExponential_le_observable_rate {n d : ℕ} {ε : ℝ}
    (hn : 1 ≤ n) (hd : 2 ≤ d) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    Real.exp (-(n : ℝ) / 2) ≤
      2 * ((d : ℝ) / ((n : ℝ) * ε * logAlphabet d)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hL := logAlphabet_pos (by omega : 1 ≤ d)
  have hLd := logAlphabet_le_card (by omega : 1 ≤ d)
  have hεL : ε * logAlphabet d ≤ d := by nlinarith
  have hinv : 1 / (n : ℝ) ≤ (d : ℝ) / ((n : ℝ) * ε * logAlphabet d) := by
    apply (div_le_div_iff₀ hn0 (by positivity)).2
    nlinarith
  apply (capExponential_le_inverse_sample hn).trans
  calc
    2 / (n : ℝ) = 2 * (1 / (n : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hinv (by norm_num)


-- @node: quarterPoisson_overflow_prob_le
/-- Equation (35) in real probability for any count with the quarter-mean Poisson law. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hM), the [stated conclusion](goal) holds. -/
lemma quarterPoisson_overflow_prob_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (M : Ω → ℕ)
    (hM : HasLaw M (poissonMeasure ((n : ℝ≥0) / 4)) μ) :
    μ.real {ω | n < M ω} ≤ Real.exp (-(n : ℝ) / 2) := by
  have hs : MeasurableSet {w : ℕ | n < w} := measurableSet_Ioi
  rw [hM.measureReal_eq hs]
  exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _)
    (Real.exp_nonneg _)).mp
      (Causalean.Stat.Concentration.Poisson.poisson_quarter_mean_cap_tail n)


-- @node: coupled_cap_sqRisk_le
/-- Coupled unit-range statistics agreeing below the cap differ in risk by at most one unit of loss times the overflow probability. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hM,ht,hcap,hagree,hcapInt,hinfInt), the [stated conclusion](goal) holds. -/
lemma coupled_cap_sqRisk_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (M : Ω → ℕ)
    (hM : HasLaw M (poissonMeasure ((n : ℝ≥0) / 4)) μ)
    (Vcap Vinf : Ω → ℝ) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (hcap : ∀ ω, 0 ≤ Vcap ω ∧ Vcap ω ≤ 1)
    (hagree : ∀ ω, M ω ≤ n → Vcap ω = Vinf ω)
    (hcapInt : Integrable (fun ω => (Vcap ω - t) ^ 2) μ)
    (hinfInt : Integrable (fun ω => (Vinf ω - t) ^ 2) μ) :
    Causalean.Stat.sqRisk μ Vcap t ≤
      Causalean.Stat.sqRisk μ Vinf t + Real.exp (-(n : ℝ) / 2) := by
  let s : Set Ω := {ω | n < M ω}
  have hs : NullMeasurableSet s μ :=
    hM.aemeasurable.nullMeasurableSet_preimage
      (show MeasurableSet {w : ℕ | n < w} from measurableSet_Ioi)
  have hi : Integrable (s.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator₀ hs
  have hp (ω : Ω) : (Vcap ω - t) ^ 2 ≤
      (Vinf ω - t) ^ 2 + s.indicator (fun _ => (1 : ℝ)) ω := by
    by_cases h : M ω ≤ n
    · rw [hagree ω h]
      simp [s, Nat.not_lt.mpr h]
    · have hv := hcap ω
      have hb : |Vcap ω - t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.2], by linarith [ht.1]⟩
      have hb₂ : (Vcap ω - t) ^ 2 ≤ 1 := by
        simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg _) hb 2
      rw [Set.indicator_of_mem (show ω ∈ s from Nat.lt_of_not_ge h)]
      linarith [sq_nonneg (Vinf ω - t)]
  have hr := integral_mono hcapInt (hinfInt.add hi) hp
  simp only [Pi.add_apply] at hr
  rw [integral_add hinfInt hi, integral_indicator₀ hs, setIntegral_const] at hr
  simp only [smul_eq_mul, mul_one] at hr
  exact hr.trans (add_le_add_right (quarterPoisson_overflow_prob_le μ n M hM) _)


-- @node: coupled_cap_observable_rate_le
/-- Restoring the cap converts the uncapped m=n/8 risk to the fixed-n scale, with an explicit additive universal constant for overflow. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hn,hd,hε,hε1,hM,ht,hcap,hagree,hcapInt,hinfInt,huncapped), the [stated conclusion](goal) holds. -/
lemma coupled_cap_observable_rate_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n d : ℕ} {ε : ℝ}
    (hn : 1 ≤ n) (hd : 2 ≤ d) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (M : Ω → ℕ) (hM : HasLaw M (poissonMeasure ((n : ℝ≥0) / 4)) μ)
    (Vcap Vinf : Ω → ℝ) (t C : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (hcap : ∀ ω, 0 ≤ Vcap ω ∧ Vcap ω ≤ 1)
    (hagree : ∀ ω, M ω ≤ n → Vcap ω = Vinf ω)
    (hcapInt : Integrable (fun ω => (Vcap ω - t) ^ 2) μ)
    (hinfInt : Integrable (fun ω => (Vinf ω - t) ^ 2) μ)
    (huncapped : Causalean.Stat.sqRisk μ Vinf t ≤
      C * ((d : ℝ) / (((n : ℝ) / 8) * ε * logAlphabet d))) :
    Causalean.Stat.sqRisk μ Vcap t ≤
      (8 * C + 2) * ((d : ℝ) / ((n : ℝ) * ε * logAlphabet d)) := by
  have hr := coupled_cap_sqRisk_le μ n M hM Vcap Vinf t ht hcap hagree hcapInt hinfInt
  have he := capExponential_le_observable_rate hn hd hε hε1
  have hid : (d : ℝ) / (((n : ℝ) / 8) * ε * logAlphabet d) =
      8 * ((d : ℝ) / ((n : ℝ) * ε * logAlphabet d)) := by ring
  rw [hid] at huncapped
  nlinarith

end CausalSmith.Stat.OptvalueVanishingoverlapRate
