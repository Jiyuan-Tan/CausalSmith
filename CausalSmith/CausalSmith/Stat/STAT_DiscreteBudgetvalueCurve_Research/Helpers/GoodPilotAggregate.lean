module
public import CausalSmith.Stat.STAT_DiscreteBudgetvalueCurve_Research.Helpers.GoodPilotCellOuterMoment

/-! Identification and simplification of the aggregate good-pilot path risk. -/

@[expose] public section

namespace CausalSmith.Stat.DiscreteBudgetvalueCurve

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open Causalean.Stat.Concentration.BoundedVariation

/-- The paper's scalar centered good-pilot risk is exactly the squared norm
risk of the centered sum of its continuous cell paths. With [the specified inputs and conditions](hyp:n,d,epsilon,he,he',hn,hd,P), [the stated relationship holds](goal). The argument assumes [the probability-law premise](hyp:hprob). -/
-- @node: centeredIdealGoodPilotErrorRisk_eq_path_integral
lemma centeredIdealGoodPilotErrorRisk_eq_path_integral
    {n d : ℕ} (epsilon : ℝ) (he : 0 < epsilon) (he' : epsilon < 1 / 2)
    (hn : 1 ≤ n) (hd : 16 ≤ d) (P : DiscreteLaw d)
    (hprob : IsProbabilityMeasure (idealCountLaw (n := n) P)) :
    let hcont : ∀ j counts, Continuous (fun lambda : Time =>
      idealPilotErrorCell (n := n) epsilon lambda P counts j true) :=
      fun j counts => idealPilotErrorCell_continuous_time_of_pos he hn
        (show 1 ≤ d by omega) P counts j true
    centeredIdealPilotErrorRisk (n := n) epsilon P true =
      ∫ counts, ‖∑ j, (idealPilotErrorCellPath epsilon P counts j true
          (hcont j counts) -
        ∫ x, idealPilotErrorCellPath epsilon P x j true (hcont j x)
          ∂idealCountLaw (n := n) P)‖ ^ 2
        ∂idealCountLaw (n := n) P := by
  classical
  dsimp only
  letI : IsProbabilityMeasure (idealCountLaw (n := n) P) := hprob
  let hcont : ∀ j counts, Continuous (fun lambda : Time =>
      idealPilotErrorCell (n := n) epsilon lambda P counts j true) :=
    fun j counts => idealPilotErrorCell_continuous_time_of_pos he hn
      (show 1 ≤ d by omega) P counts j true
  let X : Fin d → ((Fin d → Cell → ℕ) × (Fin d → Cell → ℕ)) → Path :=
    fun j counts => idealPilotErrorCellPath epsilon P counts j true (hcont j counts)
  have hXint (j : Fin d) : Integrable (X j) (idealCountLaw (n := n) P) := by
    simpa [X, hcont] using idealGoodPilotCellPath_integrable
      epsilon he he' hn hd P hprob j
  have hmean (lambda : Time) :
      idealPilotErrorMean (n := n) epsilon lambda P true =
        ∑ j : Fin d, ∫ x, X j x lambda ∂idealCountLaw (n := n) P := by
    unfold idealPilotErrorMean
    simp_rw [idealPilotErrorPart_eq_sum_cells]
    rw [integral_finsetSum]
    · simp [X, idealPilotErrorCellPath]
    · intro j _
      simpa [X, idealPilotErrorCellPath] using
        (ContinuousMap.evalCLM ℝ lambda).integrable_comp (hXint j)
  have heval (j : Fin d) (lambda : Time) :
      (∫ x, X j x ∂idealCountLaw (n := n) P) lambda =
        ∫ x, X j x lambda ∂idealCountLaw (n := n) P := by
    simpa using
      ((ContinuousMap.evalCLM ℝ lambda).integral_comp_comm (hXint j)).symm
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun counts => by
    let Z : Path := ∑ j, (X j counts -
      ∫ x, X j x ∂idealCountLaw (n := n) P)
    have hpoint (lambda : Time) : Z lambda =
        idealPilotErrorPart (n := n) epsilon lambda P counts true -
          idealPilotErrorMean (n := n) epsilon lambda P true := by
      dsimp [Z]
      simp_rw [ContinuousMap.sum_apply, ContinuousMap.sub_apply, heval]
      rw [idealPilotErrorPart_eq_sum_cells, hmean]
      rw [Finset.sum_sub_distrib]
      simp only [X, idealPilotErrorCellPath]
      congr 1
    have hg : Continuous (fun lambda : Time =>
        idealPilotErrorPart (n := n) epsilon lambda P counts true -
          idealPilotErrorMean (n := n) epsilon lambda P true) := by
      convert Z.continuous using 1
      funext lambda
      exact (hpoint lambda).symm
    change (sSup ((fun lambda : ℝ =>
      |idealPilotErrorPart (n := n) epsilon lambda P counts true -
        idealPilotErrorMean (n := n) epsilon lambda P true|) '' Set.Icc 0 1)) ^ 2 =
      ‖Z‖ ^ 2
    rw [← path_norm_eq_sSup_abs_restrict
      (fun lambda => idealPilotErrorPart (n := n) epsilon lambda P counts true -
        idealPilotErrorMean (n := n) epsilon lambda P true) hg]
    congr 2
    apply ContinuousMap.ext
    intro lambda
    exact (hpoint lambda).symm

/-- The centered aggregate good-pilot error is continuous in the shadow price. With [the specified inputs and conditions](hyp:n,d,epsilon,he,he',hn,hd,P), [the stated relationship holds](goal). The argument assumes [the probability-law premise](hyp:hprob). -/
lemma centeredIdealGoodPilotError_continuous
    {n d : ℕ} (epsilon : ℝ) (he : 0 < epsilon) (he' : epsilon < 1 / 2)
    (hn : 1 ≤ n) (hd : 16 ≤ d) (P : DiscreteLaw d)
    (hprob : IsProbabilityMeasure (idealCountLaw (n := n) P))
    (counts : (Fin d → Cell → ℕ) × (Fin d → Cell → ℕ)) :
    Continuous (fun lambda : Time =>
      idealPilotErrorPart (n := n) epsilon lambda P counts true -
        idealPilotErrorMean (n := n) epsilon lambda P true) := by
  classical
  let hcont : ∀ j counts, Continuous (fun lambda : Time =>
      idealPilotErrorCell (n := n) epsilon lambda P counts j true) :=
    fun j counts => idealPilotErrorCell_continuous_time_of_pos he hn
      (show 1 ≤ d by omega) P counts j true
  let X : Fin d → ((Fin d → Cell → ℕ) × (Fin d → Cell → ℕ)) → Path :=
    fun j x => idealPilotErrorCellPath epsilon P x j true (hcont j x)
  have hXint (j : Fin d) : Integrable (X j) (idealCountLaw (n := n) P) := by
    simpa [X, hcont] using idealGoodPilotCellPath_integrable
      epsilon he he' hn hd P hprob j
  let Y : Path := ∑ j, X j counts
  let M : Path := ∑ j, ∫ x, X j x ∂idealCountLaw (n := n) P
  apply (Y - M).continuous.congr
  intro lambda
  have heval (j : Fin d) :
      (∫ x, X j x ∂idealCountLaw (n := n) P) lambda =
        ∫ x, X j x lambda ∂idealCountLaw (n := n) P := by
    simpa using
      ((ContinuousMap.evalCLM ℝ lambda).integral_comp_comm (hXint j)).symm
  simp only [Y, M, ContinuousMap.sub_apply, ContinuousMap.sum_apply]
  simp_rw [heval]
  rw [idealPilotErrorPart_eq_sum_cells]
  unfold idealPilotErrorMean
  simp_rw [idealPilotErrorPart_eq_sum_cells]
  rw [integral_finsetSum]
  · simp [X, idealPilotErrorCellPath]
  · intro j _
    simpa [X, idealPilotErrorCellPath] using
      (ContinuousMap.evalCLM ℝ lambda).integrable_comp (hXint j)

/-- Equations (21), (32), and (33), before the final elementary rate
simplification, bound the exact scalar good-pilot risk. With [the specified inputs and conditions](hyp:epsilon,he,he'), [the stated relationship holds](goal). -/
-- @node: centeredIdealGoodPilotErrorRisk_le_raw
lemma centeredIdealGoodPilotErrorRisk_le_raw
    (epsilon : ℝ) (he : 0 < epsilon) (he' : epsilon < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {n d : ℕ} (hn : 1 ≤ n) (hd : 16 ≤ d) (P : DiscreteLaw d),
      IsProbabilityMeasure (idealCountLaw (n := n) P) →
      centeredIdealPilotErrorRisk (n := n) epsilon P true ≤
        C * (d : ℝ) ^ (1 / 16 : ℝ) *
          (2 * logAlphabet d / ((n : ℝ) / 8) +
            2 * d * (logAlphabet d / ((n : ℝ) / 8)) ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := idealGoodPilotError_centered_maximal_quantitative
    epsilon he he'
  refine ⟨C, hC, ?_⟩
  intro n d hn hd P hprob
  rw [centeredIdealGoodPilotErrorRisk_eq_path_integral
    epsilon he he' hn hd P hprob]
  exact hbound hn hd P hprob

/-- The logarithmic cell-scale expression in the raw equation (33) bound is
absorbed by the advertised `d /(m log(ed))` rate on the paper's main branch. With [the specified inputs and conditions](hyp:n,d,hn,hd,hbranch), [the stated relationship holds](goal). -/
-- @node: goodPilot_raw_scale_le_rate
lemma goodPilot_raw_scale_le_rate {n d : ℕ} (hn : 1 ≤ n) (hd : 16 ≤ d)
    (hbranch : (d : ℝ) / logAlphabet d ≤ n) :
    (d : ℝ) ^ (1 / 16 : ℝ) *
        (2 * logAlphabet d / ((n : ℝ) / 8) +
          2 * d * (logAlphabet d / ((n : ℝ) / 8)) ^ 2) ≤
      2000000 * d / (((n : ℝ) / 8) * logAlphabet d) := by
  let m : ℝ := (n : ℝ) / 8
  let L : ℝ := logAlphabet d
  let r : ℝ := (d : ℝ) ^ (1 / 16 : ℝ)
  have hm : 0 < m := by dsimp [m]; positivity
  have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hdpos : (0 : ℝ) < d := lt_of_lt_of_le zero_lt_one hdreal
  have hLform : L = 1 + Real.log d := by
    dsimp [L]
    rw [logAlphabet, Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hdpos),
      Real.log_exp]
  have hL : 0 < L := by
    rw [hLform]
    linarith [Real.log_nonneg hdreal]
  have hr : 1 ≤ r := Real.one_le_rpow hdreal (by norm_num)
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hr16 : r ^ 16 = (d : ℝ) := by
    dsimp [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg d)]
    norm_num
  have hlog := Real.log_natCast_le_rpow_div d
    (show (0 : ℝ) < 1 / 16 by norm_num)
  have hLr : L ≤ 17 * r := by
    rw [hLform]
    dsimp [r]
    norm_num at hlog ⊢
    nlinarith [Real.one_le_rpow hdreal (by norm_num : (0 : ℝ) ≤ 1 / 16)]
  have hL0 : 0 ≤ L := hL.le
  have hL2 : L ^ 2 ≤ (17 * r) ^ 2 := pow_le_pow_left₀ hL0 hLr 2
  have hL4 : L ^ 4 ≤ (17 * r) ^ 4 := pow_le_pow_left₀ hL0 hLr 4
  have hr3 : r ^ 3 ≤ (d : ℝ) := by
    rw [← hr16]
    exact pow_le_pow_right₀ hr (by omega)
  have hr5 : r ^ 5 ≤ (d : ℝ) := by
    rw [← hr16]
    exact pow_le_pow_right₀ hr (by omega)
  have hfirst : 2 * r * L ^ 2 ≤ 578 * d := by
    calc
      2 * r * L ^ 2 ≤ 2 * r * (17 * r) ^ 2 := by gcongr
      _ = 578 * r ^ 3 := by ring
      _ ≤ 578 * d := by gcongr
  have hddiv : (d : ℝ) / m ≤ 8 * L := by
    apply (div_le_iff₀ hm).2
    have hdle : (d : ℝ) ≤ (n : ℝ) * L := (div_le_iff₀ hL).1 hbranch
    dsimp [m]
    nlinarith
  have hsecond : 2 * r * ((d : ℝ) / m) * L ^ 3 ≤
      (16 * 17 ^ 4) * d := by
    calc
      2 * r * ((d : ℝ) / m) * L ^ 3 ≤ 2 * r * (8 * L) * L ^ 3 := by
        gcongr
      _ = 16 * r * L ^ 4 := by ring
      _ ≤ 16 * r * (17 * r) ^ 4 := by gcongr
      _ = (16 * 17 ^ 4) * r ^ 5 := by ring
      _ ≤ (16 * 17 ^ 4) * d := by gcongr
  apply (le_div_iff₀ (mul_pos hm hL)).2
  change r * (2 * L / m + 2 * d * (L / m) ^ 2) * (m * L) ≤
    2000000 * d
  have hrearrange :
      r * (2 * L / m + 2 * d * (L / m) ^ 2) * (m * L) =
        2 * r * L ^ 2 + 2 * r * ((d : ℝ) / m) * L ^ 3 := by
    field_simp
  rw [hrearrange]
  nlinarith

/-- Equation (33) in its advertised rate form. The constant depends only on
the fixed overlap level through the preceding Jackson envelope. With [the specified inputs and conditions](hyp:epsilon,he,he'), [the stated relationship holds](goal). -/
-- @node: centeredIdealGoodPilotErrorRisk_le_rate
lemma centeredIdealGoodPilotErrorRisk_le_rate
    (epsilon : ℝ) (he : 0 < epsilon) (he' : epsilon < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {n d : ℕ} (hn : 1 ≤ n) (hd : 16 ≤ d)
      (hbranch : (d : ℝ) / logAlphabet d ≤ n) (P : DiscreteLaw d),
      IsProbabilityMeasure (idealCountLaw (n := n) P) →
      centeredIdealPilotErrorRisk (n := n) epsilon P true ≤
        C * d / (((n : ℝ) / 8) * logAlphabet d) := by
  obtain ⟨C₀, hC₀, hraw⟩ := centeredIdealGoodPilotErrorRisk_le_raw
    epsilon he he'
  refine ⟨2000000 * C₀, by positivity, ?_⟩
  intro n d hn hd hbranch P hprob
  calc
    centeredIdealPilotErrorRisk (n := n) epsilon P true ≤
        C₀ * ((d : ℝ) ^ (1 / 16 : ℝ) *
          (2 * logAlphabet d / ((n : ℝ) / 8) +
            2 * d * (logAlphabet d / ((n : ℝ) / 8)) ^ 2)) := by
      simpa [mul_assoc] using hraw hn hd P hprob
    _ ≤ C₀ * (2000000 * d /
        (((n : ℝ) / 8) * logAlphabet d)) := by
      gcongr
      exact goodPilot_raw_scale_le_rate hn hd hbranch
    _ = (2000000 * C₀) * d /
        (((n : ℝ) / 8) * logAlphabet d) := by ring

end CausalSmith.Stat.DiscreteBudgetvalueCurve
