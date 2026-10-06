module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperBadPilotClipped
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperLogAbsorption
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperNullPilot

/-! # Aggregating actual bad-pilot losses

The exponential estimates in (22) absorb the clipping inflation and yield
an alphabet-decaying cell loss. Summing these actual losses on the active
branch gives the variance-scale rate in (31), including null cells.
-/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory ProbabilityTheory
open Causalean.Stat.Concentration.PoissonSelfNormalized
open Causalean.Stat.Concentration.Poisson.EmpiricalRadius
open scoped BigOperators NNReal


-- @node: logAlphabet_exp_decay_mul_rpow_le
/-- An exponential tail at the logarithmic alphabet scale absorbs any smaller prescribed polynomial inflation and decay. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hd,hβ,hgap), the [stated conclusion](goal) holds. -/
lemma logAlphabet_exp_decay_mul_rpow_le {d : ℕ} (hd : 1 ≤ d)
    (α β δ : ℝ) (hβ : 0 ≤ β) (hgap : α + δ ≤ β) :
    (d : ℝ) ^ α * Real.exp (-β * logAlphabet d) ≤ (d : ℝ) ^ (-δ) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hlog : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg hd1
  have hL : logAlphabet d = 1 + Real.log (d : ℝ) := by
    rw [logAlphabet, Real.log_mul (Real.exp_pos 1).ne' hd0.ne', Real.log_exp]
  rw [Real.rpow_def_of_pos hd0, Real.rpow_def_of_pos hd0, ← Real.exp_add, hL]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hgap) hlog]


-- @node: badPilot_squared_coefficient_decay_le
/-- The precise squared clipping inflation in (22) is absorbed by the exponential bad-pilot tail, retaining the paper's d⁻⁴ factor. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hd,hC,hD), the [stated conclusion](goal) holds. -/
lemma badPilot_squared_coefficient_decay_le {d : ℕ} (hd : 1 ≤ d)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) :
    2 * (((d : ℝ) ^ (1 / 4 : ℝ)) ^ 2 * C + D) *
      Real.exp (-20 * logAlphabet d) ≤ 2 * (C + D) * (d : ℝ) ^ (-4 : ℝ) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hpow : ((d : ℝ) ^ (1 / 4 : ℝ)) ^ 2 = (d : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_mul_natCast hd0]
    norm_num
  have h₁ := logAlphabet_exp_decay_mul_rpow_le hd (1 / 2) 20 4
    (by norm_num) (by norm_num)
  have h₂ := logAlphabet_exp_decay_mul_rpow_le hd 0 20 4
    (by norm_num) (by norm_num)
  simp only [Real.rpow_zero, one_mul] at h₂
  rw [hpow]
  nlinarith [mul_le_mul_of_nonneg_left h₁ hC, mul_le_mul_of_nonneg_left h₂ hD]

open Classical in
/-- The actual bad-pilot cell loss has the d⁻⁴ bound in (22), without an occupied-cell premise: null cells are localized almost surely. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hd,hε,hε1,hP,m,hm,hHpos,hH,hW,hlaw,hind), the [stated conclusion](goal) holds. -/
lemma pilotRectangle_bad_clippedCellValue_alphabet_sq_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d : ℕ} (hd : 1 ≤ d) (ε : ℝ) (P : DiscreteLaw d)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hP : ObservedClass ε P) (x : Fin d)
    (W : Fin 4 → Ω → ℕ) (Ne : Ω → Fin 4 → ℕ) (m : ℝ≥0) (hm : 0 < m)
    (H : ℝ) (hHpos : 0 < H) (hH : universalH ≤ H)
    (hW : ∀ j, Measurable (W j))
    (hlaw : ∀ j, HasLaw (W j)
      (poissonMeasure (m * ⟨cellVector P x j, ENNReal.toReal_nonneg⟩)) μ)
    (hind : iIndepFun W μ) (K : ℕ) :
    let C := 512 * H ^ 2 * (8 + 2 * (H / universalH) * productMomentConstant 4 1)
    let D := 1024 * Real.sqrt (8 * scalarMomentConstant 4) * (H / universalH) ^ 2
    (∫ ω, if cellVector P x ∉ pilotRectangle
        (pilotLower H hHpos m (logAlphabet d) (fun j => W j ω))
        (pilotUpperFormula H hHpos m (logAlphabet d) (fun j => W j ω)) then
      (clippedCellValueFormula ε K d m
        (pilotMidpoint H hHpos m (logAlphabet d) (fun j => W j ω))
        (pilotRadiusFormula H hHpos m (logAlphabet d) (fun j => W j ω)) (Ne ω) -
        armwiseExtensionFormula ε (cellVector P x)) ^ 2 else 0 ∂μ) ≤
      2 * (C + D) * (d : ℝ) ^ (-4 : ℝ) *
        (cellMass P x * logAlphabet d / (m * ε) +
          logAlphabet d ^ 2 / ((m : ℝ) ^ 2 * ε ^ 2)) := by
  classical
  dsimp only
  have hC : 0 ≤ 512 * H ^ 2 *
      (8 + 2 * (H / universalH) * productMomentConstant 4 1) := by
    have hu := universalH_pos
    have hc := productMomentConstant_pos 4 1
    positivity
  have hD : 0 ≤ 1024 * Real.sqrt (8 * scalarMomentConstant 4) * (H / universalH) ^ 2 :=
    by positivity
  have hp0 : 0 ≤ cellMass P x :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun y _ => ENNReal.toReal_nonneg
  have hs : 0 ≤ cellMass P x * logAlphabet d / (m * ε) +
      logAlphabet d ^ 2 / ((m : ℝ) ^ 2 * ε ^ 2) := by
    have hL := logAlphabet_pos hd
    positivity
  by_cases hp : cellMass P x = 0
  · have hnull := nullCell_pilotRectangle_ae_contains μ P x hp H hHpos m
      (logAlphabet d) (NNReal.coe_pos.mpr hm) (logAlphabet_pos hd).le W (by
        intro j
        convert hlaw j using 1
        congr 1)
    have heq : (∫ ω, if cellVector P x ∉ pilotRectangle
        (pilotLower H hHpos m (logAlphabet d) (fun j => W j ω))
        (pilotUpperFormula H hHpos m (logAlphabet d) (fun j => W j ω)) then
      (clippedCellValueFormula ε K d m
        (pilotMidpoint H hHpos m (logAlphabet d) (fun j => W j ω))
        (pilotRadiusFormula H hHpos m (logAlphabet d) (fun j => W j ω)) (Ne ω) -
        armwiseExtensionFormula ε (cellVector P x)) ^ 2 else 0 ∂μ) = 0 := by
      calc
        _ = ∫ _, (0 : ℝ) ∂μ := integral_congr_ae (by
          filter_upwards [hnull] with ω hω
          simp only [if_neg (not_not.mpr hω)])
        _ = 0 := integral_zero _ _
    rw [heq]
    exact mul_nonneg (mul_nonneg (by linarith)
      (Real.rpow_nonneg (Nat.cast_nonneg d) _)) hs
  · have hL : 1 ≤ logAlphabet d := by
      have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
      rw [logAlphabet, Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp]
      linarith [Real.log_nonneg hd1]
    exact (pilotRectangle_bad_clippedCellValue_integral_sq_le μ ε P hε hε1 hP x
      (lt_of_le_of_ne hp0 (ne_comm.mp hp)) W Ne m hm H hHpos (logAlphabet d) hH hL
      hW hlaw hind K).trans
      (mul_le_mul_of_nonneg_right (badPilot_squared_coefficient_decay_le hd _ _ hC hD) hs)

open Classical in
/-- On the active branch, d times the summed actual bad-pilot squared loss is at most a universal multiple of d/(m ε L). This controls both its variance contribution and the Cauchy–Schwarz bound for its total bias. No cross-cell or evaluation-count independence is required. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hHpos,hH), the [stated conclusion](goal) holds. -/
lemma activeBranch_badPilot_clippedCellValue_sum_sq_rate_le
    (H : ℝ) (hHpos : 0 < H) (hH : universalH ≤ H) :
    ∃ A : ℝ, 0 < A ∧ ∀ {Ω : Type*} [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ}, 1 ≤ d →
      ∀ (ε : ℝ) (P : DiscreteLaw d), 0 < ε → ε ≤ 1 → ObservedClass ε P →
      ∀ (W : Fin d → Fin 4 → Ω → ℕ) (Ne : Fin d → Ω → Fin 4 → ℕ)
      (m : ℝ≥0), 0 < m → (d : ℝ) ≤ 8 * (m * ε) * logAlphabet d →
      (∀ x j, Measurable (W x j)) →
      (∀ x j, HasLaw (W x j)
        (poissonMeasure (m * ⟨cellVector P x j, ENNReal.toReal_nonneg⟩)) μ) →
      (∀ x, iIndepFun (W x) μ) → ∀ K : ℕ,
      (d : ℝ) * (∑ x : Fin d, ∫ ω, if cellVector P x ∉ pilotRectangle
          (pilotLower H hHpos m (logAlphabet d) (fun j => W x j ω))
          (pilotUpperFormula H hHpos m (logAlphabet d) (fun j => W x j ω)) then
        (clippedCellValueFormula ε K d m
          (pilotMidpoint H hHpos m (logAlphabet d) (fun j => W x j ω))
          (pilotRadiusFormula H hHpos m (logAlphabet d) (fun j => W x j ω)) (Ne x ω) -
          armwiseExtensionFormula ε (cellVector P x)) ^ 2 else 0 ∂μ) ≤
        A * ((d : ℝ) / (m * ε * logAlphabet d)) := by
  let C := 512 * H ^ 2 * (8 + 2 * (H / universalH) * productMomentConstant 4 1)
  let D := 1024 * Real.sqrt (8 * scalarMomentConstant 4) * (H / universalH) ^ 2
  have hC : 0 < C := by
    have hu := universalH_pos
    have hc := productMomentConstant_pos 4 1
    dsimp [C]
    positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  obtain ⟨A₀, hA₀, hrate⟩ := activeBranch_pilot_moment_sum_rate_le 1 (by norm_num)
  refine ⟨2 * (C + D) * A₀, by positivity, ?_⟩
  intro Ω _ μ _ d hd ε P hε hε1 hP W Ne m hm hactive hW hlaw hind K
  let v : Fin d → ℝ := fun x => ∫ ω, if cellVector P x ∉ pilotRectangle
      (pilotLower H hHpos m (logAlphabet d) (fun j => W x j ω))
      (pilotUpperFormula H hHpos m (logAlphabet d) (fun j => W x j ω)) then
    (clippedCellValueFormula ε K d m
      (pilotMidpoint H hHpos m (logAlphabet d) (fun j => W x j ω))
      (pilotRadiusFormula H hHpos m (logAlphabet d) (fun j => W x j ω)) (Ne x ω) -
      armwiseExtensionFormula ε (cellVector P x)) ^ 2 else 0 ∂μ
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hdecay : (d : ℝ) * (d : ℝ) ^ (-4 : ℝ) ≤ 1 := by
    nth_rw 1 [← Real.rpow_one (d : ℝ)]
    rw [← Real.rpow_add hd0]
    exact Real.rpow_le_one_of_one_le_of_nonpos hd1 (by norm_num)
  have hv (x : Fin d) : (d : ℝ) * v x ≤
      (2 * (C + D)) * (cellMass P x * logAlphabet d / (m * ε) +
        logAlphabet d ^ 2 / ((m : ℝ) * ε) ^ 2) := by
    have ht := pilotRectangle_bad_clippedCellValue_alphabet_sq_le μ hd ε P hε hε1 hP x
      (W x) (Ne x) m hm H hHpos hH (hW x) (hlaw x) (hind x) K
    change v x ≤ 2 * (C + D) * (d : ℝ) ^ (-4 : ℝ) * _ at ht
    have hp0 : 0 ≤ cellMass P x :=
      Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun y _ => ENNReal.toReal_nonneg
    have hL := logAlphabet_pos hd
    have hscale : 0 ≤ cellMass P x * logAlphabet d / (m * ε) +
        logAlphabet d ^ 2 / ((m : ℝ) ^ 2 * ε ^ 2) := by positivity
    have hs := mul_le_mul_of_nonneg_right hdecay
      (mul_nonneg (show 0 ≤ 2 * (C + D) by positivity) hscale)
    have ht' := mul_le_mul_of_nonneg_left ht hd0.le
    simpa only [mul_pow] using (ht'.trans (by nlinarith [hs]))
  have hr := hrate hd P (fun x => (d : ℝ) * v x) (2 * (C + D)) (m * ε)
    (by positivity) (by positivity) hactive hv
  norm_num only [sub_self, Real.rpow_zero, one_mul] at hr
  rw [← Finset.mul_sum] at hr
  exact hr

open Classical in
/-- The actual absolute bad-pilot error retains the d⁻² decay in (22), including null cells and arbitrary evaluation counts. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hd,hε,hε1,hP,m,hm,hHpos,hH,hW,hlaw,hind), the [stated conclusion](goal) holds. -/
lemma pilotRectangle_bad_clippedCellValue_alphabet_abs_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d : ℕ} (hd : 1 ≤ d) (ε : ℝ) (P : DiscreteLaw d)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hP : ObservedClass ε P) (x : Fin d)
    (W : Fin 4 → Ω → ℕ) (Ne : Ω → Fin 4 → ℕ) (m : ℝ≥0) (hm : 0 < m)
    (H : ℝ) (hHpos : 0 < H) (hH : universalH ≤ H)
    (hW : ∀ j, Measurable (W j))
    (hlaw : ∀ j, HasLaw (W j)
      (poissonMeasure (m * ⟨cellVector P x j, ENNReal.toReal_nonneg⟩)) μ)
    (hind : iIndepFun W μ) (K : ℕ) :
    let C := Real.sqrt (8 * (512 * H ^ 2 * (8 + 2 * (H / universalH) * productMomentConstant 4 1)))
    let D := Real.sqrt (8 * (1024 * Real.sqrt (8 * scalarMomentConstant 4) * (H / universalH) ^ 2))
    (∫ ω, if cellVector P x ∉ pilotRectangle
        (pilotLower H hHpos m (logAlphabet d) (fun j => W j ω))
        (pilotUpperFormula H hHpos m (logAlphabet d) (fun j => W j ω)) then
      |clippedCellValueFormula ε K d m
        (pilotMidpoint H hHpos m (logAlphabet d) (fun j => W j ω))
        (pilotRadiusFormula H hHpos m (logAlphabet d) (fun j => W j ω)) (Ne ω) -
        armwiseExtensionFormula ε (cellVector P x)| else 0 ∂μ) ≤
      (C + D) * (d : ℝ) ^ (-2 : ℝ) *
        (Real.sqrt (cellMass P x * logAlphabet d / (m * ε)) +
          logAlphabet d / (m * ε)) := by
  classical
  dsimp only
  have hC : 0 ≤ Real.sqrt (8 * (512 * H ^ 2 *
      (8 + 2 * (H / universalH) * productMomentConstant 4 1))) := Real.sqrt_nonneg _
  have hD : 0 ≤ Real.sqrt (8 * (1024 * Real.sqrt (8 * scalarMomentConstant 4) *
      (H / universalH) ^ 2)) := Real.sqrt_nonneg _
  have hL := logAlphabet_pos hd
  have hs : 0 ≤ Real.sqrt (cellMass P x * logAlphabet d / (m * ε)) +
      logAlphabet d / (m * ε) := by positivity
  have hp0 : 0 ≤ cellMass P x :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun y _ => ENNReal.toReal_nonneg
  by_cases hp : cellMass P x = 0
  · have hnull := nullCell_pilotRectangle_ae_contains μ P x hp H hHpos m
      (logAlphabet d) (NNReal.coe_pos.mpr hm) hL.le W (by
        intro j
        convert hlaw j using 1
        congr 1)
    have heq : (∫ ω, if cellVector P x ∉ pilotRectangle
        (pilotLower H hHpos m (logAlphabet d) (fun j => W j ω))
        (pilotUpperFormula H hHpos m (logAlphabet d) (fun j => W j ω)) then
      |clippedCellValueFormula ε K d m
        (pilotMidpoint H hHpos m (logAlphabet d) (fun j => W j ω))
        (pilotRadiusFormula H hHpos m (logAlphabet d) (fun j => W j ω)) (Ne ω) -
        armwiseExtensionFormula ε (cellVector P x)| else 0 ∂μ) = 0 := by
      calc
        _ = ∫ _, (0 : ℝ) ∂μ := integral_congr_ae (by
          filter_upwards [hnull] with ω hω
          simp only [if_neg (not_not.mpr hω)])
        _ = 0 := integral_zero _ _
    rw [heq]
    positivity
  · have hL1 : 1 ≤ logAlphabet d := by
      have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
      rw [logAlphabet, Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp]
      linarith [Real.log_nonneg hd1]
    have ht := pilotRectangle_bad_clippedCellValue_integral_le μ ε P hε hε1 hP x
      (lt_of_le_of_ne hp0 (ne_comm.mp hp)) W Ne m hm H hHpos (logAlphabet d) hH hL1
      hW hlaw hind K
    have h₁ := logAlphabet_exp_decay_mul_rpow_le hd (1 / 4) 30 2
      (by norm_num) (by norm_num)
    have h₂ := logAlphabet_exp_decay_mul_rpow_le hd 0 30 2
      (by norm_num) (by norm_num)
    simp only [Real.rpow_zero, one_mul] at h₂
    apply ht.trans
    apply mul_le_mul_of_nonneg_right _ hs
    nlinarith [mul_le_mul_of_nonneg_left h₁ hC, mul_le_mul_of_nonneg_left h₂ hD]

open Classical in
/-- The total actual bad-pilot absolute bias, squared after summing cells, is controlled on the active branch. No cross-cell independence is needed. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hHpos,hH), the [stated conclusion](goal) holds. -/
lemma activeBranch_badPilot_clippedCellValue_total_abs_sq_rate_le
    (H : ℝ) (hHpos : 0 < H) (hH : universalH ≤ H) :
    ∃ A : ℝ, 0 < A ∧ ∀ {Ω : Type*} [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ}, 1 ≤ d →
      ∀ (ε : ℝ) (P : DiscreteLaw d), 0 < ε → ε ≤ 1 → ObservedClass ε P →
      ∀ (W : Fin d → Fin 4 → Ω → ℕ) (Ne : Fin d → Ω → Fin 4 → ℕ)
      (m : ℝ≥0), 0 < m → (d : ℝ) ≤ 8 * (m * ε) * logAlphabet d →
      (∀ x j, Measurable (W x j)) →
      (∀ x j, HasLaw (W x j)
        (poissonMeasure (m * ⟨cellVector P x j, ENNReal.toReal_nonneg⟩)) μ) →
      (∀ x, iIndepFun (W x) μ) → ∀ K : ℕ,
      (∑ x : Fin d, ∫ ω, if cellVector P x ∉ pilotRectangle
          (pilotLower H hHpos m (logAlphabet d) (fun j => W x j ω))
          (pilotUpperFormula H hHpos m (logAlphabet d) (fun j => W x j ω)) then
        |clippedCellValueFormula ε K d m
          (pilotMidpoint H hHpos m (logAlphabet d) (fun j => W x j ω))
          (pilotRadiusFormula H hHpos m (logAlphabet d) (fun j => W x j ω)) (Ne x ω) -
          armwiseExtensionFormula ε (cellVector P x)| else 0 ∂μ) ^ 2 ≤
        A * ((d : ℝ) / (m * ε * logAlphabet d)) := by
  let C := Real.sqrt (8 * (512 * H ^ 2 *
    (8 + 2 * (H / universalH) * productMomentConstant 4 1))) +
    Real.sqrt (8 * (1024 * Real.sqrt (8 * scalarMomentConstant 4) * (H / universalH) ^ 2))
  have hC : 0 < C := by
    have hu := universalH_pos
    have hc := productMomentConstant_pos 4 1
    dsimp [C]
    positivity
  obtain ⟨A₀, hA₀, hrate⟩ := activeBranch_pilot_moment_sum_rate_le 1 (by norm_num)
  refine ⟨2 * C ^ 2 * A₀, by positivity, ?_⟩
  intro Ω _ μ _ d hd ε P hε hε1 hP W Ne m hm hactive hW hlaw hind K
  let v : Fin d → ℝ := fun x => ∫ ω, if cellVector P x ∉ pilotRectangle
      (pilotLower H hHpos m (logAlphabet d) (fun j => W x j ω))
      (pilotUpperFormula H hHpos m (logAlphabet d) (fun j => W x j ω)) then
    |clippedCellValueFormula ε K d m
      (pilotMidpoint H hHpos m (logAlphabet d) (fun j => W x j ω))
      (pilotRadiusFormula H hHpos m (logAlphabet d) (fun j => W x j ω)) (Ne x ω) -
      armwiseExtensionFormula ε (cellVector P x)| else 0 ∂μ
  have hv0 (x : Fin d) : 0 ≤ v x := integral_nonneg (fun ω => by
    dsimp only
    split_ifs <;> positivity)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hdecay : (d : ℝ) * ((d : ℝ) ^ (-2 : ℝ)) ^ 2 ≤ 1 := by
    rw [← Real.rpow_mul_natCast hd0.le]
    nth_rw 1 [← Real.rpow_one (d : ℝ)]
    rw [← Real.rpow_add hd0]
    exact Real.rpow_le_one_of_one_le_of_nonpos hd1 (by norm_num)
  have hv (x : Fin d) : (d : ℝ) * (v x) ^ 2 ≤
      (2 * C ^ 2) * (cellMass P x * logAlphabet d / (m * ε) +
        logAlphabet d ^ 2 / ((m : ℝ) * ε) ^ 2) := by
    have ht := pilotRectangle_bad_clippedCellValue_alphabet_abs_le μ hd ε P hε hε1 hP x
      (W x) (Ne x) m hm H hHpos hH (hW x) (hlaw x) (hind x) K
    change v x ≤ C * (d : ℝ) ^ (-2 : ℝ) *
      (Real.sqrt (cellMass P x * logAlphabet d / (m * ε)) +
        logAlphabet d / (m * ε)) at ht
    have hp0 : 0 ≤ cellMass P x :=
      Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun y _ => ENNReal.toReal_nonneg
    have hL := logAlphabet_pos hd
    have hscale : 0 ≤ cellMass P x * logAlphabet d / (m * ε) := by positivity
    have hsqrt := Real.sq_sqrt hscale
    have htwo : (Real.sqrt (cellMass P x * logAlphabet d / (m * ε)) +
        logAlphabet d / (m * ε)) ^ 2 ≤
        2 * (cellMass P x * logAlphabet d / (m * ε) +
          logAlphabet d ^ 2 / ((m : ℝ) * ε) ^ 2) := by
      rw [← div_pow]
      nlinarith [sq_nonneg (Real.sqrt (cellMass P x * logAlphabet d / (m * ε)) -
        logAlphabet d / (m * ε))]
    calc
      _ ≤ (d : ℝ) * (C * (d : ℝ) ^ (-2 : ℝ) *
          (Real.sqrt (cellMass P x * logAlphabet d / (m * ε)) +
            logAlphabet d / (m * ε))) ^ 2 := by
        gcongr
      _ = C ^ 2 * ((d : ℝ) * ((d : ℝ) ^ (-2 : ℝ)) ^ 2) *
          (Real.sqrt (cellMass P x * logAlphabet d / (m * ε)) +
            logAlphabet d / (m * ε)) ^ 2 := by ring
      _ ≤ C ^ 2 * 1 * (2 * (cellMass P x * logAlphabet d / (m * ε) +
          logAlphabet d ^ 2 / ((m : ℝ) * ε) ^ 2)) := by gcongr
      _ = _ := by ring
  have hr := hrate hd P (fun x => (d : ℝ) * (v x) ^ 2) (2 * C ^ 2) (m * ε)
    (by positivity) (by positivity) hactive hv
  norm_num only [sub_self, Real.rpow_zero, one_mul] at hr
  rw [← Finset.mul_sum] at hr
  have hsum := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin d))
    (fun _ => (1 : ℝ)) v
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at hsum
  exact hsum.trans hr

end CausalSmith.Stat.OptvalueVanishingoverlapRate
