module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperJacksonCoefficients
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperOccupiedCell
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperNullCell

/-! # Calibrated localized clipping

One universal degree tuning yields both assertions of roadmap (28).
Combining its mean displacement with the occupied-cell Jackson bias (20)
controls the actual clipped statistic around the cell target.
-/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- The same universal degree choice controls clipping bias and second moment. The Poisson laws provide the factorial mean and integrability; localization provides containment. No coefficient or moment bound is assumed. In the econometric construction, no additional assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma pilotClippedCellValue_tuning_exists :
    ∃ κ A : ℝ, 0 < κ ∧ 0 < A ∧ ∀ {Ω : Type*} [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ}, 1 ≤ d →
      ∀ (W : Fin 4 → Ω → ℕ) (q : Fin 4 → ℝ) (hqnonneg : ∀ j, 0 ≤ q j)
      (H : ℝ) (hH : 0 < H), 1 ≤ H → ∀ (m : ℝ) (hm : 0 < m) (Np : Fin 4 → ℕ),
      (∀ j, HasLaw (W j)
        (poissonMeasure ⟨m * q j, mul_nonneg hm.le (hqnonneg j)⟩) μ) →
      iIndepFun W μ →
      q ∈ pilotRectangle (pilotLower H hH m (logAlphabet d) Np)
        (pilotUpperFormula H hH m (logAlphabet d) Np) →
      ∀ (ε : ℝ), 0 < ε →
      let b := pilotMidpoint H hH m (logAlphabet d) Np
      let r := pilotRadiusFormula H hH m (logAlphabet d) Np
      let K := jacksonDegree κ d
      let p := armwiseExtensionFormula ε b + ∑ α : Fin 4 → Fin (2 * (K - 1) + 1),
        jacksonCoeff ε K b r α * ∏ j, ((q j - b j) / r j) ^ (α j).val
      (|(∫ ω, clippedCellValueFormula ε K d m b r (fun j => W j ω) ∂μ) - p| ≤
        A * (d : ℝ) ^ (-(3 / 16 : ℝ)) * clippingScaleFormula ε b r) ∧
      ((∫ ω, (clippedCellValueFormula ε K d m b r (fun j => W j ω) - p) ^ 2 ∂μ) ≤
        A * (d : ℝ) ^ (1 / 16 : ℝ) * clippingScaleFormula ε b r ^ 2) := by
  obtain ⟨κ, A, hκ, hA, htune⟩ := pilotJacksonCoeff_square_tuning_exists
  refine ⟨κ, A, hκ, hA, ?_⟩
  intro Ω _ μ _ d hd W q hqnonneg H hH hHlarge m hm Np hWlaw hind hq ε hε
  dsimp only
  have hL := logAlphabet_pos hd
  have hK : 0 < jacksonDegree κ d := by unfold jacksonDegree; omega
  have hs := clippingScale_pos ε (pilotMidpoint H hH m (logAlphabet d) Np)
    (pilotRadiusFormula H hH m (logAlphabet d) Np) (pilotMidpoint_nonneg H hH m (logAlphabet d) hm Np)
    (pilotRadius_pos H hH m _ hm hL Np)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hw := mul_pos (Real.rpow_pos_of_pos hd0 (1 / 4 : ℝ)) hs
  have hc := htune hd H hH m hm Np ε hε
  constructor
  · apply (pilotClippedCellValue_bias_envelope μ W q hqnonneg H hH hHlarge
      m _ hm hL Np hWlaw hind hq ε _ d hw).trans
    apply (div_le_div_of_nonneg_right hc hw.le).trans_eq
    have hp : (d : ℝ) ^ (1 / 16 : ℝ) / (d : ℝ) ^ (1 / 4 : ℝ) =
        (d : ℝ) ^ (-(3 / 16 : ℝ)) := by
      rw [← Real.rpow_sub hd0]
      norm_num
    rw [show A * (d : ℝ) ^ (1 / 16 : ℝ) *
        clippingScaleFormula ε (pilotMidpoint H hH m (logAlphabet d) Np)
          (pilotRadiusFormula H hH m (logAlphabet d) Np) ^ 2 /
        ((d : ℝ) ^ (1 / 4 : ℝ) *
          clippingScaleFormula ε (pilotMidpoint H hH m (logAlphabet d) Np)
            (pilotRadiusFormula H hH m (logAlphabet d) Np)) =
        A * ((d : ℝ) ^ (1 / 16 : ℝ) / (d : ℝ) ^ (1 / 4 : ℝ)) *
          clippingScaleFormula ε (pilotMidpoint H hH m (logAlphabet d) Np)
            (pilotRadiusFormula H hH m (logAlphabet d) Np) by
      field_simp]
    rw [hp]
  · exact (pilotClippedCellValue_square_envelope_of_localized μ W q hqnonneg
      H hH hHlarge m _ hm hL Np hWlaw hind hq ε hε _ d hK hd).trans hc

/-- Combining (20) and both parts of (28) controls the actual clipped occupied-cell mean and loss around the statistical target. The polynomial approximation error is retained explicitly in the squared-loss bound. In the econometric construction, no additional assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma observed_pilotClippedCellValue_target_tuning_exists :
    ∃ κ A : ℝ, 0 < κ ∧ 0 < A ∧ ∀ {Ω : Type*} [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ}, 1 ≤ d →
      ∀ (ε : ℝ) (P : DiscreteLaw d), 0 < ε → ObservedClass ε P →
      ∀ (x : Fin d), 0 < cellMass P x →
      ∀ (W : Fin 4 → Ω → ℕ) (H : ℝ) (hH : 0 < H), 1 ≤ H →
      ∀ (m : ℝ) (hm : 0 < m) (Np : Fin 4 → ℕ),
      (∀ j, HasLaw (W j)
        (poissonMeasure ⟨m * cellVector P x j,
          mul_nonneg hm.le ENNReal.toReal_nonneg⟩) μ) →
      iIndepFun W μ →
      cellVector P x ∈ pilotRectangle (pilotLower H hH m (logAlphabet d) Np)
        (pilotUpperFormula H hH m (logAlphabet d) Np) →
      let b := pilotMidpoint H hH m (logAlphabet d) Np
      let r := pilotRadiusFormula H hH m (logAlphabet d) Np
      let K := jacksonDegree κ d
      let B := 512 * (H * (H + 2)) * Real.sqrt 2 * (1 / (κ / 2) + 1 / (κ / 2) ^ 2) *
        (Real.sqrt (cellMass P x / (m * ε * logAlphabet d)) + 1 / (m * ε * logAlphabet d))
      (|(∫ ω, clippedCellValueFormula ε K d m b r (fun j => W j ω) ∂μ) -
          armwiseExtensionFormula ε (cellVector P x)| ≤
        B + A * (d : ℝ) ^ (-(3 / 16 : ℝ)) * clippingScaleFormula ε b r) ∧
      ((∫ ω, (clippedCellValueFormula ε K d m b r (fun j => W j ω) -
          armwiseExtensionFormula ε (cellVector P x)) ^ 2 ∂μ) ≤
        2 * A * (d : ℝ) ^ (1 / 16 : ℝ) * clippingScaleFormula ε b r ^ 2 + 2 * B ^ 2) := by
  obtain ⟨κ, A, hκ, hA, hclip⟩ := pilotClippedCellValue_tuning_exists
  refine ⟨κ, A, hκ, hA, ?_⟩
  intro Ω _ μ _ d hd ε P hε hP x hp W H hH hHlarge m hm Np hWlaw hind hloc
  dsimp only
  let b := pilotMidpoint H hH m (logAlphabet d) Np
  let r := pilotRadiusFormula H hH m (logAlphabet d) Np
  let K := jacksonDegree κ d
  let p := armwiseExtensionFormula ε b + ∑ α : Fin 4 → Fin (2 * (K - 1) + 1),
    jacksonCoeff ε K b r α * ∏ j, ((cellVector P x j - b j) / r j) ^ (α j).val
  have hK : 0 < K := by dsimp [K]; unfold jacksonDegree; omega
  have hL1 : 1 ≤ logAlphabet d := by
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    rw [logAlphabet, Real.log_mul (ne_of_gt (Real.exp_pos _)) (by positivity), Real.log_exp]
    linarith [Real.log_nonneg hd1]
  have hb := observed_pilotJackson_mean_bias_normalized_le ε P hε hP x hp
    H hH hHlarge m (logAlphabet d) (κ / 2) hm hL1 (by positivity)
    K hK (jacksonDegree_ge_half_log κ d) Np hloc
  obtain ⟨hbclip, hsclip⟩ := hclip μ hd W (cellVector P x)
    (fun _ => ENNReal.toReal_nonneg) H hH hHlarge m hm Np hWlaw hind hloc ε hε
  constructor
  · exact (abs_sub_le _ p _).trans ((add_le_add hbclip hb).trans_eq (add_comm _ _))
  · have hsq := pow_le_pow_left₀ (abs_nonneg _) hb 2
    rw [sq_abs] at hsq
    have hmeanmem := pilotJackson_mean_mem_clipping_interval H hH m _ hm
      (logAlphabet_pos hd) Np ε hε K d hK hd (cellVector P x) hloc
    have hsint : Integrable (fun ω =>
        (clippedCellValueFormula ε K d m b r (fun j => W j ω) - p) ^ 2) μ := by
      have hraw := factorialCellValue_memLp_two μ W _ hWlaw hind ε K m b r
      have hT : Integrable (fun ω => clippedCellValueFormula ε K d m b r (fun j => W j ω)) μ := by
        exact (integrable_const _).sup ((integrable_const _).inf
          (hraw.integrable (by norm_num)))
      have hmeas := (hT.sub (integrable_const p)).aestronglyMeasurable.pow 2
      exact (factorialCellValue_centered_square_integrable μ W _ hWlaw hind
        ε K m b r p).mono' hmeas (ae_of_all _ fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          exact clippedCellValue_sq_error_le ε K d m b r _ p hmeanmem.1 hmeanmem.2)
    calc
      _ ≤ ∫ ω, 2 * (clippedCellValueFormula ε K d m b r (fun j => W j ω) - p) ^ 2 +
          2 * (p - armwiseExtensionFormula ε (cellVector P x)) ^ 2 ∂μ := by
        apply integral_mono_of_nonneg (ae_of_all _ fun _ => sq_nonneg _)
          ((hsint.const_mul 2).add (integrable_const _))
        apply ae_of_all
        intro ω
        change (clippedCellValueFormula ε K d m b r (fun j => W j ω) -
          armwiseExtensionFormula ε (cellVector P x)) ^ 2 ≤
          2 * (clippedCellValueFormula ε K d m b r (fun j => W j ω) - p) ^ 2 +
          2 * (p - armwiseExtensionFormula ε (cellVector P x)) ^ 2
        nlinarith [sq_nonneg (clippedCellValueFormula ε K d m b r (fun j => W j ω) -
          p - (p - armwiseExtensionFormula ε (cellVector P x)))]
      _ = 2 * (∫ ω, (clippedCellValueFormula ε K d m b r (fun j => W j ω) - p) ^ 2 ∂μ) +
          2 * (p - armwiseExtensionFormula ε (cellVector P x)) ^ 2 := by
        rw [integral_add (hsint.const_mul 2) (integrable_const _), integral_const_mul]
        simp
      _ ≤ _ := by nlinarith [hsclip]

/-- A zero-count pilot always contains the null atom, including at its lower boundary. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hH,hm,hL), the [stated conclusion](goal) holds. -/
lemma zeroPilot_rectangle_contains_zero (H : ℝ) (hH : 0 < H) (m L : ℝ)
    (hm : 0 < m) (hL : 0 ≤ L) :
    (0 : Fin 4 → ℝ) ∈ pilotRectangle
      (pilotLower H hH m L (fun _ => 0))
      (pilotUpperFormula H hH m L (fun _ => 0)) := by
  have hh : 0 ≤ H * (L / m) := by positivity
  intro j
  simp [pilotLower, pilotUpperFormula, pilotCenterFormula, pilotHalfWidthFormula, hh]

/-- The null-cell instance of (20) and (28) controls the clipped statistic's mean and second moment around the zero target, without inverse arm masses. The degree tuning is the same universal tuning used for occupied cells. In the econometric construction, no additional assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma zeroPilot_clippedCellValue_target_tuning_exists :
    ∃ κ A : ℝ, 0 < κ ∧ 0 < A ∧ ∀ {Ω : Type*} [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ}, 1 ≤ d →
      ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
      ∀ (W : Fin 4 → Ω → ℕ) (H : ℝ) (hH : 0 < H), 1 ≤ H →
      ∀ (m : ℝ) (_hm : 0 < m),
      (∀ j, HasLaw (W j)
        (poissonMeasure 0) μ) →
      iIndepFun W μ →
      let b := pilotMidpoint H hH m (logAlphabet d) (fun _ => 0)
      let r := pilotRadiusFormula H hH m (logAlphabet d) (fun _ => 0)
      let K := jacksonDegree κ d
      let B := (64 * H / (κ / 2) ^ 2) * (1 / (m * ε * logAlphabet d))
      (|(∫ ω, clippedCellValueFormula ε K d m b r (fun j => W j ω) ∂μ) -
          armwiseExtensionFormula ε (0 : Fin 4 → ℝ)| ≤
        B + A * (d : ℝ) ^ (-(3 / 16 : ℝ)) * clippingScaleFormula ε b r) ∧
      ((∫ ω, (clippedCellValueFormula ε K d m b r (fun j => W j ω) -
          armwiseExtensionFormula ε (0 : Fin 4 → ℝ)) ^ 2 ∂μ) ≤
        2 * A * (d : ℝ) ^ (1 / 16 : ℝ) * clippingScaleFormula ε b r ^ 2 + 2 * B ^ 2) := by
  obtain ⟨κ, A, hκ, hA, hclip⟩ := pilotClippedCellValue_tuning_exists
  refine ⟨κ, A, hκ, hA, ?_⟩
  intro Ω _ μ _ d hd ε hε hε1 W H hH hHlarge m hm hWlaw hind
  have hloc := zeroPilot_rectangle_contains_zero H hH m (logAlphabet d) hm
    (logAlphabet_pos hd).le
  dsimp only
  let b := pilotMidpoint H hH m (logAlphabet d) (fun _ => 0)
  let r := pilotRadiusFormula H hH m (logAlphabet d) (fun _ => 0)
  let K := jacksonDegree κ d
  let p := armwiseExtensionFormula ε b + ∑ α : Fin 4 → Fin (2 * (K - 1) + 1),
    jacksonCoeff ε K b r α * ∏ j, (((0 : Fin 4 → ℝ) j - b j) / r j) ^ (α j).val
  have hK : 0 < K := by dsimp [K]; unfold jacksonDegree; omega
  have hb := zeroPilot_jacksonCoeff_mean_normalized_le H hH m (logAlphabet d)
    hm (logAlphabet_pos hd) ε hε hε1 K hK (κ / 2) (by positivity)
    (jacksonDegree_ge_half_log κ d)
  have hWlaw0 : ∀ j, HasLaw (W j)
      (poissonMeasure ⟨m * (0 : Fin 4 → ℝ) j,
        mul_nonneg hm.le (le_refl 0)⟩) μ := by
    intro j
    have hz : (⟨m * (0 : Fin 4 → ℝ) j,
        mul_nonneg hm.le (le_refl 0)⟩ : NNReal) = 0 := by
      ext
      simp
    rw [hz]
    exact hWlaw j
  obtain ⟨hbclip, hsclip⟩ := hclip μ hd W (0 : Fin 4 → ℝ)
    (fun _ => le_rfl) H hH hHlarge m hm (fun _ => 0) hWlaw0 hind hloc ε hε
  constructor
  · exact (abs_sub_le _ p _).trans ((add_le_add hbclip hb).trans_eq (add_comm _ _))
  · have hsq := pow_le_pow_left₀ (abs_nonneg _) hb 2
    rw [sq_abs] at hsq
    change (p - armwiseExtensionFormula ε 0) ^ 2 ≤ _ at hsq
    have hmeanmem := pilotJackson_mean_mem_clipping_interval H hH m _ hm
      (logAlphabet_pos hd) (fun _ => 0) ε hε K d hK hd (0 : Fin 4 → ℝ) hloc
    have hsint : Integrable (fun ω =>
        (clippedCellValueFormula ε K d m b r (fun j => W j ω) - p) ^ 2) μ := by
      have hraw := factorialCellValue_memLp_two μ W _ hWlaw0 hind ε K m b r
      have hT : Integrable (fun ω => clippedCellValueFormula ε K d m b r (fun j => W j ω)) μ := by
        exact (integrable_const _).sup ((integrable_const _).inf
          (hraw.integrable (by norm_num)))
      have hmeas := (hT.sub (integrable_const p)).aestronglyMeasurable.pow 2
      exact (factorialCellValue_centered_square_integrable μ W _ hWlaw0 hind
        ε K m b r p).mono' hmeas (ae_of_all _ fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          exact clippedCellValue_sq_error_le ε K d m b r _ p hmeanmem.1 hmeanmem.2)
    calc
      _ ≤ ∫ ω, 2 * (clippedCellValueFormula ε K d m b r (fun j => W j ω) - p) ^ 2 +
          2 * (p - armwiseExtensionFormula ε (0 : Fin 4 → ℝ)) ^ 2 ∂μ := by
        apply integral_mono_of_nonneg (ae_of_all _ fun _ => sq_nonneg _)
          ((hsint.const_mul 2).add (integrable_const _))
        apply ae_of_all
        intro ω
        change (clippedCellValueFormula ε K d m b r (fun j => W j ω) -
          armwiseExtensionFormula ε (0 : Fin 4 → ℝ)) ^ 2 ≤
          2 * (clippedCellValueFormula ε K d m b r (fun j => W j ω) - p) ^ 2 +
          2 * (p - armwiseExtensionFormula ε (0 : Fin 4 → ℝ)) ^ 2
        nlinarith [sq_nonneg (clippedCellValueFormula ε K d m b r (fun j => W j ω) -
          p - (p - armwiseExtensionFormula ε (0 : Fin 4 → ℝ)))]
      _ = 2 * (∫ ω, (clippedCellValueFormula ε K d m b r (fun j => W j ω) - p) ^ 2 ∂μ) +
          2 * (p - armwiseExtensionFormula ε (0 : Fin 4 → ℝ)) ^ 2 := by
        rw [integral_add (hsint.const_mul 2) (integrable_const _), integral_const_mul]
        simp
      _ ≤ _ := by nlinarith [hsclip]


end CausalSmith.Stat.OptvalueVanishingoverlapRate
