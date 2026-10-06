module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperMarkedAssembly
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperNullPilot

/-! # Null-cell loss without factorial inflation

At a null cell both count vectors vanish almost surely. The factorial lift
then equals its Jackson mean, which is inside the clipping interval. Thus
only the null-corner approximation error remains in roadmap (20)/(28).
-/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open scoped BigOperators NNReal

/-- At a null cell clipping has no displacement or stochastic inflation: the random-pilot loss is bounded by the null-corner Jackson error alone. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hd,hp,hH,hm,hL,hε,hε1,hK,hκ,hdegree,hNp,hNe,hind), the [stated conclusion](goal) holds. -/
lemma nullCell_clippedCellValue_ae_error_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} (hd : 1 ≤ d)
    (P : DiscreteLaw d) (x : Fin d) (hp : cellMass P x = 0)
    (H : ℝ) (hH : 0 < H) (m L ε : ℝ) (hm : 0 < m) (hL : 0 < L)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (K : ℕ) (hK : 0 < K)
    (κ : ℝ) (hκ : 0 < κ) (hdegree : κ * L ≤ K)
    (Np Ne : Fin 4 → Ω → ℕ)
    (hNp : ∀ j, HasLaw (Np j)
      (poissonMeasure ⟨m * cellVector P x j,
        mul_nonneg hm.le ENNReal.toReal_nonneg⟩) μ)
    (hNe : ∀ j, HasLaw (Ne j)
      (poissonMeasure ⟨m * cellVector P x j,
        mul_nonneg hm.le ENNReal.toReal_nonneg⟩) μ)
    (hind : iIndepFun Ne μ) :
    ∀ᵐ ω ∂μ, |clippedCellValueFormula ε K d m
      (pilotMidpoint H hH m L (fun j => Np j ω))
      (pilotRadiusFormula H hH m L (fun j => Np j ω)) (fun j => Ne j ω) -
        armwiseExtensionFormula ε (cellVector P x)| ≤
      (64 * H / κ ^ 2) * (1 / (m * ε * L)) := by
  let b := pilotMidpoint H hH m L (fun _ => 0)
  let r := pilotRadiusFormula H hH m L (fun _ => 0)
  let p := armwiseExtensionFormula ε b + ∑ α : Fin 4 → Fin (2 * (K - 1) + 1),
    jacksonCoeff ε K b r α * ∏ j, ((0 - b j) / r j) ^ (α j).val
  have hq := cellVector_eq_zero_of_cellMass_eq_zero P x hp
  have hep := nullCell_poissonCounts_ae_zero μ P x hp m hm.le Np hNp
  have hee := nullCell_poissonCounts_ae_zero μ P x hp m hm.le Ne hNe
  have hmean := factorialCellValue_integral_eq_scaled μ Ne (cellVector P x)
    (fun _ => ENNReal.toReal_nonneg) m hm hNe hind ε K b r
  have hraw : factorialCellValue ε K m b r 0 = p := by
    have he : (fun ω => factorialCellValue ε K m b r (fun j => Ne j ω)) =ᵐ[μ]
        (fun _ => factorialCellValue ε K m b r 0) := by
      filter_upwards [hee] with ω hω
      rw [hω]
    rw [integral_congr_ae he] at hmean
    simpa [hq, p] using hmean
  have hmem := pilotJackson_mean_mem_clipping_interval H hH m L hm hL
    (fun _ => 0) ε hε K d hK hd (0 : Fin 4 → ℝ)
    (zeroPilot_rectangle_contains_zero H hH m L hm hL.le)
  change 0 ≤ (d : ℝ) ^ (1 / 4 : ℝ) * clippingScaleFormula ε b r ∧
    |p - armwiseExtensionFormula ε b| ≤ (d : ℝ) ^ (1 / 4 : ℝ) * clippingScaleFormula ε b r at hmem
  have hclip : clippedCellValueFormula ε K d m b r 0 = p := by
    rw [clippedCellValueFormula, hraw]
    rw [min_eq_right (by linarith [(abs_le.mp hmem.2).2]),
      max_eq_right (by linarith [(abs_le.mp hmem.2).1])]
  have hb := zeroPilot_jacksonCoeff_mean_normalized_le H hH m L hm hL
    ε hε hε1 K hK κ hκ hdegree
  filter_upwards [hep, hee] with ω hωp hωe
  rw [hωp, hωe, hq]
  change |clippedCellValueFormula ε K d m b r 0 - armwiseExtensionFormula ε 0| ≤ _
  rw [hclip]
  exact hb


-- @node: markedPoissonEvaluation_iIndepFun
/-- Evaluation coordinates of one implemented marked cell are independent; this specializes the independent marked histogram to the false mark. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma markedPoissonEvaluation_iIndepFun {d : ℕ} (P : DiscreteLaw d) (n : ℕ)
    (x : Fin d) :
    iIndepFun (fun j : Fin 4 => fun s :
      FiniteSample (Obs d × Bool) =>
      markedCount (le_refl s.1) (fun i => (s.2 i).1) (fun i => (s.2 i).2) false x j)
      (finitePoissonSampleLaw
        (P.pmf.toMeasure.prod (Causalean.Mathlib.Probability.bernoulliBool (1 / 2)))
        ((n : ℝ≥0) / 4)) := by
  let g : Fin 4 → Obs d × Bool := fun j =>
    ((x, decide (j.val / 2 = 1), decide (j.val % 2 = 1)), false)
  have hg : Function.Injective g := by
    intro j k hjk
    fin_cases j <;> fin_cases k <;> simp_all [g]
  simp_rw [markedCount_eq_markedPoissonHistogram]
  exact (markedPoissonHistogram_iIndepFun P n).precomp hg

/-- The actual null-cell statistic satisfies the normalized approximation bound almost surely for every positive degree coefficient. All count-law and independence inputs are supplied by the implemented marked experiment. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hn,hd,hp,hH,hκ,hε,hε1), the [stated conclusion](goal) holds. -/
lemma markedPoissonCellValue_null_ae_error_le {n d : ℕ} (hn : 1 ≤ n) (hd : 1 ≤ d)
    (P : DiscreteLaw d) (x : Fin d) (hp : cellMass P x = 0)
    (H : ℝ) (hH : 0 < H) (κ ε : ℝ) (hκ : 0 < κ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let μ := finitePoissonSampleLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
      ((n : ℝ≥0) / 4)
    ∀ᵐ s ∂μ, |markedPoissonCellValue n d H hH κ ε x s -
      armwiseExtensionFormula ε (cellVector P x)| ≤
      (64 * H / (κ / 2) ^ 2) * (1 / (poissonIntensityFormula n * ε * logAlphabet d)) := by
  let μ := finitePoissonSampleLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
    ((n : ℝ≥0) / 4)
  let W : Bool → Fin 4 → FiniteSample (Obs d × Bool) → ℕ := fun a j s =>
    markedCount (le_refl s.1) (fun i => (s.2 i).1) (fun i => (s.2 i).2) a x j
  have hm : 0 < poissonIntensityFormula n := by unfold poissonIntensityFormula; positivity
  have hlaw (a : Bool) (j : Fin 4) : HasLaw (W a j)
      (poissonMeasure ⟨poissonIntensityFormula n * cellVector P x j,
        mul_nonneg hm.le ENNReal.toReal_nonneg⟩) μ := by
    convert markedCount_poisson_hasLaw P n a x j using 1
    congr 1
  have ht := nullCell_clippedCellValue_ae_error_le μ hd P x hp H hH
    (poissonIntensityFormula n) (logAlphabet d) ε hm (logAlphabet_pos hd) hε hε1
    (jacksonDegree κ d) (by unfold jacksonDegree; omega) (κ / 2) (by positivity)
    (jacksonDegree_ge_half_log κ d) (W true) (W false) (hlaw true) (hlaw false)
    (markedPoissonEvaluation_iIndepFun P n x)
  exact ht

open Classical in
/-- Both good-pilot content estimates for an implemented null cell hold without a scale-moment or factorial-inflation term. Only the squared Jackson approximation scale remains in the second moment. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hn,hd,hp,hH,hκ,hε,hε1), the [stated conclusion](goal) holds. -/
lemma markedPoissonCellValue_null_good_moments_le {n d : ℕ}
    (hn : 1 ≤ n) (hd : 1 ≤ d) (P : DiscreteLaw d) (x : Fin d)
    (hp : cellMass P x = 0) (H : ℝ) (hH : 0 < H)
    (κ ε : ℝ) (hκ : 0 < κ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let μ := finitePoissonSampleLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
      ((n : ℝ≥0) / 4)
    let B := (64 * H / (κ / 2) ^ 2) *
      (1 / (poissonIntensityFormula n * ε * logAlphabet d))
    (∫ s, if s ∈ markedPoissonGoodPilot n P H hH x then
      (markedPoissonCellValue n d H hH κ ε x s -
        armwiseExtensionFormula ε (cellVector P x)) ^ 2 else 0 ∂μ) ≤ B ^ 2 ∧
    |∫ s, if s ∈ markedPoissonGoodPilot n P H hH x then
      markedPoissonCellValue n d H hH κ ε x s -
        armwiseExtensionFormula ε (cellVector P x) else 0 ∂μ| ≤ B := by
  classical
  dsimp only
  let μ := finitePoissonSampleLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
    ((n : ℝ≥0) / 4)
  let B := (64 * H / (κ / 2) ^ 2) *
    (1 / (poissonIntensityFormula n * ε * logAlphabet d))
  have hm : 0 < poissonIntensityFormula n := by unfold poissonIntensityFormula; positivity
  have hL := logAlphabet_pos hd
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have he := markedPoissonCellValue_null_ae_error_le hn hd P x hp H hH κ ε hκ hε hε1
  constructor
  · apply (integral_mono_of_nonneg (ae_of_all μ (fun s => by
      split_ifs <;> positivity)) (integrable_const (B ^ 2)) ?_).trans_eq (by simp [B])
    filter_upwards [he] with s hs
    split_ifs
    · have hsq := pow_le_pow_left₀ (abs_nonneg _) hs 2
      simpa only [sq_abs] using hsq
    · exact sq_nonneg B
  · apply abs_integral_le_integral_abs.trans
    apply (integral_mono_of_nonneg (ae_of_all μ (fun _ => abs_nonneg _))
      (integrable_const B) ?_).trans_eq (by simp [B])
    filter_upwards [he] with s hs
    split_ifs
    · exact hs
    · simpa only [abs_zero] using hB

end CausalSmith.Stat.OptvalueVanishingoverlapRate
