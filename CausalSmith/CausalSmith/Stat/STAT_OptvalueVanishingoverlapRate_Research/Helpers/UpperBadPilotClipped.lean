module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperBadPilotCenter
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperBadPilotScale
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperClipping

/-! # Actual clipped-cell moments on failed pilot rectangles

The width and center estimates in roadmap (22) control the actual cell
statistic on bad pilots, as required after (28). Evaluation counts may be
arbitrary: clipping supplies the pathwise bound without evaluation moments.
-/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory ProbabilityTheory
open Causalean.Stat.Concentration.PoissonSelfNormalized
open Causalean.Stat.Concentration.Poisson.EmpiricalRadius
open scoped BigOperators NNReal

/-- The pilot center functional is square-integrable by domination by total midpoint mass. This regularity holds on failed rectangles as well. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:q,m,hm,hHpos,hH,hL,hε,hW,hlaw), the [stated conclusion](goal) holds. -/
lemma pilotCellValue_memLp_two {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Fin 4 → Ω → ℕ) (q : Fin 4 → ℝ≥0) (m : ℝ≥0) (hm : 0 < m)
    (H : ℝ) (hHpos : 0 < H) (L ε : ℝ) (hH : universalH ≤ H) (hL : 1 ≤ L)
    (hε : 0 < ε) (hW : ∀ j, Measurable (W j))
    (hlaw : ∀ j, HasLaw (W j) (poissonMeasure (m * q j)) μ) :
    MemLp (fun ω => armwiseExtensionFormula ε
      (pilotMidpoint H hHpos m L (fun j => W j ω))) 2 μ := by
  apply (pilotTotalMass_memLp_two μ W q m hm H hHpos L hH hL hW hlaw).of_le
  · first | fun_prop | exact ((Measurable.of_discrete (f := fun z : Fin 4 → ℕ =>
        armwiseExtensionFormula ε (pilotMidpoint H hHpos m L z))).comp
      (measurable_pi_lambda _ hW)).aestronglyMeasurable
  · apply ae_of_all
    intro ω
    have hb := pilotMidpoint_nonneg H hHpos m L (NNReal.coe_pos.mpr hm)
      (fun j => W j ω)
    have hf := armwiseExtension_nonneg_le_totalMassVec hε hb
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hf.1]
    exact hf.2.trans (le_abs_self _)

open Classical in
/-- On failed pilot rectangles, the actual clipped occupied-cell absolute error is exponentially small on the normalized mass and overlap scales of (22). No law or moment assumption on evaluation counts is needed. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hε,hε1,hP,hp,m,hm,hHpos,hH,hL,hW,hlaw,hind), the [stated conclusion](goal) holds. -/
lemma pilotRectangle_bad_clippedCellValue_integral_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d : ℕ} (ε : ℝ) (P : DiscreteLaw d) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hP : ObservedClass ε P) (x : Fin d) (hp : 0 < cellMass P x)
    (W : Fin 4 → Ω → ℕ) (Ne : Ω → Fin 4 → ℕ) (m : ℝ≥0) (hm : 0 < m)
    (H : ℝ) (hHpos : 0 < H) (L : ℝ) (hH : universalH ≤ H) (hL : 1 ≤ L)
    (hW : ∀ j, Measurable (W j))
    (hlaw : ∀ j, HasLaw (W j)
      (poissonMeasure (m * ⟨cellVector P x j, ENNReal.toReal_nonneg⟩)) μ)
    (hind : iIndepFun W μ) (K : ℕ) :
    (∫ ω, if cellVector P x ∉ pilotRectangle
        (pilotLower H hHpos m L (fun j => W j ω))
        (pilotUpperFormula H hHpos m L (fun j => W j ω)) then
      |clippedCellValueFormula ε K d m
        (pilotMidpoint H hHpos m L (fun j => W j ω))
        (pilotRadiusFormula H hHpos m L (fun j => W j ω)) (Ne ω) -
        armwiseExtensionFormula ε (cellVector P x)| else 0 ∂μ) ≤
      ((d : ℝ) ^ (1 / 4 : ℝ) * Real.sqrt (8 * (512 * H ^ 2 *
        (8 + 2 * (H / universalH) * productMomentConstant 4 1))) +
        Real.sqrt (8 * (1024 * Real.sqrt (8 * scalarMomentConstant 4) * (H / universalH) ^ 2))) *
        Real.exp (-30 * L) *
        (Real.sqrt (cellMass P x * L / (m * ε)) + L / (m * ε)) := by
  classical
  let q : Fin 4 → ℝ≥0 := fun j => ⟨cellVector P x j, ENNReal.toReal_nonneg⟩
  let B : Set Ω := {ω | cellVector P x ∉ pilotRectangle
    (pilotLower H hHpos m L (fun j => W j ω))
    (pilotUpperFormula H hHpos m L (fun j => W j ω))}
  let b : Ω → Fin 4 → ℝ := fun ω => pilotMidpoint H hHpos m L (fun j => W j ω)
  let r : Ω → Fin 4 → ℝ := fun ω => pilotRadiusFormula H hHpos m L (fun j => W j ω)
  have hB : MeasurableSet B := by
    dsimp [B]
    unfold pilotRectangle pilotLower pilotUpperFormula pilotHalfWidthFormula pilotCenterFormula
    measurability
  have hS := pilotClippingScale_memLp_two μ W q m hm H hHpos L ε hH hL hε hε1 hW hlaw
  have hF := (pilotCellValue_memLp_two μ W q m hm H hHpos L ε hH hL hε hW hlaw).sub
    (memLp_const (armwiseExtensionFormula ε (cellVector P x)))
  have hw (ω : Ω) (_ : ω ∈ B) :
      0 ≤ (d : ℝ) ^ (1 / 4 : ℝ) * clippingScaleFormula ε (b ω) (r ω) := by
    apply mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    exact clippingScale_nonneg ε _ _
      (pilotMidpoint_nonneg H hHpos m L (NNReal.coe_pos.mpr hm) _)
      (fun j => (pilotRadius_pos H hHpos m L (NNReal.coe_pos.mpr hm) (by linarith) _ j).le)
  have hmass : (∑ j, (q j : ℝ)) = cellMass P x := by
    change (∑ j, cellVector P x j) = cellMass P x
    simp [cellVector, cellMass, Fin.sum_univ_succ]
    ring
  have ht := clippedCellValue_integral_abs_on_le μ B b r Ne ε K d m
    (armwiseExtensionFormula ε (cellVector P x)) hw
    ((hS.integrable (by norm_num)).const_mul _).restrict
    (hF.abs.integrable (by norm_num)).restrict hB
  have hs := pilotRectangle_bad_clippingScale_integral_le μ W q m hm H hHpos L ε
    hH hL hε hε1 hW hlaw hind
  have hf := pilotRectangle_bad_cellValue_integral_le μ ε P hε hP x hp W m hm
    H hHpos L hH hL hW hlaw
  rw [hmass] at hs
  have hqfun : (fun j => (q j : ℝ)) = cellVector P x := rfl
  rw [hqfun] at hs
  rw [← integral_indicator hB] at ht
  rw [← integral_indicator hB, ← integral_indicator hB] at ht
  have hscale (ω : Ω) : B.indicator (fun ω =>
      (d : ℝ) ^ (1 / 4 : ℝ) * clippingScaleFormula ε (b ω) (r ω)) ω =
      (d : ℝ) ^ (1 / 4 : ℝ) *
        B.indicator (fun ω => clippingScaleFormula ε (b ω) (r ω)) ω := by
    by_cases h : ω ∈ B <;> simp [h]
  simp_rw [hscale] at ht
  rw [integral_const_mul] at ht
  simp only [Set.indicator, B, b, r, Set.mem_ofPred_eq] at ht
  have hsum := add_le_add (mul_le_mul_of_nonneg_left hs
    (Real.rpow_nonneg (Nat.cast_nonneg d) (1 / 4 : ℝ))) hf
  exact (ht.trans hsum).trans_eq (by ring)

open Classical in
/-- On failed pilot rectangles, the actual clipped occupied-cell loss is exponentially small on the normalized mass and overlap scales of (22). No law or moment assumption on evaluation counts is needed. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hε,hε1,hP,hp,m,hm,hHpos,hH,hL,hW,hlaw,hind), the [stated conclusion](goal) holds. -/
lemma pilotRectangle_bad_clippedCellValue_integral_sq_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d : ℕ} (ε : ℝ) (P : DiscreteLaw d) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hP : ObservedClass ε P) (x : Fin d) (hp : 0 < cellMass P x)
    (W : Fin 4 → Ω → ℕ) (Ne : Ω → Fin 4 → ℕ) (m : ℝ≥0) (hm : 0 < m)
    (H : ℝ) (hHpos : 0 < H) (L : ℝ) (hH : universalH ≤ H) (hL : 1 ≤ L)
    (hW : ∀ j, Measurable (W j))
    (hlaw : ∀ j, HasLaw (W j)
      (poissonMeasure (m * ⟨cellVector P x j, ENNReal.toReal_nonneg⟩)) μ)
    (hind : iIndepFun W μ) (K : ℕ) :
    (∫ ω, if cellVector P x ∉ pilotRectangle
        (pilotLower H hHpos m L (fun j => W j ω))
        (pilotUpperFormula H hHpos m L (fun j => W j ω)) then
      (clippedCellValueFormula ε K d m
        (pilotMidpoint H hHpos m L (fun j => W j ω))
        (pilotRadiusFormula H hHpos m L (fun j => W j ω)) (Ne ω) -
        armwiseExtensionFormula ε (cellVector P x)) ^ 2 else 0 ∂μ) ≤
      2 * (((d : ℝ) ^ (1 / 4 : ℝ)) ^ 2 * (512 * H ^ 2 *
        (8 + 2 * (H / universalH) * productMomentConstant 4 1)) +
        (1024 * Real.sqrt (8 * scalarMomentConstant 4) * (H / universalH) ^ 2)) *
        Real.exp (-20 * L) *
        (cellMass P x * L / (m * ε) + L ^ 2 / ((m : ℝ) ^ 2 * ε ^ 2)) := by
  classical
  let q : Fin 4 → ℝ≥0 := fun j => ⟨cellVector P x j, ENNReal.toReal_nonneg⟩
  let B : Set Ω := {ω | cellVector P x ∉ pilotRectangle
    (pilotLower H hHpos m L (fun j => W j ω))
    (pilotUpperFormula H hHpos m L (fun j => W j ω))}
  let b : Ω → Fin 4 → ℝ := fun ω => pilotMidpoint H hHpos m L (fun j => W j ω)
  let r : Ω → Fin 4 → ℝ := fun ω => pilotRadiusFormula H hHpos m L (fun j => W j ω)
  have hB : MeasurableSet B := by
    dsimp [B]
    unfold pilotRectangle pilotLower pilotUpperFormula pilotHalfWidthFormula pilotCenterFormula
    measurability
  have hS := pilotClippingScale_memLp_two μ W q m hm H hHpos L ε hH hL hε hε1 hW hlaw
  have hF := (pilotCellValue_memLp_two μ W q m hm H hHpos L ε hH hL hε hW hlaw).sub
    (memLp_const (armwiseExtensionFormula ε (cellVector P x)))
  have hw (ω : Ω) (_ : ω ∈ B) :
      0 ≤ (d : ℝ) ^ (1 / 4 : ℝ) * clippingScaleFormula ε (b ω) (r ω) := by
    apply mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    exact clippingScale_nonneg ε _ _
      (pilotMidpoint_nonneg H hHpos m L (NNReal.coe_pos.mpr hm) _)
      (fun j => (pilotRadius_pos H hHpos m L (NNReal.coe_pos.mpr hm) (by linarith) _ j).le)
  have hmass : (∑ j, (q j : ℝ)) = cellMass P x := by
    change (∑ j, cellVector P x j) = cellMass P x
    simp [cellVector, cellMass, Fin.sum_univ_succ]
    ring
  have hiS := (memLp_two_iff_integrable_sq hS.aestronglyMeasurable).1 hS
  have hiF := (memLp_two_iff_integrable_sq hF.aestronglyMeasurable).1 hF
  have ht := clippedCellValue_integral_sq_on_le μ B b r Ne ε K d m
    (armwiseExtensionFormula ε (cellVector P x)) hw
    (by simpa only [mul_pow] using (hiS.const_mul (((d : ℝ) ^ (1 / 4 : ℝ)) ^ 2)).restrict)
    hiF.restrict hB
  have hs := pilotRectangle_bad_clippingScale_normalized_le μ W q m hm H hHpos L ε
    hH hL hε hε1 hW hlaw hind
  have hf := pilotRectangle_bad_cellValue_normalized_le μ ε P hε hP x hp W m hm
    H hHpos L hH hL hW hlaw
  rw [hmass] at hs
  have hqfun : (fun j => (q j : ℝ)) = cellVector P x := rfl
  rw [hqfun] at hs
  rw [← integral_indicator hB] at ht
  rw [← integral_indicator hB, ← integral_indicator hB] at ht
  have hscale (ω : Ω) : B.indicator (fun ω =>
      ((d : ℝ) ^ (1 / 4 : ℝ) * clippingScaleFormula ε (b ω) (r ω)) ^ 2) ω =
      ((d : ℝ) ^ (1 / 4 : ℝ)) ^ 2 *
        B.indicator (fun ω => clippingScaleFormula ε (b ω) (r ω) ^ 2) ω := by
    by_cases h : ω ∈ B <;> simp [h, mul_pow]
  simp_rw [hscale] at ht
  rw [integral_const_mul] at ht
  simp only [Set.indicator, B, b, r, Set.mem_ofPred_eq] at ht
  have hsum := add_le_add (mul_le_mul_of_nonneg_left hs (sq_nonneg ((d : ℝ) ^ (1 / 4 : ℝ)))) hf
  have hb := mul_le_mul_of_nonneg_left hsum (show (0 : ℝ) ≤ 2 by norm_num)
  rw [← mul_add] at ht
  exact (ht.trans hb).trans_eq (by ring)

end CausalSmith.Stat.OptvalueVanishingoverlapRate
