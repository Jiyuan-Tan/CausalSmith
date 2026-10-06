module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperLocalizedClipping
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperPilotTail
public import Mathlib.Probability.Moments.Variance

/-! # Random pilots at null cells

The null-cell argument after roadmap (11) applies to the actual random pilot:
zero cell mass forces all four Poisson counts to vanish almost surely. This
transfers the calibrated zero-pilot bounds (20)/(28) to the random-pilot
statistic, without conditioning on a positive-probability pilot event.
-/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory ProbabilityTheory

-- @node: cellVector_eq_zero_of_cellMass_eq_zero
/-- Zero cell mass forces every observed atom in that cell to have zero mass. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hp), the [stated conclusion](goal) holds. -/
lemma cellVector_eq_zero_of_cellMass_eq_zero {d : ℕ} (P : DiscreteLaw d)
    (x : Fin d) (hp : cellMass P x = 0) : cellVector P x = 0 := by
  have ha (a : Bool) : (∑ y : Bool, jointMass P x a y) = 0 := by
    have h := (Finset.sum_eq_zero_iff_of_nonneg
      (fun a (_ : a ∈ Finset.univ) =>
        Finset.sum_nonneg (fun y _ => ENNReal.toReal_nonneg))).mp hp
    exact h a (Finset.mem_univ a)
  have hj (a y : Bool) : jointMass P x a y = 0 := by
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun y (_ : y ∈ Finset.univ) => ENNReal.toReal_nonneg)).mp (ha a)
        y (Finset.mem_univ y)
  funext j
  exact hj _ _

-- @node: nullCell_poissonCounts_ae_zero
/-- The marginal Poisson laws alone force the entire null-cell count vector to vanish almost surely; independence is unnecessary for this conclusion. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hp,hm,hW), the [stated conclusion](goal) holds. -/
lemma nullCell_poissonCounts_ae_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {d : ℕ} (P : DiscreteLaw d) (x : Fin d)
    (hp : cellMass P x = 0) (m : ℝ) (hm : 0 ≤ m) (W : Fin 4 → Ω → ℕ)
    (hW : ∀ j, HasLaw (W j)
      (poissonMeasure ⟨m * cellVector P x j,
        mul_nonneg hm ENNReal.toReal_nonneg⟩) μ) :
    (fun ω j => W j ω) =ᵐ[μ] (fun _ => 0) := by
  have hq := cellVector_eq_zero_of_cellMass_eq_zero P x hp
  have hz (j : Fin 4) : W j =ᵐ[μ] (fun _ => 0) := by
    have hrate : (⟨m * cellVector P x j,
        mul_nonneg hm ENNReal.toReal_nonneg⟩ : NNReal) = 0 := by
      ext
      simp [hq]
    have h := hW j
    rw [hrate] at h
    exact (h.ae_iff (by fun_prop)).mpr
      Causalean.Stat.Concentration.PoissonSelfNormalized.poissonMeasure_zero_ae
  filter_upwards [Filter.eventually_all.mpr hz] with ω hω
  funext j
  exact hω j

/-- A null cell is localized almost surely on the actual random pilot rectangle, including its lower boundary, as required in the paragraph after (11). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hp,hH,hm,hL,hNp), the [stated conclusion](goal) holds. -/
lemma nullCell_pilotRectangle_ae_contains {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {d : ℕ} (P : DiscreteLaw d) (x : Fin d)
    (hp : cellMass P x = 0) (H : ℝ) (hH : 0 < H) (m L : ℝ)
    (hm : 0 < m) (hL : 0 ≤ L) (Np : Fin 4 → Ω → ℕ)
    (hNp : ∀ j, HasLaw (Np j)
      (poissonMeasure ⟨m * cellVector P x j,
        mul_nonneg hm.le ENNReal.toReal_nonneg⟩) μ) :
    ∀ᵐ ω ∂μ, cellVector P x ∈ pilotRectangle
      (pilotLower H hH m L (fun j => Np j ω))
      (pilotUpperFormula H hH m L (fun j => Np j ω)) := by
  filter_upwards [nullCell_poissonCounts_ae_zero μ P x hp m hm.le Np hNp] with ω hω
  rw [hω, cellVector_eq_zero_of_cellMass_eq_zero P x hp]
  exact zeroPilot_rectangle_contains_zero H hH m L hm hL

/-- With both pilot and evaluation Poisson counts at a null cell, the actual clipped cell statistic is almost surely a deterministic constant. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hp,hH,hm,hNp,hNe), the [stated conclusion](goal) holds. -/
lemma nullCell_clippedCellValue_ae_constant {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {d : ℕ} (P : DiscreteLaw d) (x : Fin d)
    (hp : cellMass P x = 0) (H : ℝ) (hH : 0 < H) (m L ε : ℝ)
    (hm : 0 < m) (K : ℕ) (Np Ne : Fin 4 → Ω → ℕ)
    (hNp : ∀ j, HasLaw (Np j)
      (poissonMeasure ⟨m * cellVector P x j,
        mul_nonneg hm.le ENNReal.toReal_nonneg⟩) μ)
    (hNe : ∀ j, HasLaw (Ne j)
      (poissonMeasure ⟨m * cellVector P x j,
        mul_nonneg hm.le ENNReal.toReal_nonneg⟩) μ) :
    (fun ω => clippedCellValueFormula ε K d m
      (pilotMidpoint H hH m L (fun j => Np j ω))
      (pilotRadiusFormula H hH m L (fun j => Np j ω)) (fun j => Ne j ω)) =ᵐ[μ]
    (fun _ => clippedCellValueFormula ε K d m
      (pilotMidpoint H hH m L 0) (pilotRadiusFormula H hH m L 0) 0) := by
  filter_upwards [nullCell_poissonCounts_ae_zero μ P x hp m hm.le Np hNp,
    nullCell_poissonCounts_ae_zero μ P x hp m hm.le Ne hNe] with ω hωp hωe
  rw [hωp, hωe]

/-- Null cells contribute no variance to the independent-cell assembly (29). Their approximation bias need not vanish and is still controlled by (20). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hp,hH,hm,hNp,hNe), the [stated conclusion](goal) holds. -/
lemma nullCell_clippedCellValue_variance_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} (P : DiscreteLaw d) (x : Fin d)
    (hp : cellMass P x = 0) (H : ℝ) (hH : 0 < H) (m L ε : ℝ)
    (hm : 0 < m) (K : ℕ) (Np Ne : Fin 4 → Ω → ℕ)
    (hNp : ∀ j, HasLaw (Np j)
      (poissonMeasure ⟨m * cellVector P x j,
        mul_nonneg hm.le ENNReal.toReal_nonneg⟩) μ)
    (hNe : ∀ j, HasLaw (Ne j)
      (poissonMeasure ⟨m * cellVector P x j,
        mul_nonneg hm.le ENNReal.toReal_nonneg⟩) μ) :
    variance (fun ω => clippedCellValueFormula ε K d m
      (pilotMidpoint H hH m L (fun j => Np j ω))
      (pilotRadiusFormula H hH m L (fun j => Np j ω)) (fun j => Ne j ω)) μ = 0 := by
  rw [variance_congr
    (nullCell_clippedCellValue_ae_constant μ P x hp H hH m L ε hm K Np Ne hNp hNe)]
  simp [variance, evariance]

/-- The same universal degree tuning as (28) bounds the actual random-pilot null-cell mean and second moment. The marginal count laws derive the zero pilot, rather than imposing it as an extra localization assumption. In the econometric construction, no additional assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma nullCell_randomPilot_target_tuning_exists :
    ∃ κ A : ℝ, 0 < κ ∧ 0 < A ∧ ∀ {Ω : Type*} [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ}, 1 ≤ d →
      ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ (P : DiscreteLaw d) (x : Fin d),
      cellMass P x = 0 → ∀ (Np Ne : Fin 4 → Ω → ℕ)
      (H : ℝ) (hH : 0 < H), 1 ≤ H → ∀ (m : ℝ) (hm : 0 < m),
      (∀ j, HasLaw (Np j)
        (poissonMeasure ⟨m * cellVector P x j,
          mul_nonneg hm.le ENNReal.toReal_nonneg⟩) μ) →
      (∀ j, HasLaw (Ne j)
        (poissonMeasure ⟨m * cellVector P x j,
          mul_nonneg hm.le ENNReal.toReal_nonneg⟩) μ) →
      iIndepFun Ne μ →
      let b := fun ω => pilotMidpoint H hH m (logAlphabet d) (fun j => Np j ω)
      let r := fun ω => pilotRadiusFormula H hH m (logAlphabet d) (fun j => Np j ω)
      let K := jacksonDegree κ d
      let S := clippingScaleFormula ε (pilotMidpoint H hH m (logAlphabet d) 0)
        (pilotRadiusFormula H hH m (logAlphabet d) 0)
      let B := (64 * H / (κ / 2) ^ 2) * (1 / (m * ε * logAlphabet d))
      (|(∫ ω, clippedCellValueFormula ε K d m (b ω) (r ω) (fun j => Ne j ω) ∂μ) -
          armwiseExtensionFormula ε (cellVector P x)| ≤
        B + A * (d : ℝ) ^ (-(3 / 16 : ℝ)) * S) ∧
      ((∫ ω, (clippedCellValueFormula ε K d m (b ω) (r ω) (fun j => Ne j ω) -
          armwiseExtensionFormula ε (cellVector P x)) ^ 2 ∂μ) ≤
        2 * A * (d : ℝ) ^ (1 / 16 : ℝ) * S ^ 2 + 2 * B ^ 2) := by
  obtain ⟨κ, A, hκ, hA, hzero⟩ := zeroPilot_clippedCellValue_target_tuning_exists
  refine ⟨κ, A, hκ, hA, ?_⟩
  intro Ω _ μ _ d hd ε hε hε1 P x hp Np Ne H hH hHlarge m hm hNp hNe hind
  have hq := cellVector_eq_zero_of_cellMass_eq_zero P x hp
  have hNe0 : ∀ j, HasLaw (Ne j) (poissonMeasure 0) μ := by
    intro j
    have hrate : (⟨m * cellVector P x j,
        mul_nonneg hm.le ENNReal.toReal_nonneg⟩ : NNReal) = 0 := by
      ext
      simp [hq]
    have h := hNe j
    rw [hrate] at h
    exact h
  have hpilot := nullCell_poissonCounts_ae_zero μ P x hp m hm.le Np hNp
  dsimp only
  have heq :
      (fun ω => clippedCellValueFormula ε (jacksonDegree κ d) d m
        (pilotMidpoint H hH m (logAlphabet d) (fun j => Np j ω))
        (pilotRadiusFormula H hH m (logAlphabet d) (fun j => Np j ω)) (fun j => Ne j ω)) =ᵐ[μ]
      (fun ω => clippedCellValueFormula ε (jacksonDegree κ d) d m
        (pilotMidpoint H hH m (logAlphabet d) 0)
        (pilotRadiusFormula H hH m (logAlphabet d) 0) (fun j => Ne j ω)) := by
    filter_upwards [hpilot] with ω hω
    rw [hω]
  have hsq := heq.fun_comp (fun z => (z - armwiseExtensionFormula ε (cellVector P x)) ^ 2)
  dsimp only [Function.comp_def] at hsq
  rw [integral_congr_ae heq, integral_congr_ae hsq, hq]
  exact hzero μ hd ε hε hε1 Ne H hH hHlarge m hm hNe0 hind

end CausalSmith.Stat.OptvalueVanishingoverlapRate
