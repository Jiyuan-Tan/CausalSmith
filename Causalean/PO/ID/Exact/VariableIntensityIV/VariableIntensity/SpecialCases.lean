/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Variable-intensity instrumental variables

A directed-pair Wald specialization of the Angrist--Imbens causal-response
algebra for finite ordered treatment intensities: one directed instrument
contrast identifies an average causal response over the treatment-intensity
margins crossed by that contrast. This file does not derive the paper's general
population 2SLS characterization for multivalued instruments.
-/

module

public import Causalean.Mathlib.Probability.FiniteCellConditionalMomentBridge
public import Causalean.PO.ID.Exact.VariableIntensityIV.VariableIntensity.Identification

/-! # Variable-intensity IV special cases and linear-score interfaces

This part gives binary-treatment and constant-response specializations and defines interfaces for
a linear-score moment ratio and a supplied signed-contrast decomposition. -/

@[expose] public section

open Causalean.Mathlib.Probability

namespace Causalean
namespace PO.ID.Exact
namespace VariableIntensityIV

open Finset MeasureTheory ProbabilityTheory

noncomputable section

namespace VariableIntensityIVSystem

variable {P : POSystem} {𝒵 : Type*} [MeasurableSpace 𝒵]
variable [Fintype 𝒵] [MeasurableSingletonClass 𝒵]
variable {J : ℕ} (S : VariableIntensityIVSystem P 𝒵 J)

namespace SpecialCases

/-- [The unique binary-treatment margin](goal) is the sole adjacent dose increment when [the
ordered treatment scale has exactly one margin](hyp:hBinaryIntensity). -/
def binaryMargin (hBinaryIntensity : J = 1) : Fin J :=
  hBinaryIntensity.symm ▸ (0 : Fin 1)

/-- **Binary-intensity specialization: Wald recovers LATE.** Under [the
variable-intensity IV validity assumptions](hyp:hValid), with [positive probability of the
instrument cell `Z = z0`](hyp:hCell0), [positive probability of the instrument cell
`Z = z1`](hyp:hCell1), and [a single treatment margin, `J = 1`](hyp:hBinaryIntensity), [the
directed Wald estimand equals the conditional mean unit causal response given the unique
crossing event — the classical binary-treatment local average treatment effect](goal). -/
theorem wald_eq_late_of_binaryIntensity {z0 z1 : 𝒵}
    (hValid : S.ValidContrastAssumptions z0 z1)
    (hCell0 : 0 < (P.μ (S.zEvent z0)).toReal)
    (hCell1 : 0 < (P.μ (S.zEvent z1)).toReal)
    (hBinaryIntensity : J = 1) :
    S.wald z0 z1 =
      normalizedRestrictedIntegral P.μ
        (S.crossingEvent z0 z1 (binaryMargin hBinaryIntensity))
        (S.marginResponse (binaryMargin hBinaryIntensity)) := by
  subst hBinaryIntensity
  rw [S.directedPairWald_eq_averageCausalResponse hValid hCell0 hCell1]
  have hweight : S.crossingWeight z0 z1 0 = 1 := by
    simpa using S.sum_crossingWeight_eq_one hValid
  simp [averageCausalResponse, binaryMargin, conditionalMarginResponse, hweight]

/-- [With a single treatment margin, the crossing subgroup is exactly the classical complier
population that moves from zero to the maximum treatment level](goal) in [the variable-intensity
IV system](hyp:S), for [the two instrument values](hyp:z0,z1) under [the binary-scale
condition](hyp:hJ). -/
lemma crossingEvent_eq_complianceEvent (z0 z1 : 𝒵) (hJ : J = 1) :
    S.crossingEvent z0 z1 (binaryMargin hJ) =
      {ω | S.DofZ z1 ω = Fin.last J ∧ S.DofZ z0 ω = (0 : Fin (J + 1))} := by
  subst hJ
  ext ω
  simp only [binaryMargin, crossingEvent, OrderedTreatment.Crossing,
    OrderedTreatment.upperLevel, Set.mem_setOf_eq, Fin.last]
  have hone : (Fin.succ (0 : Fin 1)) = (⟨1, by omega⟩ : Fin 2) := by decide
  rw [hone]
  have hone_val : (⟨1, by omega⟩ : Fin 2).val = 1 := rfl
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨le_antisymm (Fin.le_last _) h1, Fin.ext ?_⟩
    have hv2 : (S.DofZ z0 ω).val < (⟨1, by omega⟩ : Fin 2).val :=
      Fin.val_fin_lt.mpr h2
    rw [hone_val] at hv2
    have hge : 0 ≤ (S.DofZ z0 ω).val := Nat.zero_le _
    simp only [Fin.val_zero]
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨h1 ▸ le_refl _, Fin.val_fin_lt.mp ?_⟩
    rw [hone_val]
    have hv2 : (S.DofZ z0 ω).val = (0 : Fin 2).val := congr_arg Fin.val h2
    simp only [Fin.val_zero] at hv2
    omega

/-- [The directed Wald estimand equals a common causal response shared by every treatment
margin](goal) under [the variable-intensity IV assumptions](hyp:hValid), [positive first
instrument-cell mass](hyp:hCell0), [positive second instrument-cell mass](hyp:hCell1), and [the
constant-response condition](hyp:τ,hConstantResponse).
The margin weights disappear because they sum to one. -/
theorem wald_eq_constantResponse {z0 z1 : 𝒵} {τ : ℝ}
    (hValid : S.ValidContrastAssumptions z0 z1)
    (hCell0 : 0 < (P.μ (S.zEvent z0)).toReal)
    (hCell1 : 0 < (P.μ (S.zEvent z1)).toReal)
    (hConstantResponse : ∀ j : Fin J, S.marginResponse j =ᵐ[P.μ] fun _ => τ) :
    S.wald z0 z1 = τ := by
  rw [S.directedPairWald_eq_averageCausalResponse hValid hCell0 hCell1]
  rw [← S.indicatorWeightedACR_eq_averageCausalResponse]
  unfold indicatorWeightedACR unnormalizedACRContrast totalCrossingProb indicatorWeightedEffect
    crossingProb
  have hterm : ∀ j : Fin J,
      (∫ ω in S.crossingEvent z0 z1 j, S.marginResponse j ω ∂P.μ) =
        τ * (P.μ (S.crossingEvent z0 z1 j)).toReal := by
    intro j
    rw [MeasureTheory.setIntegral_congr_ae (S.measurableSet_crossingEvent z0 z1 j)
      ((hConstantResponse j).mono fun _ hx _ => hx)]
    rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def]
    exact smul_eq_mul _ _ |>.trans (mul_comm _ _)
  rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.mul_sum]
  have hpos : 0 < ∑ j : Fin J, (P.μ (S.crossingEvent z0 z1 j)).toReal := by
    simpa [crossingProb] using (by
      rw [← S.firstStage_eq_sum_crossingProb hValid]
      exact hValid.hRelevance : 0 < ∑ j : Fin J, S.crossingProb z0 z1 j)
  field_simp [ne_of_gt hpos]

/-- **Margin-specific response average specialization.** For [a candidate margin-response
schedule](hyp:m), under [the variable-intensity IV validity assumptions](hyp:hValid), with
[positive probability of the instrument cell
`Z = z0`](hyp:hCell0), [positive probability of the instrument cell `Z = z1`](hyp:hCell1),
and [a candidate margin-response function `m` that agrees, on each treatment-intensity
margin, with the conditional mean causal response given that margin's crossing
event](hyp:hMarginResponse), [the directed Wald estimand equals the
crossing-probability-weighted average of `m` across margins](goal). -/
theorem wald_eq_marginResponseAverage {z0 z1 : 𝒵} (m : Fin J → ℝ)
    (hValid : S.ValidContrastAssumptions z0 z1)
    (hCell0 : 0 < (P.μ (S.zEvent z0)).toReal)
    (hCell1 : 0 < (P.μ (S.zEvent z1)).toReal)
    (hMarginResponse : ∀ j : Fin J, m j = S.conditionalMarginResponse z0 z1 j) :
    S.wald z0 z1 = ∑ j : Fin J, S.crossingWeight z0 z1 j * m j := by
  rw [S.directedPairWald_eq_averageCausalResponse hValid hCell0 hCell1]
  simp [averageCausalResponse, hMarginResponse]

end SpecialCases

/-- A linear-score IV moment-ratio specification for a variable-intensity IV system and score
dimension supplies [instrument-score coordinates](hyp:score),
[a coefficient vector](hyp:gammaD), [centered score coordinates](hyp:centered), and
[a nonzero score-treatment moment](hyp:denom_nonzero). -/
structure LinearScoreMomentSpec (k : ℕ) where
  /-- Instrument-score coordinate schedule. -/
  score : 𝒵 → Fin k → ℝ
  /-- User-supplied coefficient vector for the linear instrument score. -/
  gammaD : Fin k → ℝ
  /-- Every score coordinate has population mean zero. -/
  centered : ∀ r : Fin k, ∫ ω, score (S.factualZ ω) r ∂P.μ = 0
  /-- The linear-score--treatment moment is nonzero. -/
  denom_nonzero :
    ∫ ω, (∑ r : Fin k, gammaD r * score (S.factualZ ω) r) *
      OrderedTreatment.intensityValue (S.factualD ω) ∂P.μ ≠ 0

namespace LinearScoreMomentSpec

variable {S} (T : S.LinearScoreMomentSpec k)

/-- [The linear instrument-score combination](goal) weights the centered score coordinates in
[the supplied score specification](hyp:T) by its user-provided coefficient vector.

It is `D_S(ω) = γ_D^T S(Z(ω))`. -/
def linearCombination : P.Ω → ℝ :=
  fun ω => ∑ r : Fin k, T.gammaD r * T.score (S.factualZ ω) r

/-- [The linear-score IV moment ratio](goal) divides the score-outcome moment by the
score-treatment moment for [the supplied score and coefficient vector](hyp:T). The stored nonzero
condition makes this ratio well defined. -/
def momentRatio : ℝ :=
  (∫ ω, T.linearCombination ω * S.factualY ω ∂P.μ) /
    (∫ ω, T.linearCombination ω * OrderedTreatment.intensityValue (S.factualD ω) ∂P.μ)

end LinearScoreMomentSpec

/-- A supplied signed-pair decomposition for a linear-score moment-ratio specification records
[weights on ordered instrument-cell pairs](hyp:contrastWeight),
[denominator contributions](hyp:pairFirstStage), [numerator
contributions](hyp:pairReducedForm), and [stored numerator](hyp:reducedForm_decomp) and
[denominator](hyp:firstStage_decomp) expansions.

The contribution functions are not required to equal this module's pairwise reduced-form or
first-stage contrasts; only the displayed sum equalities are stored. -/
structure LinearScoreContrastDecomposition {k : ℕ} (T : S.LinearScoreMomentSpec k) where
  /-- Signed weight on an ordered instrument-cell contrast. -/
  contrastWeight : 𝒵 × 𝒵 → ℝ
  /-- Supplied denominator contribution attached to each ordered pair. -/
  pairFirstStage : 𝒵 × 𝒵 → ℝ
  /-- Supplied numerator contribution attached to each ordered pair. -/
  pairReducedForm : 𝒵 × 𝒵 → ℝ
  /-- The score-outcome numerator moment equals the supplied finite signed sum. -/
  reducedForm_decomp :
    ∫ ω, T.linearCombination ω * S.factualY ω ∂P.μ =
      ∑ p : 𝒵 × 𝒵, contrastWeight p * pairReducedForm p
  /-- The score-treatment denominator moment equals the supplied finite signed sum. -/
  firstStage_decomp :
    ∫ ω, T.linearCombination ω * OrderedTreatment.intensityValue (S.factualD ω) ∂P.μ =
      ∑ p : 𝒵 × 𝒵, contrastWeight p * pairFirstStage p

end VariableIntensityIVSystem
end
end VariableIntensityIV
end PO.ID.Exact
end Causalean
