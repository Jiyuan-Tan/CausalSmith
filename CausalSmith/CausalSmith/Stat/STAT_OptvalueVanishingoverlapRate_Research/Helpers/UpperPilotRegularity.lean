module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperJacksonOscillation
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperPilotMoments
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperPilotTail
public import Mathlib.MeasureTheory.Function.L2Space

/-! # Unconditional pilot and clipped-cell regularity

The variance assembly in roadmap (29) requires square-integrable cell
statistics before splitting good and bad pilots. Marginal Poisson score
moments supply this regularity, even off the localization event. Clipping
removes any need for unconditional moments of the pilot-selected factorial
polynomial or independence between pilot and evaluation counts here.
-/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory ProbabilityTheory
open Causalean.Stat.Concentration.Poisson
open Causalean.Stat.Concentration.PoissonSelfNormalized
open Causalean.Stat.Concentration.Poisson.EmpiricalRadius
open scoped BigOperators NNReal


-- @node: pilotAggregateScore_memLp_two
/-- The aggregate pilot deviation-and-width score is square-integrable under its marginal Poisson laws, without a joint independence assumption. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:q,m,hm,hH,hL,hW,hlaw), the [stated conclusion](goal) holds. -/
lemma pilotAggregateScore_memLp_two {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (W : Fin 4 → Ω → ℕ) (q : Fin 4 → ℝ≥0)
    (m : ℝ≥0) (hm : 0 < m) (H L : ℝ) (hH : universalH ≤ H) (hL : 1 ≤ L)
    (hW : ∀ j, Measurable (W j))
    (hlaw : ∀ j, HasLaw (W j) (poissonMeasure (m * q j)) μ) :
    MemLp (empiricalAggregateScore W H L m q) 2 μ := by
  have hs : AEStronglyMeasurable (empiricalAggregateScore W H L m q) μ := by
    unfold empiricalAggregateScore normalizedDeviation empiricalRadius
    fun_prop
  exact (memLp_two_iff_integrable_sq hs).2
    (pilotAggregateScore_pow_integrable μ W q m hm H L hH hL hW hlaw 2
      (Or.inr (Or.inl rfl)))

/-- Total midpoint mass is square-integrable on the entire pilot space. The deterministic displacement bound dominates it by the true mass plus the aggregate score, so bad pilots are included. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:q,m,hm,hHpos,hH,hL,hW,hlaw), the [stated conclusion](goal) holds. -/
lemma pilotTotalMass_memLp_two {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Fin 4 → Ω → ℕ) (q : Fin 4 → ℝ≥0) (m : ℝ≥0) (hm : 0 < m)
    (H : ℝ) (hHpos : 0 < H) (L : ℝ) (hH : universalH ≤ H) (hL : 1 ≤ L)
    (hW : ∀ j, Measurable (W j))
    (hlaw : ∀ j, HasLaw (W j) (poissonMeasure (m * q j)) μ) :
    MemLp (fun ω => totalMassVecFormula (pilotMidpoint H hHpos m L (fun j => W j ω))) 2 μ := by
  have hscore := pilotAggregateScore_memLp_two μ W q m hm H L hH hL hW hlaw
  have hdom := (memLp_const (∑ j, (q j : ℝ)) (p := (2 : ENNReal)) (μ := μ)).add hscore
  apply hdom.of_le
  · first | fun_prop | exact ((Measurable.of_discrete (f := fun N : Fin 4 → ℕ =>
        totalMassVecFormula (pilotMidpoint H hHpos m L N))).comp
        (measurable_pi_lambda _ hW)).aestronglyMeasurable
  · apply ae_of_all
    intro ω
    have hb := pilotMidpoint_nonneg H hHpos m L (NNReal.coe_pos.mpr hm)
      (fun j => W j ω)
    have hB : 0 ≤ totalMassVecFormula (pilotMidpoint H hHpos m L (fun j => W j ω)) := by
      rw [totalMassVec_eq_sum_coordinates]
      exact Finset.sum_nonneg fun j _ => hb j
    have he := pilotMidpoint_total_abs_error_le_score W q m hm H hHpos L (by linarith) ω
    have hsum : totalMassVecFormula (pilotMidpoint H hHpos m L (fun j => W j ω)) -
        ∑ j, (q j : ℝ) ≤ ∑ j, |pilotMidpoint H hHpos m L (fun i => W i ω) j - q j| := by
      rw [totalMassVec_eq_sum_coordinates, ← Finset.sum_sub_distrib]
      exact Finset.sum_le_sum fun j _ => le_abs_self _
    rw [Real.norm_eq_abs, abs_of_nonneg hB, Real.norm_eq_abs]
    exact (show _ ≤ (∑ j, (q j : ℝ)) + empiricalAggregateScore W H L m q ω by
      linarith).trans (le_abs_self _)

/-- The random clipping scale has an integrable square on good and bad pilots. Its anchored-radius square envelope is affine in the integrable midpoint mass. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:q,m,hm,hHpos,hH,hL,hε,hε1,hW,hlaw), the [stated conclusion](goal) holds. -/
lemma pilotClippingScale_memLp_two {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Fin 4 → Ω → ℕ) (q : Fin 4 → ℝ≥0) (m : ℝ≥0) (hm : 0 < m)
    (H : ℝ) (hHpos : 0 < H) (L ε : ℝ) (hH : universalH ≤ H) (hL : 1 ≤ L)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hW : ∀ j, Measurable (W j))
    (hlaw : ∀ j, HasLaw (W j) (poissonMeasure (m * q j)) μ) :
    MemLp (fun ω => clippingScaleFormula ε (pilotMidpoint H hHpos m L (fun j => W j ω))
      (pilotRadiusFormula H hHpos m L (fun j => W j ω))) 2 μ := by
  have hB := (pilotTotalMass_memLp_two μ W q m hm H hHpos L hH hL hW hlaw).integrable
    (by norm_num : (1 : ENNReal) ≤ 2)
  have hmeas : AEStronglyMeasurable (fun ω => clippingScaleFormula ε
      (pilotMidpoint H hHpos m L (fun j => W j ω))
      (pilotRadiusFormula H hHpos m L (fun j => W j ω))) μ := by
    first | fun_prop | exact ((Measurable.of_discrete (f := fun N : Fin 4 → ℕ =>
        clippingScaleFormula ε (pilotMidpoint H hHpos m L N) (pilotRadiusFormula H hHpos m L N))).comp
        (measurable_pi_lambda _ hW)).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hmeas).2
  have hi := (((hB.mul_const (L / m)).div_const ε).add
    (integrable_const (((L / m) / ε) ^ 2))).const_mul (512 * H ^ 2)
  apply hi.mono' (hmeas.pow 2)
  apply ae_of_all
  intro ω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pilotClippingScale_sq_le H hHpos m L ε (NNReal.coe_pos.mpr hm)
    (by linarith) hε hε1 (fun j => W j ω)

/-- The actual clipped cell statistic is square-integrable for any measurable evaluation counts. Its random center and width dominate it pathwise, and both have already derived pilot moments; no evaluation moment gate is needed. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:q,m,hm,hHpos,hH,hL,hε,hε1,hW,hNe,hlaw), the [stated conclusion](goal) holds. -/
lemma pilotClippedCellValue_memLp_two {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W Ne : Fin 4 → Ω → ℕ) (q : Fin 4 → ℝ≥0) (m : ℝ≥0) (hm : 0 < m)
    (H : ℝ) (hHpos : 0 < H) (L ε : ℝ) (hH : universalH ≤ H) (hL : 1 ≤ L)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (K d : ℕ)
    (hW : ∀ j, Measurable (W j)) (hNe : ∀ j, Measurable (Ne j))
    (hlaw : ∀ j, HasLaw (W j) (poissonMeasure (m * q j)) μ) :
    MemLp (fun ω => clippedCellValueFormula ε K d m
      (pilotMidpoint H hHpos m L (fun j => W j ω))
      (pilotRadiusFormula H hHpos m L (fun j => W j ω)) (fun j => Ne j ω)) 2 μ := by
  have hB := pilotTotalMass_memLp_two μ W q m hm H hHpos L hH hL hW hlaw
  have hS := pilotClippingScale_memLp_two μ W q m hm H hHpos L ε hH hL hε hε1 hW hlaw
  have hdom := (hS.const_mul ((d : ℝ) ^ (1 / 4 : ℝ))).add hB
  apply hdom.of_le
  · first | fun_prop | exact ((Measurable.of_discrete (f := fun z : (Fin 4 → ℕ) × (Fin 4 → ℕ) =>
        clippedCellValueFormula ε K d m (pilotMidpoint H hHpos m L z.1)
          (pilotRadiusFormula H hHpos m L z.1) z.2)).comp
      ((measurable_pi_lambda _ hW).prodMk (measurable_pi_lambda _ hNe))).aestronglyMeasurable
  · apply ae_of_all
    intro ω
    let b := pilotMidpoint H hHpos m L (fun j => W j ω)
    let r := pilotRadiusFormula H hHpos m L (fun j => W j ω)
    have hb := pilotMidpoint_nonneg H hHpos m L (NNReal.coe_pos.mpr hm) (fun j => W j ω)
    have hr (j : Fin 4) : 0 ≤ r j :=
      (pilotRadius_pos H hHpos m L (NNReal.coe_pos.mpr hm) (by linarith) _ j).le
    have hs := clippingScale_nonneg ε b r hb hr
    have hw : 0 ≤ (d : ℝ) ^ (1 / 4 : ℝ) * clippingScaleFormula ε b r :=
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) hs
    have hf := armwiseExtension_nonneg_le_totalMassVec hε hb
    have ht := clippedCellValue_abs_error_le ε K d m b r (fun j => Ne j ω) 0 hw
    have hf0 : 0 ≤ armwiseExtensionFormula ε b := hf.1
    simp only [sub_zero, abs_of_nonneg hf0] at ht
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact (ht.trans (add_le_add le_rfl hf.2)).trans (le_abs_self _)

end CausalSmith.Stat.OptvalueVanishingoverlapRate
