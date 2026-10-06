/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.Limit.ConvergenceVec
public import Causalean.Stat.Limit.ContinuousMapping

/-! # Continuous mapping for random quadratic forms

This module provides two contact lemmas for weak-convergence proofs.  The first
allows the pushforward target produced by continuous mapping to be replaced by
an identified measure.  The second is a quadratic-form Slutsky theorem: an
operator converging in probability in operator norm may replace its limit
inside a quadratic form evaluated at a tight random vector.
-/

public section

namespace Causalean.Stat

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace

/-- Every [`o_P(1)` sequence](hyp:hA) is [bounded in probability](goal). -/
theorem IsLittleOp.isBigOp_one
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {A : ℕ → Ω → ℝ}
    (hA : IsLittleOp A (fun _ => (1 : ℝ)) μ) :
    IsBigOp A (fun _ => (1 : ℝ)) μ := by
  exact Modes.IsLittleOpF.boundedInProbability hA

/-- **Stochastic absorption.** Suppose [a nonnegative random coefficient is
`o_P(1)`](hyp:hA), [a nonnegative forcing sequence is `O_P(1)`](hyp:hB), and
[a nonnegative target sequence is eventually almost surely bounded by the forcing term plus
that small coefficient times the target itself](hyp:hbound), with the stated
[nonnegativity conditions](hyp:hA_nonneg,hB_nonneg,hY_nonneg). Then [the target
sequence is `O_P(1)`](goal). -/
theorem IsLittleOp.isBigOp_of_absorption
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {A B Y : ℕ → Ω → ℝ}
    (hA : IsLittleOp A (fun _ => (1 : ℝ)) μ)
    (hB : IsBigOp B (fun _ => (1 : ℝ)) μ)
    (hA_nonneg : ∀ n ω, 0 ≤ A n ω)
    (hB_nonneg : ∀ n ω, 0 ≤ B n ω)
    (hY_nonneg : ∀ n ω, 0 ≤ Y n ω)
    (hbound : ∀ᶠ n in atTop, ∀ᵐ ω ∂μ,
      Y n ω ≤ B n ω + A n ω * Y n ω) :
    IsBigOp Y (fun _ => (1 : ℝ)) μ := by
  intro δ hδ
  have hhalf : 0 < δ / 2 := ENNReal.div_pos hδ.ne' (by norm_num)
  rcases hB (δ / 2) hhalf with ⟨M, hM, hBevent⟩
  refine ⟨2 * M, mul_pos (by norm_num) hM, ?_⟩
  let Aevent : ℕ → Set Ω := fun n => {ω | (1 / 2 : ℝ) ≤ |A n ω|}
  let Bevent : ℕ → Set Ω := fun n => {ω | M ≤ |B n ω|}
  let Cevent : ℕ → Set Ω := fun n => {ω | 2 * M ≤ |Y n ω|}
  have hAt : Tendsto (fun n => μ (Aevent n)) atTop (𝓝 0) := by
    simpa [Aevent] using hA (1 / 2) (by norm_num)
  have hAevent := (ENNReal.tendsto_nhds_zero.mp hAt) (δ / 2) hhalf
  filter_upwards [hAevent, hBevent, hbound] with n hAn hBn hboundn
  have hsubset : ∀ᵐ ω ∂μ, ω ∈ Cevent n → ω ∈ Aevent n ∪ Bevent n := by
    filter_upwards [hboundn] with ω hboundω
    intro hω
    by_contra hnot
    have hnotA : ¬ (1 / 2 : ℝ) ≤ |A n ω| := by
      intro h
      exact hnot (Or.inl h)
    have hnotB : ¬ M ≤ |B n ω| := by
      intro h
      exact hnot (Or.inr h)
    have hAlt : A n ω < 1 / 2 := by
      rw [← abs_of_nonneg (hA_nonneg n ω)]
      exact lt_of_not_ge hnotA
    have hBlt : B n ω < M := by
      rw [← abs_of_nonneg (hB_nonneg n ω)]
      exact lt_of_not_ge hnotB
    have hYlt : Y n ω < 2 * M := by nlinarith [hY_nonneg n ω]
    have hYge : 2 * M ≤ Y n ω := by
      change 2 * M ≤ |Y n ω| at hω
      rwa [abs_of_nonneg (hY_nonneg n ω)] at hω
    exact (not_lt_of_ge hYge) hYlt
  have hBn' : μ (Bevent n) ≤ δ / 2 := by simpa [Bevent] using hBn
  calc
    μ {ω | (2 * M) * (fun _ => (1 : ℝ)) n ≤ |Y n ω|}
        = μ (Cevent n) := by simp [Cevent]
    _ ≤ μ (Aevent n ∪ Bevent n) := measure_mono_ae hsubset
    _ ≤ μ (Aevent n) + μ (Bevent n) := measure_union_le _ _
    _ ≤ δ / 2 + δ / 2 := add_le_add hAn hBn'
    _ = δ := ENNReal.add_halves δ

/-- **Continuous mapping with an identified target.** If [the random-element sequence is
measurable](hyp:hXn), [its elements converge weakly](hyp:hX), [the applied map is
continuous](hyp:hg), and
[the pushforward of the limiting law through that map is the named probability
law](hyp:hmap), then [the mapped random elements converge weakly to that named
law](goal). -/
theorem Tendsto_dist_vec.map_continuous_of_map_eq
    {Ω E F : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [PseudoMetricSpace F] [MeasurableSpace F] [BorelSpace F]
    {Xn : ℕ → Ω → E} {Q : Measure E} [IsProbabilityMeasure Q]
    {R : Measure F} [IsProbabilityMeasure R]
    {g : E → F} (hg : Continuous g)
    (hXn : ∀ n, AEMeasurable (Xn n) μ)
    (hX : Tendsto_dist_vec Xn Q μ hXn)
    (hmap : Q.map g = R) :
    Tendsto (β := ProbabilityMeasure F)
      (fun n =>
        ⟨μ.map (fun ω => g (Xn n ω)),
          Measure.isProbabilityMeasure_map
            (hg.measurable.aemeasurable.comp_aemeasurable (hXn n))⟩)
      atTop (𝓝 ⟨R, ‹IsProbabilityMeasure R›⟩) := by
  simpa [hmap] using hX.map_continuous hg hXn

/-- **Quadratic-form Slutsky theorem.** Suppose [a measurable vector sequence](hyp:hXn)
[converges weakly](hyp:hX), [a random continuous-linear operator family](hyp:An)
[converges in probability in operator norm](hyp:hA) to [a fixed operator](hyp:A), and [the random
quadratic forms are measurable](hyp:hQuadraticMeas). Then [the random quadratic
forms converge weakly to the pushforward of the vector limit through the fixed
quadratic form](goal). -/
theorem Tendsto_dist_vec.quadraticForm_of_operator_tendstoInProb
    {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {Xn : ℕ → Ω → E} {Q : Measure E} [IsProbabilityMeasure Q]
    (hXn : ∀ n, AEMeasurable (Xn n) μ)
    (hX : Tendsto_dist_vec Xn Q μ hXn)
    (An : ℕ → Ω → (E →L[ℝ] E)) (A : E →L[ℝ] E)
    (hA : Tendsto_inProb (fun n ω => ‖An n ω - A‖) (fun _ => 0) μ)
    (hQuadraticMeas : ∀ n,
      AEMeasurable (fun ω => ⟪An n ω (Xn n ω), Xn n ω⟫) μ) :
    Tendsto (β := ProbabilityMeasure ℝ)
      (fun n =>
        ⟨μ.map (fun ω => ⟪An n ω (Xn n ω), Xn n ω⟫),
          Measure.isProbabilityMeasure_map (hQuadraticMeas n)⟩)
      atTop
      (𝓝 ⟨Q.map (fun x => ⟪A x, x⟫),
        Measure.isProbabilityMeasure_map
          ((A.continuous.inner continuous_id).measurable.aemeasurable)⟩) := by
  let q : E → ℝ := fun x => ⟪A x, x⟫
  have hq : Continuous q := A.continuous.inner continuous_id
  have hqXn : ∀ n, AEMeasurable (fun ω => q (Xn n ω)) μ := fun n =>
    hq.measurable.aemeasurable.comp_aemeasurable (hXn n)
  letI : IsProbabilityMeasure (Q.map q) :=
    Measure.isProbabilityMeasure_map hq.measurable.aemeasurable
  have hfixed : Tendsto_dist (fun n ω => q (Xn n ω)) (Q.map q) μ hqXn := by
    exact (Tendsto_dist_iff _ _ _ hqXn).2 (hX.map_continuous hq hXn)
  have hnormMeas : ∀ n, AEMeasurable (fun ω => ‖Xn n ω‖) μ := fun n =>
    continuous_norm.measurable.aemeasurable.comp_aemeasurable (hXn n)
  letI : IsProbabilityMeasure (Q.map norm) :=
    Measure.isProbabilityMeasure_map continuous_norm.measurable.aemeasurable
  have hnormDist : Tendsto_dist (fun n ω => ‖Xn n ω‖) (Q.map norm) μ hnormMeas := by
    exact (Tendsto_dist_iff _ _ _ hnormMeas).2
      (hX.map_continuous continuous_norm hXn)
  have hnormBig : IsBigOp (fun n ω => ‖Xn n ω‖) (fun _ => (1 : ℝ)) μ := by
    exact Tendsto_dist.tightness hnormMeas hnormDist
  have hnormSqBig : IsBigOp (fun n ω => ‖Xn n ω‖ * ‖Xn n ω‖)
      (fun _ => (1 : ℝ)) μ := by
    simpa only [one_mul] using Modes.BoundedInProbability.mul hnormBig hnormBig
      (Eventually.of_forall fun _ => zero_lt_one)
      (Eventually.of_forall fun _ => zero_lt_one)
  have hdeltaLittle : IsLittleOp (fun n ω => ‖An n ω - A‖)
      (fun _ => (1 : ℝ)) μ := hA.isLittleOp_one
  have hproductLittle : IsLittleOp
      (fun n ω => ‖An n ω - A‖ * (‖Xn n ω‖ * ‖Xn n ω‖))
      (fun _ => (1 : ℝ)) μ := by
    simpa using hdeltaLittle.mul_isBigOp
      (Eventually.of_forall fun _ => zero_lt_one)
      (Eventually.of_forall fun _ => zero_lt_one) hnormSqBig
  have hrem : IsLittleOp
      (fun n ω => ⟪An n ω (Xn n ω), Xn n ω⟫ - q (Xn n ω))
      (fun _ => (1 : ℝ)) μ := by
    refine IsLittleOp.of_abs_le_const_mul_one (C := 1) zero_lt_one hproductLittle ?_
    intro n ω
    rw [one_mul, abs_of_nonneg (mul_nonneg (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)))]
    calc
      |⟪An n ω (Xn n ω), Xn n ω⟫ - q (Xn n ω)|
          = |⟪(An n ω - A) (Xn n ω), Xn n ω⟫| := by
              simp only [q, sub_apply, inner_sub_left]
      _ ≤ ‖(An n ω - A) (Xn n ω)‖ * ‖Xn n ω‖ :=
            abs_real_inner_le_norm _ _
      _ ≤ ‖An n ω - A‖ * (‖Xn n ω‖ * ‖Xn n ω‖) := by
            calc
              ‖(An n ω - A) (Xn n ω)‖ * ‖Xn n ω‖
                  ≤ (‖An n ω - A‖ * ‖Xn n ω‖) * ‖Xn n ω‖ := by
                    gcongr
                    exact (An n ω - A).le_opNorm (Xn n ω)
              _ = ‖An n ω - A‖ * (‖Xn n ω‖ * ‖Xn n ω‖) := by ring
  exact (Tendsto_dist_iff _ _ _ hQuadraticMeas).1
    (Tendsto_dist_vec.add_isLittleOp_one hqXn hQuadraticMeas hfixed
      (IsLittleOp.of_abs_le_const_mul_one (C := 1) one_pos hrem
        (by intro n omega; simp [Real.norm_eq_abs])))

end Causalean.Stat
