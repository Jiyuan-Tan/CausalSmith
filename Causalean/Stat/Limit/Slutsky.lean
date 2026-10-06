/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.Limit.ContinuousMapping
public import Causalean.Stat.Limit.ConvergenceVec

/-!
# Random-multiplier Slutsky lemmas

This module supplies the two scalar forms of Slutsky's theorem used in
asymptotic statistics.  A random sequence converging in probability to a
constant may be added to, or multiplied by, a sequence converging in
distribution.  The proofs reduce the random part to an `o_p(1)` perturbation
and use the project's tightness and Slutsky-absorption lemmas.
-/

public section

namespace Causalean.Stat

open MeasureTheory Filter Topology

/-- **Additive Slutsky theorem.** Suppose [`Xn` and `Yn` are measurable at every sample
size](hyp:hXn,hYn), [`Xn` converges in distribution to `Q`](hyp:hX), and [`Yn` converges
in probability to the constant `c`](hyp:hY). Then [`Xn + Yn` converges in distribution
to the pushforward of `Q` by addition of `c`](goal).

This is the additive random-perturbation conclusion in van der Vaart, Lemma 2.8. -/
theorem Tendsto_dist.add_tendstoInProbability_const
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Xn Yn : ℕ → Ω → ℝ} {Q : Measure ℝ} [IsProbabilityMeasure Q] {c : ℝ}
    (hXn : ∀ n, AEMeasurable (Xn n) μ)
    (hYn : ∀ n, AEMeasurable (Yn n) μ)
    (hX : Tendsto_dist Xn Q μ hXn)
    (hY : Tendsto_inProb Yn (fun _ => c) μ) :
    @Tendsto_dist Ω _ (fun n ω => Xn n ω + Yn n ω)
      (Q.map fun x => x + c) μ _
      (Measure.isProbabilityMeasure_map
        (measurable_id.add measurable_const).aemeasurable)
      (fun n => (hXn n).add (hYn n)) := by
  have hBaseMeas : ∀ n, AEMeasurable (fun ω => Xn n ω + c) μ := fun n =>
    (hXn n).add aemeasurable_const
  letI : IsProbabilityMeasure (Q.map fun x : ℝ => x + c) :=
    Measure.isProbabilityMeasure_map (measurable_id.add measurable_const).aemeasurable
  have hBase : Tendsto_dist (fun n ω => Xn n ω + c) (Q.map fun x => x + c) μ hBaseMeas := by
    exact (Tendsto_dist_iff _ _ _ hBaseMeas).2
      (Tendsto_dist_vec.map_continuous (continuous_id.add continuous_const) hXn hX)
  have hRem : IsLittleOp (fun n ω => Yn n ω - c) (fun _ => (1 : ℝ)) μ :=
    (Tendsto_inProb.sub_const hY).isLittleOp_one
  apply Tendsto_dist_vec.add_isLittleOp_one hBaseMeas
    (fun n => (hXn n).add (hYn n)) hBase
  refine IsLittleOp.of_abs_le_const_mul_one (C := 1) one_pos hRem ?_
  intro n ω
  simp [Real.norm_eq_abs]

/-- **Multiplicative Slutsky theorem.** Suppose [`Xn` and `Yn` are measurable at every
sample size](hyp:hXn,hYn), [`Xn` converges in distribution to `Q`](hyp:hX), and [`Yn`
converges in probability to the constant `c`](hyp:hY). Then [`Xn * Yn` converges in
distribution to the pushforward of `Q` by multiplication by `c`](goal).

This is the random-multiplier conclusion in van der Vaart, Lemma 2.8. -/
theorem Tendsto_dist.mul_tendstoInProbability_const
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Xn Yn : ℕ → Ω → ℝ} {Q : Measure ℝ} [IsProbabilityMeasure Q] {c : ℝ}
    (hXn : ∀ n, AEMeasurable (Xn n) μ)
    (hYn : ∀ n, AEMeasurable (Yn n) μ)
    (hX : Tendsto_dist Xn Q μ hXn)
    (hY : Tendsto_inProb Yn (fun _ => c) μ) :
    @Tendsto_dist Ω _ (fun n ω => Xn n ω * Yn n ω)
      (Q.map fun x => c * x) μ _
      (Measure.isProbabilityMeasure_map
        (measurable_const.mul measurable_id).aemeasurable)
      (fun n => (hXn n).mul (hYn n)) := by
  have hBaseMeas : ∀ n, AEMeasurable (fun ω => c * Xn n ω) μ := fun n =>
    aemeasurable_const.mul (hXn n)
  letI : IsProbabilityMeasure (Q.map fun x : ℝ => c * x) :=
    Measure.isProbabilityMeasure_map (measurable_const.mul measurable_id).aemeasurable
  have hBase : Tendsto_dist (fun n ω => c * Xn n ω) (Q.map fun x => c * x) μ hBaseMeas := by
    exact (Tendsto_dist_iff _ _ _ hBaseMeas).2
      (Tendsto_dist.const_mul_tendsto hXn hX tendsto_const_nhds)
  have hTight : IsBigOp Xn (fun _ => (1 : ℝ)) μ := hX.tightness hXn
  have hSmall : IsLittleOp (fun n ω => Yn n ω - c) (fun _ => (1 : ℝ)) μ :=
    (Tendsto_inProb.sub_const hY).isLittleOp_one
  have hRem : IsLittleOp (fun n ω => Xn n ω * (Yn n ω - c))
      (fun _ => (1 : ℝ)) μ := hTight.mul_isLittleOp_one_isLittleOp hSmall
  apply Tendsto_dist_vec.add_isLittleOp_one hBaseMeas
    (fun n => (hXn n).mul (hYn n)) hBase
  refine IsLittleOp.of_abs_le_const_mul_one (C := 1) one_pos hRem ?_
  intro n ω
  simp [Real.norm_eq_abs, mul_sub, mul_comm]

/-- **Vector random-multiplier Slutsky theorem.** Suppose [the vector sequence `Xn` is
measurable](hyp:hXn), [the scalar multipliers `Yn` are measurable](hyp:hYn), [`Xn`
converges in distribution to `Q`](hyp:hX), and [`Yn` converges in probability to the
constant `c`](hyp:hY). Then [the scalar multiples `Yn • Xn` converge in distribution to
the pushforward of `Q` by `x ↦ c • x`](goal). -/
theorem Tendsto_dist_vec.smul_tendstoInProbability_const
    {Omega E : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    {Xn : ℕ → Omega → E} {Yn : ℕ → Omega → ℝ}
    {Q : Measure E} [IsProbabilityMeasure Q] {c : ℝ}
    (hXn : ∀ n, AEMeasurable (Xn n) mu)
    (hYn : ∀ n, AEMeasurable (Yn n) mu)
    (hX : Tendsto_dist_vec Xn Q mu hXn)
    (hY : Tendsto_inProb Yn (fun _ => c) mu) :
    @Tendsto_dist_vec Omega E _ _ _ _ (fun n omega => Yn n omega • Xn n omega)
      (Q.map fun x => c • x) mu _
      (Measure.isProbabilityMeasure_map
        (continuous_const_smul c).measurable.aemeasurable)
      (fun n => (hYn n).smul (hXn n)) := by
  have hBaseMeas : ∀ n, AEMeasurable (fun omega => c • Xn n omega) mu := fun n =>
    aemeasurable_const.smul (hXn n)
  letI : IsProbabilityMeasure (Q.map fun x : E => c • x) :=
    Measure.isProbabilityMeasure_map (continuous_const_smul c).measurable.aemeasurable
  have hBase : Tendsto_dist_vec (fun n omega => c • Xn n omega)
      (Q.map fun x => c • x) mu hBaseMeas :=
    (Tendsto_dist_vec_iff _ _ _ hBaseMeas).2
      (Tendsto_dist_vec.map_continuous (continuous_const_smul c) hXn hX)
  have hNormMeas : ∀ n, AEMeasurable (fun omega => ‖Xn n omega‖) mu := fun n =>
    continuous_norm.measurable.comp_aemeasurable (hXn n)
  letI : IsProbabilityMeasure (Q.map fun x : E => ‖x‖) :=
    Measure.isProbabilityMeasure_map continuous_norm.measurable.aemeasurable
  have hNormDist : Tendsto_dist (fun n omega => ‖Xn n omega‖)
      (Q.map fun x => ‖x‖) mu hNormMeas :=
    (Tendsto_dist_iff _ _ _ hNormMeas).2
      (Tendsto_dist_vec.map_continuous continuous_norm hXn hX)
  have hTight : IsBigOp (fun n omega => ‖Xn n omega‖) (fun _ => (1 : ℝ)) mu :=
    hNormDist.tightness hNormMeas
  have hSmall : IsLittleOp (fun n omega => Yn n omega - c) (fun _ => (1 : ℝ)) mu :=
    (Tendsto_inProb.sub_const hY).isLittleOp_one
  have hProduct : IsLittleOp (fun n omega => ‖Xn n omega‖ * (Yn n omega - c))
      (fun _ => (1 : ℝ)) mu := hTight.mul_isLittleOp_one_isLittleOp hSmall
  apply Tendsto_dist_vec.add_isLittleOp_one hBaseMeas
    (fun n => (hYn n).smul (hXn n)) hBase
  have heq : (fun n omega => ‖Yn n omega • Xn n omega - c • Xn n omega‖) =
      fun n omega => ‖Xn n omega‖ * |Yn n omega - c| := by
    funext n omega
    rw [← sub_smul, norm_smul, Real.norm_eq_abs, mul_comm]
  change IsLittleOp (fun n omega =>
    ‖Yn n omega • Xn n omega - c • Xn n omega‖) (fun _ => (1 : ℝ)) mu
  rw [heq]
  refine IsLittleOp.of_abs_le_const_mul_one (C := 1) one_pos hProduct ?_
  intro n omega
  simp [abs_mul]

end Causalean.Stat
