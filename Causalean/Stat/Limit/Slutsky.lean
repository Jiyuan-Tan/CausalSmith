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

/-- If [a real sequence converges in distribution](hyp:hX),
[a second sequence is a.e. measurable](hyp:hYn), and [the second sequence
converges in probability to a constant](hyp:hY), then [their sum converges
in distribution to the limiting law shifted by that constant](goal).

This is the additive random-perturbation conclusion in van der Vaart, Lemma 2.8. -/
theorem Modes.TendstoInLaw.add_tendstoInProbability_const
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Xn Yn : ℕ → Ω → ℝ} {Q : Measure ℝ} [IsProbabilityMeasure Q] {c : ℝ}
    (hX : Modes.TendstoInLaw (fun _ : ℕ => μ) Xn atTop Q)
    (hYn : ∀ n, AEMeasurable (Yn n) μ)
    (hY : Modes.TendstoInProbability (fun _ : ℕ => μ) Yn atTop (fun _ _ => c)) :
    @Modes.TendstoInLaw ℕ (fun _ => Ω) _ ℝ _ _ _ (fun _ => μ) _
      (fun n ω => Xn n ω + Yn n ω) atTop (Q.map fun x => x + c)
      (Measure.isProbabilityMeasure_map
        (measurable_id.add measurable_const).aemeasurable) := by
  have hXn : ∀ n, AEMeasurable (Xn n) μ := hX.forall_aemeasurable
  have hBaseMeas : ∀ n, AEMeasurable (fun ω => Xn n ω + c) μ := fun n =>
    (hXn n).add aemeasurable_const
  letI : IsProbabilityMeasure (Q.map fun x : ℝ => x + c) :=
    Measure.isProbabilityMeasure_map (measurable_id.add measurable_const).aemeasurable
  have hBase : Modes.TendstoInLaw (fun _ : ℕ => μ) (fun n ω => Xn n ω + c) atTop
      (Q.map fun x => x + c) := by
    exact (Tendsto_dist_iff _ _ _ hBaseMeas).2
      (Modes.TendstoInLaw.map_continuous hX (continuous_id.add continuous_const))
  have hRem : IsLittleOp (fun n ω => Yn n ω - c) (fun _ => (1 : ℝ)) μ :=
    (Modes.TendstoInProbability.isLittleOp_one (Modes.TendstoInProbability.sub_const hY))
  apply Modes.TendstoInLaw.add_isLittleOp_one hBase
    (fun n => (hXn n).add (hYn n))
  refine IsLittleOp.of_abs_le_const_mul_one (C := 1) one_pos hRem ?_
  intro n ω
  simp [Real.norm_eq_abs]
/-- If [a real sequence converges in distribution](hyp:hX),
[a sequence of multipliers is a.e. measurable](hyp:hYn), and [the
multipliers converge in probability to a constant](hyp:hY), then [the
product sequence converges in distribution to the limiting law scaled by
that constant](goal).

This is the random-multiplier conclusion in van der Vaart, Lemma 2.8. -/
theorem Modes.TendstoInLaw.mul_tendstoInProbability_const
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Xn Yn : ℕ → Ω → ℝ} {Q : Measure ℝ} [IsProbabilityMeasure Q] {c : ℝ}
    (hX : Modes.TendstoInLaw (fun _ : ℕ => μ) Xn atTop Q)
    (hYn : ∀ n, AEMeasurable (Yn n) μ)
    (hY : Modes.TendstoInProbability (fun _ : ℕ => μ) Yn atTop (fun _ _ => c)) :
    @Modes.TendstoInLaw ℕ (fun _ => Ω) _ ℝ _ _ _ (fun _ => μ) _
      (fun n ω => Xn n ω * Yn n ω) atTop (Q.map fun x => c * x)
      (Measure.isProbabilityMeasure_map
        (measurable_const.mul measurable_id).aemeasurable) := by
  have hXn : ∀ n, AEMeasurable (Xn n) μ := hX.forall_aemeasurable
  have hBaseMeas : ∀ n, AEMeasurable (fun ω => c * Xn n ω) μ := fun n =>
    aemeasurable_const.mul (hXn n)
  letI : IsProbabilityMeasure (Q.map fun x : ℝ => c * x) :=
    Measure.isProbabilityMeasure_map (measurable_const.mul measurable_id).aemeasurable
  have hBase : Modes.TendstoInLaw (fun _ : ℕ => μ) (fun n ω => c * Xn n ω) atTop
      (Q.map fun x => c * x) := by
    exact (Tendsto_dist_iff _ _ _ hBaseMeas).2
      (Modes.TendstoInLaw.const_mul_tendsto hX tendsto_const_nhds)
  have hTight : IsBigOp Xn (fun _ => (1 : ℝ)) μ := Modes.TendstoInLaw.tightness hX
  have hSmall : IsLittleOp (fun n ω => Yn n ω - c) (fun _ => (1 : ℝ)) μ :=
    (Modes.TendstoInProbability.isLittleOp_one (Modes.TendstoInProbability.sub_const hY))
  have hRem : IsLittleOp (fun n ω => Xn n ω * (Yn n ω - c))
      (fun _ => (1 : ℝ)) μ := hTight.mul_isLittleOp_one_isLittleOp hSmall
  apply Modes.TendstoInLaw.add_isLittleOp_one hBase
    (fun n => (hXn n).mul (hYn n))
  refine IsLittleOp.of_abs_le_const_mul_one (C := 1) one_pos hRem ?_
  intro n ω
  simp [Real.norm_eq_abs, mul_sub, mul_comm]
/-- If [a vector sequence converges in distribution](hyp:hX),
[scalar multipliers are a.e. measurable](hyp:hYn), and [the multipliers
converge in probability to a constant](hyp:hY), then [the scalar multiples
converge in distribution to the limiting law scaled by that constant](goal). -/
theorem Modes.TendstoInLaw.smul_tendstoInProbability_const
    {Omega E : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    {Xn : ℕ → Omega → E} {Yn : ℕ → Omega → ℝ}
    {Q : Measure E} [IsProbabilityMeasure Q] {c : ℝ}
    (hX : Modes.TendstoInLaw (fun _ : ℕ => mu) Xn atTop Q)
    (hYn : ∀ n, AEMeasurable (Yn n) mu)
    (hY : Modes.TendstoInProbability (fun _ : ℕ => mu) Yn atTop (fun _ _ => c)) :
    @Modes.TendstoInLaw ℕ (fun _ => Omega) _ E _ _ _ (fun _ => mu) _
      (fun n omega => Yn n omega • Xn n omega) atTop (Q.map fun x => c • x)
      (Measure.isProbabilityMeasure_map
        (continuous_const_smul c).measurable.aemeasurable) := by
  have hXn : ∀ n, AEMeasurable (Xn n) mu := hX.forall_aemeasurable
  have hBaseMeas : ∀ n, AEMeasurable (fun omega => c • Xn n omega) mu := fun n =>
    aemeasurable_const.smul (hXn n)
  letI : IsProbabilityMeasure (Q.map fun x : E => c • x) :=
    Measure.isProbabilityMeasure_map (continuous_const_smul c).measurable.aemeasurable
  have hBase : Modes.TendstoInLaw (fun _ : ℕ => mu) (fun n omega => c • Xn n omega) atTop
      (Q.map fun x => c • x) :=
    (Tendsto_dist_vec_iff _ _ _ hBaseMeas).2
      (Modes.TendstoInLaw.map_continuous hX (continuous_const_smul c))
  have hNormMeas : ∀ n, AEMeasurable (fun omega => ‖Xn n omega‖) mu := fun n =>
    continuous_norm.measurable.comp_aemeasurable (hXn n)
  letI : IsProbabilityMeasure (Q.map fun x : E => ‖x‖) :=
    Measure.isProbabilityMeasure_map continuous_norm.measurable.aemeasurable
  have hNormDist : Modes.TendstoInLaw (fun _ : ℕ => mu) (fun n omega => ‖Xn n omega‖) atTop
      (Q.map fun x => ‖x‖) :=
    (Tendsto_dist_iff _ _ _ hNormMeas).2
      (Modes.TendstoInLaw.map_continuous hX continuous_norm)
  have hTight : IsBigOp (fun n omega => ‖Xn n omega‖) (fun _ => (1 : ℝ)) mu :=
    Modes.TendstoInLaw.tightness hNormDist
  have hSmall : IsLittleOp (fun n omega => Yn n omega - c) (fun _ => (1 : ℝ)) mu :=
    (Modes.TendstoInProbability.isLittleOp_one (Modes.TendstoInProbability.sub_const hY))
  have hProduct : IsLittleOp (fun n omega => ‖Xn n omega‖ * (Yn n omega - c))
      (fun _ => (1 : ℝ)) mu := hTight.mul_isLittleOp_one_isLittleOp hSmall
  apply Modes.TendstoInLaw.add_isLittleOp_one hBase
    (fun n => (hYn n).smul (hXn n))
  have hRem : IsLittleOp (fun n omega =>
      ‖Yn n omega • Xn n omega - c • Xn n omega‖) (fun _ => (1 : ℝ)) mu := by
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
  intro ε hε
  simpa only [norm_norm, Pi.smul_apply'] using hRem ε hε
end Causalean.Stat
