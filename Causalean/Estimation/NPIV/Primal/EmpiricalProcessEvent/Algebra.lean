/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.Concentration.Localization.UniformDeviation
public import Causalean.Stat.Concentration.Rademacher.StarHull
public import Causalean.Stat.Concentration.Localization.CriticalRadius
public import Causalean.Stat.Sample.PiTransport

/-!
Collects deterministic algebra for the NPIV empirical-process master event.
The lemmas turn localized deviation inequalities and regularizer bounds into
the additive envelopes used by the primal rate proof.
-/

public section

namespace Causalean
namespace Estimation
namespace NPIV
namespace Primal

open MeasureTheory Causalean.Stat Causalean.Stat.Concentration

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Probability bounds for event assembly -/

/-- If [every measurable event](hyp:hE_meas) in a countable family has [probability at
least one minus its assigned error](hyp:hE), then [their intersection has probability at
least one minus the sum of the errors](goal). -/
lemma measure_iInter_nat_ge_one_sub_tsum_of_ge
    [IsProbabilityMeasure μ]
    {E : ℕ → Set Ω} {a : ℕ → ENNReal}
    (hE_meas : ∀ n, MeasurableSet (E n))
    (hE : ∀ n, μ (E n) ≥ 1 - a n) :
    μ (⋂ n, E n) ≥ 1 - ∑' n, a n := by
  have hE_compl : ∀ n, μ (E n)ᶜ ≤ a n := by
    intro n
    have hone_le : (1 : ENNReal) ≤ a n + μ (E n) :=
      tsub_le_iff_left.mp (hE n)
    rw [measure_compl (hE_meas n) (measure_ne_top _ _), measure_univ]
    exact tsub_le_iff_right.mpr (by simpa [add_comm] using hone_le)
  have hbad_subset : (⋂ n, E n)ᶜ ⊆ ⋃ n, (E n)ᶜ := by
    simp
  have hbad_le : μ (⋂ n, E n)ᶜ ≤ ∑' n, a n := by
    calc
      μ (⋂ n, E n)ᶜ ≤ μ (⋃ n, (E n)ᶜ) := measure_mono hbad_subset
      _ ≤ ∑' n, μ (E n)ᶜ := measure_iUnion_le fun n => (E n)ᶜ
      _ ≤ ∑' n, a n := ENNReal.tsum_le_tsum hE_compl
  have hA_meas : MeasurableSet (⋂ n, E n) := MeasurableSet.iInter hE_meas
  rw [measure_compl hA_meas (measure_ne_top _ _), measure_univ] at hbad_le
  have hone_le : (1 : ENNReal) ≤ (∑' n, a n) + μ (⋂ n, E n) :=
    tsub_le_iff_right.mp hbad_le
  exact tsub_le_iff_left.mpr hone_le

/-- If [two measurable events](hyp:hA_meas,hB_meas) have [failure probabilities bounded by
`a` and `b`](hyp:hA,hB), then [their intersection has failure probability at most
`a + b`](goal). -/
lemma measure_inter_ge_one_sub_add_of_ge
    [IsProbabilityMeasure μ]
    {A B : Set Ω} {a b : ENNReal}
    (hA_meas : MeasurableSet A) (hB_meas : MeasurableSet B)
    (hA : μ A ≥ 1 - a) (hB : μ B ≥ 1 - b) :
    μ (A ∩ B) ≥ 1 - (a + b) := by
  have hA_compl : μ Aᶜ ≤ a := by
    have hone_le : (1 : ENNReal) ≤ a + μ A := tsub_le_iff_left.mp hA
    rw [measure_compl hA_meas (measure_ne_top _ _), measure_univ]
    exact tsub_le_iff_right.mpr (by simpa [add_comm] using hone_le)
  have hB_compl : μ Bᶜ ≤ b := by
    have hone_le : (1 : ENNReal) ≤ b + μ B := tsub_le_iff_left.mp hB
    rw [measure_compl hB_meas (measure_ne_top _ _), measure_univ]
    exact tsub_le_iff_right.mpr (by simpa [add_comm] using hone_le)
  have hbad_le : μ (A ∩ B)ᶜ ≤ a + b := by
    rw [Set.compl_inter]
    exact (measure_union_le Aᶜ Bᶜ).trans (add_le_add hA_compl hB_compl)
  have hAB_meas : MeasurableSet (A ∩ B) := hA_meas.inter hB_meas
  rw [measure_compl hAB_meas (measure_ne_top _ _), measure_univ] at hbad_le
  have hone_le : (1 : ENNReal) ≤ (a + b) + μ (A ∩ B) :=
    tsub_le_iff_right.mp hbad_le
  exact tsub_le_iff_left.mpr hone_le

/-! ## Deterministic Young / AM-GM envelope lemma

The lemma below is the deterministic real-analysis step bridging the raw
additive Foster-style deviation bound

    δ · ‖integrand‖_{L²}  +  b · √(log(1/ζ)/n)

(which `localized_uniform_deviation` produces; see
`Causalean/Stat/Concentration/UniformDeviationLocalized.lean`) to the
quadratic envelope shape

    R² + δ · w + δ²

appearing on the RHS of `ep_inequality_from_localized` and of the proof
sketch (`trae_inverse_problems.tex` line 308).  The bridge is two
applications of Young's inequality (`x · y ≤ (x² + y²)/2`) on the cross
terms `δ · R` and `R · κ`, where:

* `R := R_b = ‖T(h*_λ - h_0)‖`  (population weak-norm bias);
* `δ := δ_n`                     (localized rate);
* `w := ‖T(ĥ_n - h*_λ)‖`        (weak-norm gap, *unknown* random scalar);
* `κ`                            (the residual `b · √(log(1/ζ)/n)` McDiarmid term).

Once the EP step produces `δ·(R + w + δ) + R·κ` (via Foster's loss-norm
bound `‖loss(h, f) − loss(h*_λ, f)‖_{L²} ≲ R + w + δ` for `f ∈ F`), the
envelope below absorbs the bilinear `δ·R` and `R·κ` cross terms into
quadratic factors `R²` and `κ²`, leaving only the *honest* dependence on
the unknown `w` as the cross term `δ · w` — which is exactly what gets
absorbed downstream via AM-GM `δ · w ≤ ½ w² + ½ δ²`.
-/

/-- **Young / AM-GM cross-term envelope.** [The mixed sum
`δ · (R + w + δ) + R · κ` is bounded above by the quadratic envelope
`R² + δ · w + (3/2) · δ² + (1/2) · κ²`](goal).

Two applications of Young's inequality on `δ · R` and `R · κ`.  The
remaining `δ · w` term is *not* squared here because `w` is the random
weak-norm gap that gets absorbed downstream (see proof sketch line 365). -/
lemma young_cross_envelope (R δ w κ : ℝ) :
    δ * (R + w + δ) + R * κ
      ≤ R ^ 2 + δ * w + (3 / 2) * δ ^ 2 + (1 / 2) * κ ^ 2 := by
  nlinarith [sq_nonneg (R - δ), sq_nonneg (R - κ)]


end Primal
end NPIV
end Estimation
end Causalean
