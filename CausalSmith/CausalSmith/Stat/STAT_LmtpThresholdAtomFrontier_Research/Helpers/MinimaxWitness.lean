/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Basic
import Causalean.Mathlib.Probability.BernoulliMeasure
import Causalean.Stat.PolynomialTail.PowerIntegral
import Mathlib.Probability.UniformOn

/-!
# Canonical design for the clamp minimax witnesses

The witness design uses uniform finite strata and the normalized polynomial
density `(κ + 1) a^κ` on `[0,1]`.  Outcome tilts are added in later lemmas.
-/

namespace CausalSmith.Stat.LmtpThresholdAtomFrontier

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

/-- Uniform probability law on the finite stratum space. -/
def minimaxStratumMeasure (J : ℕ) : Measure (Fin J) :=
  ProbabilityTheory.uniformOn Set.univ

/-- The normalized polynomial treatment law on `[0,1]`. -/
def minimaxTreatmentMeasure (kappa : ℝ) : Measure ℝ :=
  (volume.restrict (Set.Icc (0 : ℝ) 1)).withDensity
    (fun a => ENNReal.ofReal ((kappa + 1) * a ^ kappa))

/-- [the stated minimax treatment density integral property holds](goal) for [the specified `kappa` input](hyp:kappa), [the specified `hkappa` input](hyp:hkappa). -/
lemma minimaxTreatmentDensity_integral (kappa : ℝ) (hkappa : 0 ≤ kappa) :
    (∫ a in Set.Icc (0 : ℝ) 1, (kappa + 1) * a ^ kappa) = 1 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num),
    intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith : -1 < kappa))]
  rw [Real.one_rpow, Real.zero_rpow (by linarith : kappa + 1 ≠ 0)]
  field_simp
  norm_num

/-- [minimax treatment measure is a probability measure](goal) for [the specified `kappa` input](hyp:kappa), [the specified `hkappa` input](hyp:hkappa). -/
lemma minimaxTreatmentMeasure_isProbabilityMeasure (kappa : ℝ) (hkappa : 0 ≤ kappa) :
    IsProbabilityMeasure (minimaxTreatmentMeasure kappa) := by
  rw [isProbabilityMeasure_iff]
  rw [minimaxTreatmentMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  have hfint : Integrable (fun a : ℝ => (kappa + 1) * a ^ kappa)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    change IntegrableOn (fun a : ℝ => (kappa + 1) * a ^ kappa)
      (Set.Icc (0 : ℝ) 1) volume
    rw [← intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)]
    exact (intervalIntegral.intervalIntegrable_rpow (Or.inl hkappa)).const_mul (kappa + 1)
  have hfnn : 0 ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)]
      (fun a : ℝ => (kappa + 1) * a ^ kappa) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with a ha
    exact mul_nonneg (by linarith) (Real.rpow_nonneg ha.1 _)
  rw [← ofReal_integral_eq_lintegral_ofReal hfint hfnn,
    minimaxTreatmentDensity_integral kappa hkappa]
  simp

/-- The common `(X,A)` law of every minimax witness. -/
def minimaxDesignMeasure (J : ℕ) (kappa : ℝ) : Measure (Fin J × ℝ) :=
  (minimaxStratumMeasure J).prod (minimaxTreatmentMeasure kappa)

/-- [minimax design measure is a probability measure](goal) for [the specified `J` input](hyp:J), [the specified `kappa` input](hyp:kappa), [the specified `hJ` input](hyp:hJ), [the specified `hkappa` input](hyp:hkappa). -/
lemma minimaxDesignMeasure_isProbabilityMeasure (J : ℕ) (kappa : ℝ)
    (hJ : 0 < J) (hkappa : 0 ≤ kappa) :
    IsProbabilityMeasure (minimaxDesignMeasure J kappa) := by
  letI : Nonempty (Fin J) := Fin.pos_iff_nonempty.mp hJ
  letI : IsProbabilityMeasure (minimaxTreatmentMeasure kappa) :=
    minimaxTreatmentMeasure_isProbabilityMeasure kappa hkappa
  unfold minimaxDesignMeasure minimaxStratumMeasure
  infer_instance

/-- [the stated minimax stratum measure real singleton property holds](goal) for [the specified `J` input](hyp:J), [the specified `hJ` input](hyp:hJ), [the specified `x` input](hyp:x). -/
lemma minimaxStratumMeasure_real_singleton (J : ℕ) (hJ : 0 < J) (x : Fin J) :
    (minimaxStratumMeasure J).real {x} = 1 / (J : ℝ) := by
  classical
  rw [measureReal_def, minimaxStratumMeasure, ProbabilityTheory.uniformOn_univ]
  simp [measureReal_def, ENNReal.toReal_div, hJ.ne']

/-- [the stated minimax treatment measure real property holds](goal) for [the specified `kappa` input](hyp:kappa), [the specified `hkappa` input](hyp:hkappa), [the specified `B` input](hyp:B), [the specified `hB` input](hyp:hB), [the specified `hsub` input](hyp:hsub). -/
lemma minimaxTreatmentMeasure_real (kappa : ℝ) (hkappa : 0 ≤ kappa)
    (B : Set ℝ) (hB : MeasurableSet B) (hsub : B ⊆ Set.Icc (0 : ℝ) 1) :
    (minimaxTreatmentMeasure kappa).real B =
      ∫ a in B, (kappa + 1) * a ^ kappa := by
  let f : ℝ → ℝ := fun a => (kappa + 1) * a ^ kappa
  have hfint : Integrable f (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    change IntegrableOn f (Set.Icc (0 : ℝ) 1) volume
    rw [← intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)]
    exact (intervalIntegral.intervalIntegrable_rpow (Or.inl hkappa)).const_mul (kappa + 1)
  have hfB : Integrable f (volume.restrict B) := by
    exact hfint.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hfnn : 0 ≤ᵐ[volume.restrict B] f := by
    filter_upwards [ae_restrict_mem hB] with a ha
    exact mul_nonneg (by linarith) (Real.rpow_nonneg (hsub ha).1 _)
  have hrestrict :
      (volume.restrict (Set.Icc (0 : ℝ) 1)).restrict B = volume.restrict B := by
    rw [Measure.restrict_restrict hB]
    congr 1
    exact Set.inter_eq_left.mpr hsub
  rw [measureReal_def, minimaxTreatmentMeasure, withDensity_apply _ hB]
  have he := ofReal_integral_eq_lintegral_ofReal hfB hfnn
  change (∫⁻ a, ENNReal.ofReal ((kappa + 1) * a ^ kappa)
    ∂(volume.restrict (Set.Icc (0 : ℝ) 1)).restrict B).toReal = _
  rw [hrestrict]
  rw [← he]
  rw [ENNReal.toReal_ofReal (integral_nonneg_of_ae hfnn)]

/-- [the stated minimax design measure real rectangle property holds](goal) for [the specified `J` input](hyp:J), [the specified `kappa` input](hyp:kappa), [the specified `hJ` input](hyp:hJ), [the specified `hkappa` input](hyp:hkappa), [the specified `x` input](hyp:x), [the specified `B` input](hyp:B), [the specified `hB` input](hyp:hB), [the specified `hsub` input](hyp:hsub). -/
lemma minimaxDesignMeasure_real_rectangle (J : ℕ) (kappa : ℝ)
    (hJ : 0 < J) (hkappa : 0 ≤ kappa) (x : Fin J)
    (B : Set ℝ) (hB : MeasurableSet B) (hsub : B ⊆ Set.Icc (0 : ℝ) 1) :
    (minimaxDesignMeasure J kappa).real ({x} ×ˢ B) =
      (1 / (J : ℝ)) * ∫ a in B, (kappa + 1) * a ^ kappa := by
  letI : Nonempty (Fin J) := Fin.pos_iff_nonempty.mp hJ
  letI : IsProbabilityMeasure (minimaxTreatmentMeasure kappa) :=
    minimaxTreatmentMeasure_isProbabilityMeasure kappa hkappa
  rw [minimaxDesignMeasure, measureReal_prod_prod,
    minimaxStratumMeasure_real_singleton J hJ x,
    minimaxTreatmentMeasure_real kappa hkappa B hB hsub]

end

end CausalSmith.Stat.LmtpThresholdAtomFrontier
