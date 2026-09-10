/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.MinimaxHolder

/-! # Clamp functional on the canonical witness family -/

namespace CausalSmith.Stat.LmtpThresholdAtomFrontier

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

noncomputable section

/-- [the stated minimax atom mass property holds](goal) for [the specified `J` input](hyp:J), [the specified `kappa` input](hyp:kappa), [the specified `delta` input](hyp:delta), [the specified `hkappa` input](hyp:hkappa), [the specified `hdelta` input](hyp:hdelta), [the specified `q` input](hyp:q), [the specified `x` input](hyp:x). -/
lemma minimaxAtomMass (J : ℕ) (kappa delta : ℝ) (hkappa : 0 ≤ kappa)
    (hdelta : 0 ≤ delta) (q : ℝ → ℝ) (x : Fin J) :
    atomMass (minimaxClampLaw J kappa (fun p => q p.2)) x delta =
      delta ^ (kappa + 1) := by
  unfold atomMass minimaxClampLaw
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hdelta,
    intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (by linarith : -1 < kappa))]
  rw [Real.zero_rpow (by linarith : kappa + 1 ≠ 0)]
  have hk1 : kappa + 1 ≠ 0 := by linarith
  field_simp [hk1]
  ring

/-- [the stated minimax retained mean property holds](goal) for [the specified `J` input](hyp:J), [the specified `kappa` input](hyp:kappa), [the specified `delta` input](hyp:delta), [the specified `hJ` input](hyp:hJ), [the specified `hkappa` input](hyp:hkappa), [the specified `q` input](hyp:q), [the specified `hqmeas` input](hyp:hqmeas), [the specified `hqbound` input](hyp:hqbound). -/
lemma minimaxRetainedMean (J : ℕ) (kappa delta : ℝ)
    (hJ : 0 < J) (hkappa : 0 ≤ kappa)
    (q : ℝ → ℝ) (hqmeas : Measurable q) (hqbound : ∀ a, |q a| ≤ 1 / 2) :
    retainedMean (minimaxClampLaw J kappa (fun p => q p.2)) delta =
      ∫ a in Set.Ioi delta, (1 / 2 + q a) ∂minimaxTreatmentMeasure kappa := by
  let g : Fin J × ℝ → ℝ := fun p => q p.2
  have hgmeas : Measurable g := hqmeas.comp measurable_snd
  have hgbound : ∀ p, |g p| ≤ 1 / 2 := fun p => hqbound p.2
  let T : Set (Fin J × ℝ) := (Set.univ : Set (Fin J)) ×ˢ Set.Ioi delta
  have hT : MeasurableSet T := MeasurableSet.univ.prod measurableSet_Ioi
  have hreg := minimaxDataMeasure_integral_Y_design J kappa hJ hkappa g hgmeas
    hgbound T hT
  haveI : Nonempty (Fin J) := Fin.pos_iff_nonempty.mp hJ
  haveI : IsProbabilityMeasure (minimaxStratumMeasure J) := by
    unfold minimaxStratumMeasure
    infer_instance
  haveI : IsProbabilityMeasure (minimaxTreatmentMeasure kappa) :=
    minimaxTreatmentMeasure_isProbabilityMeasure kappa hkappa
  have hprod := setIntegral_prod_mul
    (μ := minimaxStratumMeasure J) (ν := minimaxTreatmentMeasure kappa)
    (fun _ : Fin J => (1 : ℝ)) (fun a => 1 / 2 + q a)
    (Set.univ : Set (Fin J)) (Set.Ioi delta)
  rw [show retainedMean (minimaxClampLaw J kappa (fun p => q p.2)) delta =
      ∫ o in (fun o : ClampObs J => (o.X, o.A)) ⁻¹' T, o.Y
        ∂minimaxDataMeasure J kappa g by
    unfold retainedMean
    change (∫ o, o.Y * Set.indicator {o : ClampObs J | delta < o.A}
      (fun _ => (1 : ℝ)) o ∂minimaxDataMeasure J kappa g) = _
    have hd : Measurable (fun o : ClampObs J => (o.X, o.A)) := by
      let hall : Measurable (fun o : ClampObs J => (o.X, o.A, o.Y)) :=
        Measurable.of_comap_le le_rfl
      exact (measurable_fst.comp hall).prodMk
        (measurable_fst.comp (measurable_snd.comp hall))
    calc
      (∫ o, o.Y * Set.indicator {o : ClampObs J | delta < o.A}
          (fun _ => (1 : ℝ)) o ∂minimaxDataMeasure J kappa g) =
          ∫ o, ((fun o : ClampObs J => (o.X, o.A)) ⁻¹' T).indicator
            (fun o => o.Y) o ∂minimaxDataMeasure J kappa g := by
        apply integral_congr_ae
        filter_upwards with o
        simp [T, Set.indicator, g]
      _ = _ := integral_indicator (hT.preimage hd)]
  rw [hreg]
  change (∫ p in T, (1 / 2 + q p.2) ∂minimaxDesignMeasure J kappa) = _
  rw [minimaxDesignMeasure]
  calc
    (∫ p in T, (1 / 2 + q p.2)
        ∂(minimaxStratumMeasure J).prod (minimaxTreatmentMeasure kappa)) =
        (∫ _x in (Set.univ : Set (Fin J)), (1 : ℝ) ∂minimaxStratumMeasure J) *
          ∫ a in Set.Ioi delta, (1 / 2 + q a) ∂minimaxTreatmentMeasure kappa := by
            simpa [T] using hprod
    _ = _ := by simp

/-- [the stated minimax clamp functional property holds](goal) for [the specified `J` input](hyp:J), [the specified `kappa` input](hyp:kappa), [the specified `delta` input](hyp:delta), [the specified `hJ` input](hyp:hJ), [the specified `hkappa` input](hyp:hkappa), [the specified `hdelta` input](hyp:hdelta), [the specified `q` input](hyp:q), [the specified `hqmeas` input](hyp:hqmeas), [the specified `hqbound` input](hyp:hqbound). -/
lemma minimaxClampFunctional (J : ℕ) (kappa delta : ℝ)
    (hJ : 0 < J) (hkappa : 0 ≤ kappa) (hdelta : 0 ≤ delta)
    (q : ℝ → ℝ) (hqmeas : Measurable q) (hqbound : ∀ a, |q a| ≤ 1 / 2) :
    clampFunctional (minimaxClampLaw J kappa (fun p => q p.2)) delta =
      (∫ a in Set.Ioi delta, (1 / 2 + q a) ∂minimaxTreatmentMeasure kappa) +
        delta ^ (kappa + 1) * (1 / 2 + q delta) := by
  rw [clampFunctional, minimaxRetainedMean J kappa delta hJ hkappa q hqmeas hqbound]
  simp_rw [minimaxAtomMass J kappa delta hkappa hdelta q]
  simp [minimaxClampLaw]
  have hJR : (J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  field_simp [hJR]

/-- [the stated minimax treatment measure real ioi property holds](goal) for [the specified `kappa` input](hyp:kappa), [the specified `delta` input](hyp:delta), [the specified `hkappa` input](hyp:hkappa), [the specified `hdelta` input](hyp:hdelta). -/
lemma minimaxTreatmentMeasure_real_Ioi (kappa delta : ℝ)
    (hkappa : 0 ≤ kappa) (hdelta : delta ∈ Set.Icc (0 : ℝ) 1) :
    (minimaxTreatmentMeasure kappa).real (Set.Ioi delta) =
      1 - delta ^ (kappa + 1) := by
  letI : IsProbabilityMeasure (minimaxTreatmentMeasure kappa) :=
    minimaxTreatmentMeasure_isProbabilityMeasure kappa hkappa
  have hicc : (minimaxTreatmentMeasure kappa).real (Set.Icc (0 : ℝ) delta) =
      delta ^ (kappa + 1) := by
    rw [minimaxTreatmentMeasure_real kappa hkappa _ measurableSet_Icc
      (fun a ha => ⟨ha.1, ha.2.trans hdelta.2⟩)]
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hdelta.1,
      intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (by linarith : -1 < kappa))]
    rw [Real.zero_rpow (by linarith : kappa + 1 ≠ 0)]
    have hk1 : kappa + 1 ≠ 0 := by linarith
    field_simp [hk1]
    ring
  have hiic : (minimaxTreatmentMeasure kappa).real (Set.Iic delta) =
      delta ^ (kappa + 1) := by
    rw [← hicc]
    apply measureReal_congr
    filter_upwards [minimaxTreatmentMeasure_ae_mem_Icc kappa] with a ha
    apply propext
    change a ≤ delta ↔ 0 ≤ a ∧ a ≤ delta
    constructor
    · intro had
      exact ⟨ha.1, had⟩
    · intro had
      exact had.2
  rw [← Set.compl_Iic, measureReal_compl measurableSet_Iic, hiic]
  simp

/-- [the stated minimax global separation property holds](goal) for [the specified `J` input](hyp:J), [the specified `kappa` input](hyp:kappa), [the specified `delta` input](hyp:delta), [the specified `eps` input](hyp:eps), [the specified `hJ` input](hyp:hJ), [the specified `hkappa` input](hyp:hkappa), [the specified `hdelta` input](hyp:hdelta), [the specified `heps` input](hyp:heps). -/
lemma minimaxGlobalSeparation (J : ℕ) (kappa delta eps : ℝ)
    (hJ : 0 < J) (hkappa : 0 ≤ kappa) (hdelta : delta ∈ Set.Icc (0 : ℝ) 1)
    (heps : |eps| ≤ 1 / 2) :
    clampFunctional (minimaxClampLaw J kappa (fun _ => eps)) delta -
      clampFunctional (minimaxClampLaw J kappa (fun _ => 0)) delta = eps := by
  rw [minimaxClampFunctional J kappa delta hJ hkappa hdelta.1
      (fun _ => eps) measurable_const (fun _ => heps),
    minimaxClampFunctional J kappa delta hJ hkappa hdelta.1
      (fun _ => 0) measurable_const (fun _ => by norm_num)]
  have hconst (c : ℝ) :
      (∫ _a in Set.Ioi delta, c ∂minimaxTreatmentMeasure kappa) =
        c * (minimaxTreatmentMeasure kappa).real (Set.Ioi delta) := by
    simp [mul_comm]
  rw [show (∫ a in Set.Ioi delta, (1 / 2 + eps) ∂minimaxTreatmentMeasure kappa) =
      (1 / 2 + eps) * (minimaxTreatmentMeasure kappa).real (Set.Ioi delta) by
        exact hconst _,
    show (∫ a in Set.Ioi delta, (1 / 2 + 0) ∂minimaxTreatmentMeasure kappa) =
      (1 / 2) * (minimaxTreatmentMeasure kappa).real (Set.Ioi delta) by
        simpa using hconst (1 / 2)]
  rw [minimaxTreatmentMeasure_real_Ioi kappa delta hkappa hdelta]
  ring

/-- [the stated minimax local separation property holds](goal) for [the specified `J` input](hyp:J), [the specified `beta` input](hyp:beta), [the specified `kappa` input](hyp:kappa), [the specified `delta` input](hyp:delta), [the specified `h` input](hyp:h), [the specified `amplitude` input](hyp:amplitude), [the specified `hJ` input](hyp:hJ), [the specified `hbeta` input](hyp:hbeta), [the specified `hkappa` input](hyp:hkappa), [the specified `hdelta` input](hyp:hdelta), [the specified `hh` input](hyp:hh), [the specified `hh1` input](hyp:hh1), [the specified `hamp` input](hyp:hamp), [the specified `hamp_le` input](hyp:hamp_le). -/
lemma minimaxLocalSeparation (J : ℕ) (beta kappa delta h amplitude : ℝ)
    (hJ : 0 < J) (hbeta : 0 < beta) (hkappa : 0 ≤ kappa)
    (hdelta : delta ∈ Set.Icc (0 : ℝ) 1) (hh : 0 < h)
    (hh1 : h ≤ 1) (hamp : 0 ≤ amplitude) (hamp_le : amplitude ≤ 1 / 4) :
    let q := fun a : ℝ => amplitude * h ^ beta *
      CausalSmith.Stat.DoseResponseMinimax.doseBump ((a - delta) / h)
    amplitude * delta ^ (kappa + 1) * h ^ beta ≤
      clampFunctional (minimaxClampLaw J kappa (fun p => q p.2)) delta -
        clampFunctional (minimaxClampLaw J kappa (fun _ => 0)) delta := by
  dsimp only
  let q := fun a : ℝ => amplitude * h ^ beta *
    CausalSmith.Stat.DoseResponseMinimax.doseBump ((a - delta) / h)
  have hqmeas : Measurable q := by
    dsimp [q]
    fun_prop
  have hqnonneg : ∀ a, 0 ≤ q a := by
    intro a
    dsimp [q]
    exact mul_nonneg (mul_nonneg hamp (Real.rpow_nonneg hh.le _))
      (CausalSmith.Stat.DoseResponseMinimax.doseBump_nonneg _)
  have hqbound : ∀ a, |q a| ≤ 1 / 2 := by
    intro a
    rw [abs_of_nonneg (hqnonneg a)]
    have hb := CausalSmith.Stat.DoseResponseMinimax.doseBump_le_one ((a - delta) / h)
    calc
      q a ≤ amplitude * h ^ beta := by
        dsimp [q]
        nlinarith [mul_nonneg hamp (Real.rpow_nonneg hh.le beta)]
      _ ≤ 1 / 2 := by
        have hp : h ^ beta ≤ 1 := Real.rpow_le_one hh.le hh1 hbeta.le
        calc
          amplitude * h ^ beta ≤ amplitude * 1 := mul_le_mul_of_nonneg_left hp hamp
          _ ≤ 1 / 2 := by linarith
  rw [minimaxClampFunctional J kappa delta hJ hkappa hdelta.1 q hqmeas hqbound,
    minimaxClampFunctional J kappa delta hJ hkappa hdelta.1
      (fun _ => 0) measurable_const (fun _ => by norm_num)]
  haveI : IsProbabilityMeasure (minimaxTreatmentMeasure kappa) :=
    minimaxTreatmentMeasure_isProbabilityMeasure kappa hkappa
  have hqint : Integrable q (minimaxTreatmentMeasure kappa) := by
    refine Integrable.of_bound hqmeas.aestronglyMeasurable (1 / 2) ?_
    filter_upwards with a
    simpa [Real.norm_eq_abs] using hqbound a
  have honeint : Integrable (fun _ : ℝ => (1 / 2 : ℝ))
      (minimaxTreatmentMeasure kappa) := integrable_const _
  rw [show (∫ a in Set.Ioi delta, (1 / 2 + q a) ∂minimaxTreatmentMeasure kappa) =
      (∫ a in Set.Ioi delta, (1 / 2 : ℝ) ∂minimaxTreatmentMeasure kappa) +
        ∫ a in Set.Ioi delta, q a ∂minimaxTreatmentMeasure kappa by
          rw [integral_add honeint.integrableOn hqint.integrableOn],
    show (∫ a in Set.Ioi delta, (1 / 2 + 0) ∂minimaxTreatmentMeasure kappa) =
      ∫ a in Set.Ioi delta, (1 / 2 : ℝ) ∂minimaxTreatmentMeasure kappa by simp]
  have hqdelta : q delta = amplitude * h ^ beta := by
    simp [q, hh.ne', CausalSmith.Stat.DoseResponseMinimax.doseBump_zero]
  rw [hqdelta]
  have hnonnegint : 0 ≤ ∫ a in Set.Ioi delta, q a ∂minimaxTreatmentMeasure kappa :=
    integral_nonneg_of_ae (ae_of_all _ hqnonneg)
  nlinarith

end

end CausalSmith.Stat.LmtpThresholdAtomFrontier
