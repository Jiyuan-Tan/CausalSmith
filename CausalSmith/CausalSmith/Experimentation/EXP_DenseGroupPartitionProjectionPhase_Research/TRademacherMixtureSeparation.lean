import CausalSmith.Experimentation.EXP_DenseGroupPartitionProjectionPhase_Research.Helpers.RademacherMoments
import CausalSmith.Experimentation.EXP_DenseGroupPartitionProjectionPhase_Research.Helpers.RademacherDegreeOne
import CausalSmith.Experimentation.EXP_DenseGroupPartitionProjectionPhase_Research.Helpers.RademacherScaledVariance
import CausalSmith.Experimentation.EXP_DenseGroupPartitionProjectionPhase_Research.TExactPameVariance
import Causalean.Experimentation.FinitePopulationMoments

/-!
# Rademacher mixture separation

The two product priors induce the same one-realization observation law while
their group-scaled exact variances separate at positive sampling density.
-/

open scoped Topology
open Filter

namespace CausalSmith.Experimentation.DenseGroupPartitionProjectionPhase

open Causalean.Experimentation.DesignBased
open Causalean.Experimentation.FinitePopulationMoments

/-- Expected value of a statistic of observed data under the common-sign mixture. -/
noncomputable def sameObservedExpectation {M : ℕ} (A : ScheduleArray M) (r : ℕ)
    (φ : ObservedData (A.popSize r) M (A.groups r) (A.treated r) → ℝ) : ℝ :=
  (priorSame (A.popSize r)).E (fun u =>
    (A.design r).E (fun w => φ (observe (A.popSize r) M (A.groups r) (A.treated r)
      (samePriorSchedule (A.popSize r) M u) w)))

/-- Expected value of a statistic of observed data under the independent-arm mixture. -/
noncomputable def independentObservedExpectation {M : ℕ} (A : ScheduleArray M) (r : ℕ)
    (φ : ObservedData (A.popSize r) M (A.groups r) (A.treated r) → ℝ) : ℝ :=
  (priorIndependent (A.popSize r)).E (fun u =>
    (A.design r).E (fun w => φ (observe (A.popSize r) M (A.groups r) (A.treated r)
      (independentPriorSchedule (A.popSize r) M u) w)))

/-- Group-scaled exact variance under a common-sign schedule draw. -/
noncomputable def sameScaledVariance {M : ℕ} (A : ScheduleArray M) (r : ℕ)
    (u : Fin (A.popSize r) → Bool) : ℝ :=
  (A.groups r : ℝ) * sigmaSq (samePriorSchedule (A.popSize r) M u)
    (A.grouped_le r) (A.treated_pos r) (A.treated_lt r)

/-- Group-scaled exact variance under an independent-arm schedule draw. -/
noncomputable def independentScaledVariance {M : ℕ} (A : ScheduleArray M) (r : ℕ)
    (u : Fin (A.popSize r) × Bool → Bool) : ℝ :=
  (A.groups r : ℝ) * sigmaSq (independentPriorSchedule (A.popSize r) M u)
    (A.grouped_le r) (A.treated_pos r) (A.treated_lt r)

-- @node: sameObservedExpectation_eq_independent
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:M,A,r), [the stated expectation identity holds](goal). -/
lemma sameObservedExpectation_eq_independent {M : ℕ} (A : ScheduleArray M) (r : ℕ)
    (φ : ObservedData (A.popSize r) M (A.groups r) (A.treated r) → ℝ) :
    sameObservedExpectation A r φ = independentObservedExpectation A r φ := by
  unfold sameObservedExpectation independentObservedExpectation
  calc
    (priorSame (A.popSize r)).E (fun u => (A.design r).E (fun w =>
        φ (observe (A.popSize r) M (A.groups r) (A.treated r)
          (samePriorSchedule (A.popSize r) M u) w))) =
        (A.design r).E (fun w => (priorSame (A.popSize r)).E (fun u =>
          φ (observe (A.popSize r) M (A.groups r) (A.treated r)
            (samePriorSchedule (A.popSize r) M u) w))) :=
      finiteDesign_E_swap _ _ _
    _ = (A.design r).E (fun w => (priorIndependent (A.popSize r)).E (fun u =>
          φ (observe (A.popSize r) M (A.groups r) (A.treated r)
            (independentPriorSchedule (A.popSize r) M u) w))) := by
      apply (A.design r).E_congr
      intro w
      rw [← priorIndependent_E_select (observedArmSelector w)]
      apply (priorIndependent (A.popSize r)).E_congr
      intro u
      rw [observe_independent_eq_same_selected]
    _ = (priorIndependent (A.popSize r)).E (fun u => (A.design r).E (fun w =>
        φ (observe (A.popSize r) M (A.groups r) (A.treated r)
          (independentPriorSchedule (A.popSize r) M u) w))) :=
      (finiteDesign_E_swap _ _ _).symm

-- @node: prop:rademacher-mixture-separation
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:M,hM,A,p,rho,hrho,J,hGroupCountGrowth,hStableTreatmentFraction,hSamplingFractionLimit,hJohnsonOrthogonalDecomposition_of_gate,hKneserAdjacencySpectrum_of_gate), [the rademacher mixture separation result holds](goal). -/
theorem rademacher_mixture_separation {M : ℕ} (hM : 2 ≤ M) (A : ScheduleArray M)
    (p rho : ℝ) (hrho : 0 < rho)
    (J : ∀ r, JohnsonProjections (A.popSize r) M)
    (hGroupCountGrowth : GroupCountGrowth A)
    (hStableTreatmentFraction : StableTreatmentFraction A p)
    (hSamplingFractionLimit : SamplingFractionLimit A rho)
    (hJohnsonOrthogonalDecomposition_of_gate :
      ∀ r, JohnsonOrthogonalDecomposition (A.popSize r) M (J r))
    (hKneserAdjacencySpectrum_of_gate :
      ∀ r, KneserAdjacencySpectrum (A.popSize r) M) :
    (∀ r φ, sameObservedExpectation A r φ = independentObservedExpectation A r φ) ∧
    FiniteDesign.TendstoInProb (fun r => priorSame (A.popSize r))
      (fun r u => armVar (A.popSize r) M (A.groupSize_le r)
        (samePriorSchedule (A.popSize r) M u) true) (fun _ => 1 / (M : ℝ)) ∧
    FiniteDesign.TendstoInProb (fun r => priorSame (A.popSize r))
      (fun r u => armVar (A.popSize r) M (A.groupSize_le r)
        (samePriorSchedule (A.popSize r) M u) false) (fun _ => 1 / (M : ℝ)) ∧
    FiniteDesign.TendstoInProb (fun r => priorSame (A.popSize r))
      (fun r u => degreeOneEnergy (A.popSize r) M (by omega) (A.groupSize_le r)
        (J r) (samePriorSchedule (A.popSize r) M u)) (fun _ => 0) ∧
    FiniteDesign.TendstoInProb (fun r => priorIndependent (A.popSize r))
      (fun r u => degreeOneEnergy (A.popSize r) M (by omega) (A.groupSize_le r)
        (J r) (independentPriorSchedule (A.popSize r) M u)) (fun _ => 2 / (M : ℝ)) ∧
    FiniteDesign.TendstoInProb (fun r => priorSame (A.popSize r))
      (sameScaledVariance A) (fun _ => 1 / ((M : ℝ) * p * (1 - p))) ∧
    FiniteDesign.TendstoInProb (fun r => priorIndependent (A.popSize r))
      (independentScaledVariance A)
      (fun _ => 1 / ((M : ℝ) * p * (1 - p)) - 2 * rho / (M : ℝ)) ∧
    0 < 2 * rho / (M : ℝ) ∧
    2 / (M : ℝ) ≤ 1 / ((M : ℝ) * p * (1 - p)) - 2 * rho / (M : ℝ) ∧
    ∀ cSigma : ℝ, 0 < cSigma →
      cSigma < 1 / ((M : ℝ) * p * (1 - p)) - 2 * rho / (M : ℝ) →
      Tendsto (fun r => (priorSame (A.popSize r)).Pr
        (fun u => cSigma ≤ sameScaledVariance A r u)) atTop (nhds 1) ∧
      Tendsto (fun r => (priorIndependent (A.popSize r)).Pr
        (fun u => cSigma ≤ independentScaledVariance A r u)) atTop (nhds 1) := by
  have hp0 := hStableTreatmentFraction.1
  have hp1 := hStableTreatmentFraction.2.1
  have hp := hStableTreatmentFraction.2.2
  have hrho1 := hSamplingFractionLimit.2.1
  have hpop := A.popSize_tendsto_atTop hGroupCountGrowth
  have hpopR : Tendsto (fun r => (A.popSize r : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hpop
  have hinvN : Tendsto (fun r => ((A.popSize r : ℝ))⁻¹) atTop (nhds 0) :=
    hpopR.inv_tendsto_atTop
  have hpInv : Tendsto (fun r => (A.treatmentFraction r)⁻¹) atTop (nhds p⁻¹) :=
    hp.inv₀ hp0.ne'
  have hq : Tendsto (fun r => 1 - A.treatmentFraction r) atTop (nhds (1 - p)) :=
    tendsto_const_nhds.sub hp
  have hqInv : Tendsto (fun r => (1 - A.treatmentFraction r)⁻¹)
      atTop (nhds (1 - p)⁻¹) := hq.inv₀ (by linarith)
  have hsameV1 := scheduleArray_same_armVar_tendstoInProb A hGroupCountGrowth true
  have hsameV0 := scheduleArray_same_armVar_tendstoInProb A hGroupCountGrowth false
  have hindV1 := scheduleArray_independent_armVar_tendstoInProb A hGroupCountGrowth true
  have hindV0 := scheduleArray_independent_armVar_tendstoInProb A hGroupCountGrowth false
  have hsameE := scheduleArray_same_degreeOne_tendstoInProb A J
  have hindE := scheduleArray_independent_degreeOne_tendstoInProb A hGroupCountGrowth J
    hJohnsonOrthogonalDecomposition_of_gate
  let rsame : (r : ℕ) → (Fin (A.popSize r) → Bool) → ℝ := fun r u =>
    armVar (A.popSize r) M (A.groupSize_le r)
        (samePriorSchedule (A.popSize r) M u) true / A.treatmentFraction r +
      armVar (A.popSize r) M (A.groupSize_le r)
        (samePriorSchedule (A.popSize r) M u) false / (1 - A.treatmentFraction r)
  let rind : (r : ℕ) → (Fin (A.popSize r) × Bool → Bool) → ℝ := fun r u =>
    armVar (A.popSize r) M (A.groupSize_le r)
        (independentPriorSchedule (A.popSize r) M u) true / A.treatmentFraction r +
      armVar (A.popSize r) M (A.groupSize_le r)
        (independentPriorSchedule (A.popSize r) M u) false / (1 - A.treatmentFraction r)
  have hsameR : FiniteDesign.TendstoInProb (fun r => priorSame (A.popSize r)) rsame
      (fun _ => 1 / ((M : ℝ) * p * (1 - p))) := by
    have h1 := FiniteDesign.TendstoInProb.deterministic_mul hsameV1 hpInv
    have h0 := FiniteDesign.TendstoInProb.deterministic_mul hsameV0 hqInv
    have hs := h1.add h0
    convert hs using 1
    · funext r u
      dsimp [rsame]
      simp only [div_eq_mul_inv]
      ring
    · funext r
      have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
      field_simp [hp0.ne', sub_ne_zero.mpr (ne_of_gt hp1)]
      ring
  have hindR : FiniteDesign.TendstoInProb (fun r => priorIndependent (A.popSize r)) rind
      (fun _ => 1 / ((M : ℝ) * p * (1 - p))) := by
    have h1 := FiniteDesign.TendstoInProb.deterministic_mul hindV1 hpInv
    have h0 := FiniteDesign.TendstoInProb.deterministic_mul hindV0 hqInv
    have hs := h1.add h0
    convert hs using 1
    · funext r u
      dsimp [rind]
      simp only [div_eq_mul_inv]
      ring
    · funext r
      have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
      field_simp [hp0.ne', sub_ne_zero.mpr (ne_of_gt hp1)]
      ring
  let lam : ℕ → ℝ := fun r => kneserEigenvalue (A.popSize r) M ⟨1, by omega⟩
  have hlam : Tendsto lam atTop (nhds 0) := by
    have hden : Tendsto (fun r => 1 - (M : ℝ) / (A.popSize r : ℝ))
        atTop (nhds 1) := by
      have hmzero : Tendsto (fun r => (M : ℝ) / (A.popSize r : ℝ))
          atTop (nhds 0) := by
        simpa [div_eq_mul_inv] using
          (tendsto_const_nhds.mul hinvN : Tendsto (fun r => (M : ℝ) *
            ((A.popSize r : ℝ))⁻¹) atTop (nhds ((M : ℝ) * 0)))
      simpa using tendsto_const_nhds.sub hmzero
    have hfrac : Tendsto (fun r => -(M : ℝ) / (A.popSize r : ℝ) /
        (1 - (M : ℝ) / (A.popSize r : ℝ))) atTop (nhds 0) := by
      have hnum : Tendsto (fun r => -(M : ℝ) / (A.popSize r : ℝ))
          atTop (nhds 0) := by
        simpa [div_eq_mul_inv] using
          (tendsto_const_nhds.mul hinvN : Tendsto (fun r => (-(M : ℝ)) *
            ((A.popSize r : ℝ))⁻¹) atTop (nhds ((-(M : ℝ)) * 0)))
      change Tendsto ((fun r => -(M : ℝ) / (A.popSize r : ℝ)) /
        (fun r => 1 - (M : ℝ) / (A.popSize r : ℝ))) atTop (nhds 0)
      simpa only [zero_div] using hnum.div hden (by norm_num : (1 : ℝ) ≠ 0)
    apply Tendsto.congr' _ hfrac
    filter_upwards [] with r
    have hGtwo : 2 ≤ A.groups r := by
      have := A.treated_pos r
      have := A.treated_lt r
      omega
    have h2Mr : 2 * M ≤ A.popSize r := by
      calc
        2 * M = M * 2 := Nat.mul_comm 2 M
        _ ≤ M * A.groups r := Nat.mul_le_mul_left M hGtwo
        _ ≤ A.popSize r := A.grouped_le r
    dsimp [lam]
    rw [kneserEigenvalue_one hM h2Mr]
    have hn : (A.popSize r : ℝ) ≠ 0 := by
      exact_mod_cast (lt_of_lt_of_le (Nat.mul_pos (by omega) (A.groups_pos r))
        (A.grouped_le r)).ne'
    field_simp
  have hGlambda : Tendsto (fun r => (A.groups r : ℝ) * lam r)
      atTop (nhds (-rho)) := by
    let coeff : ℕ → ℝ := fun r =>
      (M : ℝ) * (A.groups r : ℝ) / ((A.popSize r : ℝ) - M)
    have hden : Tendsto (fun r => 1 - (M : ℝ) / (A.popSize r : ℝ))
        atTop (nhds 1) := by
      have hz : Tendsto (fun r => (M : ℝ) / (A.popSize r : ℝ))
          atTop (nhds 0) := by
        simpa [div_eq_mul_inv] using
          (tendsto_const_nhds.mul hinvN : Tendsto (fun r => (M : ℝ) *
            ((A.popSize r : ℝ))⁻¹) atTop (nhds ((M : ℝ) * 0)))
      simpa using tendsto_const_nhds.sub hz
    have hc : Tendsto coeff atTop (nhds rho) := by
      have hquot := hSamplingFractionLimit.2.2.div hden (by norm_num : (1 : ℝ) ≠ 0)
      convert hquot using 1
      · funext r
        dsimp [coeff, ScheduleArray.grouped]
        have hn : (A.popSize r : ℝ) ≠ 0 := by
          exact_mod_cast (lt_of_lt_of_le (Nat.mul_pos (by omega) (A.groups_pos r))
            (A.grouped_le r)).ne'
        field_simp
        push_cast
        ring
      · norm_num
    have hneg : Tendsto (fun r => -coeff r) atTop (nhds (-rho)) := hc.neg
    apply Tendsto.congr' _ hneg
    filter_upwards [] with r
    have hGtwo : 2 ≤ A.groups r := by
      have := A.treated_pos r
      have := A.treated_lt r
      omega
    have h2Mr : 2 * M ≤ A.popSize r := by
      calc
        2 * M = M * 2 := Nat.mul_comm 2 M
        _ ≤ M * A.groups r := Nat.mul_le_mul_left M hGtwo
        _ ≤ A.popSize r := A.grouped_le r
    dsimp [lam, coeff]
    rw [kneserEigenvalue_one hM h2Mr]
    ring
  have hOneMinusLam : Tendsto (fun r => 1 - lam r) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hlam
  have htreatTwo : ∀ᶠ r in atTop, 2 ≤ A.treated r := by
    have hlower := (tendsto_order.1 hp).1 (p / 2) (by linarith)
    have hGlarge := (tendsto_natCast_atTop_atTop.comp hGroupCountGrowth).eventually_gt_atTop
      (4 / p)
    filter_upwards [hlower, hGlarge] with r hfr hGr
    by_contra ht
    have htone : A.treated r = 1 := by
      have := A.treated_pos r
      omega
    have hGpos : (0 : ℝ) < A.groups r := by exact_mod_cast A.groups_pos r
    unfold ScheduleArray.treatmentFraction pFrac at hfr
    rw [htone] at hfr
    norm_num at hfr
    have hpG : 4 < p * (A.groups r : ℝ) := by
      simpa [mul_comm] using (div_lt_iff₀ hp0).1 hGr
    have : p * (A.groups r : ℝ) < 2 := by
      rw [← one_div] at hfr
      have hh := mul_lt_mul_of_pos_right hfr hGpos
      calc
        p * (A.groups r : ℝ) =
            (p / 2 * (A.groups r : ℝ)) * 2 := by ring
        _ < (1 / (A.groups r : ℝ) * (A.groups r : ℝ)) * 2 := by
          gcongr
        _ = 2 := by field_simp
    linarith
  have hcontrolTwo : ∀ᶠ r in atTop, 2 ≤ A.controls r := by
    have hupper := (tendsto_order.1 hp).2 ((1 + p) / 2) (by linarith)
    have hGlarge := (tendsto_natCast_atTop_atTop.comp hGroupCountGrowth).eventually_gt_atTop
      (4 / (1 - p))
    filter_upwards [hupper, hGlarge] with r hfr hGr
    by_contra hc
    have hcone : A.controls r = 1 := by
      have : 0 < A.controls r := by
        unfold ScheduleArray.controls
        have := A.treated_lt r
        omega
      omega
    have hGpos : (0 : ℝ) < A.groups r := by exact_mod_cast A.groups_pos r
    have hcast : (A.treated r : ℝ) = (A.groups r : ℝ) - 1 := by
      have hn : A.treated r = A.groups r - 1 := by
        unfold ScheduleArray.controls at hcone
        omega
      rw [hn, Nat.cast_sub (A.groups_pos r)]
      norm_num
    unfold ScheduleArray.treatmentFraction pFrac at hfr
    rw [hcast] at hfr
    have hqG : 4 < (1 - p) * (A.groups r : ℝ) := by
      simpa [mul_comm] using (div_lt_iff₀ (by linarith)).1 hGr
    have : (1 - p) * (A.groups r : ℝ) < 2 := by
      have hh := (div_lt_iff₀ hGpos).1 hfr
      field_simp at hh
      linarith
    linarith
  have hsameScaled : FiniteDesign.TendstoInProb (fun r => priorSame (A.popSize r))
      (sameScaledVariance A) (fun _ => 1 / ((M : ℝ) * p * (1 - p))) := by
    have hs := (FiniteDesign.TendstoInProb.deterministic_mul hsameR hOneMinusLam).add
      (FiniteDesign.TendstoInProb.deterministic_mul hsameE hGlambda)
    apply FiniteDesign.TendstoInProb.congr_eventually _ (by
      convert hs using 1; funext r; ring)
    filter_upwards [htreatTwo, hcontrolTwo] with r ht hc
    intro u
    let x : Fin (A.popSize r) → ℝ := fun i => rademacherSign (u i)
    have htable (z : Bool) : armTable (A.popSize r) M
        (samePriorSchedule (A.popSize r) M u) z = sampleMean M x := by
      simpa [x] using armTable_samePrior_eq_sampleMean (n := A.popSize r) (M := M) u z
    have htabled : (fun S => armTable (A.popSize r) M
        (samePriorSchedule (A.popSize r) M u) true S - armTable (A.popSize r) M
        (samePriorSchedule (A.popSize r) M u) false S) = sampleMean M (fun _ => 0) := by
      funext S
      rw [htable true, htable false]
      simp [sampleMean]
    simpa [sameScaledVariance, rsame, ScheduleArray.treatmentFraction,
      indepGroupVar, lam] using scaledSigmaSq_eq_of_additive_armTables hM
        (A.grouped_le r) ht (by simpa [ScheduleArray.controls] using hc)
        (A.treated_pos r) (A.treated_lt r) (A.groupSize_le r) (by
          have hGtwo : 2 ≤ A.groups r := by
            have := A.treated_pos r
            have := A.treated_lt r
            omega
          calc
            2 * M = M * 2 := Nat.mul_comm 2 M
            _ ≤ M * A.groups r := Nat.mul_le_mul_left M hGtwo
            _ ≤ A.popSize r := A.grouped_le r)
        (J r) (hJohnsonOrthogonalDecomposition_of_gate r)
        (hKneserAdjacencySpectrum_of_gate r) _ x x (fun _ => 0)
        (htable true) (htable false) htabled
  have hindScaled : FiniteDesign.TendstoInProb
      (fun r => priorIndependent (A.popSize r)) (independentScaledVariance A)
      (fun _ => 1 / ((M : ℝ) * p * (1 - p)) - 2 * rho / (M : ℝ)) := by
    have hs := (FiniteDesign.TendstoInProb.deterministic_mul hindR hOneMinusLam).add
      (FiniteDesign.TendstoInProb.deterministic_mul hindE hGlambda)
    apply FiniteDesign.TendstoInProb.congr_eventually _ (by
      convert hs using 1; funext r; ring)
    filter_upwards [htreatTwo, hcontrolTwo] with r ht hc
    intro u
    let x1 : Fin (A.popSize r) → ℝ := fun i => rademacherSign (u (i, true))
    let x0 : Fin (A.popSize r) → ℝ := fun i => rademacherSign (u (i, false))
    let xd : Fin (A.popSize r) → ℝ := fun i => x1 i - x0 i
    have htable (z : Bool) : armTable (A.popSize r) M
        (independentPriorSchedule (A.popSize r) M u) z =
        sampleMean M (fun i => rademacherSign (u (i, z))) :=
      armTable_independentPrior_eq_sampleMean u z
    have htabled : (fun S => armTable (A.popSize r) M
        (independentPriorSchedule (A.popSize r) M u) true S -
        armTable (A.popSize r) M (independentPriorSchedule (A.popSize r) M u) false S) =
        sampleMean M xd := by
      rw [htable true, htable false]
      funext S
      unfold sampleMean xd x1 x0
      rw [← sub_div, ← Finset.sum_sub_distrib]
      apply congrArg (fun q : ℝ => q / (M : ℝ))
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ S.1 <;> simp [hi]
    simpa [independentScaledVariance, rind, ScheduleArray.treatmentFraction,
      indepGroupVar, lam, x1, x0] using scaledSigmaSq_eq_of_additive_armTables hM
        (A.grouped_le r) ht (by simpa [ScheduleArray.controls] using hc)
        (A.treated_pos r) (A.treated_lt r) (A.groupSize_le r) (by
          have hGtwo : 2 ≤ A.groups r := by
            have := A.treated_pos r
            have := A.treated_lt r
            omega
          calc
            2 * M = M * 2 := Nat.mul_comm 2 M
            _ ≤ M * A.groups r := Nat.mul_le_mul_left M hGtwo
            _ ≤ A.popSize r := A.grouped_le r)
        (J r) (hJohnsonOrthogonalDecomposition_of_gate r)
        (hKneserAdjacencySpectrum_of_gate r) _ x1 x0 xd
        (by simpa [x1] using htable true) (by simpa [x0] using htable false) htabled
  have hgap : 0 < 2 * rho / (M : ℝ) := by positivity
  have hsmall : 2 / (M : ℝ) ≤
      1 / ((M : ℝ) * p * (1 - p)) - 2 * rho / (M : ℝ) := by
    have hpProd : p * (1 - p) ≤ 1 / 4 := by nlinarith [sq_nonneg (p - 1 / 2)]
    have hpProdPos : 0 < p * (1 - p) := mul_pos hp0 (by linarith)
    have hMreal : 0 < (M : ℝ) := by positivity
    have hinvBound : 4 ≤ 1 / (p * (1 - p)) := by
      rw [le_div_iff₀ hpProdPos]
      nlinarith
    calc
      2 / (M : ℝ) ≤ 1 / (M : ℝ) * (4 - 2 * rho) := by
        have : 2 ≤ 4 - 2 * rho := by linarith
        simpa [div_eq_mul_inv, mul_comm] using
          mul_le_mul_of_nonneg_left this (one_div_nonneg.mpr hMreal.le)
      _ ≤ 1 / (M : ℝ) * (1 / (p * (1 - p)) - 2 * rho) := by
        gcongr
      _ = 1 / ((M : ℝ) * p * (1 - p)) - 2 * rho / (M : ℝ) := by
        field_simp
  refine ⟨fun r φ => sameObservedExpectation_eq_independent A r φ,
    hsameV1, hsameV0, hsameE, hindE, hsameScaled, hindScaled, hgap, hsmall, ?_⟩
  intro cSigma hc0 hcLt
  constructor
  · exact probability_ge_tendsto_one_of_tendstoInProb hsameScaled
      (lt_of_lt_of_le hcLt (by linarith [hgap]))
  · exact probability_ge_tendsto_one_of_tendstoInProb hindScaled hcLt

end CausalSmith.Experimentation.DenseGroupPartitionProjectionPhase
