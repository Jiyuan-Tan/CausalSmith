import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.TObservedVMWMarginInclusion
import Causalean.Mathlib.IndepIntegral

/-!
Paper-local conditional-moment identities used in the outcome-weighted proxy factorization.
-/

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open MeasureTheory Set ProbabilityTheory
open Causalean.Mathlib.Probability

/-- Armwise latent ignorability identifies the potential-outcome mean on a positive
latent-treatment cell with its latent-class mean. -/
-- @node: outcomeFactorization_conditionalMean_potential_latentCell
lemma conditionalMean_potential_latentCell
    {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hpi : 0 < pi0)
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P)
    (u : Fin k) (t : Bool) :
    conditionalMean P (latentCell u t) (potential t) = latentMean P t u := by
  let C : Set (FullData k dx dz) := latentClass u
  let A : Set (FullData k dx dz) := {w | w.T = t}
  let μ := normalizedRestrict P C
  have hcellpos := latentCell_pos_of_latentArmPositivity P hpi hM.latentArmPositivity u t
  have hCpos : 0 < P C := lt_of_lt_of_le hcellpos <| measure_mono <| by
    intro w hw
    exact hw.1
  let _ : IsProbabilityMeasure μ :=
    normalizedRestrict_isProbabilityMeasure (measurableSet_latentClass u) hCpos
  have hfac := latentIgnorability_to_normalizedFactorization
    hM.latentIgnorability u t hCpos
  have hInd : IndepFun (fun w : FullData k dx dz => w.T) (potential t) μ :=
    (indepFun_of_boundedTestFactorization (measurable_potential t)
      measurable_fullData_T hfac).symm
  have hdrop := hInd.integral_restrict_preimage_eq_mul
    measurable_fullData_T.aemeasurable (measurable_potential t).aemeasurable
    (measurableSet_singleton t) (measurableSet_fullDataArm t)
    (continuous_id.aestronglyMeasurable :
      AEStronglyMeasurable (fun x : ℝ => x) (μ.map (potential t)))
  have hA : (fun w : FullData k dx dz => w.T) ⁻¹' ({t} : Set Bool) = A := by
    ext w
    simp [A]
  rw [hA] at hdrop
  have hAC : A ∩ C = latentCell u t := by
    ext w
    simp [A, C, latentCell, latentClass, and_comm]
  have hmuA : (μ A).toReal = P.real (latentCell u t) / P.real C := by
    rw [normalizedRestrict_apply hCpos (measurableSet_fullDataArm t), hAC]
    simp [Measure.real]
    field_simp
  have hleft : (∫ w in A, potential t w ∂μ) =
      (P.real C)⁻¹ * ∫ w in latentCell u t, potential t w ∂P := by
    change (∫ w, potential t w ∂((P C)⁻¹ • P.restrict C).restrict A) = _
    rw [Measure.restrict_smul, Measure.restrict_restrict (measurableSet_fullDataArm t),
      hAC, MeasureTheory.integral_smul_measure, ENNReal.toReal_inv]
    simp [Measure.real]
  have hright : (∫ w, potential t w ∂μ) =
      (P.real C)⁻¹ * ∫ w in C, potential t w ∂P := by
    rw [← normalizedRestrictedIntegral]
    exact normalizedRestrictedIntegral_eq hCpos (potential t)
  simp only [id_eq] at hdrop
  rw [hleft, hright, hmuA] at hdrop
  unfold latentMean conditionalMean
  dsimp [C] at hdrop ⊢
  have hcellreal : P.real (latentCell u t) ≠ 0 :=
    ne_of_gt (ENNReal.toReal_pos hcellpos.ne' (measure_ne_top _ _))
  have hCreal : P.real (latentClass u) ≠ 0 :=
    ne_of_gt (ENNReal.toReal_pos hCpos.ne' (measure_ne_top _ _))
  field_simp at hdrop ⊢
  nlinarith

/-- Consistency replaces the observed outcome by the arm-specific potential outcome inside
a latent-treatment cell. -/
-- @node: outcomeFactorization_conditionalMean_observed_eq_potential
lemma conditionalMean_observed_eq_potential
    {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P)
    (u : Fin k) (t : Bool) :
    conditionalMean P (latentCell u t) (fun w => w.Y) =
      conditionalMean P (latentCell u t) (potential t) := by
  unfold conditionalMean
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hM.consistency,
    self_mem_ae_restrict (measurableSet_latentCell u t)] with w hcons hw
  have ht : w.T = t := hw.2
  simpa [ht] using hcons

/-- Consequently the observed outcome mean on each latent-treatment cell equals the
latent potential-outcome mean from the roadmap's factorization. -/
-- @node: outcomeFactorization_conditionalMean_observed_latentCell
lemma conditionalMean_observed_latentCell
    {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hpi : 0 < pi0)
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P)
    (u : Fin k) (t : Bool) :
    conditionalMean P (latentCell u t) (fun w => w.Y) = latentMean P t u := by
  rw [conditionalMean_observed_eq_potential P hM u t]
  exact conditionalMean_potential_latentCell P hpi hM u t

/-- Target-proxy separation remains valid after conditioning on treatment because the
separated second random element contains both the outcome and treatment coordinates. -/
-- @node: outcomeFactorization_conditionalMean_target_mul_observed
lemma conditionalMean_target_mul_observed
    {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hpi : 0 < pi0)
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P)
    (u : Fin k) (t : Bool) (j : Fin dx) :
    conditionalMean P (latentCell u t) (fun w => w.X j * w.Y) =
      targetFeature P j u * conditionalMean P (latentCell u t) (fun w => w.Y) := by
  let C : Set (FullData k dx dz) := latentClass u
  let A : Set (FullData k dx dz) := {w | w.T = t}
  let μ := normalizedRestrict P C
  have hcellpos := latentCell_pos_of_latentArmPositivity P hpi hM.latentArmPositivity u t
  have hCpos : 0 < P C := lt_of_lt_of_le hcellpos <| measure_mono <| by
    intro w hw
    exact hw.1
  let _ : IsProbabilityMeasure μ :=
    normalizedRestrict_isProbabilityMeasure (measurableSet_latentClass u) hCpos
  have hfac := targetProxySeparation_to_normalizedFactorization
    hM.targetProxySeparation u hCpos
  have hIndVec : IndepFun (fun w : FullData k dx dz => w.X)
      (fun w => (w.Y, w.T)) μ :=
    indepFun_of_boundedTestFactorization measurable_fullData_X
      (measurable_fullData_Y.prodMk measurable_fullData_T) hfac
  have hInd : IndepFun (fun w : FullData k dx dz => w.X j)
      (fun w => (w.Y, w.T)) μ :=
    hIndVec.comp (measurable_pi_apply j) measurable_id
  let psi : ℝ × Bool → ℝ := fun yt => if yt.2 = t then yt.1 else 0
  have hprod := hInd.integral_fun_comp_mul_comp
    (((measurable_pi_apply j).comp measurable_fullData_X).aemeasurable)
    ((measurable_fullData_Y.prodMk measurable_fullData_T).aemeasurable)
    (continuous_id.aestronglyMeasurable :
      AEStronglyMeasurable (fun x : ℝ => x) (μ.map fun w => w.X j))
    ((by
      dsimp [psi]
      exact Measurable.ite (measurable_snd (measurableSet_singleton t))
        measurable_fst measurable_const : Measurable psi).aestronglyMeasurable)
  have hleft : (∫ w, (fun x : ℝ => x) (w.X j) * psi (w.Y, w.T) ∂μ) =
      ∫ w in A, w.X j * w.Y ∂μ := by
    rw [← integral_indicator (measurableSet_fullDataArm t)]
    apply integral_congr_ae
    filter_upwards [] with w
    by_cases hw : w.T = t <;> simp [psi, hw]
  have hy : (∫ w, psi (w.Y, w.T) ∂μ) = ∫ w in A, w.Y ∂μ := by
    rw [← integral_indicator (measurableSet_fullDataArm t)]
    apply integral_congr_ae
    filter_upwards [] with w
    by_cases hw : w.T = t <;> simp [psi, hw]
  simp only [id_eq] at hprod
  rw [hleft, hy] at hprod
  have hAC : A ∩ C = latentCell u t := by
    ext w
    simp [A, C, latentCell, latentClass, and_comm]
  have scaleSet (f : FullData k dx dz → ℝ) :
      (∫ w in A, f w ∂μ) = (P.real C)⁻¹ * ∫ w in latentCell u t, f w ∂P := by
    change (∫ w, f w ∂((P C)⁻¹ • P.restrict C).restrict A) = _
    rw [Measure.restrict_smul, Measure.restrict_restrict (measurableSet_fullDataArm t),
      hAC, MeasureTheory.integral_smul_measure, ENNReal.toReal_inv]
    simp [Measure.real]
  have scaleClass : (∫ w, w.X j ∂μ) =
      (P.real C)⁻¹ * ∫ w in C, w.X j ∂P := by
    rw [← normalizedRestrictedIntegral]
    exact normalizedRestrictedIntegral_eq hCpos (fun w => w.X j)
  rw [scaleSet (fun w => w.X j * w.Y), scaleClass, scaleSet (fun w => w.Y)] at hprod
  unfold targetFeature conditionalMean
  dsimp [C] at hprod ⊢
  have hcellreal : P.real (latentCell u t) ≠ 0 :=
    ne_of_gt (ENNReal.toReal_pos hcellpos.ne' (measure_ne_top _ _))
  have hCreal : P.real (latentClass u) ≠ 0 :=
    ne_of_gt (ENNReal.toReal_pos hCpos.ne' (measure_ne_top _ _))
  field_simp at hprod ⊢
  nlinarith

/-- The cell target--outcome moment therefore factors into the target feature and the
latent potential-outcome mean. -/
-- @node: outcomeFactorization_conditionalMean_targetOutcome_latentCell
lemma conditionalMean_targetOutcome_latentCell
    {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hpi : 0 < pi0)
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P)
    (u : Fin k) (t : Bool) (j : Fin dx) :
    conditionalMean P (latentCell u t) (fun w => w.X j * w.Y) =
      targetFeature P j u * latentMean P t u := by
  rw [conditionalMean_target_mul_observed P hpi hM u t j,
    conditionalMean_observed_latentCell P hpi hM u t]

/-- Reference-proxy separation factors the outcome-weighted proxy product on each positive
latent-treatment cell. -/
-- @node: outcomeFactorization_conditionalMean_reference_targetOutcome
lemma conditionalMean_reference_targetOutcome
    {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hpi : 0 < pi0)
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P)
    (u : Fin k) (t : Bool) (i : Fin dz) (j : Fin dx) :
    conditionalMean P (latentCell u t) (fun w => w.Z i * w.X j * w.Y) =
      conditionalMean P (latentCell u t) (fun w => w.Z i) *
        conditionalMean P (latentCell u t) (fun w => w.X j * w.Y) := by
  let C : Set (FullData k dx dz) := latentCell u t
  let μ := normalizedRestrict P C
  have hCpos := latentCell_pos_of_latentArmPositivity P hpi hM.latentArmPositivity u t
  let _ : IsProbabilityMeasure μ :=
    normalizedRestrict_isProbabilityMeasure (measurableSet_latentCell u t) hCpos
  have hfac := referenceProxySeparation_to_normalizedFactorization
    hM.referenceProxySeparation u t hCpos
  have hIndVec : IndepFun (fun w : FullData k dx dz => w.Z)
      (fun w => (w.X, w.Y)) μ :=
    indepFun_of_boundedTestFactorization measurable_fullData_Z
      (measurable_fullData_X.prodMk measurable_fullData_Y) hfac
  have hInd : IndepFun (fun w : FullData k dx dz => w.Z i)
      (fun w => (w.X, w.Y)) μ :=
    hIndVec.comp (measurable_pi_apply i) measurable_id
  have hprod := hInd.integral_fun_comp_mul_comp
    (((measurable_pi_apply i).comp measurable_fullData_Z).aemeasurable)
    ((measurable_fullData_X.prodMk measurable_fullData_Y).aemeasurable)
    (continuous_id.aestronglyMeasurable :
      AEStronglyMeasurable (fun x : ℝ => x) (μ.map fun w => w.Z i))
    (((measurable_pi_apply j).comp measurable_fst).mul measurable_snd).aestronglyMeasurable
  rw [conditionalMean_eq_normalizedRestrictedIntegral hCpos,
    conditionalMean_eq_normalizedRestrictedIntegral hCpos,
    conditionalMean_eq_normalizedRestrictedIntegral hCpos]
  simpa only [normalizedRestrictedIntegral, id_eq, mul_assoc, Function.comp_apply,
    Pi.mul_apply] using hprod

/-- Combining the two proxy separations, consistency, and latent ignorability gives the
cellwise outcome-weighted factorization in equation (16). -/
-- @node: outcomeFactorization_latentCell_outcomeProxy
lemma latentCell_outcomeProxy_factorization
    {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hpi : 0 < pi0)
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P)
    (u : Fin k) (t : Bool) (i : Fin dz) (j : Fin dx) :
    conditionalMean P (latentCell u t) (fun w => w.Y * w.Z i * w.X j) =
      referenceFeature P t i u * latentMean P t u * targetFeature P j u := by
  rw [show (fun w : FullData k dx dz => w.Y * w.Z i * w.X j) =
      (fun w => w.Z i * w.X j * w.Y) by funext w; ring,
    conditionalMean_reference_targetOutcome P hpi hM u t i j,
    conditionalMean_targetOutcome_latentCell P hpi hM u t j]
  unfold referenceFeature
  ring

/-- The observed armwise outcome-weighted proxy moment has the roadmap's finite-mixture
factorization (16). -/
-- @node: outcomeFactorization_observedOutcomeProxyMoment
lemma observedOutcomeProxyMoment_factorization
    {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hk : 2 ≤ k) (hpi : 0 < pi0)
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P)
    (t : Bool) :
    observedOutcomeProxyMoment (obsSummary P) t =
      referenceFeature P t * latentArmWeights P t * Matrix.diagonal (latentMean P t) *
        (targetFeature P).transpose := by
  ext i j
  have hint : ∀ u : Fin k, IntegrableOn
      (fun w : FullData k dx dz => w.Y * w.Z i * w.X j) (latentCell u t) P := by
    intro u
    apply IntegrableOn.of_bound (measure_lt_top P (latentCell u t))
    · exact ((measurable_fullData_Y.mul
        ((measurable_pi_apply i).comp measurable_fullData_Z)).mul
          ((measurable_pi_apply j).comp measurable_fullData_X)).aestronglyMeasurable
    · exact ae_restrict_of_ae <| hM.boundedOutcomeProxyProduct.mono fun w hw => by
        rw [Real.norm_eq_abs]
        have hentry := abs_matrix_entry_le_matrixCLM_norm
          (w.Y • outerProduct w.Z w.X) i j
        simpa [outerProduct, mul_assoc] using hentry.trans hw
  have harmpos : 0 < P.real {w : FullData k dx dz | w.T = t} := by
    exact lt_of_lt_of_le (mul_pos (Nat.cast_pos.mpr (by omega)) hpi)
      (arm_mass_lower_of_latentArmPositivity P hM.latentArmPositivity t)
  have hmix := conditionalMean_fullDataArm_eq_sum_latentCell P t
    (fun w => w.Y * w.Z i * w.X j) hint harmpos
  have hobs : conditionalMean (obsLaw P) (obsArm t) (fun o => o.Y * o.Z i * o.X j) =
      conditionalMean P {w | w.T = t} (fun w => w.Y * w.Z i * w.X j) := by
    exact conditionalMean_obsArm_eq_fullDataArm P t _ <| by
      exact (measurable_obs_Y.mul ((measurable_pi_apply i).comp measurable_obs_Z)).mul
        ((measurable_pi_apply j).comp measurable_obs_X)
  have heval : observedOutcomeProxyMoment (obsSummary P) t i j =
      conditionalMean (obsLaw P) (obsArm t) (fun o => o.Y * o.Z i * o.X j) := by
    cases t <;> rfl
  rw [heval, hobs, hmix]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, latentArmWeights,
    Matrix.diagonal_apply, mul_ite, mul_zero]
  apply Finset.sum_congr rfl
  intro u _
  rw [latentCell_outcomeProxy_factorization P hpi hM u t i j]
  simp [referenceFeature, targetFeature]
  ring

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
