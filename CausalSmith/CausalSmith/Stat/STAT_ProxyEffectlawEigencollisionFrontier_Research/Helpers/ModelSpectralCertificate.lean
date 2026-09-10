import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.ModelSpectralConstruction
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.AmbientOperatorBridge

/-!
The model-local bounded real-diagonalization certificate used by the gap-free modulus.
-/

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open scoped Matrix.Norms.L2Operator
open CausalSmith.Substrate.CollisionSafeSpectralLaw
open Causalean.Mathlib.Probability

-- @node: modelRealDiagonalization_targetFeature_entry_bound
lemma targetFeature_entry_bound {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (P : MeasureTheory.Measure (FullData k dx dz)) [MeasureTheory.IsProbabilityMeasure P]
    (hk : 2 ≤ k) (hkx : k ≤ dx) (hL : 1 ≤ L) (hpi : 0 < pi0)
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P)
    (i : Fin dx) (u : Fin k) : |targetFeature P i u| ≤ L := by
  have hclass : 0 < P (latentClass u) :=
    lt_of_lt_of_le
      (latentCell_pos_of_latentArmPositivity P hpi hM.latentArmPositivity u false)
      (MeasureTheory.measure_mono fun _ hw => hw.1)
  let mu := normalizedRestrict P (latentClass u)
  let _ : MeasureTheory.IsProbabilityMeasure mu :=
    normalizedRestrict_isProbabilityMeasure (measurableSet_latentClass u) hclass
  have hboundP := (proxy_coordinate_bounds_of_model P hk hkx hM).1
  have hbound : ∀ᵐ w ∂mu, |w.X i| ≤ L :=
    (ae_normalizedRestrict_iff hclass).mpr <|
      MeasureTheory.ae_restrict_of_ae (hboundP.mono fun w hw => hw i)
  have hint : MeasureTheory.Integrable (fun w : FullData k dx dz => w.X i) mu :=
    MeasureTheory.Integrable.of_bound
      ((measurable_pi_apply i).comp measurable_fullData_X).aestronglyMeasurable L hbound
  rw [targetFeature, conditionalMean_eq_normalizedRestrictedIntegral hclass]
  unfold normalizedRestrictedIntegral
  calc
    |∫ w, w.X i ∂mu| ≤ ∫ w, |w.X i| ∂mu := MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ _w, L ∂mu := MeasureTheory.integral_mono_ae hint.abs
      (MeasureTheory.integrable_const L) hbound
    _ = L := by simp

-- @node: modelRealDiagonalization_model_certificate
theorem model_realDiagonalization_certificate
    {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (P : MeasureTheory.Measure (FullData k dx dz)) [MeasureTheory.IsProbabilityMeasure P]
    (hk : 2 ≤ k) (hkx : k ≤ dx) (hkz : k ≤ dz) (hL : 1 ≤ L)
    (hpi : 0 < pi0) (hpiMax : pi0 ≤ 1 / (2 * k : ℝ))
    (hsigma : 0 < sigma0) (hsigmaMax : sigma0 ≤ 1)
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P) :
    ∃ D : RealDiagonalization (AmbientOperatorBridge.ambientEffectOperator (obsSummary P)),
      D.conditionNumber ≤ conditionBound dx k L sigma0 ∧
      D.SpectrumBound (effectRadius dz L sigma0) ∧
      RepresentsAtomicLaw D (WithLp.toLp 2 (obsSummary P).mX)
        (WithLp.toLp 2 (firstBasis dx))
        (GapFreeModulusBridge.asNeutral (quotientLawRaw P (effectRadius dz L sigma0))) := by
  let B := targetFeature P
  have hsle (r : Fin k) : sigma0 ≤ (singularSystem B).sigma r := by
    rw [(singularSystem B).sigma_eq]
    exact hM.proxyRankMargin.2.2.trans <|
      (Matrix.toEuclideanLin B).singularValues_antitone <| by
        simpa using Nat.le_sub_one_of_lt r.isLt
  have hpos (r : Fin k) : 0 < (singularSystem B).sigma r := hsigma.trans_le (hsle r)
  let F := thinSignalFactorization B hpos
  letI : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  have hop : F.factorOperator (latentEffect P) =
      AmbientOperatorBridge.ambientEffectOperator (obsSummary P) := by
    calc
      F.factorOperator (latentEffect P) =
          (moorePenroseInverse B).transpose * Matrix.diagonal (latentEffect P) * B.transpose :=
        factorOperator_eq_moorePenrose F _
      _ = AmbientOperatorBridge.ambientEffectOperator (obsSummary P) :=
        (AmbientOperatorBridge.model_ambientEffectOperator_factorization
          P hk hkx hL hpi hsigma hM).symm
  rw [← hop]
  let D := F.realDiagonalization (latentEffect P)
  refine ⟨D, ?_, ?_, ?_⟩
  · apply F.diagonalization_conditionNumber_le (latentEffect P) (by linarith) hsigma
      (fun i u => targetFeature_entry_bound P hk hkx hL hpi hM i u)
      (fun i j => thinSignalFactorization_coordInv_entry_bound B hpos hsigma hsle i j)
    omega
  · intro i
    by_cases hi : i ∈ Set.range F.V.ambientExtension.signalIndex
    · obtain ⟨u, rfl⟩ := hi
      rw [show D.eigenvalue (F.V.ambientExtension.signalIndex u) = latentEffect P u by
        exact ambientEigenvalue_signal F.V (latentEffect P) u]
      exact latentEffect_abs_le_of_model P hk hkx hkz hL hpi hsigma hM u
    · rw [show D.eigenvalue i = 0 by exact ambientEigenvalue_nonsignal F.V _ i hi]
      have hr : 0 ≤ effectRadius dz L sigma0 := by unfold effectRadius; positivity
      simpa using hr
  · apply AmbientOperatorBridge.represents_raw_quotientLaw D
      (targetFeature P) (latentMass P) (latentEffect P)
    · exact congrArg (WithLp.toLp 2) (AmbientOperatorBridge.obsSummary_mX_factorization P hpi hM)
    · simpa using AmbientOperatorBridge.targetFeature_transpose_firstBasis P hk hkx hpi hM
    · intro f hf0
      exact realDiagonalization_applyFunction_moorePenrose F (latentEffect P) f hf0
    · apply AmbientOperatorBridge.moorePenroseInverse_mul_eq_one_of_injective
      rw [LinearMap.injective_iff_forall_lt_finrank_singularValues_pos]
      intro i hi
      have hik : i ≤ k - 1 := by
        simpa using (Nat.le_sub_one_of_lt (by simpa using hi))
      exact lt_of_lt_of_le (lt_of_lt_of_le hsigma hM.proxyRankMargin.2.2)
        ((Matrix.toEuclideanLin (targetFeature P)).singularValues_antitone hik)

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
