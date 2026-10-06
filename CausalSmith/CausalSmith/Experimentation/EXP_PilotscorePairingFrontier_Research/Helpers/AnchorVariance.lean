module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.VarianceNormalization

/-!
# Variance normalization for the anchor class

This module supplies the latent design-domain support fact and the exact
finite-second-moment variance identity needed by anchor-class arguments.
-/

public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open MeasureTheory

variable {d m N : ℕ} {β cX CX : ℝ}

/-- An anchor-class law produces pilot covariates, main covariates, and the
auxiliary randomizer inside the matching design domain almost surely. -/
lemma anchorClass_latentTwoWaveLaw_designDomain_ae
    (P : Measure (UnitRecord d)) (hclass : AnchorClass P β cX CX) :
    ∀ᵐ w ∂latentTwoWaveLaw (m := m) (N := N) P,
      designInput w ∈ designDomain m N d := by
  letI : IsProbabilityMeasure P := hclass.covariate_density.1
  letI : IsProbabilityMeasure fairCoin := fairCoin_probability
  letI : IsProbabilityMeasure (pilotUnitLaw P) :=
    pilotUnitLaw_probability P hclass.covariate_density.1
  letI : IsProbabilityMeasure randomizerLaw := randomizerLaw_probability
  have hcube_meas : MeasurableSet (cube d) := by
    unfold cube
    measurability
  have hXmap : ∀ᵐ x ∂P.map Prod.fst, x ∈ cube d := by
    change cube d ∈ ae (P.map Prod.fst)
    rw [mem_ae_iff]
    apply hclass.covariate_density.2.1
    simp [cubeMeasure, hcube_meas]
  have hX : ∀ᵐ u ∂P, u.1 ∈ cube d :=
    ae_of_ae_map measurable_fst.aemeasurable hXmap
  have hpilot : ∀ᵐ v ∂pilotUnitLaw P, v.1 ∈ cube d := by
    unfold pilotUnitLaw
    have hm : Measurable (fun ua : UnitRecord d × Bool => observedPilot ua.1 ua.2) := by
      unfold observedPilot
      apply Measurable.prodMk
      · fun_prop
      apply Measurable.prodMk
      · fun_prop
      apply Measurable.ite
      · exact measurable_snd (measurableSet_singleton true)
      · fun_prop
      · fun_prop
    rw [ae_map_iff hm.aemeasurable (by measurability)]
    rw [Measure.ae_prod_iff_ae_ae (by measurability)]
    filter_upwards [hX] with u hu
    filter_upwards [] with a
    simpa [observedPilot] using hu
  have hpilots : ∀ᵐ p ∂Measure.pi (fun _ : Fin m => pilotUnitLaw P),
      ∀ r, (p r).1 ∈ cube d := by
    apply Measure.ae_pi_le_pi
    exact Filter.eventually_pi fun _ => hpilot
  have hmains : ∀ᵐ us ∂Measure.pi (fun _ : Fin N => P),
      ∀ i, (us i).1 ∈ cube d := by
    apply Measure.ae_pi_le_pi
    exact Filter.eventually_pi fun _ => hX
  have hU : ∀ᵐ u ∂randomizerLaw, u ∈ Set.Icc (0 : ℝ) 1 := by
    unfold randomizerLaw
    exact ae_restrict_mem measurableSet_Icc
  have hdommeas : MeasurableSet
      {w : WaveInput m N d | designInput w ∈ designDomain m N d} := by
    unfold designInput designDomain cube
    measurability
  unfold latentTwoWaveLaw
  rw [Measure.ae_prod_iff_ae_ae hdommeas]
  rw [Measure.ae_prod_iff_ae_ae (by
    unfold designInput designDomain cube
    measurability)]
  filter_upwards [hpilots] with p hp
  filter_upwards [hmains] with us hus
  filter_upwards [hU] with u hu
  exact ⟨hp, hus, hu⟩

/-- Every anchor-class law has a canonical half-sum score for which the paired
estimator is exactly unbiased and its normalized variance is the efficiency
bound plus four times the matching risk. -/
lemma anchorClass_variance_normalization
    (P : Measure (UnitRecord d)) (hclass : AnchorClass P β cX CX)
    (D : Design m N d) (hD : MatchingDesignClass D)
    (hm : 1 ≤ m) (hN : Even N) (hN2 : 2 ≤ N) :
    let g : XSpace d → ℝ := Classical.choose hclass.score_version
    (∫ wz, pairedEstimator N wz ∂experimentLaw (m := m) (N := N) P
      (fun w => pairedCoinLaw (D (designInput w)))) = ate P ∧
      (N : ℝ) * realVariance (experimentLaw (m := m) (N := N) P
        (fun w => pairedCoinLaw (D (designInput w))))
        (pairedEstimator N) = efficiencyBound P + 4 * risk P g D := by
  let g : XSpace d → ℝ := Classical.choose hclass.score_version
  have hg : IsHalfSumVersion P g := (Classical.choose_spec hclass.score_version).1
  have hdom : ∀ᵐ w ∂latentTwoWaveLaw (m := m) (N := N) P,
      designInput w ∈ designDomain m N d :=
    anchorClass_latentTwoWaveLaw_designDomain_ae P hclass
  exact variance_normalization_L2 P g D hclass.covariate_density.1
    hclass.second_moment0 hclass.second_moment1 hg hD hdom hm hN hN2

end CausalSmith.Experimentation.PilotscorePairingFrontier
