import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.Kernel

/-!
# Canonical second-moment contrast integral

This file isolates the density cancellation that rewrites a canonical
second-moment contrast as the rational mechanism integral used by both the
explicit sparse witness and the analytic perturbation argument.
-/

open MeasureTheory Set Filter
open scoped BigOperators

noncomputable section

namespace CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

/-- For a positive normalized mechanism and distinct intervention and ratio targets, the
canonical second-moment contrast equals the rational mechanism integral obtained by cancelling
the observational child-density factor.  Given [the stated inputs and conditions](hyp:hpos,hji), [the stated conclusion](goal) follows. -/
-- @node: canonical_secondMomentContrast_eq_integral_for_witness
lemma canonical_secondMomentContrast_eq_integral_for_witness
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (hpos : PositiveNormalizedSmoothMechanisms G θ) {j i : Fin n}
    (hji : j ≠ i) :
    secondMomentContrast (canonicalObservedWorld G θ (Equiv.refl (Fin n))) j i =
      ∫ v in latentCube n,
        (θ.q i (v i)) ^ 2 * (θ.q j (v j) - θ.p j v) *
          (∏ l ∈ (Finset.univ.erase i).erase j, θ.p l v) / θ.p i v := by
  let μ : Measure (LatentState n) := volume.restrict (latentCube n)
  let r : LatentState n → ℝ := fun v => θ.q i (v i) / θ.p i v
  have hcube : MeasurableSet (latentCube n) := by
    rw [latentCube]
    exact MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hcubeCompact : IsCompact (latentCube n) := by
    rw [latentCube]
    exact isCompact_univ_pi fun _ => isCompact_Icc
  have hpcont (l : Fin n) : ContinuousOn (θ.p l) (latentCube n) :=
    (hpos.2.2.1 l).continuousOn
  have hqcont (l : Fin n) : ContinuousOn (fun v : LatentState n => θ.q l (v l))
      (latentCube n) :=
    (hpos.2.2.2.1 l).continuousOn.comp ((continuous_apply l).continuousOn)
      (fun v hv => hv l (Set.mem_univ l))
  have hrcont : ContinuousOn r (latentCube n) := by
    exact (hqcont i).div (hpcont i) fun v hv => ne_of_gt (hpos.1 i v hv)
  have hobscont : ContinuousOn (observationalDensity θ) (latentCube n) := by
    unfold observationalDensity
    exact continuousOn_finsetProd _ fun l _ => hpcont l
  have hintcont : ContinuousOn (interventionalDensity θ j) (latentCube n) := by
    unfold interventionalDensity
    exact (hqcont j).mul (continuousOn_finsetProd _ fun l _ => hpcont l)
  have hobsint : Integrable (fun v => observationalDensity θ v * r v ^ 2) μ := by
    exact (hobscont.mul (hrcont.pow 2)).integrableOn_compact hcubeCompact
  have hintint : Integrable (fun v => interventionalDensity θ j v * r v ^ 2) μ := by
    exact (hintcont.mul (hrcont.pow 2)).integrableOn_compact hcubeCompact
  have hobs : (∫ v, r v ^ 2 ∂observationalLaw θ) =
      ∫ v, observationalDensity θ v * r v ^ 2 ∂μ := by
    unfold observationalLaw
    rw [integral_withDensity_eq_integral_toReal_smul₀]
    · apply integral_congr_ae
      filter_upwards [ae_restrict_mem hcube] with v hv
      rw [ENNReal.toReal_ofReal (le_of_lt (by
        unfold observationalDensity
        exact Finset.prod_pos fun l _ => hpos.1 l v hv))]
      rfl
    · exact (hobscont.aestronglyMeasurable hcube).aemeasurable.ennreal_ofReal
    · filter_upwards with v
      exact ENNReal.ofReal_lt_top
  have hint : (∫ v, r v ^ 2 ∂interventionalLaw θ j) =
      ∫ v, interventionalDensity θ j v * r v ^ 2 ∂μ := by
    unfold interventionalLaw
    rw [integral_withDensity_eq_integral_toReal_smul₀]
    · apply integral_congr_ae
      filter_upwards [ae_restrict_mem hcube] with v hv
      rw [ENNReal.toReal_ofReal (le_of_lt (by
        unfold interventionalDensity
        exact mul_pos (hpos.2.1 j (v j) (hv j (Set.mem_univ j)))
          (Finset.prod_pos fun l _ => hpos.1 l v hv)))]
      rfl
    · exact (hintcont.aestronglyMeasurable hcube).aemeasurable.ennreal_ofReal
    · filter_upwards with v
      exact ENNReal.ofReal_lt_top
  unfold secondMomentContrast
  change (∫ v, r v ^ 2 ∂interventionalLaw θ j) -
    (∫ v, r v ^ 2 ∂observationalLaw θ) = _
  rw [hint, hobs, ← integral_sub hintint hobsint]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hcube] with v hv
  have hpi : θ.p i v ≠ 0 := ne_of_gt (hpos.1 i v hv)
  have hinterDensity : interventionalDensity θ j v =
      θ.q j (v j) * θ.p i v *
        (∏ l ∈ (Finset.univ.erase i).erase j, θ.p l v) := by
    unfold interventionalDensity
    have hprod : (∏ l ∈ Finset.univ.erase j, θ.p l v) =
        θ.p i v * (∏ l ∈ (Finset.univ.erase j).erase i, θ.p l v) := by
      rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem
        (Finset.mem_erase.mpr ⟨Ne.symm hji, Finset.mem_univ i⟩)]
      simp only [Finset.sdiff_singleton_eq_erase]
    rw [hprod, Finset.erase_right_comm]
    ring
  have hobsDensity : observationalDensity θ v =
      θ.p i v * θ.p j v *
        (∏ l ∈ (Finset.univ.erase i).erase j, θ.p l v) := by
    unfold observationalDensity
    rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i)]
    simp only [Finset.sdiff_singleton_eq_erase]
    rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem
      (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)]
    simp only [Finset.sdiff_singleton_eq_erase]
    ring
  unfold r
  rw [hinterDensity, hobsDensity]
  field_simp

end CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity
