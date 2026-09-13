import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.Decoder
import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.FiniteDensityBridge

/-!
# Structural pieces of the exact population decoder

This file collects paper-local consequences of the primitive observed-world assumptions that
feed directly into the exact population decoder.
-/

open MeasureTheory Set
open Causalean.Mathlib.MeasureTheory

noncomputable section

namespace CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

private lemma closure_interior_latentCube (n : ℕ) :
    closure (interior (latentCube n)) = latentCube n := by
  rw [latentCube, interior_pi_set Set.finite_univ, closure_pi_set]
  simp

private lemma unitCubeReference_support_eq_latentCube (n : ℕ) :
    Measure.support (Causalean.Graph.FiniteDensity.unitCubeReference (Fin n)) = latentCube n := by
  rw [Causalean.Graph.FiniteDensity.unitCubeReference_eq_volume_restrict]
  apply Set.Subset.antisymm
  · refine (Measure.support_restrict_subset).trans ?_
    change closure (latentCube n) ∩ Measure.support volume ⊆ latentCube n
    rw [closure_eq_iff_isClosed.mpr (by
      rw [latentCube]
      exact isClosed_set_pi fun _ _ ↦ isClosed_Icc)]
    exact Set.inter_subset_left
  · rw [← closure_interior_latentCube n]
    apply closure_minimal _ Measure.isClosed_support
    intro v hv
    exact Measure.interior_inter_support ⟨hv, by
      rw [Measure.support_eq_univ]
      trivial⟩

private lemma observationalLaw_support_eq_latentCube
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (hpos : PositiveNormalizedSmoothMechanisms G θ) :
    Measure.support (observationalLaw θ) = latentCube n := by
  letI : SigmaFinite Causalean.Graph.FiniteDensity.unitIntervalReference := by
    unfold Causalean.Graph.FiniteDensity.unitIntervalReference
    infer_instance
  let B := mechanismUnitCubeFactorization hpos
  let μ := Causalean.Graph.FiniteDensity.unitCubeReference (Fin n)
  have hobs_μ : observationalLaw θ ≪ μ := by
    rw [← mechanismUnitCubeFactorization_observationalMeasure hpos]
    exact withDensity_absolutelyContinuous _ _
  have hdens_ne : ∀ v, B.observationalDensity v ≠ 0 := by
    intro v
    unfold Causalean.Graph.FiniteDensity.Factorization.observationalDensity
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    change ENNReal.ofReal
      (θ.p i (Causalean.Graph.FiniteDensity.clampCube (Fin n) v)) ≠ 0
    exact (ENNReal.ofReal_pos.mpr (hpos.1 i _ (by
      simpa only [latentCube, Causalean.Graph.FiniteDensity.unitCube] using
        Causalean.Graph.FiniteDensity.clampCube_mem (Fin n) v))).ne'
  have hμ_obs : μ ≪ observationalLaw θ := by
    rw [← mechanismUnitCubeFactorization_observationalMeasure hpos]
    exact withDensity_absolutelyContinuous' B.measurable_observationalDensity.aemeasurable
      (Filter.Eventually.of_forall hdens_ne)
  apply Set.Subset.antisymm
  · exact hobs_μ.support_mono.trans (by
      rw [unitCubeReference_support_eq_latentCube n])
  · rw [← unitCubeReference_support_eq_latentCube n]
    exact hμ_obs.support_mono

/-- Strict positivity of every retained factor and the replacement density gives each latent
single-target intervention law the full closed cube as its support.  Given [the stated inputs and conditions](hyp:hpos), [the stated conclusion](goal) follows. -/
lemma interventionalLaw_support_eq_latentCube
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (hpos : PositiveNormalizedSmoothMechanisms G θ) (e : Fin n) :
    Measure.support (interventionalLaw θ (W.targetPerm e)) = latentCube n := by
  letI : SigmaFinite Causalean.Graph.FiniteDensity.unitIntervalReference := by
    unfold Causalean.Graph.FiniteDensity.unitIntervalReference
    infer_instance
  let B := mechanismUnitCubeFactorization hpos
  let q := mechanismInterventionDensity W hpos e
  let μ := Causalean.Graph.FiniteDensity.unitCubeReference (Fin n)
  have hint_μ : interventionalLaw θ (W.targetPerm e) ≪ μ := by
    rw [← mechanismUnitCubeFactorization_interventionMeasure W hpos e]
    exact withDensity_absolutelyContinuous _ _
  have hdens_ne : ∀ v, B.interventionDensity (W.targetPerm e) q v ≠ 0 := by
    intro v
    apply mul_ne_zero
    · change ENNReal.ofReal
        (θ.q (W.targetPerm e) (max 0 (min 1 (v (W.targetPerm e))))) ≠ 0
      apply (ENNReal.ofReal_pos.mpr (hpos.2.1 (W.targetPerm e) _ ?_)).ne'
      exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
    · unfold Causalean.Graph.FiniteDensity.Factorization.partialDensity
      apply Finset.prod_ne_zero_iff.mpr
      intro i _
      change ENNReal.ofReal
        (θ.p i (Causalean.Graph.FiniteDensity.clampCube (Fin n) v)) ≠ 0
      exact (ENNReal.ofReal_pos.mpr (hpos.1 i _ (by
        simpa only [latentCube, Causalean.Graph.FiniteDensity.unitCube] using
          Causalean.Graph.FiniteDensity.clampCube_mem (Fin n) v))).ne'
  have hμ_int : μ ≪ interventionalLaw θ (W.targetPerm e) := by
    rw [← mechanismUnitCubeFactorization_interventionMeasure W hpos e]
    exact withDensity_absolutelyContinuous'
      (B.measurable_interventionDensity (W.targetPerm e) q).aemeasurable
      (Filter.Eventually.of_forall hdens_ne)
  apply Set.Subset.antisymm
  · exact hint_μ.support_mono.trans (by
      rw [unitCubeReference_support_eq_latentCube n])
  · rw [← unitCubeReference_support_eq_latentCube n]
    exact hμ_int.support_mono

-- @node: observedLaw_support_eq_observedSupport
/-- The observational observed law has exactly the image of the latent cube as its support.  Given [the stated inputs and conditions](hyp:hpos,hmix,hone), [the stated conclusion](goal) follows. -/
lemma observedLaw_support_eq_observedSupport
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W) :
    Measure.support (W.law 0) = observedSupport G W := by
  have hcube_compact : IsCompact (latentCube n) := by
    rw [latentCube]
    exact isCompact_univ_pi fun _ => isCompact_Icc
  have hsupport_closed : IsClosed (observedSupport G W) := by
    exact (hcube_compact.image_of_continuousOn hmix.1.continuousOn).isClosed
  have hobs_cube : ∀ᵐ v ∂observationalLaw θ, v ∈ latentCube n := by
    filter_upwards [Measure.support_mem_ae (μ := observationalLaw θ)] with v hv
    rw [observationalLaw_support_eq_latentCube hpos] at hv
    exact hv
  have hcube_meas : MeasurableSet (latentCube n) := by
    rw [latentCube]
    exact MeasurableSet.pi Set.countable_univ (fun _ _ ↦ measurableSet_Icc)
  have hmixAE : AEMeasurable W.mix (observationalLaw θ) :=
    aemeasurable_of_supportMeasurableOn hcube_meas
      (ae_iff.mp hobs_cube) hmix.1.continuousOn.domRestrict.measurable
  have hfull : W.law 0 (observedSupport G W)ᶜ = 0 := by
    rw [hone.1, Measure.map_apply_of_aemeasurable hmixAE hsupport_closed.isOpen_compl.measurableSet]
    apply measure_mono_null (t := (latentCube n)ᶜ)
    · intro v hv hvcube
      exact hv ⟨v, hvcube, rfl⟩
    · exact ae_iff.mp hobs_cube
  apply Set.Subset.antisymm
  · exact Measure.support_subset_of_isClosed hsupport_closed (ae_iff.mpr hfull)
  · rintro x ⟨v, hv, rfl⟩
    rw [Measure.mem_support_iff_forall]
    intro U hU
    rcases mem_nhds_iff.mp hU with ⟨O, hOU, hOopen, hmixO⟩
    rw [hone.1]
    apply lt_of_lt_of_le _ (measure_mono hOU)
    rw [Measure.map_apply_of_aemeasurable hmixAE hOopen.measurableSet]
    have hpre : W.mix ⁻¹' O ∈ nhdsWithin v (latentCube n) :=
      (hmix.1.continuousOn v hv) (hOopen.mem_nhds hmixO)
    rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hpre with ⟨V, hV, hVsub⟩
    have hVpos : 0 < observationalLaw θ V :=
      (Measure.mem_support_iff_forall v).mp
        ((observationalLaw_support_eq_latentCube hpos).symm.subset hv) V hV
    rw [← Measure.measure_inter_eq_of_ae hobs_cube] at hVpos
    exact hVpos.trans_le (measure_mono (by simpa [inter_comm] using hVsub))

private lemma factorization_observationalMeasure_univ
    {n : ℕ} {G : Causalean.DAG (Fin n)}
    (B : Causalean.Graph.FiniteDensity.UnitCubeFactorization (Fin n) G) :
    B.observationalMeasure Set.univ = 1 := by
  classical
  letI : SigmaFinite Causalean.Graph.FiniteDensity.unitIntervalReference := by
    unfold Causalean.Graph.FiniteDensity.unitIntervalReference
    infer_instance
  let x : Fin n → ℝ := fun _ ↦ 0
  have hmarg := B.lmarginal_compl_observationalDensity_eq (A := ∅) (by
    intro i hi
    simp at hi)
  have hlin : ∫⁻ v, B.observationalDensity v ∂Measure.pi
      (fun _ : Fin n ↦ Causalean.Graph.FiniteDensity.unitIntervalReference) = 1 := by
    rw [MeasureTheory.lintegral_eq_lmarginal_univ x]
    simpa [Causalean.Graph.FiniteDensity.Factorization.partialDensity] using congrFun hmarg x
  rw [Causalean.Graph.FiniteDensity.Factorization.observationalMeasure,
    withDensity_apply _ MeasurableSet.univ]
  simpa using hlin

private lemma factorization_interventionMeasure_univ
    {n : ℕ} {G : Causalean.DAG (Fin n)}
    (B : Causalean.Graph.FiniteDensity.UnitCubeFactorization (Fin n) G) (j : Fin n)
    (q : Causalean.Graph.FiniteDensity.InterventionDensity j
      (fun _ : Fin n ↦ ℝ)
      (fun _ : Fin n ↦ Causalean.Graph.FiniteDensity.unitIntervalReference)) :
    B.interventionMeasure j q Set.univ = 1 := by
  classical
  letI : SigmaFinite Causalean.Graph.FiniteDensity.unitIntervalReference := by
    unfold Causalean.Graph.FiniteDensity.unitIntervalReference
    infer_instance
  let x : Fin n → ℝ := fun _ ↦ 0
  have hmarg := B.lmarginal_compl_interventionDensity_eq (A := ∅) (by
    intro i hi
    simp at hi) (by simp) q
  have hlin : ∫⁻ v, B.interventionDensity j q v ∂Measure.pi
      (fun _ : Fin n ↦ Causalean.Graph.FiniteDensity.unitIntervalReference) = 1 := by
    rw [MeasureTheory.lintegral_eq_lmarginal_univ x]
    simpa [Causalean.Graph.FiniteDensity.Factorization.partialDensity] using congrFun hmarg x
  rw [Causalean.Graph.FiniteDensity.Factorization.interventionMeasure,
    withDensity_apply _ MeasurableSet.univ]
  simpa using hlin

/-- Normalized local factors make the observational latent law a probability measure.  Given [the stated inputs and conditions](hyp:hpos), [the stated conclusion](goal) follows. -/
lemma observationalLaw_isProbabilityMeasure
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (hpos : PositiveNormalizedSmoothMechanisms G θ) :
    IsProbabilityMeasure (observationalLaw θ) := by
  constructor
  rw [← mechanismUnitCubeFactorization_observationalMeasure hpos]
  exact factorization_observationalMeasure_univ (mechanismUnitCubeFactorization hpos)

/-- Normalized local and replacement factors make every interventional latent law a
probability measure.  Given [the stated inputs and conditions](hyp:hpos), [the stated conclusion](goal) follows. -/
lemma interventionalLaw_isProbabilityMeasure
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (hpos : PositiveNormalizedSmoothMechanisms G θ) (e : Fin n) :
    IsProbabilityMeasure (interventionalLaw θ (W.targetPerm e)) := by
  constructor
  rw [← mechanismUnitCubeFactorization_interventionMeasure W hpos e]
  exact factorization_interventionMeasure_univ (mechanismUnitCubeFactorization hpos)
    (W.targetPerm e) (mechanismInterventionDensity W hpos e)

-- @node: observedWorld_laws_isProbabilityMeasure
/-- The pushforward assumptions and normalized latent factors make every observed environment
law a probability measure.  Given [the stated inputs and conditions](hyp:hpos,hmix,hone), [the stated conclusion](goal) follows. -/
lemma observedWorld_laws_isProbabilityMeasure
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W) :
    ∀ e, IsProbabilityMeasure (W.law e) := by
  intro e
  let μ := Causalean.Graph.FiniteDensity.unitCubeReference (Fin n)
  have hcube : MeasurableSet (latentCube n) := by
    rw [latentCube]
    exact MeasurableSet.pi Set.countable_univ (fun _ _ ↦ measurableSet_Icc)
  have hμ_cube : μ (latentCube n)ᶜ = 0 := by
    simpa only [μ, latentCube, Causalean.Graph.FiniteDensity.unitCube] using
      Causalean.Graph.FiniteDensity.unitCubeReference_compl (Fin n)
  refine Fin.cases ?_ (fun i => ?_) e
  · letI : IsProbabilityMeasure (observationalLaw θ) :=
      observationalLaw_isProbabilityMeasure hpos
    have hobs_μ : observationalLaw θ ≪ μ := by
      rw [← mechanismUnitCubeFactorization_observationalMeasure hpos]
      exact withDensity_absolutelyContinuous _ _
    have hmixAE : AEMeasurable W.mix (observationalLaw θ) :=
      aemeasurable_of_supportMeasurableOn hcube (hobs_μ hμ_cube)
        hmix.1.continuousOn.domRestrict.measurable
    rw [hone.1]
    exact Measure.isProbabilityMeasure_map hmixAE
  · letI : IsProbabilityMeasure (interventionalLaw θ (W.targetPerm i)) :=
      interventionalLaw_isProbabilityMeasure W hpos i
    let B := mechanismUnitCubeFactorization hpos
    let q := mechanismInterventionDensity W hpos i
    have hint_μ : B.interventionMeasure (W.targetPerm i) q ≪ μ := by
      rw [Causalean.Graph.FiniteDensity.Factorization.interventionMeasure]
      exact withDensity_absolutelyContinuous _ _
    have hint_cube : interventionalLaw θ (W.targetPerm i) (latentCube n)ᶜ = 0 := by
      rw [← mechanismUnitCubeFactorization_interventionMeasure W hpos i]
      exact hint_μ hμ_cube
    have hmixAE : AEMeasurable W.mix (interventionalLaw θ (W.targetPerm i)) :=
      aemeasurable_of_supportMeasurableOn hcube hint_cube
        hmix.1.continuousOn.domRestrict.measurable
    rw [hone.2.1 i]
    exact Measure.isProbabilityMeasure_map hmixAE

/-- Transporting the latent canonical Radon--Nikodym ratio through the support diffeomorphism
does not change its law under any latent base measure dominated by the observational law.  Given [the stated inputs and conditions](hyp:hpos,hmix,hone,hρ), [the stated conclusion](goal) follows. -/
lemma canonicalRatio_map_eq_observedLawRatio_map_mix
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W)
    (i : Fin n) (ρ : Measure (LatentState n))
    (hρ : ρ ≪ observationalLaw θ) :
    Measure.map (fun v ↦ ((interventionalLaw θ (W.targetPerm i)).rnDeriv
        (observationalLaw θ) v).toReal) ρ =
      Measure.map (observedLawRatio W.law i) (Measure.map W.mix ρ) := by
  let m := interventionalLaw θ (W.targetPerm i)
  let ν := observationalLaw θ
  let S := latentCube n
  let T := observedSupport G W
  letI : IsProbabilityMeasure m := interventionalLaw_isProbabilityMeasure W hpos i
  letI : IsProbabilityMeasure ν := observationalLaw_isProbabilityMeasure hpos
  have hS : MeasurableSet S := by
    change MeasurableSet (latentCube n)
    rw [latentCube]
    exact MeasurableSet.pi Set.countable_univ (fun _ _ ↦ measurableSet_Icc)
  have hcompact : IsCompact S := by
    change IsCompact (latentCube n)
    rw [latentCube]
    exact isCompact_univ_pi fun _ => isCompact_Icc
  have hT : MeasurableSet T :=
    (hcompact.image_of_continuousOn hmix.1.continuousOn).isClosed.measurableSet
  have hmS : m Sᶜ = 0 := by
    change interventionalLaw θ (W.targetPerm i) (latentCube n)ᶜ = 0
    rw [← interventionalLaw_support_eq_latentCube W hpos i]
    exact Measure.measure_compl_support
  have hνS : ν Sᶜ = 0 := by
    change observationalLaw θ (latentCube n)ᶜ = 0
    rw [← observationalLaw_support_eq_latentCube hpos]
    exact Measure.measure_compl_support
  have hmn : m ≪ ν := interventionalLaw_absolutelyContinuous_observational W hpos i
  have hrn := rnDeriv_map_of_support_equiv m ν hmn S T hS hT hmS hνS
    W.mix W.unmix hmix.1.continuousOn.domRestrict.measurable
      hmix.2.1.continuousOn.domRestrict.measurable
    (fun x hx ↦ ⟨x, hx, rfl⟩)
    (fun y hy ↦ by
      rcases hy with ⟨x, hx, rfl⟩
      simpa only [hmix.2.2.1 x hx] using hx)
    hmix.2.2.1 hmix.2.2.2
  have hrnW :
      (fun v ↦ ((W.law i.succ).rnDeriv (W.law 0) (W.mix v)).toReal) =ᵐ[ν]
        (fun v ↦ (m.rnDeriv ν v).toReal) := by
    filter_upwards [hrn] with v hv
    change ((W.law i.succ).rnDeriv (W.law 0) (W.mix v)).toReal =
      ((interventionalLaw θ (W.targetPerm i)).rnDeriv (observationalLaw θ) v).toReal
    rw [hone.2.1 i, hone.1]
    exact congrArg ENNReal.toReal hv
  have hrnρ := hρ.ae_eq hrnW
  have hρS : ρ Sᶜ = 0 := hρ hνS
  have hmixρ : AEMeasurable W.mix ρ :=
    aemeasurable_of_supportMeasurableOn hS hρS
      hmix.1.continuousOn.domRestrict.measurable
  calc
    Measure.map (fun v ↦ (m.rnDeriv ν v).toReal) ρ =
        Measure.map (observedLawRatio W.law i ∘ W.mix) ρ :=
      Measure.map_congr hrnρ.symm
    _ = Measure.map (observedLawRatio W.law i) (Measure.map W.mix ρ) := by
      symm
      exact AEMeasurable.map_map_of_aemeasurable
        (measurable_observedLawRatio W.law i).aemeasurable hmixρ

/-- The observational latent law is concentrated on the closed latent cube.  Given [the stated inputs and conditions](hyp:hpos), [the stated conclusion](goal) follows. -/
-- @node: observationalLaw_ae_mem_latentCube
lemma observationalLaw_ae_mem_latentCube
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (hpos : PositiveNormalizedSmoothMechanisms G θ) :
    ∀ᵐ v ∂observationalLaw θ, v ∈ latentCube n := by
  let μ := Causalean.Graph.FiniteDensity.unitCubeReference (Fin n)
  have hobs_μ : observationalLaw θ ≪ μ := by
    rw [← mechanismUnitCubeFactorization_observationalMeasure hpos]
    exact withDensity_absolutelyContinuous _ _
  apply ae_iff.mpr
  change observationalLaw θ (latentCube n)ᶜ = 0
  exact hobs_μ (by
    simpa only [μ, latentCube, Causalean.Graph.FiniteDensity.unitCube] using
      Causalean.Graph.FiniteDensity.unitCubeReference_compl (Fin n))

/-- Strict positivity of all latent factors makes the observational and target-intervention
observed laws equivalent; this is the reverse direction not needed by the ratio-law bridge.  Given [the stated inputs and conditions](hyp:hpos,hmix,hone), [the stated conclusion](goal) follows. -/
lemma observedObservational_absolutelyContinuous_interventional
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W) (e : Fin n) :
    W.law 0 ≪ W.law e.succ := by
  let B := mechanismUnitCubeFactorization hpos
  let q := mechanismInterventionDensity W hpos e
  let μ := Causalean.Graph.FiniteDensity.unitCubeReference (Fin n)
  have hmeas_int : Measurable (B.interventionDensity (W.targetPerm e) q) := by
    unfold Causalean.Graph.FiniteDensity.Factorization.interventionDensity
    exact (q.measurable_density.comp (measurable_pi_apply _)).mul
      (Finset.measurable_prod _ fun i _ ↦ B.measurable_factor i)
  have hint_pos : ∀ v, B.interventionDensity (W.targetPerm e) q v ≠ 0 := by
    intro v
    unfold Causalean.Graph.FiniteDensity.Factorization.interventionDensity
    apply mul_ne_zero
    · change ENNReal.ofReal
          (θ.q (W.targetPerm e) (max 0 (min 1 (v (W.targetPerm e))))) ≠ 0
      exact (ENNReal.ofReal_pos.mpr (hpos.2.1 (W.targetPerm e) _ ⟨le_max_left _ _,
        max_le zero_le_one (min_le_left _ _)⟩)).ne'
    · exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ by
        change ENNReal.ofReal
          (θ.p i (Causalean.Graph.FiniteDensity.clampCube (Fin n) v)) ≠ 0
        exact (ENNReal.ofReal_pos.mpr (hpos.1 i _ (by
          simpa only [latentCube, Causalean.Graph.FiniteDensity.unitCube] using
            Causalean.Graph.FiniteDensity.clampCube_mem (Fin n) v))).ne'
  have hμ_int : μ ≪ B.interventionMeasure (W.targetPerm e) q := by
    rw [Causalean.Graph.FiniteDensity.Factorization.interventionMeasure]
    exact withDensity_absolutelyContinuous' hmeas_int.aemeasurable
      (Filter.Eventually.of_forall hint_pos)
  have hobs_μ : B.observationalMeasure ≪ μ := by
    rw [Causalean.Graph.FiniteDensity.Factorization.observationalMeasure]
    exact withDensity_absolutelyContinuous _ _
  have hlatentB : B.observationalMeasure ≪
      B.interventionMeasure (W.targetPerm e) q := hobs_μ.trans hμ_int
  have hlatent : observationalLaw θ ≪ interventionalLaw θ (W.targetPerm e) := by
    simpa only [B, q, mechanismUnitCubeFactorization_observationalMeasure hpos,
      mechanismUnitCubeFactorization_interventionMeasure W hpos e] using hlatentB
  let ν := interventionalLaw θ (W.targetPerm e)
  have hcube : MeasurableSet (latentCube n) := by
    rw [latentCube]
    exact MeasurableSet.pi Set.countable_univ (fun _ _ ↦ measurableSet_Icc)
  have hobs_cube : observationalLaw θ (latentCube n)ᶜ = 0 := by
    rw [← mechanismUnitCubeFactorization_observationalMeasure hpos]
    exact hobs_μ (by
      simpa only [μ, latentCube, Causalean.Graph.FiniteDensity.unitCube] using
        Causalean.Graph.FiniteDensity.unitCubeReference_compl (Fin n))
  have hint_μ : B.interventionMeasure (W.targetPerm e) q ≪ μ := by
    rw [Causalean.Graph.FiniteDensity.Factorization.interventionMeasure]
    exact withDensity_absolutelyContinuous _ _
  have hint_cube : ν (latentCube n)ᶜ = 0 := by
    change interventionalLaw θ (W.targetPerm e) (latentCube n)ᶜ = 0
    rw [← mechanismUnitCubeFactorization_interventionMeasure W hpos e]
    exact hint_μ (by
      simpa only [μ, latentCube, Causalean.Graph.FiniteDensity.unitCube] using
        Causalean.Graph.FiniteDensity.unitCubeReference_compl (Fin n))
  have hmixObs : AEMeasurable W.mix (observationalLaw θ) :=
    aemeasurable_of_supportMeasurableOn hcube hobs_cube
      hmix.1.continuousOn.domRestrict.measurable
  have hmixInt : AEMeasurable W.mix ν :=
    aemeasurable_of_supportMeasurableOn hcube hint_cube
      hmix.1.continuousOn.domRestrict.measurable
  let mix' := hmixInt.mk W.mix
  have heqInt : W.mix =ᵐ[ν] mix' := hmixInt.ae_eq_mk
  have heqObs : W.mix =ᵐ[observationalLaw θ] mix' := hlatent.ae_eq heqInt
  rw [hone.1, hone.2.1 e]
  calc
    Measure.map W.mix (observationalLaw θ) =
        Measure.map mix' (observationalLaw θ) := Measure.map_congr heqObs
    _ ≪ Measure.map mix' ν :=
      @Measure.AbsolutelyContinuous.map _ _ _ _ _ _ hlatent mix' hmixInt.measurable_mk
    _ = Measure.map W.mix ν := (Measure.map_congr heqInt).symm

/-- The supplied observed-world ratio agrees almost everywhere with the canonical law ratio,
and the law-selected rank construction is unchanged by a compatible representation.  Given [the stated inputs and conditions](hyp:hpos,hmix,hone), [the stated conclusion](goal) follows. -/
lemma observedWorldLawCoherent_of_assumptions
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W) :
    ObservedWorldLawCoherent W := by
  classical
  constructor
  · intro i
    let μ := Causalean.Graph.FiniteDensity.unitCubeReference (Fin n)
    have hcube : MeasurableSet (latentCube n) := by
      rw [latentCube]
      exact MeasurableSet.pi Set.countable_univ (fun _ _ ↦ measurableSet_Icc)
    have hμ_cube : μ (latentCube n)ᶜ = 0 := by
      simpa only [μ, latentCube, Causalean.Graph.FiniteDensity.unitCube] using
        Causalean.Graph.FiniteDensity.unitCubeReference_compl (Fin n)
    have hobs_μ : observationalLaw θ ≪ μ := by
      rw [← mechanismUnitCubeFactorization_observationalMeasure hpos]
      exact withDensity_absolutelyContinuous _ _
    have hobs_cube : observationalLaw θ (latentCube n)ᶜ = 0 := hobs_μ hμ_cube
    have hmixAE : AEMeasurable W.mix (observationalLaw θ) :=
      aemeasurable_of_supportMeasurableOn hcube hobs_cube
        hmix.1.continuousOn.domRestrict.measurable
    have hint_cube : interventionalLaw θ (W.targetPerm i) (latentCube n)ᶜ = 0 := by
      let B := mechanismUnitCubeFactorization hpos
      let q := mechanismInterventionDensity W hpos i
      have hint_μ : B.interventionMeasure (W.targetPerm i) q ≪ μ := by
        rw [Causalean.Graph.FiniteDensity.Factorization.interventionMeasure]
        exact withDensity_absolutelyContinuous _ _
      rw [← mechanismUnitCubeFactorization_interventionMeasure W hpos i]
      exact hint_μ hμ_cube
    have hmixAEInt : AEMeasurable W.mix
        (interventionalLaw θ (W.targetPerm i)) :=
      aemeasurable_of_supportMeasurableOn hcube hint_cube
        hmix.1.continuousOn.domRestrict.measurable
    have hrn_pos : ∀ᵐ x ∂W.law 0,
        0 < (W.law i.succ).rnDeriv (W.law 0) x :=
      by
        letI : IsProbabilityMeasure (observationalLaw θ) :=
          observationalLaw_isProbabilityMeasure hpos
        letI : IsProbabilityMeasure (interventionalLaw θ (W.targetPerm i)) :=
          interventionalLaw_isProbabilityMeasure W hpos i
        letI : IsProbabilityMeasure (W.law 0) := ⟨by
          rw [hone.1, Measure.map_apply_of_aemeasurable hmixAE MeasurableSet.univ,
            preimage_univ, measure_univ]⟩
        letI : IsProbabilityMeasure (W.law i.succ) := ⟨by
          rw [hone.2.1 i, Measure.map_apply_of_aemeasurable hmixAEInt MeasurableSet.univ,
            preimage_univ, measure_univ]⟩
        exact Measure.rnDeriv_pos'
          (observedObservational_absolutelyContinuous_interventional W hpos hmix hone i)
    filter_upwards [hone.2.2.1 i, hrn_pos] with x hx hrnpos
    have hposx : 0 < W.ratio i x := by
      by_contra hnot
      have hle : W.ratio i x ≤ 0 := le_of_not_gt hnot
      have : ENNReal.ofReal (W.ratio i x) = 0 := ENNReal.ofReal_eq_zero.mpr hle
      rw [hx] at this
      exact hrnpos.ne' this
    calc
      W.ratio i x = (ENNReal.ofReal (W.ratio i x)).toReal :=
        (ENNReal.toReal_ofReal hposx.le).symm
      _ = ((W.law i.succ).rnDeriv (W.law 0) x).toReal := congrArg ENNReal.toReal hx
      _ = observedLawRatio W.law i x := rfl
  · intro G' θ' W' hcompat order i x hx
    rcases hcompat with ⟨hlaw, _hsupport⟩
    rw [← hlaw]

-- @node: smoothObservedRatio
/-- The smooth mechanism formula for an observed ratio, extended through the unmixing map. -/
def smoothObservedRatio
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (i : Fin n) (x : LatentState n) : ℝ :=
  θ.q (W.targetPerm i) (W.unmix x (W.targetPerm i)) /
    θ.p (W.targetPerm i) (W.unmix x)

-- @node: smoothObservedRatio_isVersion
/-- Under the [positive smooth mechanism assumptions](hyp:hpos), [shared mixing
assumptions](hyp:hmix), and [perfect-intervention assumptions](hyp:hone), the smooth mechanism
ratio is a [continuous observed-ratio version](goal) for [world `W`](hyp:W) and
[environment `i`](hyp:i). -/
lemma smoothObservedRatio_isVersion
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W) (i : Fin n) :
    IsContinuousObservedRatioVersion W.law i (smoothObservedRatio W i) := by
  constructor
  · have hratio := (observedWorldLawCoherent_of_assumptions W hpos hmix hone).1 i
    apply Filter.EventuallyEq.trans _ hratio
    filter_upwards [Measure.support_mem_ae (μ := W.law 0)] with x hx
    rw [observedLaw_support_eq_observedSupport W hpos hmix hone] at hx
    rcases hx with ⟨v, hv, rfl⟩
    rw [smoothObservedRatio, show W.unmix (W.mix v) = v from hmix.2.2.1 v hv]
    exact (hone.2.2.2 i v hv).symm
  · rw [observedLaw_support_eq_observedSupport W hpos hmix hone]
    have hunmix_mem : Set.MapsTo W.unmix (observedSupport G W) (latentCube n) := by
      rintro x ⟨v, hv, rfl⟩
      simpa only [hmix.2.2.1 v hv] using hv
    have hunmix_cont : ContinuousOn W.unmix (observedSupport G W) :=
      hmix.2.1.continuousOn
    have hcoord_cont : ContinuousOn
        (fun x ↦ W.unmix x (W.targetPerm i)) (observedSupport G W) :=
      (continuous_apply (W.targetPerm i)).comp_continuousOn hunmix_cont
    have hcoord_mem : Set.MapsTo
        (fun x ↦ W.unmix x (W.targetPerm i)) (observedSupport G W) (Set.Icc 0 1) := by
      intro x hx
      exact hunmix_mem hx (W.targetPerm i) (Set.mem_univ _)
    apply ((hpos.2.2.2.1 (W.targetPerm i)).continuousOn.comp
      hcoord_cont hcoord_mem).div
      ((hpos.2.2.1 (W.targetPerm i)).continuousOn.comp hunmix_cont hunmix_mem)
    intro x hx
    exact ne_of_gt (hpos.1 (W.targetPerm i) _ (hunmix_mem hx))

-- @node: exists_continuousObservedRatioVersion
/-- Under [positive smooth mechanisms](hyp:hpos), [shared diffeomorphic mixing](hyp:hmix), and
[one perfect intervention per node](hyp:hone), [each observed ratio law has a continuous version](goal). -/
lemma exists_continuousObservedRatioVersion
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W) (i : Fin n) :
    ∃ R, IsContinuousObservedRatioVersion W.law i R := by
  exact ⟨smoothObservedRatio W i,
    smoothObservedRatio_isVersion W hpos hmix hone i⟩

/-- The law-selected logarithmic ratio pulled back through the mixing map [agrees pointwise on the
latent cube with the smooth mechanism ratio](goal), under the [positive smooth mechanism
assumptions](hyp:hpos), [shared mixing assumptions](hyp:hmix), and [perfect-intervention
assumptions](hyp:hone), for [world `W`](hyp:W) and [environment `i`](hyp:i). -/
-- @node: observedLawLogRatio_comp_mix_eq
lemma observedLawLogRatio_comp_mix_eq
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W) (i : Fin n) :
    ∀ v, v ∈ latentCube n →
      observedLawLogRatio W.law i (W.mix v) =
        Real.log (θ.q (W.targetPerm i) (v (W.targetPerm i)) /
          θ.p (W.targetPerm i) v) := by
  intro v hv
  have hselected := observedContinuousRatio_isVersion W.law i
    (exists_continuousObservedRatioVersion W hpos hmix hone i)
  have hR := smoothObservedRatio_isVersion W hpos hmix hone i
  have heq := hselected.eqOn hR
  have hmix_support : W.mix v ∈ Measure.support (W.law 0) := by
    rw [observedLaw_support_eq_observedSupport W hpos hmix hone]
    exact ⟨v, hv, rfl⟩
  rw [observedLawLogRatio, heq hmix_support, smoothObservedRatio,
    hmix.2.2.1 v hv]

/-- The observed-law logarithmic ratio pulled back through the mixing map agrees almost
everywhere with the mechanism's scalar log ratio.  Given [the stated inputs and conditions](hyp:hpos,hmix,hone), [the stated conclusion](goal) follows. -/
-- @node: observedLawLogRatio_comp_mix_ae_eq
lemma observedLawLogRatio_comp_mix_ae_eq
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W) (i : Fin n) :
    (fun v => observedLawLogRatio W.law i (W.mix v)) =ᵐ[observationalLaw θ]
      fun v => Real.log
        (θ.q (W.targetPerm i) (v (W.targetPerm i)) / θ.p (W.targetPerm i) v) := by
  filter_upwards [observationalLaw_ae_mem_latentCube hpos] with v hv
  exact observedLawLogRatio_comp_mix_eq W hpos hmix hone i v hv

end CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity
