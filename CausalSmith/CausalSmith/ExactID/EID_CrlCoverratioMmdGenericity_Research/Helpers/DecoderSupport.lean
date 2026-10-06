module
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.DecoderCore
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.DecoderTriangularInverse

/-!
# Realized predecessor-score support

This file proves that every predecessor-score vector produced by a latent cube
point lies in the support of its observed interventional predecessor law.  It
is the support bridge needed to turn continuous-version uniqueness into the
pointwise equation-(11) identity.
-/

public section

open Causalean.Graph


open MeasureTheory Set Filter
open scoped Topology

noncomputable section

namespace CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

-- @node: observedInterventionalLaw_support_eq_observedSupport
/-- Every supplied observed single-target intervention law has the full observed model
support, because its latent density is strictly positive on the full cube.  Given [the stated inputs and conditions](hyp:hpos,hmix,hone), [the stated conclusion](goal) follows. -/
lemma observedInterventionalLaw_support_eq_observedSupport
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W) (e : Fin n) :
    Measure.support (W.law e.succ) = observedSupport G W := by
  let μ := interventionalLaw θ (W.targetPerm e)
  have hcube_compact : IsCompact (latentCube n) := by
    rw [latentCube]
    exact isCompact_univ_pi fun _ => isCompact_Icc
  have hsupport_closed : IsClosed (observedSupport G W) :=
    (hcube_compact.image_of_continuousOn hmix.1.continuousOn).isClosed
  have hμ_cube : ∀ᵐ v ∂μ, v ∈ latentCube n := by
    filter_upwards [Measure.support_mem_ae (μ := μ)] with v hv
    simpa [μ, interventionalLaw_support_eq_latentCube W hpos e] using hv
  have hcube_meas : MeasurableSet (latentCube n) := by
    rw [latentCube]
    exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Icc)
  have hmixAE : AEMeasurable W.mix μ :=
    Causalean.Mathlib.MeasureTheory.aemeasurable_of_supportMeasurableOn hcube_meas
      (ae_iff.mp hμ_cube) hmix.1.continuousOn.domRestrict.measurable
  have hfull : W.law e.succ (observedSupport G W)ᶜ = 0 := by
    rw [hone.2.1 e,
      Measure.map_apply_of_aemeasurable hmixAE hsupport_closed.isOpen_compl.measurableSet]
    apply measure_mono_null (t := (latentCube n)ᶜ)
    · intro v hv hvcube
      exact hv ⟨v, hvcube, rfl⟩
    · exact ae_iff.mp hμ_cube
  apply Set.Subset.antisymm
  · exact Measure.support_subset_of_isClosed hsupport_closed (ae_iff.mpr hfull)
  · rintro x ⟨v, hv, rfl⟩
    rw [Measure.mem_support_iff_forall]
    intro U hU
    rcases mem_nhds_iff.mp hU with ⟨O, hOU, hOopen, hmixO⟩
    rw [hone.2.1 e]
    apply lt_of_lt_of_le _ (measure_mono hOU)
    rw [Measure.map_apply_of_aemeasurable hmixAE hOopen.measurableSet]
    have hpre : W.mix ⁻¹' O ∈ nhdsWithin v (latentCube n) :=
      (hmix.1.continuousOn v hv) (hOopen.mem_nhds hmixO)
    rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hpre with ⟨V, hV, hVsub⟩
    have hVpos : 0 < μ V :=
      (Measure.mem_support_iff_forall v).mp
        ((interventionalLaw_support_eq_latentCube W hpos e).symm.subset hv) V hV
    rw [← Measure.measure_inter_eq_of_ae hμ_cube] at hVpos
    exact hVpos.trans_le (measure_mono (by simpa [inter_comm] using hVsub))

-- @node: continuousOn_observedLawLogRatio_observedSupport
/-- The law-selected log ratio is continuous on the common observed support.  Given [the stated inputs and conditions](hyp:hpos,hmix,hone), [the stated conclusion](goal) follows. -/
lemma continuousOn_observedLawLogRatio_observedSupport
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W) (i : Fin n) :
    ContinuousOn (observedLawLogRatio W.law i) (observedSupport G W) := by
  have hex := exists_continuousObservedRatioVersion W hpos hmix hone i
  have hselected := observedContinuousRatio_isVersion W.law i hex
  have hsmooth := smoothObservedRatio_isVersion W hpos hmix hone i
  have heq := hselected.eqOn hsmooth
  rw [← observedLaw_support_eq_observedSupport W hpos hmix hone]
  apply ContinuousOn.log hselected.2
  intro x hx
  rw [heq hx]
  rw [observedLaw_support_eq_observedSupport W hpos hmix hone] at hx
  rcases hx with ⟨v, hv, rfl⟩
  rw [smoothObservedRatio, hmix.2.2.1 v hv]
  exact div_ne_zero (ne_of_gt (hpos.2.1 _ _ (hv _ (Set.mem_univ _))))
    (ne_of_gt (hpos.1 _ _ hv))

-- @node: continuousOn_predecessorLogRatioProjection_observedSupport
/-- The vector of predecessor log ratios is continuous on the common observed support.  Given [the stated inputs and conditions](hyp:hpos,hmix,hone), [the stated conclusion](goal) follows. -/
lemma continuousOn_predecessorLogRatioProjection_observedSupport
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W)
    (order : Fin n → ℕ) (i : Fin n) :
    ContinuousOn
      (familyProjection (observedLawLogRatio W.law) (predecessorSet order i))
      (observedSupport G W) := by
  rw [continuousOn_pi]
  intro j
  exact continuousOn_observedLawLogRatio_observedSupport W hpos hmix hone j

-- @node: continuousOn_map_mem_support
/-- A function continuous on the support of a measure sends support points into the support
of its pushforward.  Given [the stated inputs and conditions](hyp:hf,hcont,hx), [the stated conclusion](goal) follows. -/
lemma continuousOn_map_mem_support
    {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [HereditarilyLindelofSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {μ : Measure X} {f : X → Y} (hf : AEMeasurable f μ)
    (hcont : ContinuousOn f (Measure.support μ)) {x : X}
    (hx : x ∈ Measure.support μ) : f x ∈ Measure.support (Measure.map f μ) := by
  rw [Measure.mem_support_iff_forall]
  intro U hU
  rcases mem_nhds_iff.mp hU with ⟨O, hOU, hOopen, hfxO⟩
  apply lt_of_lt_of_le _ (measure_mono hOU)
  rw [Measure.map_apply_of_aemeasurable hf hOopen.measurableSet]
  have hpre : f ⁻¹' O ∈ nhdsWithin x (Measure.support μ) :=
    (hcont x hx) (hOopen.mem_nhds hfxO)
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hpre with ⟨V, hV, hVsub⟩
  have hVpos : 0 < μ V := (Measure.mem_support_iff_forall x).mp hx V hV
  rw [← Measure.measure_inter_eq_of_ae (Measure.support_mem_ae (μ := μ))] at hVpos
  exact hVpos.trans_le (measure_mono (fun y hy => hVsub ⟨hy.2, hy.1⟩))

-- @node: observedPredecessorLogRatio_mem_support
/-- Every predecessor-score vector realized by a latent cube point belongs to the support of
the observed predecessor law under the current intervention.  Given [the stated inputs and conditions](hyp:hpos,hmix,hone,hv), [the stated conclusion](goal) follows. -/
lemma observedPredecessorLogRatio_mem_support
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W)
    {order : Fin n → ℕ} (i : Fin n) (v : LatentState n)
    (hv : v ∈ latentCube n) :
    familyProjection (observedLawLogRatio W.law) (predecessorSet order i) (W.mix v) ∈
      Measure.support (Measure.map
        (familyProjection (observedLawLogRatio W.law) (predecessorSet order i))
        (W.law i.succ)) := by
  let pred := familyProjection (observedLawLogRatio W.law) (predecessorSet order i)
  have hpred : Measurable pred := by
    dsimp only [pred, familyProjection]
    apply measurable_pi_lambda
    intro j
    exact measurable_observedLawLogRatio W.law j
  have hx : W.mix v ∈ Measure.support (W.law i.succ) := by
    rw [observedInterventionalLaw_support_eq_observedSupport W hpos hmix hone i]
    exact ⟨v, hv, rfl⟩
  apply continuousOn_map_mem_support (μ := W.law i.succ) (f := pred)
    hpred.aemeasurable
    (show ContinuousOn pred (Measure.support (W.law i.succ)) by
      rw [observedInterventionalLaw_support_eq_observedSupport W hpos hmix hone i]
      exact continuousOn_predecessorLogRatioProjection_observedSupport
        W hpos hmix hone order i)
    hx

end CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity
