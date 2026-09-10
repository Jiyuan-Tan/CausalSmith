import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.Kernel
import CausalSmith.Substrate.UnitCubeFactorizationRnTransport.Main

/-!
# Finite-density bridge for observed ratio laws

This file records the model-specific identification needed to instantiate the
general finite-DAG nonancestor marginal theorem with the paper's observed laws.
-/

open MeasureTheory
open scoped ENNReal
open CausalSmith.Substrate.UnitCubeFactorizationRnTransport

noncomputable section

namespace CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

/-- A paper mechanism and observed world are represented by the reusable unit-cube
factorization, including identification of the canonical observed ratio pushforwards. -/
-- @node: FiniteDensityObservedWorldBridge
structure FiniteDensityObservedWorldBridge
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) where
  factorization : Causalean.Graph.FiniteDensity.UnitCubeFactorization (Fin n) G
  intervention : ∀ e : Fin n,
    Causalean.Graph.FiniteDensity.InterventionDensity (W.targetPerm e)
      (fun _ : Fin n => ℝ)
      (fun _ : Fin n => Causalean.Graph.FiniteDensity.unitIntervalReference)
  numerator : Fin n → ℝ → ℝ≥0∞
  ratio_measurable : ∀ i, Measurable (fun v : LatentState n =>
    numerator i (v (W.targetPerm i)) /
      factorization.factor (W.targetPerm i) v)
  observational_identification : ∀ i,
    observationalRatioLaw W i = Measure.map
      (fun v : LatentState n =>
        (numerator i (v (W.targetPerm i)) /
          factorization.factor (W.targetPerm i) v).toReal)
      factorization.observationalMeasure
  interventional_identification : ∀ j i,
    interventionalRatioLaw W j i = Measure.map
      (fun v : LatentState n =>
        (numerator i (v (W.targetPerm i)) /
          factorization.factor (W.targetPerm i) v).toReal)
      (factorization.interventionMeasure (W.targetPerm j) (intervention j))

/-! ## Construction from the paper's primitive assumptions -/

/-- A [positive normalized smooth latent mechanism](hyp:hpos) determines [the reusable
unit-cube factorization of its observational conditional densities](goal). -/
def mechanismUnitCubeFactorization
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (hpos : PositiveNormalizedSmoothMechanisms G θ) :
    Causalean.Graph.FiniteDensity.UnitCubeFactorization (Fin n) G := by
  apply unitCubeFactorizationOfRealCubeFactors θ.p
  · apply measurableOnSet_of_continuousOn_cube
    intro i
    exact (hpos.2.2.1 i).continuousOn
  · intro i v hv
    exact (hpos.1 i v hv).le
  · intro i v w hv hw hvw
    apply θ.parent_local i v w
    · exact hvw i (Finset.mem_insert_self i (G.parents i))
    · intro k hk
      exact hvw k (Finset.mem_insert_of_mem hk)
  · exact hpos.2.2.2.2.1

/-- A [positive normalized smooth latent mechanism](hyp:hpos) and [observed target
permutation](hyp:W) determine [the reusable unit-cube intervention density for an
environment](goal). -/
def mechanismInterventionDensity
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (hpos : PositiveNormalizedSmoothMechanisms G θ) (e : Fin n) :
    Causalean.Graph.FiniteDensity.InterventionDensity (W.targetPerm e)
      (fun _ : Fin n => ℝ)
      (fun _ : Fin n => Causalean.Graph.FiniteDensity.unitIntervalReference) := by
  apply interventionDensityOfRealCube (W.targetPerm e) (θ.q (W.targetPerm e))
  · exact (hpos.2.2.2.1 (W.targetPerm e)).continuousOn.domRestrict.measurable
  · intro x hx
    exact (hpos.2.1 (W.targetPerm e) x hx).le
  · exact hpos.2.2.2.2.2 (W.targetPerm e)

/-- A [positive normalized smooth mechanism](hyp:hpos) has [the same observational law as
the observational measure of its clamped unit-cube factorization](goal). -/
theorem mechanismUnitCubeFactorization_observationalMeasure
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (hpos : PositiveNormalizedSmoothMechanisms G θ) :
    (mechanismUnitCubeFactorization hpos).observationalMeasure = observationalLaw θ := by
  -- Unfold the paper law after applying the substrate's real cube-product identification.
  change (mechanismUnitCubeFactorization hpos).observationalMeasure =
    realCubeProductDensityMeasure θ.p
  simpa only [mechanismUnitCubeFactorization, latentCube] using
    observationalMeasure_unitCubeFactorizationOfRealCubeFactors θ.p
      (measurableOnSet_of_continuousOn_cube θ.p
        (fun i => (hpos.2.2.1 i).continuousOn))
      (fun i v hv => (hpos.1 i v hv).le)
      (fun i v w _ _ hvw => θ.parent_local i v w
        (hvw i (Finset.mem_insert_self _ _))
        (fun k hk => hvw k (Finset.mem_insert_of_mem hk)))
      hpos.2.2.2.2.1

/-- A [positive normalized smooth mechanism](hyp:hpos) has [the same target-intervention law
as the intervention measure of its clamped unit-cube factorization](goal). -/
theorem mechanismUnitCubeFactorization_interventionMeasure
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (hpos : PositiveNormalizedSmoothMechanisms G θ) (e : Fin n) :
    (mechanismUnitCubeFactorization hpos).interventionMeasure (W.targetPerm e)
        (mechanismInterventionDensity W hpos e) =
      interventionalLaw θ (W.targetPerm e) := by
  -- Unfold the paper law after applying the substrate's real cube-intervention identification.
  change (mechanismUnitCubeFactorization hpos).interventionMeasure (W.targetPerm e)
      (mechanismInterventionDensity W hpos e) =
    realCubeInterventionDensityMeasure θ.p (W.targetPerm e) (θ.q (W.targetPerm e))
  simpa only [mechanismUnitCubeFactorization, mechanismInterventionDensity, latentCube] using
    interventionMeasure_unitCubeFactorizationOfRealCubeFactors θ.p
      (measurableOnSet_of_continuousOn_cube θ.p
        (fun i => (hpos.2.2.1 i).continuousOn))
      (fun i v hv => (hpos.1 i v hv).le)
      (fun i v w _ _ hvw => θ.parent_local i v w
        (hvw i (Finset.mem_insert_self _ _))
        (fun k hk => hvw k (Finset.mem_insert_of_mem hk)))
      hpos.2.2.2.2.1 (W.targetPerm e) (θ.q (W.targetPerm e))
      ((hpos.2.2.2.1 (W.targetPerm e)).continuousOn.domRestrict.measurable)
      (fun x hx => (hpos.2.1 (W.targetPerm e) x hx).le)
      (hpos.2.2.2.2.2 (W.targetPerm e))

/-- The [positive normalized smooth mechanism](hyp:hpos) and [environment target](hyp:W)
determine [the globally measurable clamped numerator used in the canonical target ratio](goal). -/
def mechanismRatioNumerator
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (e : Fin n) : ℝ → ℝ≥0∞ :=
  (mechanismInterventionDensity W hpos e).density

/-- On [the latent unit cube](hyp:hv), the [real value of the clamped factor ratio](goal) is
the paper's ordinary replacement-to-observational density ratio. -/
theorem mechanismTargetRatio_toReal_eq
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (e : Fin n) {v : LatentState n} (hv : v ∈ latentCube n) :
    (mechanismRatioNumerator W hpos e (v (W.targetPerm e)) /
      (mechanismUnitCubeFactorization hpos).factor (W.targetPerm e) v).toReal =
        θ.q (W.targetPerm e) (v (W.targetPerm e)) / θ.p (W.targetPerm e) v := by
  -- Both clamped extensions are unchanged on the cube; positivity removes `ofReal` truncation.
  have hj := hv (W.targetPerm e) (Set.mem_univ _)
  have hnum : mechanismRatioNumerator W hpos e (v (W.targetPerm e)) =
      ENNReal.ofReal (θ.q (W.targetPerm e) (v (W.targetPerm e))) := by
    simp [mechanismRatioNumerator, mechanismInterventionDensity,
      interventionDensityOfRealCube, interventionDensityOfCube,
      min_eq_right hj.2, max_eq_right hj.1]
  have hden : (mechanismUnitCubeFactorization hpos).factor (W.targetPerm e) v =
      ENNReal.ofReal (θ.p (W.targetPerm e) v) := by
    simpa only [mechanismUnitCubeFactorization, latentCube] using
      unitCubeFactorizationOfRealCubeFactors_factor_eq θ.p
        (measurableOnSet_of_continuousOn_cube θ.p
          (fun i => (hpos.2.2.1 i).continuousOn))
        (fun i w hw => (hpos.1 i w hw).le)
        (fun i x y _ _ hxy => θ.parent_local i x y
          (hxy i (Finset.mem_insert_self _ _))
          (fun k hk => hxy k (Finset.mem_insert_of_mem hk)))
        hpos.2.2.2.2.1 (W.targetPerm e) hv
  rw [hnum, hden, ENNReal.toReal_div,
    ENNReal.toReal_ofReal (hpos.2.1 _ _ hj).le,
    ENNReal.toReal_ofReal (hpos.1 _ _ hv).le]

/-- The [clamped target ratio](hyp:W,hpos) is [globally measurable](goal). -/
theorem measurable_mechanismTargetRatio
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (hpos : PositiveNormalizedSmoothMechanisms G θ) (e : Fin n) :
    Measurable (fun v : LatentState n =>
      mechanismRatioNumerator W hpos e (v (W.targetPerm e)) /
        (mechanismUnitCubeFactorization hpos).factor (W.targetPerm e) v) := by
  exact ((mechanismInterventionDensity W hpos e).measurable_density.comp
      (measurable_pi_apply (W.targetPerm e))).div
    ((mechanismUnitCubeFactorization hpos).measurable_factor (W.targetPerm e))

/-- Under [positive latent densities](hyp:hpos), [support-local shared mixing](hyp:hmix), and
[the supplied pushforward laws](hyp:hone), every observed single-target intervention law is
absolutely continuous with respect to the observed observational law](goal). -/
theorem observedInterventional_absolutelyContinuous_observational
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W) (e : Fin n) :
    W.law e.succ ≪ W.law 0 := by
  -- First compare both cube-restricted densities to the common restricted-volume reference,
  -- then transport absolute continuity through the map using its a.e. measurability on the cube.
  let B := mechanismUnitCubeFactorization hpos
  let q := mechanismInterventionDensity W hpos e
  let μ := Causalean.Graph.FiniteDensity.unitCubeReference (Fin n)
  have hfactor_pos : ∀ i v, 0 < B.factor i v := by
    intro i v
    change 0 < ENNReal.ofReal (θ.p i (clampCube (Fin n) v))
    rw [ENNReal.ofReal_pos]
    exact hpos.1 i _ (by
      simpa only [latentCube, Causalean.Graph.FiniteDensity.unitCube] using
        clampCube_mem (Fin n) v)
  have hmeas_obs : Measurable B.observationalDensity := by
    unfold Causalean.Graph.FiniteDensity.Factorization.observationalDensity
      Causalean.Graph.FiniteDensity.Factorization.partialDensity
    exact Finset.measurable_prod Finset.univ (fun i _ => B.measurable_factor i)
  have hμ_obs : μ ≪ B.observationalMeasure := by
    rw [Causalean.Graph.FiniteDensity.Factorization.observationalMeasure]
    apply withDensity_absolutelyContinuous' hmeas_obs.aemeasurable
    filter_upwards with v
    change (∏ i ∈ Finset.univ, B.factor i v) ≠ 0
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => (hfactor_pos i v).ne')
  have hint_μ : B.interventionMeasure (W.targetPerm e) q ≪ μ := by
    rw [Causalean.Graph.FiniteDensity.Factorization.interventionMeasure]
    exact withDensity_absolutelyContinuous _ _
  have hlatentB : B.interventionMeasure (W.targetPerm e) q ≪ B.observationalMeasure :=
    hint_μ.trans hμ_obs
  have hlatent : interventionalLaw θ (W.targetPerm e) ≪ observationalLaw θ := by
    simpa only [B, q, mechanismUnitCubeFactorization_interventionMeasure W hpos e,
      mechanismUnitCubeFactorization_observationalMeasure hpos] using hlatentB
  have hcube : MeasurableSet (latentCube n) := by
    rw [latentCube]
    exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Icc)
  have hμ_cube : μ (latentCube n)ᶜ = 0 := by
    simpa only [μ, latentCube, Causalean.Graph.FiniteDensity.unitCube] using
      Causalean.Graph.FiniteDensity.unitCubeReference_compl (Fin n)
  have hobs_μ : observationalLaw θ ≪ μ := by
    rw [← mechanismUnitCubeFactorization_observationalMeasure hpos]
    exact withDensity_absolutelyContinuous _ _
  have hobs_cube : observationalLaw θ (latentCube n)ᶜ = 0 := hobs_μ hμ_cube
  have hmixOn : SupportMeasurableOn W.mix (latentCube n) :=
    hmix.1.continuousOn.domRestrict.measurable
  have hmixAE : AEMeasurable W.mix (observationalLaw θ) :=
    aemeasurable_of_supportMeasurableOn hcube hobs_cube hmixOn
  let mix' := hmixAE.mk W.mix
  have hmix_eq_obs : W.mix =ᵐ[observationalLaw θ] mix' := hmixAE.ae_eq_mk
  have hmix_eq_int : W.mix =ᵐ[interventionalLaw θ (W.targetPerm e)] mix' :=
    hlatent.ae_eq hmix_eq_obs
  have hmap : Measure.map mix' (interventionalLaw θ (W.targetPerm e)) ≪
      Measure.map mix' (observationalLaw θ) :=
    @Measure.AbsolutelyContinuous.map _ _ _ _ _ _ hlatent mix' hmixAE.measurable_mk
  rw [hone.2.1 e, hone.1]
  calc
    Measure.map W.mix (interventionalLaw θ (W.targetPerm e)) =
        Measure.map mix' (interventionalLaw θ (W.targetPerm e)) :=
      Measure.map_congr hmix_eq_int
    _ ≪ Measure.map mix' (observationalLaw θ) := hmap
    _ = Measure.map W.mix (observationalLaw θ) := (Measure.map_congr hmix_eq_obs).symm

/-- The [primitive smooth-mechanism, support-local mixing, and observed-law hypotheses]
(hyp:hpos,hmix,hone) [construct the paper's finite-density observed-world bridge](goal). -/
def finiteDensityObservedWorldBridge_of_assumptions
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W) :
    FiniteDensityObservedWorldBridge W where
  factorization := mechanismUnitCubeFactorization hpos
  intervention := mechanismInterventionDensity W hpos
  numerator := mechanismRatioNumerator W hpos
  ratio_measurable := measurable_mechanismTargetRatio W hpos
  observational_identification := by
    intro i
    -- Pull the canonical observed RN ratio back along `W.mix`, use `hone`'s a.e. canonical-ratio
    -- clause and its cube formula, then rewrite the latent law with the factorization identity.
    let μ := Causalean.Graph.FiniteDensity.unitCubeReference (Fin n)
    have hcube : MeasurableSet (latentCube n) := by
      rw [latentCube]
      exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Icc)
    have hμ_cube : μ (latentCube n)ᶜ = 0 := by
      simpa only [μ, latentCube, Causalean.Graph.FiniteDensity.unitCube] using
        Causalean.Graph.FiniteDensity.unitCubeReference_compl (Fin n)
    have hobs_μ : observationalLaw θ ≪ μ := by
      rw [← mechanismUnitCubeFactorization_observationalMeasure hpos]
      exact withDensity_absolutelyContinuous _ _
    have hobs_cube : observationalLaw θ (latentCube n)ᶜ = 0 := hobs_μ hμ_cube
    have hmixOn : SupportMeasurableOn W.mix (latentCube n) :=
      hmix.1.continuousOn.domRestrict.measurable
    have hmixAE : AEMeasurable W.mix (observationalLaw θ) :=
      aemeasurable_of_supportMeasurableOn hcube hobs_cube hmixOn
    let mix' := hmixAE.mk W.mix
    have hmix_eq : W.mix =ᵐ[observationalLaw θ] mix' := hmixAE.ae_eq_mk
    have htend : Filter.Tendsto W.mix (ae (observationalLaw θ)) (ae (W.law 0)) := by
      have hrep :=
        (hmixAE.measurable_mk.quasiMeasurePreserving (observationalLaw θ)).tendsto_ae
      rw [← Measure.map_congr hmix_eq, ← hone.1] at hrep
      exact Filter.Tendsto.congr' hmix_eq.symm hrep
    have hpull := (hone.2.2.1 i).comp_tendsto htend
    let r := fun v : LatentState n =>
      mechanismRatioNumerator W hpos i (v (W.targetPerm i)) /
        (mechanismUnitCubeFactorization hpos).factor (W.targetPerm i) v
    have hr : (observedLawRatio W.law i ∘ W.mix) =ᵐ[observationalLaw θ]
        (ENNReal.toReal ∘ r) := by
      filter_upwards [hpull, ae_iff.mpr hobs_cube] with v hvcanon hv
      have hratio_pos : 0 < W.ratio i (W.mix v) := by
        rw [hone.2.2.2 i v hv]
        exact div_pos (hpos.2.1 _ _ (hv (W.targetPerm i) (Set.mem_univ _)))
          (hpos.1 _ _ hv)
      change ((W.law i.succ).rnDeriv (W.law 0) (W.mix v)).toReal = (r v).toReal
      calc
        _ = (ENNReal.ofReal (W.ratio i (W.mix v))).toReal :=
          (congrArg ENNReal.toReal hvcanon).symm
        _ = W.ratio i (W.mix v) := ENNReal.toReal_ofReal hratio_pos.le
        _ = θ.q (W.targetPerm i) (v (W.targetPerm i)) /
            θ.p (W.targetPerm i) v := hone.2.2.2 i v hv
        _ = (r v).toReal := (mechanismTargetRatio_toReal_eq W hpos i hv).symm
    unfold observationalRatioLaw
    rw [hone.1]
    calc
      Measure.map (observedLawRatio W.law i)
          (Measure.map W.mix (observationalLaw θ)) =
          Measure.map (observedLawRatio W.law i ∘ W.mix) (observationalLaw θ) :=
        AEMeasurable.map_map_of_aemeasurable
          (measurable_observedLawRatio W.law i).aemeasurable hmixAE
      _ = Measure.map (ENNReal.toReal ∘ r) (observationalLaw θ) := Measure.map_congr hr
      _ = Measure.map (ENNReal.toReal ∘ r)
          (mechanismUnitCubeFactorization hpos).observationalMeasure := by
        rw [mechanismUnitCubeFactorization_observationalMeasure hpos]
      _ = _ := by rfl
  interventional_identification := by
    intro j i
    -- The same pullback equality holds under environment `j` by the preceding absolute
    -- continuity lemma; rewrite both the environment and factorized intervention measures.
    let B := mechanismUnitCubeFactorization hpos
    let qj := mechanismInterventionDensity W hpos j
    let μ := Causalean.Graph.FiniteDensity.unitCubeReference (Fin n)
    let ν := interventionalLaw θ (W.targetPerm j)
    have hcube : MeasurableSet (latentCube n) := by
      rw [latentCube]
      exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Icc)
    have hμ_cube : μ (latentCube n)ᶜ = 0 := by
      simpa only [μ, latentCube, Causalean.Graph.FiniteDensity.unitCube] using
        Causalean.Graph.FiniteDensity.unitCubeReference_compl (Fin n)
    have hν_μ : ν ≪ μ := by
      change interventionalLaw θ (W.targetPerm j) ≪
        Causalean.Graph.FiniteDensity.unitCubeReference (Fin n)
      rw [← mechanismUnitCubeFactorization_interventionMeasure W hpos j]
      rw [Causalean.Graph.FiniteDensity.Factorization.interventionMeasure]
      exact withDensity_absolutelyContinuous _ _
    have hν_cube : ν (latentCube n)ᶜ = 0 := hν_μ hμ_cube
    have hmixOn : SupportMeasurableOn W.mix (latentCube n) :=
      hmix.1.continuousOn.domRestrict.measurable
    have hmixAE : AEMeasurable W.mix ν :=
      aemeasurable_of_supportMeasurableOn hcube hν_cube hmixOn
    let mix' := hmixAE.mk W.mix
    have hmix_eq : W.mix =ᵐ[ν] mix' := hmixAE.ae_eq_mk
    have htend : Filter.Tendsto W.mix (ae ν) (ae (W.law j.succ)) := by
      have hrep := (hmixAE.measurable_mk.quasiMeasurePreserving ν).tendsto_ae
      rw [← Measure.map_congr hmix_eq, ← hone.2.1 j] at hrep
      exact Filter.Tendsto.congr' hmix_eq.symm hrep
    have hcanon_j := (observedInterventional_absolutelyContinuous_observational
      W hpos hmix hone j).ae_eq (hone.2.2.1 i)
    have hpull := hcanon_j.comp_tendsto htend
    let r := fun v : LatentState n =>
      mechanismRatioNumerator W hpos i (v (W.targetPerm i)) /
        (mechanismUnitCubeFactorization hpos).factor (W.targetPerm i) v
    have hr : (observedLawRatio W.law i ∘ W.mix) =ᵐ[ν] (ENNReal.toReal ∘ r) := by
      filter_upwards [hpull, ae_iff.mpr hν_cube] with v hvcanon hv
      have hratio_pos : 0 < W.ratio i (W.mix v) := by
        rw [hone.2.2.2 i v hv]
        exact div_pos (hpos.2.1 _ _ (hv (W.targetPerm i) (Set.mem_univ _)))
          (hpos.1 _ _ hv)
      change ((W.law i.succ).rnDeriv (W.law 0) (W.mix v)).toReal = (r v).toReal
      calc
        _ = (ENNReal.ofReal (W.ratio i (W.mix v))).toReal :=
          (congrArg ENNReal.toReal hvcanon).symm
        _ = W.ratio i (W.mix v) := ENNReal.toReal_ofReal hratio_pos.le
        _ = θ.q (W.targetPerm i) (v (W.targetPerm i)) /
            θ.p (W.targetPerm i) v := hone.2.2.2 i v hv
        _ = (r v).toReal := (mechanismTargetRatio_toReal_eq W hpos i hv).symm
    unfold interventionalRatioLaw
    rw [hone.2.1 j]
    calc
      Measure.map (observedLawRatio W.law i) (Measure.map W.mix ν) =
          Measure.map (observedLawRatio W.law i ∘ W.mix) ν :=
        AEMeasurable.map_map_of_aemeasurable
          (measurable_observedLawRatio W.law i).aemeasurable hmixAE
      _ = Measure.map (ENNReal.toReal ∘ r) ν := Measure.map_congr hr
      _ = Measure.map (ENNReal.toReal ∘ r)
          (B.interventionMeasure (W.targetPerm j) qj) := by
        change Measure.map (ENNReal.toReal ∘ r)
            (interventionalLaw θ (W.targetPerm j)) =
          Measure.map (ENNReal.toReal ∘ r)
            ((mechanismUnitCubeFactorization hpos).interventionMeasure (W.targetPerm j)
              (mechanismInterventionDensity W hpos j))
        rw [mechanismUnitCubeFactorization_interventionMeasure W hpos j]
      _ = _ := by rfl

/-- The finite-density bridge turns nonancestry into equality of the two canonical
real-valued ratio laws. -/
-- @node: FiniteDensityObservedWorldBridge.ratioLaw_eq_of_nonancestor
lemma FiniteDensityObservedWorldBridge.ratioLaw_eq_of_nonancestor
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    {W : ObservedWorld G θ} (B : FiniteDensityObservedWorldBridge W)
    {j i : Fin n} (hji : j ≠ i)
    (hna : ¬ G.isAncestor (W.targetPerm j) (W.targetPerm i)) :
    observationalRatioLaw W i = interventionalRatioLaw W j i := by
  rw [B.observational_identification i, B.interventional_identification j i]
  have hσ : ∀ _ : Fin n,
      SigmaFinite Causalean.Graph.FiniteDensity.unitIntervalReference := fun _ => by
    unfold Causalean.Graph.FiniteDensity.unitIntervalReference
    infer_instance
  have htarget : W.targetPerm j ≠ W.targetPerm i := by
    exact fun h => hji (W.targetPerm.injective h)
  have h := @Causalean.Graph.FiniteDensity.Factorization.targetRatio_map_eq
    (Fin n) _ _ (fun _ : Fin n => ℝ) _
    (fun _ : Fin n => Causalean.Graph.FiniteDensity.unitIntervalReference)
    hσ G B.factorization (W.targetPerm i) (W.targetPerm j) htarget hna
    (B.intervention j) (B.numerator i) (B.ratio_measurable i) (fun _ => 0)
  let r := fun v : LatentState n =>
    B.numerator i (v (W.targetPerm i)) / B.factorization.factor (W.targetPerm i) v
  change Measure.map (ENNReal.toReal ∘ r) B.factorization.observationalMeasure =
    Measure.map (ENNReal.toReal ∘ r)
      (B.factorization.interventionMeasure (W.targetPerm j) (B.intervention j))
  calc
    _ = Measure.map ENNReal.toReal
        (Measure.map r B.factorization.observationalMeasure) := by
      simpa [r] using (Measure.map_map ENNReal.measurable_toReal
        (B.ratio_measurable i)).symm
    _ = Measure.map ENNReal.toReal
        (Measure.map r (B.factorization.interventionMeasure
          (W.targetPerm j) (B.intervention j))) := congrArg (Measure.map ENNReal.toReal) h
    _ = _ := by
      simpa [r] using Measure.map_map ENNReal.measurable_toReal
        (B.ratio_measurable i)

end CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity
