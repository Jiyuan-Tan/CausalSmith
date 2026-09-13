import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.AnalyticEdgePerturbation
import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.GaussianRecoveryBridge
import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.UniformSetIntegralContinuity
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.GDelta.Basic
import Mathlib.Order.Cover
import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# Generic cover separation

This file states the open-dense direct-edge result and its residual
Gaussian-MMD ancestral-cover consequence, including the empty-graph case.
-/

open Set MeasureTheory
open scoped Topology

noncomputable section

namespace CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

/-- Relabelling the canonical intervention environments does not change the latent direct-edge
contrast after transporting the two environment indices back through the permutation.  [the stated conclusion](goal) follows. -/
lemma canonical_secondMomentContrast_perm_eq
    {n : ℕ} {G : Causalean.DAG (Fin n)} (theta : Mechanism n G)
    (pi : Equiv.Perm (Fin n)) (j i : Fin n) :
    secondMomentContrast (canonicalObservedWorld G theta pi) (pi.symm j) (pi.symm i) =
      secondMomentContrast (canonicalObservedWorld G theta (Equiv.refl (Fin n))) j i := by
  unfold secondMomentContrast canonicalObservedWorld
  simp

/-- For each fixed direct edge, the corresponding canonical contrast-nonzero locus is dense in
the mechanism stratum, independently of the target permutation.  Given [the stated inputs and conditions](hyp:hji), [the stated conclusion](goal) follows. -/
lemma edgeContrastNonzeroSet_dense
    {n : ℕ} (G : Causalean.DAG (Fin n)) (s : SignVector n)
    (pi : Equiv.Perm (Fin n)) {j i : Fin n} (hji : G.edge j i) :
    Dense {theta : StratumPoint G s |
      secondMomentContrast (canonicalObservedWorld G theta.1 pi)
        (pi.symm j) (pi.symm i) ≠ 0} := by
  rw [dense_iff_inter_open]
  intro U hU hUne
  rcases hUne with ⟨theta, hthetaU⟩
  rcases isOpen_induced_iff.mp hU with ⟨V, hV, hVU⟩
  have hthetaV : theta.1 ∈ V := by
    have : theta ∈ Subtype.val ⁻¹' V := by simpa [hVU] using hthetaU
    exact this
  have hIntervention : OnePerfectInterventionPerNode G theta.1
      (canonicalObservedWorld G theta.1 (Equiv.refl (Fin n))) :=
    canonicalObservedWorld_onePerfectInterventionPerNode
      theta.property.positiveSmooth (Equiv.refl (Fin n))
  rcases (analytic_edge_perturbation theta hji hIntervention).2.2 V
      (hV.mem_nhds hthetaV) with ⟨t, htV, htStratum, htne⟩
  let eta : StratumPoint G s :=
    ⟨affinePath s theta hji ⟨t.1, ⟨le_of_lt t.2.1, le_of_lt t.2.2⟩⟩, htStratum⟩
  refine ⟨eta, ?_, ?_⟩
  · have : eta ∈ Subtype.val ⁻¹' V := htV
    simpa [hVU] using this
  · change secondMomentContrast (canonicalObservedWorld G eta.1 pi)
      (pi.symm j) (pi.symm i) ≠ 0
    rw [canonical_secondMomentContrast_perm_eq]
    exact htne

/-- The observational value coordinate is continuous on the mechanism stratum by construction of
the induced product C² topology.  [the stated conclusion](goal) follows. -/
lemma continuous_stratum_p_valueCoordinate
    {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n} (i : Fin n) :
    Continuous (fun theta : StratumPoint G s ↦
      UniformOnFun.ofFun {latentCube n} (theta.1.p i)) := by
  have hcoordinates : Continuous
      (fun theta : StratumPoint G s ↦ mechanismC2Coordinates theta.1) :=
    (continuous_induced_dom (f := @mechanismC2Coordinates n G)).comp continuous_subtype_val
  unfold mechanismC2Coordinates at hcoordinates
  exact (continuous_apply i).comp (continuous_fst.comp hcoordinates)

/-- The intervention value coordinate is continuous on the mechanism stratum by construction of
the induced product C² topology.  [the stated conclusion](goal) follows. -/
lemma continuous_stratum_q_valueCoordinate
    {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n} (i : Fin n) :
    Continuous (fun theta : StratumPoint G s ↦
      UniformOnFun.ofFun {Set.Icc (0 : ℝ) 1} (theta.1.q i)) := by
  have hcoordinates : Continuous
      (fun theta : StratumPoint G s ↦ mechanismC2Coordinates theta.1) :=
    (continuous_induced_dom (f := @mechanismC2Coordinates n G)).comp continuous_subtype_val
  unfold mechanismC2Coordinates at hcoordinates
  exact (continuous_apply i).comp
    (continuous_fst.comp (continuous_snd.comp
      (continuous_snd.comp (continuous_snd.comp hcoordinates))))

/-- Uniform convergence of a continuous family, combined with continuous motion of the argument,
gives joint continuity of evaluation.  Given [the stated inputs and conditions](hyp:hF,hc), [the stated conclusion](goal) follows. -/
lemma continuous_uniformFun_eval₂_of_continuous
    {X alpha beta : Type*} [TopologicalSpace X] [TopologicalSpace alpha]
    [UniformSpace beta] (F : X → UniformFun alpha beta) (hF : Continuous F)
    (hc : ∀ x, Continuous (UniformFun.toFun (F x))) :
    Continuous (fun z : X × alpha ↦ UniformFun.toFun (F z.1) z.2) := by
  rw [continuous_iff_continuousAt]
  intro z
  have hFt : Filter.Tendsto (F ∘ Prod.fst) (nhds z) (nhds (F z.1)) :=
    hF.continuousAt.comp continuousAt_fst
  have hu := UniformFun.tendsto_iff_tendstoUniformly.mp hFt
  exact hu.tendsto_comp (hc z.1).continuousAt continuousAt_snd

/-- Observational-factor evaluation is jointly continuous in a stratum mechanism and a compact
latent state.  [the stated conclusion](goal) follows. -/
lemma continuous_stratum_p_eval
    {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n} (i : Fin n) :
    Continuous (fun z : StratumPoint G s × {v : LatentState n // v ∈ latentCube n} ↦
      z.1.1.p i z.2.1) := by
  let F : StratumPoint G s →
      UniformFun {v : LatentState n // v ∈ latentCube n} ℝ := fun theta ↦
    UniformFun.ofFun ((latentCube n).domRestrict (theta.1.p i))
  have hF : Continuous F := by
    have h := (UniformOnFun.continuous_rng_iff.mp
      (continuous_stratum_p_valueCoordinate (G := G) (s := s) i)
      (latentCube n) (by simp))
    simpa [F, Function.comp_def] using h
  apply continuous_uniformFun_eval₂_of_continuous F hF
  intro theta
  exact (theta.property.positiveSmooth.2.2.1 i).continuousOn.restrict

/-- Intervention-factor evaluation is jointly continuous in a stratum mechanism and a unit
coordinate.  [the stated conclusion](goal) follows. -/
lemma continuous_stratum_q_eval
    {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n} (i : Fin n) :
    Continuous (fun z : StratumPoint G s × {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1} ↦
      z.1.1.q i z.2.1) := by
  let F : StratumPoint G s →
      UniformFun {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1} ℝ := fun theta ↦
    UniformFun.ofFun (Set.Icc (0 : ℝ) 1 |>.domRestrict (theta.1.q i))
  have hF : Continuous F := by
    have h := (UniformOnFun.continuous_rng_iff.mp
      (continuous_stratum_q_valueCoordinate (G := G) (s := s) i)
      (Set.Icc (0 : ℝ) 1) (by simp))
    simpa [F, Function.comp_def] using h
  apply continuous_uniformFun_eval₂_of_continuous F hF
  intro theta
  exact (theta.property.positiveSmooth.2.2.2.1 i).continuousOn.restrict

/-- Coordinatewise projection supplies a continuous ambient representative of a latent-cube
point.  [the stated conclusion](goal) follows. -/
lemma continuous_compactCube_projection (n : ℕ) :
    Continuous (fun v : LatentState n ↦
      compactCubeInclude n (compactCubeRetract n v)) := by
  unfold compactCubeInclude compactCubeRetract
  fun_prop

/-- The [coordinatewise compact-cube projection belongs to the latent cube](goal). -/
lemma compactCube_projection_mem (n : ℕ) (v : LatentState n) :
    compactCubeInclude n (compactCubeRetract n v) ∈ latentCube n := by
  intro i _
  exact (Set.projIcc 0 1 (by norm_num) (v i)).property

/-- The compact-cube rational contrast integrand, continuously extended to the ambient latent
space by coordinatewise projection, is jointly continuous in the mechanism and latent state.  Given [the stated inputs and conditions](hyp:hji), [the stated conclusion](goal) follows. -/
lemma continuous_stratum_contrastIntegrand
    {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n}
    {j i : Fin n} (hji : G.edge j i) :
    Continuous (fun z : StratumPoint G s × LatentState n ↦
      let v := compactCubeInclude n (compactCubeRetract n z.2)
      (z.1.1.q i (v i)) ^ 2 * (z.1.1.q j (v j) - z.1.1.p j v) *
        (∏ l ∈ (Finset.univ.erase i).erase j, z.1.1.p l v) / z.1.1.p i v) := by
  let R : LatentState n → LatentState n := fun v ↦
    compactCubeInclude n (compactCubeRetract n v)
  have hR : Continuous R := continuous_compactCube_projection n
  have hRmem : ∀ v, R v ∈ latentCube n := compactCube_projection_mem n
  have hp (l : Fin n) : Continuous (fun z : StratumPoint G s × LatentState n ↦
      z.1.1.p l (R z.2)) := by
    exact (continuous_stratum_p_eval (G := G) (s := s) l).comp
      (continuous_fst.prodMk
        ((hR.comp continuous_snd).subtype_mk (fun z ↦ hRmem z.2)))
  have hq (l : Fin n) : Continuous (fun z : StratumPoint G s × LatentState n ↦
      z.1.1.q l (R z.2 l)) := by
    exact (continuous_stratum_q_eval (G := G) (s := s) l).comp
      (continuous_fst.prodMk (((continuous_apply l).comp (hR.comp continuous_snd)).subtype_mk
        (fun z ↦ hRmem z.2 l (Set.mem_univ l))))
  dsimp only
  apply Continuous.div
  · exact (((hq i).pow 2).mul ((hq j).sub (hp j))).mul
      (continuous_finsetProd _ fun l _ ↦ hp l)
  · exact hp i
  · intro z
    exact ne_of_gt (z.1.property.positiveSmooth.1 i (R z.2) (hRmem z.2))

/-- A canonical direct-edge second-moment contrast varies continuously with the mechanism in the
induced relative product C² topology.  Given [the stated inputs and conditions](hyp:hji), [the stated conclusion](goal) follows. -/
lemma continuous_canonical_secondMomentContrast
    {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n}
    (pi : Equiv.Perm (Fin n)) {j i : Fin n} (hji : G.edge j i) :
    Continuous (fun theta : StratumPoint G s ↦
      secondMomentContrast (canonicalObservedWorld G theta.1 pi)
        (pi.symm j) (pi.symm i)) := by
  let F : StratumPoint G s → LatentState n → ℝ := fun theta v ↦
    (theta.1.q i (v i)) ^ 2 * (theta.1.q j (v j) - theta.1.p j v) *
      (∏ l ∈ (Finset.univ.erase i).erase j, theta.1.p l v) / theta.1.p i v
  letI : CompactSpace {v : LatentState n // v ∈ latentCube n} :=
    isCompact_iff_compactSpace.mp (by
    rw [latentCube]
    exact isCompact_univ_pi fun _ ↦ isCompact_Icc)
  have hFcont (theta : StratumPoint G s) : ContinuousOn (F theta) (latentCube n) := by
    have hq (l : Fin n) : ContinuousOn (fun v : LatentState n ↦ theta.1.q l (v l))
        (latentCube n) :=
      (theta.property.positiveSmooth.2.2.2.1 l).continuousOn.comp
        (continuous_apply l).continuousOn (fun v hv ↦ hv l (Set.mem_univ l))
    have hp (l : Fin n) := (theta.property.positiveSmooth.2.2.1 l).continuousOn
    exact (((hq i).pow 2).mul ((hq j).sub (hp j))).mul
      (continuousOn_finsetProd _ fun l _ ↦ hp l) |>.div (hp i)
        (fun v hv ↦ ne_of_gt (theta.property.positiveSmooth.1 i v hv))
  have hJoint : Continuous (fun z : StratumPoint G s ×
      {v : LatentState n // v ∈ latentCube n} ↦ F z.1 z.2.1) := by
    have h := (continuous_stratum_contrastIntegrand (G := G) (s := s) hji).comp
      (show Continuous (fun z : StratumPoint G s ×
          {v : LatentState n // v ∈ latentCube n} ↦ (z.1, z.2.1)) by fun_prop)
    convert h using 1
    funext z
    dsimp [F]
    rw [compactCubeInclude_retract_of_mem z.2.property]
  let FC : StratumPoint G s → C({v : LatentState n // v ∈ latentCube n}, ℝ) := fun theta ↦
    ⟨fun v ↦ F theta v.1, (hFcont theta).restrict⟩
  have hFC : Continuous FC := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : StratumPoint G s ×
      {v : LatentState n // v ∈ latentCube n} ↦ F z.1 z.2.1)
    exact hJoint
  have hUniform : Continuous (fun theta ↦
      UniformOnFun.ofFun {latentCube n} (F theta)) := by
    apply (ContinuousOn.continuous_domRestrict_iff_continuous_uniformOnFun hFcont).mp
    exact hFC
  have hmu : MeasureTheory.volume (latentCube n) < ⊤ := (show IsCompact (latentCube n) by
    rw [latentCube]
    exact isCompact_univ_pi fun _ ↦ isCompact_Icc).measure_lt_top
  have hInt (theta : StratumPoint G s) :
      MeasureTheory.IntegrableOn (F theta) (latentCube n) :=
    (hFcont theta).integrableOn_compact (by
      rw [latentCube]
      exact isCompact_univ_pi fun _ ↦ isCompact_Icc)
  have hint : Continuous (fun theta ↦ ∫ v in latentCube n, F theta v) :=
    Causalean.Mathlib.MeasureTheory.continuous_setIntegral_of_continuous_uniformOn
      MeasureTheory.volume
      (latentCube n) hmu F hUniform hInt
  have hne : j ≠ i := fun h ↦ by subst j; exact G.irrefl i hji
  rw [show (fun theta : StratumPoint G s ↦
      secondMomentContrast (canonicalObservedWorld G theta.1 pi)
        (pi.symm j) (pi.symm i)) = fun theta ↦ ∫ v in latentCube n, F theta v by
    funext theta
    rw [canonical_secondMomentContrast_perm_eq,
      canonical_secondMomentContrast_eq_integral theta.property.positiveSmooth hne]]
  exact hint

/-- The explicit Gaussian feature vector depends continuously on its scalar argument.  [the stated conclusion](goal) follows. -/
lemma continuous_gaussianFeature : Continuous gaussianFeature := by
  rw [continuous_iff_continuousAt]
  intro r
  have hnormsq (x : ℝ) : ‖gaussianFeature x - gaussianFeature r‖ ^ 2 =
      2 - 2 * gaussianKernel x r := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, gaussianFeature_inner]
    simp [gaussianKernel]
    ring
  have hsquare : ContinuousAt (fun x : ℝ =>
      2 - 2 * gaussianKernel x r) r := by
    unfold gaussianKernel
    fun_prop
  have hzero : 2 - 2 * gaussianKernel r r = 0 := by
    simp [gaussianKernel]
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hsqrt := Real.continuous_sqrt.continuousAt.comp hsquare
  change Filter.Tendsto (fun x : ℝ => Real.sqrt
      (2 - 2 * gaussianKernel x r)) (nhds r)
      (nhds (Real.sqrt (2 - 2 * gaussianKernel r r))) at hsqrt
  have hsqrt' : Filter.Tendsto (fun x : ℝ => Real.sqrt
      (2 - 2 * gaussianKernel x r)) (nhds r)
      (nhds (Real.sqrt (2 - 2 * gaussianKernel r r))) := by
    exact hsqrt
  rw [hzero, Real.sqrt_zero] at hsqrt'
  convert hsqrt' using 1
  funext x
  rw [← hnormsq x, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

/-- The observational Gaussian-embedding integrand is jointly continuous on the mechanism
stratum and compact latent cube.  [the stated conclusion](goal) follows. -/
lemma continuous_stratum_observationalGaussianIntegrand
    {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n} (i : Fin n) :
    Continuous (fun z : StratumPoint G s ×
        {v : LatentState n // v ∈ latentCube n} ↦
      observationalDensity z.1.1 z.2.1 •
        gaussianFeature (z.1.1.q i (z.2.1 i) / z.1.1.p i z.2.1)) := by
  have hp (l : Fin n) : Continuous (fun z : StratumPoint G s ×
      {v : LatentState n // v ∈ latentCube n} ↦ z.1.1.p l z.2.1) :=
    continuous_stratum_p_eval (G := G) (s := s) l
  have hq (l : Fin n) : Continuous (fun z : StratumPoint G s ×
      {v : LatentState n // v ∈ latentCube n} ↦ z.1.1.q l (z.2.1 l)) := by
    have hc : Continuous (fun z : StratumPoint G s ×
        {v : LatentState n // v ∈ latentCube n} ↦ z.2.1 l) :=
      (continuous_apply l).comp (continuous_subtype_val.comp continuous_snd)
    have hc' : Continuous (fun z : StratumPoint G s ×
        {v : LatentState n // v ∈ latentCube n} ↦
        (⟨z.2.1 l, z.2.property l (Set.mem_univ l)⟩ :
          {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1})) :=
      hc.subtype_mk _
    convert (continuous_stratum_q_eval (G := G) (s := s) l).comp
        (continuous_fst.prodMk hc') using 1 <;> rfl
  have hr : Continuous (fun z : StratumPoint G s ×
      {v : LatentState n // v ∈ latentCube n} ↦
      z.1.1.q i (z.2.1 i) / z.1.1.p i z.2.1) := by
    exact (hq i).div (hp i) fun z ↦
      ne_of_gt (z.1.property.positiveSmooth.1 i z.2.1 z.2.property)
  unfold observationalDensity
  exact (continuous_finsetProd _ fun l _ ↦ hp l).smul
    (continuous_gaussianFeature.comp hr)

/-- The target-interventional Gaussian-embedding integrand is jointly continuous on the
mechanism stratum and compact latent cube.  [the stated conclusion](goal) follows. -/
lemma continuous_stratum_interventionalGaussianIntegrand
    {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n} (j i : Fin n) :
    Continuous (fun z : StratumPoint G s ×
        {v : LatentState n // v ∈ latentCube n} ↦
      interventionalDensity z.1.1 j z.2.1 •
        gaussianFeature (z.1.1.q i (z.2.1 i) / z.1.1.p i z.2.1)) := by
  have hp (l : Fin n) : Continuous (fun z : StratumPoint G s ×
      {v : LatentState n // v ∈ latentCube n} ↦ z.1.1.p l z.2.1) :=
    continuous_stratum_p_eval (G := G) (s := s) l
  have hq (l : Fin n) : Continuous (fun z : StratumPoint G s ×
      {v : LatentState n // v ∈ latentCube n} ↦ z.1.1.q l (z.2.1 l)) := by
    have hc : Continuous (fun z : StratumPoint G s ×
        {v : LatentState n // v ∈ latentCube n} ↦ z.2.1 l) :=
      (continuous_apply l).comp (continuous_subtype_val.comp continuous_snd)
    have hc' : Continuous (fun z : StratumPoint G s ×
        {v : LatentState n // v ∈ latentCube n} ↦
        (⟨z.2.1 l, z.2.property l (Set.mem_univ l)⟩ :
          {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1})) :=
      hc.subtype_mk _
    convert (continuous_stratum_q_eval (G := G) (s := s) l).comp
        (continuous_fst.prodMk hc') using 1 <;> rfl
  have hr : Continuous (fun z : StratumPoint G s ×
      {v : LatentState n // v ∈ latentCube n} ↦
      z.1.1.q i (z.2.1 i) / z.1.1.p i z.2.1) := by
    exact (hq i).div (hp i) fun z ↦
      ne_of_gt (z.1.property.positiveSmooth.1 i z.2.1 z.2.property)
  unfold interventionalDensity
  exact ((hq j).mul (continuous_finsetProd _ fun l _ ↦ hp l)).smul
    (continuous_gaussianFeature.comp hr)

/-- The canonical observational ratio-law embedding is the explicit weighted cube integral.  Given [the stated inputs and conditions](hyp:hpos), [the stated conclusion](goal) follows. -/
lemma canonical_observationalMeanEmbedding_eq_setIntegral
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (π : Equiv.Perm (Fin n)) (i : Fin n) :
    meanEmbedding gaussianFeatureMap
        (observationalRatioLaw (canonicalObservedWorld G θ π) i) =
      ∫ v in latentCube n, observationalDensity θ v •
        gaussianFeature (θ.q (π i) (v (π i)) / θ.p (π i) v) := by
  let W := canonicalObservedWorld G θ π
  let r : LatentState n → ℝ := fun v ↦
    θ.q (π i) (v (π i)) / θ.p (π i) v
  let μ : MeasureTheory.Measure (LatentState n) :=
    MeasureTheory.volume.restrict (latentCube n)
  have hcube : MeasurableSet (latentCube n) := by
    rw [latentCube]
    exact MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc
  have hobsCube : ∀ᵐ v ∂observationalLaw θ, v ∈ latentCube n :=
    observationalLaw_ae_mem_latentCube hpos
  have hone := canonicalObservedWorld_onePerfectInterventionPerNode hpos π
  have hr : observedLawRatio W.law i =ᵐ[observationalLaw θ] r := by
    filter_upwards [hone.2.2.1 i, hobsCube] with v hrv hv
    change ((interventionalLaw θ (π i)).rnDeriv (observationalLaw θ) v).toReal = r v
    calc
      _ = (ENNReal.ofReal (W.ratio i v)).toReal := congrArg ENNReal.toReal hrv.symm
      _ = W.ratio i v := ENNReal.toReal_ofReal
        (div_nonneg (hpos.2.1 _ _ (hv (π i) (Set.mem_univ _))).le
          (hpos.1 _ _ hv).le)
      _ = r v := by rfl
  have hobscont : ContinuousOn (observationalDensity θ) (latentCube n) := by
    unfold observationalDensity
    exact continuousOn_finsetProd _ fun l _ ↦ (hpos.2.2.1 l).continuousOn
  unfold meanEmbedding observationalRatioLaw
  change (∫ x, gaussianFeature x ∂MeasureTheory.Measure.map
      (observedLawRatio W.law i) (observationalLaw θ)) = _
  rw [MeasureTheory.integral_map
    (measurable_observedLawRatio W.law i).aemeasurable
    continuous_gaussianFeature.aestronglyMeasurable]
  calc
    (∫ v, gaussianFeature (observedLawRatio W.law i v) ∂observationalLaw θ) =
        ∫ v, gaussianFeature (r v) ∂observationalLaw θ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [hr] with v hv
      rw [hv]
    _ = ∫ v, observationalDensity θ v • gaussianFeature (r v) ∂μ := by
      unfold observationalLaw
      rw [integral_withDensity_eq_integral_toReal_smul₀]
      · apply MeasureTheory.integral_congr_ae
        filter_upwards [MeasureTheory.ae_restrict_mem hcube] with v hv
        rw [ENNReal.toReal_ofReal (le_of_lt (by
          unfold observationalDensity
          exact Finset.prod_pos fun l _ ↦ hpos.1 l v hv))]
      · exact (hobscont.aestronglyMeasurable hcube).aemeasurable.ennreal_ofReal
      · filter_upwards with v
        exact ENNReal.ofReal_lt_top
    _ = _ := by rfl

/-- The canonical interventional ratio-law embedding is the explicit weighted cube integral.  Given [the stated inputs and conditions](hyp:hpos), [the stated conclusion](goal) follows. -/
lemma canonical_interventionalMeanEmbedding_eq_setIntegral
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (π : Equiv.Perm (Fin n)) (j i : Fin n) :
    meanEmbedding gaussianFeatureMap
        (interventionalRatioLaw (canonicalObservedWorld G θ π) j i) =
      ∫ v in latentCube n, interventionalDensity θ (π j) v •
        gaussianFeature (θ.q (π i) (v (π i)) / θ.p (π i) v) := by
  let W := canonicalObservedWorld G θ π
  let r : LatentState n → ℝ := fun v ↦
    θ.q (π i) (v (π i)) / θ.p (π i) v
  let μ : MeasureTheory.Measure (LatentState n) :=
    MeasureTheory.volume.restrict (latentCube n)
  have hcube : MeasurableSet (latentCube n) := by
    rw [latentCube]
    exact MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc
  have hobsCube : ∀ᵐ v ∂observationalLaw θ, v ∈ latentCube n :=
    observationalLaw_ae_mem_latentCube hpos
  have hone := canonicalObservedWorld_onePerfectInterventionPerNode hpos π
  have hrObs : observedLawRatio W.law i =ᵐ[observationalLaw θ] r := by
    filter_upwards [hone.2.2.1 i, hobsCube] with v hrv hv
    change ((interventionalLaw θ (π i)).rnDeriv (observationalLaw θ) v).toReal = r v
    calc
      _ = (ENNReal.ofReal (W.ratio i v)).toReal := congrArg ENNReal.toReal hrv.symm
      _ = W.ratio i v := ENNReal.toReal_ofReal
        (div_nonneg (hpos.2.1 _ _ (hv (π i) (Set.mem_univ _))).le
          (hpos.1 _ _ hv).le)
      _ = r v := by rfl
  have hac : interventionalLaw θ (π j) ≪ observationalLaw θ := by
    simpa only [W, canonicalObservedWorld] using
      interventionalLaw_absolutelyContinuous_observational W hpos j
  have hr : observedLawRatio W.law i =ᵐ[interventionalLaw θ (π j)] r :=
    hac.ae_eq hrObs
  have hintcont : ContinuousOn (interventionalDensity θ (π j)) (latentCube n) := by
    unfold interventionalDensity
    have hq : ContinuousOn (fun v : LatentState n ↦ θ.q (π j) (v (π j)))
        (latentCube n) :=
      (hpos.2.2.2.1 (π j)).continuousOn.comp
        ((continuous_apply (π j)).continuousOn)
        (fun v hv ↦ hv (π j) (Set.mem_univ _))
    exact hq.mul (continuousOn_finsetProd _ fun l _ ↦
      (hpos.2.2.1 l).continuousOn)
  unfold meanEmbedding interventionalRatioLaw
  change (∫ x, gaussianFeature x ∂MeasureTheory.Measure.map
      (observedLawRatio W.law i) (interventionalLaw θ (π j))) = _
  rw [MeasureTheory.integral_map
    (measurable_observedLawRatio W.law i).aemeasurable
    continuous_gaussianFeature.aestronglyMeasurable]
  calc
    (∫ v, gaussianFeature (observedLawRatio W.law i v)
        ∂interventionalLaw θ (π j)) =
        ∫ v, gaussianFeature (r v) ∂interventionalLaw θ (π j) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [hr] with v hv
      rw [hv]
    _ = ∫ v, interventionalDensity θ (π j) v • gaussianFeature (r v) ∂μ := by
      unfold interventionalLaw
      rw [integral_withDensity_eq_integral_toReal_smul₀]
      · apply MeasureTheory.integral_congr_ae
        filter_upwards [MeasureTheory.ae_restrict_mem hcube] with v hv
        rw [ENNReal.toReal_ofReal (le_of_lt (by
          unfold interventionalDensity
          exact mul_pos (hpos.2.1 (π j) (v (π j))
            (hv (π j) (Set.mem_univ _)))
            (Finset.prod_pos fun l _ ↦ hpos.1 l v hv)))]
      · exact (hintcont.aestronglyMeasurable hcube).aemeasurable.ennreal_ofReal
      · filter_upwards with v
        exact ENNReal.ofReal_lt_top
    _ = _ := by rfl

/-- The canonical Gaussian population discrepancy varies continuously with the mechanism.  [the stated conclusion](goal) follows. -/
lemma continuous_canonical_populationDiscrepancy
    {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n}
    (π : Equiv.Perm (Fin n)) (j i : Fin n) :
    Continuous (fun θ : StratumPoint G s ↦
      populationDiscrepancy gaussianFeatureMap
        (canonicalObservedWorld G θ.1 π) (π.symm j) (π.symm i)) := by
  let Fobs := fun θ : StratumPoint G s ↦ fun v : LatentState n ↦
    observationalDensity θ.1 v •
      gaussianFeature (θ.1.q i (v i) / θ.1.p i v)
  let Fint := fun θ : StratumPoint G s ↦ fun v : LatentState n ↦
    interventionalDensity θ.1 j v •
      gaussianFeature (θ.1.q i (v i) / θ.1.p i v)
  letI : CompactSpace {v : LatentState n // v ∈ latentCube n} :=
    isCompact_iff_compactSpace.mp (by
      rw [latentCube]
      exact isCompact_univ_pi fun _ ↦ isCompact_Icc)
  have hcompact : IsCompact (latentCube n) := by
    rw [latentCube]
    exact isCompact_univ_pi fun _ ↦ isCompact_Icc
  have hobsJoint : Continuous (fun z : StratumPoint G s ×
      {v : LatentState n // v ∈ latentCube n} ↦ Fobs z.1 z.2.1) := by
    exact continuous_stratum_observationalGaussianIntegrand
      (G := G) (s := s) i
  have hintJoint : Continuous (fun z : StratumPoint G s ×
      {v : LatentState n // v ∈ latentCube n} ↦ Fint z.1 z.2.1) := by
    exact continuous_stratum_interventionalGaussianIntegrand
      (G := G) (s := s) j i
  have hobsOn (θ : StratumPoint G s) : ContinuousOn (Fobs θ) (latentCube n) := by
    apply continuousOn_iff_continuous_restrict.mpr
    exact hobsJoint.comp (continuous_const.prodMk continuous_id)
  have hintOn (θ : StratumPoint G s) : ContinuousOn (Fint θ) (latentCube n) := by
    apply continuousOn_iff_continuous_restrict.mpr
    exact hintJoint.comp (continuous_const.prodMk continuous_id)
  let Cobs : StratumPoint G s →
      C({v : LatentState n // v ∈ latentCube n}, lp (fun _ : ℕ => ℝ) 2) :=
    fun θ ↦ ⟨fun v ↦ Fobs θ v.1, (hobsOn θ).restrict⟩
  let Cint : StratumPoint G s →
      C({v : LatentState n // v ∈ latentCube n}, lp (fun _ : ℕ => ℝ) 2) :=
    fun θ ↦ ⟨fun v ↦ Fint θ v.1, (hintOn θ).restrict⟩
  have hCobs : Continuous Cobs := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact hobsJoint
  have hCint : Continuous Cint := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact hintJoint
  have hobsUniform : Continuous (fun θ ↦
      UniformOnFun.ofFun {latentCube n} (Fobs θ)) := by
    apply (ContinuousOn.continuous_domRestrict_iff_continuous_uniformOnFun hobsOn).mp
    exact hCobs
  have hintUniform : Continuous (fun θ ↦
      UniformOnFun.ofFun {latentCube n} (Fint θ)) := by
    apply (ContinuousOn.continuous_domRestrict_iff_continuous_uniformOnFun hintOn).mp
    exact hCint
  have hmu : volume (latentCube n) < ⊤ := hcompact.measure_lt_top
  have hobsInt (θ : StratumPoint G s) : IntegrableOn (Fobs θ) (latentCube n) :=
    (hobsOn θ).integrableOn_compact hcompact
  have hintInt (θ : StratumPoint G s) : IntegrableOn (Fint θ) (latentCube n) :=
    (hintOn θ).integrableOn_compact hcompact
  have hobsIntegral : Continuous (fun θ ↦
      ∫ v in latentCube n, Fobs θ v) :=
    Causalean.Mathlib.MeasureTheory.continuous_setIntegral_of_continuous_uniformOn
      volume (latentCube n) hmu
      Fobs hobsUniform hobsInt
  have hintIntegral : Continuous (fun θ ↦
      ∫ v in latentCube n, Fint θ v) :=
    Causalean.Mathlib.MeasureTheory.continuous_setIntegral_of_continuous_uniformOn
      volume (latentCube n) hmu
      Fint hintUniform hintInt
  rw [show (fun θ : StratumPoint G s ↦
      populationDiscrepancy gaussianFeatureMap
        (canonicalObservedWorld G θ.1 π) (π.symm j) (π.symm i)) =
      fun θ ↦ ‖(∫ v in latentCube n, Fobs θ v) -
        ∫ v in latentCube n, Fint θ v‖ by
    funext θ
    unfold populationDiscrepancy
    rw [canonical_observationalMeanEmbedding_eq_setIntegral
      θ.property.positiveSmooth π (π.symm i),
      canonical_interventionalMeanEmbedding_eq_setIntegral
        θ.property.positiveSmooth π (π.symm j) (π.symm i)]
    simp only [Equiv.apply_symm_apply, Fobs, Fint]]
  exact (hobsIntegral.sub hintIntegral).norm

/-- A finite intersection of open dense sets is dense, without any Baire-space assumption.  Given [the stated inputs and conditions](hyp:hopen,hdense), [the stated conclusion](goal) follows. -/
lemma dense_biInter_finset_of_open
    {X I : Type*} [TopologicalSpace X] [DecidableEq I]
    (S : Finset I) (A : I → Set X)
    (hopen : ∀ i ∈ S, IsOpen (A i)) (hdense : ∀ i ∈ S, Dense (A i)) :
    Dense (⋂ i ∈ S, A i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      rw [show (⋂ i ∈ insert a S, A i) = A a ∩ ⋂ i ∈ S, A i by
        ext x
        simp [ha]]
      exact (hdense a (by simp)).inter_of_isOpen_left
        (ih (fun i hi ↦ hopen i (by simp [hi])) (fun i hi ↦ hdense i (by simp [hi])))
        (hopen a (by simp))

/-- Direct-edge contrast separation is open in the stratum topology.  [the stated conclusion](goal) follows. -/
lemma edgeSeparatedSet_isOpen
    {n : ℕ} (G : Causalean.DAG (Fin n)) (s : SignVector n)
    (pi : Equiv.Perm (Fin n)) :
    IsOpen (edgeSeparatedSet (G := G) (s := s) pi) := by
  rw [isOpen_iff_mem_nhds]
  intro theta htheta
  have hall : ∀ᶠ eta in nhds theta, ∀ j i, G.edge j i →
      secondMomentContrast (canonicalObservedWorld G eta.1 pi)
        (pi.symm j) (pi.symm i) ≠ 0 := by
    have hpairs : ∀ᶠ eta in nhds theta, ∀ ji : Fin n × Fin n,
        ji ∈ (Set.univ : Set (Fin n × Fin n)) → G.edge ji.1 ji.2 →
        secondMomentContrast (canonicalObservedWorld G eta.1 pi)
          (pi.symm ji.1) (pi.symm ji.2) ≠ 0 :=
      (Filter.eventually_all_finite
        (l := nhds theta)
        (p := fun ji eta ↦ G.edge ji.1 ji.2 →
          secondMomentContrast (canonicalObservedWorld G eta.1 pi)
            (pi.symm ji.1) (pi.symm ji.2) ≠ 0)
        (Set.toFinite (Set.univ : Set (Fin n × Fin n)))).2
        (fun ji _ ↦ by
          by_cases hedge : G.edge ji.1 ji.2
          · have hc := continuous_canonical_secondMomentContrast
              (G := G) (s := s) pi hedge
            filter_upwards [hc.continuousAt (isOpen_compl_singleton.mem_nhds
              (by simpa [edgeSeparatedSet] using htheta hedge))] with eta heta
            exact fun _ ↦ heta
          · exact Filter.Eventually.of_forall fun _ h ↦ (hedge h).elim)
    filter_upwards [hpairs] with eta heta
    exact fun j i hji ↦ heta (j, i) (Set.mem_univ _) hji
  filter_upwards [hall] with eta heta
  exact heta

/-- Direct-edge contrast separation is dense in the stratum topology.  [the stated conclusion](goal) follows. -/
lemma edgeSeparatedSet_dense
    {n : ℕ} (G : Causalean.DAG (Fin n)) (s : SignVector n)
    (pi : Equiv.Perm (Fin n)) :
    Dense (edgeSeparatedSet (G := G) (s := s) pi) := by
  let A : (Fin n × Fin n) → Set (StratumPoint G s) := fun ji ↦
    if h : G.edge ji.1 ji.2 then
      {theta | secondMomentContrast (canonicalObservedWorld G theta.1 pi)
        (pi.symm ji.1) (pi.symm ji.2) ≠ 0}
    else Set.univ
  have hopen : ∀ ji ∈ (Finset.univ : Finset (Fin n × Fin n)), IsOpen (A ji) := by
    intro ji _
    dsimp [A]
    split_ifs with h
    · exact (continuous_canonical_secondMomentContrast
        (G := G) (s := s) pi h).isOpen_preimage {0}ᶜ isOpen_compl_singleton
    · exact isOpen_univ
  have hdense : ∀ ji ∈ (Finset.univ : Finset (Fin n × Fin n)), Dense (A ji) := by
    intro ji _
    dsimp [A]
    split_ifs with h
    · exact edgeContrastNonzeroSet_dense G s pi h
    · exact dense_univ
  have h := dense_biInter_finset_of_open (Finset.univ : Finset (Fin n × Fin n))
    A hopen hdense
  apply h.mono
  intro theta htheta j i hji
  have hmem : theta ∈ A (j, i) :=
    Set.mem_iInter.mp (Set.mem_iInter.mp htheta (j, i)) (Finset.mem_univ _)
  simpa [A, hji] using hmem

/-- Ancestral-cover Gaussian-MMD separation is open in the mechanism stratum.  [the stated conclusion](goal) follows. -/
lemma coverSeparatedSet_isOpen
    {n : ℕ} (G : Causalean.DAG (Fin n)) (s : SignVector n)
    (π : Equiv.Perm (Fin n)) :
    IsOpen (coverSeparatedSet (G := G) (s := s) gaussianFeatureMap π) := by
  rw [isOpen_iff_mem_nhds]
  intro θ hθ
  have hpairs : ∀ᶠ η in nhds θ, ∀ ji : Fin n × Fin n,
      ji ∈ (Set.univ : Set (Fin n × Fin n)) → ancestralCover G ji.1 ji.2 →
      0 < populationDiscrepancy gaussianFeatureMap
        (canonicalObservedWorld G η.1 π) (π.symm ji.1) (π.symm ji.2) :=
    (Filter.eventually_all_finite
      (l := nhds θ)
      (p := fun ji η ↦ ancestralCover G ji.1 ji.2 →
        0 < populationDiscrepancy gaussianFeatureMap
          (canonicalObservedWorld G η.1 π) (π.symm ji.1) (π.symm ji.2))
      (Set.toFinite (Set.univ : Set (Fin n × Fin n)))).2
      (fun ji _ ↦ by
        by_cases hcover : ancestralCover G ji.1 ji.2
        · have hc := continuous_canonical_populationDiscrepancy
            (G := G) (s := s) π ji.1 ji.2
          filter_upwards [hc.continuousAt
            (isOpen_Ioi.mem_nhds (hθ hcover))] with η hη
          exact fun _ ↦ hη
        · exact Filter.Eventually.of_forall fun _ h ↦ (hcover h).elim)
  filter_upwards [hpairs] with η hη
  exact fun j i hji ↦ hη (j, i) (Set.mem_univ _) hji

-- @node: ancestralCover_edge
/-- An ancestral cover in a DAG is necessarily a direct edge.  Given [the stated inputs and conditions](hyp:hji), [the stated conclusion](goal) follows. -/
lemma ancestralCover_edge
    {n : ℕ} {G : Causalean.DAG (Fin n)} {j i : Fin n}
    (hji : ancestralCover G j i) : G.edge j i := by
  have hanc : G.isAncestor j i :=
    @CovBy.lt (Fin n) ⟨G.isAncestor⟩ j i hji
  rcases G.isAncestor_child hanc with hedge | ⟨k, hjk, hki⟩
  · exact hedge
  · exact (hji.2 (Causalean.DAG.isAncestor.edge hjk) hki).elim

-- @node: ancestralCover_false_of_no_edge
/-- An edge-free DAG has no ancestral covers.  Given [the stated inputs and conditions](hyp:hG,hji), [the stated conclusion](goal) follows. -/
lemma ancestralCover_false_of_no_edge
    {n : ℕ} {G : Causalean.DAG (Fin n)}
    (hG : ∀ j i, ¬ G.edge j i) {j i : Fin n}
    (hji : ancestralCover G j i) : False := by
  exact hG j i (ancestralCover_edge hji)

-- @node: separatedSets_eq_univ_of_no_edge
/-- Both separation conditions are vacuous for an edge-free DAG.  Given [the stated inputs and conditions](hyp:hG), [the stated conclusion](goal) follows. -/
lemma separatedSets_eq_univ_of_no_edge
    {n : ℕ} (G : Causalean.DAG (Fin n)) (s : SignVector n)
    (π : Equiv.Perm (Fin n)) (hG : ∀ j i, ¬ G.edge j i) :
    edgeSeparatedSet (G := G) (s := s) π = Set.univ ∧
      coverSeparatedSet (G := G) (s := s) gaussianFeatureMap π = Set.univ := by
  constructor
  · ext θ
    simp only [edgeSeparatedSet, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    intro j i hji
    exact (hG j i hji).elim
  · ext θ
    simp only [coverSeparatedSet, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    intro j i hji
    exact (ancestralCover_false_of_no_edge hG hji).elim

-- @node: openDense_compl_topology
/-- The complement of an open dense set is closed, nowhere dense, and meagre.  Given [the stated inputs and conditions](hyp:hopen,hdense), [the stated conclusion](goal) follows. -/
lemma openDense_compl_topology
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hopen : IsOpen A) (hdense : Dense A) :
    IsMeagre Aᶜ ∧ IsClosed Aᶜ ∧ IsNowhereDense Aᶜ := by
  have hclosed_nowhere : IsClosed Aᶜ ∧ IsNowhereDense Aᶜ := by
    rw [isClosed_isNowhereDense_iff_compl]
    simpa using And.intro hopen hdense
  exact ⟨hclosed_nowhere.2.isMeagre, hclosed_nowhere.1, hclosed_nowhere.2⟩

-- @node: edgeSeparated_subset_coverSeparated
/-- Direct-edge raw second-moment separation implies Gaussian-MMD separation on every
ancestral cover.  [the stated conclusion](goal) follows. -/
lemma edgeSeparated_subset_coverSeparated
    {n : ℕ} (G : Causalean.DAG (Fin n)) (s : SignVector n)
    (π : Equiv.Perm (Fin n)) :
    edgeSeparatedSet (G := G) (s := s) π ⊆
      coverSeparatedSet (G := G) (s := s) gaussianFeatureMap π := by
  intro θ hθ j i hji
  apply canonical_populationDiscrepancy_pos_of_secondMomentContrast_ne
    θ.property.positiveSmooth π
  exact hθ (ancestralCover_edge hji)

-- @node: thm:generic-cover-separation
/-- In every nonempty fixed-DAG sign stratum, direct-edge moment separation is open dense and
implies an open dense residual ancestral-cover MMD region with closed nowhere-dense complement.  Given [the stated inputs and conditions](hyp:hne), [the stated conclusion](goal) follows. -/
theorem generic_cover_separation
    {n : ℕ} (G : Causalean.DAG (Fin n)) (s : SignVector n)
    (π : Equiv.Perm (Fin n))
    (hne : (Set.univ : Set (StratumPoint G s)).Nonempty) :
    IsOpen (edgeSeparatedSet (G := G) (s := s) π) ∧
    Dense (edgeSeparatedSet (G := G) (s := s) π) ∧
    edgeSeparatedSet (G := G) (s := s) π ⊆
      coverSeparatedSet (G := G) (s := s) gaussianFeatureMap π ∧
    IsOpen (coverSeparatedSet (G := G) (s := s) gaussianFeatureMap π) ∧
    Dense (coverSeparatedSet (G := G) (s := s) gaussianFeatureMap π) ∧
    IsMeagre ((coverSeparatedSet (G := G) (s := s) gaussianFeatureMap π)ᶜ) ∧
    IsClosed ((coverSeparatedSet (G := G) (s := s) gaussianFeatureMap π)ᶜ) ∧
    IsNowhereDense ((coverSeparatedSet (G := G) (s := s) gaussianFeatureMap π)ᶜ) ∧
    ((∀ j i, ¬ G.edge j i) →
      edgeSeparatedSet (G := G) (s := s) π = Set.univ ∧
      coverSeparatedSet (G := G) (s := s) gaussianFeatureMap π = Set.univ) := by
  have hsubset := edgeSeparated_subset_coverSeparated G s π
  have htopology :
      IsOpen (edgeSeparatedSet (G := G) (s := s) π) ∧
      Dense (edgeSeparatedSet (G := G) (s := s) π) ∧
      IsOpen (coverSeparatedSet (G := G) (s := s) gaussianFeatureMap π) := by
    exact ⟨edgeSeparatedSet_isOpen G s π, edgeSeparatedSet_dense G s π,
      coverSeparatedSet_isOpen G s π⟩
  have hdenseCover : Dense
      (coverSeparatedSet (G := G) (s := s) gaussianFeatureMap π) :=
    htopology.2.1.mono hsubset
  have hcompl := openDense_compl_topology htopology.2.2 hdenseCover
  exact ⟨htopology.1, htopology.2.1, hsubset, htopology.2.2, hdenseCover,
    hcompl.1, hcompl.2.1, hcompl.2.2,
    separatedSets_eq_univ_of_no_edge G s π⟩

end CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity
