module
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.CompactCubeBridge
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.DecoderOrderedLocalMarkov
public import Causalean.Graph.Density.FiniteDAG.Positive.Main
public import Causalean.Mathlib.Probability.Independence.Conditional.Transport.AeRetraction
public import CausalSmith.Substrate.MeasurePreservingCondindepDomainTransport.WithDensity
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.UnitIntervalOpenPos

/-!
# Conditional-independence bridge to compact cube factorizations

This file transports the paper's ambient, cube-supported coordinate conditional independence
to the compact coordinate-product presentation used by positive finite-DAG factorizations.
-/

@[expose] public section

open Causalean.Graph


open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

open Causalean.Mathlib.Probability.Independence.Conditional.Transport

namespace CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

open Causalean.Graph.FiniteDensity
open CausalSmith.Substrate.MeasurePreservingCondindepDomainTransport

attribute [local instance] Measure.Subtype.measureSpace

/-- The [finite-coordinate projection from latent states is measurable](goal). -/
@[fun_prop]
lemma measurable_paperCoordinateProjection {n : ℕ} (S : Finset (Fin n)) :
    Measurable (coordinateProjection S) := by
  exact measurable_pi_lambda _ fun j ↦ measurable_pi_apply j.1

/-- On compact coordinates, the real-valued coordinate projection generates the same
sigma-algebra as the subtype-valued coordinate projection.  [the stated conclusion](goal) follows. -/
lemma comap_compact_realProjection_eq (n : ℕ) (S : Finset (Fin n)) :
    MeasurableSpace.comap
        ((coordinateProjection S) ∘ compactCubeInclude n) inferInstance =
      MeasurableSpace.comap
        (Causalean.Mathlib.MeasureTheory.FiniteCoordinate.coordinateProjection
          (X := fun _ : Fin n ↦ Set.Icc (0 : ℝ) 1) S) inferInstance := by
  let compactProjection :=
    Causalean.Mathlib.MeasureTheory.FiniteCoordinate.coordinateProjection
      (X := fun _ : Fin n ↦ Set.Icc (0 : ℝ) 1) S
  let coeProjection : ((j : {j // j ∈ S}) → Set.Icc (0 : ℝ) 1) →
      ((j : {j // j ∈ S}) → ℝ) := fun x j ↦ x j
  let retractProjection : ((j : {j // j ∈ S}) → ℝ) →
      ((j : {j // j ∈ S}) → Set.Icc (0 : ℝ) 1) :=
    fun x j ↦ Set.projIcc 0 1 (by norm_num) (x j)
  have hcoe : Measurable coeProjection := by
    exact measurable_pi_lambda _ fun j ↦
      measurable_subtype_coe.comp (measurable_pi_apply j)
  have hretract : Measurable retractProjection := by
    exact measurable_pi_lambda _ fun j ↦
      continuous_projIcc.measurable.comp (measurable_pi_apply j)
  have hreal : ((coordinateProjection S) ∘ compactCubeInclude n) =
      coeProjection ∘ compactProjection := rfl
  have hback : compactProjection = retractProjection ∘
      ((coordinateProjection S) ∘ compactCubeInclude n) := by
    funext x j
    apply Subtype.ext
    change (x j : ℝ) =
      ((Set.projIcc 0 1 (by norm_num) (x j) : Set.Icc (0 : ℝ) 1) : ℝ)
    exact congrArg Subtype.val
      (Set.projIcc_of_mem (show (0 : ℝ) ≤ 1 by norm_num) (x j).property).symm
  apply le_antisymm
  · rw [hreal]
    change MeasurableSpace.comap (coeProjection ∘ compactProjection) inferInstance ≤
      MeasurableSpace.comap compactProjection inferInstance
    simpa only [MeasurableSpace.comap_comp] using
      MeasurableSpace.comap_mono hcoe.comap_le
  · change MeasurableSpace.comap compactProjection inferInstance ≤
      MeasurableSpace.comap
        ((coordinateProjection S) ∘ compactCubeInclude n) inferInstance
    rw [hback]
    simpa only [MeasurableSpace.comap_comp] using
      MeasurableSpace.comap_mono hretract.comap_le

/-- On compact coordinates, coercing one interval-valued coordinate to a real generates the
same sigma-algebra as the original interval-valued coordinate.  [the stated conclusion](goal) follows. -/
lemma comap_compact_realCoordinate_eq (n : ℕ) (i : Fin n) :
    MeasurableSpace.comap
        ((fun v : LatentState n ↦ v i) ∘ compactCubeInclude n) inferInstance =
      MeasurableSpace.comap
        (fun x : (k : Fin n) → Set.Icc (0 : ℝ) 1 ↦ x i) inferInstance := by
  let compactCoordinate : ((k : Fin n) → Set.Icc (0 : ℝ) 1) →
      Set.Icc (0 : ℝ) 1 := fun x ↦ x i
  let coeCoordinate : Set.Icc (0 : ℝ) 1 → ℝ := Subtype.val
  let retractCoordinate : ℝ → Set.Icc (0 : ℝ) 1 :=
    Set.projIcc 0 1 (by norm_num)
  have hcoe : Measurable coeCoordinate := measurable_subtype_coe
  have hretract : Measurable retractCoordinate := continuous_projIcc.measurable
  have hreal : ((fun v : LatentState n ↦ v i) ∘ compactCubeInclude n) =
      coeCoordinate ∘ compactCoordinate := rfl
  have hback : compactCoordinate = retractCoordinate ∘
      ((fun v : LatentState n ↦ v i) ∘ compactCubeInclude n) := by
    funext x
    apply Subtype.ext
    exact congrArg Subtype.val
      (Set.projIcc_of_mem (show (0 : ℝ) ≤ 1 by norm_num) (x i).property).symm
  apply le_antisymm
  · rw [hreal]
    change MeasurableSpace.comap (coeCoordinate ∘ compactCoordinate) inferInstance ≤
      MeasurableSpace.comap compactCoordinate inferInstance
    simpa only [MeasurableSpace.comap_comp] using
      MeasurableSpace.comap_mono hcoe.comap_le
  · change MeasurableSpace.comap compactCoordinate inferInstance ≤
      MeasurableSpace.comap
        ((fun v : LatentState n ↦ v i) ∘ compactCubeInclude n) inferInstance
    rw [hback]
    simpa only [MeasurableSpace.comap_comp] using
      MeasurableSpace.comap_mono hretract.comap_le

/-- The real-coordinate presentation on the compact cube is equivalent to the native
subtype-coordinate presentation of a compact positive factorization.  [the stated conclusion](goal) follows. -/
lemma compactRealCondIndep_iff
    {n : ℕ} {G : DAG (Fin n)}
    {mu : Fin n → Measure (Set.Icc (0 : ℝ) 1)} [∀ k, SigmaFinite (mu k)]
    (M : UniformlyPositiveContinuousFactorization G
      (fun _ : Fin n ↦ Set.Icc (0 : ℝ) 1) mu)
    (i j : Fin n) (C : Finset (Fin n)) :
    CondIndepFun
        (MeasurableSpace.comap
          ((coordinateProjection C) ∘ compactCubeInclude n) inferInstance)
        ((measurable_paperCoordinateProjection C).comp
          (measurable_compactCubeInclude n)).comap_le
        ((fun v : LatentState n ↦ v i) ∘ compactCubeInclude n)
        ((fun v : LatentState n ↦ v j) ∘ compactCubeInclude n)
        M.observationalMeasure ↔
      M.CondIndepCoordinates i j C := by
  unfold UniformlyPositiveContinuousFactorization.CondIndepCoordinates
  rw [ProbabilityTheory.condIndepFun_iff_condIndep,
    ProbabilityTheory.condIndepFun_iff_condIndep]
  have hZ := comap_compact_realProjection_eq n C
  have hX := comap_compact_realCoordinate_eq n i
  have hY := comap_compact_realCoordinate_eq n j
  simpa only [hZ, hX, hY]

/-- If a compact positive factorization's observational measure includes to the paper's
ambient observational law, then the two singleton-coordinate conditional-independence
encodings are equivalent.  Given [the stated inputs and conditions](hyp:hobs), [the stated conclusion](goal) follows. -/
lemma condIndepCoordinates_iff_compactPositiveFactorization
    {n : ℕ} {G : DAG (Fin n)} {s : SignVector n}
    {mu : Fin n → Measure (Set.Icc (0 : ℝ) 1)} [∀ k, SigmaFinite (mu k)]
    (theta : StratumPoint G s)
    (M : UniformlyPositiveContinuousFactorization G
      (fun _ : Fin n ↦ Set.Icc (0 : ℝ) 1)
      mu)
    (hobs : Measure.map (compactCubeInclude n) M.observationalMeasure =
      observationalLaw theta.1)
    (i j : Fin n) (C : Finset (Fin n)) :
    CondIndepCoordinates theta.1 {i} {j} C ↔ M.CondIndepCoordinates i j C := by
  letI : IsFiniteMeasure (observationalLaw theta.1) := by
    rw [← hobs]
    infer_instance
  have hmapRetract : Measure.map (compactCubeRetract n) (observationalLaw theta.1) =
      M.observationalMeasure := by
    rw [← hobs]
    exact map_compactCubeRetract_map_compactCubeInclude M.observationalMeasure
  have hcompact := condIndepFun_comp_aeEquiv_iff
    (compactCubeInclude n) (compactCubeRetract n)
    (measurable_compactCubeInclude n) (measurable_compactCubeRetract n)
    hobs hmapRetract
    (compactCubeInclude_retract_ae_observationalLaw theta.1)
    (fun v : LatentState n ↦ v i) (fun v : LatentState n ↦ v j)
    (coordinateProjection C)
    (measurable_pi_apply i) (measurable_pi_apply j)
    (measurable_paperCoordinateProjection C)
  rw [condIndepCoordinates_singletons_iff_condIndepGiven i j C]
  constructor
  · rintro ⟨_, _, _, _, hambient⟩
    exact (compactRealCondIndep_iff M i j C).mp (hcompact.mpr hambient)
  · intro hM
    have hreal := (compactRealCondIndep_iff M i j C).mpr hM
    refine ⟨inferInstance, measurable_pi_apply i, measurable_pi_apply j,
      measurable_paperCoordinateProjection C, ?_⟩
    exact hcompact.mp hreal

/-- The paper and compact-factorization singleton conditional-independence encodings agree for
an arbitrary mechanism whenever their observational measures agree.  Given [the stated inputs and conditions](hyp:hobs), [the stated conclusion](goal) follows. -/
lemma condIndepCoordinates_iff_compactPositiveFactorization_mechanism
    {n : ℕ} {G : DAG (Fin n)}
    {mu : Fin n → Measure (Set.Icc (0 : ℝ) 1)} [∀ k, SigmaFinite (mu k)]
    (theta : Mechanism n G)
    (M : UniformlyPositiveContinuousFactorization G
      (fun _ : Fin n ↦ Set.Icc (0 : ℝ) 1) mu)
    (hobs : Measure.map (compactCubeInclude n) M.observationalMeasure =
      observationalLaw theta)
    (i j : Fin n) (C : Finset (Fin n)) :
    CondIndepCoordinates theta {i} {j} C ↔ M.CondIndepCoordinates i j C := by
  letI : IsFiniteMeasure (observationalLaw theta) := by
    rw [← hobs]
    infer_instance
  have hmapRetract : Measure.map (compactCubeRetract n) (observationalLaw theta) =
      M.observationalMeasure := by
    rw [← hobs]
    exact map_compactCubeRetract_map_compactCubeInclude M.observationalMeasure
  have hcompact := condIndepFun_comp_aeEquiv_iff
    (compactCubeInclude n) (compactCubeRetract n)
    (measurable_compactCubeInclude n) (measurable_compactCubeRetract n)
    hobs hmapRetract
    (compactCubeInclude_retract_ae_observationalLaw theta)
    (fun v : LatentState n ↦ v i) (fun v : LatentState n ↦ v j)
    (coordinateProjection C)
    (measurable_pi_apply i) (measurable_pi_apply j)
    (measurable_paperCoordinateProjection C)
  rw [condIndepCoordinates_singletons_iff_condIndepGiven i j C]
  constructor
  · rintro ⟨_, _, _, _, hambient⟩
    exact (compactRealCondIndep_iff M i j C).mp (hcompact.mpr hambient)
  · intro hM
    have hreal := (compactRealCondIndep_iff M i j C).mpr hM
    refine ⟨inferInstance, measurable_pi_apply i, measurable_pi_apply j,
      measurable_paperCoordinateProjection C, ?_⟩
    exact hcompact.mp hreal

/-- A positive normalized smooth paper mechanism restricts to a compact positive
factorization on the product of unit-interval coordinate subtypes. -/
def mechanismCompactPositiveFactorization
    {n : ℕ} {G : DAG (Fin n)} {theta : Mechanism n G}
    (hpos : PositiveNormalizedSmoothMechanisms G theta) :
    UniformlyPositiveContinuousFactorization G
      (fun _ : Fin n ↦ Set.Icc (0 : ℝ) 1)
      (fun _ : Fin n ↦ (volume : Measure (Set.Icc (0 : ℝ) 1))) := by
  let B := mechanismUnitCubeFactorization hpos
  have hcube (x : (k : Fin n) → Set.Icc (0 : ℝ) 1) :
      compactCubeInclude n x ∈ latentCube n := fun k _ ↦ (x k).property
  have hfactor (i : Fin n) (x : (k : Fin n) → Set.Icc (0 : ℝ) 1) :
      B.factor i (compactCubeInclude n x) =
        ENNReal.ofReal (theta.p i (compactCubeInclude n x)) := by
    simpa only [B, mechanismUnitCubeFactorization, latentCube] using
      unitCubeFactorizationOfRealCubeFactors_factor_eq theta.p
        (measurableOnSet_of_continuousOn_cube theta.p
          (fun k => (hpos.2.2.1 k).continuousOn))
        (fun k v hv => (hpos.1 k v hv).le)
        (fun k v w _ _ hvw => theta.parent_local k v w
          (hvw k (Finset.mem_insert_self _ _))
          (fun l hl => hvw l (Finset.mem_insert_of_mem hl)))
        hpos.2.2.2.2.1 i (hcube x)
  have hlower_exists : ∃ lower > 0, ∀ z ∈ Set.univ ×ˢ latentCube n,
      lower ≤ theta.p z.1 z.2 :=
    (isCompact_univ.prod (by
      rw [latentCube]
      exact isCompact_univ_pi fun _ => isCompact_Icc)).exists_forall_le'
      (by
        rw [continuousOn_prod_of_discrete_left]
        intro i
        simpa only [Set.mem_prod, Set.mem_univ, true_and, Set.ofPred_mem_eq] using
          (hpos.2.2.1 i).continuousOn)
      (fun z hz => hpos.1 z.1 z.2 hz.2)
  let lower := Classical.choose hlower_exists
  have hlower_spec := Classical.choose_spec hlower_exists
  have hlower : 0 < lower := hlower_spec.1
  have hlower_le : ∀ z ∈ Set.univ ×ˢ latentCube n,
      lower ≤ theta.p z.1 z.2 := hlower_spec.2
  refine
    { toFactorization :=
        { factor := fun i x ↦ B.factor i (compactCubeInclude n x)
          measurable_factor := fun i ↦
            (B.measurable_factor i).comp (measurable_compactCubeInclude n)
          local_factor := ?_
          normalized_factor := ?_ }
      lower := lower
      lower_pos := hlower
      factor_ne_top := ?_
      factor_continuous := ?_
      lower_le_factor := ?_ }
  · intro i x y hxy
    apply B.local_factor i
    intro k hk
    exact congrArg Subtype.val (hxy k hk)
  · intro i x
    have hfun : (fun z : Set.Icc (0 : ℝ) 1 ↦
        B.factor i (compactCubeInclude n (Function.update x i z))) =
        (fun z : ℝ ↦ B.factor i
          (Function.update (compactCubeInclude n x) i z)) ∘ Subtype.val := by
      funext z
      congr 2
      funext k
      by_cases hki : k = i
      · subst k
        simp [compactCubeInclude]
      · simp [Function.update, hki, compactCubeInclude]
    have hf : Measurable (fun z : ℝ ↦ B.factor i
        (Function.update (compactCubeInclude n x) i z)) :=
      (B.measurable_factor i).comp (measurable_update (compactCubeInclude n x))
    rw [hfun, unitInterval.volume_def]
    let f : ℝ → ℝ≥0∞ := fun z ↦
      B.factor i (Function.update (compactCubeInclude n x) i z)
    have he : MeasurePreserving
        (Subtype.val : Set.Icc (0 : ℝ) 1 → ℝ)
        (Measure.comap Subtype.val volume)
        (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
      measurePreserving_subtype_coe measurableSet_Icc
    calc
      (∫⁻ z : Set.Icc (0 : ℝ) 1, f z ∂Measure.comap Subtype.val volume) =
          ∫⁻ z : ℝ, f z ∂volume.restrict (Set.Icc (0 : ℝ) 1) :=
        he.lintegral_comp hf
      _ = 1 := B.normalized_factor i (compactCubeInclude n x)
  · intro i x
    rw [hfactor]
    exact ENNReal.ofReal_ne_top
  · intro i
    have hinclude : Continuous (compactCubeInclude n) := by
      exact continuous_pi fun k ↦ continuous_subtype_val.comp (continuous_apply k)
    have hmaps : MapsTo (compactCubeInclude n)
        Set.univ (latentCube n) := fun x _ ↦ hcube x
    have hcont : Continuous (fun x => theta.p i (compactCubeInclude n x)) :=
      (hpos.2.2.1 i).continuousOn.comp_continuous hinclude (fun x => hcube x)
    convert hcont using 1
    funext x
    rw [hfactor, ENNReal.toReal_ofReal (hpos.1 i _ (hcube x)).le]
  · intro i x
    rw [hfactor, ENNReal.toReal_ofReal (hpos.1 i _ (hcube x)).le]
    exact hlower_le (i, compactCubeInclude n x) ⟨Set.mem_univ i, hcube x⟩

/-- The compact factorization's local factor is the paper mechanism factor evaluated at the
included compact assignment.  Given [the stated inputs and conditions](hyp:hpos), [the stated conclusion](goal) follows. -/
lemma mechanismCompactPositiveFactorization_factor_eq
    {n : ℕ} {G : DAG (Fin n)} {theta : Mechanism n G}
    (hpos : PositiveNormalizedSmoothMechanisms G theta)
    (i : Fin n) (x : (k : Fin n) → Set.Icc (0 : ℝ) 1) :
    (mechanismCompactPositiveFactorization hpos).toFactorization.factor i x =
      ENNReal.ofReal (theta.p i (compactCubeInclude n x)) := by
  change (mechanismUnitCubeFactorization hpos).factor i (compactCubeInclude n x) = _
  change (mechanismUnitCubeFactorization hpos).factor i (fun k => (x k : ℝ)) =
    ENNReal.ofReal (theta.p i (fun k => (x k : ℝ)))
  simpa only [mechanismUnitCubeFactorization, latentCube] using
    unitCubeFactorizationOfRealCubeFactors_factor_eq theta.p
      (measurableOnSet_of_continuousOn_cube theta.p
        (fun k => (hpos.2.2.1 k).continuousOn))
      (fun k v hv => (hpos.1 k v hv).le)
      (fun k v w _ _ hvw => theta.parent_local k v w
        (hvw k (Finset.mem_insert_self _ _))
        (fun l hl => hvw l (Finset.mem_insert_of_mem hl)))
      hpos.2.2.2.2.1 i (fun k _ => (x k).property)

/-- Uniform closeness of paper observational factors implies `FactorSupClose` for their compact
positive factorizations.  Given [the stated inputs and conditions](hyp:hθ,hη,hclose), [the stated conclusion](goal) follows. -/
lemma mechanismCompact_factorSupClose_of_p_close
    {n : ℕ} {G : DAG (Fin n)} {theta eta : Mechanism n G}
    (hθ : PositiveNormalizedSmoothMechanisms G theta)
    (hη : PositiveNormalizedSmoothMechanisms G eta) {ε : ℝ}
    (hclose : ∀ i v, v ∈ latentCube n → |eta.p i v - theta.p i v| < ε) :
    (mechanismCompactPositiveFactorization hθ).FactorSupClose
      (mechanismCompactPositiveFactorization hη) ε := by
  intro i x
  have hx : compactCubeInclude n x ∈ latentCube n := fun k _ => (x k).property
  change
    |((mechanismCompactPositiveFactorization hη).toFactorization.factor i x).toReal -
      ((mechanismCompactPositiveFactorization hθ).toFactorization.factor i x).toReal| < ε
  rw [mechanismCompactPositiveFactorization_factor_eq,
    mechanismCompactPositiveFactorization_factor_eq,
    ENNReal.toReal_ofReal (hη.1 i _ hx).le,
    ENNReal.toReal_ofReal (hθ.1 i _ hx).le]
  exact hclose i _ hx

/-- Including the compact factorization's observational measure into the ambient latent
space recovers the paper's cube-supported observational law.  Given [the stated inputs and conditions](hyp:hpos), [the stated conclusion](goal) follows. -/
lemma mechanismCompactPositiveFactorization_observationalMeasure
    {n : ℕ} {G : DAG (Fin n)} {theta : Mechanism n G}
    (hpos : PositiveNormalizedSmoothMechanisms G theta) :
    Measure.map (compactCubeInclude n)
        (mechanismCompactPositiveFactorization hpos).observationalMeasure =
      observationalLaw theta := by
  let M := mechanismCompactPositiveFactorization hpos
  let e := compactCubeEquiv n
  let d : {v : LatentState n // v ∈ latentCube n} → ℝ≥0∞ :=
    fun v => ENNReal.ofReal (observationalDensity theta v.1)
  have hdensity : M.toFactorization.observationalDensity = d ∘ e := by
    funext x
    unfold Causalean.Graph.FiniteDensity.Factorization.observationalDensity
      Causalean.Graph.FiniteDensity.Factorization.partialDensity
    change (∏ i, (mechanismCompactPositiveFactorization hpos).toFactorization.factor i x) =
      ENNReal.ofReal (∏ i, theta.p i (compactCubeInclude n x))
    simp_rw [mechanismCompactPositiveFactorization_factor_eq hpos]
    rw [← ENNReal.ofReal_prod_of_nonneg]
    intro i hi
    exact (hpos.1 i (compactCubeInclude n x) (fun k _ => (x k).property)).le
  have heWeighted : Measure.map e M.observationalMeasure =
      (volume : Measure {v : LatentState n // v ∈ latentCube n}).withDensity d := by
    unfold UniformlyPositiveContinuousFactorization.observationalMeasure
      Causalean.Graph.FiniteDensity.Factorization.observationalMeasure
    rw [hdensity]
    exact map_withDensity_comp_measurableEquiv e
        (compactCubeEquiv_measurePreserving n) d
  have hcube : MeasurableSet (latentCube n) := by
    rw [latentCube]
    exact MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hcoe : MeasurePreserving
      (Subtype.val : {v : LatentState n // v ∈ latentCube n} → LatentState n)
      volume (volume.restrict (latentCube n)) :=
    measurePreserving_subtype_coe hcube
  have hcoeWeighted : Measure.map
      (Subtype.val : {v : LatentState n // v ∈ latentCube n} → LatentState n)
      ((volume : Measure {v : LatentState n // v ∈ latentCube n}).withDensity d) =
      observationalLaw theta := by
    ext s hs
    rw [Measure.map_apply measurable_subtype_coe hs,
      withDensity_apply _ (measurable_subtype_coe hs)]
    unfold observationalLaw
    rw [withDensity_apply _ hs]
    exact hcoe.setLIntegral_comp_preimage_emb
      (MeasurableEmbedding.subtype_coe hcube)
      (fun v => ENNReal.ofReal (observationalDensity theta v)) s
  rw [← heWeighted] at hcoeWeighted
  rw [Measure.map_map measurable_subtype_coe e.measurable] at hcoeWeighted
  exact hcoeWeighted

/-- For a positive smooth mechanism, the paper's singleton-block conditional independence is
exactly the compact positive factorization's coordinate conditional independence.  [the stated conclusion](goal) follows. -/
lemma condIndepCoordinates_iff_mechanismCompactPositiveFactorization
    {n : ℕ} {G : DAG (Fin n)} {s : SignVector n}
    (theta : StratumPoint G s) (i j : Fin n) (C : Finset (Fin n)) :
    CondIndepCoordinates theta.1 {i} {j} C ↔
      UniformlyPositiveContinuousFactorization.CondIndepCoordinates
        (mechanismCompactPositiveFactorization theta.property.positiveSmooth) i j C := by
  exact condIndepCoordinates_iff_compactPositiveFactorization theta
    (mechanismCompactPositiveFactorization theta.property.positiveSmooth)
    (mechanismCompactPositiveFactorization_observationalMeasure
      theta.property.positiveSmooth) i j C

/-- Every paper stratum point has one uniform compact-factor neighborhood in which causal
minimality persists on all directed edges.  [the stated conclusion](goal) follows. -/
lemma mechanismCompact_all_edge_witnesses_open
    {n : ℕ} {G : DAG (Fin n)} {s : SignVector n}
    (theta : StratumPoint G s) :
    let M := mechanismCompactPositiveFactorization theta.property.positiveSmooth
    ∃ ε > 0, ∀ N : UniformlyPositiveContinuousFactorization G
        (fun _ : Fin n ↦ Set.Icc (0 : ℝ) 1)
        (fun _ : Fin n ↦ (volume : Measure (Set.Icc (0 : ℝ) 1))),
      M.FactorSupClose N ε →
      ∀ i j (hji : G.edge j i),
        ¬ N.CondIndepCoordinates i j ((G.parents i).erase j) := by
  classical
  dsimp only
  let M := mechanismCompactPositiveFactorization theta.property.positiveSmooth
  have hwitness : ∀ i j, G.edge j i → Nonempty (M.EdgeWitness i j) := by
    intro i j hji
    have hnot : ¬ M.CondIndepCoordinates i j ((G.parents i).erase j) := by
      rw [← condIndepCoordinates_iff_mechanismCompactPositiveFactorization theta]
      exact theta.property.causalMinimal hji
    have hnotAll : ¬ ∀ (x : ∀ k : Fin n, Set.Icc (0 : ℝ) 1)
        (xi xi' : Set.Icc (0 : ℝ) 1) (xj xj' : Set.Icc (0 : ℝ) 1),
        M.localContrast i j x xi xi' xj xj' = 0 := by
      exact fun hall => hnot ((M.edge_condIndep_iff_localContrast_zero hji).mpr hall)
    push_neg at hnotAll
    rcases hnotAll with ⟨x, xi, xi', xj, xj', hne⟩
    exact ⟨
      { base := x
        child₀ := xi
        child₁ := xi'
        parent₀ := xj
        parent₁ := xj'
        nonzero := hne }⟩
  exact M.all_edge_witnesses_open fun i j hji => Classical.choice (hwitness i j hji)

end CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity
