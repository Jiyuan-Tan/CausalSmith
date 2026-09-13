import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.DecoderGraph
import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.FiniteDensityBridge
import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.DecoderTriangularInverse
import Causalean.Graph.FiniteDensity.Elimination

/-!
# Intervention marginal density for the decoder

This file supplies the factor-elimination identity underlying equation (10): when a
parent-closed retained set contains the intervention target, its marginal density is the
replacement density times the product of the remaining retained observational factors.
It also constructs the equation-(11) Markov kernel on the compact predecessor cube and
transports it through the triangular predecessor-score homeomorphism.
-/

open scoped ENNReal
open MeasureTheory ProbabilityTheory Set

noncomputable section

namespace CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

open Causalean.Graph.FiniteDensity

-- @node: interventionMarginalDensity_eq_replacement_mul_partialDensity
/-- Eliminating all coordinates outside a parent-closed set containing the intervention target
leaves the intervention density times the observational factors at the other retained nodes.  Given [the stated inputs and conditions](hyp:hA,hj), [the stated conclusion](goal) follows. -/
lemma interventionMarginalDensity_eq_replacement_mul_partialDensity
    {V : Type*} [DecidableEq V] [Fintype V]
    {X : V → Type*} [∀ i, MeasurableSpace (X i)]
    {μ : ∀ i, Measure (X i)} [∀ i, SigmaFinite (μ i)]
    {G : Causalean.DAG V} (B : Factorization G X μ)
    {A : Finset V} (hA : ParentClosed G A) {j : V} (hj : j ∈ A)
    (q : InterventionDensity j X μ) :
    (∫⋯∫⁻_(Finset.univ \ A), B.interventionDensity j q ∂μ) =
      fun v => q.density (v j) * B.partialDensity (A.erase j) v := by
  rw [← B.observationalDensity_intervene]
  rw [(B.intervene j q).lmarginal_compl_observationalDensity_eq hA]
  funext v
  unfold Factorization.partialDensity Factorization.intervene
  rw [← Finset.prod_erase_mul _ _ hj]
  have hprod :
      (∏ i ∈ A.erase j,
        if i = j then q.density (v j) else B.factor i v) =
        ∏ i ∈ A.erase j, B.factor i v := by
    apply Finset.prod_congr rfl
    intro i hi
    have hij : i ≠ j := (Finset.mem_erase.mp hi).1
    simp [hij]
  rw [hprod]
  simp only [if_pos]
  exact mul_comm _ _

-- @node: decoderRetainedLatentSet
/-- The latent-coordinate image of a decoder predecessor set, together with the current
intervention target. -/
def decoderRetainedLatentSet
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (order : Fin n → ℕ) (i : Fin n) : Finset (Fin n) :=
  insert (W.targetPerm i) ((predecessorSet order i).map W.targetPerm.toEmbedding)

-- @node: decoderRetainedLatentSet_parentClosed
/-- If the selected order respects the recovered ancestral order, the target and its decoder
predecessors form a parent-closed latent set.  Given [the stated inputs and conditions](hyp:horder,hgraphOrder), [the stated conclusion](goal) follows. -/
lemma decoderRetainedLatentSet_parentClosed
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) {order : Fin n → ℕ}
    (horder : IsTopologicalOrdering (observedLawRatioGraph gaussianFeatureMap W.law) order)
    (hgraphOrder : PermutedGraphOrdered W order) (i : Fin n) :
    ParentClosed G (decoderRetainedLatentSet W order i) := by
  intro k hk a ha
  rw [decoderRetainedLatentSet, Finset.mem_insert] at hk ⊢
  rcases hk with rfl | hk
  · right
    refine Finset.mem_map.mpr ⟨W.targetPerm.symm a, ?_, ?_⟩
    · apply environmentParentSet_subset_predecessorSet_of_transitiveClosure W horder hgraphOrder i
      simpa only [environmentParentSet, Finset.mem_filter, Finset.mem_univ, true_and,
        Equiv.apply_symm_apply] using G.mem_parents.mp ha
    · simp
  · right
    rcases Finset.mem_map.mp hk with ⟨b, hb, rfl⟩
    refine Finset.mem_map.mpr ⟨W.targetPerm.symm a, ?_, ?_⟩
    · have hab : W.targetPerm.symm a ∈ predecessorSet order b := by
        apply environmentParentSet_subset_predecessorSet_of_transitiveClosure W horder hgraphOrder b
        have hedge : G.edge a (W.targetPerm b) := by
          simpa using G.mem_parents.mp ha
        simpa only [environmentParentSet, Finset.mem_filter, Finset.mem_univ, true_and,
          Equiv.apply_symm_apply] using hedge
      simp only [predecessorSet, Finset.mem_filter, Finset.mem_univ, true_and] at hab hb ⊢
      exact hab.trans hb
    · simp

-- @node: equationTen_predecessorDensity_update_target
/-- The predecessor-factor part of equation (10) is constant along the current target's
own-coordinate fiber.  Given [the stated inputs and conditions](hyp:hpos,horder,hgraphOrder), [the stated conclusion](goal) follows. -/
lemma equationTen_predecessorDensity_update_target
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (hpos : PositiveNormalizedSmoothMechanisms G θ)
    {order : Fin n → ℕ}
    (horder : IsTopologicalOrdering (observedLawRatioGraph gaussianFeatureMap W.law) order)
    (hgraphOrder : PermutedGraphOrdered W order) (i : Fin n)
    (v : LatentState n) (w : ℝ) :
    let B := mechanismUnitCubeFactorization hpos
    let A := decoderRetainedLatentSet W order i
    B.partialDensity (A.erase (W.targetPerm i))
        (Function.update v (W.targetPerm i) w) =
      B.partialDensity (A.erase (W.targetPerm i)) v := by
  dsimp only
  unfold Causalean.Graph.FiniteDensity.Factorization.partialDensity
  apply Finset.prod_congr rfl
  intro k hk
  apply (mechanismUnitCubeFactorization hpos).local_factor k
  intro a ha
  have hatarget : a ≠ W.targetPerm i := by
    intro hEq
    subst a
    rcases Finset.mem_insert.mp ha with hki | hparent
    · exact (Finset.mem_erase.mp hk).1 hki.symm
    · have hkA := (Finset.mem_erase.mp hk).2
      rw [decoderRetainedLatentSet, Finset.mem_insert] at hkA
      rcases hkA with hkTarget | hkPred
      · exact (Finset.mem_erase.mp hk).1 hkTarget
      · rcases Finset.mem_map.mp hkPred with ⟨b, hb, hkb⟩
        subst k
        exact target_not_parent_of_mem_predecessorSet W horder hgraphOrder hb hparent
  simp [Function.update, hatarget]

-- @node: equationTen_interventionMarginalDensity
/-- Equation (10) at the density-elimination level: under the current intervention, retaining
the target and all predecessor coordinates leaves the replacement density times the remaining
retained observational factors.  Given [the stated inputs and conditions](hyp:hpos,horder,hgraphOrder), [the stated conclusion](goal) follows. -/
lemma equationTen_interventionMarginalDensity
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (hpos : PositiveNormalizedSmoothMechanisms G θ)
    {order : Fin n → ℕ}
    (horder : IsTopologicalOrdering (observedLawRatioGraph gaussianFeatureMap W.law) order)
    (hgraphOrder : PermutedGraphOrdered W order) (i : Fin n) :
    let B := mechanismUnitCubeFactorization hpos
    let q := mechanismInterventionDensity W hpos i
    let A := decoderRetainedLatentSet W order i
    (∫⋯∫⁻_(Finset.univ \ A), B.interventionDensity (W.targetPerm i) q
        ∂fun _ : Fin n => Causalean.Graph.FiniteDensity.unitIntervalReference) =
      fun v => q.density (v (W.targetPerm i)) * B.partialDensity (A.erase (W.targetPerm i)) v := by
  dsimp only
  have hσ : ∀ _ : Fin n,
      SigmaFinite Causalean.Graph.FiniteDensity.unitIntervalReference := fun _ => by
    unfold Causalean.Graph.FiniteDensity.unitIntervalReference
    infer_instance
  exact @interventionMarginalDensity_eq_replacement_mul_partialDensity
    (Fin n) _ _ (fun _ : Fin n => ℝ) (fun _ : Fin n => inferInstance)
    (fun _ : Fin n => Causalean.Graph.FiniteDensity.unitIntervalReference) hσ G
    (mechanismUnitCubeFactorization hpos) (decoderRetainedLatentSet W order i)
    (decoderRetainedLatentSet_parentClosed W horder hgraphOrder i) (W.targetPerm i)
    (by simp [decoderRetainedLatentSet]) (mechanismInterventionDensity W hpos i)

-- @node: equationTen_interventionMarginalDensity_fiber_product
/-- Equation (10) in explicit fiber-product form: after fixing predecessor coordinates,
the retained intervention density is the own-coordinate replacement density times a factor
that is constant along that coordinate's fiber.  Given [the stated inputs and conditions](hyp:hpos,horder,hgraphOrder), [the stated conclusion](goal) follows. -/
lemma equationTen_interventionMarginalDensity_fiber_product
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (hpos : PositiveNormalizedSmoothMechanisms G θ)
    {order : Fin n → ℕ}
    (horder : IsTopologicalOrdering (observedLawRatioGraph gaussianFeatureMap W.law) order)
    (hgraphOrder : PermutedGraphOrdered W order) (i : Fin n)
    (v : LatentState n) (w : ℝ) :
    let B := mechanismUnitCubeFactorization hpos
    let q := mechanismInterventionDensity W hpos i
    let A := decoderRetainedLatentSet W order i
    (∫⋯∫⁻_(Finset.univ \ A),
        B.interventionDensity (W.targetPerm i) q
        ∂fun _ : Fin n => Causalean.Graph.FiniteDensity.unitIntervalReference)
        (Function.update v (W.targetPerm i) w) =
      q.density w * B.partialDensity (A.erase (W.targetPerm i)) v := by
  dsimp only
  have hten := congrFun
    (equationTen_interventionMarginalDensity W hpos horder hgraphOrder i)
    (Function.update v (W.targetPerm i) w)
  rw [equationTen_predecessorDensity_update_target W hpos horder hgraphOrder i v w] at hten
  simpa using hten

-- @node: decoderInterventionCoordinateMeasure
/-- The normalized replacement density, viewed as a probability measure on the target's
scalar coordinate. -/
def decoderInterventionCoordinateMeasure
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (i : Fin n) : Measure ℝ :=
  Causalean.Graph.FiniteDensity.unitIntervalReference.withDensity
    (mechanismInterventionDensity W hpos i).density

-- @node: decoderInterventionCoordinateMeasure_isProbability
/-- Normalization of the replacement density makes its coordinate measure a probability
measure. -/
instance decoderInterventionCoordinateMeasure_isProbability
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (i : Fin n) : IsProbabilityMeasure (decoderInterventionCoordinateMeasure W hpos i) := by
  constructor
  rw [decoderInterventionCoordinateMeasure, withDensity_apply _ MeasurableSet.univ]
  simpa only [Measure.restrict_univ] using
    (mechanismInterventionDensity W hpos i).normalized_density

-- @node: equationElevenClampedScore
/-- A globally measurable clamped extension of the target log-ratio score along a predecessor
fiber.  On the unit interval it is the score appearing in equation (11). -/
def equationElevenClampedScore
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (order : Fin n → ℕ) (i : Fin n)
    (zw : PredecessorLatentCube order i × ℝ) : ℝ :=
  let w := max 0 (min 1 zw.2)
  let v := predecessorCubeLatentState W order i zw.1
  Real.log (θ.q (W.targetPerm i) w /
    θ.p (W.targetPerm i) (Function.update v (W.targetPerm i) w))

-- @node: measurable_equationElevenClampedScore
/-- Smoothness on the compact cube makes the clamped equation-(11) score jointly measurable
in predecessor coordinates and the target coordinate.  Given [the stated inputs and conditions](hyp:hpos), [the stated conclusion](goal) follows. -/
@[fun_prop]
lemma measurable_equationElevenClampedScore
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (order : Fin n → ℕ) (i : Fin n) : Measurable (equationElevenClampedScore W order i) := by
  have hw : Continuous (fun zw : PredecessorLatentCube order i × ℝ =>
      max 0 (min 1 zw.2)) := by fun_prop
  have hwmem : ∀ zw : PredecessorLatentCube order i × ℝ,
      max 0 (min 1 zw.2) ∈ Set.Icc (0 : ℝ) 1 := by
    intro zw
    exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hbase : Continuous (predecessorCubeLatentState W order i) := by
    apply continuous_pi
    intro a
    simp only [predecessorCubeLatentState]
    split <;> fun_prop
  have hv : Continuous (fun zw : PredecessorLatentCube order i × ℝ =>
      Function.update (predecessorCubeLatentState W order i zw.1)
        (W.targetPerm i) (max 0 (min 1 zw.2))) := by
    apply continuous_pi
    intro k
    by_cases hki : k = W.targetPerm i
    · subst k
      simpa using hw
    · have heq : (fun a : PredecessorLatentCube order i × ℝ =>
          Function.update (predecessorCubeLatentState W order i a.1)
              (W.targetPerm i) (max 0 (min 1 a.2)) k) =
          fun a => predecessorCubeLatentState W order i a.1 k := by
        funext a
        simp [Function.update, hki]
      rw [heq]
      exact (continuous_apply k).comp (hbase.comp continuous_fst)
  have hvmem : ∀ zw : PredecessorLatentCube order i × ℝ,
      Function.update (predecessorCubeLatentState W order i zw.1)
        (W.targetPerm i) (max 0 (min 1 zw.2)) ∈ latentCube n := by
    intro zw k hk
    by_cases hki : k = W.targetPerm i
    · subst k
      simpa using hwmem zw
    · simp [Function.update, hki]
      exact predecessorCubeLatentState_mem_latentCube W order i zw.1 k (Set.mem_univ k)
  have hq := (hpos.2.2.2.1 (W.targetPerm i)).continuousOn.comp_continuous hw hwmem
  have hp := (hpos.2.2.1 (W.targetPerm i)).continuousOn.comp_continuous hv hvmem
  have hpne : ∀ zw : PredecessorLatentCube order i × ℝ, θ.p (W.targetPerm i)
      (Function.update (predecessorCubeLatentState W order i zw.1)
        (W.targetPerm i) (max 0 (min 1 zw.2))) ≠ 0 := fun zw =>
    ne_of_gt (hpos.1 _ _ (hvmem zw))
  have hqne : ∀ zw : PredecessorLatentCube order i × ℝ,
      θ.q (W.targetPerm i) (max 0 (min 1 zw.2)) ≠ 0 := fun zw =>
    ne_of_gt (hpos.2.1 _ _ (hwmem zw))
  exact (hq.div hp hpne |>.log (fun zw => div_ne_zero (hqne zw) (hpne zw))).measurable

-- @node: equationElevenPredecessorKernel
/-- The equation-(11) Markov kernel on predecessor latent coordinates: draw the target from
its replacement density and push it through the target log-ratio score. -/
def equationElevenPredecessorKernel
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (order : Fin n → ℕ) (i : Fin n) : Kernel (PredecessorLatentCube order i) ℝ :=
  (((Kernel.id : Kernel (PredecessorLatentCube order i) _) ∥ₖ
      Kernel.const Unit (decoderInterventionCoordinateMeasure W hpos i)).comap
      (fun z => (z, ())) (by fun_prop)).map (equationElevenClampedScore W order i)

-- @node: equationElevenPredecessorKernel_isMarkov
/-- The equation-(11) predecessor kernel has unit mass on every predecessor fiber. -/
instance equationElevenPredecessorKernel_isMarkov
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (order : Fin n → ℕ) (i : Fin n) :
    IsMarkovKernel (equationElevenPredecessorKernel W hpos order i) := by
  unfold equationElevenPredecessorKernel
  let base : Kernel (PredecessorLatentCube order i × Unit)
      (PredecessorLatentCube order i × ℝ) :=
    Kernel.id ∥ₖ Kernel.const Unit (decoderInterventionCoordinateMeasure W hpos i)
  haveI : IsMarkovKernel base := by dsimp only [base]; infer_instance
  haveI : IsMarkovKernel (base.comap (fun z => (z, ())) (by fun_prop)) :=
    Kernel.IsMarkovKernel.comap base (by fun_prop)
  exact Kernel.IsMarkovKernel.map _ (measurable_equationElevenClampedScore W hpos order i)

-- @node: equationElevenPredecessorKernel_apply_Iic
/-- Every lower-interval probability of the predecessor kernel is exactly the explicit
equation-(11) conditional-CDF integral.  Given [the stated inputs and conditions](hyp:hpos), [the stated conclusion](goal) follows. -/
lemma equationElevenPredecessorKernel_apply_Iic
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (order : Fin n → ℕ) (i : Fin n) (z : PredecessorLatentCube order i) (t : ℝ) :
    ((equationElevenPredecessorKernel W hpos order i) z (Set.Iic t)).toReal =
      equationElevenConditionalRatioCDF θ (W.targetPerm i) t
        (predecessorCubeLatentState W order i z) := by
  rw [equationElevenPredecessorKernel,
    Kernel.map_apply' _ (measurable_equationElevenClampedScore W hpos order i) _
      measurableSet_Iic,
    Kernel.comap_apply, Kernel.parallelComp_apply, Kernel.id_apply, Kernel.const_apply]
  rw [Measure.dirac_prod]
  rw [Measure.map_apply (by fun_prop)
    (measurableSet_Iic.preimage (measurable_equationElevenClampedScore W hpos order i))]
  change ((decoderInterventionCoordinateMeasure W hpos i)
      {w | equationElevenClampedScore W order i (z, w) ≤ t}).toReal = _
  rw [decoderInterventionCoordinateMeasure]
  have hset : MeasurableSet {w | equationElevenClampedScore W order i (z, w) ≤ t} :=
    measurableSet_Iic.preimage ((measurable_equationElevenClampedScore W hpos order i).comp
      (measurable_const.prodMk measurable_id))
  rw [withDensity_apply _ hset]
  let v := predecessorCubeLatentState W order i z
  let score : ℝ → ℝ := fun w => Real.log
    (θ.q (W.targetPerm i) w /
      θ.p (W.targetPerm i) (Function.update v (W.targetPerm i) w))
  let f : ℝ → ℝ := fun w => if score w ≤ t then θ.q (W.targetPerm i) w else 0
  have hf_nonneg : 0 ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with w hw
    simp only [f]
    split
    · exact le_of_lt (hpos.2.1 _ w hw)
    · exact le_rfl
  have hf_meas : AEStronglyMeasurable f (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    have hscore : ContinuousOn score (Set.Icc (0 : ℝ) 1) := by
      dsimp only [score, v]
      have hq := (hpos.2.2.2.1 (W.targetPerm i)).continuousOn
      have hbase := predecessorCubeLatentState_mem_latentCube W order i z
      have hp : ContinuousOn (fun w => θ.p (W.targetPerm i)
          (Function.update (predecessorCubeLatentState W order i z)
            (W.targetPerm i) w)) (Set.Icc (0 : ℝ) 1) := by
        apply (hpos.2.2.1 (W.targetPerm i)).continuousOn.comp
        · fun_prop
        · intro w hw k hk
          by_cases hki : k = W.targetPerm i
          · subst k
            simpa using hw
          · simp [Function.update, hki]
            exact hbase k (Set.mem_univ k)
      have hpne : ∀ w ∈ Set.Icc (0 : ℝ) 1, θ.p (W.targetPerm i)
          (Function.update (predecessorCubeLatentState W order i z)
            (W.targetPerm i) w) ≠ 0 := fun w hw => ne_of_gt (hpos.1 _ _ (by
        intro k hk
        by_cases hki : k = W.targetPerm i
        · subst k
          simpa using hw
        · simp [Function.update, hki]
          exact hbase k (Set.mem_univ k)))
      exact (hq.div hp hpne).log (fun w hw => div_ne_zero
        (ne_of_gt (hpos.2.1 _ w hw)) (hpne w hw))
    have hqae : AEMeasurable (θ.q (W.targetPerm i))
        (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
      (hpos.2.2.2.1 (W.targetPerm i)).continuousOn.aemeasurable measurableSet_Icc
    have hscoreae : AEMeasurable score (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
      hscore.aemeasurable measurableSet_Icc
    let qm := hqae.mk
    let sm := hscoreae.mk
    have hfm : Measurable (fun w => if sm w ≤ t then qm w else 0) := by
      exact Measurable.ite (measurableSet_le hscoreae.measurable_mk measurable_const)
        hqae.measurable_mk measurable_const
    apply hfm.aestronglyMeasurable.congr
    filter_upwards [hqae.ae_eq_mk, hscoreae.ae_eq_mk] with w hqw hsw
    simp only [qm, sm, f] at hqw hsw ⊢
    rw [← hqw, ← hsw]
  rw [equationElevenConditionalRatioCDF]
  change _ = ∫ w in Set.Icc (0 : ℝ) 1, f w
  rw [integral_eq_lintegral_of_nonneg_ae hf_nonneg hf_meas]
  congr 1
  rw [← lintegral_indicator hset]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with w hw
  have hclamp : max 0 (min 1 w) = w := by
    rw [min_eq_right hw.2, max_eq_right hw.1]
  have hscoreeq : equationElevenClampedScore W order i (z, w) = score w := by
    simp only [equationElevenClampedScore, score, v, hclamp]
  simp only [Set.indicator, Set.mem_ofPred_eq, hscoreeq]
  simp only [mechanismInterventionDensity,
    Causalean.Graph.FiniteDensity.interventionDensityOfRealCube,
    Causalean.Graph.FiniteDensity.interventionDensityOfCube, hclamp]
  by_cases hs : score w ≤ t
  · simp [f, hs]
  · simp [f, hs]

-- @node: equationElevenScoreImageKernel
/-- Transporting the predecessor kernel through the compact triangular inverse gives the
equation-(11) kernel on the realized predecessor-score image. -/
def equationElevenScoreImageKernel
    {n : ℕ} {G : Causalean.DAG (Fin n)} (s : SignVector n)
    {θ : Mechanism n G} (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W)
    (hsign : FixedOwnDerivativeSign G s θ)
    {order : Fin n → ℕ}
    (horder : IsTopologicalOrdering (observedLawRatioGraph gaussianFeatureMap W.law) order)
    (hgraphOrder : PermutedGraphOrdered W order) (i : Fin n) :
    Kernel (Set.range (predecessorScoreMap W order i)) ℝ :=
  (equationElevenPredecessorKernel W hpos order i).comap
    (predecessorScoreHomeomorph s W hpos hmix hone hsign horder hgraphOrder i).symm
    (continuous_predecessorScoreInverse s W hpos hmix hone hsign horder hgraphOrder i).measurable

-- @node: equationElevenScoreImageKernel_isMarkov
/-- The score-image transport of the equation-(11) kernel remains Markov. -/
instance equationElevenScoreImageKernel_isMarkov
    {n : ℕ} {G : Causalean.DAG (Fin n)} (s : SignVector n)
    {θ : Mechanism n G} (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W)
    (hsign : FixedOwnDerivativeSign G s θ)
    {order : Fin n → ℕ}
    (horder : IsTopologicalOrdering (observedLawRatioGraph gaussianFeatureMap W.law) order)
    (hgraphOrder : PermutedGraphOrdered W order) (i : Fin n) :
    IsMarkovKernel
      (equationElevenScoreImageKernel s W hpos hmix hone hsign horder hgraphOrder i) := by
  exact Kernel.IsMarkovKernel.comap _
    (continuous_predecessorScoreInverse s W hpos hmix hone hsign horder hgraphOrder i).measurable

-- @node: equationElevenScoreImageKernel_apply_Iic
/-- On every realized predecessor score, the transported kernel's lower-interval probability
is the explicit equation-(11) integral at the reconstructed predecessor coordinates.  Given [the stated inputs and conditions](hyp:hpos,hmix,hone,hsign,horder,hgraphOrder), [the stated conclusion](goal) follows. -/
lemma equationElevenScoreImageKernel_apply_Iic
    {n : ℕ} {G : Causalean.DAG (Fin n)} (s : SignVector n)
    {θ : Mechanism n G} (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W)
    (hsign : FixedOwnDerivativeSign G s θ)
    {order : Fin n → ℕ}
    (horder : IsTopologicalOrdering (observedLawRatioGraph gaussianFeatureMap W.law) order)
    (hgraphOrder : PermutedGraphOrdered W order) (i : Fin n)
    (ell : Set.range (predecessorScoreMap W order i)) (t : ℝ) :
    ((equationElevenScoreImageKernel s W hpos hmix hone hsign horder hgraphOrder i)
        ell (Set.Iic t)).toReal =
      equationElevenConditionalRatioCDF θ (W.targetPerm i) t
        (predecessorCubeLatentState W order i
          ((predecessorScoreHomeomorph s W hpos hmix hone hsign horder hgraphOrder i).symm ell)) := by
  rw [equationElevenScoreImageKernel, Kernel.comap_apply]
  exact equationElevenPredecessorKernel_apply_Iic W hpos order i _ t

-- @node: equationElevenScoreImageKernel_apply_Iic_of_latentState
/-- At every predecessor score realized by a latent cube point, the transported Markov
kernel has exactly the equation-(11) lower-interval probability at that latent state.  Given [the stated inputs and conditions](hyp:hpos,hmix,hone,hsign,horder,hgraphOrder,hv), [the stated conclusion](goal) follows. -/
lemma equationElevenScoreImageKernel_apply_Iic_of_latentState
    {n : ℕ} {G : Causalean.DAG (Fin n)} (s : SignVector n)
    {θ : Mechanism n G} (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W)
    (hsign : FixedOwnDerivativeSign G s θ)
    {order : Fin n → ℕ}
    (horder : IsTopologicalOrdering (observedLawRatioGraph gaussianFeatureMap W.law) order)
    (hgraphOrder : PermutedGraphOrdered W order)
    (i : Fin n) (v : LatentState n) (hv : v ∈ latentCube n) (t : ℝ) :
    let ell : Set.range (predecessorScoreMap W order i) :=
      ⟨familyProjection (observedLawLogRatio W.law) (predecessorSet order i) (W.mix v),
        observedPredecessorLogRatio_mem_scoreRange W hpos hmix hone horder hgraphOrder i v hv⟩
    ((equationElevenScoreImageKernel s W hpos hmix hone hsign horder hgraphOrder i)
        ell (Set.Iic t)).toReal =
      equationElevenConditionalRatioCDF θ (W.targetPerm i) t v := by
  dsimp only
  let z := predecessorLatentCubeOfState W order i v hv
  let e := predecessorScoreHomeomorph s W hpos hmix hone hsign horder hgraphOrder i
  let ell : Set.range (predecessorScoreMap W order i) :=
    ⟨familyProjection (observedLawLogRatio W.law) (predecessorSet order i) (W.mix v),
      observedPredecessorLogRatio_mem_scoreRange W hpos hmix hone horder hgraphOrder i v hv⟩
  have hinv : e.symm ell = z := by
    apply e.injective
    rw [e.apply_symm_apply]
    apply Subtype.ext
    exact (predecessorScoreMap_of_latentState W hpos hmix hone horder hgraphOrder i v hv).symm
  rw [equationElevenScoreImageKernel_apply_Iic s W hpos hmix hone hsign horder hgraphOrder i ell t]
  apply equationElevenConditionalRatioCDF_eq_of_parents_eq θ (W.targetPerm i) t
  intro a ha
  let k := W.targetPerm.symm a
  have hkParent : k ∈ environmentParentSet W i := by
    simpa [k, environmentParentSet, Causalean.DAG.parents] using ha
  have hkPred := environmentParentSet_subset_predecessorSet_of_transitiveClosure
    W horder hgraphOrder i hkParent
  rw [hinv]
  simpa [z, k] using predecessorCubeLatentState_ofState_apply W order i v hv k hkPred

-- @node: predecessorScoreRangeRetraction
/-- A measurable retraction of the ambient predecessor-score space onto the compact realized
score image.  Off the image it uses the score of the zero predecessor vector. -/
noncomputable def predecessorScoreRangeRetraction
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (order : Fin n → ℕ) (i : Fin n)
    (ell : PredecessorLogRatios order i) :
    Set.range (predecessorScoreMap W order i) := by
  classical
  exact if h : ell ∈ Set.range (predecessorScoreMap W order i) then ⟨ell, h⟩ else
    ⟨predecessorScoreMap W order i (fun _ => ⟨0, by norm_num⟩),
      ⟨fun _ => ⟨0, by norm_num⟩, rfl⟩⟩

-- @node: measurable_predecessorScoreRangeRetraction
/-- The compact-score retraction is measurable.  Given [the stated inputs and conditions](hyp:hpos), [the stated conclusion](goal) follows. -/
@[fun_prop]
lemma measurable_predecessorScoreRangeRetraction
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (order : Fin n → ℕ) (i : Fin n) :
    Measurable (predecessorScoreRangeRetraction W order i) := by
  classical
  have hclosed : IsClosed (Set.range (predecessorScoreMap W order i)) :=
    by simpa only [Set.image_univ] using
      (isCompact_univ.image (continuous_predecessorScoreMap W hpos order i)).isClosed
  unfold predecessorScoreRangeRetraction
  apply Measurable.dite measurable_id measurable_const hclosed.measurableSet

-- @node: equationElevenAmbientKernel
/-- The equation-(11) kernel on the full predecessor-score space, obtained by a measurable
retraction to the compact realized score image.  Its off-support values are immaterial. -/
def equationElevenAmbientKernel
    {n : ℕ} {G : Causalean.DAG (Fin n)} (s : SignVector n)
    {θ : Mechanism n G} (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W)
    (hsign : FixedOwnDerivativeSign G s θ)
    {order : Fin n → ℕ}
    (horder : IsTopologicalOrdering (observedLawRatioGraph gaussianFeatureMap W.law) order)
    (hgraphOrder : PermutedGraphOrdered W order) (i : Fin n) :
    Kernel (PredecessorLogRatios order i) ℝ :=
  (equationElevenScoreImageKernel s W hpos hmix hone hsign horder hgraphOrder i).comap
    (predecessorScoreRangeRetraction W order i)
    (measurable_predecessorScoreRangeRetraction W hpos order i)

-- @node: equationElevenAmbientKernel_isMarkov
/-- The ambient extension of the equation-(11) kernel remains Markov. -/
instance equationElevenAmbientKernel_isMarkov
    {n : ℕ} {G : Causalean.DAG (Fin n)} (s : SignVector n)
    {θ : Mechanism n G} (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W)
    (hsign : FixedOwnDerivativeSign G s θ)
    {order : Fin n → ℕ}
    (horder : IsTopologicalOrdering (observedLawRatioGraph gaussianFeatureMap W.law) order)
    (hgraphOrder : PermutedGraphOrdered W order) (i : Fin n) :
    IsMarkovKernel
      (equationElevenAmbientKernel s W hpos hmix hone hsign horder hgraphOrder i) := by
  exact Kernel.IsMarkovKernel.comap _
    (measurable_predecessorScoreRangeRetraction W hpos order i)

-- @node: equationElevenAmbientKernel_apply_Iic_of_latentState
/-- On every predecessor score realized by a latent cube point, the ambient kernel evaluates
to the explicit equation-(11) conditional CDF.  Given [the stated inputs and conditions](hyp:hpos,hmix,hone,hsign,horder,hgraphOrder,hv), [the stated conclusion](goal) follows. -/
lemma equationElevenAmbientKernel_apply_Iic_of_latentState
    {n : ℕ} {G : Causalean.DAG (Fin n)} (s : SignVector n)
    {θ : Mechanism n G} (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W)
    (hsign : FixedOwnDerivativeSign G s θ)
    {order : Fin n → ℕ}
    (horder : IsTopologicalOrdering (observedLawRatioGraph gaussianFeatureMap W.law) order)
    (hgraphOrder : PermutedGraphOrdered W order)
    (i : Fin n) (v : LatentState n) (hv : v ∈ latentCube n) (t : ℝ) :
    ((equationElevenAmbientKernel s W hpos hmix hone hsign horder hgraphOrder i)
        (familyProjection (observedLawLogRatio W.law) (predecessorSet order i) (W.mix v))
        (Set.Iic t)).toReal =
      equationElevenConditionalRatioCDF θ (W.targetPerm i) t v := by
  let ell := familyProjection (observedLawLogRatio W.law) (predecessorSet order i) (W.mix v)
  have hell : ell ∈ Set.range (predecessorScoreMap W order i) :=
    observedPredecessorLogRatio_mem_scoreRange W hpos hmix hone horder hgraphOrder i v hv
  rw [equationElevenAmbientKernel, Kernel.comap_apply]
  have hretract : predecessorScoreRangeRetraction W order i ell = ⟨ell, hell⟩ := by
    simp [predecessorScoreRangeRetraction, hell]
  rw [hretract]
  exact equationElevenScoreImageKernel_apply_Iic_of_latentState
    s W hpos hmix hone hsign horder hgraphOrder i v hv t

-- @node: lmarginal_eq_self_of_update_eq
/-- Integrating out coordinates on which a measurable function is invariant leaves the
function unchanged when every coordinate reference measure has unit mass.  Given [the stated inputs and conditions](hyp:hf,hinv,μ,f), [the stated conclusion](goal) follows. -/
lemma lmarginal_eq_self_of_update_eq
    {V : Type*} [DecidableEq V]
    {X : V → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (T : Finset V) (f : (∀ i, X i) → ℝ≥0∞) (hf : Measurable f)
    (hinv : ∀ k ∈ T, ∀ x y, f (Function.update x k y) = f x) :
    (∫⋯∫⁻_T, f ∂μ) = f := by
  induction T using Finset.induction with
  | empty => simp
  | @insert k T hk ih =>
      rw [MeasureTheory.lmarginal_insert' _ hf hk]
      have hinner : (fun x => ∫⁻ y, f (Function.update x k y) ∂μ k) = f := by
        funext x
        simp_rw [hinv k (Finset.mem_insert_self k T) x]
        simp
      rw [hinner]
      exact ih (fun j hj => hinv j (Finset.mem_insert_of_mem hj))

-- @node: equationTen_retainedDensity_update_outside
/-- The factorized retained density from equation (10) is invariant under every coordinate
outside the target-plus-predecessor set.  Given [the stated inputs and conditions](hyp:hpos,horder,hgraphOrder,hk), [the stated conclusion](goal) follows. -/
lemma equationTen_retainedDensity_update_outside
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (hpos : PositiveNormalizedSmoothMechanisms G θ)
    {order : Fin n → ℕ}
    (horder : IsTopologicalOrdering (observedLawRatioGraph gaussianFeatureMap W.law) order)
    (hgraphOrder : PermutedGraphOrdered W order) (i k : Fin n)
    (hk : k ∉ decoderRetainedLatentSet W order i)
    (v : LatentState n) (x : ℝ) :
    let B := mechanismUnitCubeFactorization hpos
    let q := mechanismInterventionDensity W hpos i
    let A := decoderRetainedLatentSet W order i
    q.density ((Function.update v k x) (W.targetPerm i)) *
        B.partialDensity (A.erase (W.targetPerm i)) (Function.update v k x) =
      q.density (v (W.targetPerm i)) *
        B.partialDensity (A.erase (W.targetPerm i)) v := by
  dsimp only
  have hkt : k ≠ W.targetPerm i := by
    intro h
    subst k
    exact hk (by simp [decoderRetainedLatentSet])
  congr 1
  · simp [Function.update, hkt.symm]
  · unfold Causalean.Graph.FiniteDensity.Factorization.partialDensity
    apply Finset.prod_congr rfl
    intro l hl
    apply (mechanismUnitCubeFactorization hpos).local_factor l
    intro a ha
    have haA : a ∈ decoderRetainedLatentSet W order i := by
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact (Finset.mem_erase.mp hl).2
      · exact decoderRetainedLatentSet_parentClosed W horder hgraphOrder i
          (Finset.mem_erase.mp hl).2 ha
    have hka : k ≠ a := fun h => hk (h ▸ haA)
    simp [Function.update, hka.symm]

-- @node: equationTen_retainedMarginalMeasure
/-- Equation (10) as an equality of retained-coordinate measures: the actual intervention
law has the same target-plus-predecessor marginal as the explicit replacement-density product.  Given [the stated inputs and conditions](hyp:hpos,horder,hgraphOrder), [the stated conclusion](goal) follows. -/
lemma equationTen_retainedMarginalMeasure
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (hpos : PositiveNormalizedSmoothMechanisms G θ)
    {order : Fin n → ℕ}
    (horder : IsTopologicalOrdering (observedLawRatioGraph gaussianFeatureMap W.law) order)
    (hgraphOrder : PermutedGraphOrdered W order) (i : Fin n) :
    let B := mechanismUnitCubeFactorization hpos
    let q := mechanismInterventionDensity W hpos i
    let A := decoderRetainedLatentSet W order i
    Measure.map (Causalean.Mathlib.MeasureTheory.FiniteCoordinate.coordinateProjection
        (X := fun _ : Fin n => ℝ) A)
        (interventionalLaw θ (W.targetPerm i)) =
      Measure.map (Causalean.Mathlib.MeasureTheory.FiniteCoordinate.coordinateProjection
        (X := fun _ : Fin n => ℝ) A)
        ((Measure.pi (fun _ : Fin n =>
          Causalean.Graph.FiniteDensity.unitIntervalReference)).withDensity
            (fun v => q.density (v (W.targetPerm i)) *
              B.partialDensity (A.erase (W.targetPerm i)) v)) := by
  dsimp only
  let B := mechanismUnitCubeFactorization hpos
  let q := mechanismInterventionDensity W hpos i
  let A := decoderRetainedLatentSet W order i
  have hσ : ∀ _ : Fin n,
      SigmaFinite Causalean.Graph.FiniteDensity.unitIntervalReference := fun _ => by
    unfold Causalean.Graph.FiniteDensity.unitIntervalReference
    infer_instance
  have hprob : ∀ _ : Fin n,
      IsProbabilityMeasure Causalean.Graph.FiniteDensity.unitIntervalReference := fun _ => by
    constructor
    unfold Causalean.Graph.FiniteDensity.unitIntervalReference
    simp [Real.volume_Icc]
  have hBint : Measurable (B.interventionDensity (W.targetPerm i) q) :=
    @Causalean.Graph.FiniteDensity.Factorization.measurable_interventionDensity
      (Fin n) _ _ (fun _ : Fin n => ℝ) _
      (fun _ : Fin n => Causalean.Graph.FiniteDensity.unitIntervalReference) hσ G B
      (W.targetPerm i) q
  have hBpartial : Measurable (B.partialDensity (A.erase (W.targetPerm i))) :=
    @Causalean.Graph.FiniteDensity.Factorization.measurable_partialDensity
      (Fin n) _ _ (fun _ : Fin n => ℝ) _
      (fun _ : Fin n => Causalean.Graph.FiniteDensity.unitIntervalReference) hσ G B
      (A.erase (W.targetPerm i))
  rw [← mechanismUnitCubeFactorization_interventionMeasure W hpos i]
  unfold Causalean.Graph.FiniteDensity.Factorization.interventionMeasure
  apply @Causalean.Mathlib.MeasureTheory.FiniteCoordinate.map_coordinateProjection_withDensity_eq_of_lmarginal_eq
    (Fin n) _ (fun _ : Fin n => ℝ) _ _
    (fun _ : Fin n => Causalean.Graph.FiniteDensity.unitIntervalReference) hσ A
  · exact hBint
  · exact q.measurable_density.comp (measurable_pi_apply _) |>.mul hBpartial
  · rw [equationTen_interventionMarginalDensity W hpos horder hgraphOrder i]
    symm
    apply @lmarginal_eq_self_of_update_eq (Fin n) _ (fun _ : Fin n => ℝ) _
      (fun _ : Fin n => Causalean.Graph.FiniteDensity.unitIntervalReference) hprob
      (Finset.univ \ A)
    · exact (q.measurable_density.comp (measurable_pi_apply _)).mul hBpartial
    · intro k hk v x
      exact equationTen_retainedDensity_update_outside W hpos horder hgraphOrder i k
        (show k ∉ decoderRetainedLatentSet W order i from (Finset.mem_sdiff.mp hk).2) v x

-- @node: rawObservedConditionalRatioCDF_ae_eq_kernel_of_compProd
/-- A candidate finite kernel whose compositional product is the observed predecessor/score
law is the raw conditional-ratio CDF at every fixed threshold.  This is the
conditional-distribution uniqueness step used after equation (10).  Given [the stated inputs and conditions](hyp:hjoint), [the stated conclusion](goal) follows. -/
lemma rawObservedConditionalRatioCDF_ae_eq_kernel_of_compProd
    {n : ℕ}
    (laws : ObservedProbabilityLawFamily n) (order : Fin n → ℕ) (i : Fin n)
    (κ : Kernel (PredecessorLogRatios order i) ℝ) [IsFiniteKernel κ]
    (hjoint : Measure.map
      (fun x ↦
        (familyProjection (observedLawLogRatio laws.1) (predecessorSet order i) x,
          observedLawLogRatio laws.1 i x)) (laws.1 i.succ) =
      Measure.map
          (familyProjection (observedLawLogRatio laws.1) (predecessorSet order i))
          (laws.1 i.succ) ⊗ₘ κ) :
    ∀ t, (fun ell ↦ rawObservedConditionalRatioCDF laws order i t ell) =ᵐ[
      Measure.map
        (familyProjection (observedLawLogRatio laws.1) (predecessorSet order i))
        (laws.1 i.succ)] fun ell ↦ (κ ell (Set.Iic t)).toReal := by
  letI : IsProbabilityMeasure (laws.1 i.succ) := laws.2 i.succ
  have hcond := ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd
    (familyProjection (observedLawLogRatio laws.1) (predecessorSet order i))
    (measurable_observedLawLogRatio laws.1 i).aemeasurable hjoint
  intro t
  filter_upwards [hcond] with ell hell
  have hfinite : ∀ e, IsFiniteMeasure (laws.1 e) := by
    intro e
    letI : IsProbabilityMeasure (laws.1 e) := laws.2 e
    infer_instance
  rw [rawObservedConditionalRatioCDF, dif_pos hfinite, hell]

end CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity
