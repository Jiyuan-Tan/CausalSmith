module
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.DecoderGraph

/-!
# Compact triangular predecessor-score inverse

This file packages equations (7)--(9): predecessor latent coordinates form a compact cube,
their triangular log-ratio score map is a continuous injection, and hence it has a continuous
inverse on its image.
-/

@[expose] public section

open Causalean.Graph


open MeasureTheory Set
open scoped Topology

noncomputable section

namespace CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

-- @node: PredecessorLatentCube
/-- The compact product cube of latent coordinates indexed by predecessors of `i`. -/
abbrev PredecessorLatentCube {n : ℕ} (order : Fin n → ℕ) (i : Fin n) :=
  (j : {j // j ∈ predecessorSet order i}) → Set.Icc (0 : ℝ) 1

-- @node: predecessorCubeLatentState
/-- Embed predecessor coordinates into the full latent cube, filling nonpredecessors with zero. -/
def predecessorCubeLatentState
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (order : Fin n → ℕ) (i : Fin n)
    (z : PredecessorLatentCube order i) : LatentState n := fun k =>
  if h : W.targetPerm.symm k ∈ predecessorSet order i then
    z ⟨W.targetPerm.symm k, h⟩ else 0

-- @node: predecessorLatentCubeOfState
/-- Restrict a latent cube point to the coordinates indexed by decoder predecessors. -/
def predecessorLatentCubeOfState
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (order : Fin n → ℕ) (i : Fin n)
    (v : LatentState n) (hv : v ∈ latentCube n) : PredecessorLatentCube order i :=
  fun j => ⟨v (W.targetPerm j), hv _ (Set.mem_univ _)⟩

-- @node: predecessorCubeLatentState_ofState_apply
/-- Embedding the predecessor restriction back into the ambient cube preserves every
predecessor coordinate.  Given [the stated inputs and conditions](hyp:hv,hj), [the stated conclusion](goal) follows. -/
lemma predecessorCubeLatentState_ofState_apply
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (order : Fin n → ℕ) (i : Fin n)
    (v : LatentState n) (hv : v ∈ latentCube n)
    (j : Fin n) (hj : j ∈ predecessorSet order i) :
    predecessorCubeLatentState W order i
        (predecessorLatentCubeOfState W order i v hv) (W.targetPerm j) =
      v (W.targetPerm j) := by
  simp [predecessorCubeLatentState, predecessorLatentCubeOfState, hj]

-- @node: predecessorScoreMap
/-- The triangular predecessor log-ratio map, written directly in latent coordinates. -/
def predecessorScoreMap
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (order : Fin n → ℕ) (i : Fin n)
    (z : PredecessorLatentCube order i) : PredecessorLogRatios order i := fun j =>
  Real.log
    (θ.q (W.targetPerm j)
        ((predecessorCubeLatentState W order i z) (W.targetPerm j)) /
      θ.p (W.targetPerm j) (predecessorCubeLatentState W order i z))

-- @node: predecessorCubeLatentState_mem_latentCube
/-- The zero-filled predecessor-coordinate embedding always lies in the full latent cube.  [the stated conclusion](goal) follows. -/
lemma predecessorCubeLatentState_mem_latentCube
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (order : Fin n → ℕ) (i : Fin n)
    (z : PredecessorLatentCube order i) :
    predecessorCubeLatentState W order i z ∈ latentCube n := by
  intro k hk
  simp only [predecessorCubeLatentState]
  split
  · exact (z _).property
  · exact ⟨by norm_num, by norm_num⟩

-- @node: predecessorScoreMap_of_latentState
/-- On a latent cube point, the compact triangular score map is exactly the observed
predecessor log-ratio projection pulled back through the mixing map.  Given [the stated inputs and conditions](hyp:hpos,hmix,hone,horder,hgraphOrder,hv), [the stated conclusion](goal) follows. -/
lemma predecessorScoreMap_of_latentState
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W)
    {order : Fin n → ℕ}
    (horder : IsTopologicalOrdering (observedLawRatioGraph gaussianFeatureMap W.law) order)
    (hgraphOrder : PermutedGraphOrdered W order)
    (i : Fin n) (v : LatentState n) (hv : v ∈ latentCube n) :
    predecessorScoreMap W order i (predecessorLatentCubeOfState W order i v hv) =
      familyProjection (observedLawLogRatio W.law) (predecessorSet order i) (W.mix v) := by
  funext j
  unfold familyProjection
  rw [observedLawLogRatio_comp_mix_eq W hpos hmix hone j v hv]
  unfold predecessorScoreMap
  congr 2
  · exact congrArg (θ.q (W.targetPerm j))
      (predecessorCubeLatentState_ofState_apply W order i v hv j j.property)
  · apply θ.parent_local (W.targetPerm j)
    · exact predecessorCubeLatentState_ofState_apply W order i v hv j j.property
    · intro a ha
      let k := W.targetPerm.symm a
      have hkParent : k ∈ environmentParentSet W j := by
        simpa [k, environmentParentSet, DAG.parents] using ha
      have hkBeforeJ := environmentParentSet_subset_predecessorSet_of_transitiveClosure
        W horder hgraphOrder j hkParent
      have hjBeforeI : order j < order i := by
        simpa [predecessorSet] using j.property
      have hkBeforeI : k ∈ predecessorSet order i := by
        simpa [predecessorSet] using
          (show order k < order i from (by
            simpa [predecessorSet] using hkBeforeJ : order k < order j).trans hjBeforeI)
      simpa [k] using predecessorCubeLatentState_ofState_apply
        W order i v hv k hkBeforeI

-- @node: observedPredecessorLogRatio_mem_scoreRange
/-- Every predecessor log-ratio vector realized by a latent cube point belongs to the image
of the compact triangular predecessor-score map.  Given [the stated inputs and conditions](hyp:hpos,hmix,hone,horder,hgraphOrder,hv), [the stated conclusion](goal) follows. -/
lemma observedPredecessorLogRatio_mem_scoreRange
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W)
    {order : Fin n → ℕ}
    (horder : IsTopologicalOrdering (observedLawRatioGraph gaussianFeatureMap W.law) order)
    (hgraphOrder : PermutedGraphOrdered W order)
    (i : Fin n) (v : LatentState n) (hv : v ∈ latentCube n) :
    familyProjection (observedLawLogRatio W.law) (predecessorSet order i) (W.mix v) ∈
      Set.range (predecessorScoreMap W order i) := by
  refine ⟨predecessorLatentCubeOfState W order i v hv, ?_⟩
  exact predecessorScoreMap_of_latentState W hpos hmix hone horder hgraphOrder i v hv

-- @node: continuous_predecessorScoreMap
/-- Smooth positive mechanisms make the triangular predecessor score map continuous.  Given [the stated inputs and conditions](hyp:hpos), [the stated conclusion](goal) follows. -/
lemma continuous_predecessorScoreMap
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (order : Fin n → ℕ) (i : Fin n) : Continuous (predecessorScoreMap W order i) := by
  have hlatent : Continuous (predecessorCubeLatentState W order i) := by
    apply continuous_pi
    intro k
    simp only [predecessorCubeLatentState]
    split <;> fun_prop
  apply continuous_pi
  intro j
  have hcoord : ∀ z, predecessorCubeLatentState W order i z (W.targetPerm j) ∈
      Set.Icc (0 : ℝ) 1 := by
    intro z
    simpa only [predecessorCubeLatentState, Equiv.symm_apply_apply,
      dif_pos j.property] using (z j).property
  have hpne : ∀ z, θ.p (W.targetPerm j)
      (predecessorCubeLatentState W order i z) ≠ 0 := fun z =>
    ne_of_gt (hpos.1 _ _ (predecessorCubeLatentState_mem_latentCube W order i z))
  have hqne : ∀ z, θ.q (W.targetPerm j)
      (predecessorCubeLatentState W order i z (W.targetPerm j)) ≠ 0 := fun z =>
    ne_of_gt (hpos.2.1 _ _ (hcoord z))
  apply Continuous.log _ (fun z => div_ne_zero (hqne z) (hpne z))
  apply Continuous.div _ _ hpne
  · exact (hpos.2.2.2.1 (W.targetPerm j)).continuousOn.comp_continuous
      (continuous_apply (W.targetPerm j) |>.comp hlatent) hcoord
  · exact (hpos.2.2.1 (W.targetPerm j)).continuousOn.comp_continuous hlatent
      (predecessorCubeLatentState_mem_latentCube W order i)

-- @node: predecessorScoreMap_injective
/-- The prescribed own-score signs make the triangular predecessor score map injective.  Given [the stated inputs and conditions](hyp:hpos,hmix,hone,hsign,horder,hgraphOrder), [the stated conclusion](goal) follows. -/
lemma predecessorScoreMap_injective
    {n : ℕ} {G : DAG (Fin n)} (s : SignVector n)
    {θ : Mechanism n G} (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W)
    (hsign : FixedOwnDerivativeSign G s θ)
    {order : Fin n → ℕ}
    (horder : IsTopologicalOrdering (observedLawRatioGraph gaussianFeatureMap W.law) order)
    (hgraphOrder : PermutedGraphOrdered W order)
    (i : Fin n) : Function.Injective (predecessorScoreMap W order i) := by
  intro z w heq
  let vz := predecessorCubeLatentState W order i z
  let vw := predecessorCubeLatentState W order i w
  have hvz : vz ∈ latentCube n := predecessorCubeLatentState_mem_latentCube W order i z
  have hvw : vw ∈ latentCube n := predecessorCubeLatentState_mem_latentCube W order i w
  have heq' : familyProjection (observedLawLogRatio W.law) (predecessorSet order i)
        (W.mix vz) = familyProjection (observedLawLogRatio W.law)
          (predecessorSet order i) (W.mix vw) := by
    funext j
    simp only [familyProjection]
    rw [observedLawLogRatio_comp_mix_eq W hpos hmix hone j vz hvz,
      observedLawLogRatio_comp_mix_eq W hpos hmix hone j vw hvw]
    exact congrFun heq j
  have hcoords := predecessorLogRatioProjection_injective_on_predecessors
    s W hpos hmix hone hsign horder hgraphOrder i hvz hvw heq'
  funext j
  apply Subtype.ext
  simpa only [vz, vw, predecessorCubeLatentState, Equiv.symm_apply_apply,
    dif_pos j.property] using hcoords j j.property

-- @node: predecessorScoreHomeomorph
/-- The compact triangular predecessor score map is a homeomorphism onto its image. -/
noncomputable def predecessorScoreHomeomorph
    {n : ℕ} {G : DAG (Fin n)} (s : SignVector n)
    {θ : Mechanism n G} (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W)
    (hsign : FixedOwnDerivativeSign G s θ)
    {order : Fin n → ℕ}
    (horder : IsTopologicalOrdering (observedLawRatioGraph gaussianFeatureMap W.law) order)
    (hgraphOrder : PermutedGraphOrdered W order)
    (i : Fin n) :
    PredecessorLatentCube order i ≃ₜ Set.range (predecessorScoreMap W order i) :=
  ((continuous_predecessorScoreMap W hpos order i).isClosedEmbedding
      (predecessorScoreMap_injective s W hpos hmix hone hsign horder hgraphOrder i)).isEmbedding
    |>.toHomeomorph

-- @node: continuous_predecessorScoreInverse
/-- The inverse predecessor-coordinate reconstruction is continuous on the score image.  Given [the stated inputs and conditions](hyp:hpos,hmix,hone,hsign,horder,hgraphOrder), [the stated conclusion](goal) follows. -/
lemma continuous_predecessorScoreInverse
    {n : ℕ} {G : DAG (Fin n)} (s : SignVector n)
    {θ : Mechanism n G} (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W)
    (hsign : FixedOwnDerivativeSign G s θ)
    {order : Fin n → ℕ}
    (horder : IsTopologicalOrdering (observedLawRatioGraph gaussianFeatureMap W.law) order)
    (hgraphOrder : PermutedGraphOrdered W order)
    (i : Fin n) :
    Continuous (predecessorScoreHomeomorph s W hpos hmix hone hsign horder hgraphOrder i).symm :=
  (predecessorScoreHomeomorph s W hpos hmix hone hsign horder hgraphOrder i).symm.continuous

end CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity
