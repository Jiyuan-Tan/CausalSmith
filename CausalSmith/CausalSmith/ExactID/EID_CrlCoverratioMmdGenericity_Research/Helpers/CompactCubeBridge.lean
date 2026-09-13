import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Basic
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Compact cube carrier bridge

This file identifies the ambient closed cube used by the paper with the product of compact
interval coordinate types used by finite positive-density factorizations.
-/

open MeasureTheory Set

noncomputable section

namespace CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

attribute [local instance] Measure.Subtype.measureSpace

-- @node: compactCubeEquiv
/-- The product of unit-interval coordinate types is measurably equivalent to the subtype of
ambient latent vectors lying in the closed cube. -/
def compactCubeEquiv (n : ℕ) :
    ((i : Fin n) → Set.Icc (0 : ℝ) 1) ≃ᵐ {v : LatentState n // v ∈ latentCube n} where
  toFun x := ⟨fun i ↦ x i, fun i _ ↦ (x i).property⟩
  invFun v := fun i ↦ ⟨v.1 i, v.2 i (Set.mem_univ i)⟩
  left_inv x := by
    funext i
    exact Subtype.ext rfl
  right_inv v := by
    exact Subtype.ext (funext fun _ ↦ rfl)
  measurable_toFun := by
    apply Measurable.subtype_mk
    exact measurable_pi_iff.mpr fun i ↦
      measurable_subtype_coe.comp (measurable_pi_apply i)
  measurable_invFun := by
    apply measurable_pi_iff.mpr
    intro i
    change Measurable (fun v : {v : LatentState n // v ∈ latentCube n} ↦
      (⟨v.1 i, v.2 i (Set.mem_univ i)⟩ : Set.Icc (0 : ℝ) 1))
    exact Measurable.subtype_mk
      ((measurable_pi_apply i).comp measurable_subtype_coe)

-- @node: compactCubeEquiv_measurePreserving
/-- The cube equivalence carries the product of restricted coordinate volumes to the restricted
ambient volume on the closed cube.  [the stated conclusion](goal) follows. -/
lemma compactCubeEquiv_measurePreserving (n : ℕ) :
    MeasurePreserving (compactCubeEquiv n)
      (Measure.pi fun _ : Fin n ↦ (volume : Measure (Set.Icc (0 : ℝ) 1)))
      (volume : Measure {v : LatentState n // v ∈ latentCube n}) := by
  let e := compactCubeEquiv n
  let c : ((i : Fin n) → Set.Icc (0 : ℝ) 1) → LatentState n :=
    fun x i ↦ x i
  have hc : MeasurePreserving c
      (Measure.pi fun _ : Fin n ↦ (volume : Measure (Set.Icc (0 : ℝ) 1)))
      (Measure.pi fun _ : Fin n ↦ volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    exact measurePreserving_pi _ _ fun _ ↦
      measurePreserving_subtype_coe measurableSet_Icc
  have hcube : MeasurableSet (latentCube n) := by
    rw [latentCube]
    exact MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc
  have hcoe : MeasurePreserving
      (Subtype.val : {v : LatentState n // v ∈ latentCube n} → LatentState n)
      volume (volume.restrict (latentCube n)) :=
    measurePreserving_subtype_coe hcube
  refine ⟨e.measurable, ?_⟩
  apply (MeasurableEmbedding.subtype_coe hcube).map_injective
  rw [Measure.map_map measurable_subtype_coe e.measurable, hcoe.map_eq]
  change Measure.map c
      (Measure.pi fun _ : Fin n ↦ (volume : Measure (Set.Icc (0 : ℝ) 1))) =
    volume.restrict (latentCube n)
  rw [hc.map_eq]
  change (Measure.pi fun _ : Fin n ↦ volume.restrict (Set.Icc (0 : ℝ) 1)) =
    volume.restrict (Set.univ.pi fun _ : Fin n ↦ Set.Icc (0 : ℝ) 1)
  rw [MeasureTheory.volume_pi, Measure.restrict_pi_pi]

-- @node: compactCubeInclude
/-- Compact coordinate assignments include into the ambient latent vector space. -/
def compactCubeInclude (n : ℕ) :
    ((i : Fin n) → Set.Icc (0 : ℝ) 1) → LatentState n :=
  fun x i ↦ x i

-- @node: compactCubeRetract
/-- Coordinatewise projection onto the unit interval retracts the ambient latent vector space
onto compact coordinate assignments. -/
def compactCubeRetract (n : ℕ) :
    LatentState n → ((i : Fin n) → Set.Icc (0 : ℝ) 1) :=
  fun v i ↦ Set.projIcc 0 1 (by norm_num) (v i)

-- @node: measurable_compactCubeInclude
/-- Inclusion of compact coordinate assignments into ambient latent vectors is measurable.  [the stated conclusion](goal) follows. -/
lemma measurable_compactCubeInclude (n : ℕ) : Measurable (compactCubeInclude n) := by
  exact measurable_pi_iff.mpr fun i ↦
    measurable_subtype_coe.comp (measurable_pi_apply i)

-- @node: measurable_compactCubeRetract
/-- The coordinatewise compact-cube retraction is measurable.  [the stated conclusion](goal) follows. -/
lemma measurable_compactCubeRetract (n : ℕ) : Measurable (compactCubeRetract n) := by
  exact measurable_pi_iff.mpr fun i ↦
    continuous_projIcc.measurable.comp (measurable_pi_apply i)

-- @node: compactCubeRetract_include
/-- Retraction after inclusion is exactly the identity on compact coordinate assignments.  [the stated conclusion](goal) follows. -/
lemma compactCubeRetract_include (n : ℕ) :
    compactCubeRetract n ∘ compactCubeInclude n = id := by
  funext x
  funext i
  apply Subtype.ext
  exact congrArg Subtype.val
    (Set.projIcc_of_mem (show (0 : ℝ) ≤ 1 by norm_num) (x i).property)

-- @node: compactCubeInclude_retract_of_mem
/-- Inclusion after retraction fixes every ambient point belonging to the latent cube.  Given [the stated inputs and conditions](hyp:hv), [the stated conclusion](goal) follows. -/
lemma compactCubeInclude_retract_of_mem {n : ℕ} {v : LatentState n}
    (hv : v ∈ latentCube n) :
    compactCubeInclude n (compactCubeRetract n v) = v := by
  funext i
  exact congrArg Subtype.val
    (Set.projIcc_of_mem (show (0 : ℝ) ≤ 1 by norm_num)
      (hv i (Set.mem_univ i)))

-- @node: compactCubeInclude_retract_ae_observationalLaw
/-- Under a positive smooth mechanism's cube-supported observational law, inclusion after the
compact-cube retraction is almost everywhere the ambient identity.  [the stated conclusion](goal) follows. -/
lemma compactCubeInclude_retract_ae_observationalLaw
    {n : ℕ} {G : Causalean.DAG (Fin n)} (θ : Mechanism n G) :
    (compactCubeInclude n ∘ compactCubeRetract n) =ᵐ[observationalLaw θ] id := by
  have hcube : MeasurableSet (latentCube n) := by
    rw [latentCube]
    exact MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc
  have hbase : (compactCubeInclude n ∘ compactCubeRetract n)
      =ᵐ[volume.restrict (latentCube n)] id := by
    filter_upwards [ae_restrict_mem hcube] with v hv
    simpa only [Function.comp_apply, id_eq] using compactCubeInclude_retract_of_mem hv
  exact (withDensity_absolutelyContinuous _ _).ae_le hbase

-- @node: map_compactCubeInclude_map_compactCubeRetract_observationalLaw
/-- Pushing a cube-supported observational law to compact coordinates and including it back
recovers the original ambient law.  [the stated conclusion](goal) follows. -/
lemma map_compactCubeInclude_map_compactCubeRetract_observationalLaw
    {n : ℕ} {G : Causalean.DAG (Fin n)} (θ : Mechanism n G) :
    Measure.map (compactCubeInclude n)
        (Measure.map (compactCubeRetract n) (observationalLaw θ)) =
      observationalLaw θ := by
  rw [Measure.map_map (measurable_compactCubeInclude n)
    (measurable_compactCubeRetract n)]
  rw [Measure.map_congr (compactCubeInclude_retract_ae_observationalLaw θ)]
  exact Measure.map_id

-- @node: map_compactCubeRetract_map_compactCubeInclude
/-- For every compact-coordinate measure, inclusion followed by retraction also recovers the
original measure.  [the stated conclusion](goal) follows. -/
lemma map_compactCubeRetract_map_compactCubeInclude
    {n : ℕ} (μ : Measure ((i : Fin n) → Set.Icc (0 : ℝ) 1)) :
    Measure.map (compactCubeRetract n) (Measure.map (compactCubeInclude n) μ) = μ := by
  rw [Measure.map_map (measurable_compactCubeRetract n)
    (measurable_compactCubeInclude n)]
  rw [compactCubeRetract_include]
  exact Measure.map_id

end CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity
