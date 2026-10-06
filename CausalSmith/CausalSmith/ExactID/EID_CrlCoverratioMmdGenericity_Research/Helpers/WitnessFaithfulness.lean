module
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.WitnessQuantitative
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.DecoderOrderedLocalMarkov
public import Causalean.Mathlib.Probability.Independence.Basic

/-!
# Graph reduction for explicit-witness faithfulness

This file isolates the finite graph calculation used to reduce faithfulness of
the explicit three-node witnesses to dependence of the unique adjacent pair.
-/

public section

open Causalean.Graph


noncomputable section

open MeasureTheory ProbabilityTheory Set

open Causalean.Mathlib.Probability.Independence

open Causalean.Mathlib.Probability.Independence.Conditional

namespace CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

-- @node: indepFun_of_condIndepFun_bot
/-- Conditional independence given the trivial sigma algebra is ordinary independence
on a probability space.  This is the reverse of Causalean's existing trivial-conditioning
bridge and is used to expose dependence of the explicit witness edge.  Given [the stated inputs and conditions](hyp:hf,hg,h), [the stated conclusion](goal) follows. -/
lemma indepFun_of_condIndepFun_bot
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    {f : Ω → β} {g : Ω → γ} (hf : Measurable f) (hg : Measurable g)
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    (h : ProbabilityTheory.CondIndepFun ⊥ bot_le f g μ) :
    IndepFun f g μ := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t hs ht
  have hfs : MeasurableSet (f ⁻¹' s) := hf hs
  have hgt : MeasurableSet (g ⁻¹' t) := hg ht
  have hfgst : MeasurableSet (f ⁻¹' s ∩ g ⁻¹' t) := hfs.inter hgt
  rw [ProbabilityTheory.condIndepFun_iff_condExp_inter_preimage_eq_mul hf hg] at h
  have heq := h s t hs ht
  change MeasureTheory.condExp ⊥ μ
      (Set.indicator (f ⁻¹' s ∩ g ⁻¹' t) (1 : Ω → ℝ)) =ᵐ[μ]
    fun ω =>
      MeasureTheory.condExp ⊥ μ (Set.indicator (f ⁻¹' s) (1 : Ω → ℝ)) ω *
        MeasureTheory.condExp ⊥ μ (Set.indicator (g ⁻¹' t) (1 : Ω → ℝ)) ω at heq
  rw [MeasureTheory.condExp_bot (μ := μ) _, MeasureTheory.condExp_bot (μ := μ) _,
    MeasureTheory.condExp_bot (μ := μ) _] at heq
  have hpoint := heq.exists
  rcases hpoint with ⟨ω, hω⟩
  rw [← ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _)
    (ENNReal.mul_ne_top (measure_ne_top μ _) (measure_ne_top μ _))]
  simpa only [MeasureTheory.integral_indicator_one hfgst,
    MeasureTheory.integral_indicator_one hfs,
    MeasureTheory.integral_indicator_one hgt, MeasureTheory.measureReal_def,
    ENNReal.toReal_mul] using hω

-- @node: indepFun_of_condIndepCoordinates_empty
/-- Coordinate-block conditional independence given the empty block implies ordinary
independence whenever the observational law is a probability measure.  Given [the stated inputs and conditions](hyp:hCI), [the stated conclusion](goal) follows. -/
lemma indepFun_of_condIndepCoordinates_empty
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    (X Y : Finset (Fin n)) [IsProbabilityMeasure (observationalLaw θ)]
    (hCI : CondIndepCoordinates θ X Y ∅) :
    IndepFun (coordinateProjection X) (coordinateProjection Y) (observationalLaw θ) := by
  rcases hCI with ⟨hμ, hX, hY, hZ, hCI⟩
  let _ := hμ
  have hbot : MeasurableSpace.comap (coordinateProjection (∅ : Finset (Fin n)))
      inferInstance = (⊥ : MeasurableSpace (LatentState n)) :=
    comap_eq_bot_of_subsingleton _
  rw [condIndepFun_iff_condExp_inter_preimage_eq_mul hX hY] at hCI
  rw [hbot] at hCI
  apply indepFun_of_condIndepFun_bot hX hY
  rw [condIndepFun_iff_condExp_inter_preimage_eq_mul hX hY]
  exact hCI

set_option maxHeartbeats 2000000 in
-- Exhaustive evaluation unfolds the bounded Bayes-ball search for all three finite blocks.
-- @node: threeNodeDAG_not_dSep_iff_cross_edge
/-- For pairwise-disjoint blocks in the three-node witness DAG, d-separation fails exactly
when the endpoints of its unique edge occur in opposite query blocks.  Given [the stated inputs and conditions](hyp:hXY,hXZ,hYZ), [the stated conclusion](goal) follows. -/
lemma threeNodeDAG_not_dSep_iff_cross_edge (X Y Z : Finset (Fin 3))
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z) :
    ¬ threeNodeDAG.dSep X Y Z ↔
      ((0 ∈ X ∧ 1 ∈ Y) ∨ (1 ∈ X ∧ 0 ∈ Y)) := by
  classical
  fin_cases X <;> fin_cases Y <;> fin_cases Z <;>
    first | contradiction | decide

-- @node: condIndepCoordinates_singletons_of_mem
/-- Conditional independence of two coordinate blocks descends to any chosen singleton
coordinate from each block.  Given [the stated inputs and conditions](hyp:ha,hb,hCI), [the stated conclusion](goal) follows. -/
lemma condIndepCoordinates_singletons_of_mem
    {n : ℕ} {G : DAG (Fin n)} (θ : Mechanism n G)
    (X Y Z : Finset (Fin n)) {a b : Fin n} (ha : a ∈ X) (hb : b ∈ Y)
    (hCI : CondIndepCoordinates θ X Y Z) :
    CondIndepCoordinates θ {a} {b} Z := by
  rcases hCI with ⟨hμ, hX, hY, hZ, hCI⟩
  let left : ((j : {j // j ∈ X}) → ℝ) →
      ((j : {j // j ∈ ({a} : Finset (Fin n))}) → ℝ) :=
    fun v _ => v ⟨a, ha⟩
  let right : ((j : {j // j ∈ Y}) → ℝ) →
      ((j : {j // j ∈ ({b} : Finset (Fin n))}) → ℝ) :=
    fun v _ => v ⟨b, hb⟩
  have hleft : coordinateProjection ({a} : Finset (Fin n)) =
      left ∘ coordinateProjection X := by
    funext v j
    have hj : (j : Fin n) = a := Finset.mem_singleton.mp j.prop
    change v j = v a
    exact congrArg v hj
  have hright : coordinateProjection ({b} : Finset (Fin n)) =
      right ∘ coordinateProjection Y := by
    funext v j
    have hj : (j : Fin n) = b := Finset.mem_singleton.mp j.prop
    change v j = v b
    exact congrArg v hj
  refine ⟨hμ, ?_, ?_, hZ, ?_⟩
  · rw [hleft]
    fun_prop
  · rw [hright]
    fun_prop
  have hc := hCI.comp (show Measurable left by fun_prop)
    (show Measurable right by fun_prop)
  simpa only [← hleft, ← hright] using hc

-- @node: condIndepCoordinates_symm
/-- Coordinate-block conditional independence is symmetric in its two query blocks.  Given [the stated inputs and conditions](hyp:hCI), [the stated conclusion](goal) follows. -/
lemma condIndepCoordinates_symm
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    {X Y Z : Finset (Fin n)} (hCI : CondIndepCoordinates θ X Y Z) :
    CondIndepCoordinates θ Y X Z := by
  rcases hCI with ⟨hμ, hX, hY, hZ, hCI⟩
  exact ⟨hμ, hY, hX, hZ, hCI.symm⟩

-- @node: threeNodeDAG_faithful_of_edge_dependence
/-- For the three-node witness DAG, dependence of the unique adjacent pair under every
admissible conditioning block suffices for full faithfulness.  Given [the stated inputs and conditions](hyp:hdep), [the stated conclusion](goal) follows. -/
lemma threeNodeDAG_faithful_of_edge_dependence
    {θ : Mechanism 3 threeNodeDAG}
    (hdep : ∀ Z : Finset (Fin 3), Disjoint ({0} : Finset (Fin 3)) Z →
      Disjoint ({1} : Finset (Fin 3)) Z →
      ¬ CondIndepCoordinates θ {0} {1} Z) :
    Faithfulness threeNodeDAG θ := by
  intro X Y Z hXY hXZ hYZ hCI
  by_contra hdsep
  rcases (threeNodeDAG_not_dSep_iff_cross_edge X Y Z hXY hXZ hYZ).mp hdsep with
    hcross | hcross
  · exact hdep Z (Finset.disjoint_singleton_left.mpr fun h0Z =>
      (Finset.disjoint_left.mp hXZ) hcross.1 h0Z)
      (Finset.disjoint_singleton_left.mpr fun h1Z =>
        (Finset.disjoint_left.mp hYZ) hcross.2 h1Z)
      (condIndepCoordinates_singletons_of_mem θ X Y Z hcross.1 hcross.2 hCI)
  · exact hdep Z (Finset.disjoint_singleton_left.mpr fun h0Z =>
      (Finset.disjoint_left.mp hYZ) hcross.2 h0Z)
      (Finset.disjoint_singleton_left.mpr fun h1Z =>
        (Finset.disjoint_left.mp hXZ) hcross.1 h1Z)
      (condIndepCoordinates_symm
        (condIndepCoordinates_singletons_of_mem θ X Y Z hcross.1 hcross.2 hCI))

-- @node: threeNodeDAG_faithful_of_unconditional_edge_dependence
/-- For the three-node witness DAG, unconditional dependence of the unique edge
and independence of its first endpoint from the isolated node imply full faithfulness.  Given [the stated inputs and conditions](hyp:hdep,hisolated), [the stated conclusion](goal) follows. -/
lemma threeNodeDAG_faithful_of_unconditional_edge_dependence
    {θ : Mechanism 3 threeNodeDAG}
    (hdep : ¬ CondIndepCoordinates θ {0} {1} ∅)
    (hisolated : CondIndepCoordinates θ {0} {2} ∅) :
    Faithfulness threeNodeDAG θ := by
  apply threeNodeDAG_faithful_of_edge_dependence
  intro Z h0Z h1Z hCI
  classical
  have hZ : Z = ∅ ∨ Z = {2} := by
    apply Finset.subset_singleton_iff.mp
    intro k hk
    fin_cases k
    · exact (Finset.disjoint_singleton_left.mp h0Z hk).elim
    · exact (Finset.disjoint_singleton_left.mp h1Z hk).elim
    · simp
  rcases hZ with rfl | rfl
  · exact hdep hCI
  · apply hdep
    rcases hCI with ⟨hμ, hX, hY, hW, hXY⟩
    letI := hμ
    rcases hisolated with ⟨_, hX', hW', hEmpty, hXW⟩
    have hbot : MeasurableSpace.comap (coordinateProjection (∅ : Finset (Fin 3)))
        inferInstance = (⊥ : MeasurableSpace (LatentState 3)) :=
      comap_eq_bot_of_subsingleton _
    have hXY' : ProbabilityTheory.CondIndepFun
        ((⊥ : MeasurableSpace (LatentState 3)) ⊔
          MeasurableSpace.comap (coordinateProjection ({2} : Finset (Fin 3))) inferInstance)
        (sup_le bot_le hW.comap_le) (coordinateProjection {0})
          (coordinateProjection {1}) (observationalLaw θ) := by
      simpa using hXY
    have hXW' : ProbabilityTheory.CondIndepFun
        (⊥ : MeasurableSpace (LatentState 3)) bot_le
        (coordinateProjection {0}) (coordinateProjection {2}) (observationalLaw θ) := by
      simpa only [hbot] using hXW
    have hpair := condIndepFun_contraction_of_prodMk bot_le
      hX hY hW hXY' hXW'
    have hplain : ProbabilityTheory.CondIndepFun
        (⊥ : MeasurableSpace (LatentState 3)) bot_le
        (coordinateProjection {0}) (coordinateProjection {1}) (observationalLaw θ) := by
      convert hpair.comp measurable_id measurable_fst using 1 <;> funext ω <;> rfl
    exact ⟨hμ, hX, hY, hEmpty, by simpa only [hbot] using hplain⟩

-- @node: threeNodeDAG_isolated_independence
/-- Every positive normalized mechanism factorizing over the three-node witness DAG makes
the first endpoint of the unique edge independent of the isolated third coordinate.  Given [the stated inputs and conditions](hyp:hpos), [the stated conclusion](goal) follows. -/
lemma threeNodeDAG_isolated_independence
    {θ : Mechanism 3 threeNodeDAG}
    (hpos : PositiveNormalizedSmoothMechanisms threeNodeDAG θ) :
    CondIndepCoordinates θ {0} {2} ∅ := by
  let τ : Causalean.Graph.FiniteDensity.TopologicalRanking threeNodeDAG := {
    rank := fun i ↦ i.val
    injective_rank := Fin.val_injective
    edge_lt := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp [threeNodeDAG, threeNodeEdge] at hij ⊢ }
  have hpred : Causalean.Graph.FiniteDensity.predecessors τ 2 = {0, 1} := by
    ext k
    fin_cases k <;> decide
  have hraw := mechanism_condIndepGiven_orderedLocalMarkov hpos τ 2 ∅
    (by simp [hpred]) (by simp [threeNodeDAG, threeNodeEdge, DAG.parents])
  rw [hpred] at hraw
  rcases hraw with ⟨hμ, h2, h01, hE, hci⟩
  letI := hμ
  have h0 : Measurable (coordinateProjection ({0} : Finset (Fin 3))) := by
    unfold coordinateProjection
    fun_prop
  have h2local : Measurable (coordinateProjection ({2} : Finset (Fin 3))) := by
    unfold coordinateProjection
    fun_prop
  have hleft : Measurable (fun r : ℝ ↦
      fun _ : {j // j ∈ ({2} : Finset (Fin 3))} ↦ r) := by
    apply measurable_pi_lambda
    intro j
    exact measurable_id
  have hright : Measurable
      (fun z : (j : {j // j ∈ ({0, 1} : Finset (Fin 3))}) → ℝ ↦
        fun _ : {j // j ∈ ({0} : Finset (Fin 3))} ↦ z ⟨0, by simp⟩) := by
    apply measurable_pi_lambda
    intro j
    exact measurable_pi_apply _
  have hci' := hci.comp hleft hright
  have hEmptyLocal : Measurable (coordinateProjection (∅ : Finset (Fin 3))) := by
    unfold coordinateProjection
    fun_prop
  refine condIndepCoordinates_symm ⟨hμ, h2local, h0, hEmptyLocal, ?_⟩
  change ProbabilityTheory.CondIndepFun
    (MeasurableSpace.comap
      (Causalean.Mathlib.MeasureTheory.FiniteCoordinate.coordinateProjection (∅ : Finset (Fin 3)))
      inferInstance) _ (coordinateProjection {2}) (coordinateProjection {0})
      (observationalLaw θ)
  convert hci' using 1
  · funext v j
    have hj : (j : Fin 3) = 2 := Finset.mem_singleton.mp j.prop
    change v j = v 2
    exact congrArg v hj
  · funext v j
    have hj : (j : Fin 3) = 0 := Finset.mem_singleton.mp j.prop
    change v j = v 0
    exact congrArg v hj

-- @node: threeNodeDAG_faithful_of_causalMinimality
/-- On the explicit three-node DAG, positivity and causal minimality already imply
faithfulness because the only nontrivial d-connection is its unique edge.  Given [the stated inputs and conditions](hyp:hpos,hminimal), [the stated conclusion](goal) follows. -/
lemma threeNodeDAG_faithful_of_causalMinimality
    {θ : Mechanism 3 threeNodeDAG}
    (hpos : PositiveNormalizedSmoothMechanisms threeNodeDAG θ)
    (hminimal : CausalMinimality threeNodeDAG θ) :
    Faithfulness threeNodeDAG θ := by
  apply threeNodeDAG_faithful_of_unconditional_edge_dependence
  · intro h01
    have h10 := condIndepCoordinates_symm h01
    have hm := hminimal (j := 0) (i := 1) (by
      simp [threeNodeDAG, threeNodeEdge])
    apply hm
    convert h10 using 1
    ext k
    fin_cases k <;> simp [threeNodeDAG, threeNodeEdge, DAG.parents]
  · exact threeNodeDAG_isolated_independence hpos

end CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity
