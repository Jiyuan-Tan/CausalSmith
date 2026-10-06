module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.SignComponents
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.MixtureOccupancySeries
public import Causalean.Stat.RandomGraph.Expectation
public import Mathlib.MeasureTheory.Function.Floor

/-! # Original-covariate component occupancy

Cell adjacency has child-section mass at most 3/k. A single root for each
selected vertex set avoids an extra factor of the component size in the
spanning-tree union bound.
-/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier
attribute [local instance] Classical.propDecidable

/-- The half-open cell convention, including its endpoint totalization, is measurable. [The stated conclusion follows](goal). -/
-- @node: cellIndex_measurable
@[fun_prop] lemma cellIndex_measurable (k : ℕ) : Measurable (cellIndex k) := by
  unfold cellIndex
  fun_prop

/-- A cell graph edge is a measurable event of its two original covariates. -/
-- @node: cellCoordinateGraph
def cellCoordinateGraph (n k : ℕ) :
    Causalean.Stat.RandomGraph.CoordinateGraph (fun _ : Fin n => Covariate) where
  edgeEvent _ _ := {z | cellIndex k z.1 ≤ cellIndex k z.2 + 1 ∧
    cellIndex k z.2 ≤ cellIndex k z.1 + 1}
  measurable_edgeEvent _ _ := by
    apply MeasurableSet.inter
    · exact measurableSet_le ((cellIndex_measurable k).comp measurable_fst)
        (((cellIndex_measurable k).comp measurable_snd).add_const 1)
    · exact measurableSet_le ((cellIndex_measurable k).comp measurable_snd)
        (((cellIndex_measurable k).comp measurable_fst).add_const 1)
  symmetric _ _ _ _ := and_comm

/-- The coordinate-local graph is exactly the original-record sign graph. Under the stated assumptions. [The stated conclusion follows](goal). -/
-- @node: cellCoordinateGraph_eq
lemma cellCoordinateGraph_eq {n : ℕ} (k : ℕ) (x : Fin n → Covariate) :
    (cellCoordinateGraph n k).graph x = originalRecordSignGraph k x := by
  rfl

/-- [A child's admissible cells fit inside a real interval of length 3/k.](goal) Under [the stated assumptions](hyp:hk,h). -/
-- @node: cell_adjacent_child_interval
lemma cell_adjacent_child_interval (k : ℕ) (hk : 1 ≤ k) (y z : Covariate)
    (h : cellIndex k z ≤ cellIndex k y + 1 ∧ cellIndex k y ≤ cellIndex k z + 1) :
    (z : ℝ) ∈ Set.Icc (((cellIndex k y : ℝ)-1)/(k : ℝ))
      (((cellIndex k y : ℝ)+2)/(k : ℝ)) := by
  have hkp : (0 : ℝ) < k := by exact_mod_cast hk
  have hz := cellCoord_mem_unit k hk z
  have hleft : (cellIndex k y : ℝ) ≤ (cellIndex k z : ℝ)+1 := by
    exact_mod_cast h.2
  have hright : (cellIndex k z : ℝ) ≤ (cellIndex k y : ℝ)+1 := by
    exact_mod_cast h.1
  unfold cellCoord at hz
  constructor
  · apply (div_le_iff₀ hkp).mpr
    nlinarith [hz.1]
  · apply (le_div_iff₀ hkp).mpr
    nlinarith [hz.2]

/-- [Integrating one leaf costs at most 3/k, including boundary cells.](goal) Under [the stated assumptions](hyp:hk). -/
-- @node: cell_adjacent_child_mass_le
lemma cell_adjacent_child_mass_le (k : ℕ) (hk : 1 ≤ k) (y : Covariate) :
    uniformLaw {z | cellIndex k z ≤ cellIndex k y + 1 ∧
      cellIndex k y ≤ cellIndex k z + 1} ≤ ENNReal.ofReal (3/(k : ℝ)) := by
  rw [uniformLaw, comap_subtype_coe_apply measurableSet_Icc]
  calc
    _ ≤ (volume : Measure ℝ)
        (Set.Icc (((cellIndex k y : ℝ)-1)/(k : ℝ))
          (((cellIndex k y : ℝ)+2)/(k : ℝ))) := by
      apply measure_mono
      rintro v ⟨z, hz, rfl⟩
      exact cell_adjacent_child_interval k hk y z hz
    _ = _ := by
      rw [Real.volume_Icc]
      congr 1
      ring

/-- [A specified nonempty component has one selected rooted-parent cover.
The root is fixed before sampling, so no extra factor of its size is charged. [the documented result](goal) Under [the stated assumptions](hyp:hr,x). -/
-- @node: component_indicator_le_rootWitness
lemma component_indicator_le_rootWitness {V : Type*} [DecidableEq V]
    {X : V → Type*} [∀ i, MeasurableSpace (X i)]
    (M : Causalean.Stat.RandomGraph.CoordinateGraph X)
    (S : Finset V) (r : V) (hr : r ∈ S) (x : ∀ i, X i) :
    (if Causalean.Stat.RandomGraph.IsComponent (M.graph x) S
      then (1 : ℝ) else 0) ≤
    Causalean.Stat.RandomGraph.rootTreeWitnessCount M
      (fun _ => Set.univ) r (S.erase r) x := by
  classical
  cases Subsingleton.elim (inferInstance : DecidableEq V) (Classical.decEq V)
  have hrecover : insert r (S.erase r) = S := Finset.insert_erase hr
  have hnonneg (P : Causalean.Stat.RandomGraph.ParentEncoding
      ↥(insert r (S.erase r)) ⟨r, Finset.mem_insert_self r _⟩) :
      0 ≤ (if P.Valid ∧ x ∈ Causalean.Stat.RandomGraph.partialTreeEvent
        (Causalean.Stat.RandomGraph.selectedEmbedding _) P Set.univ
        M.edgeEvent Finset.univ then (1 : ℝ) else 0) := by
    split_ifs <;> norm_num
  by_cases hc : Causalean.Stat.RandomGraph.IsComponent (M.graph x) S
  · rw [if_pos hc]
    have hc' : x ∈ Causalean.Stat.RandomGraph.componentEvent
        M {r} (fun _ => Set.univ) (insert r (S.erase r)) := by
      refine ⟨?_, r, by simp, by simp, Set.mem_univ _⟩
      simpa only [hrecover] using hc
    obtain ⟨r', hr', hrS, P, hP⟩ :=
      Causalean.Stat.RandomGraph.component_event_parent_cover
        M {r} (fun _ => Set.univ) _ x hc'
    have he : r' = r := Finset.mem_singleton.mp hr'
    subst r'
    unfold Causalean.Stat.RandomGraph.rootTreeWitnessCount
    dsimp only
    have ht : (if P.Valid ∧ x ∈ Causalean.Stat.RandomGraph.partialTreeEvent
        (Causalean.Stat.RandomGraph.selectedEmbedding _) P Set.univ
        M.edgeEvent Finset.univ then (1 : ℝ) else 0) = 1 :=
      if_pos hP
    conv_lhs => rw [← ht]
    exact Finset.single_le_sum (fun Q _ => hnonneg Q) (Finset.mem_univ P)
  · rw [if_neg hc]
    unfold Causalean.Stat.RandomGraph.rootTreeWitnessCount
    exact Finset.sum_nonneg (fun P _ => hnonneg P)

/-- [With all roots eligible, the library event is exactly the actual component event. [the stated conclusion](goal) holds. -/
-- @node: cell_componentEvent_eq
lemma cell_componentEvent_eq {n : ℕ} (k : ℕ) (S : Finset (Fin n)) :
    Causalean.Stat.RandomGraph.componentEvent (cellCoordinateGraph n k)
      Finset.univ (fun _ => Set.univ) S =
      {x | Causalean.Stat.RandomGraph.IsComponent (originalRecordSignGraph k x) S} := by
  ext x
  constructor
  · exact fun h => h.1
  · intro hc
    obtain ⟨r⟩ := hc.1.nonempty
    exact ⟨hc, r.val, Finset.mem_univ _, r.property, Set.mem_univ _⟩

/-- The event that a selected vertex set is an actual component is measurable. [the stated conclusion](goal) holds. -/
-- @node: cell_component_event_measurable
lemma cell_component_event_measurable {n : ℕ} (k : ℕ) (S : Finset (Fin n)) :
    MeasurableSet {x | Causalean.Stat.RandomGraph.IsComponent
      (originalRecordSignGraph k x) S} := by
  rw [← cell_componentEvent_eq]
  exact Causalean.Stat.RandomGraph.measurableSet_componentEvent
    (cellCoordinateGraph n k) Finset.univ (fun _ => Set.univ) S
    (fun _ => MeasurableSet.univ)

/-- The indicator of a component event is bounded and integrable. [the stated conclusion](goal) holds. -/
-- @node: cell_component_indicator_integrable
lemma cell_component_indicator_integrable {n : ℕ} (k : ℕ) (S : Finset (Fin n)) :
    Integrable (fun x => if Causalean.Stat.RandomGraph.IsComponent
      (originalRecordSignGraph k x) S then (1 : ℝ) else 0)
      (Measure.pi (fun _ : Fin n => uniformLaw)) := by
  classical
  apply (integrable_const (1 : ℝ)).mono_nonneg
  · exact (Measurable.ite (cell_component_event_measurable k S)
      measurable_const measurable_const).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun x => by split_ifs <;> norm_num)
  · exact Filter.Eventually.of_forall (fun x => by split_ifs <;> norm_num)

/-- The expected indicator of each actual component has the finite-parent tree bound. Under the stated assumptions. [The stated hypotheses](hyp:hk,hS) hold, and [the stated conclusion follows](goal). -/
-- @node: cell_component_probability_le
lemma cell_component_probability_le {n : ℕ} (k : ℕ) (hk : 1 ≤ k)
    (S : Finset (Fin n)) (hS : S.Nonempty) :
    (∫ x, (if Causalean.Stat.RandomGraph.IsComponent
      (originalRecordSignGraph k x) S then (1 : ℝ) else 0)
      ∂Measure.pi (fun _ : Fin n => uniformLaw)) ≤
      (S.card : ℝ)^(S.card-1) * (3/(k : ℝ))^(S.card-1) := by
  classical
  obtain ⟨r, hr⟩ := hS
  have hcover := integral_mono (cell_component_indicator_integrable k S)
    (Causalean.Stat.RandomGraph.integrable_rootTreeWitnessCount
      (fun _ : Fin n => uniformLaw) (cellCoordinateGraph n k)
      (fun _ => Set.univ) r (S.erase r) MeasurableSet.univ)
    (component_indicator_le_rootWitness (cellCoordinateGraph n k) S r hr)
  have hb := Causalean.Stat.RandomGraph.integral_rootTreeWitnessCount_le
    (fun _ : Fin n => uniformLaw) (cellCoordinateGraph n k)
    (fun _ => Set.univ) r (S.erase r) 1 (3/(k : ℝ)) (by norm_num) (by positivity)
    MeasurableSet.univ (by simp)
    (fun i j hij y => cell_adjacent_child_mass_le k hk y)
  apply hcover.trans
  simpa only [Finset.insert_erase hr, mul_one] using hb

/-- [The number of actual size-m components, each counted once by its vertex set. -/
-- @node: cellComponentCount
def cellComponentCount (n k m : ℕ) (x : Fin n → Covariate) : ℝ :=
  Causalean.Stat.RandomGraph.labeledComponentCount (cellCoordinateGraph n k)
    Finset.univ (fun _ => Set.univ) m x

/-- The literal component count equals the sum of the actual component indicators. Under the stated assumptions. [The stated conclusion follows](goal). -/
-- @node: cellComponentCount_eq
lemma cellComponentCount_eq (n k m : ℕ) (x : Fin n → Covariate) :
    cellComponentCount n k m x = ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
      if Causalean.Stat.RandomGraph.IsComponent (originalRecordSignGraph k x) S
        then (1 : ℝ) else 0 := by
  unfold cellComponentCount Causalean.Stat.RandomGraph.labeledComponentCount
  simp_rw [cell_componentEvent_eq]
  rfl

/-- [Expected size-m components obey the precise unrooted subset coefficient.](goal) Under [the stated assumptions](hyp:hk,hm). -/
-- @node: cellComponentCount_integral_le
lemma cellComponentCount_integral_le (n k m : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m) :
    (∫ x, cellComponentCount n k m x ∂Measure.pi (fun _ : Fin n => uniformLaw)) ≤
      (n.choose m : ℝ) * (m : ℝ)^(m-1) * (3/(k : ℝ))^(m-1) := by
  simp_rw [cellComponentCount_eq]
  rw [integral_finsetSum _ (fun S _ => cell_component_indicator_integrable k S)]
  calc
    _ ≤ ∑ _S ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
        (m : ℝ)^(m-1) * (3/(k : ℝ))^(m-1) := by
      apply Finset.sum_le_sum
      intro S hS
      have hcard := (Finset.mem_powersetCard.mp hS).2
      have hnonempty : S.Nonempty := Finset.card_pos.mp (by omega)
      simpa only [hcard] using cell_component_probability_le k hk S hnonempty
    _ = _ := by simp; ring

/-- [The finite weighted count of all non-singleton components. Sizes above n contribute zero. -/
-- @node: cellComponentWeight
def cellComponentWeight (n k : ℕ) (B : ℝ) (x : Fin n → Covariate) : ℝ :=
  ∑ j ∈ Finset.range n, ((j+2 : ℕ) : ℝ)^4 * B^(j+2) *
    cellComponentCount n k (j+2) x

/-- The weighted component count is an integrable statistic of the original covariates. [the stated conclusion](goal) holds. -/
-- @node: cellComponentWeight_integrable
lemma cellComponentWeight_integrable (n k : ℕ) (B : ℝ) :
    Integrable (cellComponentWeight n k B) (Measure.pi (fun _ : Fin n => uniformLaw)) := by
  unfold cellComponentWeight cellComponentCount
  apply integrable_finsetSum
  intro j hj
  exact (Causalean.Stat.RandomGraph.integrable_labeledComponentCount
    (fun _ : Fin n => uniformLaw) (cellCoordinateGraph n k)
    Finset.univ (fun _ => Set.univ) (j+2) (fun _ => MeasurableSet.univ)).const_mul _

/-- The weighted spanning-tree envelope applies to the actual original-covariate graph. Under the stated assumptions. [The stated hypotheses](hyp:hk,hB) hold, and [the stated conclusion follows](goal). -/
-- @node: cellComponentWeight_integral_tree_le
lemma cellComponentWeight_integral_tree_le (n k : ℕ) (hk : 1 ≤ k)
    (B : ℝ) (hB : 0 ≤ B) :
    (∫ x, cellComponentWeight n k B x ∂Measure.pi (fun _ : Fin n => uniformLaw)) ≤
      ∑ j ∈ Finset.range n,
        ((j+2 : ℕ) : ℝ)^4 * B^(j+2) * (n.choose (j+2) : ℝ) *
          ((j+2 : ℕ) : ℝ)^(j+1) * (3/(k : ℝ))^(j+1) := by
  unfold cellComponentWeight
  rw [integral_finsetSum]
  · apply Finset.sum_le_sum
    intro j hj
    rw [integral_const_mul]
    have hb := mul_le_mul_of_nonneg_left
      (cellComponentCount_integral_le n k (j+2) hk (by omega))
      (show 0 ≤ ((j+2 : ℕ) : ℝ)^4 * B^(j+2) by positivity)
    simpa only [show j+2-1 = j+1 by omega, mul_assoc] using hb
  · intro j hj
    exact (Causalean.Stat.RandomGraph.integrable_labeledComponentCount
      (fun _ : Fin n => uniformLaw) (cellCoordinateGraph n k)
      Finset.univ (fun _ => Set.univ) (j+2) (fun _ => MeasurableSet.univ)).const_mul _

/-- [At the prescribed occupancy threshold, actual components have quadratic expected weight.](goal) Under [the stated assumptions](hyp:hk). Under [the stated assumptions](hyp:hnk). -/
-- @node: cellComponentWeight_integral_eight_le
lemma cellComponentWeight_integral_eight_le (n k : ℕ) (hk : 1 ≤ k)
    (hnk : (n : ℝ) / (k : ℝ) ≤ 1 / (96 * Real.exp 1)) :
    (∫ x, cellComponentWeight n k 8 x ∂Measure.pi (fun _ : Fin n => uniformLaw)) ≤
      96*Real.exp 2*8^2*(n : ℝ)^2/(k : ℝ) := by
  exact (cellComponentWeight_integral_tree_le n k hk 8 (by norm_num)).trans
    (mixture_tree_sum_eight_bound n k n hk hnk)

/-- [Counting component supports by size agrees with counting the graph quotient.
The finite powerset representation supplies a measurable statistic despite the
sample-dependent type of connected components. [the documented result](goal) -/
-- @node: cellComponentCount_eq_components
lemma cellComponentCount_eq_components (n k m : ℕ) (x : Fin n → Covariate) :
    cellComponentCount n k m x =
      let G := originalRecordSignGraph k x
      let : Fintype G.ConnectedComponent := Fintype.ofFinite _
      ∑ c : G.ConnectedComponent,
        if c.supp.toFinset.card = m then (1 : ℝ) else 0 := by
  classical
  dsimp only
  let G := originalRecordSignGraph k x
  let : Fintype G.ConnectedComponent := Fintype.ofFinite _
  rw [cellComponentCount_eq]
  change (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
      if Causalean.Stat.RandomGraph.IsComponent G S then (1 : ℝ) else 0) = _
  rw [← Finset.sum_filter]
  symm
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun c _ => c.supp.toFinset)
  · intro c hc
    have hcard := (Finset.mem_filter.mp hc).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩, ?_⟩
    apply (Causalean.Stat.RandomGraph.isComponent_iff_exists_connectedComponent G _).mpr
    exact ⟨c, by simp⟩
  · intro c hc d hd hcd
    apply SimpleGraph.ConnectedComponent.supp_injective
    simpa using congrArg (fun S : Finset (Fin n) => (S : Set (Fin n))) hcd
  · intro S hS
    obtain ⟨c, hc⟩ := (Causalean.Stat.RandomGraph.isComponent_iff_exists_connectedComponent G S).mp
      (Finset.mem_filter.mp hS).2
    refine ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · simpa only [hc, Finset.toFinset_coe] using (Finset.mem_powersetCard.mp
        (Finset.mem_filter.mp hS).1).2
    · simp only [hc, Finset.toFinset_coe]
  · intro c hc
    rfl

/-- [The finite size sum is exactly the non-singleton weighted component sum.](goal) Under [the stated assumptions](hyp:x). -/
-- @node: cellComponentWeight_eq_components
lemma cellComponentWeight_eq_components (n k : ℕ) (B : ℝ) (x : Fin n → Covariate) :
    cellComponentWeight n k B x =
      let G := originalRecordSignGraph k x
      let : Fintype G.ConnectedComponent := Fintype.ofFinite _
      ∑ c : G.ConnectedComponent,
        if 2 ≤ c.supp.toFinset.card then
          (c.supp.toFinset.card : ℝ)^4 * B^c.supp.toFinset.card else 0 := by
  classical
  dsimp only
  let G := originalRecordSignGraph k x
  let : Fintype G.ConnectedComponent := Fintype.ofFinite _
  unfold cellComponentWeight
  simp_rw [cellComponentCount_eq_components, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  have hcard : c.supp.toFinset.card ≤ n := by
    simpa using Finset.card_le_card (Finset.subset_univ c.supp.toFinset)
  by_cases htwo : 2 ≤ c.supp.toFinset.card
  · rw [if_pos htwo]
    rw [Finset.sum_eq_single (c.supp.toFinset.card-2)]
    · rw [Nat.sub_add_cancel htwo]
      simp only [ite_true, mul_one]
    · intro j hj hne
      have hjne : c.supp.toFinset.card ≠ j+2 := by omega
      simp only [if_neg hjne, mul_zero]
    · intro hnot
      have hmem : c.supp.toFinset.card-2 ∈ Finset.range n := by
        rw [Finset.mem_range]
        omega
      exact (hnot hmem).elim
  · rw [if_neg htwo]
    apply Finset.sum_eq_zero
    intro j hj
    have hjne : c.supp.toFinset.card ≠ j+2 := by omega
    simp only [if_neg hjne, mul_zero]

/-- [The complete component Taylor coefficient integrates to the paper's explicit
mixture constant, for either amplitude product. [the documented result](goal) Under [the stated assumptions](hyp:hnk). Under [the stated assumptions](hyp:hk). -/
-- @node: mixture_weighted_component_integral_bound
lemma mixture_weighted_component_integral_bound (n k : ℕ) (hk : 1 ≤ k)
    (hnk : (n : ℝ) / (k : ℝ) ≤ 1 / (96 * Real.exp 1)) (M ω : ℝ) :
    M^4 * ω^2 *
        (∫ x, cellComponentWeight n k 8 x ∂Measure.pi (fun _ : Fin n => uniformLaw)) ≤
      (96 * Real.exp 2 * 8^2 * M^4) * (n : ℝ)^2 / (k : ℝ) * ω^2 := by
  apply (mul_le_mul_of_nonneg_left (cellComponentWeight_integral_eight_le n k hk hnk)
    (show 0 ≤ M^4 * ω^2 by positivity)).trans_eq
  ring

end CausalSmith.Stat.LogoddsLowsmoothFrontier
