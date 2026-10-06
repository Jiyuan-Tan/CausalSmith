module
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.ComponentCounting
/-! General labeled spanning-tree assembly for the shared-sign component count.
A component induces a connected graph. Enumerating its vertices identifies a spanning tree
on `Fin s`; a finite union bound then applies the published Cayley count. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace CausalSmith.Stat.PrivateCateRoughdesign

/-- The induced graph on any selected component is connected, with no size restriction.  [the theorem's stated inputs and assumptions](hyp:C,hC), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,n,x). -/
-- @node: orderedComponent_induce_connected
lemma orderedComponent_induce_connected (hL : ℝ) (n : ℕ) (x : Fin n → Covariate)
    (C : Finset (Fin n)) (hC : C ∈ orderedComponents hL n x) :
    ((sharedGraph hL n x).induce (C : Set (Fin n))).Connected := by
  classical
  obtain ⟨r, _, hr⟩ := (mem_orderedComponents hL n x C).mp hC
  have hs : ((sharedGraph hL n x).connectedComponentMk r).supp = (C : Set (Fin n)) := by
    ext i
    rw [← hr]
    simp only [Finset.mem_coe, mem_componentVertices,
      SimpleGraph.ConnectedComponent.mem_supp_iff,
      SimpleGraph.ConnectedComponent.eq, SimpleGraph.reachable_comm]
  have h := ((sharedGraph hL n x).connectedComponentMk r).connected_toSimpleGraph
  change ((sharedGraph hL n x).induce
    ((sharedGraph hL n x).connectedComponentMk r).supp).Connected at h
  rw [hs] at h
  exact h

/-- The event that all edges of a specified labeled tree share signs on selected coordinates.
Extra graph edges and all isolation requirements are deliberately discarded. -/
-- @node: labeledSharedTreeEvent
def labeledSharedTreeEvent (hL : ℝ) (n s : ℕ) (e : Fin s → Fin n)
    (T : SimpleGraph (Fin s)) : Set (Fin n → Covariate) :=
  {x | ∀ i j, T.Adj i j → sharedAdj hL n x (e i) (e j)}

/-- A specified labeled-tree event is Borel because it is a finite intersection of edge events.  [the theorem's stated inputs and assumptions](hyp:T), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,n,s,e). -/
-- @node: measurableSet_labeledSharedTreeEvent
lemma measurableSet_labeledSharedTreeEvent (hL : ℝ) (n s : ℕ) (e : Fin s → Fin n)
    (T : SimpleGraph (Fin s)) : MeasurableSet (labeledSharedTreeEvent hL n s e T) := by
  classical
  change MeasurableSet {x : Fin n → Covariate |
    ∀ i j, T.Adj i j → sharedAdj hL n x (e i) (e j)}
  simp_rw [ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  by_cases h : T.Adj i j
  · simpa [h] using measurableSet_sharedAdj hL n (e i) (e j)
  · simp [h]

/-- For any fixed enumeration of a component, a labeled spanning tree exists in that
component's graph. The enumeration is fixed before taking probabilities.  [the theorem's stated inputs and assumptions](hyp:C,e,x,hC), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,n,s). -/
-- @node: orderedComponent_contains_labeled_tree
lemma orderedComponent_contains_labeled_tree (hL : ℝ) (n s : ℕ)
    (C : Finset (Fin n)) (e : Fin s ≃ C) (x : Fin n → Covariate)
    (hC : C ∈ orderedComponents hL n x) :
    ∃ T : {T : SimpleGraph (Fin s) // T.IsTree},
      x ∈ labeledSharedTreeEvent hL n s (fun i => (e i).val) T.val := by
  classical
  let G := (sharedGraph hL n x).induce (C : Set (Fin n))
  have hG : G.Connected := orderedComponent_induce_connected hL n x C hC
  have hGe : (G.comap e).Connected := (SimpleGraph.Iso.comap e G).connected_iff.mpr hG
  obtain ⟨T, hle, ht⟩ := hGe.exists_isTree_le
  refine ⟨⟨T, ht⟩, ?_⟩
  intro i j hij
  exact hle hij

/-- The component event is contained in the union over all labeled trees on its fixed
vertex enumeration. This inclusion also covers singleton components.  [the theorem's stated inputs and assumptions](hyp:C,e), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,n,s). -/
-- @node: fixed_component_subset_labeled_tree_union
lemma fixed_component_subset_labeled_tree_union (hL : ℝ) (n s : ℕ)
    (C : Finset (Fin n)) (e : Fin s ≃ C) :
    {x : Fin n → Covariate | C ∈ orderedComponents hL n x} ⊆
      ⋃ T : {T : SimpleGraph (Fin s) // T.IsTree},
        labeledSharedTreeEvent hL n s (fun i => (e i).val) T.val := by
  intro x hx
  obtain ⟨T, ht⟩ := orderedComponent_contains_labeled_tree hL n s C e x hx
  exact Set.mem_iUnion.mpr ⟨T, ht⟩

/-- A common probability envelope for specified labeled trees gives the component
probability bound by the finite union bound and the explicit Cayley gate. The result uses [the stated assumptions](hyp:hL,hs,b,hb) and establishes [the displayed conclusion](goal). -/
-- @node: fixed_component_measure_le_cayley_mul
lemma fixed_component_measure_le_cayley_mul (cayley : CayleyLabeledTreeCount)
    (hL : ℝ) (n s : ℕ) (hs : 2 ≤ s) (C : Finset (Fin n)) (e : Fin s ≃ C)
    (μ : Measure (Fin n → Covariate)) (b : ℝ≥0∞)
    (hb : ∀ T : {T : SimpleGraph (Fin s) // T.IsTree},
      μ (labeledSharedTreeEvent hL n s (fun i => (e i).val) T.val) ≤ b) :
    μ {x | C ∈ orderedComponents hL n x} ≤ (s ^ (s - 2) : ℕ) * b := by
  classical
  let := Fintype.ofFinite {T : SimpleGraph (Fin s) // T.IsTree}
  calc
    _ ≤ μ (⋃ T : {T : SimpleGraph (Fin s) // T.IsTree},
        labeledSharedTreeEvent hL n s (fun i => (e i).val) T.val) :=
      measure_mono (fixed_component_subset_labeled_tree_union hL n s C e)
    _ ≤ ∑' T : {T : SimpleGraph (Fin s) // T.IsTree},
        μ (labeledSharedTreeEvent hL n s (fun i => (e i).val) T.val) :=
      measure_iUnion_le _
    _ ≤ ∑' _T : {T : SimpleGraph (Fin s) // T.IsTree}, b := ENNReal.tsum_le_tsum hb
    _ = _ := by
      rw [tsum_fintype]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← Nat.card_eq_fintype_card, cayley s hs]

/-- The general size-s count assembly: a specified-tree envelope, on arbitrary distinct
sample coordinates, implies the binomial Cayley estimate for the actual component count.
The tree probability estimate remains an explicit input here, rather than a
paper-theorem premise. The result uses [the stated assumptions](hyp:hL,hs,b,hb) and establishes [the displayed conclusion](goal). -/
-- @node: lintegral_sizeComponentCount_le_of_labeled_tree_bound
lemma lintegral_sizeComponentCount_le_of_labeled_tree_bound
    (cayley : CayleyLabeledTreeCount) (hL : ℝ) (n s : ℕ) (hs : 2 ≤ s)
    (μ : Measure (Fin n → Covariate)) (b : ℝ≥0∞)
    (hb : ∀ (e : Fin s → Fin n), Function.Injective e →
      ∀ T : {T : SimpleGraph (Fin s) // T.IsTree},
        μ (labeledSharedTreeEvent hL n s e T.val) ≤ b) :
    (∫⁻ x, (sizeComponentCount hL n x s : ℝ≥0∞) ∂μ) ≤
      (n.choose s : ℝ≥0∞) * (s ^ (s - 2) : ℕ) * b := by
  classical
  rw [mul_assoc]
  apply lintegral_sizeComponentCount_le_choose_mul
  intro C hC
  let e : Fin s ≃ C := (Finset.equivFinOfCardEq hC).symm
  apply fixed_component_measure_le_cayley_mul cayley hL n s hs C e μ b
  apply hb
  intro i j hij
  exact e.injective (Subtype.ext hij)

/-- Selecting distinct coordinates pulls a labeled-tree event back from its own vertex
space; neither extra vertices nor unused coordinates add restrictions.  [the theorem's stated inputs and assumptions](hyp:he,T), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,n,s,e). -/
-- @node: labeledSharedTreeEvent_eq_preimage
lemma labeledSharedTreeEvent_eq_preimage (hL : ℝ) (n s : ℕ) (e : Fin s → Fin n)
    (he : Function.Injective e) (T : SimpleGraph (Fin s)) :
    labeledSharedTreeEvent hL n s e T =
      (fun x i => x (e i)) ⁻¹' labeledSharedTreeEvent hL s s id T := by
  ext x
  constructor
  · intro hx i j hij
    obtain ⟨_, hsign⟩ := hx i j hij
    exact ⟨hij.ne, hsign⟩
  · intro hx i j hij
    obtain ⟨hne, hsign⟩ := hx i j hij
    exact ⟨fun h => hne (he h), hsign⟩

/-- The probability of a labeled-tree event on arbitrary distinct sample coordinates
is exactly its probability under the smaller iid uniform design.  [the theorem's stated inputs and assumptions](hyp:e,he,T), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,n,s). -/
-- @node: labeledSharedTreeEvent_uniform_volume_eq
lemma labeledSharedTreeEvent_uniform_volume_eq (hL : ℝ) (n s : ℕ)
    (e : Fin s → Fin n) (he : Function.Injective e) (T : SimpleGraph (Fin s)) :
    (Measure.pi (fun _ : Fin n => (volume : Measure Covariate)))
      (labeledSharedTreeEvent hL n s e T) =
    (Measure.pi (fun _ : Fin s => (volume : Measure Covariate)))
      (labeledSharedTreeEvent hL s s id T) := by
  rw [labeledSharedTreeEvent_eq_preimage hL n s e he T]
  exact uniform_covariate_injection_preimage n s e he _
    (measurableSet_labeledSharedTreeEvent hL s s id T)

/-- The roadmap's general component-count bound follows from specified-tree probabilities
on their own vertex spaces. Cayley and coordinate selection supply all the assembly factors. The result uses [the stated assumptions](hyp:hL,hs,htree) and establishes [the displayed conclusion](goal). -/
-- @node: lintegral_sizeComponentCount_le_of_uniform_labeled_tree_bound
lemma lintegral_sizeComponentCount_le_of_uniform_labeled_tree_bound
    (cayley : CayleyLabeledTreeCount) (hL : ℝ)
    (n s : ℕ) (hs : 2 ≤ s)
    (htree : ∀ T : {T : SimpleGraph (Fin s) // T.IsTree},
      (Measure.pi (fun _ : Fin s => (volume : Measure Covariate)))
        (labeledSharedTreeEvent hL s s id T.val) ≤
          ENNReal.ofReal (2 * hL * (4 * deltaL hL) ^ (s - 1))) :
    (∫⁻ x, (sizeComponentCount hL n x s : ℝ≥0∞)
      ∂(Measure.pi (fun _ : Fin n => (volume : Measure Covariate)))) ≤
      ENNReal.ofReal ((n.choose s : ℝ) * 2 * hL * (s : ℝ) ^ (s - 2) *
        (4 * deltaL hL) ^ (s - 1)) := by
  have hb := lintegral_sizeComponentCount_le_of_labeled_tree_bound cayley hL n s hs
    (Measure.pi (fun _ : Fin n => (volume : Measure Covariate)))
    (ENNReal.ofReal (2 * hL * (4 * deltaL hL) ^ (s - 1)))
    (fun e he T => by rw [labeledSharedTreeEvent_uniform_volume_eq hL n s e he]; exact htree T)
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ← ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))] at hb
  convert hb using 1
  congr 1
  push_cast
  ring

/-- The actual sparse dataset coupling obeys the Hamming-cost bound once each specified
labeled tree has its geometric probability envelope. All component-count assembly is proved. The result uses [the stated assumptions](hyp:hL,hhL,hn,hcap,htree) and establishes [the displayed conclusion](goal). -/
-- @node: commonMassCoupling_hamming_cost_le_of_labeled_tree_bound
lemma commonMassCoupling_hamming_cost_le_of_labeled_tree_bound
    (cayley : CayleyLabeledTreeCount) (hL : ℝ) (hhL : 0 < hL ∧ hL ≤ 1 / 4)
    (n : ℕ) (hn : 1 ≤ n) (hcap : (n : ℝ) * deltaL hL ≤ 1 / 128)
    (htree : ∀ s : ℕ, 2 ≤ s → s ≤ n →
      ∀ T : {T : SimpleGraph (Fin s) // T.IsTree},
        (Measure.pi (fun _ : Fin s => (volume : Measure Covariate)))
          (labeledSharedTreeEvent hL s s id T.val) ≤
            ENNReal.ofReal (2 * hL * (4 * deltaL hL) ^ (s - 1))) :
    (∫⁻ zw, (dHam n zw.1 zw.2 : ℝ≥0∞) ∂commonMassCoupling hL n) ≤
      ENNReal.ofReal (1024 * separation hL * (n : ℝ) ^ 2 * hL * deltaL hL) := by
  apply commonMassCoupling_hamming_cost_le_of_tree_counts hL hhL n hn hcap
  intro i hi
  have hi' := Finset.mem_range.mp hi
  have hb := lintegral_sizeComponentCount_le_of_uniform_labeled_tree_bound
    cayley hL n (i + 2) (by omega) (htree (i + 2) (by omega) (by omega))
  convert hb using 1
  congr 1
  simp
  ring

end CausalSmith.Stat.PrivateCateRoughdesign
