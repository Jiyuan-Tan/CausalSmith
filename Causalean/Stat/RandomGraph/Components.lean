module
public import Causalean.Stat.RandomGraph.RootedTree
public import Mathlib.Data.Finset.Powerset
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Root-qualified component counts and their finite witness cover

Coordinate-local, symmetric measurable edge events define a random simple graph. Components
are counted once by their vertex sets. A component qualifies only if it contains a distinguished
root whose coordinate satisfies its root event. Its spanning-parent witnesses are enumerated
by a root, an unordered selection of remaining vertices, and a candidate parent array.

This avoids assuming edge independence: edges sharing coordinates may be dependent. The
parent witness count may overcount components and is used only as an upper bound.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace Causalean.Stat.RandomGraph

universe u v

variable {V : Type u}

/-- [Coordinate spaces](hyp:X) determine [a measurable symmetric edge-event model](hyp:edgeEvent,measurable_edgeEvent,symmetric), where an edge depends only on its two endpoint coordinates. -/
structure CoordinateGraph (X : V → Type v) [∀ i, MeasurableSpace (X i)] where
  /-- The event for an oriented pair of endpoint coordinates. -/
  edgeEvent : ∀ i j, Set (X i × X j)
  /-- Every pair event is measurable in the product endpoint space. -/
  measurable_edgeEvent : ∀ i j, MeasurableSet (edgeEvent i j)
  /-- Reversing endpoints leaves the undirected edge event unchanged. -/
  symmetric : ∀ i j (z : X i) (y : X j),
    (z, y) ∈ edgeEvent i j ↔ (y, z) ∈ edgeEvent j i

variable {X : V → Type v} [∀ i, MeasurableSpace (X i)]

/-- An [edge-event model](hyp:M) and [coordinate outcome](hyp:x) determine the
[simple graph of occurring edges](goal). -/
def CoordinateGraph.graph (M : CoordinateGraph X) (x : ∀ i, X i) : SimpleGraph V where
  Adj i j := i ≠ j ∧ (x i, x j) ∈ M.edgeEvent i j
  symm := ⟨fun i j h => ⟨h.1.symm, (M.symmetric i j (x i) (x j)).mp h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- With [finitely many vertices](hyp:V), the event that a [coordinate edge model](hyp:M)
[equals a specified graph](hyp:G) [is measurable](goal). -/
theorem CoordinateGraph.measurableSet_graph_eq [Finite V]
    (M : CoordinateGraph X) (G : SimpleGraph V) :
    MeasurableSet {x | M.graph x = G} := by
  classical
  have heq : {x | M.graph x = G} =
      ⋂ i : V, ⋂ j : V, {x | (i ≠ j ∧ (x i, x j) ∈ M.edgeEvent i j) ↔ G.Adj i j} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro h i j
      change (M.graph x).Adj i j ↔ G.Adj i j
      rw [h]
    · intro h
      ext i j
      exact h i j
  rw [heq]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  exact ((MeasurableSet.const (i ≠ j)).inter
    ((M.measurable_edgeEvent i j).preimage
      ((measurable_pi_apply i).prodMk (measurable_pi_apply j)))).iff
        (MeasurableSet.const (G.Adj i j))

/-- A [finite vertex set](hyp:S) is [a component](goal) of a [graph](hyp:G) when its induced
graph is connected and all neighbors of its vertices stay in that set. -/
def IsComponent (G : SimpleGraph V) (S : Finset V) : Prop :=
  (G.induce (S : Set V)).Connected ∧ ∀ i ∈ S, ∀ j, G.Adj i j → j ∈ S

/-- The finite-set [component predicate](hyp:G,S) [is equivalent to being the support of a
connected component in Mathlib](goal). -/
theorem isComponent_iff_exists_connectedComponent (G : SimpleGraph V) (S : Finset V) :
    IsComponent G S ↔ ∃ C : G.ConnectedComponent, C.supp = (S : Set V) := by
  constructor
  · rintro ⟨hconn, hclosed⟩
    obtain ⟨r⟩ := hconn.nonempty
    refine ⟨G.connectedComponentMk r.val, ?_⟩
    ext v
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff,
      SimpleGraph.ConnectedComponent.eq]
    constructor
    · rintro ⟨w⟩
      -- Neighbor closure propagates membership from the start of every walk.
      have hwalk : ∀ {a b : V}, G.Walk a b → a ∈ S → b ∈ S := by
        intro a b w
        induction w with
        | nil => exact id
        | cons hadj w ih => exact fun ha => ih (hclosed _ ha _ hadj)
      exact hwalk w.reverse r.property
    · intro hv
      exact (hconn.preconnected (⟨v, hv⟩ : (S : Set V)) r).map
        ⟨Subtype.val, fun h => h⟩
  · rintro ⟨C, hC⟩
    refine ⟨?_, ?_⟩
    · have hconn := C.connected_toSimpleGraph
      change (G.induce C.supp).Connected at hconn
      rwa [hC] at hconn
    · intro i hi j hadj
      have hiC : i ∈ C.supp := by simpa [hC] using hi
      simpa [hC] using C.mem_supp_of_adj_mem_supp hiC hadj

/-- The [inclusion embedding](goal) of a [selected finite vertex set](hyp:S) sends each
selected vertex to the ambient population. -/
def selectedEmbedding (S : Finset V) : S ↪ V := ⟨Subtype.val, Subtype.val_injective⟩

/-- The [qualified component event](goal) for an [edge model](hyp:M), [distinguished roots](hyp:R),
[coordinate root events](hyp:rootEvent), and [vertex set](hyp:S) requires a component containing
at least one distinguished root whose root event occurs. -/
def componentEvent (M : CoordinateGraph X) (R : Finset V)
    (rootEvent : ∀ r, Set (X r)) (S : Finset V) : Set (∀ i, X i) :=
  {x | IsComponent (M.graph x) S ∧ ∃ r ∈ R, r ∈ S ∧ x r ∈ rootEvent r}

/-- The [labeled component count](goal) for an [edge model](hyp:M), [roots](hyp:R), [root
events](hyp:rootEvent), [size](hyp:p), and [outcome](hyp:x) counts each qualifying size-p component
of the outcome's graph once, irrespective of how many qualifying roots it contains. -/
def labeledComponentCount [Fintype V] (M : CoordinateGraph X) (R : Finset V)
    (rootEvent : ∀ r, Set (X r)) (p : ℕ) (x : ∀ i, X i) : ℝ := by
  classical
  exact ∑ S ∈ (Finset.univ : Finset V).powersetCard p,
    if x ∈ componentEvent M R rootEvent S then (1 : ℝ) else 0

/-- The [rooted witness count](goal) on a [root and completion set](hyp:r,T) sums the
occurring valid parent-array events for an [edge model](hyp:M), [root events](hyp:rootEvent),
and [outcome](hyp:x). -/
def rootTreeWitnessCount (M : CoordinateGraph X) (rootEvent : ∀ r, Set (X r))
    (r : V) (T : Finset V) (x : ∀ i, X i) : ℝ := by
  classical
  let s : Finset V := insert r T
  let root : s := ⟨r, Finset.mem_insert_self r T⟩
  exact ∑ P : ParentEncoding s root,
    if P.Valid ∧ x ∈ partialTreeEvent (selectedEmbedding s) P
      (rootEvent r) M.edgeEvent Finset.univ then (1 : ℝ) else 0

/-- The [total witness count](goal) enumerates [distinguished roots](hyp:R), unordered
selections of p minus one other vertices, and parent arrays, for an [edge model](hyp:M),
[root events](hyp:rootEvent), [size](hyp:p), and [outcome](hyp:x). -/
def treeWitnessCount [Fintype V] [DecidableEq V] (M : CoordinateGraph X) (R : Finset V)
    (rootEvent : ∀ r, Set (X r)) (p : ℕ) (x : ∀ i, X i) : ℝ :=
  ∑ r ∈ R, ∑ T ∈ ((Finset.univ : Finset V).erase r).powersetCard (p - 1),
    rootTreeWitnessCount M rootEvent r T x

/-- For an [edge model](hyp:M), [distinguished roots](hyp:R), [root events](hyp:rootEvent), a
[vertex set](hyp:S), and an [outcome](hyp:x), whenever [the vertex set is a qualifying component at
that outcome](hyp:hcomponent), [some distinguished root in the set whose root event occurs carries
a valid parent encoding of the set, rooted there, all of whose edge events occur](goal). -/
theorem component_event_parent_cover [DecidableEq V] (M : CoordinateGraph X) (R : Finset V)
    (rootEvent : ∀ r, Set (X r)) (S : Finset V) (x : ∀ i, X i)
    (hcomponent : x ∈ componentEvent M R rootEvent S) :
    ∃ r ∈ R, ∃ hr : r ∈ S, ∃ P : ParentEncoding S (⟨r, hr⟩ : S),
      P.Valid ∧ x ∈ partialTreeEvent (selectedEmbedding S) P
        (rootEvent r) M.edgeEvent Finset.univ := by
  classical
  obtain ⟨hS, r, hrR, hrS, hroot⟩ := hcomponent
  obtain ⟨P, hP, hadj, _⟩ := rooted_spanning_parent_cover
    ((M.graph x).induce (S : Set V)) hS.1 (⟨r, hrS⟩ : S)
  refine ⟨r, hrR, hrS, P, hP, hroot, ?_⟩
  intro v _
  exact (hadj v).2

/-- For an [edge model](hyp:M), [distinguished roots](hyp:R), [root events](hyp:rootEvent), and a
[component size](hyp:p) that is [at least one](hyp:hp), [the labeled component count is at most the
total rooted witness count](goal) at every [outcome](hyp:x). -/
theorem labeledComponentCount_le_treeWitnessCount [Fintype V] [DecidableEq V]
    (M : CoordinateGraph X) (R : Finset V)
    (rootEvent : ∀ r, Set (X r)) (p : ℕ) (hp : 1 ≤ p) (x : ∀ i, X i) :
    labeledComponentCount M R rootEvent p x ≤ treeWitnessCount M R rootEvent p x := by
  classical
  -- Use the same equality decision procedure as the dependent witness-count definition.
  cases Subsingleton.elim (inferInstance : DecidableEq V) (Classical.decEq V)
  let source := ((Finset.univ : Finset V).powersetCard p).filter
    (fun S => x ∈ componentEvent M R rootEvent S)
  let A := {S : Finset V // S ∈ source}
  have hA (S : A) : S.val.card = p ∧ x ∈ componentEvent M R rootEvent S.val := by
    have h := Finset.mem_filter.mp S.property
    exact ⟨(Finset.mem_powersetCard.mp h.1).2, h.2⟩
  let root (S : A) : V :=
    (component_event_parent_cover M R rootEvent S.val x (hA S).2).choose
  have hroot (S : A) : root S ∈ R ∧ ∃ hr : root S ∈ S.val,
      ∃ P : ParentEncoding S.val (⟨root S, hr⟩ : S.val),
        P.Valid ∧ x ∈ partialTreeEvent (selectedEmbedding S.val) P
          (rootEvent (root S)) M.edgeEvent Finset.univ :=
    (component_event_parent_cover M R rootEvent S.val x (hA S).2).choose_spec
  let slots := R.sigma (fun r => ((Finset.univ : Finset V).erase r).powersetCard (p - 1))
  let e (S : A) : Σ _ : V, Finset V := ⟨root S, S.val.erase (root S)⟩
  -- Reinsert the chosen root to recover the component, proving slot injectivity.
  have hrecover (S : A) : insert (root S) (S.val.erase (root S)) = S.val :=
    Finset.insert_erase (hroot S).2.choose
  have hinj : Function.Injective e := by
    intro S U h
    apply Subtype.ext
    calc
      S.val = insert (e S).1 (e S).2 := (hrecover S).symm
      _ = insert (e U).1 (e U).2 := congrArg (fun q => insert q.1 q.2) h
      _ = U.val := hrecover U
  have hslot (S : A) : e S ∈ slots := by
    refine Finset.mem_sigma.mpr ⟨(hroot S).1, Finset.mem_powersetCard.mpr ⟨?_, ?_⟩⟩
    · intro v hv
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hv).1, Finset.mem_univ v⟩
    · rw [Finset.card_erase_of_mem (hroot S).2.choose, (hA S).1]
  -- Every parent-array summand is nonnegative, and the selected witness contributes one.
  have hnonneg (r : V) (T : Finset V) : 0 ≤ rootTreeWitnessCount M rootEvent r T x := by
    unfold rootTreeWitnessCount
    exact Finset.sum_nonneg fun P _ => by split_ifs <;> norm_num
  have hone (S : A) : 1 ≤ rootTreeWitnessCount M rootEvent (root S)
      (S.val.erase (root S)) x := by
    -- Transport the witness before unfolding the sum over its dependent parent type.
    have hex (s : Finset V) (hs : s = S.val) : ∃ hr : root S ∈ s,
        ∃ P : ParentEncoding s (⟨root S, hr⟩ : s),
          P.Valid ∧ x ∈ partialTreeEvent (selectedEmbedding s) P
            (rootEvent (root S)) M.edgeEvent Finset.univ := by
      subst s
      exact (hroot S).2
    obtain ⟨hr, P, hP⟩ := hex _ (hrecover S)
    unfold rootTreeWitnessCount
    dsimp only
    have hterm : (if P.Valid ∧ x ∈ partialTreeEvent
        (selectedEmbedding (insert (root S) (S.val.erase (root S)))) P
        (rootEvent (root S)) M.edgeEvent Finset.univ then (1 : ℝ) else 0) = 1 :=
      if_pos hP
    conv_lhs => rw [← hterm]
    exact Finset.single_le_sum
      (f := fun Q : ParentEncoding ↥(insert (root S) (S.val.erase (root S))) ⟨root S, hr⟩ =>
        if Q.Valid ∧ x ∈ partialTreeEvent
          (selectedEmbedding (insert (root S) (S.val.erase (root S)))) Q
          (rootEvent (root S)) M.edgeEvent Finset.univ then (1 : ℝ) else 0)
      (fun Q _ => by split_ifs <;> norm_num) (Finset.mem_univ P)
  have hcount : labeledComponentCount M R rootEvent p x = ∑ _S : A, (1 : ℝ) := by
    unfold labeledComponentCount
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype source (fun _ => Iff.rfl) (fun _ => (1 : ℝ))
  rw [hcount]
  change (∑ _S : A, (1 : ℝ)) ≤ ∑ r ∈ R,
    ∑ T ∈ ((Finset.univ : Finset V).erase r).powersetCard (p - 1),
      rootTreeWitnessCount M rootEvent r T x
  rw [Finset.sum_sigma']
  let g (q : Σ _ : V, Finset V) : ℝ := rootTreeWitnessCount M rootEvent q.1 q.2 x
  calc
    (∑ _S : A, (1 : ℝ)) ≤ ∑ S : A, g (e S) :=
      Finset.sum_le_sum (fun S _ => hone S)
    _ = ∑ q ∈ Finset.univ.image e, g q :=
      (Finset.sum_image (fun _ _ _ _ h => hinj h)).symm
    _ ≤ ∑ q ∈ slots, g q := Finset.sum_le_sum_of_subset_of_nonneg
      (by intro q hq; obtain ⟨S, _, rfl⟩ := Finset.mem_image.mp hq; exact hslot S)
      (fun q _ _ => hnonneg q.1 q.2)

/-- A [qualified component event](hyp:M,R,rootEvent,S) [is measurable](goal) when the
[coordinate root events are measurable](hyp:hroot). -/
theorem measurableSet_componentEvent [Finite V] (M : CoordinateGraph X) (R : Finset V)
    (rootEvent : ∀ r, Set (X r)) (S : Finset V)
    (hroot : ∀ r, MeasurableSet (rootEvent r)) :
    MeasurableSet (componentEvent M R rootEvent S) := by
  classical
  have hgraph : {x | IsComponent (M.graph x) S} =
      ⋃ G : SimpleGraph V, {x | M.graph x = G} ∩ {x | IsComponent G S} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨M.graph x, rfl, h⟩
    · rintro ⟨G, hG, h⟩
      simpa only [hG] using h
  have hgraphMeas : MeasurableSet {x | IsComponent (M.graph x) S} := by
    rw [hgraph]
    exact MeasurableSet.iUnion fun G =>
      (M.measurableSet_graph_eq G).inter (MeasurableSet.const (IsComponent G S))
  have hroots : {x : ∀ i, X i | ∃ r ∈ R, r ∈ S ∧ x r ∈ rootEvent r} =
      ⋃ r ∈ R, {x : ∀ i, X i | r ∈ S} ∩ {x | x r ∈ rootEvent r} := by
    ext x
    simp [and_left_comm]
  change MeasurableSet ({x | IsComponent (M.graph x) S} ∩
    {x | ∃ r ∈ R, r ∈ S ∧ x r ∈ rootEvent r})
  rw [hroots]
  exact hgraphMeas.inter (R.measurableSet_biUnion fun r hr =>
    (MeasurableSet.const (r ∈ S)).inter
      ((hroot r).preimage (measurable_pi_apply r)))

/-- The [finite component count](hyp:M,R,rootEvent,p) [is measurable](goal) for
[measurable coordinate root events](hyp:hroot). -/
@[fun_prop]
theorem measurable_labeledComponentCount [Fintype V] (M : CoordinateGraph X) (R : Finset V)
    (rootEvent : ∀ r, Set (X r)) (p : ℕ) (hroot : ∀ r, MeasurableSet (rootEvent r)) :
    Measurable (labeledComponentCount M R rootEvent p) := by
  classical
  unfold labeledComponentCount
  apply Finset.measurable_sum
  intro S hS
  apply Measurable.ite (measurableSet_componentEvent M R rootEvent S hroot)
    measurable_const measurable_const

/-- The [component count](hyp:M,R,rootEvent,p,x) [lies between zero and the number of
size-p subsets of the population](goal). -/
theorem labeledComponentCount_bounds [Fintype V] (M : CoordinateGraph X) (R : Finset V)
    (rootEvent : ∀ r, Set (X r)) (p : ℕ) (x : ∀ i, X i) :
    0 ≤ labeledComponentCount M R rootEvent p x ∧
      labeledComponentCount M R rootEvent p x ≤ (Nat.choose (Fintype.card V) p : ℝ) := by
  classical
  unfold labeledComponentCount
  constructor
  · exact Finset.sum_nonneg fun S _ => by
      by_cases h : x ∈ componentEvent M R rootEvent S <;> simp [h]
  · calc
      (∑ S ∈ (Finset.univ : Finset V).powersetCard p,
        if x ∈ componentEvent M R rootEvent S then (1 : ℝ) else 0) ≤
          ∑ _S ∈ (Finset.univ : Finset V).powersetCard p, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro S hS
            by_cases h : x ∈ componentEvent M R rootEvent S <;> simp [h]
      _ = (Nat.choose (Fintype.card V) p : ℝ) := by simp

/-- The [finite component count](hyp:M,R,rootEvent,p) [is integrable](goal) under
[coordinate probability laws](hyp:μ), for [measurable root events](hyp:hroot). -/
theorem integrable_labeledComponentCount [Fintype V]
    (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (M : CoordinateGraph X) (R : Finset V) (rootEvent : ∀ r, Set (X r)) (p : ℕ)
    (hroot : ∀ r, MeasurableSet (rootEvent r)) :
    Integrable (labeledComponentCount M R rootEvent p) (Measure.pi μ) := by
  exact (integrable_const (Nat.choose (Fintype.card V) p : ℝ)).mono_nonneg
    (measurable_labeledComponentCount M R rootEvent p hroot).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => (labeledComponentCount_bounds M R rootEvent p x).1)
    (Filter.Eventually.of_forall fun x => (labeledComponentCount_bounds M R rootEvent p x).2)

end Causalean.Stat.RandomGraph

