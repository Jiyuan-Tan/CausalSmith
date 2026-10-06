module
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.MeasureTheory.Integral.Marginal

/-!
# Finite rooted-tree events under product measures

This module encodes finite rooted spanning trees as parent functions and proves their
product-measure event bound by successive leaf elimination. It is independent of a particular
random-graph model: an injectively embedded finite tree, measurable root and edge events, and
uniform child-coordinate section bounds are sufficient.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace Causalean.Stat.RandomGraph

universe u v w

/-- A [vertex type](hyp:V) and [root](hyp:r) determine the [candidate parent encodings](goal):
one vertex-valued parent choice for each nonroot vertex. -/
abbrev ParentEncoding (V : Type u) (r : V) : Type u := {v : V // v ≠ r} → V

variable {V : Type u} {r : V}

/-- A [parent encoding](hyp:P) is [valid](goal) when a natural-number height is zero at the
root and strictly decreases along every parent edge. -/
def ParentEncoding.Valid (P : ParentEncoding V r) : Prop :=
  ∃ height : V → ℕ, height r = 0 ∧ ∀ v, height (P v) < height v.val

/-- The [parent step](goal) for an [encoding](hyp:P) fixes the root and sends every other
[vertex](hyp:v) to its chosen parent. -/
def ParentEncoding.step [DecidableEq V] (P : ParentEncoding V r) (v : V) : V :=
  if h : v = r then r else P ⟨v, h⟩

/-- The [undirected graph](goal) of a [parent encoding](hyp:P) joins distinct vertices when
one is the chosen parent of the other. -/
def ParentEncoding.graph (P : ParentEncoding V r) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ((∃ h : u ≠ r, P ⟨u, h⟩ = v) ∨
    (∃ h : v ≠ r, P ⟨v, h⟩ = u))
  symm := by
    constructor
    intro u v h
    exact ⟨h.1.symm, h.2.symm⟩
  loopless := by
    constructor
    intro v h
    exact h.1 rfl

/-- The [number of all candidate parent encodings](goal) on a finite vertex type is exactly
the number of vertices raised to one less than that number, for a [chosen root](hyp:r). -/
theorem card_parentEncoding [Fintype V] [DecidableEq V] (r : V) :
    Fintype.card (ParentEncoding V r) = Fintype.card V ^ (Fintype.card V - 1) := by
  rw [Fintype.card_fun]
  congr 1
  simp

/-- In a [valid](hyp:hP) [parent encoding](hyp:P), [no nonroot vertex](hyp:v) [is equal to its own
chosen parent](goal). -/
theorem ParentEncoding.parent_ne (P : ParentEncoding V r) (hP : P.Valid)
    (v : {v : V // v ≠ r}) : P v ≠ v.val := by
  obtain ⟨height, _, hheight⟩ := hP
  intro h
  have := hheight v
  rw [h] at this
  exact (Nat.lt_irrefl _) this

/-- Iterating the parent step in a [valid encoding](hyp:hP) [eventually reaches the root](goal)
from any [starting vertex](hyp:v). -/
theorem ParentEncoding.iterate_eq_root [DecidableEq V]
    (P : ParentEncoding V r) (hP : P.Valid) (v : V) :
    ∃ k : ℕ, (P.step)^[k] v = r := by
  obtain ⟨height, _, hheight⟩ := hP
  have arrival : ∀ n, ∀ w : V, height w = n → ∃ k : ℕ, (P.step)^[k] w = r := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro w hw
      by_cases hr : w = r
      · exact ⟨0, hr⟩
      · obtain ⟨k, hk⟩ := ih (height (P ⟨w, hr⟩)) (hw ▸ hheight ⟨w, hr⟩)
          (P ⟨w, hr⟩) rfl
        refine ⟨k + 1, ?_⟩
        simpa [Function.iterate_succ_apply, ParentEncoding.step, hr] using hk
  exact arrival (height v) v rfl

/-- The graph of a [valid parent encoding](hyp:hP) [is a tree](goal). -/
theorem ParentEncoding.isTree (P : ParentEncoding V r) (hP : P.Valid) : P.graph.IsTree := by
  classical
  have stepReach (v : V) : P.graph.Reachable v (P.step v) := by
    by_cases hv : v = r
    · simp [ParentEncoding.step, hv]
    · have ha : P.graph.Adj v (P ⟨v, hv⟩) :=
        ⟨(P.parent_ne hP ⟨v, hv⟩).symm, Or.inl ⟨hv, rfl⟩⟩
      simpa [ParentEncoding.step, hv] using ha.reachable
  have rootReach (v : V) : P.graph.Reachable v r := by
    obtain ⟨k, hk⟩ := P.iterate_eq_root hP v
    have reach : ∀ n : ℕ, ∀ w : V, P.graph.Reachable w ((P.step)^[n] w) := by
      intro n
      induction n with
      | zero => intro w; exact SimpleGraph.Reachable.refl w
      | succ n ih =>
        intro w
        rw [Function.iterate_succ_apply]
        exact (stepReach w).trans (ih (P.step w))
    simpa [hk] using reach k v
  refine ⟨?_, ?_⟩
  · have : Nonempty V := ⟨r⟩
    exact SimpleGraph.Connected.mk (fun u v => (rootReach u).trans (rootReach v).symm)
  · obtain ⟨height, _, hheight⟩ := hP
    intro v c hc
    obtain ⟨l, hl, hmax⟩ := c.support.toFinset.exists_max_image height
      ⟨v, by simp⟩
    have hlc : l ∈ c.support := List.mem_toFinset.mp hl
    let q := c.rotate l hlc
    have hq : q.IsCycle := hc.rotate hlc
    have bound (w : V) (hw : w ∈ q.support) : height w ≤ height l :=
      hmax w (List.mem_toFinset.mpr ((c.mem_support_rotate_iff l hlc).mp hw))
    -- At a maximum-height vertex, every cycle neighbor must be its chosen parent.
    have parent (w : V) (ha : P.graph.Adj l w) (hw : height w ≤ height l) :
        ∃ h : l ≠ r, P ⟨l, h⟩ = w := by
      rcases ha.2 with h | ⟨h, he⟩
      · exact h
      · have hlt := hheight ⟨w, h⟩
        rw [he] at hlt
        exact False.elim ((not_lt_of_ge hw) hlt)
    obtain ⟨hs, hes⟩ := parent q.snd (q.adj_snd hq.not_nil)
      (bound q.snd (q.getVert_mem_support 1))
    obtain ⟨hp, hep⟩ := parent q.penultimate (q.adj_penultimate hq.not_nil).symm
      (bound q.penultimate (q.getVert_mem_support (q.length - 1)))
    exact hq.snd_ne_penultimate (hes.symm.trans hep)

/-- In a [connected graph](hyp:hG), every [nonroot vertex](hyp:v) has [an adjacent vertex
exactly one step closer to the root](goal). -/
theorem exists_parent_step_closer (G : SimpleGraph V) (hG : G.Connected) (r : V)
    (v : {v : V // v ≠ r}) :
    ∃ w : V, G.Adj v.val w ∧ G.dist r w + 1 = G.dist r v.val := by
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist v.val r
  have hn := p.not_nil_of_ne v.property
  refine ⟨p.snd, p.adj_snd hn, ?_⟩
  have hlow := G.dist_le p.tail
  obtain ⟨s, hs⟩ := hG.exists_walk_length_eq_dist p.snd r
  have hupp := G.dist_le (s.cons (p.adj_snd hn))
  have hlen := p.length_tail_add_one hn
  rw [G.dist_comm] at hp hlow
  rw [SimpleGraph.Walk.length_cons, hs, G.dist_comm (u := p.snd) (v := r),
    G.dist_comm (u := v.val) (v := r)] at hupp
  omega

/-- A [connected finite graph](hyp:hG) with a [chosen root](hyp:r) [admits a valid parent
encoding using its edges, with at most p to the power p minus one candidates](goal), where
p is the number of vertices. -/
theorem rooted_spanning_parent_cover [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.Connected) (r : V) :
    ∃ P : ParentEncoding V r, P.Valid ∧ (∀ v, G.Adj v.val (P v)) ∧
      Fintype.card (ParentEncoding V r) ≤ Fintype.card V ^ (Fintype.card V - 1) := by
  classical
  choose P hadj hdist using (fun v => exists_parent_step_closer G hG r v)
  refine ⟨P, ⟨G.dist r, G.dist_self, ?_⟩, hadj, (card_parentEncoding r).le⟩
  intro v
  rw [← hdist v]
  exact Nat.lt_succ_self _

/-- An [active set of nonroot vertices](hyp:A) is [parent closed](goal) for an
[encoding](hyp:P) if every active vertex has its parent at the root or in the active set. -/
def ParentEncoding.ParentClosed (P : ParentEncoding V r)
    (A : Finset {v : V // v ≠ r}) : Prop :=
  ∀ v ∈ A, P v = r ∨ ∃ h : P v ≠ r, (⟨P v, h⟩ : {v : V // v ≠ r}) ∈ A

/-- In a [valid](hyp:hP) [parent encoding](hyp:P), every [nonempty](hyp:hA) [active set of nonroot
vertices](hyp:A) [contains a vertex that is not the parent of any active vertex](goal). -/
theorem ParentEncoding.exists_leaf (P : ParentEncoding V r) (hP : P.Valid)
    (A : Finset {v : V // v ≠ r}) (hA : A.Nonempty) :
    ∃ l ∈ A, ∀ v ∈ A, P v ≠ l.val := by
  obtain ⟨height, _, hheight⟩ := hP
  obtain ⟨l, hl, hmax⟩ := A.exists_max_image (fun v => height v.val) hA
  refine ⟨l, hl, ?_⟩
  intro v hv heq
  have hlt := hheight v
  rw [heq] at hlt
  exact (not_lt_of_ge (hmax v hv)) hlt

/-- For a [parent encoding](hyp:P), deleting from a [parent-closed](hyp:hA) [active set of nonroot
vertices](hyp:A) [a vertex](hyp:l) that [is not the parent of any active vertex](hyp:hl) [leaves a
parent-closed set](goal). -/
theorem ParentEncoding.parentClosed_erase [DecidableEq V] (P : ParentEncoding V r)
    (A : Finset {v : V // v ≠ r}) (hA : P.ParentClosed A)
    (l : {v : V // v ≠ r}) (hl : ∀ v ∈ A, P v ≠ l.val) :
    P.ParentClosed (A.erase l) := by
  intro v hv
  rcases hA v (Finset.mem_of_mem_erase hv) with h | ⟨h, hm⟩
  · exact Or.inl h
  · exact Or.inr ⟨h, Finset.mem_erase.mpr ⟨fun he => hl v
      (Finset.mem_of_mem_erase hv) (congrArg Subtype.val he), hm⟩⟩

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {X : V → Type v} [∀ i, MeasurableSpace (X i)]

/-- Under [independent coordinate probability laws](hyp:μ), [the probability that two events both
occur is at most the probability of the first event times β](goal). Here the [two events](hyp:A,B)
are [measurable](hyp:hA,hB), [the first event does not depend on a chosen
coordinate](hyp:i,hinvariant), and [β](hyp:β) is a number such that, [whatever the other
coordinates are, the values of the chosen coordinate that put the outcome in the second event have
probability at most β](hyp:hsection). -/
theorem pi_measure_intersection_le_of_section
    (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (i : V) (A B : Set (∀ i, X i)) (β : ℝ≥0∞)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hinvariant : ∀ (x : ∀ i, X i) (z : X i), Function.update x i z ∈ A ↔ x ∈ A)
    (hsection : ∀ x : ∀ i, X i, μ i {z | Function.update x i z ∈ B} ≤ β) :
    Measure.pi μ (A ∩ B) ≤ Measure.pi μ A * β := by
  classical
  have hbound :
      (∫⁻ x, (A ∩ B).indicator (fun _ => (1 : ℝ≥0∞)) x ∂Measure.pi μ) ≤
        ∫⁻ x, A.indicator (fun _ => β) x ∂Measure.pi μ := by
    apply lintegral_le_of_lmarginal_le {i}
      (measurable_const.indicator (hA.inter hB)) (measurable_const.indicator hA)
    rw [lmarginal_singleton, lmarginal_singleton]
    intro x
    dsimp only
    by_cases hx : x ∈ A
    · have hleft :
          (fun z => (A ∩ B).indicator (fun _ => (1 : ℝ≥0∞))
            (Function.update x i z)) =
          {z | Function.update x i z ∈ B}.indicator (fun _ => (1 : ℝ≥0∞)) := by
        funext z
        simp [Set.indicator, hinvariant x z, hx]
      have hright : (fun z => A.indicator (fun _ => β) (Function.update x i z)) =
          (fun _ => β) := by
        funext z
        simp [Set.indicator, hinvariant x z, hx]
      rw [hleft, hright]
      change (∫⁻ z, {z | Function.update x i z ∈ B}.indicator
        (fun _ => (1 : ℝ≥0∞)) z ∂μ i) ≤ ∫⁻ (_ : X i), β ∂μ i
      have hmeas : MeasurableSet {z | Function.update x i z ∈ B} :=
        hB.preimage (measurable_update x (a := i))
      rw [lintegral_indicator_const hmeas 1, lintegral_const]
      simpa using hsection x
    · have hleft :
          (fun z => (A ∩ B).indicator (fun _ => (1 : ℝ≥0∞))
            (Function.update x i z)) = (fun _ => 0) := by
        funext z
        simp [Set.indicator, hinvariant x z, hx]
      have hright : (fun z => A.indicator (fun _ => β) (Function.update x i z)) =
          (fun _ => 0) := by
        funext z
        simp [Set.indicator, hinvariant x z, hx]
      rw [hleft, hright]
  simpa only [lintegral_indicator_const (hA.inter hB), one_mul,
    lintegral_indicator_const hA, mul_comm β] using hbound

variable {V : Type u}
variable {W : Type v}
variable {X : V → Type w} [∀ i, MeasurableSpace (X i)]

/-- The [partial rooted-tree event](goal) for an [embedded tree](hyp:e,P) requires the
[root event](hyp:rootEvent) and the [edge events](hyp:edgeEvent) of the
[active nonroot vertices](hyp:A). -/
def partialTreeEvent {r : W} (e : W ↪ V) (P : ParentEncoding W r)
    (rootEvent : Set (X (e r))) (edgeEvent : ∀ i j, Set (X i × X j))
    (A : Finset {v : W // v ≠ r}) : Set (∀ i, X i) :=
  {x | x (e r) ∈ rootEvent ∧ ∀ v ∈ A, (x (e v.val), x (e (P v))) ∈
    edgeEvent (e v.val) (e (P v))}

/-- For an [embedded parent tree](hyp:e,P) and an [active set of nonroot vertices](hyp:A), a [root
event](hyp:rootEvent) and [edge events](hyp:edgeEvent) that are [measurable](hyp:hroot,hedge) give
a [measurable partial rooted-tree event](goal). -/
theorem measurableSet_partialTreeEvent {r : W} (e : W ↪ V) (P : ParentEncoding W r)
    (rootEvent : Set (X (e r))) (edgeEvent : ∀ i j, Set (X i × X j))
    (A : Finset {v : W // v ≠ r}) (hroot : MeasurableSet rootEvent)
    (hedge : ∀ i j, MeasurableSet (edgeEvent i j)) :
    MeasurableSet (partialTreeEvent e P rootEvent edgeEvent A) := by
  classical
  change MeasurableSet ({x : ∀ i, X i | x (e r) ∈ rootEvent} ∩
    {x : ∀ i, X i | ∀ v ∈ A,
      (x (e v.val), x (e (P v))) ∈ edgeEvent (e v.val) (e (P v))})
  refine (hroot.preimage (measurable_pi_apply (e r))).inter ?_
  have hset : {x : ∀ i, X i | ∀ v ∈ A,
      (x (e v.val), x (e (P v))) ∈ edgeEvent (e v.val) (e (P v))} =
      ⋂ v ∈ A, (fun x : ∀ i, X i => (x (e v.val), x (e (P v)))) ⁻¹'
        edgeEvent (e v.val) (e (P v)) := by
    ext x
    simp
  rw [hset]
  exact A.measurableSet_biInter (fun v hv =>
    (hedge (e v.val) (e (P v))).preimage
      ((measurable_pi_apply (e v.val)).prodMk (measurable_pi_apply (e (P v)))))

omit [∀ i, MeasurableSpace (X i)] in
/-- For [any vertex](hyp:l) [in the active set](hyp:hl), the [partial tree
event](hyp:e,P,rootEvent,edgeEvent,A) [is exactly the partial tree event of the active set with
that vertex removed, intersected with the edge event joining that vertex to its parent](goal). -/
theorem partialTreeEvent_erase_inter [DecidableEq W] {r : W}
    (e : W ↪ V) (P : ParentEncoding W r)
    (rootEvent : Set (X (e r))) (edgeEvent : ∀ i j, Set (X i × X j))
    (A : Finset {v : W // v ≠ r}) (l : {v : W // v ≠ r}) (hl : l ∈ A) :
    partialTreeEvent e P rootEvent edgeEvent A =
      partialTreeEvent e P rootEvent edgeEvent (A.erase l) ∩
        {x | (x (e l.val), x (e (P l))) ∈ edgeEvent (e l.val) (e (P l))} := by
  ext x
  constructor
  · intro hx
    exact ⟨⟨hx.1, fun v hv => hx.2 v (Finset.mem_of_mem_erase hv)⟩, hx.2 l hl⟩
  · rintro ⟨hx, hedge⟩
    refine ⟨hx.1, fun v hv => ?_⟩
    by_cases h : v = l
    · subst v
      exact hedge
    · exact hx.2 v (Finset.mem_erase.mpr ⟨h, hv⟩)

omit [∀ i, MeasurableSpace (X i)] in
/-- After deleting from the active set of an [embedded partial tree](hyp:e,P,rootEvent,edgeEvent,A)
[a vertex](hyp:l) that [is not the parent of any active vertex](hyp:hleaf), [membership in the
remaining partial tree event is unaffected by replacing the deleted vertex's coordinate](goal), for
every [outcome and replacement value](hyp:x,z). -/
theorem partialTreeEvent_update_erase [DecidableEq V] [DecidableEq W] {r : W}
    (e : W ↪ V) (P : ParentEncoding W r)
    (rootEvent : Set (X (e r))) (edgeEvent : ∀ i j, Set (X i × X j))
    (A : Finset {v : W // v ≠ r}) (l : {v : W // v ≠ r})
    (hleaf : ∀ v ∈ A, P v ≠ l.val) (x : ∀ i, X i) (z : X (e l.val)) :
    Function.update x (e l.val) z ∈ partialTreeEvent e P rootEvent edgeEvent (A.erase l) ↔
      x ∈ partialTreeEvent e P rootEvent edgeEvent (A.erase l) := by
  have hr : e r ≠ e l.val := fun h => l.property (e.injective h).symm
  have hv : ∀ v ∈ A.erase l, e v.val ≠ e l.val := by
    intro v hv h
    exact (Finset.mem_erase.mp hv).1 (Subtype.ext (e.injective h))
  have hp : ∀ v ∈ A.erase l, e (P v) ≠ e l.val := by
    intro v hv h
    exact hleaf v (Finset.mem_of_mem_erase hv) (e.injective h)
  simp only [partialTreeEvent, Set.mem_ofPred_eq, Function.update_of_ne hr]
  constructor <;> rintro ⟨hroot, hedge⟩ <;> refine ⟨hroot, fun v hmem => ?_⟩
  · simpa only [Function.update_of_ne (hv v hmem), Function.update_of_ne (hp v hmem)]
      using hedge v hmem
  · simpa only [Function.update_of_ne (hv v hmem), Function.update_of_ne (hp v hmem)]
      using hedge v hmem

/-- Under [coordinate probability laws](hyp:μ), the
[partial tree with no active edges](hyp:e,P,edgeEvent)
[has exactly the mass of its measurable root event](goal),
for [measurable root events](hyp:hroot). -/
theorem pi_measure_partialTreeEvent_empty [Fintype V]
    (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    {r : W} (e : W ↪ V) (P : ParentEncoding W r)
    (rootEvent : Set (X (e r))) (edgeEvent : ∀ i j, Set (X i × X j))
    (hroot : MeasurableSet rootEvent) :
    Measure.pi μ (partialTreeEvent e P rootEvent edgeEvent ∅) = μ (e r) rootEvent := by
  have hevent : partialTreeEvent e P rootEvent edgeEvent ∅ =
      Function.eval (e r) ⁻¹' rootEvent := by
    ext x
    simp [partialTreeEvent, Function.eval]
  rw [hevent]
  exact (measurePreserving_eval μ (e r)).measure_preimage hroot.nullMeasurableSet

/-- Under [independent coordinate probability laws](hyp:μ), take an [embedded parent tree](hyp:e,P)
that is [valid](hyp:hP), a [root event](hyp:rootEvent) and [edge events](hyp:edgeEvent) that are
[measurable](hyp:hroot,hedge), [two bounds α and β](hyp:α,β), and an [active set of nonroot
vertices](hyp:A) that is [parent closed](hyp:hA). If [the root event has probability at most
α](hyp:hrootMass) and [for any two distinct coordinates and any value of the second, the values of
the first that satisfy their edge event have probability at most β](hyp:hsection), then [the
partial tree event has probability at most α times β raised to the number of active
vertices](goal). -/
theorem pi_measure_partial_tree_event_le [Fintype V]
    (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    {r : W} (e : W ↪ V) (P : ParentEncoding W r) (hP : P.Valid)
    (rootEvent : Set (X (e r))) (edgeEvent : ∀ i j, Set (X i × X j))
    (α β : ℝ≥0∞) (A : Finset {v : W // v ≠ r}) (hA : P.ParentClosed A)
    (hroot : MeasurableSet rootEvent) (hedge : ∀ i j, MeasurableSet (edgeEvent i j))
    (hrootMass : μ (e r) rootEvent ≤ α)
    (hsection : ∀ (i j : V), i ≠ j → ∀ y : X j,
      μ i {z | (z, y) ∈ edgeEvent i j} ≤ β) :
    Measure.pi μ (partialTreeEvent e P rootEvent edgeEvent A) ≤ α * β ^ A.card := by
  classical
  induction A using Finset.strongInductionOn with
  | _ A ih =>
    by_cases hempty : A = ∅
    · subst A
      simpa only [pi_measure_partialTreeEvent_empty μ e P rootEvent edgeEvent hroot,
        Finset.card_empty, pow_zero, mul_one] using hrootMass
    · obtain ⟨l, hl, hleaf⟩ := P.exists_leaf hP A (Finset.nonempty_iff_ne_empty.mpr hempty)
      have hparent : e (P l) ≠ e l.val := fun h => P.parent_ne hP l (e.injective h)
      have hstep :
          Measure.pi μ (partialTreeEvent e P rootEvent edgeEvent A) ≤
            Measure.pi μ (partialTreeEvent e P rootEvent edgeEvent (A.erase l)) * β := by
        rw [partialTreeEvent_erase_inter e P rootEvent edgeEvent A l hl]
        apply pi_measure_intersection_le_of_section μ (e l.val)
          (partialTreeEvent e P rootEvent edgeEvent (A.erase l))
          {x | (x (e l.val), x (e (P l))) ∈ edgeEvent (e l.val) (e (P l))} β
          (measurableSet_partialTreeEvent e P rootEvent edgeEvent (A.erase l) hroot hedge)
          ((hedge (e l.val) (e (P l))).preimage
            ((measurable_pi_apply (e l.val)).prodMk (measurable_pi_apply (e (P l)))))
          (partialTreeEvent_update_erase e P rootEvent edgeEvent A l hleaf)
        intro x
        simpa only [Set.mem_ofPred_eq, Function.update_self, Function.update_of_ne hparent]
          using hsection (e l.val) (e (P l)) hparent.symm (x (e (P l)))
      calc
        Measure.pi μ (partialTreeEvent e P rootEvent edgeEvent A) ≤
            Measure.pi μ (partialTreeEvent e P rootEvent edgeEvent (A.erase l)) * β := hstep
        _ ≤ (α * β ^ (A.erase l).card) * β :=
          mul_le_mul_left (ih (A.erase l) (Finset.erase_ssubset hl)
            (P.parentClosed_erase A hA l hleaf)) β
        _ = α * β ^ A.card := by
          rw [← Finset.card_erase_add_one hl, pow_succ, mul_assoc]

/-- Under [independent coordinate probability laws](hyp:μ), take an [embedded parent tree](hyp:e,P)
that is [valid](hyp:hP), a [root event](hyp:rootEvent) and [edge events](hyp:edgeEvent) that are
[measurable](hyp:hroot,hedge), and [two bounds α and β](hyp:α,β). If [the root event has
probability at most α](hyp:hrootMass) and [for any two distinct coordinates and any value of the
second, the values of the first that satisfy their edge event have probability at most
β](hyp:hsection), then [the event that the root event and every edge event of the tree occur has
probability at most α times β to the power p minus one](goal), where p is the tree's vertex count.
-/
theorem pi_measure_rooted_tree_event_le [Fintype V] [Fintype W] [DecidableEq W]
    (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    {r : W} (e : W ↪ V) (P : ParentEncoding W r) (hP : P.Valid)
    (rootEvent : Set (X (e r))) (edgeEvent : ∀ i j, Set (X i × X j))
    (α β : ℝ≥0∞) (hroot : MeasurableSet rootEvent)
    (hedge : ∀ i j, MeasurableSet (edgeEvent i j)) (hrootMass : μ (e r) rootEvent ≤ α)
    (hsection : ∀ (i j : V), i ≠ j → ∀ y : X j,
      μ i {z | (z, y) ∈ edgeEvent i j} ≤ β) :
    Measure.pi μ (partialTreeEvent e P rootEvent edgeEvent Finset.univ) ≤
      α * β ^ (Fintype.card W - 1) := by
  have hclosed : P.ParentClosed Finset.univ := by
    intro v hv
    by_cases h : P v = r
    · exact Or.inl h
    · exact Or.inr ⟨h, Finset.mem_univ _⟩
  simpa using pi_measure_partial_tree_event_le μ e P hP rootEvent edgeEvent α β
    Finset.univ hclosed hroot hedge hrootMass hsection

end Causalean.Stat.RandomGraph

