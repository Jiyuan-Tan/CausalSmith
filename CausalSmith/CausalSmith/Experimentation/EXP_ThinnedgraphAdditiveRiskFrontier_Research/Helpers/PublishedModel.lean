module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Basic
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.BlockPrior
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# Published SNIPE convention gate and specialization
-/

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Published raw-polynomial schedules allow diagonal arrows and zero edge coefficients. -/
structure PublishedSchedule (V : Type*) where
  edge : V → V → Prop
  decEdge : DecidableRel edge
  coef : V → Finset V → ℝ

/-- The published in-neighborhood, including diagonal arrows when present. -/
def pubNbhd (ϑ : PublishedSchedule V) (i : V) : Finset V :=
  Finset.univ.filter (fun j => ϑ.edge j i)
/-- The published out-neighborhood, including diagonal arrows when present. -/
def pubOutNbhd (ϑ : PublishedSchedule V) (j : V) : Finset V :=
  Finset.univ.filter (fun i => ϑ.edge j i)

/-- Order-one neighborhood interference restricts only unsupported and higher-order
coefficients; loops and zero singleton coefficients are permitted. -/
def PublishedOrderOne (ϑ : PublishedSchedule V) : Prop :=
  (∀ i S, ¬ S ⊆ pubNbhd ϑ i → ϑ.coef i S = 0) ∧
  (∀ i S, 1 < S.card → ϑ.coef i S = 0)

/-- The published raw-monomial polynomial potential outcome, including the empty monomial. -/
def pubOutcome (ϑ : PublishedSchedule V) (i : V) (z : Assign V) : ℝ :=
  ∑ S ∈ (pubNbhd ϑ i).powerset, ϑ.coef i S * ∏ j ∈ S, treatment (z j)

/-- The coefficient-mass envelope is the maximum row sum of absolute polynomial coefficients,
including the empty monomial. The empty-population extension is zero. -/
def pubEnvelope (ϑ : PublishedSchedule V) : ℝ≥0 :=
  Finset.univ.sup (fun i => (∑ S ∈ (pubNbhd ϑ i).powerset, |ϑ.coef i S|).toNNReal)

/-- Cortez-Rodriguez, Eichhorn and Yu (2023), arXiv:2208.05553v4,
Sections 3.1–3.2, Assumptions 1–2 and equations (3.2)–(3.3).
At interaction order one the polynomial has a constant and neighborhood singleton terms,
and its defined envelope is their maximum absolute-coefficient mass. Neighborhoods may contain
their own vertices, and singleton coefficients may vanish. No normalization or degree bound
is part of this convention gate.
Source: https://arxiv.org/html/2208.05553v4#S3 . -/
-- @node: lem:snipe-model-conventions
def SnipeModelConventions : Sort 0 :=
  ∀ ϑ : PublishedSchedule V, PublishedOrderOne ϑ →
    (∀ i z, pubOutcome ϑ i z =
      ϑ.coef i ∅ + ∑ j ∈ pubNbhd ϑ i, ϑ.coef i {j} * treatment (z j)) ∧
    pubEnvelope ϑ = Finset.univ.sup (fun i =>
      (|ϑ.coef i ∅| + ∑ j ∈ pubNbhd ϑ i, |ϑ.coef i {j}|).toNNReal)

/-- The paper's bounded-envelope and bounded-total-degree specialization of the order-one
published model. These restrictions belong to the specialization, not the cited conventions. -/
def PublishedClass (ϑ : PublishedSchedule V) (D : ℕ) : Prop :=
  PublishedOrderOne ϑ ∧ pubEnvelope ϑ ≤ 1 ∧
    (∀ i, (pubNbhd ϑ i).card ≤ D) ∧ (∀ j, (pubOutNbhd ϑ j).card ≤ D)

/-- The all-treated minus all-control average in the published polynomial carrier. -/
def pubTte (ϑ : PublishedSchedule V) : ℝ :=
  (Fintype.card V : ℝ)⁻¹ * ∑ i,
    (pubOutcome ϑ i (fun _ => true) - pubOutcome ϑ i (fun _ => false))

/-- Adjoin all diagonal arrows and encode the baseline, own effect, and off-diagonal coefficients
as order-one monomials. -/
def augment (θ : Schedule V) : PublishedSchedule V where
  edge := fun j i => θ.edge j i ∨ j = i
  decEdge := Classical.decRel _
  coef := fun i S => if S = ∅ then θ.a i else
    ∑ j : V, if S = {j} then
      (if j = i then θ.t i else if θ.edge j i then θ.b i j else 0) else 0

omit [Fintype V] [DecidableEq V] in
/-- Removing diagonal arrows gives an irreflexive published graph.  [For the stated data and conditions](hyp:ϑ), [the stated conclusion holds](goal). -/
-- @node: strip_edge_irrefl
lemma strip_edge_irrefl (ϑ : PublishedSchedule V) :
    ∀ i, ¬ (ϑ.edge i i ∧ i ≠ i) := by
  intro i h
  exact h.2 rfl

/-- Remove diagonal arrows and read the empty and singleton polynomial coefficients as additive
schedule coefficients. -/
def strip (ϑ : PublishedSchedule V) : Schedule V where
  edge := fun j i => ϑ.edge j i ∧ j ≠ i
  decEdge := Classical.decRel _
  irrefl := strip_edge_irrefl ϑ
  a := fun i => ϑ.coef i ∅
  t := fun i => ϑ.coef i {i}
  b := fun i j => ϑ.coef i {j}

/-- Equality of graph and all supported polynomial coefficients. -/
def PublishedEquivalent (ϑ ψ : PublishedSchedule V) : Prop :=
  (∀ j i, ϑ.edge j i ↔ ψ.edge j i) ∧
    ∀ i S, S ⊆ pubNbhd ϑ i → ϑ.coef i S = ψ.coef i S

/-- Equality of schedules modulo unused off-graph values of the coefficient array. -/
def ScheduleEquivalent (θ ψ : Schedule V) : Prop :=
  (∀ j i, θ.edge j i ↔ ψ.edge j i) ∧ θ.a = ψ.a ∧ θ.t = ψ.t ∧
    ∀ i j, θ.edge j i → θ.b i j = ψ.b i j

/-- The measurable augmented graph carrier contains every known diagonal arrow. -/
abbrev AugGraph (V : Type*) := {A : V × V → Bool // ∀ i, A (i,i) = true}
/-- The augmented complete record consists of the diagonal-complete graph, assignments, and
outcomes. -/
abbrev AugRecord (V : Type*) := AugGraph V × (V → Bool) × (V → ℝ)

/-- Add the known diagonal arrows to a recorded off-diagonal labeled graph. -/
def adjoinGraph (H : OffDiag V → Bool) : V × V → Bool :=
  fun e => if h : e.1 ≠ e.2 then H ⟨e,h⟩ else true

omit [Fintype V] in
/-- Every diagonal arrow is present after graph augmentation.  [For the stated data and conditions](hyp:H), [the stated conclusion holds](goal). -/
-- @node: adjoinGraph_diagonal
lemma adjoinGraph_diagonal (H : OffDiag V → Bool) : ∀ i, adjoinGraph H (i,i) = true := by
  intro i
  simp [adjoinGraph]

/-- Augment only the graph coordinate of the complete record. -/
def adjoinRecord (o : Record V) : AugRecord V :=
  (⟨adjoinGraph o.1, adjoinGraph_diagonal o.1⟩, o.2)
/-- Remove known diagonal arrows while preserving all assignments and outcomes. -/
def removeRecord (o : AugRecord V) : Record V :=
  (fun e => o.1.1 e.1, o.2)

omit [Fintype V] in
/-- Removing and re-adjoining diagonals is the identity on augmented records.  [For the stated data and conditions](hyp:o), [the stated conclusion holds](goal). -/
-- @node: adjoin_remove
lemma adjoin_remove (o : AugRecord V) : adjoinRecord (removeRecord o) = o := by
  apply Prod.ext
  · apply Subtype.ext
    funext e
    rcases e with ⟨j, i⟩
    by_cases h : j ≠ i
    · simp [adjoinRecord, removeRecord, adjoinGraph, h]
    · have heq : j = i := not_ne_iff.mp h
      subst j
      simp [adjoinRecord, removeRecord, adjoinGraph, o.1.2 i]
  · rfl
omit [Fintype V] in
/-- Adjoining and then removing diagonals is the identity on original records.  [For the stated data and conditions](hyp:o), [the stated conclusion holds](goal). -/
-- @node: remove_adjoin
lemma remove_adjoin (o : Record V) : removeRecord (adjoinRecord o) = o := by
  apply Prod.ext
  · funext e
    simp [removeRecord, adjoinRecord, adjoinGraph, e.2]
  · rfl
omit [Fintype V] in
/-- [Adjoining known diagonal arrows is measurable](goal). -/
-- @node: adjoinRecord_measurable
@[fun_prop] lemma adjoinRecord_measurable : Measurable (adjoinRecord (V := V)) := by
  unfold adjoinRecord
  apply Measurable.prodMk _ measurable_snd
  apply Measurable.subtype_mk
  apply measurable_pi_lambda
  intro e
  by_cases h : e.1 ≠ e.2
  · simpa only [adjoinGraph, dif_pos h] using
      (measurable_fst.eval : Measurable (fun o : Record V => o.1 ⟨e, h⟩))
  · simpa only [adjoinGraph, dif_neg h] using
      (measurable_const : Measurable (fun _ : Record V => true))
omit [Fintype V] [DecidableEq V] in
/-- [Removing known diagonal arrows is measurable](goal). -/
-- @node: removeRecord_measurable
@[fun_prop] lemma removeRecord_measurable : Measurable (removeRecord (V := V)) := by
  unfold removeRecord
  apply Measurable.prodMk _ measurable_snd
  apply measurable_pi_lambda
  intro e
  exact (measurable_subtype_coe.comp measurable_fst).eval

/-- The deterministic measurable equivalence adds the known diagonals. -/
def augmentRecord : Record V ≃ᵐ AugRecord V where
  toFun := adjoinRecord
  invFun := removeRecord
  left_inv := remove_adjoin
  right_inv := adjoin_remove
  measurable_toFun := adjoinRecord_measurable
  measurable_invFun := removeRecord_measurable

/-- The published schedule under the same off-diagonal audit and assignment channel, with known
diagonals adjoined. -/
def pubRecordOf (ϑ : PublishedSchedule V) (ω : Assign V × Audit V) : AugRecord V :=
  adjoinRecord (fun e => decide (ϑ.edge e.1.1 e.1.2) && ω.2 e,
    ω.1, fun i => pubOutcome ϑ i ω.1)

/-- The complete augmented record and independent uniform seed law at a published schedule. -/
def pubRecordLaw (D : Measure (Assign V × Audit V)) (ϑ : PublishedSchedule V) :
    Measure (AugRecord V × ℝ) :=
  (D.prod seedLaw).map (fun ω => (pubRecordOf ϑ ω.1, ω.2))

/-- All measurable seeded real-valued estimators of the augmented record. -/
abbrev PubEstimator (V : Type*) [Fintype V] [DecidableEq V] :=
  {T : AugRecord V × ℝ → ℝ // Measurable T}

/-- The extended minimax risk over a specified published class and all measurable seeded
augmented-record estimators. -/
def pubMinimaxRisk (D : Measure (Assign V × Audit V)) (𝔠 : Set (PublishedSchedule V)) : ℝ≥0∞ :=
  Causalean.Stat.minimaxValueENNReal
    (fun (T : PubEstimator V) (ϑ : 𝔠) =>
      ∫⁻ x, ENNReal.ofReal ((T.1 x - pubTte ϑ.1) ^ 2) ∂(pubRecordLaw D ϑ.1))

/-- Augmentation puts the baseline at the empty monomial.  [For the stated data and conditions](hyp:θ,i), [the stated conclusion holds](goal). -/
-- @node: augment_coef_empty
lemma augment_coef_empty (θ : Schedule V) (i : V) :
    (augment θ).coef i ∅ = θ.a i := by
  simp [augment]

/-- Augmentation puts each treatment effect at its singleton monomial.  [For the stated data and conditions](hyp:θ,i,j), [the stated conclusion holds](goal). -/
-- @node: augment_coef_singleton
lemma augment_coef_singleton (θ : Schedule V) (i j : V) :
    (augment θ).coef i {j} =
      if j = i then θ.t i else if θ.edge j i then θ.b i j else 0 := by
  classical
  simp [augment, Finset.singleton_inj]

/-- The augmented neighborhood is the original one with the own coordinate inserted.  [For the stated data and conditions](hyp:θ,i), [the stated conclusion holds](goal). -/
-- @node: pubNbhd_augment
lemma pubNbhd_augment (θ : Schedule V) (i : V) :
    pubNbhd (augment θ) i = insert i (inNbhd θ i) := by
  ext j
  simp [pubNbhd, augment, inNbhd, or_comm]

/-- Stripping the augmented schedule recovers every coefficient that is used by an outcome.  [For the stated data and conditions](hyp:θ), [the stated conclusion holds](goal). -/
-- @node: strip_augment_equivalent
lemma strip_augment_equivalent (θ : Schedule V) :
    ScheduleEquivalent (strip (augment θ)) θ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j i
    change ((θ.edge j i ∨ j = i) ∧ j ≠ i) ↔ θ.edge j i
    constructor
    · intro h
      exact h.1.resolve_right h.2
    · intro h
      exact ⟨Or.inl h, fun heq => θ.irrefl i (heq ▸ h)⟩
  · funext i
    exact augment_coef_empty θ i
  · funext i
    exact (augment_coef_singleton θ i i).trans (if_pos rfl)
  · intro i j hij
    have hji : j ≠ i := hij.2
    have hedge : θ.edge j i := hij.1.resolve_right hji
    exact (augment_coef_singleton θ i j).trans (by rw [if_neg hji, if_pos hedge])

/-- Only the empty and supported singleton monomials survive augmentation.  [For the stated data and conditions](hyp:θ), [the stated conclusion holds](goal). -/
-- @node: augment_orderOne
lemma augment_orderOne (θ : Schedule V) : PublishedOrderOne (augment θ) := by
  constructor
  · intro i S hS
    have hne : S ≠ ∅ := by
      intro heq
      exact hS (heq ▸ Finset.empty_subset _)
    simp only [augment, if_neg hne]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hsj : S = {j}
    · have hnot : ¬ (θ.edge j i ∨ j = i) := by
        intro hj
        apply hS
        rw [hsj, Finset.singleton_subset_iff, pubNbhd_augment]
        simpa [inNbhd, or_comm] using hj
      rw [if_pos hsj, if_neg (fun h => hnot (Or.inr h)),
        if_neg (fun h => hnot (Or.inl h))]
    · exact if_neg hsj
  · intro i S hcard
    have hne : S ≠ ∅ := by
      intro heq
      simp [heq] at hcard
    simp only [augment, if_neg hne]
    apply Finset.sum_eq_zero
    intro j _
    apply if_neg
    intro heq
    simp [heq] at hcard

/-- Under the published polynomial convention, augmentation preserves every outcome.  [For the stated data and conditions](hyp:hconv), [the stated conclusion holds](goal). -/
-- @node: pubOutcome_augment
lemma pubOutcome_augment (hconv : SnipeModelConventions (V := V))
    (θ : Schedule V) (i : V) (z : Assign V) :
    pubOutcome (augment θ) i z = potentialOutcome θ i z := by
  rw [(hconv (augment θ) (augment_orderOne θ)).1 i z, augment_coef_empty, pubNbhd_augment]
  have hnot : i ∉ inNbhd θ i := by simp [inNbhd, θ.irrefl]
  rw [Finset.sum_insert hnot]
  rw [augment_coef_singleton θ i i, if_pos rfl]
  unfold potentialOutcome
  rw [← add_assoc]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hij : θ.edge j i := (Finset.mem_filter.mp hj).2
  have hji : j ≠ i := fun heq => θ.irrefl i (heq ▸ hij)
  rw [augment_coef_singleton, if_neg hji, if_pos hij]

/-- Preserving all outcomes preserves the all-treated causal contrast.  [For the stated data and conditions](hyp:hconv,θ), [the stated conclusion holds](goal). -/
-- @node: pubTte_augment
lemma pubTte_augment (hconv : SnipeModelConventions (V := V)) (θ : Schedule V) :
    pubTte (augment θ) = tte θ := by
  simp only [pubTte, tte, pubOutcome_augment hconv]

/-- The augmented original record is exactly the published record under the same channel.  [For the stated data and conditions](hyp:hconv), [the stated conclusion holds](goal). -/
-- @node: pubRecordOf_augment
lemma pubRecordOf_augment (hconv : SnipeModelConventions (V := V))
    (θ : Schedule V) (ω : Assign V × Audit V) :
    augmentRecord (recordOf θ ω) = pubRecordOf (augment θ) ω := by
  change adjoinRecord (recordOf θ ω) = pubRecordOf (augment θ) ω
  unfold pubRecordOf
  congr 1
  apply Prod.ext
  · funext e
    have hne : e.1.1 ≠ e.1.2 := e.2
    simp [recordOf, augment, hne]
  · apply Prod.ext
    · rfl
    funext i
    exact (pubOutcome_augment hconv θ i ω.1).symm

/-- Augmentation adds exactly the own recipient to each out-neighborhood.  [For the stated data and conditions](hyp:θ,j), [the stated conclusion holds](goal). -/
-- @node: pubOutNbhd_augment
lemma pubOutNbhd_augment (θ : Schedule V) (j : V) :
    pubOutNbhd (augment θ) j =
      insert j (Finset.univ.filter (fun i => j ∈ inNbhd θ i)) := by
  ext i
  simp [pubOutNbhd, augment, inNbhd, or_comm, eq_comm]

/-- The published coefficient mass equals the original row coefficient mass.  [For the stated data and conditions](hyp:θ,i), [the stated conclusion holds](goal). -/
-- @node: augment_coefficientMass
lemma augment_coefficientMass (θ : Schedule V) (i : V) :
    |(augment θ).coef i ∅| + ∑ j ∈ pubNbhd (augment θ) i, |(augment θ).coef i {j}| =
      |θ.a i| + |θ.t i| + ∑ j ∈ inNbhd θ i, |θ.b i j| := by
  rw [augment_coef_empty, pubNbhd_augment]
  have hnot : i ∉ inNbhd θ i := by simp [inNbhd, θ.irrefl]
  rw [Finset.sum_insert hnot, augment_coef_singleton θ i i, if_pos rfl, ← add_assoc]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hij : θ.edge j i := (Finset.mem_filter.mp hj).2
  have hji : j ≠ i := fun heq => θ.irrefl i (heq ▸ hij)
  rw [augment_coef_singleton, if_neg hji, if_pos hij]

/-- A degree-d additive schedule maps to a diagonal-complete degree-(d+1) published schedule.  [For the stated data and conditions](hyp:hconv,hclass), [the stated conclusion holds](goal). -/
-- @node: augment_publishedClass
lemma augment_publishedClass (hconv : SnipeModelConventions (V := V))
    (θ : Schedule V) (d : ℕ) (hclass : ScheduleClass θ d) :
    PublishedClass (augment θ) (d + 1) ∧ ∀ i, (augment θ).edge i i := by
  refine ⟨⟨augment_orderOne θ, ?_, ?_, ?_⟩, fun _ => Or.inr rfl⟩
  · rw [(hconv (augment θ) (augment_orderOne θ)).2]
    apply Finset.sup_le
    intro i _
    rw [augment_coefficientMass]
    exact Real.toNNReal_le_one.mpr (hclass.coeffMass i)
  · intro i
    rw [pubNbhd_augment, Finset.card_insert_of_notMem (by simp [inNbhd, θ.irrefl])]
    exact Nat.add_le_add_right (hclass.inDegree i) 1
  · intro j
    rw [pubOutNbhd_augment, Finset.card_insert_of_notMem (by simp [inNbhd, θ.irrefl])]
    exact Nat.add_le_add_right (hclass.outDegree j) 1

/-- A diagonal-complete published neighborhood is the stripped neighborhood plus its own vertex.  [For the stated data and conditions](hyp:ϑ,hdiag,i), [the stated conclusion holds](goal). -/
-- @node: pubNbhd_strip
lemma pubNbhd_strip (ϑ : PublishedSchedule V) (hdiag : ∀ i, ϑ.edge i i) (i : V) :
    pubNbhd ϑ i = insert i (inNbhd (strip ϑ) i) := by
  ext j
  constructor
  · intro hj
    have he := (Finset.mem_filter.mp hj).2
    by_cases h : j = i
    · exact Finset.mem_insert.mpr (Or.inl h)
    · exact Finset.mem_insert.mpr (Or.inr
        (Finset.mem_filter.mpr ⟨Finset.mem_univ j, he, h⟩))
  · intro hj
    rcases Finset.mem_insert.mp hj with h | h
    · subst j
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hdiag i⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, (Finset.mem_filter.mp h).2.1⟩

/-- The same diagonal removal identity holds for out-neighborhoods.  [For the stated data and conditions](hyp:ϑ,hdiag,j), [the stated conclusion holds](goal). -/
-- @node: pubOutNbhd_strip
lemma pubOutNbhd_strip (ϑ : PublishedSchedule V) (hdiag : ∀ i, ϑ.edge i i) (j : V) :
    pubOutNbhd ϑ j = insert j (Finset.univ.filter (fun i => j ∈ inNbhd (strip ϑ) i)) := by
  ext i
  constructor
  · intro hi
    have he := (Finset.mem_filter.mp hi).2
    by_cases h : i = j
    · exact Finset.mem_insert.mpr (Or.inl h)
    · exact Finset.mem_insert.mpr (Or.inr
        (Finset.mem_filter.mpr ⟨Finset.mem_univ i,
          Finset.mem_filter.mpr ⟨Finset.mem_univ j, he, Ne.symm h⟩⟩))
  · intro hi
    rcases Finset.mem_insert.mp hi with h | h
    · subst i
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hdiag j⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,
        (Finset.mem_filter.mp (Finset.mem_filter.mp h).2).2.1⟩

/-- Stripping removes one degree and retains exactly the published row coefficient mass.  [For the stated data and conditions](hyp:hconv,hclass,hdiag), [the stated conclusion holds](goal). -/
-- @node: strip_scheduleClass
lemma strip_scheduleClass (hconv : SnipeModelConventions (V := V))
    (ϑ : PublishedSchedule V) (d : ℕ) (hclass : PublishedClass ϑ (d + 1))
    (hdiag : ∀ i, ϑ.edge i i) : ScheduleClass (strip ϑ) d := by
  constructor
  · intro i
    have hi := hclass.2.2.1 i
    rw [pubNbhd_strip ϑ hdiag,
      Finset.card_insert_of_notMem (fun h => (Finset.mem_filter.mp h).2.2 rfl)] at hi
    exact Nat.le_of_add_le_add_right hi
  · intro j
    have hj := hclass.2.2.2 j
    rw [pubOutNbhd_strip ϑ hdiag,
      Finset.card_insert_of_notMem (fun h =>
        (Finset.mem_filter.mp (Finset.mem_filter.mp h).2).2.2 rfl)] at hj
    exact Nat.le_of_add_le_add_right hj
  · intro i
    have hm := hclass.2.1
    rw [(hconv ϑ hclass.1).2] at hm
    have hi := (Finset.le_sup (f := fun i =>
      (|ϑ.coef i ∅| + ∑ j ∈ pubNbhd ϑ i, |ϑ.coef i {j}|).toNNReal)
      (Finset.mem_univ i)).trans hm
    have hr := Real.toNNReal_le_one.mp hi
    rw [pubNbhd_strip ϑ hdiag,
      Finset.sum_insert (fun h => (Finset.mem_filter.mp h).2.2 rfl), ← add_assoc] at hr
    exact hr

/-- Re-augmentation recovers the graph and every supported coefficient of an order-one schedule.  [For the stated data and conditions](hyp:ϑ,horder,hdiag), [the stated conclusion holds](goal). -/
-- @node: augment_strip_equivalent
lemma augment_strip_equivalent (ϑ : PublishedSchedule V)
    (horder : PublishedOrderOne ϑ) (hdiag : ∀ i, ϑ.edge i i) :
    PublishedEquivalent (augment (strip ϑ)) ϑ := by
  refine ⟨?_, ?_⟩
  · intro j i
    change ((ϑ.edge j i ∧ j ≠ i) ∨ j = i) ↔ ϑ.edge j i
    by_cases h : j = i
    · subst j
      simp [hdiag]
    · simp [h]
  · intro i S hS
    by_cases hempty : S = ∅
    · subst S
      exact augment_coef_empty (strip ϑ) i
    by_cases hcard : 1 < S.card
    · rw [(augment_orderOne (strip ϑ)).2 i S hcard, horder.2 i S hcard]
    · obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      have hsingle : S = {j} := by
        ext k
        constructor
        · intro hk
          exact Finset.mem_singleton.mpr
            (Finset.card_le_one.mp (Nat.le_of_not_gt hcard) k hk j hj)
        · intro hk
          simpa only [Finset.mem_singleton.mp hk] using hj
      subst S
      rw [augment_coef_singleton]
      by_cases hji : j = i
      · subst j
        rw [if_pos rfl]
        rfl
      · have hedge : ϑ.edge j i := by
          have hjmem := hS (Finset.mem_singleton_self j)
          have he := (Finset.mem_filter.mp hjmem).2
          exact (he.resolve_right hji).1
        rw [if_neg hji, if_pos (show (strip ϑ).edge j i from ⟨hedge, hji⟩)]
        rfl

/-- Composing a published estimator with record augmentation preserves squared loss.  [For the stated data and conditions](hyp:hconv), [the stated conclusion holds](goal). -/
-- @node: augmented_estimator_loss
lemma augmented_estimator_loss (hconv : SnipeModelConventions (V := V))
    (D : Measure (Assign V × Audit V)) (θ : Schedule V) (T : PubEstimator V) :
    sqLoss D θ ⟨fun x => T.1 (adjoinRecord x.1, x.2),
      T.2.comp (adjoinRecord_measurable.comp measurable_fst |>.prodMk measurable_snd)⟩ =
      ∫⁻ x, ENNReal.ofReal ((T.1 x - pubTte (augment θ)) ^ 2)
        ∂(pubRecordLaw D (augment θ)) := by
  have hm : Measurable (fun ω : (Assign V × Audit V) × ℝ =>
      (recordOf θ ω.1, ω.2)) := by
    exact ((Measurable.of_discrete : Measurable (recordOf θ)).comp
      measurable_fst).prodMk measurable_snd
  have hpub : Measurable (fun ω : (Assign V × Audit V) × ℝ =>
      (pubRecordOf (augment θ) ω.1, ω.2)) := by
    exact ((Measurable.of_discrete : Measurable (pubRecordOf (augment θ))).comp
      measurable_fst).prodMk measurable_snd
  have hT := T.2
  have hcomp : Measurable (fun x : Record V × ℝ => T.1 (adjoinRecord x.1, x.2)) :=
    T.2.comp (adjoinRecord_measurable.comp measurable_fst |>.prodMk measurable_snd)
  unfold sqLoss recordLaw pubRecordLaw
  dsimp only
  rw [lintegral_map (by fun_prop) hm, lintegral_map (by fun_prop) hpub]
  simp only [pubTte_augment hconv, ← pubRecordOf_augment hconv]
  rfl

/-- Class inclusion and the measurable record map transfer the minimax lower bound.  [For the stated data and conditions](hyp:hconv,hcontains), [the stated conclusion holds](goal). -/
-- @node: minimaxRisk_le_pubMinimaxRisk
lemma minimaxRisk_le_pubMinimaxRisk (hconv : SnipeModelConventions (V := V))
    (D : Measure (Assign V × Audit V)) (d : ℕ) (𝔠 : Set (PublishedSchedule V))
    (hcontains : ∀ θ, ScheduleClass θ d → augment θ ∈ 𝔠) :
    minimaxRisk D d ≤ pubMinimaxRisk D 𝔠 := by
  unfold minimaxRisk pubMinimaxRisk
  apply Causalean.Stat.minimaxValueENNReal_le_minimaxValue
  intro T
  let T' : Estimator V := ⟨fun x => T.1 (adjoinRecord x.1, x.2),
    T.2.comp (adjoinRecord_measurable.comp measurable_fst |>.prodMk measurable_snd)⟩
  refine ⟨T', ?_⟩
  apply Causalean.Stat.worstCaseRiskENNReal_le
  intro θ
  rw [show sqLoss D θ.1 T' =
    ∫⁻ x, ENNReal.ofReal ((T.1 x - pubTte (augment θ.1)) ^ 2)
      ∂(pubRecordLaw D (augment θ.1)) from augmented_estimator_loss hconv D θ.1 T]
  exact le_iSup_of_le (⟨augment θ.1, hcontains θ.1 θ.2⟩ : 𝔠) le_rfl

/-- Conditional on the cited conventions, diagonal augmentation and stripping are inverse
specializations,
preserve all outcomes and the target, give an invertible record transformation, and transfer
  lower bounds
by class inclusion under the same assignment-audit channel.  [For the stated data and conditions](hyp:hconv_of_gate), [the stated conclusion holds](goal). -/
-- @node: lem:published-model
lemma published_model (hconv_of_gate : SnipeModelConventions (V := V)) :
    (∀ (θ : Schedule V) d, ScheduleClass θ d → PublishedClass (augment θ) (d + 1) ∧
      ∀ i, (augment θ).edge i i) ∧
    (∀ (ϑ : PublishedSchedule V) d, PublishedClass ϑ (d + 1) → (∀ i, ϑ.edge i i) →
      ScheduleClass (strip ϑ) d ∧ PublishedEquivalent (augment (strip ϑ)) ϑ) ∧
    (∀ θ : Schedule V, ScheduleEquivalent (strip (augment θ)) θ) ∧
    (∀ (θ : Schedule V) (i : V) (z : Assign V),
      pubOutcome (augment θ) i z = potentialOutcome θ i z) ∧
    (∀ θ : Schedule V, pubTte (augment θ) = tte θ) ∧
    (∀ (θ : Schedule V) (ω : Assign V × Audit V),
      augmentRecord (recordOf θ ω) = pubRecordOf (augment θ) ω) ∧
    (∀ (D : Measure (Assign V × Audit V)) (q : ℝ) (d : ℕ),
      AssignmentLaw D → AuditLaw D q → DesignIndependent D →
      ∀ 𝔠 : Set (PublishedSchedule V), (∀ θ, ScheduleClass θ d → augment θ ∈ 𝔠) →
        minimaxRisk D d ≤ pubMinimaxRisk D 𝔠) := by
  refine ⟨augment_publishedClass hconv_of_gate, ?_, strip_augment_equivalent,
    pubOutcome_augment hconv_of_gate,
    pubTte_augment hconv_of_gate, pubRecordOf_augment hconv_of_gate, ?_⟩
  · intro ϑ d hclass hdiag
    exact ⟨strip_scheduleClass hconv_of_gate ϑ d hclass hdiag,
      augment_strip_equivalent ϑ hclass.1 hdiag⟩
  · intro D q d _ha _hw _hi 𝔠 hcontains
    exact minimaxRisk_le_pubMinimaxRisk hconv_of_gate D d 𝔠 hcontains

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
