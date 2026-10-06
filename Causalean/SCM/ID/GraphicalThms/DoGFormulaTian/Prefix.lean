/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.SCM.ID.GraphicalThms.DoGFormula
public import Causalean.SCM.Do.ObsMarkov
public import Causalean.SCM.Factored.ObsChainKernel
public import Causalean.SCM.ID.Density.QFactor
public import Causalean.SCM.ID.Density.DoLawMarginal
public import Causalean.SCM.ID.GraphicalThms.NonAncestorKernelTransport
public import Causalean.Graph.DSep.InduceTransport

/-! # Prefix infrastructure for Tian density products

This file develops the measurable extension maps, reference-measure transport,
and prefix-density product identities used to peel off nodes in graph order.
It connects the full prefix product to `tianDensityProduct`; the chain rule and
SCM recovery results are proved in the sibling modules.
-/

@[expose] public section

open Causalean.Graph


open Causalean.Mathlib.MeasureTheory

namespace Causalean

open scoped MeasureTheory ProbabilityTheory ENNReal BigOperators

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

namespace SCM.ID

/-- The canonical equivalence between value spaces over propositionally equal index sets
acts as plain coordinate restriction.

Reading `valuesEquivOfEq h` as a function is the same as restricting coordinates along
`h`; the equality holds by definition and is stated so that `simp` can rewrite the
coercion without unfolding the bundled structure. -/
lemma coe_valuesEquivOfEq {M : Type*}
    {I J : Finset M} {Ω' : M → Type*} [∀ n, MeasurableSpace (Ω' n)]
    (h : I = J) :
    (⇑(valuesEquivOfEq (Ω := Ω') h) : ValuesOn I Ω' → ValuesOn J Ω')
      = valuesProjection (le_of_eq h.symm) := rfl

/-- For [a finite population of variables](hyp:N) with [measurable value spaces](hyp:Ω),
[a SWIG graph](hyp:H), [a finite node set](hyp:D), and [an index strictly below its
cardinality](hyp:n,hn), [the prefix-extension map](goal) combines an assignment on the
first indexed nodes with an assignment on the next node into an assignment on the
one-node-longer prefix.

Extend a `D`-prefix assignment by the next singleton coordinate. -/
noncomputable def extendTianPrefix (H : SWIGGraph N) (D : Finset (SWIGNode N))
    {n : ℕ} (hn : n < D.card) :
    ValuesOn (H.prefixIn D n) (swigΩ Ω) ×
        ValuesOn ({(H.nodesAt D ⟨n, hn⟩).val} : Finset (SWIGNode N)) (swigΩ Ω) →
      ValuesOn (H.prefixIn D (n + 1)) (swigΩ Ω) :=
  fun p =>
    (valuesEquivOfEq (Ω := swigΩ Ω) (prefixIn_succ H D hn).symm)
      (valuesUnionMk p.1 p.2)

/-- Prefix extension is measurable. -/
@[fun_prop]
lemma measurable_extendTianPrefix (H : SWIGGraph N) (D : Finset (SWIGNode N))
    {n : ℕ} (hn : n < D.card) :
    Measurable (extendTianPrefix (Ω := Ω) H D hn) := by
  unfold extendTianPrefix
  exact (valuesEquivOfEq (Ω := swigΩ Ω) (prefixIn_succ H D hn).symm).measurable.comp
    (measurable_valuesUnionMk (Ω := swigΩ Ω))

/-- The successor-prefix extension is inverse to the union-equivalence view of
the successor prefix. -/
lemma valuesUnionEquiv_extendTianPrefix (H : SWIGGraph N) (D : Finset (SWIGNode N))
    {n : ℕ} (hn : n < D.card)
    (p : ValuesOn (H.prefixIn D n) (swigΩ Ω) ×
        ValuesOn ({(H.nodesAt D ⟨n, hn⟩).val} : Finset (SWIGNode N)) (swigΩ Ω)) :
    valuesUnionEquiv (Ω := Ω) (prefixIn_disjoint_singleton_next H D hn)
        ((valuesEquivOfEq (Ω := swigΩ Ω) (prefixIn_succ H D hn))
          (extendTianPrefix (Ω := Ω) H D hn p))
      = p := by
  unfold extendTianPrefix
  exact valuesUnionEquiv_valuesEquivOfEq_symm_valuesUnionMk
    (prefixIn_disjoint_singleton_next H D hn) (prefixIn_succ H D hn) p

/-- The successor prefix extension carries the product of the old-prefix
reference and the next singleton reference to the successor-prefix reference. -/
lemma jointRef_extendTianPrefix
    (H : SWIGGraph N) (D : Finset (SWIGNode N))
    (ref : Causalean.SCM.ReferenceMeasures Ω)
    {k : ℕ} (hk : k < D.card) :
    ((Causalean.SCM.jointRef ref (H.prefixIn D k)).prod
        (Causalean.SCM.jointRef ref
          ({(H.nodesAt D ⟨k, hk⟩).val} : Finset (SWIGNode N)))).map
        (extendTianPrefix (Ω := Ω) H D hk)
      = Causalean.SCM.jointRef ref (H.prefixIn D (k + 1)) := by
  classical
  let v : SWIGNode N := (H.nodesAt D ⟨k, hk⟩).val
  let A : Finset (SWIGNode N) := H.prefixIn D k
  let B : Finset (SWIGNode N) := ({v} : Finset (SWIGNode N))
  let hDisj : Disjoint A B := by
    simpa [A, B, v] using prefixIn_disjoint_singleton_next H D hk
  have hunion :
      ((Causalean.SCM.jointRef ref A).prod (Causalean.SCM.jointRef ref B)).map
          ((valuesUnionEquiv (Ω := Ω) hDisj).symm)
        = Causalean.SCM.jointRef ref (A ∪ B) := by
    have hmp :=
      (Causalean.SCM.measurePreserving_valuesUnionEquiv (Ω := Ω) hDisj ref.μ).symm
        (valuesUnionEquiv (Ω := Ω) hDisj)
    simpa [Causalean.SCM.jointRef] using hmp.map_eq
  unfold extendTianPrefix
  change
    (((Causalean.SCM.jointRef ref A).prod (Causalean.SCM.jointRef ref B)).map
      ((valuesEquivOfEq (Ω := swigΩ Ω) (prefixIn_succ H D hk).symm) ∘
        (fun p : ValuesOn A (swigΩ Ω) × ValuesOn B (swigΩ Ω) =>
          valuesUnionMk p.1 p.2)))
      = Causalean.SCM.jointRef ref (H.prefixIn D (k + 1))
  rw [← MeasureTheory.Measure.map_map]
  · have hinner :
        (fun p : ValuesOn A (swigΩ Ω) × ValuesOn B (swigΩ Ω) =>
          valuesUnionMk p.1 p.2)
          = ((valuesUnionEquiv (Ω := Ω) hDisj).symm) := by
      rfl
    rw [hinner, hunion]
    rw [Causalean.SCM.jointRef, Causalean.SCM.map_pi_valuesEquivOfEq]
    rfl
  · exact (valuesEquivOfEq (Ω := swigΩ Ω) (prefixIn_succ H D hk).symm).measurable
  · exact measurable_valuesUnionMk (Ω := swigΩ Ω)

/-- The reference marginal of any `D`-prefix is absolutely continuous with
respect to the corresponding product reference. -/
lemma jointRef_map_prefixIn_absolutelyContinuous
    (H : SWIGGraph N) (D : Finset (SWIGNode N))
    (ref : Causalean.SCM.ReferenceMeasures Ω)
    (k : ℕ) :
    (Causalean.SCM.jointRef ref D).map
        (valuesProjection (H.prefixIn_subset D k))
      ≪ Causalean.SCM.jointRef ref (H.prefixIn D k) := by
  classical
  have hsubset : H.prefixIn D k ⊆ D := H.prefixIn_subset D k
  have hDisj : Disjoint (H.prefixIn D k) (D \ H.prefixIn D k) :=
    disjoint_sdiff_self_right
  have hAB : H.prefixIn D k ∪ (D \ H.prefixIn D k) = D :=
    Finset.union_sdiff_of_subset hsubset
  have hfun :
      (valuesProjection (Ω := swigΩ Ω) hsubset)
        = Prod.fst ∘ (valuesUnionEquiv (Ω := Ω) hDisj) ∘
            (valuesEquivOfEq (Ω := swigΩ Ω) hAB.symm) := by
    funext ω i
    rfl
  have hmarg :
      (Causalean.SCM.jointRef ref D).map (valuesProjection hsubset)
        = (Causalean.SCM.jointRef ref (D \ H.prefixIn D k) Set.univ)
            • Causalean.SCM.jointRef ref (H.prefixIn D k) := by
    rw [hfun]
    rw [← MeasureTheory.Measure.map_map measurable_fst
        ((valuesUnionEquiv (Ω := Ω) hDisj).measurable.comp
          (valuesEquivOfEq (Ω := swigΩ Ω) hAB.symm).measurable)]
    rw [← MeasureTheory.Measure.map_map
        (valuesUnionEquiv (Ω := Ω) hDisj).measurable
        (valuesEquivOfEq (Ω := swigΩ Ω) hAB.symm).measurable]
    rw [Causalean.SCM.jointRef,
      Causalean.SCM.map_pi_valuesEquivOfEq hAB.symm
        (fun i : {i // i ∈ D} => ref.μ i.val)]
    have hsplit :
        (MeasureTheory.Measure.pi
            (fun j : {j // j ∈ H.prefixIn D k ∪ (D \ H.prefixIn D k)} =>
              ref.μ j.val)).map (valuesUnionEquiv (Ω := Ω) hDisj)
          = (Causalean.SCM.jointRef ref (H.prefixIn D k)).prod
              (Causalean.SCM.jointRef ref (D \ H.prefixIn D k)) := by
      have hmp := Causalean.SCM.measurePreserving_valuesUnionEquiv (Ω := Ω) hDisj ref.μ
      simpa [Causalean.SCM.jointRef] using hmp.map_eq
    rw [hsplit, MeasureTheory.Measure.map_fst_prod]
  rw [hmarg]
  intro t ht
  simp [MeasureTheory.Measure.smul_apply, ht]

/-- Domination of a dominated law's prefix marginal by the prefix reference. -/
lemma measure_map_prefixIn_absolutelyContinuous_jointRef
    (H : SWIGGraph N) (D : Finset (SWIGNode N))
    (μ : MeasureTheory.Measure (ValuesOn D (swigΩ Ω)))
    (ref : Causalean.SCM.ReferenceMeasures Ω)
    (hdom : μ ≪ Causalean.SCM.jointRef ref D)
    (k : ℕ) :
    μ.map (valuesProjection (H.prefixIn_subset D k))
      ≪ Causalean.SCM.jointRef ref (H.prefixIn D k) := by
  exact ((hdom.map (measurable_valuesProjection (H.prefixIn_subset D k))).trans
    (jointRef_map_prefixIn_absolutelyContinuous H D ref k))

/-- For [a finite population of variables](hyp:N) with [measurable value spaces](hyp:Ω),
[a SWIG graph](hyp:H), [a finite node set](hyp:D), [a finite measure on its joint value
space](hyp:μ), and [reference measures](hyp:ref), assuming every graph-ordered singleton
node value space is standard Borel and nonempty, [the Tian prefix density product](goal) at
[a prefix length and an assignment on that prefix](hyp:k) is one [at length zero](step:1) and
otherwise [the preceding product multiplied by the next conditional-density factor, with that factor taken as one when its index is outside the node set](step:2).

Recursive Tian prefix density product on an intermediate prefix. -/
noncomputable def tianPrefixDensityProductInPrefix
    (H : SWIGGraph N) (D : Finset (SWIGNode N))
    (μ : MeasureTheory.Measure (ValuesOn D (swigΩ Ω)))
    (ref : Causalean.SCM.ReferenceMeasures Ω)
    [MeasureTheory.IsFiniteMeasure μ]
    [∀ (k : ℕ) (hk : k < D.card),
      StandardBorelSpace
        (ValuesOn ({(H.nodesAt D ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < D.card),
      Nonempty
        (ValuesOn ({(H.nodesAt D ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))] :
    (k : ℕ) → ValuesOn (H.prefixIn D k) (swigΩ Ω) → ENNReal
  | 0, _ => 1
  | k + 1, z =>
      tianPrefixDensityProductInPrefix H D μ ref k
        (valuesProjection (prefixIn_mono H D (Nat.le_succ k)) z) *
        if hk : k < D.card then
          ((ProbabilityTheory.condDistrib
              (valuesProjection
                (show ({(H.nodesAt D ⟨k, hk⟩).val} : Finset (SWIGNode N)) ⊆ D from by
                  intro v hv
                  rw [Finset.mem_singleton] at hv
                  exact hv ▸ (H.nodesAt D ⟨k, hk⟩).property))
              (valuesProjection (H.prefixIn_subset D k))
              μ)
              (valuesProjection (prefixIn_mono H D (Nat.le_succ k)) z)).rnDeriv
            (Causalean.SCM.jointRef ref
              ({(H.nodesAt D ⟨k, hk⟩).val} : Finset (SWIGNode N)))
            (valuesProjection
              (show ({(H.nodesAt D ⟨k, hk⟩).val} : Finset (SWIGNode N)) ⊆
                  H.prefixIn D (k + 1) from by
                intro v hv
                rw [Finset.mem_singleton] at hv
                subst hv
                rw [nodesAt_mem_prefixIn_iff H D (k + 1) ⟨k, hk⟩]
                exact Nat.lt_succ_self k) z)
        else
          1

/-- For [a finite population of variables](hyp:N) with [measurable value spaces](hyp:Ω),
[a SWIG graph](hyp:H), [a finite node set](hyp:D), [a finite measure on its joint value
space](hyp:μ), [reference measures](hyp:ref), assuming every graph-ordered singleton node
value space is standard Borel and nonempty, [a prefix length](hyp:k), [an assignment on that
prefix](hyp:z), and [a node index](hyp:i), [the one-step Tian density](goal) is the
conditional-density factor for that indexed node when it lies in both the prefix and the node
set, and is one otherwise.

One-step Tian density read from a `k`-prefix assignment. -/
noncomputable def tianPrefixStepDensityInPrefix
    (H : SWIGGraph N) (D : Finset (SWIGNode N))
    (μ : MeasureTheory.Measure (ValuesOn D (swigΩ Ω)))
    (ref : Causalean.SCM.ReferenceMeasures Ω)
    [MeasureTheory.IsFiniteMeasure μ]
    [∀ (i : ℕ) (hi : i < D.card),
      StandardBorelSpace
        (ValuesOn ({(H.nodesAt D ⟨i, hi⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (i : ℕ) (hi : i < D.card),
      Nonempty
        (ValuesOn ({(H.nodesAt D ⟨i, hi⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    (k : ℕ) (z : ValuesOn (H.prefixIn D k) (swigΩ Ω)) (i : ℕ) : ENNReal :=
  if hi : i < k then
    if hcard : i < D.card then
      ((ProbabilityTheory.condDistrib
          (valuesProjection
            (show ({(H.nodesAt D ⟨i, hcard⟩).val} : Finset (SWIGNode N)) ⊆ D from by
              intro v hv
              rw [Finset.mem_singleton] at hv
              exact hv ▸ (H.nodesAt D ⟨i, hcard⟩).property))
          (valuesProjection (H.prefixIn_subset D i))
          μ)
          (valuesProjection (prefixIn_mono H D (Nat.le_of_lt hi)) z)).rnDeriv
        (Causalean.SCM.jointRef ref
          ({(H.nodesAt D ⟨i, hcard⟩).val} : Finset (SWIGNode N)))
        (valuesProjection
          (show ({(H.nodesAt D ⟨i, hcard⟩).val} : Finset (SWIGNode N)) ⊆
              H.prefixIn D k from by
            intro v hv
            rw [Finset.mem_singleton] at hv
            subst hv
            rw [nodesAt_mem_prefixIn_iff H D k ⟨i, hcard⟩]
            exact hi) z)
    else
      1
  else
    1

/-- The recursive prefix density product is the range product of its one-step
factors. -/
lemma tianPrefixDensityProductInPrefix_eq_range_product
    (H : SWIGGraph N) (D : Finset (SWIGNode N))
    (μ : MeasureTheory.Measure (ValuesOn D (swigΩ Ω)))
    (ref : Causalean.SCM.ReferenceMeasures Ω)
    [MeasureTheory.IsFiniteMeasure μ]
    [∀ (k : ℕ) (hk : k < D.card),
      StandardBorelSpace
        (ValuesOn ({(H.nodesAt D ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < D.card),
      Nonempty
        (ValuesOn ({(H.nodesAt D ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    (k : ℕ) (hk : k ≤ D.card)
    (z : ValuesOn (H.prefixIn D k) (swigΩ Ω)) :
    tianPrefixDensityProductInPrefix H D μ ref k z =
      ∏ i ∈ Finset.range k, tianPrefixStepDensityInPrefix H D μ ref k z i := by
  induction k with
  | zero =>
      simp [tianPrefixDensityProductInPrefix]
  | succ k ih =>
      have hkcard : k < D.card := Nat.lt_of_succ_le hk
      rw [tianPrefixDensityProductInPrefix]
      rw [ih (Nat.le_of_succ_le hk)
        (valuesProjection (prefixIn_mono H D (Nat.le_succ k)) z)]
      rw [Finset.prod_range_succ]
      congr 1
      · refine Finset.prod_congr rfl ?_
        intro i hi
        have hik : i < k := Finset.mem_range.mp hi
        have hisucc : i < k + 1 := Nat.lt_succ_of_lt hik
        have hicard : i < D.card := lt_of_lt_of_le hik (Nat.le_of_succ_le hk)
        have hproj :
            valuesProjection (prefixIn_mono H D (Nat.le_of_lt hik))
                (valuesProjection (prefixIn_mono H D (Nat.le_succ k)) z)
              =
            valuesProjection (prefixIn_mono H D (Nat.le_of_lt hisucc)) z := by
          funext a
          rfl
        have hnode :
            valuesProjection
                (show ({(H.nodesAt D ⟨i, hicard⟩).val} : Finset (SWIGNode N)) ⊆
                    H.prefixIn D k from by
                  intro v hv
                  rw [Finset.mem_singleton] at hv
                  subst hv
                  rw [nodesAt_mem_prefixIn_iff H D k ⟨i, hicard⟩]
                  exact hik)
                (valuesProjection (prefixIn_mono H D (Nat.le_succ k)) z)
              =
            valuesProjection
                (show ({(H.nodesAt D ⟨i, hicard⟩).val} : Finset (SWIGNode N)) ⊆
                    H.prefixIn D (k + 1) from by
                  intro v hv
                  rw [Finset.mem_singleton] at hv
                  subst hv
                  rw [nodesAt_mem_prefixIn_iff H D (k + 1) ⟨i, hicard⟩]
                  exact hisucc) z := by
          funext a
          rfl
        simp [tianPrefixStepDensityInPrefix, hik, hisucc, hicard, hproj, hnode]
      · simp [tianPrefixStepDensityInPrefix, hkcard]

/-- For [a finite acyclic graph with measurable node-value spaces](hyp:N,Ω,H), [a finite node
set](hyp:D), [a finite law on that set](hyp:μ), [coordinate reference measures](hyp:ref), and
[a realization of the node values](hyp:y), [the recursive density product at the full graph-
ordered prefix equals Tian's finite product over all node positions](goal).

At the full `D` prefix, the recursive prefix density product is Tian's finite product over all
`D` indices. -/
lemma tianPrefixDensityProductInPrefix_card_eq_tianDensityProduct
    (H : SWIGGraph N) (D : Finset (SWIGNode N))
    (μ : MeasureTheory.Measure (ValuesOn D (swigΩ Ω)))
    (ref : Causalean.SCM.ReferenceMeasures Ω)
    [MeasureTheory.IsFiniteMeasure μ]
    [∀ (k : ℕ) (hk : k < D.card),
      StandardBorelSpace
        (ValuesOn ({(H.nodesAt D ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < D.card),
      Nonempty
        (ValuesOn ({(H.nodesAt D ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    (y : ValuesOn (H.prefixIn D D.card) (swigΩ Ω)) :
    tianPrefixDensityProductInPrefix H D μ ref D.card y =
      tianDensityProduct H D μ ref
        ((valuesEquivOfEq (Ω := swigΩ Ω) (prefixIn_card H D)) y) := by
  rw [tianPrefixDensityProductInPrefix_eq_range_product H D μ ref D.card (le_refl _) y]
  rw [Finset.prod_range]
  simp only [tianDensityProduct, tianPrefixStepDensity, tianPrefixStepDensityInPrefix,
    coe_valuesEquivOfEq]
  refine Finset.prod_congr rfl ?_
  intro i _hi
  have hproj :
      valuesProjection (H.prefixIn_subset D i.val)
          (valuesProjection (le_of_eq (prefixIn_card H D).symm) y)
        =
      valuesProjection (prefixIn_mono H D (Nat.le_of_lt i.isLt)) y := by
    funext a
    rfl
  have hnode :
      valuesProjection
          (show ({(H.nodesAt D i).val} : Finset (SWIGNode N)) ⊆ D from by
            intro v hv
            rw [Finset.mem_singleton] at hv
            exact hv ▸ (H.nodesAt D i).property)
          (valuesProjection (le_of_eq (prefixIn_card H D).symm) y)
        =
      valuesProjection
          (show ({(H.nodesAt D i).val} : Finset (SWIGNode N)) ⊆
              H.prefixIn D D.card from by
            intro v hv
            rw [Finset.mem_singleton] at hv
            subst hv
            rw [nodesAt_mem_prefixIn_iff H D D.card i]
            exact i.isLt) y := by
    funext a
    rfl
  simp [i.isLt, hproj, hnode]


end SCM.ID
end Causalean
