/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module

public import Causalean.Mathlib.MeasureTheory.FinsetValues
public import Causalean.Mathlib.MeasureTheory.RnDerivCompProdSigmaFinite
public import Causalean.SCM.ID.Density.FiniteReference
public import Causalean.SCM.ID.Density.PiUnion
public import Causalean.SCM.ID.GraphicalThms.ChainRuleFactorization
public import Mathlib.Probability.Kernel.CompProdEqIff
public import Mathlib.Probability.Kernel.Composition.RadonNikodym
public import Mathlib.Probability.Kernel.RadonNikodym

/-! # Core constructions for the observational chain-rule density

This file defines the measurable fibre Radon--Nikodym data and prefix-density
products used by the chain rule.  It also establishes the reference-measure
reindexing and product-measure Radon--Nikodym lemmas needed for the induction;
the final observational factorization is proved in `RadonNikodym`.
-/

@[expose] public section

open Causalean.Graph


open Causalean.Mathlib.MeasureTheory

namespace Causalean.SCM

open scoped MeasureTheory ProbabilityTheory ENNReal

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- For [a finite collection of distinguishable node labels with measurable
value spaces](hyp:N), [a structural causal model](hyp:M), [a family of $\sigma$-finite reference measures for
its node values](hyp:ref), [a fixed-node assignment](hyp:s), [an observed-node
position](hyp:i), and assuming finite observational kernels, standard-Borel and
nonempty one-node value spaces, and countably generated prefix value spaces,
the [one-node conditional density factor](goal) maps each full observed assignment
to the Radon--Nikodym derivative of the conditional law of the node at that
position, given its preceding observed values, with respect to that node's
reference measure.

The **one-node conditional density factor** at an observed coordinate.

Given a full observed assignment, this reads the prefix before coordinate `i`,
applies the conditional kernel for the next observed node, and takes its
Radon--Nikodym derivative with respect to that node's reference measure. -/
noncomputable def obsStepCondDensity
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω) (s : M.FixedValues)
    (i : Fin M.observed.card)
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [StandardBorelSpace
      (ValuesOn ({(M.observedAt i).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [Nonempty
      (ValuesOn ({(M.observedAt i).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [MeasurableSpace.CountableOrCountablyGenerated
      M.FixedValues (ValuesOn (M.prefixNodes i.val) (swigΩ Ω))] :
    ValuesOn M.observed (swigΩ Ω) → ENNReal :=
  fun x =>
    ((M.obsStepCondKernel i.isLt)
        (s, valuesProjection (M.prefixNodes_subset_observed i.val) x)).rnDeriv
      (ref.μ (M.observedAt i).val)
      (x (M.observedAt i))

/-- For [a finite collection of distinguishable node labels with measurable
value spaces](hyp:N), [a structural causal model](hyp:M), [a family of $\sigma$-finite reference measures for
its node values](hyp:ref), and [a fixed-node assignment](hyp:s), assuming finite
observational kernels, standard-Borel and nonempty one-node value spaces, and
countably generated prefix value spaces, the [chain-rule density product](goal)
maps each full observed assignment to the product of all one-node conditional
density factors in the canonical observed topological order.

The **chain-rule density product** for the observational law.

This is the product, in observed topological order, of the one-node conditional
density factors.  The product is scalar-valued, so later regrouping into
c-components is legitimate in a way that regrouping composed kernels is not. -/
noncomputable def qFactorDensityProduct
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω) (s : M.FixedValues)
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      Nonempty
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        M.FixedValues (ValuesOn (M.prefixNodes k) (swigΩ Ω))] :
    ValuesOn M.observed (swigΩ Ω) → ENNReal :=
  fun x => ∏ i : Fin M.observed.card, M.obsStepCondDensity ref s i x

/-- Prefix node sets are monotone in the prefix length. -/
lemma prefixNodes_mono (M : Causalean.SCM N Ω) {m k : ℕ} (h : m ≤ k) :
    M.prefixNodes m ⊆ M.prefixNodes k := by
  intro v hv
  rcases (M.mem_prefixNodes_iff m v).mp hv with ⟨hobs, hlt⟩
  exact (M.mem_prefixNodes_iff k v).mpr ⟨hobs, lt_of_lt_of_le hlt h⟩

/-- For [a finite collection of distinguishable node labels with measurable
value spaces](hyp:N), [a structural causal model](hyp:M), [a family of $\sigma$-finite reference measures for
its node values](hyp:ref), and [a fixed-node assignment](hyp:s), assuming finite
observational kernels, standard-Borel and nonempty one-node value spaces, and
countably generated prefix value spaces, the [recursive prefix-density product](goal)
maps every prefix length and assignment on that prefix to [the value $1$ for the
empty prefix](step:1), and otherwise [the preceding prefix density multiplied by
the conditional density of the newly appended node, or by $1$ when that position
is not observed](step:2).

The recursive prefix density product matching `obsChainKernel`.

At successor prefixes this multiplies the previous-prefix density by the
one-node conditional RN derivative for the newly adjoined observed node. -/
noncomputable def prefixDensityProduct
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω) (s : M.FixedValues)
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      Nonempty
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        M.FixedValues (ValuesOn (M.prefixNodes k) (swigΩ Ω))] :
    (k : ℕ) → ValuesOn (M.prefixNodes k) (swigΩ Ω) → ENNReal
  | 0, _ => 1
  | k + 1, z =>
      M.prefixDensityProduct ref s k
        (valuesProjection (M.prefixNodes_mono (Nat.le_succ k)) z) *
        if h : k < M.observed.card then
          ((M.obsStepCondKernel h)
              (s, valuesProjection (M.prefixNodes_mono (Nat.le_succ k)) z)).rnDeriv
            (ref.μ (M.observedAt ⟨k, h⟩).val)
            (z ⟨(M.observedAt ⟨k, h⟩).val,
              by
                rw [M.prefixNodes_succ h]
                exact Finset.mem_union_right _
                  (Finset.mem_singleton_self _)⟩)
        else
          1

/-- For [a finite collection of distinguishable node labels with measurable
value spaces](hyp:N), [a structural causal model](hyp:M), [a family of $\sigma$-finite reference measures for
its node values](hyp:ref), and [a fixed-node assignment](hyp:s), assuming finite
observational kernels, standard-Borel and nonempty one-node value spaces, and
countably generated prefix value spaces, the [stepwise fibre Radon--Nikodym
condition](goal) requires that, at every observed position, [the next observed
node is selected](step:1), the product reference measure on its preceding
prefix is formed, the observational law of that prefix is formed,
the conditional kernel of that next node given the prefix is formed,
and that kernel is almost surely dominated by its reference measure under the
prefix law while its fibre derivative is jointly almost-everywhere measurable
under the product reference measure.

Per-step analytic hypotheses needed to expose the fibre Radon--Nikodym
derivative against a σ-finite one-node reference.

The global domination assumption gives joint domination of each successor prefix.
For an infinite σ-finite reference, Mathlib does not currently extract the
corresponding fibre domination or jointly measurable fibre RN representative, so
the chain-rule density theorem carries those as explicit assumptions. -/
def ObsStepFiberRN
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω) (s : M.FixedValues)
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      Nonempty
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        M.FixedValues (ValuesOn (M.prefixNodes k) (swigΩ Ω))] :
    Prop :=
  ∀ (k : ℕ) (hk : k < M.observed.card),
    let node : SWIGNode N := (M.observedAt ⟨k, hk⟩).val
    let νk : MeasureTheory.Measure (ValuesOn (M.prefixNodes k) (swigΩ Ω)) :=
      jointRef ref (M.prefixNodes k)
    let chain : MeasureTheory.Measure (ValuesOn (M.prefixNodes k) (swigΩ Ω)) :=
      M.obsChainKernel k (Nat.le_of_lt hk) s
    let stepK : ProbabilityTheory.Kernel
        (ValuesOn (M.prefixNodes k) (swigΩ Ω)) (swigΩ Ω node) :=
      (M.obsStepCondKernel hk).sectR s
    (∀ᵐ a ∂chain, stepK a ≪ ref.μ node) ∧
      AEMeasurable
        (fun p : ValuesOn (M.prefixNodes k) (swigΩ Ω) × swigΩ Ω node =>
          (stepK p.1).rnDeriv (ref.μ node) p.2)
        (νk.prod (ref.μ node))

/-- `Measure.pi` reindexes along `valuesEquivOfEq`, with **no** probability-measure
hypothesis (the index equality reduces the equiv to the identity).  This is the
σ-finite-friendly companion of `measurePreserving_valuesEquivOfEq`. -/
lemma map_pi_valuesEquivOfEq {M' : Type*} [DecidableEq M']
    {I J : Finset M'} {Ω' : M' → Type*} [∀ n, MeasurableSpace (Ω' n)]
    (h : I = J) (μ : (i : {i // i ∈ I}) → MeasureTheory.Measure (Ω' i.val)) :
    (MeasureTheory.Measure.pi μ).map (valuesEquivOfEq (Ω := Ω') h)
      = MeasureTheory.Measure.pi (fun j : {j // j ∈ J} => μ ⟨j.val, h ▸ j.property⟩) := by
  subst h
  have hid : (⇑(valuesEquivOfEq (Ω := Ω') (rfl : I = I))
      : ValuesOn I Ω' → ValuesOn I Ω') = id := by
    funext ξ; rfl
  rw [hid, MeasureTheory.Measure.map_id]

/-- The scalar reference on one node maps to the singleton product reference. -/
lemma singletonValues_map_ref_eq_jointRef
    (ref : ReferenceMeasures Ω) (v : SWIGNode N) :
    (ref.μ v).map (singletonValues (α := swigΩ Ω) (v := v))
      = jointRef ref ({v} : Finset (SWIGNode N)) := by
  classical
  rw [jointRef]
  let e := MeasurableEquiv.piUnique
    (fun i : {i // i ∈ ({v} : Finset (SWIGNode N))} => swigΩ Ω i.val)
  have hfun :
      (singletonValues (α := swigΩ Ω) (v := v))
        = (fun x : swigΩ Ω v => (e.symm) (by simpa using x)) := by
    funext x
    ext i
    obtain ⟨w, hw⟩ := i
    have hwv : w = v := by simpa using hw
    subst w
    rfl
  calc
    MeasureTheory.Measure.map (singletonValues (α := swigΩ Ω) (v := v)) (ref.μ v)
        = MeasureTheory.Measure.map
            (fun x : swigΩ Ω v => (e.symm) (by simpa using x)) (ref.μ v) := by
          rw [hfun]
    _ = MeasureTheory.Measure.pi
        (fun i : {i // i ∈ ({v} : Finset (SWIGNode N))} => ref.μ i.val) := by
      have hmp :=
        (MeasureTheory.measurePreserving_piUnique
          (fun i : {i // i ∈ ({v} : Finset (SWIGNode N))} => ref.μ i.val)).symm e
      simpa using hmp.map_eq

/-- Transport the full-prefix reference measure to the observed-value reference.

This is the final `Measure.pi` reindexing along
`prefixNodes observed.card = observed`. -/
lemma jointRef_prefix_card_map
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω) :
    (jointRef ref (M.prefixNodes M.observed.card)).map
        (valuesEquivOfEq (Ω := swigΩ Ω)
          (M.prefixNodes_card M.observed.card (le_refl _)))
      = jointRef ref M.observed := by
  rw [jointRef, jointRef,
    map_pi_valuesEquivOfEq (M.prefixNodes_card M.observed.card (le_refl _))
      (fun i => ref.μ i.val)]

/-- The successor prefix extension carries the product of the old-prefix reference
and the next-node reference to the successor-prefix reference. -/
lemma jointRef_extendObsPrefix
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω)
    {k : ℕ} (hk : k < M.observed.card) :
    ((jointRef ref (M.prefixNodes k)).prod
        (ref.μ (M.observedAt ⟨k, hk⟩).val)).map (M.extendObsPrefix hk)
      = jointRef ref (M.prefixNodes (k + 1)) := by
  classical
  let v : SWIGNode N := (M.observedAt ⟨k, hk⟩).val
  let A : Finset (SWIGNode N) := M.prefixNodes k
  let B : Finset (SWIGNode N) := ({v} : Finset (SWIGNode N))
  let hDisj : Disjoint A B := by
    simpa [A, B, v] using M.prefixNodes_disjoint_singleton_next hk
  have hsing :
      (ref.μ v).map (singletonValues (α := swigΩ Ω) (v := v)) = jointRef ref B := by
    simpa [B] using singletonValues_map_ref_eq_jointRef (Ω := Ω) ref v
  have hprod :
      ((jointRef ref A).prod (ref.μ v)).map
          (Prod.map id (singletonValues (α := swigΩ Ω) (v := v)))
        = (jointRef ref A).prod (jointRef ref B) := by
    rw [← MeasureTheory.Measure.map_prod_map
      (jointRef ref A) (ref.μ v) measurable_id
        (measurable_singletonValues (α := swigΩ Ω))]
    simp [hsing]
  have hunion :
      ((jointRef ref A).prod (jointRef ref B)).map
          ((valuesUnionEquiv (Ω := Ω) hDisj).symm)
        = jointRef ref (A ∪ B) := by
    have hmp :=
      (measurePreserving_valuesUnionEquiv (Ω := Ω) hDisj ref.μ).symm
        (valuesUnionEquiv (Ω := Ω) hDisj)
    simpa [jointRef] using hmp.map_eq
  unfold extendObsPrefix
  change
    (((jointRef ref A).prod (ref.μ v)).map
      ((valuesEquivOfEq (Ω := swigΩ Ω) (M.prefixNodes_succ hk).symm) ∘
        (fun p : ValuesOn A (swigΩ Ω) × swigΩ Ω v =>
          valuesUnionMk p.1 (singletonValues (α := swigΩ Ω) (v := v) p.2))))
      = jointRef ref (M.prefixNodes (k + 1))
  rw [← MeasureTheory.Measure.map_map]
  · have hinner :
        (fun p : ValuesOn A (swigΩ Ω) × swigΩ Ω v =>
          valuesUnionMk p.1 (singletonValues (α := swigΩ Ω) (v := v) p.2))
          =
        ((fun q : ValuesOn A (swigΩ Ω) × ValuesOn B (swigΩ Ω) =>
            valuesUnionMk q.1 q.2) ∘
          (Prod.map id (singletonValues (α := swigΩ Ω) (v := v)))) := by
      rfl
    rw [hinner]
    rw [← MeasureTheory.Measure.map_map]
    · have hunion_fun :
          (fun q : ValuesOn A (swigΩ Ω) × ValuesOn B (swigΩ Ω) =>
              valuesUnionMk q.1 q.2)
            = ((valuesUnionEquiv (Ω := Ω) hDisj).symm) := by
        rfl
      rw [hunion_fun, hprod, hunion]
      rw [jointRef, map_pi_valuesEquivOfEq]
      rfl
    · exact measurable_valuesUnionMk (Ω := swigΩ Ω)
    · exact measurable_id.prodMap (measurable_singletonValues (α := swigΩ Ω))
  · exact (valuesEquivOfEq (Ω := swigΩ Ω) (M.prefixNodes_succ hk).symm).measurable
  · exact (measurable_valuesUnionMk (Ω := swigΩ Ω)).comp
      (measurable_id.prodMap (measurable_singletonValues (α := swigΩ Ω)))

/-- For [a finite collection of distinguishable node labels with measurable
value spaces](hyp:N), [a structural causal model](hyp:M), [a family of $\sigma$-finite reference measures for
its node values](hyp:ref), [a fixed-node assignment](hyp:s), [a prefix length
$k$](hyp:k), [an assignment on its prefix](hyp:z), and [a natural-number
position $i$](hyp:i), assuming finite observational kernels, standard-Borel
and nonempty one-node value spaces, and countably generated prefix value
spaces, the [prefix-read one-step
density factor](goal) is [the conditional density factor at position $i$ when
$i<k$ and that position is observed](step:1), the value $1$ when $i<k$ but the
position is not observed, and the value $1$ when $i\ge k$. -/
noncomputable def prefixStepDensityInPrefix
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω) (s : M.FixedValues)
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [∀ (i : ℕ) (hi : i < M.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M.observedAt ⟨i, hi⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (i : ℕ) (hi : i < M.observed.card),
      Nonempty
        (ValuesOn ({(M.observedAt ⟨i, hi⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ i : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        M.FixedValues (ValuesOn (M.prefixNodes i) (swigΩ Ω))]
    (k : ℕ) (z : ValuesOn (M.prefixNodes k) (swigΩ Ω)) (i : ℕ) : ENNReal :=
  if hi : i < k then
    if hcard : i < M.observed.card then
      ((M.obsStepCondKernel hcard)
          (s, valuesProjection (M.prefixNodes_mono (Nat.le_of_lt hi)) z)).rnDeriv
        (ref.μ (M.observedAt ⟨i, hcard⟩).val)
        (z ⟨(M.observedAt ⟨i, hcard⟩).val,
          by
            rw [M.observedAt_mem_prefixNodes_iff k ⟨i, hcard⟩]
            exact hi⟩)
    else
      1
  else
    1

/-- The recursive prefix density product is the range product of its one-step
factors. -/
lemma prefixDensityProduct_eq_range_product
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω) (s : M.FixedValues)
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      Nonempty
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        M.FixedValues (ValuesOn (M.prefixNodes k) (swigΩ Ω))]
    (k : ℕ) (hk : k ≤ M.observed.card)
    (z : ValuesOn (M.prefixNodes k) (swigΩ Ω)) :
    M.prefixDensityProduct ref s k z =
      ∏ i ∈ Finset.range k, M.prefixStepDensityInPrefix ref s k z i := by
  induction k with
  | zero =>
      simp [prefixDensityProduct]
  | succ k ih =>
      have hkcard : k < M.observed.card := Nat.lt_of_succ_le hk
      rw [prefixDensityProduct]
      rw [ih (Nat.le_of_succ_le hk)
        (valuesProjection (M.prefixNodes_mono (Nat.le_succ k)) z)]
      rw [Finset.prod_range_succ]
      congr 1
      · refine Finset.prod_congr rfl ?_
        intro i hi
        have hik : i < k := Finset.mem_range.mp hi
        have hisucc : i < k + 1 := Nat.lt_succ_of_lt hik
        have hicard : i < M.observed.card :=
          lt_of_lt_of_le hik (Nat.le_of_succ_le hk)
        have hproj :
            valuesProjection (M.prefixNodes_mono (Nat.le_of_lt hik))
                (valuesProjection (M.prefixNodes_mono (Nat.le_succ k)) z)
              =
            valuesProjection (M.prefixNodes_mono (Nat.le_of_lt hisucc)) z := by
          funext a
          rfl
        simp [prefixStepDensityInPrefix, hik, hisucc, hicard, hproj, valuesProjection]
      · simp [prefixStepDensityInPrefix, hkcard]

/-- At the full observed prefix, the recursive prefix density product is the
existing finite product over observed indices. -/
lemma prefixDensityProduct_card_eq_qFactorDensityProduct
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω) (s : M.FixedValues)
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      Nonempty
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        M.FixedValues (ValuesOn (M.prefixNodes k) (swigΩ Ω))]
    (y : ValuesOn (M.prefixNodes M.observed.card) (swigΩ Ω)) :
    M.prefixDensityProduct ref s M.observed.card y =
      M.qFactorDensityProduct ref s
        ((valuesEquivOfEq (Ω := swigΩ Ω)
          (M.prefixNodes_card M.observed.card (le_refl _))) y) := by
  rw [prefixDensityProduct_eq_range_product M ref s M.observed.card (le_refl _) y]
  rw [Finset.prod_range]
  simp only [qFactorDensityProduct, obsStepCondDensity, prefixStepDensityInPrefix,
    valuesEquivOfEq]
  refine Finset.prod_congr rfl ?_
  intro i _hi
  have hproj :
      valuesProjection (M.prefixNodes_subset_observed i.val)
          (valuesProjection
            (le_of_eq (M.prefixNodes_card M.observed.card (le_refl _)).symm) y)
        =
      valuesProjection (M.prefixNodes_mono (Nat.le_of_lt i.isLt)) y := by
    funext a
    rfl
  simp only [i.isLt]
  rfl

/-- **Conditional factor of the composition-product Radon–Nikodym derivative.**

For composition-products with the *same* first measure `μ`, the density of
`μ ⊗ₘ κ` against `μ ⊗ₘ η` is the per-slice (kernel) Radon–Nikodym derivative
`dκ/dη`.  This is the disintegration form Mathlib's `rnDeriv_compProd` leaves
implicit; it is what turns the second factor there into a one-step conditional
density. -/
lemma rnDeriv_compProd_same_left {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace.CountableOrCountablyGenerated α β]
    (μ : MeasureTheory.Measure α)
    (κ η : ProbabilityTheory.Kernel α β)
    [MeasureTheory.IsFiniteMeasure μ]
    [ProbabilityTheory.IsFiniteKernel κ] [ProbabilityTheory.IsFiniteKernel η]
    (h_ac : ∀ a, κ a ≪ η a) :
    (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η)
      =ᵐ[μ ⊗ₘ η] fun p => ProbabilityTheory.Kernel.rnDeriv κ η p.1 p.2 := by
  have hκeq : η.withDensity (ProbabilityTheory.Kernel.rnDeriv κ η) = κ :=
    ProbabilityTheory.Kernel.ext fun a =>
      ProbabilityTheory.Kernel.withDensity_rnDeriv_eq (h_ac a)
  haveI : ProbabilityTheory.IsSFiniteKernel
      (η.withDensity (ProbabilityTheory.Kernel.rnDeriv κ η)) := by
    rw [hκeq]; infer_instance
  have hcp : μ ⊗ₘ κ
      = (μ ⊗ₘ η).withDensity (fun p => ProbabilityTheory.Kernel.rnDeriv κ η p.1 p.2) := by
    conv_lhs => rw [← hκeq]
    exact MeasureTheory.Measure.compProd_withDensity
      (ProbabilityTheory.Kernel.measurable_rnDeriv κ η)
  rw [hcp]
  exact MeasureTheory.Measure.rnDeriv_withDensity (μ ⊗ₘ η)
    (ProbabilityTheory.Kernel.measurable_rnDeriv κ η)

/-- Pull absolute continuity back through a measurable embedding. -/
lemma absolutelyContinuous_of_map_measurableEmbedding {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {f : α → β}
    (hf : MeasurableEmbedding f) {μ ν : MeasureTheory.Measure α}
    (h : μ.map f ≪ ν.map f) :
    μ ≪ ν := by
  intro A hνA
  have hν_image : ν.map f (f '' A) = 0 := by
    rw [hf.map_apply ν (f '' A), hf.injective.preimage_image]
    exact hνA
  have hμ_image : μ.map f (f '' A) = 0 := h hν_image
  rw [hf.map_apply μ (f '' A), hf.injective.preimage_image] at hμ_image
  exact hμ_image

/-- Same-left composition-product RN derivative under a.e. fibre absolute
continuity.  This is the a.e. variant needed after extracting fibre domination
from product domination. -/
lemma rnDeriv_compProd_same_left_ae {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace.CountableOrCountablyGenerated α β]
    (μ : MeasureTheory.Measure α)
    (κ η : ProbabilityTheory.Kernel α β)
    [MeasureTheory.IsFiniteMeasure μ]
    [ProbabilityTheory.IsFiniteKernel κ] [ProbabilityTheory.IsFiniteKernel η]
    (h_ac : ∀ᵐ a ∂μ, κ a ≪ η a) :
    (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η)
      =ᵐ[μ ⊗ₘ η] fun p => ProbabilityTheory.Kernel.rnDeriv κ η p.1 p.2 := by
  have hκeq : κ =ᵐ[μ]
      η.withDensity (ProbabilityTheory.Kernel.rnDeriv κ η) := by
    filter_upwards [h_ac] with a ha
    exact (ProbabilityTheory.Kernel.withDensity_rnDeriv_eq ha).symm
  haveI : ProbabilityTheory.IsSFiniteKernel
      (η.withDensity (ProbabilityTheory.Kernel.rnDeriv κ η)) := by
    infer_instance
  have hcp : μ ⊗ₘ κ
      = (μ ⊗ₘ η).withDensity (fun p => ProbabilityTheory.Kernel.rnDeriv κ η p.1 p.2) := by
    calc
      μ ⊗ₘ κ = μ ⊗ₘ
          (η.withDensity (ProbabilityTheory.Kernel.rnDeriv κ η)) :=
        MeasureTheory.Measure.compProd_congr hκeq
      _ = (μ ⊗ₘ η).withDensity
          (fun p => ProbabilityTheory.Kernel.rnDeriv κ η p.1 p.2) := by
        exact MeasureTheory.Measure.compProd_withDensity
          (ProbabilityTheory.Kernel.measurable_rnDeriv κ η)
  rw [hcp]
  exact MeasureTheory.Measure.rnDeriv_withDensity (μ ⊗ₘ η)
    (ProbabilityTheory.Kernel.measurable_rnDeriv κ η)

/-- For [two measurable spaces](hyp:α,β), [a finite source measure, a source reference
measure, a target reference measure, a finite transition kernel, and a proposed source
density](hyp:μ,ν,ρ,κ,f), if [the source measure is dominated by its reference](hyp:hμν),
[almost every transition fibre is dominated by the target reference](hyp:hfiber), [the fibre
density is jointly almost-everywhere measurable](hyp:hfiber_meas), and [the proposed source
density is the source Radon–Nikodym derivative](hyp:hf), then [the joint composition-product
density is almost surely the product of the source and conditional densities](goal).

σ-finite product-reference RN derivative for a finite kernel, under explicit
fibre domination and fibre-density measurability.

This is the measure-level replacement for `ProbabilityTheory.rnDeriv_compProd`
when the second reference is a σ-finite measure, not a finite kernel. -/
lemma rnDeriv_compProd_prod_sigmaFinite_of_fiber_ac {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (μ ν : MeasureTheory.Measure α) (ρ : MeasureTheory.Measure β)
    (κ : ProbabilityTheory.Kernel α β)
    (f : α → ENNReal)
    [MeasureTheory.IsFiniteMeasure μ]
    [MeasureTheory.SigmaFinite ν] [MeasureTheory.SigmaFinite ρ]
    [ProbabilityTheory.IsFiniteKernel κ]
    (hμν : μ ≪ ν) (hfiber : ∀ᵐ a ∂μ, κ a ≪ ρ)
    (hfiber_meas :
      AEMeasurable
        (fun p : α × β => (κ p.1).rnDeriv ρ p.2) (ν.prod ρ))
    (hf : μ.rnDeriv ν =ᵐ[ν] f) :
    (μ ⊗ₘ κ).rnDeriv (ν.prod ρ)
      =ᵐ[ν.prod ρ] fun p => f p.1 * (κ p.1).rnDeriv ρ p.2 := by
  exact MeasureTheory.rnDeriv_compProd_prod_sigmaFinite
    μ ν ρ κ f hμν hfiber hfiber_meas hf

end Causalean.SCM
