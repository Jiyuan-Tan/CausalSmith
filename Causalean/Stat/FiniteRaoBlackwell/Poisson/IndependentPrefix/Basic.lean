/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.Basic

/-!
# Independent unequal Poisson prefixes

This module provides the measurable sample spaces and deterministic maps used to
Poissonize two independent fixed iid pools.  The pools may have different
capacities and observation spaces.  It also identifies the exact joint law of
the two untruncated Poisson prefixes and the jointly nonoverflowing part of the
capped construction.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

universe uX uY

variable {X : Type uX} {Y : Type uY}
  [MeasurableSpace X] [MeasurableSpace Y]

/-- Given [the first pool capacity](hyp:NX) and [the second pool capacity](hyp:NY),
[two fixed observation pools](goal) are given by ordered pools whose capacities may differ.
[They are represented by the product of the two ordered pools](step:1). -/
abbrev FixedPools (NX NY : ℕ) := (Fin NX → X) × (Fin NY → Y)

/-- Given [the first pool capacity](hyp:NX) and [the second pool capacity](hyp:NY),
[the randomized two-pool experiment](goal) attaches an independent requested prefix length to
each fixed pool. [It is represented by the pair of pool-length pairs](step:1). -/
abbrev RandomizedPools (NX NY : ℕ) :=
  ((Fin NX → X) × ℕ) × ((Fin NY → Y) × ℕ)

/-- Given [a probability law for the first observations](hyp:P), [a probability law for the
second observations](hyp:Q), [the first pool capacity](hyp:NX), and [the second pool
capacity](hyp:NY), [the independent fixed-pool law](goal) is the product of the two iid
pool laws. [It is given by their product measure](step:1). -/
noncomputable def fixedPoolsLaw
    (P : Measure X) [IsProbabilityMeasure P]
    (Q : Measure Y) [IsProbabilityMeasure Q] (NX NY : ℕ) :
    Measure (FixedPools (X := X) (Y := Y) NX NY) :=
  (Measure.pi (fun _ : Fin NX ↦ P)).prod
    (Measure.pi (fun _ : Fin NY ↦ Q))

/-- Given [probability laws for the first and second observations](hyp:P,Q), [the first
Poisson intensity](hyp:lambdaX), [the second Poisson intensity](hyp:lambdaY), [the first
pool capacity](hyp:NX), and [the second pool capacity](hyp:NY), [the randomized-pool law](goal)
has independent iid pools and independent Poisson requested lengths. [It is given by the
product of both pool-count laws](step:1). -/
noncomputable def randomizedPoolsLaw
    (P : Measure X) [IsProbabilityMeasure P]
    (Q : Measure Y) [IsProbabilityMeasure Q]
    (lambdaX lambdaY : ℝ≥0) (NX NY : ℕ) :
    Measure (RandomizedPools (X := X) (Y := Y) NX NY) :=
  ((Measure.pi (fun _ : Fin NX ↦ P)).prod (poissonMeasure lambdaX)).prod
    ((Measure.pi (fun _ : Fin NY ↦ Q)).prod (poissonMeasure lambdaY))

/-- Given [a probability law for the first observations](hyp:P), [a probability law for the
second observations](hyp:Q), [the first Poisson intensity](hyp:lambdaX), and [the second
Poisson intensity](hyp:lambdaY), [the independent Poisson-prefix law](goal) is the joint law
of two untruncated iid prefixes. [It is given by their product law](step:1). -/
noncomputable def independentPoissonPrefixLaw
    (P : Measure X) [IsProbabilityMeasure P]
    (Q : Measure Y) [IsProbabilityMeasure Q]
    (lambdaX lambdaY : ℝ≥0) : Measure (FiniteSample X × FiniteSample Y) :=
  (finitePoissonSampleLaw P lambdaX).prod
    (finitePoissonSampleLaw Q lambdaY)

/-- Given [the first pool capacity](hyp:NX) and [the second pool capacity](hyp:NY), [the
joint nonoverflow event](goal) says that both requested prefixes fit in their respective
pools. [It is given by the conjunction of the two capacity bounds](step:1). -/
def nonoverflowSet (NX NY : ℕ) :
    Set (RandomizedPools (X := X) (Y := Y) NX NY) :=
  {z | z.1.2 ≤ NX ∧ z.2.2 ≤ NY}

/-- Given [the first pool capacity](hyp:NX) and [the second pool capacity](hyp:NY), [the
overflow event](goal) says that at least one requested prefix is too long. [It is given by the
union of the two marginal overflow events](step:1). -/
def overflowSet (NX NY : ℕ) :
    Set (RandomizedPools (X := X) (Y := Y) NX NY) :=
  {z | NX < z.1.2} ∪ {z | NY < z.2.2}

/-- Given [the first pool capacity](hyp:NX) and [the second pool capacity](hyp:NY), [the
joint nonoverflow event is measurable](goal). -/
theorem measurableSet_nonoverflowSet (NX NY : ℕ) :
    MeasurableSet (nonoverflowSet (X := X) (Y := Y) NX NY) := by
  change MeasurableSet
    (((fun z : RandomizedPools (X := X) (Y := Y) NX NY ↦ z.1.2) ⁻¹' Set.Iic NX) ∩
      ((fun z : RandomizedPools (X := X) (Y := Y) NX NY ↦ z.2.2) ⁻¹' Set.Iic NY))
  have hX : Measurable
      (fun z : RandomizedPools (X := X) (Y := Y) NX NY ↦ z.1.2) := by
    fun_prop
  have hY : Measurable
      (fun z : RandomizedPools (X := X) (Y := Y) NX NY ↦ z.2.2) := by
    fun_prop
  exact (hX measurableSet_Iic).inter (hY measurableSet_Iic)

/-- Given [the first pool capacity](hyp:NX) and [the second pool capacity](hyp:NY), [the
union of the two overflow events is measurable](goal). -/
theorem measurableSet_overflowSet (NX NY : ℕ) :
    MeasurableSet (overflowSet (X := X) (Y := Y) NX NY) := by
  change MeasurableSet
    (((fun z : RandomizedPools (X := X) (Y := Y) NX NY ↦ z.1.2) ⁻¹' Set.Ioi NX) ∪
      ((fun z : RandomizedPools (X := X) (Y := Y) NX NY ↦ z.2.2) ⁻¹' Set.Ioi NY))
  have hX : Measurable
      (fun z : RandomizedPools (X := X) (Y := Y) NX NY ↦ z.1.2) := by
    fun_prop
  have hY : Measurable
      (fun z : RandomizedPools (X := X) (Y := Y) NX NY ↦ z.2.2) := by
    fun_prop
  exact (hX measurableSet_Ioi).union (hY measurableSet_Ioi)

/-- Given [the first pool capacity](hyp:NX) and [the second pool capacity](hyp:NY), [joint
nonoverflow is exactly the complement of either marginal overflow](goal). -/
theorem nonoverflowSet_eq_compl_overflowSet (NX NY : ℕ) :
    nonoverflowSet (X := X) (Y := Y) NX NY =
      (overflowSet (X := X) (Y := Y) NX NY)ᶜ := by
  ext z
  simp [nonoverflowSet, overflowSet, not_lt]

/-- Given [a fallback first prefix](hyp:overflowX), [a fallback second prefix](hyp:overflowY),
and [a randomized two-pool outcome](hyp:z), [the totalized prefix pair](goal) retains both
requested prefixes when possible and uses the corresponding fallback otherwise. [It is given
by applying the one-pool totalization in each coordinate](step:1). -/
def totalizedPrefixPair {NX NY : ℕ}
    (overflowX : FiniteSample X) (overflowY : FiniteSample Y)
    (z : RandomizedPools (X := X) (Y := Y) NX NY) :
    FiniteSample X × FiniteSample Y :=
  (totalizedPrefix overflowX z.1.1 z.1.2,
    totalizedPrefix overflowY z.2.1 z.2.2)

/-- Given [a fallback first prefix](hyp:overflowX) and [a fallback second prefix](hyp:overflowY),
[the totalized prefix pair is measurable](goal). -/
@[fun_prop]
theorem measurable_totalizedPrefixPair {NX NY : ℕ}
    (overflowX : FiniteSample X) (overflowY : FiniteSample Y) :
    Measurable (totalizedPrefixPair (NX := NX) (NY := NY) overflowX overflowY) := by
  exact (measurable_totalizedPrefix overflowX).prodMap
    (measurable_totalizedPrefix overflowY)

/-- Given [a two-prefix statistic](hyp:T), [a fallback value](hyp:zOver), and [a randomized
two-pool outcome](hyp:z), [the capped-prefix statistic](goal) uses the genuine prefixes when
both fit and the fallback when either overflows. [It is given by the two capacity tests](step:1). -/
def cappedPrefixStatistic {NX NY : ℕ}
    (T : (FiniteSample X × FiniteSample Y) → ℝ) (zOver : ℝ)
    (z : RandomizedPools (X := X) (Y := Y) NX NY) : ℝ :=
  if hX : z.1.2 ≤ NX then
    if hY : z.2.2 ≤ NY then
      T (prefixOfLE z.1.1 z.1.2 hX, prefixOfLE z.2.1 z.2.2 hY)
    else zOver
  else zOver

/-- Given [a measurable two-prefix statistic](hyp:hT) and [a fallback value](hyp:zOver), [the
capped-prefix statistic is measurable](goal) on the two fixed pools and their independent
requested lengths. -/
@[fun_prop]
theorem measurable_cappedPrefixStatistic {NX NY : ℕ}
    {T : (FiniteSample X × FiniteSample Y) → ℝ} (hT : Measurable T)
    (zOver : ℝ) :
    Measurable (cappedPrefixStatistic (NX := NX) (NY := NY) T zOver) := by
  -- First expose the two count coordinates using
  -- `measurable_from_prod_countable_left` (twice, after reassociation).
  -- For fixed counts, split on the two bounds; the genuine branch is `hT`
  -- composed with the product of the two `measurable_prefixOfLE` maps, while
  -- every overflow branch is constant.
  let g : ((((Fin NX → X) × ℕ) × (Fin NY → Y)) × ℕ) → ℝ := fun z ↦
    cappedPrefixStatistic T zOver ((z.1.1.1, z.1.1.2), (z.1.2, z.2))
  have hg : Measurable g := by
    apply measurable_from_prod_countable_left
    intro n
    let f : (((Fin NX → X) × (Fin NY → Y)) × ℕ) → ℝ := fun z ↦
      cappedPrefixStatistic T zOver ((z.1.1, z.2), (z.1.2, n))
    have hf : Measurable f := by
      apply measurable_from_prod_countable_left
      intro m
      by_cases hX : m ≤ NX
      · by_cases hY : n ≤ NY
        · rw [show (fun z ↦ f (z, m)) =
              T ∘ Prod.map (fun x ↦ prefixOfLE x m hX)
                (fun y ↦ prefixOfLE y n hY) by
            funext z
            simp only [f, cappedPrefixStatistic, hX, hY, dite_true,
              Function.comp_apply]
            congr]
          exact hT.comp ((measurable_prefixOfLE (X := X) hX).prodMap
            (measurable_prefixOfLE (X := Y) hY))
        · simpa [f, cappedPrefixStatistic, hX, hY] using
            (measurable_const : Measurable (fun _ : (Fin NX → X) × (Fin NY → Y) ↦ zOver))
      · simpa [f, cappedPrefixStatistic, hX] using
          (measurable_const : Measurable (fun _ : (Fin NX → X) × (Fin NY → Y) ↦ zOver))
    exact hf.comp
      (((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
        (measurable_snd.comp measurable_fst))
  exact hg.comp
    ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd))

/-- Given [a two-prefix statistic](hyp:T), [a fallback value](hyp:zOver), [fallback first and
second prefixes](hyp:overflowX,overflowY), [a randomized two-pool outcome](hyp:z), and [a
certificate of no overflow](hyp:hz), [the capped statistic equals the statistic of the
corresponding totalized prefixes](goal). -/
theorem cappedPrefixStatistic_eq_off_overflow {NX NY : ℕ}
    (T : (FiniteSample X × FiniteSample Y) → ℝ) (zOver : ℝ)
    (overflowX : FiniteSample X) (overflowY : FiniteSample Y)
    (z : RandomizedPools (X := X) (Y := Y) NX NY)
    (hz : z ∉ overflowSet (X := X) (Y := Y) NX NY) :
    cappedPrefixStatistic T zOver z =
      T (totalizedPrefixPair overflowX overflowY z) := by
  have hX : z.1.2 ≤ NX := by
    exact Nat.le_of_not_gt fun h ↦ hz (by simp [overflowSet, h])
  have hY : z.2.2 ≤ NY := by
    exact Nat.le_of_not_gt fun h ↦ hz (by simp [overflowSet, h])
  simp [cappedPrefixStatistic, totalizedPrefixPair, totalizedPrefix,
    cappedPrefix, hX, hY]

/-- Given [a probability law for the first stream](hyp:P), [a probability law for the second
stream](hyp:Q), [the first Poisson intensity](hyp:lambdaX), and [the second Poisson
intensity](hyp:lambdaY), [mapping independent iid streams to finite prefixes gives exactly
the product untruncated-prefix law](goal). -/
theorem map_independent_streams_eq_independentPoissonPrefixLaw
    (P : Measure X) [IsProbabilityMeasure P]
    (Q : Measure Y) [IsProbabilityMeasure Q]
    (lambdaX lambdaY : ℝ≥0) :
    Measure.map (Prod.map streamToFiniteSample streamToFiniteSample)
        ((poissonIIDStreamLaw P lambdaX).prod
          (poissonIIDStreamLaw Q lambdaY)) =
      independentPoissonPrefixLaw P Q lambdaX lambdaY := by
  unfold independentPoissonPrefixLaw finitePoissonSampleLaw
  rw [← MeasureTheory.Measure.map_prod_map _ _ measurable_streamToFiniteSample
    measurable_streamToFiniteSample]

/-- Given [probability laws for the first and second pools](hyp:P,Q), [the first and second
Poisson intensities](hyp:lambdaX,lambdaY), [the first and second pool capacities](hyp:NX,NY),
and [fallback first and second prefixes](hyp:overflowX,overflowY), [mapping the jointly
nonoverflowing fixed pools to their totalized prefixes gives the correspondingly restricted
product Poisson-prefix law](goal). -/
theorem map_totalizedPrefixPair_restrict_nonoverflow
    (P : Measure X) [IsProbabilityMeasure P]
    (Q : Measure Y) [IsProbabilityMeasure Q]
    (lambdaX lambdaY : ℝ≥0) (NX NY : ℕ)
    (overflowX : FiniteSample X) (overflowY : FiniteSample Y) :
    Measure.map (totalizedPrefixPair overflowX overflowY)
        ((randomizedPoolsLaw P Q lambdaX lambdaY NX NY).restrict
          (nonoverflowSet (X := X) (Y := Y) NX NY)) =
      (independentPoissonPrefixLaw P Q lambdaX lambdaY).restrict
        ((FiniteSample.count ⁻¹' Set.Iic NX) ×ˢ
          (FiniteSample.count ⁻¹' Set.Iic NY)) := by
  -- Rewrite `nonoverflowSet` as the product of the two marginal good events,
  -- commute product and restriction with `Measure.prod_restrict`, and use
  -- `Measure.map_prod_map`.  Each marginal map is then exactly
  -- `map_totalizedPrefix_restrict_nonoverflow`; fold the target product
  -- restriction back with the same product/restriction identity.
  have hset : nonoverflowSet (X := X) (Y := Y) NX NY =
      (Prod.snd ⁻¹' Set.Iic NX) ×ˢ (Prod.snd ⁻¹' Set.Iic NY) := by
    ext z
    simp [nonoverflowSet]
  rw [hset]
  unfold randomizedPoolsLaw independentPoissonPrefixLaw totalizedPrefixPair
  rw [← Measure.prod_restrict]
  change Measure.map
      (Prod.map
        (fun z : (Fin NX → X) × ℕ ↦ totalizedPrefix overflowX z.1 z.2)
        (fun z : (Fin NY → Y) × ℕ ↦ totalizedPrefix overflowY z.1 z.2))
      _ = _
  rw [← Measure.map_prod_map _ _ (measurable_totalizedPrefix overflowX)
    (measurable_totalizedPrefix overflowY)]
  rw [map_totalizedPrefix_restrict_nonoverflow P lambdaX NX overflowX,
    map_totalizedPrefix_restrict_nonoverflow Q lambdaY NY overflowY,
    Measure.prod_restrict]

end Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix
