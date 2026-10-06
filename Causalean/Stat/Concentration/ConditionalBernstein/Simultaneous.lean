module
public import Causalean.Stat.Concentration.ConditionalBernstein.Fibre

/-!
# Simultaneous finite-family conditional histogram tails

The failure event is a union over all design-cell and outcome-bin pairs. Outside it,
every count deviation is at most `sqrt (2 * pMax * N_c * u) + u` without division.
Finite union bounds require no independence or disjointness between different pairs.
-/

@[expose] public section

namespace Causalean.Stat.Concentration.ConditionalBernstein
open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {D Y C B : Type*} [MeasurableSpace D] [MeasurableSpace Y] {n : ℕ}

/-- The [histogram failure event](goal) records an excessive joint-count deviation for
some [design cell](hyp:key) and [outcome bin](hyp:bins), centered by the [outcome kernel](hyp:K)
and using [the envelope and tail parameter](hyp:pMax,u). -/
def histogramBadEvent (key : D → C) (K : Kernel D Y) (bins : B → Set Y)
    (pMax u : ℝ) : Set ((Fin n → D) × (Fin n → Y)) :=
  {p | ∃ c b, bernsteinRadius (pMax * (cellCount key c p.1 : ℝ)) u <
    |(jointCount key (bins b) c p.1 p.2 : ℝ) - conditionalMean key K (bins b) c p.1|}

/-- With [finite cell and bin families](hyp:C,B),
[measurable cell fibres and bins](hyp:hcell,hbins),
the [histogram failure event](hyp:key,K,bins,pMax,u) is [measurable](goal). -/
theorem measurableSet_histogramBadEvent [Finite C] [Finite B]
    (key : D → C) (K : Kernel D Y) (bins : B → Set Y)
    (hcell : ∀ c, MeasurableSet {d | key d = c})
    (hbins : ∀ b, MeasurableSet (bins b)) (pMax u : ℝ) :
    MeasurableSet (histogramBadEvent (n := n) key K bins pMax u) := by
  simp only [histogramBadEvent, Set.ofPred_exists]
  refine MeasurableSet.iUnion (fun c => MeasurableSet.iUnion (fun b => ?_))
  have hcount : Measurable (fun p : (Fin n → D) × (Fin n → Y) =>
      (cellCount key c p.1 : ℝ)) :=
    (measurable_cellCount_real (n := n) (hcell c)).comp measurable_fst
  have hmean : Measurable (fun p : (Fin n → D) × (Fin n → Y) =>
      conditionalMean key K (bins b) c p.1) :=
    (measurable_conditionalMean (n := n) K (hcell c) (hbins b)).comp measurable_fst
  exact measurableSet_lt
    ((((hcount.const_mul pMax).const_mul 2).mul_const u).sqrt.add_const u)
    ((measurable_jointCount_real (n := n) (hcell c) (hbins b)).sub hmean).abs

/-- Given a [complete design vector](hyp:x), [finite cells and measurable bins](hyp:key,bins,hbins),
and a [Markov outcome kernel](hyp:K) with [bin probabilities bounded on active
coordinates by a nonnegative envelope](hyp:hprob,hpMax), the [conditional probability of
any count deviation exceeding its cell-dependent Bernstein radius is at most twice
the number of pairs times the exponential tail](goal) at [nonnegative tail parameter](hyp:hu).

Express the existential failure event as an indexed union over `C × B`, use
Mathlib's `MeasureTheory.measureReal_iUnion_fintype_le`, then `fibre_pair_tail_le`.
For a pair `q`, the envelope argument is `hprob q.1 q.2`; no cell-fibre
measurability is needed after fixing `x`. Rewrite the preimage/union equality by
set extensionality and `simp [histogramBadEvent]`. Bound the finite sum by
`Finset.sum_le_sum`, then simplify the constant sum using `Fintype.card_prod`
and natural-number casts; `ring` puts the factors in the stated order.
Empty index types are included. Reuse the Mathlib union lemma directly rather
than importing a similarly named lemma from another substrate run.
-/
theorem fibre_simultaneous_tail_le [Fintype C] [Fintype B]
    (key : D → C) (K : Kernel D Y) [IsMarkovKernel K] (bins : B → Set Y)
    (hbins : ∀ b, MeasurableSet (bins b)) (x : Fin n → D)
    {pMax u : ℝ} (hpMax : 0 ≤ pMax) (hu : 0 ≤ u)
    (hprob : ∀ c b i, key (x i) = c → binProbability K (bins b) (x i) ≤ pMax) :
    (Causalean.Stat.finProductKernel n K x).real
      (Prod.mk x ⁻¹' histogramBadEvent key K bins pMax u) ≤
      2 * (Fintype.card C : ℝ) * (Fintype.card B : ℝ) * Real.exp (-u) := by
  classical
  let events : C × B → Set (Fin n → Y) := fun q =>
    {y | bernsteinRadius (pMax * (cellCount key q.1 x : ℝ)) u <
      |(jointCount key (bins q.2) q.1 x y : ℝ) - conditionalMean key K (bins q.2) q.1 x|}
  have hevent : Prod.mk x ⁻¹' histogramBadEvent key K bins pMax u =
      ⋃ q : C × B, events q := by
    ext y
    simp only [histogramBadEvent, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_iUnion,
      events]
    exact ⟨fun ⟨c, b, h⟩ => ⟨(c, b), h⟩, fun ⟨q, h⟩ => ⟨q.1, q.2, h⟩⟩
  rw [hevent]
  calc
    _ ≤ ∑ q : C × B, (Causalean.Stat.finProductKernel n K x).real (events q) :=
      measureReal_iUnion_fintype_le events
    _ ≤ ∑ _q : C × B, 2 * Real.exp (-u) :=
      Finset.sum_le_sum (fun q _ =>
        fibre_pair_tail_le key K q.1 x (hbins q.2) hpMax hu (hprob q.1 q.2))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul,
        Nat.cast_mul]
      ring

/-- Outside the [histogram failure event](hyp:hgood),
[all cell/bin deviations obey their Bernstein radii](goal). -/
theorem simultaneous_deviation_of_not_mem_badEvent
    {key : D → C} {K : Kernel D Y} {bins : B → Set Y} {pMax u : ℝ}
    {p : (Fin n → D) × (Fin n → Y)}
    (hgood : p ∉ histogramBadEvent key K bins pMax u) :
    ∀ c b, |(jointCount key (bins b) c p.1 p.2 : ℝ) -
      conditionalMean key K (bins b) c p.1| ≤
        bernsteinRadius (pMax * (cellCount key c p.1 : ℝ)) u := by
  intro c b
  exact le_of_not_gt (fun h => hgood ⟨c, b, h⟩)

end Causalean.Stat.Concentration.ConditionalBernstein
