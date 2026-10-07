module
public import Causalean.Stat.RandomGraph.Components
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Expected numbers of root-qualified finite components

The final estimate combines root choices, unordered completion choices, the parent-array
envelope, and the fixed-tree probability bound. The count includes only components containing
a distinguished root satisfying its measurable root event. Constants are real and nonnegative;
the underlying event estimates use extended nonnegative measures.

Reference grounding: the spanning-tree union-bound argument appears in Lemma 4.14 of
the 2014 draft of *Foundations of Data Science* (Hopcroft, Kannan),
https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/book-No-Solutions-Aug-21-2014.pdf .
That reference concerns independent edges. Here the edge factors are instead justified by
coordinate-section Tonelli elimination; no edge independence is assumed. We count all parent
arrays rather than using Cayley's sharper enumeration. The primary PDF was fetched and
the lemma and its proof on printed pages 116--117 were checked on 2026-10-01; the
proof explicitly covers connectivity by the union of spanning-tree events. We discard
its additional isolation factor, so it supplies context rather than a premise.
Penrose's *Random Geometric Graphs*,
Chapter 3, is the geometric context; its publisher-hosted chapter was not accessible.
-/

public section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Causalean.Stat.RandomGraph

universe u v

variable {V : Type u} [Fintype V]
variable {X : V → Type v} [∀ i, MeasurableSpace (X i)]

/-- For a [root](hyp:r), [the number of unordered completion sets](goal) of
[size p minus one](hyp:p) is the population size minus one choose p minus one. -/
theorem card_root_completions [DecidableEq V] (r : V) (p : ℕ) :
    (((Finset.univ : Finset V).erase r).powersetCard (p - 1)).card =
      Nat.choose (Fintype.card V - 1) (p - 1) := by
  simp

/-- For [p at least one](hyp:hp), adjoining the [root](hyp:r) to a
[completion set of size p minus one](hyp:hT) [gives a selected set of size p](goal). -/
theorem card_insert_root_of_mem_completions [DecidableEq V] (r : V) (p : ℕ) (hp : 1 ≤ p)
    (T : Finset V) (hT : T ∈ ((Finset.univ : Finset V).erase r).powersetCard (p - 1)) :
    (insert r T).card = p := by
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hT
  have hr : r ∉ T := fun h => (Finset.mem_erase.mp (hsub h)).1 rfl
  rw [Finset.card_insert_of_notMem hr, hcard]
  exact Nat.sub_add_cancel hp

/-- The [witness count for one root and completion set](hyp:M,rootEvent,r,T)
[is integrable](goal) under [coordinate probability laws](hyp:μ), provided the
[root event is measurable](hyp:hroot). -/
@[fun_prop]
theorem integrable_rootTreeWitnessCount
    (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (M : CoordinateGraph X) (rootEvent : ∀ r, Set (X r)) (r : V) (T : Finset V)
    (hroot : MeasurableSet (rootEvent r)) :
    Integrable (rootTreeWitnessCount M rootEvent r T) (Measure.pi μ) := by
  classical
  unfold rootTreeWitnessCount
  dsimp only
  apply integrable_finsetSum
  intro P hP
  by_cases hv : P.Valid
  · simp only [hv, true_and]
    have hm := measurableSet_partialTreeEvent (selectedEmbedding _) P (rootEvent r)
      M.edgeEvent Finset.univ hroot M.measurable_edgeEvent
    apply (integrable_const (1 : ℝ)).mono_nonneg
    · exact (Measurable.ite hm measurable_const measurable_const).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun x => by split_ifs <;> norm_num)
    · exact Filter.Eventually.of_forall (fun x => by split_ifs <;> norm_num)
  · simp only [hv, false_and, ite_false]
    exact integrable_const 0

/-- The [rooted witness count](hyp:M,R,rootEvent,p) [is integrable](goal) under
[coordinate probability laws](hyp:μ) when [root events are measurable](hyp:hroot). -/
@[fun_prop]
theorem integrable_treeWitnessCount [DecidableEq V]
    (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (M : CoordinateGraph X) (R : Finset V) (rootEvent : ∀ r, Set (X r)) (p : ℕ)
    (hroot : ∀ r, MeasurableSet (rootEvent r)) :
    Integrable (treeWitnessCount M R rootEvent p) (Measure.pi μ) := by
  classical
  unfold treeWitnessCount
  apply integrable_finsetSum
  intro r hr
  apply integrable_finsetSum
  intro T hT
  exact integrable_rootTreeWitnessCount μ M rootEvent r T (hroot r)

/-- Under [coordinate probability laws](hyp:μ), the [expected witness count for a root
and completion set](hyp:M,rootEvent,r,T) [is at most the parent-array cardinality times
the fixed-tree mass bound](goal), for [nonnegative constants](hyp:hα,hβ),
[a measurable root event](hyp:hroot), [root mass at most α](hyp:hrootMass), and
[oriented child-section masses at most β](hyp:hsection). -/
theorem integral_rootTreeWitnessCount_le [DecidableEq V]
    (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (M : CoordinateGraph X) (rootEvent : ∀ r, Set (X r)) (r : V) (T : Finset V)
    (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hroot : MeasurableSet (rootEvent r))
    (hrootMass : μ r (rootEvent r) ≤ ENNReal.ofReal α)
    (hsection : ∀ (i j : V), i ≠ j → ∀ y : X j,
      μ i {z | (z, y) ∈ M.edgeEvent i j} ≤ ENNReal.ofReal β) :
    (∫ x, rootTreeWitnessCount M rootEvent r T x ∂Measure.pi μ) ≤
      ((insert r T).card : ℝ) ^ ((insert r T).card - 1) *
        α * β ^ ((insert r T).card - 1) := by
  classical
  let : DecidableEq V := fun a b => Classical.propDecidable (a = b)
  unfold rootTreeWitnessCount
  dsimp only
  have hInt (P : ParentEncoding ↥(insert r T) ⟨r, Finset.mem_insert_self r T⟩) :
      Integrable (fun x => if P.Valid ∧ x ∈ partialTreeEvent (selectedEmbedding _) P
        (rootEvent r) M.edgeEvent Finset.univ then (1 : ℝ) else 0) (Measure.pi μ) := by
    by_cases hv : P.Valid
    · simp only [hv, true_and]
      have hm := measurableSet_partialTreeEvent (selectedEmbedding _) P (rootEvent r)
        M.edgeEvent Finset.univ hroot M.measurable_edgeEvent
      apply (integrable_const (1 : ℝ)).mono_nonneg
      · exact (Measurable.ite hm measurable_const measurable_const).aestronglyMeasurable
      · exact Filter.Eventually.of_forall (fun x => by split_ifs <;> norm_num)
      · exact Filter.Eventually.of_forall (fun x => by split_ifs <;> norm_num)
    · simp only [hv, false_and, ite_false]
      exact integrable_const 0
  rw [integral_finsetSum _ (fun P _ => hInt P)]
  calc
    _ ≤ ∑ _P : ParentEncoding ↥(insert r T) ⟨r, Finset.mem_insert_self r T⟩,
        α * β ^ ((insert r T).card - 1) := by
      apply Finset.sum_le_sum
      intro P hP
      by_cases hv : P.Valid
      · simp only [hv, true_and]
        have hm := measurableSet_partialTreeEvent (selectedEmbedding _) P (rootEvent r)
          M.edgeEvent Finset.univ hroot M.measurable_edgeEvent
        have hb := pi_measure_rooted_tree_event_le μ (selectedEmbedding _) P hv
          (rootEvent r) M.edgeEvent (ENNReal.ofReal α) (ENNReal.ofReal β)
          hroot M.measurable_edgeEvent hrootMass hsection
        have hr := ENNReal.toReal_mono (by finiteness) hb
        change (∫ x, (partialTreeEvent (selectedEmbedding _) P (rootEvent r)
          M.edgeEvent Finset.univ).indicator (fun _ => (1 : ℝ)) x ∂Measure.pi μ) ≤ _
        calc
          _ = (Measure.pi μ).real _ := integral_indicator_one hm
          _ ≤ _ := by
            simpa only [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_pow,
              ENNReal.toReal_ofReal hα, ENNReal.toReal_ofReal hβ, Fintype.card_coe] using hr
      · simp only [hv, false_and, ite_false, integral_zero]
        exact mul_nonneg hα (pow_nonneg hβ _)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, card_parentEncoding,
        Fintype.card_coe, nsmul_eq_mul, Nat.cast_pow]
      convert (by ring :
        ((insert r T).card : ℝ) ^ ((insert r T).card - 1) *
          (α * β ^ ((insert r T).card - 1)) =
        ((insert r T).card : ℝ) ^ ((insert r T).card - 1) *
          α * β ^ ((insert r T).card - 1)) using 1
      congr 7 <;> exact Subsingleton.elim _ _

/-- For an [edge model](hyp:M), [distinguished roots](hyp:R), [root events](hyp:rootEvent), a [size
p](hyp:p) that is [at least one](hyp:hp), and [constants α and β](hyp:α,β) that are
[nonnegative](hyp:hα,hβ), under [independent coordinate probability laws](hyp:μ) with [measurable
root events](hyp:hroot), [root-event probabilities at most α](hyp:hrootMass), and [oriented
child-section probabilities at most β for distinct coordinates](hyp:hsection), [the expected total
rooted witness count is at most n times choose(N minus one, p minus one) times p to the power p
minus one times α times β to the power p minus one](goal). Here n is the root-set size and N the
population size. -/
theorem integral_treeWitnessCount_le [DecidableEq V]
    (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (M : CoordinateGraph X) (R : Finset V) (rootEvent : ∀ r, Set (X r))
    (p : ℕ) (hp : 1 ≤ p) (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hroot : ∀ r, MeasurableSet (rootEvent r))
    (hrootMass : ∀ r ∈ R, μ r (rootEvent r) ≤ ENNReal.ofReal α)
    (hsection : ∀ (i j : V), i ≠ j → ∀ y : X j,
      μ i {z | (z, y) ∈ M.edgeEvent i j} ≤ ENNReal.ofReal β) :
    (∫ x, treeWitnessCount M R rootEvent p x ∂Measure.pi μ) ≤
      (R.card : ℝ) * (Nat.choose (Fintype.card V - 1) (p - 1) : ℝ) *
        (p : ℝ) ^ (p - 1) * α * β ^ (p - 1) := by
  classical
  have hsum : (∫ x, treeWitnessCount M R rootEvent p x ∂Measure.pi μ) =
      ∑ r ∈ R, ∑ T ∈ ((Finset.univ : Finset V).erase r).powersetCard (p - 1),
        ∫ x, rootTreeWitnessCount M rootEvent r T x ∂Measure.pi μ := by
    unfold treeWitnessCount
    rw [integral_finsetSum R (fun r _ => integrable_finsetSum _
      (fun T _ => integrable_rootTreeWitnessCount μ M rootEvent r T (hroot r)))]
    apply Finset.sum_congr rfl
    intro r hr
    exact integral_finsetSum _
      (fun T _ => integrable_rootTreeWitnessCount μ M rootEvent r T (hroot r))
  rw [hsum]
  calc
    (∑ r ∈ R, ∑ T ∈ ((Finset.univ : Finset V).erase r).powersetCard (p - 1),
      ∫ x, rootTreeWitnessCount M rootEvent r T x ∂Measure.pi μ) ≤
        ∑ r ∈ R, ∑ _T ∈ ((Finset.univ : Finset V).erase r).powersetCard (p - 1),
          (p : ℝ) ^ (p - 1) * α * β ^ (p - 1) := by
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro T hT
      have hb := integral_rootTreeWitnessCount_le μ M rootEvent r T α β hα hβ
        (hroot r) (hrootMass r hr) hsection
      simpa only [card_insert_root_of_mem_completions r p hp T hT] using hb
    _ = (R.card : ℝ) * (Nat.choose (Fintype.card V - 1) (p - 1) : ℝ) *
        (p : ℝ) ^ (p - 1) * α * β ^ (p - 1) := by
      simp only [Finset.sum_const, card_root_completions, nsmul_eq_mul]
      ring

/-- For an [edge model](hyp:M), [distinguished roots](hyp:R), [root events](hyp:rootEvent), a [size
p](hyp:p) that is [at least two](hyp:hp), and [constants α and β](hyp:α,β) that are
[nonnegative](hyp:hα,hβ), under [independent coordinate probability laws](hyp:μ) with [measurable
root events](hyp:hroot), [root-event probabilities at most α](hyp:hrootMass), and [oriented
child-section probabilities at most β for distinct coordinates](hyp:hsection), [the expected number
of size-p components containing a distinguished root satisfying its root event is at most n times
choose(N minus one, p minus one) times p to the power p minus one times α times β to the power p
minus one](goal). Here n is the root-set size and N the population size. -/
theorem expected_labeled_component_count_le
    (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (M : CoordinateGraph X) (R : Finset V) (rootEvent : ∀ r, Set (X r))
    (p : ℕ) (hp : 2 ≤ p) (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hroot : ∀ r, MeasurableSet (rootEvent r))
    (hrootMass : ∀ r ∈ R, μ r (rootEvent r) ≤ ENNReal.ofReal α)
    (hsection : ∀ (i j : V), i ≠ j → ∀ y : X j,
      μ i {z | (z, y) ∈ M.edgeEvent i j} ≤ ENNReal.ofReal β) :
    (∫ x, labeledComponentCount M R rootEvent p x ∂Measure.pi μ) ≤
      (R.card : ℝ) * (Nat.choose (Fintype.card V - 1) (p - 1) : ℝ) *
        (p : ℝ) ^ (p - 1) * α * β ^ (p - 1) := by
  classical
  have hp1 : 1 ≤ p := le_trans (by decide : 1 ≤ 2) hp
  exact (integral_mono (integrable_labeledComponentCount μ M R rootEvent p hroot)
    (integrable_treeWitnessCount μ M R rootEvent p hroot)
    (labeledComponentCount_le_treeWitnessCount M R rootEvent p)).trans
      (integral_treeWitnessCount_le μ M R rootEvent p hp1 α β hα hβ hroot hrootMass hsection)

end Causalean.Stat.RandomGraph

