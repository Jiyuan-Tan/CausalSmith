import Causalean.Stat.Quantile.EmpiricalCDF
import Mathlib.Data.Finset.Sort

/-!
# Boolean-marked finite samples

This module defines exact mark words, their selected coordinates, and the
empirical CDF obtained after retaining one Boolean arm.  The definitions are
deterministic and form the reindexing layer for conditional probability
arguments in the companion modules.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Causalean.Stat.Quantile.ConditionalMarkedSubsampleDkw

/-- For [a Boolean word](hyp:w) and [a requested mark](hyp:a), [the selected positions](goal)
are the finite set of coordinates carrying that mark, [as given by filtering all coordinates](step:1). -/
noncomputable def selectedIndices {n : ℕ} (w : Fin n → Bool) (a : Bool) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i => w i = a

/-- For [a Boolean word](hyp:w) and [a requested mark](hyp:a), [the selected count](goal) is
the number of its selected positions, [given by their cardinality](step:1). -/
noncomputable def selectedWordCount {n : ℕ} (w : Fin n → Bool) (a : Bool) : ℕ :=
  (selectedIndices w a).card

/-- For [a Boolean word](hyp:w) and [a requested mark](hyp:a), [the selected-coordinate
embedding](goal) enumerates the selected positions in their original order, [using the ordered
finite-set enumeration](step:1). -/
noncomputable def selectedIndex {n : ℕ} (w : Fin n → Bool) (a : Bool) :
    Fin (selectedWordCount w a) ↪o Fin n :=
  (selectedIndices w a).orderEmbOfFin rfl

/-- For [a Boolean word](hyp:w), [a requested mark](hyp:a), and [a selected-coordinate index](hyp:j),
[the coordinate selected by the embedding carries the requested mark](goal). -/
lemma selectedIndex_mark {n : ℕ} (w : Fin n → Bool) (a : Bool)
    (j : Fin (selectedWordCount w a)) :
    w (selectedIndex w a j) = a := by
  -- Unfold the filtered finset and use `Finset.orderEmbOfFin_mem`.
  classical
  have hj : selectedIndex w a j ∈ selectedIndices w a := by
    unfold selectedIndex
    apply Finset.orderEmbOfFin_mem
  exact (Finset.mem_filter.mp hj).2

/-- For [a Boolean word](hyp:w), [a requested mark](hyp:a), and [a summand function](hyp:f),
[summing over the reindexed selected coordinates equals summing over all requested-mark positions](goal). -/
lemma sum_selectedIndex {n : ℕ} (w : Fin n → Bool) (a : Bool) {R : Type*}
    [AddCommMonoid R] (f : Fin n → R) :
    (∑ j : Fin (selectedWordCount w a), f (selectedIndex w a j)) =
      ∑ i ∈ selectedIndices w a, f i := by
  -- Convert the left sum along `orderIsoOfFin`, then use `sum_subtype`.
  classical
  let hcard : (selectedIndices w a).card = selectedWordCount w a := rfl
  have hidx : selectedIndex w a = (selectedIndices w a).orderEmbOfFin hcard := rfl
  rw [hidx]
  calc
    (∑ j : Fin (selectedWordCount w a), f ((selectedIndices w a).orderEmbOfFin hcard j)) =
        ∑ i : ↥(selectedIndices w a), f i := by
          exact
            Equiv.sum_comp ((selectedIndices w a).orderIsoOfFin hcard).toEquiv
              (fun i : ↥(selectedIndices w a) => f i)
    _ = ∑ i ∈ selectedIndices w a, f i := Finset.sum_coe_sort _ _

/-- For [a marked sample](hyp:Z) and [a Boolean word](hyp:w), [the exact-word event](goal)
is [the set of outcomes whose complete mark vector equals that word](step:1). -/
def wordEvent {Ω : Type*} {n : ℕ} (Z : Fin n → Ω → Bool × ℝ)
    (w : Fin n → Bool) : Set Ω :=
  {ω | ∀ i, (Z i ω).1 = w i}

/-- Given [a marked sample](hyp:Z), [measurability of every marked observation](hyp:hZ), and
[a Boolean word](hyp:w), [the corresponding exact-word event is measurable](goal). -/
lemma measurableSet_wordEvent {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (Z : Fin n → Ω → Bool × ℝ) (hZ : ∀ i, Measurable (Z i)) (w : Fin n → Bool) :
    MeasurableSet (wordEvent Z w) := by
  -- Express the event as a finite intersection of preimages of measurable Bool singletons.
  rw [show wordEvent Z w = ⋂ i, (fun ω => (Z i ω).1) ⁻¹' ({w i} : Set Bool) by
    ext ω
    simp [wordEvent]]
  exact MeasurableSet.iInter fun i =>
    (measurableSet_singleton (w i)).preimage (hZ i).fst

/-- Given [a marked sample](hyp:Z) and [two distinct Boolean words](hyp:hwv), [their exact-word
events are disjoint](goal). -/
lemma disjoint_wordEvent {Ω : Type*} {n : ℕ} (Z : Fin n → Ω → Bool × ℝ)
    {w v : Fin n → Bool} (hwv : w ≠ v) :
    Disjoint (wordEvent Z w) (wordEvent Z v) := by
  -- Choose a coordinate where the two words differ and contradict simultaneous membership.
  apply Set.disjoint_left.2
  intro ω hωw hωv
  apply hwv
  funext i
  exact (hωw i).symm.trans (hωv i)

/-- For [a marked sample](hyp:Z), [the union of all exact-word events is the whole sample space](goal). -/
lemma iUnion_wordEvent {Ω : Type*} {n : ℕ} (Z : Fin n → Ω → Bool × ℝ) :
    (⋃ w : Fin n → Bool, wordEvent Z w) = Set.univ := by
  -- For each outcome choose the word `fun i => (Z i ω).1`.
  ext ω
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨fun i => (Z i ω).1, fun _ => rfl⟩

/-- For [a marked sample](hyp:Z), [a requested mark](hyp:a), and [a sample outcome](hyp:ω),
[the selected count](goal) is [the number of observed coordinates carrying that mark](step:1). -/
noncomputable def selectedCount {Ω : Type*} {n : ℕ}
    (Z : Fin n → Ω → Bool × ℝ) (a : Bool) (ω : Ω) : ℕ := by
  classical
  exact (Finset.univ.filter fun i => (Z i ω).1 = a).card

/-- Given [a marked sample](hyp:Z), [a requested mark](hyp:a), [a Boolean word](hyp:w), and
[an outcome in that word's event](hyp:hω), [the observed selected count equals the word's deterministic selected count](goal). -/
lemma selectedCount_eq_on_wordEvent {Ω : Type*} {n : ℕ}
    (Z : Fin n → Ω → Bool × ℝ) (a : Bool) (w : Fin n → Bool)
    {ω : Ω} (hω : ω ∈ wordEvent Z w) :
    selectedCount Z a ω = selectedWordCount w a := by
  -- Membership in `wordEvent` identifies the two filtered finsets extensionally.
  classical
  unfold selectedCount selectedWordCount selectedIndices
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hω i]

/-- For [a marked sample](hyp:Z), [a Boolean word](hyp:w), and [a requested mark](hyp:a),
[the selected outcome vector](goal) [takes the outcome component at each reindexed selected coordinate](step:1). -/
noncomputable def selectedOutcomes {Ω : Type*} {n : ℕ}
    (Z : Fin n → Ω → Bool × ℝ) (w : Fin n → Bool) (a : Bool) :
    Ω → Fin (selectedWordCount w a) → ℝ :=
  fun ω j => (Z (selectedIndex w a j) ω).2

/-- For [a finite real vector](hyp:x) and [a threshold](hyp:y), [the vector empirical CDF](goal)
is [the normalized sum of lower-ray indicators](step:1). -/
noncomputable def empiricalCDFVec {m : ℕ} (x : Fin m → ℝ) (y : ℝ) : ℝ :=
  (m : ℝ)⁻¹ * ∑ i, Causalean.Stat.cdfStat y (x i)

/-- For [a marked sample](hyp:Z), [a requested mark](hyp:a), [a sample outcome](hyp:ω), and
[a threshold](hyp:y), [the selected empirical CDF](goal) is [the lower-ray count in the selected arm divided by its observed size](step:1). -/
noncomputable def selectedEmpiricalCDF {Ω : Type*} {n : ℕ}
    (Z : Fin n → Ω → Bool × ℝ) (a : Bool) (ω : Ω) (y : ℝ) : ℝ := by
  classical
  exact (selectedCount Z a ω : ℝ)⁻¹ *
    ∑ i ∈ Finset.univ.filter (fun i => (Z i ω).1 = a),
      Causalean.Stat.cdfStat y (Z i ω).2

/-- Given [a marked sample](hyp:Z), [a requested mark](hyp:a), [a Boolean word](hyp:w), [an
outcome in its exact-word event](hyp:hω), and [a threshold](hyp:y), [the reindexed-vector empirical CDF equals the directly selected empirical CDF](goal). -/
lemma empiricalCDFVec_selectedOutcomes_eq {Ω : Type*} {n : ℕ}
    (Z : Fin n → Ω → Bool × ℝ) (a : Bool) (w : Fin n → Bool)
    {ω : Ω} (hω : ω ∈ wordEvent Z w) (y : ℝ) :
    empiricalCDFVec (selectedOutcomes Z w a ω) y = selectedEmpiricalCDF Z a ω y := by
  -- Rewrite the count on the word event and apply `sum_selectedIndex`.
  classical
  have hs : Finset.univ.filter (fun i => (Z i ω).1 = a) = selectedIndices w a := by
    ext i
    simp [selectedIndices, hω i]
  simp only [empiricalCDFVec, selectedOutcomes, selectedEmpiricalCDF]
  rw [selectedCount_eq_on_wordEvent Z a w hω, hs]
  congr 1
  exact sum_selectedIndex w a (fun i => Causalean.Stat.cdfStat y (Z i ω).2)

/-- For [a population law](hyp:ρ) and [a finite real vector](hyp:x), [the uniform empirical-CDF
deviation](goal) is [the supremum over thresholds of the absolute empirical-minus-population CDF difference](step:1). -/
noncomputable def uniformCDFDeviation {m : ℕ} (ρ : Measure ℝ) (x : Fin m → ℝ) : ℝ :=
  sSup (Set.range fun y : ℝ => |empiricalCDFVec x y - cdf ρ y|)

/-- For [a population law](hyp:ρ) and [a deviation radius](hyp:radius), [the fixed-size bad set](goal)
is [the set of vectors whose uniform empirical-CDF deviation exceeds that radius](step:1). -/
def fixedCDFBadSet {m : ℕ} (ρ : Measure ℝ) (radius : ℝ) : Set (Fin m → ℝ) :=
  {x | uniformCDFDeviation ρ x > radius}

/-- For [a marked sample](hyp:Z), [a requested mark](hyp:a), [a population law](hyp:ρ), and [a
count-indexed radius](hyp:radius), [the selected-sample bad event](goal) is [the event that the selected arm is nonempty and its uniform deviation exceeds the radius at its observed size](step:1). -/
def selectedCDFBadEvent {Ω : Type*} {n : ℕ}
    (Z : Fin n → Ω → Bool × ℝ) (a : Bool) (ρ : Measure ℝ)
    (radius : ℕ → ℝ) : Set Ω :=
  {ω | selectedCount Z a ω > 0 ∧
    sSup (Set.range fun y : ℝ =>
      |selectedEmpiricalCDF Z a ω y - cdf ρ y|) > radius (selectedCount Z a ω)}

/-- Given [a marked sample](hyp:Z), [a requested mark](hyp:a), [a population law](hyp:ρ), [a
count-indexed radius](hyp:radius), [a Boolean word](hyp:w), and [a positive selected count for that word](hyp:hw), [intersecting the selected bad event with its exact-word event equals the reindexed fixed-size bad event intersected with that word event](goal). -/
lemma selectedCDFBadEvent_inter_wordEvent {Ω : Type*} {n : ℕ}
    (Z : Fin n → Ω → Bool × ℝ) (a : Bool) (ρ : Measure ℝ)
    (radius : ℕ → ℝ) (w : Fin n → Bool) (hw : 0 < selectedWordCount w a) :
    selectedCDFBadEvent Z a ρ radius ∩ wordEvent Z w =
      (selectedOutcomes Z w a) ⁻¹'
        fixedCDFBadSet ρ (radius (selectedWordCount w a)) ∩ wordEvent Z w := by
  -- Extensionality reduces this to the count identity and pointwise empirical-CDF reindexing.
  ext ω
  constructor
  · rintro ⟨⟨_, hbad⟩, hω⟩
    refine ⟨?_, hω⟩
    simpa [fixedCDFBadSet, uniformCDFDeviation,
      selectedCount_eq_on_wordEvent Z a w hω,
      empiricalCDFVec_selectedOutcomes_eq Z a w hω] using hbad
  · rintro ⟨hbad, hω⟩
    refine ⟨⟨?_, ?_⟩, hω⟩
    · simpa [selectedCount_eq_on_wordEvent Z a w hω] using hw
    · simpa [fixedCDFBadSet, uniformCDFDeviation,
        selectedCount_eq_on_wordEvent Z a w hω,
        empiricalCDFVec_selectedOutcomes_eq Z a w hω] using hbad

end Causalean.Stat.Quantile.ConditionalMarkedSubsampleDkw
