module
public import Mathlib.Data.ENat.Lattice
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
Defines extended metric covering numbers for arbitrary sets and proves their
basic properties.

This file provides the extended-natural `coveringNumber`, the natural-valued
compatibility function `coveringNumber'`, the chosen minimizing net
`coveringFinset`, and the basic facts used by the Dudley entropy-integral
bound: positivity on nonempty sets, antitonicity in the radius, and
almost-everywhere measurability of the covering-number function.

UPSTREAM-DELTA: unlike the vendored original, `coveringNumber` is defined for
every set and takes value `∞` when no finite cover exists. This intentional
departure permits entropy bounds to be stated before total boundedness is
established. The natural-valued API is retained under the primed name to keep
the downstream Dudley development close to upstream.
-/

@[expose] public section

-- Adapted from auto-res/lean-rademacher FoML/CoveringNumber.lean (commit 72d28921dc960f47691640fb973303a1be9d13ca, MIT License (c) 2025 AutoRes)



namespace Causalean.Stat.Concentration

attribute [local instance] Classical.propDecidable

/-- A totally bounded set has a finite positive-radius net, with the net size
recorded as a natural number. -/
lemma coveringNumber_exists {X : Type*} {A : Set X} [PseudoMetricSpace X]
    (ha : TotallyBounded A) {ε : ℝ} (εpos : ε > 0) :
    ∃ n : Nat, ∃ t : Finset X, t.card = n ∧ A ⊆ ⋃ y ∈ t, Metric.ball y ε := by
  have hball := Metric.finite_approx_of_totallyBounded ha ε εpos
  have ⟨t, ⟨_ht, tfin, tball⟩⟩ := hball
  have : Fintype t := tfin.fintype
  let n : Nat := this.card
  exists n
  exists t.toFinset
  constructor
  · exact Set.toFinset_card t
  · convert tball
    simp only [Set.mem_toFinset]

/-- For [any subset $A$ of a pseudometric space](hyp:A) and [any real radius
$\varepsilon$](hyp:ε), the [extended covering number](goal) is the infimum of the
extended-natural cardinalities of finite families of open $\varepsilon$-balls
that cover $A$; it is infinite when there is no such finite cover. -/
noncomputable def coveringNumber {X : Type*} [PseudoMetricSpace X]
    (A : Set X) (ε : ℝ) : ℕ∞ :=
  sInf {n : ℕ∞ | ∃ t : Finset X,
    (t.card : ℕ∞) = n ∧ A ⊆ ⋃ y ∈ t, Metric.ball y ε}

/-- For [a totally bounded set](hyp:ha) and [a radius](hyp:ε), the
[natural-valued compatibility covering number](goal) is the finite part of its
extended covering number. -/
noncomputable def coveringNumber' {X : Type*} [PseudoMetricSpace X] {A : Set X}
    (ha : TotallyBounded A) (ε : ℝ) : ℕ :=
  (coveringNumber A ε).toNat

/-- For [a totally bounded subset of a pseudometric space](hyp:ha) and [a
positive covering radius](hyp:hε), [the extended covering number is the natural
minimum cardinality selected by `coveringNumber_exists`](goal). -/
theorem coveringNumber_eq {X : Type*} [PseudoMetricSpace X] {A : Set X}
    (ha : TotallyBounded A) {ε : ℝ} (hε : ε > 0) :
    coveringNumber A ε = (Nat.find (coveringNumber_exists ha hε) : ℕ∞) := by
  apply IsLeast.csInf_eq
  constructor
  · obtain ⟨t, htcard, htcover⟩ := Nat.find_spec (coveringNumber_exists ha hε)
    exact ⟨t, by exact_mod_cast htcard, htcover⟩
  · intro n hn
    obtain ⟨t, htcard, htcover⟩ := hn
    rw [← htcard]
    exact_mod_cast Nat.find_min' (coveringNumber_exists ha hε)
      ⟨t, rfl, htcover⟩

/-- A [totally bounded set](hyp:ha) at [a positive radius](hyp:hε) has
[finite extended covering number](goal). -/
theorem coveringNumber_lt_top_of_totallyBounded
    {X : Type*} [PseudoMetricSpace X] {A : Set X}
    (ha : TotallyBounded A) {ε : ℝ} (hε : ε > 0) :
    coveringNumber A ε < ⊤ := by
  rw [coveringNumber_eq ha hε]
  exact ENat.natCast_lt_top _

/-- For [a totally bounded subset](hyp:ha) and [a positive radius](hyp:hε),
the [natural-valued compatibility covering number equals the selected minimum
finite-net cardinality](goal). -/
theorem coveringNumber'_eq {X : Type*} [PseudoMetricSpace X] {A : Set X}
    (ha : TotallyBounded A) {ε : ℝ} (hε : ε > 0) :
    coveringNumber' ha ε = Nat.find (coveringNumber_exists ha hε) := by
  simp [coveringNumber', coveringNumber_eq ha hε]

/-- For [a totally bounded set](hyp:ha), [its natural-valued covering number weakly decreases
as the positive covering radius grows](goal). -/
theorem coveringNumber'_antitone {X : Type*} [PseudoMetricSpace X] {A : Set X}
    (ha : TotallyBounded A) :
    AntitoneOn (coveringNumber' ha) (Set.Ioi 0) := by
  intro ε₁ hε₁ ε₂ hε₂ hε₁ε₂
  rw [coveringNumber'_eq ha hε₁, coveringNumber'_eq ha hε₂]
  apply Nat.find_mono
  intro n ⟨t, ht₁, ht₂⟩
  exists t, ht₁
  apply ht₂.trans
  apply Set.iUnion_mono
  intro _
  apply Set.iUnion_mono
  intro _
  exact Metric.ball_subset_ball hε₁ε₂

/-- For [a nonempty set](hyp:hs), [total boundedness](hyp:ha), and [a positive radius](hyp:hε),
[the natural-valued covering number is positive](goal). -/
theorem coveringNumber'_nonzero {X : Type*} [PseudoMetricSpace X] {A : Set X}
    (hs : A.Nonempty) (ha : TotallyBounded A) {ε : ℝ} (hε : ε > 0) :
    0 < coveringNumber' ha ε := by
  rw [coveringNumber'_eq ha hε]
  rw [Nat.find_pos]
  simpa using Set.nonempty_iff_ne_empty.mp hs

/-- For [a totally bounded subset](hyp:ha) at [a nonpositive radius](hyp:hε),
the [natural-valued compatibility covering number is zero](goal), matching the
legacy convention. -/
theorem coveringNumber'_eq_zero_of_nonpos
    {X : Type*} [PseudoMetricSpace X] {A : Set X}
    (ha : TotallyBounded A) {ε : ℝ} (hε : ε ≤ 0) :
    coveringNumber' ha ε = 0 := by
  rw [coveringNumber', ENat.toNat_eq_zero]
  by_cases hA : A.Nonempty
  · right
    rw [coveringNumber]
    rw [show {n : ℕ∞ | ∃ t : Finset X,
        (t.card : ℕ∞) = n ∧ A ⊆ ⋃ y ∈ t, Metric.ball y ε} = ∅ by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro n hn
      obtain ⟨t, _htcard, htcover⟩ := hn
      obtain ⟨x, hx⟩ := hA
      have hxcover := htcover hx
      simp only [Set.mem_iUnion] at hxcover
      obtain ⟨y, _hy, hxy⟩ := hxcover
      have hdist : ε ≤ dist x y := hε.trans dist_nonneg
      exact (not_lt_of_ge hdist) (Metric.mem_ball.mp hxy)]
    exact sInf_empty
  · left
    rw [coveringNumber, ENat.sInf_eq_zero]
    refine ⟨∅, ?_, ?_⟩
    · simp
    · simpa [Set.not_nonempty_iff_eq_empty.mp hA]

/-- For [a totally bounded set](hyp:ha) and [a measure on the radius line](hyp:μ), [the
natural-valued covering-number function is almost-everywhere measurable](goal). -/
@[fun_prop]
theorem coveringNumber'_aemeasurable {X : Type*} [PseudoMetricSpace X] {A : Set X}
    (ha : TotallyBounded A) (μ : MeasureTheory.Measure ℝ) :
    AEMeasurable (coveringNumber' ha) μ := by
  have h₀ : AEMeasurable (coveringNumber' ha) (μ.restrict (Set.Ioi 0)) :=
    aemeasurable_restrict_of_antitoneOn measurableSet_Ioi (coveringNumber'_antitone ha)
  convert (aemeasurable_indicator_iff measurableSet_Ioi).mpr h₀
  ext ε
  if h : ε ∈ Set.Ioi 0 then
    rw [Set.indicator_of_mem h]
  else
    rw [Set.indicator_of_notMem h]
    exact coveringNumber'_eq_zero_of_nonpos ha (le_of_not_gt h)

/-- For [a totally bounded subset $A$ of a pseudometric space](hyp:ha) and [a strictly positive real radius $\varepsilon$](hyp:ε,hε), the [chosen finite $\varepsilon$-net for $A$](goal) is a finite set whose cardinality attains the covering number.

A chosen finite positive-radius net attains the covering number. -/
noncomputable def coveringFinset
    {X : Type*} [PseudoMetricSpace X] {A : Set X}
    (ha : TotallyBounded A) {ε : ℝ} (hε : ε > 0) : Finset X :=
  Classical.choose (Nat.find_spec (coveringNumber_exists (X := X) (A := A) ha hε))

/-- For [a totally bounded set](hyp:ha) and [a positive radius](hyp:hε), [the chosen covering
finset covers the target set by balls of that radius](goal). -/
lemma coveringFinset_cover
    {X : Type*} [PseudoMetricSpace X] {A : Set X}
    (ha : TotallyBounded A) {ε : ℝ} (hε : ε > 0) :
    A ⊆ ⋃ y ∈ coveringFinset ha hε, Metric.ball y ε := by
  simpa [coveringFinset, coveringNumber_exists] using
    (Classical.choose_spec
      (Nat.find_spec (coveringNumber_exists (X := X) (A := A) ha hε))).2

/-- For [a totally bounded set](hyp:ha) and [a positive radius](hyp:hε), [the chosen covering
finset has cardinality equal to the natural-valued covering number](goal). -/
lemma coveringFinset_card
    {X : Type*} [PseudoMetricSpace X] {A : Set X}
    (ha : TotallyBounded A) {ε : ℝ} (hε : ε > 0) :
    (coveringFinset ha hε).card = coveringNumber' ha ε := by
  have h :=
    (Classical.choose_spec
      (Nat.find_spec (coveringNumber_exists (X := X) (A := A) ha hε))).1
  simpa [coveringFinset, coveringNumber'_eq (X := X) (A := A) ha hε,
    coveringNumber_exists] using h

end Causalean.Stat.Concentration
