/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
module

public import Causalean.Stat.Limit.Modes

/-!
# Stochastic order

This module provides filter-general, row-varying stochastic big-O and little-o.  Together with
`Causalean.Stat.Limit.Modes`, it supplies one vocabulary for scalar and vector statistics,
triangular arrays, and finite-design rows.  The definitions are filter-general, row-varying
extensions of the sequence definitions in van der Vaart (1998), §2.2, and Hansen (2022), §5.11;
the eventually-small formulation of `O_p` is primary because it composes directly with filters,
while `boundedInProbability_iff_limsup` recovers the textbook limsup form.
-/

@[expose] public section

open Filter MeasureTheory Topology
open scoped ENNReal NNReal Topology

namespace Causalean.Stat.Modes

/-- Given [row measures](hyp:μ), [normed row random variables](hyp:X), [an index
filter](hyp:l), and [a real rate](hyp:r), [boundedness in probability at that rate](goal) means
that every positive probability tolerance has [a positive finite multiplier](step:1) for which
[the weak norm tail is eventually below the tolerance](step:2). -/
def BoundedInProbability {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    {E : Type*} [SeminormedAddCommGroup E]
    (μ : (i : ι) → Measure (Ω i)) (X : (i : ι) → Ω i → E) (l : Filter ι)
    (r : ι → ℝ) : Prop :=
  ∀ δ : ℝ≥0∞, 0 < δ → ∃ M : ℝ, 0 < M ∧
    ∀ᶠ i in l, μ i {ω | M * r i ≤ ‖X i ω‖} ≤ δ

/-- Given [row measures](hyp:μ), [normed row random variables](hyp:X), [an index
filter](hyp:l), and [a real rate](hyp:r), [stochastic little-o at that rate](goal) means that
the weak norm tail at every positive multiple of the rate tends to zero. -/
def IsLittleOpF {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    {E : Type*} [SeminormedAddCommGroup E]
    (μ : (i : ι) → Measure (Ω i)) (X : (i : ι) → Ω i → E) (l : Filter ι)
    (r : ι → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto (fun i => μ i {ω | ε * r i ≤ ‖X i ω‖}) l (𝓝 0)

private lemma measure_norm_tail_mono
    {Ω E : Type*} [MeasurableSpace Ω] [SeminormedAddCommGroup E]
    (μ : Measure Ω) (X : Ω → E) {a b : ℝ} (hab : a ≤ b) :
    μ {ω | b ≤ ‖X ω‖} ≤ μ {ω | a ≤ ‖X ω‖} :=
  measure_mono fun _ h => hab.trans h

/-- If [the rate is eventually positive](hyp:hr), then for [row measures](hyp:μ), [row
variables](hyp:X), [a filter](hyp:l), and [that rate](hyp:r), [boundedness in probability using
weak tail events is equivalent to the usual strict-tail formulation](goal). -/
theorem boundedInProbability_iff_strict
    {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    {E : Type*} [SeminormedAddCommGroup E]
    (μ : (i : ι) → Measure (Ω i)) (X : (i : ι) → Ω i → E) (l : Filter ι)
    (r : ι → ℝ) (hr : ∀ᶠ i in l, 0 < r i) :
    BoundedInProbability μ X l r ↔
      ∀ δ : ℝ≥0∞, 0 < δ → ∃ M : ℝ, 0 < M ∧
        ∀ᶠ i in l, μ i {ω | M * r i < ‖X i ω‖} ≤ δ := by
  constructor
  · intro h δ hδ
    obtain ⟨M, hM, htail⟩ := h δ hδ
    refine ⟨M, hM, ?_⟩
    filter_upwards [htail] with i hi
    exact (measure_mono fun _ hω => (show M * r i ≤ _ from hω.le)).trans hi
  · intro h δ hδ
    obtain ⟨M, hM, htail⟩ := h δ hδ
    refine ⟨2 * M, by positivity, ?_⟩
    filter_upwards [hr, htail] with i hri hi
    refine (measure_mono fun _ hω => ?_).trans hi
    change M * r i < _
    exact (by nlinarith : M * r i < 2 * M * r i).trans_le hω

/-- If [the rate is eventually positive](hyp:hr), then for [row measures](hyp:μ), [row
variables](hyp:X), [a filter](hyp:l), and [that rate](hyp:r), [stochastic little-o using weak
tail events is equivalent to the usual strict-tail formulation](goal). -/
theorem isLittleOpF_iff_strict
    {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    {E : Type*} [SeminormedAddCommGroup E]
    (μ : (i : ι) → Measure (Ω i)) (X : (i : ι) → Ω i → E) (l : Filter ι)
    (r : ι → ℝ) (hr : ∀ᶠ i in l, 0 < r i) :
    IsLittleOpF μ X l r ↔
      ∀ ε : ℝ, 0 < ε →
        Tendsto (fun i => μ i {ω | ε * r i < ‖X i ω‖}) l (𝓝 0) := by
  constructor
  · intro h ε hε
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h ε hε)
      (fun _ => zero_le) ?_
    intro i
    exact measure_mono fun _ hω => (show ε * r i ≤ _ from hω.le)
  · intro h ε hε
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (h (ε / 2) (by positivity)) (.of_forall fun _ => zero_le) ?_
    filter_upwards [hr] with i hri
    refine measure_mono fun _ hω => ?_
    change ε / 2 * r i < _
    exact (by nlinarith : ε / 2 * r i < ε * r i).trans_le hω

/-- For [row measures](hyp:μ), [row variables](hyp:X), [a filter](hyp:l), and [a
rate](hyp:r), [boundedness in probability is equivalent to the textbook limsup tail
criterion](goal). -/
theorem boundedInProbability_iff_limsup
    {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    {E : Type*} [SeminormedAddCommGroup E]
    (μ : (i : ι) → Measure (Ω i)) (X : (i : ι) → Ω i → E) (l : Filter ι)
    (r : ι → ℝ) :
    BoundedInProbability μ X l r ↔
      ∀ δ : ℝ≥0∞, 0 < δ → ∃ M : ℝ, 0 < M ∧
        l.limsup (fun i => μ i {ω | M * r i ≤ ‖X i ω‖}) ≤ δ := by
  constructor
  · intro h δ hδ
    obtain ⟨M, hM, htail⟩ := h δ hδ
    exact ⟨M, hM, Filter.limsup_le_of_le (u := fun i => μ i {ω | M * r i ≤ ‖X i ω‖})
      (a := δ) (h := htail)⟩
  · intro h δ hδ
    by_cases hδtop : δ = ∞
    · exact ⟨1, one_pos, by simp [hδtop]⟩
    have hhalf : 0 < δ / 2 := ENNReal.div_pos hδ.ne' (by norm_num)
    obtain ⟨M, hM, hlim⟩ := h (δ / 2) hhalf
    refine ⟨M, hM, ?_⟩
    have hhalf_lt : δ / 2 < δ := ENNReal.half_lt_self hδ.ne' hδtop
    exact (((Filter.limsup_le_iff
      (u := fun i => μ i {ω | M * r i ≤ ‖X i ω‖}) (x := δ / 2)).mp hlim)
        δ hhalf_lt).mono fun _ hi => hi.le

/-- If [a row family is stochastic little-o at a rate](hyp:h), then [it is bounded in
probability at the same rate](goal). -/
theorem IsLittleOpF.boundedInProbability
    {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    {E : Type*} [SeminormedAddCommGroup E]
    {μ : (i : ι) → Measure (Ω i)} {X : (i : ι) → Ω i → E}
    {l : Filter ι} {r : ι → ℝ} (h : IsLittleOpF μ X l r) :
    BoundedInProbability μ X l r := by
  intro δ hδ
  refine ⟨1, one_pos, ?_⟩
  have ht := h 1 one_pos
  rw [ENNReal.tendsto_nhds_zero] at ht
  simpa only [one_mul] using ht δ hδ

/-- For [row measures](hyp:μ), [normed row random variables](hyp:X), and [an index
filter](hyp:l), [convergence in probability to zero is equivalent to stochastic little-o at the
constant unit rate](goal). -/
theorem tendstoInProbability_zero_iff_isLittleOpF_one
    {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    {E : Type*} [SeminormedAddCommGroup E]
    (μ : (i : ι) → Measure (Ω i)) (X : (i : ι) → Ω i → E) (l : Filter ι) :
    TendstoInProbability μ X l (fun _ _ => 0) ↔
      IsLittleOpF μ X l (fun _ => 1) := by
  rw [tendstoInProbability_iff_norm]
  simp only [IsLittleOpF, sub_zero, mul_one]

private lemma measure_add_norm_tail_le
    {Ω E : Type*} [MeasurableSpace Ω] [SeminormedAddCommGroup E]
    (μ : Measure Ω) (X Y : Ω → E) {a b r : ℝ} :
    μ {ω | (a + b) * r ≤ ‖X ω + Y ω‖} ≤
      μ {ω | a * r ≤ ‖X ω‖} + μ {ω | b * r ≤ ‖Y ω‖} := by
  calc
    μ {ω | (a + b) * r ≤ ‖X ω + Y ω‖}
        ≤ μ ({ω | a * r ≤ ‖X ω‖} ∪ {ω | b * r ≤ ‖Y ω‖}) := by
      refine measure_mono fun ω hω => ?_
      change (a * r ≤ ‖X ω‖) ∨ (b * r ≤ ‖Y ω‖)
      by_cases hX : a * r ≤ ‖X ω‖
      · exact Or.inl hX
      · right
        by_contra hY
        have hX' : ‖X ω‖ < a * r := lt_of_not_ge hX
        have hY' : ‖Y ω‖ < b * r := lt_of_not_ge hY
        have hsum : ‖X ω + Y ω‖ < (a + b) * r :=
          (norm_add_le _ _).trans_lt (by linarith)
        exact (not_lt_of_ge hω) hsum
    _ ≤ μ {ω | a * r ≤ ‖X ω‖} + μ {ω | b * r ≤ ‖Y ω‖} := measure_union_le _ _

private lemma measure_mul_norm_tail_le
    {Ω E : Type*} [MeasurableSpace Ω] [NormedRing E]
    (μ : Measure Ω) (X Y : Ω → E) {a b r s : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (hs : 0 < s) :
    μ {ω | (a * b) * (r * s) ≤ ‖X ω * Y ω‖} ≤
      μ {ω | a * r ≤ ‖X ω‖} + μ {ω | b * s ≤ ‖Y ω‖} := by
  calc
    μ {ω | (a * b) * (r * s) ≤ ‖X ω * Y ω‖}
        ≤ μ ({ω | a * r ≤ ‖X ω‖} ∪ {ω | b * s ≤ ‖Y ω‖}) := by
      refine measure_mono fun ω hω => ?_
      change (a * r ≤ ‖X ω‖) ∨ (b * s ≤ ‖Y ω‖)
      by_cases hX : a * r ≤ ‖X ω‖
      · exact Or.inl hX
      · right
        by_contra hY
        have hX' : ‖X ω‖ < a * r := lt_of_not_ge hX
        have hY' : ‖Y ω‖ < b * s := lt_of_not_ge hY
        have _har : 0 < a * r := mul_pos ha hr
        have _hbs : 0 < b * s := mul_pos hb hs
        have hprod : ‖X ω * Y ω‖ < (a * b) * (r * s) := calc
          ‖X ω * Y ω‖ ≤ ‖X ω‖ * ‖Y ω‖ := norm_mul_le _ _
          _ < (a * r) * (b * s) :=
            mul_lt_mul'' hX' hY' (norm_nonneg _) (norm_nonneg _)
          _ = (a * b) * (r * s) := by ring
        exact (not_lt_of_ge hω) hprod
    _ ≤ μ {ω | a * r ≤ ‖X ω‖} + μ {ω | b * s ≤ ‖Y ω‖} := measure_union_le _ _

/-- If [two row families are bounded in probability at the same rate](hyp:hX,hY), then
[their sum is bounded in probability at that rate](goal). -/
theorem BoundedInProbability.add
    {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    {E : Type*} [SeminormedAddCommGroup E]
    {μ : (i : ι) → Measure (Ω i)} {X Y : (i : ι) → Ω i → E}
    {l : Filter ι} {r : ι → ℝ}
    (hX : BoundedInProbability μ X l r) (hY : BoundedInProbability μ Y l r) :
    BoundedInProbability μ (fun i ω => X i ω + Y i ω) l r := by
  intro δ hδ
  by_cases hδtop : δ = ∞
  · exact ⟨1, one_pos, by simp [hδtop]⟩
  have hhalf : 0 < δ / 2 := ENNReal.div_pos hδ.ne' (by norm_num)
  obtain ⟨M, hM, hXM⟩ := hX (δ / 2) hhalf
  obtain ⟨N, hN, hYN⟩ := hY (δ / 2) hhalf
  refine ⟨M + N, add_pos hM hN, ?_⟩
  filter_upwards [hXM, hYN] with i hXi hYi
  calc
    μ i {ω | (M + N) * r i ≤ ‖X i ω + Y i ω‖}
        ≤ μ i {ω | M * r i ≤ ‖X i ω‖} + μ i {ω | N * r i ≤ ‖Y i ω‖} :=
      measure_add_norm_tail_le (μ i) (X i) (Y i)
    _ ≤ δ / 2 + δ / 2 := add_le_add hXi hYi
    _ = δ := ENNReal.add_halves δ

/-- If [two row families are stochastic little-o at the same rate](hyp:hX,hY) and
[that rate is eventually nonnegative](hyp:hr), then [their sum is stochastic little-o at that
rate](goal). -/
theorem IsLittleOpF.add
    {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    {E : Type*} [SeminormedAddCommGroup E]
    {μ : (i : ι) → Measure (Ω i)} {X Y : (i : ι) → Ω i → E}
    {l : Filter ι} {r : ι → ℝ}
    (hX : IsLittleOpF μ X l r) (hY : IsLittleOpF μ Y l r)
    (hr : ∀ᶠ i in l, 0 ≤ r i) :
    IsLittleOpF μ (fun i ω => X i ω + Y i ω) l r := by
  intro ε hε
  have ht : Tendsto
      (fun i => μ i {ω | ε / 2 * r i ≤ ‖X i ω‖} +
        μ i {ω | ε / 2 * r i ≤ ‖Y i ω‖}) l (𝓝 0) := by
    simpa using (hX (ε / 2) (by positivity)).add (hY (ε / 2) (by positivity))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
    (.of_forall fun _ => zero_le) ?_
  filter_upwards [hr] with i _hri
  have hhalf : ε / 2 + ε / 2 = ε := by ring
  simpa only [hhalf] using
    measure_add_norm_tail_le (μ i) (X i) (Y i)
      (a := ε / 2) (b := ε / 2) (r := r i)

/-- If [two row families are bounded in probability at respective rates](hyp:hX,hY) and
[both rates are eventually positive](hyp:hr,hs), then [their product is bounded in probability
at the product rate](goal). -/
theorem BoundedInProbability.mul
    {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    {E : Type*} [NormedRing E]
    {μ : (i : ι) → Measure (Ω i)} {X Y : (i : ι) → Ω i → E}
    {l : Filter ι} {r s : ι → ℝ}
    (hX : BoundedInProbability μ X l r) (hY : BoundedInProbability μ Y l s)
    (hr : ∀ᶠ i in l, 0 < r i) (hs : ∀ᶠ i in l, 0 < s i) :
    BoundedInProbability μ (fun i ω => X i ω * Y i ω) l (fun i => r i * s i) := by
  intro δ hδ
  by_cases hδtop : δ = ∞
  · exact ⟨1, one_pos, by simp [hδtop]⟩
  have hhalf : 0 < δ / 2 := ENNReal.div_pos hδ.ne' (by norm_num)
  obtain ⟨M, hM, hXM⟩ := hX (δ / 2) hhalf
  obtain ⟨N, hN, hYN⟩ := hY (δ / 2) hhalf
  refine ⟨M * N, mul_pos hM hN, ?_⟩
  filter_upwards [hr, hs, hXM, hYN] with i hri hsi hXi hYi
  calc
    μ i {ω | (M * N) * (r i * s i) ≤ ‖X i ω * Y i ω‖}
        ≤ μ i {ω | M * r i ≤ ‖X i ω‖} + μ i {ω | N * s i ≤ ‖Y i ω‖} :=
      measure_mul_norm_tail_le (μ i) (X i) (Y i) hM hN hri hsi
    _ ≤ δ / 2 + δ / 2 := add_le_add hXi hYi
    _ = δ := ENNReal.add_halves δ

/-- If [one row family is stochastic little-o at one rate](hyp:hX), [another is bounded in
probability at a second rate](hyp:hY), and [both rates are eventually positive](hyp:hr,hs), then
[their product is stochastic little-o at the product rate](goal). -/
theorem IsLittleOpF.mul_boundedInProbability
    {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    {E : Type*} [NormedRing E]
    {μ : (i : ι) → Measure (Ω i)} {X Y : (i : ι) → Ω i → E}
    {l : Filter ι} {r s : ι → ℝ}
    (hX : IsLittleOpF μ X l r) (hY : BoundedInProbability μ Y l s)
    (hr : ∀ᶠ i in l, 0 < r i) (hs : ∀ᶠ i in l, 0 < s i) :
    IsLittleOpF μ (fun i ω => X i ω * Y i ω) l (fun i => r i * s i) := by
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  by_cases hδtop : δ = ∞
  · simp [hδtop]
  have hhalf : 0 < δ / 2 := ENNReal.div_pos hδ.ne' (by norm_num)
  obtain ⟨M, hM, hYM⟩ := hY (δ / 2) hhalf
  have hXt := hX (ε / M) (div_pos hε hM)
  rw [ENNReal.tendsto_nhds_zero] at hXt
  have hXsmall := hXt (δ / 2) hhalf
  filter_upwards [hr, hs, hYM, hXsmall] with i hri hsi hYi hXi
  have htail := measure_mul_norm_tail_le (μ i) (X i) (Y i)
    (div_pos hε hM) hM hri hsi
  rw [div_mul_cancel₀ ε hM.ne'] at htail
  exact htail.trans (by simpa [ENNReal.add_halves] using add_le_add hXi hYi)

/-- If [two row families are stochastic little-o at respective rates](hyp:hX,hY) and
[both rates are eventually positive](hyp:hr,hs), then [their product is stochastic little-o at
the product rate](goal). -/
theorem IsLittleOpF.mul
    {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    {E : Type*} [NormedRing E]
    {μ : (i : ι) → Measure (Ω i)} {X Y : (i : ι) → Ω i → E}
    {l : Filter ι} {r s : ι → ℝ}
    (hX : IsLittleOpF μ X l r) (hY : IsLittleOpF μ Y l s)
    (hr : ∀ᶠ i in l, 0 < r i) (hs : ∀ᶠ i in l, 0 < s i) :
    IsLittleOpF μ (fun i ω => X i ω * Y i ω) l (fun i => r i * s i) :=
  hX.mul_boundedInProbability hY.boundedInProbability hr hs

/-- If [a row family is bounded in probability at a rate](hyp:hX), [the comparison rate is
eventually positive](hyp:hs), and [the ratio of the first rate to the comparison rate tends to
zero](hyp:hrs), then [the family is stochastic little-o at the comparison rate](goal). -/
theorem BoundedInProbability.isLittleOpF_of_tendsto_ratio
    {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    {E : Type*} [SeminormedAddCommGroup E]
    {μ : (i : ι) → Measure (Ω i)} {X : (i : ι) → Ω i → E}
    {l : Filter ι} {r s : ι → ℝ}
    (hX : BoundedInProbability μ X l r) (hs : ∀ᶠ i in l, 0 < s i)
    (hrs : Tendsto (fun i => r i / s i) l (𝓝 0)) :
    IsLittleOpF μ X l s := by
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  obtain ⟨M, hM, htail⟩ := hX δ hδ
  have hratio : ∀ᶠ i in l, r i / s i < ε / M :=
    hrs.eventually_lt_const (div_pos hε hM)
  filter_upwards [hs, hratio, htail] with i hsi hri hi
  have hquot : (M * r i) / s i < ε := by
    calc
      (M * r i) / s i = (r i / s i) * M := by ring
      _ < ε := (lt_div_iff₀ hM).mp hri
  have hrate : M * r i ≤ ε * s i := ((div_lt_iff₀ hsi).mp hquot).le
  exact (measure_norm_tail_mono (μ i) (X i) hrate).trans hi

end Causalean.Stat.Modes
