module
public import Causalean.Mathlib.MeasureTheory.FiniteIntervalPartition
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.UniformSpace.HeineCantor

/-! Finite paired weighted scalar quantization: measurable partitions, cost, and compact
regularity of the coefficients. The cells in this module may be disconnected. -/

@[expose] public section

open MeasureTheory Set Filter
open scoped BigOperators

namespace Causalean.Mathlib.Analysis.Quantization

noncomputable section

/-- [A family of `k` cells](hyp:k,B) is [a measurable partition](goal) of [the closed source
interval from `a` to `b`](hyp:a,b) when its cells are measurable, pairwise disjoint, and their
union is exactly that interval. No cell is required to be an interval. This is the real-line
instance of the library's finite measurable partition predicate `IsIntervalPartition`. -/
abbrev IsMeasurablePartition (a b : ℝ) (k : ℕ) (B : Fin k → Set ℝ) : Prop :=
  Causalean.Mathlib.MeasureTheory.IsIntervalPartition a b k B

/-- The paired weighted absolute-deviation cost of a family of k cells B_j and reproduction
points z_(j,s), for S coefficient functions β_s, is the sum over cells j and coefficients s of
the integral over x in B_j of β_s(x, z_(j,s))·|x − z_(j,s)|. One common cell partition is used
for all coefficients, with a separate reproduction point for each coefficient in each cell. -/
def weightedCost (S k : ℕ) (β : Fin S → ℝ → ℝ → ℝ)
    (B : Fin k → Set ℝ) (z : Fin k → Fin S → ℝ) : ℝ :=
  ∑ j : Fin k, ∑ s : Fin S,
    ∫ x in B j, β s x (z j s) * |x - z j s|

/-- The optimal paired cost on the source interval from a to b with k cells is the infimum of
the paired weighted cost over every measurable partition of that interval into k cells and every
array of reproduction points lying in the interval. When no such partition exists or the costs
are unbounded below, the infimum is read as zero. -/
def optimalCost (a b : ℝ) (S k : ℕ) (β : Fin S → ℝ → ℝ → ℝ) : ℝ :=
  sInf {v : ℝ | ∃ (B : Fin k → Set ℝ) (z : Fin k → Fin S → ℝ),
    IsMeasurablePartition a b k B ∧
    (∀ j s, z j s ∈ Set.Icc a b) ∧
    v = weightedCost S k β B z}

/-- The diagonal density is the sum of the coefficients evaluated at the same
source and reproduction point. -/
def diagonalWeight (S : ℕ) (β : Fin S → ℝ → ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ s : Fin S, β s x x

/-- All members of a finite family of continuous positive coefficients have
one strictly positive lower bound and one finite upper bound on the square. -/
theorem coefficient_bounds (a b : ℝ) (hab : a < b) (S : ℕ) (hS : 0 < S)
    (β : Fin S → ℝ → ℝ → ℝ)
    (hcont : ∀ s, ContinuousOn (fun p : ℝ × ℝ => β s p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc a b))
    (hpos : ∀ s x z, x ∈ Set.Icc a b → z ∈ Set.Icc a b → 0 < β s x z) :
    ∃ c C : ℝ, 0 < c ∧ ∀ s, ∀ x ∈ Set.Icc a b, ∀ z ∈ Set.Icc a b,
      c ≤ β s x z ∧ β s x z ≤ C := by
  -- Apply compact extrema on the square for each index and take finite min/max.
  classical
  let K : Set (ℝ × ℝ) := Set.Icc a b ×ˢ Set.Icc a b
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKn : K.Nonempty := ⟨(a, a), ⟨⟨le_refl a, le_of_lt hab⟩,
    ⟨le_refl a, le_of_lt hab⟩⟩⟩
  have hlocal (s : Fin S) : ∃ c C : ℝ, 0 < c ∧
      ∀ x ∈ Set.Icc a b, ∀ z ∈ Set.Icc a b,
        c ≤ β s x z ∧ β s x z ≤ C := by
    obtain ⟨p, hp, hmin⟩ := hK.exists_isMinOn hKn (hcont s)
    obtain ⟨q, hq, hmax⟩ := hK.exists_isMaxOn hKn (hcont s)
    refine ⟨β s p.1 p.2, β s q.1 q.2, hpos s p.1 p.2 hp.1 hp.2, ?_⟩
    intro x hx z hz
    have hmem : (x, z) ∈ K := ⟨hx, hz⟩
    exact ⟨hmin hmem, hmax hmem⟩
  choose c C hc using hlocal
  let : Nonempty (Fin S) := ⟨⟨0, hS⟩⟩
  obtain ⟨i, hi⟩ := Finite.exists_min c
  obtain ⟨j, hj⟩ := Finite.exists_max C
  refine ⟨c i, C j, (hc i).1, ?_⟩
  intro s x hx z hz
  obtain ⟨hl, hu⟩ := (hc s).2 x hx z hz
  exact ⟨(hi s).trans hl, hu.trans (hj s)⟩

/-- Joint continuity on the compact square is uniform across the finite family.
Here closeness of pairs uses the product metric. -/
theorem coefficient_uniform_continuity (a b : ℝ) (S : ℕ)
    (β : Fin S → ℝ → ℝ → ℝ)
    (hcont : ∀ s, ContinuousOn (fun p : ℝ × ℝ => β s p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc a b)) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ s (p q : ℝ × ℝ), p ∈ Set.Icc a b ×ˢ Set.Icc a b →
        q ∈ Set.Icc a b ×ˢ Set.Icc a b →
        dist p q < δ → |β s p.1 p.2 - β s q.1 q.2| < ε := by
  -- Heine-Cantor for each index, followed by a finite minimum of the radii.
  classical
  intro ε hε
  by_cases hS : 0 < S
  · have hlocal (s : Fin S) : ∃ δ : ℝ, 0 < δ ∧
        ∀ (p q : ℝ × ℝ), p ∈ Set.Icc a b ×ˢ Set.Icc a b →
          q ∈ Set.Icc a b ×ˢ Set.Icc a b →
          dist p q < δ → |β s p.1 p.2 - β s q.1 q.2| < ε := by
      have hu := (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous
        (hcont s)
      obtain ⟨δ, hδ, hd⟩ := (Metric.uniformContinuousOn_iff.mp hu) ε hε
      refine ⟨δ, hδ, ?_⟩
      intro p q hp hq hpq
      simpa [Real.dist_eq] using hd p hp q hq hpq
    choose d hd using hlocal
    let : Nonempty (Fin S) := ⟨⟨0, hS⟩⟩
    obtain ⟨i, hi⟩ := Finite.exists_min d
    refine ⟨d i, (hd i).1, ?_⟩
    intro s p q hp hq hpq
    exact (hd s).2 p q hp hq (lt_of_lt_of_le hpq (hi s))
  · have hzero : S = 0 := Nat.eq_zero_of_not_pos hS
    subst S
    refine ⟨1, by norm_num, ?_⟩
    intro s
    exact Fin.elim0 s

/-- The diagonal density is continuous and strictly positive throughout the
source interval. -/
theorem diagonal_regular (a b : ℝ) (S : ℕ) (hS : 0 < S)
    (β : Fin S → ℝ → ℝ → ℝ)
    (hcont : ∀ s, ContinuousOn (fun p : ℝ × ℝ => β s p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc a b))
    (hpos : ∀ s x z, x ∈ Set.Icc a b → z ∈ Set.Icc a b → 0 < β s x z) :
    ContinuousOn (diagonalWeight S β) (Set.Icc a b) ∧
      ∀ x ∈ Set.Icc a b, 0 < diagonalWeight S β x := by
  -- Compose each coefficient with the diagonal and sum; positivity uses hS.
  constructor
  · unfold diagonalWeight
    apply continuousOn_finsetSum
    intro s hs
    have hdiag : ContinuousOn (fun x : ℝ => (x, x)) (Set.Icc a b) := by
      fun_prop
    exact (hcont s).comp hdiag (by
      intro x hx
      exact ⟨hx, hx⟩)
  · intro x hx
    unfold diagonalWeight
    exact Finset.sum_pos (fun s hs => hpos s x x hx hx)
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, hS⟩⟩)

/-- On [the interval endpoints](hyp:a,b) with [strict positive length](hyp:hab),
a [nonempty finite family](hyp:S,hS) of [loss weights](hyp:β) that are
[jointly continuous](hyp:hcont) and [strictly positive](hyp:hpos) has
[a continuous square-root diagonal density with positive total mass](goal). -/
theorem sqrt_mass_regular (a b : ℝ) (hab : a < b) (S : ℕ) (hS : 0 < S)
    (β : Fin S → ℝ → ℝ → ℝ)
    (hcont : ∀ s, ContinuousOn (fun p : ℝ × ℝ => β s p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc a b))
    (hpos : ∀ s x z, x ∈ Set.Icc a b → z ∈ Set.Icc a b → 0 < β s x z) :
    ContinuousOn (fun x => Real.sqrt (diagonalWeight S β x)) (Set.Icc a b) ∧
      0 < ∫ x in a..b, Real.sqrt (diagonalWeight S β x) := by
  -- Use diagonal_regular, positive compact minimum, and integral positivity.
  obtain ⟨hc, hp⟩ := diagonal_regular a b S hS β hcont hpos
  have hroot : ContinuousOn (fun x => Real.sqrt (diagonalWeight S β x))
      (Set.Icc a b) := Real.continuous_sqrt.comp_continuousOn hc
  refine ⟨hroot, intervalIntegral.integral_pos hab hroot ?_ ?_⟩
  · intro x hx
    exact (Real.sqrt_nonneg _)
  · refine ⟨a, ⟨le_refl a, le_of_lt hab⟩, ?_⟩
    exact Real.sqrt_pos.2 (hp a ⟨le_refl a, le_of_lt hab⟩)

/-- Every feasible paired distortion is nonnegative when its weights are
nonnegative on the source square. -/
theorem weightedCost_nonneg (a b : ℝ) (S k : ℕ)
    (β : Fin S → ℝ → ℝ → ℝ) (B : Fin k → Set ℝ)
    (z : Fin k → Fin S → ℝ)
    (hB : IsMeasurablePartition a b k B)
    (hz : ∀ j s, z j s ∈ Set.Icc a b)
    (hβ : ∀ s x y, x ∈ Set.Icc a b → y ∈ Set.Icc a b → 0 ≤ β s x y) :
    0 ≤ weightedCost S k β B z := by
  -- Each cell is contained in Icc a b; integrate pointwise nonnegativity.
  have hsub (j : Fin k) : B j ⊆ Set.Icc a b := by
    intro x hx
    rw [← hB.2.2]
    exact Set.mem_iUnion.mpr ⟨j, hx⟩
  unfold weightedCost
  apply Finset.sum_nonneg
  intro j hj
  apply Finset.sum_nonneg
  intro s hs
  apply MeasureTheory.setIntegral_nonneg_ae (hB.1 j)
  exact Filter.Eventually.of_forall (fun x hx =>
    mul_nonneg (hβ s x (z j s) (hsub j hx) (hz j s)) (abs_nonneg _))

/-- Every feasible code bounds the optimal paired cost from above when the
weights are nonnegative on the source square. -/
theorem optimalCost_le_feasible (a b : ℝ) (S k : ℕ)
    (β : Fin S → ℝ → ℝ → ℝ) (B : Fin k → Set ℝ)
    (z : Fin k → Fin S → ℝ)
    (hB : IsMeasurablePartition a b k B)
    (hz : ∀ j s, z j s ∈ Set.Icc a b)
    (hβ : ∀ s x y, x ∈ Set.Icc a b → y ∈ Set.Icc a b → 0 ≤ β s x y) :
    optimalCost a b S k β ≤ weightedCost S k β B z := by
  -- weightedCost_nonneg supplies the lower bound needed by csInf_le.
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro v ⟨B', z', hB', hz', rfl⟩
    exact weightedCost_nonneg a b S k β B' z' hB' hz' hβ
  · exact ⟨B, z, hB, hz, rfl⟩

end

end Causalean.Mathlib.Analysis.Quantization
