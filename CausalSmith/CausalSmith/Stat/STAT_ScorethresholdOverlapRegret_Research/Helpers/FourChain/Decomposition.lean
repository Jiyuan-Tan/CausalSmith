module
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.Estimator

/-! # Score-threshold overlap regret — exact threshold chains

Finite trace complexity and the exact four right-oracle disagreement branches.
The interval identities retain endpoint atoms, the branches are nested, and
their comparison integrands share a cutoff-independent sign. Reflection
exchanges the two orientations; constant zero is retained as a singleton.
-/

public section

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.ScorethresholdOverlapRegret

open MeasureTheory
open scoped BigOperators ENNReal

/-- Finite trace complexity of the two-orientation threshold class, including ties. -/
-- @node: threshold_trace_card_le
lemma threshold_trace_card_le {n : ℕ} (d : Fin n → Observation)
    (hd : ∀ i, (d i).X ∈ Set.Icc (0:ℝ) 1) :
    Nat.card {b : Fin n → Bool //
      ∃ π ∈ thresholdClass, ∀ i : Fin n, b i = π (d i).X}
      ≤ 2*(n+1) := by
  classical
  let count (b : Fin n → Bool) : ℕ := (Finset.univ.filter fun i => b i).card
  let L (b : Fin n → Bool) : Prop :=
    ∃ t : ℝ, ∀ i, b i = decide ((d i).X ≤ t)
  let R (b : Fin n → Bool) : Prop :=
    ∃ t : ℝ, ∀ i, b i = decide (t ≤ (d i).X)
  have hshape (b : {b : Fin n → Bool // ∃ π ∈ thresholdClass,
      ∀ i : Fin n, b i = π (d i).X}) : L b.1 ∨ R b.1 := by
    obtain ⟨π, hπ, hb⟩ := b.2
    rcases hπ with hfalse | htrue | hleft | hright
    · left
      refine ⟨-1, ?_⟩
      intro i
      rw [hb i, hfalse _ (hd i)]
      have hlo := (Set.mem_Icc.mp (hd i)).1
      simp
      linarith
    · left
      refine ⟨1, ?_⟩
      intro i
      rw [hb i, htrue _ (hd i)]
      exact (decide_eq_true (Set.mem_Icc.mp (hd i)).2).symm
    · left
      obtain ⟨t, _, ht⟩ := hleft
      exact ⟨t, fun i => by rw [hb i, ht _ (hd i)]; rfl⟩
    · right
      obtain ⟨t, _, ht⟩ := hright
      exact ⟨t, fun i => by rw [hb i, ht _ (hd i)]; rfl⟩
  have hcount (b : Fin n → Bool) : count b < n+1 := by
    dsimp [count]
    have h := Finset.card_filter_le (s := Finset.univ) (p := fun i : Fin n => b i)
    simpa using Nat.lt_succ_of_le h
  let code (b : {b : Fin n → Bool // ∃ π ∈ thresholdClass,
      ∀ i : Fin n, b i = π (d i).X}) : Bool × Fin (n+1) :=
    (if L b.1 then false else true, ⟨count b.1, hcount b.1⟩)
  have hcode : Function.Injective code := by
    intro b c hbc
    apply Subtype.ext
    have hside : (if L b.1 then false else true) =
        (if L c.1 then false else true) := congrArg Prod.fst hbc
    have hcard : count b.1 = count c.1 := congrArg (fun p : Bool × Fin (n+1) => p.2.1) hbc
    have hnested (u v : Fin n → Bool) (hu : L u) (hv : L v) :
        (∀ i, u i = true → v i = true) ∨
        (∀ i, v i = true → u i = true) := by
      obtain ⟨s, hs⟩ := hu
      obtain ⟨t, ht⟩ := hv
      rcases le_total s t with hst | hts
      · left
        intro i hi
        rw [hs i] at hi
        rw [ht i]
        exact decide_eq_true (le_trans (of_decide_eq_true hi) hst)
      · right
        intro i hi
        rw [ht i] at hi
        rw [hs i]
        exact decide_eq_true (le_trans (of_decide_eq_true hi) hts)
    have hnestedR (u v : Fin n → Bool) (hu : R u) (hv : R v) :
        (∀ i, u i = true → v i = true) ∨
        (∀ i, v i = true → u i = true) := by
      obtain ⟨s, hs⟩ := hu
      obtain ⟨t, ht⟩ := hv
      rcases le_total s t with hst | hts
      · right
        intro i hi
        rw [ht i] at hi
        rw [hs i]
        exact decide_eq_true (le_trans hst (of_decide_eq_true hi))
      · left
        intro i hi
        rw [hs i] at hi
        rw [ht i]
        exact decide_eq_true (le_trans hts (of_decide_eq_true hi))
    have heq (u v : Fin n → Bool) (hcnt : count u = count v)
        (hn : (∀ i, u i = true → v i = true) ∨
          (∀ i, v i = true → u i = true)) : u = v := by
      have hsets : (Finset.univ.filter fun i => u i) =
          (Finset.univ.filter fun i => v i) := by
        rcases hn with huv | hvu
        · apply Finset.eq_of_subset_of_card_le
          · intro i hi
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
            exact huv i hi
          · exact hcnt.ge
        · symm
          apply Finset.eq_of_subset_of_card_le
          · intro i hi
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
            exact hvu i hi
          · exact hcnt.le
      funext i
      have hi := congrArg (fun s : Finset (Fin n) => i ∈ s) hsets
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      cases hbu : u i <;> cases hbv : v i <;> simp_all
    by_cases hb : L b.1
    · have hc : L c.1 := by
        by_contra hnc
        simp [hb, hnc] at hside
      exact heq b.1 c.1 hcard (hnested _ _ hb hc)
    · have hc : ¬ L c.1 := by
        intro hcl
        simp [hb, hcl] at hside
      exact heq b.1 c.1 hcard (hnestedR _ _ ((hshape b).resolve_left hb)
        ((hshape c).resolve_left hc))
  have h := Nat.card_le_card_of_injective code hcode
  simpa using h

/-- Below a right-oracle cutoff, disagreement is the left-closed, right-open interval. -/
-- @node: rightOracle_right_below_disagreement
lemma rightOracle_right_below_disagreement (c t x : ℝ) (ht : t < c) :
    rightThr t x ≠ rightThr c x ↔ x ∈ Set.Ico t c := by
  simp only [rightThr, ne_eq, decide_eq_decide, Set.mem_Ico]
  constructor
  · intro h
    by_cases hx : t ≤ x
    · exact ⟨hx, lt_of_not_ge (fun hc => h (iff_of_true hx hc))⟩
    · exact False.elim (h (iff_of_false hx (by intro hc; linarith)))
  · rintro ⟨hx, hxc⟩ h
    exact (not_le_of_gt hxc) (h.mp hx)

/-- At or above a right-oracle cutoff, the oracle-side endpoint remains included. -/
-- @node: rightOracle_right_above_disagreement
lemma rightOracle_right_above_disagreement (c t x : ℝ) (ht : c ≤ t) :
    rightThr t x ≠ rightThr c x ↔ x ∈ Set.Ico c t := by
  simp only [rightThr, ne_eq, decide_eq_decide, Set.mem_Ico]
  constructor
  · intro h
    by_cases hx : c ≤ x
    · exact ⟨hx, lt_of_not_ge (fun htx => h (iff_of_true htx hx))⟩
    · exact False.elim (h (iff_of_false (by intro htx; linarith) hx))
  · rintro ⟨hx, hxt⟩ h
    exact (not_le_of_gt hxt) (h.mpr hx)

/-- A left competitor below the oracle disagrees on two closed outer pieces. -/
-- @node: rightOracle_left_below_disagreement
lemma rightOracle_left_below_disagreement (c t x : ℝ) (ht : t < c)
    (hx : x ∈ Set.Icc (0:ℝ) 1) :
    leftThr t x ≠ rightThr c x ↔ x ∈ Set.Icc 0 t ∪ Set.Icc c 1 := by
  simp only [leftThr, rightThr, ne_eq, decide_eq_decide,
    Set.mem_union, Set.mem_Icc]
  constructor
  · intro h
    by_cases hxt : x ≤ t
    · exact Or.inl ⟨hx.1, hxt⟩
    · right
      refine ⟨?_, hx.2⟩
      by_contra hcx
      exact h (iff_of_false hxt hcx)
  · rintro (⟨_, hxt⟩ | ⟨hcx, _⟩) h
    · have hcx := h.mp hxt
      linarith
    · have hxt := h.mpr hcx
      linarith

/-- A left competitor above the oracle leaves both inner endpoints open. -/
-- @node: rightOracle_left_above_disagreement
lemma rightOracle_left_above_disagreement (c t x : ℝ) (ht : c ≤ t)
    (hx : x ∈ Set.Icc (0:ℝ) 1) :
    leftThr t x ≠ rightThr c x ↔ x ∈ Set.Ico 0 c ∪ Set.Ioc t 1 := by
  simp only [leftThr, rightThr, ne_eq, decide_eq_decide,
    Set.mem_union, Set.mem_Ico, Set.mem_Ioc]
  constructor
  · intro h
    by_cases hcx : c ≤ x
    · right
      exact ⟨lt_of_not_ge (fun hxt => h (iff_of_true hxt hcx)), hx.2⟩
    · exact Or.inl ⟨hx.1, lt_of_not_ge hcx⟩
  · rintro (⟨_, hxc⟩ | ⟨htx, _⟩) h
    · have hxt : x ≤ t := by linarith
      exact (not_le_of_gt hxc) (h.mp hxt)
    · have hcx : c ≤ x := by linarith
      exact (not_le_of_gt htx) (h.mpr hcx)

/-- The comparison sign is constantly negative on the lower same-orientation branch. -/
-- @node: rightOracle_right_below_coefficient
lemma rightOracle_right_below_coefficient (c t x : ℝ) (ht : t < c) :
    ((if rightThr t x then (0:ℝ) else 1) -
      (if rightThr c x then (0:ℝ) else 1)) =
      if x ∈ Set.Ico t c then -1 else 0 := by
  by_cases htx : t ≤ x <;> by_cases hcx : c ≤ x <;>
    simp [rightThr, htx, hcx, Set.mem_Ico] <;> linarith

/-- The comparison sign is constantly positive on the upper same-orientation branch. -/
-- @node: rightOracle_right_above_coefficient
lemma rightOracle_right_above_coefficient (c t x : ℝ) (ht : c ≤ t) :
    ((if rightThr t x then (0:ℝ) else 1) -
      (if rightThr c x then (0:ℝ) else 1)) =
      if x ∈ Set.Ico c t then 1 else 0 := by
  by_cases htx : t ≤ x <;> by_cases hcx : c ≤ x <;>
    simp [rightThr, htx, hcx, Set.mem_Ico] <;> linarith

/-- The below-oracle opposite branch has a fixed negative left sign and positive right sign. -/
-- @node: rightOracle_left_below_coefficient
lemma rightOracle_left_below_coefficient (c t x : ℝ) (ht : t < c) :
    ((if leftThr t x then (0:ℝ) else 1) -
      (if rightThr c x then (0:ℝ) else 1)) =
      (if x ≤ t then -1 else 0) + (if c ≤ x then 1 else 0) := by
  by_cases hxt : x ≤ t <;> by_cases hcx : c ≤ x <;>
    simp [leftThr, rightThr, hxt, hcx] <;> linarith

/-- The above-oracle opposite branch keeps the strict endpoint conventions in its signs. -/
-- @node: rightOracle_left_above_coefficient
lemma rightOracle_left_above_coefficient (c t x : ℝ) (ht : c ≤ t) :
    ((if leftThr t x then (0:ℝ) else 1) -
      (if rightThr c x then (0:ℝ) else 1)) =
      (if x < c then -1 else 0) + (if t < x then 1 else 0) := by
  by_cases hxt : x ≤ t <;> by_cases hcx : c ≤ x <;>
    simp [leftThr, rightThr, hxt, hcx, not_lt.mpr, lt_of_not_ge] <;> linarith

/-- Decreasing the lower same-orientation cutoff increases disagreement. -/
-- @node: rightOracle_right_below_nested
lemma rightOracle_right_below_nested (c s t : ℝ) (hst : s ≤ t) :
    Set.Ico t c ⊆ Set.Ico s c :=
  Set.Ico_subset_Ico_left hst

/-- Increasing the upper same-orientation cutoff increases disagreement. -/
-- @node: rightOracle_right_above_nested
lemma rightOracle_right_above_nested (c s t : ℝ) (hst : s ≤ t) :
    Set.Ico c s ⊆ Set.Ico c t :=
  Set.Ico_subset_Ico_right hst

/-- Increasing the lower opposite-orientation cutoff increases its two-piece disagreement. -/
-- @node: rightOracle_left_below_nested
lemma rightOracle_left_below_nested (c s t : ℝ) (hst : s ≤ t) :
    Set.Icc 0 s ∪ Set.Icc c 1 ⊆ Set.Icc 0 t ∪ Set.Icc c 1 :=
  Set.union_subset_union (Set.Icc_subset_Icc_right hst) Set.Subset.rfl

/-- Decreasing the upper opposite-orientation cutoff increases its two-piece disagreement. -/
-- @node: rightOracle_left_above_nested
lemma rightOracle_left_above_nested (c s t : ℝ) (hst : s ≤ t) :
    Set.Ico 0 c ∪ Set.Ioc t 1 ⊆ Set.Ico 0 c ∪ Set.Ioc s 1 :=
  Set.union_subset_union Set.Subset.rfl (Set.Ioc_subset_Ioc_left hst)

/-- The lower right branch is the score times a negative interval indicator. -/
-- @node: comparisonIntegrand_rightOracle_right_below
lemma comparisonIntegrand_rightOracle_right_below (P : RowLaw) (a c t : ℝ)
    (o : Observation) (ht : t < c)
    (horacle : canonicalPolicy P o.X = rightThr c o.X) :
    comparisonIntegrand P a (rightThr t) o =
      (if o.X ∈ Set.Ico t c then (-1:ℝ) else 0) * zScore a P.logger o := by
  unfold comparisonIntegrand
  rw [horacle, rightOracle_right_below_coefficient c t o.X ht]

/-- The upper right branch is the score times a positive interval indicator. -/
-- @node: comparisonIntegrand_rightOracle_right_above
lemma comparisonIntegrand_rightOracle_right_above (P : RowLaw) (a c t : ℝ)
    (o : Observation) (ht : c ≤ t)
    (horacle : canonicalPolicy P o.X = rightThr c o.X) :
    comparisonIntegrand P a (rightThr t) o =
      (if o.X ∈ Set.Ico c t then (1:ℝ) else 0) * zScore a P.logger o := by
  unfold comparisonIntegrand
  rw [horacle, rightOracle_right_above_coefficient c t o.X ht]

/-- The lower opposite branch has a cutoff-independent sign on each outer piece. -/
-- @node: comparisonIntegrand_rightOracle_left_below
lemma comparisonIntegrand_rightOracle_left_below (P : RowLaw) (a c t : ℝ)
    (o : Observation) (ht : t < c)
    (horacle : canonicalPolicy P o.X = rightThr c o.X) :
    comparisonIntegrand P a (leftThr t) o =
      ((if o.X ≤ t then (-1:ℝ) else 0) +
        (if c ≤ o.X then 1 else 0)) * zScore a P.logger o := by
  unfold comparisonIntegrand
  rw [horacle, rightOracle_left_below_coefficient c t o.X ht]

/-- The upper opposite branch retains strict cutoffs in its signed score pieces. -/
-- @node: comparisonIntegrand_rightOracle_left_above
lemma comparisonIntegrand_rightOracle_left_above (P : RowLaw) (a c t : ℝ)
    (o : Observation) (ht : c ≤ t)
    (horacle : canonicalPolicy P o.X = rightThr c o.X) :
    comparisonIntegrand P a (leftThr t) o =
      ((if o.X < c then (-1:ℝ) else 0) +
        (if t < o.X then 1 else 0)) * zScore a P.logger o := by
  unfold comparisonIntegrand
  rw [horacle, rightOracle_left_above_coefficient c t o.X ht]

/-- Score reflection exchanges left and right orientations without changing closed endpoints. -/
-- @node: leftThr_reflection
lemma leftThr_reflection (t x : ℝ) : leftThr t x = rightThr (1-t) (1-x) := by
  unfold leftThr rightThr
  congr 1
  apply propext
  constructor <;> intro h <;> linarith

/-- Score reflection exchanges right and left orientations without changing closed endpoints. -/
-- @node: rightThr_reflection
lemma rightThr_reflection (t x : ℝ) : rightThr t x = leftThr (1-t) (1-x) := by
  unfold leftThr rightThr
  congr 1
  apply propext
  constructor <;> intro h <;> linarith

/-- The constant-zero rule is a separate singleton branch, retaining an atom at one. -/
-- @node: rightOracle_zero_disagreement
lemma rightOracle_zero_disagreement (c x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) :
    false ≠ rightThr c x ↔ x ∈ Set.Icc c 1 := by
  simp [rightThr, Set.mem_Icc, hx.2]

/-- Constant one is the right endpoint-zero threshold on the score support. -/
-- @node: rightOracle_one_endpoint
lemma rightOracle_one_endpoint (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) :
    rightThr 0 x = true := by
  simp [rightThr, hx.1]

/-- Every right-oracle comparison has a common sign function independent of its competitor. -/
-- @node: rightOracle_fixed_sign
lemma rightOracle_fixed_sign (c x : ℝ) (b : Bool) :
    ((if b then (0:ℝ) else 1) - (if rightThr c x then (0:ℝ) else 1)) =
      (if c ≤ x then (1:ℝ) else -1) *
        (if b ≠ rightThr c x then (1:ℝ) else 0) := by
  cases b <;> by_cases hcx : c ≤ x <;> simp [rightThr, hcx]

/-- The score process on every right-oracle branch is a fixed signed score restricted to disagreement. -/
-- @node: comparisonIntegrand_rightOracle_fixed_sign
lemma comparisonIntegrand_rightOracle_fixed_sign (P : RowLaw) (a c : ℝ)
    (π : ℝ → Bool) (o : Observation)
    (horacle : canonicalPolicy P o.X = rightThr c o.X) :
    comparisonIntegrand P a π o =
      ((if c ≤ o.X then (1:ℝ) else -1) * zScore a P.logger o) *
        (if π o.X ≠ rightThr c o.X then (1:ℝ) else 0) := by
  unfold comparisonIntegrand
  rw [horacle, rightOracle_fixed_sign c o.X (π o.X)]
  ring

end CausalSmith.Stat.ScorethresholdOverlapRegret
