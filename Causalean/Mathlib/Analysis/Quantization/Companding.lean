module
public import Causalean.Mathlib.Analysis.Quantization.Moment
public import Mathlib.Order.Interval.Set.Union

/-! Equal-square-root-mass companding boundaries, ordered cells, midpoint
reproduction, and uniform continuity estimates on fine cells. -/

@[expose] public section

open MeasureTheory Set Filter
open scoped BigOperators

namespace Causalean.Mathlib.Analysis.Quantization

noncomputable section

/-- The `j`th companding boundary is the first source point at which cumulative
square-root-diagonal mass reaches the fraction `j/k` of total mass. -/
def boundary (a b : ℝ) (S k j : ℕ)
    (β : Fin S → ℝ → ℝ → ℝ) : ℝ :=
  sInf {x : ℝ | x ∈ Set.Icc a b ∧
    (j : ℝ) / k *
      (∫ t in a..b, Real.sqrt (diagonalWeight S β t)) ≤
        ∫ t in a..x, Real.sqrt (diagonalWeight S β t)}

/-- Every valid companding boundary divides cumulative square-root-diagonal
mass at precisely its prescribed fraction. -/
theorem boundary_equal_mass (a b : ℝ) (hab : a < b)
    (S k j : ℕ) (hS : 0 < S) (hk : 0 < k) (hj : j ≤ k)
    (β : Fin S → ℝ → ℝ → ℝ)
    (hcont : ∀ s, ContinuousOn (fun p : ℝ × ℝ => β s p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc a b))
    (hpos : ∀ s x z, x ∈ Set.Icc a b → z ∈ Set.Icc a b → 0 < β s x z) :
    boundary a b S k j β ∈ Set.Icc a b ∧
      (∫ t in a..boundary a b S k j β,
        Real.sqrt (diagonalWeight S β t)) =
      (j : ℝ) / k *
        (∫ t in a..b, Real.sqrt (diagonalWeight S β t)) := by
  let f : ℝ → ℝ := fun x => Real.sqrt (diagonalWeight S β x)
  let F : ℝ → ℝ := fun x => ∫ t in a..x, f t
  have hf : ContinuousOn f (Set.Icc a b) :=
    (sqrt_mass_regular a b hab S hS β hcont hpos).1
  have hfpos : ∀ x ∈ Set.Icc a b, 0 < f x := by
    intro x hx
    exact Real.sqrt_pos.2 ((diagonal_regular a b S hS β hcont hpos).2 x hx)
  have hFcont : ContinuousOn F (Set.Icc a b) := by
    have hfi : IntegrableOn f (Set.Icc a b) := hf.integrableOn_Icc
    have hfu : IntegrableOn f (Set.uIcc a b) := by
      simpa only [Set.uIcc_of_le hab.le] using hfi
    have hc : ContinuousOn F (Set.uIcc a b) :=
      intervalIntegral.continuousOn_primitive_interval (a := a) (b := b) hfu
    simpa only [Set.uIcc_of_le hab.le] using hc
  have hFstrict : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
      x < y → F x < F y := by
    intro x hx y hy hxy
    have hxycont : ContinuousOn f (Set.Icc x y) :=
      hf.mono (by intro z hz; exact ⟨hx.1.trans hz.1, hz.2.trans hy.2⟩)
    have hpositive : 0 < ∫ t in x..y, f t :=
      intervalIntegral.integral_pos hxy hxycont
        (by intro z hz; exact (hfpos z ⟨hx.1.trans (le_of_lt hz.1), hz.2.trans hy.2⟩).le)
        ⟨x, ⟨le_refl x, hxy.le⟩, hfpos x hx⟩
    have hax : IntervalIntegrable f volume a x :=
      ContinuousOn.intervalIntegrable_of_Icc hx.1
        (hf.mono (by intro z hz; exact ⟨hz.1, hz.2.trans hx.2⟩))
    have hxyint : IntervalIntegrable f volume x y :=
      ContinuousOn.intervalIntegrable_of_Icc hxy.le hxycont
    have hadd := intervalIntegral.integral_add_adjacent_intervals hax hxyint
    dsimp [F]
    linarith
  have hmass : 0 < F b := (sqrt_mass_regular a b hab S hS β hcont hpos).2
  have hFzero : F a = 0 := by simp [F]
  have htarget : F a ≤ (j : ℝ) / k * F b ∧
      (j : ℝ) / k * F b ≤ F b := by
    rw [hFzero]
    have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
    have hjreal : (j : ℝ) ≤ k := by exact_mod_cast hj
    constructor
    · exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) hkreal.le) hmass.le
    · exact mul_le_of_le_one_left hmass.le (div_le_one_of_le₀ hjreal hkreal.le)
  obtain ⟨x, hx, hFx'⟩ :=
    intermediate_value_Icc hab.le hFcont htarget
  have hxset : x ∈ {y : ℝ | y ∈ Set.Icc a b ∧
      (j : ℝ) / k * F b ≤ F y} := ⟨hx, hFx'.ge⟩
  have hleast : ∀ y ∈ {y : ℝ | y ∈ Set.Icc a b ∧
      (j : ℝ) / k * F b ≤ F y}, x ≤ y := by
    intro y hy
    by_contra h
    have hyx : y < x := lt_of_not_ge h
    exact (not_lt_of_ge hy.2) (hFx' ▸ hFstrict y hy.1 x hx hyx)
  have hboundary : boundary a b S k j β = x := by
    unfold boundary
    apply le_antisymm
    · exact csInf_le ⟨a, by rintro y ⟨hy, _⟩; exact hy.1⟩ hxset
    · exact le_csInf ⟨x, hxset⟩ hleast
  rw [hboundary]
  exact ⟨hx, hFx'⟩

/-- Companding boundaries start at the left endpoint, end at the right
endpoint, and strictly increase with their valid indices. -/
theorem boundary_order (a b : ℝ) (hab : a < b)
    (S k : ℕ) (hS : 0 < S) (hk : 0 < k)
    (β : Fin S → ℝ → ℝ → ℝ)
    (hcont : ∀ s, ContinuousOn (fun p : ℝ × ℝ => β s p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc a b))
    (hpos : ∀ s x z, x ∈ Set.Icc a b → z ∈ Set.Icc a b → 0 < β s x z) :
    boundary a b S k 0 β = a ∧ boundary a b S k k β = b ∧
      ∀ i j, i < j → j ≤ k → boundary a b S k i β < boundary a b S k j β := by
  let f : ℝ → ℝ := fun x => Real.sqrt (diagonalWeight S β x)
  let F : ℝ → ℝ := fun x => ∫ t in a..x, f t
  have hf : ContinuousOn f (Set.Icc a b) :=
    (sqrt_mass_regular a b hab S hS β hcont hpos).1
  have hfpos : ∀ x ∈ Set.Icc a b, 0 < f x := by
    intro x hx
    exact Real.sqrt_pos.2 ((diagonal_regular a b S hS β hcont hpos).2 x hx)
  have hFstrict : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
      x < y → F x < F y := by
    intro x hx y hy hxy
    have hxycont : ContinuousOn f (Set.Icc x y) :=
      hf.mono (by intro z hz; exact ⟨hx.1.trans hz.1, hz.2.trans hy.2⟩)
    have hpositive : 0 < ∫ t in x..y, f t :=
      intervalIntegral.integral_pos hxy hxycont
        (by intro z hz; exact (hfpos z ⟨hx.1.trans (le_of_lt hz.1), hz.2.trans hy.2⟩).le)
        ⟨x, ⟨le_refl x, hxy.le⟩, hfpos x hx⟩
    have hax : IntervalIntegrable f volume a x :=
      ContinuousOn.intervalIntegrable_of_Icc hx.1
        (hf.mono (by intro z hz; exact ⟨hz.1, hz.2.trans hx.2⟩))
    have hxyint : IntervalIntegrable f volume x y :=
      ContinuousOn.intervalIntegrable_of_Icc hxy.le hxycont
    have hadd := intervalIntegral.integral_add_adjacent_intervals hax hxyint
    dsimp [F]
    linarith
  have hbound (j : ℕ) (hj : j ≤ k) :
      boundary a b S k j β ∈ Set.Icc a b ∧
        F (boundary a b S k j β) = (j : ℝ) / k * F b :=
    boundary_equal_mass a b hab S k j hS hk hj β hcont hpos
  have hzero : boundary a b S k 0 β = a := by
    obtain ⟨hx, heq⟩ := hbound 0 (Nat.zero_le k)
    by_contra h
    have hlt : a < boundary a b S k 0 β := lt_of_le_of_ne hx.1 (Ne.symm h)
    have hstrict := hFstrict a ⟨le_refl a, hab.le⟩ _ hx hlt
    simp [F] at heq hstrict
    linarith
  have hlast : boundary a b S k k β = b := by
    obtain ⟨hx, heq⟩ := hbound k (le_refl k)
    by_contra h
    have hlt : boundary a b S k k β < b := lt_of_le_of_ne hx.2 h
    have hstrict := hFstrict _ hx b ⟨hab.le, le_refl b⟩ hlt
    have hkreal : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
    simp [hkreal] at heq
    linarith
  refine ⟨hzero, hlast, ?_⟩
  intro i j hij hj
  obtain ⟨hi_mem, hi_eq⟩ := hbound i (Nat.le_trans (Nat.le_of_lt hij) hj)
  obtain ⟨hj_mem, hj_eq⟩ := hbound j hj
  by_contra h
  have hji : boundary a b S k j β ≤ boundary a b S k i β := le_of_not_gt h
  have hFji : F (boundary a b S k j β) ≤ F (boundary a b S k i β) := by
    rcases hji.eq_or_lt with heq | hlt
    · rw [heq]
    · exact (hFstrict _ hj_mem _ hi_mem hlt).le
  have hmass : 0 < F b := (sqrt_mass_regular a b hab S hS β hcont hpos).2
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  have hijreal : (i : ℝ) < j := by exact_mod_cast hij
  rw [hi_eq, hj_eq] at hFji
  have hfrac : (i : ℝ) / k < (j : ℝ) / k :=
    (div_lt_div_iff_of_pos_right hkreal).2 (by nlinarith)
  nlinarith

/-- The `j`th ordered companding cell is half-open except at the final
right endpoint, where it is closed. -/
def compandingCell (a b : ℝ) (S k : ℕ)
    (β : Fin S → ℝ → ℝ → ℝ) (j : Fin k) : Set ℝ :=
  if j.val + 1 = k then
    Set.Icc (boundary a b S k j.val β) (boundary a b S k (j.val + 1) β)
  else
    Set.Ico (boundary a b S k j.val β) (boundary a b S k (j.val + 1) β)

/-- Every coefficient in a companding cell uses the same interval midpoint
as its reproduction point. -/
def compandingMidpoint (a b : ℝ) (S k : ℕ)
    (β : Fin S → ℝ → ℝ → ℝ) (j : Fin k) (_s : Fin S) : ℝ :=
  (boundary a b S k j.val β + boundary a b S k (j.val + 1) β) / 2

/-- On [a nondegenerate interval](hyp:a,b,hab), [a nonempty family](hyp:S,hS),
[a positive number of cells](hyp:k,hk), and [jointly continuous strictly
positive weights](hyp:β,hcont,hpos) give [a measurable disjoint
companding partition with feasible midpoint reproductions](goal). -/
theorem companding_feasible (a b : ℝ) (hab : a < b)
    (S k : ℕ) (hS : 0 < S) (hk : 0 < k)
    (β : Fin S → ℝ → ℝ → ℝ)
    (hcont : ∀ s, ContinuousOn (fun p : ℝ × ℝ => β s p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc a b))
    (hpos : ∀ s x z, x ∈ Set.Icc a b → z ∈ Set.Icc a b → 0 < β s x z) :
    IsMeasurablePartition a b k (compandingCell a b S k β) ∧
      ∀ j s, compandingMidpoint a b S k β j s ∈ Set.Icc a b := by
  classical
  obtain ⟨hfirst, hlast, hstrict⟩ :=
    boundary_order a b hab S k hS hk β hcont hpos
  let A : ℕ → ℝ := fun n => boundary a b S k n β
  have hmem (n : ℕ) (hn : n ≤ k) : A n ∈ Set.Icc a b :=
    (boundary_equal_mass a b hab S k n hS hk hn β hcont hpos).1
  have hcell_bounds (j : Fin k) (x : ℝ)
      (hx : x ∈ compandingCell a b S k β j) :
      A j.val ≤ x ∧ x ≤ A (j.val + 1) := by
    unfold compandingCell at hx
    split_ifs at hx with h
    · exact hx
    · exact ⟨hx.1, hx.2.le⟩
  have hcell_open (j : Fin k) (hj : j.val + 1 < k) (x : ℝ)
      (hx : x ∈ compandingCell a b S k β j) : x < A (j.val + 1) := by
    unfold compandingCell at hx
    split_ifs at hx with h
    · omega
    · exact hx.2
  have hmeas (j : Fin k) : MeasurableSet (compandingCell a b S k β j) := by
    unfold compandingCell
    split_ifs <;> measurability
  have hdisj : ∀ i j : Fin k, i ≠ j →
      Disjoint (compandingCell a b S k β i)
        (compandingCell a b S k β j) := by
    intro i j hne
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    have hi : i.val < j.val ∨ j.val < i.val :=
      lt_or_gt_of_ne (Fin.val_injective.ne hne)
    rcases hi with hij | hji
    · have hnext : i.val + 1 ≤ j.val := by omega
      have hupper : A (i.val + 1) ≤ A j.val := by
        rcases eq_or_lt_of_le hnext with heq | hlt
        · exact le_of_eq (congrArg A heq)
        · exact (hstrict _ _ hlt j.isLt.le).le
      have hxi' := hcell_open i (by omega) x hxi
      have hxj' := (hcell_bounds j x hxj).1
      linarith
    · have hnext : j.val + 1 ≤ i.val := by omega
      have hupper : A (j.val + 1) ≤ A i.val := by
        rcases eq_or_lt_of_le hnext with heq | hlt
        · exact le_of_eq (congrArg A heq)
        · exact (hstrict _ _ hlt i.isLt.le).le
      have hxj' := hcell_open j (by omega) x hxj
      have hxi' := (hcell_bounds i x hxi).1
      linarith
  have hcover : (⋃ j : Fin k, compandingCell a b S k β j) =
      Set.Icc a b := by
    ext x
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hl, hu⟩ := hcell_bounds j x hj
      exact ⟨(hmem j.val j.isLt.le).1.trans hl,
        hu.trans (hmem (j.val + 1) (by omega)).2⟩
    · intro hx
      by_cases hxb : x = b
      · let j : Fin k := ⟨k - 1, by omega⟩
        have hjlast : j.val + 1 = k := by dsimp [j]; omega
        apply Set.mem_iUnion.mpr
        refine ⟨j, ?_⟩
        unfold compandingCell
        rw [if_pos hjlast]
        rw [hjlast, hlast]
        subst x
        exact ⟨(hmem j.val j.isLt.le).2, le_refl b⟩
      · have hxab : x ∈ Set.Ico (A 0) (A k) := by
          simpa [A, hfirst, hlast] using (show x ∈ Set.Ico a b from ⟨hx.1, lt_of_le_of_ne hx.2 hxb⟩)
        have hxunion := Ico_subset_biUnion_Ico k A hxab
        simp only [Set.mem_iUnion, Finset.mem_range] at hxunion
        obtain ⟨n, hn, hxn⟩ := hxunion
        let j : Fin k := ⟨n, hn⟩
        apply Set.mem_iUnion.mpr
        refine ⟨j, ?_⟩
        unfold compandingCell
        by_cases hlastj : j.val + 1 = k
        · rw [if_pos hlastj]
          exact ⟨hxn.1, hxn.2.le⟩
        · rw [if_neg hlastj]
          exact hxn
  refine ⟨⟨hmeas, hdisj, hcover⟩, ?_⟩
  intro j s
  unfold compandingMidpoint
  have hj0 := hmem j.val j.isLt.le
  have hj1 := hmem (j.val + 1) (by omega)
  exact ⟨by linarith [hj0.1, hj1.1], by linarith [hj0.2, hj1.2]⟩

/-- Each companding cell has exactly one `k`th of the total square-root
diagonal mass, expressed as an integral between its consecutive boundaries. -/
theorem companding_interval_mass (a b : ℝ) (hab : a < b)
    (S k : ℕ) (hS : 0 < S) (hk : 0 < k)
    (β : Fin S → ℝ → ℝ → ℝ)
    (hcont : ∀ s, ContinuousOn (fun p : ℝ × ℝ => β s p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc a b))
    (hpos : ∀ s x z, x ∈ Set.Icc a b → z ∈ Set.Icc a b → 0 < β s x z)
    (j : Fin k) :
    (∫ x in boundary a b S k j.val β..boundary a b S k (j.val + 1) β,
      Real.sqrt (diagonalWeight S β x)) =
      (∫ x in a..b, Real.sqrt (diagonalWeight S β x)) / k := by
  -- Subtract the two boundary_equal_mass identities using integral_add_adjacent_intervals.
  have h0 := boundary_equal_mass a b hab S k j.val hS hk j.isLt.le β hcont hpos
  have h1 := boundary_equal_mass a b hab S k (j.val + 1) hS hk
    (by omega) β hcont hpos
  have hf := (sqrt_mass_regular a b hab S hS β hcont hpos).1
  have hi0 : IntervalIntegrable (fun x => Real.sqrt (diagonalWeight S β x))
      volume a (boundary a b S k j.val β) :=
    ContinuousOn.intervalIntegrable_of_Icc h0.1.1
      (hf.mono (by intro x hx; exact ⟨hx.1, hx.2.trans h0.1.2⟩))
  have hi1 : IntervalIntegrable (fun x => Real.sqrt (diagonalWeight S β x))
      volume (boundary a b S k j.val β) (boundary a b S k (j.val + 1) β) := by
    have hord := (boundary_order a b hab S k hS hk β hcont hpos).2.2
      j.val (j.val + 1) (by omega) (by omega)
    exact ContinuousOn.intervalIntegrable_of_Icc hord.le
      (hf.mono (by intro x hx; exact ⟨h0.1.1.trans hx.1, hx.2.trans h1.1.2⟩))
  have hadd := intervalIntegral.integral_add_adjacent_intervals hi0 hi1
  rw [h0.2, h1.2] at hadd
  have hkreal : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hcast : ((j.val + 1 : ℕ) : ℝ) = (j.val : ℝ) + 1 := by norm_cast
  rw [hcast] at hadd
  calc
    (∫ x in boundary a b S k j.val β..boundary a b S k (j.val + 1) β,
      Real.sqrt (diagonalWeight S β x)) =
        ((j.val : ℝ) + 1) / k * (∫ x in a..b, Real.sqrt (diagonalWeight S β x)) -
        (j.val : ℝ) / k * (∫ x in a..b, Real.sqrt (diagonalWeight S β x)) := by
          linarith [hadd]
    _ = (∫ x in a..b, Real.sqrt (diagonalWeight S β x)) / k := by ring

/-- A positive uniform lower bound for square-root diagonal mass forces every
companding cell length to be at most a constant times `1/k`. -/
theorem companding_length_bound (a b : ℝ) (hab : a < b)
    (S : ℕ) (hS : 0 < S) (β : Fin S → ℝ → ℝ → ℝ)
    (hcont : ∀ s, ContinuousOn (fun p : ℝ × ℝ => β s p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc a b))
    (hpos : ∀ s x z, x ∈ Set.Icc a b → z ∈ Set.Icc a b → 0 < β s x z) :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 0 < k → ∀ j : Fin k,
      c * (boundary a b S k (j.val + 1) β - boundary a b S k j.val β) ≤
        (∫ x in a..b, Real.sqrt (diagonalWeight S β x)) / k := by
  -- Minimize the positive continuous square-root weight on Icc a b, then
  -- compare its constant lower bound with companding_interval_mass.
  let f : ℝ → ℝ := fun x => Real.sqrt (diagonalWeight S β x)
  have hf := (sqrt_mass_regular a b hab S hS β hcont hpos).1
  obtain ⟨c, hc, hcf⟩ := isCompact_Icc.exists_forall_le' hf
    (a := (0 : ℝ)) (by
      intro x hx
      exact Real.sqrt_pos.2 ((diagonal_regular a b S hS β hcont hpos).2 x hx))
  refine ⟨c, hc, ?_⟩
  intro k hk j
  have h0 := (boundary_equal_mass a b hab S k j.val hS hk j.isLt.le β hcont hpos).1
  have h1 := (boundary_equal_mass a b hab S k (j.val + 1) hS hk
    (by omega) β hcont hpos).1
  have hord := (boundary_order a b hab S k hS hk β hcont hpos).2.2
    j.val (j.val + 1) (by omega) (by omega)
  have hfi : IntervalIntegrable f volume
      (boundary a b S k j.val β) (boundary a b S k (j.val + 1) β) :=
    ContinuousOn.intervalIntegrable_of_Icc hord.le
      (hf.mono (by intro x hx; exact ⟨h0.1.trans hx.1, hx.2.trans h1.2⟩))
  have hmono := intervalIntegral.integral_mono_on hord.le intervalIntegrable_const hfi
    (by intro x hx; exact hcf x ⟨h0.1.trans hx.1, hx.2.trans h1.2⟩)
  rw [intervalIntegral.integral_const] at hmono
  simpa only [smul_eq_mul, mul_comm] using
    (hmono.trans_eq (companding_interval_mass a b hab S k hS hk β hcont hpos j))

/-- The midpoint diagonal-weight surrogate is the exact leading term obtained
by replacing each cell's varying weights by their diagonal value at its midpoint. -/
noncomputable def compandingSurrogateCost (a b : ℝ) (S k : ℕ)
    (β : Fin S → ℝ → ℝ → ℝ) : ℝ :=
  ∑ j : Fin k,
    diagonalWeight S β
        ((boundary a b S k j.val β + boundary a b S k (j.val + 1) β) / 2) *
      (boundary a b S k (j.val + 1) β - boundary a b S k j.val β) ^ 2 / 4

/-- The absolute-distance integral over each half-open companding cell is
exactly one quarter of the square of its endpoint separation. -/
theorem companding_cell_midpoint_moment (a b : ℝ) (hab : a < b)
    (S k : ℕ) (hS : 0 < S) (hk : 0 < k)
    (β : Fin S → ℝ → ℝ → ℝ)
    (hcont : ∀ s, ContinuousOn (fun p : ℝ × ℝ => β s p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc a b))
    (hpos : ∀ s x z, x ∈ Set.Icc a b → z ∈ Set.Icc a b → 0 < β s x z)
    (j : Fin k) (s : Fin S) :
    (∫ x in compandingCell a b S k β j,
      |x - compandingMidpoint a b S k β j s|) =
      (boundary a b S k (j.val + 1) β - boundary a b S k j.val β) ^ 2 / 4 := by
  have hord := (boundary_order a b hab S k hS hk β hcont hpos).2.2
    j.val (j.val + 1) (by omega) (by omega)
  unfold compandingCell compandingMidpoint
  split_ifs with hlast
  · rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hord.le]
    exact interval_midpoint_moment _ _ hord.le
  · rw [integral_Ico_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hord.le]
    exact interval_midpoint_moment _ _ hord.le

/-- On sufficiently fine companding cells, the midpoint square-root weight
times cell length differs from the cell's exact equal mass by at most an
arbitrarily small multiple of that length, uniformly across cells. -/
theorem companding_midpoint_mass_error_eventually (a b : ℝ) (hab : a < b)
    (S : ℕ) (hS : 0 < S) (β : Fin S → ℝ → ℝ → ℝ)
    (hcont : ∀ s, ContinuousOn (fun p : ℝ × ℝ => β s p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc a b))
    (hpos : ∀ s x z, x ∈ Set.Icc a b → z ∈ Set.Icc a b → 0 < β s x z) :
    ∀ η : ℝ, 0 < η → ∃ K : ℕ, ∀ k : ℕ, K ≤ k → 0 < k →
      ∀ j : Fin k,
      |Real.sqrt (diagonalWeight S β
          ((boundary a b S k j.val β + boundary a b S k (j.val + 1) β) / 2)) *
          (boundary a b S k (j.val + 1) β - boundary a b S k j.val β) -
        (∫ x in a..b, Real.sqrt (diagonalWeight S β x)) / k| ≤
        η * (boundary a b S k (j.val + 1) β - boundary a b S k j.val β) := by
  -- Use uniform continuity of sqrt(diagonalWeight) on Icc a b and
  -- companding_length_bound to make every cell shorter than its modulus.
  -- Integrate the pointwise midpoint error, then use companding_interval_mass.
  intro η hη
  let f : ℝ → ℝ := fun x => Real.sqrt (diagonalWeight S β x)
  have hf : ContinuousOn f (Set.Icc a b) :=
    (sqrt_mass_regular a b hab S hS β hcont hpos).1
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous hf
  obtain ⟨δ, hδ, huc⟩ := (Metric.uniformContinuousOn_iff.mp hu) η hη
  obtain ⟨c, hc, hbound⟩ := companding_length_bound a b hab S hS β hcont hpos
  let M : ℝ := ∫ x in a..b, f x
  obtain ⟨K, hK⟩ := exists_nat_gt (M / (c * δ))
  refine ⟨K, ?_⟩
  intro k hkK hk j
  let l := boundary a b S k j.val β
  let r := boundary a b S k (j.val + 1) β
  let m := (l + r) / 2
  have hl : l ∈ Set.Icc a b :=
    (boundary_equal_mass a b hab S k j.val hS hk j.isLt.le β hcont hpos).1
  have hr : r ∈ Set.Icc a b :=
    (boundary_equal_mass a b hab S k (j.val + 1) hS hk (by omega) β hcont hpos).1
  have hord : l ≤ r :=
    ((boundary_order a b hab S k hS hk β hcont hpos).2.2
      j.val (j.val + 1) (by omega) (by omega)).le
  have hm : m ∈ Set.Icc a b :=
    ⟨by dsimp [m]; linarith [hl.1, hr.1], by dsimp [m]; linarith [hl.2, hr.2]⟩
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  have hKreal : (K : ℝ) ≤ k := by exact_mod_cast hkK
  have hshort : r - l < δ := by
    have hlen := hbound k hk j
    have hmass : M < (k : ℝ) * (c * δ) :=
      (div_lt_iff₀ (mul_pos hc hδ)).mp (lt_of_lt_of_le hK hKreal)
    have hlen' : c * (r - l) * (k : ℝ) ≤ M :=
      (le_div_iff₀ hkreal).mp hlen
    by_contra hn
    have hge := mul_le_mul_of_nonneg_left (le_of_not_gt hn) hc.le
    have hge' := mul_le_mul_of_nonneg_left hge hkreal.le
    nlinarith
  have hfi : IntervalIntegrable f volume l r :=
    ContinuousOn.intervalIntegrable_of_Icc hord
      (hf.mono (by intro x hx; exact ⟨hl.1.trans hx.1, hx.2.trans hr.2⟩))
  have hpoint : ∀ x ∈ Set.uIoc l r, ‖f m - f x‖ ≤ η := by
    intro x hx
    rw [Set.uIoc_of_le hord] at hx
    have hxmem : x ∈ Set.Icc a b :=
      ⟨hl.1.trans hx.1.le, hx.2.trans hr.2⟩
    have hmx : |m - x| ≤ r - l := by
      apply abs_le.mpr
      dsimp [m]
      constructor <;> linarith [hx.1, hx.2]
    have hdist : dist m x < δ := by
      simpa [Real.dist_eq] using (lt_of_le_of_lt hmx hshort)
    simpa [Real.norm_eq_abs, Real.dist_eq] using (huc m hm x hxmem hdist).le
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  have heq : f m * (r - l) - M / k = ∫ x in l..r, (f m - f x) := by
    rw [← companding_interval_mass a b hab S k hS hk β hcont hpos j]
    rw [intervalIntegral.integral_sub intervalIntegrable_const hfi,
      intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  rw [show Real.sqrt (diagonalWeight S β ((boundary a b S k j.val β +
    boundary a b S k (j.val + 1) β) / 2)) = f m from rfl]
  change |f m * (r - l) - M / k| ≤ η * (r - l)
  rw [heq, ← Real.norm_eq_abs]
  simpa only [abs_of_nonneg (sub_nonneg.mpr hord)] using hnorm

/-- On sufficiently fine companding cells, each actual coefficient differs
from its midpoint diagonal value by at most any prescribed positive error. -/
theorem companding_coefficient_error_eventually (a b : ℝ) (hab : a < b)
    (S : ℕ) (hS : 0 < S) (β : Fin S → ℝ → ℝ → ℝ)
    (hcont : ∀ s, ContinuousOn (fun p : ℝ × ℝ => β s p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc a b))
    (hpos : ∀ s x z, x ∈ Set.Icc a b → z ∈ Set.Icc a b → 0 < β s x z) :
    ∀ η : ℝ, 0 < η → ∃ K : ℕ, ∀ k : ℕ, K ≤ k → 0 < k →
      ∀ (j : Fin k) (s : Fin S) (x : ℝ),
        x ∈ compandingCell a b S k β j →
        |β s x (compandingMidpoint a b S k β j s) -
          β s (compandingMidpoint a b S k β j s)
            (compandingMidpoint a b S k β j s)| ≤ η := by
  -- Uniform continuity on the compact square controls the pairs (x,m)
  -- and (m,m); companding_length_bound makes their distance uniformly small.
  intro η hη
  obtain ⟨δ, hδ, huc⟩ := coefficient_uniform_continuity a b hab S β hcont η hη
  obtain ⟨c, hc, hbound⟩ := companding_length_bound a b hab S hS β hcont hpos
  let M : ℝ := ∫ x in a..b, Real.sqrt (diagonalWeight S β x)
  obtain ⟨K, hK⟩ := exists_nat_gt (M / (c * δ))
  refine ⟨K, ?_⟩
  intro k hkK hk j s x hx
  let l := boundary a b S k j.val β
  let r := boundary a b S k (j.val + 1) β
  let m := compandingMidpoint a b S k β j s
  have hl : l ∈ Set.Icc a b :=
    (boundary_equal_mass a b hab S k j.val hS hk j.isLt.le β hcont hpos).1
  have hr : r ∈ Set.Icc a b :=
    (boundary_equal_mass a b hab S k (j.val + 1) hS hk (by omega) β hcont hpos).1
  have hm : m ∈ Set.Icc a b := (companding_feasible a b hab S k hS hk β hcont hpos).2 j s
  have hxr : l ≤ x ∧ x ≤ r := by
    unfold compandingCell at hx
    split_ifs at hx with h
    · exact hx
    · exact ⟨hx.1, hx.2.le⟩
  have hxmem : x ∈ Set.Icc a b := ⟨hl.1.trans hxr.1, hxr.2.trans hr.2⟩
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  have hKreal : (K : ℝ) ≤ k := by exact_mod_cast hkK
  have hshort : r - l < δ := by
    have hlen := hbound k hk j
    have hmass : M < (k : ℝ) * (c * δ) :=
      (div_lt_iff₀ (mul_pos hc hδ)).mp (lt_of_lt_of_le hK hKreal)
    have hlen' : c * (r - l) * (k : ℝ) ≤ M :=
      (le_div_iff₀ hkreal).mp hlen
    by_contra hn
    have hge := mul_le_mul_of_nonneg_left (le_of_not_gt hn) hc.le
    have hge' := mul_le_mul_of_nonneg_left hge hkreal.le
    nlinarith
  have hxm : |x - m| ≤ r - l := by
    dsimp [m, compandingMidpoint]
    apply abs_le.mpr
    constructor <;> dsimp [l, r] at * <;> linarith
  have hdist : dist (x, m) (m, m) < δ := by
    simpa [dist_prod_same_right, Real.dist_eq] using (lt_of_le_of_lt hxm hshort)
  exact (huc s (x, m) (m, m) ⟨hxmem, hm⟩ ⟨hm, hm⟩ hdist).le

end

end Causalean.Mathlib.Analysis.Quantization
