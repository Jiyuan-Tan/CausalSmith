module
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.Construction
/-! All-count sensitivity and Efron--Stein-conditional iid variance stability. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
namespace CausalSmith.Stat.PrivateCateRoughdesign
/-- Appending a last index adds exactly its pairs with the existing indices. [The displayed conclusion](goal) follows. -/
-- @node: ordered_pair_sum_append
lemma ordered_pair_sum_append (s : ℕ) (f : Fin (s + 1) → Fin (s + 1) → ℝ) :
    (∑ i, ∑ l, if i < l then f i l else 0) =
      (∑ i : Fin s, ∑ l : Fin s,
        if i < l then f i.castSucc l.castSucc else 0) +
      ∑ i : Fin s, f i.castSucc (Fin.last s) := by
  classical
  rw [Fin.sum_univ_castSucc]
  have hlast : ∀ i : Fin s, ¬ Fin.last s < i.castSucc :=
    fun i => not_lt.mpr (Fin.castSucc_lt_last i).le
  simp [Fin.sum_univ_castSucc, hlast, Finset.sum_add_distrib]

/-- The number of ordered index pairs with the first strictly smaller is the binomial count. [The displayed conclusion](goal) follows. -/
-- @node: ordered_pair_count
lemma ordered_pair_count (s : ℕ) :
    (∑ i : Fin s, ∑ l : Fin s, if i < l then (1 : ℝ) else 0) =
      (Nat.choose s 2 : ℝ) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [ordered_pair_sum_append, ih]
    simp [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]

/-- A unit-bounded kernel has a pair sum bounded by the number of pairs.  [the theorem's stated inputs and assumptions](hyp:hK), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:s,K,z). -/
-- @node: ordered_pair_sum_bound
lemma ordered_pair_sum_bound (s : ℕ) (K : O → O → ℝ) (z : Fin s → O)
    (hK : ∀ x y, |K x y| ≤ 1) :
    |∑ i : Fin s, ∑ l : Fin s, if i < l then K (z i) (z l) else 0| ≤
      (Nat.choose s 2 : ℝ) := by
  calc
    _ ≤ ∑ i : Fin s, |∑ l : Fin s, if i < l then K (z i) (z l) else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin s, ∑ l : Fin s, |if i < l then K (z i) (z l) else 0| := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin s, ∑ l : Fin s, if i < l then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro l hl
      by_cases hil : i < l
      · simpa only [if_pos hil] using hK (z i) (z l)
      · simp only [if_neg hil, abs_zero, le_refl]
    _ = _ := ordered_pair_count s

/-- Count-weighted pair contributions are bounded by the occupancy, at every count.  [the theorem's stated inputs and assumptions](hyp:hK), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:s,K,z). -/
-- @node: pairContribution_abs_le
lemma pairContribution_abs_le (s : ℕ) (K : O → O → ℝ) (z : Fin s → O)
    (hK : ∀ x y, |K x y| ≤ 1) : |pairContribution K z| ≤ s := by
  classical
  by_cases hs : s < 2
  · simp [pairContribution, hs]
  have hc : 0 < (Nat.choose s 2 : ℝ) := by
    exact_mod_cast Nat.choose_pos (show 2 ≤ s by omega)
  rw [pairContribution, if_neg hs, abs_mul,
    abs_of_nonneg (div_nonneg (Nat.cast_nonneg s) hc.le)]
  calc
    _ ≤ ((s : ℝ) / Nat.choose s 2) * (Nat.choose s 2 : ℝ) :=
      mul_le_mul_of_nonneg_left (ordered_pair_sum_bound s K z hK) (by positivity)
    _ = _ := div_mul_cancel₀ _ hc.ne'

/-- At occupancy at least two, insertion equals twice the new-pair average minus the old
pair average, as in the all-count stability roadmap.  [the theorem's stated inputs and assumptions](hyp:K,z), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:s,hs). -/
-- @node: pairContribution_insertion_identity
lemma pairContribution_insertion_identity (s : ℕ) (hs : 2 ≤ s)
    (K : O → O → ℝ) (z : Fin (s + 1) → O) :
    pairContribution K z - pairContribution K (fun i : Fin s => z i.castSucc) =
      2 / (s : ℝ) * (∑ i : Fin s, K (z i.castSucc) (z (Fin.last s))) -
      pairContribution K (fun i : Fin s => z i.castSucc) / (s : ℝ) := by
  classical
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast (show s ≠ 0 by omega)
  have hs1 : (s : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ s := by exact_mod_cast hs
    linarith
  simp only [pairContribution, show ¬s < 2 by omega, show ¬s + 1 < 2 by omega,
    if_false]
  rw [ordered_pair_sum_append]
  simp only [Nat.cast_choose_two ℝ, Nat.cast_add, Nat.cast_one]
  have hsp : (s : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hs0, hs1, hsp]
  ring

/-- The new pairs have total absolute value at most the old occupancy.  [the theorem's stated inputs and assumptions](hyp:z,hK), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:s,K). -/
-- @node: insertion_pair_sum_bound
lemma insertion_pair_sum_bound (s : ℕ) (K : O → O → ℝ)
    (z : Fin (s + 1) → O) (hK : ∀ x y, |K x y| ≤ 1) :
    |∑ i : Fin s, K (z i.castSucc) (z (Fin.last s))| ≤ s := by
  calc
    _ ≤ ∑ i : Fin s, |K (z i.castSucc) (z (Fin.last s))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin s, (1 : ℝ) := Finset.sum_le_sum (fun i hi => hK _ _)
    _ = _ := by simp

/-- Inserting into a cell with at least two records changes a scalar contribution by at most
three, using the exact pair identity rather than a count-specific approximation.  [the theorem's stated inputs and assumptions](hyp:K,z,hK), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:s,hs). -/
-- @node: pairContribution_insertion_bound_large
lemma pairContribution_insertion_bound_large (s : ℕ) (hs : 2 ≤ s)
    (K : O → O → ℝ) (z : Fin (s + 1) → O) (hK : ∀ x y, |K x y| ≤ 1) :
    |pairContribution K z - pairContribution K (fun i : Fin s => z i.castSucc)| ≤ 3 := by
  have hsR : 0 < (s : ℝ) := by exact_mod_cast (show 0 < s by omega)
  have hb := insertion_pair_sum_bound s K z hK
  have hf := pairContribution_abs_le s K (fun i => z i.castSucc) hK
  rw [pairContribution_insertion_identity s hs K z]
  calc
    _ ≤ |2 / (s : ℝ) * ∑ i : Fin s, K (z i.castSucc) (z (Fin.last s))| +
        |pairContribution K (fun i : Fin s => z i.castSucc) / (s : ℝ)| :=
      abs_sub _ _
    _ = (2 / (s : ℝ)) * |∑ i : Fin s, K (z i.castSucc) (z (Fin.last s))| +
        |pairContribution K (fun i : Fin s => z i.castSucc)| / (s : ℝ) := by
      simp only [abs_mul, abs_div, abs_of_pos hsR, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ (2 / (s : ℝ)) * (s : ℝ) + (s : ℝ) / (s : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_left hb (by positivity))
        (div_le_div_of_nonneg_right hf hsR.le)
    _ = 3 := by field_simp; ring

/-- A singleton contributes zero, and the first pair contributes twice its kernel value. [The displayed conclusion](goal) follows. -/
-- @node: pairContribution_small_counts
lemma pairContribution_small_counts (K : O → O → ℝ) (z : Fin 2 → O) :
    pairContribution K (fun i : Fin 1 => z i.castSucc) = 0 ∧
      pairContribution K z = 2 * K (z 0) (z 1) := by
  classical
  simp [pairContribution, Fin.sum_univ_two]

/-- The insertion bound includes empty and singleton cells as well as all larger occupancies.  [the theorem's stated inputs and assumptions](hyp:z,hK), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:s,K). -/
-- @node: pairContribution_insertion_bound
lemma pairContribution_insertion_bound (s : ℕ) (K : O → O → ℝ)
    (z : Fin (s + 1) → O) (hK : ∀ x y, |K x y| ≤ 1) :
    |pairContribution K z - pairContribution K (fun i : Fin s => z i.castSucc)| ≤ 3 := by
  by_cases hs : 2 ≤ s
  · exact pairContribution_insertion_bound_large s hs K z hK
  have hsmall : s = 0 ∨ s = 1 := by omega
  rcases hsmall with rfl | rfl
  · simp [pairContribution]
  · obtain ⟨hzero, hpair⟩ := pairContribution_small_counts K z
    rw [hzero, hpair, sub_zero, abs_mul]
    have hb := hK (z 0) (z 1)
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith

/-- Both causal pair kernels are symmetric, and their joint absolute mass is at most two.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:z,z'). -/
-- @node: causal_pair_kernel_bounds
lemma causal_pair_kernel_bounds (z z' : O) :
    KN z z' = KN z' z ∧ KD z z' = KD z' z ∧
    |KN z z'| ≤ KD z z' ∧ 0 ≤ KD z z' ∧ KD z z' ≤ 1 := by
  rcases z with ⟨x, a, y⟩
  rcases z' with ⟨x', a', y'⟩
  cases a <;> cases a' <;> cases y <;> cases y' <;> norm_num [KN, KD, bit]

/-- The causal numerator and denominator satisfy the scalar unit-kernel bound.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:z,z'). -/
-- @node: causal_pair_kernel_unit_bounds
lemma causal_pair_kernel_unit_bounds (z z' : O) : |KN z z'| ≤ 1 ∧ |KD z z'| ≤ 1 := by
  obtain ⟨hsN, hsD, hND, hD0, hD1⟩ := causal_pair_kernel_bounds z z'
  exact ⟨hND.trans hD1, by rwa [abs_of_nonneg hD0]⟩

/-- The two causal contributions have joint insertion sensitivity at most six at every count.  [the theorem's stated inputs and assumptions](hyp:s,z), and [the asserted conclusion follows](goal). -/
-- @node: causal_pair_insertion_bound
lemma causal_pair_insertion_bound (s : ℕ) (z : Fin (s + 1) → O) :
    |pairContribution KN z - pairContribution KN (fun i : Fin s => z i.castSucc)| +
      |pairContribution KD z - pairContribution KD (fun i : Fin s => z i.castSucc)| ≤ 6 := by
  have hN := pairContribution_insertion_bound s KN z
    (fun x y => (causal_pair_kernel_unit_bounds x y).1)
  have hD := pairContribution_insertion_bound s KD z
    (fun x y => (causal_pair_kernel_unit_bounds x y).2)
  linarith

/-- A replacement through a common deleted dataset has joint sensitivity at most twelve.  [the theorem's stated inputs and assumptions](hyp:hcommon), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:s,z,z'). -/
-- @node: causal_pair_replacement_bound
lemma causal_pair_replacement_bound (s : ℕ) (z z' : Fin (s + 1) → O)
    (hcommon : ∀ i : Fin s, z i.castSucc = z' i.castSucc) :
    |pairContribution KN z - pairContribution KN z'| +
      |pairContribution KD z - pairContribution KD z'| ≤ 12 := by
  have hN : pairContribution KN (fun i : Fin s => z i.castSucc) =
      pairContribution KN (fun i : Fin s => z' i.castSucc) := by
    congr 1
    funext i
    exact hcommon i
  have hD : pairContribution KD (fun i : Fin s => z i.castSucc) =
      pairContribution KD (fun i : Fin s => z' i.castSucc) := by
    congr 1
    funext i
    exact hcommon i
  have hz := causal_pair_insertion_bound s z
  have hz' := causal_pair_insertion_bound s z'
  rw [← hN, ← hD] at hz'
  have htN := abs_sub_le (pairContribution KN z)
    (pairContribution KN (fun i : Fin s => z i.castSucc)) (pairContribution KN z')
  have htD := abs_sub_le (pairContribution KD z)
    (pairContribution KD (fun i : Fin s => z i.castSucc)) (pairContribution KD z')
  rw [abs_sub_comm (pairContribution KN (fun i : Fin s => z i.castSucc))] at htN
  rw [abs_sub_comm (pairContribution KD (fun i : Fin s => z i.castSucc))] at htD
  linarith

/-- The insertion indicator bound yields the squared replacement bound used by Efron--Stein.  [the theorem's stated inputs and assumptions](hyp:hJ,hJ',hchange), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:change,J,J'). -/
-- @node: replacement_square_indicator_bound
lemma replacement_square_indicator_bound (change J J' : ℝ)
    (hJ : J = 0 ∨ J = 1) (hJ' : J' = 0 ∨ J' = 1)
    (hchange : |change| ≤ 3 * (J + J')) : change^2 ≤ 18 * (J + J') := by
  have hsq : change^2 ≤ (3 * (J + J'))^2 := by
    have hnonneg := abs_nonneg change
    nlinarith [sq_abs change]
  rcases hJ with rfl | rfl <;> rcases hJ' with rfl | rfl <;> nlinarith

/-- Reindexing the selected record set by any finite enumeration preserves its moment sums.  [the theorem's stated inputs and assumptions](hyp:e,v), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,s,I). -/
-- @node: selected_sum
lemma selected_sum (n s : ℕ) (I : Finset (Fin n))
    (e : Fin s ≃ {i // i ∈ I}) (v : Fin n → ℝ) :
    (∑ i : Fin s, v (e i)) = ∑ i ∈ I, v i := by
  classical
  rw [e.sum_comp (fun i => v i.val)]
  exact Finset.sum_attach I v

/-- Every enumeration of the records in a cell realizes its closed numerator and denominator as
count-weighted pair contributions.  [the theorem's stated inputs and assumptions](hyp:e), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k,h,D,j). -/
-- @node: cell_pair_formulas
lemma cell_pair_formulas (n k : ℕ) (h : ℝ) (D : Dataset n) (j : Fin k)
    (e : Fin (cellCount n h k D j) ≃ {i // i ∈ cellRecords n h k D j}) :
    pairContribution KN (fun i => D (e i)) = numeratorCell n h k D j ∧
    pairContribution KD (fun i => D (e i)) = denominatorCell n h k D j := by
  classical
  obtain ⟨hN, hD⟩ := pair_moment_formulas _ (fun i => D (e i))
  have hsum (v : O → ℝ) :
      (∑ i, v (D (e i))) = cellSum n h k D j v :=
    selected_sum n _ _ e (fun i => v (D i))
  rw [hsum (fun z => bit z.2.1 * bit z.2.2),
    hsum (fun z => bit z.2.1), hsum (fun z => bit z.2.2)] at hN
  rw [hsum (fun z => bit z.2.1)] at hD
  exact ⟨hN, hD⟩

/-- Each scalar cell contribution is bounded by its occupancy, including empty and singleton
cells.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k,h,D,j). -/
-- @node: cell_contribution_bounds
lemma cell_contribution_bounds (n k : ℕ) (h : ℝ) (D : Dataset n) (j : Fin k) :
    |numeratorCell n h k D j| ≤ cellCount n h k D j ∧
    |denominatorCell n h k D j| ≤ cellCount n h k D j := by
  classical
  let e : Fin (cellCount n h k D j) ≃ {i // i ∈ cellRecords n h k D j} :=
    (Fintype.equivFinOfCardEq (by simp [cellCount])).symm
  obtain ⟨hN, hD⟩ := cell_pair_formulas n k h D j e
  rw [← hN, ← hD]
  exact ⟨pairContribution_abs_le _ KN _ (fun x y => (causal_pair_kernel_unit_bounds x y).1),
    pairContribution_abs_le _ KD _ (fun x y => (causal_pair_kernel_unit_bounds x y).2)⟩

/-- Distinct public cells are disjoint, including the final right endpoint.  [the theorem's stated inputs and assumptions](hyp:i,j,hij), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:k,h,hh,hk). -/
-- @node: cell_disjoint
lemma cell_disjoint (k : ℕ) (h : ℝ) (hh : 0 < h) (hk : 0 < k)
    (i j : Fin k) (hij : i ≠ j) : Disjoint (cell h k i) (cell h k j) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hd : 0 < cellWidth h k := by unfold cellWidth; positivity
  have hw : (k : ℝ) * cellWidth h k = 2 * h := by
    unfold cellWidth
    field_simp
  have hlt (i j : Fin k) (hij : i < j) : Disjoint (cell h k i) (cell h k j) := by
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    have horder : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast hij
    have hupper := mul_le_mul_of_nonneg_right horder hd.le
    rcases hxi.2 with hi | ⟨hi, hx⟩
    · linarith [hxj.1]
    · have : i.val < j.val := hij
      omega
  rcases lt_or_gt_of_ne hij with hij | hij
  · exact hlt i j hij
  · exact (hlt j i hij).symm

/-- Disjoint cell selection counts each dataset record at most once.  [the theorem's stated inputs and assumptions](hyp:D), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k,h,hh,hk). -/
-- @node: total_cell_counts
lemma total_cell_counts (n k : ℕ) (h : ℝ) (hh : 0 < h) (hk : 0 < k)
    (D : Dataset n) : (∑ j : Fin k, cellCount n h k D j) ≤ n := by
  classical
  have hd : ∀ i j : Fin k, i ≠ j →
      Disjoint (cellRecords n h k D i) (cellRecords n h k D j) := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro r hi hj
    have hx := Set.disjoint_left.mp (cell_disjoint k h hh hk i j hij)
    exact hx (by simpa [cellRecords] using hi) (by simpa [cellRecords] using hj)
  have hcard := Finset.card_biUnion (s := (Finset.univ : Finset (Fin k)))
    (t := fun j => cellRecords n h k D j) (fun i _ j _ hij => hd i j hij)
  have hle := Finset.card_le_card
    (show Finset.univ.biUnion (fun j : Fin k => cellRecords n h k D j) ⊆
      (Finset.univ : Finset (Fin n)) from Finset.subset_univ _)
  simpa only [hcard, Finset.card_univ, Fintype.card_fin, cellCount] using hle

/-- Both scalar statistics are bounded by the sample size on every input dataset.  [the theorem's stated inputs and assumptions](hyp:D), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k,h,hh,hk). -/
-- @node: statistic_bounds
lemma statistic_bounds (n k : ℕ) (h : ℝ) (hh : 0 < h) (hk : 0 < k)
    (D : Dataset n) : |SN n h k D| ≤ n ∧ |SD n h k D| ≤ n := by
  have hc : (∑ j : Fin k, (cellCount n h k D j : ℝ)) ≤ n := by
    exact_mod_cast total_cell_counts n k h hh hk D
  constructor
  · exact (Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_sum (fun j _ => (cell_contribution_bounds n k h D j).1)).trans hc)
  · exact (Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_sum (fun j _ => (cell_contribution_bounds n k h D j).2)).trans hc)

/-- The bounded measurable statistics belong to every finite-measure Lp space, in particular the
square-integrability class needed for Efron--Stein.  [the theorem's stated inputs and assumptions](hyp:Q,p), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k,h,hh,hk). -/
-- @node: statistic_memLp
lemma statistic_memLp (n k : ℕ) (h : ℝ) (hh : 0 < h) (hk : 0 < k)
    (Q : Measure (Dataset n)) [IsFiniteMeasure Q] (p : ENNReal) :
    MemLp (SN n h k) p Q ∧ MemLp (SD n h k) p Q := by
  constructor
  · apply MemLp.of_bound (by fun_prop) (n : ℝ)
    exact ae_of_all _ (fun D => by simpa only [Real.norm_eq_abs] using
      (statistic_bounds n k h hh hk D).1)
  · apply MemLp.of_bound (by fun_prop) (n : ℝ)
    exact ae_of_all _ (fun D => by simpa only [Real.norm_eq_abs] using
      (statistic_bounds n k h hh hk D).2)


open Classical in
/-- The closed numerator moment formula on an arbitrary finite selected record set. -/
-- @node: selectedNumerator
def selectedNumerator {n : ℕ} (I : Finset (Fin n)) (D : Dataset n) : ℝ :=
  if I.card < 2 then 0 else
    2 * ((I.card : ℝ) * (∑ i ∈ I, bit (D i).2.1 * bit (D i).2.2) -
      (∑ i ∈ I, bit (D i).2.1) * (∑ i ∈ I, bit (D i).2.2)) / ((I.card : ℝ) - 1)
open Classical in
/-- The closed denominator moment formula on an arbitrary finite selected record set. -/
-- @node: selectedDenominator
def selectedDenominator {n : ℕ} (I : Finset (Fin n)) (D : Dataset n) : ℝ :=
  if I.card < 2 then 0 else
    2 * ((I.card : ℝ) * (∑ i ∈ I, bit (D i).2.1) -
      (∑ i ∈ I, bit (D i).2.1)^2) / ((I.card : ℝ) - 1)

/-- An arbitrary finite record selection has the same closed moments as its enumerated pair
contributions.  [the theorem's stated inputs and assumptions](hyp:e), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,I,D). -/
-- @node: selected_pair_formulas
lemma selected_pair_formulas {n : ℕ} (I : Finset (Fin n)) (D : Dataset n)
    (e : Fin I.card ≃ {i // i ∈ I}) :
    pairContribution KN (fun i => D (e i)) = selectedNumerator I D ∧
    pairContribution KD (fun i => D (e i)) = selectedDenominator I D := by
  obtain ⟨hN, hD⟩ := pair_moment_formulas _ (fun i => D (e i))
  have hsum (v : O → ℝ) :
      (∑ i, v (D (e i))) = ∑ i ∈ I, v (D i) :=
    selected_sum n _ _ e (fun i => v (D i))
  rw [hsum (fun z => bit z.2.1 * bit z.2.2),
    hsum (fun z => bit z.2.1), hsum (fun z => bit z.2.2)] at hN
  rw [hsum (fun z => bit z.2.1)] at hD
  exact ⟨hN, hD⟩

/-- Inserting one record into an arbitrary selected set changes the joint causal contribution by
at most six, at every count.  [the theorem's stated inputs and assumptions](hyp:r,hr), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,I,D). -/
-- @node: selected_insertion_bound
lemma selected_insertion_bound {n : ℕ} (I : Finset (Fin n)) (D : Dataset n)
    (r : Fin n) (hr : r ∉ I) :
    |selectedNumerator (insert r I) D - selectedNumerator I D| +
      |selectedDenominator (insert r I) D - selectedDenominator I D| ≤ 6 := by
  classical
  let e : Fin I.card ≃ {i // i ∈ I} :=
    (Fintype.equivFinOfCardEq (by simp)).symm
  let z : Fin (I.card + 1) → O := Fin.lastCases (D r) (fun i => D (e i))
  have hz (i : Fin I.card) : z i.castSucc = D (e i) := by simp [z]
  have hlast : z (Fin.last I.card) = D r := by simp [z]
  have hsum (v : O → ℝ) :
      (∑ i, v (z i)) = ∑ i ∈ insert r I, v (D i) := by
    rw [Fin.sum_univ_castSucc]
    simp_rw [hz]
    rw [selected_sum n _ I e (fun i => v (D i)), Finset.sum_insert hr, hlast]
    exact add_comm _ _
  obtain ⟨hN, hD⟩ := pair_moment_formulas _ z
  rw [hsum (fun z => bit z.2.1 * bit z.2.2),
    hsum (fun z => bit z.2.1), hsum (fun z => bit z.2.2)] at hN
  rw [hsum (fun z => bit z.2.1)] at hD
  have hcard := Finset.card_insert_of_notMem hr
  have hNi : pairContribution KN z = selectedNumerator (insert r I) D := by
    simpa only [selectedNumerator, hcard, Nat.cast_add, Nat.cast_one] using hN
  have hDi : pairContribution KD z = selectedDenominator (insert r I) D := by
    simpa only [selectedDenominator, hcard, Nat.cast_add, Nat.cast_one] using hD
  obtain ⟨hNo, hDo⟩ := selected_pair_formulas I D e
  have hb := causal_pair_insertion_bound I.card z
  simp_rw [hz] at hb
  rwa [hNi, hDi, hNo, hDo] at hb


/-- Selected contributions depend only on records at the selected indices.  [the theorem's stated inputs and assumptions](hyp:heq), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,I,D,D'). -/
-- @node: selected_congr
lemma selected_congr {n : ℕ} (I : Finset (Fin n)) (D D' : Dataset n)
    (heq : ∀ i ∈ I, D i = D' i) :
    selectedNumerator I D = selectedNumerator I D' ∧
    selectedDenominator I D = selectedDenominator I D' := by
  have hs (v : O → ℝ) : (∑ i ∈ I, v (D i)) = ∑ i ∈ I, v (D' i) :=
    Finset.sum_congr rfl (fun i hi => congrArg v (heq i hi))
  simp only [selectedNumerator, selectedDenominator]
  rw [hs (fun z => bit z.2.1 * bit z.2.2), hs (fun z => bit z.2.1),
    hs (fun z => bit z.2.2)]
  exact ⟨rfl, rfl⟩

/-- Erasing one selected record has joint sensitivity at most six; erasing an absent record has
zero effect.  [the theorem's stated inputs and assumptions](hyp:r), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,I,D). -/
-- @node: selected_erasure_bound
lemma selected_erasure_bound {n : ℕ} (I : Finset (Fin n)) (D : Dataset n)
    (r : Fin n) :
    |selectedNumerator I D - selectedNumerator (I.erase r) D| +
      |selectedDenominator I D - selectedDenominator (I.erase r) D| ≤
        if r ∈ I then 6 else 0 := by
  classical
  by_cases hr : r ∈ I
  · rw [if_pos hr]
    have hb := selected_insertion_bound (I.erase r) D r (Finset.notMem_erase r I)
    rwa [Finset.insert_erase hr] at hb
  · simp [hr]

open Classical in
/-- A replacement changes only its old and new cells, using their common erased selection.  [the theorem's stated inputs and assumptions](hyp:heq,j), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k,D,D',r). -/
-- @node: cell_replacement_bound
lemma cell_replacement_bound (n k : ℕ) (h : ℝ) (D D' : Dataset n) (r : Fin n)
    (heq : ∀ i, i ≠ r → D i = D' i) (j : Fin k) :
    |numeratorCell n h k D j - numeratorCell n h k D' j| +
      |denominatorCell n h k D j - denominatorCell n h k D' j| ≤
        (if (D r).1 ∈ cell h k j then 6 else 0) +
        (if (D' r).1 ∈ cell h k j then 6 else 0) := by
  classical
  let I := cellRecords n h k D j
  let I' := cellRecords n h k D' j
  have hbase : I.erase r = I'.erase r := by
    ext i
    by_cases hi : i = r
    · subst i; simp
    · simp [I, I', cellRecords, hi, heq i hi]
  have hcommon : ∀ i ∈ I.erase r, D i = D' i := by
    intro i hi
    exact heq i (Finset.mem_erase.mp hi).1
  obtain ⟨hcN, hcD⟩ := selected_congr (I.erase r) D D' hcommon
  rw [hbase] at hcN hcD
  have hb := selected_erasure_bound I D r
  have hb' := selected_erasure_bound I' D' r
  rw [← hcN, ← hcD, ← hbase] at hb'
  have hN := abs_sub_le (selectedNumerator I D)
    (selectedNumerator (I.erase r) D) (selectedNumerator I' D')
  have hD := abs_sub_le (selectedDenominator I D)
    (selectedDenominator (I.erase r) D) (selectedDenominator I' D')
  rw [abs_sub_comm (selectedNumerator (I.erase r) D)] at hN
  rw [abs_sub_comm (selectedDenominator (I.erase r) D)] at hD
  change |selectedNumerator I D - selectedNumerator I' D'| +
    |selectedDenominator I D - selectedDenominator I' D'| ≤ _
  have hmem : (r ∈ I) ↔ (D r).1 ∈ cell h k j := by simp [I, cellRecords]
  have hmem' : (r ∈ I') ↔ (D' r).1 ∈ cell h k j := by simp [I', cellRecords]
  simp only [hmem] at hb
  simp only [hmem'] at hb'
  linarith

open Classical in
/-- A covariate belongs to at most one public cell, so its summed insertion envelope is at most
six.  [the theorem's stated inputs and assumptions](hyp:x), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:k,h,hh,hk). -/
-- @node: cell_membership_sum
lemma cell_membership_sum (k : ℕ) (h : ℝ) (hh : 0 < h) (hk : 0 < k)
    (x : Covariate) :
    (∑ j : Fin k, if x ∈ cell h k j then (6 : ℝ) else 0) ≤ 6 := by
  classical
  by_cases hx : ∃ j : Fin k, x ∈ cell h k j
  · obtain ⟨j, hj⟩ := hx
    rw [Finset.sum_eq_single j]
    · simp [hj]
    · intro i hi hij
      have hnot : x ∉ cell h k i := by
        intro hx
        exact Set.disjoint_left.mp (cell_disjoint k h hh hk i j hij) hx hj
      simp [hnot]
    · simp
  · have hn : ∀ j : Fin k, x ∉ cell h k j := by simpa using hx
    simp [hn]

/-- Deletion followed by insertion bounds the joint statistic change by twelve, including
replacements between different cells.  [the theorem's stated inputs and assumptions](hyp:D,D',r,heq), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k,h,hh,hk). -/
-- @node: statistic_replacement_bound
lemma statistic_replacement_bound (n k : ℕ) (h : ℝ) (hh : 0 < h) (hk : 0 < k)
    (D D' : Dataset n) (r : Fin n) (heq : ∀ i, i ≠ r → D i = D' i) :
    |SN n h k D - SN n h k D'| + |SD n h k D - SD n h k D'| ≤ 12 := by
  have hb := Finset.sum_le_sum (s := Finset.univ)
    (fun j _ => cell_replacement_bound n k h D D' r heq j)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hb
  have hN : |SN n h k D - SN n h k D'| ≤
      ∑ j : Fin k, |numeratorCell n h k D j - numeratorCell n h k D' j| := by
    rw [SN, SN, ← Finset.sum_sub_distrib]
    exact Finset.abs_sum_le_sum_abs _ _
  have hD : |SD n h k D - SD n h k D'| ≤
      ∑ j : Fin k, |denominatorCell n h k D j - denominatorCell n h k D' j| := by
    rw [SD, SD, ← Finset.sum_sub_distrib]
    exact Finset.abs_sum_le_sum_abs _ _
  have ho := cell_membership_sum k h hh hk (D r).1
  have hn := cell_membership_sum k h hh hk (D' r).1
  linarith


/-- Hamming-distance-one datasets satisfy the asserted joint sensitivity bound on the entire input
space.  [the theorem's stated inputs and assumptions](hyp:D,D',hadj), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k,h,hh,hk). -/
-- @node: statistic_hamming_sensitivity
lemma statistic_hamming_sensitivity (n k : ℕ) (h : ℝ) (hh : 0 < h) (hk : 0 < k)
    (D D' : Dataset n) (hadj : dHam n D D' = 1) :
    |SN n h k D - SN n h k D'| + |SD n h k D - SD n h k D'| ≤ 12 := by
  classical
  unfold dHam hammingDist at hadj
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hadj
  apply statistic_replacement_bound n k h hh hk D D' r
  intro i hi
  by_contra hne
  have hmem : i ∈ (Finset.univ.filter (fun i => D i ≠ D' i)) := by simp [hne]
  rw [hr] at hmem
  exact hi (Finset.mem_singleton.mp hmem)

end CausalSmith.Stat.PrivateCateRoughdesign
