module
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.PartnerProbability
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.PointVersion
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.Stability
/-! Partner-sensitive replacement increments and the occupancy-weighted Efron--Stein assembly. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
namespace CausalSmith.Stat.PrivateCateRoughdesign

/-- Inserting one record into an arbitrary selected set changes each scalar causal contribution by
at most three, at every count.  [the theorem's stated inputs and assumptions](hyp:r,hr), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,I,D). -/
-- @node: selected_scalar_insertion_bound
lemma selected_scalar_insertion_bound {n : ℕ} (I : Finset (Fin n)) (D : Dataset n)
    (r : Fin n) (hr : r ∉ I) :
    |selectedNumerator (insert r I) D - selectedNumerator I D| ≤ 3 ∧
      |selectedDenominator (insert r I) D - selectedDenominator I D| ≤ 3 := by
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
  have hbN := pairContribution_insertion_bound I.card KN z
    (fun x y => (causal_pair_kernel_unit_bounds x y).1)
  have hbD := pairContribution_insertion_bound I.card KD z
    (fun x y => (causal_pair_kernel_unit_bounds x y).2)
  simp_rw [hz] at hbN hbD
  rw [hNi, hNo] at hbN
  rw [hDi, hDo] at hbD
  exact ⟨hbN, hbD⟩

/-- Without a remaining selected record, both scalar contributions before and after insertion
are zero. With a partner, the scalar insertion bound is three.  [the theorem's stated inputs and assumptions](hyp:r), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,I,D). -/
-- @node: selected_partner_erasure_bound
lemma selected_partner_erasure_bound {n : ℕ} (I : Finset (Fin n)) (D : Dataset n)
    (r : Fin n) :
    |selectedNumerator I D - selectedNumerator (I.erase r) D| ≤
      (if r ∈ I ∧ (I.erase r).Nonempty then 3 else 0) ∧
    |selectedDenominator I D - selectedDenominator (I.erase r) D| ≤
      (if r ∈ I ∧ (I.erase r).Nonempty then 3 else 0) := by
  classical
  by_cases hr : r ∈ I
  · by_cases hp : (I.erase r).Nonempty
    · simp only [hr, hp, and_self, if_true]
      have hb := selected_scalar_insertion_bound (I.erase r) D r (Finset.notMem_erase r I)
      rwa [Finset.insert_erase hr] at hb
    · have he : I.erase r = ∅ := Finset.not_nonempty_iff_eq_empty.mp hp
      have hI : I = {r} := by
        have hi := Finset.insert_erase hr
        rw [he] at hi
        simpa using hi.symm
      simp [hI, selectedNumerator, selectedDenominator]
  · simp [hr]

open Classical in
/-- The partner indicator records whether a proposed record shares a public cell with any
record other than the replaced index. -/
-- @node: partnerIndicator
def partnerIndicator (n k : ℕ) (h : ℝ) (D : Dataset n) (r : Fin n) (z : O) : ℝ :=
  if ∃ j : Fin k, z.1 ∈ cell h k j ∧ (cellRecords n h k D j |>.erase r).Nonempty
  then 1 else 0

/-- Partner indicators take only the values zero and one.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k,h,D,r,z). -/
-- @node: partnerIndicator_values
lemma partnerIndicator_values (n k : ℕ) (h : ℝ) (D : Dataset n) (r : Fin n) (z : O) :
    partnerIndicator n k h D r z = 0 ∨ partnerIndicator n k h D r z = 1 := by
  classical
  unfold partnerIndicator
  split_ifs <;> simp

/-- The two datasets in a replacement have identical cell selections after erasing its index.  [the theorem's stated inputs and assumptions](hyp:heq,j), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k,D,D',r). -/
-- @node: erased_cellRecords_congr
lemma erased_cellRecords_congr (n k : ℕ) (h : ℝ) (D D' : Dataset n) (r : Fin n)
    (heq : ∀ i, i ≠ r → D i = D' i) (j : Fin k) :
    (cellRecords n h k D j).erase r = (cellRecords n h k D' j).erase r := by
  classical
  ext i
  by_cases hi : i = r
  · subst i; simp
  · simp [cellRecords, hi, heq i hi]

open Classical in
/-- A scalar cell replacement is bounded by the old and new partner indicators in that cell.  [the theorem's stated inputs and assumptions](hyp:heq,j), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k,D,D',r). -/
-- @node: cell_partner_replacement_bound
lemma cell_partner_replacement_bound (n k : ℕ) (h : ℝ) (D D' : Dataset n) (r : Fin n)
    (heq : ∀ i, i ≠ r → D i = D' i) (j : Fin k) :
    let B := (cellRecords n h k D j).erase r
    let old := if (D r).1 ∈ cell h k j ∧ B.Nonempty then (3 : ℝ) else 0
    let new := if (D' r).1 ∈ cell h k j ∧ B.Nonempty then (3 : ℝ) else 0
    |numeratorCell n h k D j - numeratorCell n h k D' j| ≤ old + new ∧
    |denominatorCell n h k D j - denominatorCell n h k D' j| ≤ old + new := by
  classical
  dsimp only
  let I := cellRecords n h k D j
  let I' := cellRecords n h k D' j
  have hbase : I.erase r = I'.erase r := erased_cellRecords_congr n k h D D' r heq j
  have hcommon : ∀ i ∈ I.erase r, D i = D' i := by
    intro i hi
    exact heq i (Finset.mem_erase.mp hi).1
  obtain ⟨hcN, hcD⟩ := selected_congr (I.erase r) D D' hcommon
  rw [hbase] at hcN hcD
  obtain ⟨hbN, hbD⟩ := selected_partner_erasure_bound I D r
  obtain ⟨hbN', hbD'⟩ := selected_partner_erasure_bound I' D' r
  rw [← hcN, ← hbase] at hbN'
  rw [← hcD, ← hbase] at hbD'
  have hN := abs_sub_le (selectedNumerator I D)
    (selectedNumerator (I.erase r) D) (selectedNumerator I' D')
  have hD := abs_sub_le (selectedDenominator I D)
    (selectedDenominator (I.erase r) D) (selectedDenominator I' D')
  rw [abs_sub_comm (selectedNumerator (I.erase r) D)] at hN
  rw [abs_sub_comm (selectedDenominator (I.erase r) D)] at hD
  have hmem : (r ∈ I) ↔ (D r).1 ∈ cell h k j := by simp [I, cellRecords]
  have hmem' : (r ∈ I') ↔ (D' r).1 ∈ cell h k j := by simp [I', cellRecords]
  simp only [hmem] at hbN hbD
  simp only [hmem'] at hbN' hbD'
  change |selectedNumerator I D - selectedNumerator I' D'| ≤ _ ∧
    |selectedDenominator I D - selectedDenominator I' D'| ≤ _
  constructor <;> linarith

open Classical in
/-- Disjointness reduces the sum of cellwise partner envelopes to the single partner indicator.  [the theorem's stated inputs and assumptions](hyp:D,r,z), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k,h,hh,hk). -/
-- @node: cell_partner_sum
lemma cell_partner_sum (n k : ℕ) (h : ℝ) (hh : 0 < h) (hk : 0 < k)
    (D : Dataset n) (r : Fin n) (z : O) :
    (∑ j : Fin k, if z.1 ∈ cell h k j ∧
      ((cellRecords n h k D j).erase r).Nonempty then (3 : ℝ) else 0) =
        3 * partnerIndicator n k h D r z := by
  classical
  unfold partnerIndicator
  by_cases hx : ∃ j : Fin k, z.1 ∈ cell h k j ∧
      ((cellRecords n h k D j).erase r).Nonempty
  · rw [if_pos hx]
    obtain ⟨j, hj⟩ := hx
    rw [Finset.sum_eq_single j]
    · simp [hj]
    · intro i hi hij
      have hnot : z.1 ∉ cell h k i := by
        intro hz
        exact Set.disjoint_left.mp (cell_disjoint k h hh hk i j hij) hz hj.1
      simp [hnot]
    · simp
  · rw [if_neg hx]
    have hn : ∀ j : Fin k, ¬(z.1 ∈ cell h k j ∧
        ((cellRecords n h k D j).erase r).Nonempty) := by simpa using hx
    simp [hn]

/-- Each scalar replacement increment vanishes without partners and is at most three times
the sum of its old and new partner indicators.  [the theorem's stated inputs and assumptions](hyp:D,D',r,heq), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k,h,hh,hk). -/
-- @node: statistic_partner_replacement_bound
lemma statistic_partner_replacement_bound (n k : ℕ) (h : ℝ) (hh : 0 < h) (hk : 0 < k)
    (D D' : Dataset n) (r : Fin n) (heq : ∀ i, i ≠ r → D i = D' i) :
    let J := partnerIndicator n k h D r (D r)
    let J' := partnerIndicator n k h D r (D' r)
    |SN n h k D - SN n h k D'| ≤ 3 * (J + J') ∧
    |SD n h k D - SD n h k D'| ≤ 3 * (J + J') := by
  classical
  dsimp only
  have hbN := Finset.sum_le_sum (s := Finset.univ)
    (fun j _ => (cell_partner_replacement_bound n k h D D' r heq j).1)
  have hbD := Finset.sum_le_sum (s := Finset.univ)
    (fun j _ => (cell_partner_replacement_bound n k h D D' r heq j).2)
  simp only [Finset.sum_add_distrib, cell_partner_sum n k h hh hk D r] at hbN hbD
  have hN : |SN n h k D - SN n h k D'| ≤
      ∑ j : Fin k, |numeratorCell n h k D j - numeratorCell n h k D' j| := by
    rw [SN, SN, ← Finset.sum_sub_distrib]
    exact Finset.abs_sum_le_sum_abs _ _
  have hD : |SD n h k D - SD n h k D'| ≤
      ∑ j : Fin k, |denominatorCell n h k D j - denominatorCell n h k D' j| := by
    rw [SD, SD, ← Finset.sum_sub_distrib]
    exact Finset.abs_sum_le_sum_abs _ _
  constructor <;> linarith

/-- Squared scalar replacement increments are bounded by eighteen times the two partner
indicators, exactly the deterministic envelope in the variance roadmap.  [the theorem's stated inputs and assumptions](hyp:D,r,z), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k,h,hh,hk). -/
-- @node: statistic_partner_square_bound
lemma statistic_partner_square_bound (n k : ℕ) (h : ℝ) (hh : 0 < h) (hk : 0 < k)
    (D : Dataset n) (r : Fin n) (z : O) :
    let J := partnerIndicator n k h D r (D r)
    let J' := partnerIndicator n k h D r z
    (SN n h k D - SN n h k (Function.update D r z))^2 ≤ 18 * (J + J') ∧
    (SD n h k D - SD n h k (Function.update D r z))^2 ≤ 18 * (J + J') := by
  have hb := statistic_partner_replacement_bound n k h hh hk D
    (Function.update D r z) r (fun i hi => (Function.update_of_ne hi z D).symm)
  simp only [Function.update_self] at hb
  exact ⟨replacement_square_indicator_bound _ _ _
      (partnerIndicator_values n k h D r (D r)) (partnerIndicator_values n k h D r z) hb.1,
    replacement_square_indicator_bound _ _ _
      (partnerIndicator_values n k h D r (D r)) (partnerIndicator_values n k h D r z) hb.2⟩

/-- Partner indicators are Borel functions of the dataset and proposed record. [The displayed conclusion](goal) follows. -/
-- @node: measurable_partnerIndicator
@[fun_prop] lemma measurable_partnerIndicator (n k : ℕ) (h : ℝ) (r : Fin n) :
    Measurable (fun zz : Dataset n × O => partnerIndicator n k h zz.1 r zz.2) := by
  classical
  unfold partnerIndicator
  simp only [Finset.Nonempty, Finset.mem_erase, cellRecords, Finset.mem_filter,
    Finset.mem_univ, true_and]
  refine measurable_const.ite ?_ measurable_const
  simp only [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro j
  apply MeasurableSet.inter
  · exact (measurableSet_cell h k j).preimage (by fun_prop)
  · change MeasurableSet {zz : Dataset n × O | ∃ i : Fin n,
        i ≠ r ∧ (zz.1 i).1 ∈ cell h k j}
    rw [Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro i
    by_cases hi : i = r
    · simp [hi]
    · simp only [ne_eq, hi, not_false_eq_true, true_and]
      exact (measurableSet_cell h k j).preimage (by fun_prop)

/-- Partner indicators are bounded by one and integrable under every finite measure. [The displayed conclusion](goal) follows. -/
-- @node: partnerIndicator_integrable
@[fun_prop] lemma partnerIndicator_integrable (n k : ℕ) (h : ℝ) (r : Fin n)
    (Q : Measure (Dataset n × O)) [IsFiniteMeasure Q] :
    Integrable (fun zz => partnerIndicator n k h zz.1 r zz.2) Q := by
  apply Integrable.of_bound (by fun_prop) 1
  apply ae_of_all
  intro zz
  rcases partnerIndicator_values n k h zz.1 r zz.2 with hz | hz <;> simp [hz]

/-- The squared replacement differences of the bounded statistics are integrable under every
finite measure on dataset and replacement pairs.  [the theorem's stated inputs and assumptions](hyp:hh,hk,r,Q), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k). -/
-- @node: statistic_replacement_square_integrable
lemma statistic_replacement_square_integrable (n k : ℕ) (h : ℝ)
    (hh : 0 < h) (hk : 0 < k) (r : Fin n) (Q : Measure (Dataset n × O))
    [IsFiniteMeasure Q] :
    Integrable (fun zz => (SN n h k zz.1 - SN n h k (Function.update zz.1 r zz.2))^2) Q ∧
    Integrable (fun zz => (SD n h k zz.1 - SD n h k (Function.update zz.1 r zz.2))^2) Q := by
  have hb (zz : Dataset n × O) :
      (SN n h k zz.1 - SN n h k (Function.update zz.1 r zz.2))^2 ≤ 36 ∧
      (SD n h k zz.1 - SD n h k (Function.update zz.1 r zz.2))^2 ≤ 36 := by
    obtain ⟨hN, hD⟩ := statistic_partner_square_bound n k h hh hk zz.1 r zz.2
    have hv := partnerIndicator_values n k h zz.1 r (zz.1 r)
    have hv' := partnerIndicator_values n k h zz.1 r zz.2
    rcases hv with hv | hv <;> rcases hv' with hv' | hv' <;>
      simp only [hv, hv'] at hN hD <;> constructor <;> linarith
  constructor
  · apply Integrable.of_bound (by fun_prop) 36
    exact ae_of_all _ (fun zz => by simpa only [Real.norm_eq_abs, abs_sq]
      using (hb zz).1)
  · apply Integrable.of_bound (by fun_prop) 36
    exact ae_of_all _ (fun zz => by simpa only [Real.norm_eq_abs, abs_sq]
      using (hb zz).2)

open Classical in
/-- Disjoint public cells express the partner indicator as a sum of cell event indicators.  [the theorem's stated inputs and assumptions](hyp:D,r,z), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k,h,hh,hk). -/
-- @node: partnerIndicator_eq_sum
lemma partnerIndicator_eq_sum (n k : ℕ) (h : ℝ) (hh : 0 < h) (hk : 0 < k)
    (D : Dataset n) (r : Fin n) (z : O) :
    partnerIndicator n k h D r z = ∑ j : Fin k,
      (if z.1 ∈ cell h k j ∧ ∃ i, i ≠ r ∧ (D i).1 ∈ cell h k j then 1 else 0) := by
  classical
  have he (j : Fin k) : ((cellRecords n h k D j).erase r).Nonempty ↔
      ∃ i, i ≠ r ∧ (D i).1 ∈ cell h k j := by
    simp [Finset.Nonempty, cellRecords]
  have hs := cell_partner_sum n k h hh hk D r z
  simp only [he] at hs
  have ht : (∑ j : Fin k, if z.1 ∈ cell h k j ∧
      ∃ i, i ≠ r ∧ (D i).1 ∈ cell h k j then (3 : ℝ) else 0) =
      3 * ∑ j : Fin k, if z.1 ∈ cell h k j ∧
      ∃ i, i ≠ r ∧ (D i).1 ∈ cell h k j then (1 : ℝ) else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> norm_num
  rw [ht] at hs
  linarith

/-- Existence of an unreplaced record in an event is measurable.  [the theorem's stated inputs and assumptions](hyp:hs), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,r,s). -/
-- @node: measurableSet_has_partner
lemma measurableSet_has_partner (n : ℕ) (r : Fin n) (s : Set O)
    (hs : MeasurableSet s) :
    MeasurableSet {D : Dataset n | ∃ i, i ≠ r ∧ D i ∈ s} := by
  have he : {D : Dataset n | ∃ i, i ≠ r ∧ D i ∈ s} =
      {D : Dataset n | ∀ i, i ≠ r → D i ∉ s}ᶜ := by
    ext D
    simp [not_forall, _root_.not_imp]
  rw [he]
  exact (measurableSet_no_partner n r s hs).compl

open Classical in
/-- Old and independent-copy cell partner indicators both have the Bernoulli occupancy mean.  [the theorem's stated inputs and assumptions](hyp:r,j), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k,h,P). -/
-- @node: integral_cell_partner_indicators
lemma integral_cell_partner_indicators (n k : ℕ) (h : ℝ) (P : CausalLaw)
    (r : Fin n) (j : Fin k) :
    let Q := (dataLaw n P).prod (Pobs P)
    let p := cellMass h k P j
    (∫ zz : Dataset n × O, if (zz.1 r).1 ∈ cell h k j ∧
      ∃ i, i ≠ r ∧ (zz.1 i).1 ∈ cell h k j then (1 : ℝ) else 0 ∂Q) =
        p * (1 - (1 - p)^(n - 1)) ∧
    (∫ zz : Dataset n × O, if zz.2.1 ∈ cell h k j ∧
      ∃ i, i ≠ r ∧ (zz.1 i).1 ∈ cell h k j then (1 : ℝ) else 0 ∂Q) =
        p * (1 - (1 - p)^(n - 1)) := by
  classical
  let : IsProbabilityMeasure (Pobs P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (dataLaw n P) := by unfold dataLaw; infer_instance
  dsimp only
  let s : Set O := {z | z.1 ∈ cell h k j}
  have hs : MeasurableSet s := (measurableSet_cell h k j).preimage measurable_fst
  have hp := measurableSet_has_partner n r s hs
  have hor : MeasurableSet {D : Dataset n | D r ∈ s} :=
    hs.preimage (measurable_pi_apply r)
  have ho : MeasurableSet {zz : Dataset n × O | (zz.1 r) ∈ s ∧
      ∃ i, i ≠ r ∧ zz.1 i ∈ s} :=
    (hor.inter hp).preimage measurable_fst
  have hn : MeasurableSet {zz : Dataset n × O | zz.2 ∈ s ∧
      ∃ i, i ≠ r ∧ zz.1 i ∈ s} :=
    (hs.preimage measurable_snd).inter (hp.preimage measurable_fst)
  have he : {zz : Dataset n × O | (zz.1 r) ∈ s ∧ ∃ i, i ≠ r ∧ zz.1 i ∈ s} =
      {D : Dataset n | D r ∈ s ∧ ∃ i, i ≠ r ∧ D i ∈ s} ×ˢ Set.univ := by
    ext zz; simp
  constructor
  · have ht := integral_indicator_one (μ := (dataLaw n P).prod (Pobs P)) ho
    simp only [Set.indicator, Set.mem_setOf_eq, Pi.one_apply, s] at ht
    simp only [s, Set.mem_setOf_eq] at he
    rw [ht, he, measureReal_prod_prod, probReal_univ, mul_one]
    simpa only [s, Set.mem_setOf_eq, observed_cell_mass] using iid_old_partner_probability n P r s hs
  · have ht := integral_indicator_one (μ := (dataLaw n P).prod (Pobs P)) hn
    simp only [Set.indicator, Set.mem_setOf_eq, Pi.one_apply, s] at ht
    rw [ht]
    simpa only [s, Set.mem_setOf_eq, observed_cell_mass] using iid_new_partner_probability n P r s hs

/-- The old-record partner indicator is Borel on the dataset and independent-copy space. [The displayed conclusion](goal) follows. -/
-- @node: measurable_oldPartnerIndicator
@[fun_prop] lemma measurable_oldPartnerIndicator (n k : ℕ) (h : ℝ) (r : Fin n) :
    Measurable (fun zz : Dataset n × O => partnerIndicator n k h zz.1 r (zz.1 r)) := by
  fun_prop

/-- The old-record partner indicator is integrable under any finite pair measure. [The displayed conclusion](goal) follows. -/
-- @node: oldPartnerIndicator_integrable
@[fun_prop] lemma oldPartnerIndicator_integrable (n k : ℕ) (h : ℝ) (r : Fin n)
    (Q : Measure (Dataset n × O)) [IsFiniteMeasure Q] :
    Integrable (fun zz => partnerIndicator n k h zz.1 r (zz.1 r)) Q := by
  apply Integrable.of_bound (measurable_oldPartnerIndicator n k h r |>.aestronglyMeasurable) 1
  exact ae_of_all _ (fun zz => by
    rcases partnerIndicator_values n k h zz.1 r (zz.1 r) with hz | hz <;> simp [hz])

open Classical in
/-- Cellwise partner indicators are integrable for any finite pair measure.  [the theorem's stated inputs and assumptions](hyp:Q), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k,h,r,j). -/
-- @node: integrable_cell_partner_indicators
lemma integrable_cell_partner_indicators (n k : ℕ) (h : ℝ) (r : Fin n) (j : Fin k)
    (Q : Measure (Dataset n × O)) [IsFiniteMeasure Q] :
    Integrable (fun zz : Dataset n × O => if (zz.1 r).1 ∈ cell h k j ∧
      ∃ i, i ≠ r ∧ (zz.1 i).1 ∈ cell h k j then (1 : ℝ) else 0) Q ∧
    Integrable (fun zz : Dataset n × O => if zz.2.1 ∈ cell h k j ∧
      ∃ i, i ≠ r ∧ (zz.1 i).1 ∈ cell h k j then (1 : ℝ) else 0) Q := by
  let s : Set O := {z | z.1 ∈ cell h k j}
  have hs : MeasurableSet s := (measurableSet_cell h k j).preimage measurable_fst
  have hp := measurableSet_has_partner n r s hs
  have hor : MeasurableSet {D : Dataset n | D r ∈ s} :=
    hs.preimage (measurable_pi_apply r)
  have ho : MeasurableSet {zz : Dataset n × O | (zz.1 r) ∈ s ∧
      ∃ i, i ≠ r ∧ zz.1 i ∈ s} := (hor.inter hp).preimage measurable_fst
  have hn : MeasurableSet {zz : Dataset n × O | zz.2 ∈ s ∧
      ∃ i, i ≠ r ∧ zz.1 i ∈ s} :=
    (hs.preimage measurable_snd).inter (hp.preimage measurable_fst)
  constructor
  · apply Integrable.of_bound (measurable_const.ite ho measurable_const).aestronglyMeasurable 1
    exact ae_of_all _ (fun zz => by split_ifs <;> norm_num)
  · apply Integrable.of_bound (measurable_const.ite hn measurable_const).aestronglyMeasurable 1
    exact ae_of_all _ (fun zz => by split_ifs <;> norm_num)

/-- Each of the two partner indicators has mean W/n under the iid law and its independent copy.  [the theorem's stated inputs and assumptions](hyp:hh,hk,P,r), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k,hn). -/
-- @node: iid_partner_expectations
lemma iid_partner_expectations (n k : ℕ) (h : ℝ) (hn : 0 < n)
    (hh : 0 < h) (hk : 0 < k) (P : CausalLaw) (r : Fin n) :
    (∫ zz : Dataset n × O, partnerIndicator n k h zz.1 r (zz.1 r)
      ∂((dataLaw n P).prod (Pobs P))) = Wocc n h k P / n ∧
    (∫ zz : Dataset n × O, partnerIndicator n k h zz.1 r zz.2
      ∂((dataLaw n P).prod (Pobs P))) = Wocc n h k P / n := by
  classical
  let : IsProbabilityMeasure (Pobs P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (dataLaw n P) := by unfold dataLaw; infer_instance
  have hw : (∑ j : Fin k, cellMass h k P j *
      (1 - (1 - cellMass h k P j)^(n - 1))) = Wocc n h k P / n := by
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    unfold Wocc occupancyWeight
    simp only [mul_assoc, ← Finset.mul_sum]
    field_simp
  constructor
  · simp_rw [partnerIndicator_eq_sum n k h hh hk]
    rw [integral_finset_sum _ (fun j _ =>
      (integrable_cell_partner_indicators n k h r j _).1)]
    calc
      _ = ∑ j : Fin k, cellMass h k P j *
          (1 - (1 - cellMass h k P j)^(n - 1)) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact (integral_cell_partner_indicators n k h P r j).1
      _ = _ := hw
  · simp_rw [partnerIndicator_eq_sum n k h hh hk]
    rw [integral_finset_sum _ (fun j _ =>
      (integrable_cell_partner_indicators n k h r j _).2)]
    calc
      _ = ∑ j : Fin k, cellMass h k P j *
          (1 - (1 - cellMass h k P j)^(n - 1)) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact (integral_cell_partner_indicators n k h P r j).2
      _ = _ := hw

/-- The old-plus-new partner expectation is exactly twice W/n.  [the theorem's stated inputs and assumptions](hyp:hh,hk,P,r), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k,hn). -/
-- @node: iid_partner_sum_expectation
lemma iid_partner_sum_expectation (n k : ℕ) (h : ℝ) (hn : 0 < n)
    (hh : 0 < h) (hk : 0 < k) (P : CausalLaw) (r : Fin n) :
    (∫ zz : Dataset n × O,
      (partnerIndicator n k h zz.1 r (zz.1 r) + partnerIndicator n k h zz.1 r zz.2)
      ∂((dataLaw n P).prod (Pobs P))) = 2 * Wocc n h k P / n := by
  let : IsProbabilityMeasure (Pobs P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (dataLaw n P) := by unfold dataLaw; infer_instance
  obtain ⟨ho, hn'⟩ := iid_partner_expectations n k h hn hh hk P r
  rw [integral_add (oldPartnerIndicator_integrable n k h r _)
    (partnerIndicator_integrable n k h r _), ho, hn']
  ring

/-- Integrating the deterministic squared replacement bound reduces both second moments to
the common old-plus-new partner expectation. The result uses [the stated assumptions](hyp:hh,hk,hpartners) and establishes [the displayed conclusion](goal). -/
-- @node: statistic_replacement_moments_of_partners
lemma statistic_replacement_moments_of_partners (n k : ℕ) (h : ℝ)
    (hh : 0 < h) (hk : 0 < k) (P : CausalLaw) (r : Fin n)
    (hpartners : (∫ zz : Dataset n × O,
      (partnerIndicator n k h zz.1 r (zz.1 r) + partnerIndicator n k h zz.1 r zz.2)
      ∂((dataLaw n P).prod (Pobs P))) = 2 * Wocc n h k P / n) :
    (∫ zz, (SN n h k zz.1 - SN n h k (Function.update zz.1 r zz.2))^2
      ∂((dataLaw n P).prod (Pobs P))) ≤ 36 * Wocc n h k P / n ∧
    (∫ zz, (SD n h k zz.1 - SD n h k (Function.update zz.1 r zz.2))^2
      ∂((dataLaw n P).prod (Pobs P))) ≤ 36 * Wocc n h k P / n := by
  let : IsProbabilityMeasure (Pobs P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (dataLaw n P) := by unfold dataLaw; infer_instance
  obtain ⟨hiN, hiD⟩ := statistic_replacement_square_integrable n k h hh hk r
    ((dataLaw n P).prod (Pobs P))
  have hi : Integrable (fun zz : Dataset n × O =>
      18 * (partnerIndicator n k h zz.1 r (zz.1 r) + partnerIndicator n k h zz.1 r zz.2))
      ((dataLaw n P).prod (Pobs P)) := by fun_prop
  have he : (∫ zz : Dataset n × O,
      18 * (partnerIndicator n k h zz.1 r (zz.1 r) + partnerIndicator n k h zz.1 r zz.2)
      ∂((dataLaw n P).prod (Pobs P))) = 36 * Wocc n h k P / n := by
    rw [integral_const_mul, hpartners]
    ring
  constructor
  · calc
      _ ≤ _ := integral_mono hiN hi
        (fun zz => (statistic_partner_square_bound n k h hh hk zz.1 r zz.2).1)
      _ = _ := he
  · calc
      _ ≤ _ := integral_mono hiD hi
        (fun zz => (statistic_partner_square_bound n k h hh hk zz.1 r zz.2).2)
      _ = _ := he

/-- Efron--Stein converts the two occupancy-weighted replacement second-moment estimates into
the asserted variance bound.  [the theorem's stated inputs and assumptions](hyp:n,k,h,hn,hk,hh,P,hstep), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:efronStein_of_gate). -/
-- @node: statistic_efronStein_assembly
lemma statistic_efronStein_assembly (efronStein_of_gate : EfronSteinReplacement)
    (n k : ℕ) (h : ℝ) (hn : 0 < n) (hk : 0 < k) (hh : 0 < h) (P : CausalLaw)
    (hstep : ∀ r : Fin n,
      (∫ zz, (SN n h k zz.1 - SN n h k (Function.update zz.1 r zz.2))^2
        ∂((dataLaw n P).prod (Pobs P))) ≤ 36 * Wocc n h k P / n ∧
      (∫ zz, (SD n h k zz.1 - SD n h k (Function.update zz.1 r zz.2))^2
        ∂((dataLaw n P).prod (Pobs P))) ≤ 36 * Wocc n h k P / n) :
    max (variance (SN n h k) (dataLaw n P))
      (variance (SD n h k) (dataLaw n P)) ≤ 18 * Wocc n h k P := by
  let : IsProbabilityMeasure (Pobs P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (dataLaw n P) := by unfold dataLaw; infer_instance
  have hLp := statistic_memLp n k h hh hk (dataLaw n P) 2
  have hN := efronStein_of_gate n (fun _ => O) (fun _ => inferInstance)
    (fun _ => Pobs P) (fun _ => inferInstance) (SN n h k) (by fun_prop) hLp.1
  have hD := efronStein_of_gate n (fun _ => O) (fun _ => inferInstance)
    (fun _ => Pobs P) (fun _ => inferInstance) (SD n h k) (by fun_prop) hLp.2
  have hsN := Finset.sum_le_sum (s := Finset.univ) (fun r _ => (hstep r).1)
  have hsD := Finset.sum_le_sum (s := Finset.univ) (fun r _ => (hstep r).2)
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have heq : (∑ _ : Fin n, 36 * Wocc n h k P / (n : ℝ)) = 36 * Wocc n h k P := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  rw [heq] at hsN hsD
  dsimp only [dataLaw] at hsN hsD
  apply max_le
  · exact hN.trans (by linarith)
  · exact hD.trans (by linarith)

/-- Sensitivity includes every input and every occupancy; iid variance on the complete model is
controlled by the population occupancy weight. The replacement-copy inequality is an explicit
assumed gate.  [the theorem's stated inputs and assumptions](hyp:n,k,h,hn,hk,hh,P,Q,hiid,hP), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:efronStein_of_gate). -/
-- @node: lem:all-count-stability
lemma all_count_stability (efronStein_of_gate : EfronSteinReplacement)
    (n k : ℕ) (h : ℝ) (hn : 2 ≤ n) (hk : 2 ≤ k) (hh : 0 < h ∧ h ≤ 1 / 4)
    (P : CausalLaw) (Q : Measure (Dataset n)) (hiid : IIDSampling n P Q)
    (hP : CompleteModel P) :
    (∀ D Dprime : Dataset n, dHam n D Dprime = 1 →
      |SN n h k D - SN n h k Dprime| + |SD n h k D - SD n h k Dprime| ≤ 12) ∧
    max (variance (SN n h k) Q) (variance (SD n h k) Q) ≤ 18*Wocc n h k P := by
  constructor
  · intro D Dprime hadj
    exact statistic_hamming_sensitivity n k h hh.1 (by omega) D Dprime hadj
  · -- The iid product calculation gives both old and new partner expectations.
    have hpartners : ∀ r : Fin n, (∫ zz : Dataset n × O,
        (partnerIndicator n k h zz.1 r (zz.1 r) + partnerIndicator n k h zz.1 r zz.2)
        ∂((dataLaw n P).prod (Pobs P))) = 2 * Wocc n h k P / n := by
      intro r
      exact iid_partner_sum_expectation n k h (by omega) hh.1 (by omega) P r
    have hvariance := statistic_efronStein_assembly efronStein_of_gate n k h
      (by omega) (by omega) hh.1 P
      (fun r => statistic_replacement_moments_of_partners n k h hh.1 (by omega) P r
        (hpartners r))
    rw [show Q = dataLaw n P from hiid]
    exact hvariance
end CausalSmith.Stat.PrivateCateRoughdesign
