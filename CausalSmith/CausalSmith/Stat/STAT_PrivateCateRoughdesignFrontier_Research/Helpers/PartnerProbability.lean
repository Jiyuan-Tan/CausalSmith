module
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.Construction
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.PointVersion
/-! Product-law probabilities of a record having another record in a specified cell. -/
public section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace CausalSmith.Stat.PrivateCateRoughdesign

/-- The observed probability of a covariate cell equals its design probability. [The displayed conclusion](goal) follows. -/
-- @node: observed_cell_mass
lemma observed_cell_mass (h : ℝ) (k : ℕ) (P : CausalLaw) (j : Fin k) :
    (Pobs P).real {z : O | z.1 ∈ cell h k j} = cellMass h k P j := by
  have hs : MeasurableSet {z : O | z.1 ∈ cell h k j} :=
    (measurableSet_cell h k j).preimage measurable_fst
  simp only [cellMass, PX, Pobs, measureReal_def]
  rw [Measure.map_apply measurable_observe hs,
    Measure.map_apply measurable_X (measurableSet_cell h k j)]
  rfl

/-- A product rectangle has real mass equal to the product of its coordinate real masses.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,P,s). -/
-- @node: iid_rectangle_real
lemma iid_rectangle_real (n : ℕ) (P : CausalLaw) (s : Fin n → Set O) :
    (dataLaw n P).real (Set.univ.pi s) = ∏ i, (Pobs P).real (s i) := by
  let : IsProbabilityMeasure (Pobs P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  rw [dataLaw, measureReal_def, Measure.pi_pi, ENNReal.toReal_prod]
  rfl

/-- Under iid sampling, none of the other records belongs to a fixed measurable event with
probability p with probability (1-p)^(n-1).  [the theorem's stated inputs and assumptions](hyp:s,hs), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,P,r). -/
-- @node: iid_no_partner_probability
lemma iid_no_partner_probability (n : ℕ) (P : CausalLaw) (r : Fin n)
    (s : Set O) (hs : MeasurableSet s) :
    (dataLaw n P).real {D | ∀ i, i ≠ r → D i ∉ s} =
      (1 - (Pobs P).real s) ^ (n - 1) := by
  classical
  let : IsProbabilityMeasure (Pobs P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  have he : {D : Dataset n | ∀ i, i ≠ r → D i ∉ s} =
      Set.univ.pi (fun i => if i = r then Set.univ else sᶜ) := by
    ext D
    simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, forall_const]
    constructor
    · intro h i
      by_cases hi : i = r <;> simp [hi, h i]
    · intro h i hi
      simpa [hi] using h i
  rw [he, iid_rectangle_real, ← Finset.mul_prod_erase _ _ (Finset.mem_univ r)]
  simp only [if_pos rfl, probReal_univ, one_mul]
  have hp : (∏ i ∈ Finset.univ.erase r, (Pobs P).real
      (if i = r then Set.univ else sᶜ)) =
      ∏ _i ∈ Finset.univ.erase r, (1 - (Pobs P).real s) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [if_neg (Finset.mem_erase.mp hi).1, probReal_compl_eq_one_sub hs]
  rw [hp]
  simp

/-- The probability that the distinguished record belongs to an event and all other records
avoid it is p(1-p)^(n-1).  [the theorem's stated inputs and assumptions](hyp:s,hs), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,P,r). -/
-- @node: iid_isolated_record_probability
lemma iid_isolated_record_probability (n : ℕ) (P : CausalLaw) (r : Fin n)
    (s : Set O) (hs : MeasurableSet s) :
    (dataLaw n P).real {D | D r ∈ s ∧ ∀ i, i ≠ r → D i ∉ s} =
      (Pobs P).real s * (1 - (Pobs P).real s) ^ (n - 1) := by
  classical
  let : IsProbabilityMeasure (Pobs P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  have he : {D : Dataset n | D r ∈ s ∧ ∀ i, i ≠ r → D i ∉ s} =
      Set.univ.pi (fun i => if i = r then s else sᶜ) := by
    ext D
    simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, forall_const]
    constructor
    · rintro ⟨hr, h⟩ i
      by_cases hi : i = r <;> simp [hi, hr, h i]
    · intro h
      exact ⟨by simpa using h r, fun i hi => by simpa [hi] using h i⟩
  rw [he, iid_rectangle_real, ← Finset.mul_prod_erase _ _ (Finset.mem_univ r)]
  simp only [if_pos rfl]
  congr 1
  calc
    _ = ∏ _i ∈ Finset.univ.erase r, (1 - (Pobs P).real s) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [if_neg (Finset.mem_erase.mp hi).1, probReal_compl_eq_one_sub hs]
    _ = _ := by simp

/-- Avoidance by all records except the distinguished one is a measurable event.  [the theorem's stated inputs and assumptions](hyp:hs), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,r,s). -/
-- @node: measurableSet_no_partner
lemma measurableSet_no_partner (n : ℕ) (r : Fin n) (s : Set O)
    (hs : MeasurableSet s) :
    MeasurableSet {D : Dataset n | ∀ i, i ≠ r → D i ∉ s} := by
  simp only [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro i
  by_cases hi : i = r
  · simp [hi]
  · have hm : MeasurableSet {D : Dataset n | D i ∉ s} :=
      hs.compl.preimage (measurable_pi_apply i)
    simpa [hi] using hm

/-- The real mass of a single iid coordinate event is the observed marginal mass.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,P,r,s). -/
-- @node: iid_record_probability
lemma iid_record_probability (n : ℕ) (P : CausalLaw) (r : Fin n) (s : Set O) :
    (dataLaw n P).real {D | D r ∈ s} = (Pobs P).real s := by
  classical
  let : IsProbabilityMeasure (Pobs P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  have he : {D : Dataset n | D r ∈ s} =
      Set.univ.pi (fun i => if i = r then s else Set.univ) := by
    ext D
    simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, forall_const]
    constructor
    · intro hr i; by_cases hi : i = r <;> simp [hi, hr]
    · intro h; simpa using h r
  rw [he, iid_rectangle_real, ← Finset.mul_prod_erase _ _ (Finset.mem_univ r)]
  simp only [if_pos rfl]
  have hp : (∏ i ∈ Finset.univ.erase r, (Pobs P).real
      (if i = r then s else Set.univ)) = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    rw [if_neg (Finset.mem_erase.mp hi).1, probReal_univ]
  simp [hp]

/-- The old record has a partner in a measurable event with probability p[1-(1-p)^(n-1)].  [the theorem's stated inputs and assumptions](hyp:s,hs), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,P,r). -/
-- @node: iid_old_partner_probability
lemma iid_old_partner_probability (n : ℕ) (P : CausalLaw) (r : Fin n)
    (s : Set O) (hs : MeasurableSet s) :
    (dataLaw n P).real {D | D r ∈ s ∧ ∃ i, i ≠ r ∧ D i ∈ s} =
      (Pobs P).real s * (1 - (1 - (Pobs P).real s) ^ (n - 1)) := by
  let : IsProbabilityMeasure (Pobs P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (dataLaw n P) := by unfold dataLaw; infer_instance
  have his : MeasurableSet {D : Dataset n | D r ∈ s ∧ ∀ i, i ≠ r → D i ∉ s} :=
    (hs.preimage (measurable_pi_apply r)).inter (measurableSet_no_partner n r s hs)
  have he : {D : Dataset n | D r ∈ s ∧ ∃ i, i ≠ r ∧ D i ∈ s} =
      {D | D r ∈ s} \ {D | D r ∈ s ∧ ∀ i, i ≠ r → D i ∉ s} := by
    ext D; simp only [Set.mem_setOf_eq, Set.mem_sdiff]
    simp only [not_and, not_forall, _root_.not_imp, not_not, exists_prop]
    tauto
  rw [he, measureReal_sdiff (s₁ := {D : Dataset n | D r ∈ s}) (fun D hD => hD.1) his,
    iid_record_probability, iid_isolated_record_probability n P r s hs]
  ring

/-- An independent replacement has a partner among the unreplaced records with the same
probability p[1-(1-p)^(n-1)].  [the theorem's stated inputs and assumptions](hyp:s,hs), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,P,r). -/
-- @node: iid_new_partner_probability
lemma iid_new_partner_probability (n : ℕ) (P : CausalLaw) (r : Fin n)
    (s : Set O) (hs : MeasurableSet s) :
    ((dataLaw n P).prod (Pobs P)).real
      {zz : Dataset n × O | zz.2 ∈ s ∧ ∃ i, i ≠ r ∧ zz.1 i ∈ s} =
      (Pobs P).real s * (1 - (1 - (Pobs P).real s) ^ (n - 1)) := by
  let : IsProbabilityMeasure (Pobs P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (dataLaw n P) := by unfold dataLaw; infer_instance
  have he : {zz : Dataset n × O | zz.2 ∈ s ∧ ∃ i, i ≠ r ∧ zz.1 i ∈ s} =
      {D : Dataset n | ∀ i, i ≠ r → D i ∉ s}ᶜ ×ˢ s := by
    ext zz; simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_compl_iff]
    simp only [not_forall, _root_.not_imp, not_not, exists_prop]
    exact and_comm
  rw [he, measureReal_prod_prod,
    probReal_compl_eq_one_sub (measurableSet_no_partner n r s hs),
    iid_no_partner_probability n P r s hs]
  ring
/-- Having a partner in a measurable event is itself a measurable dataset event.  [the theorem's stated inputs and assumptions](hyp:hs), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,r,s). -/
-- @node: measurableSet_old_partner
lemma measurableSet_old_partner (n : ℕ) (r : Fin n) (s : Set O)
    (hs : MeasurableSet s) :
    MeasurableSet {D : Dataset n | D r ∈ s ∧ ∃ i, i ≠ r ∧ D i ∈ s} := by
  have he : {D : Dataset n | D r ∈ s ∧ ∃ i, i ≠ r ∧ D i ∈ s} =
      {D | D r ∈ s} ∩ {D | ∀ i, i ≠ r → D i ∉ s}ᶜ := by
    ext D
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff,
      not_forall, _root_.not_imp, not_not, exists_prop]
  rw [he]
  exact (hs.preimage (measurable_pi_apply r)).inter
    (measurableSet_no_partner n r s hs).compl

open Classical in
/-- Counting members with a distinct partner discards exactly the empty and singleton counts. [The displayed conclusion](goal) follows. -/
-- @node: finite_partner_count
lemma finite_partner_count {α : Type*} [Fintype α] (s : Finset α) :
    (∑ r : α, if r ∈ s ∧ ∃ i ∈ s, i ≠ r then (1 : ℝ) else 0) =
      if s.card < 2 then 0 else (s.card : ℝ) := by
  classical
  by_cases hs : s.card < 2
  · rw [if_pos hs]
    apply Finset.sum_eq_zero
    intro r hr
    have hn : ¬ (r ∈ s ∧ ∃ i ∈ s, i ≠ r) := by
      rintro ⟨hr, i, hi, hir⟩
      have hc := Finset.one_lt_card.mpr ⟨i, hi, r, hr, hir⟩
      omega
    simp only [if_neg hn]
  · rw [if_neg hs]
    have he (r : α) : (r ∈ s ∧ ∃ i ∈ s, i ≠ r) ↔ r ∈ s := by
      constructor
      · exact And.left
      · intro hr
        exact ⟨hr, Finset.exists_mem_ne (by omega) r⟩
    simp_rw [he]
    simp

open Classical in
/-- The eligible cell occupancy is the sum of record-level partner indicators. [The displayed conclusion](goal) follows. -/
-- @node: cell_partner_count
lemma cell_partner_count (n k : ℕ) (h : ℝ) (D : Dataset n) (j : Fin k) :
    (if cellCount n h k D j < 2 then 0 else (cellCount n h k D j : ℝ)) =
      ∑ r : Fin n, if (D r).1 ∈ cell h k j ∧
        ∃ i, i ≠ r ∧ (D i).1 ∈ cell h k j then (1 : ℝ) else 0 := by
  classical
  have he (r : Fin n) : (r ∈ cellRecords n h k D j ∧
      ∃ i ∈ cellRecords n h k D j, i ≠ r) ↔
      ((D r).1 ∈ cell h k j ∧ ∃ i, i ≠ r ∧ (D i).1 ∈ cell h k j) := by
    simp only [cellRecords, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hr, i, hi, hir⟩
      exact ⟨hr, i, hir, hi⟩
    · rintro ⟨hr, i, hir, hi⟩
      exact ⟨hr, i, hi, hir⟩
  rw [cellCount, ← finite_partner_count]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hp : (D r).1 ∈ cell h k j ∧ ∃ i, i ≠ r ∧ (D i).1 ∈ cell h k j
  · rw [if_pos hp, if_pos ((he r).mpr hp)]
  · rw [if_neg hp, if_neg (fun hc => hp ((he r).mp hc))]

/-- Eligible occupancy is integrable under every finite dataset measure. [The displayed conclusion](goal) follows. -/
-- @node: integrable_cell_partner_count
@[fun_prop] lemma integrable_cell_partner_count (n k : ℕ) (h : ℝ) (j : Fin k)
    (Q : Measure (Dataset n)) [IsFiniteMeasure Q] :
    Integrable (fun D => if cellCount n h k D j < 2 then 0 else
      (cellCount n h k D j : ℝ)) Q := by
  classical
  simp_rw [cell_partner_count]
  apply integrable_finset_sum
  intro r hr
  have hs := measurableSet_old_partner n r {z : O | z.1 ∈ cell h k j}
    ((measurableSet_cell h k j).preimage measurable_fst)
  have hi := (integrable_const (μ := Q) (1 : ℝ)).indicator hs
  apply hi.congr
  filter_upwards with D
  by_cases hp : (D r).1 ∈ cell h k j ∧ ∃ i, i ≠ r ∧ (D i).1 ∈ cell h k j
  · simp [Set.indicator_apply, hp]
  · simp [Set.indicator_apply, hp]

/-- The binomial occupancy identity follows by summing iid record-partner probabilities,
without requiring independence between different cell counts.  [the theorem's stated inputs and assumptions](hyp:j), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k,h,P). -/
-- @node: iid_cell_partner_count_expectation
lemma iid_cell_partner_count_expectation (n k : ℕ) (h : ℝ) (P : CausalLaw)
    (j : Fin k) :
    (∫ D, (if cellCount n h k D j < 2 then 0 else
      (cellCount n h k D j : ℝ)) ∂dataLaw n P) = occupancyWeight n h k P j := by
  classical
  let : IsProbabilityMeasure (Pobs P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (dataLaw n P) := by unfold dataLaw; infer_instance
  let s : Set O := {z | z.1 ∈ cell h k j}
  have hs : MeasurableSet s := (measurableSet_cell h k j).preimage measurable_fst
  have hi (r : Fin n) : Integrable (fun D : Dataset n =>
      if D r ∈ s ∧ ∃ i, i ≠ r ∧ D i ∈ s then (1 : ℝ) else 0) (dataLaw n P) := by
    have hi := (integrable_const (μ := dataLaw n P) (1 : ℝ)).indicator (measurableSet_old_partner n r s hs)
    apply hi.congr
    filter_upwards with D
    by_cases hp : D r ∈ s ∧ ∃ i, i ≠ r ∧ D i ∈ s
    · simp [Set.indicator_apply, hp]
    · simp [Set.indicator_apply, hp]
  simp_rw [cell_partner_count]
  change (∫ D : Dataset n, (∑ r : Fin n,
    if D r ∈ s ∧ ∃ i, i ≠ r ∧ D i ∈ s then (1 : ℝ) else 0) ∂dataLaw n P) = _
  rw [integral_finset_sum _ (fun r _ => hi r)]
  have hm (r : Fin n) : (∫ D : Dataset n,
      (if D r ∈ s ∧ ∃ i, i ≠ r ∧ D i ∈ s then (1 : ℝ) else 0) ∂dataLaw n P) =
      cellMass h k P j * (1 - (1 - cellMass h k P j) ^ (n - 1)) := by
    have hv := integral_indicator_one (μ := dataLaw n P)
      (measurableSet_old_partner n r s hs)
    simp only [Set.indicator, Set.mem_setOf_eq, Pi.one_apply] at hv
    rw [hv, iid_old_partner_probability n P r s hs]
    rw [show (Pobs P).real s = cellMass h k P j from observed_cell_mass h k P j]
  change (∑ r : Fin n, (∫ D : Dataset n,
    (if D r ∈ s ∧ ∃ i, i ≠ r ∧ D i ∈ s then (1 : ℝ) else 0) ∂dataLaw n P)) = _
  simp_rw [hm]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    occupancyWeight]
  ring

end CausalSmith.Stat.PrivateCateRoughdesign
