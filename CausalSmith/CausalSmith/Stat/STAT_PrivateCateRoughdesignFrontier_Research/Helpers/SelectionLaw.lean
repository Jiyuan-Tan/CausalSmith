module
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.Occupancy
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.PartnerProbability
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.Stability
/-! Membership-label rectangles and their normalized iid product laws. -/
public section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace CausalSmith.Stat.PrivateCateRoughdesign

/-- Specifying every cell membership label is a rectangle in the iid sample space.  [the theorem's stated inputs and assumptions](hyp:I), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k,h,j). -/
-- @node: cell_membership_rectangle
lemma cell_membership_rectangle (n k : ℕ) (h : ℝ) (j : Fin k)
    (I : Finset (Fin n)) :
    {D : Dataset n | cellRecords n h k D j = I} =
      Set.univ.pi (fun i => if i ∈ I then {z : O | z.1 ∈ cell h k j}
        else {z : O | z.1 ∈ cell h k j}ᶜ) := by
  classical
  ext D
  simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_const]
  constructor
  · intro hD i
    have hi : i ∈ cellRecords n h k D j ↔ i ∈ I := by rw [hD]
    simp only [cellRecords, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    by_cases hI : i ∈ I <;> simp [hI, hi]
  · intro hD
    apply Finset.ext
    intro i
    simp only [cellRecords, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hI : i ∈ I <;> simpa [hI] using hD i

/-- Every exact membership-label event is measurable.  [the theorem's stated inputs and assumptions](hyp:I), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k,h,j). -/
-- @node: measurableSet_cell_membership
lemma measurableSet_cell_membership (n k : ℕ) (h : ℝ) (j : Fin k)
    (I : Finset (Fin n)) :
    MeasurableSet {D : Dataset n | cellRecords n h k D j = I} := by
  classical
  rw [cell_membership_rectangle]
  apply MeasurableSet.univ_pi
  intro i
  split_ifs
  · exact (measurableSet_cell h k j).preimage measurable_fst
  · exact ((measurableSet_cell h k j).preimage measurable_fst).compl

/-- Restricting the iid sample law to specified labels factors coordinate by coordinate.  [the theorem's stated inputs and assumptions](hyp:j,I), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k,h,P). -/
-- @node: iid_membership_restriction
lemma iid_membership_restriction (n k : ℕ) (h : ℝ) (P : CausalLaw)
    (j : Fin k) (I : Finset (Fin n)) :
    (dataLaw n P).restrict {D | cellRecords n h k D j = I} =
      Measure.pi (fun i => (Pobs P).restrict
        (if i ∈ I then {z : O | z.1 ∈ cell h k j}
          else {z : O | z.1 ∈ cell h k j}ᶜ)) := by
  classical
  let : IsProbabilityMeasure (Pobs P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  rw [cell_membership_rectangle, dataLaw, Measure.restrict_pi_pi]

/-- Normalizing any positive-mass restriction gives a probability law.  [the theorem's stated inputs and assumptions](hyp:s,hs), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:μ). -/
-- @node: normalized_record_restriction_probability
lemma normalized_record_restriction_probability (μ : Measure O) [IsFiniteMeasure μ]
    (s : Set O) (hs : μ s ≠ 0) :
    IsProbabilityMeasure ((μ s)⁻¹ • μ.restrict s) := by
  refine ⟨?_⟩
  rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hs (measure_ne_top μ s)

/-- Dividing a positive rectangle restriction by its mass preserves the product structure.  [the theorem's stated inputs and assumptions](hyp:s,hs), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,μ). -/
-- @node: iid_normalized_rectangle
lemma iid_normalized_rectangle (n : ℕ) (μ : Measure O) [IsFiniteMeasure μ]
    (s : Fin n → Set O) (hs : ∀ i, μ (s i) ≠ 0) :
    ((Measure.pi (fun _ : Fin n => μ)) (Set.univ.pi s))⁻¹ •
      (Measure.pi (fun _ : Fin n => μ)).restrict (Set.univ.pi s) =
      Measure.pi (fun i => (μ (s i))⁻¹ • μ.restrict (s i)) := by
  let ν := fun i => (μ (s i))⁻¹ • μ.restrict (s i)
  let : ∀ i, IsProbabilityMeasure (ν i) :=
    fun i => normalized_record_restriction_probability μ (s i) (hs i)
  apply (Measure.pi_eq (μ := ν) _).symm
  intro t ht
  rw [Measure.smul_apply, smul_eq_mul, Measure.pi_pi,
    Measure.restrict_pi_pi, Measure.pi_pi]
  simp only [ν, Measure.smul_apply, smul_eq_mul]
  rw [Finset.prod_mul_distrib, ENNReal.prod_inv_distrib]
  intro i hi l hl hil
  exact Or.inl (hs i)

/-- Given a specified positive-probability label pattern, all records are independent with
coordinate laws conditioned on their own labels. The result uses [the stated assumptions](hyp:hp) and establishes [the displayed conclusion](goal). -/
-- @node: iid_conditional_membership_law
lemma iid_conditional_membership_law (n k : ℕ) (h : ℝ) (P : CausalLaw)
    (j : Fin k) (I : Finset (Fin n))
    (hp : ∀ i : Fin n, (Pobs P)
      (if i ∈ I then {z : O | z.1 ∈ cell h k j}
        else {z : O | z.1 ∈ cell h k j}ᶜ) ≠ 0) :
    ((dataLaw n P) {D | cellRecords n h k D j = I})⁻¹ •
      (dataLaw n P).restrict {D | cellRecords n h k D j = I} =
      Measure.pi (fun i =>
        ((Pobs P) (if i ∈ I then {z : O | z.1 ∈ cell h k j}
          else {z : O | z.1 ∈ cell h k j}ᶜ))⁻¹ •
        (Pobs P).restrict (if i ∈ I then {z : O | z.1 ∈ cell h k j}
          else {z : O | z.1 ∈ cell h k j}ᶜ)) := by
  classical
  let : IsProbabilityMeasure (Pobs P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  rw [cell_membership_rectangle, dataLaw]
  exact iid_normalized_rectangle n (Pobs P) _ hp

/-- On an exact label event, two selected coordinates have the independent conditional cell
law, irrespective of the membership of the other records. The result uses [the stated assumptions](hyp:hp,hi,hl,hil) and establishes [the displayed conclusion](goal). -/
-- @node: iid_conditional_membership_pair
lemma iid_conditional_membership_pair (n k : ℕ) (h : ℝ) (P : CausalLaw)
    (j : Fin k) (I : Finset (Fin n))
    (hp : ∀ r : Fin n, (Pobs P)
      (if r ∈ I then {z : O | z.1 ∈ cell h k j}
        else {z : O | z.1 ∈ cell h k j}ᶜ) ≠ 0)
    (i l : Fin n) (hi : i ∈ I) (hl : l ∈ I) (hil : i ≠ l) :
    MeasurePreserving (fun D : Dataset n => (D i, D l))
      (((dataLaw n P) {D | cellRecords n h k D j = I})⁻¹ •
        (dataLaw n P).restrict {D | cellRecords n h k D j = I})
      ((conditionalCellLaw h k P j).prod (conditionalCellLaw h k P j)) := by
  classical
  let : IsProbabilityMeasure (Pobs P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let s := fun r : Fin n => if r ∈ I then {z : O | z.1 ∈ cell h k j}
    else {z : O | z.1 ∈ cell h k j}ᶜ
  let ν := fun r => ((Pobs P) (s r))⁻¹ • (Pobs P).restrict (s r)
  let : ∀ r, IsProbabilityMeasure (ν r) :=
    fun r => normalized_record_restriction_probability (Pobs P) (s r) (hp r)
  have hind := ProbabilityTheory.iIndepFun_pi
    (μ := ν) (X := fun _ (z : O) => z) (fun _ => measurable_id.aemeasurable)
  have hm := (hind.indepFun hil).map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply l).aemeasurable
  rw [(measurePreserving_eval ν i).map_eq, (measurePreserving_eval ν l).map_eq] at hm
  have hvi : ν i = conditionalCellLaw h k P j := by
    simp [ν, s, hi, conditionalCellLaw]
  have hvl : ν l = conditionalCellLaw h k P j := by
    simp [ν, s, hl, conditionalCellLaw]
  rw [hvi, hvl] at hm
  rw [iid_conditional_membership_law n k h P j I hp]
  exact ⟨by fun_prop, hm⟩

/-- Every selected pair on a fixed label event has the same kernel expectation. This is the
conditional pair identity needed before summing the unordered pairs and then the label events. The result uses [the stated assumptions](hyp:hp,hi,hl,hil,hK) and establishes [the displayed conclusion](goal). -/
-- @node: iid_conditional_membership_pair_integral
lemma iid_conditional_membership_pair_integral (n k : ℕ) (h : ℝ) (P : CausalLaw)
    (j : Fin k) (I : Finset (Fin n))
    (hp : ∀ r : Fin n, (Pobs P)
      (if r ∈ I then {z : O | z.1 ∈ cell h k j}
        else {z : O | z.1 ∈ cell h k j}ᶜ) ≠ 0)
    (i l : Fin n) (hi : i ∈ I) (hl : l ∈ I) (hil : i ≠ l)
    (K : O → O → ℝ)
    (hK : Integrable (fun z : O × O => K z.1 z.2)
      ((conditionalCellLaw h k P j).prod (conditionalCellLaw h k P j))) :
    Integrable (fun D : Dataset n => K (D i) (D l))
      (((dataLaw n P) {D | cellRecords n h k D j = I})⁻¹ •
        (dataLaw n P).restrict {D | cellRecords n h k D j = I}) ∧
    (∫ D : Dataset n, K (D i) (D l)
      ∂(((dataLaw n P) {D | cellRecords n h k D j = I})⁻¹ •
        (dataLaw n P).restrict {D | cellRecords n h k D j = I})) =
      ∫ z, K z.1 z.2
        ∂(conditionalCellLaw h k P j).prod (conditionalCellLaw h k P j) := by
  have hf := iid_conditional_membership_pair n k h P j I hp i l hi hl hil
  constructor
  · exact hf.integrable_comp_of_integrable hK
  · rw [← hf.map_eq] at hK ⊢
    exact (integral_map hf.measurable.aemeasurable hK.aestronglyMeasurable).symm

/-- The complete density model gives positive probability to either membership label.  [the theorem's stated inputs and assumptions](hyp:hh,P,hP,j,I,i), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k,hk). -/
-- @node: cell_membership_label_positive
lemma cell_membership_label_positive (n k : ℕ) (h : ℝ) (hk : 2 ≤ k)
    (hh : 0 < h ∧ h ≤ 1 / 4) (P : CausalLaw) (hP : CompleteModel P)
    (j : Fin k) (I : Finset (Fin n)) (i : Fin n) :
    (Pobs P) (if i ∈ I then {z : O | z.1 ∈ cell h k j}
      else {z : O | z.1 ∈ cell h k j}ᶜ) ≠ 0 := by
  classical
  let : IsProbabilityMeasure (Pobs P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  have hd := (cell_endpoint_bounds k h (by omega) hh j).2.2.2
  obtain ⟨hlo, hhi⟩ := cellMass_density_bounds k h (by omega) hh P hP j
  have hw : cellWidth h k ≤ 1 / 4 := by
    unfold cellWidth
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < k)).mpr
    have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith [hh.2]
  have hp : 0 < (Pobs P).real {z : O | z.1 ∈ cell h k j} := by
    rw [observed_cell_mass]
    linarith
  have hc : 0 < (Pobs P).real {z : O | z.1 ∈ cell h k j}ᶜ := by
    have hs : MeasurableSet {z : O | z.1 ∈ cell h k j} :=
      (measurableSet_cell h k j).preimage measurable_fst
    rw [probReal_compl_eq_one_sub (μ := Pobs P) hs,
      observed_cell_mass]
    linarith
  split_ifs
  · intro hz
    simp [measureReal_def, hz] at hp
  · intro hz
    simp [measureReal_def, hz] at hc

/-- A normalized exact label event is a probability measure. The result uses [the stated assumptions](hyp:hp) and establishes [the displayed conclusion](goal). -/
-- @node: conditional_membership_probability
lemma conditional_membership_probability (n k : ℕ) (h : ℝ) (P : CausalLaw)
    (j : Fin k) (I : Finset (Fin n))
    (hp : ∀ r : Fin n, (Pobs P)
      (if r ∈ I then {z : O | z.1 ∈ cell h k j}
        else {z : O | z.1 ∈ cell h k j}ᶜ) ≠ 0) :
    IsProbabilityMeasure (((dataLaw n P) {D | cellRecords n h k D j = I})⁻¹ •
      (dataLaw n P).restrict {D | cellRecords n h k D j = I}) := by
  classical
  let : IsProbabilityMeasure (Pobs P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  rw [iid_conditional_membership_law n k h P j I hp]
  let : ∀ r : Fin n, IsProbabilityMeasure
      (((Pobs P) (if r ∈ I then {z : O | z.1 ∈ cell h k j}
        else {z : O | z.1 ∈ cell h k j}ᶜ))⁻¹ •
        (Pobs P).restrict (if r ∈ I then {z : O | z.1 ∈ cell h k j}
          else {z : O | z.1 ∈ cell h k j}ᶜ)) :=
    fun r => normalized_record_restriction_probability (Pobs P) _ (hp r)
  infer_instance

/-- Summing the selected unordered pairs at fixed membership labels gives occupancy times the
common conditional pair moment. The result uses [the stated assumptions](hyp:hp,e,hK) and establishes [the displayed conclusion](goal). -/
-- @node: conditional_selected_pairContribution_expectation
lemma conditional_selected_pairContribution_expectation (n k : ℕ) (h : ℝ)
    (P : CausalLaw) (j : Fin k) (I : Finset (Fin n))
    (hp : ∀ r : Fin n, (Pobs P)
      (if r ∈ I then {z : O | z.1 ∈ cell h k j}
        else {z : O | z.1 ∈ cell h k j}ᶜ) ≠ 0)
    (e : Fin I.card ≃ {i // i ∈ I}) (K : O → O → ℝ)
    (hK : Integrable (fun z : O × O => K z.1 z.2)
      ((conditionalCellLaw h k P j).prod (conditionalCellLaw h k P j))) :
    (∫ D : Dataset n, pairContribution K (fun i => D (e i))
      ∂(((dataLaw n P) {D | cellRecords n h k D j = I})⁻¹ •
        (dataLaw n P).restrict {D | cellRecords n h k D j = I})) =
      (if I.card < 2 then 0 else (I.card : ℝ)) *
        ∫ z, K z.1 z.2
          ∂(conditionalCellLaw h k P j).prod (conditionalCellLaw h k P j) := by
  classical
  let Q := ((dataLaw n P) {D | cellRecords n h k D j = I})⁻¹ •
    (dataLaw n P).restrict {D | cellRecords n h k D j = I}
  by_cases hs : I.card < 2
  · simp [pairContribution, hs]
  have hc : (Nat.choose I.card 2 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (show 2 ≤ I.card by omega)).ne'
  have hpairs (i l : Fin I.card) (hil : i ≠ l) :=
    iid_conditional_membership_pair_integral n k h P j I hp (e i) (e l)
      (e i).property (e l).property
      (fun he => hil (e.injective (Subtype.ext he))) K hK
  have hi (i l : Fin I.card) : Integrable (fun D : Dataset n =>
      if i < l then K (D (e i)) (D (e l)) else 0) Q := by
    by_cases hil : i < l
    · simpa only [if_pos hil] using (hpairs i l hil.ne).1
    · simp only [if_neg hil]
      exact integrable_zero _ _ _
  have hm (i l : Fin I.card) :
      (∫ D : Dataset n, (if i < l then K (D (e i)) (D (e l)) else 0) ∂Q) =
        (if i < l then (1 : ℝ) else 0) *
          ∫ z, K z.1 z.2
            ∂(conditionalCellLaw h k P j).prod (conditionalCellLaw h k P j) := by
    by_cases hil : i < l
    · simp only [if_pos hil, one_mul]
      exact (hpairs i l hil.ne).2
    · simp [hil]
  change (∫ D : Dataset n, pairContribution K (fun i => D (e i)) ∂Q) = _
  simp only [pairContribution, if_neg hs]
  rw [integral_const_mul, integral_finset_sum _ (fun i _ =>
    integrable_finset_sum _ (fun l _ => hi i l))]
  simp_rw [integral_finset_sum _ (fun l _ => hi _ l), hm, ← Finset.sum_mul]
  rw [ordered_pair_count]
  field_simp [hc]

end CausalSmith.Stat.PrivateCateRoughdesign
