module
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.DesignPairMoments
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.Occupancy
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.PartnerProbability
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.SelectionLaw
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.Stability
/-! Positive-mass conditional cell laws, independent binary pair moments and occupancy-certificate assembly. -/
public section
open MeasureTheory
open scoped ENNReal
namespace CausalSmith.Stat.PrivateCateRoughdesign

/-- The observed cell event has exactly the mass of the corresponding design cell.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:k,h,P,j). -/
-- @node: observed_cell_measure
lemma observed_cell_measure (k : ℕ) (h : ℝ) (P : CausalLaw) (j : Fin k) :
    (Pobs P) {z | z.1 ∈ cell h k j} = (PX P) (cell h k j) := by
  change (P.law.map observe) (Prod.fst ⁻¹' cell h k j) = (P.law.map X) (cell h k j)
  rw [Measure.map_apply measurable_observe
    ((measurableSet_cell h k j).preimage measurable_fst),
    Measure.map_apply measurable_X (measurableSet_cell h k j)]
  rfl

/-- Density bounded below ensures that conditioning on any public cell gives a probability law.  [the theorem's stated inputs and assumptions](hyp:hh,P,hP,j), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:k,hk). -/
-- @node: conditionalCellLaw_probability
lemma conditionalCellLaw_probability (k : ℕ) (h : ℝ) (hk : 0 < k)
    (hh : 0 < h ∧ h ≤ 1 / 4) (P : CausalLaw) (hP : CompleteModel P) (j : Fin k) :
    IsProbabilityMeasure (conditionalCellLaw h k P j) := by
  let : IsProbabilityMeasure (PX P) := Measure.isProbabilityMeasure_map measurable_X.aemeasurable
  let : IsProbabilityMeasure (PX P) := Measure.isProbabilityMeasure_map measurable_X.aemeasurable
  have hp : 0 < cellMass h k P j := lt_of_lt_of_le
    (half_pos (cell_endpoint_bounds k h hk hh j).2.2.2)
    (cellMass_density_bounds k h hk hh P hP j).1
  have hzero : (PX P) (cell h k j) ≠ 0 := by
    intro hz
    simp [cellMass, measureReal_def, hz] at hp
  refine ⟨?_⟩
  simp only [conditionalCellLaw, Measure.smul_apply, Measure.restrict_apply
    MeasurableSet.univ, Set.univ_inter, smul_eq_mul, observed_cell_measure]
  exact ENNReal.inv_mul_cancel hzero (measure_ne_top _ _)

/-- The bounded binary numerator kernel is integrable under any finite pair measure. [The displayed conclusion](goal) follows. -/
-- @node: integrable_causal_pair_numerator
@[fun_prop] lemma integrable_causal_pair_numerator (μ : Measure (O × O)) [IsFiniteMeasure μ] :
    Integrable (fun z => KN z.1 z.2) μ := by
  apply Integrable.of_bound (by unfold KN; fun_prop) 1
  filter_upwards [] with z
  simpa only [Real.norm_eq_abs] using (causal_pair_kernel_unit_bounds z.1 z.2).1

/-- The bounded binary denominator kernel is integrable under any finite pair measure. [The displayed conclusion](goal) follows. -/
-- @node: integrable_causal_pair_denominator
@[fun_prop] lemma integrable_causal_pair_denominator (μ : Measure (O × O)) [IsFiniteMeasure μ] :
    Integrable (fun z => KD z.1 z.2) μ := by
  apply Integrable.of_bound (by unfold KD; fun_prop) 1
  filter_upwards [] with z
  simpa only [Real.norm_eq_abs] using (causal_pair_kernel_unit_bounds z.1 z.2).2

/-- The conditional pair numerator cannot exceed the denominator in absolute value.  [the theorem's stated inputs and assumptions](hyp:hh,P,hP,j), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:k,hk). -/
-- @node: conditional_cell_numerator_abs_le_denominator
lemma conditional_cell_numerator_abs_le_denominator (k : ℕ) (h : ℝ) (hk : 0 < k)
    (hh : 0 < h ∧ h ≤ 1 / 4) (P : CausalLaw) (hP : CompleteModel P) (j : Fin k) :
    |nu h k P j| ≤ dj h k P j := by
  let := conditionalCellLaw_probability k h hk hh P hP j
  let μ := (conditionalCellLaw h k P j).prod (conditionalCellLaw h k P j)
  have hN := integrable_causal_pair_numerator μ
  have hD := integrable_causal_pair_denominator μ
  calc
    |nu h k P j| ≤ ∫ z, |KN z.1 z.2| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ z, KD z.1 z.2 ∂μ := integral_mono hN.abs hD
      (fun z => (causal_pair_kernel_bounds z.1 z.2).2.2.1)
    _ = dj h k P j := rfl

/-- The normalized cell treatment mean is the selected propensity averaged over that cell.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:k,h,P,j). -/
-- @node: conditional_cell_treatment_mean
lemma conditional_cell_treatment_mean (k : ℕ) (h : ℝ) (P : CausalLaw) (j : Fin k) :
    (∫ z, bit z.2.1 ∂conditionalCellLaw h k P j) =
      (∫ x in cell h k j, P.e x ∂PX P) / cellMass h k P j := by
  have ht : MeasurableSet {z : O | z.2.1 = true} :=
    measurableSet_eq_fun (by fun_prop) measurable_const
  have heq : (fun z : O => bit z.2.1) =
      {z : O | z.2.1 = true}.indicator (fun _ => (1 : ℝ)) := by
    funext z
    cases hz : z.2.1 <;> simp [bit, Set.indicator, hz]
  rw [conditionalCellLaw, integral_smul_measure, heq, integral_indicator ht,
    setIntegral_one_eq_measureReal]
  simp only [measureReal_def, Measure.restrict_apply ht, ENNReal.toReal_inv]
  rw [observed_cell_measure]
  have hj : MeasurableSet ({z : O | z.2.1 = true} ∩ {z | z.1 ∈ cell h k j}) :=
    ht.inter ((measurableSet_cell h k j).preimage measurable_fst)
  rw [Pobs, Measure.map_apply measurable_observe hj]
  have hs : observe ⁻¹' ({z : O | z.2.1 = true} ∩ {z | z.1 ∈ cell h k j}) =
      {z | X z ∈ cell h k j ∧ A z = true} := by
    ext z
    simp [observe, and_comm]
  rw [hs]
  change ((PX P).real (cell h k j))⁻¹ *
    P.law.real {z | X z ∈ cell h k j ∧ A z = true} = _
  rw [← P.e_version _ (measurableSet_cell h k j)]
  simp only [cellMass, PX, div_eq_mul_inv, mul_comm]

/-- Averaging the everywhere overlap bounds under a positive-mass cell preserves overlap.  [the theorem's stated inputs and assumptions](hyp:hh,P,hP,j), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:k,hk). -/
-- @node: conditional_cell_treatment_overlap
lemma conditional_cell_treatment_overlap (k : ℕ) (h : ℝ) (hk : 0 < k)
    (hh : 0 < h ∧ h ≤ 1 / 4) (P : CausalLaw) (hP : CompleteModel P) (j : Fin k) :
    1 / 4 ≤ (∫ z, bit z.2.1 ∂conditionalCellLaw h k P j) ∧
      (∫ z, bit z.2.1 ∂conditionalCellLaw h k P j) ≤ 3 / 4 := by
  let : IsProbabilityMeasure (PX P) := Measure.isProbabilityMeasure_map measurable_X.aemeasurable
  have hp : 0 < cellMass h k P j := lt_of_lt_of_le
    (half_pos (cell_endpoint_bounds k h hk hh j).2.2.2)
    (cellMass_density_bounds k h hk hh P hP j).1
  have hlo : ∫ x in cell h k j, (1 / 4 : ℝ) ∂PX P ≤
      ∫ x in cell h k j, P.e x ∂PX P := by
    exact integral_mono_ae (integrable_const _) P.e_integrable.integrableOn
      (ae_of_all _ (fun x => (hP.overlap x).1))
  have hhi : ∫ x in cell h k j, P.e x ∂PX P ≤
      ∫ x in cell h k j, (3 / 4 : ℝ) ∂PX P := by
    exact integral_mono_ae P.e_integrable.integrableOn (integrable_const _)
      (ae_of_all _ (fun x => (hP.overlap x).2))
  simp only [setIntegral_const, smul_eq_mul] at hlo hhi
  rw [conditional_cell_treatment_mean]
  constructor
  · apply (le_div_iff₀ hp).mpr
    simpa only [cellMass, mul_comm] using hlo
  · apply (div_le_iff₀ hp).mpr
    simpa only [cellMass, mul_comm] using hhi

/-- Independent binary treatments have denominator moment twice p times one minus p.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:μ). -/
-- @node: independent_binary_denominator_moment
lemma independent_binary_denominator_moment (μ : Measure O) [IsProbabilityMeasure μ] :
    (∫ z, KD z.1 z.2 ∂μ.prod μ) =
      2 * (∫ z, bit z.2.1 ∂μ) * (1 - ∫ z, bit z.2.1 ∂μ) := by
  have hb := integrable_bit_comp μ (fun z : O => z.2.1) (by fun_prop)
  rw [integral_prod _ (integrable_causal_pair_denominator (μ.prod μ))]
  have hk (x y : O) : KD x y =
      bit x.2.1 + bit y.2.1 - (2 * bit x.2.1) * bit y.2.1 := by
    cases hx : x.2.1 <;> cases hy : y.2.1 <;> norm_num [KD, bit, hx, hy]
  simp_rw [hk]
  have hinner (x : O) :
      (∫ y, bit x.2.1 + bit y.2.1 - (2 * bit x.2.1) * bit y.2.1 ∂μ) =
        bit x.2.1 + (∫ y, bit y.2.1 ∂μ) - (2 * bit x.2.1) * (∫ y, bit y.2.1 ∂μ) := by
    integral_linearity
    simp
  simp_rw [hinner]
  integral_linearity
  simp only [integral_const, probReal_univ, one_smul]
  ring

/-- The conditional pair denominator satisfies the paper's three-eighths lower bound.  [the theorem's stated inputs and assumptions](hyp:hh,P,hP,j), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:k,hk). -/
-- @node: conditional_cell_denominator_lower
lemma conditional_cell_denominator_lower (k : ℕ) (h : ℝ) (hk : 0 < k)
    (hh : 0 < h ∧ h ≤ 1 / 4) (P : CausalLaw) (hP : CompleteModel P) (j : Fin k) :
    3 / 8 ≤ dj h k P j := by
  let := conditionalCellLaw_probability k h hk hh P hP j
  have he := conditional_cell_treatment_overlap k h hk hh P hP j
  have hd := (cross_treatment_denominator_bounds _ _ he he).1
  rw [dj, independent_binary_denominator_moment]
  nlinarith

/-- Conditioning rescales an observed cell integral by its actual design probability.  [the theorem's stated inputs and assumptions](hyp:f), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:k,h,P,j). -/
-- @node: conditional_cell_integral
lemma conditional_cell_integral (k : ℕ) (h : ℝ) (P : CausalLaw) (j : Fin k)
    (f : O → ℝ) :
    (∫ z, f z ∂conditionalCellLaw h k P j) =
      (∫ z in {z : O | z.1 ∈ cell h k j}, f z ∂Pobs P) / cellMass h k P j := by
  rw [conditionalCellLaw, integral_smul_measure, ENNReal.toReal_inv,
    observed_cell_measure]
  simp only [cellMass, measureReal_def, smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- The arm-response integral equals the design integral of the arm probability times its mean.  [the theorem's stated inputs and assumptions](hyp:d,s,hs), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:P,hP). -/
-- @node: observed_arm_response_design_integral
lemma observed_arm_response_design_integral (P : CausalLaw) (hP : CompleteModel P)
    (d : Bool) (s : Set Covariate) (hs : MeasurableSet s) :
    (∫ z in {z : O | z.1 ∈ s ∧ z.2.1 = d}, bit z.2.2 ∂Pobs P) =
      ∫ x in s, (if d then P.e x else 1 - P.e x) *
        (if d then P.mu1 x else P.mu0 x) ∂PX P := by
  rw [← observed_arm_outcome_integral P d s hs]
  have hv : (∫ z in {z | X z ∈ s ∧ A z = d}, bit (Y z) ∂P.law) =
      ∫ x in s, (if d then P.mu1 x else P.mu0 x)
        ∂((P.law.restrict {z | A z = d}).map X) := by
    cases d
    · exact (P.mu0_version s hs).symm
    · exact (P.mu1_version s hs).symm
  rw [hv, arm_design_withDensity P hP d]
  have hq : Measurable (fun x => if d then P.e x else 1 - P.e x) := by
    have he := P.e_measurable
    cases d <;> simp only [Bool.false_eq_true, if_false, if_true] <;> fun_prop
  change (∫ x in s, (if d then P.mu1 x else P.mu0 x)
    ∂(PX P).withDensity (ENNReal.ofReal ∘ (fun x => if d then P.e x else 1 - P.e x))) = _
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul₀ (μ := PX P)
    (ENNReal.measurable_ofReal.comp hq).aemeasurable
    (ae_of_all _ (fun x => ENNReal.ofReal_lt_top)) _ hs]
  apply integral_congr_ae
  filter_upwards with x
  have hn : 0 ≤ (if d then P.e x else 1 - P.e x) := by
    cases d <;> simp only [Bool.false_eq_true, if_false, if_true] <;>
      linarith [(hP.overlap x).1, (hP.overlap x).2]
  simp only [Function.comp_def, ENNReal.toReal_ofReal hn, smul_eq_mul]

/-- Each conditional arm-response moment averages the selected arm regression with its propensity.  [the theorem's stated inputs and assumptions](hyp:hP,j,d), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:k,P). -/
-- @node: conditional_cell_arm_response_mean
lemma conditional_cell_arm_response_mean (k : ℕ) (h : ℝ) (P : CausalLaw)
    (hP : CompleteModel P) (j : Fin k) (d : Bool) :
    (∫ z, (if z.2.1 = d then bit z.2.2 else 0) ∂conditionalCellLaw h k P j) =
      (∫ x in cell h k j, (if d then P.e x else 1 - P.e x) *
        (if d then P.mu1 x else P.mu0 x) ∂PX P) / cellMass h k P j := by
  have ht : MeasurableSet {z : O | z.2.1 = d} :=
    measurableSet_eq_fun (by fun_prop) measurable_const
  have heq : (fun z : O => if z.2.1 = d then bit z.2.2 else 0) =
      {z : O | z.2.1 = d}.indicator (fun z => bit z.2.2) := by
    funext z
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  rw [conditional_cell_integral, heq, setIntegral_indicator ht]
  have hs : {z : O | z.1 ∈ cell h k j} ∩ {z : O | z.2.1 = d} =
      {z : O | z.1 ∈ cell h k j ∧ z.2.1 = d} := rfl
  rw [hs, observed_arm_response_design_integral P hP d _ (measurableSet_cell h k j)]

/-- The conditional treated-response moment is the cell average of propensity times treated mean.  [the theorem's stated inputs and assumptions](hyp:hP,j), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:k,P). -/
-- @node: conditional_cell_treated_response_mean
lemma conditional_cell_treated_response_mean (k : ℕ) (h : ℝ) (P : CausalLaw)
    (hP : CompleteModel P) (j : Fin k) :
    (∫ z, bit z.2.1 * bit z.2.2 ∂conditionalCellLaw h k P j) =
      (∫ x in cell h k j, P.e x * P.mu1 x ∂PX P) / cellMass h k P j := by
  have heq : (fun z : O => bit z.2.1 * bit z.2.2) =
      (fun z : O => if z.2.1 = true then bit z.2.2 else 0) := by
    funext z
    cases z.2.1 <;> simp [bit]
  rw [heq, conditional_cell_arm_response_mean k h P hP j true]
  simp only [if_true]

/-- The conditional response mean sums the propensity-weighted means in the two treatment arms.  [the theorem's stated inputs and assumptions](hyp:hh,P,hP,j), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:k,hk). -/
-- @node: conditional_cell_response_mean
lemma conditional_cell_response_mean (k : ℕ) (h : ℝ) (hk : 0 < k)
    (hh : 0 < h ∧ h ≤ 1 / 4) (P : CausalLaw)
    (hP : CompleteModel P) (j : Fin k) :
    (∫ z, bit z.2.2 ∂conditionalCellLaw h k P j) =
      (∫ x in cell h k j, (1 - P.e x) * P.mu0 x ∂PX P) / cellMass h k P j +
      (∫ x in cell h k j, P.e x * P.mu1 x ∂PX P) / cellMass h k P j := by
  let μ := conditionalCellLaw h k P j
  let : IsProbabilityMeasure μ := conditionalCellLaw_probability k h hk hh P hP j
  have hy := integrable_bit_comp μ (fun z : O => z.2.2) (by fun_prop)
  have ht (d : Bool) : MeasurableSet {z : O | z.2.1 = d} :=
    measurableSet_eq_fun (by fun_prop) measurable_const
  have hi (d : Bool) : Integrable (fun z : O => if z.2.1 = d then bit z.2.2 else 0) μ := by
    have heq : (fun z : O => if z.2.1 = d then bit z.2.2 else 0) =
        {z : O | z.2.1 = d}.indicator (fun z => bit z.2.2) := by
      funext z
      simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    rw [heq]
    exact hy.indicator (ht d)
  have heq : (fun z : O => bit z.2.2) =
      (fun z : O => (if z.2.1 = false then bit z.2.2 else 0) +
        (if z.2.1 = true then bit z.2.2 else 0)) := by
    funext z
    cases z.2.1 <;> simp
  rw [heq, integral_add (hi false) (hi true),
    conditional_cell_arm_response_mean k h P hP j false,
    conditional_cell_arm_response_mean k h P hP j true]
  simp only [Bool.false_eq_true, if_false, if_true]

/-- Independent binary records have numerator moment twice the treatment-response covariance.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:μ). -/
-- @node: independent_binary_numerator_moment
lemma independent_binary_numerator_moment (μ : Measure O) [IsProbabilityMeasure μ] :
    (∫ z, KN z.1 z.2 ∂μ.prod μ) =
      2 * ((∫ z, bit z.2.1 * bit z.2.2 ∂μ) -
        (∫ z, bit z.2.1 ∂μ) * (∫ z, bit z.2.2 ∂μ)) := by
  have ha := integrable_bit_comp μ (fun z : O => z.2.1) (by fun_prop)
  have hy := integrable_bit_comp μ (fun z : O => z.2.2) (by fun_prop)
  have hay : Integrable (fun z : O => bit z.2.1 * bit z.2.2) μ := by
    apply Integrable.of_mem_Icc 0 1 (by fun_prop)
    filter_upwards with z
    cases z.2.1 <;> cases z.2.2 <;> norm_num [bit]
  rw [integral_prod _ (integrable_causal_pair_numerator (μ.prod μ))]
  have hk (x y : O) : KN x y =
      bit x.2.1 * bit x.2.2 - bit x.2.1 * bit y.2.2 -
        bit y.2.1 * bit x.2.2 + bit y.2.1 * bit y.2.2 := by
    unfold KN
    ring
  simp_rw [hk]
  have hinner (x : O) :
      (∫ y, bit x.2.1 * bit x.2.2 - bit x.2.1 * bit y.2.2 -
        bit y.2.1 * bit x.2.2 + bit y.2.1 * bit y.2.2 ∂μ) =
      bit x.2.1 * bit x.2.2 - bit x.2.1 * (∫ y, bit y.2.2 ∂μ) -
        (∫ y, bit y.2.1 ∂μ) * bit x.2.2 + ∫ y, bit y.2.1 * bit y.2.2 ∂μ := by
    integral_linearity
    simp
  simp_rw [hinner]
  integral_linearity
  simp only [integral_const, probReal_univ, one_smul]
  ring

/-- The conditional numerator is the treatment-response covariance within the actual cell law.  [the theorem's stated inputs and assumptions](hyp:hh,P,hP,j), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:k,hk). -/
-- @node: conditional_cell_numerator_covariance
lemma conditional_cell_numerator_covariance (k : ℕ) (h : ℝ) (hk : 0 < k)
    (hh : 0 < h ∧ h ≤ 1 / 4) (P : CausalLaw) (hP : CompleteModel P) (j : Fin k) :
    nu h k P j =
      2 * ((∫ z, bit z.2.1 * bit z.2.2 ∂conditionalCellLaw h k P j) -
        (∫ z, bit z.2.1 ∂conditionalCellLaw h k P j) *
        (∫ z, bit z.2.2 ∂conditionalCellLaw h k P j)) := by
  let := conditionalCellLaw_probability k h hk hh P hP j
  exact independent_binary_numerator_moment _

/-- The conditional numerator uses the actual design-weighted cell moments, with no density approximation.  [the theorem's stated inputs and assumptions](hyp:hh,P,hP,j), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:k,hk). -/
-- @node: conditional_cell_numerator_design_formula
lemma conditional_cell_numerator_design_formula (k : ℕ) (h : ℝ) (hk : 0 < k)
    (hh : 0 < h ∧ h ≤ 1 / 4) (P : CausalLaw) (hP : CompleteModel P) (j : Fin k) :
    nu h k P j = 2 *
      ((∫ x in cell h k j, P.e x * P.mu1 x ∂PX P) / cellMass h k P j -
        ((∫ x in cell h k j, P.e x ∂PX P) / cellMass h k P j) *
        ((∫ x in cell h k j, (1 - P.e x) * P.mu0 x ∂PX P) / cellMass h k P j +
          (∫ x in cell h k j, P.e x * P.mu1 x ∂PX P) / cellMass h k P j)) := by
  rw [conditional_cell_numerator_covariance k h hk hh P hP j,
    conditional_cell_treated_response_mean k h P hP j,
    conditional_cell_treatment_mean k h P j,
    conditional_cell_response_mean k h hk hh P hP j]

/-- The observed conditional numerator equals the cross-treatment moment of two actual
conditional covariates.  [the theorem's stated inputs and assumptions](hyp:hh,P,hP,j), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:k,hk). -/
-- @node: conditional_cell_numerator_design_pair
lemma conditional_cell_numerator_design_pair (k : ℕ) (h : ℝ) (hk : 0 < k)
    (hh : 0 < h ∧ h ≤ 1 / 4) (P : CausalLaw) (hP : CompleteModel P) (j : Fin k) :
    nu h k P j = ∫ z, designPairNumerator P z
      ∂(conditionalDesignLaw h k P j).prod (conditionalDesignLaw h k P j) := by
  let := conditionalDesignLaw_probability k h hk hh P hP j
  rw [(design_pair_numerator_moment P hP (conditionalDesignLaw h k P j)).2]
  simp only [conditionalDesignLaw_integral]
  exact conditional_cell_numerator_design_formula k h hk hh P hP j

/-- The observed conditional denominator equals the cross-treatment probability for two actual
conditional covariates.  [the theorem's stated inputs and assumptions](hyp:hh,P,hP,j), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:k,hk). -/
-- @node: conditional_cell_denominator_design_pair
lemma conditional_cell_denominator_design_pair (k : ℕ) (h : ℝ) (hk : 0 < k)
    (hh : 0 < h ∧ h ≤ 1 / 4) (P : CausalLaw) (hP : CompleteModel P) (j : Fin k) :
    dj h k P j = ∫ z, designPairDenominator P z
      ∂(conditionalDesignLaw h k P j).prod (conditionalDesignLaw h k P j) := by
  let := conditionalDesignLaw_probability k h hk hh P hP j
  let := conditionalCellLaw_probability k h hk hh P hP j
  rw [(design_pair_denominator_moment P hP (conditionalDesignLaw h k P j)).2,
    dj, independent_binary_denominator_moment, conditional_cell_treatment_mean]
  simp only [conditionalDesignLaw_integral]

/-- The actual conditional cell moments satisfy the paper's complete causal bias bound.  [the theorem's stated inputs and assumptions](hyp:hh,P,hP,j), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:k,hk). -/
-- @node: conditional_cell_bias_bound
lemma conditional_cell_bias_bound (k : ℕ) (h : ℝ) (hk : 0 < k)
    (hh : 0 < h ∧ h ≤ 1 / 4) (P : CausalLaw) (hP : CompleteModel P) (j : Fin k) :
    |nu h k P j - theta P * dj h k P j| ≤ bias h k * dj h k P j := by
  rw [conditional_cell_numerator_design_pair k h hk hh P hP j,
    conditional_cell_denominator_design_pair k h hk hh P hP j]
  exact conditional_design_pair_bias k h hk hh P hP j

/-- Two distinct coordinates of an iid array have the product of the record law as their law.  [the theorem's stated inputs and assumptions](hyp:i,l,hil), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:s,μ). -/
-- @node: iid_pair_coordinates
lemma iid_pair_coordinates (s : ℕ) (μ : Measure O) [IsProbabilityMeasure μ]
    (i l : Fin s) (hil : i ≠ l) :
    MeasurePreserving (fun z : Fin s → O => (z i, z l))
      (Measure.pi (fun _ : Fin s => μ)) (μ.prod μ) := by
  have hind := ProbabilityTheory.iIndepFun_pi
    (μ := fun _ : Fin s => μ) (X := fun _ (z : O) => z)
    (fun _ => measurable_id.aemeasurable)
  have hm := (hind.indepFun hil).map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply l).aemeasurable
  rw [(measurePreserving_eval (fun _ : Fin s => μ) i).map_eq,
    (measurePreserving_eval (fun _ : Fin s => μ) l).map_eq] at hm
  exact ⟨by fun_prop, hm⟩

/-- Every distinct iid coordinate pair has the same integrable kernel moment. The result uses [the stated assumptions](hyp:hil,hK) and establishes [the displayed conclusion](goal). -/
-- @node: iid_pair_kernel_integral
lemma iid_pair_kernel_integral (s : ℕ) (μ : Measure O) [IsProbabilityMeasure μ]
    (i l : Fin s) (hil : i ≠ l) (K : O → O → ℝ)
    (hK : Integrable (fun z : O × O => K z.1 z.2) (μ.prod μ)) :
    Integrable (fun z : Fin s → O => K (z i) (z l)) (Measure.pi (fun _ : Fin s => μ)) ∧
    (∫ z : Fin s → O, K (z i) (z l) ∂Measure.pi (fun _ : Fin s => μ)) =
      ∫ z, K z.1 z.2 ∂μ.prod μ := by
  have hp := iid_pair_coordinates s μ i l hil
  constructor
  · exact hp.integrable_comp_of_integrable hK
  · rw [← hp.map_eq] at hK ⊢
    exact (integral_map hp.measurable.aemeasurable hK.aestronglyMeasurable).symm

/-- At a fixed iid cell count, the count-weighted pair sum has expectation s times the
conditional pair moment; empty and singleton samples contribute zero. The result uses [the stated assumptions](hyp:hK) and establishes [the displayed conclusion](goal). -/
-- @node: iid_pairContribution_expectation
lemma iid_pairContribution_expectation (s : ℕ) (μ : Measure O) [IsProbabilityMeasure μ]
    (K : O → O → ℝ)
    (hK : Integrable (fun z : O × O => K z.1 z.2) (μ.prod μ)) :
    (∫ z : Fin s → O, pairContribution K z ∂Measure.pi (fun _ : Fin s => μ)) =
      (if s < 2 then 0 else (s : ℝ)) * (∫ z, K z.1 z.2 ∂μ.prod μ) := by
  classical
  by_cases hs : s < 2
  · simp [pairContribution, hs]
  have hc : (Nat.choose s 2 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (show 2 ≤ s by omega)).ne'
  have hi (i l : Fin s) : Integrable (fun z : Fin s → O =>
      if i < l then K (z i) (z l) else 0) (Measure.pi (fun _ : Fin s => μ)) := by
    by_cases hil : i < l
    · simpa only [if_pos hil] using (iid_pair_kernel_integral s μ i l hil.ne K hK).1
    · simp only [if_neg hil]
      exact integrable_zero _ _ _
  have hm (i l : Fin s) :
      (∫ z : Fin s → O, (if i < l then K (z i) (z l) else 0)
        ∂Measure.pi (fun _ : Fin s => μ)) =
        (if i < l then (1 : ℝ) else 0) * (∫ z, K z.1 z.2 ∂μ.prod μ) := by
    by_cases hil : i < l
    · simp only [if_pos hil, one_mul]
      exact (iid_pair_kernel_integral s μ i l hil.ne K hK).2
    · simp [hil]
  simp only [pairContribution, if_neg hs]
  rw [integral_const_mul, integral_finset_sum _ (fun i _ =>
    integrable_finset_sum _ (fun l _ => hi i l))]
  simp_rw [integral_finset_sum _ (fun l _ => hi _ l), hm]
  simp_rw [← Finset.sum_mul]
  rw [ordered_pair_count]
  field_simp [hc]

/-- Every numerator cell contribution is integrable under a finite dataset law. [The displayed conclusion](goal) follows. -/
-- @node: integrable_numeratorCell
@[fun_prop] lemma integrable_numeratorCell (n k : ℕ) (h : ℝ) (j : Fin k)
    (Q : Measure (Dataset n)) [IsFiniteMeasure Q] :
    Integrable (fun D => numeratorCell n h k D j) Q := by
  apply Integrable.mono' (integrable_const (μ := Q) (n : ℝ)) (by fun_prop)
  filter_upwards with D
  have hc : cellCount n h k D j ≤ n := by
    simpa only [cellCount, Fintype.card_fin] using
      (Finset.card_le_univ (cellRecords n h k D j))
  simpa only [Real.norm_eq_abs] using
    (cell_contribution_bounds n k h D j).1.trans (by exact_mod_cast hc)

/-- Every denominator cell contribution is integrable under a finite dataset law. [The displayed conclusion](goal) follows. -/
-- @node: integrable_denominatorCell
@[fun_prop] lemma integrable_denominatorCell (n k : ℕ) (h : ℝ) (j : Fin k)
    (Q : Measure (Dataset n)) [IsFiniteMeasure Q] :
    Integrable (fun D => denominatorCell n h k D j) Q := by
  apply Integrable.mono' (integrable_const (μ := Q) (n : ℝ)) (by fun_prop)
  filter_upwards with D
  have hc : cellCount n h k D j ≤ n := by
    simpa only [cellCount, Fintype.card_fin] using
      (Finset.card_le_univ (cellRecords n h k D j))
  simpa only [Real.norm_eq_abs] using
    (cell_contribution_bounds n k h D j).2.trans (by exact_mod_cast hc)

/-- Population statistics sum the cell expectations, without independence between cell counts.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k,h,Q). -/
-- @node: population_cell_sum
lemma population_cell_sum (n k : ℕ) (h : ℝ) (Q : Measure (Dataset n))
    [IsFiniteMeasure Q] :
    Nbar n h k Q = ∑ j : Fin k, ∫ D, numeratorCell n h k D j ∂Q ∧
    Dbar n h k Q = ∑ j : Fin k, ∫ D, denominatorCell n h k D j ∂Q := by
  constructor
  · exact integral_finset_sum _ (fun j _ => integrable_numeratorCell n k h j Q)
  · exact integral_finset_sum _ (fun j _ => integrable_denominatorCell n k h j Q)

/-- Conditional on exact membership labels, the two cell contributions equal the eligible
occupancy times their respective conditional pair moments.  [the theorem's stated inputs and assumptions](hyp:hh,P,hP,j,I), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k,hk). -/
-- @node: conditional_cell_contribution_expectation
lemma conditional_cell_contribution_expectation (n k : ℕ) (h : ℝ) (hk : 2 ≤ k)
    (hh : 0 < h ∧ h ≤ 1 / 4) (P : CausalLaw) (hP : CompleteModel P)
    (j : Fin k) (I : Finset (Fin n)) :
    let Q := ((dataLaw n P) {D | cellRecords n h k D j = I})⁻¹ •
      (dataLaw n P).restrict {D | cellRecords n h k D j = I}
    (∫ D, numeratorCell n h k D j ∂Q) =
      (∫ D, (if cellCount n h k D j < 2 then 0 else
        (cellCount n h k D j : ℝ)) ∂Q) * nu h k P j ∧
    (∫ D, denominatorCell n h k D j ∂Q) =
      (∫ D, (if cellCount n h k D j < 2 then 0 else
        (cellCount n h k D j : ℝ)) ∂Q) * dj h k P j := by
  classical
  dsimp only
  let Q := ((dataLaw n P) {D | cellRecords n h k D j = I})⁻¹ •
    (dataLaw n P).restrict {D | cellRecords n h k D j = I}
  have hp := cell_membership_label_positive n k h hk hh P hP j I
  let : IsProbabilityMeasure Q := conditional_membership_probability n k h P j I hp
  let := conditionalCellLaw_probability k h (by omega) hh P hP j
  let e : Fin I.card ≃ {i // i ∈ I} := (Fintype.equivFinOfCardEq (by simp)).symm
  have hae : ∀ᵐ D ∂Q, cellRecords n h k D j = I :=
    Measure.ae_smul_measure (ae_restrict_mem (measurableSet_cell_membership n k h j I)) _
  have hcount : (∫ D, (if cellCount n h k D j < 2 then 0 else
      (cellCount n h k D j : ℝ)) ∂Q) = if I.card < 2 then 0 else (I.card : ℝ) := by
    calc
      _ = ∫ _D : Dataset n, (if I.card < 2 then 0 else (I.card : ℝ)) ∂Q := by
        apply integral_congr_ae
        filter_upwards [hae] with D hD
        simp only [cellCount, hD]
      _ = _ := by simp
  have hN : (fun D => numeratorCell n h k D j) =ᵐ[Q]
      (fun D => pairContribution KN (fun i => D (e i))) := by
    filter_upwards [hae] with D hD
    rw [(selected_pair_formulas I D e).1]
    simp only [numeratorCell, selectedNumerator, cellCount, cellSum, hD]
  have hD : (fun D => denominatorCell n h k D j) =ᵐ[Q]
      (fun D => pairContribution KD (fun i => D (e i))) := by
    filter_upwards [hae] with D hD
    rw [(selected_pair_formulas I D e).2]
    simp only [denominatorCell, selectedDenominator, cellCount, cellSum, hD]
  change (∫ D, numeratorCell n h k D j ∂Q) = _ ∧
    (∫ D, denominatorCell n h k D j ∂Q) = _
  rw [integral_congr_ae hN, integral_congr_ae hD, hcount]
  constructor
  · exact conditional_selected_pairContribution_expectation n k h P j I hp e KN
      (integrable_causal_pair_numerator _)
  · exact conditional_selected_pairContribution_expectation n k h P j I hp e KD
      (integrable_causal_pair_denominator _)

/-- Integrating a function over all datasets is summing its integrals on the disjoint exact
membership-label events.  [the theorem's stated inputs and assumptions](hyp:μ,f,hf), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k,h,j). -/
-- @node: integral_cell_membership_partition
lemma integral_cell_membership_partition (n k : ℕ) (h : ℝ) (j : Fin k)
    (μ : Measure (Dataset n)) (f : Dataset n → ℝ) (hf : Integrable f μ) :
    (∫ D, f D ∂μ) = ∑ I : Finset (Fin n),
      ∫ D in {D | cellRecords n h k D j = I}, f D ∂μ := by
  have huniv : (⋃ I : Finset (Fin n), {D | cellRecords n h k D j = I}) = Set.univ := by
    ext D
    simp
  rw [← integral_iUnion_fintype
    (fun I => measurableSet_cell_membership n k h j I)
    (fun I J hIJ => Set.disjoint_left.mpr (fun D hI hJ => hIJ (hI.symm.trans hJ)))
    (fun _ => hf.integrableOn), huniv, Measure.restrict_univ]

/-- Undoing normalization multiplies each conditional integral by the probability of its
membership-label event.  [the theorem's stated inputs and assumptions](hyp:hh,P,hP,j,I,f), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k,hk). -/
-- @node: cell_membership_setIntegral_normalize
lemma cell_membership_setIntegral_normalize (n k : ℕ) (h : ℝ) (hk : 2 ≤ k)
    (hh : 0 < h ∧ h ≤ 1 / 4) (P : CausalLaw) (hP : CompleteModel P)
    (j : Fin k) (I : Finset (Fin n)) (f : Dataset n → ℝ) :
    (∫ D in {D | cellRecords n h k D j = I}, f D ∂dataLaw n P) =
      (dataLaw n P).real {D | cellRecords n h k D j = I} *
        ∫ D, f D ∂(((dataLaw n P) {D | cellRecords n h k D j = I})⁻¹ •
          (dataLaw n P).restrict {D | cellRecords n h k D j = I}) := by
  classical
  let : IsProbabilityMeasure (Pobs P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (dataLaw n P) := by unfold dataLaw; infer_instance
  have hp : (dataLaw n P) {D | cellRecords n h k D j = I} ≠ 0 := by
    rw [cell_membership_rectangle, dataLaw, Measure.pi_pi]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact cell_membership_label_positive n k h hk hh P hP j I i
  have hr : (dataLaw n P).real {D | cellRecords n h k D j = I} ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨hp, measure_ne_top _ _⟩
  rw [integral_smul_measure, ENNReal.toReal_inv]
  simp only [smul_eq_mul, ← mul_assoc]
  rw [show ((dataLaw n P) {D | cellRecords n h k D j = I}).toReal =
    (dataLaw n P).real {D | cellRecords n h k D j = I} from rfl,
    mul_inv_cancel₀ hr, one_mul]

/-- The common occupancy weights cancel in the population ratio for every admissible density.  [the theorem's stated inputs and assumptions](hyp:hh,P,Q,hiid,hP), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:n,k,hn,hk). -/
-- @node: lem:occupancy-cancellation
lemma occupancy_cancellation (n k : ℕ) (h : ℝ) (hn : 2 ≤ n) (hk : 2 ≤ k)
    (hh : 0 < h ∧ h ≤ 1 / 4) (P : CausalLaw) (Q : Measure (Dataset n))
    (hiid : IIDSampling n P Q) (hP : CompleteModel P) :
    Nbar n h k Q = ∑ j : Fin k, occupancyWeight n h k P j * nu h k P j ∧
    Dbar n h k Q = ∑ j : Fin k, occupancyWeight n h k P j * dj h k P j ∧
    (∀ j : Fin k, 3/8 ≤ dj h k P j ∧
      |nu h k P j - theta P * dj h k P j| ≤ bias h k * dj h k P j) ∧
    info n h k / 8 ≤ Wocc n h k P ∧ Wocc n h k P ≤ 9*info n h k/2 ∧
    d0 n h k ≤ Dbar n h k Q ∧
    |Nbar n h k Q / Dbar n h k Q - theta P| ≤ bias h k := by
  let : IsProbabilityMeasure (Pobs P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let : IsProbabilityMeasure (dataLaw n P) := by unfold dataLaw; infer_instance
  let : IsProbabilityMeasure Q := hiid.symm ▸ inferInstance
  have hconditional : ∀ j : Fin k,
      (∫ D, numeratorCell n h k D j ∂Q) =
        (∫ D, (if cellCount n h k D j < 2 then 0 else
          (cellCount n h k D j : ℝ)) ∂Q) * nu h k P j ∧
      (∫ D, denominatorCell n h k D j ∂Q) =
        (∫ D, (if cellCount n h k D j < 2 then 0 else
          (cellCount n h k D j : ℝ)) ∂Q) * dj h k P j := by
    intro j
    rw [hiid]
    have hlabel (I : Finset (Fin n)) :=
      conditional_cell_contribution_expectation n k h hk hh P hP j I
    have hlocal (I : Finset (Fin n)) :
        (∫ D in {D | cellRecords n h k D j = I}, numeratorCell n h k D j ∂dataLaw n P) =
          (∫ D in {D | cellRecords n h k D j = I},
            (if cellCount n h k D j < 2 then 0 else (cellCount n h k D j : ℝ))
            ∂dataLaw n P) * nu h k P j ∧
        (∫ D in {D | cellRecords n h k D j = I}, denominatorCell n h k D j ∂dataLaw n P) =
          (∫ D in {D | cellRecords n h k D j = I},
            (if cellCount n h k D j < 2 then 0 else (cellCount n h k D j : ℝ))
            ∂dataLaw n P) * dj h k P j := by
      simp only [cell_membership_setIntegral_normalize n k h hk hh P hP j I]
      rw [(hlabel I).1, (hlabel I).2]
      constructor <;> ring
    rw [integral_cell_membership_partition n k h j _ _
      (integrable_numeratorCell n k h j _),
      integral_cell_membership_partition n k h j _ _
      (integrable_denominatorCell n k h j _),
      integral_cell_membership_partition n k h j _ _
      (integrable_cell_partner_count n k h j _)]
    constructor
    · simp_rw [(hlocal _).1, Finset.sum_mul]
    · simp_rw [(hlocal _).2, Finset.sum_mul]
  have hweight (j : Fin k) :
      (∫ D, (if cellCount n h k D j < 2 then 0 else
        (cellCount n h k D j : ℝ)) ∂Q) = occupancyWeight n h k P j := by
    rw [hiid]
    exact iid_cell_partner_count_expectation n k h P j
  have hpopulation :
      Nbar n h k Q = ∑ j : Fin k, occupancyWeight n h k P j * nu h k P j ∧
      Dbar n h k Q = ∑ j : Fin k, occupancyWeight n h k P j * dj h k P j := by
    obtain ⟨hsN, hsD⟩ := population_cell_sum n k h Q
    constructor
    · rw [hsN]
      apply Finset.sum_congr rfl
      intro j hj
      rw [(hconditional j).1, hweight]
    · rw [hsD]
      apply Finset.sum_congr rfl
      intro j hj
      rw [(hconditional j).2, hweight]
  obtain ⟨hN, hD⟩ := hpopulation
  have hc : ∀ j : Fin k, 3 / 8 ≤ dj h k P j ∧
      |nu h k P j - theta P * dj h k P j| ≤ bias h k * dj h k P j :=
    fun j => ⟨conditional_cell_denominator_lower k h (by omega) hh P hP j,
      conditional_cell_bias_bound k h (by omega) hh P hP j⟩
  obtain ⟨hWlo, hWhi⟩ := occupancy_comparisons n k h hn (by omega) hh P hP
  obtain ⟨hfloor, hbias⟩ := occupancy_ratio_assembly n k h P Q
    (by omega) (by omega) hh.1 hN hD hc hWlo
  exact ⟨hN, hD, hc, hWlo, hWhi, hfloor, hbias⟩
end CausalSmith.Stat.PrivateCateRoughdesign
