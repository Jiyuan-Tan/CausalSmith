module
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Estimators
public import CausalSmith.Experimentation.EXP_NoisygraphTtePrecision_Research.Helpers.DesignBridge
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.OracleVariance
public import Mathlib.Probability.Moments.Variance

/-!
# Conditional inverse-channel score moments

The inverse-channel score is unbiased. Its exact variance is obtained from
independent acquisition coordinates, their Bernoulli variances, and the
finite-product second-moment decomposition over assignment and acquisition.
-/

public section

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory
namespace CausalSmith.Experimentation.NoisygraphTtePrecision
attribute [local instance] Classical.propDecidable
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.style.whitespace false

variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Given [the stated assumptions](hyp:hqr), [The mean numeric report at an arrow label is its channel probability.](goal) -/
-- @node: integral_acquisition_report
lemma integral_acquisition_report (η : Schedule V) (q r : ℝ)
    (hqr : ChannelDomain q r) (e : OffDiag V) :
    (∫ H, (if H e then (1 : ℝ) else 0) ∂acquisitionLaw η q r) =
      if η.edge e.1.1 e.1.2 then q else r := by
  have hp (e : OffDiag V) : (if η.edge e.1.1 e.1.2 then q else r) ∈ Set.Icc 0 1 := by
    split_ifs
    · exact ⟨hqr.1.trans hqr.2.1, hqr.2.2⟩
    · exact ⟨hqr.1, hqr.2.1.trans hqr.2.2⟩
  let : ∀ e : OffDiag V, IsProbabilityMeasure
      (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw
        (if η.edge e.1.1 e.1.2 then q else r)) := fun e =>
    CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw_probability _ (hp e)
  unfold acquisitionLaw
  rw [integral_comp_eval (μ := fun e : OffDiag V =>
    CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw
      (if η.edge e.1.1 e.1.2 then q else r)) (i := e) (f := fun b : Bool => if b then (1 : ℝ) else 0)
    (by fun_prop)]
  rw [show CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw
      (if η.edge e.1.1 e.1.2 then q else r) =
      Causalean.Mathlib.Probability.bernoulliBool
        (if η.edge e.1.1 e.1.2 then q else r) from add_comm _ _]
  rw [Causalean.Mathlib.Probability.bernoulliBool_integral (hp e).1 (hp e).2]
  simp

/-- Given [the stated assumptions](hyp:hqr,hrq), [The conditional acquisition mean is the supplied-graph score.](goal) -/
-- @node: rawScore_given_assignment
lemma rawScore_given_assignment (η : Schedule V) (q r : ℝ) (hqr : ChannelDomain q r)
    (hrq : r < q) (z : Assign V) :
    (∫ H, rawScore q r (recordOf η (z,H)) ∂acquisitionLaw η q r) = CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.oracleScore η z := by
  let := acquisitionLaw_probability q r hqr η
  have hint (f : Acq V → ℝ) : Integrable f (acquisitionLaw η q r) := by
    fun_prop
  unfold rawScore
  dsimp only [recordOf]
  simp only [if_pos hrq]
  rw [integral_const_mul, integral_finsetSum _ (fun _ _ => hint _)]
  unfold CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.oracleScore
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul, integral_add (hint _) (hint _), integral_const,
    probReal_univ, one_smul, integral_finsetSum _ (fun _ _ => hint _)]
  congr 2
  rw [CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.inNbhd,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hji : j ≠ i
  · simp only [dif_pos hji]
    change (∫ H, ((if H ⟨(j,i), hji⟩ then (1 : ℝ) else 0) - r) *
      signOf (z j) / (q-r) ∂acquisitionLaw η q r) =
      if η.edge j i then signOf (z j) else 0
    integral_linearity
    rw [integral_acquisition_report η q r hqr ⟨(j,i), hji⟩, integral_const, probReal_univ, one_smul]
    by_cases he : η.edge j i
    · simp only [if_pos he]
      exact mul_div_cancel_left₀ _ (sub_ne_zero.mpr (ne_of_gt hrq))
    · simp [he]
  · have he : ¬ η.edge j i := by
      have h : j = i := not_ne_iff.mp hji
      subst j
      exact η.irrefl i
    simp [hji, he]

/-- Given [the stated assumptions](hyp:hqr,hrq,ha,hH,hi), [The centered score is unbiased under every design with the three atoms.](goal) -/
-- @node: integral_rawScore_eq_tte
lemma integral_rawScore_eq_tte (η : Schedule V) (q r : ℝ) (hqr : ChannelDomain q r)
    (hrq : r < q) (D : Design V) (ha : AssignmentLaw D) (hH : AcquisitionLaw D q r)
    (hi : DesignIndependent D) :
    (∫ ω, rawScore q r (recordOf η ω) ∂D η) = CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.tte η := by
  rw [design_eq_noisyDesign D q r ha hH hi]
  let := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.halfBernoulli_probability (V := V)
  let := acquisitionLaw_probability q r hqr η
  rw [noisyDesign, integral_prod _ (show Integrable _ _ from Integrable.of_finite)]
  simp_rw [rawScore_given_assignment η q r hqr hrq]
  exact CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.integral_oracleScore_eq_tte η

/-- [Reindex all off-diagonal arrows by their recipient and donor labels.](goal) -/
-- @node: sum_offDiag_by_recipient
lemma sum_offDiag_by_recipient (f : OffDiag V → ℝ) :
    (∑ e, f e) = ∑ i : V, ∑ j : V, if h : j ≠ i then f ⟨(j,i), h⟩ else 0 := by
  rw [← Finset.sum_comm]
  simp only [OffDiag]
  have hp := Fintype.sum_prod_type
    (fun e : V × V => if h : e.1 ≠ e.2 then f ⟨e, h⟩ else 0)
  rw [← hp]
  let g := fun e : V × V => if h : e.1 ≠ e.2 then f ⟨e,h⟩ else 0
  have hfilter : (∑ e ∈ Finset.univ.filter (fun e : V × V => e.1 ≠ e.2), g e) =
      ∑ e : V × V, g e := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro e _ he
    have heq : e.1 = e.2 := by simpa using he
    simp [g, heq]
  rw [← hfilter]
  symm
  apply Finset.sum_bij (fun e he => ⟨e, (Finset.mem_filter.mp he).2⟩)
  · intro e he; simp
  · intro e he e' he' h; exact congrArg Subtype.val h
  · intro e he
    exact ⟨e.1, by simp [e.2], rfl⟩
  · intro e he
    simp [g, (Finset.mem_filter.mp he).2]

/-- Given [the stated assumptions](hyp:hp), [A numeric Bernoulli report has variance p(1-p), including both endpoints.](goal) -/
-- @node: bernoulli_report_variance
lemma bernoulli_report_variance (p : ℝ) (hp : p ∈ Set.Icc 0 1) :
    ProbabilityTheory.variance (fun b : Bool => if b then (1 : ℝ) else 0)
      (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw p) = p*(1-p) := by
  let := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw_probability p hp
  rw [ProbabilityTheory.variance_eq_sub MemLp.of_discrete]
  rw [show CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw p =
      Causalean.Mathlib.Probability.bernoulliBool p from add_comm _ _]
  rw [Causalean.Mathlib.Probability.bernoulliBool_integral hp.1 hp.2,
    Causalean.Mathlib.Probability.bernoulliBool_integral hp.1 hp.2]
  simp
  <;> ring

/-- Given [the stated assumptions](hyp:hrq), [At a fixed assignment the score is a constant plus a sum of coordinate marks.](goal) -/
-- @node: rawScore_coordinate_sum
lemma rawScore_coordinate_sum (η : Schedule V) (q r : ℝ) (hrq : r < q)
    (z : Assign V) (H : Acq V) :
    rawScore q r (recordOf η (z,H)) = (2 / (Fintype.card V : ℝ)) *
      ((∑ i, CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.potentialOutcome η i z * signOf (z i)) +
       ∑ e : OffDiag V,
         (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.potentialOutcome η e.1.2 z *
           signOf (z e.1.1) / (q-r)) * ((if H e then 1 else 0)-r)) := by
  rw [sum_offDiag_by_recipient]
  simp only [rawScore, if_pos hrq, recordOf]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> (try simp_all only [Bool.false_eq_true, ↓reduceIte]) <;> ring

/-- Given [the stated assumptions](hyp:hqr,hrq), [Independence of acquisition coordinates gives the fixed-assignment score variance.](goal) -/
-- @node: rawScore_acquisition_variance
lemma rawScore_acquisition_variance (η : Schedule V) (q r : ℝ)
    (hqr : ChannelDomain q r) (hrq : r < q) (z : Assign V) :
    ProbabilityTheory.variance (fun H => rawScore q r (recordOf η (z,H)))
      (acquisitionLaw η q r) =
      (2 / (Fintype.card V : ℝ))^2 * ∑ e : OffDiag V,
        (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.potentialOutcome η e.1.2 z)^2 /
          (q-r)^2 *
          (if η.edge e.1.1 e.1.2 then q*(1-q) else r*(1-r)) := by
  have hp (e : OffDiag V) : (if η.edge e.1.1 e.1.2 then q else r) ∈ Set.Icc 0 1 := by
    split_ifs
    · exact ⟨hqr.1.trans hqr.2.1, hqr.2.2⟩
    · exact ⟨hqr.1, hqr.2.1.trans hqr.2.2⟩
  letI := acquisitionLaw_probability q r hqr η
  letI : ∀ e : OffDiag V, IsProbabilityMeasure
      (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw
        (if η.edge e.1.1 e.1.2 then q else r)) := fun e =>
    CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.bernoulliLaw_probability _ (hp e)
  simp_rw [rawScore_coordinate_sum η q r hrq z]
  rw [ProbabilityTheory.variance_const_mul,
    ProbabilityTheory.variance_const_add (by fun_prop)]
  unfold acquisitionLaw
  rw [show (fun H : Acq V => ∑ e : OffDiag V,
      (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.potentialOutcome η e.1.2 z *
        signOf (z e.1.1) / (q-r)) * ((if H e then 1 else 0)-r)) =
      ∑ e : OffDiag V, fun H : Acq V =>
      (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.potentialOutcome η e.1.2 z *
        signOf (z e.1.1) / (q-r)) * ((if H e then 1 else 0)-r) by ext H; simp]
  rw [ProbabilityTheory.variance_sum_pi (X := fun (e : OffDiag V) (b : Bool) =>
    (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.potentialOutcome η e.1.2 z *
      signOf (z e.1.1) / (q-r)) * ((if b then 1 else 0)-r))
    (fun _ => MemLp.of_discrete)]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  rw [ProbabilityTheory.variance_const_mul,
    ProbabilityTheory.variance_sub_const (by fun_prop), bernoulli_report_variance _ (hp e)]
  have hs : signOf (z e.1.1)^2 = 1 := by cases z e.1.1 <;> norm_num [signOf, CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.signOf]
  rw [div_pow, mul_pow, hs, mul_one]
  split_ifs <;> rfl

/-- [Summing local channel variances counts true donors and the remaining off-diagonal donors.](goal) -/
-- @node: sum_channel_variances_row
lemma sum_channel_variances_row (η : Schedule V) (i : V) (q r : ℝ) :
    (∑ j : V, if j ≠ i then
      (if η.edge j i then q*(1-q) else r*(1-r)) else 0) =
    ((CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.inNbhd η i).card : ℝ)*q*(1-q) +
      ((Fintype.card V : ℝ)-1-
        (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.inNbhd η i).card)*r*(1-r) := by
  have hterm (j : V) : (if j ≠ i then
      (if η.edge j i then q*(1-q) else r*(1-r)) else 0) =
      (if η.edge j i then q*(1-q)-r*(1-r) else 0) + r*(1-r) -
        (if j = i then r*(1-r) else 0) := by
    by_cases hji : j = i
    · subst j; simp [η.irrefl i]
    · by_cases he : η.edge j i <;> simp [hji, he]
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hedge : (∑ j : V, if η.edge j i then q*(1-q)-r*(1-r) else 0) =
      ((CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.inNbhd η i).card : ℝ) *
        (q*(1-q)-r*(1-r)) := by
    rw [← Finset.sum_filter]
    simp [CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.inNbhd]
    <;> ring
  rw [hedge]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/-- [The finite-product variance decomposition follows by integrating second moments.](goal) -/
-- @node: finite_product_variance_decomposition
lemma finite_product_variance_decomposition {A B : Type*}
    [Fintype A] [Fintype B] [MeasurableSpace A] [MeasurableSpace B]
    [DiscreteMeasurableSpace A] [DiscreteMeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : A × B → ℝ) :
    ProbabilityTheory.variance f (μ.prod ν) =
      ProbabilityTheory.variance (fun a => ∫ b, f (a,b) ∂ν) μ +
        ∫ a, ProbabilityTheory.variance (fun b => f (a,b)) ν ∂μ := by
  rw [ProbabilityTheory.variance_eq_sub MemLp.of_discrete,
    ProbabilityTheory.variance_eq_sub MemLp.of_discrete]
  simp_rw [ProbabilityTheory.variance_eq_sub MemLp.of_discrete]
  rw [integral_sub Integrable.of_finite Integrable.of_finite]
  rw [integral_prod _ Integrable.of_finite, integral_prod _ Integrable.of_finite]
  simp only [Pi.pow_apply]
  ring

/-- Given [the stated assumptions](hyp:hqr,hrq,ha,hH,hi), [The acquisition variance separates the true-arrow and non-arrow Bernoulli costs.](goal) -/
-- @node: rawScore_variance
lemma rawScore_variance (η : Schedule V) (q r : ℝ) (hqr : ChannelDomain q r)
    (hrq : r < q) (D : Design V) (ha : AssignmentLaw D) (hH : AcquisitionLaw D q r)
    (hi : DesignIndependent D) :
    ProbabilityTheory.variance (fun ω => rawScore q r (recordOf η ω)) (D η) =
      ProbabilityTheory.variance (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.oracleScore η) (CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.halfBernoulli V) +
      4 / ((Fintype.card V : ℝ)^2 * (q-r)^2) * ∑ i,
        (∫ z, CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.potentialOutcome η i z ^ 2 ∂CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.halfBernoulli V) *
        (((CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.inNbhd η i).card : ℝ)*q*(1-q) +
          ((Fintype.card V : ℝ)-1-(CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.inNbhd η i).card)*r*(1-r)) := by
  rw [design_eq_noisyDesign D q r ha hH hi]
  letI := CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.halfBernoulli_probability (V := V)
  letI := acquisitionLaw_probability q r hqr η
  rw [noisyDesign, finite_product_variance_decomposition]
  simp_rw [rawScore_given_assignment η q r hqr hrq,
    rawScore_acquisition_variance η q r hqr hrq]
  congr 1
  rw [integral_const_mul, integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  simp_rw [div_mul_eq_mul_div, integral_div, integral_mul_const]
  rw [sum_offDiag_by_recipient]
  have hrow (i : V) :
      (∑ j : V, if h : j ≠ i then
        (∫ z, CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.potentialOutcome η i z ^ 2
          ∂CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.halfBernoulli V) *
          (if η.edge j i then q*(1-q) else r*(1-r)) / (q-r)^2 else 0) =
      (∫ z, CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.potentialOutcome η i z ^ 2
        ∂CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.halfBernoulli V) / (q-r)^2 *
        (((CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.inNbhd η i).card : ℝ)*q*(1-q) +
          ((Fintype.card V : ℝ)-1-(CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier.inNbhd η i).card)*r*(1-r)) := by
    rw [← sum_channel_variances_row η i q r, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  simp_rw [hrow]
  rw [div_pow]
  simp only [show (2 : ℝ)^2 = 4 by norm_num]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end CausalSmith.Experimentation.NoisygraphTtePrecision
