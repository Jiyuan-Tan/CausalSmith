module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.ScoreMean
public import Mathlib.Probability.Moments.Variance

/-!
# Independent audit noise and conditional second moments
-/

public section

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A numeric Bernoulli mark has variance q(1-q).  [For the stated data and conditions](hyp:q,hq), [the stated conclusion holds](goal). -/
-- @node: variance_bernoulli_treatment
lemma variance_bernoulli_treatment (q : ℝ) (hq : q ∈ Set.Icc 0 1) :
    variance treatment (bernoulliLaw q) = q * (1 - q) := by
  let := bernoulliLaw_probability q hq
  rw [variance_eq_sub (show MemLp treatment 2 (bernoulliLaw q) from MemLp.of_discrete)]
  have he : bernoulliLaw q = Causalean.Mathlib.Probability.bernoulliBool q := by
    unfold bernoulliLaw Causalean.Mathlib.Probability.bernoulliBool
    exact add_comm _ _
  rw [he]
  rw [Causalean.Mathlib.Probability.bernoulliBool_integral hq.1 hq.2,
    Causalean.Mathlib.Probability.bernoulliBool_integral hq.1 hq.2]
  norm_num [treatment, Pi.pow_apply]
  ring

/-- Independent centered audit marks have a diagonal weighted variance.  [For the stated data and conditions](hyp:q,hq,c), [the stated conclusion holds](goal). -/
-- @node: variance_weighted_audit_marks
lemma variance_weighted_audit_marks (q : ℝ) (hq : q ∈ Set.Icc 0 1)
    (c : OffDiag V → ℝ) :
    variance (fun w : Audit V => ∑ e, c e * (treatment (w e) - q)) (auditLaw V q) =
      q * (1 - q) * ∑ e, (c e) ^ 2 := by
  let := bernoulliLaw_probability q hq
  have hs := variance_sum_pi (μ := fun _ : OffDiag V => bernoulliLaw q)
    (X := fun e b => c e * (treatment b - q))
    (fun _ => (show MemLp _ 2 _ from MemLp.of_discrete))
  have hs' : variance (fun w : Audit V => ∑ e, c e * (treatment (w e) - q))
      (auditLaw V q) = ∑ e, variance (fun b => c e * (treatment b - q)) (bernoulliLaw q) := by
    convert hs using 1
    congr 1
    funext w
    simp
  rw [hs']
  simp_rw [variance_const_mul,
    variance_sub_const (show AEStronglyMeasurable treatment (bernoulliLaw q) from by fun_prop),
    variance_bernoulli_treatment q hq]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

/-- An off-diagonal label sum can be organized by recipient and source.  [For the stated data and conditions](hyp:f), [the stated conclusion holds](goal). -/
-- @node: sum_offDiag_by_recipient
lemma sum_offDiag_by_recipient (f : OffDiag V → ℝ) :
    (∑ e, f e) = ∑ i : V, ∑ j : V, if hji : j ≠ i then f ⟨(j, i), hji⟩ else 0 := by
  let g : V × V → ℝ := fun e => if he : e.1 ≠ e.2 then f ⟨e, he⟩ else 0
  have ht : (∑ e, f e) = ∑ e : V × V, g e := by
    calc
      (∑ e, f e) = ∑ e : OffDiag V, g e.val := by
        apply Finset.sum_congr rfl
        intro e _
        simp only [g, dif_pos e.property]
      _ = ∑ e ∈ Finset.univ.filter (fun e : V × V => e.1 ≠ e.2), g e :=
        (Finset.sum_subtype _ (by simp) g).symm
      _ = ∑ e : V × V, g e := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro e _
        by_cases he : e.1 ≠ e.2 <;> simp [g, he]
  rw [ht, Fintype.sum_prod_type_right]

/-- The recorded-neighbor sum is the true-edge sum multiplied by numeric marks.  [For the stated data and conditions](hyp:θ,z,w,i), [the stated conclusion holds](goal). -/
-- @node: recorded_sign_sum_eq_mark_sum
lemma recorded_sign_sum_eq_mark_sum (θ : Schedule V) (z : Assign V) (w : Audit V) (i : V) :
    (∑ j ∈ recordedNbhd (recordOf θ (z, w)).1 i, signOf (z j)) =
      ∑ j : V, if he : θ.edge j i then
        treatment (w ⟨(j, i), by
          intro hji; change j = i at hji; subst j; exact θ.irrefl i he⟩) *
          signOf (z j) else 0 := by
  simp only [recordedNbhd]
  rw [Finset.sum_filter]
  dsimp only [recordOf]
  apply Finset.sum_congr rfl
  intro j _
  by_cases he : θ.edge j i
  · have hji : j ≠ i := by intro hji; change j = i at hji; subst j; exact θ.irrefl i he
    cases hw : w ⟨(j, i), hji⟩ <;> simp [he, hji, hw, treatment]
  · simp [he]

/-- The audit error is a weighted sum of independent centered true-edge marks.  [For the stated data and conditions](hyp:θ,q,hq,z,w), [the stated conclusion holds](goal). -/
-- @node: auditScore_sub_oracle_eq_noise
lemma auditScore_sub_oracle_eq_noise (θ : Schedule V) (q : ℝ) (hq : q ≠ 0)
    (z : Assign V) (w : Audit V) :
    auditScore q (recordOf θ (z, w)) - oracleScore θ z =
      (2 / (Fintype.card V : ℝ) / q) * ∑ e : OffDiag V,
        (if θ.edge e.1.1 e.1.2 then potentialOutcome θ e.1.2 z * signOf (z e.1.1)
          else 0) * (treatment (w e) - q) := by
  rw [sum_offDiag_by_recipient]
  simp only [auditScore, oracleScore]
  change (2 / (Fintype.card V : ℝ)) *
    (∑ i, potentialOutcome θ i z * (signOf (z i) + q⁻¹ *
      ∑ j ∈ recordedNbhd (recordOf θ (z, w)).1 i, signOf (z j))) - _ = _
  simp_rw [recorded_sign_sum_eq_mark_sum]
  rw [← mul_sub, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [show potentialOutcome θ i z * (signOf (z i) + q⁻¹ *
      ∑ j, if he : θ.edge j i then
        treatment (w ⟨(j, i), by
          intro hji; change j = i at hji; subst j; exact θ.irrefl i he⟩) * signOf (z j)
        else 0) - potentialOutcome θ i z *
      (signOf (z i) + ∑ j ∈ inNbhd θ i, signOf (z j)) =
      potentialOutcome θ i z * (q⁻¹ *
        (∑ j, if he : θ.edge j i then
          treatment (w ⟨(j, i), by
            intro hji; change j = i at hji; subst j; exact θ.irrefl i he⟩) * signOf (z j)
          else 0) - ∑ j ∈ inNbhd θ i, signOf (z j)) by ring]
  simp only [inNbhd, Finset.sum_filter]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases he : θ.edge j i
  · have hji : j ≠ i := fun hji => θ.irrefl i (hji ▸ he)
    simp only [dif_pos he, if_pos he, dif_pos hji]
    field_simp
  · by_cases hji : j ≠ i <;> simp [he, hji]

/-- Squared noise weights sum to the in-degree weighted squared outcomes.  [For the stated data and conditions](hyp:θ,z), [the stated conclusion holds](goal). -/
-- @node: audit_noise_weights_sq
lemma audit_noise_weights_sq (θ : Schedule V) (z : Assign V) :
    (∑ e : OffDiag V,
      (if θ.edge e.1.1 e.1.2 then potentialOutcome θ e.1.2 z * signOf (z e.1.1)
        else 0) ^ 2) = ∑ i, (inNbhd θ i).card * (potentialOutcome θ i z) ^ 2 := by
  rw [sum_offDiag_by_recipient]
  apply Finset.sum_congr rfl
  intro i _
  have hp : (∑ j : V, if hji : j ≠ i then
      (if θ.edge j i then potentialOutcome θ i z * signOf (z j) else 0) ^ 2 else 0) =
      ∑ j ∈ inNbhd θ i, (potentialOutcome θ i z) ^ 2 := by
    rw [inNbhd, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    by_cases he : θ.edge j i
    · have hji : j ≠ i := fun hji => θ.irrefl i (hji ▸ he)
      cases z j <;> simp [he, hji, signOf]
    · by_cases hji : j ≠ i <;> simp [he, hji]
  rw [hp, Finset.sum_const, nsmul_eq_mul]

/-- Conditional audit variance follows from the diagonal centered-mark calculation.  [For the stated data and conditions](hyp:θ,q,hq,hq0,hn,z), [the stated conclusion holds](goal). -/
-- @node: variance_auditScore_given_assignment
lemma variance_auditScore_given_assignment (θ : Schedule V) (q : ℝ)
    (hq : q ∈ Set.Icc 0 1) (hq0 : 0 < q) (hn : 0 < Fintype.card V) (z : Assign V) :
    variance (fun w => auditScore q (recordOf θ (z, w))) (auditLaw V q) =
      4 * (1 - q) / ((Fintype.card V : ℝ) ^ 2 * q) *
        ∑ i, (inNbhd θ i).card * (potentialOutcome θ i z) ^ 2 := by
  let := auditLaw_probability (V := V) q hq
  have he : (fun w => auditScore q (recordOf θ (z, w)) - oracleScore θ z) =
      fun w => (2 / (Fintype.card V : ℝ) / q) * ∑ e : OffDiag V,
        (if θ.edge e.1.1 e.1.2 then potentialOutcome θ e.1.2 z * signOf (z e.1.1)
          else 0) * (treatment (w e) - q) := by
    funext w
    exact auditScore_sub_oracle_eq_noise θ q (ne_of_gt hq0) z w
  rw [← variance_sub_const (show AEStronglyMeasurable
    (fun w => auditScore q (recordOf θ (z, w))) (auditLaw V q) from
      (show MemLp _ 2 _ from MemLp.of_discrete).aestronglyMeasurable)
    (oracleScore θ z), he, variance_const_mul, variance_weighted_audit_marks q hq,
    audit_noise_weights_sq]
  have hn0 : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp
  ring

/-- Integrating the conditional variance adds the oracle squared conditional mean.  [For the stated data and conditions](hyp:θ,q,hq,hq0,hn,z), [the stated conclusion holds](goal). -/
-- @node: integral_auditScore_sq_given_assignment
lemma integral_auditScore_sq_given_assignment (θ : Schedule V) (q : ℝ)
    (hq : q ∈ Set.Icc 0 1) (hq0 : 0 < q) (hn : 0 < Fintype.card V) (z : Assign V) :
    (∫ w, (auditScore q (recordOf θ (z, w))) ^ 2 ∂auditLaw V q) =
      (oracleScore θ z) ^ 2 +
      4 * (1 - q) / ((Fintype.card V : ℝ) ^ 2 * q) *
        ∑ i, (inNbhd θ i).card * (potentialOutcome θ i z) ^ 2 := by
  let := auditLaw_probability (V := V) q hq
  have hv := variance_auditScore_given_assignment θ q hq hq0 hn z
  rw [variance_eq_sub (show MemLp _ 2 _ from MemLp.of_discrete),
    integral_auditScore_given_assignment θ q hq hq0 z] at hv
  change (∫ w, (auditScore q (recordOf θ (z, w))) ^ 2 ∂auditLaw V q) -
    (oracleScore θ z) ^ 2 = _ at hv
  linarith

/-- The full assignment-audit variance is the oracle variance plus the expected audit variance.  [For the stated data and conditions](hyp:D,θ,q,hn,ha,hw,hi,hq), [the stated conclusion holds](goal). -/
-- @node: variance_auditScore_eq_oracle_add
lemma variance_auditScore_eq_oracle_add (D : Measure (Assign V × Audit V))
    (θ : Schedule V) (q : ℝ) (hn : 0 < Fintype.card V)
    (ha : AssignmentLaw D) (hw : AuditLaw D q) (hi : DesignIndependent D) (hq : 0 < q) :
    variance (fun ω => auditScore q (recordOf θ ω)) D =
      variance (oracleScore θ) (halfBernoulli V) +
        4 * (1 - q) / ((Fintype.card V : ℝ) ^ 2 * q) *
          ∑ i, (inNbhd θ i).card *
            ∫ z, (potentialOutcome θ i z) ^ 2 ∂halfBernoulli V := by
  let := design_isProbabilityMeasure D q ha hw hi
  let := halfBernoulli_probability (V := V)
  let := auditLaw_probability (V := V) q ⟨hw.1, hw.2.1⟩
  rw [variance_eq_sub (show MemLp _ 2 D from MemLp.of_discrete),
    integral_auditScore_eq_tte D θ q ha hw hi hq,
    variance_eq_sub (show MemLp _ 2 (halfBernoulli V) from MemLp.of_discrete),
    integral_oracleScore_eq_tte]
  have hs : (∫ ω, (auditScore q (recordOf θ ω)) ^ 2 ∂D) =
      (∫ z, (oracleScore θ z) ^ 2 ∂halfBernoulli V) +
        4 * (1 - q) / ((Fintype.card V : ℝ) ^ 2 * q) *
          ∑ i, (inNbhd θ i).card *
            ∫ z, (potentialOutcome θ i z) ^ 2 ∂halfBernoulli V := by
    rw [design_eq_thinnedDesign D q ha hw hi, thinnedDesign,
      integral_prod _ (show Integrable _ _ from Integrable.of_finite)]
    simp_rw [integral_auditScore_sq_given_assignment θ q ⟨hw.1, hw.2.1⟩ hq hn]
    rw [integral_add (halfBernoulli_integrable _) (halfBernoulli_integrable _),
      integral_const_mul, integral_finsetSum _ (fun _ _ => halfBernoulli_integrable _)]
    simp_rw [integral_const_mul]
  change (∫ ω, (auditScore q (recordOf θ ω)) ^ 2 ∂D) - (tte θ) ^ 2 =
    (∫ z, (oracleScore θ z) ^ 2 ∂halfBernoulli V) - (tte θ) ^ 2 + _
  rw [hs]
  ring

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
