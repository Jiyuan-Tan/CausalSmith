module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.DesignBridge

/-!
# Assignment moments and conditional audit means
-/

public section

open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The assignment law is a probability measure.  [the stated conclusion holds](goal). -/
-- @node: halfBernoulli_probability
lemma halfBernoulli_probability : IsProbabilityMeasure (halfBernoulli V) := by
  let : IsProbabilityMeasure (bernoulliLaw (1 / 2)) :=
    bernoulliLaw_probability _ (by constructor <;> norm_num)
  unfold halfBernoulli
  infer_instance

/-- Every real statistic on the finite assignment space is integrable.  [For the stated data and conditions](hyp:f), [the stated conclusion holds](goal). -/
-- @node: halfBernoulli_integrable
lemma halfBernoulli_integrable (f : Assign V → ℝ) : Integrable f (halfBernoulli V) := by
  let := halfBernoulli_probability (V := V)
  exact Integrable.of_finite

/-- A half-Bernoulli centered sign has mean zero.  [For the stated data and conditions](hyp:j), [the stated conclusion holds](goal). -/
-- @node: integral_signOf_halfBernoulli
lemma integral_signOf_halfBernoulli (j : V) :
    (∫ z, signOf (z j) ∂halfBernoulli V) = 0 := by
  have he : (fun z : Assign V => signOf (z j)) =
      fun z => 2 * Causalean.Experimentation.DesignBased.centeredMonomial
        (fun _ : V => (1 / 2 : ℝ)) {j} z := by
    funext z
    cases hz : z j <;>
      simp [Causalean.Experimentation.DesignBased.centeredMonomial,
        Causalean.Experimentation.DesignBased.treatInd, signOf, hz] <;> norm_num
  rw [he, integral_halfBernoulli_eq_bernoulliDesign_E,
    Causalean.Experimentation.DesignBased.FiniteDesign.E_const_mul,
    Causalean.Experimentation.DesignBased.bernoulliDesign_E_centeredMonomial]
  simp

/-- Pairing a treatment indicator with a sign isolates its own coordinate.  [For the stated data and conditions](hyp:k,j), [the stated conclusion holds](goal). -/
-- @node: integral_treatment_mul_signOf
lemma integral_treatment_mul_signOf (k j : V) :
    (∫ z, treatment (z k) * signOf (z j) ∂halfBernoulli V) =
      if k = j then (1 / 2 : ℝ) else 0 := by
  have he : (fun z : Assign V => treatment (z k) * signOf (z j)) =
      fun z => 2 * (Causalean.Experimentation.DesignBased.centeredMonomial
        (fun _ : V => (1 / 2 : ℝ)) {j} z *
          ∏ l ∈ ({k} : Finset V), Causalean.Experimentation.DesignBased.treatInd l z) := by
    funext z
    cases hk : z k <;> cases hj : z j <;>
      simp [Causalean.Experimentation.DesignBased.centeredMonomial,
        Causalean.Experimentation.DesignBased.treatInd, signOf, treatment, hk, hj] <;>
      norm_num
  rw [he, integral_halfBernoulli_eq_bernoulliDesign_E,
    Causalean.Experimentation.DesignBased.FiniteDesign.E_const_mul,
    Causalean.Experimentation.DesignBased.bernoulliDesign_E_centeredMonomial_mul_treatInd_prod]
  by_cases h : k = j
  · subst k; norm_num
  · simp [h, Ne.symm h]

/-- A row outcome paired with a sign has half its corresponding additive coefficient.  [For the stated data and conditions](hyp:θ,i,j), [the stated conclusion holds](goal). -/
-- @node: integral_potentialOutcome_mul_signOf
lemma integral_potentialOutcome_mul_signOf (θ : Schedule V) (i j : V) :
    (∫ z, potentialOutcome θ i z * signOf (z j) ∂halfBernoulli V) =
      (θ.t i * (if i = j then 1 else 0) +
        ∑ k ∈ inNbhd θ i, θ.b i k * (if k = j then 1 else 0)) / 2 := by
  simp_rw [potentialOutcome, add_mul, Finset.sum_mul, mul_assoc]
  rw [integral_add (halfBernoulli_integrable _) (halfBernoulli_integrable _),
    integral_add (halfBernoulli_integrable _) (halfBernoulli_integrable _),
    integral_const_mul, integral_signOf_halfBernoulli, mul_zero, zero_add,
    integral_const_mul, integral_treatment_mul_signOf,
    integral_finsetSum _ (fun _ _ => halfBernoulli_integrable _)]
  simp_rw [integral_const_mul, integral_treatment_mul_signOf]
  simp only [div_eq_mul_inv, add_mul, Finset.sum_mul]
  congr 1
  · split <;> ring
  · apply Finset.sum_congr rfl
    intro k _
    split <;> ring

/-- Orthogonal sign moments identify the oracle score's constant term with the causal target.  [For the stated data and conditions](hyp:θ), [the stated conclusion holds](goal). -/
-- @node: integral_oracleScore_eq_tte
lemma integral_oracleScore_eq_tte (θ : Schedule V) :
    (∫ z, oracleScore θ z ∂halfBernoulli V) = tte θ := by
  unfold oracleScore
  rw [integral_const_mul, integral_finsetSum _ (fun _ _ => halfBernoulli_integrable _)]
  have hrow (i : V) :
      (∫ z, potentialOutcome θ i z * (signOf (z i) +
        ∑ j ∈ inNbhd θ i, signOf (z j)) ∂halfBernoulli V) =
          (θ.t i + ∑ j ∈ inNbhd θ i, θ.b i j) / 2 := by
    simp_rw [mul_add, Finset.mul_sum]
    rw [integral_add (halfBernoulli_integrable _) (halfBernoulli_integrable _),
      integral_finsetSum _ (fun _ _ => halfBernoulli_integrable _)]
    simp_rw [integral_potentialOutcome_mul_signOf]
    have hii : i ∉ inNbhd θ i := by simp [inNbhd, θ.irrefl i]
    simp only [ite_true, mul_one]
    simp_rw [mul_ite, mul_one, mul_zero]
    simp only [Finset.sum_ite_eq', hii, ite_false, add_zero]
    have hs : (∑ j ∈ inNbhd θ i,
        ((if i = j then θ.t i else 0) + if j ∈ inNbhd θ i then θ.b i j else 0) / 2) =
            (∑ j ∈ inNbhd θ i, θ.b i j) / 2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      have hji : i ≠ j := fun h => hii (h ▸ hj)
      simp [hji, hj]
    rw [hs]
    ring
  simp_rw [hrow]
  simp only [tte, potentialOutcome, treatment, ite_true, Bool.false_eq_true,
    ite_false, mul_one, mul_zero, Finset.sum_const_zero, add_zero]
  simp_rw [show ∀ i, θ.a i + θ.t i + ∑ j ∈ inNbhd θ i, θ.b i j - θ.a i =
    θ.t i + ∑ j ∈ inNbhd θ i, θ.b i j by intro i; ring]
  rw [← Finset.sum_div]
  ring

/-- The audit product is a probability law at admissible retention.  [For the stated data and conditions](hyp:q,hq), [the stated conclusion holds](goal). -/
-- @node: auditLaw_probability
lemma auditLaw_probability (q : ℝ) (hq : q ∈ Set.Icc 0 1) :
    IsProbabilityMeasure (auditLaw V q) := by
  let := bernoulliLaw_probability q hq
  unfold auditLaw
  infer_instance

/-- Every real audit statistic is integrable on the finite audit space.  [For the stated data and conditions](hyp:q,hq,f), [the stated conclusion holds](goal). -/
-- @node: auditLaw_integrable
lemma auditLaw_integrable (q : ℝ) (hq : q ∈ Set.Icc 0 1) (f : Audit V → ℝ) :
    Integrable f (auditLaw V q) := by
  let := auditLaw_probability (V := V) q hq
  exact Integrable.of_finite

/-- The mean of a single numeric audit mark is its retention probability.  [For the stated data and conditions](hyp:q,hq,e), [the stated conclusion holds](goal). -/
-- @node: integral_audit_treatment
lemma integral_audit_treatment (q : ℝ) (hq : q ∈ Set.Icc 0 1) (e : OffDiag V) :
    (∫ w, treatment (w e) ∂auditLaw V q) = q := by
  let := bernoulliLaw_probability q hq
  have hm := (measurePreserving_eval (fun _ : OffDiag V => bernoulliLaw q) e).map_eq
  have he := integral_map (μ := auditLaw V q)
    (φ := fun w => w e) ((measurable_pi_apply e).aemeasurable) (f := treatment) (by fun_prop)
  rw [show (auditLaw V q).map (fun w => w e) = bernoulliLaw q from hm] at he
  rw [← he]
  rw [show bernoulliLaw q = Causalean.Mathlib.Probability.bernoulliBool q by
    unfold bernoulliLaw Causalean.Mathlib.Probability.bernoulliBool
    exact add_comm _ _]
  rw [Causalean.Mathlib.Probability.bernoulliBool_integral hq.1 hq.2]
  simp [treatment]

/-- Conditional on assignment, the retained-neighbor sign sum has mean q times the true sum.  [For the stated data and conditions](hyp:θ,q,hq,z,i), [the stated conclusion holds](goal). -/
-- @node: integral_recorded_sign_sum
lemma integral_recorded_sign_sum (θ : Schedule V) (q : ℝ) (hq : q ∈ Set.Icc 0 1)
    (z : Assign V) (i : V) :
    (∫ w, ∑ j ∈ recordedNbhd (recordOf θ (z, w)).1 i, signOf (z j)
      ∂auditLaw V q) = q * ∑ j ∈ inNbhd θ i, signOf (z j) := by
  simp only [recordedNbhd]
  simp_rw [Finset.sum_filter]
  dsimp only [recordOf]
  rw [integral_finsetSum _ (fun _ _ => auditLaw_integrable q hq _)]
  have ht (j : V) :
      (∫ w, if (∃ hji : j ≠ i, (decide (θ.edge j i) && w ⟨(j, i), hji⟩) = true)
        then signOf (z j) else 0 ∂auditLaw V q) =
          if θ.edge j i then q * signOf (z j) else 0 := by
    by_cases hj : θ.edge j i
    · have hji : j ≠ i := by intro he; subst j; exact θ.irrefl i hj
      have he : (fun w : Audit V => if (∃ hji : j ≠ i,
          (decide (θ.edge j i) && w ⟨(j, i), hji⟩) = true) then signOf (z j) else 0) =
            fun w => treatment (w ⟨(j, i), hji⟩) * signOf (z j) := by
        funext w
        cases hw : w ⟨(j, i), hji⟩ <;> simp [hj, hji, hw, treatment]
      rw [he, integral_mul_const, integral_audit_treatment q hq, if_pos hj]
    · simp [hj]
  trans ∑ j : V, if θ.edge j i then q * signOf (z j) else 0
  · exact Finset.sum_congr rfl (fun j _ => ht j)
  · rw [inNbhd, Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    split <;> simp_all

/-- Inverse inclusion weighting recovers the oracle score's conditional mean.  [For the stated data and conditions](hyp:θ,q,hq,hq0,z), [the stated conclusion holds](goal). -/
-- @node: integral_auditScore_given_assignment
lemma integral_auditScore_given_assignment (θ : Schedule V) (q : ℝ)
    (hq : q ∈ Set.Icc 0 1) (hq0 : 0 < q) (z : Assign V) :
    (∫ w, auditScore q (recordOf θ (z, w)) ∂auditLaw V q) = oracleScore θ z := by
  let := auditLaw_probability (V := V) q hq
  simp only [auditScore, recordOf]
  rw [integral_const_mul, integral_finsetSum _ (fun _ _ => auditLaw_integrable q hq _)]
  unfold oracleScore
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul, integral_add (auditLaw_integrable q hq _)
    (auditLaw_integrable q hq _), integral_const, probReal_univ, one_smul,
    integral_const_mul]
  have he := integral_recorded_sign_sum θ q hq z i
  change (∫ w, ∑ j ∈ recordedNbhd
    (fun e => decide (θ.edge e.1.1 e.1.2) && w e) i, signOf (z j) ∂auditLaw V q) =
      q * ∑ j ∈ inNbhd θ i, signOf (z j) at he
  rw [he, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hq0), one_mul]

/-- The complete-record inverse-inclusion score is unbiased under the three design atoms.  [For the stated data and conditions](hyp:D,θ,q,ha,hw,hi,hq), [the stated conclusion holds](goal). -/
-- @node: integral_auditScore_eq_tte
lemma integral_auditScore_eq_tte (D : Measure (Assign V × Audit V)) (θ : Schedule V)
    (q : ℝ) (ha : AssignmentLaw D) (hw : AuditLaw D q)
    (hi : DesignIndependent D) (hq : 0 < q) :
    (∫ ω, auditScore q (recordOf θ ω) ∂D) = tte θ := by
  rw [design_eq_thinnedDesign D q ha hw hi]
  let := halfBernoulli_probability (V := V)
  let := auditLaw_probability (V := V) q ⟨hw.1, hw.2.1⟩
  rw [thinnedDesign, integral_prod _ (show Integrable _ _ from Integrable.of_finite)]
  simp_rw [integral_auditScore_given_assignment θ q ⟨hw.1, hw.2.1⟩ hq]
  exact integral_oracleScore_eq_tte θ

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
