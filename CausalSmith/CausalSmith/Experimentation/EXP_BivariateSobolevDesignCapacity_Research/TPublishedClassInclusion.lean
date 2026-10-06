module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.PublishedClass

/-! # Strict published-class inclusion and independent-sign comparison

The d=2 converse and the independent-sign L² identity retain the full frozen outcome class.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

/-- [ Independent fair signs have identity second-moment matrix.](goal) -/
-- @node: fairSigns_product_integral
lemma fairSigns_product_integral (n : ℕ) (i j : Fin n) :
    (∫ z, sgn (z i) * sgn (z j) ∂fairSigns n) = if i = j then 1 else 0 := by
  letI := fairSigns_probability n
  by_cases hij : i = j
  · subst j
    have hsq (z : Signs n) : sgn (z i) * sgn (z i) = 1 := by
      cases z i <;> norm_num [sgn]
    simp [hsq]
  · rw [if_neg hij, integral_fintype (Integrable.of_finite)]
    simp only [Measure.real, fairSigns,
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
      PMF.uniformOfFintype_apply, smul_eq_mul]
    let e : Signs n ≃ Signs n :=
      { toFun := fun z => Function.update z i (!(z i))
        invFun := fun z => Function.update z i (!(z i))
        left_inv := by intro z; funext k; by_cases hk : k = i <;> simp [hk]
        right_inv := by intro z; funext k; by_cases hk : k = i <;> simp [hk] }
    have hsum := e.sum_comp (fun z =>
      ((Fintype.card (Signs n) : ℝ≥0∞)⁻¹).toReal * (sgn (z i) * sgn (z j)))
    have hi (z : Signs n) : sgn (e z i) = -sgn (z i) := by
      change sgn (Function.update z i (!(z i)) i) = _
      simp only [Function.update_self]
      cases z i <;> norm_num [sgn]
    have hj (z : Signs n) : e z j = z j := by
      exact Function.update_of_ne (Ne.symm hij) _ _
    simp only [hi, hj, neg_mul, mul_neg, Finset.sum_neg_distrib] at hsum
    linarith

/-- [ Averaging a deterministic signed sum over all independent fair signs leaves only
its diagonal squares.](goal) -/
-- @node: fairSigns_sum_second_moment
lemma fairSigns_sum_second_moment (n : ℕ) (u : Fin n → ℝ) :
    (∫ z, (∑ i, sgn (z i) * u i) ^ 2 ∂fairSigns n) = ∑ i, u i ^ 2 := by
  letI := fairSigns_probability n
  have hexpand (z : Signs n) : (∑ i, sgn (z i) * u i) ^ 2 =
      ∑ i, ∑ j, u i * (sgn (z i) * sgn (z j)) * u j := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp_rw [hexpand]
  rw [integral_finsetSum _ (fun i _ => Integrable.of_finite)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum _ (fun j _ => Integrable.of_finite)]
  simp_rw [integral_mul_const, integral_const_mul, fairSigns_product_integral]
  simp [pow_two]

/-- Independent fair assignment has exactly four times the prognostic second moment
as its original-unit imbalance loss. Under [the stated conditions](hyp:hn), [the asserted mathematical result follows](goal). -/
-- @node: loss_fairSigns_eq
lemma loss_fairSigns_eq (n d : ℕ) (hn : 0 < n) (m : CenteredL2Fn d) :
    loss (fairSignKernel n d) m.val =
      ENNReal.ofReal (4 * ∫ x, m.val x ^ 2 ∂cubeMeasure d) := by
  letI := cubeMeasure_probability d
  letI := fairSigns_probability n
  have hi (i : Fin n) : Integrable (fun x : Covariates n d => m.val (x i) ^ 2)
      (covLaw n d) :=
    (m.property.2.1.comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin n => cubeMeasure d) i)).integrable_sq
  have hsum : Integrable (fun x : Covariates n d => ∑ i, m.val (x i) ^ 2)
      (covLaw n d) := integrable_finsetSum Finset.univ (fun i _ => hi i)
  have hinner (x : Covariates n d) :
      (∫⁻ z, ENNReal.ofReal ((∑ i, sgn (z i) * m.val (x i)) ^ 2) ∂fairSigns n) =
        ENNReal.ofReal (∑ i, m.val (x i) ^ 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal Integrable.of_finite
      (Filter.Eventually.of_forall (fun z => sq_nonneg _)),
      fairSigns_sum_second_moment]
  have heval (i : Fin n) :
      (∫ x : Covariates n d, m.val (x i) ^ 2 ∂covLaw n d) =
        ∫ x, m.val x ^ 2 ∂cubeMeasure d := by
    exact integral_comp_eval (μ := fun _ : Fin n => cubeMeasure d) (i := i)
      (m.property.1.pow_const 2).aestronglyMeasurable
  change ENNReal.ofReal (4 / (n : ℝ)) *
    (∫⁻ x, ∫⁻ z, ENNReal.ofReal ((∑ i, sgn (z i) * m.val (x i)) ^ 2)
      ∂fairSigns n ∂covLaw n d) = _
  simp_rw [hinner]
  rw [← ofReal_integral_eq_lintegral_ofReal hsum
    (Filter.Eventually.of_forall (fun x => Finset.sum_nonneg (fun i _ => sq_nonneg _))),
    integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [heval]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

/-- [ In dimension two the comparison scale is the single-pair power of sample size.](goal) Under [the stated conditions](hyp:hn,hs). -/
-- @node: bScale_two
lemma bScale_two (n : ℕ) (hn : 2 ≤ n) (s : ℝ) (hs : 0 < s) :
    bScale n 2 s = (n : ℝ) ^ (-s) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hpow : (n : ℝ) ^ (-s) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn1 (neg_nonpos.mpr hs.le)
  norm_num [bScale, pairCount, one_div, ← Real.rpow_neg_eq_inv_rpow,
    min_eq_right hpow]

-- @node: prop:published-class-inclusion
/-- Gaussian completions form a proper published subclass, with the same admissible
kernels, a single-pair lower exponent, and independent-sign loss at most four. This uses [the hExcess_of_gate hypothesis](hyp:hExcess_of_gate), [the hContraction_of_gate hypothesis](hyp:hContraction_of_gate), [the stated conclusion](goal). -/
theorem published_class_inclusion
    (hExcess_of_gate : PublishedHTExcessIdentity)
    (hContraction_of_gate : ClassicalRademacherContraction) :
    ∀ s : ℝ, 0 < s → s ≤ 1 →
    (∀ (d : ℕ) (hd : 2 ≤ d),
      gaussianLawClass d (lt_of_lt_of_le (Nat.zero_lt_succ 1) hd) s ⊂ frozenUniformClass d s) ∧
    (∀ n d : ℕ, 2 ≤ n → 2 ≤ d → ∀ π : Design n d,
      PublishedAdmissible π ↔ DesignClass n d π) ∧
    (∀ n : ℕ, 2 ≤ n → ENNReal.ofReal (cLower s * (n : ℝ) ^ (-s)) ≤ capacity n 2 s) ∧
    (∀ n d : ℕ, 2 ≤ n → 2 ≤ d → ∀ m : CenteredL2Fn d, SobolevClass d s m →
      loss (fairSignKernel n d) m.val =
        ENNReal.ofReal (4 * ∫ x, m.val x ^ 2 ∂cubeMeasure d) ∧
      loss (fairSignKernel n d) m.val ≤ 4) := by
  intro s hs hs1
  have hpublished := published_prognostic_capacity hExcess_of_gate hContraction_of_gate
  refine ⟨?_, hpublished.2.1, ?_, ?_⟩
  · intro d hd
    exact (hpublished.1 d hd s hs hs1).2.1
  · intro n hn
    have hlower := ((full_design_lower hContraction_of_gate s hs hs1).2 n 2 hn
      (by omega)).2
    rw [bScale_two n hn s hs] at hlower
    exact hlower
  · intro n d hn hd m hm
    refine ⟨loss_fairSigns_eq n d (by omega) m, ?_⟩
    rw [loss_fairSigns_eq n d (by omega) m]
    have hmoment := sobolev_cube_second_moment_le_one hd hs hs1 m hm
    calc
      ENNReal.ofReal (4 * ∫ x, m.val x ^ 2 ∂cubeMeasure d) ≤
          ENNReal.ofReal (4 * 1) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hmoment (by norm_num))
      _ = 4 := by norm_num

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
