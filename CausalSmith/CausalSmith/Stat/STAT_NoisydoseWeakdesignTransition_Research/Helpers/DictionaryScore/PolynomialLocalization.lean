module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.DictionaryScore.InverseHeat
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Polynomial localization bounds

Roadmap S11: the odd polynomial weight is bounded by one, has a sixth-order tail,
and is bounded below on an interval of radius proportional to the inverse degree.
These estimates use the declared trigonometric representation, including its value at zero.
-/
public section
open MeasureTheory Set Filter
set_option linter.style.longLine false
set_option linter.style.whitespace false
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition

/-- The addition formula bounds the sine of an integer multiple. [This is the stated conclusion](goal). -/
-- @node: polynomial_abs_sin_nat_mul_le
lemma polynomial_abs_sin_nat_mul_le (m : ℕ) (z : ℝ) :
    |Real.sin ((m : ℝ)*z)| ≤ (m : ℝ)*|Real.sin z| := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.cast_succ, add_mul, one_mul, Real.sin_add]
    calc
      _ ≤ |Real.sin ((m : ℝ)*z)*Real.cos z| +
          |Real.cos ((m : ℝ)*z)*Real.sin z| := abs_add_le _ _
      _ ≤ |Real.sin ((m : ℝ)*z)| + |Real.sin z| := by
        rw [abs_mul, abs_mul]
        exact add_le_add
          (by simpa using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one z) (abs_nonneg (Real.sin ((m : ℝ)*z))))
          (by simpa using mul_le_mul_of_nonneg_right (Real.abs_cos_le_one ((m : ℝ)*z)) (abs_nonneg (Real.sin z)))
      _ ≤ _ := by nlinarith

/-- The normalized sine quotient never exceeds one on the latent support. [Under the stated conditions](hyp:hm,hmpos,ht). [This is the stated conclusion](goal). -/
-- @node: qM_le_one
lemma qM_le_one (m : ℕ) (hm : Odd m) (hmpos : 0 < m) (t : ℝ)
    (ht : t ∈ Icc (-1/2 : ℝ) (1/2)) : qM m t ≤ 1 := by
  rw [qM_trig m hm hmpos t ht]
  split_ifs with htzero
  · norm_num
  · have hmR : 0 < (m : ℝ) := by exact_mod_cast hmpos
    have hsin := polynomial_abs_sin_nat_mul_le m (Real.arcsin (2*t))
    rw [Real.sin_arcsin (by linarith [ht.1]) (by linarith [ht.2]), abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hsin
    have hquot : |Real.sin (m*Real.arcsin (2*t)) / (2*m*t)| ≤ 1 := by
      rw [abs_div, div_le_one (by positivity : 0 < |(2 : ℝ)*m*t|)]
      simpa [abs_mul, abs_of_pos hmR, mul_assoc, mul_left_comm, mul_comm] using hsin
    have hp := pow_le_pow_left₀ (abs_nonneg _) hquot 6
    simpa only [pow_abs_two_mul (n := 3), one_pow] using hp

/-- The numerator's unit bound gives sixth-order decay away from the target. [Under the stated conditions](hyp:hm,hmpos,htzero,ht). [This is the stated conclusion](goal). -/
-- @node: qM_tail_bound
lemma qM_tail_bound (m : ℕ) (hm : Odd m) (hmpos : 0 < m) (t : ℝ)
    (ht : t ∈ Icc (-1/2 : ℝ) (1/2)) (htzero : t ≠ 0) :
    qM m t ≤ (1 / (2*(m : ℝ)*|t|))^6 := by
  rw [qM_trig m hm hmpos t ht, if_neg htzero]
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hmpos
  have hquot : |Real.sin (m*Real.arcsin (2*t)) / (2*m*t)| ≤
      1 / (2*(m : ℝ)*|t|) := by
    rw [abs_div, abs_mul, abs_mul, abs_of_pos hmR,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (by positivity)
  have hp := pow_le_pow_left₀ (abs_nonneg _) hquot 6
  simpa only [pow_abs_two_mul (n := 3)] using hp

/-- Jordan's inequality controls arcsine linearly throughout the dose support. [This is the stated conclusion](goal). [Under the stated conditions](hyp:ht). -/
-- @node: polynomial_arcsin_bounds
lemma polynomial_arcsin_bounds (t : ℝ) (ht : t ∈ Icc (-1/2 : ℝ) (1/2)) :
    2*|t| ≤ |Real.arcsin (2*t)| ∧ |Real.arcsin (2*t)| ≤ Real.pi*|t| := by
  have hs : Real.sin (Real.arcsin (2*t)) = 2*t :=
    Real.sin_arcsin (by linarith [ht.1]) (by linarith [ht.2])
  have ha : |Real.arcsin (2*t)| ≤ Real.pi/2 :=
    abs_le.mpr ⟨Real.neg_pi_div_two_le_arcsin _, Real.arcsin_le_pi_div_two _⟩
  have hl := Real.abs_sin_le_abs (x := Real.arcsin (2*t))
  have hu := Real.mul_abs_le_abs_sin ha
  rw [hs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hl hu
  refine ⟨hl, ?_⟩
  rw [div_mul_eq_mul_div] at hu
  have h := (div_le_iff₀ Real.pi_pos).mp hu
  nlinarith

/-- On the inverse-degree central interval the weight has a fixed positive lower bound. [Under the stated conditions](hyp:hm,hmpos,ht). [This is the stated conclusion](goal). -/
-- @node: qM_central_lower
lemma qM_central_lower (m : ℕ) (hm : Odd m) (hmpos : 0 < m) (t : ℝ)
    (ht : |t| ≤ 1 / (2*(m : ℝ))) :
    (2/Real.pi)^6 ≤ qM m t := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hmpos
  have hmone : (1 : ℝ) ≤ m := by exact_mod_cast hmpos
  have hmt : 2*(m : ℝ)*|t| ≤ 1 := by
    have h := (le_div_iff₀ (by positivity : 0 < 2*(m : ℝ))).mp ht
    nlinarith
  have hsupport : t ∈ Icc (-1/2 : ℝ) (1/2) := by
    have := mul_le_mul_of_nonneg_right hmone (abs_nonneg t)
    have habs : |t| ≤ 1/2 := by nlinarith
    exact ⟨by linarith [(abs_le.mp habs).1], by linarith [(abs_le.mp habs).2]⟩
  rw [qM_trig m hm hmpos t hsupport]
  split_ifs with htzero
  · have hc : 2/Real.pi ≤ 1 := (div_le_one Real.pi_pos).mpr Real.two_le_pi
    exact (pow_le_pow_left₀ (by positivity) hc 6).trans_eq (by norm_num)
  · obtain ⟨hl, hu⟩ := polynomial_arcsin_bounds t hsupport
    have hz : |(m : ℝ)*Real.arcsin (2*t)| ≤ Real.pi/2 := by
      rw [abs_mul, abs_of_pos hmR]
      have h := mul_le_mul_of_nonneg_left hu hmR.le
      have h' := mul_le_mul_of_nonneg_left hmt Real.pi_pos.le
      nlinarith
    have hs := Real.mul_abs_le_abs_sin hz
    rw [abs_mul, abs_of_pos hmR] at hs
    have hquot : 2/Real.pi ≤ |Real.sin (m*Real.arcsin (2*t)) / (2*m*t)| := by
      rw [abs_div, abs_mul, abs_mul, abs_of_pos hmR,
        abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      apply (le_div_iff₀ (by positivity : 0 < 2*(m : ℝ)*|t|)).mpr
      have h := mul_le_mul_of_nonneg_left hl
        (show 0 ≤ (2/Real.pi)*(m : ℝ) by positivity)
      nlinarith
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 2/Real.pi) hquot 6
    simpa only [pow_abs_two_mul (n := 3)] using hp

/-- Dilation of a central power moment gives the precise localization exponent. [Under the stated conditions](hyp:h,hh). [This is the stated conclusion](goal). -/
-- @node: polynomial_central_power_moment
lemma polynomial_central_power_moment (s h : ℝ) (hh : 0 < h) :
    (∫ t in Icc (-h/2) (h/2), |t|^s) =
      h^(s+1) * weightMoment s (fun _ => 1) := by
  have he (t : ℝ) : |t|^s = h^s * |t/h|^s := by
    have ha : |t| = h * |t/h| := by
      rw [abs_div, abs_of_pos hh]
      field_simp
    rw [ha, Real.mul_rpow hh.le (abs_nonneg _)]
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -h/2 ≤ h/2)]
  conv_lhs => arg 1; ext t; rw [he t]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_div (fun u : ℝ => |u|^s) hh.ne', smul_eq_mul]
  have hl : (-h/2)/h = (-1/2 : ℝ) := by field_simp
  have hu : (h/2)/h = (1/2 : ℝ) := by field_simp
  rw [hl, hu, intervalIntegral.integral_of_le (by norm_num : (-1/2 : ℝ) ≤ 1/2),
    ← integral_Icc_eq_integral_Ioc, Real.rpow_add hh, Real.rpow_one]
  simp only [weightMoment, mul_one]
  ring

/-- S11's denominator lower bound follows from the fixed central plateau. [Under the stated conditions](hyp:hs,hm,hmpos). [This is the stated conclusion](goal). -/
-- @node: qM_weightMoment_lower
lemma qM_weightMoment_lower (s : ℝ) (hs : 0 ≤ s) (m : ℕ)
    (hm : Odd m) (hmpos : 0 < m) :
    (2/Real.pi)^6 * ((m : ℝ)⁻¹)^(s+1) * weightMoment s (fun _ => 1) ≤
      weightMoment s (qM m) := by
  let h : ℝ := (m : ℝ)⁻¹
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hmpos
  have hh : 0 < h := inv_pos.mpr hmR
  have hmone : (1 : ℝ) ≤ m := by exact_mod_cast hmpos
  have hhone : h ≤ 1 := (inv_le_one₀ hmR).mpr hmone
  have hsubset : Icc (-h/2) (h/2) ⊆ Icc (-1/2 : ℝ) (1/2) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hcentral : ∀ t ∈ Icc (-h/2) (h/2), (2/Real.pi)^6 ≤ qM m t := by
    intro t ht
    apply qM_central_lower m hm hmpos t
    have ha : |t| ≤ h/2 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
    convert ha using 1
    dsimp [h]
    field_simp
  have hi : Integrable (fun t : ℝ => |t|^s)
      (volume.restrict (Icc (-h/2) (h/2))) :=
    (continuous_abs.rpow_const (fun _ => Or.inr hs)).integrableOn_Icc
  calc
    _ = (2/Real.pi)^6 * ∫ t in Icc (-h/2) (h/2), |t|^s := by
      rw [polynomial_central_power_moment s h hh]
      simp only [h]; ring
    _ ≤ ∫ t in Icc (-h/2) (h/2), |t|^s * qM m t := by
      rw [← integral_const_mul]
      apply integral_mono_ae (hi.const_mul _) ((qM_weighted_continuous s hs m).integrableOn_Icc)
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_left (hcentral t ht) (Real.rpow_nonneg (abs_nonneg t) s)
    _ ≤ weightMoment s (qM m) := by
      apply setIntegral_mono_set (qM_weighted_integrable s hs m)
        (Eventually.of_forall (fun t => mul_nonneg (Real.rpow_nonneg (abs_nonneg t) s) (qM_nonneg m t)))
      exact Eventually.of_forall hsubset

/-- A rescaled cubic tail dominates all S11 weighted integrands uniformly in degree. [Under the stated conditions](hyp:hm,hmpos,hs,ht). [This is the stated conclusion](goal). -/
-- @node: qM_weighted_tail_bound
lemma qM_weighted_tail_bound (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 3)
    (m : ℕ) (hm : Odd m) (hmpos : 0 < m) (t : ℝ)
    (ht : t ∈ Icc (-1/2 : ℝ) (1/2)) :
    |t|^s * qM m t ≤ ((m : ℝ)⁻¹)^s * (8 / (1 + |t / (m : ℝ)⁻¹|)^3) := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hmpos
  let h : ℝ := (m : ℝ)⁻¹
  let u : ℝ := t/h
  have hh : 0 < h := inv_pos.mpr hmR
  have hscale : |t|^s = h^s * |u|^s := by
    have ha : |t| = h*|u| := by
      dsimp [u]; rw [abs_div, abs_of_pos hh]; field_simp
    rw [ha, Real.mul_rpow hh.le (abs_nonneg _)]
  have hunit : |u|^s * qM m t ≤ 8 / (1+|u|)^3 := by
    have ha : 0 ≤ |u| := abs_nonneg u
    have hp : 0 < 1+|u| := by positivity
    by_cases hu : |u| ≤ 1
    · have hw := Real.rpow_le_one ha hu hs.1
      have hq := qM_le_one m hm hmpos t ht
      have hprod : |u|^s * qM m t ≤ 1 := by
        nlinarith [Real.rpow_nonneg ha s, qM_nonneg m t]
      apply hprod.trans
      apply (le_div_iff₀ (pow_pos hp 3)).mpr
      have hb := pow_le_pow_left₀ hp.le (show 1+|u| ≤ 2 by linarith) 3
      norm_num at hb ⊢
      exact hb
    · have hu1 : 1 ≤ |u| := (lt_of_not_ge hu).le
      have hup : 0 < |u| := by linarith
      have htzero : t ≠ 0 := by
        intro htzero; have : u = 0 := by simp [u, htzero]
        simp [this] at hu
      have hw : |u|^s ≤ |u|^(3 : ℕ) := by
        simpa using Real.rpow_le_rpow_of_exponent_le hu1 hs.2
      have hq : qM m t ≤ (1/|u|)^6 := by
        have htail := qM_tail_bound m hm hmpos t ht htzero
        have he : 2*(m : ℝ)*|t| = 2*|u| := by
          simp [u, h, div_eq_mul_inv, abs_mul, abs_of_pos hmR, mul_comm, mul_assoc]
        rw [he] at htail
        apply htail.trans
        apply pow_le_pow_left₀ (by positivity)
        apply one_div_le_one_div_of_le hup
        linarith
      calc
        _ ≤ |u|^3 * (1/|u|)^6 :=
          mul_le_mul hw hq (qM_nonneg m t) (by positivity)
        _ = 1/|u|^3 := by field_simp
        _ ≤ 8/(1+|u|)^3 := by
          apply (div_le_div_iff₀ (pow_pos hup 3) (pow_pos hp 3)).mpr
          have hb := pow_le_pow_left₀ hp.le (show 1+|u| ≤ 2*|u| by linarith) 3
          nlinarith [hb]
  rw [hscale, mul_assoc]
  exact mul_le_mul_of_nonneg_left hunit (Real.rpow_nonneg hh.le s)

/-- The dominating cubic envelope is integrable at every positive localization scale. [Under the stated conditions](hyp:h,hh). [This is the stated conclusion](goal). -/
-- @node: polynomial_tail_envelope_integrable
lemma polynomial_tail_envelope_integrable (s h : ℝ) (hh : 0 < h) :
    Integrable (fun t : ℝ => h^s * (8 / (1+|t/h|)^3)) := by
  have hi : Integrable (fun u : ℝ => (1+‖u‖)^(-(3 : ℝ))) :=
    integrable_one_add_norm (by norm_num)
  have hd : Integrable (fun u : ℝ => 8/(1+|u|)^3) := by
    simpa [Real.norm_eq_abs, Real.rpow_neg, div_eq_mul_inv] using hi.const_mul 8
  have hc := (integrable_comp_mul_left_iff (fun u : ℝ => 8/(1+|u|)^3)
    (inv_ne_zero hh.ne')).mpr hd
  simpa only [← div_eq_inv_mul] using hc.const_mul (h^s)

/-- The envelope's whole-line integral scales with exactly the S11 moment exponent. [Under the stated conditions](hyp:h,hh). [This is the stated conclusion](goal). -/
-- @node: polynomial_tail_envelope_integral
lemma polynomial_tail_envelope_integral (s h : ℝ) (hh : 0 < h) :
    (∫ t : ℝ, h^s * (8/(1+|t/h|)^3)) =
      h^(s+1) * (∫ u : ℝ, 8/(1+|u|)^3) := by
  rw [integral_const_mul]
  have hc := Measure.integral_comp_mul_left (fun u : ℝ => 8/(1+|u|)^3) h⁻¹
  simp only [inv_inv, abs_of_pos hh, smul_eq_mul, ← div_eq_inv_mul] at hc
  rw [hc, Real.rpow_add hh, Real.rpow_one]
  ring

/-- S11's upper bound has a degree-independent constant for every required exponent. [Under the stated conditions](hyp:hm,hmpos,hs). [This is the stated conclusion](goal). -/
-- @node: qM_weightMoment_upper
lemma qM_weightMoment_upper (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 3)
    (m : ℕ) (hm : Odd m) (hmpos : 0 < m) :
    weightMoment s (qM m) ≤ ((m : ℝ)⁻¹)^(s+1) * (∫ u : ℝ, 8/(1+|u|)^3) := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hmpos
  have hi := polynomial_tail_envelope_integrable s ((m : ℝ)⁻¹) (inv_pos.mpr hmR)
  calc
    _ ≤ ∫ t in Icc (-1/2 : ℝ) (1/2),
        ((m : ℝ)⁻¹)^s * (8/(1+|t/(m : ℝ)⁻¹|)^3) := by
      apply integral_mono_ae (qM_weighted_integrable s hs.1 m) hi.integrableOn
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact qM_weighted_tail_bound s hs m hm hmpos t ht
    _ ≤ ∫ t : ℝ, ((m : ℝ)⁻¹)^s * (8/(1+|t/(m : ℝ)⁻¹|)^3) :=
      integral_mono_measure Measure.restrict_le_self
        (Eventually.of_forall (fun t => by positivity)) hi
    _ = _ := polynomial_tail_envelope_integral s _ (inv_pos.mpr hmR)

/-- The constants in S11 are positive and independent of the odd degree. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hs). -/
-- @node: qM_weightMoment_bounds
lemma qM_weightMoment_bounds (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 3) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ m : ℕ, Odd m → 0 < m →
      c * ((m : ℝ)⁻¹)^(s+1) ≤ weightMoment s (qM m) ∧
      weightMoment s (qM m) ≤ C * ((m : ℝ)⁻¹)^(s+1) := by
  have hI : 0 < weightMoment s (fun _ => 1) := by
    simpa only [weightMoment, qM_one] using qM_weightMoment_pos s hs.1 1 (by decide) (by norm_num)
  have hc : 0 < (2/Real.pi)^6 * weightMoment s (fun _ => 1) := by positivity
  have hC : 0 < ∫ u : ℝ, 8/(1+|u|)^3 := by
    have hb := qM_weightMoment_upper s hs 1 (by decide) (by norm_num)
    simp only [Nat.cast_one, inv_one, Real.one_rpow, one_mul, weightMoment, qM_one] at hb
    exact hI.trans_le hb
  refine ⟨(2/Real.pi)^6 * weightMoment s (fun _ => 1),
    ∫ u : ℝ, 8/(1+|u|)^3, hc, hC, ?_⟩
  intro m hm hmpos
  constructor
  · simpa only [mul_assoc, mul_left_comm, mul_comm] using qM_weightMoment_lower s hs.1 m hm hmpos
  · simpa only [mul_comm] using qM_weightMoment_upper s hs m hm hmpos

/-- The moment comparison assembles the exact S11 bias rate for every valid degree. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hbeta,hkappa). -/
-- @node: qM_bias_bound
lemma qM_bias_bound (beta kappa : ℝ) (hbeta : beta ∈ Ioc (0 : ℝ) 1)
    (hkappa : kappa ∈ Icc (0 : ℝ) 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, Odd m → 0 < m →
      unitBq beta kappa (qM m) ≤ C * ((m : ℝ)⁻¹)^beta := by
  have hs : kappa+beta ∈ Icc (0 : ℝ) 3 := by
    constructor <;> linarith [hbeta.1, hbeta.2, hkappa.1, hkappa.2]
  obtain ⟨c, K, hc, hK, hden⟩ := qM_weightMoment_bounds kappa
    ⟨hkappa.1, by linarith [hkappa.2]⟩
  obtain ⟨c', K', hc', hK', hnum⟩ := qM_weightMoment_bounds (kappa+beta) hs
  refine ⟨64*K'/c, by positivity, ?_⟩
  intro m hm hmpos
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hmpos
  have hh : 0 < (m : ℝ)⁻¹ := inv_pos.mpr hmR
  have hlo := (hden m hm hmpos).1
  have hhi := (hnum m hm hmpos).2
  have hp : 0 < ((m : ℝ)⁻¹)^(kappa+1) := Real.rpow_pos_of_pos hh _
  calc
    unitBq beta kappa (qM m) = 64 * weightMoment (kappa+beta) (qM m) /
      weightMoment kappa (qM m) := rfl
    _ ≤ (64 * (K' * ((m : ℝ)⁻¹)^(kappa+beta+1))) /
        (c * ((m : ℝ)⁻¹)^(kappa+1)) :=
      div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hhi (by norm_num))
        (mul_pos hc hp) hlo
    _ = (64*K'/c) * ((m : ℝ)⁻¹)^beta := by
      rw [show kappa+beta+1 = beta+(kappa+1) by ring, Real.rpow_add hh]
      field_simp [hp.ne']

end CausalSmith.Stat.NoisydoseWeakdesignTransition
