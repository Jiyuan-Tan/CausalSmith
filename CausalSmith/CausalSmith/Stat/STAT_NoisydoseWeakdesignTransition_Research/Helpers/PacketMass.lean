module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.CitedGates
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Weighted absolute mass from a localized packet envelope (P6--P7).
The decay exponent kappa + 2 leaves an integrable quadratic envelope after
absorbing the power-law weight. -/
public section
noncomputable section
open MeasureTheory Set
open scoped Topology
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition

/-- Absorbing the weight into the decay envelope gives the bandwidth power. [Under the stated conditions](hyp:hkappa,ht,hu). [This is the stated conclusion](goal). -/
-- @node: packet_weighted_decay_le
lemma packet_weighted_decay_le (kappa t u : ℝ) (hkappa : 0 ≤ kappa)
    (ht : 0 < t) (hu : 0 ≤ u) :
    u^kappa * (1+t*u)^(-(kappa+2)) ≤ t^(-kappa) * (1+t*u)^(-2 : ℝ) := by
  have hb : 0 < 1+t*u := by positivity
  have hp : (t*u)^kappa ≤ (1+t*u)^kappa :=
    Real.rpow_le_rpow (by positivity) (by linarith) hkappa
  have hm : t^kappa * u^kappa = (t*u)^kappa := (Real.mul_rpow ht.le hu).symm
  have hn : (1+t*u)^(-(kappa+2)) =
      ((1+t*u)^kappa)⁻¹ * (1+t*u)^(-2 : ℝ) := by
    rw [show -(kappa+2) = -kappa + (-2 : ℝ) by ring, Real.rpow_add hb,
      Real.rpow_neg hb.le]
  rw [hn, Real.rpow_neg ht.le]
  have htk : 0 < t^kappa := Real.rpow_pos_of_pos ht _
  have hbk : 0 < (1+t*u)^kappa := Real.rpow_pos_of_pos hb _
  have h : u^kappa / (1+t*u)^kappa ≤ (t^kappa)⁻¹ := by
    apply (div_le_iff₀ hbk).2
    rw [mul_comm, ← div_eq_mul_inv]
    apply (le_div_iff₀ htk).2
    nlinarith [hp]
  simpa only [div_eq_mul_inv, mul_assoc] using
    mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hb.le (-2))

/-- The quadratic envelope on the positive half interval has mass at most 1/t. [Under the stated conditions](hyp:ht). [This is the stated conclusion](goal). -/
-- @node: packet_quadratic_half_mass_le
lemma packet_quadratic_half_mass_le (t : ℝ) (ht : 0 < t) :
    (∫ u in (0 : ℝ)..1, (1+t*u)^(-2 : ℝ)) ≤ t⁻¹ := by
  have hc : ContinuousOn (fun u : ℝ => (1+t*u)^(-2 : ℝ)) (Icc 0 1) := by
    apply ContinuousOn.rpow_const (by fun_prop)
    intro u hu
    left
    have : 0 < 1+t*u := by nlinarith [hu.1]
    exact ne_of_gt this
  have hi := hc.intervalIntegrable_of_Icc (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
  have he : (∫ u in (0 : ℝ)..1, (1+t*u)^(-2 : ℝ)) =
      -(1+t)⁻¹/t + 1/t := by
    have hd : ∀ u ∈ uIcc (0 : ℝ) 1,
        HasDerivAt (fun u : ℝ => -(1+t*u)⁻¹/t) ((1+t*u)^(-2 : ℝ)) u := by
      intro u hu
      have hu0 : 0 ≤ u := by simpa using hu.1
      have hb : 1+t*u ≠ 0 := ne_of_gt (by positivity)
      convert! (((hasDerivAt_id u).const_mul t).const_add 1).inv hb |>.neg |>.div_const t using 1
      rw [Real.rpow_neg (by positivity), Real.rpow_two]
      dsimp
      field_simp
    simpa [neg_div, sub_neg_eq_add] using intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  rw [he]
  have : 0 ≤ (1+t)⁻¹/t := by positivity
  simp only [neg_div, one_div]
  linarith

/-- P7: a continuous even packet with decay exponent kappa + 2 has weighted
absolute mass at most 2 C times the bandwidth power. No improper integral is
needed: the residual quadratic envelope has an explicit antiderivative. [Under the stated conditions](hyp:hkappa,ht,hC,hpsi,heven,hdecay). [This is the stated conclusion](goal). -/
-- @node: packet_decay_absolute_mass_le
lemma packet_decay_absolute_mass_le (kappa t C : ℝ) (psi : ℝ → ℝ)
    (hkappa : 0 ≤ kappa) (ht : 0 < t) (hC : 0 ≤ C)
    (hpsi : Continuous psi) (heven : Function.Even psi)
    (hdecay : ∀ u, |psi u| ≤ C * (1 + t * |u|) ^ (-(kappa + 2))) :
    (∫ u in Icc (-1 : ℝ) 1, |u|^kappa * |psi u|) ≤ 2*C*t^(-kappa-1) := by
  let f : ℝ → ℝ := fun u => |u|^kappa * |psi u|
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hfeven : ∀ u, f (-u) = f u := by
    intro u
    simp only [f, abs_neg, heven u]
  have hc : ContinuousOn (fun u : ℝ => (1+t*u)^(-2 : ℝ)) (Icc 0 1) := by
    apply ContinuousOn.rpow_const (by fun_prop)
    intro u hu
    left
    exact ne_of_gt (by nlinarith [hu.1] : 0 < 1+t*u)
  have hhalf : (∫ u in (0 : ℝ)..1, f u) ≤ C*t^(-kappa)*t⁻¹ := by
    calc
      _ ≤ ∫ u in (0 : ℝ)..1, (C*t^(-kappa)) * (1+t*u)^(-2 : ℝ) := by
        apply intervalIntegral.integral_mono_on (by norm_num)
          (hf.intervalIntegrable 0 1)
          ((hc.const_mul (C*t^(-kappa))).intervalIntegrable_of_Icc
            (μ := volume) (by norm_num))
        intro u hu
        have hu0 : 0 ≤ u := hu.1
        dsimp [f]
        rw [abs_of_nonneg hu0]
        calc
          _ ≤ u^kappa * (C*(1+t*u)^(-(kappa+2))) :=
            mul_le_mul_of_nonneg_left (by simpa [abs_of_nonneg hu0] using hdecay u)
              (Real.rpow_nonneg hu0 _)
          _ = C * (u^kappa * (1+t*u)^(-(kappa+2))) := by ring
          _ ≤ C * (t^(-kappa) * (1+t*u)^(-2 : ℝ)) :=
            mul_le_mul_of_nonneg_left (packet_weighted_decay_le kappa t u hkappa ht hu0) hC
          _ = _ := by ring
      _ = (C*t^(-kappa)) * (∫ u in (0 : ℝ)..1, (1+t*u)^(-2 : ℝ)) :=
        intervalIntegral.integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (packet_quadratic_half_mass_le t ht) (by positivity)
  have hreflect := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := 1) f
  simp only [hfeven, neg_zero] at hreflect
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le
    (by norm_num : (-1 : ℝ) ≤ 1)]
  change (∫ u in (-1 : ℝ)..1, f u) ≤ _
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (-1) 0) (hf.intervalIntegrable 0 1), ← hreflect]
  have ht_pow : t^(-kappa-1) = t^(-kappa)*t⁻¹ := by
    rw [sub_eq_add_neg, Real.rpow_add ht, Real.rpow_neg_one]
  rw [ht_pow]
  linarith

end CausalSmith.Stat.NoisydoseWeakdesignTransition
