module
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.DerivativeBounds
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.DerivativeChains
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.DerivativeCoefficients
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.LegendreBasis
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.Procedure
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

/-!
# True-side Gaussian measurement-error endpoint frontier

Helpers/Law-level constructions and the obligations specified by the typed core.
Cited logical facts are explicit inputs; bibliographic records have no logical consumers.
-/

public section

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology

namespace CausalSmith.Stat.RdTruesideNoiseFrontier


/-- The removable endpoint value of the Chebyshev quotient is the squared index. Given [the displayed inputs and assumptions](hyp:L), [the stated mathematical conclusion holds](goal). -/
lemma endpointF_eval_zero (L : ℕ) : (endpointF L).eval 0 = (L : ℝ)^2 := by
  let p : Polynomial ℝ := 1 - (chebyshev L).comp (1 - Polynomial.C 2 * Polynomial.X)
  have hid := congrArg (fun q : Polynomial ℝ => q.derivative.eval 0)
    (Polynomial.X_mul_divX_add p)
  simp only [Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_X, Polynomial.derivative_C, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_X,
    zero_mul, add_zero, one_mul] at hid
  have hd : p.derivative.eval 0 = 2 * (L : ℝ)^2 := by
    simp [p, chebyshev, Polynomial.derivative_comp, Polynomial.Chebyshev.T_derivative_eq_U,
      Polynomial.Chebyshev.U_eval_one]
    ring
  simp only [endpointF, Polynomial.eval_mul, Polynomial.eval_C]
  change (1/2 : ℝ) * (Polynomial.divX p).eval 0 = (L : ℝ)^2
  rw [hid, hd]
  ring
/-- Multiplication by the score recovers the Chebyshev numerator, including zero. Given [the displayed inputs and assumptions](hyp:L,x), [the stated mathematical conclusion holds](goal). -/
lemma endpointF_mul_score (L : ℕ) (x : ℝ) :
    2 * x * (endpointF L).eval x = 1 - (chebyshev L).eval (1 - 2*x) := by
  have hid := congrArg (fun p : Polynomial ℝ => p.eval x)
    (Polynomial.X_mul_divX_add
      (1 - (chebyshev L).comp (1 - Polynomial.C 2 * Polynomial.X)))
  have hz : (1 - (chebyshev L).comp
      (1 - Polynomial.C 2 * Polynomial.X)).coeff 0 = 0 := by
    simp [Polynomial.coeff_zero_eq_eval_zero, chebyshev]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_comp,
    hz] at hid
  simp only [endpointF, Polynomial.eval_mul, Polynomial.eval_C]
  nlinarith [hid]

/-- The quotient has the sine-square representation used for endpoint concentration. Given [the displayed inputs and assumptions](hyp:L,u), [the stated mathematical conclusion holds](goal). -/
lemma endpointF_sine_identity (L : ℕ) (u : ℝ) :
    (Real.sin u)^2 * (endpointF L).eval ((Real.sin u)^2) =
      (Real.sin ((L : ℝ)*u))^2 := by
  have hcos : 1 - 2 * (Real.sin u)^2 = Real.cos (2*u) := by
    nlinarith [Real.cos_two_mul u, Real.sin_sq_add_cos_sq u]
  have h := endpointF_mul_score L ((Real.sin u)^2)
  rw [hcos, chebyshev, Polynomial.Chebyshev.T_real_cos] at h
  have hh := Real.sin_sq_eq_half_sub ((L : ℝ)*u)
  have he : (L : ℝ) * (2*u) = 2*((L : ℝ)*u) := by ring
  norm_cast at h
  rw [he] at h
  nlinarith

/-- The sine addition formula bounds an integer frequency by its index times the base sine. Given [the displayed inputs and assumptions](hyp:L,u), [the stated mathematical conclusion holds](goal). -/
lemma endpoint_sin_nat_mul_bound (L : ℕ) (u : ℝ) :
    |Real.sin ((L : ℝ)*u)| ≤ (L : ℝ) * |Real.sin u| := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Nat.cast_succ, add_mul, one_mul, Real.sin_add]
    calc
      _ ≤ |Real.sin ((L : ℝ)*u) * Real.cos u| +
          |Real.cos ((L : ℝ)*u) * Real.sin u| := abs_add_le _ _
      _ ≤ |Real.sin ((L : ℝ)*u)| + |Real.sin u| := by
        rw [abs_mul, abs_mul]
        exact add_le_add
          (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _))
          (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _))
      _ ≤ ((L : ℝ)+1) * |Real.sin u| := by nlinarith [ih]

/-- The quotient is uniformly bounded by the squared index throughout the latent arm. Given [the displayed inputs and assumptions](hyp:L,x,hx), [the stated mathematical conclusion holds](goal). -/
lemma endpointF_le_index_sq (L : ℕ) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    (endpointF L).eval x ≤ (L : ℝ)^2 := by
  by_cases hz : x = 0
  · subst x; exact le_of_eq (endpointF_eval_zero L)
  have hxp : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hz)
  let u := Real.arcsin (Real.sqrt x)
  have hs : Real.sin u = Real.sqrt x :=
    Real.sin_arcsin (by linarith [Real.sqrt_nonneg x]) ((Real.sqrt_le_one).mpr hx.2)
  have hs2 : (Real.sin u)^2 = x := by rw [hs, Real.sq_sqrt hx.1]
  have hid := endpointF_sine_identity L u
  rw [hs2] at hid
  have hb := endpoint_sin_nat_mul_bound L u
  have hsq := mul_self_le_mul_self (abs_nonneg (Real.sin ((L : ℝ)*u))) hb
  rw [← sq, ← sq, sq_abs, mul_pow, sq_abs, hs2] at hsq
  nlinarith

/-- Away from zero the quotient is bounded by the reciprocal score. Given [the displayed inputs and assumptions](hyp:L,x,hx), [the stated mathematical conclusion holds](goal). -/
lemma endpointF_le_inv_score (L : ℕ) (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) 1) :
    (endpointF L).eval x ≤ x⁻¹ := by
  have hc : -1 ≤ (chebyshev L).eval (1 - 2*x) := by
    rw [chebyshev, ← Real.cos_arccos (show -1 ≤ 1 - 2*x by linarith [hx.2])
      (show 1 - 2*x ≤ 1 by linarith [hx.1]), Polynomial.Chebyshev.T_real_cos]
    exact Real.neg_one_le_cos _
  have hid := endpointF_mul_score L x
  apply (mul_le_mul_iff_left₀ hx.1).mp
  rw [inv_mul_cancel₀ hx.1.ne']
  nlinarith

/-- On the endpoint window, Jordan's sine inequality gives a squared-index lower bound. Given [the displayed inputs and assumptions](hyp:L,hL,x,hx), [the stated mathematical conclusion holds](goal). -/
lemma endpointF_lower_window (L : ℕ) (hL : 1 ≤ L) (x : ℝ)
    (hx : x ∈ Icc (0 : ℝ) (1 / (16*(L : ℝ)^2))) :
    (2 / Real.pi)^2 * (L : ℝ)^2 ≤ (endpointF L).eval x := by
  have hLp : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have ha : 0 < 2 / Real.pi := by positivity
  have ha1 : 2 / Real.pi ≤ 1 := (div_le_one Real.pi_pos).mpr (by linarith [Real.two_le_pi])
  by_cases hz : x = 0
  · subst x
    rw [endpointF_eval_zero]
    exact mul_le_of_le_one_left (sq_nonneg _) (by nlinarith)
  have hxp : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hz)
  have hx1 : x ≤ 1 := by
    have hb := (le_div_iff₀ (by positivity : 0 < 16*(L : ℝ)^2)).mp hx.2
    nlinarith
  let u := Real.arcsin (Real.sqrt x)
  have hu : 0 ≤ u := Real.arcsin_nonneg.mpr (Real.sqrt_nonneg x)
  have hs : Real.sin u = Real.sqrt x := Real.sin_arcsin
    (by linarith [Real.sqrt_nonneg x]) (Real.sqrt_le_one.mpr hx1)
  have hs2 : (Real.sin u)^2 = x := by rw [hs, Real.sq_sqrt hx.1]
  have hbase := Real.mul_le_sin hu (Real.arcsin_le_pi_div_two (Real.sqrt x))
  have hroot : (L : ℝ) * Real.sqrt x ≤ 1/4 := by
    have hb := (le_div_iff₀ (by positivity : 0 < 16*(L : ℝ)^2)).mp hx.2
    nlinarith [Real.sq_sqrt hx.1, mul_nonneg hLp.le (Real.sqrt_nonneg x)]
  have hLu : (L : ℝ) * u ≤ Real.pi / 2 := by
    rw [hs] at hbase
    have hm := mul_le_mul_of_nonneg_left hbase hLp.le
    have hp := (div_le_iff₀ Real.pi_pos).mp
      (show 2*((L : ℝ)*u)/Real.pi ≤ 1/4 by
        calc
          _ = (L : ℝ) * (2/Real.pi*u) := by ring
          _ ≤ (L : ℝ) * Real.sqrt x := hm
          _ ≤ 1/4 := hroot)
    linarith [Real.pi_pos]
  have hlow := Real.mul_le_sin (mul_nonneg hLp.le hu) hLu
  have hup : Real.sin u ≤ u := Real.sin_le hu
  have hsinL : 0 ≤ Real.sin ((L : ℝ)*u) :=
    le_trans (mul_nonneg ha.le (mul_nonneg hLp.le hu)) hlow
  have hscale : (2/Real.pi) * (L : ℝ) * Real.sin u ≤ Real.sin ((L : ℝ)*u) := by
    calc
      _ ≤ (2/Real.pi) * (L : ℝ) * u :=
        mul_le_mul_of_nonneg_left hup (mul_nonneg ha.le hLp.le)
      _ ≤ _ := by simpa only [mul_assoc] using hlow
  have hsq := mul_self_le_mul_self
    (mul_nonneg (mul_nonneg ha.le hLp.le) (by rw [hs]; positivity)) hscale
  have hid := endpointF_sine_identity L u
  rw [← sq, ← sq, mul_pow, mul_pow, hs2, ← hid, hs2] at hsq
  exact (mul_le_mul_iff_left₀ hxp).mp (by simpa only [mul_comm] using hsq)

/-- The nonnegative cubed endpoint quotient has strictly positive normalization for every positive index. Given [the displayed inputs and assumptions](hyp:L,hL), [the stated mathematical conclusion holds](goal). -/
lemma endpointNormalizer_pos (L : ℕ) (hL : 1 ≤ L) :
    0 < ∫ t in (0 : ℝ)..1, (endpointF L).eval t ^ 3 := by
  apply intervalIntegral.integral_pos (by norm_num)
  · fun_prop
  · intro x hx
    exact pow_nonneg (endpointF_nonneg L x ⟨hx.1.le, hx.2⟩) 3
  · refine ⟨0, by norm_num, ?_⟩
    rw [endpointF_eval_zero]
    have hLp : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
    positivity

/-- Integrating the endpoint window gives the normalization lower bound from the roadmap. Given [the displayed inputs and assumptions](hyp:L,hL), [the stated mathematical conclusion holds](goal). -/
lemma endpointNormalizer_lower_bound (L : ℕ) (hL : 1 ≤ L) :
    4 / Real.pi^6 * (L : ℝ)^4 ≤
      ∫ t in (0 : ℝ)..1, (endpointF L).eval t ^ 3 := by
  have hLp : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  let δ : ℝ := 1 / (16*(L : ℝ)^2)
  have hδ : 0 ≤ δ := by positivity
  have hδ1 : δ ≤ 1 := by
    apply (div_le_one (by positivity : 0 < 16*(L : ℝ)^2)).mpr
    nlinarith
  have hint : IntervalIntegrable (fun t => (endpointF L).eval t ^ 3) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hsub : (∫ t in (0 : ℝ)..δ, (endpointF L).eval t ^ 3) ≤
      ∫ t in (0 : ℝ)..1, (endpointF L).eval t ^ 3 := by
    apply intervalIntegral.integral_mono_interval le_rfl hδ hδ1 _ hint
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact pow_nonneg (endpointF_nonneg L t ⟨ht.1.le, ht.2⟩) 3
  have hlocal : (∫ _t in (0 : ℝ)..δ, ((2/Real.pi)^2*(L : ℝ)^2)^3) ≤
      ∫ t in (0 : ℝ)..δ, (endpointF L).eval t ^ 3 := by
    apply intervalIntegral.integral_mono_on hδ
      (continuous_const.intervalIntegrable 0 δ)
      (((endpointF L).continuous.pow 3).intervalIntegrable 0 δ)
    intro t ht
    exact pow_le_pow_left₀ (by positivity) (endpointF_lower_window L hL t ht) 3
  have heq : (∫ _t in (0 : ℝ)..δ, ((2/Real.pi)^2*(L : ℝ)^2)^3) =
      4 / Real.pi^6 * (L : ℝ)^4 := by
    rw [intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul, δ]
    field_simp
    <;> ring
  rw [heq] at hlocal
  exact hlocal.trans hsub

/-- The endpoint kernel has unit mass because its cubed quotient normalization is nonzero. Given [the displayed inputs and assumptions](hyp:L,hL), [the stated mathematical conclusion holds](goal). -/
lemma endpointKernel_integral_one (L : ℕ) (hL : 1 ≤ L) :
    (∫ x in (0 : ℝ)..1, (endpointKernel L).eval x) = 1 := by
  have hz := endpointNormalizer_pos L hL
  simp only [endpointKernel, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow]
  rw [intervalIntegral.integral_const_mul]
  exact inv_mul_cancel₀ hz.ne'

/-- Normalization converts the quotient bound into a uniform squared-index kernel envelope. Given [the displayed inputs and assumptions](hyp:L,hL,x,hx), [the stated mathematical conclusion holds](goal). -/
lemma endpointKernel_le_index_sq (L : ℕ) (hL : 1 ≤ L) (x : ℝ)
    (hx : x ∈ Icc (0 : ℝ) 1) :
    (endpointKernel L).eval x ≤ (Real.pi^6 / 4) * (L : ℝ)^2 := by
  let Z : ℝ := ∫ t in (0 : ℝ)..1, (endpointF L).eval t ^ 3
  have hZ : 0 < Z := endpointNormalizer_pos L hL
  have hlow := endpointNormalizer_lower_bound L hL
  have hc : 0 ≤ Real.pi^6 / 4 * (L : ℝ)^2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hlow hc
  have heq : (Real.pi^6 / 4 * (L : ℝ)^2) *
      (4 / Real.pi^6 * (L : ℝ)^4) = (L : ℝ)^6 := by
    field_simp
    <;> ring
  rw [heq] at hmul
  have hcube : ((endpointF L).eval x)^3 ≤ (L : ℝ)^6 := by
    have h := pow_le_pow_left₀ (endpointF_nonneg L x hx) (endpointF_le_index_sq L x hx) 3
    simpa only [← pow_mul] using h
  simp only [endpointKernel, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow]
  change Z⁻¹ * ((endpointF L).eval x)^3 ≤ _
  apply (mul_le_mul_iff_right₀ hZ).mp
  calc
    Z * (Z⁻¹ * ((endpointF L).eval x)^3) = ((endpointF L).eval x)^3 := by
      rw [← mul_assoc, mul_inv_cancel₀ hZ.ne', one_mul]
    _ ≤ (L : ℝ)^6 := hcube
    _ ≤ Z * (Real.pi^6 / 4 * (L : ℝ)^2) := by
      simpa only [Z, mul_comm] using hmul

/-- Unit mass and the uniform kernel envelope give its square-mass bound. Given [the displayed inputs and assumptions](hyp:L,hL), [the stated mathematical conclusion holds](goal). -/
lemma endpointKernel_square_integral_bound (L : ℕ) (hL : 1 ≤ L) :
    (∫ x in (0 : ℝ)..1, ((endpointKernel L).eval x)^2) ≤
      (Real.pi^6 / 4) * (L : ℝ)^2 := by
  calc
    _ ≤ ∫ x in (0 : ℝ)..1,
        (Real.pi^6 / 4 * (L : ℝ)^2) * (endpointKernel L).eval x := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (((endpointKernel L).continuous.pow 2).intervalIntegrable 0 1)
        ((continuous_const.mul (endpointKernel L).continuous).intervalIntegrable 0 1)
      intro x hx
      simpa only [Pi.mul_apply, pow_two] using mul_le_mul_of_nonneg_right
        (endpointKernel_le_index_sq L hL x hx) (endpointKernel_nonneg L x hx)
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, endpointKernel_integral_one L hL, mul_one]

/-- The reciprocal-score quotient bound and normalization give the cubic kernel tail. Given [the displayed inputs and assumptions](hyp:L,hL,x,hx), [the stated mathematical conclusion holds](goal). -/
lemma endpointKernel_tail_bound (L : ℕ) (hL : 1 ≤ L) (x : ℝ)
    (hx : x ∈ Ioc (0 : ℝ) 1) :
    (endpointKernel L).eval x ≤ (Real.pi^6 / 4) * ((L : ℝ)^2)⁻¹^2 * x ^ (-3 : ℝ) := by
  let Z : ℝ := ∫ t in (0 : ℝ)..1, (endpointF L).eval t ^ 3
  have hZ : 0 < Z := endpointNormalizer_pos L hL
  have hLp : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hlow := endpointNormalizer_lower_bound L hL
  have hcube := pow_le_pow_left₀ (endpointF_nonneg L x ⟨hx.1.le, hx.2⟩)
    (endpointF_le_inv_score L x hx) 3
  have heq : (Real.pi^6 / 4 * ((L : ℝ)^2)⁻¹^2 * x ^ (-3 : ℝ)) *
      (4 / Real.pi^6 * (L : ℝ)^4) = x⁻¹^3 := by
    rw [Real.rpow_neg hx.1.le]
    norm_num [Real.rpow_ofNat]
    field_simp
    <;> ring
  have hm := mul_le_mul_of_nonneg_left hlow
    (show 0 ≤ Real.pi^6 / 4 * ((L : ℝ)^2)⁻¹^2 * x ^ (-3 : ℝ) by
      exact mul_nonneg (by positivity) (Real.rpow_nonneg hx.1.le _))
  rw [heq] at hm
  simp only [endpointKernel, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow]
  change Z⁻¹ * ((endpointF L).eval x)^3 ≤ _
  apply (mul_le_mul_iff_right₀ hZ).mp
  calc
    Z * (Z⁻¹ * ((endpointF L).eval x)^3) = ((endpointF L).eval x)^3 := by
      rw [← mul_assoc, mul_inv_cancel₀ hZ.ne', one_mul]
    _ ≤ x⁻¹^3 := hcube
    _ ≤ Z * _ := by simpa only [Z, mul_comm] using hm

/-- Splitting at the squared-index resolution bounds the endpoint bias moment. Given [the displayed inputs and assumptions](hyp:β,hβ,L,hL), [the stated mathematical conclusion holds](goal). -/
lemma endpointKernel_moment_bound (β : ℝ) (hβ : β ∈ Ioc (0 : ℝ) 1)
    (L : ℕ) (hL : 1 ≤ L) :
    kernelMoment L β ≤ (2 * (Real.pi^6 / 4)) * (L : ℝ) ^ (-2 * β) := by
  let δ : ℝ := ((L : ℝ)^2)⁻¹
  let C : ℝ := Real.pi^6 / 4
  have hLp : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hδ : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    apply inv_le_one_of_one_le₀
    nlinarith
  have hC : 0 ≤ C := by positivity
  have hβ0 : 0 ≤ β := hβ.1.le
  have hcont : Continuous (fun x : ℝ => x ^ β * (endpointKernel L).eval x) := by
    fun_prop
  have hlo : (∫ x in (0 : ℝ)..δ, x ^ β * (endpointKernel L).eval x) ≤ C * δ ^ β := by
    calc
      _ ≤ ∫ _x in (0 : ℝ)..δ, δ ^ β * (C * (L : ℝ)^2) := by
        apply intervalIntegral.integral_mono_on hδ.le
          (hcont.intervalIntegrable 0 δ) (continuous_const.intervalIntegrable 0 δ)
        intro x hx
        exact mul_le_mul (Real.rpow_le_rpow hx.1 hx.2 hβ.1.le)
          (endpointKernel_le_index_sq L hL x ⟨hx.1, hx.2.trans hδ1⟩)
          (endpointKernel_nonneg L x ⟨hx.1, hx.2.trans hδ1⟩)
          (Real.rpow_nonneg hδ.le β)
      _ = C * δ ^ β := by
        rw [intervalIntegral.integral_const]
        simp only [sub_zero, smul_eq_mul]
        dsimp [δ]
        field_simp
  have hpow : ContinuousOn (fun x : ℝ => x ^ (β - 3)) (Icc δ 1) := by
    apply ContinuousOn.rpow_const continuousOn_id
    intro x hx
    exact Or.inl (ne_of_gt (hδ.trans_le hx.1))
  have hint : IntervalIntegrable (fun x : ℝ => x ^ (β - 3)) volume δ 1 :=
    hpow.intervalIntegrable_of_Icc hδ1
  have hhi : (∫ x in δ..1, x ^ β * (endpointKernel L).eval x) ≤ C * δ ^ β := by
    calc
      _ ≤ ∫ x in δ..1, C * δ^2 * x ^ (β - 3) := by
        apply intervalIntegral.integral_mono_on hδ1
          (hcont.intervalIntegrable δ 1) (hint.const_mul (C * δ^2))
        intro x hx
        have hxpos := hδ.trans_le hx.1
        calc
          _ ≤ x ^ β * (C * δ^2 * x ^ (-3 : ℝ)) :=
            mul_le_mul_of_nonneg_left (endpointKernel_tail_bound L hL x ⟨hxpos, hx.2⟩)
              (Real.rpow_nonneg hxpos.le β)
          _ = C * δ^2 * x ^ (β - 3) := by
            rw [sub_eq_add_neg, Real.rpow_add hxpos]
            ring
      _ = C * δ^2 * ((δ ^ (β - 2) - 1) / (2 - β)) := by
        rw [intervalIntegral.integral_const_mul, integral_rpow]
        · simp only [Real.one_rpow]
          congr 1
          have he : β - 3 + 1 = β - 2 := by ring
          rw [he]
          field_simp [show β - 2 ≠ 0 by linarith [hβ.2],
            show 2 - β ≠ 0 by linarith [hβ.2]]
          <;> ring
        · right
          refine ⟨by linarith [hβ.2], ?_⟩
          rw [uIcc_of_le hδ1]
          exact fun h => (not_le_of_gt hδ) h.1
      _ ≤ C * δ^2 * δ ^ (β - 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply (div_le_iff₀ (show 0 < 2 - β by linarith [hβ.2])).mpr
        nlinarith [Real.rpow_nonneg hδ.le (β - 2), hβ.2]
      _ = C * δ ^ β := by
        rw [Real.rpow_sub hδ]
        norm_num [Real.rpow_ofNat]
        field_simp
  have hres : δ ^ β = (L : ℝ) ^ (-2 * β) := by
    have hd : δ = (L : ℝ) ^ (-2 : ℝ) := by
      dsimp [δ]
      rw [Real.rpow_neg hLp.le]
      norm_num [Real.rpow_ofNat]
    rw [hd, ← Real.rpow_mul hLp.le]
  unfold kernelMoment
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable 0 δ) (hcont.intervalIntegrable δ 1)]
  calc
    _ ≤ C * δ ^ β + C * δ ^ β := add_le_add hlo hhi
    _ = _ := by rw [hres]; dsimp [C]; ring

/-- Positive normalized endpoint kernels and their bias and square-mass bounds. Given [the displayed inputs and assumptions](hyp:β,hβ), [the stated mathematical conclusion holds](goal). -/
-- @node: lem:positive-endpoint
lemma positive_endpoint (β : ℝ) (hβ : β ∈ Ioc (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℕ, 1 ≤ L → -- @realizes C(beta-dependent positive constant)
      (∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ (endpointKernel L).eval x) ∧
      (∫ x in (0 : ℝ)..1, (endpointKernel L).eval x) = 1 ∧
      kernelMoment L β ≤ C * (L : ℝ) ^ (-2 * β) ∧
      (∫ x in (0 : ℝ)..1, ((endpointKernel L).eval x)^2) ≤ C * (L : ℝ)^2 := by
  suffices hmoment : ∃ C : ℝ, 0 < C ∧ ∀ L : ℕ, 1 ≤ L →
      kernelMoment L β ≤ C * (L : ℝ) ^ (-2 * β) by
    obtain ⟨C, hC, hb⟩ := hmoment
    refine ⟨max C (Real.pi^6 / 4), lt_max_of_lt_left hC, ?_⟩
    intro L hL
    refine ⟨endpointKernel_nonneg L, endpointKernel_integral_one L hL, ?_, ?_⟩
    · exact (hb L hL).trans (mul_le_mul_of_nonneg_right
        (le_max_left _ _) (Real.rpow_nonneg (by positivity) _))
    · exact (endpointKernel_square_integral_bound L hL).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _))
  refine ⟨2 * (Real.pi^6 / 4), by positivity, ?_⟩
  exact fun L hL => endpointKernel_moment_bound β hβ L hL
/-- The odd-parity Legendre derivative weights have the exact endpoint total. Given [the displayed inputs and assumptions](hyp:j), [the stated mathematical conclusion holds](goal). -/
lemma shiftedLegendre_parity_weight_sum (j : ℕ) :
    2 * (∑ k ∈ (Finset.range j).filter (fun k => Odd (j-k)),
      (2 * (k : ℝ) + 1)) = (j : ℝ) * (j+1) := by
  have hall (n : ℕ) : (∑ k ∈ Finset.range n, (2 * (k : ℝ) + 1)) = (n : ℝ)^2 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  induction j with
  | zero => simp
  | succ j ih =>
    have hsum :
        (∑ k ∈ (Finset.range (j+1)).filter (fun k => Odd (j+1-k)), (2*(k : ℝ)+1)) +
        (∑ k ∈ (Finset.range j).filter (fun k => Odd (j-k)), (2*(k : ℝ)+1)) =
        ((j : ℝ)+1)^2 := by
      simp only [Finset.sum_filter]
      rw [Finset.sum_range_succ]
      have hflip : (∑ k ∈ Finset.range j,
          if Odd (j+1-k) then (2*(k : ℝ)+1) else 0) +
          (∑ k ∈ Finset.range j,
          if Odd (j-k) then (2*(k : ℝ)+1) else 0) = (j : ℝ)^2 := by
        rw [← Finset.sum_add_distrib, ← hall j]
        apply Finset.sum_congr rfl
        intro k hk
        have heq : j+1-k = (j-k)+1 := by have := Finset.mem_range.mp hk; omega
        rw [heq]
        by_cases ho : Odd (j-k) <;> simp [Nat.odd_add_one, ho]
      have hone : j+1-j = 1 := by omega
      simp only [hone, show Odd (1 : ℕ) from odd_one, if_true]
      nlinarith [hflip]
    simp only [Nat.cast_succ]
    nlinarith [hsum]
/-- The cited unit bound and derivative expansion imply the sharp endpoint derivative bound. Given [the displayed inputs and assumptions](hyp:hleg,j,hexp), [the stated mathematical conclusion holds](goal). -/
lemma shiftedLegendre_deriv_bound_of_expansion (hleg : ClassicalLegendreFacts) (j : ℕ)
    (hexp : ∀ t : ℝ, deriv (shiftedLegendre j) t =
      2 * ∑ k ∈ (Finset.range j).filter (fun k => Odd (j-k)),
        (2 * (k : ℝ) + 1) * shiftedLegendre k t) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, |deriv (shiftedLegendre j) t| ≤ (j : ℝ) * (j+1) := by
  intro t ht
  have hunit (k : ℕ) : |shiftedLegendre k t| ≤ 1 := by
    exact (hleg k 0).2.2.1 (2*t-1) ⟨by linarith [ht.1], by linarith [ht.2]⟩
  rw [hexp t, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ ≤ 2 * ∑ k ∈ (Finset.range j).filter (fun k => Odd (j-k)),
        |(2 * (k : ℝ) + 1) * shiftedLegendre k t| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)
    _ ≤ 2 * ∑ k ∈ (Finset.range j).filter (fun k => Odd (j-k)),
        (2 * (k : ℝ) + 1) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro k hk
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * (k : ℝ) + 1)]
      exact mul_le_of_le_one_right (by positivity) (hunit k)
    _ = _ := shiftedLegendre_parity_weight_sum j

/-- Derivative expansion with the odd parity restriction, and its endpoint bound. Given [the displayed inputs and assumptions](hyp:j,hj), [the stated mathematical conclusion holds](goal). -/
-- @node: lem:shifted-legendre-derivative
lemma shifted_legendre_derivative (j : ℕ) (hj : 1 ≤ j) :
    (∀ t : ℝ, deriv (shiftedLegendre j) t =
      2 * ∑ k ∈ (Finset.range j).filter (fun k => Odd (j-k)),
        (2 * (k : ℝ) + 1) * shiftedLegendre k t) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, |deriv (shiftedLegendre j) t| ≤ (j : ℝ) * (j+1)) := by
  let legendre_of_gate : ClassicalLegendreFacts := classicalLegendreFacts
  suffices hexp : ∀ t : ℝ, deriv (shiftedLegendre j) t =
      2 * ∑ k ∈ (Finset.range j).filter (fun k => Odd (j-k)),
        (2 * (k : ℝ) + 1) * shiftedLegendre k t by
    exact ⟨hexp, shiftedLegendre_deriv_bound_of_expansion legendre_of_gate j hexp⟩
  exact shiftedLegendre_derivative_expansion legendre_of_gate j
/-- Finite shifted Legendre expansions have the diagonal square integral prescribed by orthogonality. Given [the displayed inputs and assumptions](hyp:hleg,s,c), [the stated mathematical conclusion holds](goal). -/
lemma shiftedLegendre_sum_square_integral (hleg : ClassicalLegendreFacts)
    (s : Finset ℕ) (c : ℕ → ℝ) :
    (∫ x in (0 : ℝ)..1, (∑ k ∈ s, c k * shiftedLegendre k x)^2) =
      ∑ k ∈ s, (c k)^2 / (2*(k : ℝ)+1) := by
  classical
  have hint (j k : ℕ) : IntervalIntegrable
      (fun x => c j * shiftedLegendre j x * (c k * shiftedLegendre k x)) volume 0 1 := by
    apply Continuous.intervalIntegrable
    unfold shiftedLegendre
    fun_prop
  simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [intervalIntegral.integral_finsetSum]
    · have heq (k : ℕ) :
          (∫ x in (0 : ℝ)..1, c j * shiftedLegendre j x * (c k * shiftedLegendre k x)) =
            if j = k then (c j)^2 / (2*(j : ℝ)+1) else 0 := by
        have hf : (fun x => c j * shiftedLegendre j x * (c k * shiftedLegendre k x)) =
            (fun x => (c j * c k) * (legendreP j (2*x-1) * legendreP k (2*x-1))) := by
          funext x
          unfold shiftedLegendre
          ring
        rw [hf, intervalIntegral.integral_const_mul, shiftedLegendre_orthogonal hleg]
        split_ifs with h
        · subst k; ring
        · ring
      simp_rw [heq]
      simp [hj, pow_two]
    · intro k hk
      exact hint j k
  · intro j hj
    apply Continuous.intervalIntegrable
    unfold shiftedLegendre
    fun_prop

/-- Orthogonal expansion gives Parseval's identity for every degree-bounded real polynomial. Given [the displayed inputs and assumptions](hyp:hleg,p,m,hm), [the stated mathematical conclusion holds](goal). -/
lemma polynomial_shiftedLegendre_parseval (hleg : ClassicalLegendreFacts)
    (p : Polynomial ℝ) (m : ℕ) (hm : p.natDegree ≤ m) :
    (∫ x in (0 : ℝ)..1, (p.eval x)^2) =
      ∑ k ∈ Finset.range (m+1),
        ((2*(k : ℝ)+1) * (∫ x in (0 : ℝ)..1, p.eval x * shiftedLegendre k x))^2 /
          (2*(k : ℝ)+1) := by
  have hd : p.degree < (m+1 : ℕ) :=
    lt_of_le_of_lt (Polynomial.degree_le_natDegree) (by exact_mod_cast (Nat.lt_succ_of_le hm))
  conv_lhs => arg 1; ext x; rw [polynomial_shiftedLegendre_expansion hleg p (m+1) hd x]
  exact shiftedLegendre_sum_square_integral hleg _ _

/-- Parseval identifies the square mass of every iterated derivative with the
weighted squared norm of the iterated differentiation coefficients. Given [the displayed inputs and assumptions](hyp:hleg,p,m,j,hm), [the stated mathematical conclusion holds](goal). -/
lemma polynomial_iterated_derivative_parseval (hleg : ClassicalLegendreFacts)
    (p : Polynomial ℝ) (m j : ℕ) (hm : p.natDegree ≤ m) :
    (∫ x in (0 : ℝ)..1, ((polyDeriv j p).eval x)^2) =
      ∑ k ∈ Finset.range (m+1),
        (((legendreDerivativeAction m)^[j])
          (fun l => (2*(l : ℝ)+1) *
            (∫ x in (0 : ℝ)..1, p.eval x * shiftedLegendre l x)) k)^2 /
          (2*(k : ℝ)+1) := by
  have hp := polynomial_legendre_coefficient_identity hleg p m hm
  have hd := congrArg (polyDeriv j) hp
  rw [legendre_expansion_iterated_derivative hleg] at hd
  rw [hd]
  simp only [Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
    forwardLegendrePolynomial_eval]
  exact shiftedLegendre_sum_square_integral hleg _ _

/-- The parity-restricted derivative expansion has exact square mass twice its endpoint weight. Given [the displayed inputs and assumptions](hyp:hleg,j), [the stated mathematical conclusion holds](goal). -/
lemma shiftedLegendre_derivative_square_integral (hleg : ClassicalLegendreFacts) (j : ℕ) :
    (∫ x in (0 : ℝ)..1, (deriv (shiftedLegendre j) x)^2) = 2*(j : ℝ)*(j+1) := by
  simp_rw [shiftedLegendre_derivative_expansion hleg j]
  have hf : (fun x => (2 * ∑ k ∈ (Finset.range j).filter (fun k => Odd (j-k)),
      (2*(k : ℝ)+1) * shiftedLegendre k x)^2) =
      (fun x => 4 * (∑ k ∈ (Finset.range j).filter (fun k => Odd (j-k)),
      (2*(k : ℝ)+1) * shiftedLegendre k x)^2) := by funext x; ring
  rw [hf, intervalIntegral.integral_const_mul, shiftedLegendre_sum_square_integral hleg]
  have hs : (∑ k ∈ (Finset.range j).filter (fun k => Odd (j-k)),
      (2*(k : ℝ)+1)^2 / (2*(k : ℝ)+1)) =
      ∑ k ∈ (Finset.range j).filter (fun k => Odd (j-k)), (2*(k : ℝ)+1) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hn : 2*(k : ℝ)+1 ≠ 0 := by positivity
    field_simp
  rw [hs]
  nlinarith [shiftedLegendre_parity_weight_sum j]

/-- The Legendre coefficient matrix and weighted Cauchy--Schwarz bound the first derivative square mass. Given [the displayed inputs and assumptions](hyp:hleg,p,m,hm), [the stated mathematical conclusion holds](goal). -/
lemma polynomial_first_derivative_square_bound (hleg : ClassicalLegendreFacts)
    (p : Polynomial ℝ) (m : ℕ) (hm : p.natDegree ≤ m) :
    (∫ x in (0 : ℝ)..1, (p.derivative.eval x)^2) ≤
      4 * ((m : ℝ)+1)^4 * (∫ x in (0 : ℝ)..1, (p.eval x)^2) := by
  classical
  let c (k : ℕ) : ℝ := (2*(k : ℝ)+1) *
    (∫ x in (0 : ℝ)..1, p.eval x * shiftedLegendre k x)
  let E : ℝ := ∫ x in (0 : ℝ)..1, (p.eval x)^2
  have hE : 0 ≤ E := intervalIntegral.integral_nonneg (by norm_num) (by
    intro x hx; exact sq_nonneg _)
  have hparse : (∑ k ∈ Finset.range (m+1), (c k)^2 / (2*(k : ℝ)+1)) = E :=
    (polynomial_shiftedLegendre_parseval hleg p m hm).symm
  have hd : p.degree < (m+1 : ℕ) :=
    lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast (Nat.lt_succ_of_le hm))
  have hexp : (fun x => p.eval x) =
      (fun x => ∑ k ∈ Finset.range (m+1), c k * shiftedLegendre k x) := by
    funext x
    exact polynomial_shiftedLegendre_expansion hleg p (m+1) hd x
  have hder (x : ℝ) : p.derivative.eval x =
      ∑ k ∈ Finset.range (m+1), c k * deriv (shiftedLegendre k) x := by
    rw [← Polynomial.deriv, hexp]
    rw [show (fun x => ∑ k ∈ Finset.range (m+1), c k * shiftedLegendre k x) =
      (∑ k ∈ Finset.range (m+1), fun x => c k * shiftedLegendre k x) by
        ext x; simp]
    rw [deriv_sum]
    · simp_rw [deriv_const_mul_field]
    · intro k hk
      exact ((shiftedLegendre_differentiable k).differentiableAt).const_mul _
  have hpoint (x : ℝ) : (p.derivative.eval x)^2 ≤
      E * ∑ k ∈ Finset.range (m+1), (2*(k : ℝ)+1) * (deriv (shiftedLegendre k) x)^2 := by
    rw [hder]
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.range (m+1))
      (r := fun k => c k * deriv (shiftedLegendre k) x)
      (f := fun k => (c k)^2 / (2*(k : ℝ)+1))
      (g := fun k => (2*(k : ℝ)+1) * (deriv (shiftedLegendre k) x)^2)
      (by intro k hk; positivity) (by intro k hk; positivity)
      (by
        intro k hk
        have hn : 2*(k : ℝ)+1 ≠ 0 := by positivity
        apply le_of_eq
        field_simp
        <;> ring)
    rwa [hparse] at hcs
  have hcont (k : ℕ) : Continuous (fun x => deriv (shiftedLegendre k) x) := by
    have he : (fun x => deriv (shiftedLegendre k) x) =
        (fun x => (forwardLegendrePolynomial k).derivative.eval x) := by
      funext x; exact (forwardLegendrePolynomial_derivative_eval k x).symm
    rw [he]
    fun_prop
  have hint : IntervalIntegrable
      (fun x => E * ∑ k ∈ Finset.range (m+1),
        (2*(k : ℝ)+1) * (deriv (shiftedLegendre k) x)^2) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hi := intervalIntegral.integral_mono (by norm_num : (0 : ℝ) ≤ 1)
    (p.derivative.continuous.pow 2 |>.intervalIntegrable 0 1) hint hpoint
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum] at hi
  · simp_rw [intervalIntegral.integral_const_mul,
      shiftedLegendre_derivative_square_integral hleg] at hi
    have hweights : (∑ k ∈ Finset.range (m+1),
        (2*(k : ℝ)+1) * (2*(k : ℝ)*(k+1))) ≤ 4*((m : ℝ)+1)^4 := by
      calc
        _ ≤ ∑ k ∈ Finset.range (m+1),
            (2*(k : ℝ)+1) * (2*((m : ℝ)+1)^2) := by
          apply Finset.sum_le_sum
          intro k hk
          have hkm : (k : ℝ) ≤ m := by exact_mod_cast (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          nlinarith [show (0 : ℝ) ≤ k by positivity]
        _ = 2*((m : ℝ)+1)^4 := by
          rw [← Finset.sum_mul]
          have hs (n : ℕ) : (∑ k ∈ Finset.range n, (2*(k : ℝ)+1)) = (n : ℝ)^2 := by
            induction n with
            | zero => simp
            | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
          rw [hs]
          push_cast
          ring
        _ ≤ _ := by nlinarith [sq_nonneg (((m : ℝ)+1)^2)]
    exact hi.trans (by simpa only [E, mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left hweights hE)
  · intro k hk
    apply Continuous.intervalIntegrable
    exact continuous_const.mul ((hcont k).pow 2)

/-- The first-order case of the factorial bound follows from its Legendre square-mass estimate. Given [the displayed inputs and assumptions](hyp:hleg,p,m,hm), [the stated mathematical conclusion holds](goal). -/
lemma polynomial_first_derivative_norm_bound (hleg : ClassicalLegendreFacts)
    (p : Polynomial ℝ) (m : ℕ) (hm : p.natDegree ≤ m) :
    Real.sqrt (∫ x in (0 : ℝ)..1, (p.derivative.eval x)^2) ≤
      4 * ((m : ℝ)+1)^2 * Real.sqrt (∫ x in (0 : ℝ)..1, (p.eval x)^2) := by
  have hE : 0 ≤ ∫ x in (0 : ℝ)..1, (p.eval x)^2 :=
    intervalIntegral.integral_nonneg (by norm_num) (by intro x hx; exact sq_nonneg _)
  have hb := polynomial_first_derivative_square_bound hleg p m hm
  have hsqE := Real.sq_sqrt hE
  apply (Real.sqrt_le_left (by positivity)).mpr
  calc
    _ ≤ 4 * ((m : ℝ)+1)^4 * (∫ x in (0 : ℝ)..1, (p.eval x)^2) := hb
    _ ≤ 16 * ((m : ℝ)+1)^4 * (∫ x in (0 : ℝ)..1, (p.eval x)^2) := by
      nlinarith [mul_nonneg (pow_nonneg (show 0 ≤ (m : ℝ)+1 by positivity) 4) hE]
    _ = _ := by simp only [mul_pow, hsqE]; ring

/-- Factorial gain in the interval square-integral derivative bound. Given [the displayed inputs and assumptions](hyp:p,m,j,hm,hj,hjm), [the stated mathematical conclusion holds](goal). -/
-- @node: lem:factorial-derivatives
lemma factorial_derivatives (p : Polynomial ℝ) (m j : ℕ) (hm : p.natDegree ≤ m)
    (hj : 1 ≤ j) (hjm : j ≤ m) : -- @realizes Polynomial(real polynomial with degree scope)
    Real.sqrt (∫ x in (0 : ℝ)..1, ((polyDeriv j p).eval x)^2) ≤
      4^j * ((m : ℝ)+1)^(2*j) * Real.sqrt (∫ x in (0 : ℝ)..1, (p.eval x)^2) /
        (Nat.factorial j : ℝ) := by
  let legendre_of_gate : ClassicalLegendreFacts := classicalLegendreFacts
  by_cases hj1 : j = 1
  · subst j
    simpa [polyDeriv] using polynomial_first_derivative_norm_bound legendre_of_gate p m hm
  · let c : ℕ → ℝ := fun l => (2*(l : ℝ)+1) *
      (∫ x in (0 : ℝ)..1, p.eval x * shiftedLegendre l x)
    let A : ℝ := 4^j * ((m : ℝ)+1)^(2*j) / (Nat.factorial j : ℝ)
    have hbase : (∫ x in (0 : ℝ)..1, (p.eval x)^2) =
        ∑ k ∈ Finset.range (m+1), (c k)^2 / (2*(k : ℝ)+1) :=
      polynomial_shiftedLegendre_parseval legendre_of_gate p m hm
    have hderiv : (∫ x in (0 : ℝ)..1, ((polyDeriv j p).eval x)^2) =
        ∑ k ∈ Finset.range (m+1),
          (((legendreDerivativeAction m)^[j]) c k)^2 / (2*(k : ℝ)+1) :=
      polynomial_iterated_derivative_parseval legendre_of_gate p m j hm
    have hcoeff : (∑ k ∈ Finset.range (m+1),
        (((legendreDerivativeAction m)^[j]) c k)^2 / (2*(k : ℝ)+1)) ≤
        A^2 * (∑ k ∈ Finset.range (m+1), (c k)^2 / (2*(k : ℝ)+1)) := by
      -- The increasing-chain prefix bound supplies the factorial gain;
      -- weighted Cauchy--Schwarz transfers it to the coefficient norm.
      exact legendreDerivativeAction_factorial_bound m j hj c
    have hE : 0 ≤ ∫ x in (0 : ℝ)..1, (p.eval x)^2 :=
      intervalIntegral.integral_nonneg (by norm_num) (by intro x hx; exact sq_nonneg _)
    have hA : 0 ≤ A := by dsimp [A]; positivity
    have hn : Real.sqrt (∫ x in (0 : ℝ)..1, ((polyDeriv j p).eval x)^2) ≤
        A * Real.sqrt (∫ x in (0 : ℝ)..1, (p.eval x)^2) := by
      apply (Real.sqrt_le_left (mul_nonneg hA (Real.sqrt_nonneg _))).mpr
      rw [mul_pow, Real.sq_sqrt hE, hderiv, hbase]
      exact hcoeff
    simpa only [A, div_mul_eq_mul_div] using hn

end CausalSmith.Stat.RdTruesideNoiseFrontier
