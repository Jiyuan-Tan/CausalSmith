module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.DictionaryScore.FourierQuantitative

/-! Uniform logarithmic tuning for the Fourier dictionary. -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology FourierTransform
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition

/-- The logarithmic factor in S9 is uniformly bounded for effective sample size at least one.
The fixed bandwidth multiplier twelve leaves three quarters of the exponential available
for absorbing the logarithmic powers. [Under the stated conditions](hyp:hd). [This is the stated conclusion](goal). -/
-- @node: fourier_log_tuning_bound
lemma fourier_log_tuning_bound (d : ℝ) (hd : d ≤ 5) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 1 ≤ N →
      (Real.log (Real.exp 1 + N))^(d/2) *
        (1 + Real.sqrt (Real.log (Real.exp 1 + N))/12)^10 *
        Real.exp (Real.log (Real.exp 1 + N)/4) / N ≤ C := by
  let K : ℝ := (8 : ℕ).factorial * (4/3 : ℝ)^8
  refine ⟨1024*K*(Real.exp 1+1), by dsimp [K]; positivity, ?_⟩
  intro N hN
  let S := Real.log (Real.exp 1 + N)
  have hN0 : 0 < N := by linarith
  have hS : 1 ≤ S := by
    dsimp [S]
    simpa only [Real.log_exp] using
      Real.log_le_log (Real.exp_pos 1) (show Real.exp 1 ≤ Real.exp 1 + N by linarith)
  have hS0 : 0 ≤ S := by linarith
  have hsqrt : 1 ≤ Real.sqrt S := by
    simpa using Real.sqrt_le_sqrt hS
  have hdim : S^(d/2) ≤ S^3 := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hS (by linarith)
  have hpoly : (1+Real.sqrt S/12)^10 ≤ 1024*S^5 := by
    calc
      _ ≤ (2*Real.sqrt S)^10 :=
        pow_le_pow_left₀ (by positivity) (by linarith) 10
      _ = 1024*S^5 := by
        rw [mul_pow, show (Real.sqrt S)^10 = ((Real.sqrt S)^2)^5 by ring,
          Real.sq_sqrt hS0]
        norm_num
  have hseries := Real.pow_div_factorial_le_exp (3*S/4) (by positivity) 8
  have habsorb : S^8 ≤ K*Real.exp (3*S/4) := by
    dsimp [K]
    norm_num [Nat.factorial] at hseries ⊢
    nlinarith
  have hwhole : S^(d/2)*(1+Real.sqrt S/12)^10*Real.exp (S/4) ≤
      1024*K*(Real.exp 1+N) := by
    calc
      _ ≤ S^3*(1024*S^5)*Real.exp (S/4) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hdim hpoly (by positivity) (by positivity)) (Real.exp_pos _).le
      _ = 1024*S^8*Real.exp (S/4) := by ring
      _ ≤ 1024*(K*Real.exp (3*S/4))*Real.exp (S/4) := by
        gcongr
      _ = 1024*K*Real.exp S := by
        calc
          _ = (1024*K)*(Real.exp (3*S/4)*Real.exp (S/4)) := by ring
          _ = _ := by rw [← Real.exp_add]; congr 2 <;> ring
      _ = _ := by rw [Real.exp_log (by positivity : 0 < Real.exp 1+N)]
  apply (div_le_iff₀ hN0).mpr
  have harg : Real.exp 1+N ≤ (Real.exp 1+1)*N := by
    nlinarith [Real.exp_pos 1]
  exact hwhole.trans (by
    calc
      _ ≤ (1024*K)*((Real.exp 1+1)*N) :=
        mul_le_mul_of_nonneg_left harg (by dsimp [K]; positivity)
      _ = _ := by ring)

/-- The Fourier scale is positive whenever the noise scale is positive. [Under the stated conditions](hyp:hsigma). [This is the stated conclusion](goal). -/
-- @node: fourierScale_pos
lemma fourierScale_pos (beta kappa sigma : ℝ) (n : ℕ) (hsigma : 0 < sigma) :
    0 < fourierScale beta kappa sigma n := by
  have hS : 0 < Real.log (Real.exp 1 + n*sigma^effDim beta kappa) := by
    apply Real.log_pos
    have he : 1 < Real.exp 1 := by simpa using Real.exp_lt_exp.mpr zero_lt_one
    have hp : 0 ≤ (n : ℝ)*sigma^effDim beta kappa := by positivity
    linarith
  exact div_pos hsigma (Real.sqrt_pos.mpr hS)

/-- The effective sample size exactly balances the power of the Fourier scale against
its logarithmic denominator. This is the algebraic normalization used in S9. [Under the stated conditions](hyp:hn,hsigma). [This is the stated conclusion](goal). -/
-- @node: fourierScale_power_balance
lemma fourierScale_power_balance (beta kappa sigma : ℝ) (n : ℕ)
    (hn : 0 < n) (hsigma : 0 < sigma) :
    (fourierScale beta kappa sigma n)^(-effDim beta kappa) / n =
      (Real.log (Real.exp 1+n*sigma^effDim beta kappa))^(effDim beta kappa/2) /
        (n*sigma^effDim beta kappa) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hS : 0 < Real.log (Real.exp 1 + n*sigma^effDim beta kappa) := by
    apply Real.log_pos
    have he : 1 < Real.exp 1 := by simpa using Real.exp_lt_exp.mpr zero_lt_one
    have hp : 0 ≤ (n : ℝ)*sigma^effDim beta kappa := by positivity
    linarith
  rw [fourierScale, Real.rpow_neg (by positivity),
    Real.div_rpow hsigma.le (Real.sqrt_nonneg _),
    ← Real.rpow_div_two_eq_sqrt _ hS.le]
  field_simp

/-- At twelve times the Fourier scale, S9 bounds the stochastic term by the bandwidth bias.
The bound is uniform in every effective sample size at least one. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hbeta,hkappa). -/
-- @node: fourier_intermediate_stochastic_bound
lemma fourier_intermediate_stochastic_bound (beta kappa : ℝ)
    (hbeta : beta ∈ Ioc (0 : ℝ) 1) (hkappa : kappa ∈ Icc (0 : ℝ) 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → ∀ sigma : ℝ, 0 < sigma →
      1 ≤ (n : ℝ)*sigma^effDim beta kappa →
      Real.sqrt ((12*fourierScale beta kappa sigma n)^(-kappa-1) *
        (1+sigma/(12*fourierScale beta kappa sigma n))^10 *
        Real.exp (36*(sigma/(12*fourierScale beta kappa sigma n))^2) / n) ≤
      C*(12*fourierScale beta kappa sigma n)^beta := by
  have hd : 0 < effDim beta kappa := by unfold effDim; linarith [hbeta.1, hkappa.1]
  obtain ⟨C, hC, hbound⟩ := fourier_log_tuning_bound (effDim beta kappa)
    (by unfold effDim; linarith [hbeta.2, hkappa.2])
  refine ⟨Real.sqrt C, Real.sqrt_pos.mpr hC, ?_⟩
  intro n hn sigma hsigma hN
  let F := fourierScale beta kappa sigma n
  let h := 12*F
  let S := Real.log (Real.exp 1+n*sigma^effDim beta kappa)
  have hF : 0 < F := fourierScale_pos beta kappa sigma n hsigma
  have hh : 0 < h := by dsimp [h]; positivity
  have hS : 0 < S := by
    dsimp [S]
    apply Real.log_pos
    have he : 1 < Real.exp 1 := by simpa using Real.exp_lt_exp.mpr zero_lt_one
    linarith
  have hratio : sigma/h = Real.sqrt S/12 := by
    dsimp [h, F, fourierScale, S]
    field_simp
  have hexp : 36*(sigma/h)^2 = S/4 := by
    rw [hratio, div_pow, Real.sq_sqrt hS.le]
    ring
  have hpower : h^(-kappa-1) = (h^beta)^2*h^(-effDim beta kappa) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hh.le, ← Real.rpow_add hh]
    congr 1
    unfold effDim
    ring
  have hneg : h^(-effDim beta kappa)/n ≤ S^(effDim beta kappa/2)/
      (n*sigma^effDim beta kappa) := by
    rw [← fourierScale_power_balance beta kappa sigma n hn hsigma]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    exact Real.rpow_le_rpow_of_nonpos hF (by dsimp [h]; linarith) (by linarith)
  have hsquared : h^(-kappa-1)*(1+sigma/h)^10*
      Real.exp (36*(sigma/h)^2)/n ≤ (h^beta)^2*C := by
    rw [hpower, hexp, hratio]
    calc
      _ = (h^beta)^2 * ((h^(-effDim beta kappa)/n)*
          (1+Real.sqrt S/12)^10*Real.exp (S/4)) := by ring
      _ ≤ (h^beta)^2 * ((S^(effDim beta kappa/2)/
          (n*sigma^effDim beta kappa))*(1+Real.sqrt S/12)^10*Real.exp (S/4)) := by
        gcongr
      _ ≤ (h^beta)^2*C := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        dsimp only [S]
        convert hbound ((n : ℝ)*sigma^effDim beta kappa) hN using 1 <;> first | rfl | ring
  calc
    _ ≤ Real.sqrt ((h^beta)^2*C) := Real.sqrt_le_sqrt hsquared
    _ = _ := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]; ring

/-- Dropping the nonnegative noise multipliers from S9 bounds the inverse effective bandwidth. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hbeta,hkappa). -/
-- @node: fourierScale_inverse_power_bound
lemma fourierScale_inverse_power_bound (beta kappa : ℝ)
    (hbeta : beta ∈ Ioc (0 : ℝ) 1) (hkappa : kappa ∈ Icc (0 : ℝ) 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → ∀ sigma : ℝ, 0 < sigma →
      1 ≤ (n : ℝ)*sigma^effDim beta kappa →
      (fourierScale beta kappa sigma n)^(-effDim beta kappa)/n ≤ C := by
  obtain ⟨C, hC, hbound⟩ := fourier_log_tuning_bound (effDim beta kappa)
    (by unfold effDim; linarith [hbeta.2, hkappa.2])
  refine ⟨C, hC, ?_⟩
  intro n hn sigma hsigma hN
  rw [fourierScale_power_balance beta kappa sigma n hn hsigma]
  let S := Real.log (Real.exp 1 + n*sigma^effDim beta kappa)
  have hS : 0 ≤ S := by
    apply Real.log_nonneg
    have he : 1 < Real.exp 1 := by simpa using Real.exp_lt_exp.mpr zero_lt_one
    linarith
  have hp : 1 ≤ (1+Real.sqrt S/12)^10 := one_le_pow₀ (by linarith [Real.sqrt_nonneg S])
  have he : 1 ≤ Real.exp (S/4) := Real.one_le_exp_iff.mpr (by positivity)
  calc
    _ ≤ S^(effDim beta kappa/2)*(1+Real.sqrt S/12)^10*Real.exp (S/4)/
        (n*sigma^effDim beta kappa) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      calc
        _ = S^(effDim beta kappa/2)*1*1 := by ring
        _ ≤ _ := mul_le_mul
          (mul_le_mul_of_nonneg_left hp (by positivity)) he (by norm_num) (by positivity)
    _ ≤ C := hbound _ hN

/-- The Fourier scale is no larger than the positive noise scale. [Under the stated conditions](hyp:hsigma). [This is the stated conclusion](goal). -/
-- @node: fourierScale_le_sigma
lemma fourierScale_le_sigma (beta kappa sigma : ℝ) (n : ℕ) (hsigma : 0 < sigma) :
    fourierScale beta kappa sigma n ≤ sigma := by
  have hS : 1 ≤ Real.log (Real.exp 1+n*sigma^effDim beta kappa) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1)
      (show Real.exp 1 ≤ Real.exp 1+n*sigma^effDim beta kappa by
        have hp : 0 ≤ (n : ℝ)*sigma^effDim beta kappa := by positivity
        linarith)
  apply (div_le_iff₀ (Real.sqrt_pos.mpr (by linarith :
    0 < Real.log (Real.exp 1+n*sigma^effDim beta kappa)))).mpr
  have hr : 1 ≤ Real.sqrt (Real.log (Real.exp 1+n*sigma^effDim beta kappa)) := by
    simpa using Real.sqrt_le_sqrt hS
  nlinarith

/-- The unweighted frequency error is controlled by the Fourier bias throughout
intermediate tuning, using the inverse-power consequence of S9. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hbeta,hkappa). -/
-- @node: fourierScale_frequency_bound
lemma fourierScale_frequency_bound (beta kappa : ℝ)
    (hbeta : beta ∈ Ioc (0 : ℝ) 1) (hkappa : kappa ∈ Icc (0 : ℝ) 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → ∀ sigma ∈ Ioc (0 : ℝ) (1/4),
      1 ≤ (n : ℝ)*sigma^effDim beta kappa →
      Real.sqrt (1/(n : ℝ)) ≤ C*(fourierScale beta kappa sigma n)^beta := by
  obtain ⟨C, hC, hbound⟩ := fourierScale_inverse_power_bound beta kappa hbeta hkappa
  refine ⟨Real.sqrt C, Real.sqrt_pos.mpr hC, ?_⟩
  intro n hn sigma hsigma hN
  let F := fourierScale beta kappa sigma n
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hF : 0 < F := fourierScale_pos beta kappa sigma n hsigma.1
  have hF1 : F ≤ 1 := (fourierScale_le_sigma beta kappa sigma n hsigma.1).trans
    (by linarith [hsigma.2])
  have hb := hbound n hn sigma hsigma.1 hN
  have hpow : 0 < F^effDim beta kappa := by positivity
  rw [Real.rpow_neg hF.le] at hb
  have hbal : 1/(n : ℝ) ≤ C*F^effDim beta kappa := by
    have hmul := mul_le_mul_of_nonneg_right ((div_le_iff₀ hnR).mp hb) hpow.le
    have he : (F^effDim beta kappa)⁻¹ * F^effDim beta kappa = 1 :=
      inv_mul_cancel₀ hpow.ne'
    rw [he] at hmul
    apply (div_le_iff₀ hnR).mpr
    nlinarith
  have hsmall : F^effDim beta kappa ≤ (F^beta)^2 := by
    rw [← Real.rpow_two, ← Real.rpow_mul hF.le]
    apply Real.rpow_le_rpow_of_exponent_ge hF hF1
    unfold effDim
    linarith [hkappa.1]
  calc
    _ ≤ Real.sqrt (C*(F^beta)^2) := Real.sqrt_le_sqrt
      (hbal.trans (mul_le_mul_of_nonneg_left hsmall hC.le))
    _ = _ := by rw [Real.sqrt_mul hC.le, Real.sqrt_sq (by positivity)]

/-- S8 and S9 control the certificate at any bandwidth rounded up from twelve times
the Fourier scale, provided the rounded bandwidth is in the public window. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hbeta,hkappa). -/
-- @node: qF_intermediate_certificate_bound
lemma qF_intermediate_certificate_bound (beta kappa : ℝ)
    (hbeta : beta ∈ Ioc (0 : ℝ) 1) (hkappa : kappa ∈ Icc (0 : ℝ) 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → ∀ sigma ∈ Ioc (0 : ℝ) (1/4),
      1 ≤ (n : ℝ)*sigma^effDim beta kappa → ∀ h ∈ Ioc (0 : ℝ) (1/4),
      12*fourierScale beta kappa sigma n ≤ h →
      h ≤ 24*fourierScale beta kappa sigma n →
      unitAq beta kappa n sigma ⟨qF h, ellF sigma h⟩ ≤
        C*(fourierScale beta kappa sigma n)^beta := by
  obtain ⟨C, hC, hcert⟩ := qF_certificate_bound beta kappa hbeta hkappa
  obtain ⟨D, hD, hstoch⟩ := fourier_intermediate_stochastic_bound beta kappa hbeta hkappa
  obtain ⟨E, hE, hfreq⟩ := fourierScale_frequency_bound beta kappa hbeta hkappa
  refine ⟨C*(24^beta+D*12^beta+E), by positivity, ?_⟩
  intro n hn sigma hsigma hN h hh hlo hhi
  have hsigma0 : 0 ≤ sigma := hsigma.1.le
  have hh0 : 0 < h := hh.1
  let F := fourierScale beta kappa sigma n
  have hF : 0 < F := fourierScale_pos beta kappa sigma n hsigma.1
  have hb : h^beta ≤ 24^beta*F^beta := by
    calc
      _ ≤ (24*F)^beta := Real.rpow_le_rpow hh.1.le hhi (by linarith [hbeta.1])
      _ = _ := Real.mul_rpow (by norm_num) hF.le
  have hs : Real.sqrt (h^(-kappa-1)*(1+sigma/h)^10*
      Real.exp (36*(sigma/h)^2)/n) ≤ D*12^beta*F^beta := by
    calc
      _ ≤ Real.sqrt ((12*F)^(-kappa-1)*(1+sigma/(12*F))^10*
          Real.exp (36*(sigma/(12*F))^2)/n) := by
        have hratio : sigma/h ≤ sigma/(12*F) :=
          div_le_div_of_nonneg_left hsigma.1.le (by positivity) hlo
        apply Real.sqrt_le_sqrt
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
        apply mul_le_mul _ _ (by positivity) (by positivity)
        · exact mul_le_mul
            (Real.rpow_le_rpow_of_nonpos (by positivity) hlo (by linarith [hkappa.1]))
            (pow_le_pow_left₀ (by positivity) (by linarith) 10) (by positivity) (by positivity)
        · apply Real.exp_le_exp.mpr
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hratio 2)
            (by norm_num)
      _ ≤ D*(12*F)^beta := hstoch n hn sigma hsigma.1 hN
      _ = _ := by rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 12) hF.le]; ring
  have hf := hfreq n hn sigma hsigma hN
  calc
    _ ≤ C*(h^beta+Real.sqrt (h^(-kappa-1)*(1+sigma/h)^10*
        Real.exp (36*(sigma/h)^2)/n)+Real.sqrt (1/(n : ℝ))) :=
      hcert n hn h hh sigma ⟨hsigma.1.le, hsigma.2⟩
    _ ≤ C*(24^beta*F^beta+D*12^beta*F^beta+E*F^beta) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add hb hs) hf) hC.le
    _ = _ := by ring

end CausalSmith.Stat.NoisydoseWeakdesignTransition
