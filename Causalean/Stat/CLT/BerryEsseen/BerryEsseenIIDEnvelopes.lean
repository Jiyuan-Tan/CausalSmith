module
public import Causalean.Stat.CLT.BerryEsseen.BerryEsseenGaussian
public import Causalean.Stat.CLT.BerryEsseen.BerryEsseenTaylor
public import Causalean.Stat.CLT.BerryEsseen.BerryEsseenWideCharFun
public import Causalean.Stat.CLT.BerryEsseen.PrawitzEnvelopes

/-! # Iid powers under the explicit Prawitz moment envelopes

These analytic estimates connect the proved one-observation moment bounds to
the deterministic smoothing budget. They import neither a CDF smoothing
comparison nor any numerical allocation. Both estimates retain sample sizes
at least two; the moment lower bound is explicit and can later be discharged
by unit_second_moment_third_absolute_moment_ge_one.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory ProbabilityTheory

/-- The squared cubic modulus estimate implies exponential damping at every frequency. -/
private theorem norm_le_exp_cubic_of_sq_bound (z : ℂ) (M u : ℝ) (hM : 1 ≤ M)
    (h : ‖z‖ ^ 2 ≤ 1 - u ^ 2 + (M + 1) * |u| ^ 3 / 5) :
    ‖z‖ ≤ Real.exp (-(u ^ 2 / 2) + M * |u| ^ 3 / 5) := by
  apply (sq_le_sq₀ (norm_nonneg _) (Real.exp_nonneg _)).mp
  rw [← Real.exp_nat_mul]
  have hc : (M + 1) * |u| ^ 3 / 5 ≤ 2 * M * |u| ^ 3 / 5 := by
    nlinarith [pow_nonneg (abs_nonneg u) 3]
  have he := Real.add_one_le_exp (2 * (-(u ^ 2 / 2) + M * |u| ^ 3 / 5))
  norm_num only [Nat.cast_ofNat] at *
  linarith

/-- Bound a complex power difference using the geometric-sum identity. -/
private theorem norm_pow_sub_pow_le_radius (a b : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) (n : ℕ) :
    ‖a ^ n - b ^ n‖ ≤ (n : ℝ) * ‖a - b‖ * r ^ (n - 1) := by
  rw [← geom_sum₂_mul a b n, norm_mul]
  have hsum : ‖∑ i ∈ Finset.range n, a ^ i * b ^ (n - 1 - i)‖ ≤
      (n : ℝ) * r ^ (n - 1) := by
    calc
      _ ≤ ∑ i ∈ Finset.range n, ‖a ^ i * b ^ (n - 1 - i)‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ Finset.range n, r ^ (n - 1) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_mul, norm_pow, norm_pow]
        calc
          _ ≤ r ^ i * r ^ (n - 1 - i) :=
            mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) ha _)
              (pow_le_pow_left₀ (norm_nonneg _) hb _) (by positivity) (by positivity)
          _ = r ^ (n - 1) := by
            rw [← pow_add]
            congr 1
            have := Finset.mem_range.mp hi
            omega
      _ = _ := by simp
  calc
    _ ≤ ((n : ℝ) * r ^ (n - 1)) * ‖a - b‖ :=
      mul_le_mul_of_nonneg_right hsum (norm_nonneg _)
    _ = _ := by ring

/-- For [a centered unit-variance probability law with third absolute moment
at most a bound no smaller than one](hyp:μ,M3,hM3,hmean_int,hmean,hvar_int,hvar,hthird_int,hthird),
the [standardized iid characteristic-function power at every frequency and
sample size at least two](hyp:n,hn,t) is [bounded by the explicit cubic
moment envelope](goal). -/
theorem iid_unit_variance_charFun_prawitz_moment_bound
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (M3 : ℝ) (hM3 : 1 ≤ M3)
    (hmean_int : Integrable (fun x : ℝ => x) μ)
    (hmean : ∫ x : ℝ, x ∂μ = 0)
    (hvar_int : Integrable (fun x : ℝ => x ^ 2) μ)
    (hvar : ∫ x : ℝ, x ^ 2 ∂μ = 1)
    (hthird_int : Integrable (fun x : ℝ => |x| ^ 3) μ)
    (hthird : ∫ x : ℝ, |x| ^ 3 ∂μ ≤ M3)
    (n : ℕ) (hn : 2 ≤ n) (t : ℝ) :
    ‖(charFun μ (t / Real.sqrt (n : ℝ))) ^ n‖ ≤
      prawitzMomentEnvelope (M3 / Real.sqrt (n : ℝ)) t := by
  /- Put u=t/sqrt(n). The proved squared modulus is bounded by
  1-u²+(M3+1)|u|³/5 <= exp(-u²+(M3+1)|u|³/5).
  Taking square roots and raising to n gives exp(-t²/2+
  (M3+1)|t|³/(10*sqrt(n))). Since M3>=1 this is at most
  exp(-t²/2+rho|t|³/5). Independently norm_charFun_le_one and
  norm_pow bound the power by one. No frequency restriction is needed.
  Use Real.add_one_le_exp, Real.exp_nat_mul, and sqrt(n)^2=n.
  The nonnegative squared modulus justifies taking the square root even
  when the intermediate polynomial was not separately proved positive. -/
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hspos : 0 < Real.sqrt (n : ℝ) := by positivity
  have hsne := ne_of_gt hspos
  have hs2 : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt (by positivity)
  have ha := norm_le_exp_cubic_of_sq_bound _ M3 _ hM3
    (unit_variance_charFun_norm_sq_cubic_bound μ M3 hmean_int hmean
      hvar_int hvar hthird_int hthird (t / Real.sqrt (n : ℝ)))
  rw [prawitzMomentEnvelope, norm_pow]
  apply le_min
  · simpa using pow_le_pow_left₀ (norm_nonneg _)
      (norm_charFun_le_one (μ := μ) (t / Real.sqrt (n : ℝ))) n
  · calc
      ‖charFun μ (t / Real.sqrt (n : ℝ))‖ ^ n ≤
          (Real.exp ( -((t / Real.sqrt (n : ℝ)) ^ 2 / 2) +
            M3 * |t / Real.sqrt (n : ℝ)| ^ 3 / 5)) ^ n :=
        pow_le_pow_left₀ (norm_nonneg _) ha n
      _ = Real.exp (-(t ^ 2 / 2) + (M3 / Real.sqrt (n : ℝ)) * |t| ^ 3 / 5) := by
        rw [← Real.exp_nat_mul]
        congr 1
        generalize hs : Real.sqrt (n : ℝ) = s at *
        rw [abs_div, abs_of_pos hspos, div_pow, div_pow, ← hs2]
        field_simp


/-- For [a centered unit-variance probability law with integrable third absolute
moment at most a bound M3 no smaller than one](hyp:μ,M3,hM3,hmean_int,hmean,hvar_int,hvar,hthird_int,hthird),
[a sample size n of at least two](hyp:n,hn), and
[a frequency t in the full outer Prawitz band |t| ≤ 12√n/(5·M3)](hyp:t,ht),
[the distance between the characteristic function of the standardized iid sum
and the standard Gaussian characteristic function is at most Prawitz's
discrepancy envelope at ratio M3/√n](goal). -/
theorem iid_unit_variance_charFun_prawitz_discrepancy_bound
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (M3 : ℝ) (hM3 : 1 ≤ M3)
    (hmean_int : Integrable (fun x : ℝ => x) μ)
    (hmean : ∫ x : ℝ, x ∂μ = 0)
    (hvar_int : Integrable (fun x : ℝ => x ^ 2) μ)
    (hvar : ∫ x : ℝ, x ^ 2 ∂μ = 1)
    (hthird_int : Integrable (fun x : ℝ => |x| ^ 3) μ)
    (hthird : ∫ x : ℝ, |x| ^ 3 ∂μ ≤ M3)
    (n : ℕ) (hn : 2 ≤ n) (t : ℝ)
    (ht : |t| ≤ 12 / (5 * (M3 / Real.sqrt (n : ℝ)))) :
    ‖(charFun μ (t / Real.sqrt (n : ℝ))) ^ n -
      charFun (gaussianReal 0 1) t‖ ≤
      prawitzDiscrepancyEnvelope (M3 / Real.sqrt (n : ℝ)) t := by
  /- Derive BOTH minimum branches. The modulus-sum branch follows from
  the preceding moment bound, norm_sub_le, and the exact Gaussian norm.
  For the Taylor branch let a=phi_mu(u), b=phi_G(u), rho=M3/sqrt(n).
  One-step Taylor and Gaussian remainders give
  n*norm(a-b) <= rho*|t|³/6 + rho²*t⁴/8 (M3>=1).
  The one-step squared-modulus proof also gives norm(a),norm(b) <=
  exp((-t²/2+rho*|t|³/5)/n). Difference-of-powers then supplies
  exp(((n-1)/n)*(-t²/2+rho*|t|³/5)). The exponent is NONPOSITIVE
  because rho*|t|<=12/5<5/2; (n-1)/n>=1/2 therefore yields
  exp(-t²/4+rho*|t|³/10), exactly the original envelope.
  Do not substitute the narrower local-product theorem, restrict n, or
  change the coefficients. The power inequality is also in Mathlib;
  verify availability before duplicating the existing private induction.
  No integrability or distributional approximation is a new hypothesis. -/
  let s : ℝ := Real.sqrt (n : ℝ)
  let u : ℝ := t / s
  let ρ : ℝ := M3 / s
  let a : ℂ := charFun μ u
  let b : ℂ := charFun (gaussianReal 0 1) u
  let e : ℝ := -(u ^ 2 / 2) + M3 * |u| ^ 3 / 5
  let r : ℝ := Real.exp e
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hspos : 0 < s := by dsimp [s]; positivity
  have hsne : s ≠ 0 := ne_of_gt hspos
  have hs2 : s ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
  have hMpos : 0 < M3 := by linarith
  have hρpos : 0 < ρ := div_pos hMpos hspos
  have habsu : |u| = |t| / s := by simp [u, abs_div, abs_of_pos hspos]
  have hescale : (n : ℝ) * e = -(t ^ 2 / 2) + ρ * |t| ^ 3 / 5 := by
    dsimp [e, ρ]
    rw [habsu]
    dsimp [u]
    rw [div_pow, div_pow, ← hs2]
    field_simp
  have har : ‖a‖ ≤ r := norm_le_exp_cubic_of_sq_bound _ M3 u hM3
    (unit_variance_charFun_norm_sq_cubic_bound μ M3 hmean_int hmean
      hvar_int hvar hthird_int hthird u)
  have hgauss (v : ℝ) : charFun (gaussianReal 0 1) v =
      Complex.exp ((-(v ^ 2 / 2) : ℝ) : ℂ) := by
    rw [charFun_gaussianReal]
    congr 1
    push_cast
    ring
  have hgnorm (v : ℝ) : ‖charFun (gaussianReal 0 1) v‖ =
      Real.exp (-(v ^ 2 / 2)) := by
    rw [hgauss, Complex.norm_exp]
    simp
    norm_cast
  have hbr : ‖b‖ ≤ r := by
    rw [show ‖b‖ = Real.exp (-(u ^ 2 / 2)) from hgnorm u]
    apply Real.exp_le_exp.mpr
    dsimp [e]
    have hc : 0 ≤ M3 * |u| ^ 3 / 5 := by positivity
    linarith
  have hbscale : b ^ n = charFun (gaussianReal 0 1) t := by
    have hscale : (n : ℝ) * (u ^ 2 / 2) = t ^ 2 / 2 := by
      dsimp [u]
      rw [div_pow, ← hs2]
      field_simp
    dsimp [b]
    rw [hgauss, hgauss, ← Complex.exp_nat_mul]
    congr 1
    norm_cast
    linarith [hscale]
  have hsum : ‖a ^ n - charFun (gaussianReal 0 1) t‖ ≤
      prawitzMomentEnvelope ρ t + Real.exp (-(t ^ 2 / 2)) := by
    calc
      _ ≤ ‖a ^ n‖ + ‖charFun (gaussianReal 0 1) t‖ := norm_sub_le _ _
      _ ≤ _ := by
        rw [hgnorm]
        exact add_le_add (iid_unit_variance_charFun_prawitz_moment_bound
          μ M3 hM3 hmean_int hmean hvar_int hvar hthird_int hthird n hn t) le_rfl
  have hgap : ‖a - b‖ ≤ M3 * |u| ^ 3 / 6 + |u| ^ 4 / 8 := by
    let q : ℂ := 1 - (u : ℂ) ^ 2 / 2
    have haerr : ‖a - q‖ ≤ M3 * |u| ^ 3 / 6 := by
      simpa [a, q] using centered_charFun_quadratic_remainder μ 1 M3
        hmean_int hmean hvar_int hvar hthird_int hthird u
    have hberr : ‖b - q‖ ≤ |u| ^ 4 / 8 := gaussian_charFun_quadratic_remainder u
    calc
      _ ≤ ‖a - q‖ + ‖q - b‖ := norm_sub_le_norm_sub_add_norm_sub a q b
      _ ≤ _ := by rw [norm_sub_rev q b]; exact add_le_add haerr hberr
  have hscaled : (n : ℝ) * ‖a - b‖ ≤ ρ * |t| ^ 3 / 6 + ρ ^ 2 * t ^ 4 / 8 := by
    calc
      _ ≤ (n : ℝ) * (M3 * |u| ^ 3 / 6 + |u| ^ 4 / 8) :=
        mul_le_mul_of_nonneg_left hgap hnpos.le
      _ = ρ * |t| ^ 3 / 6 + t ^ 4 / (8 * s ^ 2) := by
        rw [habsu, div_pow, div_pow]
        dsimp [ρ]
        have ht4 : |t| ^ 4 = t ^ 4 := by
          rw [← abs_pow, abs_of_nonneg (by positivity : 0 ≤ t ^ 4)]
        rw [← hs2, ht4]
        field_simp
      _ ≤ _ := by
        have hMsq : 1 ≤ M3 ^ 2 := by nlinarith
        have h := mul_le_mul_of_nonneg_right hMsq
          (show 0 ≤ t ^ 4 / (8 * s ^ 2) by positivity)
        have heq : ρ ^ 2 * t ^ 4 / 8 = M3 ^ 2 * (t ^ 4 / (8 * s ^ 2)) := by
          dsimp [ρ]
          field_simp
        rw [heq]
        linarith
  have hband : ρ * |t| ≤ 12 / 5 := by
    have h := (le_div_iff₀ (show 0 < 5 * ρ by positivity)).mp ht
    change |t| * (5 * ρ) ≤ 12 at h
    linarith
  have hE : -(t ^ 2 / 2) + ρ * |t| ^ 3 / 5 ≤ 0 := by
    have h := mul_le_mul_of_nonneg_right hband (sq_nonneg t)
    have hid : |t| ^ 3 = |t| * t ^ 2 := by rw [pow_succ, sq_abs]; ring
    rw [hid]
    nlinarith
  have he : e ≤ 0 := by nlinarith [hescale]
  have hrpow : r ^ (n - 1) ≤ Real.exp (-(t ^ 2 / 4) + ρ * |t| ^ 3 / 10) := by
    dsimp [r]
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hnsubreal : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      simp
    rw [hnsubreal]
    have hhalf : (n : ℝ) / 2 ≤ (n : ℝ) - 1 := by linarith
    have h := mul_le_mul_of_nonpos_right hhalf he
    nlinarith [hescale]
  rw [prawitzDiscrepancyEnvelope]
  apply le_min
  · rw [← hbscale]
    change ‖a ^ n - b ^ n‖ ≤ _
    calc
      _ ≤ (n : ℝ) * ‖a - b‖ * r ^ (n - 1) :=
        norm_pow_sub_pow_le_radius a b r (Real.exp_nonneg _) har hbr n
      _ ≤ (ρ * |t| ^ 3 / 6 + ρ ^ 2 * t ^ 4 / 8) * r ^ (n - 1) :=
        mul_le_mul_of_nonneg_right hscaled (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hrpow (by positivity)
  · exact hsum


end Causalean.Stat.CLT.BerryEsseen
