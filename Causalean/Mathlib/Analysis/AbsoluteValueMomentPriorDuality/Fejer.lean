/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.Basic
import Causalean.Mathlib.Analysis.BernsteinSzegoTrig.Szego
import Mathlib.Analysis.Fourier.AddCircle

/-!
# Fejér and de la Vallée--Poussin certificates

This module develops the periodic Fourier-analytic certificate used for the
lower bound on uniform polynomial approximation of absolute value.  It proves
the multiplier and norm properties of normalized Fejér means, packages the
de la Vallée--Poussin mean, and constructs a bounded cusp functional that
annihilates the low Fourier modes coming from algebraic polynomials.
-/

open scoped Real ComplexConjugate
open Set MeasureTheory

namespace Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.FejerCertificate

noncomputable section

local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

/-- For [a nonnegative integer order](hyp:n), [the one-sided Fourier sum](goal) is the continuous complex-valued function on the circle obtained by summing the Fourier characters with integer frequencies from zero through one less than that order. -/
noncomputable def oneSidedFourierSum (n : ℕ) : C(AddCircle Real.pi, ℂ) :=
  ∑ r ∈ Finset.range n, fourier (r : ℤ)

/-- For [a nonnegative integer order](hyp:n) and [a point on the circle of period π](hyp:t), [the normalized Fejér kernel](goal) is the squared complex modulus of the one-sided Fourier sum at that point, divided by the order; at order zero, this quotient is defined to be zero. -/
noncomputable def fejerKernel (n : ℕ) (t : AddCircle Real.pi) : ℝ :=
  ‖oneSidedFourierSum n t‖ ^ 2 / (n : ℝ)

/-- For [a Fejér order](hyp:n), [the normalized Fejér kernel is continuous](goal).

 The normalized Fejér kernel is continuous. -/
lemma continuous_fejerKernel (n : ℕ) : Continuous (fejerKernel n) := by
  unfold fejerKernel oneSidedFourierSum
  fun_prop

/-- For [a nonnegative integer order](hyp:n) and [a continuous complex-valued function on the circle of period π](hyp:f), [the Fejér mean](goal) is the Haar integral of the function multiplied by the normalized Fejér kernel of that order. -/
noncomputable def fejerMean (n : ℕ) (f : C(AddCircle Real.pi, ℂ)) : ℂ :=
  ∫ t, (fejerKernel n t : ℂ) * f t ∂AddCircle.haarAddCircle

/-- For [a Fourier frequency](hyp:k), [its Haar integral is one at frequency zero and zero otherwise](goal).

 A Fourier character has Haar integral one at frequency zero and zero at
every nonzero frequency. -/
lemma integral_fourier (k : ℤ) :
    (∫ x : AddCircle Real.pi, fourier k x ∂AddCircle.haarAddCircle) =
      if k = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := Real.pi) k) 0
  rw [fourierCoeff] at h
  simp only [neg_zero, fourier_zero, one_smul] at h
  by_cases hk : k = 0
  · subst k
    simpa using h
  · simpa [hk, Ne.symm hk] using h

/-- For [a Fejér order, Fourier frequency, and circle point](hyp:n,k,t), [the kernel-weighted character has the stated finite Fourier expansion](goal).

 Multiplying a nonnegative Fourier character by the Fejér kernel expands
as the normalized double sum of characters with shifted frequencies. -/
lemma fejer_integrand_expand (n k : ℕ) (t : AddCircle Real.pi) :
    (fejerKernel n t : ℂ) * fourier (k : ℤ) t =
      (n : ℂ)⁻¹ * ∑ r ∈ Finset.range n, ∑ s ∈ Finset.range n,
        fourier ((r : ℤ) - (s : ℤ) + (k : ℤ)) t := by
  rw [fejerKernel, Complex.sq_norm]
  simp only [Complex.ofReal_div, Complex.ofReal_natCast]
  rw [← Complex.mul_conj]
  simp only [oneSidedFourierSum, ContinuousMap.sum_apply, map_sum]
  simp_rw [← fourier_neg]
  simp_rw [div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s hs
  rw [← fourier_add]
  rw [show fourier ((r : ℤ) + -(s : ℤ)) t * (n : ℂ)⁻¹ * fourier (k : ℤ) t =
      (n : ℂ)⁻¹ * (fourier ((r : ℤ) + -(s : ℤ)) t * fourier (k : ℤ) t) by ring]
  rw [← fourier_add]
  congr 2

/-- For [a positive Fejér order](hyp:n,hn) and [a nonnegative frequency](hyp:k), [the Fejér mean has the stated triangular multiplier](goal).

 The Fejér mean multiplies the nonnegative frequency `k` by
`(n-k)/n` below the cutoff and by zero above it. -/
lemma fejerMean_fourier_nat (n k : ℕ) (hn : 0 < n) :
    fejerMean n (fourier (k : ℤ)) =
      if k < n then ((n - k : ℕ) : ℝ) / n else 0 := by
  rw [fejerMean]
  simp_rw [fejer_integrand_expand]
  have hfourier (j : ℤ) :
      Integrable (fourier j : AddCircle Real.pi → ℂ) AddCircle.haarAddCircle :=
    (fourier j).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hinner (r : ℕ) : Integrable
      (fun t : AddCircle Real.pi => ∑ s ∈ Finset.range n,
        fourier ((r : ℤ) - (s : ℤ) + (k : ℤ)) t) AddCircle.haarAddCircle :=
    (show Continuous (fun t : AddCircle Real.pi => ∑ s ∈ Finset.range n,
        fourier ((r : ℤ) - (s : ℤ) + (k : ℤ)) t) by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_const_mul]
  rw [integral_finset_sum (Finset.range n) (fun r hr => hinner r)]
  simp_rw [integral_finset_sum (Finset.range n)
    (fun s hs => hfourier ((_ : ℤ) - (s : ℤ) + (k : ℤ)))]
  simp_rw [integral_fourier]
  have hinner_sum (r : ℕ) :
      (∑ s ∈ Finset.range n,
        if (r : ℤ) - (s : ℤ) + (k : ℤ) = 0 then (1 : ℂ) else 0) =
        if r + k < n then 1 else 0 := by
    by_cases h : r + k < n
    · rw [if_pos h, Finset.sum_eq_single (r + k)]
      · simp
      · intro b hb hne
        simp only [ite_eq_right_iff]
        intro heq
        have : b = r + k := by omega
        exact (hne this).elim
      · simp [h]
    · rw [if_neg h]
      apply Finset.sum_eq_zero
      intro b hb
      simp only [ite_eq_right_iff]
      intro heq
      have : b = r + k := by omega
      subst b
      exact (h (Finset.mem_range.mp hb)).elim
  simp_rw [hinner_sum]
  by_cases hk : k < n
  · rw [if_pos hk]
    have hset : Finset.filter (fun r => r + k < n) (Finset.range n) =
        Finset.range (n - k) := by
      ext r
      simp
      omega
    rw [← Finset.sum_filter, hset]
    simp
    field_simp
  · rw [if_neg hk]
    have hzero : (∑ r ∈ Finset.range n,
        if r + k < n then (1 : ℂ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro r hr
      rw [if_neg]
      omega
    rw [hzero]
    simp

/-- For [a positive Fejér order](hyp:n,hn) and [a negative frequency magnitude](hyp:k), [the Fejér mean has the same triangular multiplier](goal).

 The Fejér mean has the same triangular multiplier at negative natural
frequencies. -/
lemma fejerMean_fourier_neg_nat (n k : ℕ) (hn : 0 < n) :
    fejerMean n (fourier (-(k : ℤ))) =
      if k < n then ((n - k : ℕ) : ℝ) / n else 0 := by
  rw [fejerMean]
  simp_rw [fourier_neg]
  calc
    (∫ t, (fejerKernel n t : ℂ) *
        (starRingEnd ℂ) (fourier (k : ℤ) t) ∂AddCircle.haarAddCircle) =
        (starRingEnd ℂ) (∫ t, (fejerKernel n t : ℂ) *
          fourier (k : ℤ) t ∂AddCircle.haarAddCircle) := by
      rw [← integral_conj]
      congr 1
      funext t
      simp
    _ = _ := by
      rw [← fejerMean, fejerMean_fourier_nat n k hn]
      split <;> simp

/-- For [a positive Fejér order](hyp:n,hn), [the normalized kernel integrates to one](goal).

 Every positive-order normalized Fejér kernel has Haar integral one. -/
lemma integral_fejerKernel (n : ℕ) (hn : 0 < n) :
    (∫ t, fejerKernel n t ∂AddCircle.haarAddCircle) = 1 := by
  have hcomplex := fejerMean_fourier_nat n 0 hn
  simp only [if_pos hn, Nat.cast_sub (Nat.zero_le _), Nat.cast_zero, sub_zero] at hcomplex
  have hker : Integrable (fejerKernel n) AddCircle.haarAddCircle :=
    (continuous_fejerKernel n).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hmap := Complex.ofRealCLM.integral_comp_comm hker
  rw [show (fun t : AddCircle Real.pi => Complex.ofRealCLM (fejerKernel n t)) =
      (fun t => (fejerKernel n t : ℂ)) by rfl] at hmap
  rw [fejerMean] at hcomplex
  simp only [fourier_zero, mul_one] at hcomplex
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  rw [div_self hnR] at hcomplex
  have : ((∫ t, fejerKernel n t ∂AddCircle.haarAddCircle : ℝ) : ℂ) = 1 := by
    calc
      ((∫ t, fejerKernel n t ∂AddCircle.haarAddCircle : ℝ) : ℂ) =
          ∫ t, (fejerKernel n t : ℂ) ∂AddCircle.haarAddCircle := hmap.symm
      _ = 1 := hcomplex
  exact_mod_cast this

/-- For [a positive Fejér order](hyp:n,hn), [a continuous input](hyp:f), and [a uniform norm bound](hyp:E,hE), [the Fejér mean obeys that bound](goal).

 A Fejér mean is bounded in norm by any uniform bound on its input. -/
lemma fejerMean_norm_le (n : ℕ) (hn : 0 < n)
    (f : C(AddCircle Real.pi, ℂ)) (E : ℝ) (hE : ∀ t, ‖f t‖ ≤ E) :
    ‖fejerMean n f‖ ≤ E := by
  have hnonneg (t : AddCircle Real.pi) : 0 ≤ fejerKernel n t := by
    exact div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  have hleft : Integrable (fun t : AddCircle Real.pi => fejerKernel n t * ‖f t‖)
      AddCircle.haarAddCircle :=
    (show Continuous (fun t : AddCircle Real.pi => fejerKernel n t * ‖f t‖) by
      exact (continuous_fejerKernel n).mul (f.continuous.norm)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hright : Integrable (fun t : AddCircle Real.pi => fejerKernel n t * E)
      AddCircle.haarAddCircle :=
    (show Continuous (fun t : AddCircle Real.pi => fejerKernel n t * E) by
      exact (continuous_fejerKernel n).mul continuous_const).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  calc
    ‖fejerMean n f‖ ≤
        ∫ t, ‖(fejerKernel n t : ℂ) * f t‖ ∂AddCircle.haarAddCircle := by
      exact norm_integral_le_integral_norm _
    _ = ∫ t, fejerKernel n t * ‖f t‖ ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hnonneg t)]
    _ ≤ ∫ t, fejerKernel n t * E ∂AddCircle.haarAddCircle := by
      apply integral_mono hleft hright
      intro t
      exact mul_le_mul_of_nonneg_left (hE t) (hnonneg t)
    _ = E := by
      rw [integral_mul_const, integral_fejerKernel n hn, one_mul]

/-- For [a positive integer order](hyp:n,hn), [the continuous-linear Fejér mean functional](goal) maps each continuous complex-valued function on the circle of period π to its Fejér mean of that order.

The Fejér mean is packaged as a continuous complex-linear functional of operator norm at most one. -/
noncomputable def fejerMeanCLM (n : ℕ) (hn : 0 < n) :
    C(AddCircle Real.pi, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fejerMean n
      map_add' := by
        intro f g
        rw [fejerMean, fejerMean]
        simp_rw [ContinuousMap.add_apply, mul_add]
        rw [integral_add]
        · rfl
        · exact (show Continuous (fun t : AddCircle Real.pi =>
              (fejerKernel n t : ℂ) * f t) by
                exact (Complex.continuous_ofReal.comp (continuous_fejerKernel n)).mul
                  f.continuous).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)
        · exact (show Continuous (fun t : AddCircle Real.pi =>
              (fejerKernel n t : ℂ) * g t) by
                exact (Complex.continuous_ofReal.comp (continuous_fejerKernel n)).mul
                  g.continuous).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)
      map_smul' := by
        intro c f
        rw [fejerMean, fejerMean]
        simp_rw [ContinuousMap.smul_apply, smul_eq_mul]
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with t
        simp
        ring }
    1 (fun f => by
      simpa using fejerMean_norm_le n hn f ‖f‖ (fun t => ContinuousMap.norm_coe_le_norm f t))

/-- For [a positive Fejér order](hyp:n,hn) and [a continuous input](hyp:f), [the packaged linear map equals the integral definition](goal).

 Applying the continuous-linear Fejér mean agrees with its integral
definition. -/
@[simp] lemma fejerMeanCLM_apply (n : ℕ) (hn : 0 < n)
    (f : C(AddCircle Real.pi, ℂ)) : fejerMeanCLM n hn f = fejerMean n f := rfl

/-- For [a positive integer order](hyp:n,hn), [the continuous-linear de la Vallée--Poussin mean](goal) maps a continuous complex-valued function on the circle of period π to twice its Fejér mean of order twice the given order, minus its Fejér mean of the given order. -/
noncomputable def valleePoussinMeanCLM (n : ℕ) (hn : 0 < n) :
    C(AddCircle Real.pi, ℂ) →L[ℂ] ℂ :=
  (2 : ℂ) • fejerMeanCLM (2 * n) (by omega) - fejerMeanCLM n hn

/-- For [a positive order](hyp:n,hn) and [a frequency at most that order](hyp:k,hk), [the de la Vallée--Poussin mean preserves the nonnegative Fourier character](goal).

 The de la Vallée--Poussin mean acts as the identity on nonnegative
frequencies at most `n`. -/
lemma valleePoussinMean_fourier_nat (n k : ℕ) (hn : 0 < n) (hk : k ≤ n) :
    valleePoussinMeanCLM n hn (fourier (k : ℤ)) = 1 := by
  rw [valleePoussinMeanCLM]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    fejerMeanCLM_apply]
  rw [fejerMean_fourier_nat (2 * n) k (by omega), fejerMean_fourier_nat n k hn]
  by_cases hlt : k < n
  · rw [if_pos hlt, if_pos (by omega)]
    push_cast
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    rw [Nat.cast_sub (by omega : k ≤ 2 * n), Nat.cast_sub (by omega : k ≤ n)]
    push_cast
    field_simp
    ring
    exact mul_inv_cancel₀ (by exact_mod_cast (Nat.ne_of_gt hn) : (n : ℂ) ≠ 0)
  · have hkn : k = n := by omega
    subst k
    rw [if_neg (Nat.lt_irrefl _), if_pos (by omega)]
    push_cast
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    rw [Nat.cast_sub (by omega : n ≤ 2 * n)]
    push_cast
    field_simp
    ring
    exact mul_inv_cancel₀ (by exact_mod_cast (Nat.ne_of_gt hn) : (n : ℂ) ≠ 0)

/-- For [a positive order](hyp:n,hn) and [a frequency magnitude at most that order](hyp:k,hk), [the de la Vallée--Poussin mean preserves the negative Fourier character](goal).

 The de la Vallée--Poussin mean acts as the identity on negative
frequencies of magnitude at most `n`. -/
lemma valleePoussinMean_fourier_neg_nat (n k : ℕ) (hn : 0 < n) (hk : k ≤ n) :
    valleePoussinMeanCLM n hn (fourier (-(k : ℤ))) = 1 := by
  rw [valleePoussinMeanCLM]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    fejerMeanCLM_apply]
  rw [fejerMean_fourier_neg_nat (2 * n) k (by omega), fejerMean_fourier_neg_nat n k hn]
  by_cases hlt : k < n
  · rw [if_pos hlt, if_pos (by omega)]
    push_cast
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    rw [Nat.cast_sub (by omega : k ≤ 2 * n), Nat.cast_sub (by omega : k ≤ n)]
    push_cast
    field_simp
    ring
    exact mul_inv_cancel₀ (by exact_mod_cast (Nat.ne_of_gt hn) : (n : ℂ) ≠ 0)
  · have hkn : k = n := by omega
    subst k
    rw [if_neg (Nat.lt_irrefl _), if_pos (by omega)]
    push_cast
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    rw [Nat.cast_sub (by omega : n ≤ 2 * n)]
    push_cast
    field_simp
    ring
    exact mul_inv_cancel₀ (by exact_mod_cast (Nat.ne_of_gt hn) : (n : ℂ) ≠ 0)

/-- For [a positive integer order](hyp:n,hn), [the continuous-linear cusp functional](goal) maps a continuous complex-valued function on the circle of period π to its value at zero minus its de la Vallée--Poussin mean of that order.

This is the bounded functional detecting the cusp of absolute value. -/
noncomputable def cuspFunctionalCLM (n : ℕ) (hn : 0 < n) :
    C(AddCircle Real.pi, ℂ) →L[ℂ] ℂ :=
  ContinuousMap.evalCLM ℂ (0 : AddCircle Real.pi) - valleePoussinMeanCLM n hn

/-- For [a positive order](hyp:n,hn) and [a nonnegative frequency at most that order](hyp:k,hk), [the cusp functional annihilates the Fourier character](goal).

 The cusp functional annihilates nonnegative frequencies at most `n`. -/
lemma cuspFunctional_fourier_nat (n k : ℕ) (hn : 0 < n) (hk : k ≤ n) :
    cuspFunctionalCLM n hn (fourier (k : ℤ)) = 0 := by
  simp [cuspFunctionalCLM, valleePoussinMean_fourier_nat n k hn hk, fourier_eval_zero]

/-- For [a positive order](hyp:n,hn) and [a negative frequency magnitude at most that order](hyp:k,hk), [the cusp functional annihilates the Fourier character](goal).

 The cusp functional annihilates negative frequencies of magnitude at most
`n`. -/
lemma cuspFunctional_fourier_neg_nat (n k : ℕ) (hn : 0 < n) (hk : k ≤ n) :
    cuspFunctionalCLM n hn (fourier (-(k : ℤ))) = 0 := by
  simp [cuspFunctionalCLM, valleePoussinMean_fourier_neg_nat n k hn hk,
    fourier_eval_zero]

/-- For [a positive order](hyp:n,hn) and [a nonnegative frequency](hyp:k), [the real part of the cusp multiplier is nonnegative](goal).

 The real part of the cusp multiplier is nonnegative at every nonnegative
frequency. -/
lemma cuspFunctional_fourier_nat_nonneg (n k : ℕ) (hn : 0 < n) :
    0 ≤ (cuspFunctionalCLM n hn (fourier (k : ℤ))).re := by
  rw [cuspFunctionalCLM, valleePoussinMeanCLM]
  simp only [ContinuousLinearMap.sub_apply, ContinuousMap.evalCLM_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, fejerMeanCLM_apply, fourier_eval_zero]
  rw [fejerMean_fourier_nat (2 * n) k (by omega), fejerMean_fourier_nat n k hn]
  by_cases hk2 : k < 2 * n
  · rw [if_pos hk2]
    by_cases hk : k < n
    · rw [if_pos hk]
      simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, zero_mul, sub_zero]
      norm_num
      push_cast
      rw [Nat.cast_sub (by omega : k ≤ 2 * n), Nat.cast_sub (by omega : k ≤ n)]
      push_cast
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      field_simp
      nlinarith
    · rw [if_neg hk]
      simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, zero_mul, sub_zero]
      norm_num
      push_cast
      rw [Nat.cast_sub (by omega : k ≤ 2 * n)]
      push_cast
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hkR : (n : ℝ) ≤ k := by exact_mod_cast Nat.le_of_not_gt hk
      field_simp
      nlinarith
  · rw [if_neg hk2, if_neg (by omega : ¬ k < n)]
    norm_num

/-- For [a positive order](hyp:n,hn) and [a negative frequency magnitude](hyp:k), [the real part of the cusp multiplier is nonnegative](goal).

 The real part of the cusp multiplier is nonnegative at every negative
frequency. -/
lemma cuspFunctional_fourier_neg_nat_nonneg (n k : ℕ) (hn : 0 < n) :
    0 ≤ (cuspFunctionalCLM n hn (fourier (-(k : ℤ)))).re := by
  rw [cuspFunctionalCLM, valleePoussinMeanCLM]
  simp only [ContinuousLinearMap.sub_apply, ContinuousMap.evalCLM_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, fejerMeanCLM_apply, fourier_eval_zero]
  rw [fejerMean_fourier_neg_nat (2 * n) k (by omega), fejerMean_fourier_neg_nat n k hn]
  by_cases hk2 : k < 2 * n
  · rw [if_pos hk2]
    by_cases hk : k < n
    · rw [if_pos hk]
      simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, zero_mul, sub_zero]
      norm_num
      push_cast
      rw [Nat.cast_sub (by omega : k ≤ 2 * n), Nat.cast_sub (by omega : k ≤ n)]
      push_cast
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      field_simp
      nlinarith
    · rw [if_neg hk]
      simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, zero_mul, sub_zero]
      norm_num
      push_cast
      rw [Nat.cast_sub (by omega : k ≤ 2 * n)]
      push_cast
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hkR : (n : ℝ) ≤ k := by exact_mod_cast Nat.le_of_not_gt hk
      field_simp
      nlinarith
  · rw [if_neg hk2, if_neg (by omega : ¬ k < n)]
    norm_num

/-- For [a positive order](hyp:n,hn) and [a nonnegative frequency at least twice that order](hyp:k,hk), [the cusp functional has multiplier one](goal).

 The cusp functional has multiplier one at nonnegative frequencies at
least `2n`. -/
lemma cuspFunctional_fourier_nat_high (n k : ℕ) (hn : 0 < n)
    (hk : 2 * n ≤ k) : cuspFunctionalCLM n hn (fourier (k : ℤ)) = 1 := by
  rw [cuspFunctionalCLM, valleePoussinMeanCLM]
  simp only [ContinuousLinearMap.sub_apply, ContinuousMap.evalCLM_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, fejerMeanCLM_apply, fourier_eval_zero]
  rw [fejerMean_fourier_nat (2 * n) k (by omega), fejerMean_fourier_nat n k hn,
    if_neg (by omega : ¬ k < 2 * n), if_neg (by omega : ¬ k < n)]
  norm_num

/-- For [a positive order](hyp:n,hn) and [a negative frequency magnitude at least twice that order](hyp:k,hk), [the cusp functional has multiplier one](goal).

 The cusp functional has multiplier one at negative frequencies of
magnitude at least `2n`. -/
lemma cuspFunctional_fourier_neg_nat_high (n k : ℕ) (hn : 0 < n)
    (hk : 2 * n ≤ k) : cuspFunctionalCLM n hn (fourier (-(k : ℤ))) = 1 := by
  rw [cuspFunctionalCLM, valleePoussinMeanCLM]
  simp only [ContinuousLinearMap.sub_apply, ContinuousMap.evalCLM_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, fejerMeanCLM_apply, fourier_eval_zero]
  rw [fejerMean_fourier_neg_nat (2 * n) k (by omega), fejerMean_fourier_neg_nat n k hn,
    if_neg (by omega : ¬ k < 2 * n), if_neg (by omega : ¬ k < n)]
  norm_num

/-- For [a positive order](hyp:n,hn) and [a continuous input](hyp:f), [the cusp functional is bounded by four times the uniform norm](goal).

 The cusp functional is bounded pointwise by four times the uniform norm
of its input. -/
lemma cuspFunctional_norm_apply_le (n : ℕ) (hn : 0 < n)
    (f : C(AddCircle Real.pi, ℂ)) :
    ‖cuspFunctionalCLM n hn f‖ ≤ 4 * ‖f‖ := by
  rw [cuspFunctionalCLM]
  simp only [ContinuousLinearMap.sub_apply, ContinuousMap.evalCLM_apply]
  calc
    ‖f 0 - valleePoussinMeanCLM n hn f‖ ≤
        ‖f 0‖ + ‖valleePoussinMeanCLM n hn f‖ := norm_sub_le _ _
    _ ≤ ‖f‖ + (2 * ‖f‖ + ‖f‖) := by
      gcongr
      · exact ContinuousMap.norm_coe_le_norm f 0
      · rw [valleePoussinMeanCLM]
        simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
        calc
          ‖2 * fejerMeanCLM (2 * n) (by omega) f - fejerMeanCLM n hn f‖ ≤
              ‖2 * fejerMeanCLM (2 * n) (by omega) f‖ + ‖fejerMeanCLM n hn f‖ :=
            norm_sub_le _ _
          _ ≤ 2 * ‖f‖ + ‖f‖ := by
            rw [norm_mul]
            norm_num
            gcongr
            · simpa [fejerMeanCLM] using fejerMean_norm_le (2 * n) (by omega) f ‖f‖
                (fun t => ContinuousMap.norm_coe_le_norm f t)
            · simpa [fejerMeanCLM] using fejerMean_norm_le n hn f ‖f‖
                (fun t => ContinuousMap.norm_coe_le_norm f t)
    _ = 4 * ‖f‖ := by ring

/-- For [two real coefficients, a frequency, and a circle coordinate](hyp:A,B,k,t), [the conjugate Fourier pair equals the corresponding real sine--cosine mode](goal).

 A conjugate pair of Fourier characters equals the corresponding real
sine-cosine mode. -/
lemma fourier_pair_eq (A B : ℝ) (k : ℕ) (t : ℝ) :
    (((A : ℂ) - B * Complex.I) / 2) * fourier (k : ℤ) (t : AddCircle Real.pi) +
      (((A : ℂ) + B * Complex.I) / 2) * fourier (-(k : ℤ)) (t : AddCircle Real.pi) =
      ((A * Real.cos (2 * k * t) + B * Real.sin (2 * k * t) : ℝ) : ℂ) := by
  rw [fourier_coe_apply, fourier_coe_apply]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (((k : ℕ) : ℤ) : ℂ) * (t : ℂ) / Real.pi =
      ((2 * (k : ℝ) * t : ℝ) : ℂ) * Complex.I by
        field_simp
        push_cast
        ring]
  simp only [Int.cast_neg]
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (-(((k : ℕ) : ℤ) : ℂ)) * (t : ℂ) / Real.pi =
      (-((2 * (k : ℝ) * t : ℝ) : ℂ)) * Complex.I by
        field_simp
        push_cast
        ring]
  rw [Complex.exp_mul_I, Complex.exp_mul_I]
  simp only [Complex.cos_neg, Complex.sin_neg]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- For [a polynomial of degree at most a positive order](hyp:p,n,hn,hp), [there is a corresponding Fourier polynomial that agrees after sine composition and is annihilated by the cusp functional](goal).

 Composing a degree-at-most-`n` real polynomial with `sin (2t)` produces a
Fourier polynomial annihilated by the order-`n` cusp functional. -/
lemma exists_fourierPoly_sinDouble (p : Polynomial ℝ) (n : ℕ) (hn : 0 < n)
    (hp : p.natDegree ≤ n) :
    ∃ q : C(AddCircle Real.pi, ℂ),
      (∀ t : ℝ, q (t : AddCircle Real.pi) = (p.eval (Real.sin (2 * t)) : ℝ)) ∧
      cuspFunctionalCLM n hn q = 0 := by
  open Causalean.Mathlib.Analysis.BernsteinSzegoTrig in
  obtain ⟨a, b, hab⟩ := cosComp_isTrigPolyLE p n hp
  let A : ℕ → ℝ := fun k =>
    a k * Real.cos ((k : ℝ) * (Real.pi / 2)) +
      b k * Real.sin ((k : ℝ) * (Real.pi / 2))
  let B : ℕ → ℝ := fun k =>
    a k * Real.sin ((k : ℝ) * (Real.pi / 2)) -
      b k * Real.cos ((k : ℝ) * (Real.pi / 2))
  let q : C(AddCircle Real.pi, ℂ) :=
    ∑ k ∈ Finset.range (n + 1),
      ((((A k : ℂ) - B k * Complex.I) / 2) • fourier (k : ℤ) +
        (((A k : ℂ) + B k * Complex.I) / 2) • fourier (-(k : ℤ)))
  refine ⟨q, ?_, ?_⟩
  · intro t
    rw [show Real.sin (2 * t) = Real.cos (Real.pi / 2 - 2 * t) by
      rw [Real.cos_pi_div_two_sub]]
    rw [show p.eval (Real.cos (Real.pi / 2 - 2 * t)) =
        ∑ k ∈ Finset.range (n + 1),
          (a k * Real.cos ((k : ℝ) * (Real.pi / 2 - 2 * t)) +
            b k * Real.sin ((k : ℝ) * (Real.pi / 2 - 2 * t))) from
      hab (Real.pi / 2 - 2 * t)]
    simp only [q, ContinuousMap.sum_apply, ContinuousMap.add_apply,
      ContinuousMap.smul_apply, smul_eq_mul]
    push_cast
    apply Finset.sum_congr rfl
    intro k hk
    rw [fourier_pair_eq]
    push_cast
    dsimp [A, B]
    push_cast
    rw [show (k : ℂ) * ((Real.pi : ℂ) / 2 - 2 * (t : ℂ)) =
      (k : ℂ) * ((Real.pi : ℂ) / 2) - 2 * (k : ℂ) * (t : ℂ) by ring,
      Complex.cos_sub, Complex.sin_sub]
    ring
  · simp only [q, map_sum, map_add, map_smul]
    apply Finset.sum_eq_zero
    intro k hk
    have hkn : k ≤ n := by
      have := Finset.mem_range.mp hk
      omega
    rw [cuspFunctional_fourier_nat n k hn hkn,
      cuspFunctional_fourier_neg_nat n k hn hkn]
    simp

/-- [The circle-doubling map](goal) is the continuous map from the additive circle of period π to itself that sends each point to twice that point. -/
noncomputable def circleDouble : C(AddCircle Real.pi, AddCircle Real.pi) :=
  ⟨fun t => 2 • t, continuous_nsmul 2⟩

/-- For [a Fourier frequency](hyp:j), [composition with circle doubling doubles that frequency](goal).

 Composing a Fourier character with circle doubling doubles its frequency. -/
lemma fourier_comp_circleDouble (j : ℤ) :
    (fourier j).comp circleDouble = fourier (2 * j) := by
  ext t
  simp only [ContinuousMap.comp_apply, circleDouble, fourier_apply]
  congr 2
  change j • (2 • t) = (2 * j) • t
  change j • ((2 : ℤ) • t) = _
  rw [← mul_zsmul, mul_comm]


end

end Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.FejerCertificate
