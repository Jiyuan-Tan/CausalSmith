/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Estimation.NPIV.Operator.Adjoint
public import Causalean.Estimation.NPIV.Operator.Complexification
public import Causalean.Estimation.NPIV.Operator.SpectralCalculus_Part1
public import Causalean.Estimation.NPIV.Operator.Tikhonov
public import Causalean.Estimation.NPIV.SourceCondition
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Strong and weak spectral Tikhonov bias bounds

This second spectral part lifts the scalar residual estimates to the normal
operator and proves the strong- and weak-metric bias inequalities.  It ends
with `TikhonovPullback`, the explicit witness that an ambient `L²` minimizer is
represented by a member of the primal candidate set.
-/

@[expose] public section

namespace Causalean
namespace Estimation
namespace NPIV

open MeasureTheory ContinuousLinearMap

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

attribute [local instance 2000] instAlgebraRealLpCLM

namespace SpectralSourceCondition

variable {S : OperatorSystem Ω μ} {β : ℝ}
private lemma weak_residual_bound
    {x lambda β B : ℝ} (hl : 0 < lambda) (hx : 0 ≤ x) (hxB : x ≤ B)
    (hβ0 : 0 ≤ β) (hB : 1 ≤ B) :
    |x * (-lambda * sourceSymbol β x / (lambda + max 0 x)) ^ 2|
      ≤ B ^ β * lambda ^ (min (β + 1) 2) := by
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hden_pos : 0 < lambda + x := by linarith
  have hden_max : lambda + max 0 x = lambda + x := by rw [max_eq_right hx]
  have hsrc : sourceSymbol β x = x ^ (β / 2) := by
    simp [sourceSymbol, max_eq_left hx]
  have hbase_nonneg : 0 ≤ x * (-lambda * sourceSymbol β x / (lambda + max 0 x)) ^ 2 :=
    mul_nonneg hx (sq_nonneg _)
  rw [abs_of_nonneg hbase_nonneg, hden_max, hsrc]
  by_cases hβ1 : β ≤ 1
  · have hmin : min (β + 1) 2 = β + 1 := by
      rw [min_eq_left]
      linarith
    rw [hmin]
    have hβp1_nonneg : 0 ≤ β + 1 := by linarith
    have hβp1_pos : 0 < β + 1 := by linarith
    have hx_le_den : x ≤ lambda + x := by linarith
    have hl_le_den : lambda ≤ lambda + x := by linarith
    have hpow_le : x ^ (β + 1) ≤ (lambda + x) ^ (β + 1) :=
      Real.rpow_le_rpow hx hx_le_den hβp1_nonneg
    have hden_sq_pos : 0 < (lambda + x) ^ 2 := sq_pos_of_pos hden_pos
    have hdiv_le : x ^ (β + 1) / (lambda + x) ^ 2 ≤
        (lambda + x) ^ (β + 1) / (lambda + x) ^ 2 :=
      div_le_div_of_nonneg_right hpow_le (le_of_lt hden_sq_pos)
    have hden_pow : (lambda + x) ^ (β + 1) / (lambda + x) ^ 2 =
        (lambda + x) ^ (β - 1) := by
      calc
        (lambda + x) ^ (β + 1) / (lambda + x) ^ 2
            = (lambda + x) ^ (β + 1) / (lambda + x) ^ (2 : ℝ) := by norm_num
        _ = (lambda + x) ^ ((β + 1) - 2) := by rw [Real.rpow_sub hden_pos]
        _ = (lambda + x) ^ (β - 1) := by ring_nf
    have hpow_neg : (lambda + x) ^ (β - 1) ≤ lambda ^ (β - 1) :=
      Real.rpow_le_rpow_of_nonpos hl hl_le_den (by linarith)
    have hmul_lam : lambda ^ 2 * lambda ^ (β - 1) = lambda ^ (β + 1) := by
      rw [show lambda ^ (2 : ℕ) = lambda ^ (2 : ℝ) by norm_num]
      rw [← Real.rpow_add hl]
      congr 1
      ring
    have hmain :
        lambda ^ 2 * x ^ (β + 1) / (lambda + x) ^ 2 ≤ lambda ^ (β + 1) := by
      calc
        lambda ^ 2 * x ^ (β + 1) / (lambda + x) ^ 2
            = lambda ^ 2 * (x ^ (β + 1) / (lambda + x) ^ 2) := by ring
        _ ≤ lambda ^ 2 * ((lambda + x) ^ (β + 1) / (lambda + x) ^ 2) := by
          gcongr
        _ = lambda ^ 2 * (lambda + x) ^ (β - 1) := by rw [hden_pow]
        _ ≤ lambda ^ 2 * lambda ^ (β - 1) := by gcongr
        _ = lambda ^ (β + 1) := hmul_lam
    have hBpow : 1 ≤ B ^ β := Real.one_le_rpow hB hβ0
    have hlpow_nonneg : 0 ≤ lambda ^ (β + 1) := Real.rpow_nonneg (le_of_lt hl) _
    have hxpow : x * (x ^ (β / 2)) ^ 2 = x ^ (β + 1) := by
      by_cases hxzero : x = 0
      · subst x
        rw [zero_mul]
        exact (Real.zero_rpow (ne_of_gt hβp1_pos)).symm
      · have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hxzero)
        rw [sq]
        calc
          x * (x ^ (β / 2) * x ^ (β / 2))
              = (x ^ (1 : ℝ) * x ^ (β / 2)) * x ^ (β / 2) := by
                rw [Real.rpow_one]
                ring
          _ = x ^ ((1 : ℝ) + β / 2) * x ^ (β / 2) := by
                rw [← Real.rpow_add hxp]
          _ = x ^ ((1 : ℝ) + β / 2 + β / 2) := by rw [← Real.rpow_add hxp]
          _ = x ^ (β + 1) := by congr 1; ring
    calc
      x * (-lambda * x ^ (β / 2) / (lambda + x)) ^ 2
          = lambda ^ 2 * x ^ (β + 1) / (lambda + x) ^ 2 := by
            have hden_ne : lambda + x ≠ 0 := ne_of_gt hden_pos
            field_simp [hden_ne]
            exact hxpow
      _ ≤ lambda ^ (β + 1) := hmain
      _ ≤ B ^ β * lambda ^ (β + 1) := by nlinarith
  · have hβgt : 1 < β := lt_of_not_ge hβ1
    have hmin : min (β + 1) 2 = 2 := by
      rw [min_eq_right]
      linarith
    rw [hmin]
    have hβm_nonneg : 0 ≤ β - 1 := by linarith
    have hβp1_pos : 0 < β + 1 := by linarith
    have hBpow : B ^ (β - 1) ≤ B ^ β :=
      Real.rpow_le_rpow_of_exponent_le hB (by linarith)
    by_cases hxzero : x = 0
    · subst x
      rw [zero_mul]
      exact mul_nonneg (Real.rpow_nonneg (le_of_lt hBpos) _)
        (Real.rpow_nonneg (le_of_lt hl) _)
    · have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hxzero)
      have hx_sq_pos : 0 < x ^ 2 := sq_pos_of_pos hxp
      have hx_sq_le_den_sq : x ^ 2 ≤ (lambda + x) ^ 2 := by nlinarith
      have hnum_nonneg : 0 ≤ x ^ (β + 1) := Real.rpow_nonneg hx _
      have hdiv_le : x ^ (β + 1) / (lambda + x) ^ 2 ≤ x ^ (β + 1) / x ^ 2 :=
        div_le_div_of_nonneg_left hnum_nonneg hx_sq_pos hx_sq_le_den_sq
      have hxpow_div : x ^ (β + 1) / x ^ 2 = x ^ (β - 1) := by
        calc
          x ^ (β + 1) / x ^ 2 = x ^ (β + 1) / x ^ (2 : ℝ) := by norm_num
          _ = x ^ ((β + 1) - 2) := by rw [Real.rpow_sub hxp]
          _ = x ^ (β - 1) := by ring_nf
      have hxBpow : x ^ (β - 1) ≤ B ^ (β - 1) :=
        Real.rpow_le_rpow hx hxB hβm_nonneg
      have hquot : x ^ (β + 1) / (lambda + x) ^ 2 ≤ B ^ β := by
        calc
          x ^ (β + 1) / (lambda + x) ^ 2 ≤ x ^ (β + 1) / x ^ 2 := hdiv_le
          _ = x ^ (β - 1) := hxpow_div
          _ ≤ B ^ (β - 1) := hxBpow
          _ ≤ B ^ β := hBpow
      have hxpow : x * (x ^ (β / 2)) ^ 2 = x ^ (β + 1) := by
        rw [sq]
        calc
          x * (x ^ (β / 2) * x ^ (β / 2))
              = (x ^ (1 : ℝ) * x ^ (β / 2)) * x ^ (β / 2) := by
                rw [Real.rpow_one]
                ring
          _ = x ^ ((1 : ℝ) + β / 2) * x ^ (β / 2) := by
                rw [← Real.rpow_add hxp]
          _ = x ^ ((1 : ℝ) + β / 2 + β / 2) := by rw [← Real.rpow_add hxp]
          _ = x ^ (β + 1) := by congr 1; ring
      have hmain :
          lambda ^ 2 * x ^ (β + 1) / (lambda + x) ^ 2 ≤ B ^ β * lambda ^ (2 : ℝ) := by
        rw [show lambda ^ (2 : ℝ) = lambda ^ (2 : ℕ) by norm_num]
        calc
          lambda ^ 2 * x ^ (β + 1) / (lambda + x) ^ 2
              = lambda ^ 2 * (x ^ (β + 1) / (lambda + x) ^ 2) := by ring
          _ ≤ lambda ^ 2 * B ^ β := by gcongr
          _ = B ^ β * lambda ^ 2 := by ring
      calc
        x * (-lambda * x ^ (β / 2) / (lambda + x)) ^ 2
            = lambda ^ 2 * x ^ (β + 1) / (lambda + x) ^ 2 := by
              have hden_ne : lambda + x ≠ 0 := ne_of_gt hden_pos
              field_simp [hden_ne]
              exact hxpow
        _ ≤ B ^ β * lambda ^ (2 : ℝ) := hmain

/-- **Strong-metric Tikhonov bias bound.** Given a spectral β-source condition `sc` linking the
structural function `h₀` to a coefficient `w₀` through the spectral power operator `(T†T)^{β/2}`,
for [any strictly positive Tikhonov regularization level λ](hyp:lambda_pos), [the squared
strong-metric ($L^2(P_X)$) distance between the Tikhonov minimiser `h*_λ` at level λ and `h₀` is
bounded by `biasConst · ‖w₀‖² · λ^{min(β,2)}`, where `biasConst` is a constant determined by
`T†T` and β](goal).

Spectral derivation: by `tikhonovMinimiserL2_eq_resolvent` and the
spectral identity `h₀ = realCFC (T†T) (·^{β/2}) w₀` from
`SourceCondition.spectral_identity`,
    h*_λ − h₀ = realCFC (T†T) (x ↦ −λ x^{β/2}/(λ+x)) w₀.

By `Complexification.realCFC_norm_le` with the uniform sup bound
`sup_{x ≥ 0} (λ x^{β/2}/(λ+x))² ≤ biasConst · λ^{min(β,2)}`, the squared
norm is bounded by `biasConst · ‖w₀‖² · λ^{min(β,2)}`.

Proof strategy:
1.  Apply `tikhonovMinimiserL2_eq_resolvent` and `spectral_identity`.
2.  Use `Complexification.realCFC_mul` to merge the two real CFCs into
    a single CFC with the product symbol.
3.  Apply `Complexification.realCFC_norm_le` with the sup-on-spectrum
    bound (real-analysis lemma: for `x ∈ [0, ‖T†T‖]` and `λ > 0`,
    `(λ x^{β/2}/(λ+x))² ≤ biasConst · λ^{min(β,2)}`).
4.  Square to get the squared-norm bound. -/
theorem strong_bias (sc : SpectralSourceCondition S β)
    {lambda : ℝ} (lambda_pos : 0 < lambda) :
        ‖S.primalTrimEquiv (S.tikhonovMinimiserL2 lambda) - S.primalTrimEquiv (S.hL2 S.h₀_mem)‖ ^ 2
      ≤ sc.biasConst * ‖S.primalTrimEquiv (S.hL2 sc.w₀_mem)‖ ^ 2 * lambda ^ (min β 2) := by
  by_cases hnt : Nontrivial (Lp ℝ 2 (μ.trim S.m_X_le))
  swap
  · haveI : Subsingleton (Lp ℝ 2 (μ.trim S.m_X_le)) := not_nontrivial_iff_subsingleton.mp hnt
    have hdiff : S.primalTrimEquiv (S.tikhonovMinimiserL2 lambda) - S.primalTrimEquiv (S.hL2 S.h₀_mem) = 0 := Subsingleton.elim _ _
    have hpow_nonneg : 0 ≤ lambda ^ (min β 2) := Real.rpow_nonneg (le_of_lt lambda_pos) _
    have hrhs_nonneg :
        0 ≤ sc.biasConst * ‖S.primalTrimEquiv (S.hL2 sc.w₀_mem)‖ ^ 2 * lambda ^ (min β 2) :=
      mul_nonneg (mul_nonneg sc.biasConst_nonneg (sq_nonneg _)) hpow_nonneg
    simpa [hdiff] using hrhs_nonneg
  haveI : Nontrivial (Lp ℝ 2 (μ.trim S.m_X_le)) := hnt
  haveI : NormOneClass (Lp ℝ 2 (μ.trim S.m_X_le) →L[ℝ] Lp ℝ 2 (μ.trim S.m_X_le)) := ContinuousLinearMap.normOneClass
  set A := S.Tstar_T_trim with hA_def
  set w := S.primalTrimEquiv (S.hL2 sc.w₀_mem) with hw_def
  set B : ℝ := max 1 (‖A‖ + 1) with hB_def
  set c : ℝ := B ^ (β / 2) * lambda ^ (min β 2 / 2) with hc_def
  have hA_sa : IsSelfAdjoint A := by simpa [hA_def] using S.Tstar_T_trim_isSelfAdjoint
  have hβ : 0 ≤ β := sc.beta_pos.le
  have hB_ge_one : 1 ≤ B := by
    rw [hB_def]
    exact le_max_left _ _
  have hB_pos : 0 < B := lt_of_lt_of_le zero_lt_one hB_ge_one
  have hc_nonneg : 0 ≤ c := by
    rw [hc_def]
    exact mul_nonneg (Real.rpow_nonneg (le_of_lt hB_pos) _)
      (Real.rpow_nonneg (le_of_lt lambda_pos) _)
  have hden : ∀ x : ℝ, lambda + max 0 x ≠ 0 := fun x => by
    have hmax : (0 : ℝ) ≤ max 0 x := le_max_left _ _
    have hpos : 0 < lambda + max 0 x := by linarith
    exact ne_of_gt hpos
  let rSafe : ℝ → ℝ := fun x => x / (lambda + max 0 x)
  let prod : ℝ → ℝ := fun x => rSafe x * sourceSymbol β x
  have hr_cont : Continuous rSafe := by
    dsimp [rSafe]
    exact continuous_id.div (continuous_const.add (continuous_const.max continuous_id)) hden
  have hsrc_cont : Continuous (sourceSymbol β) := continuous_sourceSymbol hβ
  have hsource_eq : (fun x : ℝ => Real.rpow (max x 0) (β / 2)) = sourceSymbol β := rfl
  have hres_safe :
      S.realCFCTrim A (fun x => x / (lambda + x)) =
        S.realCFCTrim A rSafe := by
    unfold OperatorSystem.realCFCTrim
    apply @realCFC_congr_on_spectrum_local Ω S.m_X (μ.trim S.m_X_le) A
    · intro x hx
      have hx0 : 0 ≤ x := Tstar_T_spectrum_nonneg S x (by simpa [hA_def] using hx)
      dsimp [rSafe]
      rw [max_eq_right hx0]
    · exact hA_sa
  have hmul : S.realCFCTrim A prod =
      (S.realCFCTrim A rSafe).comp
        (S.realCFCTrim A (sourceSymbol β)) := by
    dsimp [prod]
    simpa [OperatorSystem.realCFCTrim] using
      (@Complexification.realCFC_mul Ω S.m_X (μ.trim S.m_X_le) A hA_sa
        rSafe (sourceSymbol β) hr_cont hsrc_cont)
  have hsub_cfc : S.realCFCTrim A (fun x => prod x - sourceSymbol β x) =
      S.realCFCTrim A prod - S.realCFCTrim A (sourceSymbol β) :=
    by
      simpa [OperatorSystem.realCFCTrim] using
        (@realCFC_sub_local Ω S.m_X (μ.trim S.m_X_le) A hA_sa
          prod (sourceSymbol β) (hr_cont.mul hsrc_cont) hsrc_cont)
  have hsymbol : S.realCFCTrim A (fun x => prod x - sourceSymbol β x) =
      S.realCFCTrim A
        (fun x => -lambda * sourceSymbol β x / (lambda + max 0 x)) := by
    unfold OperatorSystem.realCFCTrim
    apply @realCFC_congr_on_spectrum_local Ω S.m_X (μ.trim S.m_X_le) A
    · intro x hx
      have hx0 : 0 ≤ x := Tstar_T_spectrum_nonneg S x (by simpa [hA_def] using hx)
      have hne : lambda + max 0 x ≠ 0 := hden x
      dsimp [prod, rSafe]
      rw [max_eq_right hx0]
      field_simp [hne]
      ring
    · exact hA_sa
  have hresid :
      S.primalTrimEquiv (S.tikhonovMinimiserL2 lambda) - S.primalTrimEquiv (S.hL2 S.h₀_mem) =
        S.realCFCTrim A
          (fun x => -lambda * sourceSymbol β x / (lambda + max 0 x)) w := by
    calc
      S.primalTrimEquiv (S.tikhonovMinimiserL2 lambda) - S.primalTrimEquiv (S.hL2 S.h₀_mem)
          = (S.realCFCTrim A rSafe)
              ((S.realCFCTrim A (sourceSymbol β)) w) -
            (S.realCFCTrim A (sourceSymbol β)) w := by
          rw [tikhonovMinimiserL2_eq_resolvent (S := S) lambda_pos]
          rw [sc.spectral_identity]
          rw [hsource_eq]
          change (S.realCFCTrim S.Tstar_T_trim (fun x => x / (lambda + x)))
              ((S.realCFCTrim S.Tstar_T_trim (sourceSymbol β))
                (S.primalTrimEquiv (S.hL2 sc.w₀_mem))) -
            (S.realCFCTrim S.Tstar_T_trim (sourceSymbol β))
                (S.primalTrimEquiv (S.hL2 sc.w₀_mem)) = _
          rw [← hA_def, ← hw_def]
          rw [hres_safe]
      _ = ((S.realCFCTrim A rSafe).comp
            (S.realCFCTrim A (sourceSymbol β))) w -
            (S.realCFCTrim A (sourceSymbol β)) w := by rfl
      _ = (S.realCFCTrim A prod -
            S.realCFCTrim A (sourceSymbol β)) w := by
          rw [← hmul]
          simp only [ContinuousLinearMap.sub_apply]
      _ = S.realCFCTrim A (fun x => prod x - sourceSymbol β x) w := by
          rw [hsub_cfc]
      _ = S.realCFCTrim A
            (fun x => -lambda * sourceSymbol β x / (lambda + max 0 x)) w := by
          rw [hsymbol]
  have hsafe_cont :
      Continuous (fun x : ℝ => -lambda * sourceSymbol β x / (lambda + max 0 x)) :=
    (continuous_const.mul hsrc_cont).div
      (continuous_const.add (continuous_const.max continuous_id)) hden
  have hsup : ∀ x ∈ spectrum ℝ A,
      |(-lambda * sourceSymbol β x / (lambda + max 0 x))| ≤ c := by
    intro x hx
    have hx0 : 0 ≤ x := Tstar_T_spectrum_nonneg S x (by simpa [hA_def] using hx)
    rw [hc_def]
    by_cases hβ2 : β ≤ 2
    · exact residual_symbol_bound_small lambda_pos hx0 hβ hβ2 hB_ge_one
    · have hxnorm : ‖x‖ ≤ ‖A‖ := spectrum.norm_le_norm_of_mem hx
      have hx_le_norm : x ≤ ‖A‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg hx0] at hxnorm
        exact hxnorm
      have hnorm_le_B : ‖A‖ ≤ B := by
        calc
          ‖A‖ ≤ ‖A‖ + 1 := by linarith [norm_nonneg A]
          _ ≤ max 1 (‖A‖ + 1) := le_max_right _ _
          _ = B := by rw [hB_def]
      have hxB : x ≤ B := le_trans hx_le_norm hnorm_le_B
      exact residual_symbol_bound_large lambda_pos hx0 hxB (lt_of_not_ge hβ2) hB_ge_one
  have hnorm :=
    @Complexification.realCFC_norm_le Ω S.m_X (μ.trim S.m_X_le) A hA_sa
      (fun x => -lambda * sourceSymbol β x / (lambda + max 0 x)) hsafe_cont
      c hc_nonneg hsup w
  have hsq :
      ‖S.realCFCTrim A
          (fun x => -lambda * sourceSymbol β x / (lambda + max 0 x)) w‖ ^ 2
        ≤ (c * ‖w‖) ^ 2 :=
    sq_le_sq' (by
      have hmul_nonneg : 0 ≤ c * ‖w‖ := mul_nonneg hc_nonneg (norm_nonneg _)
      nlinarith [norm_nonneg
        (S.realCFCTrim A
          (fun x => -lambda * sourceSymbol β x / (lambda + max 0 x)) w), hmul_nonneg]) hnorm
  have hcoef : (c * ‖w‖) ^ 2 =
      sc.biasConst * ‖w‖ ^ 2 * lambda ^ (min β 2) := by
    rw [hc_def, mul_pow, mul_pow]
    rw [show (B ^ (β / 2)) ^ (2 : ℕ) = B ^ β by
      rw [sq, ← Real.rpow_add hB_pos]
      congr 1
      ring]
    rw [show (lambda ^ (min β 2 / 2)) ^ (2 : ℕ) = lambda ^ (min β 2) by
      rw [sq, ← Real.rpow_add lambda_pos]
      congr 1
      ring]
    rw [biasConst]
    simp [hB_def, hA_def]
    ring
  calc
    ‖S.primalTrimEquiv (S.tikhonovMinimiserL2 lambda) - S.primalTrimEquiv (S.hL2 S.h₀_mem)‖ ^ 2
        = ‖S.realCFCTrim A
            (fun x => -lambda * sourceSymbol β x / (lambda + max 0 x)) w‖ ^ 2 := by
          rw [hresid]
    _ ≤ (c * ‖w‖) ^ 2 := hsq
    _ = sc.biasConst * ‖S.primalTrimEquiv (S.hL2 sc.w₀_mem)‖ ^ 2 * lambda ^ (min β 2) := by
          rw [hcoef, hw_def]

/-- **Weak-metric Tikhonov bias bound.** Given the same spectral β-source condition `sc` linking
`h₀` to `w₀` through `(T†T)^{β/2}`, for [any strictly positive Tikhonov regularization level
λ](hyp:lambda_pos), [the squared weak-metric ($L^2(P_Z)$) norm of the operator `T` applied to the
Tikhonov-minimiser bias `h*_λ − h₀` is bounded by `biasConst · ‖w₀‖² · λ^{min(β+1,2)}`](goal).

Spectral derivation: from the same resolvent identity for `h*_λ − h₀`,
    ‖T(h*_λ − h₀)‖² = ⟨T†T (h*_λ − h₀), h*_λ − h₀⟩
                    = ⟨realCFC (T†T) (x · (λ x^{β/2}/(λ+x))²) w₀, w₀⟩.

By Cauchy–Schwarz and `realCFC_norm_le` with the sup bound
`sup_{x ≥ 0} x · (λ x^{β/2}/(λ+x))² ≤ biasConst · λ^{min(β+1, 2)}`,
the LHS is bounded by `biasConst · ‖w₀‖² · λ^{min(β+1, 2)}`.

Proof strategy:
1.  Rewrite `‖T u‖²` as `⟨T†T u, u⟩` (positivity of `T†T`).
2.  Substitute `u = realCFC (T†T) (...) w₀` from the resolvent + source
    identities.
3.  Use `realCFC_mul` and the action of `realCFC (T†T) id = T†T` to
    obtain a single CFC factor.
4.  Use `realCFC_norm_le` + Cauchy–Schwarz with the sup analysis. -/
theorem weak_bias (sc : SpectralSourceCondition S β)
    {lambda : ℝ} (lambda_pos : 0 < lambda) :
        ‖S.TlinTrim (S.primalTrimEquiv (S.tikhonovMinimiserL2 lambda) - S.primalTrimEquiv (S.hL2 S.h₀_mem))‖ ^ 2
      ≤ sc.biasConst * ‖S.primalTrimEquiv (S.hL2 sc.w₀_mem)‖ ^ 2 * lambda ^ (min (β + 1) 2) := by
  by_cases hnt : Nontrivial (Lp ℝ 2 (μ.trim S.m_X_le))
  swap
  · haveI : Subsingleton (Lp ℝ 2 (μ.trim S.m_X_le)) := not_nontrivial_iff_subsingleton.mp hnt
    have hdom :
        S.primalTrimEquiv (S.tikhonovMinimiserL2 lambda) -
            S.primalTrimEquiv (S.hL2 S.h₀_mem) = 0 :=
      Subsingleton.elim _ _
    have hpow_nonneg : 0 ≤ lambda ^ (min (β + 1) 2) :=
      Real.rpow_nonneg (le_of_lt lambda_pos) _
    have hrhs_nonneg :
        0 ≤ sc.biasConst * ‖S.primalTrimEquiv (S.hL2 sc.w₀_mem)‖ ^ 2 * lambda ^ (min (β + 1) 2) :=
      mul_nonneg (mul_nonneg sc.biasConst_nonneg (sq_nonneg _)) hpow_nonneg
    simpa [hdom] using hrhs_nonneg
  haveI : Nontrivial (Lp ℝ 2 (μ.trim S.m_X_le)) := hnt
  haveI : NormOneClass (Lp ℝ 2 (μ.trim S.m_X_le) →L[ℝ] Lp ℝ 2 (μ.trim S.m_X_le)) := ContinuousLinearMap.normOneClass
  set A := S.Tstar_T_trim with hA_def
  set w := S.primalTrimEquiv (S.hL2 sc.w₀_mem) with hw_def
  set B : ℝ := max 1 (‖A‖ + 1) with hB_def
  set f : ℝ → ℝ := fun x => -lambda * sourceSymbol β x / (lambda + max 0 x) with hf_def
  set q : ℝ → ℝ := fun x => x * f x with hq_def
  set g : ℝ → ℝ := fun x => x * f x ^ 2 with hg_def
  set c : ℝ := sc.biasConst * lambda ^ (min (β + 1) 2) with hc_def
  have hA_sa : IsSelfAdjoint A := by simpa [hA_def] using S.Tstar_T_trim_isSelfAdjoint
  have hβ : 0 ≤ β := sc.beta_pos.le
  have hB_ge_one : 1 ≤ B := by
    rw [hB_def]
    exact le_max_left _ _
  have hB_pos : 0 < B := lt_of_lt_of_le zero_lt_one hB_ge_one
  have hden : ∀ x : ℝ, lambda + max 0 x ≠ 0 := fun x => by
    have hmax : (0 : ℝ) ≤ max 0 x := le_max_left _ _
    have hpos : 0 < lambda + max 0 x := by linarith
    exact ne_of_gt hpos
  let rSafe : ℝ → ℝ := fun x => x / (lambda + max 0 x)
  let prod : ℝ → ℝ := fun x => rSafe x * sourceSymbol β x
  have hr_cont : Continuous rSafe := by
    dsimp [rSafe]
    exact continuous_id.div (continuous_const.add (continuous_const.max continuous_id)) hden
  have hsrc_cont : Continuous (sourceSymbol β) := continuous_sourceSymbol hβ
  have hf_cont : Continuous f := by
    rw [hf_def]
    exact (continuous_const.mul hsrc_cont).div
      (continuous_const.add (continuous_const.max continuous_id)) hden
  have hq_cont : Continuous q := by
    rw [hq_def]
    exact continuous_id.mul hf_cont
  have hg_cont : Continuous g := by
    rw [hg_def]
    exact continuous_id.mul (hf_cont.pow 2)
  have hsource_eq : (fun x : ℝ => Real.rpow (max x 0) (β / 2)) = sourceSymbol β := rfl
  have hres_safe :
      S.realCFCTrim A (fun x => x / (lambda + x)) =
        S.realCFCTrim A rSafe := by
    unfold OperatorSystem.realCFCTrim
    apply @realCFC_congr_on_spectrum_local Ω S.m_X (μ.trim S.m_X_le) A
    · intro x hx
      have hx0 : 0 ≤ x := Tstar_T_spectrum_nonneg S x (by simpa [hA_def] using hx)
      dsimp [rSafe]
      rw [max_eq_right hx0]
    · exact hA_sa
  have hmul : S.realCFCTrim A prod =
      (S.realCFCTrim A rSafe).comp
        (S.realCFCTrim A (sourceSymbol β)) := by
    dsimp [prod]
    simpa [OperatorSystem.realCFCTrim] using
      (@Complexification.realCFC_mul Ω S.m_X (μ.trim S.m_X_le) A hA_sa
        rSafe (sourceSymbol β) hr_cont hsrc_cont)
  have hsub_cfc : S.realCFCTrim A (fun x => prod x - sourceSymbol β x) =
      S.realCFCTrim A prod - S.realCFCTrim A (sourceSymbol β) :=
    by
      simpa [OperatorSystem.realCFCTrim] using
        (@realCFC_sub_local Ω S.m_X (μ.trim S.m_X_le) A hA_sa
          prod (sourceSymbol β) (hr_cont.mul hsrc_cont) hsrc_cont)
  have hsymbol : S.realCFCTrim A (fun x => prod x - sourceSymbol β x) =
      S.realCFCTrim A f := by
    rw [hf_def]
    unfold OperatorSystem.realCFCTrim
    apply @realCFC_congr_on_spectrum_local Ω S.m_X (μ.trim S.m_X_le) A
    · intro x hx
      have hx0 : 0 ≤ x := Tstar_T_spectrum_nonneg S x (by simpa [hA_def] using hx)
      have hne : lambda + max 0 x ≠ 0 := hden x
      dsimp [prod, rSafe]
      rw [max_eq_right hx0]
      field_simp [hne]
      ring
    · exact hA_sa
  have hresid :
      S.primalTrimEquiv (S.tikhonovMinimiserL2 lambda) - S.primalTrimEquiv (S.hL2 S.h₀_mem) =
        S.realCFCTrim A f w := by
    calc
      S.primalTrimEquiv (S.tikhonovMinimiserL2 lambda) - S.primalTrimEquiv (S.hL2 S.h₀_mem)
          = (S.realCFCTrim A rSafe)
              ((S.realCFCTrim A (sourceSymbol β)) w) -
            (S.realCFCTrim A (sourceSymbol β)) w := by
          rw [tikhonovMinimiserL2_eq_resolvent (S := S) lambda_pos]
          rw [sc.spectral_identity]
          rw [hsource_eq]
          change (S.realCFCTrim S.Tstar_T_trim (fun x => x / (lambda + x)))
              ((S.realCFCTrim S.Tstar_T_trim (sourceSymbol β))
                (S.primalTrimEquiv (S.hL2 sc.w₀_mem))) -
            (S.realCFCTrim S.Tstar_T_trim (sourceSymbol β))
                (S.primalTrimEquiv (S.hL2 sc.w₀_mem)) = _
          rw [← hA_def, ← hw_def]
          rw [hres_safe]
      _ = ((S.realCFCTrim A rSafe).comp
            (S.realCFCTrim A (sourceSymbol β))) w -
            (S.realCFCTrim A (sourceSymbol β)) w := by rfl
      _ = (S.realCFCTrim A prod -
            S.realCFCTrim A (sourceSymbol β)) w := by
          rw [← hmul]
          simp only [ContinuousLinearMap.sub_apply]
      _ = S.realCFCTrim A (fun x => prod x - sourceSymbol β x) w := by
          rw [hsub_cfc]
      _ = S.realCFCTrim A f w := by rw [hsymbol]
  have hAcomp : A.comp (S.realCFCTrim A f) =
      S.realCFCTrim A q := by
    rw [hq_def]
    rw [show (fun x : ℝ => x * f x) = fun x : ℝ => id x * f x by rfl]
    unfold OperatorSystem.realCFCTrim
    rw [@Complexification.realCFC_mul Ω S.m_X (μ.trim S.m_X_le) A hA_sa
      id f continuous_id hf_cont]
    apply ContinuousLinearMap.ext
    intro v
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    rw [@Complexification.realCFC_id Ω S.m_X (μ.trim S.m_X_le) A hA_sa
      ((@Complexification.realCFC Ω S.m_X (μ.trim S.m_X_le) A f) v)]
  have hfg_comp : (S.realCFCTrim A f).comp (S.realCFCTrim A q) =
      S.realCFCTrim A g := by
    unfold OperatorSystem.realCFCTrim
    rw [← @Complexification.realCFC_mul Ω S.m_X (μ.trim S.m_X_le) A hA_sa
      f q hf_cont hq_cont]
    rw [hg_def, hq_def]
    congr 1
    funext x
    ring
  have hTu_sq :
      ‖S.TlinTrim (S.primalTrimEquiv (S.tikhonovMinimiserL2 lambda) - S.primalTrimEquiv (S.hL2 S.h₀_mem))‖ ^ 2 =
        inner ℝ (S.realCFCTrim A g w) w := by
    rw [hresid]
    have hTstar :
        ‖S.TlinTrim (S.realCFCTrim A f w)‖ ^ 2 =
          inner ℝ (A (S.realCFCTrim A f w))
            (S.realCFCTrim A f w) := by
      rw [← real_inner_self_eq_norm_sq]
      subst A
      change inner ℝ (S.TlinTrim (S.realCFCTrim S.Tstar_T_trim f w))
          (S.TlinTrim (S.realCFCTrim S.Tstar_T_trim f w)) =
        inner ℝ (S.TadjointTrim (S.TlinTrim (S.realCFCTrim S.Tstar_T_trim f w)))
          (S.realCFCTrim S.Tstar_T_trim f w)
      rw [OperatorSystem.TadjointTrim, ContinuousLinearMap.adjoint_inner_left]
    rw [hTstar]
    have hAu : A (S.realCFCTrim A f w) =
        S.realCFCTrim A q w := by
      change (A.comp (S.realCFCTrim A f)) w =
        S.realCFCTrim A q w
      rw [hAcomp]
    rw [hAu]
    have hf_sa : IsSelfAdjoint (S.realCFCTrim A f) :=
      by
        simpa [OperatorSystem.realCFCTrim] using
          (@Complexification.realCFC_isSelfAdjoint Ω S.m_X (μ.trim S.m_X_le)
            A hA_sa f hf_cont)
    calc
      inner ℝ (S.realCFCTrim A q w) (S.realCFCTrim A f w)
          = inner ℝ ((S.realCFCTrim A f) (S.realCFCTrim A q w)) w := by
            exact ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hf_sa)
              (S.realCFCTrim A q w) w).symm
      _ = inner ℝ (((S.realCFCTrim A f).comp
            (S.realCFCTrim A q)) w) w := by rfl
      _ = inner ℝ (S.realCFCTrim A g w) w := by rw [hfg_comp]
  have hsup : ∀ x ∈ spectrum ℝ A, |g x| ≤ c := by
    intro x hx
    have hx0 : 0 ≤ x := Tstar_T_spectrum_nonneg S x (by simpa [hA_def] using hx)
    have hxnorm : ‖x‖ ≤ ‖A‖ := spectrum.norm_le_norm_of_mem hx
    have hx_le_norm : x ≤ ‖A‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg hx0] at hxnorm
      exact hxnorm
    have hnorm_le_B : ‖A‖ ≤ B := by
      calc
        ‖A‖ ≤ ‖A‖ + 1 := by linarith [norm_nonneg A]
        _ ≤ max 1 (‖A‖ + 1) := le_max_right _ _
        _ = B := by rw [hB_def]
    have hxB : x ≤ B := le_trans hx_le_norm hnorm_le_B
    rw [hc_def, hg_def, hf_def]
    have hbound := weak_residual_bound lambda_pos hx0 hxB hβ hB_ge_one
    rw [biasConst]
    simpa [hA_def, hB_def] using hbound
  have hc_nonneg : 0 ≤ c := by
    rw [hc_def]
    exact mul_nonneg sc.biasConst_nonneg (Real.rpow_nonneg (le_of_lt lambda_pos) _)
  have hnorm :=
    @Complexification.realCFC_norm_le Ω S.m_X (μ.trim S.m_X_le)
      A hA_sa g hg_cont c hc_nonneg hsup w
  have hcs : inner ℝ (S.realCFCTrim A g w) w ≤ c * ‖w‖ ^ 2 := by
    have hineq : |inner ℝ (S.realCFCTrim A g w) w| ≤
        ‖S.realCFCTrim A g w‖ * ‖w‖ :=
      abs_real_inner_le_norm _ _
    calc
      inner ℝ (S.realCFCTrim A g w) w
          ≤ |inner ℝ (S.realCFCTrim A g w) w| := le_abs_self _
      _ ≤ ‖S.realCFCTrim A g w‖ * ‖w‖ := hineq
      _ ≤ (c * ‖w‖) * ‖w‖ := by
        exact mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
      _ = c * ‖w‖ ^ 2 := by ring
  calc
    ‖S.TlinTrim (S.primalTrimEquiv (S.tikhonovMinimiserL2 lambda) - S.primalTrimEquiv (S.hL2 S.h₀_mem))‖ ^ 2
        = inner ℝ (S.realCFCTrim A g w) w := hTu_sq
    _ ≤ c * ‖w‖ ^ 2 := hcs
    _ = sc.biasConst * ‖S.primalTrimEquiv (S.hL2 sc.w₀_mem)‖ ^ 2 * lambda ^ (min (β + 1) 2) := by
      rw [hc_def, hw_def]
      ring

end SpectralSourceCondition

/-- Function-level pullback datum for the discharge.  The user provides
a `Hbar`-element `h_lambda_star_fun` whose L² class equals the
Lax–Milgram minimiser `tikhonovMinimiserL2 S λ` constructed in
`Operator/Tikhonov.lean`.  This single pullback is the only
function-level commitment needed: the bias and convexity inequalities
all live at the L² level and transport along this equation. -/
structure TikhonovPullback
    (S : OperatorSystem Ω μ) (β : ℝ)
    (sc : SpectralSourceCondition S β) where
  /-- Family of function-level minimisers indexed by the regularization level. -/
  h_lambda_star_fun : ℝ → S.𝒳 → ℝ
  /-- Every positive-level function-level minimiser lies in `Hbar`. -/
  h_lambda_star_mem : ∀ {lambda : ℝ}, 0 < lambda → h_lambda_star_fun lambda ∈ S.Hbar
  /-- Coherence: at every positive level, lifting the function-level minimiser to
  `L²(σ(X))` recovers the Lax–Milgram L² minimiser. -/
  h_lambda_star_pullback : ∀ {lambda : ℝ} (hlambda : 0 < lambda),
    S.hL2 (h_lambda_star_mem hlambda) = S.tikhonovMinimiserL2 lambda

end NPIV
end Estimation
end Causalean
