/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Structure-agnostic ATE: finite-sample lower and upper miss bounds

This file places a structure-agnostic converse and achievability bound in one finite-sample
interface.  The **converse**
(`minimax_lower_bound_var`, `VaryingCenterCase1/LowerBound.lean`) gives a lower miss bound at its
construction-induced separation; the **achievability** (`AIPWEstimator.lean`) bounds the
fixed-center AIPW estimator's worst-case miss at a separately supplied separation. Here we:

* turn the bias + variance bounds into a Chebyshev **worst-case miss** upper bound for AIPW
  (`aipw_minimaxMiss_le`), uniform over the structure-agnostic class;
* define the reusable `FiniteSampleTwoThresholdBounds` vocabulary (an estimator with a converse
  miss-lower-bound at one separation and an achievability miss-upper-bound at another);
* assemble `aipw_finiteSample_twoThreshold_bounds`, which records the construction's lower
  miss bound and the AIPW upper miss bound at a caller-supplied separation.  The interface does
  not compare the two separations, require the lower separation to be positive, or state an
  asymptotic rate conclusion.

These finite bounds are complementary to the asymptotic-normality development for DML estimators.
-/

module
public import Causalean.Estimation.MinimaxATE.Achievability.AIPWEstimator
public import Causalean.Estimation.MinimaxATE.VaryingCenterCase1.LowerBound

/-! # Finite-Sample AIPW Lower and Upper Bounds

This file combines the cell-varying minimax converse with the finite-sample AIPW upper bound.

The file first proves finite-sample facts for the fixed-center AIPW estimator: `aipw_mean_eq`
identifies its mean, `aipw_nMiss_le` turns a bias and variance bound into a miss-probability
bound, `aipw_inclass_bias_bound` supplies the uniform product-bias estimate over `InClass`, and
`aipw_minimaxMiss_le` lifts these bounds to the minimax miss probability.  It then defines
`FiniteSampleTwoThresholdBounds` and assembles the two finite-sample inequalities in
`aipw_finiteSample_twoThreshold_bounds`. No comparison between the lower and upper separation,
positivity of the lower separation, or asymptotic rate claim is included. -/

@[expose] public section

namespace Causalean.Estimation.MinimaxATE

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

variable {C : Type*} [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C] [Nonempty C]

/-- The **mean** of the AIPW estimator equals the single-observation population mean of the
score (mean of an i.i.d. average), for `n > 0`. -/
theorem aipw_mean_eq {m : C → ℝ} {g : Bool → C → ℝ} (hv : ValidDGP m g)
    (mhat : C → ℝ) (ghat : Bool → C → ℝ) {n : ℕ} (hn : 0 < n) :
    ∫ sample, estAIPW mhat ghat n sample ∂(productLaw hv n)
      = ∑ z : Obs C, obsReal m g z * aipwScoreFin mhat ghat z := by
  have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hper : ∀ i : Fin n,
      ∫ sample, aipwScoreFin mhat ghat (sample i) ∂(productLaw hv n)
        = ∑ z : Obs C, obsReal m g z * aipwScoreFin mhat ghat z := by
    intro i
    have hmap : (productLaw hv n).map (fun s : Fin n → Obs C => s i) = obsLaw hv := by
      rw [productLaw]; exact (measurePreserving_eval (fun _ : Fin n => obsLaw hv) i).map_eq
    rw [← aipw_pop_mean hv mhat ghat,
      ← integral_map (φ := fun s : Fin n → Obs C => s i) (measurable_pi_apply i).aemeasurable
        (measurable_of_finite _).aestronglyMeasurable, hmap]
  unfold estAIPW
  rw [integral_const_mul, integral_finset_sum _ (fun i _ => Integrable.of_finite)]
  simp_rw [hper]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

/-- **Per-DGP Chebyshev miss bound.**  If the plug-in bias is `≤ b` and the variance is `≤ V`,
then for any separation `s > b` the miss probability is `≤ V / (s − b)²`. -/
theorem aipw_nMiss_le {m : C → ℝ} {g : Bool → C → ℝ} (hv : ValidDGP m g)
    (mhat : C → ℝ) (ghat : Bool → C → ℝ) {n : ℕ} (hn : 0 < n)
    {b V s : ℝ}
    (hbias : |(∑ z : Obs C, obsReal m g z * aipwScoreFin mhat ghat z) - ate g| ≤ b)
    (hvar : variance (estAIPW mhat ghat n) (productLaw hv n) ≤ V) (hsb : b < s) :
    nMiss hv n (estAIPW mhat ghat n) s ≤ V / (s - b) ^ 2 := by
  have hsub0 : 0 < s - b := by linarith
  set μ' := productLaw hv n with hμ'
  set X := estAIPW mhat ghat n with hX
  have hmem : MemLp X 2 μ' :=
    ⟨(measurable_of_finite _).aestronglyMeasurable, eLpNorm_lt_top_of_finite⟩
  have hmean : ∫ a, X a ∂μ' = ∑ z : Obs C, obsReal m g z * aipwScoreFin mhat ghat z :=
    aipw_mean_eq hv mhat ghat hn
  have hEbias : |(∫ a, X a ∂μ') - ate g| ≤ b := by rw [hmean]; exact hbias
  have hsubset : {sample | s ≤ |X sample - ate g|}
      ⊆ {sample | s - b ≤ |X sample - ∫ a, X a ∂μ'|} := by
    intro sample hsample
    simp only [Set.mem_setOf_eq] at hsample ⊢
    have htri : |X sample - ate g| ≤ |X sample - ∫ a, X a ∂μ'| + |(∫ a, X a ∂μ') - ate g| :=
      abs_sub_le _ _ _
    linarith
  have hvar0 : 0 ≤ variance X μ' := variance_nonneg _ _
  calc nMiss hv n X s = μ'.real {sample | s ≤ |X sample - ate g|} := rfl
    _ ≤ μ'.real {sample | s - b ≤ |X sample - ∫ a, X a ∂μ'|} :=
        measureReal_mono hsubset (measure_ne_top _ _)
    _ ≤ variance X μ' / (s - b) ^ 2 := by
        rw [Measure.real]
        refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top
          (meas_ge_le_variance_div_sq hmem hsub0)).trans ?_
        rw [ENNReal.toReal_ofReal (by positivity)]
    _ ≤ V / (s - b) ^ 2 := by gcongr

omit [MeasurableSpace C] [MeasurableSingletonClass C] in
/-- **In-class bias bound.** For [a positive overlap threshold ε](hyp:hε) such that [the fixed
propensity estimate `mhat` stays at least ε away from both `0` and `1` at every covariate
value](hyp:hco), and for [any data-generating process `(m, g)` lying in the structure-agnostic
nuisance class around the fixed estimates `(mhat, ghat)` with error budgets `εg`,
`εm`](hyp:hin), [the plug-in bias of the fixed-center AIPW estimator's population score is at
most `ε⁻¹·2·√εg·√εm`](goal). -/
theorem aipw_inclass_bias_bound {mhat : C → ℝ} {ghat : Bool → C → ℝ} {εg εm : ℝ}
    {ε : ℝ} (hε : 0 < ε)
    (hco : ∀ x, ε ≤ mhat x ∧ ε ≤ 1 - mhat x)
    {m : C → ℝ} {g : Bool → C → ℝ} (hin : InClass mhat ghat εg εm m g) :
    |(∑ z : Obs C, obsReal m g z * aipwScoreFin mhat ghat z) - ate g|
      ≤ ε⁻¹ * (2 * Real.sqrt εg * Real.sqrt εm) := by
  refine (aipw_bias_bound mhat ghat hε hco).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ ε⁻¹)
  have hg1 : Real.sqrt (l2sq (g true) (ghat true)) ≤ Real.sqrt εg :=
    Real.sqrt_le_sqrt (hin.err_g true)
  have hg0 : Real.sqrt (l2sq (g false) (ghat false)) ≤ Real.sqrt εg :=
    Real.sqrt_le_sqrt (hin.err_g false)
  have hmm : Real.sqrt (l2sq m mhat) ≤ Real.sqrt εm := Real.sqrt_le_sqrt hin.err_m
  calc (Real.sqrt (l2sq (g true) (ghat true)) + Real.sqrt (l2sq (g false) (ghat false)))
          * Real.sqrt (l2sq m mhat)
      ≤ (2 * Real.sqrt εg) * Real.sqrt εm :=
        mul_le_mul (by linarith) hmm (Real.sqrt_nonneg _) (by positivity)
    _ = 2 * Real.sqrt εg * Real.sqrt εm := by ring

/-- **Worst-case (minimax) miss bound for AIPW.** Suppose [the fixed nuisance estimates
`(mhat, ghat)` are themselves valid](hyp:hghat), for [a positive overlap threshold ε](hyp:hε)
such that [`mhat` stays at least ε away from `0` and `1` everywhere](hyp:hco), [nonnegative
error budgets εg, εm](hyp:hεg,hεm), [a positive sample size n](hyp:hn), and [a separation s
exceeding the uniform bias bound `b = ε⁻¹·2·√εg·√εm`](hyp:hsb). Then [the worst-case-over-class
miss probability of the fixed-center AIPW estimator at separation s is at most
`((1+2/ε)²/n)/(s−b)²`](goal). -/
theorem aipw_minimaxMiss_le {mhat : C → ℝ} {ghat : Bool → C → ℝ} {εg εm : ℝ}
    (hghat : ValidDGP mhat ghat) {ε : ℝ} (hε : 0 < ε)
    (hco : ∀ x, ε ≤ mhat x ∧ ε ≤ 1 - mhat x) (hεg : 0 ≤ εg) (hεm : 0 ≤ εm)
    {n : ℕ} (hn : 0 < n) {s : ℝ} (hsb : ε⁻¹ * (2 * Real.sqrt εg * Real.sqrt εm) < s) :
    minimaxMiss mhat ghat εg εm n (estAIPW mhat ghat n) s
      ≤ ((1 + 2 / ε) ^ 2 / n) / (s - ε⁻¹ * (2 * Real.sqrt εg * Real.sqrt εm)) ^ 2 := by
  haveI : Nonempty (InClassDGP mhat ghat εg εm) :=
    ⟨⟨(mhat, ghat), { valid := hghat
                      err_g := fun d => by rw [l2sq_self]; exact hεg
                      err_m := by rw [l2sq_self]; exact hεm }⟩⟩
  refine ciSup_le (fun p => ?_)
  exact aipw_nMiss_le p.2.valid mhat ghat hn
    (aipw_inclass_bias_bound hε hco p.2)
    (aipw_var_bound p.2.valid mhat ghat hghat hε hco n) hsb

/-- For [fixed nuisance centers](hyp:mhat,ghat), [error budgets](hyp:εg,εm), and [a sample
size](hyp:n), the finite-sample two-threshold bounds package a lower miss bound for every
measurable estimator at one separation and an upper miss bound for one estimator at another.
They do not assert that the separations are positive, ordered, or comparable in rate. -/
structure FiniteSampleTwoThresholdBounds
    (mhat : C → ℝ) (ghat : Bool → C → ℝ) (εg εm : ℝ) (n : ℕ) where
  /-- The estimator appearing in the upper bound. -/
  estimator : (Fin n → Obs C) → ℝ
  /-- Separation used by the lower bound. -/
  sepLower : ℝ
  /-- Lower bound on every estimator's worst-case miss at `sepLower`. -/
  probLower : ℝ
  converse : ∀ est : (Fin n → Obs C) → ℝ, Measurable est →
    probLower ≤ minimaxMiss mhat ghat εg εm n est sepLower
  /-- Separation used by the upper bound. -/
  sepUpper : ℝ
  /-- Upper bound on `estimator`'s worst-case miss at `sepUpper`. -/
  missUpper : ℝ
  achievability : minimaxMiss mhat ghat εg εm n estimator sepUpper ≤ missUpper

variable {K : ℕ}

/-- For [a cell-varying construction over a nonzero finite number of paired covariate
cells](hyp:K,P), [a positive sample size](hyp:hn), and [nonnegative outcome-regression and
propensity-error budgets](hyp:εg,εm,hεg,hεm), suppose [for every pair $j$, the squared
propensity perturbation $(m_{0j}\beta/g_{1j})^2$ is at most $\varepsilon_m$](hyp:hm), [for
every pair $j$, the squared treated-arm outcome-regression perturbation
$g_{1j}^2(\alpha+\beta)^2/(g_{1j}-\beta)^2$ is at most $\varepsilon_g$](hyp:hg), [the
normalized overlap coefficients satisfy $\sum_j \Gamma_j/K\leq 1$](hyp:hΓsum), and [their
normalized squared sum satisfies $(n^2/2)\sum_j(\Gamma_j/K)^2\leq\log 2$](hyp:hreg).
For [a positive overlap constant](hyp:ε,hε) such that [the fitted propensity is between
$\varepsilon$ and $1-\varepsilon$ in every covariate cell](hyp:hco), and [a separation
$s$ strictly larger than $\varepsilon^{-1}2\sqrt{\varepsilon_g}\sqrt{\varepsilon_m}$](hyp:s,hsb),
[the finite-sample two-threshold bounds](goal) specify the fixed-center augmented
inverse-probability-weighted estimator, its upper miss-probability bound at $s$, and the
construction-induced lower miss-probability bound for every measurable estimator.

The lower separation is the construction's gap divided by two, and its miss lower bound is
`1/4`. The upper separation is the caller-supplied `s`, with the displayed Chebyshev upper bound.
This declaration does not require a positive lower separation, relate the two separations, or
prove that either is of order `√(εg·εm)`; those facts would require additional nondegeneracy and
comparison hypotheses. -/
noncomputable def aipw_finiteSample_twoThreshold_bounds (P : VarConstr K) [NeZero K] {n : ℕ}
    (hn : 0 < n) {εg εm : ℝ}
    (hm : ∀ j, (P.m₀ j * (P.β / P.g₁ j)) ^ 2 ≤ εm)
    (hg : ∀ j, P.g₁ j ^ 2 * (P.α + P.β) ^ 2 / (P.g₁ j - P.β) ^ 2 ≤ εg)
    (hεg : 0 ≤ εg) (hεm : 0 ≤ εm)
    (hΓsum : ∑ j, P.ΓV j / (K : ℝ) ≤ 1)
    (hreg : (n : ℝ) ^ 2 / 2 * ∑ j, (P.ΓV j / (K : ℝ)) ^ 2 ≤ Real.log 2)
    {ε : ℝ} (hε : 0 < ε)
    (hco : ∀ x, ε ≤ P.mhatV x ∧ ε ≤ 1 - P.mhatV x)
    {s : ℝ} (hsb : ε⁻¹ * (2 * Real.sqrt εg * Real.sqrt εm) < s) :
    FiniteSampleTwoThresholdBounds P.mhatV P.ghatV εg εm n where
  estimator := estAIPW P.mhatV P.ghatV n
  sepLower := (Fintype.card (Fin K × Bool) : ℝ)⁻¹ * (2 * P.β * (P.α + P.β))
        * (∑ j : Fin K, P.g₁ j / (P.g₁ j ^ 2 - P.β ^ 2)) / 2
  probLower := 1 / 4
  converse := fun _est hest =>
    P.minimax_lower_bound_var hm hg hεg hεm hΓsum hreg hest
  sepUpper := s
  missUpper := ((1 + 2 / ε) ^ 2 / n) / (s - ε⁻¹ * (2 * Real.sqrt εg * Real.sqrt εm)) ^ 2
  achievability :=
    aipw_minimaxMiss_le P.validDGP_hatV hε hco hεg hεm hn hsb

end Causalean.Estimation.MinimaxATE
