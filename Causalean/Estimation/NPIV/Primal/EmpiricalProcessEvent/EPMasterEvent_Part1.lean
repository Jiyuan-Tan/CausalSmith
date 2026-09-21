/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Estimation.NPIV.Primal.EmpiricalProcessEvent.LocalizedEvents

/-! # Deterministic comparisons for the empirical-process master event

This first implementation part relates closedness witnesses to population
weak norms and compares population regularized objectives with fold-A
empirical objectives.  These deterministic inequalities feed the localized
event assembly in the second part.
-/

public section

namespace Causalean
namespace Estimation
namespace NPIV
namespace Primal

open MeasureTheory Causalean.Stat Causalean.Stat.Concentration

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## EP inequality and centred-regulariser bound (explicit-rate form)

The two helpers below are the post-substitution forms of two displays in
the proof sketch of `thm:est-trae-rate-theorem`
(`doc/basic_concepts/po/estimation/trae_inverse_problems.tex`):

* `ep_inequality_from_localized` — proof-sketch line 308: the EP step
  controls the population weak-norm excess via the **empirical**
  regulariser difference `λ(‖h*‖²_{A(n)} − ‖ĥ‖²_{A(n)})`, with the
  regulariser term carried with coefficient `1` (it comes for free from
  the empirical sup-min optimality of `ĥ_n`).

* `centred_regulariser_bound_from_localized` — proof-sketch line 345:
  the centred (empirical-vs-population) regulariser gap
  `λ((‖h*‖²_{A(n)} − ‖ĥ‖²_{A(n)}) − (‖h*‖² − ‖ĥ‖²))` is controlled by
  the localized rate.

Both displays use the **fold-A empirical norm**
`‖h‖²_{A(n)} = (split.n₁ n)⁻¹ ∑_{i ∈ foldA n} h(X_i)²`, matching
`is_estimator.opt`.  All bounds are stated at the fold-A sample size
`split.n₁ n`; the bundles passed in are at that size, so
`criticalRadius (regime.bundle_*.regime.ψ (split.n₁ n))` is the per-fold
critical radius.

The hypothesis `1 ≤ split.n₁ n` excludes the degenerate case of an empty
fold (where `(0:ℝ)⁻¹ = 0` and the bound is vacuous but doesn't reflect
the inequality of interest).  By `split.grow` this hypothesis holds for
all sufficiently large `n`. -/
/-- Closedness witnesses attain the population adversarial value.  Local
private copy used here to avoid importing `EPPerN.lean`, which depends on
this master event. -/
lemma population_inner_eq_closedness_witness
    {S : OperatorSystem Ω μ} {TC : TRAEClasses S}
    [IsProbabilityMeasure μ]
    {h : S.𝒳 → ℝ} (hh : h ∈ TC.H)
    {f : S.𝒵 → ℝ} (hf : f ∈ TC.F)
    (hcl :
      S.T (S.hL2 S.h₀_mem - S.hL2 (TC.H_subset hh))
        = S.qL2 (TC.F_subset hf)) :
    2 * (∫ ω, S.m (S.W ω) f ∂μ)
        - 2 * (∫ ω, h (S.xOf (S.W ω)) * f (S.zOf (S.W ω)) ∂μ)
        - ∫ ω, (f (S.zOf (S.W ω))) ^ 2 ∂μ
      = (S.weakNorm
          (S.hL2 (TC.H_subset hh) - S.hL2 S.h₀_mem)) ^ 2 := by
  haveI := S.isFiniteMeasure
  haveI := S.Qbar_L2_hasProj
  have h_inner_int :
      inner ℝ (S.T (S.hL2 S.h₀_mem - S.hL2 (TC.H_subset hh)))
              (S.qL2 (TC.F_subset hf))
        = ∫ ω, (S.h₀ (S.xOf (S.W ω)) - h (S.xOf (S.W ω))) *
                f (S.zOf (S.W ω)) ∂μ :=
    S.T_inner_eq_integral S.h₀_mem (TC.H_subset hh) (TC.F_subset hf)
  have h_moment :
      ∫ ω, S.m (S.W ω) f ∂μ
        = ∫ ω, S.h₀ (S.xOf (S.W ω)) * f (S.zOf (S.W ω)) ∂μ :=
    S.primal_moment f (TC.F_subset hf)
  have hh₀f_int : Integrable
      (fun ω => S.h₀ (S.xOf (S.W ω)) * f (S.zOf (S.W ω))) μ := by
    have := S.integrable_qh S.h₀ S.h₀_mem f (TC.F_subset hf)
    simpa [mul_comm] using this
  have hhf_int : Integrable
      (fun ω => h (S.xOf (S.W ω)) * f (S.zOf (S.W ω))) μ := by
    have := S.integrable_qh h (TC.H_subset hh) f (TC.F_subset hf)
    simpa [mul_comm] using this
  have h_int_diff :
      ∫ ω, (S.h₀ (S.xOf (S.W ω)) - h (S.xOf (S.W ω))) *
              f (S.zOf (S.W ω)) ∂μ
        = (∫ ω, S.h₀ (S.xOf (S.W ω)) * f (S.zOf (S.W ω)) ∂μ)
            - ∫ ω, h (S.xOf (S.W ω)) * f (S.zOf (S.W ω)) ∂μ := by
    have : (fun ω => (S.h₀ (S.xOf (S.W ω)) - h (S.xOf (S.W ω))) *
                      f (S.zOf (S.W ω)))
              = fun ω => S.h₀ (S.xOf (S.W ω)) * f (S.zOf (S.W ω))
                          - h (S.xOf (S.W ω)) * f (S.zOf (S.W ω)) := by
      funext ω; ring
    rw [this]
    exact integral_sub hh₀f_int hhf_int
  have h_diff_eq_inner :
      (∫ ω, S.m (S.W ω) f ∂μ)
          - ∫ ω, h (S.xOf (S.W ω)) * f (S.zOf (S.W ω)) ∂μ
        = inner ℝ (S.T (S.hL2 S.h₀_mem - S.hL2 (TC.H_subset hh)))
                  (S.qL2 (TC.F_subset hf)) := by
    rw [h_moment, h_inner_int, h_int_diff]
  have h_qL2_self :
      inner ℝ (S.qL2 (TC.F_subset hf)) (S.qL2 (TC.F_subset hf))
        = ∫ ω, (f (S.zOf (S.W ω))) ^ 2 ∂μ := by
    change inner ℝ
      ((S.qL2 (TC.F_subset hf) : S.InstrumentL2) : Lp ℝ 2 μ)
      ((S.qL2 (TC.F_subset hf) : S.InstrumentL2) : Lp ℝ 2 μ) = _
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [(S.toQbarL2 f (TC.F_subset hf)).coeFn_toLp]
      with ω hω
    simp [OperatorSystem.qL2, hω, pow_two]
  have h_diff_eq_int_fsq :
      (∫ ω, S.m (S.W ω) f ∂μ)
          - ∫ ω, h (S.xOf (S.W ω)) * f (S.zOf (S.W ω)) ∂μ
        = ∫ ω, (f (S.zOf (S.W ω))) ^ 2 ∂μ := by
    rw [h_diff_eq_inner, hcl, h_qL2_self]
  have h_T_neg :
      S.T (S.hL2 (TC.H_subset hh) - S.hL2 S.h₀_mem)
        = - S.qL2 (TC.F_subset hf) := by
    rw [S.T_sub]
    have hcl' :
        S.T (S.hL2 S.h₀_mem) - S.T (S.hL2 (TC.H_subset hh))
          = S.qL2 (TC.F_subset hf) := by
      rw [← S.T_sub]; exact hcl
    rw [← hcl']
    abel
  have h_weak_eq_intf :
      (S.weakNorm (S.hL2 (TC.H_subset hh) - S.hL2 S.h₀_mem)) ^ 2
        = ∫ ω, (f (S.zOf (S.W ω))) ^ 2 ∂μ := by
    rw [OperatorSystem.weakNorm, h_T_neg, norm_neg]
    have : ‖S.qL2 (TC.F_subset hf)‖ ^ 2
            = inner ℝ (S.qL2 (TC.F_subset hf))
                      (S.qL2 (TC.F_subset hf)) := by
      rw [real_inner_self_eq_norm_sq]
    rw [this, h_qL2_self]
  rw [h_weak_eq_intf]
  linarith [h_diff_eq_int_fsq]

/-- Population adversarial inner objectives are bounded by the weak residual
norm squared.  This is the deterministic inequality
`2⟨a,q⟩ - ‖q‖² ≤ ‖a‖²`, written in the NPIV integral notation. -/
lemma population_inner_le_weak
    {S : OperatorSystem Ω μ} {TC : TRAEClasses S}
    [IsProbabilityMeasure μ]
    {h : S.𝒳 → ℝ} (hh : h ∈ TC.H)
    {f : S.𝒵 → ℝ} (hf : f ∈ TC.F) :
    2 * (∫ ω, S.m (S.W ω) f ∂μ)
        - 2 * (∫ ω, h (S.xOf (S.W ω)) * f (S.zOf (S.W ω)) ∂μ)
        - ∫ ω, (f (S.zOf (S.W ω))) ^ 2 ∂μ
      ≤ (S.weakNorm
          (S.hL2 (TC.H_subset hh) - S.hL2 S.h₀_mem)) ^ 2 := by
  haveI := S.isFiniteMeasure
  haveI := S.Qbar_L2_hasProj
  let a := S.T (S.hL2 S.h₀_mem - S.hL2 (TC.H_subset hh))
  let q := S.qL2 (TC.F_subset hf)
  have h_inner_int :
      inner ℝ a q
        = ∫ ω, (S.h₀ (S.xOf (S.W ω)) - h (S.xOf (S.W ω))) *
                f (S.zOf (S.W ω)) ∂μ := by
    simpa [a, q] using
      S.T_inner_eq_integral S.h₀_mem (TC.H_subset hh) (TC.F_subset hf)
  have h_moment :
      ∫ ω, S.m (S.W ω) f ∂μ
        = ∫ ω, S.h₀ (S.xOf (S.W ω)) * f (S.zOf (S.W ω)) ∂μ :=
    S.primal_moment f (TC.F_subset hf)
  have hh₀f_int : Integrable
      (fun ω => S.h₀ (S.xOf (S.W ω)) * f (S.zOf (S.W ω))) μ := by
    have := S.integrable_qh S.h₀ S.h₀_mem f (TC.F_subset hf)
    simpa [mul_comm] using this
  have hhf_int : Integrable
      (fun ω => h (S.xOf (S.W ω)) * f (S.zOf (S.W ω))) μ := by
    have := S.integrable_qh h (TC.H_subset hh) f (TC.F_subset hf)
    simpa [mul_comm] using this
  have h_int_diff :
      ∫ ω, (S.h₀ (S.xOf (S.W ω)) - h (S.xOf (S.W ω))) *
              f (S.zOf (S.W ω)) ∂μ
        = (∫ ω, S.h₀ (S.xOf (S.W ω)) * f (S.zOf (S.W ω)) ∂μ)
            - ∫ ω, h (S.xOf (S.W ω)) * f (S.zOf (S.W ω)) ∂μ := by
    have : (fun ω => (S.h₀ (S.xOf (S.W ω)) - h (S.xOf (S.W ω))) *
                      f (S.zOf (S.W ω)))
              = fun ω => S.h₀ (S.xOf (S.W ω)) * f (S.zOf (S.W ω))
                          - h (S.xOf (S.W ω)) * f (S.zOf (S.W ω)) := by
      funext ω; ring
    rw [this]
    exact integral_sub hh₀f_int hhf_int
  have h_diff_eq_inner :
      (∫ ω, S.m (S.W ω) f ∂μ)
          - ∫ ω, h (S.xOf (S.W ω)) * f (S.zOf (S.W ω)) ∂μ
        = inner ℝ a q := by
    rw [h_moment, h_inner_int, h_int_diff]
  have h_qL2_self :
      inner ℝ q q = ∫ ω, (f (S.zOf (S.W ω))) ^ 2 ∂μ := by
    change inner ℝ (q : Lp ℝ 2 μ) (q : Lp ℝ 2 μ) = _
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [(S.toQbarL2 f (TC.F_subset hf)).coeFn_toLp]
      with ω hω
    simp [q, OperatorSystem.qL2, hω, pow_two]
  have hweak :
      (S.weakNorm (S.hL2 (TC.H_subset hh) - S.hL2 S.h₀_mem)) ^ 2
        = ‖a‖ ^ 2 := by
    rw [OperatorSystem.weakNorm, S.T_sub]
    have hneg :
        S.T (S.hL2 (TC.H_subset hh)) - S.T (S.hL2 S.h₀_mem) = -a := by
      dsimp [a]
      rw [S.T_sub]
      abel
    rw [hneg, norm_neg]
  have hhilbert : 2 * inner ℝ a q - inner ℝ q q ≤ ‖a‖ ^ 2 := by
    have hsq : 0 ≤ ‖a - q‖ ^ 2 := sq_nonneg ‖a - q‖
    rw [norm_sub_sq_real] at hsq
    have hqnorm : inner ℝ q q = ‖q‖ ^ 2 := real_inner_self_eq_norm_sq q
    nlinarith
  rw [hweak]
  nlinarith [h_diff_eq_inner, h_qL2_self, hhilbert]

private lemma population_inner_eq_closedness_inner
    {S : OperatorSystem Ω μ} {TC : TRAEClasses S}
    [IsProbabilityMeasure μ]
    {h : S.𝒳 → ℝ} (hh : h ∈ TC.H)
    {f_closed : S.𝒵 → ℝ} (hf_closed : f_closed ∈ TC.F)
    {f : S.𝒵 → ℝ} (hf : f ∈ TC.F)
    (hcl :
      S.T (S.hL2 S.h₀_mem - S.hL2 (TC.H_subset hh))
        = S.qL2 (TC.F_subset hf_closed)) :
    2 * (∫ ω, S.m (S.W ω) f ∂μ)
        - 2 * (∫ ω, h (S.xOf (S.W ω)) * f (S.zOf (S.W ω)) ∂μ)
        - ∫ ω, (f (S.zOf (S.W ω))) ^ 2 ∂μ
      =
        2 * inner ℝ (S.qL2 (TC.F_subset hf_closed))
            (S.qL2 (TC.F_subset hf))
          - inner ℝ (S.qL2 (TC.F_subset hf))
              (S.qL2 (TC.F_subset hf)) := by
  haveI := S.isFiniteMeasure
  haveI := S.Qbar_L2_hasProj
  let q_closed := S.qL2 (TC.F_subset hf_closed)
  let q := S.qL2 (TC.F_subset hf)
  have h_inner_int :
      inner ℝ q_closed q
        = ∫ ω, (S.h₀ (S.xOf (S.W ω)) - h (S.xOf (S.W ω))) *
                f (S.zOf (S.W ω)) ∂μ := by
    dsimp [q_closed, q]
    rw [← hcl]
    simpa using
      S.T_inner_eq_integral S.h₀_mem (TC.H_subset hh) (TC.F_subset hf)
  have h_moment :
      ∫ ω, S.m (S.W ω) f ∂μ
        = ∫ ω, S.h₀ (S.xOf (S.W ω)) * f (S.zOf (S.W ω)) ∂μ :=
    S.primal_moment f (TC.F_subset hf)
  have hh₀f_int : Integrable
      (fun ω => S.h₀ (S.xOf (S.W ω)) * f (S.zOf (S.W ω))) μ := by
    have := S.integrable_qh S.h₀ S.h₀_mem f (TC.F_subset hf)
    simpa [mul_comm] using this
  have hhf_int : Integrable
      (fun ω => h (S.xOf (S.W ω)) * f (S.zOf (S.W ω))) μ := by
    have := S.integrable_qh h (TC.H_subset hh) f (TC.F_subset hf)
    simpa [mul_comm] using this
  have h_int_diff :
      ∫ ω, (S.h₀ (S.xOf (S.W ω)) - h (S.xOf (S.W ω))) *
              f (S.zOf (S.W ω)) ∂μ
        = (∫ ω, S.h₀ (S.xOf (S.W ω)) * f (S.zOf (S.W ω)) ∂μ)
            - ∫ ω, h (S.xOf (S.W ω)) * f (S.zOf (S.W ω)) ∂μ := by
    have : (fun ω => (S.h₀ (S.xOf (S.W ω)) - h (S.xOf (S.W ω))) *
                      f (S.zOf (S.W ω)))
              = fun ω => S.h₀ (S.xOf (S.W ω)) * f (S.zOf (S.W ω))
                          - h (S.xOf (S.W ω)) * f (S.zOf (S.W ω)) := by
      funext ω; ring
    rw [this]
    exact integral_sub hh₀f_int hhf_int
  have h_diff_eq_inner :
      (∫ ω, S.m (S.W ω) f ∂μ)
          - ∫ ω, h (S.xOf (S.W ω)) * f (S.zOf (S.W ω)) ∂μ
        = inner ℝ q_closed q := by
    rw [h_moment, h_inner_int, h_int_diff]
  have h_qL2_self :
      inner ℝ q q = ∫ ω, (f (S.zOf (S.W ω))) ^ 2 ∂μ := by
    change inner ℝ (q : Lp ℝ 2 μ) (q : Lp ℝ 2 μ) = _
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [(S.toQbarL2 f (TC.F_subset hf)).coeFn_toLp]
      with ω hω
    simp [q, OperatorSystem.qL2, hω, pow_two]
  nlinarith [h_diff_eq_inner, h_qL2_self]

/-- Population curvature at the closedness critic.  For a fixed candidate
`h`, the closedness witness `f_closed` is the population maximizer of the
quadratic adversarial criterion, and the drop at any critic `f` is exactly
the squared `L²` critic gap.

This is the Lean form of the second-order identity used in the proof of
Lemma 11 in Bennett--Kallus--Mao--Newey--Syrgkanis--Uehara. -/
lemma population_closedness_critic_gap_eq
    {S : OperatorSystem Ω μ} {TC : TRAEClasses S}
    [IsProbabilityMeasure μ]
    {h : S.𝒳 → ℝ} (hh : h ∈ TC.H)
    {f_closed : S.𝒵 → ℝ} (hf_closed : f_closed ∈ TC.F)
    {f : S.𝒵 → ℝ} (hf : f ∈ TC.F)
    (hcl :
      S.T (S.hL2 S.h₀_mem - S.hL2 (TC.H_subset hh))
        = S.qL2 (TC.F_subset hf_closed)) :
    (2 * (∫ ω, S.m (S.W ω) f_closed ∂μ)
        - 2 * (∫ ω, h (S.xOf (S.W ω)) *
            f_closed (S.zOf (S.W ω)) ∂μ)
        - ∫ ω, (f_closed (S.zOf (S.W ω))) ^ 2 ∂μ)
      - (2 * (∫ ω, S.m (S.W ω) f ∂μ)
        - 2 * (∫ ω, h (S.xOf (S.W ω)) *
            f (S.zOf (S.W ω)) ∂μ)
        - ∫ ω, (f (S.zOf (S.W ω))) ^ 2 ∂μ)
      =
        ‖S.qL2 (TC.F_subset hf_closed) - S.qL2 (TC.F_subset hf)‖ ^ 2 := by
  let qc := S.qL2 (TC.F_subset hf_closed)
  let q := S.qL2 (TC.F_subset hf)
  have hclosed :=
    population_inner_eq_closedness_inner
      (S := S) (TC := TC) (hh := hh)
      (hf_closed := hf_closed) (hf := hf_closed) hcl
  have hf_eq :=
    population_inner_eq_closedness_inner
      (S := S) (TC := TC) (hh := hh)
      (hf_closed := hf_closed) (hf := hf) hcl
  change _ = ‖qc - q‖ ^ 2
  rw [hclosed, hf_eq, norm_sub_sq_real]
  have hqc_self : inner ℝ qc qc = ‖qc‖ ^ 2 := real_inner_self_eq_norm_sq qc
  have hq_self : inner ℝ q q = ‖q‖ ^ 2 := real_inner_self_eq_norm_sq q
  nlinarith [hqc_self, hq_self]

/-- For [a probability space, an instrumental-variables operator system, its primal function
classes, an observed-data law, an independent sample, and a sample split](hyp:Ω,μ,S,TC,P_W,sample,split),
[a regularization level and candidate structural function](hyp:lambda,h), [membership of that
candidate in the structural class](hyp:hh), [a population closedness critic](hyp:f_closed),
[membership of that critic in the critic class](hyp:hf_closed), [an empirical critic](hyp:f_emp),
[membership of the empirical critic in the critic class](hyp:hf_emp), [a sample size, population
state, and nonnegative localization allowance](hyp:n,ω,R), [the closedness identity](hyp:hcl),
[empirical optimality of the empirical critic](hyp:hopt), and [a bound on the population-to-
empirical objective discrepancy](hyp:hdev), [the empirical critic lies within squared
population distance equal to the localization allowance of the closedness critic](goal).

Deterministic argmax-localization bridge.  If `f_emp` empirically
beats the closedness witness for the same candidate `h`, and the
population-vs-empirical loss difference is controlled by `R`, then the
empirical critic is within squared `L²` distance `R` of the closedness
witness.

This is the formal bridge missing from a direct use of
`supObjective_attained`: the arbitrary empirical maximizer becomes
localized by population curvature plus empirical optimality. -/
lemma empirical_critic_argmax_localized
    {S : OperatorSystem Ω μ} {TC : TRAEClasses S}
    {P_W : Measure S.𝒲}
    {sample : IIDSample Ω S.𝒲 μ P_W}
    {split : OneShotSplit sample}
    [IsProbabilityMeasure μ]
    {lambda : ℝ} {h : S.𝒳 → ℝ} (hh : h ∈ TC.H)
    {f_closed : S.𝒵 → ℝ} (hf_closed : f_closed ∈ TC.F)
    {f_emp : S.𝒵 → ℝ} (hf_emp : f_emp ∈ TC.F)
    {n : ℕ} {ω : Ω} {R : ℝ}
    (hcl :
      S.T (S.hL2 S.h₀_mem - S.hL2 (TC.H_subset hh))
        = S.qL2 (TC.F_subset hf_closed))
    (hopt :
      innerObjective S sample split lambda h f_closed n ω
        ≤ innerObjective S sample split lambda h f_emp n ω)
    (hdev :
      (2 * (∫ ω', S.m (S.W ω') f_closed ∂μ)
          - 2 * (∫ ω', h (S.xOf (S.W ω')) *
              f_closed (S.zOf (S.W ω')) ∂μ)
          - ∫ ω', (f_closed (S.zOf (S.W ω'))) ^ 2 ∂μ)
        - (2 * (∫ ω', S.m (S.W ω') f_emp ∂μ)
          - 2 * (∫ ω', h (S.xOf (S.W ω')) *
              f_emp (S.zOf (S.W ω')) ∂μ)
          - ∫ ω', (f_emp (S.zOf (S.W ω'))) ^ 2 ∂μ)
        ≤ innerObjective S sample split lambda h f_closed n ω
            - innerObjective S sample split lambda h f_emp n ω
          + R) :
      ‖S.qL2 (TC.F_subset hf_closed) - S.qL2 (TC.F_subset hf_emp)‖ ^ 2
        ≤ R := by
  have hgap :=
    population_closedness_critic_gap_eq
      (S := S) (TC := TC) (hh := hh)
      (hf_closed := hf_closed) (hf := hf_emp) hcl
  rw [← hgap]
  linarith [hdev, hopt]

/-! ### Objective-level master event (raw localized gap)

`ep_master_event_from_localized` is the Ω-side concentration ingredient
consumed by `ep_inequality_from_localized` in `EPPerN.lean`.  Its
conclusion is the raw localized objective modulus:

    population_excess(ĥ_n, h*_λ) ≤
      empirical_sup_excess(ĥ_n, h*_λ) + localized_envelope.

This is deliberately not the final EP inequality: without the estimator
optimality hypothesis, the empirical sup-objective excess remains on
the RHS.  `EPPerN.lean` uses `is_estimator.opt` to remove exactly that
term.  This keeps the master event non-vacuous; the later discharge
step absorbs this explicit rate into the final TRAE population shape.

The proof intersects the three localized Ω-events for the `HF`, `mF`, and
`F` empirical-process pieces, then performs the deterministic bridge from
inner objectives to `supObjective` using the max-order fields carried by
`LocalizedRegimes`, followed by the all-`n` geometric union bound on Ω. -/

private lemma innerObjective_eq_fin_sum
    {S : OperatorSystem Ω μ}
    {P_W : Measure S.𝒲}
    {sample : IIDSample Ω S.𝒲 μ P_W}
    (split : OneShotSplit sample)
    (lambda : ℝ) (h : S.𝒳 → ℝ) (f : S.𝒵 → ℝ)
    (n : ℕ) (ω : Ω) :
    innerObjective S sample split lambda h f n ω
      = ((split.n₁ n : ℕ) : ℝ)⁻¹ *
          ∑ k : Fin (split.n₁ n),
            innerIntegrand S lambda h f (sample.Z (k : ℕ) ω) := by
  rw [innerObjective, OneShotSplit.foldA, Finset.card_range]
  rw [← Fin.sum_univ_eq_sum_range]

/-- Given [a nonparametric instrumental-variables system, sample split, regularization level,
candidate functions, sample size, observation, and three deviation bounds](hyp:Ω,μ,S,P_W,sample,split,lambda,h,f,n,ω,Rm,RHF,RF),
if [the empirical moment deviation is bounded](hyp:hmF), [the empirical cross-product deviation is
bounded](hyp:hHF), and [the empirical squared-instrument deviation is bounded](hyp:hF), then [the
population regularized objective is at most the empirical inner objective plus the stated combined
deviation](goal). -/
lemma population_regularized_le_innerObjective_add_deviation
    {S : OperatorSystem Ω μ}
    {P_W : Measure S.𝒲}
    {sample : IIDSample Ω S.𝒲 μ P_W}
    (split : OneShotSplit sample)
    (lambda : ℝ) (h : S.𝒳 → ℝ) (f : S.𝒵 → ℝ)
    (n : ℕ) (ω : Ω)
    {Rm RHF RF : ℝ}
    (hmF :
      |((split.n₁ n : ℕ) : ℝ)⁻¹ *
          ∑ k : Fin (split.n₁ n), S.m (sample.Z (k : ℕ) ω) f
        - ∫ ω', S.m (S.W ω') f ∂μ| ≤ Rm)
    (hHF :
      |((split.n₁ n : ℕ) : ℝ)⁻¹ *
          ∑ k : Fin (split.n₁ n),
            h (S.xOf (sample.Z (k : ℕ) ω)) *
              f (S.zOf (sample.Z (k : ℕ) ω))
        - ∫ ω',
            h (S.xOf (S.W ω')) * f (S.zOf (S.W ω')) ∂μ| ≤ RHF)
    (hF :
      |((split.n₁ n : ℕ) : ℝ)⁻¹ *
          ∑ k : Fin (split.n₁ n),
            (f (S.zOf (sample.Z (k : ℕ) ω))) ^ 2
        - ∫ ω', (f (S.zOf (S.W ω'))) ^ 2 ∂μ| ≤ RF) :
    2 * (∫ ω', S.m (S.W ω') f ∂μ)
        - 2 * (∫ ω',
            h (S.xOf (S.W ω')) * f (S.zOf (S.W ω')) ∂μ)
        - ∫ ω', (f (S.zOf (S.W ω'))) ^ 2 ∂μ
        + lambda *
            (((split.n₁ n : ℕ) : ℝ)⁻¹ * ∑ k : Fin (split.n₁ n),
              (h (S.xOf (sample.Z (k : ℕ) ω))) ^ 2)
      ≤ innerObjective S sample split lambda h f n ω
        + (2 * Rm + 2 * RHF + RF) := by
  let mEmp : ℝ :=
    ((split.n₁ n : ℕ) : ℝ)⁻¹ *
      ∑ k : Fin (split.n₁ n), S.m (sample.Z (k : ℕ) ω) f
  let mPop : ℝ := ∫ ω', S.m (S.W ω') f ∂μ
  let hfEmp : ℝ :=
    ((split.n₁ n : ℕ) : ℝ)⁻¹ *
      ∑ k : Fin (split.n₁ n),
        h (S.xOf (sample.Z (k : ℕ) ω)) *
          f (S.zOf (sample.Z (k : ℕ) ω))
  let hfPop : ℝ :=
    ∫ ω', h (S.xOf (S.W ω')) * f (S.zOf (S.W ω')) ∂μ
  let fEmp : ℝ :=
    ((split.n₁ n : ℕ) : ℝ)⁻¹ *
      ∑ k : Fin (split.n₁ n), (f (S.zOf (sample.Z (k : ℕ) ω))) ^ 2
  let fPop : ℝ := ∫ ω', (f (S.zOf (S.W ω'))) ^ 2 ∂μ
  let hReg : ℝ :=
    lambda *
      (((split.n₁ n : ℕ) : ℝ)⁻¹ * ∑ k : Fin (split.n₁ n),
        (h (S.xOf (sample.Z (k : ℕ) ω))) ^ 2)
  have hm_abs : -Rm ≤ mEmp - mPop ∧ mEmp - mPop ≤ Rm := by
    simpa [mEmp, mPop] using abs_le.mp hmF
  have hHF_abs : -RHF ≤ hfEmp - hfPop ∧ hfEmp - hfPop ≤ RHF := by
    simpa [hfEmp, hfPop] using abs_le.mp hHF
  have hF_abs : -RF ≤ fEmp - fPop ∧ fEmp - fPop ≤ RF := by
    simpa [fEmp, fPop] using abs_le.mp hF
  have hinner :
      innerObjective S sample split lambda h f n ω
        = 2 * mEmp - 2 * hfEmp - fEmp + hReg := by
    rw [innerObjective_eq_fin_sum]
    have hsum :
        (∑ k : Fin (split.n₁ n),
            innerIntegrand S lambda h f (sample.Z (k : ℕ) ω))
          =
            2 * (∑ k : Fin (split.n₁ n), S.m (sample.Z (k : ℕ) ω) f)
            - 2 * (∑ k : Fin (split.n₁ n),
                h (S.xOf (sample.Z (k : ℕ) ω)) *
                  f (S.zOf (sample.Z (k : ℕ) ω)))
            - (∑ k : Fin (split.n₁ n),
                (f (S.zOf (sample.Z (k : ℕ) ω))) ^ 2)
            + lambda * (∑ k : Fin (split.n₁ n),
                (h (S.xOf (sample.Z (k : ℕ) ω))) ^ 2) := by
      simp only [innerIntegrand, Finset.sum_add_distrib,
        Finset.sum_sub_distrib]
      abel_nf
      simp_rw [← Finset.mul_sum]
      rw [Finset.sum_add_distrib]
      rw [← Finset.smul_sum]
      abel_nf
      ring_nf
    rw [hsum]
    simp only [mEmp, hfEmp, fEmp, hReg]
    ring_nf
  rw [hinner]
  dsimp [mPop, hfPop, fPop, hReg]
  nlinarith [hm_abs.1, hm_abs.2, hHF_abs.1, hHF_abs.2,
    hF_abs.1, hF_abs.2]

/-- Given [a nonparametric instrumental-variables system, sample split, regularization level,
candidate functions, sample size, observation, and three deviation bounds](hyp:Ω,μ,S,P_W,sample,split,lambda,h,f,n,ω,Rm,RHF,RF),
if [the empirical moment deviation is bounded](hyp:hmF), [the empirical cross-product deviation is
bounded](hyp:hHF), and [the empirical squared-instrument deviation is bounded](hyp:hF), then [the
empirical inner objective is at most the population regularized objective plus the stated combined
deviation](goal). -/
lemma innerObjective_le_population_regularized_add_deviation
    {S : OperatorSystem Ω μ}
    {P_W : Measure S.𝒲}
    {sample : IIDSample Ω S.𝒲 μ P_W}
    (split : OneShotSplit sample)
    (lambda : ℝ) (h : S.𝒳 → ℝ) (f : S.𝒵 → ℝ)
    (n : ℕ) (ω : Ω)
    {Rm RHF RF : ℝ}
    (hmF :
      |((split.n₁ n : ℕ) : ℝ)⁻¹ *
          ∑ k : Fin (split.n₁ n), S.m (sample.Z (k : ℕ) ω) f
        - ∫ ω', S.m (S.W ω') f ∂μ| ≤ Rm)
    (hHF :
      |((split.n₁ n : ℕ) : ℝ)⁻¹ *
          ∑ k : Fin (split.n₁ n),
            h (S.xOf (sample.Z (k : ℕ) ω)) *
              f (S.zOf (sample.Z (k : ℕ) ω))
        - ∫ ω',
            h (S.xOf (S.W ω')) * f (S.zOf (S.W ω')) ∂μ| ≤ RHF)
    (hF :
      |((split.n₁ n : ℕ) : ℝ)⁻¹ *
          ∑ k : Fin (split.n₁ n),
            (f (S.zOf (sample.Z (k : ℕ) ω))) ^ 2
        - ∫ ω', (f (S.zOf (S.W ω'))) ^ 2 ∂μ| ≤ RF) :
    innerObjective S sample split lambda h f n ω
      ≤ 2 * (∫ ω', S.m (S.W ω') f ∂μ)
        - 2 * (∫ ω',
            h (S.xOf (S.W ω')) * f (S.zOf (S.W ω')) ∂μ)
        - ∫ ω', (f (S.zOf (S.W ω'))) ^ 2 ∂μ
        + lambda *
            (((split.n₁ n : ℕ) : ℝ)⁻¹ * ∑ k : Fin (split.n₁ n),
              (h (S.xOf (sample.Z (k : ℕ) ω))) ^ 2)
        + (2 * Rm + 2 * RHF + RF) := by
  let mEmp : ℝ :=
    ((split.n₁ n : ℕ) : ℝ)⁻¹ *
      ∑ k : Fin (split.n₁ n), S.m (sample.Z (k : ℕ) ω) f
  let mPop : ℝ := ∫ ω', S.m (S.W ω') f ∂μ
  let hfEmp : ℝ :=
    ((split.n₁ n : ℕ) : ℝ)⁻¹ *
      ∑ k : Fin (split.n₁ n),
        h (S.xOf (sample.Z (k : ℕ) ω)) *
          f (S.zOf (sample.Z (k : ℕ) ω))
  let hfPop : ℝ :=
    ∫ ω', h (S.xOf (S.W ω')) * f (S.zOf (S.W ω')) ∂μ
  let fEmp : ℝ :=
    ((split.n₁ n : ℕ) : ℝ)⁻¹ *
      ∑ k : Fin (split.n₁ n), (f (S.zOf (sample.Z (k : ℕ) ω))) ^ 2
  let fPop : ℝ := ∫ ω', (f (S.zOf (S.W ω'))) ^ 2 ∂μ
  let hReg : ℝ :=
    lambda *
      (((split.n₁ n : ℕ) : ℝ)⁻¹ * ∑ k : Fin (split.n₁ n),
        (h (S.xOf (sample.Z (k : ℕ) ω))) ^ 2)
  have hm_abs : -Rm ≤ mEmp - mPop ∧ mEmp - mPop ≤ Rm := by
    simpa [mEmp, mPop] using abs_le.mp hmF
  have hHF_abs : -RHF ≤ hfEmp - hfPop ∧ hfEmp - hfPop ≤ RHF := by
    simpa [hfEmp, hfPop] using abs_le.mp hHF
  have hF_abs : -RF ≤ fEmp - fPop ∧ fEmp - fPop ≤ RF := by
    simpa [fEmp, fPop] using abs_le.mp hF
  have hinner :
      innerObjective S sample split lambda h f n ω
        = 2 * mEmp - 2 * hfEmp - fEmp + hReg := by
    rw [innerObjective_eq_fin_sum]
    have hsum :
        (∑ k : Fin (split.n₁ n),
            innerIntegrand S lambda h f (sample.Z (k : ℕ) ω))
          =
            2 * (∑ k : Fin (split.n₁ n), S.m (sample.Z (k : ℕ) ω) f)
            - 2 * (∑ k : Fin (split.n₁ n),
                h (S.xOf (sample.Z (k : ℕ) ω)) *
                  f (S.zOf (sample.Z (k : ℕ) ω)))
            - (∑ k : Fin (split.n₁ n),
                (f (S.zOf (sample.Z (k : ℕ) ω))) ^ 2)
            + lambda * (∑ k : Fin (split.n₁ n),
                (h (S.xOf (sample.Z (k : ℕ) ω))) ^ 2) := by
      simp only [innerIntegrand, Finset.sum_add_distrib,
        Finset.sum_sub_distrib]
      abel_nf
      simp_rw [← Finset.mul_sum]
      rw [Finset.sum_add_distrib]
      rw [← Finset.smul_sum]
      abel_nf
      ring_nf
    rw [hsum]
    simp only [mEmp, hfEmp, fEmp, hReg]
    ring_nf
  rw [hinner]
  dsimp [mPop, hfPop, fPop, hReg]
  nlinarith [hm_abs.1, hm_abs.2, hHF_abs.1, hHF_abs.2,
    hF_abs.1, hF_abs.2]

end Primal
end NPIV
end Estimation
end Causalean
