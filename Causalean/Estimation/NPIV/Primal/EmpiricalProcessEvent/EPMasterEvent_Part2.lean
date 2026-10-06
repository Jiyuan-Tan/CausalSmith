/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Estimation.NPIV.Primal.EmpiricalProcessEvent.EPMasterEvent_Part1
public import Causalean.Estimation.NPIV.Primal.EmpiricalProcessEvent.LocalizedEvents

/-! # Localized assembly of the empirical-process master event

This second implementation part turns componentwise `H·F`, `m·F`, and `F²`
deviation bounds into the critic comparison and intersects their events over
sample sizes.  The resulting master event supplies the explicit objective gap
used by `EPPerN`.
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
/-- Componentwise version of `empirical_critic_argmax_localized`.

The hypotheses are exactly the per-critic localized deviations already
available from the single-index `m∘F`, `H·F`, and `F²` events.  No
closedness or linearity of the critic class beyond the paper's closedness
witness is added here. -/
lemma empirical_critic_argmax_localized_from_components
    {S : OperatorSystem Ω μ} {TC : TRAEClasses S}
    {P_W : Measure S.𝒲}
    {sample : IIDSample Ω S.𝒲 μ P_W}
    {split : OneShotSplit sample}
    [IsProbabilityMeasure μ]
    {lambda : ℝ} {h : S.𝒳 → ℝ} (hh : h ∈ TC.H)
    {f_closed : S.𝒵 → ℝ} (hf_closed : f_closed ∈ TC.F)
    {f_emp : S.𝒵 → ℝ} (hf_emp : f_emp ∈ TC.F)
    {n : ℕ} {ω : Ω}
    {Rm_closed RHF_closed RF_closed Rm_emp RHF_emp RF_emp : ℝ}
    (hcl :
      S.T (S.hL2 S.h₀_mem - S.hL2 (TC.H_subset hh))
        = S.qL2 (TC.F_subset hf_closed))
    (hopt :
      innerObjective S sample split lambda h f_closed n ω
        ≤ innerObjective S sample split lambda h f_emp n ω)
    (hmF_closed :
      |((split.n₁ n : ℕ) : ℝ)⁻¹ *
          ∑ k : Fin (split.n₁ n), S.m (sample.Z (k : ℕ) ω) f_closed
        - ∫ ω', S.m (S.W ω') f_closed ∂μ| ≤ Rm_closed)
    (hHF_closed :
      |((split.n₁ n : ℕ) : ℝ)⁻¹ *
          ∑ k : Fin (split.n₁ n),
            h (S.xOf (sample.Z (k : ℕ) ω)) *
              f_closed (S.zOf (sample.Z (k : ℕ) ω))
        - ∫ ω',
            h (S.xOf (S.W ω')) * f_closed (S.zOf (S.W ω')) ∂μ|
          ≤ RHF_closed)
    (hF_closed :
      |((split.n₁ n : ℕ) : ℝ)⁻¹ *
          ∑ k : Fin (split.n₁ n),
            (f_closed (S.zOf (sample.Z (k : ℕ) ω))) ^ 2
        - ∫ ω', (f_closed (S.zOf (S.W ω'))) ^ 2 ∂μ| ≤ RF_closed)
    (hmF_emp :
      |((split.n₁ n : ℕ) : ℝ)⁻¹ *
          ∑ k : Fin (split.n₁ n), S.m (sample.Z (k : ℕ) ω) f_emp
        - ∫ ω', S.m (S.W ω') f_emp ∂μ| ≤ Rm_emp)
    (hHF_emp :
      |((split.n₁ n : ℕ) : ℝ)⁻¹ *
          ∑ k : Fin (split.n₁ n),
            h (S.xOf (sample.Z (k : ℕ) ω)) *
              f_emp (S.zOf (sample.Z (k : ℕ) ω))
        - ∫ ω',
            h (S.xOf (S.W ω')) * f_emp (S.zOf (S.W ω')) ∂μ|
          ≤ RHF_emp)
    (hF_emp :
      |((split.n₁ n : ℕ) : ℝ)⁻¹ *
          ∑ k : Fin (split.n₁ n),
            (f_emp (S.zOf (sample.Z (k : ℕ) ω))) ^ 2
        - ∫ ω', (f_emp (S.zOf (S.W ω'))) ^ 2 ∂μ| ≤ RF_emp) :
      ‖S.qL2 (TC.F_subset hf_closed) - S.qL2 (TC.F_subset hf_emp)‖ ^ 2
        ≤ (2 * Rm_closed + 2 * RHF_closed + RF_closed)
          + (2 * Rm_emp + 2 * RHF_emp + RF_emp) := by
  let D_closed : ℝ := 2 * Rm_closed + 2 * RHF_closed + RF_closed
  let D_emp : ℝ := 2 * Rm_emp + 2 * RHF_emp + RF_emp
  have hclosed_upper :
      2 * (∫ ω', S.m (S.W ω') f_closed ∂μ)
          - 2 * (∫ ω',
              h (S.xOf (S.W ω')) * f_closed (S.zOf (S.W ω')) ∂μ)
          - ∫ ω', (f_closed (S.zOf (S.W ω'))) ^ 2 ∂μ
          + lambda *
              (((split.n₁ n : ℕ) : ℝ)⁻¹ * ∑ k : Fin (split.n₁ n),
                (h (S.xOf (sample.Z (k : ℕ) ω))) ^ 2)
        ≤ innerObjective S sample split lambda h f_closed n ω + D_closed := by
    simpa [D_closed] using
      population_regularized_le_innerObjective_add_deviation
        split lambda h f_closed n ω hmF_closed hHF_closed hF_closed
  have hemp_upper :
      innerObjective S sample split lambda h f_emp n ω
        ≤ 2 * (∫ ω', S.m (S.W ω') f_emp ∂μ)
          - 2 * (∫ ω',
              h (S.xOf (S.W ω')) * f_emp (S.zOf (S.W ω')) ∂μ)
          - ∫ ω', (f_emp (S.zOf (S.W ω'))) ^ 2 ∂μ
          + lambda *
              (((split.n₁ n : ℕ) : ℝ)⁻¹ * ∑ k : Fin (split.n₁ n),
                (h (S.xOf (sample.Z (k : ℕ) ω))) ^ 2)
          + D_emp := by
    simpa [D_emp] using
      innerObjective_le_population_regularized_add_deviation
        split lambda h f_emp n ω hmF_emp hHF_emp hF_emp
  apply empirical_critic_argmax_localized
      (S := S) (TC := TC) (sample := sample) (split := split)
      (lambda := lambda) (hh := hh) (hf_closed := hf_closed)
      (hf_emp := hf_emp) (n := n) (ω := ω)
      (R := D_closed + D_emp) hcl hopt
  linarith [hclosed_upper, hemp_upper]

/-- **Master localized empirical-process event for the primal NPIV analysis.** Given, for every
sample size `n`, [a localized-regime bundle for the weak-norm, regularizer, and cross function
classes at that fold-A sample size](hyp:regimes), and [a confidence level `ζ` strictly between
`0` and `1`](hyp:hζ_pos,hζ_lt), [there is a single event of probability at least `1 − ζ` on
which, simultaneously for every `n` with `1 ≤ split.n₁ n`, the population weak-objective excess
plus the empirical regularizer excess is bounded by the empirical sup-objective excess plus a
localized envelope built from the regimes' critical radii and a `√(log(1/ζ)/n)` term](goal).

The envelope combines the localized regimes for the weak-norm class, the regularizer class, and
their interaction, so downstream lemmas can consume one event rather than three separate
concentration statements.  It belongs to the earlier simultaneous-in-`n`
route; `per_sample_empirical_process_event` is the current fixed-sample
replacement. -/
theorem ep_master_event_from_localized
    {S : OperatorSystem Ω μ} {TC : TRAEClasses S}
    {P_W : Measure S.𝒲}
    {sample : IIDSample Ω S.𝒲 μ P_W}
    {split : OneShotSplit sample}
    {lambda β : ℝ} {delta : ℕ → ℝ}
    {h_hat : ℕ → Ω → S.𝒳 → ℝ}
    (is_estimator : IsTRAEPrimalEstimator S TC sample split lambda h_hat)
    (sc : SourceCondition S β)
    (tb : TikhonovBiasBoundAt S β lambda sc)
    [IsProbabilityMeasure μ]
    (regimes : ∀ n, LocalizedRegimes S TC sample sc tb (split.n₁ n) (delta n))
    {ζ : ℝ} (hζ_pos : 0 < ζ) (hζ_lt : ζ < 1) :
    ∃ Aζ_master : Set Ω,
      MeasurableSet Aζ_master ∧ μ Aζ_master ≥ 1 - ENNReal.ofReal ζ ∧
      ∀ ω ∈ Aζ_master, ∀ n : ℕ, 1 ≤ split.n₁ n →
        ((S.weakNorm
            (S.hL2 (TC.H_subset (is_estimator.mem_H n ω))
              - S.hL2 S.h₀_mem)) ^ 2
          + lambda *
              (((split.n₁ n : ℕ) : ℝ)⁻¹ * ∑ k : Fin (split.n₁ n),
                (h_hat n ω (S.xOf (sample.Z (k : ℕ) ω))) ^ 2))
          - ((S.weakNorm
              (S.hL2 tb.h_lambda_star_mem
                - S.hL2 S.h₀_mem)) ^ 2
            + lambda *
                (((split.n₁ n : ℕ) : ℝ)⁻¹ * ∑ k : Fin (split.n₁ n),
                  (tb.h_lambda_star_fun (S.xOf (sample.Z (k : ℕ) ω))) ^ 2))
        ≤ supObjective S TC sample split lambda (h_hat n ω) n ω
            - supObjective S TC sample split lambda tb.h_lambda_star_fun n ω
      + (16 * delta n *
                criticalRadius ((regimes n).bundle_HF.regime.ψ (split.n₁ n))
              + 16 * delta n *
                criticalRadius ((regimes n).bundle_mF.regime.ψ (split.n₁ n))
              + 8 * delta n *
                criticalRadius ((regimes n).bundle_F.regime.ψ (split.n₁ n))
              + 4 * npivBousquetSlack (regimes n).bundle_HF.regime.b (delta n)
                  (criticalRadius ((regimes n).bundle_HF.regime.ψ (split.n₁ n)))
                  (Real.log (4 * (2 : ℝ) ^ (n + 1) / ζ)) (split.n₁ n)
              + 4 * npivBousquetSlack (regimes n).bundle_mF.regime.b (delta n)
                  (criticalRadius ((regimes n).bundle_mF.regime.ψ (split.n₁ n)))
                  (Real.log (4 * (2 : ℝ) ^ (n + 1) / ζ)) (split.n₁ n)
              + 2 * npivBousquetSlack (regimes n).bundle_F.regime.b (delta n)
                  (criticalRadius ((regimes n).bundle_F.regime.ψ (split.n₁ n)))
                  (Real.log (4 * (2 : ℝ) ^ (n + 1) / ζ)) (split.n₁ n)) := by
  classical
  let ε : ℕ → ℝ := fun n => ζ * ((1 / 2 : ℝ) ^ (n + 1))
  let η : ℕ → ℝ := fun n => ε n / 4
  have hε_pos : ∀ n, 0 < ε n := by
    intro n
    exact mul_pos hζ_pos (pow_pos (by norm_num) _)
  have hε_le_one : ∀ n, ε n ≤ 1 := by
    intro n
    have hζ_le : ζ ≤ 1 := le_of_lt hζ_lt
    have hpow_le_one : ((1 / 2 : ℝ) ^ (n + 1)) ≤ 1 := by
      exact pow_le_one₀ (by norm_num) (by norm_num)
    have hpow_nonneg : 0 ≤ ((1 / 2 : ℝ) ^ (n + 1)) := by positivity
    nlinarith
  have hη_pos : ∀ n, 0 < η n := by
    intro n
    dsimp [η]
    positivity
  have hη_le_one : ∀ n, η n ≤ 1 := by
    intro n
    dsimp [η]
    nlinarith [hε_le_one n]
  let EHF : ℕ → Set Ω := fun n =>
    if hn : 0 < split.n₁ n then
      (localized_omega_event_for_HF (regimes n) hn (hη_pos n) (hη_le_one n)).choose
    else Set.univ
  let EmF : ℕ → Set Ω := fun n =>
    if hn : 0 < split.n₁ n then
      (localized_omega_event_for_mF (regimes n) hn (hη_pos n) (hη_le_one n)).choose
    else Set.univ
  let EF : ℕ → Set Ω := fun n =>
    if hn : 0 < split.n₁ n then
      (localized_omega_event_for_F (regimes n) hn (hη_pos n) (hη_le_one n)).choose
    else Set.univ
  let En : ℕ → Set Ω := fun n => EHF n ∩ EmF n ∩ EF n
  have hEHF_meas : ∀ n, MeasurableSet (EHF n) := by
    intro n
    by_cases hn : 0 < split.n₁ n
    · simpa [EHF, hn] using
        (localized_omega_event_for_HF (regimes n) hn
          (hη_pos n) (hη_le_one n)).choose_spec.1
    · simp [EHF, hn]
  have hEmF_meas : ∀ n, MeasurableSet (EmF n) := by
    intro n
    by_cases hn : 0 < split.n₁ n
    · simpa [EmF, hn] using
        (localized_omega_event_for_mF (regimes n) hn
          (hη_pos n) (hη_le_one n)).choose_spec.1
    · simp [EmF, hn]
  have hEF_meas : ∀ n, MeasurableSet (EF n) := by
    intro n
    by_cases hn : 0 < split.n₁ n
    · simpa [EF, hn] using
        (localized_omega_event_for_F (regimes n) hn
          (hη_pos n) (hη_le_one n)).choose_spec.1
    · simp [EF, hn]
  have hEHF_mass : ∀ n, μ (EHF n) ≥ 1 - ENNReal.ofReal (η n) := by
    intro n
    by_cases hn : 0 < split.n₁ n
    · simpa [EHF, hn] using
        (localized_omega_event_for_HF (regimes n) hn
          (hη_pos n) (hη_le_one n)).choose_spec.2.1
    · simp [EHF, hn]
  have hEmF_mass : ∀ n, μ (EmF n) ≥ 1 - ENNReal.ofReal (η n) := by
    intro n
    by_cases hn : 0 < split.n₁ n
    · simpa [EmF, hn] using
        (localized_omega_event_for_mF (regimes n) hn
          (hη_pos n) (hη_le_one n)).choose_spec.2.1
    · simp [EmF, hn]
  have hEF_mass : ∀ n, μ (EF n) ≥ 1 - ENNReal.ofReal (η n) := by
    intro n
    by_cases hn : 0 < split.n₁ n
    · simpa [EF, hn] using
        (localized_omega_event_for_F (regimes n) hn
          (hη_pos n) (hη_le_one n)).choose_spec.2.1
    · simp [EF, hn]
  have hEn_meas : ∀ n, MeasurableSet (En n) := by
    intro n
    exact ((hEHF_meas n).inter (hEmF_meas n)).inter (hEF_meas n)
  have hEn_mass : ∀ n, μ (En n) ≥ 1 - ENNReal.ofReal (ε n) := by
    intro n
    have h12 :
        μ (EHF n ∩ EmF n)
          ≥ 1 - (ENNReal.ofReal (η n) + ENNReal.ofReal (η n)) :=
      measure_inter_ge_one_sub_add_of_ge (hEHF_meas n) (hEmF_meas n)
        (hEHF_mass n) (hEmF_mass n)
    have h123 :
        μ ((EHF n ∩ EmF n) ∩ EF n)
          ≥ 1 -
            ((ENNReal.ofReal (η n) + ENNReal.ofReal (η n))
              + ENNReal.ofReal (η n)) :=
      measure_inter_ge_one_sub_add_of_ge
        ((hEHF_meas n).inter (hEmF_meas n)) (hEF_meas n)
        h12 (hEF_mass n)
    have hη_nonneg : 0 ≤ η n := le_of_lt (hη_pos n)
    have htriple_eq :
        (ENNReal.ofReal (η n) + ENNReal.ofReal (η n))
            + ENNReal.ofReal (η n)
          = ENNReal.ofReal (η n + η n + η n) := by
      rw [← ENNReal.ofReal_add hη_nonneg hη_nonneg]
      rw [← ENNReal.ofReal_add (add_nonneg hη_nonneg hη_nonneg) hη_nonneg]
    have htriple_le :
        (ENNReal.ofReal (η n) + ENNReal.ofReal (η n))
            + ENNReal.ofReal (η n)
          ≤ ENNReal.ofReal (ε n) := by
      rw [htriple_eq]
      apply ENNReal.ofReal_le_ofReal
      dsimp [η]
      nlinarith [hε_pos n]
    simpa [En, Set.inter_assoc] using
      (tsub_le_tsub_left htriple_le 1).trans h123
  have htsum_ε : (∑' n, ENNReal.ofReal (ε n)) ≤ ENNReal.ofReal ζ := by
    have hterm :
        (fun n => ENNReal.ofReal (ε n))
          =
        fun n => ENNReal.ofReal ζ * (2⁻¹ : ENNReal) ^ (n + 1) := by
      funext n
      rw [show ε n = ζ * (1 / 2 : ℝ) ^ (n + 1) by rfl]
      rw [ENNReal.ofReal_mul (le_of_lt hζ_pos)]
      simp [one_div, ENNReal.inv_pow]
    rw [hterm, ENNReal.tsum_mul_left, ENNReal.tsum_geometric_add_one]
    have hgeom : (2⁻¹ : ENNReal) * (1 - 2⁻¹)⁻¹ = 1 := by
      rw [ENNReal.one_sub_inv_two, inv_inv]
      exact ENNReal.inv_mul_cancel (Ne.symm (NeZero.ne' (2 : ENNReal)))
        (by norm_num : (2 : ENNReal) ≠ ⊤)
    rw [hgeom, mul_one]
  let Aζ_master : Set Ω := ⋂ n, En n
  refine ⟨Aζ_master, MeasurableSet.iInter hEn_meas, ?_, ?_⟩
  · exact (tsub_le_tsub_left htsum_ε 1).trans
      (measure_iInter_nat_ge_one_sub_tsum_of_ge hEn_meas hEn_mass)
  · intro ω hω n _hn
    have hn_pos : 0 < split.n₁ n := lt_of_lt_of_le zero_lt_one _hn
    have hωn : ω ∈ En n := Set.mem_iInter.mp hω n
    have hωHF : ω ∈ EHF n := hωn.1.1
    have hωmF : ω ∈ EmF n := hωn.1.2
    have hωF : ω ∈ EF n := hωn.2
    have hωHF_event :
        ω ∈ (localized_omega_event_for_HF (regimes n) hn_pos
          (hη_pos n) (hη_le_one n)).choose := by
      simpa [EHF, hn_pos] using hωHF
    have hωmF_event :
        ω ∈ (localized_omega_event_for_mF (regimes n) hn_pos
          (hη_pos n) (hη_le_one n)).choose := by
      simpa [EmF, hn_pos] using hωmF
    have hωF_event :
        ω ∈ (localized_omega_event_for_F (regimes n) hn_pos
          (hη_pos n) (hη_le_one n)).choose := by
      simpa [EF, hn_pos] using hωF
    obtain ⟨f_h, hf_h, hcl_h⟩ :=
      (regimes n).closedness (h_hat n ω) (is_estimator.mem_H n ω)
    obtain ⟨f_star, hf_star, hstar_sup_le_inner⟩ :=
      (regimes n).supObjective_attained split n ω
        tb.h_lambda_star_fun (regimes n).realizability
    have hinner_le_sup :
        innerObjective S sample split lambda (h_hat n ω) f_h n ω
          ≤ supObjective S TC sample split lambda (h_hat n ω) n ω :=
      (regimes n).inner_le_supObjective split n ω
        (h_hat n ω) (is_estimator.mem_H n ω) f_h hf_h
    have hlog : 1 / η n = 4 * (2 : ℝ) ^ (n + 1) / ζ := by
      dsimp [η, ε]
      simp only [one_div]
      rw [inv_pow]
      field_simp [ne_of_gt hζ_pos,
        pow_ne_zero (n + 1) (show (2 : ℝ) ≠ 0 by norm_num)]
    have hHF_h :=
      (localized_omega_event_for_HF (regimes n) hn_pos
        (hη_pos n) (hη_le_one n)).choose_spec.2.2
        ω hωHF_event (h_hat n ω) (is_estimator.mem_H n ω) f_h hf_h
    have hmF_h :=
      (localized_omega_event_for_mF (regimes n) hn_pos
        (hη_pos n) (hη_le_one n)).choose_spec.2.2
        ω hωmF_event f_h hf_h
    have hF_h :=
      (localized_omega_event_for_F (regimes n) hn_pos
        (hη_pos n) (hη_le_one n)).choose_spec.2.2
        ω hωF_event f_h hf_h
    have hHF_star :=
      (localized_omega_event_for_HF (regimes n) hn_pos
        (hη_pos n) (hη_le_one n)).choose_spec.2.2
        ω hωHF_event tb.h_lambda_star_fun (regimes n).realizability
        f_star hf_star
    have hmF_star :=
      (localized_omega_event_for_mF (regimes n) hn_pos
        (hη_pos n) (hη_le_one n)).choose_spec.2.2
        ω hωmF_event f_star hf_star
    have hF_star :=
      (localized_omega_event_for_F (regimes n) hn_pos
        (hη_pos n) (hη_le_one n)).choose_spec.2.2
        ω hωF_event f_star hf_star
    rw [hlog] at hHF_h hmF_h hF_h hHF_star hmF_star hF_star
    let rHF : ℝ :=
      4 * delta n * criticalRadius ((regimes n).bundle_HF.regime.ψ (split.n₁ n))
        + 2 * Real.sqrt
            (((delta n) ^ 2 + 8 * (regimes n).bundle_HF.regime.b * delta n *
                criticalRadius ((regimes n).bundle_HF.regime.ψ (split.n₁ n))) *
              Real.log (4 * (2 : ℝ) ^ (n + 1) / ζ) / (split.n₁ n))
        + 8 * (regimes n).bundle_HF.regime.b *
            Real.log (4 * (2 : ℝ) ^ (n + 1) / ζ) / (split.n₁ n)
    let rmF : ℝ :=
      4 * delta n * criticalRadius ((regimes n).bundle_mF.regime.ψ (split.n₁ n))
        + 2 * Real.sqrt
            (((delta n) ^ 2 + 8 * (regimes n).bundle_mF.regime.b * delta n *
                criticalRadius ((regimes n).bundle_mF.regime.ψ (split.n₁ n))) *
              Real.log (4 * (2 : ℝ) ^ (n + 1) / ζ) / (split.n₁ n))
        + 8 * (regimes n).bundle_mF.regime.b *
            Real.log (4 * (2 : ℝ) ^ (n + 1) / ζ) / (split.n₁ n)
    let rF : ℝ :=
      4 * delta n * criticalRadius ((regimes n).bundle_F.regime.ψ (split.n₁ n))
        + 2 * Real.sqrt
            (((delta n) ^ 2 + 8 * (regimes n).bundle_F.regime.b * delta n *
                criticalRadius ((regimes n).bundle_F.regime.ψ (split.n₁ n))) *
              Real.log (4 * (2 : ℝ) ^ (n + 1) / ζ) / (split.n₁ n))
        + 8 * (regimes n).bundle_F.regime.b *
            Real.log (4 * (2 : ℝ) ^ (n + 1) / ζ) / (split.n₁ n)
    have hupper_h :
        2 * (∫ ω', S.m (S.W ω') f_h ∂μ)
            - 2 * (∫ ω',
                (h_hat n ω) (S.xOf (S.W ω')) *
                  f_h (S.zOf (S.W ω')) ∂μ)
            - ∫ ω', (f_h (S.zOf (S.W ω'))) ^ 2 ∂μ
            + lambda *
                (((split.n₁ n : ℕ) : ℝ)⁻¹ *
                  ∑ k : Fin (split.n₁ n),
                    ((h_hat n ω) (S.xOf (sample.Z (k : ℕ) ω))) ^ 2)
          ≤ innerObjective S sample split lambda (h_hat n ω) f_h n ω
            + (2 * rmF + 2 * rHF + rF) := by
      exact population_regularized_le_innerObjective_add_deviation
        split lambda (h_hat n ω) f_h n ω hmF_h hHF_h hF_h
    have hupper_star :
        innerObjective S sample split lambda tb.h_lambda_star_fun f_star n ω
          ≤ 2 * (∫ ω', S.m (S.W ω') f_star ∂μ)
            - 2 * (∫ ω',
                tb.h_lambda_star_fun (S.xOf (S.W ω')) *
                  f_star (S.zOf (S.W ω')) ∂μ)
            - ∫ ω', (f_star (S.zOf (S.W ω'))) ^ 2 ∂μ
            + lambda *
                (((split.n₁ n : ℕ) : ℝ)⁻¹ *
                  ∑ k : Fin (split.n₁ n),
                    (tb.h_lambda_star_fun (S.xOf (sample.Z (k : ℕ) ω))) ^ 2)
            + (2 * rmF + 2 * rHF + rF) := by
      exact innerObjective_le_population_regularized_add_deviation
        split lambda tb.h_lambda_star_fun f_star n ω
        hmF_star hHF_star hF_star
    have hpop_h_eq :
        2 * (∫ ω', S.m (S.W ω') f_h ∂μ)
            - 2 * (∫ ω',
                (h_hat n ω) (S.xOf (S.W ω')) *
                  f_h (S.zOf (S.W ω')) ∂μ)
            - ∫ ω', (f_h (S.zOf (S.W ω'))) ^ 2 ∂μ
          =
            (S.weakNorm
              (S.hL2 (TC.H_subset (is_estimator.mem_H n ω))
                - S.hL2 S.h₀_mem)) ^ 2 :=
      population_inner_eq_closedness_witness
        (hh := is_estimator.mem_H n ω) (hf := hf_h) hcl_h
    have hpop_star_le :
        2 * (∫ ω', S.m (S.W ω') f_star ∂μ)
            - 2 * (∫ ω',
                tb.h_lambda_star_fun (S.xOf (S.W ω')) *
                  f_star (S.zOf (S.W ω')) ∂μ)
            - ∫ ω', (f_star (S.zOf (S.W ω'))) ^ 2 ∂μ
          ≤
            (S.weakNorm
              (S.hL2 tb.h_lambda_star_mem
                - S.hL2 S.h₀_mem)) ^ 2 :=
      population_inner_le_weak
        (hh := (regimes n).realizability) (hf := hf_star)
    simp only [npivBousquetSlack]
    linarith [hupper_h, hupper_star, hpop_h_eq, hpop_star_le,
      hinner_le_sup, hstar_sup_le_inner]

end Primal
end NPIV
end Estimation
end Causalean
