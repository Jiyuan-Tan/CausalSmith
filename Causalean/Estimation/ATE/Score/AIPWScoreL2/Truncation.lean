/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Estimation.ATE.Score.AIPWScoreL2.Continuity

/-!
Combines the pointwise AIPW bound and the residual truncation estimate into the
headline L² stochastic-continuity results. It proves
`aipw_score_diff_isLittleOp_one` and its almost-everywhere overlap variant, the
forms consumed by the ATE double-machine-learning argument.
-/

public section

namespace Causalean
namespace Estimation
namespace ATE

open MeasureTheory ProbabilityTheory Filter Topology Causalean.PO Causalean.Stat

namespace BackdoorEstimationSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
/-- **Headline L²(P_Z) `o_p(1)` continuity bound for the AIPW score.**

Given:
* strict overlap `ε` for `(μ_val, e_val)`;
* `Y² ∈ L¹(P.μ)`, `(Y(d))² ∈ L¹(P.μ)` for `d ∈ {0,1}`;
* a random nuisance `η̂(n, ω) ∈ H_ε_aeL2 S ε` for all `n, ω`;
* individual rates `‖Δμ_a(n,ω,·)‖_{L²(P_X)} = o_p(1)` and
  `‖Δe(n,ω,·)‖_{L²(P_X)} = o_p(1)`.

Then `‖m_AIPW(η̂(n,ω), ·, θ₀) − m_AIPW(η₀, ·, θ₀)‖_{L²(P_Z)} = o_p(1)`
under `μ`.

**Proof outline.**  Apply `aipw_score_diff_pointwise_bound`; square and
integrate against `P_Z`; for the cross term use `|Δe| ≤ 1` and a truncation
argument on `(|y − μ_val(d,x)| + ...)²` (for any `δ > 0` choose `K` such that
the tail `∫ ... · 𝟙{... > K²} dP_Z < δ`, then dominate the bulk by `K² ·
‖Δe‖_{L¹(P_X)} ≤ K² · ‖Δe‖_{L²(P_X)}` which is `o_p(1)`). -/
private theorem aipw_score_diff_isLittleOp_one_truncation_core
    (S : BackdoorEstimationSystem P γ) {ε : ℝ}
    (h_overlap : S.StrictOverlap ε)
    (hA : S.toPOBackdoorSystem.Assumptions)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_yd2 : ∀ d : Bool, Integrable
      (fun ω => (S.toPOBackdoorSystem.YofD d ω) ^ 2) P.μ)
    (η_hat : ℕ → P.Ω → NuisanceVec γ)
    (h_in_H : ∀ n ω, η_hat n ω ∈ H_ε_aeL2 S ε)
    (h_mu_memLp :
      ∀ n ω a, MemLp
        (fun x => (η_hat n ω).μ_fn a x - S.μ_val a x) 2 S.P_X)
    (h_e_memLp :
      ∀ n ω, MemLp
        (fun x => (η_hat n ω).e_fn x - S.e_val x) 2 S.P_X)
    (h_mu_rate :
      ∀ a : Bool,
        IsLittleOp
          (fun n ω =>
            (eLpNorm (fun x => (η_hat n ω).μ_fn a x - S.μ_val a x) 2 S.P_X).toReal)
          (fun _ => (1 : ℝ)) P.μ)
    (h_e_rate :
      IsLittleOp
        (fun n ω =>
          (eLpNorm (fun x => (η_hat n ω).e_fn x - S.e_val x) 2 S.P_X).toReal)
        (fun _ => (1 : ℝ)) P.μ) :
    IsLittleOp
      (fun n ω =>
        (eLpNorm (fun z =>
            aipwMomentFunctional (η_hat n ω) z S.θ₀ -
              aipwMomentFunctional S.η₀ z S.θ₀) 2 S.P_Z).toReal)
      (fun _ => (1 : ℝ)) P.μ := by
  classical
  rcases h_overlap with ⟨hε_pos, hε_half, hprop⟩
  let R : (γ × Bool × ℝ) → ℝ := fun z =>
    |projY z - S.μ_val true (projX z)|
      + |projY z - S.μ_val false (projX z)|
  let dμZ : Bool → ℕ → P.Ω → (γ × Bool × ℝ) → ℝ := fun a n ω z =>
    (η_hat n ω).μ_fn a (projX z) - S.μ_val a (projX z)
  let deZ : ℕ → P.Ω → (γ × Bool × ℝ) → ℝ := fun n ω z =>
    (η_hat n ω).e_fn (projX z) - S.e_val (projX z)
  let cross : ℕ → P.Ω → (γ × Bool × ℝ) → ℝ := fun n ω z =>
    R z * |deZ n ω z|
  let score : ℕ → P.Ω → (γ × Bool × ℝ) → ℝ := fun n ω z =>
    aipwMomentFunctional (η_hat n ω) z S.θ₀ -
      aipwMomentFunctional S.η₀ z S.θ₀
  have hR_meas : Measurable R := by
    simpa [R] using yMuVal_residual_meas S
  have hR_nonneg : ∀ z, 0 ≤ R z := by
    intro z
    dsimp [R]
    positivity
  have hR_memLp : MemLp R 2 S.P_Z := by
    simpa [R] using yMuVal_residual_memLp S hA h_y2 h_yd2
  have hdμZ_memLp : ∀ a n ω, MemLp (dμZ a n ω) 2 S.P_Z := by
    intro a n ω
    have hmap : MemLp (fun x => (η_hat n ω).μ_fn a x - S.μ_val a x)
        2 (S.P_Z.map (fun z : γ × Bool × ℝ => z.1)) := by
      simpa [BackdoorEstimationSystem.P_Z_map_projX_eq_P_X S] using h_mu_memLp n ω a
    have hproj_ae : AEMeasurable (fun z : γ × Bool × ℝ => z.1) S.P_Z :=
      measurable_fst.aemeasurable
    exact (memLp_map_measure_iff hmap.aestronglyMeasurable hproj_ae).1 hmap
  have hdeZ_memLp : ∀ n ω, MemLp (deZ n ω) 2 S.P_Z := by
    intro n ω
    have hmap : MemLp (fun x => (η_hat n ω).e_fn x - S.e_val x)
        2 (S.P_Z.map (fun z : γ × Bool × ℝ => z.1)) := by
      simpa [BackdoorEstimationSystem.P_Z_map_projX_eq_P_X S] using h_e_memLp n ω
    have hproj_ae : AEMeasurable (fun z : γ × Bool × ℝ => z.1) S.P_Z :=
      measurable_fst.aemeasurable
    exact (memLp_map_measure_iff hmap.aestronglyMeasurable hproj_ae).1 hmap
  have hdeZ_bdd : ∀ n ω, ∀ᵐ z ∂S.P_Z, |deZ n ω z| ≤ 1 := by
    intro n ω
    filter_upwards [H_ε_aeL2_overlap_P_Z S (h_in_H n ω)] with z hη
    have hη_nonneg : 0 ≤ (η_hat n ω).e_fn (projX z) :=
      le_trans hε_pos.le hη.1
    have hη_le_one : (η_hat n ω).e_fn (projX z) ≤ 1 := by
      linarith [hη.2, hε_pos.le]
    have hS_nonneg : 0 ≤ S.e_val (projX z) := le_of_lt (S.e_pos (projX z))
    have hS_le_one : S.e_val (projX z) ≤ 1 := le_of_lt (S.e_lt_one (projX z))
    dsimp [deZ]
    rw [abs_le]
    constructor <;> linarith
  have hcross_rate :
      IsLittleOp
        (fun n ω => (eLpNorm (cross n ω) 2 S.P_Z).toReal)
        (fun _ => (1 : ℝ)) P.μ := by
    simpa [cross, R, deZ] using
      residual_mul_e_error_isLittleOp_one S ⟨hε_pos, hε_half, hprop⟩
        hA h_y2 h_yd2 η_hat h_in_H h_e_memLp h_e_rate
  have hμZ_rate : ∀ a : Bool,
      IsLittleOp
        (fun n ω => (eLpNorm (dμZ a n ω) 2 S.P_Z).toReal)
        (fun _ => (1 : ℝ)) P.μ := by
    intro a
    have heq :
        (fun n ω => (eLpNorm (dμZ a n ω) 2 S.P_Z).toReal) =
          (fun n ω =>
            (eLpNorm (fun x => (η_hat n ω).μ_fn a x - S.μ_val a x) 2 S.P_X).toReal) := by
      funext n
      funext ω
      dsimp [dμZ]
      exact congrArg ENNReal.toReal
        (eLpNorm_comp_projX_eq (S := S)
          (f := fun x => (η_hat n ω).μ_fn a x - S.μ_val a x)
          (h_mu_memLp n ω a).aestronglyMeasurable)
    rw [heq]
    exact h_mu_rate a
  have hsum_rate :
      IsLittleOp
        (fun n ω =>
          (eLpNorm (dμZ true n ω) 2 S.P_Z).toReal +
            (eLpNorm (dμZ false n ω) 2 S.P_Z).toReal +
              (eLpNorm (cross n ω) 2 S.P_Z).toReal)
        (fun _ => (1 : ℝ)) P.μ := by
    exact IsLittleOp.add_one (IsLittleOp.add_one (hμZ_rate true) (hμZ_rate false))
      hcross_rate
  have hK_pos : 0 < K_AIPW ε := lt_of_lt_of_le zero_lt_one (K_AIPW_one_le hε_pos)
  refine IsLittleOp.of_abs_le_const_mul_one (C := K_AIPW ε) hK_pos hsum_rate ?_
  intro n ω
  have hpointwise :
      ∀ᵐ z ∂S.P_Z, |score n ω z| ≤
        K_AIPW ε * (|dμZ true n ω z| + |dμZ false n ω z| + cross n ω z) := by
    simpa [score, dμZ, cross, R, deZ] using
      aipw_score_diff_pointwise_bound S ⟨hε_pos, hε_half, hprop⟩
        (η_hat n ω) (h_in_H n ω)
  let upper : (γ × Bool × ℝ) → ℝ := fun z =>
    K_AIPW ε * (|dμZ true n ω z| + |dμZ false n ω z| + cross n ω z)
  have hcross_memLp : MemLp (cross n ω) 2 S.P_Z := by
    have hcross_meas : Measurable (cross n ω) := by
      have hde_meas : Measurable (deZ n ω) := by
        have hx : Measurable (fun z : γ × Bool × ℝ => projX z) := by
          simpa [projX] using
            (measurable_fst : Measurable (fun z : γ × Bool × ℝ => z.1))
        exact ((η_hat n ω).e_meas.comp hx).sub (S.e_meas.comp hx)
      exact hR_meas.mul (continuous_abs.measurable.comp hde_meas)
    refine hR_memLp.mono' hcross_meas.aestronglyMeasurable ?_
    filter_upwards [hdeZ_bdd n ω] with z hdez_le
    have hRz : 0 ≤ R z := hR_nonneg z
    dsimp [cross]
    rw [abs_mul, abs_of_nonneg hRz, abs_of_nonneg (abs_nonneg _)]
    exact mul_le_of_le_one_right hRz hdez_le
  have hupper_memLp : MemLp upper 2 S.P_Z := by
    have hsum : MemLp
        (fun z => |dμZ true n ω z| + |dμZ false n ω z| + cross n ω z)
        2 S.P_Z := by
      have ht : MemLp (fun z => |dμZ true n ω z|) 2 S.P_Z := by
        simpa [Real.norm_eq_abs] using (hdμZ_memLp true n ω).norm
      have hf : MemLp (fun z => |dμZ false n ω z|) 2 S.P_Z := by
        simpa [Real.norm_eq_abs] using (hdμZ_memLp false n ω).norm
      exact (ht.add hf).add hcross_memLp
    exact hsum.const_smul (K_AIPW ε)
  have hmono :
      (eLpNorm (score n ω) 2 S.P_Z).toReal ≤
        (eLpNorm upper 2 S.P_Z).toReal := by
    have hle_enn : eLpNorm (score n ω) 2 S.P_Z ≤ eLpNorm upper 2 S.P_Z :=
      eLpNorm_mono_ae_real (by
        filter_upwards [hpointwise] with z hz
        simpa [Real.norm_eq_abs, upper] using hz)
    exact ENNReal.toReal_mono hupper_memLp.eLpNorm_ne_top hle_enn
  have hupper_bound :
      (eLpNorm upper 2 S.P_Z).toReal ≤
        K_AIPW ε *
          ((eLpNorm (dμZ true n ω) 2 S.P_Z).toReal +
            (eLpNorm (dμZ false n ω) 2 S.P_Z).toReal +
              (eLpNorm (cross n ω) 2 S.P_Z).toReal) := by
    let total : (γ × Bool × ℝ) → ℝ := fun z =>
      |dμZ true n ω z| + |dμZ false n ω z| + cross n ω z
    have htotal_memLp : MemLp total 2 S.P_Z := by
      have ht : MemLp (fun z => |dμZ true n ω z|) 2 S.P_Z := by
        simpa [Real.norm_eq_abs] using (hdμZ_memLp true n ω).norm
      have hf : MemLp (fun z => |dμZ false n ω z|) 2 S.P_Z := by
        simpa [Real.norm_eq_abs] using (hdμZ_memLp false n ω).norm
      exact (ht.add hf).add hcross_memLp
    have hupper_eq : upper = K_AIPW ε • total := by
      funext z
      simp [upper, total, smul_eq_mul]
    rw [hupper_eq]
    rw [toReal_eLpNorm (htotal_memLp.const_smul (K_AIPW ε)).aestronglyMeasurable]
    rw [lpNorm_const_smul]
    have hcoef : (↑‖K_AIPW ε‖₊ : ℝ) = K_AIPW ε := by
      simp [Real.norm_eq_abs, abs_of_pos hK_pos]
    rw [hcoef]
    gcongr
    have htri1 :
        lpNorm total 2 S.P_Z ≤
          lpNorm (fun z => |dμZ true n ω z| + |dμZ false n ω z|) 2 S.P_Z +
            lpNorm (cross n ω) 2 S.P_Z := by
      have htotal_eq :
          total =
            (fun z => |dμZ true n ω z| + |dμZ false n ω z|) + cross n ω := by
        funext z
        simp [total, Pi.add_apply, add_assoc]
      rw [htotal_eq]
      exact
          lpNorm_add_le (f := fun z => |dμZ true n ω z| + |dμZ false n ω z|)
            (g := cross n ω) (μ := S.P_Z)
            ((by
              have ht : MemLp (fun z => |dμZ true n ω z|) 2 S.P_Z := by
                simpa [Real.norm_eq_abs] using (hdμZ_memLp true n ω).norm
              have hf : MemLp (fun z => |dμZ false n ω z|) 2 S.P_Z := by
                simpa [Real.norm_eq_abs] using (hdμZ_memLp false n ω).norm
              exact ht.add hf))
            (by norm_num : (1 : ENNReal) ≤ 2)
    have htri2 :
        lpNorm (fun z => |dμZ true n ω z| + |dμZ false n ω z|) 2 S.P_Z ≤
          lpNorm (fun z => |dμZ true n ω z|) 2 S.P_Z +
            lpNorm (fun z => |dμZ false n ω z|) 2 S.P_Z := by
      have ht : MemLp (fun z => |dμZ true n ω z|) 2 S.P_Z := by
        simpa [Real.norm_eq_abs] using (hdμZ_memLp true n ω).norm
      exact lpNorm_add_le (f := fun z => |dμZ true n ω z|)
        (g := fun z => |dμZ false n ω z|) (μ := S.P_Z) ht
        (by norm_num : (1 : ENNReal) ≤ 2)
    have hnormT :
        lpNorm (fun z => |dμZ true n ω z|) 2 S.P_Z =
          (eLpNorm (dμZ true n ω) 2 S.P_Z).toReal := by
      rw [lpNorm_fun_abs (hdμZ_memLp true n ω).aestronglyMeasurable]
      rw [← toReal_eLpNorm (hdμZ_memLp true n ω).aestronglyMeasurable]
    have hnormF :
        lpNorm (fun z => |dμZ false n ω z|) 2 S.P_Z =
          (eLpNorm (dμZ false n ω) 2 S.P_Z).toReal := by
      rw [lpNorm_fun_abs (hdμZ_memLp false n ω).aestronglyMeasurable]
      rw [← toReal_eLpNorm (hdμZ_memLp false n ω).aestronglyMeasurable]
    have hnormC :
        lpNorm (cross n ω) 2 S.P_Z =
          (eLpNorm (cross n ω) 2 S.P_Z).toReal := by
      rw [← toReal_eLpNorm hcross_memLp.aestronglyMeasurable]
    linarith
  calc
    |(eLpNorm (score n ω) 2 S.P_Z).toReal|
        = (eLpNorm (score n ω) 2 S.P_Z).toReal := by
          rw [abs_of_nonneg ENNReal.toReal_nonneg]
    _ ≤ (eLpNorm upper 2 S.P_Z).toReal := hmono
    _ ≤ K_AIPW ε *
        ((eLpNorm (dμZ true n ω) 2 S.P_Z).toReal +
          (eLpNorm (dμZ false n ω) 2 S.P_Z).toReal +
            (eLpNorm (cross n ω) 2 S.P_Z).toReal) := hupper_bound
    _ = K_AIPW ε *
        |(eLpNorm (dμZ true n ω) 2 S.P_Z).toReal +
          (eLpNorm (dμZ false n ω) 2 S.P_Z).toReal +
            (eLpNorm (cross n ω) 2 S.P_Z).toReal| := by
          rw [abs_of_nonneg]
          positivity

/-- Fix [strict overlap at level `ε`](hyp:h_overlap), [the back-door
identification assumptions](hyp:hA), and [finite second moments of the
observed and potential outcomes](hyp:h_y2,h_yd2). For a sequence of nuisance
estimators `η̂` such that [every realization lies in the `ε`-overlap `L²`
nuisance class](hyp:h_in_H), with [outcome-regression errors in `L²(P_X)` at
every horizon and realization](hyp:h_mu_memLp) and [propensity errors in
`L²(P_X)` at every horizon and realization](hyp:h_e_memLp), if [the
outcome-regression error converges to zero in `L²(P_X)` in
probability](hyp:h_mu_rate) and [the propensity error converges to zero in
`L²(P_X)` in probability](hyp:h_e_rate), then [the `L²(P_Z)` norm of the AIPW
score difference between the estimated and true nuisance converges to zero in
probability](goal).

This headline continuity result uses the almost-sure Lipschitz bound, the
covariate pushforward identity, and a truncation argument for the
residual-weighted propensity error. -/
theorem aipw_score_diff_isLittleOp_one
    (S : BackdoorEstimationSystem P γ) {ε : ℝ}
    (h_overlap : S.StrictOverlap ε)
    (hA : S.toPOBackdoorSystem.Assumptions)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_yd2 : ∀ d : Bool, Integrable
      (fun ω => (S.toPOBackdoorSystem.YofD d ω) ^ 2) P.μ)
    (η_hat : ℕ → P.Ω → NuisanceVec γ)
    (h_in_H : ∀ n ω, η_hat n ω ∈ H_ε_aeL2 S ε)
    (h_mu_memLp :
      ∀ n ω a, MemLp
        (fun x => (η_hat n ω).μ_fn a x - S.μ_val a x) 2 S.P_X)
    (h_e_memLp :
      ∀ n ω, MemLp
        (fun x => (η_hat n ω).e_fn x - S.e_val x) 2 S.P_X)
    (h_mu_rate :
      ∀ a : Bool,
        IsLittleOp
          (fun n ω =>
            (eLpNorm (fun x => (η_hat n ω).μ_fn a x - S.μ_val a x) 2 S.P_X).toReal)
          (fun _ => (1 : ℝ)) P.μ)
    (h_e_rate :
      IsLittleOp
        (fun n ω =>
          (eLpNorm (fun x => (η_hat n ω).e_fn x - S.e_val x) 2 S.P_X).toReal)
        (fun _ => (1 : ℝ)) P.μ) :
    IsLittleOp
      (fun n ω =>
        (eLpNorm (fun z =>
            aipwMomentFunctional (η_hat n ω) z S.θ₀ -
              aipwMomentFunctional S.η₀ z S.θ₀) 2 S.P_Z).toReal)
      (fun _ => (1 : ℝ)) P.μ := by
  exact aipw_score_diff_isLittleOp_one_truncation_core
    S h_overlap hA h_y2 h_yd2 η_hat h_in_H h_mu_memLp h_e_memLp h_mu_rate h_e_rate

/-- Fix [strict overlap](hyp:h_overlap), [the back-door assumptions](hyp:hA),
and [finite outcome second moments](hyp:h_y2,h_yd2). If [the true nuisance is
in the good set](hyp:hη₀_mem), [the fitted nuisance and its regression and
propensity errors satisfy the good-set conditions almost surely at each
horizon](hyp:h_in_H,h_mu_memLp,h_e_memLp), and [the two nuisance errors vanish
in probability](hyp:h_mu_rate,h_e_rate), then [the AIPW score difference
vanishes in L² in probability](goal). -/
theorem aipw_score_diff_isLittleOp_one_of_ae
    (S : BackdoorEstimationSystem P γ) {ε : ℝ}
    (hη₀_mem : S.η₀ ∈ H_ε_aeL2 S ε)
    (h_overlap : S.StrictOverlap ε)
    (hA : S.toPOBackdoorSystem.Assumptions)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_yd2 : ∀ d : Bool, Integrable
      (fun ω => (S.toPOBackdoorSystem.YofD d ω) ^ 2) P.μ)
    (η_hat : ℕ → P.Ω → NuisanceVec γ)
    (h_in_H : ∀ n, ∀ᵐ ω ∂P.μ, η_hat n ω ∈ H_ε_aeL2 S ε)
    (h_mu_memLp : ∀ n, ∀ᵐ ω ∂P.μ, ∀ a,
      MemLp (fun x => (η_hat n ω).μ_fn a x - S.μ_val a x) 2 S.P_X)
    (h_e_memLp : ∀ n, ∀ᵐ ω ∂P.μ,
      MemLp (fun x => (η_hat n ω).e_fn x - S.e_val x) 2 S.P_X)
    (h_mu_rate : ∀ a : Bool, IsLittleOp
      (fun n ω => (eLpNorm
        (fun x => (η_hat n ω).μ_fn a x - S.μ_val a x) 2 S.P_X).toReal)
      (fun _ => (1 : ℝ)) P.μ)
    (h_e_rate : IsLittleOp
      (fun n ω => (eLpNorm
        (fun x => (η_hat n ω).e_fn x - S.e_val x) 2 S.P_X).toReal)
      (fun _ => (1 : ℝ)) P.μ) :
    IsLittleOp
      (fun n ω => (eLpNorm (fun z =>
        aipwMomentFunctional (η_hat n ω) z S.θ₀ -
          aipwMomentFunctional S.η₀ z S.θ₀) 2 S.P_Z).toReal)
      (fun _ => (1 : ℝ)) P.μ := by
  classical
  let good : ℕ → P.Ω → Prop := fun n ω =>
    η_hat n ω ∈ H_ε_aeL2 S ε ∧
      (∀ a, MemLp (fun x => (η_hat n ω).μ_fn a x - S.μ_val a x) 2 S.P_X) ∧
      MemLp (fun x => (η_hat n ω).e_fn x - S.e_val x) 2 S.P_X
  let η_safe : ℕ → P.Ω → NuisanceVec γ := fun n ω =>
    if good n ω then η_hat n ω else S.η₀
  have hgood : ∀ n, ∀ᵐ ω ∂P.μ, good n ω := by
    intro n
    filter_upwards [h_in_H n, h_mu_memLp n, h_e_memLp n] with ω hH hμ he
    exact ⟨hH, hμ, he⟩
  have hsafe_eq : ∀ n, ∀ᵐ ω ∂P.μ, η_safe n ω = η_hat n ω := by
    intro n
    filter_upwards [hgood n] with ω hω
    simp [η_safe, hω]
  have hsafe_H : ∀ n ω, η_safe n ω ∈ H_ε_aeL2 S ε := by
    intro n ω
    by_cases hω : good n ω
    · simpa [η_safe, hω] using hω.1
    · simpa [η_safe, hω] using hη₀_mem
  have hsafe_μ : ∀ n ω a, MemLp
      (fun x => (η_safe n ω).μ_fn a x - S.μ_val a x) 2 S.P_X := by
    intro n ω a
    by_cases hω : good n ω
    · simpa [η_safe, hω] using hω.2.1 a
    · simpa [η_safe, hω, BackdoorEstimationSystem.η₀]
  have hsafe_e : ∀ n ω, MemLp
      (fun x => (η_safe n ω).e_fn x - S.e_val x) 2 S.P_X := by
    intro n ω
    by_cases hω : good n ω
    · simpa [η_safe, hω] using hω.2.2
    · simpa [η_safe, hω, BackdoorEstimationSystem.η₀]
  have transfer : ∀ {f g : ℕ → P.Ω → ℝ} {r : ℕ → ℝ},
      (∀ n, ∀ᵐ ω ∂P.μ, f n ω = g n ω) →
      IsLittleOp g r P.μ → IsLittleOp f r P.μ := by
    intro f g r hfg hg
    apply IsLittleOp.of_eq_on_asymptotic ?_ hg
    have hzero : (fun n => P.μ {ω | f n ω ≠ g n ω}) = fun _ => 0 := by
      funext n
      exact ae_iff.mp (hfg n)
    rw [hzero]
    exact tendsto_const_nhds
  have hsafe_mu_rate : ∀ a : Bool, IsLittleOp
      (fun n ω => (eLpNorm
        (fun x => (η_safe n ω).μ_fn a x - S.μ_val a x) 2 S.P_X).toReal)
      (fun _ => (1 : ℝ)) P.μ := by
    intro a
    apply transfer ?_ (h_mu_rate a)
    intro n
    filter_upwards [hsafe_eq n] with ω hω
    simp [hω]
  have hsafe_e_rate : IsLittleOp
      (fun n ω => (eLpNorm
        (fun x => (η_safe n ω).e_fn x - S.e_val x) 2 S.P_X).toReal)
      (fun _ => (1 : ℝ)) P.μ := by
    apply transfer ?_ h_e_rate
    intro n
    filter_upwards [hsafe_eq n] with ω hω
    simp [hω]
  have hsafe_score := aipw_score_diff_isLittleOp_one S h_overlap hA h_y2 h_yd2
    η_safe hsafe_H hsafe_μ hsafe_e hsafe_mu_rate hsafe_e_rate
  apply transfer ?_ hsafe_score
  intro n
  filter_upwards [hsafe_eq n] with ω hω
  simp [hω]

end BackdoorEstimationSystem

end ATE
end Estimation
end Causalean
