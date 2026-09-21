/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Estimation.ATE.Score.AIPWScoreL2.Pointwise

/-!
Supplies the analytic integrability and norm-transport layer for AIPW score
continuity. It proves square-integrability of the true residual envelope,
transports L² norms along the covariate projection, and proves the truncation
estimate `residual_mul_e_error_isLittleOp_one`. The final score-level
stochastic-order theorem is in `Truncation`.
-/

@[expose] public section

namespace Causalean
namespace Estimation
namespace ATE

open MeasureTheory ProbabilityTheory Filter Topology Causalean.PO Causalean.Stat

namespace BackdoorEstimationSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
/-! ## L²(P_Z) continuity of the AIPW score on `H_ε_aeL2`

Squaring the pointwise bound and integrating against `P_Z`, with
`(a+b+c)² ≤ 3(a²+b²+c²)`, yields:

    ‖m_AIPW(η, ·, θ₀) − m_AIPW(η₀, ·, θ₀)‖²_{L²(P_Z)}
      ≤ 3 · K_AIPW(ε)² · (
          ‖Δμ(1, ·)‖²_{L²(P_X)}
          + ‖Δμ(0, ·)‖²_{L²(P_X)}
          + ∫ (|y−μ_val(1,x)| + |y−μ_val(0,x)|)² · |Δe(x)|² dP_Z).

The first two summands are direct L²(P_X) norms.  The last summand is bounded
above using `|Δe| ≤ 1` (since `ε ≤ ê, e ≤ 1−ε` ⇒ `|Δe| ≤ 1−2ε ≤ 1`):

    ∫ (|y−μ_val(1,x)| + |y−μ_val(0,x)|)² · |Δe|² dP_Z
      ≤ ∫ (|y−μ_val(1,x)| + |y−μ_val(0,x)|)² · |Δe| dP_Z.

We package this as a non-asymptotic bound; the asymptotic `o_p(1)` form is
the headline corollary below. -/

/-- For a [potential-outcome system](hyp:P) with a standard-Borel sample space and finite probability measure, a [measurable covariate space](hyp:γ), and [a back-door estimation system](hyp:S), the [squared residual-sum integrand](goal) maps each observed triple to the square of the sum of the absolute residuals from its two true outcome regressions.

This is the "tilted" cross-term integrand `(|y − μ_val(1, x)| + |y − μ_val(0, x)|)²`, viewed as a fixed L¹(P_Z) function (witness via `h_y2 + h_yd2 + Cauchy–Schwarz`). -/
noncomputable def YMuVal_residual_sq
    (S : BackdoorEstimationSystem P γ) : (γ × Bool × ℝ) → ℝ :=
  fun z => (|projY z - S.μ_val true (projX z)|
            + |projY z - S.μ_val false (projX z)|) ^ 2

/-- For [an average-treatment-effect backdoor estimation system](hyp:P,γ,S), [the sum of the
absolute treated and control outcome residuals is measurable under the observed-data law](goal). -/
lemma yMuVal_residual_meas
    (S : BackdoorEstimationSystem P γ) :
    Measurable (fun z : γ × Bool × ℝ =>
      |projY z - S.μ_val true (projX z)|
        + |projY z - S.μ_val false (projX z)|) := by
  have hx : Measurable (fun z : γ × Bool × ℝ => projX z) := by
    simpa [projX] using (measurable_fst : Measurable (fun z : γ × Bool × ℝ => z.1))
  have hy : Measurable (fun z : γ × Bool × ℝ => projY z) := by
    simpa [projY] using
      (measurable_snd.snd : Measurable (fun z : γ × Bool × ℝ => z.2.2))
  have hμt : Measurable (fun z : γ × Bool × ℝ => S.μ_val true (projX z)) :=
    (S.μ_meas true).comp hx
  have hμf : Measurable (fun z : γ × Bool × ℝ => S.μ_val false (projX z)) :=
    (S.μ_meas false).comp hx
  exact (continuous_abs.measurable.comp (hy.sub hμt)).add
    (continuous_abs.measurable.comp (hy.sub hμf))

/-- The cross-term integrand is `P_Z`-integrable, with the bound coming from
`(a+b)² ≤ 2(a² + b²)` and `Y² ∈ L¹(P_Z)`, `μ_val(d, X)² ∈ L¹(P_Z)`. -/
theorem yMuVal_residual_sq_integrable
    (S : BackdoorEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.Assumptions)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_yd2 : ∀ d : Bool, Integrable
      (fun ω => (S.toPOBackdoorSystem.YofD d ω) ^ 2) P.μ) :
    Integrable (S.YMuVal_residual_sq) S.P_Z := by
  have _ := hA
  have hY_L2 : MemLp S.toPOBackdoorSystem.factualY 2 P.μ := by
    exact (memLp_two_iff_integrable_sq
      S.toPOBackdoorSystem.measurable_factualY.aestronglyMeasurable).2 h_y2
  have hμ_L2 :
      ∀ d : Bool, MemLp
        (fun ω => S.μ_val d (S.toPOBackdoorSystem.factualX ω)) 2 P.μ := by
    intro d
    have hYd_L2 : MemLp (S.toPOBackdoorSystem.YofD d) 2 P.μ := by
      exact (memLp_two_iff_integrable_sq
        (S.toPOBackdoorSystem.measurable_YofD d).aestronglyMeasurable).2 (h_yd2 d)
    have hcond_L2 :
        MemLp (P.μ[S.toPOBackdoorSystem.YofD d |
          S.toPOBackdoorSystem.sigmaX]) 2 P.μ :=
      hYd_L2.condExp one_le_two
    exact hcond_L2.ae_eq (S.μ_compat hA d)
  let g : γ × Bool × ℝ → ℝ :=
    fun z => |projY z - S.μ_val true (projX z)|
      + |projY z - S.μ_val false (projX z)|
  have hg_meas : Measurable g := by
    have hx : Measurable (fun z : γ × Bool × ℝ => projX z) := by
      simpa [projX] using (measurable_fst : Measurable (fun z : γ × Bool × ℝ => z.1))
    have hy : Measurable (fun z : γ × Bool × ℝ => projY z) := by
      simpa [projY] using
        (measurable_snd.snd : Measurable (fun z : γ × Bool × ℝ => z.2.2))
    have hμt : Measurable (fun z : γ × Bool × ℝ => S.μ_val true (projX z)) :=
      (S.μ_meas true).comp hx
    have hμf : Measurable (fun z : γ × Bool × ℝ => S.μ_val false (projX z)) :=
      (S.μ_meas false).comp hx
    exact (continuous_abs.measurable.comp (hy.sub hμt)).add
      (continuous_abs.measurable.comp (hy.sub hμf))
  have hg_comp_L2 : MemLp (fun ω => g (S.factualZ ω)) 2 P.μ := by
    have ht : MemLp
        (fun ω => S.toPOBackdoorSystem.factualY ω -
          S.μ_val true (S.toPOBackdoorSystem.factualX ω)) 2 P.μ :=
      hY_L2.sub (hμ_L2 true)
    have hf : MemLp
        (fun ω => S.toPOBackdoorSystem.factualY ω -
          S.μ_val false (S.toPOBackdoorSystem.factualX ω)) 2 P.μ :=
      hY_L2.sub (hμ_L2 false)
    exact ht.norm.add hf.norm
  have hg_L2 : MemLp g 2 S.P_Z := by
    rw [BackdoorEstimationSystem.P_Z]
    exact (memLp_map_measure_iff hg_meas.aestronglyMeasurable
      S.measurable_factualZ.aemeasurable).2 hg_comp_L2
  exact hg_L2.integrable_sq

/-- For [an average-treatment-effect backdoor estimation system](hyp:P,γ,S), if [its causal
assumptions hold](hyp:hA), [the factual outcome has an integrable square](hyp:h_y2), and [each
potential outcome has an integrable square](hyp:h_yd2), then [the sum of the absolute treated and
control residuals is square-integrable under the observed-data law](goal). -/
lemma yMuVal_residual_memLp
    (S : BackdoorEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.Assumptions)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_yd2 : ∀ d : Bool, Integrable
      (fun ω => (S.toPOBackdoorSystem.YofD d ω) ^ 2) P.μ) :
    MemLp (fun z : γ × Bool × ℝ =>
      |projY z - S.μ_val true (projX z)|
        + |projY z - S.μ_val false (projX z)|) 2 S.P_Z := by
  exact (memLp_two_iff_integrable_sq (yMuVal_residual_meas S).aestronglyMeasurable).2
    (yMuVal_residual_sq_integrable S hA h_y2 h_yd2)

/-- For [an average-treatment-effect backdoor estimation system and a covariate function](hyp:P,γ,S,f),
if [the function is almost-everywhere strongly measurable under the covariate law](hyp:hf), then
[its second-order norm after projection from observed data equals its norm under the covariate law](goal). -/
lemma eLpNorm_comp_projX_eq
    (S : BackdoorEstimationSystem P γ) {f : γ → ℝ}
    (hf : AEStronglyMeasurable f S.P_X) :
    eLpNorm (fun z : γ × Bool × ℝ => f (projX z)) 2 S.P_Z =
      eLpNorm f 2 S.P_X := by
  have hfmap :
      AEStronglyMeasurable f (S.P_Z.map (fun z : γ × Bool × ℝ => z.1)) := by
    simpa [BackdoorEstimationSystem.P_Z_map_projX_eq_P_X S] using hf
  rw [← BackdoorEstimationSystem.P_Z_map_projX_eq_P_X S]
  simpa [projX, Function.comp_def] using
    (MeasureTheory.eLpNorm_map_measure
      (μ := S.P_Z) (f := fun z : γ × Bool × ℝ => z.1) (g := f)
      (p := 2) hfmap measurable_fst.aemeasurable).symm

set_option maxHeartbeats 800000 in
-- The projection-norm rewrite otherwise times out while unfolding the `P_Z.map projX = P_X` bridge.
private lemma e_error_eLpNorm_projX_toReal_eq
    (S : BackdoorEstimationSystem P γ) (η : NuisanceVec γ)
    (hηe : MemLp (fun x => η.e_fn x - S.e_val x) 2 S.P_X) :
    (eLpNorm (fun z : γ × Bool × ℝ => η.e_fn (projX z) - S.e_val (projX z))
        2 S.P_Z).toReal =
      (eLpNorm (fun x => η.e_fn x - S.e_val x) 2 S.P_X).toReal := by
  exact congrArg ENNReal.toReal
    (eLpNorm_comp_projX_eq (S := S)
      (f := fun x => η.e_fn x - S.e_val x) hηe.aestronglyMeasurable)

set_option maxHeartbeats 800000 in
-- The truncation proof combines several `MemLp` and `lpNorm` coercion steps;
-- the default budget is too small.
/-- For [a potential-outcome system and covariate space](hyp:P,γ), [a back-door estimation
system](hyp:S), [an overlap level](hyp:ε), [strict overlap](hyp:h_overlap), [the back-door
identification assumptions](hyp:hA), [square-integrability of the factual outcome](hyp:h_y2),
[square-integrability of both potential outcomes](hyp:h_yd2), [a sequence of nuisance
estimates](hyp:η_hat), [membership of every estimate in the overlap-restricted nuisance
class](hyp:h_in_H), [square-integrability of every propensity error](hyp:h_e_memLp), and [a
vanishing propensity-error rate](hyp:h_e_rate), [the product of the outcome-residual envelope
and the propensity error also vanishes in probability](goal). -/
theorem residual_mul_e_error_isLittleOp_one
    (S : BackdoorEstimationSystem P γ) {ε : ℝ}
    (h_overlap : S.StrictOverlap ε)
    (hA : S.toPOBackdoorSystem.Assumptions)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_yd2 : ∀ d : Bool, Integrable
      (fun ω => (S.toPOBackdoorSystem.YofD d ω) ^ 2) P.μ)
    (η_hat : ℕ → P.Ω → NuisanceVec γ)
    (h_in_H : ∀ n ω, η_hat n ω ∈ H_ε_aeL2 S ε)
    (h_e_memLp :
      ∀ n ω, MemLp
        (fun x => (η_hat n ω).e_fn x - S.e_val x) 2 S.P_X)
    (h_e_rate :
      IsLittleOp
        (fun n ω =>
          (eLpNorm (fun x => (η_hat n ω).e_fn x - S.e_val x) 2 S.P_X).toReal)
        (fun _ => (1 : ℝ)) P.μ) :
    IsLittleOp
      (fun n ω =>
        (eLpNorm (fun z : γ × Bool × ℝ =>
          (|projY z - S.μ_val true (projX z)|
            + |projY z - S.μ_val false (projX z)|) *
            |(η_hat n ω).e_fn (projX z) - S.e_val (projX z)|) 2 S.P_Z).toReal)
      (fun _ => (1 : ℝ)) P.μ := by
  classical
  rcases h_overlap with ⟨hε_pos, _hε_half, _hprop⟩
  haveI : IsProbabilityMeasure S.P_Z := by
    unfold BackdoorEstimationSystem.P_Z
    exact Measure.isProbabilityMeasure_map S.measurable_factualZ.aemeasurable
  let R : (γ × Bool × ℝ) → ℝ := fun z =>
    |projY z - S.μ_val true (projX z)|
      + |projY z - S.μ_val false (projX z)|
  let deZ : ℕ → P.Ω → (γ × Bool × ℝ) → ℝ := fun n ω z =>
    (η_hat n ω).e_fn (projX z) - S.e_val (projX z)
  have hR_meas : Measurable R := by
    simpa [R] using yMuVal_residual_meas S
  have hR_nonneg : ∀ z, 0 ≤ R z := by
    intro z
    dsimp [R]
    positivity
  have hR_memLp : MemLp R 2 S.P_Z := by
    simpa [R] using yMuVal_residual_memLp S hA h_y2 h_yd2
  have hdeZ_memLp : ∀ n ω, MemLp (deZ n ω) 2 S.P_Z := by
    intro n ω
    have hmap : MemLp (fun x => (η_hat n ω).e_fn x - S.e_val x)
        2 (S.P_Z.map (fun z : γ × Bool × ℝ => z.1)) := by
      simpa [BackdoorEstimationSystem.P_Z_map_projX_eq_P_X S] using h_e_memLp n ω
    have hproj_ae : AEMeasurable (fun z : γ × Bool × ℝ => z.1) S.P_Z :=
      measurable_fst.aemeasurable
    exact (memLp_map_measure_iff hmap.aestronglyMeasurable hproj_ae).1 hmap
  have hdeZ_meas : ∀ n ω, Measurable (deZ n ω) := by
    intro n ω
    have hx : Measurable (fun z : γ × Bool × ℝ => projX z) := by
      simpa [projX] using
        (measurable_fst : Measurable (fun z : γ × Bool × ℝ => z.1))
    exact ((η_hat n ω).e_meas.comp hx).sub (S.e_meas.comp hx)
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
  intro δ hδ
  rw [ENNReal.tendsto_nhds_zero]
  intro κ hκ
  by_cases hκtop : κ = ⊤
  · filter_upwards with n
    simp [hκtop]
  have hκpos : 0 < κ.toReal := ENNReal.toReal_pos (ne_of_gt hκ) hκtop
  let τ : ℝ := δ / 4
  have hτpos : 0 < τ := by
    dsimp [τ]
    linarith
  obtain ⟨M, hMpos, hMtail⟩ :=
    hR_memLp.eLpNorm_indicator_norm_ge_pos_le hR_meas.stronglyMeasurable hτpos
  let tail : (γ × Bool × ℝ) → ℝ := {z | M ≤ R z}.indicator R
  have htail_set : MeasurableSet {z : γ × Bool × ℝ | M ≤ R z} := by
    exact measurableSet_le measurable_const hR_meas
  have htail_memLp : MemLp tail 2 S.P_Z := by
    exact hR_memLp.indicator htail_set
  have htail_norm_le : (eLpNorm tail 2 S.P_Z).toReal ≤ τ := by
    have hle : eLpNorm tail 2 S.P_Z ≤ ENNReal.ofReal τ := by
      have htail_eq :
          tail = ({z : γ × Bool × ℝ | M ≤ ‖R z‖₊}.indicator R) := by
        funext z
        by_cases hz : M ≤ R z
        · simp [tail, hz, Real.norm_eq_abs, abs_of_nonneg (hR_nonneg z)]
        · simp [tail, hz, Real.norm_eq_abs, abs_of_nonneg (hR_nonneg z)]
      simpa [htail_eq] using hMtail
    calc
      (eLpNorm tail 2 S.P_Z).toReal ≤ (ENNReal.ofReal τ).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
      _ = τ := ENNReal.toReal_ofReal hτpos.le
  have hcross_bound : ∀ n ω,
      (eLpNorm (fun z : γ × Bool × ℝ => R z * |deZ n ω z|) 2 S.P_Z).toReal
        ≤ M * (eLpNorm (deZ n ω) 2 S.P_Z).toReal + τ := by
    intro n ω
    let bulk : (γ × Bool × ℝ) → ℝ := fun z => M * |deZ n ω z|
    let upper : (γ × Bool × ℝ) → ℝ := fun z => bulk z + tail z
    have hbulk_memLp : MemLp bulk 2 S.P_Z := by
      have h_abs : MemLp (fun z => |deZ n ω z|) 2 S.P_Z := by
        simpa [Real.norm_eq_abs] using (hdeZ_memLp n ω).norm
      exact h_abs.const_smul M
    have hupper_memLp : MemLp upper 2 S.P_Z := by
      exact hbulk_memLp.add htail_memLp
    have hpoint : ∀ᵐ z ∂S.P_Z, ‖R z * |deZ n ω z|‖ ≤ upper z := by
      filter_upwards [hdeZ_bdd n ω] with z hdez_le
      have hRz : 0 ≤ R z := hR_nonneg z
      have hdez_nonneg : 0 ≤ |deZ n ω z| := abs_nonneg _
      by_cases hz : M ≤ R z
      · have htail_eq : tail z = R z := by simp [tail, hz]
        have hmain : ‖R z * |deZ n ω z|‖ ≤ R z := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hRz, abs_of_nonneg hdez_nonneg]
          exact mul_le_of_le_one_right hRz hdez_le
        dsimp [upper, bulk]
        rw [htail_eq]
        have hbulk_nonneg : 0 ≤ M * |deZ n ω z| :=
          mul_nonneg hMpos.le hdez_nonneg
        exact hmain.trans (by nlinarith)
      · have htail_eq : tail z = 0 := by simp [tail, hz]
        have hR_lt_M : R z ≤ M := by
          exact le_of_not_ge hz
        have hmain : ‖R z * |deZ n ω z|‖ ≤ M * |deZ n ω z| := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hRz, abs_of_nonneg hdez_nonneg]
          exact mul_le_mul_of_nonneg_right hR_lt_M hdez_nonneg
        dsimp [upper, bulk]
        rw [htail_eq]
        simpa using hmain
    have hmono :
        (eLpNorm (fun z : γ × Bool × ℝ => R z * |deZ n ω z|) 2 S.P_Z).toReal
          ≤ (eLpNorm upper 2 S.P_Z).toReal := by
      exact ENNReal.toReal_mono hupper_memLp.eLpNorm_ne_top
        (eLpNorm_mono_ae_real hpoint)
    have htri :
        lpNorm upper 2 S.P_Z ≤ lpNorm bulk 2 S.P_Z + lpNorm tail 2 S.P_Z := by
      exact lpNorm_add_le (f := bulk) (g := tail)
        (μ := S.P_Z) hbulk_memLp
        (by norm_num : (1 : ENNReal) ≤ 2)
    have hbulk_norm :
        lpNorm bulk 2 S.P_Z =
          M * (eLpNorm (deZ n ω) 2 S.P_Z).toReal := by
      change lpNorm (M • (fun z : γ × Bool × ℝ => |deZ n ω z|)) 2 S.P_Z =
        M * (eLpNorm (deZ n ω) 2 S.P_Z).toReal
      rw [lpNorm_const_smul]
      rw [lpNorm_fun_abs (hdeZ_memLp n ω).aestronglyMeasurable]
      rw [← toReal_eLpNorm (hdeZ_memLp n ω).aestronglyMeasurable]
      have hcoef : (↑‖M‖₊ : ℝ) = M := by
        simp [Real.norm_eq_abs, abs_of_pos hMpos]
      rw [hcoef]
    have htail_lp :
        lpNorm tail 2 S.P_Z = (eLpNorm tail 2 S.P_Z).toReal := by
      rw [toReal_eLpNorm htail_memLp.aestronglyMeasurable]
    calc
      (eLpNorm (fun z : γ × Bool × ℝ => R z * |deZ n ω z|) 2 S.P_Z).toReal
          ≤ (eLpNorm upper 2 S.P_Z).toReal := hmono
      _ = lpNorm upper 2 S.P_Z := by
            rw [toReal_eLpNorm hupper_memLp.aestronglyMeasurable]
      _ ≤ lpNorm bulk 2 S.P_Z + lpNorm tail 2 S.P_Z := htri
      _ = M * (eLpNorm (deZ n ω) 2 S.P_Z).toReal +
          (eLpNorm tail 2 S.P_Z).toReal := by rw [hbulk_norm, htail_lp]
      _ ≤ M * (eLpNorm (deZ n ω) 2 S.P_Z).toReal + τ :=
        add_le_add_right htail_norm_le (M * (eLpNorm (deZ n ω) 2 S.P_Z).toReal)
  have hsmall := (ENNReal.tendsto_nhds_zero.mp
    (h_e_rate (δ / (2 * M)) (by positivity))) κ hκ
  filter_upwards [hsmall] with n hn
  refine (measure_mono ?_).trans hn
  intro ω hω
  have hnorm_nonneg :
      0 ≤ (eLpNorm (fun z : γ × Bool × ℝ => R z * |deZ n ω z|) 2 S.P_Z).toReal :=
    ENNReal.toReal_nonneg
  have hnorm_large :
      δ ≤ (eLpNorm (fun z : γ × Bool × ℝ => R z * |deZ n ω z|) 2 S.P_Z).toReal := by
    simpa [R, deZ, abs_of_nonneg hnorm_nonneg] using hω
  have hde_large : δ / (2 * M) ≤ (eLpNorm (deZ n ω) 2 S.P_Z).toReal := by
    have hb := hcross_bound n ω
    by_contra hnot
    have hle : (eLpNorm (deZ n ω) 2 S.P_Z).toReal ≤ δ / (2 * M) :=
      (lt_of_not_ge hnot).le
    have hprod_le :
        M * (eLpNorm (deZ n ω) 2 S.P_Z).toReal ≤ δ / 2 := by
      calc
        M * (eLpNorm (deZ n ω) 2 S.P_Z).toReal
            ≤ M * (δ / (2 * M)) := mul_le_mul_of_nonneg_left hle hMpos.le
        _ = δ / 2 := by field_simp [hMpos.ne']
    have hcross_le : (eLpNorm (fun z : γ × Bool × ℝ => R z * |deZ n ω z|)
        2 S.P_Z).toReal ≤ δ / 2 + τ := by
      exact hb.trans (add_le_add hprod_le le_rfl)
    dsimp [τ] at hcross_le
    nlinarith [hnorm_large]
  have heq_norm :
      (eLpNorm (deZ n ω) 2 S.P_Z).toReal =
        (eLpNorm (fun x => (η_hat n ω).e_fn x - S.e_val x) 2 S.P_X).toReal := by
    simpa [deZ] using e_error_eLpNorm_projX_toReal_eq S (η_hat n ω) (h_e_memLp n ω)
  have hde_large_X :
      δ / (2 * M) ≤
        (eLpNorm (fun x => (η_hat n ω).e_fn x - S.e_val x) 2 S.P_X).toReal := by
    simpa [heq_norm] using hde_large
  have hde_nonneg :
      0 ≤ (eLpNorm (fun x => (η_hat n ω).e_fn x - S.e_val x) 2 S.P_X).toReal :=
    ENNReal.toReal_nonneg
  simpa [abs_of_nonneg hde_nonneg] using hde_large_X

end BackdoorEstimationSystem

end ATE
end Estimation
end Causalean
