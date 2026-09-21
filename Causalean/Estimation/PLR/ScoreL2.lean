/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Partially linear score L²(P_Z) continuity

Constructs the `o_p(1)` score-difference rate that
`Estimation/PLR/DML.lean`'s `plr_oneStepOracleDML_isAsymLinear` supplies to the abstract
Chernozhukov engine.  Writing `z = (x, d, y)`, `ℓ̂ = (η̂ n ω).lFn`,
`m̂ = (η̂ n ω).mFn`, `ℓ₀ = ℓ_val`, `m₀ = m_val`, `Δℓ = ℓ₀ − ℓ̂`, `Δm = m₀ − m̂`,
`v₀ = d − m₀`, and `A = y − ℓ₀ − θ₀·v₀`, the Robinson partialling-out score
difference factors as

    ψ(η̂, z, θ₀) − ψ(η₀, z, θ₀)
      = A·Δm + Δℓ·v₀ + Δℓ·Δm − θ₀·Δm·v₀ − θ₀·Δm²,

a pure `ring` identity. Hölder's inequality bounds each product in L² by the
product of its two L⁴ norms. The true residual factors `A` and `v₀` have fixed
finite L⁴ norms, while the nuisance errors `Δℓ` and `Δm` converge to zero in L⁴;
an almost-sure L⁴ envelope controls the quadratic nuisance products. Transporting
the nuisance norms to `P_X` through the projection bridge
`eLpNorm_comp_projX`, and assembling with the `IsLittleOp` sum/scalar
combinators yields the headline

    `‖ψ(η̂(n,ω), ·, θ₀) − ψ(η₀, ·, θ₀)‖_{L²(P_Z)} = o_p(1)`,

mirroring `Estimation/ATE/Score/AIPWScoreL2.lean`'s
`aipw_score_diff_isLittleOp_one`.
-/

module
public import Causalean.Estimation.PLR.Setup
public import Causalean.Stat.Limit.Convergence
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! # Partially linear score L²(P_Z) `o_p(1)` continuity

This file provides the standalone lemma `plr_score_diff_isLittleOp_one`, which
discharges the score-difference `o_p(1)` hypothesis of the partially linear DML
asymptotic-linearity theorem from L⁴ moment conditions on the truth residuals,
almost-sure L⁴ envelopes for the nuisance errors, and the two individual
L⁴(P_X) nuisance rates. -/

public section

namespace Causalean
namespace Estimation
namespace PLR

open MeasureTheory ProbabilityTheory Causalean.PO Causalean.Estimation.OrthogonalMoments
open Causalean.Stat

namespace PLRSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ] [IsFiniteMeasure P.μ]

/-! ## Projection bridge `L²(P_Z)` ↔ `L²(P_X)` -/

/-- The L²-seminorm of a covariate function lifted to the observation triple
equals its L²-seminorm on the covariate marginal: for measurable `g : γ → ℝ`,
`‖fun z ↦ g(z.1)‖_{L²(P_Z)} = ‖g‖_{L²(P_X)}`.  Both sides equal the L²-seminorm
of the pullback `g ∘ X` against `μ`, since `(X, D, Y)` has covariate component
`X`. -/
private lemma eLpNorm_comp_projX
    (S : PLRSystem P γ) {g : γ → ℝ} (hg : Measurable g) {p : ENNReal} :
    eLpNorm (fun z : γ × ℝ × ℝ => g z.1) p S.P_Z = eLpNorm g p S.P_X := by
  have hX_ae : AEMeasurable S.factualX P.μ := S.measurable_factualX.aemeasurable
  have hZ_ae : AEMeasurable S.factualZ P.μ := S.measurable_factualZ.aemeasurable
  -- RHS: pull `g` along `X`.
  rw [P_X, eLpNorm_map_measure hg.aestronglyMeasurable hX_ae]
  -- LHS: pull `(fun z ↦ g z.1)` along `Z`, then collapse `(Z ω).1 = X ω`.
  rw [P_Z, eLpNorm_map_measure (g := fun z : γ × ℝ × ℝ => g z.1)
    ((hg.comp measurable_fst).aestronglyMeasurable) hZ_ae]
  have hcomp : ((fun z : γ × ℝ × ℝ => g z.1) ∘ S.factualZ) = g ∘ S.factualX := by
    funext ω; rfl
  rw [hcomp]

/-! ## Bounded-times-L² product bound -/

/-- If `|φ| ≤ C` `P_Z`-a.e. with `C ≥ 0` and `f ∈ L²(P_Z)`, then
`‖φ·f‖_{L²(P_Z)} ≤ C·‖f‖_{L²(P_Z)}`.  The L∞·L² Hölder step specialised to a
uniformly bounded multiplier, proved by the a.e. monotonicity of the
L²-seminorm against `C·|f|` and the scalar pull-out. -/
private lemma lpNorm_bdd_mul_le
    {μ : Measure (γ × ℝ × ℝ)} {φ f : (γ × ℝ × ℝ) → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hφ_meas : AEStronglyMeasurable φ μ) (hf : MemLp f 2 μ)
    (hφ : ∀ᵐ z ∂μ, |φ z| ≤ C) :
    lpNorm (fun z => φ z * f z) 2 μ ≤ C * lpNorm f 2 μ := by
  have hprod_meas : AEStronglyMeasurable (fun z => φ z * f z) μ :=
    hφ_meas.mul hf.aestronglyMeasurable
  have hCabs_memLp : MemLp (fun z => C * |f z|) 2 μ := by
    have hg : MemLp (fun z => |f z|) 2 μ := by
      simpa [Real.norm_eq_abs] using hf.norm
    exact hg.const_smul C
  have hmono :
      eLpNorm (fun z => φ z * f z) 2 μ ≤ eLpNorm (fun z => C * |f z|) 2 μ := by
    refine eLpNorm_mono_ae_real ?_
    filter_upwards [hφ] with z hz
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right hz (abs_nonneg _)
  have hCabs_norm :
      lpNorm (fun z => C * |f z|) 2 μ = C * lpNorm f 2 μ := by
    have heq : (fun z => C * |f z|) = C • (fun z => |f z|) := by
      funext z; simp [smul_eq_mul]
    rw [heq, lpNorm_const_smul, lpNorm_fun_abs hf.aestronglyMeasurable]
    have hcoef : (↑‖C‖₊ : ℝ) = C := by
      simp [Real.norm_eq_abs, abs_of_nonneg hC]
    rw [hcoef]
  calc
    lpNorm (fun z => φ z * f z) 2 μ
        = (eLpNorm (fun z => φ z * f z) 2 μ).toReal := by
          rw [toReal_eLpNorm hprod_meas]
    _ ≤ (eLpNorm (fun z => C * |f z|) 2 μ).toReal :=
          ENNReal.toReal_mono hCabs_memLp.eLpNorm_ne_top hmono
    _ = lpNorm (fun z => C * |f z|) 2 μ := by
          rw [toReal_eLpNorm hCabs_memLp.aestronglyMeasurable]
    _ = C * lpNorm f 2 μ := hCabs_norm

/-- The Robinson partialling-out score difference expands into the five-term
Neyman-orthogonal form `A·Δm + Δℓ·v₀ + Δℓ·Δm − θ₀·Δm·v₀ − θ₀·Δm²`, a pure
algebraic identity in the observation coordinates. -/
private lemma score_diff_expand
    (S : PLRSystem P γ) (η : PLRNuisance γ) (z : γ × ℝ × ℝ) :
    plrMomentFunctional η z S.θ₀ - plrMomentFunctional S.η₀ z S.θ₀
      = (z.2.2 - S.lVal z.1 - S.θ₀ * (z.2.1 - S.mVal z.1)) *
          (S.mVal z.1 - η.mFn z.1)
        + (S.lVal z.1 - η.lFn z.1) * (z.2.1 - S.mVal z.1)
        + (S.lVal z.1 - η.lFn z.1) * (S.mVal z.1 - η.mFn z.1)
        - S.θ₀ * (S.mVal z.1 - η.mFn z.1) * (z.2.1 - S.mVal z.1)
        - S.θ₀ * (S.mVal z.1 - η.mFn z.1) ^ 2 := by
  simp only [plrMomentFunctional, plrResidual, η₀]
  ring

set_option maxHeartbeats 400000 in
-- The per-`(n, ω)` envelope assembly (five `MemLp`/`lpNorm` coercion steps plus
-- the projection-bridge rewrites) exceeds the default heartbeat budget.
open Filter in
/-- Per-`(n, ω)` quantitative bound feeding `plr_score_diff_isLittleOp_one`: the
real L²(P_Z)-seminorm of the partially linear score difference is dominated by a
constant multiple of the sum of the two regression-error L²(P_X) magnitudes,
via the five-term Neyman-orthogonal expansion and the bounded-times-L² product
estimate. -/
private theorem plr_score_diff_abs_le
    (S : PLRSystem P γ)
    (η_hat : ℕ → P.Ω → PLRNuisance γ) (n : ℕ) (ω : P.Ω)
    {Ca Cv Cm : ℝ} (hCa : 0 ≤ Ca) (hCv : 0 ≤ Cv) (hCm : 0 ≤ Cm)
    (Cconst : ℝ)
    (rateL rateM : ℕ → P.Ω → ℝ)
    (hrateL : rateL = fun n ω =>
      (eLpNorm (fun x => (η_hat n ω).lFn x - S.lVal x) 2 S.P_X).toReal)
    (hrateM : rateM = fun n ω =>
      (eLpNorm (fun x => (η_hat n ω).mFn x - S.mVal x) 2 S.P_X).toReal)
    (hrateL_nonneg : ∀ n ω, 0 ≤ rateL n ω)
    (hrateM_nonneg : ∀ n ω, 0 ≤ rateM n ω)
    (hCconst : Cconst = Ca + Cv + Cm + |S.θ₀| * Cv + |S.θ₀| * Cm)
    (hA_bdd : ∀ᵐ z ∂S.P_Z,
      |z.2.2 - S.lVal z.1 - S.θ₀ * (z.2.1 - S.mVal z.1)| ≤ Ca)
    (hv_bdd : ∀ᵐ z ∂S.P_Z, |z.2.1 - S.mVal z.1| ≤ Cv)
    (hΔm_bdd : ∀ n ω x, |S.mVal x - (η_hat n ω).mFn x| ≤ Cm)
    (hΔl_memLp : ∀ n ω, MemLp (fun x => (η_hat n ω).lFn x - S.lVal x) 2 S.P_X)
    (hΔm_memLp : ∀ n ω, MemLp (fun x => (η_hat n ω).mFn x - S.mVal x) 2 S.P_X) :
    |(eLpNorm (fun z => plrMomentFunctional (η_hat n ω) z S.θ₀
                      - plrMomentFunctional S.η₀ z S.θ₀) 2 S.P_Z).toReal|
      ≤ (Cconst + 1) * |rateL n ω + rateM n ω| := by
  -- Abbreviations: the score difference and the two regression errors lifted to
  -- the observation triple.
  set sc : (γ × ℝ × ℝ) → ℝ := fun z =>
    plrMomentFunctional (η_hat n ω) z S.θ₀ - plrMomentFunctional S.η₀ z S.θ₀ with hsc
  set dL : (γ × ℝ × ℝ) → ℝ := fun z => S.lVal z.1 - (η_hat n ω).lFn z.1 with hdL
  set dM : (γ × ℝ × ℝ) → ℝ := fun z => S.mVal z.1 - (η_hat n ω).mFn z.1 with hdM
  -- The two collecting coefficients.
  set cL : ℝ := Cv + Cm with hcL
  set cM : ℝ := Ca + |S.θ₀| * Cv + |S.θ₀| * Cm with hcM
  have hcL_nonneg : 0 ≤ cL := by rw [hcL]; linarith
  have hcM_nonneg : 0 ≤ cM := by
    rw [hcM]; positivity
  -- Measurability of the lifted errors.
  have hdL_meas : Measurable dL :=
    (S.lVal_meas.comp measurable_fst).sub
      ((η_hat n ω).lMeas.comp measurable_fst)
  have hdM_meas : Measurable dM :=
    (S.mVal_meas.comp measurable_fst).sub
      ((η_hat n ω).mMeas.comp measurable_fst)
  -- The lifted errors are in `L²(P_Z)` (pull back the `P_X` membership).
  -- One bridge each: `‖dL‖_{L²(P_Z)} = ‖Δℓ‖_{L²(P_X)}`, `‖dM‖_{L²(P_Z)} = ‖Δm‖_{L²(P_X)}`.
  have hdL_eLp : eLpNorm dL 2 S.P_Z
      = eLpNorm (fun x => (η_hat n ω).lFn x - S.lVal x) 2 S.P_X := by
    have h := eLpNorm_comp_projX S (g := fun x => S.lVal x - (η_hat n ω).lFn x)
      (S.lVal_meas.sub (η_hat n ω).lMeas) (p := 2)
    rw [show dL = (fun z : γ × ℝ × ℝ => (fun x => S.lVal x - (η_hat n ω).lFn x) z.1)
        from rfl, h, ← eLpNorm_neg (fun x => (η_hat n ω).lFn x - S.lVal x)]
    congr 1; funext x; simp only [Pi.neg_apply, neg_sub]
  have hdM_eLp : eLpNorm dM 2 S.P_Z
      = eLpNorm (fun x => (η_hat n ω).mFn x - S.mVal x) 2 S.P_X := by
    have h := eLpNorm_comp_projX S (g := fun x => S.mVal x - (η_hat n ω).mFn x)
      (S.mVal_meas.sub (η_hat n ω).mMeas) (p := 2)
    rw [show dM = (fun z : γ × ℝ × ℝ => (fun x => S.mVal x - (η_hat n ω).mFn x) z.1)
        from rfl, h, ← eLpNorm_neg (fun x => (η_hat n ω).mFn x - S.mVal x)]
    congr 1; funext x; simp only [Pi.neg_apply, neg_sub]
  have hdL_memLp : MemLp dL 2 S.P_Z :=
    ⟨hdL_meas.aestronglyMeasurable, by rw [hdL_eLp]; exact (hΔl_memLp n ω).2⟩
  have hdM_memLp : MemLp dM 2 S.P_Z :=
    ⟨hdM_meas.aestronglyMeasurable, by rw [hdM_eLp]; exact (hΔm_memLp n ω).2⟩
  -- The two rate identities: `‖dL‖_{L²(P_Z)} = rateL`, `‖dM‖_{L²(P_Z)} = rateM`.
  have hdL_rate : lpNorm dL 2 S.P_Z = rateL n ω := by
    rw [← toReal_eLpNorm hdL_meas.aestronglyMeasurable, hdL_eLp, hrateL]
  have hdM_rate : lpNorm dM 2 S.P_Z = rateM n ω := by
    rw [← toReal_eLpNorm hdM_meas.aestronglyMeasurable, hdM_eLp, hrateM]
  -- The dominating envelope `upper z = cL·|dL z| + cM·|dM z|`.
  set upper : (γ × ℝ × ℝ) → ℝ := fun z => cL * |dL z| + cM * |dM z| with hupper
  have hupper_memLp : MemLp upper 2 S.P_Z := by
    have hL : MemLp (fun z => cL * |dL z|) 2 S.P_Z := by
      have hg : MemLp (fun z => |dL z|) 2 S.P_Z := by
        simpa [Real.norm_eq_abs] using hdL_memLp.norm
      exact hg.const_smul cL
    have hM : MemLp (fun z => cM * |dM z|) 2 S.P_Z := by
      have hg : MemLp (fun z => |dM z|) 2 S.P_Z := by
        simpa [Real.norm_eq_abs] using hdM_memLp.norm
      exact hg.const_smul cM
    exact hL.add hM
  -- Pointwise (a.e.) domination of the score by the envelope.
  have hpoint : ∀ᵐ z ∂S.P_Z, ‖sc z‖ ≤ upper z := by
    filter_upwards [hA_bdd, hv_bdd] with z hAz hvz
    have hexp := S.score_diff_expand (η_hat n ω) z
    -- Name the five signed summands.
    set t1 : ℝ := (z.2.2 - S.lVal z.1 - S.θ₀ * (z.2.1 - S.mVal z.1)) * dM z with ht1
    set t2 : ℝ := dL z * (z.2.1 - S.mVal z.1) with ht2
    set t3 : ℝ := dL z * dM z with ht3
    set t4 : ℝ := S.θ₀ * dM z * (z.2.1 - S.mVal z.1) with ht4
    set t5 : ℝ := S.θ₀ * dM z ^ 2 with ht5
    -- Per-term bounds against the rate factors.
    have hb1 : |t1| ≤ Ca * |dM z| := by
      rw [ht1, abs_mul]; exact mul_le_mul_of_nonneg_right hAz (abs_nonneg _)
    have hb2 : |t2| ≤ Cv * |dL z| := by
      rw [ht2, abs_mul, mul_comm]; exact mul_le_mul_of_nonneg_right hvz (abs_nonneg _)
    have hb3 : |t3| ≤ Cm * |dL z| := by
      rw [ht3, abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (by simpa [dM] using hΔm_bdd n ω z.1)
        (abs_nonneg _)
    have hb4 : |t4| ≤ |S.θ₀| * Cv * |dM z| := by
      rw [ht4, abs_mul, abs_mul]
      calc |S.θ₀| * |dM z| * |z.2.1 - S.mVal z.1|
          ≤ |S.θ₀| * |dM z| * Cv := mul_le_mul_of_nonneg_left hvz (by positivity)
        _ = |S.θ₀| * Cv * |dM z| := by ring
    have hb5 : |t5| ≤ |S.θ₀| * Cm * |dM z| := by
      rw [ht5, abs_mul, pow_two, abs_mul]
      calc |S.θ₀| * (|dM z| * |dM z|)
          ≤ |S.θ₀| * (Cm * |dM z|) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right (by simpa [dM] using hΔm_bdd n ω z.1)
                (abs_nonneg _)) (abs_nonneg _)
        _ = |S.θ₀| * Cm * |dM z| := by ring
    -- Triangle inequality on the five-term sum, then collect.
    have htri : |t1 + t2 + t3 - t4 - t5| ≤ |t1| + |t2| + |t3| + |t4| + |t5| := by
      calc |t1 + t2 + t3 - t4 - t5|
          ≤ |t1 + t2 + t3 - t4| + |t5| := by
            simpa [sub_eq_add_neg, abs_neg] using abs_add_le (t1 + t2 + t3 - t4) (-t5)
        _ ≤ (|t1 + t2 + t3| + |t4|) + |t5| := by
            gcongr
            simpa [sub_eq_add_neg, abs_neg] using abs_add_le (t1 + t2 + t3) (-t4)
        _ ≤ ((|t1 + t2| + |t3|) + |t4|) + |t5| := by gcongr; exact abs_add_le _ _
        _ ≤ (((|t1| + |t2|) + |t3|) + |t4|) + |t5| := by gcongr; exact abs_add_le _ _
        _ = |t1| + |t2| + |t3| + |t4| + |t5| := by ring
    rw [Real.norm_eq_abs, show sc z = t1 + t2 + t3 - t4 - t5 from hexp]
    calc |t1 + t2 + t3 - t4 - t5|
        ≤ |t1| + |t2| + |t3| + |t4| + |t5| := htri
      _ ≤ Ca * |dM z| + Cv * |dL z| + Cm * |dL z|
            + |S.θ₀| * Cv * |dM z| + |S.θ₀| * Cm * |dM z| := by
            have := hb1; have := hb2; have := hb3; have := hb4; have := hb5
            gcongr
      _ = upper z := by rw [hupper, hcL, hcM]; ring
  -- Measurability of the score difference.
  have hsc_meas : Measurable sc := by
    rw [hsc]
    exact (measurable_plrMomentFunctional (η_hat n ω) S.θ₀).sub
      (measurable_plrMomentFunctional S.η₀ S.θ₀)
  -- Assemble: `‖sc‖₂ ≤ ‖upper‖₂ ≤ cL·rateL + cM·rateM ≤ (Cconst+1)·(rateL+rateM)`.
  have hsc_le_upper : lpNorm sc 2 S.P_Z ≤ lpNorm upper 2 S.P_Z := by
    rw [← toReal_eLpNorm hsc_meas.aestronglyMeasurable,
      ← toReal_eLpNorm hupper_memLp.aestronglyMeasurable]
    refine ENNReal.toReal_mono hupper_memLp.eLpNorm_ne_top ?_
    exact eLpNorm_mono_ae_real (by filter_upwards [hpoint] with z hz using hz)
  -- Triangle + scalar pull-out on the two-term envelope.
  have hupper_split :
      lpNorm upper 2 S.P_Z ≤ cL * lpNorm dL 2 S.P_Z + cM * lpNorm dM 2 S.P_Z := by
    have hL_memLp : MemLp (fun z => cL * |dL z|) 2 S.P_Z := by
      have hg : MemLp (fun z => |dL z|) 2 S.P_Z := by
        simpa [Real.norm_eq_abs] using hdL_memLp.norm
      exact hg.const_smul cL
    have htri :
        lpNorm upper 2 S.P_Z ≤
          lpNorm (fun z => cL * |dL z|) 2 S.P_Z +
            lpNorm (fun z => cM * |dM z|) 2 S.P_Z := by
      have hupper_eq :
          upper = (fun z => cL * |dL z|) + (fun z => cM * |dM z|) := by
        funext z; simp [upper, Pi.add_apply]
      rw [hupper_eq]
      exact lpNorm_add_le hL_memLp (by norm_num : (1 : ENNReal) ≤ 2)
    have hnormL :
        lpNorm (fun z => cL * |dL z|) 2 S.P_Z = cL * lpNorm dL 2 S.P_Z := by
      have heq : (fun z => cL * |dL z|) = cL • (fun z => |dL z|) := by
        funext z; simp [smul_eq_mul]
      rw [heq, lpNorm_const_smul, lpNorm_fun_abs hdL_memLp.aestronglyMeasurable]
      have : (↑‖cL‖₊ : ℝ) = cL := by simp [Real.norm_eq_abs, abs_of_nonneg hcL_nonneg]
      rw [this]
    have hnormM :
        lpNorm (fun z => cM * |dM z|) 2 S.P_Z = cM * lpNorm dM 2 S.P_Z := by
      have heq : (fun z => cM * |dM z|) = cM • (fun z => |dM z|) := by
        funext z; simp [smul_eq_mul]
      rw [heq, lpNorm_const_smul, lpNorm_fun_abs hdM_memLp.aestronglyMeasurable]
      have : (↑‖cM‖₊ : ℝ) = cM := by simp [Real.norm_eq_abs, abs_of_nonneg hcM_nonneg]
      rw [this]
    rw [hnormL, hnormM] at htri
    exact htri
  -- Final numeric chain.
  have hfinal :
      (eLpNorm sc 2 S.P_Z).toReal ≤ (Cconst + 1) * (rateL n ω + rateM n ω) := by
    have h1 : (eLpNorm sc 2 S.P_Z).toReal = lpNorm sc 2 S.P_Z :=
      toReal_eLpNorm hsc_meas.aestronglyMeasurable
    rw [h1]
    have hcL_le : cL ≤ Cconst + 1 := by rw [hcL, hCconst]; nlinarith [hcM_nonneg]
    have hcM_le : cM ≤ Cconst + 1 := by rw [hcM, hCconst]; nlinarith [hcL_nonneg, hcL]
    calc
      lpNorm sc 2 S.P_Z ≤ lpNorm upper 2 S.P_Z := hsc_le_upper
      _ ≤ cL * lpNorm dL 2 S.P_Z + cM * lpNorm dM 2 S.P_Z := hupper_split
      _ = cL * rateL n ω + cM * rateM n ω := by rw [hdL_rate, hdM_rate]
      _ ≤ (Cconst + 1) * rateL n ω + (Cconst + 1) * rateM n ω := by
            gcongr <;> [exact hrateL_nonneg n ω; exact hrateM_nonneg n ω]
      _ = (Cconst + 1) * (rateL n ω + rateM n ω) := by ring
  rw [abs_of_nonneg ENNReal.toReal_nonneg,
    abs_of_nonneg (add_nonneg (hrateL_nonneg n ω) (hrateM_nonneg n ω))]
  exact hfinal

/-- Hölder's inequality in the `L⁴ × L⁴ → L²` form used by the PLR moment
argument. -/
private lemma eLpNorm_mul_four_toReal_le
    {X : Type*} [MeasurableSpace X] {ν : Measure X} {f g : X → ℝ}
    (hf : MemLp f 4 ν) (hg : MemLp g 4 ν) :
    (eLpNorm (f * g) 2 ν).toReal ≤
      (eLpNorm f 4 ν).toReal * (eLpNorm g 4 ν).toReal := by
  let : ENNReal.HolderTriple 4 4 2 := by
    change ENNReal.HolderTriple ((4 : NNReal) : ENNReal) ((4 : NNReal) : ENNReal)
      ((2 : NNReal) : ENNReal)
    exact NNReal.HolderTriple.coe_ennreal (by norm_num)
      (by constructor <;> norm_num : NNReal.HolderTriple 4 4 2)
  have hle : eLpNorm (f * g) 2 ν ≤ eLpNorm f 4 ν * eLpNorm g 4 ν := by
    simpa [smul_eq_mul] using
      (eLpNorm_smul_le_mul_eLpNorm (p := 4) (q := 4) (r := 2) hg.1 hf.1)
  rw [← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (by finiteness) hle

/-- Minkowski's inequality after converting finite `eLpNorm`s to real values. -/
private lemma eLpNorm_add_two_toReal_le
    {X : Type*} [MeasurableSpace X] {ν : Measure X} {f g : X → ℝ}
    (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    (eLpNorm (f + g) 2 ν).toReal ≤
      (eLpNorm f 2 ν).toReal + (eLpNorm g 2 ν).toReal := by
  have hle := eLpNorm_add_le hf.1 hg.1 (by norm_num : (1 : ENNReal) ≤ 2)
  rw [← ENNReal.toReal_add hf.eLpNorm_ne_top hg.eLpNorm_ne_top]
  exact ENNReal.toReal_mono (by finiteness) hle

open Filter in
/-- Almost-sure domination by a positive constant times an `oₚ(1)` sequence
preserves `oₚ(1)`. -/
private theorem IsLittleOp.of_ae_abs_le_const_mul_one
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Xn Yn : ℕ → Ω → ℝ} {C : ℝ} (hC : 0 < C)
    (hY : IsLittleOp Yn (fun _ => (1 : ℝ)) μ)
    (hbound : ∀ n, ∀ᵐ ω ∂μ, |Xn n ω| ≤ C * |Yn n ω|) :
    IsLittleOp Xn (fun _ => (1 : ℝ)) μ := by
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  have hYevent := (ENNReal.tendsto_nhds_zero.mp
    (hY (ε / C) (div_pos hε hC))) δ hδ
  filter_upwards [hYevent] with n hn
  refine (measure_mono_ae ?_).trans hn
  filter_upwards [hbound n] with ω hdom
  intro hω
  by_contra hnot
  simp only [mul_one] at hω hnot
  have hYlt : |Yn n ω| < (ε / C) := lt_of_not_ge hnot
  have hprod : C * |Yn n ω| < ε := by
    calc
      C * |Yn n ω| < C * (ε / C) := mul_lt_mul_of_pos_left hYlt hC
      _ = ε := by field_simp [hC.ne']
  exact (not_le_of_gt (hdom.trans_lt hprod)) hω

/-- **Score-difference L²(P_Z) `o_p(1)` under moment conditions.** For [a PLR
system](hyp:S) and [estimated nuisance sequence](hyp:η_hat), suppose the [true
outcome residual](hyp:hA_memLp) and [true treatment residual](hyp:hv_memLp) have
finite fourth moments. Suppose the [two nuisance errors have finite fourth
moments](hyp:hΔl_memLp,hΔm_memLp), their [fourth-moment norms are uniformly bounded
by a nonnegative constant](hyp:B,hB,hΔl_bound,hΔm_bound), and those [norms converge
to zero in probability](hyp:h_l_rate,h_m_rate). Then
[the L²(P_Z)-seminorm of the Robinson partialling-out score difference between the
estimated and the true nuisance is itself $o_p(1)$](goal).

This is a finite-fourth-moment sufficient condition for the score-continuity
consequence used in the PLR argument, not a formalization of the full uniform
model-class package in CCDDHNR Assumption 4.1. Hölder bounds the product terms,
and the uniform `L⁴` envelope makes the quadratic nuisance products comparable
to the individual errors. -/
theorem plr_score_diff_isLittleOp_one
    (S : PLRSystem P γ)
    (η_hat : ℕ → P.Ω → PLRNuisance γ)
    (hA_memLp : MemLp
      (fun z => z.2.2 - S.lVal z.1 - S.θ₀ * (z.2.1 - S.mVal z.1)) 4 S.P_Z)
    (hv_memLp : MemLp (fun z => z.2.1 - S.mVal z.1) 4 S.P_Z)
    {B : ℝ} (hB : 0 ≤ B)
    (hΔl_memLp : ∀ n ω, MemLp (fun x => (η_hat n ω).lFn x - S.lVal x) 4 S.P_X)
    (hΔm_memLp : ∀ n ω, MemLp (fun x => (η_hat n ω).mFn x - S.mVal x) 4 S.P_X)
    (hΔl_bound : ∀ n, ∀ᵐ ω ∂P.μ,
      (eLpNorm (fun x => (η_hat n ω).lFn x - S.lVal x) 4 S.P_X).toReal ≤ B)
    (hΔm_bound : ∀ n, ∀ᵐ ω ∂P.μ,
      (eLpNorm (fun x => (η_hat n ω).mFn x - S.mVal x) 4 S.P_X).toReal ≤ B)
    (h_l_rate :
      IsLittleOp
        (fun n ω =>
          (eLpNorm (fun x => (η_hat n ω).lFn x - S.lVal x) 4 S.P_X).toReal)
        (fun _ => (1 : ℝ)) P.μ)
    (h_m_rate :
      IsLittleOp
        (fun n ω =>
          (eLpNorm (fun x => (η_hat n ω).mFn x - S.mVal x) 4 S.P_X).toReal)
        (fun _ => (1 : ℝ)) P.μ) :
    IsLittleOp
      (fun n ω => (eLpNorm (fun z => plrMomentFunctional (η_hat n ω) z S.θ₀
                                   - plrMomentFunctional S.η₀ z S.θ₀) 2 S.P_Z).toReal)
      (fun _ => (1 : ℝ)) P.μ := by
  classical
  set rateL : ℕ → P.Ω → ℝ := fun n ω =>
    (eLpNorm (fun x => (η_hat n ω).lFn x - S.lVal x) 4 S.P_X).toReal with hrateL
  set rateM : ℕ → P.Ω → ℝ := fun n ω =>
    (eLpNorm (fun x => (η_hat n ω).mFn x - S.mVal x) 4 S.P_X).toReal with hrateM
  have hrateL_nonneg : ∀ n ω, 0 ≤ rateL n ω := fun _ _ => ENNReal.toReal_nonneg
  have hrateM_nonneg : ∀ n ω, 0 ≤ rateM n ω := fun _ _ => ENNReal.toReal_nonneg
  have hsum_rate :
      IsLittleOp (fun n ω => rateL n ω + rateM n ω) (fun _ => (1 : ℝ)) P.μ :=
    IsLittleOp.add_one h_l_rate h_m_rate
  let A4 := (eLpNorm
    (fun z => z.2.2 - S.lVal z.1 - S.θ₀ * (z.2.1 - S.mVal z.1)) 4 S.P_Z).toReal
  let V4 := (eLpNorm (fun z => z.2.1 - S.mVal z.1) 4 S.P_Z).toReal
  set Cconst : ℝ := A4 + V4 + B + |S.θ₀| * (V4 + B) with hCconst
  have hCconst_pos : 0 < Cconst + 1 := by
    have : 0 ≤ Cconst := by rw [hCconst]; positivity
    linarith
  refine IsLittleOp.of_ae_abs_le_const_mul_one (C := Cconst + 1)
    hCconst_pos hsum_rate ?_
  intro n
  filter_upwards [hΔl_bound n, hΔm_bound n] with ω hL hM
  let A : (γ × ℝ × ℝ) → ℝ := fun z =>
    z.2.2 - S.lVal z.1 - S.θ₀ * (z.2.1 - S.mVal z.1)
  let v : (γ × ℝ × ℝ) → ℝ := fun z => z.2.1 - S.mVal z.1
  let dL : (γ × ℝ × ℝ) → ℝ := fun z => S.lVal z.1 - (η_hat n ω).lFn z.1
  let dM : (γ × ℝ × ℝ) → ℝ := fun z => S.mVal z.1 - (η_hat n ω).mFn z.1
  let t1 := A * dM
  let t2 := dL * v
  let t3 := dL * dM
  let t4 := S.θ₀ • (dM * v)
  let t5 := S.θ₀ • (dM * dM)
  have hdL4 : MemLp dL 4 S.P_Z := by
    have heq := eLpNorm_comp_projX S
      (g := fun x => S.lVal x - (η_hat n ω).lFn x)
      (S.lVal_meas.sub (η_hat n ω).lMeas) (p := 4)
    refine ⟨((S.lVal_meas.sub (η_hat n ω).lMeas).comp measurable_fst).aestronglyMeasurable, ?_⟩
    rw [show dL = fun z => S.lVal z.1 - (η_hat n ω).lFn z.1 from rfl, heq]
    have hfun : (fun x => S.lVal x - (η_hat n ω).lFn x) =
        -(fun x => (η_hat n ω).lFn x - S.lVal x) := by
      funext x
      simp
    rw [hfun, eLpNorm_neg]
    exact (hΔl_memLp n ω).2
  have hdM4 : MemLp dM 4 S.P_Z := by
    have heq := eLpNorm_comp_projX S
      (g := fun x => S.mVal x - (η_hat n ω).mFn x)
      (S.mVal_meas.sub (η_hat n ω).mMeas) (p := 4)
    refine ⟨((S.mVal_meas.sub (η_hat n ω).mMeas).comp measurable_fst).aestronglyMeasurable, ?_⟩
    rw [show dM = fun z => S.mVal z.1 - (η_hat n ω).mFn z.1 from rfl, heq]
    have hfun : (fun x => S.mVal x - (η_hat n ω).mFn x) =
        -(fun x => (η_hat n ω).mFn x - S.mVal x) := by
      funext x
      simp
    rw [hfun, eLpNorm_neg]
    exact (hΔm_memLp n ω).2
  have hdL_norm : (eLpNorm dL 4 S.P_Z).toReal = rateL n ω := by
    change (eLpNorm (fun z => S.lVal z.1 - (η_hat n ω).lFn z.1) 4 S.P_Z).toReal = _
    have heq := eLpNorm_comp_projX S
      (g := fun x => S.lVal x - (η_hat n ω).lFn x)
      (S.lVal_meas.sub (η_hat n ω).lMeas) (p := 4)
    rw [heq]
    have hneg : (fun x => S.lVal x - (η_hat n ω).lFn x) =
        -(fun x => (η_hat n ω).lFn x - S.lVal x) := by
      funext x
      simp
    rw [hneg, eLpNorm_neg]
  have hdM_norm : (eLpNorm dM 4 S.P_Z).toReal = rateM n ω := by
    change (eLpNorm (fun z => S.mVal z.1 - (η_hat n ω).mFn z.1) 4 S.P_Z).toReal = _
    have heq := eLpNorm_comp_projX S
      (g := fun x => S.mVal x - (η_hat n ω).mFn x)
      (S.mVal_meas.sub (η_hat n ω).mMeas) (p := 4)
    rw [heq]
    have hneg : (fun x => S.mVal x - (η_hat n ω).mFn x) =
        -(fun x => (η_hat n ω).mFn x - S.mVal x) := by
      funext x
      simp
    rw [hneg, eLpNorm_neg]
  have ht1 := eLpNorm_mul_four_toReal_le hA_memLp hdM4
  have ht2 := eLpNorm_mul_four_toReal_le hdL4 hv_memLp
  have ht3 := eLpNorm_mul_four_toReal_le hdL4 hdM4
  have ht4base := eLpNorm_mul_four_toReal_le hdM4 hv_memLp
  have ht5base := eLpNorm_mul_four_toReal_le hdM4 hdM4
  let : ENNReal.HolderTriple 4 4 2 := by
    change ENNReal.HolderTriple ((4 : NNReal) : ENNReal) ((4 : NNReal) : ENNReal)
      ((2 : NNReal) : ENNReal)
    exact NNReal.HolderTriple.coe_ennreal (by norm_num)
      (by constructor <;> norm_num : NNReal.HolderTriple 4 4 2)
  have ht1mem : MemLp t1 2 S.P_Z := hdM4.mul hA_memLp
  have ht2mem : MemLp t2 2 S.P_Z := hv_memLp.mul hdL4
  have ht3mem : MemLp t3 2 S.P_Z := hdM4.mul hdL4
  have ht4mem : MemLp t4 2 S.P_Z := (hv_memLp.mul hdM4).const_smul S.θ₀
  have ht5mem : MemLp t5 2 S.P_Z := (hdM4.mul hdM4).const_smul S.θ₀
  have hscore_eq :
      (fun z => plrMomentFunctional (η_hat n ω) z S.θ₀ -
        plrMomentFunctional S.η₀ z S.θ₀) = t1 + t2 + t3 + (-t4) + (-t5) := by
    funext z
    rw [S.score_diff_expand]
    simp [t1, t2, t3, t4, t5, A, v, dL, dM, Pi.add_apply, Pi.neg_apply,
      Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have htri :
      (eLpNorm (t1 + t2 + t3 + (-t4) + (-t5)) 2 S.P_Z).toReal ≤
        (eLpNorm t1 2 S.P_Z).toReal + (eLpNorm t2 2 S.P_Z).toReal +
        (eLpNorm t3 2 S.P_Z).toReal + (eLpNorm t4 2 S.P_Z).toReal +
        (eLpNorm t5 2 S.P_Z).toReal := by
    calc
      _ ≤ (eLpNorm (t1 + t2 + t3 + (-t4)) 2 S.P_Z).toReal +
          (eLpNorm (-t5) 2 S.P_Z).toReal :=
        eLpNorm_add_two_toReal_le
          (((ht1mem.add ht2mem).add ht3mem).add ht4mem.neg) ht5mem.neg
      _ ≤ ((eLpNorm (t1 + t2 + t3) 2 S.P_Z).toReal +
          (eLpNorm (-t4) 2 S.P_Z).toReal) + (eLpNorm (-t5) 2 S.P_Z).toReal := by
        gcongr
        exact eLpNorm_add_two_toReal_le ((ht1mem.add ht2mem).add ht3mem) ht4mem.neg
      _ ≤ (((eLpNorm (t1 + t2) 2 S.P_Z).toReal + (eLpNorm t3 2 S.P_Z).toReal) +
          (eLpNorm (-t4) 2 S.P_Z).toReal) + (eLpNorm (-t5) 2 S.P_Z).toReal := by
        gcongr
        exact eLpNorm_add_two_toReal_le (ht1mem.add ht2mem) ht3mem
      _ ≤ ((((eLpNorm t1 2 S.P_Z).toReal + (eLpNorm t2 2 S.P_Z).toReal) +
          (eLpNorm t3 2 S.P_Z).toReal) + (eLpNorm (-t4) 2 S.P_Z).toReal) +
          (eLpNorm (-t5) 2 S.P_Z).toReal := by
        gcongr
        exact eLpNorm_add_two_toReal_le ht1mem ht2mem
      _ = _ := by simp only [eLpNorm_neg]
  rw [hscore_eq, abs_of_nonneg ENNReal.toReal_nonneg,
    abs_of_nonneg (add_nonneg (hrateL_nonneg n ω) (hrateM_nonneg n ω))]
  calc
    _ ≤ (eLpNorm t1 2 S.P_Z).toReal + (eLpNorm t2 2 S.P_Z).toReal +
        (eLpNorm t3 2 S.P_Z).toReal + (eLpNorm t4 2 S.P_Z).toReal +
        (eLpNorm t5 2 S.P_Z).toReal := htri
    _ ≤ A4 * rateM n ω + rateL n ω * V4 + rateL n ω * rateM n ω +
        |S.θ₀| * (rateM n ω * V4) + |S.θ₀| * (rateM n ω * rateM n ω) := by
      rw [show (eLpNorm t4 2 S.P_Z).toReal =
          |S.θ₀| * (eLpNorm (dM * v) 2 S.P_Z).toReal by
            simp [t4, eLpNorm_const_smul, Real.norm_eq_abs, ENNReal.toReal_mul],
        show (eLpNorm t5 2 S.P_Z).toReal =
          |S.θ₀| * (eLpNorm (dM * dM) 2 S.P_Z).toReal by
            simp [t5, eLpNorm_const_smul, Real.norm_eq_abs, ENNReal.toReal_mul]]
      have ht1' : (eLpNorm t1 2 S.P_Z).toReal ≤ A4 * rateM n ω := by
        simpa [t1, A, A4, hdM_norm] using ht1
      have ht2' : (eLpNorm t2 2 S.P_Z).toReal ≤ rateL n ω * V4 := by
        simpa [t2, v, V4, hdL_norm] using ht2
      have ht3' : (eLpNorm t3 2 S.P_Z).toReal ≤ rateL n ω * rateM n ω := by
        simpa [t3, hdL_norm, hdM_norm] using ht3
      have ht4' : |S.θ₀| * (eLpNorm (dM * v) 2 S.P_Z).toReal ≤
          |S.θ₀| * (rateM n ω * V4) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        simpa [v, V4, hdM_norm] using ht4base
      have ht5' : |S.θ₀| * (eLpNorm (dM * dM) 2 S.P_Z).toReal ≤
          |S.θ₀| * (rateM n ω * rateM n ω) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        simpa [hdM_norm] using ht5base
      exact add_le_add (add_le_add (add_le_add (add_le_add ht1' ht2') ht3') ht4') ht5'
    _ ≤ (Cconst + 1) * (rateL n ω + rateM n ω) := by
      change rateL n ω ≤ B at hL
      change rateM n ω ≤ B at hM
      have hLM : rateL n ω * rateM n ω ≤ B * rateL n ω := by
        nlinarith [hrateL_nonneg n ω]
      have hMM : rateM n ω * rateM n ω ≤ B * rateM n ω := by
        nlinarith [hrateM_nonneg n ω]
      calc
        _ ≤ A4 * rateM n ω + rateL n ω * V4 + B * rateL n ω +
            |S.θ₀| * (rateM n ω * V4) + |S.θ₀| * (B * rateM n ω) := by
          gcongr
        _ ≤ (A4 * rateM n ω + rateL n ω * V4 + B * rateL n ω +
              |S.θ₀| * (rateM n ω * V4) + |S.θ₀| * (B * rateM n ω)) +
            (A4 * rateL n ω + V4 * rateM n ω + B * rateM n ω +
              |S.θ₀| * (V4 * rateL n ω) + |S.θ₀| * (B * rateL n ω) +
              rateL n ω + rateM n ω) := by
          apply le_add_of_nonneg_right
          dsimp [A4, V4]
          positivity
        _ = (Cconst + 1) * (rateL n ω + rateM n ω) := by
          rw [hCconst]
          ring

end PLRSystem

end PLR
end Estimation
end Causalean
