/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Conditional bias of the DR pseudo-outcome — `prop:est-cate-dr-bias-identity`

The σ(X)-conditional bias identity used in the proof of Kennedy (2023),
Theorem 2:

    μ[ φ_η(Z) − φ_0(Z) | σ(X) ]
      =ᵐ  ∑_{a ∈ {true, false}}
            ((η.e_fn − η₀.e_fn) (η.μ_fn a − η₀.μ_fn a) /
              (a · η.e_fn + (1 − a) · (1 − η.e_fn)))(X)

equivalently in value space (`P_X`-a.e.) — the closed-form cross-product
remainder driving the double-robustness corollary
`rem:est-cate-double-robust`.

This file provides:
* `condBias η η₀ x`                — the closed-form value-space bias.
* `measurable_condBias`            — measurability of `condBias`.
* `cond_exp_residual_at_h`         — generalized residual-conditional-expectation
                                     helper (parameterised over an arbitrary
                                     measurable `h : γ → ℝ`).
* `phi_eta_minus_phi₀_cond_exp`    — the σ(X)-conditional bias identity (Ω-form).
* `phi_eta_minus_phi₀_at_x`        — lightweight value-space bridge used by
                                     downstream packaging.
* `condBias_zero_of_propensity_match` — DR corollary (correct propensity).
* `condBias_zero_of_outcome_match`     — DR corollary (correct outcomes).
* `cond_exp_phi_eta_dir_deriv_at_truth_zero` — differentiated orthogonality
                                     statement at the truth.
-/

module
public import Causalean.Estimation.CATE.Core.PseudoOutcome
public import Causalean.Estimation.CATE.Core.PhiEtaDeriv
public import Causalean.Estimation.ATE.Score.MeanZero
public import Causalean.Estimation.ATE.Score.ScorePullout

/-!
Builds the source-space half of the CATE conditional-bias identity. This file
defines the value-space cross-product remainder `condBias`, proves its
measurability, and establishes `phi_eta_minus_phi₀_cond_exp`, the σ(X)-conditional
identity on the original probability space. The value-space transport and
double-robustness consequences are in `ConditionalBias_Part2`.
-/

@[expose] public section

namespace Causalean
namespace Estimation
namespace CATE

open MeasureTheory ProbabilityTheory Filter Topology
  Causalean.PO Causalean.Estimation.ATE

variable {γ : Type*} [MeasurableSpace γ]

/-! ## Closed-form value-space bias -/
/-- For [a measurable covariate space](hyp:γ), [a candidate pair of outcome-regression and propensity-score nuisance functions](hyp:η), [a reference pair of such nuisance functions](hyp:η₀), and [a covariate value](hyp:x), the [closed-form conditional bias of the doubly robust pseudo-outcome contrast](goal) is the sum over the two treatment arms of the product of the candidate-minus-reference propensity error and the corresponding outcome-regression error, divided by the candidate probability of that arm at the covariate value.

It is given by

    condBias η η₀ x
      := ∑_{a ∈ Bool}
           ((η.e_fn x − η₀.e_fn x) (η.μ_fn a x − η₀.μ_fn a x))
             / (if a then η.e_fn x else 1 − η.e_fn x).

The denominator `if a then η.e_fn x else 1 − η.e_fn x` is the LaTeX
`a·π̂(x) + (1−a)·(1−π̂(x))` with `a : Bool`.

Mirrors the right-hand side of `prop:est-cate-dr-bias-identity` in
`doc/basic_concepts/po/estimation/dr_learner_cate.tex`. -/
noncomputable def condBias (η η₀ : NuisanceVec γ) (x : γ) : ℝ :=
  ∑ a : Bool, ((η.e_fn x - η₀.e_fn x) * (η.μ_fn a x - η₀.μ_fn a x)) /
    (if a then η.e_fn x else 1 - η.e_fn x)

/-- `condBias η η₀` is measurable in `x`.

Proof outline: a finite sum over `Bool` of products / quotients of
measurable functions; build it from `η.e_meas`, `η₀.e_meas`,
`η.μ_meas`, `η₀.μ_meas` via `Finset.measurable_sum`,
`Measurable.div`, `Measurable.mul`, `Measurable.sub`. -/
@[fun_prop]
lemma measurable_condBias (η η₀ : NuisanceVec γ) :
    Measurable (fun x : γ => condBias η η₀ x) := by
  unfold condBias
  refine Finset.measurable_sum _ ?_
  intro a _
  cases a
  · have h_num : Measurable (fun x : γ =>
        (η.e_fn x - η₀.e_fn x) * (η.μ_fn false x - η₀.μ_fn false x)) :=
      (η.e_meas.sub η₀.e_meas).mul
        ((η.μ_meas false).sub (η₀.μ_meas false))
    have h_den : Measurable (fun x : γ => 1 - η.e_fn x) :=
      measurable_const.sub η.e_meas
    simpa using h_num.fun_div h_den
  · have h_num : Measurable (fun x : γ =>
        (η.e_fn x - η₀.e_fn x) * (η.μ_fn true x - η₀.μ_fn true x)) :=
      (η.e_meas.sub η₀.e_meas).mul
        ((η.μ_meas true).sub (η₀.μ_meas true))
    simpa using h_num.fun_div η.e_meas

/-! ## Generalized residual-conditional-expectation helper -/

/-- Generalized form of `BackdoorEstimationSystem.cond_exp_residual_zero`
(in `Estimation/ATE/Score/MeanZero.lean`). The original lemma fixes
`h := S.μ_val d` and concludes the residual conditional expectation is
zero; this version allows an arbitrary measurable `h : γ → ℝ` and
exposes the residual

    μ[ 1{D=d}·(Y − h(X)) | σ(X) ]
      =ᵐ  propScore d · (μ_val d (factualX ·) − h (factualX ·)).

Proof outline: decompose
`1{D=d}·(Y − h(X)) = 1{D=d}·Y − 1{D=d}·h(X)`.
The first term has conditional expectation
`propScore d · μ_val d (factualX)` via
`S.toPOBackdoorSystem.conditionalMeanOutcome_backdoor`. The second pulls
`h(factualX)` out of the conditional expectation as it is
σ(X)-measurable via
`MeasureTheory.condExp_mul_of_stronglyMeasurable_left`), giving
`propScore d · h(factualX)`.  Subtract. -/
private lemma cond_exp_residual_at_h
    {P : POSystem} [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    (S : CATEEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.Assumptions) (d : Bool)
    (h : γ → ℝ) (hh_meas : Measurable h)
    (hh_int : Integrable
      (fun ω => h (S.toPOBackdoorSystem.factualX ω) *
        S.toPOBackdoorSystem.dVar.indicator d ω) P.μ) :
    P.μ[fun ω => S.toPOBackdoorSystem.dVar.indicator d ω *
           (S.toPOBackdoorSystem.factualY ω -
             h (S.toPOBackdoorSystem.factualX ω))
        | S.toPOBackdoorSystem.sigmaX]
      =ᵐ[P.μ]
        (fun ω =>
          S.toPOBackdoorSystem.propScore d ω *
            (S.μ_val d (S.toPOBackdoorSystem.factualX ω) -
             h (S.toPOBackdoorSystem.factualX ω))) := by
  have hYind_int : Integrable
      (fun ω => S.toPOBackdoorSystem.factualY ω *
        S.toPOBackdoorSystem.dVar.indicator d ω) P.μ :=
    S.toPOBackdoorSystem.dVar.integrable_mul_indicator d (MeasurableSet.singleton d)
      hA.integrable_factualY
  have hres_eq :
      (fun ω => S.toPOBackdoorSystem.dVar.indicator d ω *
          (S.toPOBackdoorSystem.factualY ω -
            h (S.toPOBackdoorSystem.factualX ω)))
        = (fun ω => S.toPOBackdoorSystem.factualY ω *
            S.toPOBackdoorSystem.dVar.indicator d ω -
          h (S.toPOBackdoorSystem.factualX ω) *
            S.toPOBackdoorSystem.dVar.indicator d ω) := by
    funext ω
    ring
  have hsub :
      P.μ[fun ω => S.toPOBackdoorSystem.factualY ω *
            S.toPOBackdoorSystem.dVar.indicator d ω -
          h (S.toPOBackdoorSystem.factualX ω) *
            S.toPOBackdoorSystem.dVar.indicator d ω |
          S.toPOBackdoorSystem.sigmaX]
        =ᵐ[P.μ]
          P.μ[fun ω => S.toPOBackdoorSystem.factualY ω *
            S.toPOBackdoorSystem.dVar.indicator d ω |
            S.toPOBackdoorSystem.sigmaX]
          - P.μ[fun ω => h (S.toPOBackdoorSystem.factualX ω) *
            S.toPOBackdoorSystem.dVar.indicator d ω |
            S.toPOBackdoorSystem.sigmaX] :=
    MeasureTheory.condExp_sub hYind_int hh_int S.toPOBackdoorSystem.sigmaX
  have hYce :
      P.μ[fun ω => S.toPOBackdoorSystem.factualY ω *
          S.toPOBackdoorSystem.dVar.indicator d ω |
          S.toPOBackdoorSystem.sigmaX]
        =ᵐ[P.μ]
          S.toPOBackdoorSystem.propScore d * S.toPOBackdoorSystem.conditionalMeanOutcome d := by
    have hcate := S.toPOBackdoorSystem.conditionalMeanOutcome_backdoor hA d
    filter_upwards [hcate,
      Causalean.Estimation.ATE.BackdoorEstimationSystem.propScore_ne_zero
        S.toBackdoorEstimationSystem hA d] with ω hcat hneω
    unfold POBackdoorSystem.adjustedCE at hcat
    rw [Pi.mul_apply, hcat]
    field_simp [hneω]
  have hh_sm : StronglyMeasurable[S.toPOBackdoorSystem.sigmaX]
      (fun ω => h (S.toPOBackdoorSystem.factualX ω)) := by
    change StronglyMeasurable[
      MeasurableSpace.comap S.toPOBackdoorSystem.factualX inferInstance]
      (fun ω => h (S.toPOBackdoorSystem.factualX ω))
    exact (hh_meas.comp
      (comap_measurable S.toPOBackdoorSystem.factualX)).stronglyMeasurable
  have hind_int : Integrable (S.toPOBackdoorSystem.dVar.indicator d) P.μ :=
    S.toPOBackdoorSystem.dVar.integrable_indicator d (MeasurableSet.singleton d)
  have hhce :
      P.μ[fun ω => h (S.toPOBackdoorSystem.factualX ω) *
          S.toPOBackdoorSystem.dVar.indicator d ω |
          S.toPOBackdoorSystem.sigmaX]
        =ᵐ[P.μ]
          (fun ω => h (S.toPOBackdoorSystem.factualX ω)) *
            S.toPOBackdoorSystem.propScore d := by
    have hpull := MeasureTheory.condExp_mul_of_stronglyMeasurable_left
      (μ := P.μ) (m := S.toPOBackdoorSystem.sigmaX) hh_sm hh_int hind_int
    simp only [POBackdoorSystem.propScore]
    exact hpull
  rw [hres_eq]
  refine hsub.trans ?_
  filter_upwards [hYce, hhce, S.μ_compat hA d] with ω hY hh hcompat
  have hcate_comp : S.toPOBackdoorSystem.conditionalMeanOutcome d ω =
      S.μ_val d (S.toPOBackdoorSystem.factualX ω) := by
    simpa [POBackdoorSystem.conditionalMeanOutcome] using hcompat
  rw [Pi.sub_apply, hY, hh, Pi.mul_apply, Pi.mul_apply, hcate_comp]
  ring

/-! ## σ(X)-conditional bias identity -/

/-- **σ(X)-conditional bias identity for the DR pseudo-outcome (an ingredient in the proof of
Kennedy (2023), Theorem 2).** Fix a candidate nuisance pair `η`. Under [the back-door identification
assumptions](hyp:hA), if [`η`'s propensity is uniformly bounded in `[ε, 1 − ε]` for every
covariate value](hyp:h_overlap_η), [the truth nuisance likewise has propensity uniformly
bounded in `[ε, 1 − ε]`](hyp:h_overlap_η₀), [`ε` is strictly positive](hyp:hε_pos), and
[each candidate outcome-regression arm, composed with the covariate, is
integrable](hyp:h_μ_η_int), then [the σ(X)-conditional expectation of the DR pseudo-outcome
contrast `φ_η − φ_0` equals the closed-form cross-product remainder `condBias η η₀`,
evaluated at the covariate, almost surely](goal).

Proof outline: expand `phi_eta z η - phi₀ S z` componentwise on `Ω`:

    (η.μ_fn 1 − η.μ_fn 0)(X) − (η₀.μ_fn 1 − η₀.μ_fn 0)(X)
      + (A / η.e_fn(X)) (Y − η.μ_fn 1(X)) − (A / η₀.e_fn(X)) (Y − η₀.μ_fn 1(X))
      − ((1−A) / (1 − η.e_fn(X))) (Y − η.μ_fn 0(X))
      + ((1−A) / (1 − η₀.e_fn(X))) (Y − η₀.μ_fn 0(X)).

Apply `cond_exp_residual_at_h` to each weighted residual term (with
`h := η.μ_fn d` or `η₀.μ_fn d` as appropriate) and use
`MeasureTheory.condExp_mul_of_stronglyMeasurable_left` to pull the
`(1/η.e_fn)(X)` (resp. `(1/η₀.e_fn)(X)`) factors outside the conditional
expectation as σ(X)-measurable.  The truth-side residuals (with `η₀`)
collapse to zero by the special case `h := η₀.μ_fn d` (i.e.
`cond_exp_residual_zero`).  Collect arm by arm using the algebraic
identity

    (e/ê − 1) · (μ − μ̂) = − (ê − e) · (μ̂ − μ) / ê,

which matches the `condBias` definition arm-by-arm. -/
theorem phi_eta_minus_phi₀_cond_exp
    {P : POSystem} [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    (S : CATEEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.Assumptions)
    (η : NuisanceVec γ) {ε : ℝ}
    (h_overlap_η : η ∈ BackdoorEstimationSystem.H_ε (γ := γ) ε)
    (h_overlap_η₀ : S.toBackdoorEstimationSystem.η₀ ∈
                    BackdoorEstimationSystem.H_ε (γ := γ) ε)
    (hε_pos : 0 < ε)
    -- Per-arm integrability of the candidate outcome regressions on Ω.
    -- Required to build per-summand integrability witnesses for the AIPW
    -- expansion (truth-side η₀-pieces are derivable from `μ_compat` +
    -- `conditionalMeanOutcome_backdoor`, but the candidate η-side needs an explicit hypothesis).
    (h_μ_η_int : ∀ a : Bool,
      Integrable (fun ω => η.μ_fn a (S.toBackdoorEstimationSystem.factualX ω)) P.μ) :
    P.μ[fun ω => phi_eta (S.toBackdoorEstimationSystem.factualZ ω) η -
                 phi₀ S (S.toBackdoorEstimationSystem.factualZ ω)
        | S.toPOBackdoorSystem.sigmaX]
      =ᵐ[P.μ]
        (fun ω => condBias η S.toBackdoorEstimationSystem.η₀
                    (S.toBackdoorEstimationSystem.factualX ω)) := by
  let X : P.Ω → γ := S.toPOBackdoorSystem.factualX
  let Y : P.Ω → ℝ := S.toPOBackdoorSystem.factualY
  let indT : P.Ω → ℝ := S.toPOBackdoorSystem.dVar.indicator true
  let indF : P.Ω → ℝ := S.toPOBackdoorSystem.dVar.indicator false
  let base : P.Ω → ℝ := fun ω =>
    η.μ_fn true (X ω) - η.μ_fn false (X ω) -
      (S.μ_val true (X ω) - S.μ_val false (X ω))
  let BηT : P.Ω → ℝ := fun ω =>
    (1 / η.e_fn (X ω)) *
      (indT ω * (Y ω - η.μ_fn true (X ω)))
  let B₀T : P.Ω → ℝ := fun ω =>
    (1 / S.e_val (X ω)) *
      (indT ω * (Y ω - S.μ_val true (X ω)))
  let CηF : P.Ω → ℝ := fun ω =>
    (1 / (1 - η.e_fn (X ω))) *
      (indF ω * (Y ω - η.μ_fn false (X ω)))
  let C₀F : P.Ω → ℝ := fun ω =>
    (1 / (1 - S.e_val (X ω))) *
      (indF ω * (Y ω - S.μ_val false (X ω)))
  have hindA_true : ∀ ω, BackdoorEstimationSystem.indA
      (S.toBackdoorEstimationSystem.factualZ ω) = indT ω := by
    intro ω
    by_cases hD : S.toPOBackdoorSystem.factualD ω = true
    · have hInd : indT ω = 1 :=
        S.toPOBackdoorSystem.dVar.indicator_apply_eq_one hD
      simp [BackdoorEstimationSystem.factualZ, BackdoorEstimationSystem.indA,
        BackdoorEstimationSystem.projA, indT, hD, hInd]
    · have hInd : indT ω = 0 :=
        S.toPOBackdoorSystem.dVar.indicator_apply_eq_zero (x := true) hD
      simp [BackdoorEstimationSystem.factualZ, BackdoorEstimationSystem.indA,
        BackdoorEstimationSystem.projA, indT, hD, hInd]
  have hφ_eq :
      (fun ω => phi_eta (S.toBackdoorEstimationSystem.factualZ ω) η -
          phi₀ S (S.toBackdoorEstimationSystem.factualZ ω))
        = (fun ω => base ω + BηT ω - B₀T ω - CηF ω + C₀F ω) := by
    funext ω
    have hind_true_z :
        BackdoorEstimationSystem.indA
          (S.toPOBackdoorSystem.factualX ω,
            S.toPOBackdoorSystem.factualD ω,
            S.toPOBackdoorSystem.factualY ω)
          = indT ω := by
      simpa [BackdoorEstimationSystem.factualZ] using hindA_true ω
    have hind_not : 1 - indT ω = indF ω := by
      have hsum : indT ω + indF ω = 1 :=
        S.toPOBackdoorSystem.dVar.indicator_add_indicator_not ω
      linarith
    simp [base, BηT, B₀T, CηF, C₀F, X, Y, indT, indF, phi₀, phi_eta,
      BackdoorEstimationSystem.aipwMoment, BackdoorEstimationSystem.factualZ,
      BackdoorEstimationSystem.projX, BackdoorEstimationSystem.projY,
      BackdoorEstimationSystem.η₀, hind_true_z, hind_not, mul_assoc, mul_comm,
      sub_eq_add_neg, add_assoc, add_comm]
    ring_nf
  have hμ_val_int : ∀ d : Bool, Integrable (fun ω => S.μ_val d (X ω)) P.μ := by
    intro d
    have hcate_int : Integrable (S.toPOBackdoorSystem.conditionalMeanOutcome d) P.μ := by
      unfold POBackdoorSystem.conditionalMeanOutcome
      exact MeasureTheory.integrable_condExp
    exact hcate_int.congr (S.μ_compat hA d)
  have hbase_int : Integrable base P.μ := by
    have hη := (h_μ_η_int true).sub (h_μ_η_int false)
    have hμ := (hμ_val_int true).sub (hμ_val_int false)
    refine (hη.sub hμ).congr ?_
    exact Filter.Eventually.of_forall (fun ω => by simp [base, X])
  have hbase_sm : StronglyMeasurable[S.toPOBackdoorSystem.sigmaX] base := by
    change StronglyMeasurable[
      MeasurableSpace.comap S.toPOBackdoorSystem.factualX inferInstance]
      (fun ω =>
        η.μ_fn true (S.toPOBackdoorSystem.factualX ω) -
          η.μ_fn false (S.toPOBackdoorSystem.factualX ω) -
            (S.μ_val true (S.toPOBackdoorSystem.factualX ω) -
              S.μ_val false (S.toPOBackdoorSystem.factualX ω)))
    exact ((((η.μ_meas true).comp
      (comap_measurable S.toPOBackdoorSystem.factualX)).sub
        ((η.μ_meas false).comp
          (comap_measurable S.toPOBackdoorSystem.factualX))).sub
        (((S.μ_meas true).comp
          (comap_measurable S.toPOBackdoorSystem.factualX)).sub
          ((S.μ_meas false).comp
            (comap_measurable S.toPOBackdoorSystem.factualX)))).stronglyMeasurable
  have hbase_ce :
      P.μ[base | S.toPOBackdoorSystem.sigmaX] =ᵐ[P.μ] base :=
    Filter.EventuallyEq.of_eq
      (MeasureTheory.condExp_of_stronglyMeasurable
        S.toPOBackdoorSystem.sigmaX_le hbase_sm hbase_int)
  have hηe_lower : ∀ ω, ε ≤ η.e_fn (X ω) := fun ω => (h_overlap_η (X ω)).1
  have hηe_upper : ∀ ω, η.e_fn (X ω) ≤ 1 - ε := fun ω => (h_overlap_η (X ω)).2
  have h₀e_lower : ∀ ω, ε ≤ S.e_val (X ω) := by
    intro ω
    exact (h_overlap_η₀ (X ω)).1
  have h₀e_upper : ∀ ω, S.e_val (X ω) ≤ 1 - ε := by
    intro ω
    exact (h_overlap_η₀ (X ω)).2
  have hwηT_Linf : MemLp (fun ω => 1 / η.e_fn (X ω)) ⊤ P.μ := by
    refine MemLp.of_bound ?_ ε⁻¹ ?_
    · exact ((measurable_const.div
        (η.e_meas.comp S.toPOBackdoorSystem.measurable_factualX))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun ω => by
        have hpos : 0 < η.e_fn (X ω) := lt_of_lt_of_le hε_pos (hηe_lower ω)
        have hle : (η.e_fn (X ω))⁻¹ ≤ ε⁻¹ :=
          (inv_le_inv₀ hpos hε_pos).2 (hηe_lower ω)
        simpa [one_div, Real.norm_eq_abs, abs_of_pos hpos] using hle)
  have hwηF_Linf : MemLp (fun ω => 1 / (1 - η.e_fn (X ω))) ⊤ P.μ := by
    refine MemLp.of_bound ?_ ε⁻¹ ?_
    · exact ((measurable_const.div
        (measurable_const.sub
          (η.e_meas.comp S.toPOBackdoorSystem.measurable_factualX)))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun ω => by
        have hden : ε ≤ 1 - η.e_fn (X ω) := by linarith [hηe_upper ω]
        have hpos : 0 < 1 - η.e_fn (X ω) := lt_of_lt_of_le hε_pos hden
        have hle : (1 - η.e_fn (X ω))⁻¹ ≤ ε⁻¹ :=
          (inv_le_inv₀ hpos hε_pos).2 hden
        simpa [one_div, Real.norm_eq_abs, abs_of_pos hpos] using hle)
  have hw₀T_Linf : MemLp (fun ω => 1 / S.e_val (X ω)) ⊤ P.μ := by
    refine MemLp.of_bound ?_ ε⁻¹ ?_
    · exact ((measurable_const.div
        (S.e_meas.comp S.toPOBackdoorSystem.measurable_factualX))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun ω => by
        have hpos : 0 < S.e_val (X ω) := S.e_pos _
        have hle : (S.e_val (X ω))⁻¹ ≤ ε⁻¹ :=
          (inv_le_inv₀ hpos hε_pos).2 (h₀e_lower ω)
        simpa [one_div, Real.norm_eq_abs, abs_of_pos hpos] using hle)
  have hw₀F_Linf : MemLp (fun ω => 1 / (1 - S.e_val (X ω))) ⊤ P.μ := by
    refine MemLp.of_bound ?_ ε⁻¹ ?_
    · exact ((measurable_const.div
        (measurable_const.sub
          (S.e_meas.comp S.toPOBackdoorSystem.measurable_factualX)))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun ω => by
        have hpos : 0 < 1 - S.e_val (X ω) := by linarith [S.e_lt_one (X ω)]
        have hden : ε ≤ 1 - S.e_val (X ω) := by linarith [h₀e_upper ω]
        have hle : (1 - S.e_val (X ω))⁻¹ ≤ ε⁻¹ :=
          (inv_le_inv₀ hpos hε_pos).2 hden
        simpa [one_div, Real.norm_eq_abs, abs_of_pos hpos] using hle)
  have hYind_int : ∀ d : Bool,
      Integrable (fun ω => Y ω * S.toPOBackdoorSystem.dVar.indicator d ω) P.μ :=
    fun d => S.toPOBackdoorSystem.dVar.integrable_mul_indicator d (MeasurableSet.singleton d)
      hA.integrable_factualY
  have hημind_int : ∀ d : Bool,
      Integrable (fun ω => η.μ_fn d (X ω) *
        S.toPOBackdoorSystem.dVar.indicator d ω) P.μ := by
    intro d
    exact S.toPOBackdoorSystem.dVar.integrable_mul_indicator d (MeasurableSet.singleton d)
      (h_μ_η_int d)
  have hμind_int : ∀ d : Bool,
      Integrable (fun ω => S.μ_val d (X ω) *
        S.toPOBackdoorSystem.dVar.indicator d ω) P.μ := by
    intro d
    exact S.toPOBackdoorSystem.dVar.integrable_mul_indicator d (MeasurableSet.singleton d)
      (hμ_val_int d)
  have hresη_int : ∀ d : Bool,
      Integrable (fun ω => S.toPOBackdoorSystem.dVar.indicator d ω *
        (Y ω - η.μ_fn d (X ω))) P.μ := by
    intro d
    have hY' : Integrable
        (fun ω => S.toPOBackdoorSystem.dVar.indicator d ω * Y ω) P.μ := by
      simpa [Y, mul_comm] using hYind_int d
    have hμ' : Integrable
        (fun ω => S.toPOBackdoorSystem.dVar.indicator d ω * η.μ_fn d (X ω)) P.μ := by
      simpa [mul_comm] using hημind_int d
    refine (hY'.sub hμ').congr ?_
    exact Filter.Eventually.of_forall (fun ω => by
      change S.toPOBackdoorSystem.dVar.indicator d ω * Y ω -
          S.toPOBackdoorSystem.dVar.indicator d ω * η.μ_fn d (X ω) =
        S.toPOBackdoorSystem.dVar.indicator d ω * (Y ω - η.μ_fn d (X ω))
      ring_nf)
  have hresμ_int : ∀ d : Bool,
      Integrable (fun ω => S.toPOBackdoorSystem.dVar.indicator d ω *
        (Y ω - S.μ_val d (X ω))) P.μ := by
    intro d
    have hY' : Integrable
        (fun ω => S.toPOBackdoorSystem.dVar.indicator d ω * Y ω) P.μ := by
      simpa [Y, mul_comm] using hYind_int d
    have hμ' : Integrable
        (fun ω => S.toPOBackdoorSystem.dVar.indicator d ω * S.μ_val d (X ω)) P.μ := by
      simpa [mul_comm] using hμind_int d
    refine (hY'.sub hμ').congr ?_
    exact Filter.Eventually.of_forall (fun ω => by
      change S.toPOBackdoorSystem.dVar.indicator d ω * Y ω -
          S.toPOBackdoorSystem.dVar.indicator d ω * S.μ_val d (X ω) =
        S.toPOBackdoorSystem.dVar.indicator d ω * (Y ω - S.μ_val d (X ω))
      ring_nf)
  have hBηT_int : Integrable BηT P.μ := by
    have hL1 : MemLp BηT 1 P.μ := by
      have hmul := MemLp.mul' (p := 1) (q := ⊤) (r := 1)
        hwηT_Linf (memLp_one_iff_integrable.2 (hresη_int true))
      exact hmul.ae_eq (Filter.Eventually.of_forall (fun ω => by
        simp [BηT, X, Y, indT]
        ring))
    exact hL1.integrable (by norm_num)
  have hCηF_int : Integrable CηF P.μ := by
    have hL1 : MemLp CηF 1 P.μ := by
      have hmul := MemLp.mul' (p := 1) (q := ⊤) (r := 1)
        hwηF_Linf (memLp_one_iff_integrable.2 (hresη_int false))
      exact hmul.ae_eq (Filter.Eventually.of_forall (fun ω => by
        simp [CηF, X, Y, indF]
        ring))
    exact hL1.integrable (by norm_num)
  have hB₀T_int : Integrable B₀T P.μ := by
    have hL1 : MemLp B₀T 1 P.μ := by
      have hmul := MemLp.mul' (p := 1) (q := ⊤) (r := 1)
        hw₀T_Linf (memLp_one_iff_integrable.2 (hresμ_int true))
      exact hmul.ae_eq (Filter.Eventually.of_forall (fun ω => by
        simp [B₀T, X, Y, indT]
        ring))
    exact hL1.integrable (by norm_num)
  have hC₀F_int : Integrable C₀F P.μ := by
    have hL1 : MemLp C₀F 1 P.μ := by
      have hmul := MemLp.mul' (p := 1) (q := ⊤) (r := 1)
        hw₀F_Linf (memLp_one_iff_integrable.2 (hresμ_int false))
      exact hmul.ae_eq (Filter.Eventually.of_forall (fun ω => by
        simp [C₀F, X, Y, indF]
        ring))
    exact hL1.integrable (by norm_num)
  have hweighted :
      ∀ (d : Bool) (g h : γ → ℝ), Measurable g → Measurable h →
        Integrable (fun ω => h (X ω) *
          S.toPOBackdoorSystem.dVar.indicator d ω) P.μ →
        Integrable (fun ω => g (X ω) *
          (S.toPOBackdoorSystem.dVar.indicator d ω * (Y ω - h (X ω)))) P.μ →
        Integrable (fun ω => S.toPOBackdoorSystem.dVar.indicator d ω *
          (Y ω - h (X ω))) P.μ →
        P.μ[fun ω => g (X ω) *
            (S.toPOBackdoorSystem.dVar.indicator d ω * (Y ω - h (X ω))) |
            S.toPOBackdoorSystem.sigmaX]
          =ᵐ[P.μ]
            (fun ω => g (X ω) *
              (S.toPOBackdoorSystem.propScore d ω *
                (S.μ_val d (X ω) - h (X ω)))) := by
    intro d g h hg_meas hh_meas hh_ind_int hprod_int hres_int
    have hg_sm : StronglyMeasurable[S.toPOBackdoorSystem.sigmaX]
        (fun ω => g (X ω)) := by
      change StronglyMeasurable[
        MeasurableSpace.comap S.toPOBackdoorSystem.factualX inferInstance]
        (fun ω => g (S.toPOBackdoorSystem.factualX ω))
      exact (hg_meas.comp
        (comap_measurable S.toPOBackdoorSystem.factualX)).stronglyMeasurable
    have hpull := MeasureTheory.condExp_mul_of_stronglyMeasurable_left
      (μ := P.μ) (m := S.toPOBackdoorSystem.sigmaX) hg_sm hprod_int hres_int
    refine hpull.trans ?_
    filter_upwards [cond_exp_residual_at_h S hA d h hh_meas
      (by simpa [X, mul_comm] using hh_ind_int)] with ω hω
    rw [Pi.mul_apply, hω]
  have hBηT_ce :
      P.μ[BηT | S.toPOBackdoorSystem.sigmaX]
        =ᵐ[P.μ]
          (fun ω => (1 / η.e_fn (X ω)) *
            (S.toPOBackdoorSystem.propScore true ω *
              (S.μ_val true (X ω) - η.μ_fn true (X ω)))) := by
    simpa [BηT, X, Y, indT, mul_assoc] using
      hweighted true (fun x => 1 / η.e_fn x) (η.μ_fn true)
        (measurable_const.div η.e_meas) (η.μ_meas true) (hημind_int true) hBηT_int
        (hresη_int true)
  have hB₀T_ce :
      P.μ[B₀T | S.toPOBackdoorSystem.sigmaX]
        =ᵐ[P.μ]
          (fun ω => (1 / S.e_val (X ω)) *
            (S.toPOBackdoorSystem.propScore true ω *
              (S.μ_val true (X ω) - S.μ_val true (X ω)))) := by
    simpa [B₀T, X, Y, indT, mul_assoc] using
      hweighted true (fun x => 1 / S.e_val x) (S.μ_val true)
        (measurable_const.div S.e_meas) (S.μ_meas true) (hμind_int true) hB₀T_int
        (hresμ_int true)
  have hCηF_ce :
      P.μ[CηF | S.toPOBackdoorSystem.sigmaX]
        =ᵐ[P.μ]
          (fun ω => (1 / (1 - η.e_fn (X ω))) *
            (S.toPOBackdoorSystem.propScore false ω *
              (S.μ_val false (X ω) - η.μ_fn false (X ω)))) := by
    simpa [CηF, X, Y, indF, mul_assoc] using
      hweighted false (fun x => 1 / (1 - η.e_fn x)) (η.μ_fn false)
        (measurable_const.div (measurable_const.sub η.e_meas))
        (η.μ_meas false) (hημind_int false) hCηF_int (hresη_int false)
  have hC₀F_ce :
      P.μ[C₀F | S.toPOBackdoorSystem.sigmaX]
        =ᵐ[P.μ]
          (fun ω => (1 / (1 - S.e_val (X ω))) *
            (S.toPOBackdoorSystem.propScore false ω *
              (S.μ_val false (X ω) - S.μ_val false (X ω)))) := by
    simpa [C₀F, X, Y, indF, mul_assoc] using
      hweighted false (fun x => 1 / (1 - S.e_val x)) (S.μ_val false)
        (measurable_const.div (measurable_const.sub S.e_meas))
        (S.μ_meas false) (hμind_int false) hC₀F_int (hresμ_int false)
  have h12_int : Integrable (fun ω => base ω + BηT ω) P.μ :=
    hbase_int.add hBηT_int
  have h123_int : Integrable (fun ω => base ω + BηT ω - B₀T ω) P.μ :=
    h12_int.sub hB₀T_int
  have h1234_int : Integrable (fun ω => base ω + BηT ω - B₀T ω - CηF ω) P.μ :=
    h123_int.sub hCηF_int
  have hadd :
      P.μ[fun ω => base ω + BηT ω | S.toPOBackdoorSystem.sigmaX]
        =ᵐ[P.μ]
          P.μ[base | S.toPOBackdoorSystem.sigmaX] +
            P.μ[BηT | S.toPOBackdoorSystem.sigmaX] :=
    MeasureTheory.condExp_add hbase_int hBηT_int S.toPOBackdoorSystem.sigmaX
  have hsubT :
      P.μ[fun ω => base ω + BηT ω - B₀T ω | S.toPOBackdoorSystem.sigmaX]
        =ᵐ[P.μ]
          P.μ[fun ω => base ω + BηT ω | S.toPOBackdoorSystem.sigmaX] -
            P.μ[B₀T | S.toPOBackdoorSystem.sigmaX] :=
    MeasureTheory.condExp_sub h12_int hB₀T_int S.toPOBackdoorSystem.sigmaX
  have hsubF :
      P.μ[fun ω => base ω + BηT ω - B₀T ω - CηF ω |
          S.toPOBackdoorSystem.sigmaX]
        =ᵐ[P.μ]
          P.μ[fun ω => base ω + BηT ω - B₀T ω |
            S.toPOBackdoorSystem.sigmaX] -
            P.μ[CηF | S.toPOBackdoorSystem.sigmaX] :=
    MeasureTheory.condExp_sub h123_int hCηF_int S.toPOBackdoorSystem.sigmaX
  have haddF :
      P.μ[fun ω => base ω + BηT ω - B₀T ω - CηF ω + C₀F ω |
          S.toPOBackdoorSystem.sigmaX]
        =ᵐ[P.μ]
          P.μ[fun ω => base ω + BηT ω - B₀T ω - CηF ω |
            S.toPOBackdoorSystem.sigmaX] +
            P.μ[C₀F | S.toPOBackdoorSystem.sigmaX] :=
    MeasureTheory.condExp_add h1234_int hC₀F_int S.toPOBackdoorSystem.sigmaX
  rw [hφ_eq]
  refine haddF.trans ?_
  filter_upwards [hsubF, hsubT, hadd, hbase_ce, hBηT_ce, hB₀T_ce, hCηF_ce,
    hC₀F_ce, S.e_compat, BackdoorEstimationSystem.propScore_false_ae
      S.toBackdoorEstimationSystem] with
    ω hsubFω hsubTω haddω hbaseω hBTω hB0ω hCFω hC0ω heT heF
  rw [Pi.add_apply, hsubFω, Pi.sub_apply, hsubTω, Pi.sub_apply,
    haddω, Pi.add_apply, hbaseω, hBTω, hB0ω, hCFω, hC0ω]
  rw [heF, heT]
  simp only [X, base, BackdoorEstimationSystem.η₀, one_div, sub_self,
    mul_zero, sub_zero, add_zero] at ⊢
  have hηT_ne : η.e_fn (S.toPOBackdoorSystem.factualX ω) ≠ 0 := by
    simpa [X] using ne_of_gt (lt_of_lt_of_le hε_pos (hηe_lower ω))
  have hηF_ne : 1 - η.e_fn (S.toPOBackdoorSystem.factualX ω) ≠ 0 := by
    have hden : ε ≤ 1 - η.e_fn (X ω) := by linarith [hηe_upper ω]
    simpa [X] using ne_of_gt (lt_of_lt_of_le hε_pos hden)
  let eη : ℝ := η.e_fn (S.toPOBackdoorSystem.factualX ω)
  let e₀ : ℝ := S.e_val (S.toPOBackdoorSystem.factualX ω)
  let mT : ℝ := η.μ_fn true (S.toPOBackdoorSystem.factualX ω)
  let mF : ℝ := η.μ_fn false (S.toPOBackdoorSystem.factualX ω)
  let vT : ℝ := S.μ_val true (S.toPOBackdoorSystem.factualX ω)
  let vF : ℝ := S.μ_val false (S.toPOBackdoorSystem.factualX ω)
  unfold condBias
  rw [Fintype.sum_bool]
  simp only [if_true, if_false, Bool.false_eq_true]
  field_simp [hηT_ne, hηF_ne]
  change ((mT - mF - (vT - vF)) * eη + e₀ * (vT - mT)) *
        (1 - eη) - eη * (1 - e₀) * (vF - mF) =
      (eη - e₀) * ((1 - eη) * (mT - vT) + eη * (mF - vF))
  ring

/-! ## Value-space `P_X`-a.e. form (Kennedy) -/

end CATE
end Estimation
end Causalean
