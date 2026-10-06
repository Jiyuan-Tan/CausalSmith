/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Automatic debiasing example: the back-door ATE

Instantiates the general regression-nuisance layer for a finite covariate
space.  The regression target is `g(d,x)`, the original moment is its treated
minus control mean minus `θ`, and the pairing function is the signed inverse
propensity weight.
-/

module
public import Causalean.Estimation.ATE.Score.MeanZero
public import Causalean.Estimation.ATE.Score.ScorePullout
public import Causalean.Estimation.OrthogonalMoments.AutoDebias.DML
public import Causalean.Estimation.OrthogonalMoments.AutoDebias.GeneralDML

/-! # A worked ATE regression-nuisance moment system

For finite covariate spaces, every regression direction is bounded and
integrable. This lets the standard back-door assumptions and pointwise strict
overlap produce a fully concrete `RegNuisanceMomentSys`, its matching
`LinRegFnSys`, the signed inverse-propensity pairing function, and a feasible
linear-DML estimator. -/

@[expose] public section

namespace Causalean.Estimation.OrthogonalMoments.AutoDebias

open MeasureTheory ProbabilityTheory
open Causalean.Stat
open Causalean.PO Causalean.Estimation.ATE
open Causalean.Estimation.ATE.BackdoorEstimationSystem

private lemma finite_fun_memLp
    {X : Type*} [MeasurableSpace X] [Finite X] [MeasurableSingletonClass X]
    (f : X → ℝ) (p : ENNReal) (P : Measure X) [IsFiniteMeasure P] :
    MemLp f p P := by
  rcases Finite.exists_le (fun x => |f x|) with ⟨C, hC⟩
  refine MemLp.of_bound (measurable_of_finite f).aestronglyMeasurable C ?_
  filter_upwards with x
  simpa [Real.norm_eq_abs] using hC x

private lemma finite_covariate_indicator_integrable
    {P : POSystem} {γ : Type*} [MeasurableSpace γ]
    [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    [Finite γ] [MeasurableSingletonClass γ]
    (S : BackdoorEstimationSystem P γ) (d : Bool) (f : γ → ℝ) :
    Integrable (fun ω => f (S.factualX ω) * S.dVar.indicator d ω) P.μ := by
  rcases Finite.exists_le (fun x => |f x|) with ⟨C, hC⟩
  have hm : Measurable (fun ω => f (S.factualX ω) * S.dVar.indicator d ω) :=
    ((measurable_of_finite f).comp S.measurable_factualX).mul
      (S.dVar.measurable_indicator d (MeasurableSet.singleton d))
  have hb : ∀ ω, ‖f (S.factualX ω) * S.dVar.indicator d ω‖ ≤ max C 0 := by
    intro ω
    rcases S.dVar.indicator_eq_one_or_zero d ω with hi | hi
    · rw [hi, mul_one, Real.norm_eq_abs]
      exact (hC _).trans (le_max_left _ _)
    · rw [hi, mul_zero, norm_zero]
      exact le_max_right _ _
  have hp : MemLp (fun ω => f (S.factualX ω) * S.dVar.indicator d ω) 1 P.μ :=
    MemLp.of_bound hm.aestronglyMeasurable (max C 0)
      (Filter.Eventually.of_forall hb)
  exact hp.integrable (by norm_num)

/-- For [a finite measurable covariate space](hyp:γ), the [ATE regression
nuisance type](goal) consists of the two unrestricted real regression functions
indexed by the treatment arm. -/
abbrev ATERegressionNuisance (γ : Type*) := Bool → γ → ℝ

/-- For [a back-door ATE system](hyp:S) and [an observed covariate--arm
pair](hyp:xd), the [signed inverse-propensity Riesz weight](goal) is `1/e(X)`
on the treated arm and `-1/(1-e(X))` on the control arm. -/
noncomputable def ateRieszWeight
    {P : POSystem} {γ : Type*} [MeasurableSpace γ]
    [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    (S : BackdoorEstimationSystem P γ) (xd : γ × Bool) : ℝ :=
  if xd.2 then (S.e_val xd.1)⁻¹ else -((1 - S.e_val xd.1)⁻¹)

/-- Given [a finite-covariate back-door estimation system](hyp:S) satisfying
[the standard identification assumptions](hyp:hA), the [ATE regression-nuisance
moment system](goal) has covariate object `(X,D)`, regression target `g(D,X)`,
population moment `∫(g(1,x)-g(0,x))dP_X-θ`, and its observation-level
counterpart. -/
noncomputable def ateRegNuisanceMomentSys
    {P : POSystem} {γ : Type*} [MeasurableSpace γ]
    [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    [Finite γ] [MeasurableSingletonClass γ]
    (S : BackdoorEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.Assumptions) : RegNuisanceMomentSys := by
  letI : IsProbabilityMeasure S.P_X := by
    unfold BackdoorEstimationSystem.P_X
    exact Measure.isProbabilityMeasure_map S.measurable_factualX.aemeasurable
  letI : IsProbabilityMeasure S.P_Z := by
    unfold BackdoorEstimationSystem.P_Z
    exact Measure.isProbabilityMeasure_map S.measurable_factualZ.aemeasurable
  exact {
  Z := γ × Bool × ℝ
  P_Z := S.P_Z
  X := γ × Bool
  P_X := S.P_Z.map (fun z => (z.1, z.2.1))
  H := ATERegressionNuisance γ
  proj_X := fun z => (z.1, z.2.1)
  proj_X_meas := Measurable.prod measurable_fst (measurable_fst.comp measurable_snd)
  Y_obs := fun z => z.2.2
  Y_obs_meas := measurable_snd.comp measurable_snd
  γ_target := fun g xd => g xd.2 xd.1
  γ_target_meas := fun _ => measurable_of_finite _
  γ_target_add := by intros; rfl
  γ_target_smul := by intros; rfl
  g₀ := S.μ_val
  θ₀ := S.θ₀
  M := fun θ g => ∫ x, g true x - g false x ∂S.P_X - θ
  M_truth := by simp [BackdoorEstimationSystem.θ₀]
  D_g_M := fun ν => ∫ x, ν true x - ν false x ∂S.P_X
  D_g_M_hasDerivAt := by
    intro ν
    have hμ (d : Bool) : Integrable (S.μ_val d) S.P_X :=
      (finite_fun_memLp (S.μ_val d) 1 S.P_X).integrable (by norm_num)
    have hν (d : Bool) : Integrable (ν d) S.P_X :=
      (finite_fun_memLp (ν d) 1 S.P_X).integrable (by norm_num)
    have hpath :
        (fun r : ℝ => (∫ x, (S.μ_val + r • ν) true x -
          (S.μ_val + r • ν) false x ∂S.P_X) - S.θ₀) =
        fun r : ℝ => ((∫ x, S.μ_val true x - S.μ_val false x ∂S.P_X) - S.θ₀) +
          r * (∫ x, ν true x - ν false x ∂S.P_X) := by
      funext r
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [show (fun x => (S.μ_val true x + r * ν true x) -
          (S.μ_val false x + r * ν false x)) =
          (fun x => S.μ_val true x - S.μ_val false x) +
            r • (fun x => ν true x - ν false x) by funext x; simp [smul_eq_mul]; ring]
      integral_linearity
      change (∫ a, S.μ_val true a ∂S.P_X) - (∫ a, S.μ_val false a ∂S.P_X) +
          (∫ a, r * (ν true a - ν false a) ∂S.P_X) - S.θ₀ = _
      rw [MeasureTheory.integral_const_mul]
      integral_linearity
      ring
    rw [hpath]
    simpa [BackdoorEstimationSystem.θ₀] using
      ((hasDerivAt_id (0 : ℝ)).mul_const
        (∫ x, ν true x - ν false x ∂S.P_X))
  m := fun g z θ => g true z.1 - g false z.1 - θ
  m_meas := fun g _ =>
    (((measurable_of_finite (g true)).comp measurable_fst).sub
      ((measurable_of_finite (g false)).comp measurable_fst)).sub measurable_const
  m_population := by
    intro g θ
    have hmeas : Measurable (fun x : γ => g true x - g false x) := measurable_of_finite _
    have hcomp_meas : Measurable
        (fun z : γ × Bool × ℝ => g true z.1 - g false z.1) :=
      ((measurable_of_finite (g true)).comp measurable_fst).sub
        ((measurable_of_finite (g false)).comp measurable_fst)
    rcases Finite.exists_le (fun x : γ => |g true x - g false x|) with ⟨C, hC⟩
    have hcomp_int : Integrable
        (fun z : γ × Bool × ℝ => g true z.1 - g false z.1) S.P_Z := by
      have hm : MemLp (fun z : γ × Bool × ℝ => g true z.1 - g false z.1) 1 S.P_Z :=
        MemLp.of_bound hcomp_meas.aestronglyMeasurable C
          (Filter.Eventually.of_forall fun z => by
            simpa [Real.norm_eq_abs] using hC z.1)
      exact hm.integrable (by norm_num)
    rw [show (∫ z, g true z.1 - g false z.1 - θ ∂S.P_Z) =
        (∫ z, (g true z.1 - g false z.1) ∂S.P_Z) - θ by
      rw [integral_sub hcomp_int (integrable_const θ)]
      simp]
    rw [← S.P_Z_map_projX_eq_P_X,
      MeasureTheory.integral_map measurable_fst.aemeasurable hmeas.aestronglyMeasurable]
  pushforward := rfl
  regression_resid_orthog := by
    intro α hα h_int
    have hmap : ∫ z, α (z.1, z.2.1) * (z.2.2 - S.μ_val z.2.1 z.1) ∂S.P_Z =
        ∫ ω, α (S.factualX ω, S.factualD ω) *
          (S.factualY ω - S.μ_val (S.factualD ω) (S.factualX ω)) ∂P.μ := by
      unfold BackdoorEstimationSystem.P_Z
      rw [MeasureTheory.integral_map S.measurable_factualZ.aemeasurable
        (by simpa [BackdoorEstimationSystem.P_Z] using h_int.aestronglyMeasurable)]
      apply integral_congr_ae
      filter_upwards with ω
      rfl
    rw [hmap]
    let T : P.Ω → ℝ := fun ω => α (S.factualX ω, true) *
      (S.dVar.indicator true ω * (S.factualY ω - S.μ_val true (S.factualX ω)))
    let F : P.Ω → ℝ := fun ω => α (S.factualX ω, false) *
      (S.dVar.indicator false ω * (S.factualY ω - S.μ_val false (S.factualX ω)))
    have hTF : (fun ω => α (S.factualX ω, S.factualD ω) *
        (S.factualY ω - S.μ_val (S.factualD ω) (S.factualX ω))) =
        fun ω => T ω + F ω := by
      funext ω
      cases hD : S.factualD ω
      · have hT : S.dVar.indicator true ω = 0 :=
          S.dVar.indicator_apply_eq_zero (x := true) (by
            intro he
            have hd' : S.dVar.factual ω = false := by exact hD
            rw [he] at hd'
            contradiction)
        have hF : S.dVar.indicator false ω = 1 :=
          S.dVar.indicator_apply_eq_one (by
            exact hD)
        simp [T, F, hT, hF]
      · have hT : S.dVar.indicator true ω = 1 :=
          S.dVar.indicator_apply_eq_one (by
            exact hD)
        have hF : S.dVar.indicator false ω = 0 :=
          S.dVar.indicator_apply_eq_zero (x := false) (by
            intro he
            have hd' : S.dVar.factual ω = true := by exact hD
            rw [he] at hd'
            contradiction)
        simp [T, F, hT, hF]
    rw [hTF]
    have harm_resid (d : Bool) : Integrable
        (fun ω => S.dVar.indicator d ω *
          (S.factualY ω - S.μ_val d (S.factualX ω))) P.μ := by
      have hYind : Integrable
          (fun ω => S.dVar.indicator d ω * S.factualY ω) P.μ := by
        simpa [mul_comm] using S.dVar.integrable_mul_indicator d
          (MeasurableSet.singleton d) hA.integrable_factualY
      have hμx : Integrable (fun ω => S.μ_val d (S.factualX ω)) P.μ := by
        have hc : Integrable (S.toPOBackdoorSystem.conditionalMeanOutcome d) P.μ := by
          unfold POBackdoorSystem.conditionalMeanOutcome
          exact MeasureTheory.integrable_condExp
        exact hc.congr (S.μ_compat hA d)
      have hμind : Integrable
          (fun ω => S.dVar.indicator d ω * S.μ_val d (S.factualX ω)) P.μ := by
        simpa [mul_comm] using S.dVar.integrable_mul_indicator d
          (MeasurableSet.singleton d) hμx
      exact (hYind.sub hμind).congr
        (Filter.Eventually.of_forall fun _ => by simp only [Pi.sub_apply]; ring)
    rcases Finite.exists_le (fun xd : γ × Bool => |α xd|) with ⟨C, hC⟩
    have hαbound (d : Bool) : ∀ᵐ ω ∂P.μ, ‖α (S.factualX ω, d)‖ ≤ C :=
      Filter.Eventually.of_forall fun ω => by
        simpa [Real.norm_eq_abs] using hC (S.factualX ω, d)
    have hαmeas (d : Bool) :
        AEStronglyMeasurable (fun ω => α (S.factualX ω, d)) P.μ :=
      (hα.comp (Measurable.prodMk S.measurable_factualX measurable_const)).aestronglyMeasurable
    have hTint : Integrable T P.μ := by
      exact (harm_resid true).bdd_mul (hαmeas true) (hαbound true)
    have hFint : Integrable F P.μ := by
      exact (harm_resid false).bdd_mul (hαmeas false) (hαbound false)
    rw [integral_add hTint hFint]
    dsimp only [T, F]
    rw [weighted_residual_integral_zero S hA true (fun x => α (x, true))
      (by fun_prop) hTint
      (cond_exp_residual_zero S hA true)]
    rw [weighted_residual_integral_zero S hA false (fun x => α (x, false))
      (by fun_prop) hFint
      (cond_exp_residual_zero S hA false)]
    ring
  }

/-- Given [a finite-covariate back-door estimation system](hyp:S) satisfying
[the standard identification assumptions](hyp:hA), the [ATE linear
regression-functional system](goal) reuses the observation law, regression target,
pushforward identity, and residual equation of `ateRegNuisanceMomentSys`, with
observation-level linear functional `g(1,X)-g(0,X)`. -/
noncomputable abbrev ateLinRegFnSys
    {P : POSystem} {γ : Type*} [MeasurableSpace γ]
    [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    [Finite γ] [MeasurableSingletonClass γ]
    (S : BackdoorEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.Assumptions) : LinRegFnSys := by
  letI : IsProbabilityMeasure S.P_Z := by
    unfold BackdoorEstimationSystem.P_Z
    exact Measure.isProbabilityMeasure_map S.measurable_factualZ.aemeasurable
  exact {
    Z := γ × Bool × ℝ
    P_Z := S.P_Z
    X := γ × Bool
    P_X := (ateRegNuisanceMomentSys S hA).P_X
    H_γ := ATERegressionNuisance γ
    proj_X := fun z => (z.1, z.2.1)
    proj_X_meas := Measurable.prod measurable_fst (measurable_fst.comp measurable_snd)
    Y_obs := fun z => z.2.2
    Y_obs_meas := measurable_snd.comp measurable_snd
    γ_target := fun g xd => g xd.2 xd.1
    γ_target_add := by intros; rfl
    γ_target_smul := by intros; rfl
    m_lin := fun z g => g true z.1 - g false z.1
    m_lin_addLeft := by
      intros
      simp only [Pi.add_apply]
      ring
    m_lin_smulLeft := by
      intro c z g
      change (c • g) true z.1 - (c • g) false z.1 =
        c * (g true z.1 - g false z.1)
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    m_lin_meas := fun g =>
      ((measurable_of_finite (g true)).comp measurable_fst).sub
        ((measurable_of_finite (g false)).comp measurable_fst)
    g₀ := (ateRegNuisanceMomentSys S hA).g₀
    pushforward := (ateRegNuisanceMomentSys S hA).pushforward
    regression_resid_orthog := (ateRegNuisanceMomentSys S hA).regression_resid_orthog }

/-- For [a finite-covariate back-door system](hyp:S) under [the back-door
assumptions](hyp:hA), [the ATE linear automatic-debiasing score at any nuisance and
parameter pair](hyp:η,θ) [is measurable](goal). -/
@[fun_prop] theorem ateLinRieszScore_measurable
    {P : POSystem} {γ : Type*} [MeasurableSpace γ]
    [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    [Finite γ] [MeasurableSingletonClass γ]
    (S : BackdoorEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.Assumptions)
    (η : linAutoNuisance (ateLinRegFnSys S hA)) (θ : ℝ) :
    Measurable (fun z => linRieszScore (ateLinRegFnSys S hA) η.1 η.2 θ z) := by
  change Measurable (fun z : γ × Bool × ℝ =>
    (η.1 true z.1 - η.1 false z.1) +
      η.2 (z.1, z.2.1) * (z.2.2 - η.1 z.2.1 z.1) - θ)
  have hη1 (d : Bool) : Measurable (η.1 d) := measurable_of_finite _
  have hη2 : Measurable η.2 := measurable_of_finite _
  fun_prop

/-- For [a finite-covariate back-door system](hyp:S), under [the back-door
assumptions](hyp:hA) and [pointwise overlap at the positive level
`ε`](hyp:ε,hε,hoverlap), [the signed inverse-propensity weight represents the
derivative of the ATE regression moment in the chosen regression direction](hyp:ν)
[by the displayed integral identity](goal). -/
theorem ateRieszWeight_representation
    {P : POSystem} {γ : Type*} [MeasurableSpace γ]
    [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    [Finite γ] [MeasurableSingletonClass γ]
    (S : BackdoorEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.Assumptions)
    (ε : ℝ) (hε : 0 < ε)
    (hoverlap : ∀ x, ε ≤ S.e_val x ∧ S.e_val x ≤ 1 - ε)
    (ν : ATERegressionNuisance γ) :
    (ateRegNuisanceMomentSys S hA).D_g_M ν =
      ∫ xd, ateRieszWeight S xd *
        (ateRegNuisanceMomentSys S hA).γ_target ν xd
        ∂(ateRegNuisanceMomentSys S hA).P_X := by
  let fT : γ → ℝ := fun x => ν true x / S.e_val x
  let fF : γ → ℝ := fun x => -(ν false x / (1 - S.e_val x))
  have hfT_meas : Measurable fT := measurable_of_finite _
  have hfF_meas : Measurable fF := measurable_of_finite _
  have hfT_int := finite_covariate_indicator_integrable S true fT
  have hfF_int := finite_covariate_indicator_integrable S false fF
  have hsplit : (fun ω => ateRieszWeight S (S.factualX ω, S.factualD ω) *
      ν (S.factualD ω) (S.factualX ω)) =
      fun ω => fT (S.factualX ω) * S.dVar.indicator true ω +
        fF (S.factualX ω) * S.dVar.indicator false ω := by
    funext ω
    cases hd : S.factualD ω
    · have hT : S.dVar.indicator true ω = 0 :=
        S.dVar.indicator_apply_eq_zero (x := true) (by
          intro he
          have hd' : S.dVar.factual ω = false := by exact hd
          rw [he] at hd'
          contradiction)
      have hF : S.dVar.indicator false ω = 1 :=
        S.dVar.indicator_apply_eq_one (by exact hd)
      simp [ateRieszWeight, fT, fF, hT, hF, div_eq_mul_inv, mul_comm]
    · have hT : S.dVar.indicator true ω = 1 :=
        S.dVar.indicator_apply_eq_one (by exact hd)
      have hF : S.dVar.indicator false ω = 0 :=
        S.dVar.indicator_apply_eq_zero (x := false) (by
          intro he
          have hd' : S.dVar.factual ω = true := by exact hd
          rw [he] at hd'
          contradiction)
      simp [ateRieszWeight, fT, fF, hT, hF, div_eq_mul_inv, mul_comm]
  have hright :
      (∫ xd, ateRieszWeight S xd *
          (ateRegNuisanceMomentSys S hA).γ_target ν xd
          ∂(ateRegNuisanceMomentSys S hA).P_X) =
        ∫ ω, ateRieszWeight S (S.factualX ω, S.factualD ω) *
          ν (S.factualD ω) (S.factualX ω) ∂P.μ := by
    let q : γ × Bool × ℝ → γ × Bool := fun z => (z.1, z.2.1)
    let k : γ × Bool → ℝ := fun xd =>
      ateRieszWeight S xd * ν xd.2 xd.1
    have hq : Measurable q :=
      Measurable.prod measurable_fst (measurable_fst.comp measurable_snd)
    have hk : Measurable k := measurable_of_finite _
    change (∫ xd, k xd ∂(S.P_Z.map q)) = _
    calc
      (∫ xd, k xd ∂(S.P_Z.map q)) = ∫ z, k (q z) ∂S.P_Z :=
        MeasureTheory.integral_map hq.aemeasurable hk.aestronglyMeasurable
      _ = ∫ ω, k (q (S.factualZ ω)) ∂P.μ := by
        unfold BackdoorEstimationSystem.P_Z
        exact MeasureTheory.integral_map S.measurable_factualZ.aemeasurable
          ((hk.comp hq).aestronglyMeasurable)
      _ = _ := by rfl
  have hleft : (ateRegNuisanceMomentSys S hA).D_g_M ν =
      ∫ ω, ν true (S.factualX ω) - ν false (S.factualX ω) ∂P.μ := by
    change (∫ x, ν true x - ν false x ∂S.P_X) = _
    unfold BackdoorEstimationSystem.P_X
    rw [MeasureTheory.integral_map S.measurable_factualX.aemeasurable
      (measurable_of_finite _).aestronglyMeasurable]
  rw [hleft, hright, hsplit, integral_add hfT_int hfF_int]
  rw [indicator_to_propScore_integral S true fT hfT_meas hfT_int]
  rw [indicator_to_propScore_integral S false fF hfF_meas hfF_int]
  have hTpoint : (fun ω => fT (S.factualX ω) *
      S.e_val_label true (S.factualX ω)) =
      fun ω => ν true (S.factualX ω) := by
    funext ω
    have he : S.e_val (S.factualX ω) ≠ 0 :=
      ne_of_gt (hε.trans_le (hoverlap (S.factualX ω)).1)
    simp [fT, e_val_label, he]
  have hFpoint : (fun ω => fF (S.factualX ω) *
      S.e_val_label false (S.factualX ω)) =
      fun ω => -ν false (S.factualX ω) := by
    funext ω
    have hce : 1 - S.e_val (S.factualX ω) ≠ 0 := by
      have := (hoverlap (S.factualX ω)).2
      linarith
    simp [fF, e_val_label, hce]
  rw [hTpoint, hFpoint, integral_neg]
  have hνint (d : Bool) : Integrable (fun ω => ν d (S.factualX ω)) P.μ := by
    rcases Finite.exists_le (fun x => |ν d x|) with ⟨C, hC⟩
    exact Integrable.of_bound
      ((measurable_of_finite (ν d)).comp S.measurable_factualX).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun ω => by
        simpa [Real.norm_eq_abs] using hC (S.factualX ω))
  rw [integral_sub (hνint true) (hνint false)]
  ring

/-- Given [a finite-covariate back-door system](hyp:S), [the back-door
assumptions](hyp:hA), and [pointwise strict overlap](hyp:ε,hε,hoverlap), the
[ATE automatic-debiasing mean representation](goal) uses the signed
inverse-propensity weight on `(X,D)`. -/
noncomputable def ateAutoDebiasMeanRepresentation
    {P : POSystem} {γ : Type*} [MeasurableSpace γ]
    [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    [Finite γ] [MeasurableSingletonClass γ]
    (S : BackdoorEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.Assumptions)
    (ε : ℝ) (hε : 0 < ε)
    (hoverlap : ∀ x, ε ≤ S.e_val x ∧ S.e_val x ≤ 1 - ε) :
    AutoDebiasMeanRepresentation (ateRegNuisanceMomentSys S hA) := by
  let R := ateRegNuisanceMomentSys S hA
  letI : IsProbabilityMeasure R.P_X := by
    rw [R.pushforward]
    exact Measure.isProbabilityMeasure_map R.proj_X_meas.aemeasurable
  refine {
    α₀ := ?_
    α₀_meas := ?_
    α₀_integrable := ?_
    representation := ?_ }
  · change γ × Bool → ℝ
    exact ateRieszWeight S
  · change Measurable (ateRieszWeight S)
    exact measurable_of_finite _
  · change Integrable (ateRieszWeight S)
      (S.P_Z.map fun z : γ × Bool × ℝ => (z.1, z.2.1))
    letI : IsFiniteMeasure S.P_Z := by
      unfold BackdoorEstimationSystem.P_Z
      exact Measure.isFiniteMeasure_map P.μ S.factualZ
    letI : IsFiniteMeasure
        (S.P_Z.map fun z : γ × Bool × ℝ => (z.1, z.2.1)) :=
      Measure.isFiniteMeasure_map S.P_Z fun z => (z.1, z.2.1)
    rcases Finite.exists_le (fun xd : γ × Bool => |ateRieszWeight S xd|) with ⟨C, hC⟩
    exact Integrable.of_bound (measurable_of_finite _).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun xd => by
        simpa [Real.norm_eq_abs] using hC xd)
  · change ∀ ν : ATERegressionNuisance γ,
      (ateRegNuisanceMomentSys S hA).D_g_M ν =
        ∫ xd, ateRieszWeight S xd *
          (ateRegNuisanceMomentSys S hA).γ_target ν xd
          ∂(ateRegNuisanceMomentSys S hA).P_X
    exact ateRieszWeight_representation S hA ε hε hoverlap

/-- For [a finite-covariate back-door system](hyp:S), under [the back-door
assumptions](hyp:hA) and [strict overlap at the positive level
`ε`](hyp:ε,hε,hoverlap), [the signed inverse-propensity weight gives a
mean-pairing representation for the ATE regression-functional system](goal). -/
noncomputable def ateLinMeanPairingRepresentation
    {P : POSystem} {γ : Type*} [MeasurableSpace γ]
    [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    [Finite γ] [MeasurableSingletonClass γ]
    (S : BackdoorEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.Assumptions)
    (ε : ℝ) (hε : 0 < ε)
    (hoverlap : ∀ x, ε ≤ S.e_val x ∧ S.e_val x ≤ 1 - ε) :
    MeanPairingRepresentation (ateLinRegFnSys S hA).H_γ
      (ateLinRegFnSys S hA).γ_target (L_of_m (ateLinRegFnSys S hA))
      (ateLinRegFnSys S hA).P_X := by
  let R := ateRegNuisanceMomentSys S hA
  let A := ateLinRegFnSys S hA
  refine {
    α₀ := ateRieszWeight S
    α₀_meas := by
      change Measurable (ateRieszWeight S)
      exact measurable_of_finite _
    α₀_memLp := by
      have hmeas : Measurable (ateRieszWeight S) := measurable_of_finite _
      change MemLp (ateRieszWeight S) 2
        (S.P_Z.map fun z : γ × Bool × ℝ => (z.1, z.2.1))
      letI : IsFiniteMeasure S.P_Z := by
        unfold BackdoorEstimationSystem.P_Z
        exact Measure.isFiniteMeasure_map P.μ S.factualZ
      letI : IsFiniteMeasure
          (S.P_Z.map fun z : γ × Bool × ℝ => (z.1, z.2.1)) :=
        Measure.isFiniteMeasure_map S.P_Z fun z => (z.1, z.2.1)
      rcases Finite.exists_le (fun x : γ × Bool => |ateRieszWeight S x|) with ⟨C, hC⟩
      refine MemLp.of_bound hmeas.aestronglyMeasurable C ?_
      exact Filter.Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs] using hC x
    representation := ?_ }
  intro ν
  have hobs : L_of_m A ν = R.D_g_M ν := by
    have hp := R.m_population ν 0
    convert hp.symm using 1 <;>
      simp [L_of_m, A, R, ateLinRegFnSys, ateRegNuisanceMomentSys]
    apply integral_congr_ae
    filter_upwards with z
    simp
  rw [hobs]
  exact ateRieszWeight_representation S hA ε hε hoverlap ν

/-- Given [a finite-covariate back-door system, its identifying assumptions, and
strict overlap](hyp:S,hA,ε,hε,hoverlap), [a nonnegative DML neighborhood radius](hyp:r,hr),
[an i.i.d. observed-data sample with a positive-fold split](hyp:sample,hK_pos,split),
[foldwise regression and pairing-function fits](hyp:g_hat,α_hat), [a sample size and
realization](hyp:n,ω), and [nonempty evaluation folds](hyp:hfold), [the feasible
ATE automatic-DML estimator equals the average of its foldwise observed scores](goal). -/
theorem ateLinAutoDMLEstimator_eq_foldAverage
    {P : POSystem} {γ : Type*} [MeasurableSpace γ]
    [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    [Finite γ] [MeasurableSingletonClass γ]
    (S : BackdoorEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.Assumptions)
    (ε : ℝ) (hε : 0 < ε)
    (hoverlap : ∀ x, ε ≤ S.e_val x ∧ S.e_val x ≤ 1 - ε)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (r : ℝ) (hr : 0 ≤ r)
    (sample : IIDSample Ω (ateLinRegFnSys S hA).Z μ (ateLinRegFnSys S hA).P_Z)
    {K : ℕ} (hK_pos : 0 < K) (split : KFoldSplit sample K)
    (g_hat : ℕ → Fin K → Ω → (ateLinRegFnSys S hA).H_γ)
    (α_hat : ℕ → Fin K → Ω → (ateLinRegFnSys S hA).X → ℝ)
    (n : ℕ) (ω : Ω) (hfold : ∀ k, (split.fold n k).Nonempty) :
    linAutoDMLEstimator (ateLinRegFnSys S hA)
        (ateLinMeanPairingRepresentation S hA ε hε hoverlap) r hr
        (ateLinRieszScore_measurable S hA) sample split g_hat α_hat n ω =
      (K : ℝ)⁻¹ * ∑ k : Fin K,
        ((split.fold n k).card : ℝ)⁻¹ * ∑ i ∈ split.fold n k,
          ((ateLinRegFnSys S hA).m_lin (sample.Z i ω) (g_hat n k ω) +
            α_hat n k ω ((ateLinRegFnSys S hA).proj_X (sample.Z i ω)) *
              ((ateLinRegFnSys S hA).Y_obs (sample.Z i ω) -
                (ateLinRegFnSys S hA).γ_target (g_hat n k ω)
                  ((ateLinRegFnSys S hA).proj_X (sample.Z i ω)))) := by
  exact linAutoDMLEstimator_eq_foldAverage (ateLinRegFnSys S hA)
    (ateLinMeanPairingRepresentation S hA ε hε hoverlap) r hr
    (ateLinRieszScore_measurable S hA) sample hK_pos split g_hat α_hat n ω hfold

end Causalean.Estimation.OrthogonalMoments.AutoDebias
