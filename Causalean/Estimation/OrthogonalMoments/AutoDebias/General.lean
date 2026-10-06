/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Automatic debiasing — general moment layer

This file develops the general-moment automatic-debiasing layer for
`doc/basic_concepts/po/estimation/automatic_debiasing.tex`:

* `RegNuisanceMomentSys` — regression-nuisance moment system (extends the
  data + regression infrastructure of `LinRegFnSys` to a general moment
  functional `M` with a precomputed Gateaux derivative `D_g_M`).
* `AutoDebiasMeanRepresentation` — the automatic-debiasing pairing witness
  `α₀ : X → ℝ` characterised by `D_g M(θ₀, g₀)[ν] = ∫ α₀ · γ_target ν dP_X`.
* `autoDebiasedScore`, `autoDebiasedMoment` — the debiased score and its
  population moment.
* Three orthogonality lemmas: mean-zero plus two directional zeros.
* `genRieszLoss`, `finDiffRieszLoss` — population and finite-difference
  Riesz objectives for fitting the automatic-debiasing representer.

The structure mirrors `LinRegFnSys` (defined in `AutoDebias/Linear.lean`)
but with `m_lin → m` (a moment depending on `θ` as well) and
`L_of_m → D_g_M`.
-/

module
public import Causalean.Estimation.OrthogonalMoments.AutoDebias.Linear
public import Causalean.Estimation.OrthogonalMoments.MomentFunctional
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-! # Automatic Debiasing for General Moments

This file extends the automatic-debiasing construction from linear regression
functionals to general scalar moment equations with a regression nuisance. It
packages the moment system, the mean-pairing correction, and the resulting
orthogonality identities used to build debiased scores, together with
population and finite-difference Riesz objectives for representer fitting. -/

@[expose] public section

namespace Causalean.Estimation.OrthogonalMoments.AutoDebias

open MeasureTheory

/-- **Regression-nuisance moment system.** Bundles an observation space with an induced
covariate space, an outcome variable, a regression target functional on a normed nuisance
class, the true nuisance and true scalar parameter, a population moment functional of the
parameter and nuisance, and an observation-level moment kernel that averages to it; the
regression target is required [additive](hyp:γ_target_add) and [homogeneous](hyp:γ_target_smul)
in its nuisance argument and [measurable](hyp:γ_target_meas), [the population moment vanishes at
the truth](hyp:M_truth), the
supplied Gateaux derivative of the moment at the truth [is the actual derivative of the
population moment along every nuisance direction](hyp:D_g_M_hasDerivAt), the kernel is
[measurable](hyp:m_meas) and [integrates against the observation measure to the population
moment](hyp:m_population), [the covariate measure is the pushforward of the observation
measure under the projection](hyp:pushforward), and [the regression residual at the truth,
weighted by any measurable integrable function of the covariates, integrates to
zero](hyp:regression_resid_orthog).

A bundle packaging the data + regression infrastructure of `LinRegFnSys`
together with:

* a scalar parameter truth `θ₀ : ℝ`;
* a population moment functional `M : ℝ × H → ℝ` satisfying
  `M(θ₀, g₀) = 0`;
* a precomputed Gateaux derivative `D_g_M : H → ℝ` representing
  `D_g M(θ₀, g₀)[ν]`;
* an observation-level kernel `m : H → Z → ℝ → ℝ` satisfying
  `M(θ, g) = ∫ m(g, z, θ) dP_Z`.

To keep universe parameters tame, every type, instance, and function is
declared as a field of the structure. -/
structure RegNuisanceMomentSys where
  Z : Type*
  [Z_meas : MeasurableSpace Z]
  P_Z : Measure Z
  [P_Z_prob : IsProbabilityMeasure P_Z]
  X : Type*
  [X_meas : MeasurableSpace X]
  P_X : Measure X
  H : Type*
  [H_addCommGroup : AddCommGroup H]
  [H_module : Module ℝ H]
  proj_X : Z → X
  proj_X_meas : Measurable proj_X
  Y_obs : Z → ℝ
  Y_obs_meas : Measurable Y_obs
  γ_target : H → X → ℝ
  γ_target_meas : ∀ γ, Measurable (γ_target γ)
  γ_target_add : ∀ (γ₁ γ₂ : H) (x : X),
    γ_target (γ₁ + γ₂) x = γ_target γ₁ x + γ_target γ₂ x
  γ_target_smul : ∀ (c : ℝ) (γ : H) (x : X),
    γ_target (c • γ) x = c * γ_target γ x
  g₀ : H
  θ₀ : ℝ
  M : ℝ → H → ℝ
  M_truth : M θ₀ g₀ = 0
  D_g_M : H → ℝ
  D_g_M_hasDerivAt : ∀ ν : H,
    HasDerivAt (fun r : ℝ => M θ₀ (g₀ + r • ν)) (D_g_M ν) 0
  m : H → Z → ℝ → ℝ
  m_meas : ∀ g θ, Measurable (fun z => m g z θ)
  m_population : ∀ g θ, M θ g = ∫ z, m g z θ ∂P_Z
  pushforward : P_X = P_Z.map proj_X
  regression_resid_orthog :
    ∀ α : X → ℝ, Measurable α →
      Integrable (fun z => α (proj_X z) * (Y_obs z - γ_target g₀ (proj_X z))) P_Z →
      ∫ z, α (proj_X z) * (Y_obs z - γ_target g₀ (proj_X z)) ∂P_Z = 0

attribute [instance] RegNuisanceMomentSys.Z_meas RegNuisanceMomentSys.P_Z_prob
  RegNuisanceMomentSys.X_meas RegNuisanceMomentSys.H_addCommGroup
  RegNuisanceMomentSys.H_module

attribute [fun_prop] RegNuisanceMomentSys.proj_X_meas RegNuisanceMomentSys.Y_obs_meas
  RegNuisanceMomentSys.γ_target_meas RegNuisanceMomentSys.m_meas

/-- For [a regression-nuisance moment system](hyp:S), [a scalar](hyp:c), and [a
nuisance direction](hyp:ν), [the supplied nuisance derivative is homogeneous in
its direction](goal). This is derived from uniqueness of the one-dimensional
derivative rather than stored as an independent structure field. -/
theorem RegNuisanceMomentSys.D_g_M_smul (S : RegNuisanceMomentSys)
    (c : ℝ) (ν : S.H) : S.D_g_M (c • ν) = c * S.D_g_M ν := by
  have hc : HasDerivAt (fun r : ℝ => r * c) c 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const c
  have hcomp : HasDerivAt
      ((fun q : ℝ => S.M S.θ₀ (S.g₀ + q • ν)) ∘ fun r : ℝ => r * c)
      (S.D_g_M ν * c) 0 :=
    _root_.HasDerivAt.comp_of_eq (𝕜 := ℝ) (𝕜' := ℝ)
      (h := fun r : ℝ => r * c)
      (h₂ := fun q : ℝ => S.M S.θ₀ (S.g₀ + q • ν))
      (y := 0) 0 (S.D_g_M_hasDerivAt ν) hc (by ring)
  have hcomp' : HasDerivAt
      (fun r : ℝ => S.M S.θ₀ (S.g₀ + (r * c) • ν))
      (c * S.D_g_M ν) 0 := by
    change HasDerivAt
      (fun r : ℝ => S.M S.θ₀ (S.g₀ + (r * c) • ν))
      (S.D_g_M ν * c) 0 at hcomp
    simpa only [mul_comm] using hcomp
  have heq :
      (fun r : ℝ => S.M S.θ₀ (S.g₀ + r • (c • ν))) =
        fun r : ℝ => S.M S.θ₀ (S.g₀ + (r * c) • ν) := by
    funext r
    rw [smul_smul]
  exact (S.D_g_M_hasDerivAt (c • ν)).unique <| by
    rw [heq]
    exact hcomp'

/-- For [a regression-nuisance moment system](hyp:S), an
automatic-debiasing mean-pairing witness stores a function
[α₀](hyp:α₀) on the covariate space that is [measurable](hyp:α₀_meas) and
[integrable against the covariate measure](hyp:α₀_integrable), and that
[represents the Gateaux derivative of the population moment at the truth, in
every direction, as the integral pairing of α₀ against the regression target
evaluated in that direction](hyp:representation).

A measurable, integrable `α₀ : X → ℝ` satisfying the displayed integral
identity. The structure does not assert square-integrability of the factors. -/
structure AutoDebiasMeanRepresentation (S : RegNuisanceMomentSys) where
  α₀ : S.X → ℝ
  α₀_meas : Measurable α₀
  α₀_integrable : Integrable α₀ S.P_X
  representation : ∀ ν : S.H, S.D_g_M ν = ∫ x, α₀ x * S.γ_target ν x ∂S.P_X

/-- For a [regression-nuisance moment system](hyp:S), a [regression nuisance
function](hyp:g), a [candidate representer on the covariate space](hyp:α), a [scalar target
value](hyp:θ), and an [observation](hyp:z), the [automatically debiased score](goal) is the
baseline moment contribution plus the candidate representer evaluated at the observation's
covariates times the observed-outcome residual from the regression target.

**Automatically debiased score** (observation-level form):

  `m(g, z, θ) + α(proj_X z) · (Y_obs z − γ_target g (proj_X z))`. -/
noncomputable def autoDebiasedScore (S : RegNuisanceMomentSys)
    (g : S.H) (α : S.X → ℝ) (θ : ℝ) (z : S.Z) : ℝ :=
  S.m g z θ + α (S.proj_X z) * (S.Y_obs z - S.γ_target g (S.proj_X z))

/-- For a [regression-nuisance moment system](hyp:S), a [regression nuisance
function](hyp:g), a [candidate representer on the covariate space](hyp:α), and a [scalar
target value](hyp:θ), the [automatically debiased population moment](goal) is the expectation
of the automatically debiased score under the system's observation distribution.

**Automatically debiased moment** (population form):

  `∫ z, autoDebiasedScore S g α θ z ∂P_Z`,

equivalently `M(θ, g) + ∫ α(X) · (Y − g(X)) dP_Z`. -/
noncomputable def autoDebiasedMoment (S : RegNuisanceMomentSys)
    (g : S.H) (α : S.X → ℝ) (θ : ℝ) : ℝ :=
  ∫ z, autoDebiasedScore S g α θ z ∂S.P_Z

/-- **Mean-zero of the debiased moment at the truth.** Given a regression-nuisance moment
system with representer `rep`, assume [the α₀-weighted regression-residual product at the
truth is integrable](hyp:h_α₀_resid_int) and [the baseline moment integrand at the truth
is integrable](hyp:h_int_m_truth). Then [the automatically debiased population moment,
evaluated at the true nuisance and true parameter, equals zero](goal). -/
theorem autoDebiasedMoment_meanZero_at_truth (S : RegNuisanceMomentSys)
    (rep : AutoDebiasMeanRepresentation S)
    (h_α₀_resid_int :
      Integrable
        (fun z => rep.α₀ (S.proj_X z) * (S.Y_obs z - S.γ_target S.g₀ (S.proj_X z)))
        S.P_Z)
    (h_int_m_truth : Integrable (fun z => S.m S.g₀ z S.θ₀) S.P_Z) :
    autoDebiasedMoment S S.g₀ rep.α₀ S.θ₀ = 0 := by
  unfold autoDebiasedMoment autoDebiasedScore
  rw [integral_add h_int_m_truth h_α₀_resid_int]
  rw [show ∫ z, S.m S.g₀ z S.θ₀ ∂S.P_Z = 0 by
    have h := S.m_population S.g₀ S.θ₀
    rw [← h, S.M_truth]]
  rw [S.regression_resid_orthog rep.α₀ rep.α₀_meas h_α₀_resid_int]
  ring

/-- **Neyman orthogonality in the regression direction.** For [a regression-nuisance moment
system](hyp:S) with [a mean-pairing witness](hyp:rep) and [a perturbation `ν_g`](hyp:ν_g), if the
[moment path is integrable](hyp:h_m_int), the [baseline correction is
integrable](hyp:h_resid_int), and the [directional correction is
integrable](hyp:h_dir_int), then [the Gateaux derivative of the auto-debiased population
moment along `g₀ + rν_g` exists at zero and equals zero](goal). This is the genuine
Chernozhukov--Newey--Singh (2022) Neyman-orthogonality statement: the derivative link in
`RegNuisanceMomentSys.D_g_M_hasDerivAt` and the stored pairing identity cancel
the two path derivatives. -/
theorem autoDebiasedMoment_directional_g_zero (S : RegNuisanceMomentSys)
    (rep : AutoDebiasMeanRepresentation S) (ν_g : S.H)
    (h_m_int : ∀ r : ℝ,
      Integrable (fun z => S.m (S.g₀ + r • ν_g) z S.θ₀) S.P_Z)
    (h_resid_int : Integrable
      (fun z => rep.α₀ (S.proj_X z) *
        (S.Y_obs z - S.γ_target S.g₀ (S.proj_X z))) S.P_Z)
    (h_dir_int : Integrable
      (fun z => rep.α₀ (S.proj_X z) * S.γ_target ν_g (S.proj_X z)) S.P_Z) :
    HasDerivAt
      (fun r : ℝ => autoDebiasedMoment S (S.g₀ + r • ν_g) rep.α₀ S.θ₀)
      0 0 := by
  have hpath (r : ℝ) :
      (fun z => rep.α₀ (S.proj_X z) *
        (S.Y_obs z - S.γ_target (S.g₀ + r • ν_g) (S.proj_X z))) =
      (fun z =>
        rep.α₀ (S.proj_X z) *
            (S.Y_obs z - S.γ_target S.g₀ (S.proj_X z)) -
          r * (rep.α₀ (S.proj_X z) * S.γ_target ν_g (S.proj_X z))) := by
    funext z
    rw [S.γ_target_add, S.γ_target_smul]
    ring
  have hcorr_int (r : ℝ) : Integrable
      (fun z => rep.α₀ (S.proj_X z) *
        (S.Y_obs z - S.γ_target (S.g₀ + r • ν_g) (S.proj_X z))) S.P_Z := by
    rw [hpath]
    exact h_resid_int.sub (h_dir_int.const_mul r)
  have hcorr (r : ℝ) :
      ∫ z, rep.α₀ (S.proj_X z) *
          (S.Y_obs z - S.γ_target (S.g₀ + r • ν_g) (S.proj_X z)) ∂S.P_Z =
        -r * S.D_g_M ν_g := by
    rw [hpath, integral_sub h_resid_int (h_dir_int.const_mul r), integral_const_mul]
    rw [S.regression_resid_orthog rep.α₀ rep.α₀_meas h_resid_int]
    have hmap :
        ∫ z, rep.α₀ (S.proj_X z) * S.γ_target ν_g (S.proj_X z) ∂S.P_Z =
          ∫ x, rep.α₀ x * S.γ_target ν_g x ∂S.P_X := by
      rw [S.pushforward]
      exact (MeasureTheory.integral_map S.proj_X_meas.aemeasurable
        (rep.α₀_meas.mul (S.γ_target_meas ν_g)).aestronglyMeasurable).symm
    rw [hmap, ← rep.representation]
    ring
  have hfun :
      (fun r : ℝ => autoDebiasedMoment S (S.g₀ + r • ν_g) rep.α₀ S.θ₀) =
        (fun r : ℝ => S.M S.θ₀ (S.g₀ + r • ν_g) - r • S.D_g_M ν_g) := by
    funext r
    unfold autoDebiasedMoment autoDebiasedScore
    rw [integral_add (h_m_int r) (hcorr_int r), ← S.m_population, hcorr]
    ring
  rw [hfun]
  have hderiv : HasDerivAt
      ((fun r : ℝ => S.M S.θ₀ (S.g₀ + r • ν_g)) -
        fun r : ℝ => r • S.D_g_M ν_g) 0 0 := by
    simpa only [id_eq, one_smul, sub_self] using
      (S.D_g_M_hasDerivAt ν_g).sub
        ((hasDerivAt_id (0 : ℝ)).smul_const (S.D_g_M ν_g))
  exact hderiv.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)

/-- **Neyman orthogonality in the representer direction.** For [a regression-nuisance
moment system](hyp:S) with [a mean-pairing witness](hyp:rep) and [a representer perturbation
`ν_α`](hyp:ν_α), assume [ν_α is measurable](hyp:hν_α_meas), [the baseline score is
integrable](hyp:h_m_int,h_resid_int), and [the directional residual correction is
integrable](hyp:h_dir_int). Then [the derivative of the automatically debiased moment
along `α₀ + rν_α` exists at zero and equals zero](goal). -/
theorem autoDebiasedMoment_directional_α_zero (S : RegNuisanceMomentSys)
    (rep : AutoDebiasMeanRepresentation S) (ν_α : S.X → ℝ)
    (hν_α_meas : Measurable ν_α)
    (h_m_int : Integrable (fun z => S.m S.g₀ z S.θ₀) S.P_Z)
    (h_resid_int : Integrable
      (fun z => rep.α₀ (S.proj_X z) *
        (S.Y_obs z - S.γ_target S.g₀ (S.proj_X z))) S.P_Z)
    (h_dir_int :
      Integrable
        (fun z => ν_α (S.proj_X z) * (S.Y_obs z - S.γ_target S.g₀ (S.proj_X z)))
        S.P_Z) :
    HasDerivAt
      (fun r : ℝ => autoDebiasedMoment S S.g₀
        (fun x => rep.α₀ x + r * ν_α x) S.θ₀) 0 0 := by
  have hdir :
      ∫ z, ν_α (S.proj_X z) *
        (S.Y_obs z - S.γ_target S.g₀ (S.proj_X z)) ∂S.P_Z = 0 :=
    S.regression_resid_orthog ν_α hν_α_meas h_dir_int
  have hfun :
      (fun r : ℝ => autoDebiasedMoment S S.g₀
        (fun x => rep.α₀ x + r * ν_α x) S.θ₀) =
      fun r : ℝ => autoDebiasedMoment S S.g₀ rep.α₀ S.θ₀ + r * 0 := by
    funext r
    unfold autoDebiasedMoment autoDebiasedScore
    have hbase := h_m_int.add h_resid_int
    calc
      _ = ∫ z, (S.m S.g₀ z S.θ₀ + rep.α₀ (S.proj_X z) *
            (S.Y_obs z - S.γ_target S.g₀ (S.proj_X z))) +
          r * (ν_α (S.proj_X z) *
            (S.Y_obs z - S.γ_target S.g₀ (S.proj_X z))) ∂S.P_Z := by
        apply integral_congr_ae
        filter_upwards with z
        ring
      _ = (∫ z, S.m S.g₀ z S.θ₀ + rep.α₀ (S.proj_X z) *
            (S.Y_obs z - S.γ_target S.g₀ (S.proj_X z)) ∂S.P_Z) +
          ∫ z, r * (ν_α (S.proj_X z) *
            (S.Y_obs z - S.γ_target S.g₀ (S.proj_X z))) ∂S.P_Z :=
        integral_add hbase (h_dir_int.const_mul r)
      _ = _ := by rw [integral_const_mul, hdir]
  rw [hfun]
  simpa using (hasDerivAt_const (x := (0 : ℝ))
    (c := autoDebiasedMoment S S.g₀ rep.α₀ S.θ₀))

/-- **Joint Neyman orthogonality.** For [a regression-nuisance moment
system](hyp:S) with [a mean-pairing witness](hyp:rep), a [regression direction](hyp:ν_g),
and a [measurable representer direction](hyp:ν_α,hν_α_meas), assume
[integrability of the moment path and all first- and second-order correction
terms](hyp:h_m_int,h_resid_int,h_g_dir_int,h_α_dir_int,h_cross_int).
Then [the automatically debiased moment has derivative zero when both nuisances
move simultaneously along `(ν_g,ν_α)`](goal). -/
theorem autoDebiasedMoment_directional_zero (S : RegNuisanceMomentSys)
    (rep : AutoDebiasMeanRepresentation S) (ν_g : S.H) (ν_α : S.X → ℝ)
    (hν_α_meas : Measurable ν_α)
    (h_m_int : ∀ r : ℝ,
      Integrable (fun z => S.m (S.g₀ + r • ν_g) z S.θ₀) S.P_Z)
    (h_resid_int : Integrable
      (fun z => rep.α₀ (S.proj_X z) *
        (S.Y_obs z - S.γ_target S.g₀ (S.proj_X z))) S.P_Z)
    (h_g_dir_int : Integrable
      (fun z => rep.α₀ (S.proj_X z) * S.γ_target ν_g (S.proj_X z)) S.P_Z)
    (h_α_dir_int : Integrable
      (fun z => ν_α (S.proj_X z) *
        (S.Y_obs z - S.γ_target S.g₀ (S.proj_X z))) S.P_Z)
    (h_cross_int : Integrable
      (fun z => ν_α (S.proj_X z) * S.γ_target ν_g (S.proj_X z)) S.P_Z) :
    HasDerivAt
      (fun r : ℝ => autoDebiasedMoment S (S.g₀ + r • ν_g)
        (fun x => rep.α₀ x + r * ν_α x) S.θ₀) 0 0 := by
  have hg := autoDebiasedMoment_directional_g_zero S rep ν_g h_m_int
    h_resid_int h_g_dir_int
  have hαzero :
      ∫ z, ν_α (S.proj_X z) *
        (S.Y_obs z - S.γ_target S.g₀ (S.proj_X z)) ∂S.P_Z = 0 :=
    S.regression_resid_orthog ν_α hν_α_meas h_α_dir_int
  let K : ℝ := ∫ z, ν_α (S.proj_X z) * S.γ_target ν_g (S.proj_X z) ∂S.P_Z
  have hfun :
      (fun r : ℝ => autoDebiasedMoment S (S.g₀ + r • ν_g)
        (fun x => rep.α₀ x + r * ν_α x) S.θ₀) =
      fun r : ℝ => autoDebiasedMoment S (S.g₀ + r • ν_g) rep.α₀ S.θ₀ - r ^ 2 * K := by
    funext r
    have hαpath :
        (fun z => ν_α (S.proj_X z) *
          (S.Y_obs z - S.γ_target (S.g₀ + r • ν_g) (S.proj_X z))) =
        (fun z => ν_α (S.proj_X z) *
          (S.Y_obs z - S.γ_target S.g₀ (S.proj_X z)) -
          r * (ν_α (S.proj_X z) * S.γ_target ν_g (S.proj_X z))) := by
      funext z
      rw [S.γ_target_add, S.γ_target_smul]
      ring
    have hαpath_int : Integrable
        (fun z => ν_α (S.proj_X z) *
          (S.Y_obs z - S.γ_target (S.g₀ + r • ν_g) (S.proj_X z))) S.P_Z := by
      rw [hαpath]
      exact h_α_dir_int.sub (h_cross_int.const_mul r)
    have hαint :
        ∫ z, ν_α (S.proj_X z) *
          (S.Y_obs z - S.γ_target (S.g₀ + r • ν_g) (S.proj_X z)) ∂S.P_Z =
          -r * K := by
      rw [hαpath, integral_sub h_α_dir_int (h_cross_int.const_mul r),
        integral_const_mul, hαzero]
      simp [K]
    have hg_corr_int : Integrable
        (fun z => rep.α₀ (S.proj_X z) *
          (S.Y_obs z - S.γ_target (S.g₀ + r • ν_g) (S.proj_X z))) S.P_Z := by
      rw [show (fun z => rep.α₀ (S.proj_X z) *
          (S.Y_obs z - S.γ_target (S.g₀ + r • ν_g) (S.proj_X z))) =
        (fun z => rep.α₀ (S.proj_X z) *
          (S.Y_obs z - S.γ_target S.g₀ (S.proj_X z)) -
          r * (rep.α₀ (S.proj_X z) * S.γ_target ν_g (S.proj_X z))) by
          funext z
          rw [S.γ_target_add, S.γ_target_smul]
          ring]
      exact h_resid_int.sub (h_g_dir_int.const_mul r)
    unfold autoDebiasedMoment autoDebiasedScore
    calc
      _ = ∫ z, (S.m (S.g₀ + r • ν_g) z S.θ₀ +
            rep.α₀ (S.proj_X z) *
              (S.Y_obs z - S.γ_target (S.g₀ + r • ν_g) (S.proj_X z))) +
          r * (ν_α (S.proj_X z) *
            (S.Y_obs z - S.γ_target (S.g₀ + r • ν_g) (S.proj_X z))) ∂S.P_Z := by
        apply integral_congr_ae
        filter_upwards with z
        ring
      _ = (∫ z, S.m (S.g₀ + r • ν_g) z S.θ₀ +
            rep.α₀ (S.proj_X z) *
              (S.Y_obs z - S.γ_target (S.g₀ + r • ν_g) (S.proj_X z)) ∂S.P_Z) +
          ∫ z, r * (ν_α (S.proj_X z) *
            (S.Y_obs z - S.γ_target (S.g₀ + r • ν_g) (S.proj_X z))) ∂S.P_Z :=
        integral_add ((h_m_int r).add hg_corr_int) (hαpath_int.const_mul r)
      _ = (∫ z, S.m (S.g₀ + r • ν_g) z S.θ₀ +
            rep.α₀ (S.proj_X z) *
              (S.Y_obs z - S.γ_target (S.g₀ + r • ν_g) (S.proj_X z)) ∂S.P_Z) +
          r * (-r * K) := by rw [integral_const_mul, hαint]
      _ = _ := by ring
  rw [hfun]
  have hquad : HasDerivAt (fun r : ℝ => r ^ 2 * K) 0 0 := by
    simpa [pow_two] using
      ((hasDerivAt_id (0 : ℝ)).mul (hasDerivAt_id (0 : ℝ))).mul_const K
  have hsub := hg.sub hquad
  change HasDerivAt
    (fun r : ℝ => autoDebiasedMoment S (S.g₀ + r • ν_g) rep.α₀ S.θ₀ -
      r ^ 2 * K) (0 - 0) 0 at hsub
  simpa using hsub

/-- For a [regression-nuisance moment system](hyp:S) and a [candidate regression function in
its nuisance class](hyp:α), the [general Riesz loss](goal) is the covariate-distribution mean
of the squared regression target of that function minus twice the directional derivative of the
population moment in that function's direction.

**General Riesz loss.**

The loss is `L_M(α) := ∫ (γ_target α x)² dP_X − 2 · D_g_M α`.

The first-order-condition characterisation follows the same representer
geometry as the linear-functional case in `Linear.lean`; this definition is the
general-moment population objective used by downstream automatic-debiasing
instances. -/
noncomputable def genRieszLoss (S : RegNuisanceMomentSys) (α : S.H) : ℝ :=
  ∫ x, (S.γ_target α x) ^ 2 ∂S.P_X - 2 * S.D_g_M α

/-- For a [regression-nuisance moment system](hyp:S), a [sample-indexed auxiliary sample
space](hyp:Ω), [observation-valued sample data](hyp:Z_data), [sample-indexed target
estimates](hyp:θ_hat), [sample-indexed nuisance estimates](hyp:g_hat), [finite-difference
scales](hyp:ε), a [candidate nuisance-direction function](hyp:α), [sample-index sets](hyp:C),
a [sample size](hyp:n), and a [realized auxiliary sample point](hyp:ω), the
[finite-difference representer loss](goal) is the empirical second moment of the candidate's
regression target on the specified index set minus twice the centered finite-difference
approximation to the moment's nuisance derivative at the corresponding estimates.

**Finite-difference representer loss.**

Pure-empirical analogue of `genRieszLoss`, intended as the loss minimised
by RieszNet-type estimators of Chernozhukov, Newey, Quintas-Martínez, and
Syrgkanis. The first term is
the empirical second moment of `γ_target α` on the training fold `C n`;
the second term is a centred finite-difference approximation of
`D_g M(θ̂_n, ĝ_n)[α]` using perturbation scale `ε n`. -/
noncomputable def finDiffRieszLoss (S : RegNuisanceMomentSys)
    {Ω : Type*} (Z_data : ℕ → Ω → S.Z)
    (θ_hat : ℕ → Ω → ℝ) (g_hat : ℕ → Ω → S.H)
    (ε : ℕ → ℝ) (α : S.H) (C : ℕ → Finset ℕ)
    (n : ℕ) (ω : Ω) : ℝ :=
  ((C n).card : ℝ)⁻¹ *
    ∑ i ∈ C n, (S.γ_target α (S.proj_X (Z_data i ω))) ^ 2
  - 2 * (
      ((C n).card : ℝ)⁻¹ *
        ∑ i ∈ C n, S.m (g_hat n ω + ε n • α) (Z_data i ω) (θ_hat n ω)
      - ((C n).card : ℝ)⁻¹ *
        ∑ i ∈ C n, S.m (g_hat n ω - ε n • α) (Z_data i ω) (θ_hat n ω)
    ) / (2 * ε n)

end Causalean.Estimation.OrthogonalMoments.AutoDebias
