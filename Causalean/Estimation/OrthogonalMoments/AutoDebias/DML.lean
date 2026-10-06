module
public import Causalean.Estimation.OrthogonalMoments.AutoDebias.Linear
public import Causalean.Estimation.OrthogonalMoments.DMLCrossFit.JacobianConsistency
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-! # Feasible Automatic Debiasing by Cross-Fitting

This file instantiates K-fold affine-score DML with the observation-level
automatic-debiasing score. Each evaluation fold uses a regression fit and a
Riesz fit trained on its complement. The resulting statistic is feasible: its
constant term is `m(W; ĝ) + α̂(X)(Y - ĝ(X))`, not the population functional
`L(ĝ)`. The main theorem derives the full influence function and the normal
limit follows from the library's asymptotic-linearity CLT. -/

@[expose] public section

namespace Causalean.Estimation.OrthogonalMoments.AutoDebias

open MeasureTheory ProbabilityTheory Filter Topology Causalean.Stat
  Causalean.Estimation.OrthogonalMoments

/-- For a [linear regression-function system](hyp:S), the [joint nuisance
object for feasible automatic debiasing](goal) pairs a regression-function
index with a candidate pairing function on the covariate space. -/
def linAutoNuisance (S : LinRegFnSys) : Type _ := S.H_γ × (S.X → ℝ)

/-- [A linear regression function system](hyp:S) [gives its linear automatic-debiasing nuisance
space an additive commutative group structure](goal). -/
noncomputable instance linAutoNuisance.instAddCommGroup (S : LinRegFnSys) :
    AddCommGroup (linAutoNuisance S) := by
  unfold linAutoNuisance
  infer_instance

/-- [A linear regression function system](hyp:S) [gives its linear automatic-debiasing nuisance
space the pointwise real module structure](goal). -/
noncomputable instance linAutoNuisance.instModule (S : LinRegFnSys) :
    Module ℝ (linAutoNuisance S) := by
  unfold linAutoNuisance
  exact Prod.instModule

/-- Given [an auxiliary sample-space measure](hyp:μ), a [linear regression-functional
system](hyp:S), its [mean-pairing representation](hyp:rep), a [nonnegative nuisance-neighborhood
radius](hyp:ε,hε_nn), and [measurability of every observation-level score](hyp:h_score_meas),
the [affine automatic-debiasing moment](goal) has coefficient minus one and observed constant
term `m(W;γ) + α(X)(Y-γ(X))`.

Its truth is `(g₀, α₀)` and its two seminorms are the L² errors of the
regression and pairing-function fits. -/
noncomputable def linAutoLinearMoment
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (S : LinRegFnSys)
    (rep : MeanPairingRepresentation S.H_γ S.γ_target (L_of_m S) S.P_X)
    (ε : ℝ) (hε_nn : 0 ≤ ε)
    (h_score_meas : ∀ η : linAutoNuisance S, ∀ θ : ℝ,
      Measurable (fun z => linRieszScore S η.1 η.2 θ z)) :
    LinearMoment Ω μ S.Z S.P_Z (linAutoNuisance S) where
  m := fun η z θ => linRieszScore S η.1 η.2 θ z
  η₀ := (S.g₀, rep.α₀)
  θ₀ := L_of_m S S.g₀
  H_ε := {η : linAutoNuisance S |
    (eLpNorm (fun x => S.γ_target η.1 x - S.γ_target S.g₀ x) 2 S.P_X).toReal ≤ ε ∧
    (eLpNorm (fun x => η.2 x - rep.α₀ x) 2 S.P_X).toReal ≤ ε}
  ρ₁ := fun η η' =>
    ⟨(eLpNorm (fun x => S.γ_target η.1 x - S.γ_target η'.1 x) 2 S.P_X).toReal,
      ENNReal.toReal_nonneg⟩
  ρ₂ := fun η η' =>
    ⟨(eLpNorm (fun x => η.2 x - η'.2 x) 2 S.P_X).toReal,
      ENNReal.toReal_nonneg⟩
  m_meas := h_score_meas
  η₀_mem := by
    refine ⟨?_, ?_⟩
    · have hz : (fun x => S.γ_target S.g₀ x - S.γ_target S.g₀ x) =
          (fun _ : S.X => (0 : ℝ)) := by
        funext x
        ring
      rw [hz]
      simp [hε_nn]
    · have hz : (fun x => rep.α₀ x - rep.α₀ x) =
          (fun _ : S.X => (0 : ℝ)) := by
        funext x
        ring
      rw [hz]
      simp [hε_nn]
  linScale := -1
  linScale_ne_zero := by norm_num
  m_a := fun _ _ => -1
  m_b := fun η z =>
    S.m_lin z η.1 + η.2 (S.proj_X z) *
      (S.Y_obs z - S.γ_target η.1 (S.proj_X z))
  m_a_meas := fun _ => measurable_const
  m_b_meas := fun η => by
    simpa [linRieszScore] using h_score_meas η 0
  m_decomp := by
    intro η z θ
    simp [linRieszScore]
    ring
  linScale_eq := by simp

/-- Under the [same inputs as the affine automatic-debiasing moment](hyp:μ,S,rep,ε,hε_nn,h_score_meas),
the [corresponding general moment](goal) forgets only the affine decomposition. -/
noncomputable def linAutoGeneralMoment
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (S : LinRegFnSys)
    (rep : MeanPairingRepresentation S.H_γ S.γ_target (L_of_m S) S.P_X)
    (ε : ℝ) (hε_nn : 0 ≤ ε)
    (h_score_meas : ∀ η : linAutoNuisance S, ∀ θ : ℝ,
      Measurable (fun z => linRieszScore S η.1 η.2 θ z)) :
    GeneralMoment Ω μ S.Z S.P_Z (linAutoNuisance S) :=
  (linAutoLinearMoment μ S rep ε hε_nn h_score_meas).toGeneralMoment

/-- Given [the automatic-debiasing system, representation, neighborhood, and score
regularity inputs](hyp:μ,S,rep,ε,hε_nn,h_score_meas), [an integrable observed linear
functional at the truth](hyp:h_m_lin_int), and [an integrable representer-weighted truth
residual](hyp:h_α₀_resid_int), [the observation-level automatic-debiasing moment is mean
zero at the truth](goal). -/
theorem linAuto_meanZero
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (S : LinRegFnSys)
    (rep : MeanPairingRepresentation S.H_γ S.γ_target (L_of_m S) S.P_X)
    (ε : ℝ) (hε_nn : 0 ≤ ε)
    (h_score_meas : ∀ η : linAutoNuisance S, ∀ θ : ℝ,
      Measurable (fun z => linRieszScore S η.1 η.2 θ z))
    (h_α₀_resid_int : Integrable (fun z => rep.α₀ (S.proj_X z) *
      (S.Y_obs z - S.γ_target S.g₀ (S.proj_X z))) S.P_Z)
    (h_m_lin_int : Integrable (fun z => S.m_lin z S.g₀) S.P_Z) :
    MeanZero (linAutoGeneralMoment μ S rep ε hε_nn h_score_meas) := by
  unfold MeanZero linAutoGeneralMoment
  exact linRieszScore_meanZero S rep h_α₀_resid_int h_m_lin_int

/-- For a [linear regression-functional system](hyp:S), its [mean-pairing
representation](hyp:rep), and a [joint nuisance candidate](hyp:η), the
[integrability and representer-measurability package used by the bilinear remainder](goal)
contains the finite population moments needed to compare observed and population scores;
the regression equation then supplies residual orthogonality. -/
def linAuto_int_pred (S : LinRegFnSys)
    (rep : MeanPairingRepresentation S.H_γ S.γ_target (L_of_m S) S.P_X)
    (η : linAutoNuisance S) : Prop :=
  Integrable (fun z => S.m_lin z η.1) S.P_Z ∧
  Integrable (fun z => S.m_lin z S.g₀) S.P_Z ∧
  Integrable (fun z => η.2 (S.proj_X z) *
    (S.Y_obs z - S.γ_target S.g₀ (S.proj_X z))) S.P_Z ∧
  Integrable (fun z => η.2 (S.proj_X z) * S.γ_target η.1 (S.proj_X z)) S.P_Z ∧
  Integrable (fun z => η.2 (S.proj_X z) * S.γ_target S.g₀ (S.proj_X z)) S.P_Z ∧
  Integrable (fun x => rep.α₀ x * S.γ_target η.1 x) S.P_X ∧
  Integrable (fun x => rep.α₀ x * S.γ_target S.g₀ x) S.P_X ∧
  Integrable η.2 S.P_X ∧
  Integrable (S.γ_target η.1) S.P_X ∧
  Integrable (S.γ_target S.g₀) S.P_X ∧
  Integrable (fun z => rep.α₀ (S.proj_X z) *
    (S.Y_obs z - S.γ_target S.g₀ (S.proj_X z))) S.P_Z ∧
  Measurable η.2

private theorem linRieszScore_integral_eq_populationScore (S : LinRegFnSys)
    (γ : S.H_γ) (α : S.X → ℝ) (θ : ℝ)
    (hm : Integrable (fun z => S.m_lin z γ) S.P_Z)
    (hq : Integrable (fun z => α (S.proj_X z) *
      (S.Y_obs z - S.γ_target γ (S.proj_X z))) S.P_Z) :
    ∫ z, linRieszScore S γ α θ z ∂S.P_Z =
      ∫ z, pairingScore S.γ_target (L_of_m S) S.proj_X S.Y_obs γ α θ z ∂S.P_Z := by
  let q : S.Z → ℝ := fun z => α (S.proj_X z) *
    (S.Y_obs z - S.γ_target γ (S.proj_X z))
  have hq' : Integrable q S.P_Z := hq
  have hobs : ∫ z, linRieszScore S γ α θ z ∂S.P_Z =
      L_of_m S γ + ∫ z, q z ∂S.P_Z - θ := by
    change ∫ z, (S.m_lin z γ + q z) - θ ∂S.P_Z = _
    calc
      _ = (∫ z, S.m_lin z γ + q z ∂S.P_Z) -
            ∫ _ : S.Z, θ ∂S.P_Z :=
        integral_sub (hm.add hq') (integrable_const _)
      _ = ((∫ z, S.m_lin z γ ∂S.P_Z) + ∫ z, q z ∂S.P_Z) -
            ∫ _ : S.Z, θ ∂S.P_Z := by rw [integral_add hm hq']
      _ = _ := by simp [L_of_m]
  have hpop : ∫ z, pairingScore S.γ_target (L_of_m S) S.proj_X S.Y_obs
      γ α θ z ∂S.P_Z = L_of_m S γ + ∫ z, q z ∂S.P_Z - θ := by
    change ∫ z, (L_of_m S γ + q z) - θ ∂S.P_Z = _
    calc
      _ = (∫ z, L_of_m S γ + q z ∂S.P_Z) -
            ∫ _ : S.Z, θ ∂S.P_Z :=
        integral_sub ((integrable_const _).add hq') (integrable_const _)
      _ = ((∫ _ : S.Z, L_of_m S γ ∂S.P_Z) + ∫ z, q z ∂S.P_Z) -
            ∫ _ : S.Z, θ ∂S.P_Z := by
        rw [integral_add (integrable_const _) hq']
      _ = _ := by simp
  exact hobs.trans hpop.symm

private theorem linAuto_bilinearRem_one
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (S : LinRegFnSys)
    (rep : MeanPairingRepresentation S.H_γ S.γ_target (L_of_m S) S.P_X)
    (ε : ℝ) (hε_nn : 0 ≤ ε)
    (h_score_meas : ∀ η : linAutoNuisance S, ∀ θ : ℝ,
      Measurable (fun z => linRieszScore S η.1 η.2 θ z))
    (η : linAutoNuisance S)
    (_hη_mem : η ∈ (linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).H_ε)
    (h_int : linAuto_int_pred S rep η)
    (hγ : MemLp (fun x => S.γ_target η.1 x - S.γ_target S.g₀ x) 2 S.P_X)
    (hα : MemLp (fun x => η.2 x - rep.α₀ x) 2 S.P_X) :
      |∫ z, (linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).m η z
          (linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).θ₀ ∂S.P_Z| ≤
        1 * (eLpNorm (fun x => S.γ_target η.1 x - S.γ_target S.g₀ x)
          2 S.P_X).toReal *
          (eLpNorm (fun x => η.2 x - rep.α₀ x) 2 S.P_X).toReal := by
  rcases h_int with ⟨hm, hm₀, hresidα, hαγ, hαγ₀, hα₀γ, hα₀γ₀,
    hαint, hγint, hγ₀int, hresidα₀, hαmeas⟩
  let dα : S.X → ℝ := fun x => η.2 x - rep.α₀ x
  let dγ : S.X → ℝ := fun x => S.γ_target η.1 x - S.γ_target S.g₀ x
  have horthα₀ : ∫ z, rep.α₀ (S.proj_X z) *
      (S.Y_obs z - S.γ_target S.g₀ (S.proj_X z)) ∂S.P_Z = 0 :=
    S.regression_resid_orthog rep.α₀ rep.α₀_meas hresidα₀
  have horthα : ∫ z, η.2 (S.proj_X z) *
      (S.Y_obs z - S.γ_target S.g₀ (S.proj_X z)) ∂S.P_Z = 0 :=
    S.regression_resid_orthog η.2 hαmeas hresidα
  have hqη : Integrable (fun z => η.2 (S.proj_X z) *
      (S.Y_obs z - S.γ_target η.1 (S.proj_X z))) S.P_Z := by
    refine hresidα.add (hαγ₀.sub hαγ) |>.congr ?_
    filter_upwards with z
    change η.2 (S.proj_X z) *
        (S.Y_obs z - S.γ_target S.g₀ (S.proj_X z)) +
        (η.2 (S.proj_X z) * S.γ_target S.g₀ (S.proj_X z) -
          η.2 (S.proj_X z) * S.γ_target η.1 (S.proj_X z)) =
      η.2 (S.proj_X z) *
        (S.Y_obs z - S.γ_target η.1 (S.proj_X z))
    ring
  have hobsη := linRieszScore_integral_eq_populationScore S η.1 η.2
    (L_of_m S S.g₀) hm hqη
  have hobs₀ := linRieszScore_integral_eq_populationScore S S.g₀ rep.α₀
    (L_of_m S S.g₀) hm₀ hresidα₀
  have hrem_sub :
      (∫ z, linRieszScore S η.1 η.2 (L_of_m S S.g₀) z ∂S.P_Z) -
        (∫ z, linRieszScore S S.g₀ rep.α₀ (L_of_m S S.g₀) z ∂S.P_Z) =
        -∫ x, dα x * dγ x ∂S.P_X := by
    rw [hobsη, hobs₀]
    exact pairingScore_bilinearRem rep S.g₀ η.1 η.2 S.proj_X S.Y_obs
      S.pushforward S.proj_X_meas horthα₀ horthα hresidα hαγ hαγ₀ hα₀γ
      hα₀γ₀ hαint hγint hγ₀int
  have htruth : ∫ z, linRieszScore S S.g₀ rep.α₀ (L_of_m S S.g₀) z ∂S.P_Z = 0 :=
    linRieszScore_meanZero S rep hresidα₀ hm₀
  have hrem : ∫ z, linRieszScore S η.1 η.2 (L_of_m S S.g₀) z ∂S.P_Z =
      -∫ x, dα x * dγ x ∂S.P_X := by linarith
  have hcs : |∫ x, dα x * dγ x ∂S.P_X| ≤
      (eLpNorm dα 2 S.P_X).toReal * (eLpNorm dγ 2 S.P_X).toReal := by
    refine abs_integral_le_integral_abs.trans ?_
    simpa [abs_mul] using integral_abs_mul_le_eLpNorm_mul_eLpNorm
      (ν := S.P_X) (f := dα) (g := dγ) hα hγ
  rw [show (∫ z, (linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).m η z
      (linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).θ₀ ∂S.P_Z) =
      ∫ z, linRieszScore S η.1 η.2 (L_of_m S S.g₀) z ∂S.P_Z by rfl,
    hrem, abs_neg]
  change |∫ x, dα x * dγ x ∂S.P_X| ≤
    1 * (eLpNorm dγ 2 S.P_X).toReal * (eLpNorm dα 2 S.P_X).toReal
  simpa [mul_comm] using hcs

/-- Given [the automatic-debiasing system, representation, neighborhood, and score
regularity inputs](hyp:μ,S,rep,ε,hε_nn,h_score_meas), the [absolute population score
remainder is bounded by the product of its L² regression and Riesz errors](goal) whenever
the displayed candidate satisfies the stated integrability, measurability, and L² conditions. -/
theorem linAuto_bilinearRem
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (S : LinRegFnSys)
    (rep : MeanPairingRepresentation S.H_γ S.γ_target (L_of_m S) S.P_X)
    (ε : ℝ) (hε_nn : 0 ≤ ε)
    (h_score_meas : ∀ η : linAutoNuisance S, ∀ θ : ℝ,
      Measurable (fun z => linRieszScore S η.1 η.2 θ z)) :
    ∃ C : ℝ, ∀ η ∈ (linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).H_ε,
      linAuto_int_pred S rep η →
      MemLp (fun x => S.γ_target η.1 x - S.γ_target S.g₀ x) 2 S.P_X →
      MemLp (fun x => η.2 x - rep.α₀ x) 2 S.P_X →
      |∫ z, (linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).m η z
          (linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).θ₀ ∂S.P_Z| ≤
        C * (((linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).ρ₁ η
          (linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).η₀ : NNReal) : ℝ) *
          (((linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).ρ₂ η
            (linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).η₀ : NNReal) : ℝ) := by
  refine ⟨1, ?_⟩
  intro η hη_mem h_int hγ hα
  change |∫ z, linRieszScore S η.1 η.2 (L_of_m S S.g₀) z ∂S.P_Z| ≤
    1 * (eLpNorm (fun x => S.γ_target η.1 x - S.γ_target S.g₀ x)
      2 S.P_X).toReal * (eLpNorm (fun x => η.2 x - rep.α₀ x) 2 S.P_X).toReal
  exact linAuto_bilinearRem_one μ S rep ε hε_nn h_score_meas
    η hη_mem h_int hγ hα

/-- Given [the automatic-debiasing inputs and foldwise fits](hyp:μ,S,rep,ε,hε_nn,h_score_meas,g_hat,α_hat),
if every fitted pair [lies in the nuisance neighborhood](hyp:hη_mem), [satisfies the
population integrability package](hyp:h_int), and has [square-integrable regression and
Riesz errors](hyp:hγ,hα), then [the population score remainder obeys the bilinear bound
with explicit constant one for every sample size, fold, and realization](goal). -/
theorem linAuto_bilinearRem_at
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (S : LinRegFnSys)
    (rep : MeanPairingRepresentation S.H_γ S.γ_target (L_of_m S) S.P_X)
    (ε : ℝ) (hε_nn : 0 ≤ ε)
    (h_score_meas : ∀ η : linAutoNuisance S, ∀ θ : ℝ,
      Measurable (fun z => linRieszScore S η.1 η.2 θ z))
    {K : ℕ} (g_hat : ℕ → Fin K → Ω → S.H_γ)
    (α_hat : ℕ → Fin K → Ω → S.X → ℝ)
    (hη_mem : ∀ n k ω, (g_hat n k ω, α_hat n k ω) ∈
      (linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).H_ε)
    (h_int : ∀ n k ω, linAuto_int_pred S rep (g_hat n k ω, α_hat n k ω))
    (hγ : ∀ n k ω, MemLp (fun x => S.γ_target (g_hat n k ω) x -
      S.γ_target S.g₀ x) 2 S.P_X)
    (hα : ∀ n k ω, MemLp (fun x => α_hat n k ω x - rep.α₀ x) 2 S.P_X) :
    ∀ n k ω,
      |∫ z, linRieszScore S (g_hat n k ω) (α_hat n k ω)
          (L_of_m S S.g₀) z ∂S.P_Z| ≤
        1 * (eLpNorm (fun x => S.γ_target (g_hat n k ω) x -
          S.γ_target S.g₀ x) 2 S.P_X).toReal *
          (eLpNorm (fun x => α_hat n k ω x - rep.α₀ x) 2 S.P_X).toReal := by
  intro n k ω
  exact linAuto_bilinearRem_one μ S rep ε hε_nn h_score_meas
    (g_hat n k ω, α_hat n k ω) (hη_mem n k ω)
    (h_int n k ω) (hγ n k ω) (hα n k ω)

/-- Given [a linear regression-functional system, its mean-pairing representation, and score
regularity inputs](hyp:S,rep,ε,hε_nn,h_score_meas), an [i.i.d. sample](hyp:sample), a
[K-fold split](hyp:split), and fold-specific [regression fits](hyp:g_hat) and [Riesz
fits](hyp:α_hat), the [feasible cross-fitted automatic-debiasing estimator](goal) solves the
fold-averaged empirical score equation.

Because the score coefficient is `-1`, each nonempty evaluation fold
contributes the average of
`m(Wᵢ; ĝ) + α̂(Xᵢ)(Yᵢ-ĝ(Xᵢ))`. Neither `L(ĝ)` nor the population representer
is substituted for a fitted nuisance. -/
noncomputable def linAutoDMLEstimator
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (S : LinRegFnSys)
    (rep : MeanPairingRepresentation S.H_γ S.γ_target (L_of_m S) S.P_X)
    (ε : ℝ) (hε_nn : 0 ≤ ε)
    (h_score_meas : ∀ η : linAutoNuisance S, ∀ θ : ℝ,
      Measurable (fun z => linRieszScore S η.1 η.2 θ z))
    (sample : IIDSample Ω S.Z μ S.P_Z) {K : ℕ}
    (split : KFoldSplit sample K)
    (g_hat : ℕ → Fin K → Ω → S.H_γ)
    (α_hat : ℕ → Fin K → Ω → S.X → ℝ) : ℕ → Ω → ℝ :=
  feasibleCrossFitLinearDML (linAutoLinearMoment μ S rep ε hε_nn h_score_meas)
    sample split (fun n k ω => (g_hat n k ω, α_hat n k ω))

/-- For [a linear regression-functional system, its mean-pairing representation, and score
regularity inputs](hyp:S,rep,ε,hε_nn,h_score_meas), an [i.i.d. sample with a K-fold split and
fold-specific nuisance fits](hyp:sample,split,g_hat,α_hat), a [positive number of
folds](hyp:hK_pos), a [sample-size index](hyp:n), a [sample realization](hyp:ω), and
[nonempty evaluation folds](hyp:hfold), [the estimator equals the average of the foldwise
observed automatic-debiasing scores](goal).

Thus its summands are exactly
`m(Wᵢ; ĝ) + α̂(Xᵢ)(Yᵢ-ĝ(Xᵢ))`; no population functional is evaluated at a
fitted regression. -/
theorem linAutoDMLEstimator_eq_foldAverage
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (S : LinRegFnSys)
    (rep : MeanPairingRepresentation S.H_γ S.γ_target (L_of_m S) S.P_X)
    (ε : ℝ) (hε_nn : 0 ≤ ε)
    (h_score_meas : ∀ η : linAutoNuisance S, ∀ θ : ℝ,
      Measurable (fun z => linRieszScore S η.1 η.2 θ z))
    (sample : IIDSample Ω S.Z μ S.P_Z) {K : ℕ} (hK_pos : 0 < K)
    (split : KFoldSplit sample K)
    (g_hat : ℕ → Fin K → Ω → S.H_γ)
    (α_hat : ℕ → Fin K → Ω → S.X → ℝ)
    (n : ℕ) (ω : Ω) (hfold : ∀ k, (split.fold n k).Nonempty) :
    linAutoDMLEstimator S rep ε hε_nn h_score_meas sample split g_hat α_hat n ω =
      (K : ℝ)⁻¹ * ∑ k : Fin K,
        ((split.fold n k).card : ℝ)⁻¹ * ∑ i ∈ split.fold n k,
          (S.m_lin (sample.Z i ω) (g_hat n k ω) +
            α_hat n k ω (S.proj_X (sample.Z i ω)) *
              (S.Y_obs (sample.Z i ω) -
                S.γ_target (g_hat n k ω) (S.proj_X (sample.Z i ω)))) := by
  have hcoeff : ∀ k : Fin K,
      ((split.fold n k).card : ℝ)⁻¹ *
        ∑ i ∈ split.fold n k, (-1 : ℝ) = -1 := by
    intro k
    have hcard : ((split.fold n k).card : ℝ) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero.mpr (hfold k)
    rw [Finset.sum_const]
    simp [nsmul_eq_mul, hcard]
  unfold linAutoDMLEstimator feasibleCrossFitLinearDML
  simp only [linAutoLinearMoment]
  rw [Finset.sum_congr rfl (fun k _ => hcoeff k)]
  have hKne : (K : ℝ) ≠ 0 := by exact_mod_cast hK_pos.ne'
  simp [hKne]

private theorem isLittleOp_zero_one {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) : IsLittleOp (fun _ (_ : Ω) => (0 : ℝ)) (fun _ => (1 : ℝ)) μ := by
  intro δ hδ
  have hempty : {ω : Ω | δ * (1 : ℝ) ≤ ‖(0 : ℝ)‖} = (∅ : Set Ω) := by
    ext ω
    simp only [mul_one, norm_zero, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact not_le_of_gt hδ
  change Tendsto (fun _ : ℕ => μ {ω : Ω | δ * (1 : ℝ) ≤ ‖(0 : ℝ)‖}) atTop (𝓝 0)
  rw [hempty]
  simp

/-- Under [the sampling measure](hyp:μ), for [a linear regression-functional system and
foldwise nuisance fits](hyp:S,rep,g_hat,α_hat),
if the [L² score difference is uniformly Lipschitz in the two nuisance errors](hyp:Cscore,hCscore,h_score_lipschitz)
and the [regression and Riesz errors are each `o_P(1)`](hyp:h_g_rate,h_α_rate), then [the
L² score difference is `o_P(1)`](goal). -/
theorem linAuto_score_diff_isLittleOp_one
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (S : LinRegFnSys)
    (rep : MeanPairingRepresentation S.H_γ S.γ_target (L_of_m S) S.P_X)
    {K : ℕ} (g_hat : ℕ → Fin K → Ω → S.H_γ)
    (α_hat : ℕ → Fin K → Ω → S.X → ℝ)
    (Cscore : ℝ) (hCscore : 0 < Cscore)
    (h_score_lipschitz : ∀ n k ω,
      |(eLpNorm (fun z =>
        linRieszScore S (g_hat n k ω) (α_hat n k ω) (L_of_m S S.g₀) z -
          linRieszScore S S.g₀ rep.α₀ (L_of_m S S.g₀) z) 2 S.P_Z).toReal| ≤
        Cscore * |(eLpNorm (fun x => S.γ_target (g_hat n k ω) x -
          S.γ_target S.g₀ x) 2 S.P_X).toReal +
          (eLpNorm (fun x => α_hat n k ω x - rep.α₀ x) 2 S.P_X).toReal|)
    (h_g_rate : ∀ k, IsLittleOp (fun n ω =>
      (eLpNorm (fun x => S.γ_target (g_hat n k ω) x - S.γ_target S.g₀ x)
        2 S.P_X).toReal) (fun _ => (1 : ℝ)) μ)
    (h_α_rate : ∀ k, IsLittleOp (fun n ω =>
      (eLpNorm (fun x => α_hat n k ω x - rep.α₀ x) 2 S.P_X).toReal)
        (fun _ => (1 : ℝ)) μ) :
    ∀ k, IsLittleOp (fun n ω =>
      (eLpNorm (fun z => linRieszScore S (g_hat n k ω) (α_hat n k ω)
        (L_of_m S S.g₀) z - linRieszScore S S.g₀ rep.α₀
          (L_of_m S S.g₀) z) 2 S.P_Z).toReal) (fun _ => (1 : ℝ)) μ := by
  intro k
  apply IsLittleOp.of_abs_le_const_mul_one hCscore
    (IsLittleOp.add_one (h_g_rate k) (h_α_rate k))
  exact fun n ω => h_score_lipschitz n k ω

/-- For [a linear regression-functional system, its mean-pairing representation, and score
regularity inputs](hyp:S,rep,ε,hε_nn,h_score_meas), an [i.i.d. sample, K-fold split, and
fold-specific regression and pairing-function
fits](hyp:sample,split,g_hat,α_hat), under [at least two
folds](hyp:hK_pos), [mean zero and finite variance](hyp:hMZ,hFV), [foldwise neighborhood,
integrability, and square-integrability conditions](hyp:hη_mem,h_int_pred,h_g_memLp,h_α_memLp),
[the joint and uncurried cross-fit measurability and moment
conditions](hyp:h_m_meas,h_m_train_uncurry,h_m_int,h_m_sq_int), [a curried
training-complement witness retained for compatibility](hyp:h_m_train),
[uniform L² score stability](hyp:Cscore,hCscore,h_score_lipschitz), [L² consistency of the regression fit](hyp:h_g_rate),
[L² consistency of the fitted pairing function](hyp:h_α_rate), [the parametric product
rate](hyp:h_product_rate), and [influence and oracle measurability](hyp:hψ_meas,hOracle_meas),
[the feasible K-fold automatic-debiasing estimator is asymptotically linear with the full
influence function](goal).

The cross-fit proof uses the uncurried product-measurability witness; the
separate curried witness does not enter that argument.

The empirical-process term is controlled by complementary-fold measurability
inside `crossFitOneStepOracleDML_isAsymLinear_of_everywhere`; the affine-score transfer then
replaces the proof linearization by the feasible empirical-moment solution. -/
theorem linAutoDML_asymptoticLinear
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [StandardBorelSpace Ω] [IsFiniteMeasure μ] [IsProbabilityMeasure μ]
    (S : LinRegFnSys)
    (rep : MeanPairingRepresentation S.H_γ S.γ_target (L_of_m S) S.P_X)
    (ε : ℝ) (hε_nn : 0 ≤ ε)
    (h_score_meas : ∀ η : linAutoNuisance S, ∀ θ : ℝ,
      Measurable (fun z => linRieszScore S η.1 η.2 θ z))
    (sample : IIDSample Ω S.Z μ S.P_Z) {K : ℕ} (hK_pos : 1 < K)
    (split : KFoldSplit sample K)
    (g_hat : ℕ → Fin K → Ω → S.H_γ)
    (α_hat : ℕ → Fin K → Ω → S.X → ℝ)
    (hMZ : MeanZero (linAutoGeneralMoment μ S rep ε hε_nn h_score_meas))
    (hFV : Integrable (fun z => (linAutoInfluence S rep z) ^ 2) S.P_Z)
    (hη_mem : ∀ n k ω, (g_hat n k ω, α_hat n k ω) ∈
      (linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).H_ε)
    (h_int_pred : ∀ n k ω,
      linAuto_int_pred S rep (g_hat n k ω, α_hat n k ω))
    (h_g_memLp : ∀ n k ω, MemLp (fun x => S.γ_target (g_hat n k ω) x -
      S.γ_target S.g₀ x) 2 S.P_X)
    (h_α_memLp : ∀ n k ω,
      MemLp (fun x => α_hat n k ω x - rep.α₀ x) 2 S.P_X)
    (h_m_meas : ∀ n k, Measurable (fun p : Ω × S.Z =>
      linRieszScore S (g_hat n k p.1) (α_hat n k p.1) (L_of_m S S.g₀) p.2))
    (h_m_train : ∀ n k,
      Measurable[MeasurableSpace.comap
        (fun ω (i : split.trainComplement n k) => sample.Z i ω) inferInstance]
        (fun ω z => linRieszScore S (g_hat n k ω) (α_hat n k ω)
          (L_of_m S S.g₀) z))
    (h_m_train_uncurry : ∀ n k,
      Measurable[(MeasurableSpace.comap
          (fun ω (i : split.trainComplement n k) => sample.Z i ω) inferInstance).prod
        (inferInstance : MeasurableSpace S.Z)]
        (fun p : Ω × S.Z => linRieszScore S (g_hat n k p.1) (α_hat n k p.1)
          (L_of_m S S.g₀) p.2))
    (h_m_int : ∀ n k ω, Integrable (fun z =>
      linRieszScore S (g_hat n k ω) (α_hat n k ω) (L_of_m S S.g₀) z) S.P_Z)
    (h_m_sq_int : ∀ n k ω, Integrable (fun z =>
      (linRieszScore S (g_hat n k ω) (α_hat n k ω)
        (L_of_m S S.g₀) z) ^ 2) S.P_Z)
    (Cscore : ℝ) (hCscore : 0 < Cscore)
    (h_score_lipschitz : ∀ n k ω,
      |(eLpNorm (fun z =>
        linRieszScore S (g_hat n k ω) (α_hat n k ω) (L_of_m S S.g₀) z -
          linRieszScore S S.g₀ rep.α₀ (L_of_m S S.g₀) z) 2 S.P_Z).toReal| ≤
        Cscore * |(eLpNorm (fun x => S.γ_target (g_hat n k ω) x -
          S.γ_target S.g₀ x) 2 S.P_X).toReal +
          (eLpNorm (fun x => α_hat n k ω x - rep.α₀ x) 2 S.P_X).toReal|)
    (h_g_rate : ∀ k, IsLittleOp (fun n ω =>
      (eLpNorm (fun x => S.γ_target (g_hat n k ω) x - S.γ_target S.g₀ x)
        2 S.P_X).toReal) (fun _ => (1 : ℝ)) μ)
    (h_α_rate : ∀ k, IsLittleOp (fun n ω =>
      (eLpNorm (fun x => α_hat n k ω x - rep.α₀ x) 2 S.P_X).toReal)
        (fun _ => (1 : ℝ)) μ)
    (h_product_rate : ∀ k, IsLittleOp (fun n ω =>
      (eLpNorm (fun x => S.γ_target (g_hat n k ω) x - S.γ_target S.g₀ x)
        2 S.P_X).toReal *
      (eLpNorm (fun x => α_hat n k ω x - rep.α₀ x) 2 S.P_X).toReal)
        (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) μ)
    (hψ_meas : Measurable (linAutoInfluence S rep))
    (hOracle_meas : ∀ n, AEMeasurable
      (IsAsymLinear.rescaledEstimator
        (crossFitOneStepOracleDML
          (linAutoGeneralMoment μ S rep ε hε_nn h_score_meas) sample split
          (fun n k ω => (g_hat n k ω, α_hat n k ω)))
        (L_of_m S S.g₀) (fun n => Finset.range n) n) μ) :
    IsAsymLinear
      (linAutoDMLEstimator S rep ε hε_nn h_score_meas sample split g_hat α_hat)
      (L_of_m S S.g₀)
      (linAutoInfluence S rep)
      sample (fun n => Finset.range n) := by
  let M := linAutoLinearMoment μ S rep ε hε_nn h_score_meas
  let η_hat : ℕ → Fin K → Ω → linAutoNuisance S :=
    fun n k ω => (g_hat n k ω, α_hat n k ω)
  have hBR_at := linAuto_bilinearRem_at μ S rep ε hε_nn h_score_meas
    g_hat α_hat hη_mem h_int_pred h_g_memLp h_α_memLp
  have h_score_diff_rate := linAuto_score_diff_isLittleOp_one μ S rep g_hat α_hat
    Cscore hCscore h_score_lipschitz h_g_rate h_α_rate
  have ha : MemLp (M.m_a M.η₀) 2 S.P_Z := by
    simpa [M, linAutoLinearMoment] using
      (memLp_const (-1 : ℝ) : MemLp (fun _ : S.Z => (-1 : ℝ)) 2 S.P_Z)
  have hΔa_meas : ∀ n k, Measurable (Function.uncurry
      (fun ω z => M.m_a (η_hat n k ω) z - M.m_a M.η₀ z)) := by
    intro n k
    dsimp [M, η_hat, linAutoLinearMoment]
    fun_prop
  have hΔa_train : ∀ n k,
      Measurable[MeasurableSpace.comap
        (fun ω (i : split.trainComplement n k) => sample.Z i ω) inferInstance]
        (fun ω z => M.m_a (η_hat n k ω) z - M.m_a M.η₀ z) := by
    intro n k
    simpa [M, η_hat, linAutoLinearMoment] using
      (measurable_const : Measurable[MeasurableSpace.comap
        (fun ω (i : split.trainComplement n k) => sample.Z i ω) inferInstance]
        (fun _ : Ω => (fun _ : S.Z => (0 : ℝ))))
  have hΔa_uncurry : ∀ n k,
      Measurable[(MeasurableSpace.comap
          (fun ω (i : split.trainComplement n k) => sample.Z i ω) inferInstance).prod
        (inferInstance : MeasurableSpace S.Z)]
        (Function.uncurry
          (fun ω z => M.m_a (η_hat n k ω) z - M.m_a M.η₀ z)) := by
    intro n k
    dsimp [M, η_hat, linAutoLinearMoment]
    fun_prop
  have hΔa_memLp : ∀ n k ω,
      MemLp (fun z => M.m_a (η_hat n k ω) z - M.m_a M.η₀ z) 2 S.P_Z := by
    intro n k ω
    simpa [M, η_hat, linAutoLinearMoment] using
      (memLp_const (0 : ℝ) : MemLp (fun _ : S.Z => (0 : ℝ)) 2 S.P_Z)
  have hzero := isLittleOp_zero_one (Ω := Ω) μ
  have hΔa_rate : ∀ k, IsLittleOp (fun n ω =>
      (eLpNorm (fun z => M.m_a (η_hat n k ω) z - M.m_a M.η₀ z)
        2 S.P_Z).toReal) (fun _ => (1 : ℝ)) μ := by
    intro k
    simpa [M, η_hat, linAutoLinearMoment] using hzero
  have hΔa_bias : ∀ k, IsLittleOp (fun n ω =>
      ∫ z, (M.m_a (η_hat n k ω) z - M.m_a M.η₀ z) ∂S.P_Z)
        (fun _ => (1 : ℝ)) μ := by
    intro k
    simpa [M, η_hat, linAutoLinearMoment] using hzero
  have hψM : Measurable (fun z => -M.linScaleInv * M.m M.η₀ z M.θ₀) := by
    simpa [M, linAutoLinearMoment, GeneralMoment.linScaleInv] using hψ_meas
  have hFV' : Integrable (fun z => (M.m M.η₀ z M.θ₀) ^ 2) S.P_Z := by
    simpa [M, linAutoLinearMoment] using hFV
  have h := feasibleCrossFitLinearDML_isAsymLinear M hMZ hFV' sample hK_pos split
    η_hat hBR_at h_m_meas h_m_train h_m_train_uncurry h_m_int h_m_sq_int
    h_score_diff_rate h_g_rate h_α_rate h_product_rate ha hΔa_meas hΔa_train
    hΔa_uncurry hΔa_memLp hΔa_rate hΔa_bias hψM hOracle_meas
  simpa [linAutoDMLEstimator, M, η_hat, linAutoLinearMoment,
    linAutoGeneralMoment, GeneralMoment.linScaleInv] using h

/-- For a [linear regression-functional system, its mean-pairing representation, and its affine
score regularity inputs](hyp:S,rep,ε,hε_nn,h_score_meas), an [i.i.d. sample and K-fold
split](hyp:sample,split), and [fold-specific regression and pairing-function
fits](hyp:g_hat,α_hat), if
[the resulting feasible estimator has the full observation-level asymptotic-linear
expansion](hyp:hAL), [its influence function is measurable](hyp:hψ_meas), and [its √n-scaled
error is almost-everywhere measurable](hyp:hEstimator_meas), then [that scaled error
converges to a centered Gaussian law whose variance is the second moment of the full
influence function](goal). -/
theorem linAutoDML_tendstoNormal
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (S : LinRegFnSys)
    (rep : MeanPairingRepresentation S.H_γ S.γ_target (L_of_m S) S.P_X)
    (ε : ℝ) (hε_nn : 0 ≤ ε)
    (h_score_meas : ∀ η : linAutoNuisance S, ∀ θ : ℝ,
      Measurable (fun z => linRieszScore S η.1 η.2 θ z))
    (sample : IIDSample Ω S.Z μ S.P_Z)
    {K : ℕ} (split : KFoldSplit sample K)
    (g_hat : ℕ → Fin K → Ω → S.H_γ)
    (α_hat : ℕ → Fin K → Ω → S.X → ℝ)
    (hAL : IsAsymLinear
      (linAutoDMLEstimator S rep ε hε_nn h_score_meas sample split g_hat α_hat)
      (L_of_m S S.g₀)
      (linAutoInfluence S rep)
      sample (fun n => Finset.range n))
    (hψ_meas : Measurable (linAutoInfluence S rep))
    (hEstimator_meas : ∀ n, AEMeasurable
      (IsAsymLinear.rescaledEstimator
        (linAutoDMLEstimator S rep ε hε_nn h_score_meas sample split g_hat α_hat)
        (L_of_m S S.g₀) (fun n => Finset.range n) n) μ) :
    Tendsto_dist
      (IsAsymLinear.rescaledEstimator
        (linAutoDMLEstimator S rep ε hε_nn h_score_meas sample split g_hat α_hat)
        (L_of_m S S.g₀) (fun n => Finset.range n))
      (gaussianMeasure 0 (∫ z,
        (linAutoInfluence S rep z) ^ 2 ∂S.P_Z))
      μ hEstimator_meas := by
  exact hAL.tendsto_normal hψ_meas hEstimator_meas

end Causalean.Estimation.OrthogonalMoments.AutoDebias
