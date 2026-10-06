/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Mean zero of the sequential DR (DTR) influence function

Headline theorem `seqDR_mean_zero`:

    ∫ z, ψ_seqDR z ∂(P_Z) = 0

Decomposition mirrors the ATE AIPW analysis but is staged: the
sequential DR moment expands as

* `μ₀_val(S₀)`                                                 — gives `θ₀`
* `(1{D₀=dbar 0} / e₀_val(S₀)) · (μ₁_val(S₁,D₀,S₀) − μ₀_val(S₀))` — stage-0 correction
* `(1{D₀=dbar 0} · 1{D₁=dbar 1} / (e₀_val(S₀) · e₁_val(S₁,D₀,S₀))) ·
    (Y − μ₁_val(S₁,D₀,S₀))`                                    — stage-1 correction
* `−θ₀`                                                        — constant

The two correction terms vanish via the stagewise weighted-residual integral
lemmas in `ScorePullout.lean`.
-/

module
public import Causalean.Estimation.DTR.MeanZero.StageZero

/-!
Completes the stagewise ingredients for sequential-score centering. It proves
conditional mean-zero of the stage-one outcome residual and identifies the
integral of the stage-zero truth regression with the target value.
-/

public section

open Causalean.Mathlib.Probability.Independence.Conditional

namespace Causalean
namespace Estimation
namespace DTR

open MeasureTheory ProbabilityTheory Filter Topology Causalean.PO

namespace DTREstimationSystem

variable {P : POSystem} {δ : Type} {γ : Fin 2 → Type}
  [MeasurableSpace δ] [MeasurableSingletonClass δ]
  [∀ k, MeasurableSpace (γ k)]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
/-- For [a potential-outcome system, treatment space, and two-stage covariate
spaces](hyp:P,δ,γ), [a dynamic-treatment-regime estimation system](hyp:S), [an overlap
level](hyp:ε), [strict overlap](hyp:h_overlap), [the sequential back-door
assumptions](hyp:hA), and [square-integrability of the factual outcome](hyp:h_y2), [the
stage-one treatment-weighted outcome residual has conditional mean zero almost surely given
the stage-one history](goal).

Stage-1 residual conditional expectation is zero a.s.: under DTR
assumptions, the σ(historyBundle 1)-conditional expectation of
`1{D₀ = dbar 0} · 1{D₁ = dbar 1} · (factualY − μ₁_val(S₁,D₀,S₀))` is zero a.s.

Both indicators are required: under the joint regime indicator,
`Assumptions.consistency` rewrites `factualY` to `Y_of dbar`, after which
`stageOneReg_indD_eq` plus `μ₁_reg_compat` gives the σ(historyBundle 1)-CE
of `Y_of dbar` in the required `indD₀`-weighted form. The stage-0 indicator is
σ(historyBundle 1)-measurable
(it is in particular measurable in `D₀, S₀`), so it pulls out cleanly. -/
lemma cond_exp_residual_zero_stage1
    (S : DTREstimationSystem P δ γ)
    {ε : ℝ}
    (h_overlap : S.StrictOverlap ε)
    (hA : S.toPOLongitudinalPathSystem.Assumptions)
    (h_y2 : Integrable (fun ω => (S.toPOLongitudinalPathSystem.factualY ω) ^ 2) P.μ) :
    (S.toPOLongitudinalPathSystem.historyBundle 1 (by decide)).condExpGiven
        (fun ω => (S.toPOLongitudinalPathSystem.dVar ⟨0, by decide⟩).indicator
            (S.dbar ⟨0, by decide⟩) ω *
          ((S.toPOLongitudinalPathSystem.dVar ⟨1, by decide⟩).indicator
            (S.dbar ⟨1, by decide⟩) ω *
          (S.toPOLongitudinalPathSystem.factualY ω -
            S.μ₁_val
              (S.toPOLongitudinalPathSystem.factualS ⟨1, by decide⟩ ω,
               S.toPOLongitudinalPathSystem.factualD ⟨0, by decide⟩ ω,
               S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω)))) P.μ
      =ᵐ[P.μ] (fun _ => (0 : ℝ)) := by
  let B1 := S.toPOLongitudinalPathSystem.historyBundle 1 (by decide)
  let I0 : P.Ω → ℝ :=
    (S.toPOLongitudinalPathSystem.dVar ⟨0, by decide⟩).indicator
      (S.dbar ⟨0, by decide⟩)
  let I1 : P.Ω → ℝ :=
    (S.toPOLongitudinalPathSystem.dVar ⟨1, by decide⟩).indicator
      (S.dbar ⟨1, by decide⟩)
  let Y : P.Ω → ℝ := S.toPOLongitudinalPathSystem.Y_of S.dbar
  let Yf : P.Ω → ℝ := S.toPOLongitudinalPathSystem.factualY
  let M1 : P.Ω → ℝ :=
    fun ω => S.μ₁_val
      (S.toPOLongitudinalPathSystem.factualS ⟨1, by decide⟩ ω,
       S.toPOLongitudinalPathSystem.factualD ⟨0, by decide⟩ ω,
       S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω)
  have hY_int : Integrable Y P.μ := by
    simpa [Y] using hA.integrable_Y S.dbar
  have hYf_int : Integrable Yf P.μ := by
    simpa [Yf] using hA.integrable_factualY
  have hI0_int : Integrable I0 P.μ := by fun_prop
  have hI1_int : Integrable I1 P.μ := by fun_prop
  have hM1_int : Integrable M1 P.μ := by
    have hM1_L2 : MemLp M1 2 P.μ := by
      simpa [M1] using (S.stageOneReg_memLp h_overlap h_y2).ae_eq
        (S.μ₁_val_comp_eq_stageOneReg).symm
    exact hM1_L2.integrable (by norm_num)
  have hM1_meas : Measurable M1 := by fun_prop
  have hI1Y_int : Integrable (fun ω => I1 ω * Y ω) P.μ := by fun_prop
  have hI1Yf_int : Integrable (fun ω => I1 ω * Yf ω) P.μ := by fun_prop
  have hI1M1_int : Integrable (fun ω => I1 ω * M1 ω) P.μ := by fun_prop
  have hI0I1Y_int : Integrable (fun ω => I0 ω * (I1 ω * Y ω)) P.μ := by fun_prop
  have hI0I1Yf_int : Integrable (fun ω => I0 ω * (I1 ω * Yf ω)) P.μ := by fun_prop
  have hI0I1M1_int : Integrable (fun ω => I0 ω * (I1 ω * M1 ω)) P.μ := by fun_prop
  have hres_eq :
      (fun ω => I0 ω * (I1 ω * (Yf ω - M1 ω)))
        = (fun ω => I0 ω * (I1 ω * Yf ω) -
          I0 ω * (I1 ω * M1 ω)) := by
    funext ω
    ring
  have hsub :
      B1.condExpGiven
          (fun ω => I0 ω * (I1 ω * Yf ω) - I0 ω * (I1 ω * M1 ω)) P.μ
        =ᵐ[P.μ]
          B1.condExpGiven (fun ω => I0 ω * (I1 ω * Yf ω)) P.μ
            - B1.condExpGiven (fun ω => I0 ω * (I1 ω * M1 ω)) P.μ := by
    condexp_linearity
  have hConsistency :
      (fun ω => Yf ω * S.toPOLongitudinalPathSystem.indD S.dbar 2 ω)
        = (fun ω => Y ω * S.toPOLongitudinalPathSystem.indD S.dbar 2 ω) := by
    have h := POVar.factual_mul_indicator_eq_cf_mul_indicator
      hA.consistency S.toPOLongitudinalPathSystem.yVar (S.toPOLongitudinalPathSystem.regime S.dbar)
      (S.toPOLongitudinalPathSystem.yVar_notMem_regime S.dbar)
      {ω | ∀ i : Fin 2, S.toPOLongitudinalPathSystem.factualD i ω = S.dbar i}
      (S.toPOLongitudinalPathSystem.factualAgrees_regime S.dbar)
    have hrewrite : S.toPOLongitudinalPathSystem.indD S.dbar 2 =
        ({ω | ∀ i : Fin 2, S.toPOLongitudinalPathSystem.factualD i ω = S.dbar i}).indicator
          (fun _ => (1 : ℝ)) := by
      have h0 := S.toPOLongitudinalPathSystem.indD_eq_indicator_event S.dbar 2 (le_refl 2)
      have h_set_eq :
          ({ω | ∀ i : Fin 2, i.val < 2 → S.toPOLongitudinalPathSystem.factualD i ω = S.dbar i})
            = {ω | ∀ i : Fin 2, S.toPOLongitudinalPathSystem.factualD i ω = S.dbar i} := by
        ext ω
        refine ⟨fun hω i => hω i i.isLt, fun hω i _ => hω i⟩
      rw [h0, h_set_eq]
    change
      (fun ω => S.toPOLongitudinalPathSystem.factualY ω *
        S.toPOLongitudinalPathSystem.indD S.dbar 2 ω)
        = (fun ω => S.toPOLongitudinalPathSystem.Y_of S.dbar ω *
          S.toPOLongitudinalPathSystem.indD S.dbar 2 ω)
    rw [hrewrite]
    exact h
  have hIndD2_factor :
      S.toPOLongitudinalPathSystem.indD S.dbar 2 = fun ω => I0 ω * I1 ω := by
    funext ω
    have hsplit1 := congr_fun
      (S.toPOLongitudinalPathSystem.indD_factor_split S.dbar 1 (by decide)) ω
    have hsplit0 := congr_fun
      (S.toPOLongitudinalPathSystem.indD_factor_split S.dbar 0 (by decide)) ω
    rw [hsplit1, hsplit0]
    have hzero : S.toPOLongitudinalPathSystem.indD S.dbar 0 ω = 1 := rfl
    rw [hzero]
    ring
  have hFact_to_cf :
      (fun ω => I0 ω * (I1 ω * Yf ω))
        =ᵐ[P.μ] (fun ω => I0 ω * (I1 ω * Y ω)) := by
    exact Filter.Eventually.of_forall (fun ω => by
      have hc := congr_fun hConsistency ω
      rw [hIndD2_factor] at hc
      change Yf ω * (I0 ω * I1 ω) = Y ω * (I0 ω * I1 ω) at hc
      nlinarith [hc])
  have hCE_fact_to_cf :
      B1.condExpGiven (fun ω => I0 ω * (I1 ω * Yf ω)) P.μ
        =ᵐ[P.μ]
          B1.condExpGiven (fun ω => I0 ω * (I1 ω * Y ω)) P.μ :=
    B1.condExpGiven_congr_ae hFact_to_cf
  have hI0_sm_B1 :
      StronglyMeasurable[B1.sigma] I0 := by fun_prop
  have hM1_sm_B1 : StronglyMeasurable[B1.sigma] M1 := by fun_prop
  have hI0M1_sm_B1 : StronglyMeasurable[B1.sigma] (fun ω => I0 ω * M1 ω) := by fun_prop
  have hcfY_n : (S.toPOLongitudinalPathSystem.cfYBundle S.dbar).n = 1 := rfl
  let i0 : Fin (S.toPOLongitudinalPathSystem.cfYBundle S.dbar).n :=
    ⟨0, by rw [hcfY_n]; exact Nat.one_pos⟩
  let ψ : (∀ i : Fin (S.toPOLongitudinalPathSystem.cfYBundle S.dbar).n,
      (S.toPOLongitudinalPathSystem.cfYBundle S.dbar).type i) → ℝ :=
    fun f => (f i0 : ℝ)
  have hψ_meas : Measurable ψ := by fun_prop
  have hYof_eq_proj :
      S.toPOLongitudinalPathSystem.Y_of S.dbar =
        ψ ∘ (S.toPOLongitudinalPathSystem.cfYBundle S.dbar).jointValue := by
    funext ω
    rfl
  have hCI :
      ProbabilityTheory.CondIndepFun B1.sigma B1.sigma_le
        (S.toPOLongitudinalPathSystem.factualD ⟨1, by decide⟩) Y P.μ := by
    have hproj := (hA.exch S.dbar ⟨1, by decide⟩).project (ψ := ψ) hψ_meas
    change ProbabilityTheory.CondIndepFun B1.sigma B1.sigma_le
      (S.toPOLongitudinalPathSystem.factualD ⟨1, by decide⟩)
      (S.toPOLongitudinalPathSystem.Y_of S.dbar) P.μ
    rw [hYof_eq_proj]
    exact hproj
  let u : δ → ℝ := ({S.dbar ⟨1, by decide⟩} : Set δ).indicator (fun _ => (1 : ℝ))
  have hu_meas : Measurable u := by fun_prop (disch := measurability)
  have hu_eq : (fun ω => u (S.toPOLongitudinalPathSystem.factualD ⟨1, by decide⟩ ω)) = I1 := by
    funext ω
    by_cases h : S.toPOLongitudinalPathSystem.factualD ⟨1, by decide⟩ ω =
        S.dbar ⟨1, by decide⟩
    · have h1 : S.toPOLongitudinalPathSystem.factualD ⟨1, by decide⟩ ω ∈
          ({S.dbar ⟨1, by decide⟩} : Set δ) := h
      have h2 : ω ∈ (S.toPOLongitudinalPathSystem.dVar ⟨1, by decide⟩).event
          (S.dbar ⟨1, by decide⟩) := h
      rw [show u (S.toPOLongitudinalPathSystem.factualD ⟨1, by decide⟩ ω) = (1 : ℝ) from
            Set.indicator_of_mem h1 _,
          show I1 ω = (1 : ℝ) from by
            simpa [I1] using
              (S.toPOLongitudinalPathSystem.dVar ⟨1, by decide⟩).indicator_apply_eq_one h2]
    · have h1 : S.toPOLongitudinalPathSystem.factualD ⟨1, by decide⟩ ω ∉
          ({S.dbar ⟨1, by decide⟩} : Set δ) := h
      have h2 : ω ∉ (S.toPOLongitudinalPathSystem.dVar ⟨1, by decide⟩).event
          (S.dbar ⟨1, by decide⟩) := h
      rw [show u (S.toPOLongitudinalPathSystem.factualD ⟨1, by decide⟩ ω) = (0 : ℝ) from
            Set.indicator_of_notMem h1 _,
          show I1 ω = (0 : ℝ) from by
            simpa [I1] using
              (S.toPOLongitudinalPathSystem.dVar ⟨1, by decide⟩).indicator_apply_eq_zero h2]
  have hfact :
      P.μ[fun ω => u (S.toPOLongitudinalPathSystem.factualD ⟨1, by decide⟩ ω) * Y ω
          | B1.sigma]
        =ᵐ[P.μ]
          P.μ[fun ω => u (S.toPOLongitudinalPathSystem.factualD ⟨1, by decide⟩ ω)
            | B1.sigma] * P.μ[Y | B1.sigma] :=
    condExp_mul_of_condIndep (μ := P.μ)
      (m := B1.sigma) B1.sigma_le
      (f := S.toPOLongitudinalPathSystem.factualD ⟨1, by decide⟩) (g := Y)
      (S.toPOLongitudinalPathSystem.measurable_factualD ⟨1, by decide⟩)
      (by simpa [Y] using S.toPOLongitudinalPathSystem.measurable_Y_of S.dbar) hCI
      (u := u) (v := id) hu_meas measurable_id
      (by rw [hu_eq]; exact hI1_int) hY_int
      (by
        have heq :
            (fun ω => u (S.toPOLongitudinalPathSystem.factualD ⟨1, by decide⟩ ω) * Y ω)
              = (fun ω => I1 ω * Y ω) := by
          funext ω
          rw [congr_fun hu_eq ω]
        change Integrable
          (fun ω => u (S.toPOLongitudinalPathSystem.factualD ⟨1, by decide⟩ ω) * Y ω) P.μ
        rw [heq]
        exact hI1Y_int)
  have hExch :
      B1.condExpGiven (fun ω => I1 ω * Y ω) P.μ
        =ᵐ[P.μ]
          (fun ω => B1.condExpGiven I1 P.μ ω *
            B1.condExpGiven Y P.μ ω) := by
    unfold POCFBundle.condExpGiven
    have hprod_rw :
        (fun ω => u (S.toPOLongitudinalPathSystem.factualD ⟨1, by decide⟩ ω) * Y ω)
          = (fun ω => I1 ω * Y ω) := by
      funext ω
      rw [congr_fun hu_eq ω]
    rw [hprod_rw, hu_eq] at hfact
    filter_upwards [hfact] with ω hω
    simpa [Pi.mul_apply] using hω
  have hpull_I0Y :=
    B1.condExpGiven_mul_of_stronglyMeasurable_left
      (f := I0) (g := fun ω => I1 ω * Y ω)
      hI0_sm_B1 hI0I1Y_int hI1Y_int
  have hCE_fact :
      B1.condExpGiven (fun ω => I0 ω * (I1 ω * Yf ω)) P.μ
        =ᵐ[P.μ] (fun ω => I0 ω *
          (S.e₁_val
            (S.toPOLongitudinalPathSystem.factualS ⟨1, by decide⟩ ω,
             S.toPOLongitudinalPathSystem.factualD ⟨0, by decide⟩ ω,
             S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω) * M1 ω)) := by
    refine hCE_fact_to_cf.trans ?_
    have hI0_eq_indD : I0 = S.toPOLongitudinalPathSystem.indD S.dbar 1 := by
      funext ω
      have hsplit := congr_fun
        (S.toPOLongitudinalPathSystem.indD_factor_split S.dbar 0 (by decide)) ω
      simp [I0, POLongitudinalPathSystem.indD] at hsplit ⊢
    filter_upwards [hpull_I0Y, hExch, S.e₁_compat,
      S.indD_mul_μ₁_val_comp_eq hA] with
      ω hp hE he hμ
    have hp' :
        B1.condExpGiven (fun ω => I0 ω * (I1 ω * Y ω)) P.μ ω =
          I0 ω * B1.condExpGiven (fun ω => I1 ω * Y ω) P.μ ω := by
      exact hp
    have hμ_local : I0 ω * M1 ω = I0 ω * B1.condExpGiven Y P.μ ω := by
      have hμ' : S.toPOLongitudinalPathSystem.indD S.dbar 1 ω * M1 ω
          = S.toPOLongitudinalPathSystem.indD S.dbar 1 ω * B1.condExpGiven Y P.μ ω := hμ
      rw [hI0_eq_indD]
      exact hμ'
    rw [hp', hE, he]
    calc
      I0 ω * (S.e₁_val
          (S.toPOLongitudinalPathSystem.factualS ⟨1, by decide⟩ ω,
           S.toPOLongitudinalPathSystem.factualD ⟨0, by decide⟩ ω,
           S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω) *
          B1.condExpGiven Y P.μ ω)
          =
            S.e₁_val
              (S.toPOLongitudinalPathSystem.factualS ⟨1, by decide⟩ ω,
               S.toPOLongitudinalPathSystem.factualD ⟨0, by decide⟩ ω,
               S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω) *
              (I0 ω * B1.condExpGiven Y P.μ ω) := by ring
      _ =
            S.e₁_val
              (S.toPOLongitudinalPathSystem.factualS ⟨1, by decide⟩ ω,
               S.toPOLongitudinalPathSystem.factualD ⟨0, by decide⟩ ω,
               S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω) *
              (I0 ω * M1 ω) := by rw [← hμ_local]
      _ =
          I0 ω * (S.e₁_val
            (S.toPOLongitudinalPathSystem.factualS ⟨1, by decide⟩ ω,
             S.toPOLongitudinalPathSystem.factualD ⟨0, by decide⟩ ω,
             S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω) * M1 ω) := by ring
  have hpull_I0M1 :=
    B1.condExpGiven_mul_of_stronglyMeasurable_left
      (f := fun ω => I0 ω * M1 ω) (g := I1)
      hI0M1_sm_B1
      (by
        exact hI0I1M1_int.congr
          (Filter.Eventually.of_forall (fun ω => by
            change I0 ω * (I1 ω * M1 ω) = (I0 ω * M1 ω) * I1 ω
            ring)))
      hI1_int
  have hCE_M1 :
      B1.condExpGiven (fun ω => I0 ω * (I1 ω * M1 ω)) P.μ
        =ᵐ[P.μ] (fun ω => I0 ω *
          (S.e₁_val
            (S.toPOLongitudinalPathSystem.factualS ⟨1, by decide⟩ ω,
             S.toPOLongitudinalPathSystem.factualD ⟨0, by decide⟩ ω,
             S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω) * M1 ω)) := by
    filter_upwards [hpull_I0M1, S.e₁_compat] with ω hp he
    have hp' :
        B1.condExpGiven (fun ω => I0 ω * (I1 ω * M1 ω)) P.μ ω =
          (I0 ω * M1 ω) * B1.condExpGiven I1 P.μ ω := by
      have harg :
          ((fun ω => I0 ω * M1 ω) * I1)
            = (fun ω => I0 ω * (I1 ω * M1 ω)) := by
        funext ω
        change (I0 ω * M1 ω) * I1 ω = I0 ω * (I1 ω * M1 ω)
        ring
      rw [← harg]
      simpa [Pi.mul_apply] using hp
    rw [hp', he]
    ring
  rw [show (fun ω => (S.toPOLongitudinalPathSystem.dVar ⟨0, by decide⟩).indicator
            (S.dbar ⟨0, by decide⟩) ω *
          ((S.toPOLongitudinalPathSystem.dVar ⟨1, by decide⟩).indicator
            (S.dbar ⟨1, by decide⟩) ω *
          (S.toPOLongitudinalPathSystem.factualY ω -
            S.μ₁_val
              (S.toPOLongitudinalPathSystem.factualS ⟨1, by decide⟩ ω,
               S.toPOLongitudinalPathSystem.factualD ⟨0, by decide⟩ ω,
               S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω))))
        = (fun ω => I0 ω * (I1 ω * (Yf ω - M1 ω))) by rfl]
  rw [hres_eq]
  refine hsub.trans ?_
  filter_upwards [hCE_fact, hCE_M1] with ω hfactω hMω
  rw [Pi.sub_apply, hfactω, hMω]
  ring

/-! ## Estimand lift through `factualZ`

Mirrors `theta_zero_factualX_integral` in the ATE template: writes `θ₀`
as an integral against `P.μ` of a function pulled back through
`factualS 0`. -/

/-- The DTR estimand `θ₀ = E[Y(dbar)]` lifts to an integral against `P.μ`:
under DTR backdoor assumptions, `θ₀ = ∫ ω, μ₀_val(factualS 0 ω) ∂P.μ`,
since `μ₀_val ∘ factualS 0` is the σ(historyBundle 0)-conditional
expectation of `Y_of dbar` and `P.μ` is a probability measure. -/
lemma theta_zero_factualS₀_integral
    (S : DTREstimationSystem P δ γ)
    (hA : S.toPOLongitudinalPathSystem.Assumptions) :
    S.θ₀ = ∫ ω, S.μ₀_val (S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω) ∂P.μ := by
  unfold DTREstimationSystem.θ₀ Causalean.PO.POLongitudinalPathSystem.treatmentPathMean
  calc
    ∫ ω, S.toPOLongitudinalPathSystem.Y_of S.dbar ω ∂P.μ
        = ∫ ω, (S.toPOLongitudinalPathSystem.historyBundle 0 (by decide)).condExpGiven
            (S.toPOLongitudinalPathSystem.Y_of S.dbar) P.μ ω ∂P.μ := by
          exact (MeasureTheory.integral_condExp
            (S.toPOLongitudinalPathSystem.historyBundle 0 (by decide)).sigma_le).symm
    _ = ∫ ω, S.μ₀_val (S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω) ∂P.μ :=
          MeasureTheory.integral_congr_ae (S.μ₀_compat hA)

end DTREstimationSystem

end DTR
end Estimation
end Causalean
