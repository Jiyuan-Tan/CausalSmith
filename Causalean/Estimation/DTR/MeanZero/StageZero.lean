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
public import Causalean.Estimation.DTR.SeqDRMoment
public import Causalean.Tactic.CondexpLinearity

/-!
Develops the stage-zero half of the sequential-score cancellation argument. It
proves measurability of `ψ_seqDR`, nondegeneracy of both stagewise propensity
scores, and the conditional mean-zero identity for the stage-zero regression
increment.
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
/-! ## Measurability of `ψ_seqDR` -/

/-- Measurability of the sequential DR influence function on the data tuple
`(s₀, d₀, s₁, d₁, y) : γ 0 × δ × γ 1 × δ × ℝ`.  Decomposes into
`Measurable.add`/`Measurable.mul`/`Measurable.div` chained against the
projections, the indicator functions `indEq`, and the value-space
nuisance functions stored in `S.η₀`. -/
@[fun_prop]
lemma measurable_ψ_seqDR (S : DTREstimationSystem P δ γ) :
    Measurable S.ψ_seqDR := by
  exact S.measurable_seqDRMomentFunctional S.η₀ S.θ₀

/-! ## Helpers: stagewise propensity nondegeneracy -/

/-- Stage-0 propensity is a.e. nonzero under the DTR backdoor assumptions.
The conditional indicator `μ[1{D₀ = dbar 0} | σ(historyBundle 0)]` is
identified via `e₀_compat` with `e₀_val ∘ factualS 0`, and `e₀_val > 0`
pointwise on `γ 0`. -/
lemma propScore_ne_zero_stage0 (S : DTREstimationSystem P δ γ)
    (hA : S.toPOLongitudinalPathSystem.Assumptions) :
    ∀ᵐ ω ∂P.μ,
      (S.toPOLongitudinalPathSystem.historyBundle 0 (by decide)).condExpGiven
        ((S.toPOLongitudinalPathSystem.dVar ⟨0, by decide⟩).indicator
            (S.dbar ⟨0, by decide⟩)) P.μ ω ≠ 0 := by
  filter_upwards [hA.overlap S.dbar ⟨0, by decide⟩] with ω hω
  exact ne_of_gt hω

/-- Stage-1 propensity is a.e. nonzero under the DTR backdoor assumptions.
Analogous to `propScore_ne_zero_stage0` via `e₁_compat` and `e₁_pos`. -/
lemma propScore_ne_zero_stage1 (S : DTREstimationSystem P δ γ)
    (hA : S.toPOLongitudinalPathSystem.Assumptions) :
    ∀ᵐ ω ∂P.μ,
      (S.toPOLongitudinalPathSystem.historyBundle 1 (by decide)).condExpGiven
        ((S.toPOLongitudinalPathSystem.dVar ⟨1, by decide⟩).indicator
            (S.dbar ⟨1, by decide⟩)) P.μ ω ≠ 0 := by
  filter_upwards [hA.overlap S.dbar ⟨1, by decide⟩] with ω hω
  exact ne_of_gt hω

/-! ## Stagewise residual conditional-expectation zero lemmas

Stage-0 residual `1{D₀=dbar 0}·(μ₁_val(history₁) − μ₀_val(S₀))` has
σ(historyBundle 0)-conditional expectation zero a.s.; stage-1 analogue uses
`(factualY − μ₁_val(history₁))` under σ(historyBundle 1) (where consistency
bridges `factualY` to `Y_of dbar` under the joint regime indicator). -/

/-- For [a potential-outcome system, treatment space, and two-stage covariate
spaces](hyp:P,δ,γ), [a dynamic-treatment-regime estimation system](hyp:S), [an overlap
level](hyp:ε), [strict overlap](hyp:h_overlap), [the sequential back-door
assumptions](hyp:hA), and [square-integrability of the factual outcome](hyp:h_y2), [the
stage-zero treatment-weighted regression increment has conditional mean zero almost surely
given the stage-zero history](goal).

Stage-0 residual conditional expectation is zero a.s.: under DTR
assumptions, `μ[1{D₀=dbar 0}·(μ₁_val(history₁) − μ₀_val(S₀)) | σ(historyBundle 0)] =ᵐ 0`.

Argument: by `stageOneReg_indD_eq` plus `μ₁_reg_compat`, the stage-1
observable regression agrees with the σ(historyBundle 1) CE of `Y_of dbar`
after multiplication by the partial regime indicator. Tower with
σ(history₀) ⊆ σ(history₁) gives
`E[μ₁_val(history₁)|hist₀] = E[Y_of dbar|hist₀] = μ₀_val(S₀)`
(using `μ₀_compat`). Sequential exchangeability `D₀ ⟂ Y(dbar) | history₀`
plus `e₀_compat` give `E[indD₀(dbar 0)·μ₁_val(history₁)|hist₀] =
e₀_val(S₀)·μ₀_val(S₀)`, and similarly for the `μ₀_val(S₀)` term;
the difference is zero. -/
lemma cond_exp_residual_zero_stage0
    (S : DTREstimationSystem P δ γ)
    {ε : ℝ}
    (h_overlap : S.StrictOverlap ε)
    (hA : S.toPOLongitudinalPathSystem.Assumptions)
    (h_y2 : Integrable (fun ω => (S.toPOLongitudinalPathSystem.factualY ω) ^ 2) P.μ) :
    (S.toPOLongitudinalPathSystem.historyBundle 0 (by decide)).condExpGiven
        (fun ω => (S.toPOLongitudinalPathSystem.dVar ⟨0, by decide⟩).indicator
            (S.dbar ⟨0, by decide⟩) ω *
          (S.μ₁_val
              (S.toPOLongitudinalPathSystem.factualS ⟨1, by decide⟩ ω,
               S.toPOLongitudinalPathSystem.factualD ⟨0, by decide⟩ ω,
               S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω) -
            S.μ₀_val (S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω))) P.μ
      =ᵐ[P.μ] (fun _ => (0 : ℝ)) := by
  let B0 := S.toPOLongitudinalPathSystem.historyBundle 0 (by decide)
  let B1 := S.toPOLongitudinalPathSystem.historyBundle 1 (by decide)
  let I0 : P.Ω → ℝ :=
    (S.toPOLongitudinalPathSystem.dVar ⟨0, by decide⟩).indicator
      (S.dbar ⟨0, by decide⟩)
  let Y : P.Ω → ℝ := S.toPOLongitudinalPathSystem.Y_of S.dbar
  let M0 : P.Ω → ℝ :=
    fun ω => S.μ₀_val (S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω)
  let M1 : P.Ω → ℝ :=
    fun ω => S.μ₁_val
      (S.toPOLongitudinalPathSystem.factualS ⟨1, by decide⟩ ω,
       S.toPOLongitudinalPathSystem.factualD ⟨0, by decide⟩ ω,
       S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω)
  have hY_int : Integrable Y P.μ := by
    simpa [Y] using hA.integrable_Y S.dbar
  have hI0_int : Integrable I0 P.μ := by fun_prop
  have hI0Y_int : Integrable (fun ω => I0 ω * Y ω) P.μ := by fun_prop
  have hM0_int : Integrable M0 P.μ := by
    exact (B0.integrable_condExpGiven (S.toPOLongitudinalPathSystem.Y_of S.dbar)).congr
      (by simpa [B0, M0] using S.μ₀_compat hA)
  have hM1_int : Integrable M1 P.μ := by
    have hM1_L2 : MemLp M1 2 P.μ := by
      simpa [M1] using (S.stageOneReg_memLp h_overlap h_y2).ae_eq
        (S.μ₁_val_comp_eq_stageOneReg).symm
    exact hM1_L2.integrable (by norm_num)
  have hM0_meas : Measurable M0 := by fun_prop
  have hM1_meas : Measurable M1 := by fun_prop
  have hI0M0_int : Integrable (fun ω => I0 ω * M0 ω) P.μ := by fun_prop
  have hI0M1_int : Integrable (fun ω => I0 ω * M1 ω) P.μ := by fun_prop
  have hres_eq :
      (fun ω => I0 ω * (M1 ω - M0 ω))
        = (fun ω => I0 ω * M1 ω - I0 ω * M0 ω) := by
    funext ω
    ring
  have hsub :
      B0.condExpGiven (fun ω => I0 ω * M1 ω - I0 ω * M0 ω) P.μ
        =ᵐ[P.μ]
          B0.condExpGiven (fun ω => I0 ω * M1 ω) P.μ
            - B0.condExpGiven (fun ω => I0 ω * M0 ω) P.μ := by
    condexp_linearity
  have hI0_sm_B1 :
      StronglyMeasurable[B1.sigma] I0 := by fun_prop
  have hrev_B1 :
      (fun ω => I0 ω * M1 ω)
        =ᵐ[P.μ] B1.condExpGiven (fun ω => I0 ω * Y ω) P.μ := by
    have hI0_eq_indD : I0 = S.toPOLongitudinalPathSystem.indD S.dbar 1 := by
      funext ω
      have hsplit := congr_fun
        (S.toPOLongitudinalPathSystem.indD_factor_split S.dbar 0 (by decide)) ω
      simp [I0, POLongitudinalPathSystem.indD] at hsplit ⊢
    have hpull :=
      B1.condExpGiven_mul_of_stronglyMeasurable_left
        (f := I0) (g := Y) hI0_sm_B1 hI0Y_int hY_int
    filter_upwards [hpull,
      S.indD_mul_μ₁_val_comp_eq hA] with ω hp hμ1
    have hp' :
        B1.condExpGiven (fun ω => I0 ω * Y ω) P.μ ω =
          I0 ω * B1.condExpGiven Y P.μ ω := by
      exact hp
    have hμ1_local : I0 ω * M1 ω = I0 ω * B1.condExpGiven Y P.μ ω := by
      have hμ1' : S.toPOLongitudinalPathSystem.indD S.dbar 1 ω * M1 ω
          = S.toPOLongitudinalPathSystem.indD S.dbar 1 ω * B1.condExpGiven Y P.μ ω := hμ1
      rw [hI0_eq_indD]
      exact hμ1'
    rw [hp']
    exact hμ1_local
  haveI : IsFiniteMeasure (P.μ.trim B1.sigma_le) := isFiniteMeasure_trim _
  have hB0_le_B1 : B0.sigma ≤ B1.sigma := by
    simpa [B0, B1] using
      S.toPOLongitudinalPathSystem.historyBundle_sigma_mono 0 1 (by decide) (by decide)
  have htower :
      B0.condExpGiven (B1.condExpGiven (fun ω => I0 ω * Y ω) P.μ) P.μ
        =ᵐ[P.μ] B0.condExpGiven (fun ω => I0 ω * Y ω) P.μ := by
    have h := B1.condExpGiven_tower_of_le
      (g := fun ω => I0 ω * Y ω) (μ := P.μ) (m := B0.sigma) hB0_le_B1
    simpa [POCFBundle.condExpGiven] using h
  have hCE_I0M1_to_Y :
      B0.condExpGiven (fun ω => I0 ω * M1 ω) P.μ
        =ᵐ[P.μ] B0.condExpGiven (fun ω => I0 ω * Y ω) P.μ := by
    exact (B0.condExpGiven_congr_ae hrev_B1).trans htower
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
      ProbabilityTheory.CondIndepFun B0.sigma B0.sigma_le
        (S.toPOLongitudinalPathSystem.factualD ⟨0, by decide⟩) Y P.μ := by
    have hproj := (hA.exch S.dbar ⟨0, by decide⟩).project (ψ := ψ) hψ_meas
    change ProbabilityTheory.CondIndepFun B0.sigma B0.sigma_le
      (S.toPOLongitudinalPathSystem.factualD ⟨0, by decide⟩)
      (S.toPOLongitudinalPathSystem.Y_of S.dbar) P.μ
    rw [hYof_eq_proj]
    exact hproj
  let u : δ → ℝ := ({S.dbar ⟨0, by decide⟩} : Set δ).indicator (fun _ => (1 : ℝ))
  have hu_meas : Measurable u := by fun_prop (disch := measurability)
  have hu_eq : (fun ω => u (S.toPOLongitudinalPathSystem.factualD ⟨0, by decide⟩ ω)) = I0 := by
    funext ω
    by_cases h : S.toPOLongitudinalPathSystem.factualD ⟨0, by decide⟩ ω =
        S.dbar ⟨0, by decide⟩
    · have h1 : S.toPOLongitudinalPathSystem.factualD ⟨0, by decide⟩ ω ∈
          ({S.dbar ⟨0, by decide⟩} : Set δ) := h
      have h2 : ω ∈ (S.toPOLongitudinalPathSystem.dVar ⟨0, by decide⟩).event
          (S.dbar ⟨0, by decide⟩) := h
      rw [show u (S.toPOLongitudinalPathSystem.factualD ⟨0, by decide⟩ ω) = (1 : ℝ) from
            Set.indicator_of_mem h1 _,
          show I0 ω = (1 : ℝ) from by
            simpa [I0] using
              (S.toPOLongitudinalPathSystem.dVar ⟨0, by decide⟩).indicator_apply_eq_one h2]
    · have h1 : S.toPOLongitudinalPathSystem.factualD ⟨0, by decide⟩ ω ∉
          ({S.dbar ⟨0, by decide⟩} : Set δ) := h
      have h2 : ω ∉ (S.toPOLongitudinalPathSystem.dVar ⟨0, by decide⟩).event
          (S.dbar ⟨0, by decide⟩) := h
      rw [show u (S.toPOLongitudinalPathSystem.factualD ⟨0, by decide⟩ ω) = (0 : ℝ) from
            Set.indicator_of_notMem h1 _,
          show I0 ω = (0 : ℝ) from by
            simpa [I0] using
              (S.toPOLongitudinalPathSystem.dVar ⟨0, by decide⟩).indicator_apply_eq_zero h2]
  have hfact :
      P.μ[fun ω => u (S.toPOLongitudinalPathSystem.factualD ⟨0, by decide⟩ ω) * Y ω
          | B0.sigma]
        =ᵐ[P.μ]
          P.μ[fun ω => u (S.toPOLongitudinalPathSystem.factualD ⟨0, by decide⟩ ω)
            | B0.sigma] * P.μ[Y | B0.sigma] :=
    condExp_mul_of_condIndep (μ := P.μ)
      (m := B0.sigma) B0.sigma_le
      (f := S.toPOLongitudinalPathSystem.factualD ⟨0, by decide⟩) (g := Y)
      (S.toPOLongitudinalPathSystem.measurable_factualD ⟨0, by decide⟩)
      (by simpa [Y] using S.toPOLongitudinalPathSystem.measurable_Y_of S.dbar) hCI
      (u := u) (v := id) hu_meas measurable_id
      (by rw [hu_eq]; exact hI0_int) hY_int
      (by
        change Integrable
          (fun ω => u (S.toPOLongitudinalPathSystem.factualD ⟨0, by decide⟩ ω) * Y ω) P.μ
        have heq :
            (fun ω => u (S.toPOLongitudinalPathSystem.factualD ⟨0, by decide⟩ ω) * Y ω)
              = (fun ω => I0 ω * Y ω) := by
          funext ω
          rw [congr_fun hu_eq ω]
        rw [heq]
        exact hI0Y_int)
  have hExch :
      B0.condExpGiven (fun ω => I0 ω * Y ω) P.μ
        =ᵐ[P.μ]
          (fun ω => B0.condExpGiven I0 P.μ ω *
            B0.condExpGiven Y P.μ ω) := by
    unfold POCFBundle.condExpGiven
    have hprod_rw :
        (fun ω => u (S.toPOLongitudinalPathSystem.factualD ⟨0, by decide⟩ ω) * Y ω)
          = (fun ω => I0 ω * Y ω) := by
      funext ω
      rw [congr_fun hu_eq ω]
    rw [hprod_rw, hu_eq] at hfact
    filter_upwards [hfact] with ω hω
    simpa [Pi.mul_apply] using hω
  have hCE_I0M1 :
      B0.condExpGiven (fun ω => I0 ω * M1 ω) P.μ
        =ᵐ[P.μ] (fun ω => S.e₀_val (S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω) *
          S.μ₀_val (S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω)) := by
    refine hCE_I0M1_to_Y.trans ?_
    filter_upwards [hExch, S.e₀_compat, S.μ₀_compat hA] with ω hE he hμ
    rw [hE, he, hμ]
  have hM0_sm_B0 : StronglyMeasurable[B0.sigma] M0 := by fun_prop
  have hpull_M0 :=
    B0.condExpGiven_mul_of_stronglyMeasurable_right
      (f := I0) (g := M0) hM0_sm_B0 hI0M0_int hI0_int
  have hCE_I0M0 :
      B0.condExpGiven (fun ω => I0 ω * M0 ω) P.μ
        =ᵐ[P.μ] (fun ω => S.e₀_val (S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω) *
          S.μ₀_val (S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω)) := by
    filter_upwards [hpull_M0, S.e₀_compat] with ω hp he
    have hp' :
        B0.condExpGiven (fun ω => I0 ω * M0 ω) P.μ ω =
          B0.condExpGiven I0 P.μ ω * M0 ω := by
      exact hp
    rw [hp', he]
  rw [show (fun ω => (S.toPOLongitudinalPathSystem.dVar ⟨0, by decide⟩).indicator
            (S.dbar ⟨0, by decide⟩) ω *
          (S.μ₁_val
              (S.toPOLongitudinalPathSystem.factualS ⟨1, by decide⟩ ω,
               S.toPOLongitudinalPathSystem.factualD ⟨0, by decide⟩ ω,
               S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω) -
            S.μ₀_val (S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω)))
        = (fun ω => I0 ω * (M1 ω - M0 ω)) by rfl]
  rw [hres_eq]
  refine hsub.trans ?_
  filter_upwards [hCE_I0M1, hCE_I0M0] with ω h1 h0
  rw [Pi.sub_apply, h1, h0]
  ring

end DTREstimationSystem

end DTR
end Estimation
end Causalean
