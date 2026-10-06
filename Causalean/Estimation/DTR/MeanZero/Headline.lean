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
public import Causalean.Estimation.DTR.MeanZero.StageOne

/-!
Assembles the two stagewise cancellation lemmas into the headline theorem
`seqDR_mean_zero`. The proof first centers the score on the source probability
space and then transports the integral to the observed-data law.
-/

public section

namespace Causalean
namespace Estimation
namespace DTR

open MeasureTheory ProbabilityTheory Filter Topology Causalean.PO

namespace DTREstimationSystem

variable {P : POSystem} {δ : Type} {γ : Fin 2 → Type}
  [MeasurableSpace δ] [MeasurableSingletonClass δ]
  [∀ k, MeasurableSpace (γ k)]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
/-! ## Headline lemma -/

/-- `∫ ω, ψ_seqDR(factualZ ω) ∂P.μ = 0` — the unmapped form of the
mean-zero result, used to prove the headline `seqDR_mean_zero` after
pushforward through `factualZ`. -/
private lemma seqDR_factualZ_integral_zero (S : DTREstimationSystem P δ γ)
    {ε : ℝ}
    (h_overlap : S.StrictOverlap ε)
    (hA : S.toPOLongitudinalPathSystem.Assumptions)
    (h_y2 : Integrable (fun ω => (S.toPOLongitudinalPathSystem.factualY ω) ^ 2) P.μ) :
    (∫ ω, S.ψ_seqDR (S.factualZ ω) ∂P.μ) = 0 := by
  let B0 := S.toPOLongitudinalPathSystem.historyBundle 0 (by decide)
  let B1 := S.toPOLongitudinalPathSystem.historyBundle 1 (by decide)
  let H1 : P.Ω → γ 1 × δ × γ 0 := fun ω =>
    (S.toPOLongitudinalPathSystem.factualS ⟨1, by decide⟩ ω,
     S.toPOLongitudinalPathSystem.factualD ⟨0, by decide⟩ ω,
     S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω)
  let I0 : P.Ω → ℝ :=
    (S.toPOLongitudinalPathSystem.dVar ⟨0, by decide⟩).indicator
      (S.dbar ⟨0, by decide⟩)
  let I1 : P.Ω → ℝ :=
    (S.toPOLongitudinalPathSystem.dVar ⟨1, by decide⟩).indicator
      (S.dbar ⟨1, by decide⟩)
  let M0 : P.Ω → ℝ :=
    fun ω => S.μ₀_val (S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω)
  let M1 : P.Ω → ℝ := fun ω => S.μ₁_val (H1 ω)
  let R0 : P.Ω → ℝ := fun ω => I0 ω * (M1 ω - M0 ω)
  let R1 : P.Ω → ℝ :=
    fun ω => I0 ω * (I1 ω * (S.toPOLongitudinalPathSystem.factualY ω - M1 ω))
  let W0 : P.Ω → ℝ := fun ω =>
    1 / S.e₀_val (S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω)
  let W1 : P.Ω → ℝ := fun ω =>
    1 / (S.e₀_val (S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω) *
      S.e₁_val (H1 ω))
  have hY_int : Integrable (S.toPOLongitudinalPathSystem.Y_of S.dbar) P.μ := hA.integrable_Y S.dbar
  have hM0_int : Integrable M0 P.μ := by
    exact (B0.integrable_condExpGiven (S.toPOLongitudinalPathSystem.Y_of S.dbar)).congr
      (by simpa [B0, M0] using S.μ₀_compat hA)
  have hM1_int : Integrable M1 P.μ := by
    have hM1_L2 : MemLp M1 2 P.μ := by
      simpa [H1, M1] using (S.stageOneReg_memLp h_overlap h_y2).ae_eq
        (S.μ₁_val_comp_eq_stageOneReg).symm
    exact hM1_L2.integrable (by norm_num)
  have hM0_meas : Measurable M0 := by fun_prop
  have hM1_meas : Measurable M1 := by fun_prop
  have hI0M0_int : Integrable (fun ω => I0 ω * M0 ω) P.μ := by fun_prop
  have hI0M1_int : Integrable (fun ω => I0 ω * M1 ω) P.μ := by fun_prop
  have hR0_int : Integrable R0 P.μ := by fun_prop
  have hI1Yf_int : Integrable
      (fun ω => I1 ω * S.toPOLongitudinalPathSystem.factualY ω) P.μ := by
    have h := (S.toPOLongitudinalPathSystem.dVar ⟨1, by decide⟩).integrable_mul_indicator
      (S.dbar ⟨1, by decide⟩) (MeasurableSet.singleton _) hA.integrable_factualY
    exact h.congr (Filter.Eventually.of_forall (fun ω => by simp [I1, mul_comm]))
  have hI1M1_int : Integrable (fun ω => I1 ω * M1 ω) P.μ := by fun_prop
  have hI1_res_int : Integrable
      (fun ω => I1 ω * (S.toPOLongitudinalPathSystem.factualY ω - M1 ω)) P.μ := by
    have hsub := hI1Yf_int.sub hI1M1_int
    refine hsub.congr ?_
    exact Filter.Eventually.of_forall (fun ω => by
      rw [Pi.sub_apply]
      ring)
  have hI1_res_meas : Measurable
      (fun ω => I1 ω * (S.toPOLongitudinalPathSystem.factualY ω - M1 ω)) := by fun_prop
  have hR1_int : Integrable R1 P.μ := by fun_prop
  have hW0_sm : StronglyMeasurable[B0.sigma] W0 := by fun_prop
  have hW1_sm : StronglyMeasurable[B1.sigma] W1 := by fun_prop
  have hW0_bound : ∀ᵐ ω ∂P.μ, ‖W0 ω‖ ≤ ε⁻¹ := by
    filter_upwards [h_overlap.2.2, S.e₀_compat] with ω hover hcomp
    have he : ε ≤ S.e₀_val (S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω) := by
      rw [← hcomp]
      exact hover.1.1
    have hpos : 0 < S.e₀_val (S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω) :=
      S.e₀_pos _
    have hle : (S.e₀_val (S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω))⁻¹ ≤ ε⁻¹ :=
      (inv_le_inv₀ hpos h_overlap.1).2 he
    change ‖1 / S.e₀_val (S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω)‖ ≤ ε⁻¹
    rw [norm_div, norm_one, Real.norm_eq_abs, abs_of_pos hpos]
    simpa [one_div] using hle
  have hW1_bound : ∀ᵐ ω ∂P.μ, ‖W1 ω‖ ≤ (ε * ε)⁻¹ := by
    filter_upwards [h_overlap.2.2, S.e₀_compat, S.e₁_compat] with ω hover he0c he1c
    have he0 : ε ≤ S.e₀_val (S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω) := by
      rw [← he0c]
      exact hover.1.1
    have he1 : ε ≤ S.e₁_val (H1 ω) := by
      rw [← he1c]
      simpa [H1] using hover.2.1
    have hpos0 : 0 < S.e₀_val (S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω) :=
      S.e₀_pos _
    have hpos1 : 0 < S.e₁_val (H1 ω) := S.e₁_pos _
    have hprod_le :
        ε * ε ≤ S.e₀_val (S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω) *
          S.e₁_val (H1 ω) :=
      mul_le_mul he0 he1 h_overlap.1.le hpos0.le
    have hle :
        (S.e₀_val (S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω) *
          S.e₁_val (H1 ω))⁻¹ ≤ (ε * ε)⁻¹ :=
      (inv_le_inv₀ (mul_pos hpos0 hpos1)
        (mul_pos h_overlap.1 h_overlap.1)).2 hprod_le
    change ‖1 / (S.e₀_val (S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω) *
      S.e₁_val (H1 ω))‖ ≤ (ε * ε)⁻¹
    rw [norm_div, norm_one, Real.norm_eq_abs, abs_of_pos (mul_pos hpos0 hpos1)]
    simpa [one_div] using hle
  have hW0R0_int : Integrable (fun ω => W0 ω * R0 ω) P.μ :=
    hR0_int.bdd_mul (hW0_sm.mono B0.sigma_le).aestronglyMeasurable hW0_bound
  have hW1R1_int : Integrable (fun ω => W1 ω * R1 ω) P.μ :=
    hR1_int.bdd_mul (hW1_sm.mono B1.sigma_le).aestronglyMeasurable hW1_bound
  have hstage0_zero : ∫ ω, W0 ω * R0 ω ∂P.μ = 0 := by
    have hpull := B0.condExpGiven_mul_of_stronglyMeasurable_left
      (f := W0) (g := R0) hW0_sm hW0R0_int hR0_int
    have hzero : B0.condExpGiven R0 P.μ =ᵐ[P.μ] (fun _ => (0 : ℝ)) := by
      simpa [B0, R0, I0, M0, M1, H1] using
        cond_exp_residual_zero_stage0 S h_overlap hA h_y2
    have hce : B0.condExpGiven (fun ω => W0 ω * R0 ω) P.μ
        =ᵐ[P.μ] (fun _ => (0 : ℝ)) := by
      refine hpull.trans ?_
      filter_upwards [hzero] with ω hω
      rw [Pi.mul_apply, hω, mul_zero]
    calc
      ∫ ω, W0 ω * R0 ω ∂P.μ
          = ∫ ω, B0.condExpGiven (fun ω => W0 ω * R0 ω) P.μ ω ∂P.μ := by
            exact (MeasureTheory.integral_condExp B0.sigma_le).symm
      _ = ∫ _, (0 : ℝ) ∂P.μ := MeasureTheory.integral_congr_ae hce
      _ = 0 := MeasureTheory.integral_zero _ _
  have hstage1_zero : ∫ ω, W1 ω * R1 ω ∂P.μ = 0 := by
    have hpull := B1.condExpGiven_mul_of_stronglyMeasurable_left
      (f := W1) (g := R1) hW1_sm hW1R1_int hR1_int
    have hzero : B1.condExpGiven R1 P.μ =ᵐ[P.μ] (fun _ => (0 : ℝ)) := by
      simpa [B1, R1, I0, I1, M1, H1] using
        cond_exp_residual_zero_stage1 S h_overlap hA h_y2
    have hce : B1.condExpGiven (fun ω => W1 ω * R1 ω) P.μ
        =ᵐ[P.μ] (fun _ => (0 : ℝ)) := by
      refine hpull.trans ?_
      filter_upwards [hzero] with ω hω
      rw [Pi.mul_apply, hω, mul_zero]
    calc
      ∫ ω, W1 ω * R1 ω ∂P.μ
          = ∫ ω, B1.condExpGiven (fun ω => W1 ω * R1 ω) P.μ ω ∂P.μ := by
            exact (MeasureTheory.integral_condExp B1.sigma_le).symm
      _ = ∫ _, (0 : ℝ) ∂P.μ := MeasureTheory.integral_congr_ae hce
      _ = 0 := MeasureTheory.integral_zero _ _
  have hθ : S.θ₀ = ∫ ω, M0 ω ∂P.μ := by
    simpa [M0] using theta_zero_factualS₀_integral S hA
  have hψ_eq :
      (fun ω => S.ψ_seqDR (S.factualZ ω))
        = fun ω => M0 ω + W0 ω * R0 ω + W1 ω * R1 ω - S.θ₀ := by
    funext ω
    by_cases hD0 : S.toPOLongitudinalPathSystem.factualD ⟨0, by decide⟩ ω =
        S.dbar ⟨0, by decide⟩
    · by_cases hD1 : S.toPOLongitudinalPathSystem.factualD ⟨1, by decide⟩ ω =
          S.dbar ⟨1, by decide⟩
      · have hI0 : I0 ω = 1 := by
          simpa [I0] using
            (S.toPOLongitudinalPathSystem.dVar ⟨0, by decide⟩).indicator_apply_eq_one hD0
        have hI1 : I1 ω = 1 := by
          simpa [I1] using
            (S.toPOLongitudinalPathSystem.dVar ⟨1, by decide⟩).indicator_apply_eq_one hD1
        have hI0raw :
            (S.toPOLongitudinalPathSystem.dVar ⟨0, by decide⟩).indicator
              (S.dbar ⟨0, by decide⟩) ω = 1 := by
          simpa [I0] using hI0
        have hI1raw :
            (S.toPOLongitudinalPathSystem.dVar ⟨1, by decide⟩).indicator
              (S.dbar ⟨1, by decide⟩) ω = 1 := by
          simpa [I1] using hI1
        have hD0n : S.toPOLongitudinalPathSystem.factualD 0 ω = S.dbar 0 := by simpa using hD0
        have hD1n : S.toPOLongitudinalPathSystem.factualD 1 ω = S.dbar 1 := by simpa using hD1
        have hI0rawn : (S.toPOLongitudinalPathSystem.dVar 0).indicator (S.dbar 0) ω = 1 := by
          simpa using hI0raw
        have hI1rawn : (S.toPOLongitudinalPathSystem.dVar 1).indicator (S.dbar 1) ω = 1 := by
          simpa using hI1raw
        simp [DTREstimationSystem.ψ_seqDR, DTREstimationSystem.seqDRMoment,
          Causalean.Estimation.DTR.seqDRMoment, DTREstimationSystem.factualZ,
          DTREstimationSystem.η₀, projS₀, projD₀, projS₁, projD₁, projY, histH₁,
          indEq, M0, M1, H1, R0, R1, W0, W1, I0, I1,
          hD0n, hD1n, hI0rawn, hI1rawn, one_div]
      · have hI0 : I0 ω = 1 := by
          simpa [I0] using
            (S.toPOLongitudinalPathSystem.dVar ⟨0, by decide⟩).indicator_apply_eq_one hD0
        have hI1 : I1 ω = 0 := by
          simpa [I1] using
            (S.toPOLongitudinalPathSystem.dVar ⟨1, by decide⟩).indicator_apply_eq_zero hD1
        have hI0raw :
            (S.toPOLongitudinalPathSystem.dVar ⟨0, by decide⟩).indicator
              (S.dbar ⟨0, by decide⟩) ω = 1 := by
          simpa [I0] using hI0
        have hI1raw :
            (S.toPOLongitudinalPathSystem.dVar ⟨1, by decide⟩).indicator
              (S.dbar ⟨1, by decide⟩) ω = 0 := by
          simpa [I1] using hI1
        have hD0n : S.toPOLongitudinalPathSystem.factualD 0 ω = S.dbar 0 := by simpa using hD0
        have hD1n : ¬S.toPOLongitudinalPathSystem.factualD 1 ω = S.dbar 1 := by simpa using hD1
        have hI0rawn : (S.toPOLongitudinalPathSystem.dVar 0).indicator (S.dbar 0) ω = 1 := by
          simpa using hI0raw
        have hI1rawn : (S.toPOLongitudinalPathSystem.dVar 1).indicator (S.dbar 1) ω = 0 := by
          simpa using hI1raw
        simp [DTREstimationSystem.ψ_seqDR, DTREstimationSystem.seqDRMoment,
          Causalean.Estimation.DTR.seqDRMoment, DTREstimationSystem.factualZ,
          DTREstimationSystem.η₀, projS₀, projD₀, projS₁, projD₁, projY, histH₁,
          indEq, M0, M1, H1, R0, R1, W0, W1, I0, I1,
          hD0n, hD1n, hI0rawn, hI1rawn, one_div]
    · have hI0 : I0 ω = 0 := by
        simpa [I0] using
          (S.toPOLongitudinalPathSystem.dVar ⟨0, by decide⟩).indicator_apply_eq_zero hD0
      have hI0raw :
          (S.toPOLongitudinalPathSystem.dVar ⟨0, by decide⟩).indicator
            (S.dbar ⟨0, by decide⟩) ω = 0 := by
        simpa [I0] using hI0
      have hD0n : ¬S.toPOLongitudinalPathSystem.factualD 0 ω = S.dbar 0 := by simpa using hD0
      have hI0rawn : (S.toPOLongitudinalPathSystem.dVar 0).indicator (S.dbar 0) ω = 0 := by
        simpa using hI0raw
      simp [DTREstimationSystem.ψ_seqDR, DTREstimationSystem.seqDRMoment,
        Causalean.Estimation.DTR.seqDRMoment, DTREstimationSystem.factualZ,
        DTREstimationSystem.η₀, projS₀, projD₀, projS₁, projD₁, projY, histH₁,
        indEq, hD0n, M0, M1, H1, R0, R1, W0, W1, I0, hI0rawn, one_div]
  have hconst_int : Integrable (fun _ : P.Ω => S.θ₀) P.μ := by fun_prop
  have hsum_int : Integrable
      (fun ω => M0 ω + W0 ω * R0 ω + W1 ω * R1 ω) P.μ := by fun_prop
  calc
    ∫ ω, S.ψ_seqDR (S.factualZ ω) ∂P.μ
        = ∫ ω, M0 ω + W0 ω * R0 ω + W1 ω * R1 ω - S.θ₀ ∂P.μ := by
          exact MeasureTheory.integral_congr_ae
            (Filter.Eventually.of_forall (fun ω => congr_fun hψ_eq ω))
    _ = (∫ ω, M0 ω + W0 ω * R0 ω + W1 ω * R1 ω ∂P.μ)
          - ∫ _ : P.Ω, S.θ₀ ∂P.μ := by
        exact MeasureTheory.integral_sub hsum_int hconst_int
    _ = ((∫ ω, M0 ω + W0 ω * R0 ω ∂P.μ) + ∫ ω, W1 ω * R1 ω ∂P.μ)
          - ∫ _ : P.Ω, S.θ₀ ∂P.μ := by
        have hadd := MeasureTheory.integral_add (μ := P.μ)
          (f := fun ω => M0 ω + W0 ω * R0 ω)
          (g := fun ω => W1 ω * R1 ω)
          (hM0_int.add hW0R0_int) hW1R1_int
        exact congrArg (fun x => x - ∫ _ : P.Ω, S.θ₀ ∂P.μ) hadd
    _ = (((∫ ω, M0 ω ∂P.μ) + ∫ ω, W0 ω * R0 ω ∂P.μ)
          + ∫ ω, W1 ω * R1 ω ∂P.μ) - ∫ _ : P.Ω, S.θ₀ ∂P.μ := by
        have hadd := MeasureTheory.integral_add (μ := P.μ)
          (f := M0) (g := fun ω => W0 ω * R0 ω) hM0_int hW0R0_int
        exact congrArg (fun x => (x + ∫ ω, W1 ω * R1 ω ∂P.μ)
          - ∫ _ : P.Ω, S.θ₀ ∂P.μ) hadd
    _ = 0 := by
        rw [hstage0_zero, hstage1_zero, ← hθ]
        simp

/-- **Mean zero of the sequential doubly robust score.** Under [the two-stage DTR backdoor
assumptions — sequential exchangeability, consistency, stagewise positivity, and integrability
of every counterfactual outcome](hyp:hA), [uniform two-stage strict overlap: the target-regime
propensity at each stage lies almost surely in `[ε, 1-ε]` for some `ε` in
`(0, 1/2]`](hyp:h_overlap), and [a finite second moment for the observed factual
outcome](hyp:h_y2), then [the sequential doubly robust influence function `ψ_seqDR` has
expectation zero under the observed two-stage data law](goal).

Formally, the sequential DR score `ψ_seqDR` integrates to zero against the
pushforward law `P_Z` of `(S₀, D₀, S₁, D₁, Y)`.  No square-integrability
assumption is imposed on all counterfactual outcomes; the proof uses the DTR
assumptions for counterfactual integrability and the factual second moment for
the observable stagewise regressions. -/
theorem seqDR_mean_zero (S : DTREstimationSystem P δ γ) {ε : ℝ}
    (h_overlap : S.StrictOverlap ε)
    (hA : S.toPOLongitudinalPathSystem.Assumptions)
    (h_y2 : Integrable (fun ω => (S.toPOLongitudinalPathSystem.factualY ω) ^ 2) P.μ) :
    (∫ z, S.ψ_seqDR z ∂(S.P_Z)) = 0 := by
  rw [DTREstimationSystem.P_Z]
  rw [MeasureTheory.integral_map S.measurable_factualZ.aemeasurable
    (S.measurable_ψ_seqDR).aestronglyMeasurable]
  exact seqDR_factualZ_integral_zero S h_overlap hA h_y2

end DTREstimationSystem

end DTR
end Estimation
end Causalean
