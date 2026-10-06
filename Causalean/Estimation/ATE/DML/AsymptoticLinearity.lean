/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Estimation.ATE.DML.Basic

/-! # Asymptotic linearity for one-shot ATE DML

Proves the good-event, almost-everywhere good-event, and direct forms of
asymptotic linearity for `dmlEstimator`. These wrappers discharge the abstract
AIPW DML interface from overlap, moment, sample-split, measurability, and
nuisance-rate assumptions.
-/

public section

namespace Causalean
namespace Estimation
namespace ATE

open MeasureTheory ProbabilityTheory Filter Topology Causalean.PO Causalean.Stat
open BackdoorEstimationSystem
open scoped ENNReal

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
-- The wrapper composes ~20 derived hypotheses (rate translations, score
-- measurability, integrability, two transport equalities) and applies the
-- abstract `aipw_dml_isAsymLinear`; the resulting elaboration exceeds the
-- default heartbeat budget when type-checking the final `refine ⟨…⟩` block.
set_option maxHeartbeats 1200000 in
/-- **Asymptotic linearity of the one-shot DML ATE** — `thm:est-dml-ate-al`.
For [an estimation system](hyp:S), [overlap threshold](hyp:ε), [back-door,
overlap, and outcome-moment assumptions](hyp:hA,h_overlap,h_y2,h_yd2), [an
i.i.d. sample and one-shot split with a nondegenerate limiting evaluation
fraction](hyp:sample,split,c,hc_pos,hc_lt,h_split_rate), and [outcome-regression
and propensity learners](hyp:μ_hat,e_hat), suppose [good events](hyp:goodSet)
have [failure bounds](hyp:Δ,hfail) that [vanish](hyp:hΔ). If the learners are
[measurable](hyp:h_mu_meas,h_e_meas), [square-integrable and overlapping on
the good events](hyp:h_mu_memLp,h_e_memLp,h_e_overlap), [training-fold
measurable](hyp:h_mu_foldA,h_e_foldA,h_mu_uncurry_foldA,h_e_uncurry_foldA), and
satisfy [the individual and product rates](hyp:h_mu_rate,h_e_rate,h_product_rate),
then [the one-shot DML/AIPW estimator is asymptotically linear](goal).

Hypotheses (mirroring the NL doc verbatim, including the split-rate
hypothesis `|B(n)|/n → c`):

1. back-door `Assumptions`;
2. strict overlap for the truth and learner overlap on the good event: there exists
   `ε ∈ (0, 1/2]` with `ε ≤ e(X) ≤ 1-ε` a.s. and
   `ε ≤ ê(n,ω)(X) ≤ 1-ε` `P_X`-a.e. whenever `ω ∈ goodSet n`;
3. the truth and learners belong to the source-shaped `H_ε_aeL2` nuisance
   class used by `aipwGeneralMoment`;
4. `E[Y²] < ∞`;
5. one-shot split with `|B(n)|/n → c` for some `c ∈ (0, 1)`;
6. `μ̂(n)` and `ê(n)` depend only on the nuisance fold `A(n)`;
7. individual rates `‖μ̂(n)(a, X) − μ_val(a, X)‖_{L²(P_X)} = o_p(1)` and
   `‖ê(n)(X) − e_val(X)‖_{L²(P_X)} = o_p(1)`;
8. product rate
   `‖μ̂(n)(a, X) − μ_val(a, X)‖_{L²(P_X)} · ‖ê(n)(X) − e_val(X)‖_{L²(P_X)}
       = o_p(n^{-1/2})` for each `a ∈ {0, 1}`.

Conclusion: `IsAsymLinear (dmlEstimator …) θ₀ ψ_AIPW sample split.foldB`.

The proof builds the abstract `η_hat` from `(μ_hat, e_hat)`, translates the
rate, measurability, and high-probability integrability hypotheses, applies the
high-probability abstract theorem, then transports the conclusion
along two algebraic equalities (a pointwise rescaled-error equality
`√|B(n)| · (dmlChern − θ₀) = √|B(n)| · (dmlEstimator − θ₀)` and the
influence-function equality `−linScaleInv · aipwMomentFunctional S.η₀ z S.θ₀
= S.ψ_AIPW z`). -/
theorem dml_ATE_isAsymLinear_of_goodSet
    (S : BackdoorEstimationSystem P γ)
    {ε : ℝ}
    (hA : S.toPOBackdoorSystem.Assumptions)
    (h_overlap : S.StrictOverlap ε)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_yd2 : ∀ d : Bool, Integrable
      (fun ω => (S.toPOBackdoorSystem.YofD d ω) ^ 2) P.μ)
    (sample : IIDSample P.Ω (γ × Bool × ℝ) P.μ S.P_Z)
    (split : OneShotSplit sample)
    {c : ℝ} (hc_pos : 0 < c) (hc_lt : c < 1)
    (h_split_rate :
      Tendsto (fun n => ((split.foldB n).card : ℝ) / n) atTop (𝓝 c))
    (μ_hat : ℕ → P.Ω → (Bool → γ → ℝ))
    (e_hat : ℕ → P.Ω → (γ → ℝ))
    (goodSet : ℕ → Set P.Ω)
    (Δ : ℕ → ℝ≥0∞)
    (hΔ : Tendsto Δ atTop (𝓝 0))
    (hfail : ∀ n, P.μ (goodSet n)ᶜ ≤ Δ n)
    (h_mu_meas :
      ∀ n a, Measurable (fun (p : P.Ω × γ) => μ_hat n p.1 a p.2))
    (h_e_meas :
      ∀ n, Measurable (fun (p : P.Ω × γ) => e_hat n p.1 p.2))
    (h_mu_memLp :
      ∀ n ω, ω ∈ goodSet n → ∀ a, MemLp (fun x => μ_hat n ω a x) 2 S.P_X)
    (h_e_memLp :
      ∀ n ω, ω ∈ goodSet n → MemLp (fun x => e_hat n ω x) 2 S.P_X)
    (h_e_overlap :
      ∀ n ω, ω ∈ goodSet n → ∀ᵐ x ∂S.P_X,
        ε ≤ e_hat n ω x ∧ e_hat n ω x ≤ 1 - ε)
    (h_mu_foldA :
      ∀ n,
        Measurable[MeasurableSpace.comap
          (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance]
          (μ_hat n))
    (h_e_foldA :
      ∀ n,
        Measurable[MeasurableSpace.comap
          (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance]
          (e_hat n))
    (h_mu_uncurry_foldA :
      ∀ n a,
        Measurable[(MeasurableSpace.comap
            (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
          (inferInstance : MeasurableSpace γ)]
          (fun (p : P.Ω × γ) => μ_hat n p.1 a p.2))
    (h_e_uncurry_foldA :
      ∀ n,
        Measurable[(MeasurableSpace.comap
            (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
          (inferInstance : MeasurableSpace γ)]
          (fun (p : P.Ω × γ) => e_hat n p.1 p.2))
    (h_mu_rate :
      ∀ a : Bool,
        IsLittleOp
          (fun n ω =>
            (eLpNorm (fun x => μ_hat n ω a x - S.μ_val a x) 2 S.P_X).toReal)
          (fun _ => (1 : ℝ)) P.μ)
    (h_e_rate :
      IsLittleOp
        (fun n ω =>
          (eLpNorm (fun x => e_hat n ω x - S.e_val x) 2 S.P_X).toReal)
        (fun _ => (1 : ℝ)) P.μ)
    (h_product_rate :
      ∀ a : Bool,
        IsLittleOp
          (fun n ω =>
            (eLpNorm (fun x => μ_hat n ω a x - S.μ_val a x) 2 S.P_X).toReal *
              (eLpNorm (fun x => e_hat n ω x - S.e_val x) 2 S.P_X).toReal)
          (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) P.μ) :
    IsAsymLinear
      (dmlEstimator S sample split μ_hat e_hat)
      S.θ₀
      (S.ψ_AIPW)
      sample
      split.foldB := by
  classical
  -- 1. Build the abstract `η_hat : ℕ → P.Ω → NuisanceVec γ` from `(μ_hat, e_hat)`.
  let η_hat : ℕ → P.Ω → NuisanceVec γ := fun n ω =>
    { μ_fn := μ_hat n ω
      e_fn := e_hat n ω
      μ_meas := fun a =>
        (h_mu_meas n a).comp
          (Measurable.prodMk measurable_const measurable_id)
      e_meas :=
        (h_e_meas n).comp
          (Measurable.prodMk measurable_const measurable_id) }
  -- `S.P_X` is a probability measure (used by `MemLp.of_bound` for `S.e_val`).
  haveI : IsProbabilityMeasure S.P_X := by
    unfold BackdoorEstimationSystem.P_X
    exact Measure.isProbabilityMeasure_map
      S.toPOBackdoorSystem.measurable_factualX.aemeasurable
  -- `S.P_Z` is a probability measure (used by `MemLp.integrable` on the score).
  haveI : IsProbabilityMeasure S.P_Z := by
    unfold BackdoorEstimationSystem.P_Z
    exact Measure.isProbabilityMeasure_map
      S.measurable_factualZ.aemeasurable
  -- 2. `S.μ_val a` is L²(P_X) (via condExp of square-integrable counterfactual outcomes).
  have hμ_val_memLp : ∀ a : Bool, MemLp (S.μ_val a) 2 S.P_X := by
    intro a
    have hY_L2 : MemLp (S.toPOBackdoorSystem.YofD a) 2 P.μ :=
      (memLp_two_iff_integrable_sq
        (S.toPOBackdoorSystem.measurable_YofD a).aestronglyMeasurable).2 (h_yd2 a)
    have hcond_L2 :
        MemLp (P.μ[S.toPOBackdoorSystem.YofD a |
          S.toPOBackdoorSystem.sigmaX]) 2 P.μ :=
      hY_L2.condExp (by norm_num)
    have hcomp_L2 :
        MemLp (fun ω => S.μ_val a (S.toPOBackdoorSystem.factualX ω)) 2 P.μ :=
      hcond_L2.ae_eq (S.μ_compat hA a)
    rw [BackdoorEstimationSystem.P_X]
    exact (memLp_map_measure_iff (S.μ_meas a).aestronglyMeasurable
      S.toPOBackdoorSystem.measurable_factualX.aemeasurable).2 hcomp_L2
  -- 3. `S.e_val` is L²(P_X) (via boundedness in `[0, 1]`).
  have he_val_memLp : MemLp S.e_val 2 S.P_X := by
    refine MemLp.of_bound S.e_meas.aestronglyMeasurable 1 ?_
    refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [S.e_pos x], by linarith [S.e_lt_one x]⟩
  have he_val_memLp_top : MemLp S.e_val ⊤ S.P_X := by
    refine MemLp.of_bound S.e_meas.aestronglyMeasurable 1 ?_
    refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [S.e_pos x], by linarith [S.e_lt_one x]⟩
  have hη₀_mem : S.η₀ ∈ H_ε_aeL2 S ε := by
    refine ⟨?_, ?_, ?_⟩
    · have hset : MeasurableSet {x : γ | ε ≤ S.e_val x ∧ S.e_val x ≤ 1 - ε} := by
        exact measurableSet_Icc.preimage S.e_meas
      have hΩ : ∀ᵐ ω ∂P.μ,
          ε ≤ S.e_val (S.toPOBackdoorSystem.factualX ω) ∧
            S.e_val (S.toPOBackdoorSystem.factualX ω) ≤ 1 - ε := by
        filter_upwards [h_overlap.2.2, S.e_compat] with ω hover hcomp
        simpa [hcomp] using hover
      unfold BackdoorEstimationSystem.P_X
      exact (MeasureTheory.ae_map_iff
        S.toPOBackdoorSystem.measurable_factualX.aemeasurable hset).mpr hΩ
    · exact hμ_val_memLp
    · exact he_val_memLp_top
  have h_in_Hε : ∀ n ω, ω ∈ goodSet n → η_hat n ω ∈ H_ε_aeL2 S ε := by
    intro n ω hω
    have hμ := h_mu_memLp n ω hω
    have hover := h_e_overlap n ω hω
    refine ⟨hover, hμ, ?_⟩
    refine MemLp.of_bound (η_hat n ω).e_meas.aestronglyMeasurable 1 ?_
    filter_upwards [hover] with x hx
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [h_overlap.1, hx.1],
      by linarith [h_overlap.1, hx.2]⟩
  -- 4. Per-η̂_n L² of the differences (needed by the abstract).
  have h_mu_diff_memLp : ∀ n ω, ω ∈ goodSet n → ∀ a, MemLp
      (fun x => (η_hat n ω).μ_fn a x - S.μ_val a x) 2 S.P_X := by
    intro n ω hω
    have hμ := h_mu_memLp n ω hω
    exact fun a => (hμ a).sub (hμ_val_memLp a)
  have h_e_diff_memLp : ∀ n ω, ω ∈ goodSet n → MemLp
      (fun x => (η_hat n ω).e_fn x - S.e_val x) 2 S.P_X := by
    intro n ω hω
    have he := h_e_memLp n ω hω
    exact he.sub he_val_memLp
  -- 5. Translate the production rate hypotheses to the abstract `ρ₁ / ρ₂`.
  --    `ρ₁ η η₀ = ‖Δμ_T‖ + ‖Δμ_F‖`, `ρ₂ η η₀ = ‖Δe‖`.
  have h_indiv_rate_ρ₁ :
      IsLittleOp
        (fun n ω =>
          (((aipwGeneralMoment S hη₀_mem).ρ₁
              (η_hat n ω) S.η₀ : NNReal) : ℝ))
        (fun _ => (1 : ℝ)) P.μ := by
    exact IsLittleOp.add_one (h_mu_rate true) (h_mu_rate false)
  have h_indiv_rate_ρ₂ :
      IsLittleOp
        (fun n ω =>
          (((aipwGeneralMoment S hη₀_mem).ρ₂
              (η_hat n ω) S.η₀ : NNReal) : ℝ))
        (fun _ => (1 : ℝ)) P.μ := by
    exact h_e_rate
  have h_product_rate_abs :
      IsLittleOp
        (fun n ω =>
          (((aipwGeneralMoment S hη₀_mem).ρ₁
              (η_hat n ω) S.η₀ : NNReal) : ℝ) *
            (((aipwGeneralMoment S hη₀_mem).ρ₂
                (η_hat n ω) S.η₀ : NNReal) : ℝ))
        (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) P.μ := by
    have hrn_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
      filter_upwards with n
      positivity
    have hcomb :=
      IsLittleOp.add_eventually_nonneg_rate hrn_nonneg
        (h_product_rate true) (h_product_rate false)
    have hfun :
        (fun n (ω : P.Ω) =>
            (eLpNorm (fun x => μ_hat n ω true x - S.μ_val true x) 2 S.P_X).toReal *
                (eLpNorm (fun x => e_hat n ω x - S.e_val x) 2 S.P_X).toReal +
              (eLpNorm (fun x => μ_hat n ω false x - S.μ_val false x) 2 S.P_X).toReal *
                (eLpNorm (fun x => e_hat n ω x - S.e_val x) 2 S.P_X).toReal)
          = fun n ω =>
            ((eLpNorm (fun x => μ_hat n ω true x - S.μ_val true x) 2 S.P_X).toReal +
                (eLpNorm (fun x => μ_hat n ω false x - S.μ_val false x) 2 S.P_X).toReal) *
              (eLpNorm (fun x => e_hat n ω x - S.e_val x) 2 S.P_X).toReal := by
      funext n ω
      ring
    rw [hfun] at hcomb
    exact hcomb
  -- 6. Translate score measurability / integrability to the abstract form.
  have h_m_meas :
      ∀ n, Measurable (fun (p : P.Ω × (γ × Bool × ℝ)) =>
        aipwMomentFunctional (η_hat n p.1) p.2 S.θ₀) := by
    intro n
    unfold aipwMomentFunctional aipwMoment indA projX projA projY η_hat
    have hx : Measurable (fun p : P.Ω × (γ × Bool × ℝ) => (p.1, p.2.1)) := by
      fun_prop
    have hzY : Measurable (fun p : P.Ω × (γ × Bool × ℝ) => p.2.2.2) := by
      fun_prop
    have hAind : Measurable (fun p : P.Ω × (γ × Bool × ℝ) =>
        if p.2.2.1 = true then (1 : ℝ) else 0) := by
      have ha : Measurable (fun p : P.Ω × (γ × Bool × ℝ) => p.2.2.1) := by
        fun_prop
      exact (Measurable.of_discrete
        (f := fun b : Bool => if b = true then (1 : ℝ) else 0)).comp ha
    have hμt : Measurable (fun p : P.Ω × (γ × Bool × ℝ) => μ_hat n p.1 true p.2.1) :=
      (h_mu_meas n true).comp hx
    have hμf : Measurable (fun p : P.Ω × (γ × Bool × ℝ) => μ_hat n p.1 false p.2.1) :=
      (h_mu_meas n false).comp hx
    have het : Measurable (fun p : P.Ω × (γ × Bool × ℝ) => e_hat n p.1 p.2.1) :=
      (h_e_meas n).comp hx
    exact ((((hμt.sub hμf).add ((hAind.div het).mul (hzY.sub hμt))).sub
      (((measurable_const.sub hAind).div (measurable_const.sub het)).mul
        (hzY.sub hμf))).sub measurable_const)
  have h_m_foldA :
      ∀ n,
        Measurable[MeasurableSpace.comap
          (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance]
          (fun ω z => aipwMomentFunctional (η_hat n ω) z S.θ₀) := by
    intro n
    unfold aipwMomentFunctional aipwMoment indA projX projA projY η_hat
    fun_prop
  have h_m_foldA_uncurry :
      ∀ n,
        Measurable[(MeasurableSpace.comap
            (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
          (inferInstance : MeasurableSpace (γ × Bool × ℝ))]
          (fun (p : P.Ω × (γ × Bool × ℝ)) =>
            aipwMomentFunctional (η_hat n p.1) p.2 S.θ₀) := by
    intro n
    change Measurable[(MeasurableSpace.comap
        (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
      (inferInstance : MeasurableSpace (γ × Bool × ℝ))]
      (fun (p : P.Ω × (γ × Bool × ℝ)) =>
        aipwMomentFunctional (η_hat n p.1) p.2 S.θ₀)
    unfold aipwMomentFunctional aipwMoment indA projX projA projY η_hat
    let mA : MeasurableSpace P.Ω :=
      MeasurableSpace.comap
        (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance
    have hproj :
        @Measurable (P.Ω × (γ × Bool × ℝ)) (P.Ω × γ)
          (mA.prod (inferInstance : MeasurableSpace (γ × Bool × ℝ)))
          (mA.prod (inferInstance : MeasurableSpace γ))
          (fun p => (p.1, p.2.1)) := by
      have hx :
          @Measurable (P.Ω × (γ × Bool × ℝ)) γ
            (mA.prod (inferInstance : MeasurableSpace (γ × Bool × ℝ)))
            inferInstance
            (fun p => p.2.1) := measurable_snd.fst
      exact Measurable.prodMk measurable_fst hx
    have hzY :
        @Measurable (P.Ω × (γ × Bool × ℝ)) ℝ
          (mA.prod (inferInstance : MeasurableSpace (γ × Bool × ℝ)))
          inferInstance
          (fun p => p.2.2.2) := measurable_snd.snd.snd
    have hAind :
        @Measurable (P.Ω × (γ × Bool × ℝ)) ℝ
          (mA.prod (inferInstance : MeasurableSpace (γ × Bool × ℝ)))
          inferInstance
          (fun p => if p.2.2.1 = true then (1 : ℝ) else 0) := by
      have ha :
          @Measurable (P.Ω × (γ × Bool × ℝ)) Bool
            (mA.prod (inferInstance : MeasurableSpace (γ × Bool × ℝ)))
            inferInstance
            (fun p => p.2.2.1) := measurable_snd.snd.fst
      exact (Measurable.of_discrete
        (f := fun b : Bool => if b = true then (1 : ℝ) else 0)).comp ha
    have hμt : Measurable
        (fun p : P.Ω × (γ × Bool × ℝ) => μ_hat n p.1 true p.2.1) :=
      (h_mu_uncurry_foldA n true).comp hproj
    have hμf : Measurable
        (fun p : P.Ω × (γ × Bool × ℝ) => μ_hat n p.1 false p.2.1) :=
      (h_mu_uncurry_foldA n false).comp hproj
    have het : Measurable
        (fun p : P.Ω × (γ × Bool × ℝ) => e_hat n p.1 p.2.1) :=
      (h_e_uncurry_foldA n).comp hproj
    exact ((((hμt.sub hμf).add ((hAind.div het).mul (hzY.sub hμt))).sub
      (((measurable_const.sub hAind).div (measurable_const.sub het)).mul
        (hzY.sub hμf))).sub measurable_const)
  have h_m_int :
      ∀ n ω, ω ∈ goodSet n → Integrable
        (fun z => aipwMomentFunctional (η_hat n ω) z S.θ₀) S.P_Z := by
    intro n ω hω
    have hμ := h_mu_memLp n ω hω
    have hover := h_e_overlap n ω hω
    have hη : η_hat n ω ∈ H_ε_aeL2 S ε := by
      refine ⟨hover, hμ, ?_⟩
      refine MemLp.of_bound (η_hat n ω).e_meas.aestronglyMeasurable 1 ?_
      filter_upwards [hover] with x hx
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [h_overlap.1, hx.1],
        by linarith [h_overlap.1, hx.2]⟩
    have hY_L2 : MemLp S.toPOBackdoorSystem.factualY 2 P.μ :=
      (memLp_two_iff_integrable_sq
        S.toPOBackdoorSystem.measurable_factualY.aestronglyMeasurable).2 h_y2
    have hμ_hat_comp_L2 :
        ∀ a : Bool,
          MemLp (fun ω' => μ_hat n ω a (S.toPOBackdoorSystem.factualX ω')) 2 P.μ := by
      intro a
      have hmap : MemLp (fun x => μ_hat n ω a x) 2 (P.μ.map S.toPOBackdoorSystem.factualX) := by
        simpa [BackdoorEstimationSystem.P_X] using hμ a
      exact (memLp_map_measure_iff hmap.aestronglyMeasurable
        S.toPOBackdoorSystem.measurable_factualX.aemeasurable).1 hmap
    have hw_true_bound :
        ∀ᵐ ω' ∂P.μ,
          ‖indA (S.factualZ ω') /
            e_hat n ω (S.toPOBackdoorSystem.factualX ω')‖ ≤ ε⁻¹ := by
      filter_upwards [H_ε_aeL2_overlap_factualX S hη] with ω' hηω'
      have he := hηω'.1
      by_cases hD : S.toPOBackdoorSystem.factualD ω' = true
      · have hpos : 0 < e_hat n ω (S.toPOBackdoorSystem.factualX ω') :=
          lt_of_lt_of_le h_overlap.1 he
        have hle : (e_hat n ω (S.toPOBackdoorSystem.factualX ω'))⁻¹ ≤ ε⁻¹ :=
          (inv_le_inv₀ hpos h_overlap.1).2 he
        simpa [BackdoorEstimationSystem.factualZ, indA, projA, projX, hD, one_div,
          Real.norm_eq_abs, abs_of_pos hpos] using hle
      · have hεinv_nonneg : 0 ≤ ε⁻¹ := inv_nonneg.mpr h_overlap.1.le
        simpa [BackdoorEstimationSystem.factualZ, indA, projA, projX, hD] using hεinv_nonneg
    have hw_false_bound :
        ∀ᵐ ω' ∂P.μ,
          ‖(1 - indA (S.factualZ ω')) /
            (1 - e_hat n ω (S.toPOBackdoorSystem.factualX ω'))‖ ≤ ε⁻¹ := by
      filter_upwards [H_ε_aeL2_overlap_factualX S hη] with ω' hηω'
      have he := hηω'.2
      by_cases hD : S.toPOBackdoorSystem.factualD ω' = true
      · have hεinv_nonneg : 0 ≤ ε⁻¹ := inv_nonneg.mpr h_overlap.1.le
        simpa [BackdoorEstimationSystem.factualZ, indA, projA, projX, hD] using hεinv_nonneg
      · have hden : ε ≤ 1 - e_hat n ω (S.toPOBackdoorSystem.factualX ω') := by
          linarith
        have hdenpos : 0 < 1 - e_hat n ω (S.toPOBackdoorSystem.factualX ω') :=
          lt_of_lt_of_le h_overlap.1 hden
        have hle : (1 - e_hat n ω (S.toPOBackdoorSystem.factualX ω'))⁻¹ ≤ ε⁻¹ :=
          (inv_le_inv₀ hdenpos h_overlap.1).2 hden
        simpa [BackdoorEstimationSystem.factualZ, indA, projA, projX, hD, one_div,
          Real.norm_eq_abs, abs_of_pos hdenpos] using hle
    have hw_true_Linf :
        MemLp
          (fun ω' => indA (S.factualZ ω') /
            e_hat n ω (S.toPOBackdoorSystem.factualX ω')) ⊤ P.μ := by
      refine MemLp.of_bound ?_ ε⁻¹ hw_true_bound
      apply Measurable.aestronglyMeasurable
      have hind : Measurable (fun ω' => indA (S.factualZ ω')) := by
        exact (Measurable.of_discrete
            (f := fun b : Bool => if b = true then (1 : ℝ) else 0)).fun_comp
              S.toPOBackdoorSystem.measurable_factualD
      exact hind.div ((h_e_meas n).comp
        (Measurable.prodMk measurable_const S.toPOBackdoorSystem.measurable_factualX))
    have hw_false_Linf :
        MemLp
          (fun ω' => (1 - indA (S.factualZ ω')) /
            (1 - e_hat n ω (S.toPOBackdoorSystem.factualX ω'))) ⊤ P.μ := by
      refine MemLp.of_bound ?_ ε⁻¹ hw_false_bound
      apply Measurable.aestronglyMeasurable
      have hind : Measurable (fun ω' => indA (S.factualZ ω')) := by
        exact (Measurable.of_discrete
            (f := fun b : Bool => if b = true then (1 : ℝ) else 0)).fun_comp
              S.toPOBackdoorSystem.measurable_factualD
      exact (measurable_const.sub hind).div
        (measurable_const.sub ((h_e_meas n).comp
          (Measurable.prodMk measurable_const S.toPOBackdoorSystem.measurable_factualX)))
    have hterm_true_L2 :
        MemLp
          (fun ω' =>
            (indA (S.factualZ ω') /
              e_hat n ω (S.toPOBackdoorSystem.factualX ω')) *
            (S.toPOBackdoorSystem.factualY ω' -
              μ_hat n ω true (S.toPOBackdoorSystem.factualX ω'))) 2 P.μ := by
      exact (hY_L2.sub (hμ_hat_comp_L2 true)).mul hw_true_Linf
    have hterm_false_L2 :
        MemLp
          (fun ω' =>
            ((1 - indA (S.factualZ ω')) /
              (1 - e_hat n ω (S.toPOBackdoorSystem.factualX ω'))) *
            (S.toPOBackdoorSystem.factualY ω' -
              μ_hat n ω false (S.toPOBackdoorSystem.factualX ω'))) 2 P.μ := by
      exact (hY_L2.sub (hμ_hat_comp_L2 false)).mul hw_false_Linf
    have hrand_comp_L2 :
        MemLp (fun ω' => aipwMomentFunctional (η_hat n ω) (S.factualZ ω') S.θ₀)
          2 P.μ := by
      have hbase_L2 :
          MemLp
            (fun ω' =>
              μ_hat n ω true (S.toPOBackdoorSystem.factualX ω') -
              μ_hat n ω false (S.toPOBackdoorSystem.factualX ω')) 2 P.μ :=
        (hμ_hat_comp_L2 true).sub (hμ_hat_comp_L2 false)
      have hconst_L2 : MemLp (fun _ : P.Ω => S.θ₀) 2 P.μ :=
        memLp_const _
      have hsum_L2 :=
        ((hbase_L2.add hterm_true_L2).sub hterm_false_L2).sub hconst_L2
      simp only [aipwMomentFunctional, aipwMoment, BackdoorEstimationSystem.factualZ,
        projX, projY]
      exact hsum_L2
    have hrand_meas :
        Measurable (fun z : γ × Bool × ℝ => aipwMomentFunctional (η_hat n ω) z S.θ₀) := by
      unfold aipwMomentFunctional aipwMoment indA projX projA projY η_hat
      have hx : Measurable (fun z : γ × Bool × ℝ => z.1) := measurable_fst
      have hy : Measurable (fun z : γ × Bool × ℝ => z.2.2) := by measurability
      have hμt : Measurable (fun z : γ × Bool × ℝ => μ_hat n ω true z.1) :=
        (h_mu_meas n true).comp (Measurable.prodMk measurable_const hx)
      have hμf : Measurable (fun z : γ × Bool × ℝ => μ_hat n ω false z.1) :=
        (h_mu_meas n false).comp (Measurable.prodMk measurable_const hx)
      have he : Measurable (fun z : γ × Bool × ℝ => e_hat n ω z.1) :=
        (h_e_meas n).comp (Measurable.prodMk measurable_const hx)
      have hind : Measurable (fun z : γ × Bool × ℝ =>
          if z.2.1 = true then (1 : ℝ) else 0) := by
        have ha : Measurable (fun z : γ × Bool × ℝ => z.2.1) := by measurability
        exact (Measurable.of_discrete
          (f := fun b : Bool => if b = true then (1 : ℝ) else 0)).comp ha
      exact ((((hμt.sub hμf).add ((hind.div he).mul (hy.sub hμt))).sub
        (((measurable_const.sub hind).div (measurable_const.sub he)).mul
          (hy.sub hμf))).sub measurable_const)
    have hrand_L2 :
        MemLp (fun z : γ × Bool × ℝ => aipwMomentFunctional (η_hat n ω) z S.θ₀)
          2 S.P_Z := by
      rw [BackdoorEstimationSystem.P_Z]
      exact (memLp_map_measure_iff hrand_meas.aestronglyMeasurable
        S.measurable_factualZ.aemeasurable).2 hrand_comp_L2
    exact hrand_L2.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have h_m_sq_int :
      ∀ n ω, ω ∈ goodSet n → Integrable
        (fun z => (aipwMomentFunctional (η_hat n ω) z S.θ₀) ^ 2) S.P_Z := by
    intro n ω hω
    have hμ := h_mu_memLp n ω hω
    have hover := h_e_overlap n ω hω
    have hη : η_hat n ω ∈ H_ε_aeL2 S ε := by
      refine ⟨hover, hμ, ?_⟩
      refine MemLp.of_bound (η_hat n ω).e_meas.aestronglyMeasurable 1 ?_
      filter_upwards [hover] with x hx
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [h_overlap.1, hx.1],
        by linarith [h_overlap.1, hx.2]⟩
    have hY_L2 : MemLp S.toPOBackdoorSystem.factualY 2 P.μ :=
      (memLp_two_iff_integrable_sq
        S.toPOBackdoorSystem.measurable_factualY.aestronglyMeasurable).2 h_y2
    have hμ_hat_comp_L2 :
        ∀ a : Bool,
          MemLp (fun ω' => μ_hat n ω a (S.toPOBackdoorSystem.factualX ω')) 2 P.μ := by
      intro a
      have hmap : MemLp (fun x => μ_hat n ω a x) 2 (P.μ.map S.toPOBackdoorSystem.factualX) := by
        simpa [BackdoorEstimationSystem.P_X] using hμ a
      exact (memLp_map_measure_iff hmap.aestronglyMeasurable
        S.toPOBackdoorSystem.measurable_factualX.aemeasurable).1 hmap
    have hw_true_bound :
        ∀ᵐ ω' ∂P.μ,
          ‖indA (S.factualZ ω') /
            e_hat n ω (S.toPOBackdoorSystem.factualX ω')‖ ≤ ε⁻¹ := by
      filter_upwards [H_ε_aeL2_overlap_factualX S hη] with ω' hηω'
      have he := hηω'.1
      by_cases hD : S.toPOBackdoorSystem.factualD ω' = true
      · have hpos : 0 < e_hat n ω (S.toPOBackdoorSystem.factualX ω') :=
          lt_of_lt_of_le h_overlap.1 he
        have hle : (e_hat n ω (S.toPOBackdoorSystem.factualX ω'))⁻¹ ≤ ε⁻¹ :=
          (inv_le_inv₀ hpos h_overlap.1).2 he
        simpa [BackdoorEstimationSystem.factualZ, indA, projA, projX, hD, one_div,
          Real.norm_eq_abs, abs_of_pos hpos] using hle
      · have hεinv_nonneg : 0 ≤ ε⁻¹ := inv_nonneg.mpr h_overlap.1.le
        simpa [BackdoorEstimationSystem.factualZ, indA, projA, projX, hD] using hεinv_nonneg
    have hw_false_bound :
        ∀ᵐ ω' ∂P.μ,
          ‖(1 - indA (S.factualZ ω')) /
            (1 - e_hat n ω (S.toPOBackdoorSystem.factualX ω'))‖ ≤ ε⁻¹ := by
      filter_upwards [H_ε_aeL2_overlap_factualX S hη] with ω' hηω'
      have he := hηω'.2
      by_cases hD : S.toPOBackdoorSystem.factualD ω' = true
      · have hεinv_nonneg : 0 ≤ ε⁻¹ := inv_nonneg.mpr h_overlap.1.le
        simpa [BackdoorEstimationSystem.factualZ, indA, projA, projX, hD] using hεinv_nonneg
      · have hden : ε ≤ 1 - e_hat n ω (S.toPOBackdoorSystem.factualX ω') := by
          linarith
        have hdenpos : 0 < 1 - e_hat n ω (S.toPOBackdoorSystem.factualX ω') :=
          lt_of_lt_of_le h_overlap.1 hden
        have hle : (1 - e_hat n ω (S.toPOBackdoorSystem.factualX ω'))⁻¹ ≤ ε⁻¹ :=
          (inv_le_inv₀ hdenpos h_overlap.1).2 hden
        simpa [BackdoorEstimationSystem.factualZ, indA, projA, projX, hD, one_div,
          Real.norm_eq_abs, abs_of_pos hdenpos] using hle
    have hw_true_Linf :
        MemLp
          (fun ω' => indA (S.factualZ ω') /
            e_hat n ω (S.toPOBackdoorSystem.factualX ω')) ⊤ P.μ := by
      refine MemLp.of_bound ?_ ε⁻¹ hw_true_bound
      apply Measurable.aestronglyMeasurable
      have hind : Measurable (fun ω' => indA (S.factualZ ω')) := by
        exact (Measurable.of_discrete
            (f := fun b : Bool => if b = true then (1 : ℝ) else 0)).fun_comp
              S.toPOBackdoorSystem.measurable_factualD
      exact hind.div ((h_e_meas n).comp
        (Measurable.prodMk measurable_const S.toPOBackdoorSystem.measurable_factualX))
    have hw_false_Linf :
        MemLp
          (fun ω' => (1 - indA (S.factualZ ω')) /
            (1 - e_hat n ω (S.toPOBackdoorSystem.factualX ω'))) ⊤ P.μ := by
      refine MemLp.of_bound ?_ ε⁻¹ hw_false_bound
      apply Measurable.aestronglyMeasurable
      have hind : Measurable (fun ω' => indA (S.factualZ ω')) := by
        exact (Measurable.of_discrete
            (f := fun b : Bool => if b = true then (1 : ℝ) else 0)).fun_comp
              S.toPOBackdoorSystem.measurable_factualD
      exact (measurable_const.sub hind).div
        (measurable_const.sub ((h_e_meas n).comp
          (Measurable.prodMk measurable_const S.toPOBackdoorSystem.measurable_factualX)))
    have hterm_true_L2 :
        MemLp
          (fun ω' =>
            (indA (S.factualZ ω') /
              e_hat n ω (S.toPOBackdoorSystem.factualX ω')) *
            (S.toPOBackdoorSystem.factualY ω' -
              μ_hat n ω true (S.toPOBackdoorSystem.factualX ω'))) 2 P.μ := by
      exact (hY_L2.sub (hμ_hat_comp_L2 true)).mul hw_true_Linf
    have hterm_false_L2 :
        MemLp
          (fun ω' =>
            ((1 - indA (S.factualZ ω')) /
              (1 - e_hat n ω (S.toPOBackdoorSystem.factualX ω'))) *
            (S.toPOBackdoorSystem.factualY ω' -
              μ_hat n ω false (S.toPOBackdoorSystem.factualX ω'))) 2 P.μ := by
      exact (hY_L2.sub (hμ_hat_comp_L2 false)).mul hw_false_Linf
    have hrand_comp_L2 :
        MemLp (fun ω' => aipwMomentFunctional (η_hat n ω) (S.factualZ ω') S.θ₀)
          2 P.μ := by
      have hbase_L2 :
          MemLp
            (fun ω' =>
              μ_hat n ω true (S.toPOBackdoorSystem.factualX ω') -
              μ_hat n ω false (S.toPOBackdoorSystem.factualX ω')) 2 P.μ :=
        (hμ_hat_comp_L2 true).sub (hμ_hat_comp_L2 false)
      have hconst_L2 : MemLp (fun _ : P.Ω => S.θ₀) 2 P.μ :=
        memLp_const _
      have hsum_L2 :=
        ((hbase_L2.add hterm_true_L2).sub hterm_false_L2).sub hconst_L2
      simp only [aipwMomentFunctional, aipwMoment, BackdoorEstimationSystem.factualZ,
        projX, projY]
      exact hsum_L2
    have hrand_meas :
        Measurable (fun z : γ × Bool × ℝ => aipwMomentFunctional (η_hat n ω) z S.θ₀) := by
      unfold aipwMomentFunctional aipwMoment indA projX projA projY η_hat
      have hx : Measurable (fun z : γ × Bool × ℝ => z.1) := measurable_fst
      have hy : Measurable (fun z : γ × Bool × ℝ => z.2.2) := by measurability
      have hμt : Measurable (fun z : γ × Bool × ℝ => μ_hat n ω true z.1) :=
        (h_mu_meas n true).comp (Measurable.prodMk measurable_const hx)
      have hμf : Measurable (fun z : γ × Bool × ℝ => μ_hat n ω false z.1) :=
        (h_mu_meas n false).comp (Measurable.prodMk measurable_const hx)
      have he : Measurable (fun z : γ × Bool × ℝ => e_hat n ω z.1) :=
        (h_e_meas n).comp (Measurable.prodMk measurable_const hx)
      have hind : Measurable (fun z : γ × Bool × ℝ =>
          if z.2.1 = true then (1 : ℝ) else 0) := by
        have ha : Measurable (fun z : γ × Bool × ℝ => z.2.1) := by measurability
        exact (Measurable.of_discrete
          (f := fun b : Bool => if b = true then (1 : ℝ) else 0)).comp ha
      exact ((((hμt.sub hμf).add ((hind.div he).mul (hy.sub hμt))).sub
        (((measurable_const.sub hind).div (measurable_const.sub he)).mul
          (hy.sub hμf))).sub measurable_const)
    have hrand_L2 :
        MemLp (fun z : γ × Bool × ℝ => aipwMomentFunctional (η_hat n ω) z S.θ₀)
          2 S.P_Z := by
      rw [BackdoorEstimationSystem.P_Z]
      exact (memLp_map_measure_iff hrand_meas.aestronglyMeasurable
        S.measurable_factualZ.aemeasurable).2 hrand_comp_L2
    simpa using hrand_L2.integrable_sq
  -- 7. Apply the high-probability abstract theorem.
  have hMZ := aipw_meanZero S hη₀_mem h_overlap hA h_y2 h_yd2
  have hFV : Integrable (fun z =>
      ((aipwGeneralMoment S hη₀_mem).m
        (aipwGeneralMoment S hη₀_mem).η₀ z
        (aipwGeneralMoment S hη₀_mem).θ₀) ^ 2) S.P_Z := by
    simpa [aipwGeneralMoment, BackdoorEstimationSystem.ψ_AIPW,
      BackdoorEstimationSystem.η₀, aipwMomentFunctional] using
        BackdoorEstimationSystem.aipw_finite_var_of_counterfactual_sq S
          h_overlap hA h_y2 h_yd2
  have h_L2 : ∀ η ∈ H_ε_aeL2 S ε,
      (∀ d, MemLp (fun x => η.μ_fn d x - S.μ_val d x) 2 S.P_X) ∧
      MemLp (fun x => η.e_fn x - S.e_val x) 2 S.P_X := by
    intro η hη
    refine ⟨fun d => (hη.2.1 d).sub (hμ_val_memLp d), ?_⟩
    exact (hη.2.2.mono_exponent (by norm_num)).sub he_val_memLp
  obtain ⟨Crem, hBR⟩ :=
    aipw_bilinearRem S hη₀_mem h_overlap hA h_y2 h_yd2 h_L2
  have hBR_at : ∀ n ω, ω ∈ goodSet n →
      |∫ z, (aipwGeneralMoment S hη₀_mem).m (η_hat n ω) z
        (aipwGeneralMoment S hη₀_mem).θ₀ ∂S.P_Z| ≤
        Crem * (((aipwGeneralMoment S hη₀_mem).ρ₁
          (η_hat n ω) S.η₀ : NNReal) : ℝ) *
        (((aipwGeneralMoment S hη₀_mem).ρ₂
          (η_hat n ω) S.η₀ : NNReal) : ℝ) := by
    intro n ω hω
    exact hBR (η_hat n ω) (h_in_Hε n ω hω)
  let η_safe : ℕ → P.Ω → NuisanceVec γ := fun n ω =>
    if ω ∈ goodSet n then η_hat n ω else S.η₀
  have hsafe_H : ∀ n ω, η_safe n ω ∈ H_ε_aeL2 S ε := by
    intro n ω
    by_cases hω : ω ∈ goodSet n
    · simpa [η_safe, hω] using h_in_Hε n ω hω
    · simpa [η_safe, hω] using hη₀_mem
  have hsafe_μ : ∀ n ω a, MemLp
      (fun x => (η_safe n ω).μ_fn a x - S.μ_val a x) 2 S.P_X := by
    intro n ω a
    by_cases hω : ω ∈ goodSet n
    · simpa [η_safe, hω] using h_mu_diff_memLp n ω hω a
    · simpa [η_safe, hω, BackdoorEstimationSystem.η₀]
  have hsafe_e : ∀ n ω, MemLp
      (fun x => (η_safe n ω).e_fn x - S.e_val x) 2 S.P_X := by
    intro n ω
    by_cases hω : ω ∈ goodSet n
    · simpa [η_safe, hω] using h_e_diff_memLp n ω hω
    · simpa [η_safe, hω, BackdoorEstimationSystem.η₀]
  have hsafe_mu_rate : ∀ a : Bool, IsLittleOp
      (fun n ω => (eLpNorm
        (fun x => (η_safe n ω).μ_fn a x - S.μ_val a x) 2 S.P_X).toReal)
      (fun _ => (1 : ℝ)) P.μ := by
    intro a
    apply Causalean.Stat.isLittleOp_of_isLittleOp_on_highProbEvent
      (Xn := fun n ω => (eLpNorm
        (fun x => (η_safe n ω).μ_fn a x - S.μ_val a x) 2 S.P_X).toReal)
      (Yn := fun n ω => (eLpNorm
        (fun x => (η_hat n ω).μ_fn a x - S.μ_val a x) 2 S.P_X).toReal)
      goodSet Δ hΔ hfail
    · intro n ω hω
      simp [η_safe, hω]
    · exact h_mu_rate a
  have hsafe_e_rate : IsLittleOp
      (fun n ω => (eLpNorm
        (fun x => (η_safe n ω).e_fn x - S.e_val x) 2 S.P_X).toReal)
      (fun _ => (1 : ℝ)) P.μ := by
    apply Causalean.Stat.isLittleOp_of_isLittleOp_on_highProbEvent
      (Xn := fun n ω => (eLpNorm
        (fun x => (η_safe n ω).e_fn x - S.e_val x) 2 S.P_X).toReal)
      (Yn := fun n ω => (eLpNorm
        (fun x => (η_hat n ω).e_fn x - S.e_val x) 2 S.P_X).toReal)
      goodSet Δ hΔ hfail
    · intro n ω hω
      simp [η_safe, hω]
    · exact h_e_rate
  have hsafe_score := BackdoorEstimationSystem.aipw_score_diff_isLittleOp_one
    S h_overlap hA h_y2 h_yd2 η_safe hsafe_H hsafe_μ hsafe_e
      hsafe_mu_rate hsafe_e_rate
  have h_score_diff_rate : IsLittleOp
      (fun n ω => (eLpNorm (fun z =>
        aipwMomentFunctional (η_hat n ω) z S.θ₀ -
          aipwMomentFunctional S.η₀ z S.θ₀) 2 S.P_Z).toReal)
      (fun _ => (1 : ℝ)) P.μ := by
    apply Causalean.Stat.isLittleOp_of_isLittleOp_on_highProbEvent
      (Xn := fun n ω => (eLpNorm (fun z =>
        aipwMomentFunctional (η_hat n ω) z S.θ₀ -
          aipwMomentFunctional S.η₀ z S.θ₀) 2 S.P_Z).toReal)
      (Yn := fun n ω => (eLpNorm (fun z =>
        aipwMomentFunctional (η_safe n ω) z S.θ₀ -
          aipwMomentFunctional S.η₀ z S.θ₀) 2 S.P_Z).toReal)
      goodSet Δ hΔ hfail
    · intro n ω hω
      simp [η_safe, hω]
    · exact hsafe_score
  have hAL :=
    Causalean.Estimation.OrthogonalMoments.oneStepOracleDML_isAsymLinear_on_highProbEvent
      (aipwGeneralMoment S hη₀_mem) hMZ hFV sample split hc_pos h_split_rate
      η_hat goodSet Δ hΔ hfail (Crem := Crem) hBR_at
      h_m_meas h_m_foldA h_m_foldA_uncurry
      h_m_int h_m_sq_int (by simpa [aipwGeneralMoment] using h_score_diff_rate)
      h_product_rate_abs
  -- 8. Transport the conclusion to the production form.
  --
  -- Strategy (option (b) — handles the empty-fold case correctly).  The
  -- estimators `oneStepOracleDML` and `dmlEstimator` differ when
  -- `|B(n)| = 0` (the former equals `θ₀`, the latter equals `0`), but the
  -- *rescaled* errors `√|B(n)| · (θ̂ − θ₀)` agree pointwise in `(n, ω)`
  -- (both vanish in the empty case via `√0 = 0`), and that is the only
  -- estimator-dependent quantity inside `IsAsymLinear`.  We also prove the
  -- influence-function equality `−linScaleInv · aipwMomentFunctional S.η₀ z S.θ₀
  -- = S.ψ_AIPW z` and then build the production `IsAsymLinear` field-by-field.
  --
  -- IF equality (pointwise on `z`).
  have h_if_eq :
      (fun z => -(aipwGeneralMoment S hη₀_mem).linScaleInv *
                  aipwMomentFunctional S.η₀ z S.θ₀)
      = S.ψ_AIPW := by
    funext z
    -- `linScale = -1`, so `linScaleInv = -1`, hence `-linScaleInv = 1`.
    have hJ : -(aipwGeneralMoment S hη₀_mem).linScaleInv = 1 := by
      show -((aipwGeneralMoment S hη₀_mem).linScale)⁻¹ = 1
      show -((-1 : ℝ))⁻¹ = 1
      norm_num
    rw [hJ, one_mul]
    -- `aipwMomentFunctional S.η₀ z S.θ₀ = aipwMoment z S.μ_val S.e_val S.θ₀ = S.ψ_AIPW z`.
    rfl
  -- Rescaled-error equality (pointwise on `(n, ω)`).
  have h_resc_eq : ∀ n ω,
      Real.sqrt ((split.foldB n).card : ℝ) *
        (Causalean.Estimation.OrthogonalMoments.oneStepOracleDML
          (aipwGeneralMoment S hη₀_mem) sample split η_hat n ω - S.θ₀)
      = Real.sqrt ((split.foldB n).card : ℝ) *
        (dmlEstimator S sample split μ_hat e_hat n ω - S.θ₀) := by
    intro n ω
    by_cases hcard : (split.foldB n).card = 0
    · -- Empty fold: both sides reduce to `√0 · _ = 0`.
      have hzero : Real.sqrt ((split.foldB n).card : ℝ) = 0 := by
        rw [hcard]; simp
      rw [hzero, zero_mul, zero_mul]
    · -- Nonempty fold: `dmlEstimator n ω = dmlChern n ω`.
      have hcard_pos : 0 < (split.foldB n).card := Nat.pos_of_ne_zero hcard
      have hcardR_pos : 0 < ((split.foldB n).card : ℝ) := by exact_mod_cast hcard_pos
      have hcardR_ne : ((split.foldB n).card : ℝ) ≠ 0 := hcardR_pos.ne'
      -- `(aipwGeneralMoment S hη₀_mem).linScaleInv = -1`.
      have h_J : (aipwGeneralMoment S hη₀_mem).linScaleInv = -1 := by
        show ((-1 : ℝ))⁻¹ = -1
        norm_num
      -- Pointwise: `aipwMoment(z, μ̂, ê, 0) = aipwMoment(z, μ̂, ê, S.θ₀) + S.θ₀`.
      have hpoint : ∀ i,
          aipwMoment (sample.Z i ω) (μ_hat n ω) (e_hat n ω) 0 =
            aipwMoment (sample.Z i ω) (μ_hat n ω) (e_hat n ω) S.θ₀ + S.θ₀ := by
        intro i
        unfold aipwMoment
        ring
      -- Sum the pointwise identity.
      have hsum :
          ∑ i ∈ split.foldB n,
              aipwMoment (sample.Z i ω) (μ_hat n ω) (e_hat n ω) 0
            = (∑ i ∈ split.foldB n,
                aipwMoment (sample.Z i ω) (μ_hat n ω) (e_hat n ω) S.θ₀)
              + ((split.foldB n).card : ℝ) * S.θ₀ := by
        rw [Finset.sum_congr rfl (fun i _ => hpoint i),
          Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      -- Reduce the goal: cancel the common `√|B(n)| · _` factor.
      congr 1
      -- First rewrite `linScaleInv` to `-1` for the unreduced moment.
      simp only [Causalean.Estimation.OrthogonalMoments.oneStepOracleDML, dmlEstimator]
      rw [h_J]
      -- Now unfold the remaining `M.*` projections (`θ₀`, `m`).  After this
      -- `M.m (η_hat n ω) z M.θ₀ = aipwMoment z (μ_hat n ω) (e_hat n ω) S.θ₀`.
      simp only [aipwGeneralMoment, aipwMomentFunctional]
      -- Goal: `S.θ₀ − (−1) · ((|B|⁻¹) · Σ aipwMoment(., μ̂, ê, S.θ₀)) − S.θ₀
      --       = (|B|⁻¹) · Σ aipwMoment(., μ̂, ê, 0) − S.θ₀`.
      rw [hsum]
      field_simp
      ring
  -- Build the production `IsAsymLinear` from `hAL` field-by-field.
  refine ⟨?_, ?_, ?_⟩
  · -- mean_zero: `∫ S.ψ_AIPW dP_Z = 0`.
    have h := hAL.mean_zero
    rw [← h_if_eq]
    exact h
  · -- finite_var: `Integrable (fun z => (S.ψ_AIPW z) ^ 2) S.P_Z`.
    have h := hAL.finite_var
    rw [← h_if_eq]
    exact h
  · -- remainder: the two `IsLittleOp` integrands agree pointwise.
    have h := hAL.remainder
    -- The abstract remainder integrand and the production one are equal as
    -- functions of `(n, ω)`: rescaled errors agree by `h_resc_eq`, and the
    -- influence-function partial sum agrees by `h_if_eq`.
    have hfun_eq :
        (fun n ω =>
            Real.sqrt ((split.foldB n).card : ℝ) *
              (dmlEstimator S sample split μ_hat e_hat n ω - S.θ₀) -
              (Real.sqrt ((split.foldB n).card : ℝ))⁻¹ *
                ∑ i ∈ split.foldB n, S.ψ_AIPW (sample.Z i ω))
        = (fun n ω =>
            Real.sqrt ((split.foldB n).card : ℝ) *
              (Causalean.Estimation.OrthogonalMoments.oneStepOracleDML
                (aipwGeneralMoment S hη₀_mem) sample split η_hat n ω - S.θ₀) -
              (Real.sqrt ((split.foldB n).card : ℝ))⁻¹ *
                ∑ i ∈ split.foldB n,
                  (-(aipwGeneralMoment S hη₀_mem).linScaleInv *
                    aipwMomentFunctional S.η₀ (sample.Z i ω) S.θ₀)) := by
      funext n ω
      rw [h_resc_eq n ω]
      congr 1
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      have := congrArg (fun f => f (sample.Z i ω)) h_if_eq
      simpa using this.symm
    rw [hfun_eq]
    exact h

/-- For [an ATE estimation system and threshold](hyp:S,ε), [identification,
overlap, and moment assumptions](hyp:hA,h_overlap,h_y2,h_yd2), [a sample and
one-shot split](hyp:sample,split) with [a nondegenerate limiting
fraction](hyp:c,hc_pos,hc_lt,h_split_rate),
and [nuisance learners](hyp:μ_hat,e_hat), assume [ambient
measurability](hyp:h_mu_meas,h_e_meas), [almost-sure square-integrability and
overlap at every horizon](hyp:h_mu_memLp,h_e_memLp,h_e_overlap), [training-fold
measurability](hyp:h_mu_foldA,h_e_foldA,h_mu_uncurry_foldA,h_e_uncurry_foldA),
and [the individual and product rates](hyp:h_mu_rate,h_e_rate,h_product_rate).
Then [the one-shot DML/AIPW estimator is asymptotically linear](goal).

This is the zero-failure-probability corollary of
`dml_ATE_isAsymLinear_of_goodSet`. -/
theorem dml_ATE_isAsymLinear_of_goodSet_ae
    (S : BackdoorEstimationSystem P γ)
    {ε : ℝ}
    (hA : S.toPOBackdoorSystem.Assumptions)
    (h_overlap : S.StrictOverlap ε)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_yd2 : ∀ d : Bool, Integrable
      (fun ω => (S.toPOBackdoorSystem.YofD d ω) ^ 2) P.μ)
    (sample : IIDSample P.Ω (γ × Bool × ℝ) P.μ S.P_Z)
    (split : OneShotSplit sample)
    {c : ℝ} (hc_pos : 0 < c) (hc_lt : c < 1)
    (h_split_rate :
      Tendsto (fun n => ((split.foldB n).card : ℝ) / n) atTop (𝓝 c))
    (μ_hat : ℕ → P.Ω → (Bool → γ → ℝ))
    (e_hat : ℕ → P.Ω → (γ → ℝ))
    (h_mu_meas :
      ∀ n a, Measurable (fun (p : P.Ω × γ) => μ_hat n p.1 a p.2))
    (h_e_meas :
      ∀ n, Measurable (fun (p : P.Ω × γ) => e_hat n p.1 p.2))
    (h_mu_memLp :
      ∀ n, ∀ᵐ ω ∂P.μ, ∀ a, MemLp (fun x => μ_hat n ω a x) 2 S.P_X)
    (h_e_memLp :
      ∀ n, ∀ᵐ ω ∂P.μ, MemLp (fun x => e_hat n ω x) 2 S.P_X)
    (h_e_overlap :
      ∀ n, ∀ᵐ ω ∂P.μ, ∀ᵐ x ∂S.P_X,
        ε ≤ e_hat n ω x ∧ e_hat n ω x ≤ 1 - ε)
    (h_mu_foldA :
      ∀ n,
        Measurable[MeasurableSpace.comap
          (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance]
          (μ_hat n))
    (h_e_foldA :
      ∀ n,
        Measurable[MeasurableSpace.comap
          (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance]
          (e_hat n))
    (h_mu_uncurry_foldA :
      ∀ n a,
        Measurable[(MeasurableSpace.comap
            (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
          (inferInstance : MeasurableSpace γ)]
          (fun (p : P.Ω × γ) => μ_hat n p.1 a p.2))
    (h_e_uncurry_foldA :
      ∀ n,
        Measurable[(MeasurableSpace.comap
            (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
          (inferInstance : MeasurableSpace γ)]
          (fun (p : P.Ω × γ) => e_hat n p.1 p.2))
    (h_mu_rate :
      ∀ a : Bool,
        IsLittleOp
          (fun n ω =>
            (eLpNorm (fun x => μ_hat n ω a x - S.μ_val a x) 2 S.P_X).toReal)
          (fun _ => (1 : ℝ)) P.μ)
    (h_e_rate :
      IsLittleOp
        (fun n ω =>
          (eLpNorm (fun x => e_hat n ω x - S.e_val x) 2 S.P_X).toReal)
        (fun _ => (1 : ℝ)) P.μ)
    (h_product_rate :
      ∀ a : Bool,
        IsLittleOp
          (fun n ω =>
            (eLpNorm (fun x => μ_hat n ω a x - S.μ_val a x) 2 S.P_X).toReal *
              (eLpNorm (fun x => e_hat n ω x - S.e_val x) 2 S.P_X).toReal)
          (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) P.μ) :
    IsAsymLinear
      (dmlEstimator S sample split μ_hat e_hat)
      S.θ₀
      (S.ψ_AIPW)
      sample
      split.foldB := by
  classical
  let goodSet : ℕ → Set P.Ω := fun n => {ω |
    (∀ a, MemLp (fun x => μ_hat n ω a x) 2 S.P_X) ∧
    MemLp (fun x => e_hat n ω x) 2 S.P_X ∧
    (∀ᵐ x ∂S.P_X, ε ≤ e_hat n ω x ∧ e_hat n ω x ≤ 1 - ε)}
  have hgood : ∀ n, ∀ᵐ ω ∂P.μ, ω ∈ goodSet n := by
    intro n
    filter_upwards [h_mu_memLp n, h_e_memLp n, h_e_overlap n] with ω hμ he hover
    exact ⟨hμ, he, hover⟩
  apply dml_ATE_isAsymLinear_of_goodSet S hA h_overlap h_y2 h_yd2 sample
    split hc_pos hc_lt h_split_rate μ_hat e_hat goodSet (fun _ => 0)
    tendsto_const_nhds
  · intro n
    have hz : P.μ (goodSet n)ᶜ = 0 := by
      apply ae_iff.mp
      filter_upwards [hgood n] with ω hω
      exact hω
    simpa [hz]
  · exact h_mu_meas
  · exact h_e_meas
  · intro n ω hω
    exact hω.1
  · intro n ω hω
    exact hω.2.1
  · intro n ω hω
    exact hω.2.2
  · exact h_mu_foldA
  · exact h_e_foldA
  · exact h_mu_uncurry_foldA
  · exact h_e_uncurry_foldA
  · exact h_mu_rate
  · exact h_e_rate
  · exact h_product_rate

/-- **Deprecated everywhere-good ATE DML interface.** Under [the back-door and
overlap conditions](hyp:S,hA,h_overlap), [moment assumptions](hyp:h_y2,h_yd2),
[sample-split conditions](hyp:sample,split,hc_pos,hc_lt,h_split_rate),
[nuisance learners](hyp:μ_hat,e_hat), [measurability
conditions](hyp:h_mu_meas,h_e_meas,h_mu_foldA,h_e_foldA,h_mu_uncurry_foldA,h_e_uncurry_foldA),
and [rate conditions](hyp:h_mu_rate,h_e_rate,h_product_rate),
and [the former pointwise learner conditions](hyp:h_mu_memLp,h_e_memLp,h_e_overlap),
[the one-shot ATE estimator is asymptotically linear](goal). Use
`dml_ATE_isAsymLinear_of_goodSet` for the high-probability good-set form. -/
@[deprecated dml_ATE_isAsymLinear_of_goodSet (since := "2026-09-16")]
theorem dml_ATE_isAsymLinear
    (S : BackdoorEstimationSystem P γ)
    {ε : ℝ}
    (hA : S.toPOBackdoorSystem.Assumptions)
    (h_overlap : S.StrictOverlap ε)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_yd2 : ∀ d : Bool, Integrable
      (fun ω => (S.toPOBackdoorSystem.YofD d ω) ^ 2) P.μ)
    (sample : IIDSample P.Ω (γ × Bool × ℝ) P.μ S.P_Z)
    (split : OneShotSplit sample)
    {c : ℝ} (hc_pos : 0 < c) (hc_lt : c < 1)
    (h_split_rate :
      Tendsto (fun n => ((split.foldB n).card : ℝ) / n) atTop (𝓝 c))
    (μ_hat : ℕ → P.Ω → (Bool → γ → ℝ))
    (e_hat : ℕ → P.Ω → (γ → ℝ))
    (h_mu_meas :
      ∀ n a, Measurable (fun (p : P.Ω × γ) => μ_hat n p.1 a p.2))
    (h_e_meas :
      ∀ n, Measurable (fun (p : P.Ω × γ) => e_hat n p.1 p.2))
    (h_mu_memLp :
      ∀ n ω a, MemLp (fun x => μ_hat n ω a x) 2 S.P_X)
    (h_e_memLp :
      ∀ n ω, MemLp (fun x => e_hat n ω x) 2 S.P_X)
    (h_e_overlap :
      ∀ n ω, ∀ᵐ x ∂S.P_X, ε ≤ e_hat n ω x ∧ e_hat n ω x ≤ 1 - ε)
    (h_mu_foldA :
      ∀ n,
        Measurable[MeasurableSpace.comap
          (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance]
          (μ_hat n))
    (h_e_foldA :
      ∀ n,
        Measurable[MeasurableSpace.comap
          (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance]
          (e_hat n))
    (h_mu_uncurry_foldA :
      ∀ n a,
        Measurable[(MeasurableSpace.comap
            (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
          (inferInstance : MeasurableSpace γ)]
          (fun (p : P.Ω × γ) => μ_hat n p.1 a p.2))
    (h_e_uncurry_foldA :
      ∀ n,
        Measurable[(MeasurableSpace.comap
            (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
          (inferInstance : MeasurableSpace γ)]
          (fun (p : P.Ω × γ) => e_hat n p.1 p.2))
    (h_mu_rate :
      ∀ a : Bool,
        IsLittleOp
          (fun n ω =>
            (eLpNorm (fun x => μ_hat n ω a x - S.μ_val a x) 2 S.P_X).toReal)
          (fun _ => (1 : ℝ)) P.μ)
    (h_e_rate :
      IsLittleOp
        (fun n ω =>
          (eLpNorm (fun x => e_hat n ω x - S.e_val x) 2 S.P_X).toReal)
        (fun _ => (1 : ℝ)) P.μ)
    (h_product_rate :
      ∀ a : Bool,
        IsLittleOp
          (fun n ω =>
            (eLpNorm (fun x => μ_hat n ω a x - S.μ_val a x) 2 S.P_X).toReal *
              (eLpNorm (fun x => e_hat n ω x - S.e_val x) 2 S.P_X).toReal)
          (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) P.μ) :
    IsAsymLinear
      (dmlEstimator S sample split μ_hat e_hat)
      S.θ₀
      (S.ψ_AIPW)
      sample
      split.foldB := by
  apply dml_ATE_isAsymLinear_of_goodSet S hA h_overlap h_y2 h_yd2 sample
    split hc_pos hc_lt h_split_rate μ_hat e_hat (fun _ => Set.univ)
    (fun _ => 0) tendsto_const_nhds (by simp) h_mu_meas h_e_meas
  · exact fun n ω _ a => h_mu_memLp n ω a
  · exact fun n ω _ => h_e_memLp n ω
  · exact fun n ω _ => h_e_overlap n ω
  · exact h_mu_foldA
  · exact h_e_foldA
  · exact h_mu_uncurry_foldA
  · exact h_e_uncurry_foldA
  · exact h_mu_rate
  · exact h_e_rate
  · exact h_product_rate

end ATE
end Estimation
end Causalean
