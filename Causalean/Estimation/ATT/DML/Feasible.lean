/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Estimation.ATT.DML
public import Causalean.Estimation.OrthogonalMoments.DMLCrossFit.Feasible

/-! # Feasible one-shot DML estimator for the ATT

This file defines the ATT estimator that divides its evaluation-fold AIPW
numerator by the evaluation-fold treated share. It realizes the ATT score as an
affine `LinearMoment`, then specializes the generic solved-estimator theorem to
obtain the Chernozhukov et al. (2018), equation (5.4), influence function. In
particular, the expansion contains the `-D * θ₀ / p` term induced by estimating
the treated share.
-/

@[expose] public section

namespace Causalean
namespace Estimation
namespace ATT

open MeasureTheory ProbabilityTheory Filter Topology Causalean.PO Causalean.Stat
open TreatedEstimationSystem
open Causalean.Estimation.OrthogonalMoments
open Causalean.Estimation.ATE.BackdoorEstimationSystem (indA projA)

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-- For [a potential-outcomes system](hyp:P), [a measurable covariate
space](hyp:γ), and [a treated estimation system](hyp:S), [the population integral of the
treatment indicator under its observed-data law equals the marginal treated
share](goal).

This is the coefficient identity behind the ATT score Jacobian. -/
lemma integral_indA_eq_π_val (S : TreatedEstimationSystem P γ) :
    ∫ z, indA z ∂S.P_Z = S.π_val := by
  have hindA_meas : Measurable (fun z : γ × Bool × ℝ => indA z) := by
    unfold indA projA
    refine Measurable.ite ?_ measurable_const measurable_const
    exact measurable_snd.fst (MeasurableSet.singleton true)
  rw [TreatedEstimationSystem.P_Z,
    integral_map S.measurable_factualZ.aemeasurable
      hindA_meas.aestronglyMeasurable]
  have hpoint : (fun ω => indA (S.factualZ ω)) =
      (fun ω => S.toPOBackdoorSystem.dVar.indicator true ω) := by
    funext ω
    by_cases hD : S.toPOBackdoorSystem.factualD ω = true
    · have hInd : S.toPOBackdoorSystem.dVar.indicator true ω = 1 :=
        S.toPOBackdoorSystem.dVar.indicator_apply_eq_one hD
      simp [TreatedEstimationSystem.factualZ, indA, projA, hD, hInd]
    · have hInd : S.toPOBackdoorSystem.dVar.indicator true ω = 0 :=
        S.toPOBackdoorSystem.dVar.indicator_apply_eq_zero (x := true) hD
      simp [TreatedEstimationSystem.factualZ, indA, projA, hD, hInd]
  rw [hpoint]
  rfl

/-- For [a potential-outcomes system](hyp:P), [a measurable covariate
space](hyp:γ), [a treated estimation system](hyp:S), [an overlap radius](hyp:ε),
[membership of its true nuisance in the overlap-bounded candidate
set](hyp:hη₀_mem), and [a positive population treated share](hyp:hπ_pos), the
[affine ATT AIPW moment system](goal) has
[coefficient `-D`](step:1) and [constant term equal to the ATT AIPW numerator
at parameter zero](step:2).

Its empirical moment solution divides the AIPW numerator by the empirical
treated share, while its population Jacobian is `-p`. -/
noncomputable def attLinearMoment
    (S : TreatedEstimationSystem P γ) {ε : ℝ}
    (hη₀_mem : S.η₀ ∈ H_ε S ε) (hπ_pos : 0 < S.π_val) :
    LinearMoment P.Ω P.μ (γ × Bool × ℝ) S.P_Z (TreatedNuisanceVec γ) where
  toGeneralMoment := attGeneralMoment S hη₀_mem hπ_pos
  m_a := fun _ z => -indA z
  m_b := fun η z => aipwMomentATTFunctional η z 0
  m_a_meas := fun _ => by
    unfold indA projA
    refine Measurable.neg (Measurable.ite ?_ measurable_const measurable_const)
    exact measurable_snd.fst (MeasurableSet.singleton true)
  m_b_meas := fun η => measurable_aipwMomentATTFunctional η 0
  m_decomp := by
    intro η z θ
    change aipwMomentATTFunctional η z θ =
      -indA z * θ + aipwMomentATTFunctional η z 0
    unfold aipwMomentATTFunctional aipwMomentATT
    ring
  linScale_eq := by
    rw [integral_neg, integral_indA_eq_π_val S]
    simp [attGeneralMoment]

/-- For [a potential-outcomes system](hyp:P), [a measurable covariate
space](hyp:γ), [a treated estimation system](hyp:S), [an i.i.d. observed-data
sample](hyp:sample), [a one-shot split](hyp:split), [a complementary-fold ATT
nuisance fit](hyp:η_hat), and [a sample-size index](hyp:n), the [feasible
one-shot ATT DML estimator](goal) is [the evaluation-fold AIPW numerator mean
divided by the evaluation-fold treated share](step:1).

No population treated share occurs in the statistic. When an evaluation fold
has zero treated share, Lean's totalized inverse assigns the displayed ratio
the value zero. -/
noncomputable def dmlEstimator_ATT
    (S : TreatedEstimationSystem P γ)
    (sample : IIDSample P.Ω (γ × Bool × ℝ) P.μ S.P_Z)
    (split : OneShotSplit sample)
    (η_hat : ℕ → P.Ω → TreatedNuisanceVec γ)
    (n : ℕ) : P.Ω → ℝ :=
  fun ω =>
    ((((split.foldB n).card : ℝ)⁻¹ *
      ∑ i ∈ split.foldB n, indA (sample.Z i ω))⁻¹) *
    (((split.foldB n).card : ℝ)⁻¹ *
      ∑ i ∈ split.foldB n,
        aipwMomentATTFunctional (η_hat n ω) (sample.Z i ω) 0)

/-- For [a potential-outcomes system](hyp:P), [a measurable covariate
space](hyp:γ), [a treated estimation system](hyp:S), [an overlap radius](hyp:ε),
[truth-nuisance overlap membership](hyp:hη₀_mem), [a positive population treated share](hyp:hπ_pos),
[an i.i.d. sample](hyp:sample), [a one-shot split](hyp:split), and [an ATT
nuisance fit](hyp:η_hat), [the feasible ATT estimator equals the generic solved
affine-score DML estimator](goal). -/
lemma dmlEstimator_ATT_eq_feasibleLinearDML
    (S : TreatedEstimationSystem P γ) {ε : ℝ}
    (hη₀_mem : S.η₀ ∈ H_ε S ε) (hπ_pos : 0 < S.π_val)
    (sample : IIDSample P.Ω (γ × Bool × ℝ) P.μ S.P_Z)
    (split : OneShotSplit sample)
    (η_hat : ℕ → P.Ω → TreatedNuisanceVec γ) :
    dmlEstimator_ATT S sample split η_hat =
      feasibleLinearDML (attLinearMoment S hη₀_mem hπ_pos)
        sample split η_hat := by
  funext n ω
  simp only [dmlEstimator_ATT, feasibleLinearDML, attLinearMoment]
  rw [Finset.sum_neg_distrib]
  ring

/-- **Feasible ATT DML asymptotic linearity.** For [a potential-outcomes
system](hyp:P), [a measurable covariate space](hyp:γ), [a treated estimation
system](hyp:S), [an overlap radius](hyp:ε), [truth-nuisance overlap membership](hyp:hη₀_mem), [a
nonnegative true propensity](hyp:h_e_lb), [one-sided overlap](hyp:h_overlap),
[the back-door ATT assumptions](hyp:hA), [a positive treated share](hyp:hπ_pos),
[factual- and untreated-outcome second moments](hyp:h_y2,h_y0_2), [integrable
truth IPW correction](hyp:hIPW), [an i.i.d. sample](hyp:sample), [a one-shot
split](hyp:split), [a limiting evaluation-fold share](hyp:c), [that share being
positive and below one](hyp:hc_pos,_hc_lt), [convergence of the evaluation-fold
share](hyp:h_split_rate),
and [a complementary-fold nuisance sequence](hyp:η_hat), if [every fitted
nuisance lies in the overlap set](hyp:h_in_Hε), [every fitted propensity is
nonnegative](hyp:h_e_lb_hat), [both fitted nuisance errors are
square-integrable](hyp:h_mu_diff_memLp,h_e_diff_memLp), [each fitted IPW
correction is integrable](hyp:h_IPW_at), [the fitted score has the required
joint and training-fold measurability](hyp:h_m_meas,h_m_foldA,h_m_foldA_uncurry),
[the fitted score is integrable and square-integrable](hyp:h_m_int,h_m_sq_int),
[both nuisance errors are individually negligible](hyp:h_indiv_rate_ρ₁,h_indiv_rate_ρ₂),
and [their product is negligible at the root-sample rate](hyp:h_product_rate),
then [the sample-treated-share ATT estimator is asymptotically linear with
influence function `m(η₀,z,θ₀)/p`](goal).

The score in the conclusion is exactly Chernozhukov et al. (2018), equation
(5.4), at the truth. Its final summand is `-D * θ₀ / p`, which is the
first-order contribution from estimating the treated share. -/
theorem dml_ATT_isAsymLinear
    (S : TreatedEstimationSystem P γ) {ε : ℝ}
    (hη₀_mem : S.η₀ ∈ H_ε S ε)
    (h_e_lb : ∀ x, 0 ≤ S.e_val x)
    (h_overlap : S.OneSidedOverlap ε)
    (hA : S.toPOBackdoorSystem.ATTAssumptions)
    (hπ_pos : 0 < S.π_val)
    (h_y2 : Integrable (fun ω =>
      (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_y0_2 : Integrable (fun ω =>
      (S.toPOBackdoorSystem.YofD false ω) ^ 2) P.μ)
    (hIPW : Integrable (fun ω =>
      (1 - S.toPOBackdoorSystem.dVar.indicator true ω) *
        (S.toPOBackdoorSystem.propScore true ω /
          (1 - S.toPOBackdoorSystem.propScore true ω)) *
        (S.toPOBackdoorSystem.factualY ω -
          S.toPOBackdoorSystem.adjustedCE false ω)) P.μ)
    (sample : IIDSample P.Ω (γ × Bool × ℝ) P.μ S.P_Z)
    (split : OneShotSplit sample)
    {c : ℝ} (hc_pos : 0 < c) (_hc_lt : c < 1)
    (h_split_rate :
      Tendsto (fun n => ((split.foldB n).card : ℝ) / n) atTop (𝓝 c))
    (η_hat : ℕ → P.Ω → TreatedNuisanceVec γ)
    (h_in_Hε : ∀ n ω, η_hat n ω ∈ H_ε S ε)
    (h_e_lb_hat : ∀ n ω x, 0 ≤ (η_hat n ω).e_fn x)
    (h_mu_diff_memLp : ∀ n ω, MemLp
      (fun x => (η_hat n ω).μ₀_fn x - S.μ₀_val x) 2 S.P_X)
    (h_e_diff_memLp : ∀ n ω, MemLp
      (fun x => (η_hat n ω).e_fn x - S.e_val x) 2 S.P_X)
    (h_IPW_at : ∀ n ω, Integrable (fun z =>
      (1 - indA z) *
        ((η_hat n ω).e_fn
            (Causalean.Estimation.ATE.BackdoorEstimationSystem.projX z) /
          (1 - (η_hat n ω).e_fn
            (Causalean.Estimation.ATE.BackdoorEstimationSystem.projX z))) *
        (Causalean.Estimation.ATE.BackdoorEstimationSystem.projY z -
          (η_hat n ω).μ₀_fn
            (Causalean.Estimation.ATE.BackdoorEstimationSystem.projX z))) S.P_Z)
    (h_m_meas : ∀ n, Measurable (fun (p : P.Ω × (γ × Bool × ℝ)) =>
      aipwMomentATTFunctional (η_hat n p.1) p.2 S.θ₀))
    (h_m_foldA : ∀ n,
      Measurable[MeasurableSpace.comap
        (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance]
        (fun ω z => aipwMomentATTFunctional (η_hat n ω) z S.θ₀))
    (h_m_foldA_uncurry : ∀ n,
      Measurable[(MeasurableSpace.comap
          (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
        (inferInstance : MeasurableSpace (γ × Bool × ℝ))]
        (fun (p : P.Ω × (γ × Bool × ℝ)) =>
          aipwMomentATTFunctional (η_hat n p.1) p.2 S.θ₀))
    (h_m_int : ∀ n ω, Integrable
      (fun z => aipwMomentATTFunctional (η_hat n ω) z S.θ₀) S.P_Z)
    (h_m_sq_int : ∀ n ω, Integrable
      (fun z => (aipwMomentATTFunctional (η_hat n ω) z S.θ₀) ^ 2) S.P_Z)
    (h_indiv_rate_ρ₁ : IsLittleOp
      (fun n ω => (((attGeneralMoment S hη₀_mem hπ_pos).ρ₁
        (η_hat n ω) S.η₀ : NNReal) : ℝ))
      (fun _ => (1 : ℝ)) P.μ)
    (h_indiv_rate_ρ₂ : IsLittleOp
      (fun n ω => (((attGeneralMoment S hη₀_mem hπ_pos).ρ₂
        (η_hat n ω) S.η₀ : NNReal) : ℝ))
      (fun _ => (1 : ℝ)) P.μ)
    (h_product_rate : IsLittleOp
      (fun n ω => (((attGeneralMoment S hη₀_mem hπ_pos).ρ₁
          (η_hat n ω) S.η₀ : NNReal) : ℝ) *
        (((attGeneralMoment S hη₀_mem hπ_pos).ρ₂
          (η_hat n ω) S.η₀ : NNReal) : ℝ))
      (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) P.μ) :
    IsAsymLinear (dmlEstimator_ATT S sample split η_hat) S.θ₀
      (fun z => (1 / S.π_val) *
        aipwMomentATTFunctional S.η₀ z S.θ₀)
      sample split.foldB := by
  haveI : IsProbabilityMeasure S.P_Z := by
    unfold TreatedEstimationSystem.P_Z
    exact Measure.isProbabilityMeasure_map S.measurable_factualZ.aemeasurable
  let M := attLinearMoment S hη₀_mem hπ_pos
  have hOracle : IsAsymLinear
      (oneStepOracleDML M.toGeneralMoment sample split η_hat) M.θ₀
      (fun z => -M.linScaleInv * M.m M.η₀ z M.θ₀) sample split.foldB := by
    change IsAsymLinear
      (oneStepOracleDML (attGeneralMoment S hη₀_mem hπ_pos)
        sample split η_hat) S.θ₀
      (fun z => -(attGeneralMoment S hη₀_mem hπ_pos).linScaleInv *
        aipwMomentATTFunctional S.η₀ z S.θ₀) sample split.foldB
    exact att_oneStepOracleDML_isAsymLinear S hη₀_mem h_e_lb h_overlap hA hπ_pos
      h_y2 h_y0_2 hIPW sample split hc_pos _hc_lt h_split_rate η_hat
      h_in_Hε h_e_lb_hat h_mu_diff_memLp h_e_diff_memLp h_IPW_at
      h_m_meas h_m_foldA h_m_foldA_uncurry h_m_int h_m_sq_int
      h_indiv_rate_ρ₁ h_indiv_rate_ρ₂ h_product_rate
  have hIndMeas : Measurable (fun z : γ × Bool × ℝ => -indA z) := by
    unfold indA projA
    refine Measurable.neg (Measurable.ite ?_ measurable_const measurable_const)
    exact measurable_snd.fst (MeasurableSet.singleton true)
  have hIndLp : MemLp (fun z : γ × Bool × ℝ => -indA z) 2 S.P_Z := by
    refine MemLp.of_bound hIndMeas.aestronglyMeasurable 1 ?_
    filter_upwards with z
    rcases hb : z.2.1 with _ | _ <;> simp [indA, projA, hb]
  have hJraw := OneShotSplit.foldB_sampleMean_tendsto_inProb
    sample split hIndMeas hIndLp
  have hJ : Tendsto_inProb
      (fun n ω => ((split.foldB n).card : ℝ)⁻¹ *
        ∑ i ∈ split.foldB n, M.m_a (η_hat n ω) (sample.Z i ω))
      (fun _ => M.linScale) P.μ := by
    convert hJraw using 1
    · funext n ω
      simp [M, attLinearMoment]
    · funext n
      rw [M.linScale_eq]
      simp [M, attLinearMoment]
  have hψ_meas : Measurable
      (fun z => -M.linScaleInv * M.m M.η₀ z M.θ₀) := by
    simpa [M, attLinearMoment, attGeneralMoment, GeneralMoment.linScaleInv,
      TreatedEstimationSystem.η₀, one_div] using
      (measurable_aipwMomentATTFunctional S.η₀ S.θ₀).const_mul
        (1 / S.π_val)
  have hOracle_meas : ∀ n, AEMeasurable
      (IsAsymLinear.rescaledEstimator
        (oneStepOracleDML M.toGeneralMoment sample split η_hat)
        M.θ₀ split.foldB n) P.μ := by
    intro n
    have hm : Measurable (fun p : P.Ω × (γ × Bool × ℝ) =>
        M.m (η_hat n p.1) p.2 M.θ₀) := by
      change Measurable (fun p : P.Ω × (γ × Bool × ℝ) =>
        aipwMomentATTFunctional (η_hat n p.1) p.2 S.θ₀)
      exact h_m_meas n
    have hsum : Measurable (fun ω =>
        ∑ i ∈ split.foldB n,
          M.m (η_hat n ω) (sample.Z i ω) M.θ₀) :=
      Finset.measurable_sum _ (fun i _ =>
        hm.comp (Measurable.prodMk measurable_id (sample.meas i)))
    unfold IsAsymLinear.rescaledEstimator oneStepOracleDML
    apply Measurable.aemeasurable
    exact measurable_const.mul
      ((measurable_const.sub
        (measurable_const.mul (measurable_const.mul hsum))).sub
          measurable_const)
  have hSum_meas : ∀ n, AEMeasurable
      (IsAsymLinear.normalizedSum sample
        (fun z => -M.linScaleInv * M.m M.η₀ z M.θ₀) split.foldB n) P.μ := by
    intro n
    unfold IsAsymLinear.normalizedSum
    exact ((Finset.measurable_sum _ (fun i _ =>
      hψ_meas.comp (sample.meas i))).const_mul _).aemeasurable
  have hFeasible := feasibleLinearDML_isAsymLinear_of_jacobianConsistency
    M sample split η_hat hOracle hJ hψ_meas hOracle_meas hSum_meas
  rw [dmlEstimator_ATT_eq_feasibleLinearDML S hη₀_mem hπ_pos
    sample split η_hat]
  simpa [M, attLinearMoment, attGeneralMoment, GeneralMoment.linScaleInv,
    TreatedEstimationSystem.η₀, one_div] using hFeasible

end ATT
end Estimation
end Causalean
