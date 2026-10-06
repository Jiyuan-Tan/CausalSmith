/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# One-shot DML / sequential DR estimator for the DTR (`n = 2`) effect

`def:est-dml-dtr` and `thm:est-dml-dtr-al` instantiated for the
`DTREstimationSystem` from `Setup.lean`.

The estimator is

    θ̂ⁿ_DML := (1/|B(n)|) Σ_{i ∈ B(n)} m_seqDR( dbar, Zᵢ, η̂(n), 0 )
            + θ_correction,

mirroring `Estimation/ATE/DML.lean` stage-by-stage.  The empirical mean
of `m_seqDR(·, ·, ·, 0)` over fold `B(n)` equals the empirical
sequential-DR pseudo-outcome.

The headline `dml_DTR_isAsymLinear` translates user-friendly stagewise
hypotheses (`μ̂_k_n`, `ê_k_n` for `k ∈ {0, 1}`) into the abstract
`seqDR_dml_isAsymLinear` interface, which in turn delegates to
`oneStepOracleDML_isAsymLinear_of_everywhere`.

The estimator definition accepts the bundled nuisance process
`η_hat : ℕ → P.Ω → DTRNuisanceVec₂ δ γ`.  The asymptotic-linearity theorem
is the public wrapper: it builds that bundle from the four stagewise nuisance
learners, checks the score measurability and integrability obligations, and
transports the abstract Chernozhukov estimator conclusion back to
`dml_DTR_estimator`.
-/

module
public import Causalean.Estimation.DTR.DTRInstance
public import Causalean.Estimation.DTR.ScoreL2
public import Causalean.Stat.Sample
public import Causalean.Stat.SampleSplit
public import Causalean.Stat.CLT.AsymptoticLinearity
public import Causalean.Stat.SampleSplit.PartialFoldCLT
public import Causalean.Stat.Limit.Convergence
public import Causalean.Stat.SampleSplit.FoldBEmpiricalProcess

/-! # One-shot DTR DML estimator and score interfaces

Defines `dml_DTR_estimator`, the fold-B empirical mean of the two-stage
sequential doubly robust pseudo-outcome. It also proves the joint measurability
and L² packaging lemmas needed to instantiate the abstract DML theorem. The
asymptotic-linearity wrapper itself is in `AsymptoticLinearity`.
-/

@[expose] public section
namespace Causalean
namespace Estimation
namespace DTR

open MeasureTheory ProbabilityTheory Filter Topology Causalean.PO Causalean.Stat
open DTREstimationSystem

variable {P : POSystem} {δ : Type} {γ : Fin 2 → Type}
  [MeasurableSpace δ] [MeasurableSingletonClass δ]
  [∀ k, MeasurableSpace (γ k)]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
private lemma measurable_indEq_left (d : δ) :
    Measurable (fun x : δ => indEq x d) := by
  have hset : MeasurableSet {x : δ | x = d} :=
    MeasurableSet.singleton d
  have hfun : (fun x : δ => indEq x d)
      = Set.indicator {x : δ | x = d} (fun _ => (1 : ℝ)) := by
    funext x
    by_cases hx : x = d
    · rw [Set.indicator_of_mem (by simpa using hx)]
      simp [indEq, hx]
    · rw [Set.indicator_of_notMem (by simpa using hx)]
      simp [indEq, hx]
  rw [hfun]
  exact (measurable_const.indicator hset :
    Measurable (Set.indicator {x : δ | x = d} (fun _ => (1 : ℝ))))

/-- Given [a dynamic-treatment-regime estimation system, target value, and parameterized nuisance
functions](hyp:P,δ,γ,Ω',S,θ,η_fn), if [the first outcome regression](hyp:h_mu0), [first propensity](hyp:h_e0),
[second outcome regression](hyp:h_mu1), and [second propensity](hyp:h_e1) are jointly measurable in
the parameter and observation, then [the corresponding sequential doubly robust moment is jointly
measurable](goal). -/
lemma measurable_seqDRMomentFunctional_uncurry
    {Ω' : Type*} [MeasurableSpace Ω']
    (S : DTREstimationSystem P δ γ) (θ : ℝ)
    (η_fn : Ω' → DTRNuisanceVec₂ δ γ)
    (h_mu0 : Measurable (fun p : Ω' × γ 0 => (η_fn p.1).μ₀_fn p.2))
    (h_e0 : Measurable (fun p : Ω' × γ 0 => (η_fn p.1).e₀_fn p.2))
    (h_mu1 : Measurable (fun p : Ω' × (γ 1 × δ × γ 0) =>
      (η_fn p.1).μ₁_fn p.2))
    (h_e1 : Measurable (fun p : Ω' × (γ 1 × δ × γ 0) =>
      (η_fn p.1).e₁_fn p.2)) :
    Measurable (fun p : Ω' × (γ 0 × δ × γ 1 × δ × ℝ) =>
      S.seqDRMomentFunctional (η_fn p.1) p.2 θ) := by
  unfold DTREstimationSystem.seqDRMomentFunctional
  unfold Causalean.Estimation.DTR.seqDRMoment
  have hpS0 : Measurable (fun p : Ω' × (γ 0 × δ × γ 1 × δ × ℝ) =>
      (p.1, projS₀ p.2)) := by
    unfold projS₀
    exact Measurable.prodMk measurable_fst measurable_snd.fst
  have hpH1 : Measurable (fun p : Ω' × (γ 0 × δ × γ 1 × δ × ℝ) =>
      (p.1, histH₁ p.2)) := by
    unfold histH₁ projS₁ projD₀ projS₀
    measurability
  have hμ0 : Measurable (fun p : Ω' × (γ 0 × δ × γ 1 × δ × ℝ) =>
      (η_fn p.1).μ₀_fn (projS₀ p.2)) := h_mu0.comp hpS0
  have he0 : Measurable (fun p : Ω' × (γ 0 × δ × γ 1 × δ × ℝ) =>
      (η_fn p.1).e₀_fn (projS₀ p.2)) := h_e0.comp hpS0
  have hμ1 : Measurable (fun p : Ω' × (γ 0 × δ × γ 1 × δ × ℝ) =>
      (η_fn p.1).μ₁_fn (histH₁ p.2)) := h_mu1.comp hpH1
  have he1 : Measurable (fun p : Ω' × (γ 0 × δ × γ 1 × δ × ℝ) =>
      (η_fn p.1).e₁_fn (histH₁ p.2)) := h_e1.comp hpH1
  have hind0 : Measurable (fun p : Ω' × (γ 0 × δ × γ 1 × δ × ℝ) =>
      indEq (projD₀ p.2) (S.dbar 0)) := by
    unfold projD₀
    exact (measurable_indEq_left (S.dbar 0)).comp measurable_snd.snd.fst
  have hind1 : Measurable (fun p : Ω' × (γ 0 × δ × γ 1 × δ × ℝ) =>
      indEq (projD₁ p.2) (S.dbar 1)) := by
    unfold projD₁
    exact (measurable_indEq_left (S.dbar 1)).comp measurable_snd.snd.snd.snd.fst
  have hy : Measurable (fun p : Ω' × (γ 0 × δ × γ 1 × δ × ℝ) =>
      projY p.2) := by
    unfold projY
    exact measurable_snd.snd.snd.snd.snd
  exact ((hμ0.add ((hind0.div he0).mul (hμ1.sub hμ0))).add
    (((hind0.mul hind1).div (he0.mul he1)).mul (hy.sub hμ1))).sub measurable_const

/-- For [a potential-outcome system, treatment space, and two-stage covariate
spaces](hyp:P,δ,γ), [a dynamic-treatment-regime estimation system](hyp:S), [an overlap
level](hyp:ε), [strict overlap](hyp:h_overlap), [square-integrability of the factual
outcome](hyp:h_y2), [a nuisance specification](hyp:η), [its membership in the bounded
nuisance class](hyp:hη), and [square-integrability of its stage-zero and stage-one outcome
regressions](hyp:h_mu0,h_mu1), [the resulting sequential doubly robust moment at the target is
square-integrable under the observed-data law](goal). -/
lemma seqDRMomentFunctional_memLp_two
    (S : DTREstimationSystem P δ γ) {ε : ℝ}
    (h_overlap : S.StrictOverlap ε)
    (h_y2 : Integrable (fun ω => (S.toPOLongitudinalPathSystem.factualY ω) ^ 2) P.μ)
    (η : DTRNuisanceVec₂ δ γ)
    (hη : η ∈ DTREstimationSystem.H_ε ε)
    (h_mu0 : MemLp η.μ₀_fn 2 S.P_H₀)
    (h_mu1 : MemLp η.μ₁_fn 2 S.P_H₁) :
    MemLp (fun z => S.seqDRMomentFunctional η z S.θ₀) 2 S.P_Z := by
  have hY_L2 : MemLp S.toPOLongitudinalPathSystem.factualY 2 P.μ :=
    (memLp_two_iff_integrable_sq
      S.toPOLongitudinalPathSystem.measurable_factualY.aestronglyMeasurable).2 h_y2
  have hμ0_comp_L2 :
      MemLp (fun ω => η.μ₀_fn
        (S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω)) 2 P.μ := by
    have hmap : MemLp η.μ₀_fn 2
        (P.μ.map (S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩)) := by
      simpa [DTREstimationSystem.P_H₀] using h_mu0
    exact (memLp_map_measure_iff hmap.aestronglyMeasurable
      (S.toPOLongitudinalPathSystem.measurable_factualS ⟨0, by decide⟩).aemeasurable).1 hmap
  have hμ1_comp_L2 :
      MemLp (fun ω => η.μ₁_fn
        (S.toPOLongitudinalPathSystem.factualS ⟨1, by decide⟩ ω,
         S.toPOLongitudinalPathSystem.factualD ⟨0, by decide⟩ ω,
         S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω)) 2 P.μ := by
    let H1 : P.Ω → γ 1 × δ × γ 0 := fun ω =>
      (S.toPOLongitudinalPathSystem.factualS ⟨1, by decide⟩ ω,
       S.toPOLongitudinalPathSystem.factualD ⟨0, by decide⟩ ω,
       S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω)
    have hH1_meas : Measurable H1 := by
      dsimp [H1]
      exact (S.toPOLongitudinalPathSystem.measurable_factualS ⟨1, by decide⟩).prod
        ((S.toPOLongitudinalPathSystem.measurable_factualD ⟨0, by decide⟩).prod
          (S.toPOLongitudinalPathSystem.measurable_factualS ⟨0, by decide⟩))
    have hmap : MemLp η.μ₁_fn 2 (P.μ.map H1) := by
      simpa [DTREstimationSystem.P_H₁, H1] using h_mu1
    exact (memLp_map_measure_iff hmap.aestronglyMeasurable
      hH1_meas.aemeasurable).1 hmap
  have hw0_bound :
      ∀ᵐ ω ∂P.μ,
        ‖indEq (S.toPOLongitudinalPathSystem.factualD ⟨0, by decide⟩ ω)
            (S.dbar ⟨0, by decide⟩) /
          η.e₀_fn (S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω)‖ ≤ ε⁻¹ := by
    refine Eventually.of_forall fun ω => ?_
    have he := hη.1 (S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω)
    by_cases hD : S.toPOLongitudinalPathSystem.factualD ⟨0, by decide⟩ ω =
        S.dbar ⟨0, by decide⟩
    · have hpos : 0 < η.e₀_fn (S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω) :=
        lt_of_lt_of_le h_overlap.1 he.1
      have hle : (η.e₀_fn (S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω))⁻¹ ≤ ε⁻¹ :=
        (inv_le_inv₀ hpos h_overlap.1).2 he.1
      rw [indEq, if_pos hD, norm_div, norm_one, Real.norm_eq_abs, abs_of_pos hpos]
      simpa [one_div] using hle
    · have hεinv_nonneg : 0 ≤ ε⁻¹ := inv_nonneg.mpr h_overlap.1.le
      rw [indEq, if_neg hD, zero_div, norm_zero]
      exact hεinv_nonneg
  have hw1_bound :
      ∀ᵐ ω ∂P.μ,
        ‖(indEq (S.toPOLongitudinalPathSystem.factualD ⟨0, by decide⟩ ω)
              (S.dbar ⟨0, by decide⟩) *
            indEq (S.toPOLongitudinalPathSystem.factualD ⟨1, by decide⟩ ω)
              (S.dbar ⟨1, by decide⟩)) /
          (η.e₀_fn (S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω) *
            η.e₁_fn
              (S.toPOLongitudinalPathSystem.factualS ⟨1, by decide⟩ ω,
               S.toPOLongitudinalPathSystem.factualD ⟨0, by decide⟩ ω,
               S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω))‖ ≤ (ε * ε)⁻¹ := by
    refine Eventually.of_forall fun ω => ?_
    have he0 := hη.1 (S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω)
    have he1 := hη.2
      (S.toPOLongitudinalPathSystem.factualS ⟨1, by decide⟩ ω,
       S.toPOLongitudinalPathSystem.factualD ⟨0, by decide⟩ ω,
       S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω)
    by_cases hD0 : S.toPOLongitudinalPathSystem.factualD ⟨0, by decide⟩ ω =
        S.dbar ⟨0, by decide⟩
    · by_cases hD1 : S.toPOLongitudinalPathSystem.factualD ⟨1, by decide⟩ ω =
          S.dbar ⟨1, by decide⟩
      · have hpos0 : 0 < η.e₀_fn (S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω) :=
          lt_of_lt_of_le h_overlap.1 he0.1
        have hpos1 : 0 < η.e₁_fn
            (S.toPOLongitudinalPathSystem.factualS ⟨1, by decide⟩ ω,
             S.toPOLongitudinalPathSystem.factualD ⟨0, by decide⟩ ω,
             S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω) :=
          lt_of_lt_of_le h_overlap.1 he1.1
        have hle0 : (η.e₀_fn
            (S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω))⁻¹ ≤ ε⁻¹ :=
          (inv_le_inv₀ hpos0 h_overlap.1).2 he0.1
        have hle1 : (η.e₁_fn
            (S.toPOLongitudinalPathSystem.factualS ⟨1, by decide⟩ ω,
             S.toPOLongitudinalPathSystem.factualD ⟨0, by decide⟩ ω,
             S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω))⁻¹ ≤ ε⁻¹ :=
          (inv_le_inv₀ hpos1 h_overlap.1).2 he1.1
        have hle :
            (η.e₁_fn
              (S.toPOLongitudinalPathSystem.factualS ⟨1, by decide⟩ ω,
               S.toPOLongitudinalPathSystem.factualD ⟨0, by decide⟩ ω,
               S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω))⁻¹ *
              (η.e₀_fn (S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω))⁻¹
              ≤ ε⁻¹ * ε⁻¹ :=
          mul_le_mul hle1 hle0 (inv_nonneg.mpr hpos0.le)
            (inv_nonneg.mpr h_overlap.1.le)
        have hind0eq : indEq (S.toPOLongitudinalPathSystem.factualD ⟨0, by decide⟩ ω)
            (S.dbar ⟨0, by decide⟩) = 1 := by
          unfold indEq
          rw [if_pos]
          simpa using hD0
        have hind1eq : indEq (S.toPOLongitudinalPathSystem.factualD ⟨1, by decide⟩ ω)
            (S.dbar ⟨1, by decide⟩) = 1 := by
          unfold indEq
          rw [if_pos]
          simpa using hD1
        rw [hind0eq, hind1eq, one_mul, norm_div, norm_one, norm_mul]
        rw [show ‖η.e₀_fn (S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω)‖ =
            η.e₀_fn (S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω) from
          Real.norm_of_nonneg hpos0.le]
        rw [show ‖η.e₁_fn
            (S.toPOLongitudinalPathSystem.factualS ⟨1, by decide⟩ ω,
             S.toPOLongitudinalPathSystem.factualD ⟨0, by decide⟩ ω,
             S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω)‖ =
            η.e₁_fn
              (S.toPOLongitudinalPathSystem.factualS ⟨1, by decide⟩ ω,
               S.toPOLongitudinalPathSystem.factualD ⟨0, by decide⟩ ω,
               S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω) from
          Real.norm_of_nonneg hpos1.le]
        simpa [one_div, mul_comm, mul_left_comm, mul_assoc] using hle
      · have hεεinv_nonneg : 0 ≤ (ε * ε)⁻¹ :=
          inv_nonneg.mpr (mul_nonneg h_overlap.1.le h_overlap.1.le)
        have hind1zero : indEq (S.toPOLongitudinalPathSystem.factualD ⟨1, by decide⟩ ω)
            (S.dbar ⟨1, by decide⟩) = 0 := by
          unfold indEq
          rw [if_neg]
          simpa using hD1
        rw [hind1zero, mul_zero, zero_div, norm_zero]
        exact hεεinv_nonneg
    · have hεεinv_nonneg : 0 ≤ (ε * ε)⁻¹ :=
        inv_nonneg.mpr (mul_nonneg h_overlap.1.le h_overlap.1.le)
      have hind0zero : indEq (S.toPOLongitudinalPathSystem.factualD ⟨0, by decide⟩ ω)
          (S.dbar ⟨0, by decide⟩) = 0 := by
        unfold indEq
        rw [if_neg]
        simpa using hD0
      rw [hind0zero, zero_mul, zero_div, norm_zero]
      exact hεεinv_nonneg
  have hw0_Linf :
      MemLp
        (fun ω => indEq (S.toPOLongitudinalPathSystem.factualD ⟨0, by decide⟩ ω)
            (S.dbar ⟨0, by decide⟩) /
          η.e₀_fn (S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω)) ⊤ P.μ := by
    refine MemLp.of_bound ?_ ε⁻¹ hw0_bound
    apply Measurable.aestronglyMeasurable
    exact ((measurable_indEq_left (S.dbar ⟨0, by decide⟩)).comp
      (S.toPOLongitudinalPathSystem.measurable_factualD ⟨0, by decide⟩)).div
        (η.e₀_meas.comp (S.toPOLongitudinalPathSystem.measurable_factualS ⟨0, by decide⟩))
  have hw1_Linf :
      MemLp
        (fun ω =>
          (indEq (S.toPOLongitudinalPathSystem.factualD ⟨0, by decide⟩ ω)
              (S.dbar ⟨0, by decide⟩) *
            indEq (S.toPOLongitudinalPathSystem.factualD ⟨1, by decide⟩ ω)
              (S.dbar ⟨1, by decide⟩)) /
          (η.e₀_fn (S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω) *
            η.e₁_fn
              (S.toPOLongitudinalPathSystem.factualS ⟨1, by decide⟩ ω,
               S.toPOLongitudinalPathSystem.factualD ⟨0, by decide⟩ ω,
               S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω))) ⊤ P.μ := by
    refine MemLp.of_bound ?_ (ε * ε)⁻¹ hw1_bound
    apply Measurable.aestronglyMeasurable
    have hind0 : Measurable (fun ω => indEq
        (S.toPOLongitudinalPathSystem.factualD ⟨0, by decide⟩ ω)
        (S.dbar ⟨0, by decide⟩)) :=
      (measurable_indEq_left (S.dbar ⟨0, by decide⟩)).comp
        (S.toPOLongitudinalPathSystem.measurable_factualD ⟨0, by decide⟩)
    have hind1 : Measurable (fun ω => indEq
        (S.toPOLongitudinalPathSystem.factualD ⟨1, by decide⟩ ω)
        (S.dbar ⟨1, by decide⟩)) :=
      (measurable_indEq_left (S.dbar ⟨1, by decide⟩)).comp
        (S.toPOLongitudinalPathSystem.measurable_factualD ⟨1, by decide⟩)
    have he0 : Measurable (fun ω =>
        η.e₀_fn (S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω)) :=
      η.e₀_meas.comp (S.toPOLongitudinalPathSystem.measurable_factualS ⟨0, by decide⟩)
    have he1 : Measurable (fun ω =>
        η.e₁_fn
          (S.toPOLongitudinalPathSystem.factualS ⟨1, by decide⟩ ω,
           S.toPOLongitudinalPathSystem.factualD ⟨0, by decide⟩ ω,
           S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω)) :=
      η.e₁_meas.comp
        ((S.toPOLongitudinalPathSystem.measurable_factualS ⟨1, by decide⟩).prod
          ((S.toPOLongitudinalPathSystem.measurable_factualD ⟨0, by decide⟩).prod
            (S.toPOLongitudinalPathSystem.measurable_factualS ⟨0, by decide⟩)))
    exact (hind0.mul hind1).div (he0.mul he1)
  have hterm0_L2 :
      MemLp
        (fun ω =>
          (indEq (S.toPOLongitudinalPathSystem.factualD ⟨0, by decide⟩ ω)
              (S.dbar ⟨0, by decide⟩) /
            η.e₀_fn (S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω)) *
          (η.μ₁_fn
            (S.toPOLongitudinalPathSystem.factualS ⟨1, by decide⟩ ω,
             S.toPOLongitudinalPathSystem.factualD ⟨0, by decide⟩ ω,
             S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω) -
            η.μ₀_fn (S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω))) 2 P.μ :=
    (hμ1_comp_L2.sub hμ0_comp_L2).mul hw0_Linf
  have hterm1_L2 :
      MemLp
        (fun ω =>
          ((indEq (S.toPOLongitudinalPathSystem.factualD ⟨0, by decide⟩ ω)
              (S.dbar ⟨0, by decide⟩) *
            indEq (S.toPOLongitudinalPathSystem.factualD ⟨1, by decide⟩ ω)
              (S.dbar ⟨1, by decide⟩)) /
            (η.e₀_fn (S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω) *
              η.e₁_fn
                (S.toPOLongitudinalPathSystem.factualS ⟨1, by decide⟩ ω,
                 S.toPOLongitudinalPathSystem.factualD ⟨0, by decide⟩ ω,
                 S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω))) *
          (S.toPOLongitudinalPathSystem.factualY ω -
            η.μ₁_fn
              (S.toPOLongitudinalPathSystem.factualS ⟨1, by decide⟩ ω,
               S.toPOLongitudinalPathSystem.factualD ⟨0, by decide⟩ ω,
               S.toPOLongitudinalPathSystem.factualS ⟨0, by decide⟩ ω))) 2 P.μ :=
    (hY_L2.sub hμ1_comp_L2).mul hw1_Linf
  have hscore_comp_L2 :
      MemLp (fun ω => S.seqDRMomentFunctional η (S.factualZ ω) S.θ₀) 2 P.μ := by
    have hconst_L2 : MemLp (fun _ : P.Ω => S.θ₀) 2 P.μ := memLp_const _
    have hsum_L2 :=
      ((hμ0_comp_L2.add hterm0_L2).add hterm1_L2).sub hconst_L2
    exact hsum_L2
  have hscore_meas :
      Measurable (fun z : γ 0 × δ × γ 1 × δ × ℝ =>
        S.seqDRMomentFunctional η z S.θ₀) :=
    S.measurable_seqDRMomentFunctional η S.θ₀
  rw [DTREstimationSystem.P_Z]
  exact (memLp_map_measure_iff hscore_meas.aestronglyMeasurable
    S.measurable_factualZ.aemeasurable).2 hscore_comp_L2

/-- For [a potential-outcome system whose sample space is standard Borel and whose
measure is finite](hyp:P) with [a measurable treatment space in which every
singleton is measurable](hyp:δ) and [measurable stage-specific covariate spaces](hyp:γ),
[a two-stage dynamic treatment-regime estimation system](hyp:S), [an independent identically distributed
sample whose observations comprise baseline covariates, first treatment, intermediate
covariates, second treatment, and outcome](hyp:sample), [a one-shot sample split](hyp:split),
[a sequence of stagewise nuisance-function estimates indexed by sample size and the
underlying random outcome](hyp:η_hat), and [a sample-size index](hyp:n), the [one-shot
double-machine-learning sequentially doubly robust estimator](goal) is the function of
the underlying random outcome that averages, over the split's estimation fold, the
sequential doubly robust moment at the target treatment regime, using the nuisance
estimate at that sample size and target value zero.

One-shot DML / sequential DR estimator of the DTR effect
(`def:est-dml-dtr`).

Inputs:
* `S`         — DTR estimation system carrying the value-space truth
                `(μ₀_val, e₀_val, μ₁_val, e₁_val)` at the target regime
                `S.dbar`.
* `sample`    — i.i.d. sample of data tuples `(S₀, D₀, S₁, D₁, Y) ∼ P_Z`.
* `split`     — one-shot split of the sample.
* `η_hat`     — bundled stagewise nuisance estimator at horizon `n`.

Output: empirical mean over `B(n)` of `m_seqDR(S.dbar, Zᵢ, η̂(n), 0)`.
Equivalently, the empirical sequential-DR pseudo-outcome.

The estimator takes a single bundled `DTRNuisanceVec₂` process.  The theorem
`dml_DTR_isAsymLinear` constructs this bundle from the four stagewise learners
`μ₀_hat`, `e₀_hat`, `μ₁_hat`, and `e₁_hat`. -/
noncomputable def dml_DTR_estimator
    (S : DTREstimationSystem P δ γ)
    (sample : IIDSample P.Ω (γ 0 × δ × γ 1 × δ × ℝ) P.μ S.P_Z)
    (split : OneShotSplit sample)
    (η_hat : ℕ → P.Ω → DTRNuisanceVec₂ δ γ)
    (n : ℕ) : P.Ω → ℝ :=
  fun ω =>
    ((split.foldB n).card : ℝ)⁻¹ *
      ∑ i ∈ split.foldB n,
        Causalean.Estimation.DTR.seqDRMoment S.dbar (sample.Z i ω) (η_hat n ω) 0

end DTR
end Estimation
end Causalean
