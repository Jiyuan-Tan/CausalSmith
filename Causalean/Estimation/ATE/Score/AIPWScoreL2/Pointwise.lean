/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Estimation.ATE.Score.AIPWMoment
public import Causalean.Stat.Limit.Convergence
public import Causalean.Stat.Limit.StochasticOrderEnvelope
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
Establishes the pointwise algebra behind AIPW score continuity. It defines the
overlap envelope `K_AIPW` and proves `aipw_score_diff_pointwise_bound`, which
controls the score difference by outcome-regression errors and a
residual-weighted propensity error. Integration and stochastic truncation are
handled by the subsequent files.
-/

@[expose] public section
namespace Causalean
namespace Estimation
namespace ATE

open MeasureTheory ProbabilityTheory Filter Topology Causalean.PO Causalean.Stat

namespace BackdoorEstimationSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
/-! ## Almost-everywhere Lipschitz bound on `m_AIPW(·, z, θ₀)` for `H_ε_aeL2` -/

/-- For [a real number](hyp:ε), the [AIPW Lipschitz constant](goal) is $1+2/ε+2/ε^2$.

It tracks the quadratic blow-up of the inverse weights `1/ê`, `1/(1−ê)` and the cross terms `(ê − e)/(ê·e)`. -/
noncomputable def K_AIPW (ε : ℝ) : ℝ := 1 + 2 / ε + 2 / ε ^ 2

/-- For [a strictly positive overlap margin](hyp:ε,hε), [the associated augmented inverse-probability
weighting constant is at least one](goal). -/
lemma K_AIPW_one_le {ε : ℝ} (hε : 0 < ε) :
    1 ≤ K_AIPW ε := by
  unfold K_AIPW
  field_simp [hε.ne']
  nlinarith [sq_nonneg ε]

private lemma K_AIPW_mu_le {ε : ℝ} (hε : 0 < ε) :
    1 + 1 / ε ≤ K_AIPW ε := by
  unfold K_AIPW
  field_simp [hε.ne']
  nlinarith [sq_nonneg ε]

private lemma K_AIPW_inv_sq_le {ε : ℝ} (hε : 0 < ε) :
    1 / ε ^ 2 ≤ K_AIPW ε := by
  unfold K_AIPW
  field_simp [hε.ne']
  nlinarith [sq_nonneg ε]

private lemma abs_div_sub_div_le
    {ε e ê y μ μhat : ℝ} (hε : 0 < ε) (he : ε ≤ e) (hê : ε ≤ ê) :
    |(y - μhat) / ê - (y - μ) / e| ≤
      |μhat - μ| / ε + |y - μ| * |ê - e| / ε ^ 2 := by
  have he_pos : 0 < e := lt_of_lt_of_le hε he
  have hê_pos : 0 < ê := lt_of_lt_of_le hε hê
  have he_ne : e ≠ 0 := he_pos.ne'
  have hê_ne : ê ≠ 0 := hê_pos.ne'
  have hεsq_pos : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hprod_pos : 0 < ê * e := mul_pos hê_pos he_pos
  have hmul : ε ^ 2 ≤ ê * e := by
    nlinarith [mul_le_mul hê he hε.le hê_pos.le]
  have hid : (y - μhat) / ê - (y - μ) / e =
      - (μhat - μ) / ê - (y - μ) * (ê - e) / (ê * e) := by
    field_simp [hê_ne, he_ne]
    ring
  rw [hid]
  have htermA : |-(μhat - μ) / ê| = |μhat - μ| / ê := by
    rw [abs_div, abs_neg, abs_of_pos hê_pos]
  have htermB : |(y - μ) * (ê - e) / (ê * e)| =
      |y - μ| * |ê - e| / (ê * e) := by
    rw [abs_div, abs_mul, abs_of_pos hprod_pos]
  calc
    |- (μhat - μ) / ê - (y - μ) * (ê - e) / (ê * e)|
        ≤ |-(μhat - μ) / ê| + |(y - μ) * (ê - e) / (ê * e)| := abs_sub _ _
    _ = |μhat - μ| / ê + |y - μ| * |ê - e| / (ê * e) := by
      rw [htermA, htermB]
    _ ≤ |μhat - μ| / ε + |y - μ| * |ê - e| / ε ^ 2 := by
      have hterm1 : |μhat - μ| / ê ≤ |μhat - μ| / ε := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left ((inv_le_inv₀ hê_pos hε).2 hê) (abs_nonneg _)
      have hterm2 : |y - μ| * |ê - e| / (ê * e) ≤
          |y - μ| * |ê - e| / ε ^ 2 := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left ((inv_le_inv₀ hprod_pos hεsq_pos).2 hmul)
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      exact add_le_add hterm1 hterm2

private lemma aipw_real_bound
    {ε e ê μT μF μhT μhF y θ : ℝ} {a : Bool}
    (hε : 0 < ε) (he : ε ≤ e ∧ e ≤ 1 - ε) (hê : ε ≤ ê ∧ ê ≤ 1 - ε) :
    |((μhT - μhF) + ((if a = true then 1 else 0) / ê) * (y - μhT)
        - ((1 - (if a = true then 1 else 0)) / (1 - ê)) * (y - μhF) - θ)
      - ((μT - μF) + ((if a = true then 1 else 0) / e) * (y - μT)
        - ((1 - (if a = true then 1 else 0)) / (1 - e)) * (y - μF) - θ)|
      ≤ K_AIPW ε *
          (|μhT - μT| + |μhF - μF| + (|y - μT| + |y - μF|) * |ê - e|) := by
  have hK1 : 1 ≤ K_AIPW ε := K_AIPW_one_le hε
  have hKμ : 1 + 1 / ε ≤ K_AIPW ε := K_AIPW_mu_le hε
  have hKe : 1 / ε ^ 2 ≤ K_AIPW ε := K_AIPW_inv_sq_le hε
  have hKnonneg : 0 ≤ K_AIPW ε := le_trans zero_le_one hK1
  set dT : ℝ := |μhT - μT|
  set dF : ℝ := |μhF - μF|
  set rT : ℝ := |y - μT|
  set rF : ℝ := |y - μF|
  set de : ℝ := |ê - e|
  have hdT : 0 ≤ dT := by simp [dT]
  have hdF : 0 ≤ dF := by simp [dF]
  have hrT : 0 ≤ rT := by simp [rT]
  have hrF : 0 ≤ rF := by simp [rF]
  have hde : 0 ≤ de := by simp [de]
  have hcrossT : rT * de ≤ (rT + rF) * de := by nlinarith
  have hcrossF : rF * de ≤ (rT + rF) * de := by nlinarith
  have hTcoef : (1 + 1 / ε) * dT ≤ K_AIPW ε * dT :=
    mul_le_mul_of_nonneg_right hKμ hdT
  have hFcoef : (1 + 1 / ε) * dF ≤ K_AIPW ε * dF :=
    mul_le_mul_of_nonneg_right hKμ hdF
  have hTone : dT ≤ K_AIPW ε * dT := by
    simpa using mul_le_mul_of_nonneg_right hK1 hdT
  have hFone : dF ≤ K_AIPW ε * dF := by
    simpa using mul_le_mul_of_nonneg_right hK1 hdF
  have hCrossT : rT * de / ε ^ 2 ≤ K_AIPW ε * ((rT + rF) * de) := by
    calc
      rT * de / ε ^ 2 = (1 / ε ^ 2) * (rT * de) := by ring
      _ ≤ K_AIPW ε * (rT * de) :=
        mul_le_mul_of_nonneg_right hKe (mul_nonneg hrT hde)
      _ ≤ K_AIPW ε * ((rT + rF) * de) :=
        mul_le_mul_of_nonneg_left hcrossT hKnonneg
  have hCrossF : rF * de / ε ^ 2 ≤ K_AIPW ε * ((rT + rF) * de) := by
    calc
      rF * de / ε ^ 2 = (1 / ε ^ 2) * (rF * de) := by ring
      _ ≤ K_AIPW ε * (rF * de) :=
        mul_le_mul_of_nonneg_right hKe (mul_nonneg hrF hde)
      _ ≤ K_AIPW ε * ((rT + rF) * de) :=
        mul_le_mul_of_nonneg_left hcrossF hKnonneg
  cases a
  · have hden_e : ε ≤ 1 - e := by linarith [he.2]
    have hden_ê : ε ≤ 1 - ê := by linarith [hê.2]
    have hrat := abs_div_sub_div_le (e := 1 - e) (ê := 1 - ê)
      (y := y) (μ := μF) (μhat := μhF) hε hden_e hden_ê
    have hrat' : |(y - μhF) / (1 - ê) - (y - μF) / (1 - e)| ≤
        dF / ε + rF * de / ε ^ 2 := by
      have hde' : |e - ê| = de := by
        simpa [de] using abs_sub_comm e ê
      simpa [dF, rF, de, hde'] using hrat
    have hpre :
        |((μhT - μhF) + (0 / ê) * (y - μhT)
            - ((1 - 0) / (1 - ê)) * (y - μhF) - θ)
          - ((μT - μF) + (0 / e) * (y - μT)
            - ((1 - 0) / (1 - e)) * (y - μF) - θ)|
          ≤ dT + dF + (dF / ε + rF * de / ε ^ 2) := by
      have hsplit :
          (((μhT - μhF) + (0 / ê) * (y - μhT)
              - ((1 - 0) / (1 - ê)) * (y - μhF) - θ)
            - ((μT - μF) + (0 / e) * (y - μT)
              - ((1 - 0) / (1 - e)) * (y - μF) - θ)) =
            (μhT - μT) - (μhF - μF)
              - ((y - μhF) / (1 - ê) - (y - μF) / (1 - e)) := by
        ring
      rw [hsplit]
      calc
        |(μhT - μT) - (μhF - μF)
            - ((y - μhF) / (1 - ê) - (y - μF) / (1 - e))|
            ≤ |(μhT - μT) - (μhF - μF)|
                + |(y - μhF) / (1 - ê) - (y - μF) / (1 - e)| := abs_sub _ _
        _ ≤ dT + dF + (dF / ε + rF * de / ε ^ 2) := by
          have hbase : |(μhT - μT) - (μhF - μF)| ≤ dT + dF := by
            simpa [dT, dF] using abs_sub (μhT - μT) (μhF - μF)
          nlinarith
    have htarget : dT + dF + (dF / ε + rF * de / ε ^ 2) ≤
        K_AIPW ε * (dT + dF + (rT + rF) * de) := by
      have hdFdiv : dF / ε = (1 / ε) * dF := by ring
      calc
        dT + dF + (dF / ε + rF * de / ε ^ 2)
            = dT + (1 + 1 / ε) * dF + rF * de / ε ^ 2 := by
              rw [hdFdiv]
              ring
        _ ≤ K_AIPW ε * dT + K_AIPW ε * dF +
              K_AIPW ε * ((rT + rF) * de) := by
              nlinarith
        _ = K_AIPW ε * (dT + dF + (rT + rF) * de) := by ring
    simpa [dT, dF, rT, rF, de] using le_trans hpre htarget
  · have hrat := abs_div_sub_div_le (e := e) (ê := ê)
      (y := y) (μ := μT) (μhat := μhT) hε he.1 hê.1
    have hrat' : |(y - μhT) / ê - (y - μT) / e| ≤
        dT / ε + rT * de / ε ^ 2 := by
      simpa [dT, rT, de] using hrat
    have hpre :
        |((μhT - μhF) + (1 / ê) * (y - μhT)
            - ((1 - 1) / (1 - ê)) * (y - μhF) - θ)
          - ((μT - μF) + (1 / e) * (y - μT)
            - ((1 - 1) / (1 - e)) * (y - μF) - θ)|
          ≤ dT + dF + (dT / ε + rT * de / ε ^ 2) := by
      have hsplit :
          (((μhT - μhF) + (1 / ê) * (y - μhT)
              - ((1 - 1) / (1 - ê)) * (y - μhF) - θ)
            - ((μT - μF) + (1 / e) * (y - μT)
              - ((1 - 1) / (1 - e)) * (y - μF) - θ)) =
            (μhT - μT) - (μhF - μF)
              + ((y - μhT) / ê - (y - μT) / e) := by
        ring
      rw [hsplit]
      calc
        |(μhT - μT) - (μhF - μF)
            + ((y - μhT) / ê - (y - μT) / e)|
            ≤ |(μhT - μT) - (μhF - μF)|
                + |(y - μhT) / ê - (y - μT) / e| := abs_add_le _ _
        _ ≤ dT + dF + (dT / ε + rT * de / ε ^ 2) := by
          have hbase : |(μhT - μT) - (μhF - μF)| ≤ dT + dF := by
            simpa [dT, dF] using abs_sub (μhT - μT) (μhF - μF)
          nlinarith
    have htarget : dT + dF + (dT / ε + rT * de / ε ^ 2) ≤
        K_AIPW ε * (dT + dF + (rT + rF) * de) := by
      have hdTdiv : dT / ε = (1 / ε) * dT := by ring
      calc
        dT + dF + (dT / ε + rT * de / ε ^ 2)
            = (1 + 1 / ε) * dT + dF + rT * de / ε ^ 2 := by
              rw [hdTdiv]
              ring
        _ ≤ K_AIPW ε * dT + K_AIPW ε * dF +
              K_AIPW ε * ((rT + rF) * de) := by
              nlinarith
        _ = K_AIPW ε * (dT + dF + (rT + rF) * de) := by ring
    simpa [dT, dF, rT, rF, de] using le_trans hpre htarget

/-- For [a potential-outcome system and covariate space](hyp:P,γ), [a back-door estimation
system](hyp:S), [an overlap level](hyp:ε), [strict overlap](hyp:h_overlap), [a candidate
nuisance specification](hyp:η), and [its membership in the overlap-restricted nuisance
class](hyp:hη), [the absolute augmented inverse-probability score error is almost surely
bounded by the overlap Lipschitz constant times the two outcome-regression errors plus the
outcome-residual envelope times the propensity error](goal).

**AIPW score Lipschitz bound for `H_ε_aeL2`, `P_Z`-a.e.**

For any `η ∈ H_ε_aeL2 S ε`, the AIPW moment difference satisfies, for
`P_Z`-a.e. `z`,

    |m_AIPW(η, z, θ₀) − m_AIPW(η₀, z, θ₀)|
      ≤ K_AIPW(ε) · (|Δμ(1, x)| + |Δμ(0, x)|
        + (|y − μ_val(1, x)| + |y − μ_val(0, x)|) · |Δe(x)|).

The "a.e." quantifier is needed because both overlap facts are almost
everywhere: `S.StrictOverlap ε` supplies the true-propensity bound under
`P.μ`, while `H_ε_aeL2 S ε` supplies the learner bound under `P_X`.
Transporting both facts to `P_Z` gives the full-measure set on which the
algebraic Lipschitz step applies.

Proof: expand `m_AIPW`, apply triangle inequality, and use the standard
algebraic identity
    `a/u − a/v = a · (v − u) / (u · v)`
together with `1/u, 1/v ≤ 1/ε` and `1/(u · v) ≤ 1/ε²`. -/
theorem aipw_score_diff_pointwise_bound
    (S : BackdoorEstimationSystem P γ) {ε : ℝ}
    (h_overlap : S.StrictOverlap ε)
    (η : NuisanceVec γ) (hη : η ∈ H_ε_aeL2 S ε) :
    ∀ᵐ z ∂S.P_Z,
      |aipwMomentFunctional η z S.θ₀ - aipwMomentFunctional S.η₀ z S.θ₀|
        ≤ K_AIPW ε *
            (|η.μ_fn true (projX z) - S.μ_val true (projX z)|
              + |η.μ_fn false (projX z) - S.μ_val false (projX z)|
              + (|projY z - S.μ_val true (projX z)|
                  + |projY z - S.μ_val false (projX z)|)
                * |η.e_fn (projX z) - S.e_val (projX z)|) := by
  rcases h_overlap with ⟨hε_pos, _hε_half, hprop⟩
  have h_e_ω : ∀ᵐ ω ∂P.μ,
      ε ≤ S.e_val (S.toPOBackdoorSystem.factualX ω) ∧
        S.e_val (S.toPOBackdoorSystem.factualX ω) ≤ 1 - ε := by
    filter_upwards [hprop, S.e_compat] with ω hω hcompat
    rw [hcompat] at hω
    exact hω
  have h_e_z : ∀ᵐ z ∂S.P_Z,
      ε ≤ S.e_val (projX z) ∧ S.e_val (projX z) ≤ 1 - ε := by
    have hset : MeasurableSet
        {z : γ × Bool × ℝ | ε ≤ S.e_val (projX z) ∧
          S.e_val (projX z) ≤ 1 - ε} := by
      have hx : Measurable (fun z : γ × Bool × ℝ => projX z) := by
        simpa [projX] using
          (measurable_fst : Measurable (fun z : γ × Bool × ℝ => z.1))
      exact measurableSet_Icc.preimage (S.e_meas.comp hx)
    unfold BackdoorEstimationSystem.P_Z
    rw [MeasureTheory.ae_map_iff S.measurable_factualZ.aemeasurable hset]
    filter_upwards [h_e_ω] with ω hω
    simpa [BackdoorEstimationSystem.factualZ, projX] using hω
  have hη_z : ∀ᵐ z ∂S.P_Z,
      ε ≤ η.e_fn (projX z) ∧ η.e_fn (projX z) ≤ 1 - ε :=
    H_ε_aeL2_overlap_P_Z S hη
  filter_upwards [h_e_z, hη_z] with z hz hηz
  simpa [aipwMomentFunctional, aipwMoment, η₀, indA] using
    (aipw_real_bound (a := projA z) (ε := ε)
      (e := S.e_val (projX z)) (ê := η.e_fn (projX z))
      (μT := S.μ_val true (projX z)) (μF := S.μ_val false (projX z))
      (μhT := η.μ_fn true (projX z)) (μhF := η.μ_fn false (projX z))
      (y := projY z) (θ := S.θ₀) hε_pos hz hηz)

end BackdoorEstimationSystem

end ATE
end Estimation
end Causalean
