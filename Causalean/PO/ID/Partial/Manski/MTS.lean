/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Manski bounds under MTS (prop:po-iv-mts)

Under consistency, bounded outcomes with `a ≤ b`, and MTS, the formalized MTS
bounds give

    p · E[Y|D=1] + (1-p)·a  ≤  E[Y(1)]  ≤  E[Y|D=1],
    E[Y|D=0]  ≤  E[Y(0)]  ≤  p·b + (1-p)·E[Y|D=0],

and by subtraction the two-sided ATE sandwich.

Here `p := (P.μ (dEvent true)).toReal`, and conditional means are
`normalizedRestrictedIntegral P.μ (dEvent d) (·)`. The file uses its zero-measure
convention; the MTS structure and bounds below do not assume strict
treatment-cell positivity.
-/

module

public import Causalean.Mathlib.Probability.FiniteCellConditionalMomentBridge
public import Causalean.PO.ID.Partial.Manski.Helpers

/-! # Manski bounds under monotone treatment selection

This file proves the monotone-treatment-selection version of the Manski bounds.
Under consistency and bounded outcomes, the monotone-treatment-selection
inequalities compare treatment-specific conditional means and yield a two-sided
ATE sandwich. The statements use the zero-measure convention of
`normalizedRestrictedIntegral` and do not require strict treated/control cell positivity.

The central public results are the binary total-law decomposition
`integral_YofD_eq_total_law`, the baseline bounded-outcome inequalities
`baseline_lower_le_E_Y1` and `baseline_E_Y0_le_upper`, the two MTS inequalities
`mts_E_Y1_le_condY1` and `mts_condY0_le_E_Y0`, and the final ATE sandwich
`mts_bounds_ATE`.
-/

public section

open Causalean.Mathlib.Probability

namespace Causalean
namespace PO

open MeasureTheory

namespace POManskiIVSystem

variable {P : POSystem} {α : Type*}
  [MeasurableSpace α] [MeasurableSingletonClass α]
  (S : POManskiIVSystem P α)

/-! ### Binary-event algebra for `dEvent` -/

/-- Complement of `{D = true}` is `{D = false}` (Bool case-split). -/
lemma compl_dEvent_true : (S.dEvent true)ᶜ = S.dEvent false := by
  ext ω
  simp only [Set.mem_compl_iff, dEvent, POVar.event, Set.mem_preimage,
    Set.mem_singleton_iff]
  cases S.factualD ω <;> simp

/-- Complement of `{D = false}` is `{D = true}` (Bool case-split). -/
lemma compl_dEvent_false : (S.dEvent false)ᶜ = S.dEvent true := by
  ext ω
  simp only [Set.mem_compl_iff, dEvent, POVar.event, Set.mem_preimage,
    Set.mem_singleton_iff]
  cases S.factualD ω <;> simp

/-- Probability split: `P(D=true).toReal + P(D=false).toReal = 1`. -/
lemma prob_dEvent_true_add_false :
    (P.μ (S.dEvent true)).toReal + (P.μ (S.dEvent false)).toReal = 1 := by
  have hmeas : MeasurableSet (S.dEvent true) := S.measurableSet_dEvent true
  have hcompl : (S.dEvent true)ᶜ = S.dEvent false := S.compl_dEvent_true
  have hadd : P.μ (S.dEvent true) + P.μ (S.dEvent false) = 1 := by
    rw [← hcompl]
    rw [MeasureTheory.measure_add_measure_compl hmeas]
    exact MeasureTheory.IsProbabilityMeasure.measure_univ
  have hfin1 : P.μ (S.dEvent true) ≠ ⊤ := measure_ne_top _ _
  have hfin2 : P.μ (S.dEvent false) ≠ ⊤ := measure_ne_top _ _
  have := congrArg ENNReal.toReal hadd
  rw [ENNReal.toReal_add hfin1 hfin2] at this
  simpa using this

/-! ### Bool-indexed total-law decomposition over the `D` partition

Specialisations of the generic `integral_eq_sum_measure_mul_eventCondExp`
(and `POVar.eventCondExp_cfUnder_eq_factual_on_event`) to the binary
`D`-partition.  Shared with `MTR.lean` through the same underlying lemmas. -/

/-- The two treatment events cover `P.Ω`. -/
private lemma iUnion_dEvent : (⋃ d, S.dEvent d) = Set.univ := by
  refine Set.eq_univ_of_forall (fun ω => ?_)
  exact Set.mem_iUnion.mpr ⟨S.factualD ω, rfl⟩

/-- The two treatment events are pairwise disjoint. -/
private lemma pairwise_disjoint_dEvent :
    Pairwise (Function.onFun Disjoint S.dEvent) := by
  rintro d₁ d₂ hne
  refine Set.disjoint_left.mpr (fun ω hω₁ hω₂ => ?_)
  have h₁ : S.factualD ω = d₁ := hω₁
  have h₂ : S.factualD ω = d₂ := hω₂
  exact hne (h₁.symm.trans h₂)

/-- Total-law decomposition for `YofD d` across the binary partition
`{D=true} ⊔ {D=false}`, via the generic `Fintype` total law. -/
theorem integral_YofD_eq_total_law (hA : S.BaseAssumptions) (d : Bool) :
    ∫ ω, S.YofD d ω ∂P.μ
      = (P.μ (S.dEvent true)).toReal
          * normalizedRestrictedIntegral P.μ (S.dEvent true) (S.YofD d)
        + (P.μ (S.dEvent false)).toReal
          * normalizedRestrictedIntegral P.μ (S.dEvent false) (S.YofD d) := by
  have hint : Integrable (S.YofD d) P.μ := by
    cases d
    · exact hA.integrable_Y0
    · exact hA.integrable_Y1
  have h := integral_eq_sum_measure_mul_eventCondExp (μ := P.μ)
    (A := S.dEvent) S.measurableSet_dEvent S.pairwise_disjoint_dEvent
    S.iUnion_dEvent (S.YofD d) hint
  simpa [Fintype.sum_bool] using h

/-! ### Consistency on event: `E[Y(d) | D=d] = E[Y | D=d]` -/

/-- Pointwise consistency on `{D = d}`: `YofD d = factualY` on this event. -/
lemma YofD_eq_factualY_on_dEvent (hA : S.BaseAssumptions) (d : Bool)
    {ω : P.Ω} (hω : ω ∈ S.dEvent d) :
    S.YofD d ω = S.factualY ω :=
  POVar.cf_eq_factual_on_event hA.consistency S.yVar S.dVar d (Ne.symm S.hDY) hω

/-- `E[Y(d) | D = d] = E[Y | D = d]` via consistency on the event. -/
lemma eventCondExp_YofD_eq_factualY (hA : S.BaseAssumptions) (d : Bool) :
    normalizedRestrictedIntegral P.μ (S.dEvent d) (S.YofD d)
      = normalizedRestrictedIntegral P.μ (S.dEvent d) S.factualY :=
  eventCondExp_congr_on P.μ (S.measurableSet_dEvent d) fun _ω hω =>
    POVar.cf_eq_factual_on_event hA.consistency S.yVar S.dVar d
      (Ne.symm S.hDY) hω

/-- `(μ A).toReal * normalizedRestrictedIntegral μ A (fun _ => c) = (μ A).toReal * c`.
Follows from `eventCondExp_mul_measure_toReal` with the constant integrand. -/
lemma measure_mul_eventCondExp_const (A : Set P.Ω) (c : ℝ) :
    (P.μ A).toReal * normalizedRestrictedIntegral P.μ A (fun _ : P.Ω => c)
      = (P.μ A).toReal * c := by
  rw [mul_comm, eventCondExp_mul_measure_toReal P.μ A (measure_ne_top _ _)]
  rw [MeasureTheory.setIntegral_const, smul_eq_mul,
    MeasureTheory.measureReal_def, mul_comm]

/-! ### MTS bounds -/

/-- **Baseline bounded-outcome lower bound on `E[Y(1)]`.** Under [the baseline Manski
assumptions](hyp:hA), [the inequality
`p · E[Y|D=1] + (1-p) · lo ≤ E[Y(1)]`](goal). -/
theorem baseline_lower_le_E_Y1 (hA : S.BaseAssumptions) :
    (P.μ (S.dEvent true)).toReal
        * normalizedRestrictedIntegral P.μ (S.dEvent true) S.factualY
      + (1 - (P.μ (S.dEvent true)).toReal) * hA.lo
    ≤ ∫ ω, S.YofD true ω ∂P.μ := by
  -- From boundedness: `a ≤ E[Y(1) | D=0]`.
  set p := (P.μ (S.dEvent true)).toReal with hp
  have hp_add : p + (P.μ (S.dEvent false)).toReal = 1 :=
    S.prob_dEvent_true_add_false
  have hq : (P.μ (S.dEvent false)).toReal = 1 - p := by linarith
  -- Total-law decomposition.
  have hTL := S.integral_YofD_eq_total_law hA true
  -- Bound `E[Y(1) | D=0] ≥ a` via `bounded_one` + `eventCondExp_mono_ae`.
  have hlo_ae : (fun _ : P.Ω => hA.lo) ≤ᵐ[P.μ] S.YofD true :=
    hA.bounded_one.mono (fun _ h => h.1)
  have hint_const : IntegrableOn (fun _ : P.Ω => hA.lo) (S.dEvent false) P.μ :=
    (integrable_const hA.lo).integrableOn
  have hint_Y1 : IntegrableOn (S.YofD true) (S.dEvent false) P.μ :=
    hA.integrable_Y1.integrableOn
  have hlo_cond :
      normalizedRestrictedIntegral P.μ (S.dEvent false) (fun _ => hA.lo)
        ≤ normalizedRestrictedIntegral P.μ (S.dEvent false) (S.YofD true) := by
    exact eventCondExp_mono_ae P.μ hint_const hint_Y1 (ae_restrict_of_ae hlo_ae)
  -- `normalizedRestrictedIntegral μ A (fun _ => c) = c` when `μ A ≠ 0`; else both sides are
  -- `0`.  In either case the inequality `c ≤ normalizedRestrictedIntegral μ A f` together
  -- with `(μ A).toReal * c ≤ (μ A).toReal * normalizedRestrictedIntegral μ A f` follows by
  -- multiplying by a nonneg scalar.
  have hq_nn : (0 : ℝ) ≤ (P.μ (S.dEvent false)).toReal :=
    ENNReal.toReal_nonneg
  -- Compute: (μ (dEvent false)).toReal * normalizedRestrictedIntegral ... (fun _ => a) =
  --   ∫ in dEvent false, a = (μ (dEvent false)).toReal * a.
  have heq_const :
      (P.μ (S.dEvent false)).toReal
        * normalizedRestrictedIntegral P.μ (S.dEvent false) (fun _ : P.Ω => hA.lo)
      = (P.μ (S.dEvent false)).toReal * hA.lo :=
    measure_mul_eventCondExp_const (P := P) (S.dEvent false) hA.lo
  -- Multiply both sides of hlo_cond by (μ (dEvent false)).toReal.
  have hmul :
      (P.μ (S.dEvent false)).toReal
        * normalizedRestrictedIntegral P.μ (S.dEvent false) (fun _ => hA.lo)
      ≤ (P.μ (S.dEvent false)).toReal
          * normalizedRestrictedIntegral P.μ (S.dEvent false) (S.YofD true) :=
    mul_le_mul_of_nonneg_left hlo_cond hq_nn
  rw [heq_const] at hmul
  -- Use consistency on `{D=1}`: normalizedRestrictedIntegral μ (dEvent true) (YofD true)
  -- = normalizedRestrictedIntegral μ (dEvent true) factualY.
  have hcons1 :=
    S.eventCondExp_YofD_eq_factualY hA true
  -- Combine.
  rw [hq] at hmul
  calc
    p * normalizedRestrictedIntegral P.μ (S.dEvent true) S.factualY + (1 - p) * hA.lo
        = p * normalizedRestrictedIntegral P.μ (S.dEvent true) (S.YofD true)
            + (1 - p) * hA.lo := by rw [hcons1]
    _ ≤ p * normalizedRestrictedIntegral P.μ (S.dEvent true) (S.YofD true)
          + (1 - p) * normalizedRestrictedIntegral P.μ (S.dEvent false) (S.YofD true) := by
          linarith
    _ = ∫ ω, S.YofD true ω ∂P.μ := by
          rw [hTL, hq]

/-- Under [the baseline Manski assumptions](hyp:hA) and [monotone treatment
selection with `0 < P(D=1) < 1`](hyp:hMTS), [the treated potential-outcome mean
is no larger than the observed treated-cell mean](goal). -/
theorem mts_E_Y1_le_condY1 (hA : S.BaseAssumptions) (hMTS : S.MTS) :
    ∫ ω, S.YofD true ω ∂P.μ
      ≤ normalizedRestrictedIntegral P.μ (S.dEvent true) S.factualY := by
  set p := (P.μ (S.dEvent true)).toReal with hp
  have hp_add : p + (P.μ (S.dEvent false)).toReal = 1 :=
    S.prob_dEvent_true_add_false
  have hq : (P.μ (S.dEvent false)).toReal = 1 - p := by linarith
  have hp_nn : (0 : ℝ) ≤ p := ENNReal.toReal_nonneg
  have hq_nn : (0 : ℝ) ≤ 1 - p := hq ▸ ENNReal.toReal_nonneg
  have hTL := S.integral_YofD_eq_total_law hA true
  -- MTS: E[Y(1)|D=0] ≤ E[Y(1)|D=1].
  have hmts := hMTS.mts_one true
  have hcons1 := S.eventCondExp_YofD_eq_factualY hA true
  -- Chain:
  --   ∫ YofD true = p · E[Y(1)|D=1] + (1-p) · E[Y(1)|D=0]
  --              ≤ p · E[Y(1)|D=1] + (1-p) · E[Y(1)|D=1]
  --               = E[Y(1)|D=1]
  --               = E[Y|D=1].
  calc
    ∫ ω, S.YofD true ω ∂P.μ
        = p * normalizedRestrictedIntegral P.μ (S.dEvent true) (S.YofD true)
          + (1 - p) * normalizedRestrictedIntegral P.μ (S.dEvent false) (S.YofD true) := by
            rw [hTL, hq]
    _ ≤ p * normalizedRestrictedIntegral P.μ (S.dEvent true) (S.YofD true)
          + (1 - p) * normalizedRestrictedIntegral P.μ (S.dEvent true) (S.YofD true) := by
            have := mul_le_mul_of_nonneg_left hmts hq_nn
            linarith
    _ = normalizedRestrictedIntegral P.μ (S.dEvent true) (S.YofD true) := by ring
    _ = normalizedRestrictedIntegral P.μ (S.dEvent true) S.factualY := hcons1

/-- Under [the baseline Manski assumptions](hyp:hA) and [monotone treatment
selection with `0 < P(D=1) < 1`](hyp:hMTS), [the observed control-cell mean is
no larger than the control potential-outcome mean](goal). -/
theorem mts_condY0_le_E_Y0 (hA : S.BaseAssumptions) (hMTS : S.MTS) :
    normalizedRestrictedIntegral P.μ (S.dEvent false) S.factualY
      ≤ ∫ ω, S.YofD false ω ∂P.μ := by
  set p := (P.μ (S.dEvent true)).toReal with hp
  have hp_add : p + (P.μ (S.dEvent false)).toReal = 1 :=
    S.prob_dEvent_true_add_false
  have hq : (P.μ (S.dEvent false)).toReal = 1 - p := by linarith
  have hp_nn : (0 : ℝ) ≤ p := ENNReal.toReal_nonneg
  have hq_nn : (0 : ℝ) ≤ 1 - p := hq ▸ ENNReal.toReal_nonneg
  have hTL := S.integral_YofD_eq_total_law hA false
  -- MTS on `d = 0`: E[Y(0)|D=0] ≤ E[Y(0)|D=1].
  have hmts := hMTS.mts_one false
  have hcons0 := S.eventCondExp_YofD_eq_factualY hA false
  calc
    normalizedRestrictedIntegral P.μ (S.dEvent false) S.factualY
        = normalizedRestrictedIntegral P.μ (S.dEvent false) (S.YofD false) := hcons0.symm
    _ = p * normalizedRestrictedIntegral P.μ (S.dEvent false) (S.YofD false)
          + (1 - p) * normalizedRestrictedIntegral P.μ (S.dEvent false) (S.YofD false) := by
            ring
    _ ≤ p * normalizedRestrictedIntegral P.μ (S.dEvent true) (S.YofD false)
          + (1 - p) * normalizedRestrictedIntegral P.μ (S.dEvent false) (S.YofD false) := by
            have := mul_le_mul_of_nonneg_left hmts hp_nn
            linarith
    _ = ∫ ω, S.YofD false ω ∂P.μ := by
            rw [hTL, hq]

/-- **Baseline bounded-outcome upper bound on `E[Y(0)]`.** Under [the baseline Manski
assumptions](hyp:hA), [the inequality
`E[Y(0)] ≤ p · hi + (1-p) · E[Y|D=0]`](goal). -/
theorem baseline_E_Y0_le_upper (hA : S.BaseAssumptions) :
    ∫ ω, S.YofD false ω ∂P.μ
      ≤ (P.μ (S.dEvent true)).toReal * hA.hi
        + (1 - (P.μ (S.dEvent true)).toReal)
          * normalizedRestrictedIntegral P.μ (S.dEvent false) S.factualY := by
  set p := (P.μ (S.dEvent true)).toReal with hp
  have hp_add : p + (P.μ (S.dEvent false)).toReal = 1 :=
    S.prob_dEvent_true_add_false
  have hq : (P.μ (S.dEvent false)).toReal = 1 - p := by linarith
  have hp_nn : (0 : ℝ) ≤ p := ENNReal.toReal_nonneg
  have hTL := S.integral_YofD_eq_total_law hA false
  -- Boundedness: Y(0) ≤ b a.s., hence E[Y(0)|D=1] ≤ b.
  have hhi_ae : S.YofD false ≤ᵐ[P.μ] (fun _ : P.Ω => hA.hi) :=
    hA.bounded_zero.mono (fun _ h => h.2)
  have hint_Y0 : IntegrableOn (S.YofD false) (S.dEvent true) P.μ :=
    hA.integrable_Y0.integrableOn
  have hint_const : IntegrableOn (fun _ : P.Ω => hA.hi) (S.dEvent true) P.μ :=
    (integrable_const hA.hi).integrableOn
  have hhi_cond :
      normalizedRestrictedIntegral P.μ (S.dEvent true) (S.YofD false)
        ≤ normalizedRestrictedIntegral P.μ (S.dEvent true) (fun _ => hA.hi) :=
    eventCondExp_mono_ae P.μ hint_Y0 hint_const (ae_restrict_of_ae hhi_ae)
  have heq_const :
      p * normalizedRestrictedIntegral P.μ (S.dEvent true) (fun _ : P.Ω => hA.hi)
      = p * hA.hi :=
    measure_mul_eventCondExp_const (P := P) (S.dEvent true) hA.hi
  have hmul :
      p * normalizedRestrictedIntegral P.μ (S.dEvent true) (S.YofD false)
        ≤ p * normalizedRestrictedIntegral P.μ (S.dEvent true) (fun _ => hA.hi) :=
    mul_le_mul_of_nonneg_left hhi_cond hp_nn
  rw [heq_const] at hmul
  have hcons0 := S.eventCondExp_YofD_eq_factualY hA false
  calc
    ∫ ω, S.YofD false ω ∂P.μ
        = p * normalizedRestrictedIntegral P.μ (S.dEvent true) (S.YofD false)
          + (1 - p) * normalizedRestrictedIntegral P.μ (S.dEvent false) (S.YofD false) := by
            rw [hTL, hq]
    _ ≤ p * hA.hi
          + (1 - p) * normalizedRestrictedIntegral P.μ (S.dEvent false) (S.YofD false) := by
            linarith
    _ = p * hA.hi
          + (1 - p) * normalizedRestrictedIntegral P.μ (S.dEvent false) S.factualY := by
            rw [hcons0]

/-! ### ATE sandwich -/

/-- **MTS bounds for the ATE.** Under [the baseline Manski assumptions](hyp:hA)
and [monotone treatment selection with `0 < P(D=1) < 1`](hyp:hMTS), [the
average treatment effect is sandwiched between a probability-weighted range
bound and the observed treated-control mean contrast](goal). -/
theorem mts_bounds_ATE (hA : S.BaseAssumptions) (hMTS : S.MTS) :
    (P.μ (S.dEvent true)).toReal
        * normalizedRestrictedIntegral P.μ (S.dEvent true) S.factualY
      + (1 - (P.μ (S.dEvent true)).toReal) * hA.lo
      - ((P.μ (S.dEvent true)).toReal * hA.hi
          + (1 - (P.μ (S.dEvent true)).toReal)
            * normalizedRestrictedIntegral P.μ (S.dEvent false) S.factualY)
    ≤ S.ATE
    ∧ S.ATE
      ≤ normalizedRestrictedIntegral P.μ (S.dEvent true) S.factualY
          - normalizedRestrictedIntegral P.μ (S.dEvent false) S.factualY := by
  have hATE_eq :
      S.ATE = ∫ ω, S.YofD true ω ∂P.μ - ∫ ω, S.YofD false ω ∂P.μ := by
    unfold ATE
    exact integral_sub hA.integrable_Y1 hA.integrable_Y0
  have h1L := S.baseline_lower_le_E_Y1 hA
  have h1U := S.mts_E_Y1_le_condY1 hA hMTS
  have h0L := S.mts_condY0_le_E_Y0 hA hMTS
  have h0U := S.baseline_E_Y0_le_upper hA
  refine ⟨?_, ?_⟩
  · rw [hATE_eq]; linarith
  · rw [hATE_eq]; linarith

end POManskiIVSystem

end PO
end Causalean
