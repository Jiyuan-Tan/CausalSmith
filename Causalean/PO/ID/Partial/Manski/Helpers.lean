/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Manski bounds: shared helper lemmas

Algebraic, measurability, integrability, and pointwise bound helpers
reused by all variants (NonAsp, MTR, MTS, MIV) plus normalized
restricted-integral (pre-mean-independence) stratum bounds

    L_{1,z} ≤ E[Y(1) | Z=z] and symmetric versions,

stated parametrically in `d : Bool` via `boundArm`.  Mean independence
is no longer consumed here.
-/

module

public import Causalean.Mathlib.Probability.FiniteCellConditionalMomentBridge
public import Causalean.PO.Conditioning.CondExpTooling
public import Causalean.PO.ID.Partial.Manski.Assumptions

/-! # Shared helpers for Manski-style bounds

This file collects algebraic, measurability, integrability, and pointwise bound
lemmas reused by the baseline Manski, monotone-treatment-response,
monotone-treatment-selection, and monotone-instrument variants. It also proves
parametric normalized restricted-integral bounds for each treatment arm. On a
null stratum these quantities use the library's zero convention rather than
representing ordinary conditional means.

The main public results are the arm-uniform bounds
`boundArm_lo_le_cond_YofD` and `cond_YofD_le_boundArm_hi`, together with the
legacy names `lowerBound1_le_cond_Y1`, `cond_Y1_le_upperBound1`,
`lowerBound0_le_cond_Y0`, and `cond_Y0_le_upperBound0` used by downstream
Manski theorem files.
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

/-! ### Integrability helpers -/

/-- `factualY · indicator d` is integrable. -/
lemma factualY_mul_indD_integrable (hA : S.BaseAssumptions) (d : Bool) :
    Integrable (fun ω => S.factualY ω * S.dVar.indicator d ω) P.μ := by
  exact S.dVar.integrable_mul_indicator d (measurableSet_singleton d) hA.integrable_factualY

/-- `YofD d · indicator d` is integrable. -/
lemma YofD_mul_indD_integrable (hA : S.BaseAssumptions) (d : Bool) :
    Integrable (fun ω => S.YofD d ω * S.dVar.indicator d ω) P.μ := by
  exact S.dVar.integrable_mul_indicator d (measurableSet_singleton d) (hA.integrable_YofD d)

/-- Constant times `indicator d` is integrable. -/
lemma const_mul_indD_integrable [IsFiniteMeasure P.μ] (c : ℝ) (d : Bool) :
    Integrable (fun ω => c * S.dVar.indicator d ω) P.μ :=
  (S.dVar.integrable_indicator d (measurableSet_singleton d)).const_mul c

/-! ### Pointwise a.e. bounds -/

/-- Helper: for binary `d`, `(d, !d)` indicators take opposite values. -/
private lemma dVar_inds_at_ω (d : Bool) (ω : P.Ω) :
    (S.dVar.indicator d ω = 1 ∧ S.dVar.indicator (!d) ω = 0) ∨
    (S.dVar.indicator d ω = 0 ∧ S.dVar.indicator (!d) ω = 1) := by
  by_cases hfd : S.dVar.factual ω = true
  · -- factual = true
    cases d
    · refine Or.inr ⟨?_, ?_⟩
      · exact S.dVar.indicator_apply_eq_zero (by rw [hfd]; decide)
      · exact S.dVar.indicator_apply_eq_one hfd
    · refine Or.inl ⟨?_, ?_⟩
      · exact S.dVar.indicator_apply_eq_one hfd
      · exact S.dVar.indicator_apply_eq_zero (by rw [hfd]; decide)
  · -- factual = false
    have hfd' : S.dVar.factual ω = false := by
      cases h : S.dVar.factual ω <;> simp_all
    cases d
    · refine Or.inl ⟨?_, ?_⟩
      · exact S.dVar.indicator_apply_eq_one hfd'
      · exact S.dVar.indicator_apply_eq_zero (by rw [hfd']; decide)
    · refine Or.inr ⟨?_, ?_⟩
      · exact S.dVar.indicator_apply_eq_zero (by rw [hfd']; decide)
      · exact S.dVar.indicator_apply_eq_one hfd'

/-- Pointwise a.e. bound: `Y(d) · 1_{D=d} + lo · 1_{D=!d} ≤ Y(d)` under
`lo ≤ Y(d)`. -/
lemma YofD_indD_plus_lo_le_YofD (d : Bool) (lo : ℝ)
    (hbound : ∀ᵐ ω ∂P.μ, lo ≤ S.YofD d ω) :
    (fun ω => S.YofD d ω * S.dVar.indicator d ω
                + lo * S.dVar.indicator (!d) ω)
      ≤ᵐ[P.μ] S.YofD d := by
  refine hbound.mono (fun ω hlo => ?_)
  rcases S.dVar_inds_at_ω d ω with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> simp [h₁, h₂, hlo]

/-- Pointwise a.e. bound: `Y(d) ≤ Y(d) · 1_{D=d} + hi · 1_{D=!d}` under
`Y(d) ≤ hi`. -/
lemma YofD_le_YofD_indD_plus_hi (d : Bool) (hi : ℝ)
    (hbound : ∀ᵐ ω ∂P.μ, S.YofD d ω ≤ hi) :
    S.YofD d ≤ᵐ[P.μ]
      (fun ω => S.YofD d ω * S.dVar.indicator d ω
                + hi * S.dVar.indicator (!d) ω) := by
  refine hbound.mono (fun ω hhi => ?_)
  rcases S.dVar_inds_at_ω d ω with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> simp [h₁, h₂, hhi]

/-! ### Normalized restricted-integral (pre-mean-independence) stratum bounds

Parametric forms on `d : Bool`.  The four legacy theorems
`lowerBound1_le_cond_Y1`, `cond_Y1_le_upperBound1`,
`lowerBound0_le_cond_Y0`, `cond_Y0_le_upperBound0` are retained below as
one-line corollaries so downstream files (`NonAsp`, `MTR`, `MTS`, `MIV`,
`Combined`) keep working unchanged. -/

/-- Under [the baseline Manski assumptions](hyp:hA), for [a treatment arm](hyp:d)
and [a singleton instrument stratum](hyp:z), [the normalized restricted integral
is bounded below by the unified lower-envelope functional](goal).

On a null stratum the normalized restricted integral is defined to be zero; it
has conditional-mean semantics only on positive-mass strata. -/
theorem boundArm_lo_le_cond_YofD [IsFiniteMeasure P.μ]
    (hA : S.BaseAssumptions) (d : Bool) {z : α} :
    S.boundArm d hA.lo z ≤ normalizedRestrictedIntegral P.μ (S.zEvent z) (S.YofD d) := by
  -- Rewrite `factualY · 1_{D=d}` as `Y(d) · 1_{D=d}` using consistency.
  have hcons : (fun ω => S.factualY ω * S.dVar.indicator d ω
                          + hA.lo * S.dVar.indicator (!d) ω)
              = (fun ω => S.YofD d ω * S.dVar.indicator d ω
                            + hA.lo * S.dVar.indicator (!d) ω) := by
    funext ω
    have hvw : S.yVar.v ≠ S.dVar.v := Ne.symm S.hDY
    have h := congr_fun (POVar.factual_mul_indicator_eq_cfUnder_mul_indicator_fn
      hA.consistency S.yVar S.dVar d hvw) ω
    rw [show S.factualY ω * S.dVar.indicator d ω = S.YofD d ω * S.dVar.indicator d ω from by
      simpa [POManskiIVSystem.factualY, POManskiIVSystem.YofD] using h]
  have hbound_ae :=
    S.YofD_indD_plus_lo_le_YofD d hA.lo ((hA.bounded d).mono (fun _ h => h.1))
  have hint_sum :
      IntegrableOn (fun ω => S.YofD d ω * S.dVar.indicator d ω
                              + hA.lo * S.dVar.indicator (!d) ω)
        (S.zEvent z) P.μ :=
    ((S.YofD_mul_indD_integrable hA d).add
      (S.const_mul_indD_integrable hA.lo (!d))).integrableOn
  have hint_Yd : IntegrableOn (S.YofD d) (S.zEvent z) P.μ :=
    (hA.integrable_YofD d).integrableOn
  have hmono :
      normalizedRestrictedIntegral P.μ (S.zEvent z)
          (fun ω => S.YofD d ω * S.dVar.indicator d ω
                     + hA.lo * S.dVar.indicator (!d) ω)
        ≤ normalizedRestrictedIntegral P.μ (S.zEvent z) (S.YofD d) := by
    refine eventCondExp_mono_ae P.μ hint_sum hint_Yd ?_
    exact ae_restrict_of_ae hbound_ae
  calc
    S.boundArm d hA.lo z
        = normalizedRestrictedIntegral P.μ (S.zEvent z)
            (fun ω => S.YofD d ω * S.dVar.indicator d ω
                       + hA.lo * S.dVar.indicator (!d) ω) := by
          unfold boundArm; rw [hcons]
    _ ≤ normalizedRestrictedIntegral P.μ (S.zEvent z) (S.YofD d) := hmono

/-- Under [the baseline Manski assumptions](hyp:hA), for [a treatment arm](hyp:d)
and [a singleton instrument stratum](hyp:z), [the normalized restricted integral
of the arm's potential outcome is bounded above by the unified upper-envelope
functional](goal).

On a null stratum the normalized restricted integral is defined to be zero; it
has conditional-mean semantics only on positive-mass strata. -/
theorem cond_YofD_le_boundArm_hi [IsFiniteMeasure P.μ]
    (hA : S.BaseAssumptions) (d : Bool) {z : α} :
    normalizedRestrictedIntegral P.μ (S.zEvent z) (S.YofD d) ≤ S.boundArm d hA.hi z := by
  have hcons : (fun ω => S.factualY ω * S.dVar.indicator d ω
                          + hA.hi * S.dVar.indicator (!d) ω)
              = (fun ω => S.YofD d ω * S.dVar.indicator d ω
                            + hA.hi * S.dVar.indicator (!d) ω) := by
    funext ω
    have hvw : S.yVar.v ≠ S.dVar.v := Ne.symm S.hDY
    have h := congr_fun (POVar.factual_mul_indicator_eq_cfUnder_mul_indicator_fn
      hA.consistency S.yVar S.dVar d hvw) ω
    rw [show S.factualY ω * S.dVar.indicator d ω = S.YofD d ω * S.dVar.indicator d ω from by
      simpa [POManskiIVSystem.factualY, POManskiIVSystem.YofD] using h]
  have hbound_ae :=
    S.YofD_le_YofD_indD_plus_hi d hA.hi ((hA.bounded d).mono (fun _ h => h.2))
  have hint_sum :
      IntegrableOn (fun ω => S.YofD d ω * S.dVar.indicator d ω
                              + hA.hi * S.dVar.indicator (!d) ω)
        (S.zEvent z) P.μ :=
    ((S.YofD_mul_indD_integrable hA d).add
      (S.const_mul_indD_integrable hA.hi (!d))).integrableOn
  have hint_Yd : IntegrableOn (S.YofD d) (S.zEvent z) P.μ :=
    (hA.integrable_YofD d).integrableOn
  have hmono :
      normalizedRestrictedIntegral P.μ (S.zEvent z) (S.YofD d)
        ≤ normalizedRestrictedIntegral P.μ (S.zEvent z)
            (fun ω => S.YofD d ω * S.dVar.indicator d ω
                       + hA.hi * S.dVar.indicator (!d) ω) := by
    refine eventCondExp_mono_ae P.μ hint_Yd hint_sum ?_
    exact ae_restrict_of_ae hbound_ae
  calc
    normalizedRestrictedIntegral P.μ (S.zEvent z) (S.YofD d)
        ≤ normalizedRestrictedIntegral P.μ (S.zEvent z)
            (fun ω => S.YofD d ω * S.dVar.indicator d ω
                       + hA.hi * S.dVar.indicator (!d) ω) := hmono
    _ = S.boundArm d hA.hi z := by unfold boundArm; rw [hcons]

/-! ### Legacy named corollaries

Preserved as thin wrappers so `NonAsp`, `MTR`, `MTS`, `MIV`, `Combined`
compile unchanged. -/

/-- Under [the baseline Manski assumptions](hyp:hA), within [an instrument
stratum](hyp:z), [the treated-arm lower functional does not exceed
the treated potential-outcome mean in that stratum](goal). -/
theorem lowerBound1_le_cond_Y1 [IsFiniteMeasure P.μ]
    (hA : S.BaseAssumptions) {z : α} :
    S.lowerBound1 hA.lo z ≤ normalizedRestrictedIntegral P.μ (S.zEvent z) (S.YofD true) :=
  S.boundArm_lo_le_cond_YofD hA true

/-- Under [the baseline Manski assumptions](hyp:hA), within [an instrument
stratum](hyp:z), [the treated potential-outcome mean in that
stratum does not exceed the treated-arm upper functional](goal). -/
theorem cond_Y1_le_upperBound1 [IsFiniteMeasure P.μ]
    (hA : S.BaseAssumptions) {z : α} :
    normalizedRestrictedIntegral P.μ (S.zEvent z) (S.YofD true) ≤ S.upperBound1 hA.hi z :=
  S.cond_YofD_le_boundArm_hi hA true

/-- Under [the baseline Manski assumptions](hyp:hA), within [an instrument
stratum](hyp:z), [the control-arm lower functional does not exceed
the control potential-outcome mean in that stratum](goal). -/
theorem lowerBound0_le_cond_Y0 [IsFiniteMeasure P.μ]
    (hA : S.BaseAssumptions) {z : α} :
    S.lowerBound0 hA.lo z ≤ normalizedRestrictedIntegral P.μ (S.zEvent z) (S.YofD false) :=
  S.boundArm_lo_le_cond_YofD hA false

/-- Under [the baseline Manski assumptions](hyp:hA), within [an instrument
stratum](hyp:z), [the control potential-outcome mean in that
stratum does not exceed the control-arm upper functional](goal). -/
theorem cond_Y0_le_upperBound0 [IsFiniteMeasure P.μ]
    (hA : S.BaseAssumptions) {z : α} :
    normalizedRestrictedIntegral P.μ (S.zEvent z) (S.YofD false) ≤ S.upperBound0 hA.hi z :=
  S.cond_YofD_le_boundArm_hi hA false

end POManskiIVSystem

end PO
end Causalean
