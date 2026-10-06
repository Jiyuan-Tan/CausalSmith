/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Mathlib.MeasureTheory.CondExpPreimage
public import Causalean.PO.ID.Partial.Sensitivity.MSM.Compatible

/-! # Converse validity for the marginal sensitivity model

This file derives an observed calibrated propensity candidate from every
compatible full-data model.  Conditional expectation preserves the Tan
odds box after rewriting it as a pointwise propensity interval; the resulting
`(X,Y(1))` propensity is transported through equality of observable-record
laws.  Calibration and the inverse-probability-weighted target identity are
proved rather than assumed.
-/

@[expose] public section

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace POBackdoorSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
variable {S : POBackdoorSystem P γ} {Λ : ℝ}

/-- Given [a positive sensitivity level](hyp:hΛ) and [two interior probabilities](hyp:hq0,hq1,hp0,hp1),
[Tan's odds-ratio interval is equivalent to the corresponding interval for the
complete propensity itself](goal). -/
theorem OR_box_iff_propensity_box {Λ q p : ℝ} (hΛ : 0 < Λ)
    (hq0 : 0 < q) (hq1 : q < 1) (hp0 : 0 < p) (hp1 : p < 1) :
    (1 / Λ ≤ OR p q ∧ OR p q ≤ Λ) ↔
      (q / (Λ * (1 - q) + q) ≤ p ∧
        p ≤ Λ * q / ((1 - q) + Λ * q)) := by
  have h1q : 0 < 1 - q := by linarith
  have h1p : 0 < 1 - p := by linarith
  have hdlo : 0 < Λ * (1 - q) + q := by positivity
  have hdhi : 0 < (1 - q) + Λ * q := by positivity
  have hden : 0 < (1 - p) * q := mul_pos h1p hq0
  have hor : OR p q = p * (1 - q) / ((1 - p) * q) := by
    rw [OR, div_div_eq_mul_div, div_mul_eq_mul_div, mul_comm, mul_div_mul_comm]
    ring_nf
  rw [hor]
  constructor
  · rintro ⟨hlo, hhi⟩
    rw [div_le_div_iff₀ hΛ hden] at hlo
    rw [div_le_iff₀ hden] at hhi
    constructor
    · rw [div_le_iff₀ hdlo]
      nlinarith
    · rw [le_div_iff₀ hdhi]
      nlinarith
  · rintro ⟨hlo, hhi⟩
    rw [div_le_iff₀ hdlo] at hlo
    rw [le_div_iff₀ hdhi] at hhi
    constructor
    · rw [div_le_div_iff₀ hΛ hden]
      nlinarith
    · rw [div_le_iff₀ hden]
      nlinarith

namespace MSMDataCompatible

variable (M : MSMDataCompatible S Λ)

/-- If [the observed propensity has strict overlap](hyp:hoverlap), then [the observed
covariate-level propensity evaluated in a compatible model is also strictly between zero and
one almost everywhere](goal). -/
theorem ae_propensityFactor_mem_Ioo
    (hoverlap : ∀ᵐ ω ∂P.μ,
      0 < S.propScore true ω ∧ S.propScore true ω < 1) :
    ∀ᵐ ω ∂M.Q,
      0 < S.propensityFactor (M.X ω) ∧ S.propensityFactor (M.X ω) < 1 := by
  let pred : ((γ × Bool) × ℝ) → Prop := fun r =>
    0 < S.propensityFactor r.1.1 ∧ S.propensityFactor r.1.1 < 1
  have hpred : MeasurableSet {r | pred r} := by
    apply (measurableSet_lt measurable_const
      (S.measurable_propensityFactor.comp (measurable_fst.comp measurable_fst))).inter
    exact measurableSet_lt
      (S.measurable_propensityFactor.comp (measurable_fst.comp measurable_fst))
      measurable_const
  have hmap : M.Q.map M.observedRecord = P.μ.map S.factualObservedRecord := by
    exact M.observedLaw
  have hfactual : Measurable S.factualObservedRecord := by
    unfold factualObservedRecord
    exact (S.measurable_factualX.prodMk S.measurable_factualD).prodMk
      ((S.dVar.measurable_indicator true (measurableSet_singleton true)).mul
        S.measurable_factualY)
  have htransport :=
    (Mathlib.MeasureTheory.ae_comp_iff_of_map_eq M.measurable_observedRecord
      hfactual pred hpred hmap).mpr
  apply htransport
  filter_upwards [hoverlap] with ω hω
  have hfactor := congrFun S.propScore_eq_propensityFactor_comp ω
  simpa [pred, MSMDataCompatible.observedRecord, factualObservedRecord,
    Function.comp_apply, hfactor] using hω

/-- If [the observed propensity has strict overlap](hyp:hoverlap), then [the
`(X,Y(1))`-conditional propensity in a compatible model remains strictly between zero and one
almost everywhere](goal). -/
theorem ae_xyPropensity_mem_Ioo
    (hoverlap : ∀ᵐ ω ∂P.μ,
      0 < S.propScore true ω ∧ S.propScore true ω < 1) :
    ∀ᵐ ω ∂M.Q, 0 < M.xyPropensity ω ∧ M.xyPropensity ω < 1 := by
  obtain ⟨ε, hε, hover⟩ := M.completeOverlap
  have hbounds := Mathlib.MeasureTheory.condExp_ae_mem_Icc M.sigmaXY1_le
    M.integrable_completePropensity (hover.mono fun ω hω => hω.1)
      (hover.mono fun ω hω => hω.2)
  filter_upwards [hbounds] with ω hω
  exact ⟨hε.trans_le hω.1, lt_of_le_of_lt hω.2 (sub_lt_self 1 hε)⟩

private noncomputable def lowerPropensity : M.Ω → ℝ := fun ω =>
  let q := S.propensityFactor (M.X ω)
  q / (Λ * (1 - q) + q)

private noncomputable def upperPropensity : M.Ω → ℝ := fun ω =>
  let q := S.propensityFactor (M.X ω)
  Λ * q / ((1 - q) + Λ * q)

private theorem measurable_lowerPropensity_sigmaXY1 :
    Measurable[M.sigmaXY1] M.lowerPropensity := by
  have hX : Measurable[M.sigmaXY1] M.X :=
    (comap_measurable M.X).mono le_sup_left le_rfl
  unfold lowerPropensity
  fun_prop

private theorem measurable_upperPropensity_sigmaXY1 :
    Measurable[M.sigmaXY1] M.upperPropensity := by
  have hX : Measurable[M.sigmaXY1] M.X :=
    (comap_measurable M.X).mono le_sup_left le_rfl
  unfold upperPropensity
  fun_prop

private theorem endpoint_bounds (hΛ : 0 < Λ)
    (hoverlap : ∀ᵐ ω ∂P.μ,
      0 < S.propScore true ω ∧ S.propScore true ω < 1) :
    (∀ᵐ ω ∂M.Q, 0 ≤ M.lowerPropensity ω ∧ M.lowerPropensity ω ≤ 1) ∧
      (∀ᵐ ω ∂M.Q, 0 ≤ M.upperPropensity ω ∧ M.upperPropensity ω ≤ 1) := by
  have hq := M.ae_propensityFactor_mem_Ioo hoverlap
  constructor <;> filter_upwards [hq] with ω hω
  · unfold lowerPropensity
    dsimp
    have hd : 0 < Λ * (1 - S.propensityFactor (M.X ω)) +
        S.propensityFactor (M.X ω) :=
      add_pos (mul_pos hΛ (sub_pos.mpr hω.2)) hω.1
    constructor
    · exact div_nonneg hω.1.le hd.le
    · rw [div_le_one hd]
      nlinarith [mul_pos hΛ (sub_pos.mpr hω.2)]
  · unfold upperPropensity
    dsimp
    have hd : 0 < (1 - S.propensityFactor (M.X ω)) +
        Λ * S.propensityFactor (M.X ω) :=
      add_pos (sub_pos.mpr hω.2) (mul_pos hΛ hω.1)
    constructor
    · exact div_nonneg (mul_nonneg hΛ.le hω.1.le) hd.le
    · rw [div_le_one hd]
      linarith

private theorem integrable_lowerPropensity (hΛ : 0 < Λ)
    (hoverlap : ∀ᵐ ω ∂P.μ,
      0 < S.propScore true ω ∧ S.propScore true ω < 1) :
    Integrable M.lowerPropensity M.Q := by
  have hb := (M.endpoint_bounds hΛ hoverlap).1
  apply Integrable.of_bound
    (M.measurable_lowerPropensity_sigmaXY1.mono M.sigmaXY1_le le_rfl).aestronglyMeasurable 1
  filter_upwards [hb] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg hω.1]
  exact hω.2

private theorem integrable_upperPropensity (hΛ : 0 < Λ)
    (hoverlap : ∀ᵐ ω ∂P.μ,
      0 < S.propScore true ω ∧ S.propScore true ω < 1) :
    Integrable M.upperPropensity M.Q := by
  have hb := (M.endpoint_bounds hΛ hoverlap).2
  apply Integrable.of_bound
    (M.measurable_upperPropensity_sigmaXY1.mono M.sigmaXY1_le le_rfl).aestronglyMeasurable 1
  filter_upwards [hb] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg hω.1]
  exact hω.2

/-- Under [a sensitivity level at least one](hyp:hΛ) and [observed strict overlap](hyp:hoverlap),
[the complete propensity conditioned on `(X,Y(1))` obeys the same Tan odds-ratio box](goal). -/
theorem xyPropensity_odds (hΛ : 1 ≤ Λ)
    (hoverlap : ∀ᵐ ω ∂P.μ,
      0 < S.propScore true ω ∧ S.propScore true ω < 1) :
    ∀ᵐ ω ∂M.Q,
      1 / Λ ≤ OR (M.xyPropensity ω) (S.propensityFactor (M.X ω)) ∧
        OR (M.xyPropensity ω) (S.propensityFactor (M.X ω)) ≤ Λ := by
  have hΛpos : 0 < Λ := one_pos.trans_le hΛ
  have hq := M.ae_propensityFactor_mem_Ioo hoverlap
  have he := M.completeOverlap
  obtain ⟨ε, hε, he⟩ := he
  have heIoo : ∀ᵐ ω ∂M.Q,
      0 < M.completePropensity ω ∧ M.completePropensity ω < 1 := by
    filter_upwards [he] with ω hω
    exact ⟨hε.trans_le hω.1, lt_of_le_of_lt hω.2 (sub_lt_self 1 hε)⟩
  have hbox : ∀ᵐ ω ∂M.Q,
      M.lowerPropensity ω ≤ M.completePropensity ω ∧
        M.completePropensity ω ≤ M.upperPropensity ω := by
    filter_upwards [hq, heIoo, M.completeOdds] with ω hqω heω hodds
    exact (OR_box_iff_propensity_box hΛpos hqω.1 hqω.2 heω.1 heω.2).mp hodds
  have hcond := Mathlib.MeasureTheory.condExp_ae_mem_Icc_of_stronglyMeasurable
    M.sigmaXY1_le (M.integrable_lowerPropensity hΛpos hoverlap)
    M.integrable_completePropensity (M.integrable_upperPropensity hΛpos hoverlap)
    M.measurable_lowerPropensity_sigmaXY1.stronglyMeasurable
    M.measurable_upperPropensity_sigmaXY1.stronglyMeasurable
    (hbox.mono fun ω hω => hω.1) (hbox.mono fun ω hω => hω.2)
  have hg := M.ae_xyPropensity_mem_Ioo hoverlap
  filter_upwards [hq, hg, hcond] with ω hqω hgω hcondω
  exact (OR_box_iff_propensity_box hΛpos hqω.1 hqω.2 hgω.1 hgω.2).mpr hcondω

/-- For [a compatible model](hyp:M), the [inverse-propensity treatment weight](goal) is
`1{Z=1}/g(X,Y(1))`. -/
noncomputable def inverseWeight : M.Ω → ℝ := fun ω =>
  M.treatmentIndicator ω / M.xyPropensity ω

/-- The [inverse-propensity treatment weight](hyp:M) is [integrable](goal). -/
@[fun_prop]
theorem integrable_inverseWeight : Integrable M.inverseWeight M.Q := by
  obtain ⟨ε, hε, hover⟩ := M.completeOverlap
  have hbound := Mathlib.MeasureTheory.condExp_ae_mem_Icc M.sigmaXY1_le
    M.integrable_completePropensity (hover.mono fun ω hω => hω.1)
      (hover.mono fun ω hω => hω.2)
  have hxy_meas : Measurable M.xyPropensity :=
    stronglyMeasurable_condExp.measurable.mono M.sigmaXY1_le le_rfl
  apply Integrable.of_bound
    (M.measurable_treatmentIndicator.div hxy_meas).aestronglyMeasurable (1 / ε)
  filter_upwards [hbound] with ω hω
  by_cases hz : M.Z ω
  · have hg : 0 < M.xyPropensity ω := hε.trans_le hω.1
    have hge : ε ≤ M.xyPropensity ω := by
      simpa only [xyPropensity] using hω.1
    change ‖(if M.Z ω then 1 else 0) / M.xyPropensity ω‖ ≤ 1 / ε
    rw [if_pos hz, one_div, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hg)]
    simpa [one_div] using one_div_le_one_div_of_le hε hge
  · change ‖(if M.Z ω then 1 else 0) / M.xyPropensity ω‖ ≤ 1 / ε
    simp [hz, hε.le]

/-- In [a compatible model](hyp:M), [the inverse treatment weight has conditional mean one
given `(X,Y(1))`](goal). -/
theorem condExp_inverseWeight_eq_one :
    M.Q[M.inverseWeight | M.sigmaXY1] =ᵐ[M.Q] (fun _ => 1) := by
  have hgstrong : StronglyMeasurable[M.sigmaXY1]
      (fun ω => 1 / M.xyPropensity ω) :=
    (measurable_const.div stronglyMeasurable_condExp.measurable).stronglyMeasurable
  have hreform : M.inverseWeight =
      fun ω => (1 / M.xyPropensity ω) * M.treatmentIndicator ω := by
    funext ω
    simp [inverseWeight, div_eq_inv_mul]
  have hpull :
      M.Q[fun ω => (1 / M.xyPropensity ω) * M.treatmentIndicator ω |
          M.sigmaXY1] =ᵐ[M.Q]
        (fun ω => (1 / M.xyPropensity ω) * M.xyPropensity ω) := by
    have h := condExp_mul_of_stronglyMeasurable_left
      (m := M.sigmaXY1) (μ := M.Q) hgstrong
      (M.integrable_inverseWeight.congr (ae_of_all _ fun ω => by
        simp [inverseWeight, div_eq_inv_mul]))
      M.integrable_treatmentIndicator
    exact h.trans (Filter.EventuallyEq.rfl.mul
      M.condExp_treatmentIndicator_eq_xyPropensity)
  rw [hreform]
  refine hpull.trans ?_
  obtain ⟨ε, hε, hover⟩ := M.completeOverlap
  have hbounds := Mathlib.MeasureTheory.condExp_ae_mem_Icc M.sigmaXY1_le
    M.integrable_completePropensity (hover.mono fun ω hω => hω.1)
      (hover.mono fun ω hω => hω.2)
  filter_upwards [hbounds] with ω hω
  have hpos : 0 < M.xyPropensity ω := hε.trans_le hω.1
  field_simp

/-- In [a compatible model](hyp:M), [the inverse treatment weight has conditional mean one
given the covariate alone](goal). -/
theorem condExp_inverseWeight_sigmaX_eq_one :
    M.Q[M.inverseWeight | MeasurableSpace.comap M.X inferInstance] =ᵐ[M.Q]
      (fun _ => 1) := by
  have hXle : MeasurableSpace.comap M.X inferInstance ≤ M.sigmaXY1 := le_sup_left
  have htower :
      M.Q[M.inverseWeight | MeasurableSpace.comap M.X inferInstance] =ᵐ[M.Q]
        M.Q[M.Q[M.inverseWeight | M.sigmaXY1] |
          MeasurableSpace.comap M.X inferInstance] :=
    (condExp_condExp_of_le (μ := M.Q) (f := M.inverseWeight)
      hXle M.sigmaXY1_le).symm
  refine htower.trans ?_
  refine (condExp_congr_ae M.condExp_inverseWeight_eq_one).trans ?_
  exact Filter.EventuallyEq.of_eq
    (condExp_const M.measurable_X.comap_le (1 : ℝ))

/-- For [a compatible model](hyp:M), the [inverse-propensity-weighted treated potential
outcome](goal) is `1{Z=1}Y(1)/g(X,Y(1))`. -/
noncomputable def weightedY1 : M.Ω → ℝ := fun ω =>
  M.inverseWeight ω * M.Y1 ω

/-- The [inverse-propensity-weighted treated potential outcome](hyp:M) is
[integrable](goal). -/
@[fun_prop]
theorem integrable_weightedY1 : Integrable M.weightedY1 M.Q := by
  obtain ⟨ε, hε, hover⟩ := M.completeOverlap
  have hbound := Mathlib.MeasureTheory.condExp_ae_mem_Icc M.sigmaXY1_le
    M.integrable_completePropensity (hover.mono fun ω hω => hω.1)
      (hover.mono fun ω hω => hω.2)
  unfold weightedY1
  apply M.integrable_Y1.bdd_mul
    M.integrable_inverseWeight.aestronglyMeasurable
  filter_upwards [hbound] with ω hω
  by_cases hz : M.Z ω
  · have hg : 0 < M.xyPropensity ω := hε.trans_le hω.1
    have hge : ε ≤ M.xyPropensity ω := by
      simpa only [xyPropensity] using hω.1
    change ‖(if M.Z ω then 1 else 0) / M.xyPropensity ω‖ ≤ 1 / ε
    rw [if_pos hz, one_div, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hg)]
    simpa [one_div] using one_div_le_one_div_of_le hε hge
  · change ‖(if M.Z ω then 1 else 0) / M.xyPropensity ω‖ ≤ 1 / ε
    simp [hz, hε.le]

/-- **Full-data IPW identity.** In [a compatible model](hyp:M), [the expectation of the
inverse-propensity-weighted treated outcome equals the mean of `Y(1)`](goal). -/
theorem integral_weightedY1_eq_target :
    ∫ ω, M.weightedY1 ω ∂M.Q = M.target := by
  have hYmeas : Measurable[M.sigmaXY1] M.Y1 := by
    exact (comap_measurable M.Y1).mono le_sup_right le_rfl
  have hYstrong : StronglyMeasurable[M.sigmaXY1] M.Y1 := hYmeas.stronglyMeasurable
  have hpull :
      M.Q[M.weightedY1 | M.sigmaXY1] =ᵐ[M.Q]
        (fun ω => M.Y1 ω) := by
    have h := condExp_mul_of_stronglyMeasurable_right
      (m := M.sigmaXY1) (μ := M.Q) hYstrong
      M.integrable_weightedY1 M.integrable_inverseWeight
    refine h.trans ?_
    filter_upwards [M.condExp_inverseWeight_eq_one] with ω hω
    simp [hω]
  unfold target
  rw [← integral_condExp M.sigmaXY1_le]
  exact integral_congr_ae hpull


end MSMDataCompatible

end POBackdoorSystem
end PO
end Causalean
