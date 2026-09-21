/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Variable-intensity instrumental variables

A directed-pair Wald specialization of the Angrist--Imbens causal-response
algebra for finite ordered treatment intensities: one directed instrument
contrast identifies an average causal response over the treatment-intensity
margins crossed by that contrast. This file does not derive the paper's general
population 2SLS characterization for multivalued instruments.
-/

module

public import Causalean.Mathlib.Probability.FiniteCellConditionalMomentBridge
public import Causalean.PO.Conditioning.EventCondExp
public import Causalean.PO.ID.Exact.VariableIntensityIV.VariableIntensity.Basic

/-! # Directed-pair variable-intensity IV identification

This part develops the consistency bridges and proves the first-stage, reduced-form, and
average-causal-response identification results for one directed instrument contrast. It is a
pairwise Wald specialization, not a population 2SLS characterization for multivalued
instruments. -/

public section

open Causalean.Mathlib.Probability

namespace Causalean
namespace PO.ID.Exact
namespace VariableIntensityIV

open Finset MeasureTheory ProbabilityTheory

noncomputable section

namespace VariableIntensityIVSystem

variable {P : POSystem} {𝒵 : Type*} [MeasurableSpace 𝒵]
variable [Fintype 𝒵] [MeasurableSingletonClass 𝒵]
variable {J : ℕ} (S : VariableIntensityIVSystem P 𝒵 J)

/-! ### Consistency bridges

On the cell `{Z = z}` the potential intensity `D(z)` agrees with the factual `D`,
and the factual outcome `Y` agrees with the treatment-selected counterfactual
`Y(D)`.  Both are pointwise specializations of `P.Consistency` via the shared
consistency lemmas. -/

/-- [Consistency identifies potential treatment at an instrument value with observed treatment
inside that instrument cell](goal) under [the consistency condition](hyp:hC), for [the instrument
value](hyp:z) and [a unit in its observed cell](hyp:ω,hω). -/
lemma DofZ_eq_factualD_on_zEvent (hC : P.Consistency) (z : 𝒵)
    {ω : P.Ω} (hω : ω ∈ S.zEvent z) :
    S.DofZ z ω = S.factualD ω :=
  POVar.cf_eq_factual_on_event hC S.dVar S.zVar z S.hZD.symm hω

/-- [Consistency identifies observed outcome with potential outcome at realized treatment](goal)
under [the consistency condition](hyp:hC), for [the unit being evaluated](hyp:ω). -/
lemma factualY_eq_YofD_factualD (hC : P.Consistency) (ω : P.Ω) :
    S.factualY ω = S.YofD (S.factualD ω) ω :=
  POVar.factual_eq_cfUnder_self_selected hC S.yVar S.dVar S.hDY.symm ω

/-- [The observed treatment mean in the first instrument cell equals mean potential treatment
under that instrument value](goal) under [the directed-contrast IV assumptions](hyp:hValid) when
[the first cell has positive probability](hyp:hCell0). This is the left first-stage bridge. -/
lemma condExpDZ_left_eq_integral {z0 z1 : 𝒵}
    (hValid : S.ValidContrastAssumptions z0 z1)
    (hCell0 : 0 < (P.μ (S.zEvent z0)).toReal) :
    S.condExpDZ z0 = ∫ ω, OrderedTreatment.intensityValue (S.DofZ z0 ω) ∂P.μ := by
  have hμne_zero : P.μ (S.zVar.event z0) ≠ 0 := fun h =>
    absurd hCell0 (by simp [show S.zEvent z0 = S.zVar.event z0 from rfl, h])
  have hμne_top : P.μ (S.zVar.event z0) ≠ ⊤ := measure_ne_top _ _
  let idx0 : Fin (S.cfContrastBundle z0 z1).n :=
    ⟨0, by simp [cfContrastBundle, outcomeBundle, POCFBundle.cons]⟩
  let hproj :
      (∀ i : Fin (S.cfContrastBundle z0 z1).n, (S.cfContrastBundle z0 z1).type i) → ℝ :=
    fun f => OrderedTreatment.intensityValue (f idx0)
  have hh_meas : Measurable hproj := by
    change Measurable fun f :
        (∀ i : Fin (S.cfContrastBundle z0 z1).n,
          (S.cfContrastBundle z0 z1).type i) =>
        OrderedTreatment.intensityValue (f idx0)
    exact (measurable_intensityValue (J := J)).comp (measurable_pi_apply idx0)
  have h_cons : ∀ ω ∈ S.zVar.event z0,
      OrderedTreatment.intensityValue (S.factualD ω) =
        hproj ((S.cfContrastBundle z0 z1).jointValue ω) := by
    intro ω hω
    rw [← S.DofZ_eq_factualD_on_zEvent hValid.consistency z0 hω]
    change OrderedTreatment.intensityValue (S.DofZ z0 ω) =
      OrderedTreatment.intensityValue ((S.cfContrastBundle z0 z1).jointValue ω idx0)
    rfl
  have hbridge : S.condExpDZ z0 =
      normalizedRestrictedIntegral P.μ (S.zVar.event z0)
        (fun ω => OrderedTreatment.intensityValue (S.factualD ω)) := rfl
  rw [hbridge,
    POSystem.eventCondExp_of_ae_eq_IndepCF hValid.hIndependence
      (a := S.zVar) hh_meas
      (MeasurableSet.singleton z0)
      (ae_restrict_of_forall_mem (S.measurableSet_zEvent z0) h_cons)
      hμne_zero hμne_top]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro ω
  change OrderedTreatment.intensityValue ((S.cfContrastBundle z0 z1).jointValue ω idx0) =
    OrderedTreatment.intensityValue (S.DofZ z0 ω)
  rfl

/-- [The observed treatment mean in the second instrument cell equals mean potential treatment
under that instrument value](goal) under [the directed-contrast IV assumptions](hyp:hValid) when
[the second cell has positive probability](hyp:hCell1). This is the right first-stage bridge. -/
lemma condExpDZ_right_eq_integral {z0 z1 : 𝒵}
    (hValid : S.ValidContrastAssumptions z0 z1)
    (hCell1 : 0 < (P.μ (S.zEvent z1)).toReal) :
    S.condExpDZ z1 = ∫ ω, OrderedTreatment.intensityValue (S.DofZ z1 ω) ∂P.μ := by
  have hμne_zero : P.μ (S.zVar.event z1) ≠ 0 := fun h =>
    absurd hCell1 (by simp [show S.zEvent z1 = S.zVar.event z1 from rfl, h])
  have hμne_top : P.μ (S.zVar.event z1) ≠ ⊤ := measure_ne_top _ _
  let idx1 : Fin (S.cfContrastBundle z0 z1).n :=
    ⟨1, by simp [cfContrastBundle, outcomeBundle, POCFBundle.cons]⟩
  let hproj :
      (∀ i : Fin (S.cfContrastBundle z0 z1).n, (S.cfContrastBundle z0 z1).type i) → ℝ :=
    fun f => OrderedTreatment.intensityValue (f idx1)
  have hh_meas : Measurable hproj := by
    change Measurable fun f :
        (∀ i : Fin (S.cfContrastBundle z0 z1).n,
          (S.cfContrastBundle z0 z1).type i) =>
        OrderedTreatment.intensityValue (f idx1)
    exact (measurable_intensityValue (J := J)).comp (measurable_pi_apply idx1)
  have h_cons : ∀ ω ∈ S.zVar.event z1,
      OrderedTreatment.intensityValue (S.factualD ω) =
        hproj ((S.cfContrastBundle z0 z1).jointValue ω) := by
    intro ω hω
    rw [← S.DofZ_eq_factualD_on_zEvent hValid.consistency z1 hω]
    change OrderedTreatment.intensityValue (S.DofZ z1 ω) =
      OrderedTreatment.intensityValue
        ((S.cfContrastBundle z0 z1).jointValue ω idx1)
    rfl
  have hbridge : S.condExpDZ z1 =
      normalizedRestrictedIntegral P.μ (S.zVar.event z1)
        (fun ω => OrderedTreatment.intensityValue (S.factualD ω)) := rfl
  rw [hbridge,
    POSystem.eventCondExp_of_ae_eq_IndepCF hValid.hIndependence
      (a := S.zVar) hh_meas
      (MeasurableSet.singleton z1)
      (ae_restrict_of_forall_mem (S.measurableSet_zEvent z1) h_cons)
      hμne_zero hμne_top]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro ω
  change OrderedTreatment.intensityValue
      ((S.cfContrastBundle z0 z1).jointValue ω idx1) =
    OrderedTreatment.intensityValue (S.DofZ z1 ω)
  rfl

/-- [The observed outcome mean in the first instrument cell equals mean outcome under the
treatment induced by that instrument value](goal) under [the directed-contrast IV
assumptions](hyp:hValid) when [the first cell has positive probability](hyp:hCell0). -/
lemma condExpYZ_left_eq_integral {z0 z1 : 𝒵}
    (hValid : S.ValidContrastAssumptions z0 z1)
    (hCell0 : 0 < (P.μ (S.zEvent z0)).toReal) :
    S.condExpYZ z0 = ∫ ω, S.YofDofZ z0 ω ∂P.μ := by
  classical
  have hμne_zero : P.μ (S.zVar.event z0) ≠ 0 := fun h =>
    absurd hCell0 (by simp [show S.zEvent z0 = S.zVar.event z0 from rfl, h])
  have hμne_top : P.μ (S.zVar.event z0) ≠ ⊤ := measure_ne_top _ _
  let idx0 : Fin (S.cfContrastBundle z0 z1).n :=
    ⟨0, by simp [cfContrastBundle, outcomeBundle, POCFBundle.cons]⟩
  let idxY (i : Fin (J + 1)) : Fin (S.cfContrastBundle z0 z1).n :=
    Fin.succ (Fin.succ i)
  let hproj :
      (∀ i : Fin (S.cfContrastBundle z0 z1).n, (S.cfContrastBundle z0 z1).type i) → ℝ :=
    fun f => ∑ i : Fin (J + 1), if f idx0 = i then f (idxY i) else 0
  have hh_meas : Measurable hproj := by
    change Measurable fun f :
        (∀ i : Fin (S.cfContrastBundle z0 z1).n,
          (S.cfContrastBundle z0 z1).type i) =>
        ∑ i : Fin (J + 1), if f idx0 = i then f (idxY i) else 0
    refine Finset.measurable_sum _ ?_
    intro i _hi
    refine Measurable.ite ?_ (measurable_pi_apply (idxY i)) measurable_const
    exact (MeasurableSet.singleton i).preimage (measurable_pi_apply idx0)
  have h_cons : ∀ ω ∈ S.zVar.event z0,
      S.factualY ω = hproj ((S.cfContrastBundle z0 z1).jointValue ω) := by
    intro ω hω
    rw [S.factualY_eq_YofD_factualD hValid.consistency ω,
      ← S.DofZ_eq_factualD_on_zEvent hValid.consistency z0 hω]
    have hJV0 : (S.cfContrastBundle z0 z1).jointValue ω idx0 = S.DofZ z0 ω := rfl
    have hJVY : ∀ i : Fin (J + 1),
        (S.cfContrastBundle z0 z1).jointValue ω (idxY i) = S.YofD i ω := by
      intro i
      rfl
    change S.YofD (S.DofZ z0 ω) ω =
      ∑ i : Fin (J + 1),
        if (S.cfContrastBundle z0 z1).jointValue ω idx0 = i then
          (S.cfContrastBundle z0 z1).jointValue ω (idxY i) else 0
    rw [hJV0]
    rw [Finset.sum_eq_single (S.DofZ z0 ω)]
    · exact (hJVY _).symm.trans (if_pos rfl).symm
    · intro i _hi hi
      by_cases hEq : S.DofZ z0 ω = i
      · exact False.elim (hi hEq.symm)
      · exact if_neg hEq
    · intro h
      simp at h
  have hbridge : S.condExpYZ z0 =
      normalizedRestrictedIntegral P.μ (S.zVar.event z0) S.factualY := rfl
  rw [hbridge,
    POSystem.eventCondExp_of_ae_eq_IndepCF hValid.hIndependence
      (a := S.zVar) hh_meas
      (MeasurableSet.singleton z0)
      (ae_restrict_of_forall_mem (S.measurableSet_zEvent z0) h_cons)
      hμne_zero hμne_top]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro ω
  have hJV0 : (S.cfContrastBundle z0 z1).jointValue ω idx0 = S.DofZ z0 ω := rfl
  have hJVY : ∀ i : Fin (J + 1),
      (S.cfContrastBundle z0 z1).jointValue ω (idxY i) = S.YofD i ω := by
    intro i
    rfl
  change (∑ i : Fin (J + 1),
      if (S.cfContrastBundle z0 z1).jointValue ω idx0 = i then
        (S.cfContrastBundle z0 z1).jointValue ω (idxY i) else 0) =
    S.YofDofZ z0 ω
  unfold YofDofZ
  rw [hJV0]
  rw [Finset.sum_eq_single (S.DofZ z0 ω)]
  · exact (if_pos rfl).trans (hJVY _)
  · intro i _hi hi
    by_cases hEq : S.DofZ z0 ω = i
    · exact False.elim (hi hEq.symm)
    · exact if_neg hEq
  · intro h
    simp at h

/-- [The observed outcome mean in the second instrument cell equals mean outcome under the
treatment induced by that instrument value](goal) under [the directed-contrast IV
assumptions](hyp:hValid) when [the second cell has positive probability](hyp:hCell1). -/
lemma condExpYZ_right_eq_integral {z0 z1 : 𝒵}
    (hValid : S.ValidContrastAssumptions z0 z1)
    (hCell1 : 0 < (P.μ (S.zEvent z1)).toReal) :
    S.condExpYZ z1 = ∫ ω, S.YofDofZ z1 ω ∂P.μ := by
  classical
  have hμne_zero : P.μ (S.zVar.event z1) ≠ 0 := fun h =>
    absurd hCell1 (by simp [show S.zEvent z1 = S.zVar.event z1 from rfl, h])
  have hμne_top : P.μ (S.zVar.event z1) ≠ ⊤ := measure_ne_top _ _
  let idx1 : Fin (S.cfContrastBundle z0 z1).n :=
    ⟨1, by simp [cfContrastBundle, outcomeBundle, POCFBundle.cons]⟩
  let idxY (i : Fin (J + 1)) : Fin (S.cfContrastBundle z0 z1).n :=
    Fin.succ (Fin.succ i)
  let hproj :
      (∀ i : Fin (S.cfContrastBundle z0 z1).n, (S.cfContrastBundle z0 z1).type i) → ℝ :=
    fun f => ∑ i : Fin (J + 1), if f idx1 = i then f (idxY i) else 0
  have hh_meas : Measurable hproj := by
    change Measurable fun f :
        (∀ i : Fin (S.cfContrastBundle z0 z1).n,
          (S.cfContrastBundle z0 z1).type i) =>
        ∑ i : Fin (J + 1), if f idx1 = i then f (idxY i) else 0
    refine Finset.measurable_sum _ ?_
    intro i _hi
    refine Measurable.ite ?_ (measurable_pi_apply (idxY i)) measurable_const
    exact (MeasurableSet.singleton i).preimage (measurable_pi_apply idx1)
  have h_cons : ∀ ω ∈ S.zVar.event z1,
      S.factualY ω = hproj ((S.cfContrastBundle z0 z1).jointValue ω) := by
    intro ω hω
    rw [S.factualY_eq_YofD_factualD hValid.consistency ω,
      ← S.DofZ_eq_factualD_on_zEvent hValid.consistency z1 hω]
    have hJV1 : (S.cfContrastBundle z0 z1).jointValue ω idx1 = S.DofZ z1 ω := rfl
    have hJVY : ∀ i : Fin (J + 1),
        (S.cfContrastBundle z0 z1).jointValue ω (idxY i) = S.YofD i ω := by
      intro i
      rfl
    change S.YofD (S.DofZ z1 ω) ω =
      ∑ i : Fin (J + 1),
        if (S.cfContrastBundle z0 z1).jointValue ω idx1 = i then
          (S.cfContrastBundle z0 z1).jointValue ω (idxY i) else 0
    rw [hJV1]
    rw [Finset.sum_eq_single (S.DofZ z1 ω)]
    · exact (hJVY _).symm.trans (if_pos rfl).symm
    · intro i _hi hi
      by_cases hEq : S.DofZ z1 ω = i
      · exact False.elim (hi hEq.symm)
      · exact if_neg hEq
    · intro h
      simp at h
  have hbridge : S.condExpYZ z1 =
      normalizedRestrictedIntegral P.μ (S.zVar.event z1) S.factualY := rfl
  rw [hbridge,
    POSystem.eventCondExp_of_ae_eq_IndepCF hValid.hIndependence
      (a := S.zVar) hh_meas
      (MeasurableSet.singleton z1)
      (ae_restrict_of_forall_mem (S.measurableSet_zEvent z1) h_cons)
      hμne_zero hμne_top]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro ω
  have hJV1 : (S.cfContrastBundle z0 z1).jointValue ω idx1 = S.DofZ z1 ω := rfl
  have hJVY : ∀ i : Fin (J + 1),
      (S.cfContrastBundle z0 z1).jointValue ω (idxY i) = S.YofD i ω := by
    intro i
    rfl
  change (∑ i : Fin (J + 1),
      if (S.cfContrastBundle z0 z1).jointValue ω idx1 = i then
        (S.cfContrastBundle z0 z1).jointValue ω (idxY i) else 0) =
    S.YofDofZ z1 ω
  unfold YofDofZ
  rw [hJV1]
  rw [Finset.sum_eq_single (S.DofZ z1 ω)]
  · exact (if_pos rfl).trans (hJVY _)
  · intro i _hi hi
    by_cases hEq : S.DofZ z1 ω = i
    · exact False.elim (hi hEq.symm)
    · exact if_neg hEq
  · intro h
    simp at h

/-- [The potential first-stage contrast equals the sum of treatment-margin crossing
probabilities](goal) under [the directed-contrast IV assumptions](hyp:hValid). Monotonicity makes
each unit's dose change count exactly the margins it crosses. -/
theorem firstStage_eq_sum_crossingProb {z0 z1 : 𝒵}
    (hValid : S.ValidContrastAssumptions z0 z1) :
    S.firstStageContrast z0 z1 = ∑ j : Fin J, S.crossingProb z0 z1 j := by
  unfold firstStageContrast crossingProb
  have hpoint :
      (fun ω => OrderedTreatment.intensityValue (S.DofZ z1 ω) -
          OrderedTreatment.intensityValue (S.DofZ z0 ω))
        =ᵐ[P.μ]
      fun ω => ∑ j : Fin J,
        OrderedTreatment.crossingIndicator (S.DofZ z0 ω) (S.DofZ z1 ω) j :=
    hValid.hMonotone.mono fun _ hmono =>
      OrderedTreatment.ordered_telescope_identity hmono
  calc
    ∫ ω, (OrderedTreatment.intensityValue (S.DofZ z1 ω) -
        OrderedTreatment.intensityValue (S.DofZ z0 ω)) ∂P.μ
        = ∫ ω, ∑ j : Fin J,
            OrderedTreatment.crossingIndicator (S.DofZ z0 ω) (S.DofZ z1 ω) j ∂P.μ := by
          exact MeasureTheory.integral_congr_ae hpoint
    _ = ∑ j : Fin J, ∫ ω,
            OrderedTreatment.crossingIndicator (S.DofZ z0 ω) (S.DofZ z1 ω) j ∂P.μ := by
          rw [MeasureTheory.integral_finset_sum]
          intro i _hi
          rw [S.crossingIndicator_fun_eq_indicator z0 z1 i]
          exact (MeasureTheory.integrable_const (μ := P.μ) (1 : ℝ)).indicator
            (S.measurableSet_crossingEvent z0 z1 i)
    _ = ∑ j : Fin J, (P.μ (S.crossingEvent z0 z1 j)).toReal := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          rw [S.crossingIndicator_fun_eq_indicator z0 z1 j]
          exact MeasureTheory.integral_indicator_one (S.measurableSet_crossingEvent z0 z1 j)

/-- [Every margin-crossing weight is nonnegative](goal) under [the directed-contrast IV
assumptions](hyp:hValid), for [the selected treatment margin](hyp:j), because monotonicity and a
positive first stage turn crossing shares into convex weights. -/
lemma crossingWeight_nonneg {z0 z1 : 𝒵}
    (hValid : S.ValidContrastAssumptions z0 z1) (j : Fin J) :
    0 ≤ S.crossingWeight z0 z1 j := by
  have hProb : ∀ i : Fin J, 0 ≤ S.crossingProb z0 z1 i := by
    intro i
    exact ENNReal.toReal_nonneg
  have hSum : 0 < ∑ i : Fin J, S.crossingProb z0 z1 i := by
    rw [← S.firstStage_eq_sum_crossingProb hValid]
    exact hValid.hRelevance
  exact OrderedTreatment.normalizedWeight_nonneg (S.crossingProb z0 z1) hProb hSum j

/-- [The margin-crossing weights sum to one](goal) under [the directed-contrast IV
assumptions](hyp:hValid), so the average causal response is a genuine weighted average. -/
lemma sum_crossingWeight_eq_one {z0 z1 : 𝒵}
    (hValid : S.ValidContrastAssumptions z0 z1) :
    ∑ j : Fin J, S.crossingWeight z0 z1 j = 1 := by
  have hSum : 0 < ∑ i : Fin J, S.crossingProb z0 z1 i := by
    rw [← S.firstStage_eq_sum_crossingProb hValid]
    exact hValid.hRelevance
  exact OrderedTreatment.sum_normalizedWeight_eq_one (S.crossingProb z0 z1) hSum

/-- **Reduced-form decomposition across crossed margins.** For [a directed instrument
contrast](hyp:z0,z1), under [the variable-intensity IV validity assumptions — SUTVA
consistency of treatment and outcome, instrument independence from the potential
treatments and treatment-indexed potential outcomes, almost-sure directed monotonicity of
the potential treatment intensity in the instrument, a positive first stage, and
integrability of every treatment-indexed potential outcome](hyp:hValid), [the potential
reduced-form contrast equals the sum of margin-specific causal responses among units whose dose
crosses each margin when assignment moves from the baseline to the comparison value](goal). -/
theorem reducedForm_eq_sum_crossingEffects {z0 z1 : 𝒵}
    (hValid : S.ValidContrastAssumptions z0 z1) :
    S.reducedFormContrast z0 z1 =
      ∑ j : Fin J, S.indicatorWeightedEffect z0 z1 j := by
  unfold reducedFormContrast YofDofZ indicatorWeightedEffect
  have hpoint :
      (fun ω => S.YofD (S.DofZ z1 ω) ω - S.YofD (S.DofZ z0 ω) ω)
        =ᵐ[P.μ]
      fun ω => ∑ j : Fin J, S.marginResponse j ω *
        OrderedTreatment.crossingIndicator (S.DofZ z0 ω) (S.DofZ z1 ω) j :=
    hValid.hMonotone.mono fun ω hmono => by
      simpa [OrderedTreatment.marginIncrement, marginResponse] using
        OrderedTreatment.ordered_telescope_indicator
          (J := J) (fun d : Fin (J + 1) => S.YofD d ω) hmono
  calc
    ∫ ω, (S.YofD (S.DofZ z1 ω) ω - S.YofD (S.DofZ z0 ω) ω) ∂P.μ
        = ∫ ω, ∑ j : Fin J, S.marginResponse j ω *
            OrderedTreatment.crossingIndicator (S.DofZ z0 ω) (S.DofZ z1 ω) j ∂P.μ := by
          exact MeasureTheory.integral_congr_ae hpoint
    _ = ∑ j : Fin J, ∫ ω, S.marginResponse j ω *
            OrderedTreatment.crossingIndicator (S.DofZ z0 ω) (S.DofZ z1 ω) j ∂P.μ := by
          rw [MeasureTheory.integral_finset_sum]
          intro i _hi
          rw [S.marginResponse_mul_crossingIndicator_eq_indicator z0 z1 i]
          exact (S.integrable_marginResponse hValid i).indicator
            (S.measurableSet_crossingEvent z0 z1 i)
    _ = ∑ j : Fin J, ∫ ω in S.crossingEvent z0 z1 j, S.marginResponse j ω ∂P.μ := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          rw [S.marginResponse_mul_crossingIndicator_eq_indicator z0 z1 j]
          rw [MeasureTheory.integral_indicator (S.measurableSet_crossingEvent z0 z1 j)]

/-- **Indicator-weighted and conditional-mean ACR forms agree.** In [a variable-intensity IV
system](hyp:S), for [any pair of instrument values](hyp:z0,z1), [the ratio of total causal-response
contributions on crossed margins to total crossing probability equals the
crossing-probability-weighted average of margin-specific conditional causal responses](goal).

The identity follows because each crossing-event integral is its event probability times its
normalized restricted mean, including under the library's total convention for null events. It
does not require the contrast-validity assumptions. -/
theorem indicatorWeightedACR_eq_averageCausalResponse {z0 z1 : 𝒵} :
    S.indicatorWeightedACR z0 z1 = S.averageCausalResponse z0 z1 := by
  simp only [indicatorWeightedACR, averageCausalResponse, crossingWeight,
    OrderedTreatment.normalizedWeight,
    Causalean.Stat.Weighted.NormalizedWeights.normalizedWeight, totalCrossingProb,
    conditionalMarginResponse, unnormalizedACRContrast, indicatorWeightedEffect, crossingProb]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [← eventCondExp_mul_measure_toReal P.μ (S.crossingEvent z0 z1 j)
    (measure_ne_top _ _) (S.marginResponse j)]
  ring_nf

/-- **Directed-pair Wald average-causal-response specialization.** Under [the
variable-intensity IV validity assumptions](hyp:hValid), with [the instrument cell
`Z = z0` having positive probability](hyp:hCell0) and [the instrument cell `Z = z1`
having positive probability](hyp:hCell1), [the directed Wald estimand — the ratio of the
reduced-form to first-stage conditional-mean contrasts across the two instrument cells —
equals the directed-pair average causal response: the crossing-probability-weighted
average, over treatment-intensity margins, of the conditional mean causal response among units
whose dose crosses that margin under the directed instrument contrast](goal).

This is the pairwise Wald special case of the Angrist--Imbens causal-response
algebra; it is not the general population 2SLS characterization for a
multivalued instrument. -/
theorem directedPairWald_eq_averageCausalResponse {z0 z1 : 𝒵}
    (hValid : S.ValidContrastAssumptions z0 z1)
    (hCell0 : 0 < (P.μ (S.zEvent z0)).toReal)
    (hCell1 : 0 < (P.μ (S.zEvent z1)).toReal) :
    S.wald z0 z1 = S.averageCausalResponse z0 z1 := by
  have hDZ0 := S.condExpDZ_left_eq_integral hValid hCell0
  have hDZ1 := S.condExpDZ_right_eq_integral hValid hCell1
  have hYZ0 := S.condExpYZ_left_eq_integral hValid hCell0
  have hYZ1 := S.condExpYZ_right_eq_integral hValid hCell1
  have hDint0 := S.integrable_intensityValue_DofZ z0
  have hDint1 := S.integrable_intensityValue_DofZ z1
  have hYint0 := S.integrable_YofDofZ hValid z0
  have hYint1 := S.integrable_YofDofZ hValid z1
  unfold wald
  rw [hYZ1, hYZ0, hDZ1, hDZ0]
  rw [← MeasureTheory.integral_sub hYint1 hYint0,
    ← MeasureTheory.integral_sub hDint1 hDint0]
  change S.reducedFormContrast z0 z1 / S.firstStageContrast z0 z1 =
    S.averageCausalResponse z0 z1
  rw [← S.indicatorWeightedACR_eq_averageCausalResponse]
  simp [indicatorWeightedACR, unnormalizedACRContrast, totalCrossingProb,
    S.reducedForm_eq_sum_crossingEffects hValid, S.firstStage_eq_sum_crossingProb hValid]

end VariableIntensityIVSystem
end
end VariableIntensityIV
end PO.ID.Exact
end Causalean
