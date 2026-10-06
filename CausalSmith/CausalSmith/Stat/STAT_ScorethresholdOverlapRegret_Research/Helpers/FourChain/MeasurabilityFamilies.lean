module
public import Causalean.Stat.EmpiricalProcess.Countable
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.FourChain.Decomposition
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.ScoreIdentity
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Score-threshold overlap regret — measurable policy families

Supported scores and comparison integrands are measurable. Jointly Borel policy
families have measurable empirical evaluations, population centers, losses, and
localized countable suprema, including cutoff families augmented by observed
scores.
-/

public section

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.ScorethresholdOverlapRegret

open MeasureTheory
open scoped BigOperators ENNReal

/-- The supplied logger makes the deleted score Borel on supported observations. -/
-- @node: zScore_supported_measurable
@[fun_prop] lemma zScore_supported_measurable (P : RowLaw) (a : ℝ)
    (hP : WellFormed P) :
    Measurable (fun o : {o : Observation //
      o.X ∈ Set.Icc (0 : ℝ) 1 ∧ o.Y ∈ Set.Icc (-1 : ℝ) 1} =>
      zScore a P.logger o.1) := by
  have hobs : Measurable (fun o : Observation => (o.X, o.A, o.Y)) :=
    comap_measurable _
  let Ω := {o : Observation //
    o.X ∈ Set.Icc (0 : ℝ) 1 ∧ o.Y ∈ Set.Icc (-1 : ℝ) 1}
  have hco : Measurable (fun o : Ω => o.1) := measurable_subtype_coe
  have hX := hobs.fst.comp hco
  have hA := hobs.snd.fst.comp hco
  have hY := hobs.snd.snd.comp hco
  have he : Measurable (fun o : {o : Observation //
      o.X ∈ Set.Icc (0 : ℝ) 1 ∧ o.Y ∈ Set.Icc (-1 : ℝ) 1} =>
      P.logger o.1.X) :=
    hP.2.2.2.1.comp (hX.subtype_mk (h := fun o => o.2.1))
  have hp : Measurable (fun o : Ω => min (P.logger o.1.X) (1 - P.logger o.1.X)) :=
    he.min (measurable_const.sub he)
  unfold zScore gammaScore offsetG
  apply Measurable.add
  · apply Measurable.ite (measurableSet_le measurable_const hp)
    · apply Measurable.ite (hA (measurableSet_singleton true))
      · exact hY.div he
      · exact (hY.div (measurable_const.sub he)).neg
    · fun_prop
  · exact measurable_const.min (measurable_const.div hp)

/-- The canonical policy is Borel on the score support, including zero-effect ties. -/
-- @node: canonicalPolicy_supported_measurable
@[fun_prop] lemma canonicalPolicy_supported_measurable (P : RowLaw)
    (hP : WellFormed P) :
    Measurable (fun x : Set.Icc (0 : ℝ) 1 => canonicalPolicy P x.1) := by
  change Measurable (fun x : Set.Icc (0 : ℝ) 1 =>
    if 0 ≤ P.tau x.1 then true else false)
  exact Measurable.ite (measurableSet_le measurable_const hP.2.2.2.2.1)
    measurable_const measurable_const

/-- Every fixed Borel policy has a measurable comparison score on supported rows. -/
-- @node: comparisonIntegrand_supported_measurable
@[fun_prop] lemma comparisonIntegrand_supported_measurable (P : RowLaw) (a : ℝ)
    (hP : WellFormed P) (π : ℝ → Bool) (hπ : π ∈ binaryPolicyClass) :
    Measurable (fun o : {o : Observation //
      o.X ∈ Set.Icc (0 : ℝ) 1 ∧ o.Y ∈ Set.Icc (-1 : ℝ) 1} =>
      comparisonIntegrand P a π o.1) := by
  have hobs : Measurable (fun o : Observation => (o.X, o.A, o.Y)) :=
    comap_measurable _
  have hX := (hobs.fst.comp measurable_subtype_coe).subtype_mk
    (h := fun o : {o : Observation //
      o.X ∈ Set.Icc (0 : ℝ) 1 ∧ o.Y ∈ Set.Icc (-1 : ℝ) 1} => o.2.1)
  have hπX := hπ.comp hX
  have hstar := (canonicalPolicy_supported_measurable P hP).comp hX
  unfold comparisonIntegrand
  exact ((Measurable.ite (hπX (measurableSet_singleton true))
    measurable_const measurable_const).sub
    (Measurable.ite (hstar (measurableSet_singleton true))
      measurable_const measurable_const)).mul (zScore_supported_measurable P a hP)

/-- A fixed policy's absolute centered empirical comparison is Borel in the data. -/
-- @node: centeredComparison_supported_measurable
@[fun_prop] lemma centeredComparison_supported_measurable {n : ℕ}
    (P : RowLaw) (a : ℝ) (hP : WellFormed P)
    (π : ℝ → Bool) (hπ : π ∈ binaryPolicyClass) :
    Measurable (fun d : Fin n → {o : Observation //
        o.X ∈ Set.Icc (0 : ℝ) 1 ∧ o.Y ∈ Set.Icc (-1 : ℝ) 1} =>
      |empiricalAverage (comparisonIntegrand P a π) (fun i => (d i).1) -
        ∫ o, comparisonIntegrand P a π o ∂P.obsLaw|) := by
  unfold empiricalAverage
  simp only [← Real.norm_eq_abs]
  apply Measurable.norm
  apply Measurable.sub _ measurable_const
  apply Measurable.mul measurable_const
  exact Finset.measurable_sum _ (fun i _ =>
    (comparisonIntegrand_supported_measurable P a hP π hπ).comp
      (measurable_pi_apply i))

/-- Any fixed countable skeleton of threshold comparisons has a Borel supremum.
The localization constraint is retained as a subtype of the skeleton. -/
-- @node: countableLocalizedProcess_measurable
@[fun_prop] lemma countableLocalizedProcess_measurable {n : ℕ}
    {ι : Type*} [Countable ι] (P : RowLaw) (a z : ℝ) (hP : WellFormed P)
    (π : ι → ℝ → Bool) (hπ : ∀ i, π i ∈ thresholdClass) :
    Measurable (fun d : Fin n → {o : Observation //
        o.X ∈ Set.Icc (0 : ℝ) 1 ∧ o.Y ∈ Set.Icc (-1 : ℝ) 1} =>
      ⨆ i : {i : ι // regularizedLoss P a (π i) ≤ z},
        |empiricalAverage (comparisonIntegrand P a (π i.1)) (fun j => (d j).1) -
          ∫ o, comparisonIntegrand P a (π i.1) o ∂P.obsLaw|) := by
  exact Measurable.iSup (fun i => centeredComparison_supported_measurable P a hP
    (π i.1) (thresholdClass_mem_binaryPolicyClass _ (hπ i.1)))

/-- Joint Borel policy evaluation gives joint Borel comparison scores on supported rows. -/
-- @node: comparisonIntegrand_family_supported_measurable
@[fun_prop] lemma comparisonIntegrand_family_supported_measurable
    {Ω : Type*} [MeasurableSpace Ω] (P : RowLaw) (a : ℝ) (hP : WellFormed P)
    (π : Ω → ℝ → Bool)
    (hπ : Measurable (fun q : Ω × Set.Icc (0 : ℝ) 1 => π q.1 q.2.1)) :
    Measurable (fun q : Ω × {o : Observation //
        o.X ∈ Set.Icc (0 : ℝ) 1 ∧ o.Y ∈ Set.Icc (-1 : ℝ) 1} =>
      comparisonIntegrand P a (π q.1) q.2.1) := by
  have hX : Measurable (fun q : Ω × {o : Observation //
      o.X ∈ Set.Icc (0 : ℝ) 1 ∧ o.Y ∈ Set.Icc (-1 : ℝ) 1} =>
      (⟨q.2.1.X, q.2.2.1⟩ : Set.Icc (0 : ℝ) 1)) :=
    (score_observation_X_measurable.comp
    (measurable_subtype_coe.comp measurable_snd)).subtype_mk
    (h := fun q : Ω × {o : Observation //
      o.X ∈ Set.Icc (0 : ℝ) 1 ∧ o.Y ∈ Set.Icc (-1 : ℝ) 1} => q.2.2.1)
  have heval := hπ.comp (measurable_fst.prodMk hX)
  have hstar := (canonicalPolicy_supported_measurable P hP).comp hX
  unfold comparisonIntegrand
  exact ((Measurable.ite (heval (measurableSet_singleton true))
    measurable_const measurable_const).sub
    (Measurable.ite (hstar (measurableSet_singleton true))
      measurable_const measurable_const)).mul
      ((zScore_supported_measurable P a hP).comp measurable_snd)

/-- Population centering is Borel for any jointly Borel family of policies.
Restricting to the supported observation subtype preserves the original integral. -/
-- @node: populationComparison_family_measurable
@[fun_prop] lemma populationComparison_family_measurable
    {Ω : Type*} [MeasurableSpace Ω] (P : RowLaw) (a : ℝ) (hP : WellFormed P)
    (π : Ω → ℝ → Bool)
    (hπ : Measurable (fun q : Ω × Set.Icc (0 : ℝ) 1 => π q.1 q.2.1)) :
    Measurable (fun w => ∫ o, comparisonIntegrand P a (π w) o ∂P.obsLaw) := by
  have : IsProbabilityMeasure P.full := hP.1
  have : IsProbabilityMeasure P.obsLaw :=
    Measure.isProbabilityMeasure_map score_observation_map_measurable.aemeasurable
  let B : Set Observation := {o | o.X ∈ Set.Icc (0 : ℝ) 1 ∧
    o.Y ∈ Set.Icc (-1 : ℝ) 1}
  have hcoords : Measurable (fun o : Observation => (o.X, o.A, o.Y)) :=
    comap_measurable _
  have hB : MeasurableSet B :=
    (hcoords.fst measurableSet_Icc).inter (hcoords.snd.snd measurableSet_Icc)
  have hs : ∀ᵐ o ∂P.obsLaw, o ∈ B := by
    apply (ae_map_iff score_observation_map_measurable.aemeasurable hB).2
    exact (ae_iff.mpr hP.2.1).and (ae_iff.mpr hP.2.2.1)
  have hm := comparisonIntegrand_family_supported_measurable P a hP π hπ
  have hi := hm.stronglyMeasurable.integral_prod_right'
    (ν := Measure.comap (Subtype.val : B → Observation) P.obsLaw)
  have heq (w : Ω) : (∫ o, comparisonIntegrand P a (π w) o ∂P.obsLaw) =
      ∫ o : B, comparisonIntegrand P a (π w) o.1
        ∂Measure.comap Subtype.val P.obsLaw := by
    rw [integral_subtype_comap hB,
      Measure.restrict_eq_self_of_ae_mem hs]
  simp_rw [heq]
  exact hi.measurable

/-- A Borel cutoff gives jointly Borel right-threshold labels, retaining equality. -/
-- @node: rightThr_parameter_measurable
@[fun_prop] lemma rightThr_parameter_measurable
    {Ω : Type*} [MeasurableSpace Ω] (t : Ω → ℝ) (ht : Measurable t) :
    Measurable (fun q : Ω × Set.Icc (0 : ℝ) 1 => rightThr (t q.1) q.2.1) := by
  change Measurable (fun q : Ω × Set.Icc (0 : ℝ) 1 =>
    if t q.1 ≤ q.2.1 then true else false)
  exact Measurable.ite (measurableSet_le (ht.comp measurable_fst)
    (measurable_subtype_coe.comp measurable_snd)) measurable_const measurable_const

/-- A Borel cutoff gives jointly Borel left-threshold labels, retaining equality. -/
-- @node: leftThr_parameter_measurable
@[fun_prop] lemma leftThr_parameter_measurable
    {Ω : Type*} [MeasurableSpace Ω] (t : Ω → ℝ) (ht : Measurable t) :
    Measurable (fun q : Ω × Set.Icc (0 : ℝ) 1 => leftThr (t q.1) q.2.1) := by
  change Measurable (fun q : Ω × Set.Icc (0 : ℝ) 1 =>
    if q.2.1 ≤ t q.1 then true else false)
  exact Measurable.ite (measurableSet_le
    (measurable_subtype_coe.comp measurable_snd) (ht.comp measurable_fst))
    measurable_const measurable_const

/-- A policy depending jointly on the data and score has a Borel centered
comparison, including its population centering at the data-dependent policy. -/
-- @node: centeredComparison_family_supported_measurable
@[fun_prop] lemma centeredComparison_family_supported_measurable {n : ℕ}
    (P : RowLaw) (a : ℝ) (hP : WellFormed P)
    (π : (Fin n → {o : Observation //
      o.X ∈ Set.Icc (0 : ℝ) 1 ∧ o.Y ∈ Set.Icc (-1 : ℝ) 1}) → ℝ → Bool)
    (hπ : Measurable (fun q : (Fin n → {o : Observation //
        o.X ∈ Set.Icc (0 : ℝ) 1 ∧ o.Y ∈ Set.Icc (-1 : ℝ) 1}) ×
        Set.Icc (0 : ℝ) 1 => π q.1 q.2.1)) :
    Measurable (fun d =>
      |empiricalAverage (comparisonIntegrand P a (π d)) (fun i => (d i).1) -
        ∫ o, comparisonIntegrand P a (π d) o ∂P.obsLaw|) := by
  have hm := comparisonIntegrand_family_supported_measurable P a hP π hπ
  have he (i : Fin n) : Measurable (fun d =>
      comparisonIntegrand P a (π d) (d i).1) :=
    hm.comp (measurable_id.prodMk (measurable_pi_apply i))
  have havg : Measurable (fun d =>
      empiricalAverage (comparisonIntegrand P a (π d)) (fun i => (d i).1)) := by
    unfold empiricalAverage
    exact measurable_const.mul (Finset.measurable_sum _ (fun i _ => he i))
  simpa only [Real.norm_eq_abs, Pi.sub_apply] using
    (havg.sub (populationComparison_family_measurable P a hP π hπ)).norm

/-- Every observed score can be used as a Borel cutoff in either orientation.
This is the data-dependent part of the atom-safe countable cutoff skeleton. -/
-- @node: observedCutoff_centeredComparison_measurable
lemma observedCutoff_centeredComparison_measurable {n : ℕ}
    (P : RowLaw) (a : ℝ) (hP : WellFormed P) (j : Fin n) :
    Measurable (fun d : Fin n → {o : Observation //
        o.X ∈ Set.Icc (0 : ℝ) 1 ∧ o.Y ∈ Set.Icc (-1 : ℝ) 1} =>
      |empiricalAverage (comparisonIntegrand P a (rightThr (d j).1.X))
          (fun i => (d i).1) -
        ∫ o, comparisonIntegrand P a (rightThr (d j).1.X) o ∂P.obsLaw|) ∧
    Measurable (fun d : Fin n → {o : Observation //
        o.X ∈ Set.Icc (0 : ℝ) 1 ∧ o.Y ∈ Set.Icc (-1 : ℝ) 1} =>
      |empiricalAverage (comparisonIntegrand P a (leftThr (d j).1.X))
          (fun i => (d i).1) -
        ∫ o, comparisonIntegrand P a (leftThr (d j).1.X) o ∂P.obsLaw|) := by
  have ht : Measurable (fun d : Fin n → {o : Observation //
      o.X ∈ Set.Icc (0 : ℝ) 1 ∧ o.Y ∈ Set.Icc (-1 : ℝ) 1} => (d j).1.X) :=
    score_observation_X_measurable.comp
      (measurable_subtype_coe.comp (measurable_pi_apply j))
  exact ⟨centeredComparison_family_supported_measurable P a hP _
      (rightThr_parameter_measurable _ ht),
    centeredComparison_family_supported_measurable P a hP _
      (leftThr_parameter_measurable _ ht)⟩

/-- Integrating a jointly Borel score family preserves parameter measurability.
Only values on the supported score interval enter the population integral. -/
-- @node: scoreIntegral_family_measurable
lemma scoreIntegral_family_measurable
    {Ω : Type*} [MeasurableSpace Ω] (P : RowLaw) (hP : WellFormed P)
    (f : Ω → ℝ → ℝ)
    (hf : Measurable (fun q : Ω × Set.Icc (0 : ℝ) 1 => f q.1 q.2.1)) :
    Measurable (fun w => ∫ x, f w x ∂P.PX) := by
  have : IsProbabilityMeasure P.full := hP.1
  have : IsProbabilityMeasure P.PX :=
    Measure.isProbabilityMeasure_map fullRow_X_measurable.aemeasurable
  have hs : ∀ᵐ x ∂P.PX, x ∈ Set.Icc (0 : ℝ) 1 :=
    (ae_map_iff fullRow_X_measurable.aemeasurable measurableSet_Icc).2
      (ae_iff.mpr hP.2.1)
  have hi := hf.stronglyMeasurable.integral_prod_right'
    (ν := Measure.comap (Subtype.val : Set.Icc (0 : ℝ) 1 → ℝ) P.PX)
  have heq (w : Ω) : (∫ x, f w x ∂P.PX) =
      ∫ x : Set.Icc (0 : ℝ) 1, f w x.1 ∂Measure.comap Subtype.val P.PX := by
    rw [integral_subtype_comap measurableSet_Icc,
      Measure.restrict_eq_self_of_ae_mem hs]
  simp_rw [heq]
  exact hi.measurable

/-- Population welfare is Borel for a jointly Borel family of binary rules. -/
-- @node: rawWelfare_family_measurable
@[fun_prop] lemma rawWelfare_family_measurable
    {Ω : Type*} [MeasurableSpace Ω] (P : RowLaw) (hP : WellFormed P)
    (π : Ω → ℝ → Bool)
    (hπ : Measurable (fun q : Ω × Set.Icc (0 : ℝ) 1 => π q.1 q.2.1)) :
    Measurable (fun w => rawWelfare P (π w)) := by
  unfold rawWelfare
  apply scoreIntegral_family_measurable P hP
  exact (Measurable.ite (hπ (measurableSet_singleton true))
    measurable_const measurable_const).mul
      (hP.2.2.2.2.1.comp measurable_snd)

/-- Population regret is Borel for a jointly Borel family of binary rules. -/
-- @node: rawRegret_family_measurable_of_wellFormed
@[fun_prop] lemma rawRegret_family_measurable_of_wellFormed
    {Ω : Type*} [MeasurableSpace Ω] (P : RowLaw) (hP : WellFormed P)
    (π : Ω → ℝ → Bool)
    (hπ : Measurable (fun q : Ω × Set.Icc (0 : ℝ) 1 => π q.1 q.2.1)) :
    Measurable (fun w => rawRegret P (π w)) := by
  unfold rawRegret
  exact measurable_const.sub (rawWelfare_family_measurable P hP π hπ)

/-- The offset disagreement penalty is Borel in a jointly Borel policy parameter. -/
-- @node: offsetDisagreement_family_measurable
@[fun_prop] lemma offsetDisagreement_family_measurable
    {Ω : Type*} [MeasurableSpace Ω] (P : RowLaw) (a : ℝ) (hP : WellFormed P)
    (π : Ω → ℝ → Bool)
    (hπ : Measurable (fun q : Ω × Set.Icc (0 : ℝ) 1 => π q.1 q.2.1)) :
    Measurable (fun w => offsetDisagreement P a (π w)) := by
  unfold offsetDisagreement
  apply scoreIntegral_family_measurable P hP
  have he := hP.2.2.2.1.comp (measurable_snd :
    Measurable (Prod.snd : Ω × Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1))
  have hg : Measurable (fun q : Ω × Set.Icc (0 : ℝ) 1 =>
      offsetG a P.logger q.2.1) := by
    unfold offsetG
    exact measurable_const.min
      (measurable_const.div (he.min (measurable_const.sub he)))
  have hstar := (canonicalPolicy_supported_measurable P hP).comp
    (measurable_snd : Measurable (Prod.snd :
      Ω × Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1))
  exact hg.mul (Measurable.ite (measurableSet_eq_fun hπ hstar)
    measurable_const measurable_const)

/-- The localization loss is Borel in a jointly Borel policy parameter. -/
-- @node: regularizedLoss_family_measurable
@[fun_prop] lemma regularizedLoss_family_measurable
    {Ω : Type*} [MeasurableSpace Ω] (P : RowLaw) (a : ℝ) (hP : WellFormed P)
    (π : Ω → ℝ → Bool)
    (hπ : Measurable (fun q : Ω × Set.Icc (0 : ℝ) 1 => π q.1 q.2.1)) :
    Measurable (fun w => regularizedLoss P a (π w)) := by
  unfold regularizedLoss
  exact (rawRegret_family_measurable_of_wellFormed P hP π hπ).add
    (offsetDisagreement_family_measurable P a hP π hπ)

/-- A data-dependent policy's localization test is a Borel event. -/
-- @node: regularizedLoss_family_sublevel_measurableSet
lemma regularizedLoss_family_sublevel_measurableSet
    {Ω : Type*} [MeasurableSpace Ω] (P : RowLaw) (a z : ℝ) (hP : WellFormed P)
    (π : Ω → ℝ → Bool)
    (hπ : Measurable (fun q : Ω × Set.Icc (0 : ℝ) 1 => π q.1 q.2.1)) :
    MeasurableSet {w | regularizedLoss P a (π w) ≤ z} := by
  exact measurableSet_le (regularizedLoss_family_measurable P a hP π hπ)
    measurable_const

/-- A countable family of data-dependent cutoffs has a Borel localized maximum.
Ineligible policies contribute zero, the empty real supremum convention. This
allows observed scores to be added to a fixed atom and rational skeleton. -/
-- @node: countableDataLocalizedProcess_measurable
@[fun_prop] lemma countableDataLocalizedProcess_measurable {n : ℕ}
    {ι : Type*} [Countable ι] (P : RowLaw) (a z : ℝ) (hP : WellFormed P)
    (π : ι → (Fin n → {o : Observation //
      o.X ∈ Set.Icc (0 : ℝ) 1 ∧ o.Y ∈ Set.Icc (-1 : ℝ) 1}) → ℝ → Bool)
    (hπ : ∀ i, Measurable (fun q : (Fin n → {o : Observation //
        o.X ∈ Set.Icc (0 : ℝ) 1 ∧ o.Y ∈ Set.Icc (-1 : ℝ) 1}) ×
        Set.Icc (0 : ℝ) 1 => π i q.1 q.2.1)) :
    Measurable (fun d => ⨆ i, if regularizedLoss P a (π i d) ≤ z then
      |empiricalAverage (comparisonIntegrand P a (π i d)) (fun j => (d j).1) -
        ∫ o, comparisonIntegrand P a (π i d) o ∂P.obsLaw| else 0) := by
  apply Measurable.iSup
  intro i
  exact Measurable.ite
    (regularizedLoss_family_sublevel_measurableSet P a z hP (π i) (hπ i))
    (centeredComparison_family_supported_measurable P a hP (π i) (hπ i))
    measurable_const

/-- Any countable family of Borel cutoffs, including data-dependent cutoffs,
has Borel localized suprema in both threshold orientations. -/
-- @node: countableCutoffLocalizedProcess_measurable
lemma countableCutoffLocalizedProcess_measurable {n : ℕ}
    {ι : Type*} [Countable ι] (P : RowLaw) (a z : ℝ) (hP : WellFormed P)
    (t : ι → (Fin n → {o : Observation //
      o.X ∈ Set.Icc (0 : ℝ) 1 ∧ o.Y ∈ Set.Icc (-1 : ℝ) 1}) → ℝ)
    (ht : ∀ i, Measurable (t i)) :
    Measurable (fun d => ⨆ i, if regularizedLoss P a (rightThr (t i d)) ≤ z then
      |empiricalAverage (comparisonIntegrand P a (rightThr (t i d)))
          (fun j => (d j).1) -
        ∫ o, comparisonIntegrand P a (rightThr (t i d)) o ∂P.obsLaw| else 0) ∧
    Measurable (fun d => ⨆ i, if regularizedLoss P a (leftThr (t i d)) ≤ z then
      |empiricalAverage (comparisonIntegrand P a (leftThr (t i d)))
          (fun j => (d j).1) -
        ∫ o, comparisonIntegrand P a (leftThr (t i d)) o ∂P.obsLaw| else 0) := by
  exact ⟨countableDataLocalizedProcess_measurable P a z hP _
      (fun i => rightThr_parameter_measurable (t i) (ht i)),
    countableDataLocalizedProcess_measurable P a z hP _
      (fun i => leftThr_parameter_measurable (t i) (ht i))⟩

/-- Augmenting a fixed countable cutoff skeleton by every observed score
preserves measurability after localization in both orientations. Population
atom locations, oracle cutoffs, and endpoints can all be included in `t`. -/
-- @node: augmentedCutoffLocalizedProcess_measurable
lemma augmentedCutoffLocalizedProcess_measurable {n : ℕ}
    {ι : Type*} [Countable ι] (P : RowLaw) (a z : ℝ) (hP : WellFormed P)
    (t : ι → ℝ) :
    let cutoff : ι ⊕ Fin n → (Fin n → {o : Observation //
        o.X ∈ Set.Icc (0 : ℝ) 1 ∧ o.Y ∈ Set.Icc (-1 : ℝ) 1}) → ℝ :=
      fun i d => Sum.elim t (fun j => (d j).1.X) i
    Measurable (fun d => ⨆ i, if regularizedLoss P a (rightThr (cutoff i d)) ≤ z then
      |empiricalAverage (comparisonIntegrand P a (rightThr (cutoff i d)))
          (fun j => (d j).1) -
        ∫ o, comparisonIntegrand P a (rightThr (cutoff i d)) o ∂P.obsLaw| else 0) ∧
    Measurable (fun d => ⨆ i, if regularizedLoss P a (leftThr (cutoff i d)) ≤ z then
      |empiricalAverage (comparisonIntegrand P a (leftThr (cutoff i d)))
          (fun j => (d j).1) -
        ∫ o, comparisonIntegrand P a (leftThr (cutoff i d)) o ∂P.obsLaw| else 0) := by
  apply countableCutoffLocalizedProcess_measurable P a z hP
  intro i
  cases i with
  | inl i => exact measurable_const
  | inr j =>
    exact score_observation_X_measurable.comp
      (measurable_subtype_coe.comp (measurable_pi_apply j))

end CausalSmith.Stat.ScorethresholdOverlapRegret

