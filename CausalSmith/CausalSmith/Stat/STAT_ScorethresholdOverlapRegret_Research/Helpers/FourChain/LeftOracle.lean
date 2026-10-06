module
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.FourChain.WitnessAdapter

/-! # Left-oracle five-chain adapter

This module mirrors the atom-safe right-oracle construction for a canonical
left threshold.  Half-open endpoints are chosen to preserve the policy's tie
convention at atoms.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal

namespace CausalSmith.Stat.ScorethresholdOverlapRegret

def leftSameBelowSet (c t : ℝ) : Set SupportedObservation :=
  {o | o.1.X ∈ Set.Ioc t c}

def leftSameAboveSet (c t : ℝ) : Set SupportedObservation :=
  {o | o.1.X ∈ Set.Ioc c t}

def leftOppBelowSet (c t : ℝ) : Set SupportedObservation :=
  {o | o.1.X ∈ Set.Ico 0 t ∪ Set.Ioc c 1}

def leftOppAboveSet (c t : ℝ) : Set SupportedObservation :=
  {o | o.1.X ∈ Set.Icc 0 c ∪ Set.Icc t 1}

def leftZeroSet (c : ℝ) : Set SupportedObservation :=
  {o | o.1.X ∈ Set.Icc 0 c}

noncomputable def leftOracleWeight (P : RowLaw) (a c : ℝ)
    (o : SupportedObservation) : ℝ :=
  (if o.1.X ≤ c then (1 : ℝ) else -1) * zScore a P.logger o.1

noncomputable def leftOracleOffset (P : RowLaw) (a c : ℝ)
    (o : SupportedObservation) : ℝ :=
  (if leftThr c o.1.X then (1 : ℝ) else 0) * zScore a P.logger o.1

noncomputable def leftOracleMark (P : RowLaw) (a : ℝ)
    (o : SupportedObservation) : ℝ :=
  -zScore a P.logger o.1

@[fun_prop] lemma leftOracleWeight_measurable (P : RowLaw) (a c : ℝ)
    (hP : WellFormed P) : Measurable (leftOracleWeight P a c) := by
  unfold leftOracleWeight
  exact (Measurable.ite
    (measurableSet_le supportedObservation_X_measurable measurable_const)
    measurable_const measurable_const).mul (zScore_supported_measurable P a hP)

@[fun_prop] lemma leftOracleOffset_measurable (P : RowLaw) (a c : ℝ)
    (hP : WellFormed P) : Measurable (leftOracleOffset P a c) := by
  have hm : Measurable (fun o : SupportedObservation =>
      if o.1.X ≤ c then (1 : ℝ) else 0) := Measurable.ite
    (measurableSet_le supportedObservation_X_measurable measurable_const)
    measurable_const measurable_const
  have heq : leftOracleOffset P a c = fun o : SupportedObservation =>
      (if o.1.X ≤ c then (1 : ℝ) else 0) * zScore a P.logger o.1 := by
    funext o
    by_cases h : o.1.X ≤ c <;> simp [leftOracleOffset, leftThr, h]
  rw [heq]
  exact hm.mul (zScore_supported_measurable P a hP)

@[fun_prop] lemma leftOracleMark_measurable (P : RowLaw) (a : ℝ)
    (hP : WellFormed P) : Measurable (leftOracleMark P a) :=
  (zScore_supported_measurable P a hP).neg

lemma leftOracleWeight_abs_le (P : RowLaw) (a c : ℝ)
    (ha : 0 < a ∧ a ≤ 1 / 4)
    (hlogger : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      P.logger x ∈ Set.Ioo (0 : ℝ) 1) (o : SupportedObservation) :
    |leftOracleWeight P a c o| ≤ 2 / a := by
  unfold leftOracleWeight
  rw [abs_mul]
  have hz := zScore_abs_le a P.logger o.1 ha (hlogger o.1.X o.2.1) o.2.2
  split_ifs <;> simpa using hz

lemma leftOracleOffset_abs_le (P : RowLaw) (a c : ℝ)
    (ha : 0 < a ∧ a ≤ 1 / 4)
    (hlogger : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      P.logger x ∈ Set.Ioo (0 : ℝ) 1) (o : SupportedObservation) :
    |leftOracleOffset P a c o| ≤ 2 / a := by
  have hK : 0 ≤ 2 / a := div_nonneg (by norm_num) ha.1.le
  have hz := zScore_abs_le a P.logger o.1 ha (hlogger o.1.X o.2.1) o.2.2
  by_cases h : leftThr c o.1.X = true
  · simpa [leftOracleOffset, h] using hz
  · simpa [leftOracleOffset, h] using hK

lemma leftOracleMark_abs_le (P : RowLaw) (a : ℝ)
    (ha : 0 < a ∧ a ≤ 1 / 4)
    (hlogger : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      P.logger x ∈ Set.Ioo (0 : ℝ) 1) (o : SupportedObservation) :
    |leftOracleMark P a o| ≤ 2 / a := by
  simpa [leftOracleMark] using
    zScore_abs_le a P.logger o.1 ha (hlogger o.1.X o.2.1) o.2.2

lemma leftOracleOffset_integrable (P : RowLaw) (a c : ℝ)
    (hP : WellFormed P) (ha : 0 < a ∧ a ≤ 1 / 4)
    (hlogger : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      P.logger x ∈ Set.Ioo (0 : ℝ) 1)
    [IsProbabilityMeasure (supportedObsLaw P)] :
    Integrable (leftOracleOffset P a c) (supportedObsLaw P) :=
  Integrable.of_bound (leftOracleOffset_measurable P a c hP).aestronglyMeasurable
    (2 / a) (ae_of_all _ (leftOracleOffset_abs_le P a c ha hlogger))

lemma leftOracleMark_integrable (P : RowLaw) (a : ℝ)
    (hP : WellFormed P) (ha : 0 < a ∧ a ≤ 1 / 4)
    (hlogger : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      P.logger x ∈ Set.Ioo (0 : ℝ) 1)
    [IsProbabilityMeasure (supportedObsLaw P)] :
    Integrable (leftOracleMark P a) (supportedObsLaw P) :=
  Integrable.of_bound (leftOracleMark_measurable P a hP).aestronglyMeasurable
    (2 / a) (ae_of_all _ (leftOracleMark_abs_le P a ha hlogger))

lemma leftThresholdFunction_eq_witnessComparison (P : RowLaw)
    (a c t : ℝ) (upper : Bool) :
    Causalean.Stat.EmpiricalProcess.Countable.thresholdFunction upper
      (fun o : SupportedObservation => o.1.X) (leftOracleOffset P a c)
      (leftOracleMark P a) t =
      fun o => witnessComparisonIntegrand P a (leftThr c)
        (if upper then leftThr t else rightThr t) o.1 := by
  funext o
  cases upper <;>
    simp [Causalean.Stat.EmpiricalProcess.Countable.thresholdFunction,
      leftOracleOffset, leftOracleMark, witnessComparisonIntegrand,
      leftThr, rightThr] <;>
    split_ifs <;> ring

lemma witnessComparison_left_same_below (P : RowLaw) (a c t : ℝ)
    (ht : t < c) :
    (fun o : SupportedObservation =>
      witnessComparisonIntegrand P a (leftThr c) (leftThr t) o.1) =
      (leftSameBelowSet c t).indicator (leftOracleWeight P a c) := by
  funext o
  have hx := o.2.1
  by_cases hxt : o.1.X ≤ t
  · have hxc : o.1.X ≤ c := by linarith
    simp [witnessComparisonIntegrand, leftOracleWeight, leftSameBelowSet,
      Set.indicator, leftThr, hxt, hxc]
  · by_cases hxc : o.1.X ≤ c
    · have hmem : o.1.X ∈ Set.Ioc t c := ⟨lt_of_not_ge hxt, hxc⟩
      rw [Set.indicator_of_mem
        (show o ∈ leftSameBelowSet c t from hmem)]
      simp [witnessComparisonIntegrand, leftOracleWeight, leftThr, hxt, hxc]
    · have hmem : o.1.X ∉ Set.Ioc t c := fun h => hxc h.2
      rw [Set.indicator_of_notMem
        (show o ∉ leftSameBelowSet c t from hmem)]
      simp [witnessComparisonIntegrand, leftOracleWeight, leftThr, hxt, hxc]

lemma witnessComparison_left_same_above (P : RowLaw) (a c t : ℝ)
    (ht : c ≤ t) :
    (fun o : SupportedObservation =>
      witnessComparisonIntegrand P a (leftThr c) (leftThr t) o.1) =
      (leftSameAboveSet c t).indicator (leftOracleWeight P a c) := by
  funext o
  by_cases hxc : o.1.X ≤ c
  · have hxt : o.1.X ≤ t := hxc.trans ht
    simp [witnessComparisonIntegrand, leftOracleWeight, leftSameAboveSet,
      Set.indicator, leftThr, hxc, hxt]
  · by_cases hxt : o.1.X ≤ t
    · have hmem : o.1.X ∈ Set.Ioc c t := ⟨lt_of_not_ge hxc, hxt⟩
      rw [Set.indicator_of_mem
        (show o ∈ leftSameAboveSet c t from hmem)]
      simp [witnessComparisonIntegrand, leftOracleWeight, leftThr, hxc, hxt]
    · have hmem : o.1.X ∉ Set.Ioc c t := fun h => hxt h.2
      rw [Set.indicator_of_notMem
        (show o ∉ leftSameAboveSet c t from hmem)]
      simp [witnessComparisonIntegrand, leftOracleWeight, leftThr, hxc, hxt]

lemma witnessComparison_left_opp_below (P : RowLaw) (a c t : ℝ)
    (ht : t ≤ c) :
    (fun o : SupportedObservation =>
      witnessComparisonIntegrand P a (leftThr c) (rightThr t) o.1) =
      (leftOppBelowSet c t).indicator (leftOracleWeight P a c) := by
  funext o
  have hx := o.2.1
  by_cases htx : t ≤ o.1.X
  · by_cases hxc : o.1.X ≤ c
    · have hnot : o.1.X ∉ Set.Ico 0 t ∪ Set.Ioc c 1 := by
        simp only [Set.mem_union, Set.mem_Ico, Set.mem_Ioc, not_or]
        exact ⟨fun h => (not_lt_of_ge htx) h.2,
          fun h => (not_lt_of_ge hxc) h.1⟩
      rw [Set.indicator_of_notMem
        (show o ∉ leftOppBelowSet c t from hnot)]
      simp [witnessComparisonIntegrand, leftOracleWeight,
        leftThr, rightThr, htx, hxc]
    · have hmem : o.1.X ∈ Set.Ico 0 t ∪ Set.Ioc c 1 :=
        Or.inr ⟨lt_of_not_ge hxc, hx.2⟩
      rw [Set.indicator_of_mem
        (show o ∈ leftOppBelowSet c t from hmem)]
      simp [witnessComparisonIntegrand, leftOracleWeight,
        leftThr, rightThr, htx, hxc]
  · have hxc : o.1.X ≤ c := by linarith
    have hmem : o.1.X ∈ Set.Ico 0 t ∪ Set.Ioc c 1 :=
      Or.inl ⟨hx.1, lt_of_not_ge htx⟩
    rw [Set.indicator_of_mem
      (show o ∈ leftOppBelowSet c t from hmem)]
    simp [witnessComparisonIntegrand, leftOracleWeight,
      leftThr, rightThr, htx, hxc]

lemma witnessComparison_left_opp_above (P : RowLaw) (a c t : ℝ)
    (ht : c < t) :
    (fun o : SupportedObservation =>
      witnessComparisonIntegrand P a (leftThr c) (rightThr t) o.1) =
      (leftOppAboveSet c t).indicator (leftOracleWeight P a c) := by
  funext o
  have hx := o.2.1
  by_cases hxc : o.1.X ≤ c
  · have hnt : ¬ t ≤ o.1.X := by linarith
    have hmem : o.1.X ∈ Set.Icc 0 c ∪ Set.Icc t 1 := Or.inl ⟨hx.1, hxc⟩
    rw [Set.indicator_of_mem
      (show o ∈ leftOppAboveSet c t from hmem)]
    simp [witnessComparisonIntegrand, leftOracleWeight,
      leftThr, rightThr, hxc, hnt]
  · by_cases htx : t ≤ o.1.X
    · have hmem : o.1.X ∈ Set.Icc 0 c ∪ Set.Icc t 1 := Or.inr ⟨htx, hx.2⟩
      rw [Set.indicator_of_mem
        (show o ∈ leftOppAboveSet c t from hmem)]
      simp [witnessComparisonIntegrand, leftOracleWeight,
        leftThr, rightThr, hxc, htx]
    · have hnot : o.1.X ∉ Set.Icc 0 c ∪ Set.Icc t 1 := by
        simp only [Set.mem_union, Set.mem_Icc, not_or]
        exact ⟨fun h => hxc h.2, fun h => htx h.1⟩
      rw [Set.indicator_of_notMem
        (show o ∉ leftOppAboveSet c t from hnot)]
      simp [witnessComparisonIntegrand, leftOracleWeight,
        leftThr, rightThr, hxc, htx]

lemma witnessComparison_left_zero (P : RowLaw) (a c : ℝ) :
    (fun o : SupportedObservation =>
      witnessComparisonIntegrand P a (leftThr c) (fun _ => false) o.1) =
      (leftZeroSet c).indicator (leftOracleWeight P a c) := by
  funext o
  have hx := o.2.1
  by_cases hxc : o.1.X ≤ c
  · have hmem : o.1.X ∈ Set.Icc 0 c := ⟨hx.1, hxc⟩
    rw [Set.indicator_of_mem (show o ∈ leftZeroSet c from hmem)]
    simp [witnessComparisonIntegrand, leftOracleWeight, leftThr, hxc]
  · have hnot : o.1.X ∉ Set.Icc 0 c := fun h => hxc h.2
    rw [Set.indicator_of_notMem (show o ∉ leftZeroSet c from hnot)]
    simp [witnessComparisonIntegrand, leftOracleWeight, leftThr, hxc]

structure LeftOracleLocalizedSkeleton (P : RowLaw) (a c z : ℝ)
    (upper : Bool) where
  D : Set ℝ
  countable : D.Countable
  subset : D ⊆ {t ∈ Set.Icc (0 : ℝ) 1 |
    regularizedLoss P a (if upper then leftThr t else rightThr t) ≤ z}
  reduction : ∀ (n : ℕ) (x : Fin n → SupportedObservation),
    Causalean.Stat.EmpiricalProcess.Countable.localizedThresholdSup
      (supportedObsLaw P) upper (fun o : SupportedObservation => o.1.X)
      (leftOracleOffset P a c) (leftOracleMark P a)
      (Set.Icc (0 : ℝ) 1)
      (fun t => regularizedLoss P a
        (if upper then leftThr t else rightThr t)) z x =
    Causalean.Stat.EmpiricalProcess.Countable.centeredSup
      (supportedObsLaw P)
      (fun t : D => Causalean.Stat.EmpiricalProcess.Countable.thresholdFunction
        upper (fun o : SupportedObservation => o.1.X)
        (leftOracleOffset P a c) (leftOracleMark P a) t.1) x

noncomputable def exists_leftOracle_localizedSkeletons
    (α γ θ : ℝ) (n : ℕ) (P : RowLaw) (e : ℝ → ℝ)
    (hP : LawClass α γ θ n P e) (a c z : ℝ)
    (ha : 0 < a ∧ a ≤ 1 / 4) :
    LeftOracleLocalizedSkeleton P a c z false ×
      LeftOracleLocalizedSkeleton P a c z true := by
  letI : IsProbabilityMeasure P.full := hP.wf.1
  letI : IsProbabilityMeasure P.obsLaw :=
    Measure.isProbabilityMeasure_map score_observation_map_measurable.aemeasurable
  letI : IsProbabilityMeasure (supportedObsLaw P) :=
    supportedObsLaw_isProbabilityMeasure P hP.wf
  have hlogger : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      P.logger x ∈ Set.Ioo (0 : ℝ) 1 := by
    intro x hx
    simpa only [hP.known hx] using hP.loggerSpace x hx
  have make (upper : Bool) : LeftOracleLocalizedSkeleton P a c z upper := by
    let R :=
      Causalean.Stat.EmpiricalProcess.Countable.localizedThreshold_countable_reduction
        (supportedObsLaw P) upper (fun o : SupportedObservation => o.1.X)
        (leftOracleOffset P a c) (leftOracleMark P a)
        supportedObservation_X_measurable
        (leftOracleOffset_integrable P a c hP.wf ha hlogger)
        (leftOracleMark_integrable P a hP.wf ha hlogger)
        (Set.Icc (0 : ℝ) 1)
        (fun t => regularizedLoss P a
          (if upper then leftThr t else rightThr t)) z
    let D := Classical.choose R
    have hD := Classical.choose_spec R
    exact ⟨D, hD.1, hD.2.1, hD.2.2.2.2⟩
  exact ⟨make false, make true⟩

lemma oracle_disagreement_mass_le_loss (α γ θ : ℝ) (n : ℕ)
    (P : RowLaw) (e : ℝ → ℝ) (hP : LawClass α γ θ n P e)
    (a : ℝ) (ha : 0 < a) (πstar π : ℝ → Bool)
    (hπ : π ∈ thresholdClass)
    (hstar : πstar =ᵐ[P.PX] canonicalPolicy P)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hdis : ∀ x ∈ Set.Icc (0 : ℝ) 1, (π x ≠ πstar x ↔ x ∈ B)) :
    (∫ x in B, offsetG a P.logger x ∂P.PX) ≤ regularizedLoss P a π := by
  have hs : ∀ᵐ x ∂P.PX, x ∈ Set.Icc (0 : ℝ) 1 := ae_iff.mpr hP.score.2
  have heq : B.indicator (offsetG a P.logger) =ᵐ[P.PX]
      fun x => offsetG a P.logger x *
        (if π x = canonicalPolicy P x then (0 : ℝ) else 1) := by
    filter_upwards [hs, hstar] with x hx hcanon
    by_cases hd : π x ≠ πstar x
    · have hxB := (hdis x hx).mp hd
      have hne : π x ≠ canonicalPolicy P x := by simpa [hcanon] using hd
      simp [Set.indicator_of_mem hxB, hne]
    · have hxB : x ∉ B := fun h => hd ((hdis x hx).mpr h)
      have he : π x = canonicalPolicy P x := by
        rw [← hcanon]
        exact not_ne_iff.mp hd
      simp [Set.indicator_of_notMem hxB, he]
  rw [← integral_indicator hB, integral_congr_ae heq]
  exact offsetDisagreement_le_regularizedLoss α γ θ n P e hP a ha π hπ

lemma leftSameBelow_mass_le (α γ θ : ℝ) (n : ℕ)
    (P : RowLaw) (e : ℝ → ℝ) (hP : LawClass α γ θ n P e)
    (a c t z : ℝ) (ha : 0 < a) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (htc : t < c) (hstar : leftThr c =ᵐ[P.PX] canonicalPolicy P)
    (hloss : regularizedLoss P a (leftThr t) ≤ z) :
    (∫ x in Set.Ioc t c, offsetG a P.logger x ∂P.PX) ≤ z := by
  apply (oracle_disagreement_mass_le_loss α γ θ n P e hP a ha
    (leftThr c) (leftThr t) (leftThr_mem_thresholdClass t ht) hstar
    (Set.Ioc t c) measurableSet_Ioc ?_).trans hloss
  intro x hx
  by_cases hc : x ≤ c <;> by_cases ht' : x ≤ t <;>
    simp [leftThr, hc, ht', Set.mem_Ioc] <;> linarith

lemma leftSameAbove_mass_le (α γ θ : ℝ) (n : ℕ)
    (P : RowLaw) (e : ℝ → ℝ) (hP : LawClass α γ θ n P e)
    (a c t z : ℝ) (ha : 0 < a) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hct : c ≤ t) (hstar : leftThr c =ᵐ[P.PX] canonicalPolicy P)
    (hloss : regularizedLoss P a (leftThr t) ≤ z) :
    (∫ x in Set.Ioc c t, offsetG a P.logger x ∂P.PX) ≤ z := by
  apply (oracle_disagreement_mass_le_loss α γ θ n P e hP a ha
    (leftThr c) (leftThr t) (leftThr_mem_thresholdClass t ht) hstar
    (Set.Ioc c t) measurableSet_Ioc ?_).trans hloss
  intro x hx
  by_cases hc : x ≤ c <;> by_cases ht' : x ≤ t <;>
    simp [leftThr, hc, ht', Set.mem_Ioc] <;> linarith

lemma leftOppBelow_mass_le (α γ θ : ℝ) (n : ℕ)
    (P : RowLaw) (e : ℝ → ℝ) (hP : LawClass α γ θ n P e)
    (a c t z : ℝ) (ha : 0 < a) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (htc : t ≤ c) (hstar : leftThr c =ᵐ[P.PX] canonicalPolicy P)
    (hloss : regularizedLoss P a (rightThr t) ≤ z) :
    (∫ x in Set.Ico 0 t ∪ Set.Ioc c 1,
      offsetG a P.logger x ∂P.PX) ≤ z := by
  apply (oracle_disagreement_mass_le_loss α γ θ n P e hP a ha
    (leftThr c) (rightThr t) (rightThr_mem_thresholdClass t ht) hstar
    (Set.Ico 0 t ∪ Set.Ioc c 1)
    (measurableSet_Ico.union measurableSet_Ioc) ?_).trans hloss
  intro x hx
  by_cases hc : x ≤ c
  · by_cases ht' : t ≤ x
    · simp [leftThr, rightThr, hc, ht', Set.mem_union, Set.mem_Ico,
        Set.mem_Ioc]
    · have hxt : x < t := lt_of_not_ge ht'
      simp [leftThr, rightThr, hc, ht', Set.mem_union, Set.mem_Ico,
        Set.mem_Ioc, hx.1, hx.2, hxt]
  · have hcx : c < x := lt_of_not_ge hc
    by_cases ht' : t ≤ x
    · simp [leftThr, rightThr, hc, ht', Set.mem_union, Set.mem_Ico,
        Set.mem_Ioc, hx.1, hx.2, hcx]
    · exfalso
      linarith

lemma leftOppAbove_mass_le (α γ θ : ℝ) (n : ℕ)
    (P : RowLaw) (e : ℝ → ℝ) (hP : LawClass α γ θ n P e)
    (a c t z : ℝ) (ha : 0 < a) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hct : c < t) (hstar : leftThr c =ᵐ[P.PX] canonicalPolicy P)
    (hloss : regularizedLoss P a (rightThr t) ≤ z) :
    (∫ x in Set.Icc 0 c ∪ Set.Icc t 1,
      offsetG a P.logger x ∂P.PX) ≤ z := by
  apply (oracle_disagreement_mass_le_loss α γ θ n P e hP a ha
    (leftThr c) (rightThr t) (rightThr_mem_thresholdClass t ht) hstar
    (Set.Icc 0 c ∪ Set.Icc t 1)
    (measurableSet_Icc.union measurableSet_Icc) ?_).trans hloss
  intro x hx
  by_cases hc : x ≤ c
  · have hnt : ¬ t ≤ x := by linarith
    simp [leftThr, rightThr, hc, hnt, Set.mem_union, Set.mem_Icc,
      hx.1, hx.2]
  · have hcx : c < x := lt_of_not_ge hc
    by_cases ht' : t ≤ x
    · simp [leftThr, rightThr, hc, ht', Set.mem_union, Set.mem_Icc,
        hx.1, hx.2, hcx]
    · have hxt : x < t := lt_of_not_ge ht'
      simp [leftThr, rightThr, hc, ht', Set.mem_union, Set.mem_Icc,
        hcx, hxt]

lemma leftSameBelowSkeleton_union_mass_le (α γ θ : ℝ) (n : ℕ)
    (P : RowLaw) (e : ℝ → ℝ) (hP : LawClass α γ θ n P e)
    (a c z : ℝ) (ha : 0 < a) (hz : 0 ≤ z)
    (hstar : leftThr c =ᵐ[P.PX] canonicalPolicy P)
    (S : LeftOracleLocalizedSkeleton P a c z true) :
    MeasurableSet (⋃ i : {t : S.D // t.1 < c}, Set.Ioc i.1.1 c) ∧
      (∫ x in ⋃ i : {t : S.D // t.1 < c}, Set.Ioc i.1.1 c,
        offsetG a P.logger x ∂P.PX) ≤ z := by
  letI : Countable S.D := S.countable
  apply countable_chain_offset_mass_le α γ θ n P e hP a z ha hz
  · exact fun _ => measurableSet_Ioc
  · intro i k
    rcases le_total i.1.1 k.1.1 with h | h
    · exact Or.inr fun x hx => ⟨lt_of_le_of_lt h hx.1, hx.2⟩
    · exact Or.inl fun x hx => ⟨lt_of_le_of_lt h hx.1, hx.2⟩
  · intro i
    have hi := S.subset i.1.2
    exact leftSameBelow_mass_le α γ θ n P e hP a c i.1.1 z ha
      hi.1 i.2 hstar hi.2

lemma leftSameAboveSkeleton_union_mass_le (α γ θ : ℝ) (n : ℕ)
    (P : RowLaw) (e : ℝ → ℝ) (hP : LawClass α γ θ n P e)
    (a c z : ℝ) (ha : 0 < a) (hz : 0 ≤ z)
    (hstar : leftThr c =ᵐ[P.PX] canonicalPolicy P)
    (S : LeftOracleLocalizedSkeleton P a c z true) :
    MeasurableSet (⋃ i : {t : S.D // c ≤ t.1}, Set.Ioc c i.1.1) ∧
      (∫ x in ⋃ i : {t : S.D // c ≤ t.1}, Set.Ioc c i.1.1,
        offsetG a P.logger x ∂P.PX) ≤ z := by
  letI : Countable S.D := S.countable
  apply countable_chain_offset_mass_le α γ θ n P e hP a z ha hz
  · exact fun _ => measurableSet_Ioc
  · intro i k
    rcases le_total i.1.1 k.1.1 with h | h
    · exact Or.inl fun x hx => ⟨hx.1, hx.2.trans h⟩
    · exact Or.inr fun x hx => ⟨hx.1, hx.2.trans h⟩
  · intro i
    have hi := S.subset i.1.2
    exact leftSameAbove_mass_le α γ θ n P e hP a c i.1.1 z ha
      hi.1 i.2 hstar hi.2

lemma leftOppBelowSkeleton_union_mass_le (α γ θ : ℝ) (n : ℕ)
    (P : RowLaw) (e : ℝ → ℝ) (hP : LawClass α γ θ n P e)
    (a c z : ℝ) (ha : 0 < a) (hz : 0 ≤ z)
    (hstar : leftThr c =ᵐ[P.PX] canonicalPolicy P)
    (S : LeftOracleLocalizedSkeleton P a c z false) :
    MeasurableSet (⋃ i : {t : S.D // t.1 ≤ c},
      Set.Ico 0 i.1.1 ∪ Set.Ioc c 1) ∧
      (∫ x in ⋃ i : {t : S.D // t.1 ≤ c},
        Set.Ico 0 i.1.1 ∪ Set.Ioc c 1,
        offsetG a P.logger x ∂P.PX) ≤ z := by
  letI : Countable S.D := S.countable
  apply countable_chain_offset_mass_le α γ θ n P e hP a z ha hz
  · exact fun _ => measurableSet_Ico.union measurableSet_Ioc
  · intro i k
    rcases le_total i.1.1 k.1.1 with h | h
    · exact Or.inl fun x hx => hx.elim
        (fun hxi => Or.inl ⟨hxi.1, hxi.2.trans_le h⟩) Or.inr
    · exact Or.inr fun x hx => hx.elim
        (fun hxi => Or.inl ⟨hxi.1, hxi.2.trans_le h⟩) Or.inr
  · intro i
    have hi := S.subset i.1.2
    exact leftOppBelow_mass_le α γ θ n P e hP a c i.1.1 z ha
      hi.1 i.2 hstar hi.2

lemma leftOppAboveSkeleton_union_mass_le (α γ θ : ℝ) (n : ℕ)
    (P : RowLaw) (e : ℝ → ℝ) (hP : LawClass α γ θ n P e)
    (a c z : ℝ) (ha : 0 < a) (hz : 0 ≤ z)
    (hstar : leftThr c =ᵐ[P.PX] canonicalPolicy P)
    (S : LeftOracleLocalizedSkeleton P a c z false) :
    MeasurableSet (⋃ i : {t : S.D // c < t.1},
      Set.Icc 0 c ∪ Set.Icc i.1.1 1) ∧
      (∫ x in ⋃ i : {t : S.D // c < t.1},
        Set.Icc 0 c ∪ Set.Icc i.1.1 1,
        offsetG a P.logger x ∂P.PX) ≤ z := by
  letI : Countable S.D := S.countable
  apply countable_chain_offset_mass_le α γ θ n P e hP a z ha hz
  · exact fun _ => measurableSet_Icc.union measurableSet_Icc
  · intro i k
    rcases le_total i.1.1 k.1.1 with h | h
    · exact Or.inr fun x hx => hx.elim Or.inl
        (fun hxi => Or.inr ⟨h.trans hxi.1, hxi.2⟩)
    · exact Or.inl fun x hx => hx.elim Or.inl
        (fun hxi => Or.inr ⟨h.trans hxi.1, hxi.2⟩)
  · intro i
    have hi := S.subset i.1.2
    exact leftOppAbove_mass_le α γ θ n P e hP a c i.1.1 z ha
      hi.1 i.2 hstar hi.2

end CausalSmith.Stat.ScorethresholdOverlapRegret
