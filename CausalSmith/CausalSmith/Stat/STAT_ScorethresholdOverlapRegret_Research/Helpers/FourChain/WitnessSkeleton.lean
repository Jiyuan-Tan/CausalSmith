module
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.FourChain.WitnessTransport

/-! # Localized right-oracle skeletons and branch mass budgets -/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal

namespace CausalSmith.Stat.ScorethresholdOverlapRegret
structure RightOracleLocalizedSkeleton (P : RowLaw) (a c z : ℝ)
    (upper : Bool) where
  D : Set ℝ
  countable : D.Countable
  subset : D ⊆ {t ∈ Set.Icc (0 : ℝ) 1 |
    regularizedLoss P a (if upper then leftThr t else rightThr t) ≤ z}
  reduction : ∀ (n : ℕ) (x : Fin n → SupportedObservation),
    Causalean.Stat.EmpiricalProcess.Countable.localizedThresholdSup
      (supportedObsLaw P) upper (fun o : SupportedObservation => o.1.X)
      (rightOracleOffset P a c) (rightOracleMark P a)
      (Set.Icc (0 : ℝ) 1)
      (fun t => regularizedLoss P a
        (if upper then leftThr t else rightThr t)) z x =
    Causalean.Stat.EmpiricalProcess.Countable.centeredSup
      (supportedObsLaw P)
      (fun t : D => Causalean.Stat.EmpiricalProcess.Countable.thresholdFunction
        upper (fun o : SupportedObservation => o.1.X)
        (rightOracleOffset P a c) (rightOracleMark P a) t.1) x

/-- Atom-safe separability produces deterministic countable localized
skeletons for both threshold orientations under an exact right oracle. -/
noncomputable def exists_rightOracle_localizedSkeletons (α γ θ : ℝ) (n : ℕ)
    (P : RowLaw) (e : ℝ → ℝ) (hP : LawClass α γ θ n P e)
    (a c z : ℝ) (ha : 0 < a ∧ a ≤ 1 / 4) :
    RightOracleLocalizedSkeleton P a c z false ×
      RightOracleLocalizedSkeleton P a c z true := by
  letI : IsProbabilityMeasure P.full := hP.wf.1
  letI : IsProbabilityMeasure P.obsLaw :=
    Measure.isProbabilityMeasure_map score_observation_map_measurable.aemeasurable
  letI : IsProbabilityMeasure (supportedObsLaw P) :=
    supportedObsLaw_isProbabilityMeasure P hP.wf
  have hlogger : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      P.logger x ∈ Set.Ioo (0 : ℝ) 1 := by
    intro x hx
    simpa only [hP.known hx] using hP.loggerSpace x hx
  have hs := supportedObservation_X_measurable
  have ho := rightOracleOffset_integrable P a c hP.wf ha hlogger
  have hm := rightOracleMark_integrable P a hP.wf ha hlogger
  have make (upper : Bool) : RightOracleLocalizedSkeleton P a c z upper := by
    let R :=
      Causalean.Stat.EmpiricalProcess.Countable.localizedThreshold_countable_reduction
        (supportedObsLaw P) upper (fun o : SupportedObservation => o.1.X)
        (rightOracleOffset P a c) (rightOracleMark P a) hs ho hm
        (Set.Icc (0 : ℝ) 1)
        (fun t => regularizedLoss P a
          (if upper then leftThr t else rightThr t)) z
    let D := Classical.choose R
    have hD := Classical.choose_spec R
    exact ⟨D, hD.1, hD.2.1, hD.2.2.2.2⟩
  exact ⟨make false, make true⟩

/-- The offset part of localized loss is bounded by total regularized loss. -/
lemma offsetDisagreement_le_regularizedLoss (α γ θ : ℝ) (n : ℕ)
    (P : RowLaw) (e : ℝ → ℝ) (hP : LawClass α γ θ n P e)
    (a : ℝ) (ha : 0 < a) (π : ℝ → Bool) (hπ : π ∈ thresholdClass) :
    offsetDisagreement P a π ≤ regularizedLoss P a π := by
  have hw := regret_eq_effect_disagreement α γ θ n P e hP π
    (thresholdClass_mem_binaryPolicyClass π hπ)
  change rawRegret P π = _ at hw
  have hr0 : 0 ≤ rawRegret P π := by
    rw [hw]
    exact integral_nonneg fun x => by
      unfold effectMagnitude
      positivity
  unfold regularizedLoss
  linarith

/-- For an a.e. right-threshold representative of the canonical policy,
any exact measurable disagreement set has offset mass at most localized loss. -/
lemma rightOracle_disagreement_mass_le_loss (α γ θ : ℝ) (n : ℕ)
    (P : RowLaw) (e : ℝ → ℝ) (hP : LawClass α γ θ n P e)
    (a c : ℝ) (ha : 0 < a) (π : ℝ → Bool) (hπ : π ∈ thresholdClass)
    (hstar : rightThr c =ᵐ[P.PX] canonicalPolicy P)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hdis : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      (π x ≠ rightThr c x ↔ x ∈ B)) :
    (∫ x in B, offsetG a P.logger x ∂P.PX) ≤ regularizedLoss P a π := by
  have hs : ∀ᵐ x ∂P.PX, x ∈ Set.Icc (0 : ℝ) 1 := ae_iff.mpr hP.score.2
  have heq : (B.indicator (offsetG a P.logger)) =ᵐ[P.PX]
      fun x => offsetG a P.logger x *
        (if π x = canonicalPolicy P x then (0 : ℝ) else 1) := by
    filter_upwards [hs, hstar] with x hx hcanon
    by_cases hd : π x ≠ rightThr c x
    · have hxB := (hdis x hx).mp hd
      have hne : π x ≠ canonicalPolicy P x := by simpa [hcanon] using hd
      simp [Set.indicator_of_mem hxB, hne]
    · have hxB : x ∉ B := fun h => hd ((hdis x hx).mpr h)
      have he : π x = canonicalPolicy P x := by
        rw [← hcanon]
        exact not_ne_iff.mp hd
      simp [Set.indicator_of_notMem hxB, he]
  have hid : (∫ x in B, offsetG a P.logger x ∂P.PX) =
      offsetDisagreement P a π := by
    rw [← integral_indicator hB]
    exact integral_congr_ae heq
  rw [hid]
  exact offsetDisagreement_le_regularizedLoss α γ θ n P e hP a ha π hπ

/-- A countable nested union preserves the localized offset-mass budget.
The pointwise nonnegativity required by the generic substrate is supplied by
the positive-part version of `offsetG`, which is a.e. equal under `P.PX`. -/
lemma countable_chain_offset_mass_le {ι : Type} [Countable ι]
    (α γ θ : ℝ) (n : ℕ) (P : RowLaw) (e : ℝ → ℝ)
    (hP : LawClass α γ θ n P e) (a z : ℝ) (ha : 0 < a) (hz : 0 ≤ z)
    (B : ι → Set ℝ) (hB : ∀ i, MeasurableSet (B i))
    (hchain : ∀ i k, B i ⊆ B k ∨ B k ⊆ B i)
    (hbudget : ∀ i, (∫ x in B i, offsetG a P.logger x ∂P.PX) ≤ z) :
    MeasurableSet (⋃ i, B i) ∧
      (∫ x in ⋃ i, B i, offsetG a P.logger x ∂P.PX) ≤ z := by
  letI : IsProbabilityMeasure P.PX := hP.score.1
  have hpositiveLogger : ∀ᵐ x ∂P.PX,
      0 < P.logger x ∧ P.logger x < 1 := by
    filter_upwards [hP.positive, ae_iff.mpr hP.score.2] with x hx hs
    simpa only [hP.known hs] using hx
  have hg : AEMeasurable (offsetG a P.logger) P.PX := by
    have hl := logger_aemeasurable P hP.wf
    unfold offsetG
    fun_prop
  have hgrange : ∀ᵐ x ∂P.PX,
      0 ≤ offsetG a P.logger x ∧ offsetG a P.logger x ≤ 1 := by
    filter_upwards [hpositiveLogger] with x hx
    have hp : 0 < min (P.logger x) (1 - P.logger x) :=
      lt_min hx.1 (by linarith [hx.2])
    exact ⟨le_min zero_le_one (div_nonneg ha.le hp.le), min_le_left _ _⟩
  let g : ℝ → ℝ := fun x => max 0 (offsetG a P.logger x)
  have hgm : AEMeasurable g P.PX := aemeasurable_const.max hg
  have hgi : Integrable g P.PX := by
    apply Integrable.of_bound hgm.aestronglyMeasurable 1
    filter_upwards [hgrange] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
    simp only [g, max_eq_right hx.1]
    exact hx.2
  have hgpos : ∀ x, 0 ≤ g x := fun x => le_max_left _ _
  have hgeq : g =ᵐ[P.PX] offsetG a P.logger := by
    filter_upwards [hgrange] with x hx
    exact max_eq_right hx.1
  have hbudget' : ∀ i, (∫ x in B i, g x ∂P.PX) ≤ z := by
    intro i
    rw [integral_congr_ae (ae_restrict_of_ae hgeq)]
    exact hbudget i
  have hu := Causalean.Stat.EmpiricalProcess.Countable.countable_chain_union_mass_le
    P.PX B hB hchain g hgi hgpos z hz hbudget'
  refine ⟨hu.1, ?_⟩
  rw [← integral_congr_ae (ae_restrict_of_ae hgeq)]
  exact hu.2

lemma rightThr_mem_thresholdClass (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    rightThr t ∈ thresholdClass :=
  Or.inr (Or.inr (Or.inr ⟨t, ht, fun _ _ => rfl⟩))

lemma leftThr_mem_thresholdClass (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    leftThr t ∈ thresholdClass :=
  Or.inr (Or.inr (Or.inl ⟨t, ht, fun _ _ => rfl⟩))

lemma rightBelowSet_mass_le (α γ θ : ℝ) (n : ℕ)
    (P : RowLaw) (e : ℝ → ℝ) (hP : LawClass α γ θ n P e)
    (a c t z : ℝ) (ha : 0 < a) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (htc : t < c) (hstar : rightThr c =ᵐ[P.PX] canonicalPolicy P)
    (hloss : regularizedLoss P a (rightThr t) ≤ z) :
    (∫ x in Set.Ico t c, offsetG a P.logger x ∂P.PX) ≤ z :=
  (rightOracle_disagreement_mass_le_loss α γ θ n P e hP a c ha
    (rightThr t) (rightThr_mem_thresholdClass t ht) hstar (Set.Ico t c)
    measurableSet_Ico (fun x hx => rightOracle_right_below_disagreement c t x htc)).trans hloss

lemma rightAboveSet_mass_le (α γ θ : ℝ) (n : ℕ)
    (P : RowLaw) (e : ℝ → ℝ) (hP : LawClass α γ θ n P e)
    (a c t z : ℝ) (ha : 0 < a) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hct : c ≤ t) (hstar : rightThr c =ᵐ[P.PX] canonicalPolicy P)
    (hloss : regularizedLoss P a (rightThr t) ≤ z) :
    (∫ x in Set.Ico c t, offsetG a P.logger x ∂P.PX) ≤ z :=
  (rightOracle_disagreement_mass_le_loss α γ θ n P e hP a c ha
    (rightThr t) (rightThr_mem_thresholdClass t ht) hstar (Set.Ico c t)
    measurableSet_Ico (fun x hx => rightOracle_right_above_disagreement c t x hct)).trans hloss

lemma leftBelowSet_mass_le (α γ θ : ℝ) (n : ℕ)
    (P : RowLaw) (e : ℝ → ℝ) (hP : LawClass α γ θ n P e)
    (a c t z : ℝ) (ha : 0 < a) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (htc : t < c) (hstar : rightThr c =ᵐ[P.PX] canonicalPolicy P)
    (hloss : regularizedLoss P a (leftThr t) ≤ z) :
    (∫ x in Set.Icc 0 t ∪ Set.Icc c 1,
      offsetG a P.logger x ∂P.PX) ≤ z :=
  (rightOracle_disagreement_mass_le_loss α γ θ n P e hP a c ha
    (leftThr t) (leftThr_mem_thresholdClass t ht) hstar
    (Set.Icc 0 t ∪ Set.Icc c 1) (measurableSet_Icc.union measurableSet_Icc)
    (fun x hx => rightOracle_left_below_disagreement c t x htc hx)).trans hloss

lemma leftAboveSet_mass_le (α γ θ : ℝ) (n : ℕ)
    (P : RowLaw) (e : ℝ → ℝ) (hP : LawClass α γ θ n P e)
    (a c t z : ℝ) (ha : 0 < a) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hct : c ≤ t) (hstar : rightThr c =ᵐ[P.PX] canonicalPolicy P)
    (hloss : regularizedLoss P a (leftThr t) ≤ z) :
    (∫ x in Set.Ico 0 c ∪ Set.Ioc t 1,
      offsetG a P.logger x ∂P.PX) ≤ z :=
  (rightOracle_disagreement_mass_le_loss α γ θ n P e hP a c ha
    (leftThr t) (leftThr_mem_thresholdClass t ht) hstar
    (Set.Ico 0 c ∪ Set.Ioc t 1) (measurableSet_Ico.union measurableSet_Ioc)
    (fun x hx => rightOracle_left_above_disagreement c t x hct hx)).trans hloss

lemma rightBelowSkeleton_union_mass_le (α γ θ : ℝ) (n : ℕ)
    (P : RowLaw) (e : ℝ → ℝ) (hP : LawClass α γ θ n P e)
    (a c z : ℝ) (ha : 0 < a) (hz : 0 ≤ z)
    (hstar : rightThr c =ᵐ[P.PX] canonicalPolicy P)
    (S : RightOracleLocalizedSkeleton P a c z false) :
    MeasurableSet (⋃ i : {t : S.D // t.1 < c}, Set.Ico i.1.1 c) ∧
      (∫ x in ⋃ i : {t : S.D // t.1 < c}, Set.Ico i.1.1 c,
        offsetG a P.logger x ∂P.PX) ≤ z := by
  letI : Countable S.D := S.countable
  apply countable_chain_offset_mass_le α γ θ n P e hP a z ha hz
  · exact fun _ => measurableSet_Ico
  · intro i k
    rcases le_total i.1.1 k.1.1 with h | h
    · exact Or.inr (rightOracle_right_below_nested c _ _ h)
    · exact Or.inl (rightOracle_right_below_nested c _ _ h)
  · intro i
    have hi := S.subset i.1.2
    exact rightBelowSet_mass_le α γ θ n P e hP a c i.1.1 z ha
      hi.1 i.2 hstar hi.2

lemma rightAboveSkeleton_union_mass_le (α γ θ : ℝ) (n : ℕ)
    (P : RowLaw) (e : ℝ → ℝ) (hP : LawClass α γ θ n P e)
    (a c z : ℝ) (ha : 0 < a) (hz : 0 ≤ z)
    (hstar : rightThr c =ᵐ[P.PX] canonicalPolicy P)
    (S : RightOracleLocalizedSkeleton P a c z false) :
    MeasurableSet (⋃ i : {t : S.D // c ≤ t.1}, Set.Ico c i.1.1) ∧
      (∫ x in ⋃ i : {t : S.D // c ≤ t.1}, Set.Ico c i.1.1,
        offsetG a P.logger x ∂P.PX) ≤ z := by
  letI : Countable S.D := S.countable
  apply countable_chain_offset_mass_le α γ θ n P e hP a z ha hz
  · exact fun _ => measurableSet_Ico
  · intro i k
    rcases le_total i.1.1 k.1.1 with h | h
    · exact Or.inl (rightOracle_right_above_nested c _ _ h)
    · exact Or.inr (rightOracle_right_above_nested c _ _ h)
  · intro i
    have hi := S.subset i.1.2
    exact rightAboveSet_mass_le α γ θ n P e hP a c i.1.1 z ha
      hi.1 i.2 hstar hi.2

lemma leftBelowSkeleton_union_mass_le (α γ θ : ℝ) (n : ℕ)
    (P : RowLaw) (e : ℝ → ℝ) (hP : LawClass α γ θ n P e)
    (a c z : ℝ) (ha : 0 < a) (hz : 0 ≤ z)
    (hstar : rightThr c =ᵐ[P.PX] canonicalPolicy P)
    (S : RightOracleLocalizedSkeleton P a c z true) :
    MeasurableSet (⋃ i : {t : S.D // t.1 < c},
      Set.Icc 0 i.1.1 ∪ Set.Icc c 1) ∧
      (∫ x in ⋃ i : {t : S.D // t.1 < c},
        Set.Icc 0 i.1.1 ∪ Set.Icc c 1,
        offsetG a P.logger x ∂P.PX) ≤ z := by
  letI : Countable S.D := S.countable
  apply countable_chain_offset_mass_le α γ θ n P e hP a z ha hz
  · exact fun _ => measurableSet_Icc.union measurableSet_Icc
  · intro i k
    rcases le_total i.1.1 k.1.1 with h | h
    · exact Or.inl (rightOracle_left_below_nested c _ _ h)
    · exact Or.inr (rightOracle_left_below_nested c _ _ h)
  · intro i
    have hi := S.subset i.1.2
    exact leftBelowSet_mass_le α γ θ n P e hP a c i.1.1 z ha
      hi.1 i.2 hstar hi.2

lemma leftAboveSkeleton_union_mass_le (α γ θ : ℝ) (n : ℕ)
    (P : RowLaw) (e : ℝ → ℝ) (hP : LawClass α γ θ n P e)
    (a c z : ℝ) (ha : 0 < a) (hz : 0 ≤ z)
    (hstar : rightThr c =ᵐ[P.PX] canonicalPolicy P)
    (S : RightOracleLocalizedSkeleton P a c z true) :
    MeasurableSet (⋃ i : {t : S.D // c ≤ t.1},
      Set.Ico 0 c ∪ Set.Ioc i.1.1 1) ∧
      (∫ x in ⋃ i : {t : S.D // c ≤ t.1},
        Set.Ico 0 c ∪ Set.Ioc i.1.1 1,
        offsetG a P.logger x ∂P.PX) ≤ z := by
  letI : Countable S.D := S.countable
  apply countable_chain_offset_mass_le α γ θ n P e hP a z ha hz
  · exact fun _ => measurableSet_Ico.union measurableSet_Ioc
  · intro i k
    rcases le_total i.1.1 k.1.1 with h | h
    · exact Or.inr (rightOracle_left_above_nested c _ _ h)
    · exact Or.inl (rightOracle_left_above_nested c _ _ h)
  · intro i
    have hi := S.subset i.1.2
    exact leftAboveSet_mass_le α γ θ n P e hP a c i.1.1 z ha
      hi.1 i.2 hstar hi.2

end CausalSmith.Stat.ScorethresholdOverlapRegret
