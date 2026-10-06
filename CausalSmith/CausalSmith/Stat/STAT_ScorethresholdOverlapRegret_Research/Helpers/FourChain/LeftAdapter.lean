module
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.FourChain.LeftOracle

/-! # Left-oracle localized-process adapter -/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal

namespace CausalSmith.Stat.ScorethresholdOverlapRegret

/-- The two left-oracle skeletons admit one faithful five-chain cover, with
its geometry exposed for the branch energy estimates. -/
lemma exists_leftOracle_skeleton_fiveChain
    (P : RowLaw) (a c z : ℝ) (hP : WellFormed P)
    (ha : 0 < a ∧ a ≤ 1 / 4)
    (hlogger : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      P.logger x ∈ Set.Ioo (0 : ℝ) 1)
    (Sright : LeftOracleLocalizedSkeleton P a c z false)
    (Sleft : LeftOracleLocalizedSkeleton P a c z true)
    [IsProbabilityMeasure (supportedObsLaw P)] :
    ∃ F : Causalean.Stat.EmpiricalProcess.Countable.BoundedClass
        SupportedObservation
        (FiveChainIndex
          {t : Sleft.D // t.1 < c} {t : Sleft.D // c ≤ t.1}
          {t : Sright.D // t.1 ≤ c} {t : Sright.D // c < t.1}),
      ∃ cover : Causalean.Stat.EmpiricalProcess.Countable.ChainCover F 5,
        (∀ (n : ℕ) (x : Fin n → SupportedObservation),
          Causalean.Stat.EmpiricalProcess.Countable.localizedThresholdSup
              (supportedObsLaw P) false
              (fun o : SupportedObservation => o.1.X)
              (leftOracleOffset P a c) (leftOracleMark P a)
              (Set.Icc (0 : ℝ) 1)
              (fun t => regularizedLoss P a (rightThr t)) z x ≤
            Causalean.Stat.EmpiricalProcess.Countable.centeredSup
              (supportedObsLaw P) F.f x ∧
          Causalean.Stat.EmpiricalProcess.Countable.localizedThresholdSup
              (supportedObsLaw P) true
              (fun o : SupportedObservation => o.1.X)
              (leftOracleOffset P a c) (leftOracleMark P a)
              (Set.Icc (0 : ℝ) 1)
              (fun t => regularizedLoss P a (leftThr t)) z x ≤
            Causalean.Stat.EmpiricalProcess.Countable.centeredSup
              (supportedObsLaw P) F.f x) ∧
        (F.f .branch4 = fun o => witnessComparisonIntegrand P a (leftThr c)
          (if decide (regularizedLoss P a (fun _ => false) ≤ z)
            then (fun _ => false) else leftThr c) o.1) ∧
        (∀ b, cover.weight b = leftOracleWeight P a c) ∧
        (cover.containing 0 = ⋃ i : {t : Sleft.D // t.1 < c},
          {o | o.1.X ∈ Set.Ioc i.1.1 c}) ∧
        (cover.containing 1 = ⋃ i : {t : Sleft.D // c ≤ t.1},
          {o | o.1.X ∈ Set.Ioc c i.1.1}) ∧
        (cover.containing 2 = ⋃ i : {t : Sright.D // t.1 ≤ c},
          {o | o.1.X ∈ Set.Ico 0 i.1.1 ∪ Set.Ioc c 1}) ∧
        (cover.containing 3 = ⋃ i : {t : Sright.D // c < t.1},
          {o | o.1.X ∈ Set.Icc 0 c ∪ Set.Icc i.1.1 1}) ∧
        (cover.containing 4 = if decide
          (regularizedLoss P a (fun _ => false) ≤ z)
            then leftZeroSet c else ∅) := by
  letI : Countable Sright.D := Sright.countable
  letI : Countable Sleft.D := Sleft.countable
  let ι₀ := {t : Sleft.D // t.1 < c}
  let ι₁ := {t : Sleft.D // c ≤ t.1}
  let ι₂ := {t : Sright.D // t.1 ≤ c}
  let ι₃ := {t : Sright.D // c < t.1}
  let B₀ : ι₀ → Set SupportedObservation := fun i => leftSameBelowSet c i.1.1
  let B₁ : ι₁ → Set SupportedObservation := fun i => leftSameAboveSet c i.1.1
  let B₂ : ι₂ → Set SupportedObservation := fun i => leftOppBelowSet c i.1.1
  let B₃ : ι₃ → Set SupportedObservation := fun i => leftOppAboveSet c i.1.1
  let inc := decide (regularizedLoss P a (fun _ => false) ≤ z)
  let B₄ : Set SupportedObservation := if inc then leftZeroSet c else ∅
  let weight : Fin 5 → SupportedObservation → ℝ := fun _ =>
    leftOracleWeight P a c
  let K : ℝ := 2 / a
  have hK : 0 ≤ K := div_nonneg (by norm_num) ha.1.le
  have hB₀ : ∀ i, MeasurableSet (B₀ i) := fun _ =>
    supportedObservation_X_measurable measurableSet_Ioc
  have hB₁ : ∀ i, MeasurableSet (B₁ i) := fun _ =>
    supportedObservation_X_measurable measurableSet_Ioc
  have hB₂ : ∀ i, MeasurableSet (B₂ i) := fun _ =>
    supportedObservation_X_measurable
      (measurableSet_Ico.union measurableSet_Ioc)
  have hB₃ : ∀ i, MeasurableSet (B₃ i) := fun _ =>
    supportedObservation_X_measurable
      (measurableSet_Icc.union measurableSet_Icc)
  have hB₄ : MeasurableSet B₄ := by
    by_cases hinc : inc = true
    · rw [show B₄ = leftZeroSet c by simp [B₄, hinc]]
      exact supportedObservation_X_measurable measurableSet_Icc
    · rw [show B₄ = ∅ by simp [B₄, hinc]]
      exact MeasurableSet.empty
  have hw : ∀ b, Measurable (weight b) := fun _ =>
    leftOracleWeight_measurable P a c hP
  have hwK : ∀ b x, |weight b x| ≤ K := fun _ x =>
    leftOracleWeight_abs_le P a c ha hlogger x
  let F := fiveChainBoundedClass B₀ B₁ B₂ B₃ B₄ weight K hK
    hB₀ hB₁ hB₂ hB₃ hB₄ hw hwK
  let U₀ : Set SupportedObservation := ⋃ i, B₀ i
  let U₁ : Set SupportedObservation := ⋃ i, B₁ i
  let U₂ : Set SupportedObservation := ⋃ i, B₂ i
  let U₃ : Set SupportedObservation := ⋃ i, B₃ i
  let U : Fin 5 → Set SupportedObservation := ![U₀, U₁, U₂, U₃, B₄]
  have hn₀ : ∀ i k, B₀ i ⊆ B₀ k ∨ B₀ k ⊆ B₀ i := by
    intro i k
    rcases le_total i.1.1 k.1.1 with h | h
    · exact Or.inr fun x hx => ⟨lt_of_le_of_lt h hx.1, hx.2⟩
    · exact Or.inl fun x hx => ⟨lt_of_le_of_lt h hx.1, hx.2⟩
  have hn₁ : ∀ i k, B₁ i ⊆ B₁ k ∨ B₁ k ⊆ B₁ i := by
    intro i k
    rcases le_total i.1.1 k.1.1 with h | h
    · exact Or.inl fun x hx => ⟨hx.1, hx.2.trans h⟩
    · exact Or.inr fun x hx => ⟨hx.1, hx.2.trans h⟩
  have hn₂ : ∀ i k, B₂ i ⊆ B₂ k ∨ B₂ k ⊆ B₂ i := by
    intro i k
    rcases le_total i.1.1 k.1.1 with h | h
    · exact Or.inl fun x hx => hx.elim
        (fun hxi => Or.inl ⟨hxi.1, hxi.2.trans_le h⟩) Or.inr
    · exact Or.inr fun x hx => hx.elim
        (fun hxi => Or.inl ⟨hxi.1, hxi.2.trans_le h⟩) Or.inr
  have hn₃ : ∀ i k, B₃ i ⊆ B₃ k ∨ B₃ k ⊆ B₃ i := by
    intro i k
    rcases le_total i.1.1 k.1.1 with h | h
    · exact Or.inr fun x hx => hx.elim Or.inl
        (fun hxi => Or.inr ⟨h.trans hxi.1, hxi.2⟩)
    · exact Or.inl fun x hx => hx.elim Or.inl
        (fun hxi => Or.inr ⟨h.trans hxi.1, hxi.2⟩)
  have hU₀ : ∀ i, B₀ i ⊆ U 0 := fun i x hx => by
    exact Set.mem_iUnion_of_mem i hx
  have hU₁ : ∀ i, B₁ i ⊆ U 1 := fun i x hx => by
    exact Set.mem_iUnion_of_mem i hx
  have hU₂ : ∀ i, B₂ i ⊆ U 2 := fun i x hx => by
    exact Set.mem_iUnion_of_mem i hx
  have hU₃ : ∀ i, B₃ i ⊆ U 3 := fun i x hx => by
    exact Set.mem_iUnion_of_mem i hx
  have hU₄ : B₄ ⊆ U 4 := fun _ hx => hx
  let cover := fiveChainCover B₀ B₁ B₂ B₃ B₄ weight U K hK
    hB₀ hB₁ hB₂ hB₃ hB₄ hw hwK hn₀ hn₁ hn₂ hn₃
    hU₀ hU₁ hU₂ hU₃ hU₄
  refine ⟨F, cover, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n x
    constructor
    · have hr := Sright.reduction n x
      simp only [Bool.false_eq_true, if_false] at hr
      rw [hr]
      apply centeredSup_le_of_exists_reindex (supportedObsLaw P) F _
      intro t
      rcases le_or_gt t.1 c with ht | ht
      · refine ⟨.branch2 ⟨t, ht⟩, ?_⟩
        rw [leftThresholdFunction_eq_witnessComparison]
        simpa [F, fiveChainBoundedClass, fiveChainFunction, fiveChainSet,
          fiveChainBranch, B₂, weight] using
          witnessComparison_left_opp_below P a c t.1 ht
      · refine ⟨.branch3 ⟨t, ht⟩, ?_⟩
        rw [leftThresholdFunction_eq_witnessComparison]
        simpa [F, fiveChainBoundedClass, fiveChainFunction, fiveChainSet,
          fiveChainBranch, B₃, weight] using
          witnessComparison_left_opp_above P a c t.1 ht
    · have hr := Sleft.reduction n x
      simp only [if_true] at hr
      rw [hr]
      apply centeredSup_le_of_exists_reindex (supportedObsLaw P) F _
      intro t
      rcases lt_or_ge t.1 c with ht | ht
      · refine ⟨.branch0 ⟨t, ht⟩, ?_⟩
        rw [leftThresholdFunction_eq_witnessComparison]
        simpa [F, fiveChainBoundedClass, fiveChainFunction, fiveChainSet,
          fiveChainBranch, B₀, weight] using
          witnessComparison_left_same_below P a c t.1 ht
      · refine ⟨.branch1 ⟨t, ht⟩, ?_⟩
        rw [leftThresholdFunction_eq_witnessComparison]
        simpa [F, fiveChainBoundedClass, fiveChainFunction, fiveChainSet,
          fiveChainBranch, B₁, weight] using
          witnessComparison_left_same_above P a c t.1 ht
  · cases hinc : inc with
    | false =>
        have hdec : decide (regularizedLoss P a (fun _ => false) ≤ z) = false := by
          simpa only [inc] using hinc
        change B₄.indicator (leftOracleWeight P a c) = _
        rw [show B₄ = ∅ by simp [B₄, hinc]]
        simp [hdec, witnessComparisonIntegrand]
    | true =>
        have hdec : decide (regularizedLoss P a (fun _ => false) ≤ z) = true := by
          simpa only [inc] using hinc
        change B₄.indicator (leftOracleWeight P a c) = _
        rw [show B₄ = leftZeroSet c by simp [B₄, hinc]]
        simpa only [hdec, if_true] using
          (witnessComparison_left_zero P a c).symm
  · intro b
    rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

/-- The full eligible cutoff family for a left oracle is uniformly bounded. -/
@[no_expose]
noncomputable def leftOracleThresholdBoundedClass (P : RowLaw)
    (a c : ℝ) (upper : Bool) (loss : ℝ → ℝ) (z : ℝ)
    (hP : WellFormed P) (ha : 0 < a ∧ a ≤ 1 / 4)
    (hlogger : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      P.logger x ∈ Set.Ioo (0 : ℝ) 1) :
    Causalean.Stat.EmpiricalProcess.Countable.BoundedClass
      SupportedObservation {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1 ∧ loss t ≤ z} := {
  f := fun t => Causalean.Stat.EmpiricalProcess.Countable.thresholdFunction
    upper (fun o : SupportedObservation => o.1.X)
    (leftOracleOffset P a c) (leftOracleMark P a) t.1
  bound := 4 / a
  bound_nonneg := div_nonneg (by norm_num) ha.1.le
  measurable := fun t =>
    Causalean.Stat.EmpiricalProcess.Countable.thresholdFunction_measurable
      upper _ _ _ supportedObservation_X_measurable
      (leftOracleOffset_measurable P a c hP)
      (leftOracleMark_measurable P a hP) t.1
  bounded := fun t o => by
    have hoff := leftOracleOffset_abs_le P a c ha hlogger o
    have hmark := leftOracleMark_abs_le P a ha hlogger o
    have h24 : 2 / a ≤ 4 / a :=
      div_le_div_of_nonneg_right (by norm_num) ha.1.le
    unfold Causalean.Stat.EmpiricalProcess.Countable.thresholdFunction
    split_ifs <;> first
    | calc
        |leftOracleOffset P a c o + leftOracleMark P a o|
            ≤ |leftOracleOffset P a c o| + |leftOracleMark P a o| :=
              abs_add_le _ _
        _ ≤ 2 / a + 2 / a := add_le_add hoff hmark
        _ = 4 / a := by ring
    | simpa only [add_zero] using hoff.trans h24 }

lemma leftThresholdCentered_le_localizedThresholdSup
    (P : RowLaw) (a c z : ℝ) (upper : Bool) (loss : ℝ → ℝ)
    (hP : WellFormed P) (ha : 0 < a ∧ a ≤ 1 / 4)
    (hlogger : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      P.logger x ∈ Set.Ioo (0 : ℝ) 1)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (hloss : loss t ≤ z)
    {n : ℕ} (x : Fin n → SupportedObservation)
    [IsProbabilityMeasure (supportedObsLaw P)] :
    |Causalean.Stat.Concentration.centeredEmpiricalAverage
      (supportedObsLaw P) x
      (Causalean.Stat.EmpiricalProcess.Countable.thresholdFunction upper
        (fun o : SupportedObservation => o.1.X)
        (leftOracleOffset P a c) (leftOracleMark P a) t)| ≤
      Causalean.Stat.EmpiricalProcess.Countable.localizedThresholdSup
        (supportedObsLaw P) upper (fun o : SupportedObservation => o.1.X)
        (leftOracleOffset P a c) (leftOracleMark P a)
        (Set.Icc (0 : ℝ) 1) loss z x := by
  let F := leftOracleThresholdBoundedClass P a c upper loss z hP ha hlogger
  change _ ≤ Causalean.Stat.EmpiricalProcess.Countable.centeredSup
    (supportedObsLaw P) F.f x
  exact le_ciSup (boundedClass_centered_range_bddAbove
    (supportedObsLaw P) F x) ⟨t, ht, hloss⟩

/-- Every supported localized competitor is dominated by a faithful
left-oracle five-chain class. -/
lemma supportedWitnessLocalizedProcess_le_leftFiveChain
    {ι₀ ι₁ ι₂ ι₃ : Type}
    [Countable ι₀] [Countable ι₁] [Countable ι₂] [Countable ι₃]
    (P : RowLaw) (a c z : ℝ) (hP : WellFormed P)
    (ha : 0 < a ∧ a ≤ 1 / 4)
    (hlogger : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      P.logger x ∈ Set.Ioo (0 : ℝ) 1)
    (F : Causalean.Stat.EmpiricalProcess.Countable.BoundedClass
      SupportedObservation (FiveChainIndex ι₀ ι₁ ι₂ ι₃))
    (hzero : regularizedLoss P a (fun _ => false) ≤ z →
      F.f .branch4 = fun o =>
        witnessComparisonIntegrand P a (leftThr c) (fun _ => false) o.1)
    (hright : ∀ {n : ℕ} (x : Fin n → SupportedObservation),
      Causalean.Stat.EmpiricalProcess.Countable.localizedThresholdSup
          (supportedObsLaw P) false (fun o : SupportedObservation => o.1.X)
          (leftOracleOffset P a c) (leftOracleMark P a)
          (Set.Icc (0 : ℝ) 1) (fun t => regularizedLoss P a (rightThr t)) z x ≤
        Causalean.Stat.EmpiricalProcess.Countable.centeredSup
          (supportedObsLaw P) F.f x)
    (hleft : ∀ {n : ℕ} (x : Fin n → SupportedObservation),
      Causalean.Stat.EmpiricalProcess.Countable.localizedThresholdSup
          (supportedObsLaw P) true (fun o : SupportedObservation => o.1.X)
          (leftOracleOffset P a c) (leftOracleMark P a)
          (Set.Icc (0 : ℝ) 1) (fun t => regularizedLoss P a (leftThr t)) z x ≤
        Causalean.Stat.EmpiricalProcess.Countable.centeredSup
          (supportedObsLaw P) F.f x)
    {n : ℕ} (x : Fin n → SupportedObservation)
    [IsProbabilityMeasure (supportedObsLaw P)] :
    supportedWitnessLocalizedProcess P a z (leftThr c) x ≤
      Causalean.Stat.EmpiricalProcess.Countable.centeredSup
        (supportedObsLaw P) F.f x := by
  classical
  let I := {π : ℝ → Bool // π ∈ thresholdClass ∧ regularizedLoss P a π ≤ z}
  cases isEmpty_or_nonempty I with
  | inl hempty =>
      letI := hempty
      unfold supportedWitnessLocalizedProcess
      change sSup (Set.range fun π : I =>
        |Causalean.Stat.Concentration.centeredEmpiricalAverage
          (supportedObsLaw P) x (fun o : SupportedObservation =>
            witnessComparisonIntegrand P a (leftThr c) π.1 o.1)|) ≤ _
      have hrange : Set.range (fun π : I =>
          |Causalean.Stat.Concentration.centeredEmpiricalAverage
            (supportedObsLaw P) x (fun o : SupportedObservation =>
              witnessComparisonIntegrand P a (leftThr c) π.1 o.1)|) = ∅ := by
        ext y
        constructor
        · rintro ⟨i, rfl⟩
          exact isEmptyElim i
        · simp
      rw [hrange, Real.sSup_empty]
      exact le_ciSup_of_le (boundedClass_centered_range_bddAbove
        (supportedObsLaw P) F x) (.branch4) (abs_nonneg _)
  | inr hnonempty =>
      letI := hnonempty
      unfold supportedWitnessLocalizedProcess
      apply ciSup_le
      intro π
      have bound_cutoff (upper : Bool) (t : ℝ)
          (ht : t ∈ Set.Icc (0 : ℝ) 1)
          (ρ : ℝ → Bool) (hρ : Set.EqOn π.1 ρ (Set.Icc (0 : ℝ) 1))
          (hform : ρ = if upper then leftThr t else rightThr t)
          (hloss : regularizedLoss P a ρ ≤ z) :
          |Causalean.Stat.Concentration.centeredEmpiricalAverage
            (supportedObsLaw P) x (fun o : SupportedObservation =>
              witnessComparisonIntegrand P a (leftThr c) π.1 o.1)| ≤
            Causalean.Stat.EmpiricalProcess.Countable.centeredSup
              (supportedObsLaw P) F.f x := by
        rw [witnessComparison_eq_of_eqOn P a (leftThr c) π.1 ρ hρ]
        subst ρ
        rw [← leftThresholdFunction_eq_witnessComparison P a c t upper]
        cases upper with
        | false =>
            exact (leftThresholdCentered_le_localizedThresholdSup
              P a c z false (fun u => regularizedLoss P a (rightThr u))
              hP ha hlogger t ht hloss x).trans (hright x)
        | true =>
            exact (leftThresholdCentered_le_localizedThresholdSup
              P a c z true (fun u => regularizedLoss P a (leftThr u))
              hP ha hlogger t ht hloss x).trans (hleft x)
      rcases π.2.1 with hfalse | htrue | hleftCase | hrightCase
      · have heq := witnessComparison_eq_of_eqOn P a (leftThr c) π.1
          (fun _ => false) hfalse
        have hfalseLoss : regularizedLoss P a (fun _ => false) ≤ z := by
          rw [← regularizedLoss_eq_of_eqOn P hP a π.1 (fun _ => false) hfalse]
          exact π.2.2
        rw [heq, ← hzero hfalseLoss]
        exact le_ciSup (boundedClass_centered_range_bddAbove
          (supportedObsLaw P) F x) (.branch4)
      · have hρ : Set.EqOn π.1 (rightThr 0) (Set.Icc (0 : ℝ) 1) := by
          intro y hy
          rw [htrue y hy]
          simp [rightThr, hy.1]
        have hloss : regularizedLoss P a (rightThr 0) ≤ z := by
          rw [← regularizedLoss_eq_of_eqOn P hP a π.1 (rightThr 0) hρ]
          exact π.2.2
        exact bound_cutoff false 0 (by norm_num) (rightThr 0) hρ (by simp) hloss
      · obtain ⟨t, ht, hπ⟩ := hleftCase
        have hloss : regularizedLoss P a (leftThr t) ≤ z := by
          rw [← regularizedLoss_eq_of_eqOn P hP a π.1 (leftThr t) hπ]
          exact π.2.2
        exact bound_cutoff true t ht (leftThr t) hπ (by simp) hloss
      · obtain ⟨t, ht, hπ⟩ := hrightCase
        have hloss : regularizedLoss P a (rightThr t) ≤ z := by
          rw [← regularizedLoss_eq_of_eqOn P hP a π.1 (rightThr t) hπ]
          exact π.2.2
        exact bound_cutoff false t ht (rightThr t) hπ (by simp) hloss

end CausalSmith.Stat.ScorethresholdOverlapRegret
