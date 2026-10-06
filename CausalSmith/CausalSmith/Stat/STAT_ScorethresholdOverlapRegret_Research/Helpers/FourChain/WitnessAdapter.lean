module
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.FourChain.WitnessSkeleton

/-! # Five-chain localized-process adapter -/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal

namespace CausalSmith.Stat.ScorethresholdOverlapRegret
lemma coverEnergy_sq_integrable {Ω ι : Type} [MeasurableSpace Ω]
    {F : Causalean.Stat.EmpiricalProcess.Countable.BoundedClass Ω ι}
    {m n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (cover : Causalean.Stat.EmpiricalProcess.Countable.ChainCover F m)
    (b : Fin m) (hU : MeasurableSet (cover.containing b))
    (hw : Measurable (cover.weight b)) (K : ℝ) (hK : 0 ≤ K)
    (hwK : ∀ x, |cover.weight b x| ≤ K) :
    Integrable (fun x : Fin n → Ω =>
      Causalean.Stat.EmpiricalProcess.Countable.coverEnergy cover x b ^ 2)
      (Measure.pi (fun _ : Fin n => μ)) := by
  classical
  let E : (Fin n → Ω) → ℝ := fun x =>
    Causalean.Stat.EmpiricalProcess.Countable.coverEnergy cover x b
  have hterm (j : Fin n) : Measurable (fun x : Fin n → Ω =>
      if x j ∈ cover.containing b then cover.weight b (x j) ^ 2 else 0) := by
    exact Measurable.ite ((hU.preimage (measurable_pi_apply j)))
      ((hw.comp (measurable_pi_apply j :
        Measurable (fun x : Fin n → Ω => x j))).pow_const 2) measurable_const
  have hEm : Measurable E := by
    unfold E Causalean.Stat.EmpiricalProcess.Countable.coverEnergy
    unfold Causalean.Stat.EmpiricalProcess.Countable.chainEnergy
    exact Finset.measurable_sum _ (fun j _ => hterm j)
  have hE0 (x : Fin n → Ω) : 0 ≤ E x := by
    unfold E Causalean.Stat.EmpiricalProcess.Countable.coverEnergy
    unfold Causalean.Stat.EmpiricalProcess.Countable.chainEnergy
    exact Finset.sum_nonneg fun j _ => by split_ifs <;> positivity
  have hEle (x : Fin n → Ω) : E x ≤ (n : ℝ) * K ^ 2 := by
    unfold E Causalean.Stat.EmpiricalProcess.Countable.coverEnergy
    unfold Causalean.Stat.EmpiricalProcess.Countable.chainEnergy
    calc
      (∑ j, if x j ∈ cover.containing b then cover.weight b (x j) ^ 2 else 0)
          ≤ ∑ _j : Fin n, K ^ 2 := by
        apply Finset.sum_le_sum
        intro j hj
        split_ifs
        · rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hwK (x j)) 2
        · exact sq_nonneg K
      _ = (n : ℝ) * K ^ 2 := by simp
  apply Integrable.of_bound (hEm.pow_const 2).aestronglyMeasurable
    (((n : ℝ) * K ^ 2) ^ 2)
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (E x))]
  exact pow_le_pow_left₀ (hE0 x) (hEle x) 2

/-- A branch energy on the supported observation subtype has the same
second moment as the corresponding restricted score energy under the
original iid observation law. -/
lemma integral_coverEnergy_eq_chainScore
    {ι : Type} {F : Causalean.Stat.EmpiricalProcess.Countable.BoundedClass
      SupportedObservation ι} {m : ℕ}
    (P : RowLaw) (hP : WellFormed P) (a : ℝ) (n : ℕ)
    [IsProbabilityMeasure P.obsLaw]
    (cover : Causalean.Stat.EmpiricalProcess.Countable.ChainCover F m)
    (b : Fin m) (B : Set ℝ) (hB : MeasurableSet B)
    (hcontaining : cover.containing b = {o | o.1.X ∈ B})
    (hweight : ∀ o, cover.weight b o ^ 2 = zScore a P.logger o.1 ^ 2) :
    (∫ d : Fin n → SupportedObservation,
        Causalean.Stat.EmpiricalProcess.Countable.coverEnergy cover d b ^ 2
        ∂Measure.pi (fun _ : Fin n => supportedObsLaw P)) =
      ∫ d, (∑ i : Fin n,
        ({o : Observation | o.X ∈ B}.indicator
          (fun o => zScore a P.logger o ^ 2)) (d i)) ^ 2
        ∂sampleLaw P n := by
  classical
  let g : (Fin n → Observation) → ℝ := fun d =>
    (∑ i : Fin n, ({o : Observation | o.X ∈ B}.indicator
      (fun o => zScore a P.logger o ^ 2)) (d i)) ^ 2
  have hset : MeasurableSet {o : Observation | o.X ∈ B} :=
    hB.preimage score_observation_X_measurable
  have hf : AEMeasurable
      ({o : Observation | o.X ∈ B}.indicator
        (fun o => zScore a P.logger o ^ 2)) P.obsLaw :=
    ((score_z_aemeasurable P hP a).pow_const 2).indicator hset
  have hg : AEStronglyMeasurable g (sampleLaw P n) := by
    apply AEMeasurable.aestronglyMeasurable
    change AEMeasurable (fun d : Fin n → Observation =>
      (∑ i : Fin n, ({o : Observation | o.X ∈ B}.indicator
        (fun o => zScore a P.logger o ^ 2)) (d i)) ^ 2) _
    have hfi (i : Fin n) : AEMeasurable (fun d : Fin n → Observation =>
        ({o : Observation | o.X ∈ B}.indicator
          (fun o => zScore a P.logger o ^ 2)) (d i))
        (Measure.pi fun _ : Fin n => P.obsLaw) := by
      convert hf.comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_eval
          (fun _ : Fin n => P.obsLaw) i) using 1
      funext d
      rfl
    convert (Finset.aemeasurable_sum Finset.univ
      fun i _ => hfi i).pow_const 2 using 1
    · funext d
      simp
    · rfl
  rw [← integral_supportedSampleLaw P hP n g hg]
  apply integral_congr_ae
  apply ae_of_all
  intro d
  unfold Causalean.Stat.EmpiricalProcess.Countable.coverEnergy
    Causalean.Stat.EmpiricalProcess.Countable.chainEnergy g
  change (∑ i : Fin n,
      if d i ∈ cover.containing b then cover.weight b (d i) ^ 2 else 0) ^ 2 =
    (∑ i : Fin n, ({o : Observation | o.X ∈ B}.indicator
      (fun o => zScore a P.logger o ^ 2)) (d i).1) ^ 2
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [hcontaining]
  by_cases hmem : (d i).1.X ∈ B
  · have hmem' : d i ∈ {o : SupportedObservation | o.1.X ∈ B} := hmem
    rw [Set.indicator_of_mem
        (show (d i).1 ∈ {o : Observation | o.X ∈ B} from hmem),
      if_pos hmem', hweight]
  · rw [Set.indicator_of_notMem
        (show (d i).1 ∉ {o : Observation | o.X ∈ B} from hmem),
      if_neg (show d i ∉ {o : SupportedObservation | o.1.X ∈ B} from hmem)]

/-- The run-local restricted-score estimate supplies a branch energy budget
once the containing set and squared weight have been identified. -/
lemma coverEnergy_second_moment_le
    {ι : Type} {F : Causalean.Stat.EmpiricalProcess.Countable.BoundedClass
      SupportedObservation ι} {m : ℕ}
    (α γ θ : ℝ) (n : ℕ) (P : RowLaw) (e : ℝ → ℝ)
    (hP : LawClass α γ θ n P e) (hn : 0 < n)
    (a z : ℝ) (ha : 0 < a ∧ a ≤ 1 / 4)
    (cover : Causalean.Stat.EmpiricalProcess.Countable.ChainCover F m)
    (b : Fin m) (B : Set ℝ) (hB : MeasurableSet B)
    (hmass : (∫ x in B, offsetG a P.logger x ∂P.PX) ≤ z)
    (hcontaining : cover.containing b = {o | o.1.X ∈ B})
    (hweight : ∀ o, cover.weight b o ^ 2 = zScore a P.logger o.1 ^ 2)
    [IsProbabilityMeasure P.obsLaw] :
    (∫ d : Fin n → SupportedObservation,
      Causalean.Stat.EmpiricalProcess.Countable.coverEnergy cover d b ^ 2
      ∂Measure.pi (fun _ : Fin n => supportedObsLaw P)) ≤
      24 * (n : ℝ) * z / a ^ 3 + 36 * (n : ℝ) ^ 2 * z ^ 2 / a ^ 2 := by
  rw [integral_coverEnergy_eq_chainScore P hP.wf a n cover b B hB
    hcontaining hweight]
  exact chain_score_energy_second_moment α γ θ n P e hP hn a z ha B hB hmass

/-- Policies agreeing on the score support have the same regularized loss. -/
lemma regularizedLoss_eq_of_eqOn (P : RowLaw) (hP : WellFormed P)
    (a : ℝ) (π ρ : ℝ → Bool)
    (h : Set.EqOn π ρ (Set.Icc (0 : ℝ) 1)) :
    regularizedLoss P a π = regularizedLoss P a ρ := by
  have hs : ∀ᵐ x ∂P.PX, x ∈ Set.Icc (0 : ℝ) 1 :=
    (ae_map_iff fullRow_X_measurable.aemeasurable measurableSet_Icc).2
      (ae_iff.mpr hP.2.1)
  have hw : rawWelfare P π = rawWelfare P ρ := by
    unfold rawWelfare
    apply integral_congr_ae
    filter_upwards [hs] with x hx
    rw [h hx]
  have ho : offsetDisagreement P a π = offsetDisagreement P a ρ := by
    unfold offsetDisagreement
    apply integral_congr_ae
    filter_upwards [hs] with x hx
    rw [h hx]
  unfold regularizedLoss rawRegret
  rw [hw, ho]

/-- The supported witness comparison depends only on the competitor's
restriction to the score support. -/
lemma witnessComparison_eq_of_eqOn (P : RowLaw) (a : ℝ)
    (πstar π ρ : ℝ → Bool)
    (h : Set.EqOn π ρ (Set.Icc (0 : ℝ) 1)) :
    (fun o : SupportedObservation =>
      witnessComparisonIntegrand P a πstar π o.1) =
    fun o => witnessComparisonIntegrand P a πstar ρ o.1 := by
  funext o
  simp only [witnessComparisonIntegrand, h o.2.1]

/-- Population centering of a supported comparison can be computed either
under the supported comap law or the original observation law. -/
lemma integral_supported_witnessComparison (P : RowLaw) (hP : WellFormed P)
    (a : ℝ) (πstar π : ℝ → Bool) :
    (∫ o : SupportedObservation,
      witnessComparisonIntegrand P a πstar π o.1 ∂supportedObsLaw P) =
    ∫ o, witnessComparisonIntegrand P a πstar π o ∂P.obsLaw :=
  integral_supportedObsLaw P hP (witnessComparisonIntegrand P a πstar π)

/-- The range defining a bounded class's centered supremum is bounded above;
this is the side condition needed for real-valued `iSup` reindexing. -/
lemma boundedClass_centered_range_bddAbove {Ω ι : Type}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Causalean.Stat.EmpiricalProcess.Countable.BoundedClass Ω ι)
    {n : ℕ} (x : Fin n → Ω) :
    BddAbove (Set.range fun i =>
      |Causalean.Stat.Concentration.centeredEmpiricalAverage μ x (F.f i)|) := by
  refine ⟨2 * F.bound, ?_⟩
  rintro _ ⟨i, rfl⟩
  have hi : |∫ z, F.f i z ∂μ| ≤ F.bound := by
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
      (norm_integral_le_of_norm_le_const (f := F.f i) (C := F.bound)
        (ae_of_all μ fun z => by
          simpa only [Real.norm_eq_abs] using F.bounded i z))
  exact (abs_sub _ _).trans (by
    have ha := Causalean.Stat.EmpiricalProcess.Countable.normalized_sum_bound
      (fun j => F.f i (x j)) F.bound F.bound_nonneg
      (fun j => F.bounded i (x j))
    change |(n : ℝ)⁻¹ * ∑ j, F.f i (x j)| +
      |∫ z, F.f i z ∂μ| ≤ _
    linarith)

/-- Reindexing a bounded centered class into another bounded centered class
cannot increase its real supremum. -/
lemma centeredSup_le_of_reindex {Ω ι κ : Type} [MeasurableSpace Ω]
    [Nonempty ι] [Nonempty κ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Causalean.Stat.EmpiricalProcess.Countable.BoundedClass Ω ι)
    (G : Causalean.Stat.EmpiricalProcess.Countable.BoundedClass Ω κ)
    (φ : ι → κ) (hφ : ∀ i, F.f i = G.f (φ i))
    {n : ℕ} (x : Fin n → Ω) :
    Causalean.Stat.EmpiricalProcess.Countable.centeredSup μ F.f x ≤
      Causalean.Stat.EmpiricalProcess.Countable.centeredSup μ G.f x := by
  unfold Causalean.Stat.EmpiricalProcess.Countable.centeredSup
  apply ciSup_le
  intro i
  rw [hφ i]
  exact le_ciSup (boundedClass_centered_range_bddAbove μ G x) (φ i)

/-- A possibly empty centered family is dominated when each of its members
is represented in a nonempty bounded target class.  The empty-family case is
handled at its actual real value, zero. -/
lemma centeredSup_le_of_exists_reindex {Ω ι κ : Type} [MeasurableSpace Ω]
    [Nonempty κ] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : Causalean.Stat.EmpiricalProcess.Countable.BoundedClass Ω κ)
    (f : ι → Ω → ℝ) (hrep : ∀ i, ∃ k, f i = G.f k)
    {n : ℕ} (x : Fin n → Ω) :
    Causalean.Stat.EmpiricalProcess.Countable.centeredSup μ f x ≤
      Causalean.Stat.EmpiricalProcess.Countable.centeredSup μ G.f x := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hempty =>
      letI := hempty
      unfold Causalean.Stat.EmpiricalProcess.Countable.centeredSup
      change sSup (Set.range fun i : ι =>
        |Causalean.Stat.Concentration.centeredEmpiricalAverage μ x (f i)|) ≤ _
      have hrange : Set.range (fun i : ι =>
          |Causalean.Stat.Concentration.centeredEmpiricalAverage μ x (f i)|) = ∅ := by
        ext y
        constructor
        · rintro ⟨i, rfl⟩
          exact isEmptyElim i
        · simp
      rw [hrange, Real.sSup_empty]
      exact le_ciSup_of_le (boundedClass_centered_range_bddAbove μ G x)
        (Classical.choice inferInstance) (abs_nonneg _)
  | inr hnonempty =>
      letI := hnonempty
      let φ : ι → κ := fun i => Classical.choose (hrep i)
      let F : Causalean.Stat.EmpiricalProcess.Countable.BoundedClass Ω ι := {
        f := f
        bound := G.bound
        bound_nonneg := G.bound_nonneg
        measurable := fun i => by
          rw [Classical.choose_spec (hrep i)]
          exact G.measurable (φ i)
        bounded := fun i y => by
          rw [Classical.choose_spec (hrep i)]
          exact G.bounded (φ i) y }
      exact centeredSup_le_of_reindex μ F G φ
        (fun i => Classical.choose_spec (hrep i)) x

/-- The lower-orientation localized skeleton embeds into branches zero and
one of the faithful five-chain class. -/
lemma rightSkeleton_centeredSup_le_fiveChain
    {ι₀ ι₁ ι₂ ι₃ : Type}
    [Countable ι₀] [Countable ι₁] [Countable ι₂] [Countable ι₃]
    (P : RowLaw) (a c z : ℝ)
    (S : RightOracleLocalizedSkeleton P a c z false)
    (F : Causalean.Stat.EmpiricalProcess.Countable.BoundedClass
      SupportedObservation (FiveChainIndex ι₀ ι₁ ι₂ ι₃))
    (embedBelow : {t : S.D // t.1 < c} → ι₀)
    (embedAbove : {t : S.D // c ≤ t.1} → ι₁)
    (hbelow : ∀ i, F.f (.branch0 (embedBelow i)) = fun o =>
      witnessComparisonIntegrand P a (rightThr c) (rightThr i.1.1) o.1)
    (habove : ∀ i, F.f (.branch1 (embedAbove i)) = fun o =>
      witnessComparisonIntegrand P a (rightThr c) (rightThr i.1.1) o.1)
    {n : ℕ} (x : Fin n → SupportedObservation)
    [IsProbabilityMeasure (supportedObsLaw P)] :
    Causalean.Stat.EmpiricalProcess.Countable.centeredSup
      (supportedObsLaw P)
      (fun t : S.D =>
        Causalean.Stat.EmpiricalProcess.Countable.thresholdFunction false
          (fun o : SupportedObservation => o.1.X)
          (rightOracleOffset P a c) (rightOracleMark P a) t.1) x ≤
    Causalean.Stat.EmpiricalProcess.Countable.centeredSup
      (supportedObsLaw P) F.f x := by
  apply centeredSup_le_of_exists_reindex (supportedObsLaw P) F _
  intro t
  rcases lt_or_ge t.1 c with ht | ht
  · let i : {u : S.D // u.1 < c} := ⟨t, ht⟩
    refine ⟨.branch0 (embedBelow i), ?_⟩
    rw [thresholdFunction_eq_witnessComparison]
    exact (hbelow i).symm
  · let i : {u : S.D // c ≤ u.1} := ⟨t, ht⟩
    refine ⟨.branch1 (embedAbove i), ?_⟩
    rw [thresholdFunction_eq_witnessComparison]
    exact (habove i).symm

/-- The upper-orientation localized skeleton embeds into branches two and
three of the faithful five-chain class. -/
lemma leftSkeleton_centeredSup_le_fiveChain
    {ι₀ ι₁ ι₂ ι₃ : Type}
    [Countable ι₀] [Countable ι₁] [Countable ι₂] [Countable ι₃]
    (P : RowLaw) (a c z : ℝ)
    (S : RightOracleLocalizedSkeleton P a c z true)
    (F : Causalean.Stat.EmpiricalProcess.Countable.BoundedClass
      SupportedObservation (FiveChainIndex ι₀ ι₁ ι₂ ι₃))
    (embedBelow : {t : S.D // t.1 < c} → ι₂)
    (embedAbove : {t : S.D // c ≤ t.1} → ι₃)
    (hbelow : ∀ i, F.f (.branch2 (embedBelow i)) = fun o =>
      witnessComparisonIntegrand P a (rightThr c) (leftThr i.1.1) o.1)
    (habove : ∀ i, F.f (.branch3 (embedAbove i)) = fun o =>
      witnessComparisonIntegrand P a (rightThr c) (leftThr i.1.1) o.1)
    {n : ℕ} (x : Fin n → SupportedObservation)
    [IsProbabilityMeasure (supportedObsLaw P)] :
    Causalean.Stat.EmpiricalProcess.Countable.centeredSup
      (supportedObsLaw P)
      (fun t : S.D =>
        Causalean.Stat.EmpiricalProcess.Countable.thresholdFunction true
          (fun o : SupportedObservation => o.1.X)
          (rightOracleOffset P a c) (rightOracleMark P a) t.1) x ≤
    Causalean.Stat.EmpiricalProcess.Countable.centeredSup
      (supportedObsLaw P) F.f x := by
  apply centeredSup_le_of_exists_reindex (supportedObsLaw P) F _
  intro t
  rcases lt_or_ge t.1 c with ht | ht
  · let i : {u : S.D // u.1 < c} := ⟨t, ht⟩
    refine ⟨.branch2 (embedBelow i), ?_⟩
    rw [thresholdFunction_eq_witnessComparison]
    exact (hbelow i).symm
  · let i : {u : S.D // c ≤ u.1} := ⟨t, ht⟩
    refine ⟨.branch3 (embedAbove i), ?_⟩
    rw [thresholdFunction_eq_witnessComparison]
    exact (habove i).symm

/-- The two atom-safe localized skeletons for a right oracle admit one
explicit faithful five-chain class, and both localized threshold suprema are
pointwise dominated by its centered supremum. -/
lemma exists_rightOracle_skeleton_fiveChain
    (P : RowLaw) (a c z : ℝ) (hP : WellFormed P)
    (ha : 0 < a ∧ a ≤ 1 / 4)
    (hlogger : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      P.logger x ∈ Set.Ioo (0 : ℝ) 1)
    (Sright : RightOracleLocalizedSkeleton P a c z false)
    (Sleft : RightOracleLocalizedSkeleton P a c z true)
    [IsProbabilityMeasure (supportedObsLaw P)] :
    ∃ F : Causalean.Stat.EmpiricalProcess.Countable.BoundedClass
        SupportedObservation
        (FiveChainIndex
          {t : Sright.D // t.1 < c} {t : Sright.D // c ≤ t.1}
          {t : Sleft.D // t.1 < c} {t : Sleft.D // c ≤ t.1}),
      ∃ cover : Causalean.Stat.EmpiricalProcess.Countable.ChainCover F 5,
        (∀ (n : ℕ) (x : Fin n → SupportedObservation),
          Causalean.Stat.EmpiricalProcess.Countable.localizedThresholdSup
              (supportedObsLaw P) false
              (fun o : SupportedObservation => o.1.X)
              (rightOracleOffset P a c) (rightOracleMark P a)
              (Set.Icc (0 : ℝ) 1)
              (fun t => regularizedLoss P a (rightThr t)) z x ≤
            Causalean.Stat.EmpiricalProcess.Countable.centeredSup
              (supportedObsLaw P) F.f x ∧
          Causalean.Stat.EmpiricalProcess.Countable.localizedThresholdSup
              (supportedObsLaw P) true
              (fun o : SupportedObservation => o.1.X)
              (rightOracleOffset P a c) (rightOracleMark P a)
              (Set.Icc (0 : ℝ) 1)
              (fun t => regularizedLoss P a (leftThr t)) z x ≤
            Causalean.Stat.EmpiricalProcess.Countable.centeredSup
              (supportedObsLaw P) F.f x) ∧
        (F.f .branch4 = fun o => witnessComparisonIntegrand P a (rightThr c)
          (if decide (regularizedLoss P a (fun _ => false) ≤ z)
            then (fun _ => false) else rightThr c) o.1) ∧
        (∀ b, cover.weight b = rightOracleWeight P a c) ∧
        (cover.containing 0 = ⋃ i : {t : Sright.D // t.1 < c},
          rightBelowSet c i.1.1) ∧
        (cover.containing 1 = ⋃ i : {t : Sright.D // c ≤ t.1},
          rightAboveSet c i.1.1) ∧
        (cover.containing 2 = ⋃ i : {t : Sleft.D // t.1 < c},
          leftBelowSet c i.1.1) ∧
        (cover.containing 3 = ⋃ i : {t : Sleft.D // c ≤ t.1},
          leftAboveSet c i.1.1) ∧
        (cover.containing 4 = if decide
          (regularizedLoss P a (fun _ => false) ≤ z)
            then zeroBranchSet c else ∅) := by
  letI : Countable Sright.D := Sright.countable
  letI : Countable Sleft.D := Sleft.countable
  obtain ⟨F, cover, hrest⟩ :=
    exists_rightOracle_fiveChain P a c
      (decide (regularizedLoss P a (fun _ => false) ≤ z)) hP ha hlogger
      (fun i : {t : Sright.D // t.1 < c} => i.1.1) (fun i => i.2)
      (fun i : {t : Sright.D // c ≤ t.1} => i.1.1) (fun i => i.2)
      (fun i : {t : Sleft.D // t.1 < c} => i.1.1) (fun i => i.2)
      (fun i : {t : Sleft.D // c ≤ t.1} => i.1.1) (fun i => i.2)
  rcases hrest with ⟨h₀, h₁, h₂, h₃, h₄, hw, hU₀, hU₁,
    hU₂, hU₃, hU₄⟩
  refine ⟨F, cover, ?_, h₄, hw, hU₀, hU₁, hU₂, hU₃, hU₄⟩
  intro n x
  constructor
  · have hreduction := Sright.reduction n x
    simp only [Bool.false_eq_true, if_false] at hreduction
    rw [hreduction]
    exact rightSkeleton_centeredSup_le_fiveChain P a c z Sright F
      (fun i => i) (fun i => i) h₀ h₁ x
  · have hreduction := Sleft.reduction n x
    simp only [if_true] at hreduction
    rw [hreduction]
    exact leftSkeleton_centeredSup_le_fiveChain P a c z Sleft F
      (fun i => i) (fun i => i) h₂ h₃ x

/-- The full eligible cutoff family is uniformly bounded on the supported
observation subtype. -/
@[no_expose]
noncomputable def rightOracleThresholdBoundedClass (P : RowLaw)
    (a c : ℝ) (upper : Bool) (loss : ℝ → ℝ) (z : ℝ)
    (hP : WellFormed P) (ha : 0 < a ∧ a ≤ 1 / 4)
    (hlogger : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      P.logger x ∈ Set.Ioo (0 : ℝ) 1) :
    Causalean.Stat.EmpiricalProcess.Countable.BoundedClass
      SupportedObservation {t : ℝ // t ∈ Set.Icc (0 : ℝ) 1 ∧ loss t ≤ z} := {
  f := fun t => Causalean.Stat.EmpiricalProcess.Countable.thresholdFunction
    upper (fun o : SupportedObservation => o.1.X)
    (rightOracleOffset P a c) (rightOracleMark P a) t.1
  bound := 4 / a
  bound_nonneg := div_nonneg (by norm_num) ha.1.le
  measurable := fun t =>
    Causalean.Stat.EmpiricalProcess.Countable.thresholdFunction_measurable
      upper _ _ _ supportedObservation_X_measurable
      (rightOracleOffset_measurable P a c hP)
      (rightOracleMark_measurable P a hP) t.1
  bounded := fun t o => by
    have hoff := rightOracleOffset_abs_le P a c ha hlogger o
    have hmark := rightOracleMark_abs_le P a ha hlogger o
    have h24 : 2 / a ≤ 4 / a :=
      div_le_div_of_nonneg_right (by norm_num) ha.1.le
    unfold Causalean.Stat.EmpiricalProcess.Countable.thresholdFunction
    split_ifs <;> first
    | calc
        |rightOracleOffset P a c o + rightOracleMark P a o|
            ≤ |rightOracleOffset P a c o| + |rightOracleMark P a o| :=
              abs_add_le _ _
        _ ≤ 2 / a + 2 / a := add_le_add hoff hmark
        _ = 4 / a := by ring
    | simpa only [add_zero] using hoff.trans h24 }

/-- One eligible cutoff's centered value is below the corresponding full
localized threshold supremum. -/
lemma thresholdCentered_le_localizedThresholdSup
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
        (rightOracleOffset P a c) (rightOracleMark P a) t)| ≤
      Causalean.Stat.EmpiricalProcess.Countable.localizedThresholdSup
        (supportedObsLaw P) upper (fun o : SupportedObservation => o.1.X)
        (rightOracleOffset P a c) (rightOracleMark P a)
        (Set.Icc (0 : ℝ) 1) loss z x := by
  let F := rightOracleThresholdBoundedClass P a c upper loss z hP ha hlogger
  change _ ≤ Causalean.Stat.EmpiricalProcess.Countable.centeredSup
    (supportedObsLaw P) F.f x
  exact le_ciSup (boundedClass_centered_range_bddAbove
    (supportedObsLaw P) F x) ⟨t, ht, hloss⟩

/-- The witness-localized process written directly on supported observations. -/
@[expose] noncomputable def supportedWitnessLocalizedProcess {n : ℕ} (P : RowLaw)
    (a z : ℝ) (πstar : ℝ → Bool) (x : Fin n → SupportedObservation) : ℝ :=
  ⨆ π : {π : ℝ → Bool // π ∈ thresholdClass ∧ regularizedLoss P a π ≤ z},
    |Causalean.Stat.Concentration.centeredEmpiricalAverage
      (supportedObsLaw P) x
      (fun o : SupportedObservation =>
        witnessComparisonIntegrand P a πstar π.1 o.1)|

/-- The original-law witness process and the supported-law witness process
agree exactly on a supported sample. -/
lemma witnessLocalizedProcess_on_supported {n : ℕ} (P : RowLaw)
    (hP : WellFormed P) (a z : ℝ) (πstar : ℝ → Bool)
    (x : Fin n → SupportedObservation) :
    witnessLocalizedProcess P a z πstar (fun i => (x i).1) =
      supportedWitnessLocalizedProcess P a z πstar x := by
  unfold witnessLocalizedProcess supportedWitnessLocalizedProcess
  apply iSup_congr
  intro π
  rw [← integral_supported_witnessComparison P hP a πstar π.1]
  rfl

/-- Any a.e. canonical witness transports the original localized process to
the corresponding supported witness process under the supported iid law. -/
lemma localizedProcess_ae_eq_supportedWitness_of_ae
    {n : ℕ} (P : RowLaw) (hP : WellFormed P) (a z : ℝ)
    (πstar : ℝ → Bool) (hstar : πstar =ᵐ[P.PX] canonicalPolicy P)
    [IsProbabilityMeasure P.obsLaw] :
    (fun x : Fin n → SupportedObservation =>
      localizedProcess P a z (fun i => (x i).1)) =ᵐ[
        Measure.pi (fun _ : Fin n => supportedObsLaw P)]
      supportedWitnessLocalizedProcess P a z πstar := by
  letI : IsProbabilityMeasure (supportedObsLaw P) :=
    supportedObsLaw_isProbabilityMeasure P hP
  have hX : AEMeasurable Observation.X P.obsLaw :=
    score_observation_X_measurable.aemeasurable
  have hrowObs : ∀ᵐ o ∂P.obsLaw,
      πstar o.X = canonicalPolicy P o.X := by
    apply ae_of_ae_map hX
      (p := fun y => πstar y = canonicalPolicy P y)
    rw [score_observation_X_map]
    exact hstar
  have hrowSup : ∀ᵐ o ∂supportedObsLaw P,
      πstar o.1.X = canonicalPolicy P o.1.X := by
    have he := (MeasurableEmbedding.subtype_coe
      supportedObservation_measurableSet).ae_map_iff
      (p := fun o : Observation =>
        πstar o.X = canonicalPolicy P o.X)
      (μ := supportedObsLaw P)
    rw [supportedObsLaw_map_val P hP] at he
    exact he.mp hrowObs
  have hall : ∀ᵐ x ∂Measure.pi (fun _ : Fin n => supportedObsLaw P),
      ∀ i, πstar (x i).1.X = canonicalPolicy P (x i).1.X := by
    rw [ae_all_iff]
    intro i
    exact (Measure.tendsto_eval_ae_ae
      (μ := fun _ : Fin n => supportedObsLaw P) (i := i)) hrowSup
  filter_upwards [hall] with x hx
  rw [localizedProcess_eq_witness_on_sample P a z πstar hstar
    (fun i => (x i).1) hx]
  exact witnessLocalizedProcess_on_supported P hP a z πstar x

/-- Every supported localized competitor, including both constant cases and
arbitrary representatives that agree only on `[0,1]`, is dominated by the
faithful five-chain class. -/
lemma supportedWitnessLocalizedProcess_le_fiveChain
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
        witnessComparisonIntegrand P a (rightThr c) (fun _ => false) o.1)
    (hright : ∀ {n : ℕ} (x : Fin n → SupportedObservation),
      Causalean.Stat.EmpiricalProcess.Countable.localizedThresholdSup
          (supportedObsLaw P) false (fun o : SupportedObservation => o.1.X)
          (rightOracleOffset P a c) (rightOracleMark P a)
          (Set.Icc (0 : ℝ) 1) (fun t => regularizedLoss P a (rightThr t)) z x ≤
        Causalean.Stat.EmpiricalProcess.Countable.centeredSup
          (supportedObsLaw P) F.f x)
    (hleft : ∀ {n : ℕ} (x : Fin n → SupportedObservation),
      Causalean.Stat.EmpiricalProcess.Countable.localizedThresholdSup
          (supportedObsLaw P) true (fun o : SupportedObservation => o.1.X)
          (rightOracleOffset P a c) (rightOracleMark P a)
          (Set.Icc (0 : ℝ) 1) (fun t => regularizedLoss P a (leftThr t)) z x ≤
        Causalean.Stat.EmpiricalProcess.Countable.centeredSup
          (supportedObsLaw P) F.f x)
    {n : ℕ} (x : Fin n → SupportedObservation)
    [IsProbabilityMeasure (supportedObsLaw P)] :
    supportedWitnessLocalizedProcess P a z (rightThr c) x ≤
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
            witnessComparisonIntegrand P a (rightThr c) π.1 o.1)|) ≤ _
      have hrange : Set.range (fun π : I =>
          |Causalean.Stat.Concentration.centeredEmpiricalAverage
            (supportedObsLaw P) x (fun o : SupportedObservation =>
              witnessComparisonIntegrand P a (rightThr c) π.1 o.1)|) = ∅ := by
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
              witnessComparisonIntegrand P a (rightThr c) π.1 o.1)| ≤
            Causalean.Stat.EmpiricalProcess.Countable.centeredSup
              (supportedObsLaw P) F.f x := by
        rw [witnessComparison_eq_of_eqOn P a (rightThr c) π.1 ρ hρ]
        subst ρ
        rw [← thresholdFunction_eq_witnessComparison P a c t upper]
        cases upper with
        | false =>
            exact (thresholdCentered_le_localizedThresholdSup P a c z false
              (fun u => regularizedLoss P a (rightThr u)) hP ha hlogger
              t ht hloss x).trans (hright x)
        | true =>
            exact (thresholdCentered_le_localizedThresholdSup P a c z true
              (fun u => regularizedLoss P a (leftThr u)) hP ha hlogger
              t ht hloss x).trans (hleft x)
      rcases π.2.1 with hfalse | htrue | hleftCase | hrightCase
      · have heq := witnessComparison_eq_of_eqOn P a (rightThr c) π.1
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
        have hρ : Set.EqOn π.1 (leftThr t) (Set.Icc (0 : ℝ) 1) := hπ
        have hloss : regularizedLoss P a (leftThr t) ≤ z := by
          rw [← regularizedLoss_eq_of_eqOn P hP a π.1 (leftThr t) hρ]
          exact π.2.2
        exact bound_cutoff true t ht (leftThr t) hρ (by simp) hloss
      · obtain ⟨t, ht, hπ⟩ := hrightCase
        have hρ : Set.EqOn π.1 (rightThr t) (Set.Icc (0 : ℝ) 1) := hπ
        have hloss : regularizedLoss P a (rightThr t) ≤ z := by
          rw [← regularizedLoss_eq_of_eqOn P hP a π.1 (rightThr t) hρ]
          exact π.2.2
        exact bound_cutoff false t ht (rightThr t) hρ (by simp) hloss

/-- A supported-process domination for any canonical witness lifts a.e. to
fourth powers of the paper process. -/
lemma localizedProcess_fourth_ae_le_fiveChain_of_ae
    {ι : Type} [Countable ι] [Nonempty ι]
    {n : ℕ} (P : RowLaw) (hP : WellFormed P) (a z : ℝ)
    (πstar : ℝ → Bool) (hstar : πstar =ᵐ[P.PX] canonicalPolicy P)
    (F : Causalean.Stat.EmpiricalProcess.Countable.BoundedClass
      SupportedObservation ι)
    (hdom : ∀ x : Fin n → SupportedObservation,
      supportedWitnessLocalizedProcess P a z πstar x ≤
        Causalean.Stat.EmpiricalProcess.Countable.centeredSup
          (supportedObsLaw P) F.f x)
    [IsProbabilityMeasure P.obsLaw] :
    (fun x : Fin n → SupportedObservation =>
      localizedProcess P a z (fun i => (x i).1) ^ 4) ≤ᵐ[
        Measure.pi (fun _ : Fin n => supportedObsLaw P)]
      fun x => Causalean.Stat.EmpiricalProcess.Countable.centeredSup
        (supportedObsLaw P) F.f x ^ 4 := by
  have heq := localizedProcess_ae_eq_supportedWitness_of_ae
    P hP a z πstar hstar (n := n)
  filter_upwards [heq] with x hx
  rw [hx]
  exact pow_le_pow_left₀
    (by
      unfold supportedWitnessLocalizedProcess
      exact Real.iSup_nonneg fun _ => abs_nonneg _)
    (hdom x) 4

/-- The exact remaining construction interface for the new countable L4
substrate. It packages a supported countable class, its five-chain cover,
the transport of the paper process to that class, and the five energy
budgets already supplied by `chain_score_energy_second_moment`. -/
structure LocalizedProcessL4Adapter {n : ℕ} (P : RowLaw) (a z : ℝ) where
  Index : Type
  countableIndex : Countable Index
  nonemptyIndex : Nonempty Index
  probability : IsProbabilityMeasure (supportedObsLaw P)
  F : Causalean.Stat.EmpiricalProcess.Countable.BoundedClass
    SupportedObservation Index
  cover : Causalean.Stat.EmpiricalProcess.Countable.ChainCover F 5
  moment_le :
    (∫ d, localizedProcess P a z d ^ 4 ∂sampleLaw P n) ≤
      ∫ d, Causalean.Stat.EmpiricalProcess.Countable.centeredSup
        (supportedObsLaw P) F.f d ^ 4
        ∂Measure.pi (fun _ : Fin n => supportedObsLaw P)
  energy_integrable : ∀ b,
    Integrable (fun d : Fin n → SupportedObservation =>
      Causalean.Stat.EmpiricalProcess.Countable.coverEnergy cover d b ^ 2)
      (Measure.pi (fun _ : Fin n => supportedObsLaw P))
  energy_le : ∀ b,
    (∫ d : Fin n → SupportedObservation,
      Causalean.Stat.EmpiricalProcess.Countable.coverEnergy cover d b ^ 2
      ∂Measure.pi (fun _ : Fin n => supportedObsLaw P)) ≤
      24 * (n : ℝ) * z / a ^ 3 + 36 * (n : ℝ) ^ 2 * z ^ 2 / a ^ 2

/-- Once the faithful five-branch adapter is constructed, the promoted
substrate and its explicit arithmetic close the frozen fourth-moment bound. -/
lemma localizedProcess_fourth_moment_of_adapter
    (build : ∀ (α γ θ : ℝ) (n : ℕ) (P : RowLaw) (e : ℝ → ℝ),
      0 < α → 0 < γ → 0 < θ → 0 < n → LawClass α γ θ n P e →
      ∀ (a z : ℝ), 0 < a → a ≤ 1 / 4 → 0 < z →
        LocalizedProcessL4Adapter (n := n) P a z) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (α γ θ : ℝ) (n : ℕ) (P : RowLaw) (e : ℝ → ℝ),
        0 < α → 0 < γ → 0 < θ → 0 < n → LawClass α γ θ n P e →
        ∀ (a z : ℝ), 0 < a → a ≤ 1 / 4 → 0 < z →
          (∫ d, localizedProcess P a z d ^ 4 ∂sampleLaw P n) ≤
            (81920 / 3 : ℝ) *
              (z ^ 2 / ((n : ℝ) ^ 2 * a ^ 2) +
                z / ((n : ℝ) ^ 3 * a ^ 3)) := by
  refine ⟨81920 / 3, by norm_num, ?_⟩
  intro α γ θ n P e hα hγ hθ hn hP a z ha ha4 hz
  let A := build α γ θ n P e hα hγ hθ hn hP a z ha ha4 hz
  letI : Countable A.Index := A.countableIndex
  letI : Nonempty A.Index := A.nonemptyIndex
  letI : IsProbabilityMeasure (supportedObsLaw P) := A.probability
  let budget : Fin 5 → ℝ := fun _ =>
    24 * (n : ℝ) * z / a ^ 3 + 36 * (n : ℝ) ^ 2 * z ^ 2 / a ^ 2
  have hsubstrate :=
    Causalean.Stat.EmpiricalProcess.Countable.centered_fourth_le_energy_budget
      (supportedObsLaw P) A.F A.cover n hn A.energy_integrable budget A.energy_le
  refine A.moment_le.trans (hsubstrate.trans ?_)
  have hsum : (∑ b, budget b) =
      5 * (24 * (n : ℝ) * z / a ^ 3 +
        36 * (n : ℝ) ^ 2 * z ^ 2 / a ^ 2) := by
    simp only [Fin.sum_univ_five, budget]
    ring
  rw [hsum]
  exact Causalean.Stat.EmpiricalProcess.Countable.five_branch_budget_arithmetic
    (n : ℝ) a z (by exact_mod_cast hn) ha hz.le


end CausalSmith.Stat.ScorethresholdOverlapRegret
