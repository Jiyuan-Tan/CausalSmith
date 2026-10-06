module
public import Causalean.Stat.EmpiricalProcess.Countable
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.FourChain.Decomposition
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.FourChain.Measurability
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.FourChain.RestrictedMoments

/-! # Canonical-threshold witness and five-chain transport

This module transports the localized threshold process to the supported
observation subtype and packages the exact five nested disagreement chains.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal

namespace CausalSmith.Stat.ScorethresholdOverlapRegret

/-- Comparison integrand with an explicit threshold representative in place
of the canonical policy. -/
noncomputable def witnessComparisonIntegrand (P : RowLaw) (a : ℝ)
    (πstar π : ℝ → Bool) (o : Observation) : ℝ :=
  ((if π o.X then (0 : ℝ) else 1) -
    (if πstar o.X then (0 : ℝ) else 1)) * zScore a P.logger o

/-- The witness-based integrand agrees almost everywhere with the original
integrand under the observation law. -/
lemma comparisonIntegrand_ae_witness (P : RowLaw) (a : ℝ)
    (πstar π : ℝ → Bool) (hstar : πstar =ᵐ[P.PX] canonicalPolicy P) :
    comparisonIntegrand P a π =ᵐ[P.obsLaw]
      witnessComparisonIntegrand P a πstar π := by
  have hX : AEMeasurable Observation.X P.obsLaw :=
    score_observation_X_measurable.aemeasurable
  have hpull : ∀ᵐ o ∂P.obsLaw,
      πstar o.X = canonicalPolicy P o.X := by
    apply ae_of_ae_map hX
      (p := fun x => πstar x = canonicalPolicy P x)
    rw [score_observation_X_map]
    exact hstar
  filter_upwards [hpull] with o ho
  simp only [comparisonIntegrand, witnessComparisonIntegrand, ho]

/-- Population centers are unchanged when the canonical policy is replaced
by its threshold witness. -/
lemma integral_comparisonIntegrand_eq_witness (P : RowLaw) (a : ℝ)
    (πstar π : ℝ → Bool) (hstar : πstar =ᵐ[P.PX] canonicalPolicy P) :
    (∫ o, comparisonIntegrand P a π o ∂P.obsLaw) =
      ∫ o, witnessComparisonIntegrand P a πstar π o ∂P.obsLaw :=
  integral_congr_ae (comparisonIntegrand_ae_witness P a πstar π hstar)

/-- On any sample where the witness agrees at every observed score, the
centered empirical comparison agrees exactly, including its population
center. -/
lemma centeredComparison_eq_witness_on_sample {n : ℕ} (P : RowLaw) (a : ℝ)
    (πstar π : ℝ → Bool) (hstar : πstar =ᵐ[P.PX] canonicalPolicy P)
    (d : Fin n → Observation)
    (hd : ∀ i, πstar (d i).X = canonicalPolicy P (d i).X) :
    |empiricalAverage (comparisonIntegrand P a π) d -
        ∫ o, comparisonIntegrand P a π o ∂P.obsLaw| =
      |empiricalAverage (witnessComparisonIntegrand P a πstar π) d -
        ∫ o, witnessComparisonIntegrand P a πstar π o ∂P.obsLaw| := by
  have hemp : empiricalAverage (comparisonIntegrand P a π) d =
      empiricalAverage (witnessComparisonIntegrand P a πstar π) d := by
    unfold empiricalAverage
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    simp only [comparisonIntegrand, witnessComparisonIntegrand, hd i]
  rw [hemp, integral_comparisonIntegrand_eq_witness P a πstar π hstar]

/-- The localized process centered at an explicit threshold witness. The
eligibility predicate remains the paper's original regularized loss. -/
noncomputable def witnessLocalizedProcess {n : ℕ} (P : RowLaw) (a z : ℝ)
    (πstar : ℝ → Bool) (d : Fin n → Observation) : ℝ :=
  ⨆ π : {π : ℝ → Bool // π ∈ thresholdClass ∧ regularizedLoss P a π ≤ z},
    |empiricalAverage (witnessComparisonIntegrand P a πstar π.1) d -
      ∫ o, witnessComparisonIntegrand P a πstar π.1 o ∂P.obsLaw|

/-- Pointwise sample transport of the full localized supremum. -/
lemma localizedProcess_eq_witness_on_sample {n : ℕ} (P : RowLaw) (a z : ℝ)
    (πstar : ℝ → Bool) (hstar : πstar =ᵐ[P.PX] canonicalPolicy P)
    (d : Fin n → Observation)
    (hd : ∀ i, πstar (d i).X = canonicalPolicy P (d i).X) :
    localizedProcess P a z d = witnessLocalizedProcess P a z πstar d := by
  unfold localizedProcess witnessLocalizedProcess
  apply iSup_congr
  intro π
  exact centeredComparison_eq_witness_on_sample P a πstar π.1 hstar d hd

def supportedObsSet : Set Observation :=
  {o | o.X ∈ Set.Icc (0 : ℝ) 1 ∧ o.Y ∈ Set.Icc (-1 : ℝ) 1}

abbrev SupportedObservation := supportedObsSet

noncomputable def supportedObsLaw (P : RowLaw) : Measure SupportedObservation :=
  Measure.comap (Subtype.val : SupportedObservation → Observation) P.obsLaw

lemma supportedObservation_measurableSet : MeasurableSet supportedObsSet := by
  have hcoords : Measurable (fun o : Observation => (o.X, o.A, o.Y)) :=
    comap_measurable _
  exact (hcoords.fst measurableSet_Icc).inter
    (hcoords.snd.snd measurableSet_Icc)

lemma obsLaw_ae_supported (P : RowLaw) (hP : WellFormed P) :
    ∀ᵐ o ∂P.obsLaw, o.X ∈ Set.Icc (0 : ℝ) 1 ∧
      o.Y ∈ Set.Icc (-1 : ℝ) 1 := by
  apply (ae_map_iff score_observation_map_measurable.aemeasurable
    supportedObservation_measurableSet).2
  exact (ae_iff.mpr hP.2.1).and (ae_iff.mpr hP.2.2.1)

/-- The observation law restricted to its declared support remains a
probability measure. -/
lemma supportedObsLaw_isProbabilityMeasure (P : RowLaw) (hP : WellFormed P)
    [IsProbabilityMeasure P.obsLaw] :
    IsProbabilityMeasure (supportedObsLaw P) := by
  apply (MeasurableEmbedding.subtype_coe
    supportedObservation_measurableSet).isProbabilityMeasure_comap
  filter_upwards [obsLaw_ae_supported P hP] with o ho
  exact ⟨⟨o, ho⟩, rfl⟩

/-- Integration on the supported subtype agrees with integration under the
original observation law because the latter is supported there. -/
lemma integral_supportedObsLaw (P : RowLaw) (hP : WellFormed P)
    (f : Observation → ℝ) :
    (∫ o : SupportedObservation, f o.1 ∂supportedObsLaw P) =
      ∫ o, f o ∂P.obsLaw := by
  have h := integral_subtype_comap (μ := P.obsLaw)
    supportedObservation_measurableSet f
  have hr : P.obsLaw.restrict supportedObsSet = P.obsLaw :=
    Measure.restrict_eq_self_of_ae_mem (obsLaw_ae_supported P hP)
  calc
    _ = ∫ o in supportedObsSet, f o ∂P.obsLaw := by
      simpa only [supportedObsLaw] using h
    _ = _ := by rw [hr]

/-- Mapping the supported observation law back to observations recovers the
original law. -/
lemma supportedObsLaw_map_val (P : RowLaw) (hP : WellFormed P) :
    Measure.map (Subtype.val : SupportedObservation → Observation)
      (supportedObsLaw P) = P.obsLaw := by
  rw [supportedObsLaw, map_comap_subtype_coe supportedObservation_measurableSet]
  exact Measure.restrict_eq_self_of_ae_mem (obsLaw_ae_supported P hP)

/-- Coordinatewise coercion maps the iid supported sample law to the paper's
iid observation sample law. -/
lemma supportedSampleLaw_map_val (P : RowLaw) (hP : WellFormed P) (n : ℕ)
    [IsProbabilityMeasure P.obsLaw] :
    Measure.map (fun d : Fin n → SupportedObservation =>
      fun i => (d i).1)
      (Measure.pi (fun _ : Fin n => supportedObsLaw P)) = sampleLaw P n := by
  letI (i : Fin n) : IsProbabilityMeasure
      (Measure.map (Subtype.val : SupportedObservation → Observation)
        (supportedObsLaw P)) := by
    rw [supportedObsLaw_map_val P hP]
    infer_instance
  rw [Measure.pi_map_pi (fun _ => measurable_subtype_coe.aemeasurable)]
  simp only [supportedObsLaw_map_val P hP]
  rfl

/-- Integrals of measurable sample functionals transport exactly through the
supported sample coercion. -/
lemma integral_supportedSampleLaw (P : RowLaw) (hP : WellFormed P) (n : ℕ)
    [IsProbabilityMeasure P.obsLaw] (g : (Fin n → Observation) → ℝ)
    (hg : AEStronglyMeasurable g (sampleLaw P n)) :
    (∫ d : Fin n → SupportedObservation, g (fun i => (d i).1)
      ∂Measure.pi (fun _ : Fin n => supportedObsLaw P)) =
      ∫ d, g d ∂sampleLaw P n := by
  rw [← supportedSampleLaw_map_val P hP n] at hg ⊢
  exact (integral_map
    (measurable_pi_lambda _ fun i => measurable_subtype_coe.comp
      (measurable_pi_apply i)).aemeasurable hg).symm

/-- Four countable chain branches plus the singleton constant-policy branch. -/
inductive FiveChainIndex (ι₀ ι₁ ι₂ ι₃ : Type)
  | branch0 : ι₀ → FiveChainIndex ι₀ ι₁ ι₂ ι₃
  | branch1 : ι₁ → FiveChainIndex ι₀ ι₁ ι₂ ι₃
  | branch2 : ι₂ → FiveChainIndex ι₀ ι₁ ι₂ ι₃
  | branch3 : ι₃ → FiveChainIndex ι₀ ι₁ ι₂ ι₃
  | branch4 : FiveChainIndex ι₀ ι₁ ι₂ ι₃

def fiveChainCode {ι₀ ι₁ ι₂ ι₃ : Type} :
    FiveChainIndex ι₀ ι₁ ι₂ ι₃ →
      Sum ι₀ (Sum ι₁ (Sum ι₂ (Option ι₃)))
  | .branch0 i => .inl i
  | .branch1 i => .inr (.inl i)
  | .branch2 i => .inr (.inr (.inl i))
  | .branch3 i => .inr (.inr (.inr (.some i)))
  | .branch4 => .inr (.inr (.inr .none))

lemma fiveChainCode_injective {ι₀ ι₁ ι₂ ι₃ : Type} :
    Function.Injective
      (fiveChainCode : FiveChainIndex ι₀ ι₁ ι₂ ι₃ →
        Sum ι₀ (Sum ι₁ (Sum ι₂ (Option ι₃)))) := by
  intro i k h
  cases i <;> cases k <;> simp [fiveChainCode] at h ⊢
  all_goals assumption

instance {ι₀ ι₁ ι₂ ι₃ : Type}
    [Countable ι₀] [Countable ι₁] [Countable ι₂] [Countable ι₃] :
    Countable (FiveChainIndex ι₀ ι₁ ι₂ ι₃) :=
  fiveChainCode_injective.countable

instance {ι₀ ι₁ ι₂ ι₃ : Type} :
    Nonempty (FiveChainIndex ι₀ ι₁ ι₂ ι₃) := ⟨.branch4⟩

def fiveChainBranch {ι₀ ι₁ ι₂ ι₃ : Type} :
    FiveChainIndex ι₀ ι₁ ι₂ ι₃ → Fin 5
  | .branch0 _ => 0
  | .branch1 _ => 1
  | .branch2 _ => 2
  | .branch3 _ => 3
  | .branch4 => 4

def fiveChainSet {Ω ι₀ ι₁ ι₂ ι₃ : Type}
    (B₀ : ι₀ → Set Ω) (B₁ : ι₁ → Set Ω)
    (B₂ : ι₂ → Set Ω) (B₃ : ι₃ → Set Ω) (B₄ : Set Ω) :
    FiveChainIndex ι₀ ι₁ ι₂ ι₃ → Set Ω
  | .branch0 i => B₀ i
  | .branch1 i => B₁ i
  | .branch2 i => B₂ i
  | .branch3 i => B₃ i
  | .branch4 => B₄

noncomputable def fiveChainFunction {Ω ι₀ ι₁ ι₂ ι₃ : Type}
    (B₀ : ι₀ → Set Ω) (B₁ : ι₁ → Set Ω)
    (B₂ : ι₂ → Set Ω) (B₃ : ι₃ → Set Ω) (B₄ : Set Ω)
    (weight : Fin 5 → Ω → ℝ) (i : FiveChainIndex ι₀ ι₁ ι₂ ι₃) : Ω → ℝ :=
  (fiveChainSet B₀ B₁ B₂ B₃ B₄ i).indicator
    (weight (fiveChainBranch i))

/-- A generic faithful five-chain constructor. All representation equations
are definitional; callers only supply measurability, within-branch nesting,
containing-set inclusions, and a common weight bound. -/
noncomputable def fiveChainBoundedClass {Ω ι₀ ι₁ ι₂ ι₃ : Type}
    [MeasurableSpace Ω]
    (B₀ : ι₀ → Set Ω) (B₁ : ι₁ → Set Ω)
    (B₂ : ι₂ → Set Ω) (B₃ : ι₃ → Set Ω) (B₄ : Set Ω)
    (weight : Fin 5 → Ω → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hB₀ : ∀ i, MeasurableSet (B₀ i))
    (hB₁ : ∀ i, MeasurableSet (B₁ i))
    (hB₂ : ∀ i, MeasurableSet (B₂ i))
    (hB₃ : ∀ i, MeasurableSet (B₃ i)) (hB₄ : MeasurableSet B₄)
    (hw : ∀ b, Measurable (weight b))
    (hwK : ∀ b x, |weight b x| ≤ K) :
    Causalean.Stat.EmpiricalProcess.Countable.BoundedClass Ω
      (FiveChainIndex ι₀ ι₁ ι₂ ι₃) where
  f := fiveChainFunction B₀ B₁ B₂ B₃ B₄ weight
  bound := K
  bound_nonneg := hK
  measurable i := by
    cases i with
    | branch0 i => exact (hw 0).indicator (hB₀ i)
    | branch1 i => exact (hw 1).indicator (hB₁ i)
    | branch2 i => exact (hw 2).indicator (hB₂ i)
    | branch3 i => exact (hw 3).indicator (hB₃ i)
    | branch4 => exact (hw 4).indicator hB₄
  bounded i x := by
    unfold fiveChainFunction
    by_cases hx : x ∈ fiveChainSet B₀ B₁ B₂ B₃ B₄ i
    · rw [Set.indicator_of_mem hx]
      exact hwK _ _
    · rw [Set.indicator_of_notMem hx, abs_zero]
      exact hK

/-- The corresponding `ChainCover`; equality of branch numbers rules out
all cross-branch cases and leaves exactly the supplied nested-chain facts. -/
noncomputable def fiveChainCover {Ω ι₀ ι₁ ι₂ ι₃ : Type}
    [MeasurableSpace Ω]
    (B₀ : ι₀ → Set Ω) (B₁ : ι₁ → Set Ω)
    (B₂ : ι₂ → Set Ω) (B₃ : ι₃ → Set Ω) (B₄ : Set Ω)
    (weight : Fin 5 → Ω → ℝ) (U : Fin 5 → Set Ω)
    (K : ℝ) (hK : 0 ≤ K)
    (hB₀ : ∀ i, MeasurableSet (B₀ i))
    (hB₁ : ∀ i, MeasurableSet (B₁ i))
    (hB₂ : ∀ i, MeasurableSet (B₂ i))
    (hB₃ : ∀ i, MeasurableSet (B₃ i)) (hB₄ : MeasurableSet B₄)
    (hw : ∀ b, Measurable (weight b))
    (hwK : ∀ b x, |weight b x| ≤ K)
    (hn₀ : ∀ i k, B₀ i ⊆ B₀ k ∨ B₀ k ⊆ B₀ i)
    (hn₁ : ∀ i k, B₁ i ⊆ B₁ k ∨ B₁ k ⊆ B₁ i)
    (hn₂ : ∀ i k, B₂ i ⊆ B₂ k ∨ B₂ k ⊆ B₂ i)
    (hn₃ : ∀ i k, B₃ i ⊆ B₃ k ∨ B₃ k ⊆ B₃ i)
    (hU₀ : ∀ i, B₀ i ⊆ U 0) (hU₁ : ∀ i, B₁ i ⊆ U 1)
    (hU₂ : ∀ i, B₂ i ⊆ U 2) (hU₃ : ∀ i, B₃ i ⊆ U 3)
    (hU₄ : B₄ ⊆ U 4) :
    let F := fiveChainBoundedClass B₀ B₁ B₂ B₃ B₄ weight K hK
      hB₀ hB₁ hB₂ hB₃ hB₄ hw hwK
    Causalean.Stat.EmpiricalProcess.Countable.ChainCover F 5 := by
  let F := fiveChainBoundedClass B₀ B₁ B₂ B₃ B₄ weight K hK
    hB₀ hB₁ hB₂ hB₃ hB₄ hw hwK
  refine {
    branch := fiveChainBranch
    sets := fiveChainSet B₀ B₁ B₂ B₃ B₄
    weight := weight
    containing := U
    nested := ?_
    subset_containing := ?_
    represents := ?_ }
  · intro i k hik
    cases i <;> cases k <;> simp [fiveChainBranch] at hik ⊢
    · exact hn₀ _ _
    · exact hn₁ _ _
    · exact hn₂ _ _
    · exact hn₃ _ _
  · intro i
    cases i with
    | branch0 i => exact hU₀ i
    | branch1 i => exact hU₁ i
    | branch2 i => exact hU₂ i
    | branch3 i => exact hU₃ i
    | branch4 => exact hU₄
  · intro i
    rfl

@[fun_prop] lemma supportedObservation_X_measurable :
    Measurable (fun o : SupportedObservation => o.1.X) :=
  score_observation_X_measurable.comp measurable_subtype_coe

def rightBelowSet (c t : ℝ) : Set SupportedObservation :=
  {o | o.1.X ∈ Set.Ico t c}

def rightAboveSet (c t : ℝ) : Set SupportedObservation :=
  {o | o.1.X ∈ Set.Ico c t}

def leftBelowSet (c t : ℝ) : Set SupportedObservation :=
  {o | o.1.X ∈ Set.Icc 0 t ∪ Set.Icc c 1}

def leftAboveSet (c t : ℝ) : Set SupportedObservation :=
  {o | o.1.X ∈ Set.Ico 0 c ∪ Set.Ioc t 1}

def zeroBranchSet (c : ℝ) : Set SupportedObservation :=
  {o | o.1.X ∈ Set.Icc c 1}

lemma rightBelowSet_measurable (c t : ℝ) : MeasurableSet (rightBelowSet c t) :=
  supportedObservation_X_measurable measurableSet_Ico

lemma rightAboveSet_measurable (c t : ℝ) : MeasurableSet (rightAboveSet c t) :=
  supportedObservation_X_measurable measurableSet_Ico

lemma leftBelowSet_measurable (c t : ℝ) : MeasurableSet (leftBelowSet c t) :=
  supportedObservation_X_measurable (measurableSet_Icc.union measurableSet_Icc)

lemma leftAboveSet_measurable (c t : ℝ) : MeasurableSet (leftAboveSet c t) :=
  supportedObservation_X_measurable (measurableSet_Ico.union measurableSet_Ioc)

lemma zeroBranchSet_measurable (c : ℝ) : MeasurableSet (zeroBranchSet c) :=
  supportedObservation_X_measurable measurableSet_Icc

noncomputable def rightOracleWeight (P : RowLaw) (a c : ℝ)
    (o : SupportedObservation) : ℝ :=
  (if c ≤ o.1.X then (1 : ℝ) else -1) * zScore a P.logger o.1

@[fun_prop] lemma rightOracleWeight_measurable (P : RowLaw) (a c : ℝ)
    (hP : WellFormed P) : Measurable (rightOracleWeight P a c) := by
  unfold rightOracleWeight
  exact (Measurable.ite
    (measurableSet_le measurable_const supportedObservation_X_measurable)
    measurable_const measurable_const).mul (zScore_supported_measurable P a hP)

lemma rightOracleWeight_abs_le (P : RowLaw) (a c : ℝ)
    (ha : 0 < a ∧ a ≤ 1 / 4)
    (hlogger : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      P.logger x ∈ Set.Ioo (0 : ℝ) 1)
    (o : SupportedObservation) : |rightOracleWeight P a c o| ≤ 2 / a := by
  unfold rightOracleWeight
  rw [abs_mul]
  have hz := zScore_abs_le a P.logger o.1 ha (hlogger o.1.X o.2.1) o.2.2
  split_ifs <;> simpa using hz

lemma rightBelowSet_nested (c s t : ℝ) (hst : s ≤ t) :
    rightBelowSet c t ⊆ rightBelowSet c s := by
  intro o ho
  exact rightOracle_right_below_nested c s t hst ho

lemma rightAboveSet_nested (c s t : ℝ) (hst : s ≤ t) :
    rightAboveSet c s ⊆ rightAboveSet c t := by
  intro o ho
  exact rightOracle_right_above_nested c s t hst ho

lemma leftBelowSet_nested (c s t : ℝ) (hst : s ≤ t) :
    leftBelowSet c s ⊆ leftBelowSet c t := by
  intro o ho
  exact rightOracle_left_below_nested c s t hst ho

lemma leftAboveSet_nested (c s t : ℝ) (hst : s ≤ t) :
    leftAboveSet c t ⊆ leftAboveSet c s := by
  intro o ho
  exact rightOracle_left_above_nested c s t hst ho

/-- Exact representation of the lower same-orientation branch. -/
lemma witnessComparison_right_below (P : RowLaw) (a c t : ℝ) (ht : t < c) :
    (fun o : SupportedObservation =>
      witnessComparisonIntegrand P a (rightThr c) (rightThr t) o.1) =
      (rightBelowSet c t).indicator (rightOracleWeight P a c) := by
  funext o
  unfold witnessComparisonIntegrand rightOracleWeight rightBelowSet
  rw [rightOracle_right_below_coefficient c t o.1.X ht]
  by_cases ho : o.1.X ∈ Set.Ico t c
  · have hnc : ¬ c ≤ o.1.X := not_le_of_gt (Set.mem_Ico.mp ho).2
    simp [Set.indicator, hnc, (Set.mem_Ico.mp ho).1,
      (Set.mem_Ico.mp ho).2]
  · have hcond : ¬ (t ≤ o.1.X ∧ o.1.X < c) := by
      simpa only [Set.mem_Ico] using ho
    simp [Set.indicator, hcond]

/-- Exact representation of the upper same-orientation branch. -/
lemma witnessComparison_right_above (P : RowLaw) (a c t : ℝ) (ht : c ≤ t) :
    (fun o : SupportedObservation =>
      witnessComparisonIntegrand P a (rightThr c) (rightThr t) o.1) =
      (rightAboveSet c t).indicator (rightOracleWeight P a c) := by
  funext o
  unfold witnessComparisonIntegrand rightOracleWeight rightAboveSet
  rw [rightOracle_right_above_coefficient c t o.1.X ht]
  by_cases ho : o.1.X ∈ Set.Ico c t
  · have hc : c ≤ o.1.X := (Set.mem_Ico.mp ho).1
    simp [Set.indicator, hc, (Set.mem_Ico.mp ho).2]
  · have hcond : ¬ (c ≤ o.1.X ∧ o.1.X < t) := by
      simpa only [Set.mem_Ico] using ho
    simp [Set.indicator, hcond]

/-- Exact representation of the lower opposite-orientation branch. -/
lemma witnessComparison_left_below (P : RowLaw) (a c t : ℝ) (ht : t < c) :
    (fun o : SupportedObservation =>
      witnessComparisonIntegrand P a (rightThr c) (leftThr t) o.1) =
      (leftBelowSet c t).indicator (rightOracleWeight P a c) := by
  funext o
  unfold witnessComparisonIntegrand rightOracleWeight leftBelowSet
  rw [rightOracle_left_below_coefficient c t o.1.X ht]
  have hx := o.2.1
  by_cases hxt : o.1.X ≤ t
  · have hcx : ¬ c ≤ o.1.X := by linarith
    have hmem : o.1.X ∈ Set.Icc 0 t ∪ Set.Icc c 1 :=
      Or.inl ⟨hx.1, hxt⟩
    simp [Set.indicator, hxt, hcx, hx.1, hx.2]
  · by_cases hcx : c ≤ o.1.X
    · have hmem : o.1.X ∈ Set.Icc 0 t ∪ Set.Icc c 1 :=
        Or.inr ⟨hcx, hx.2⟩
      simp [Set.indicator, hxt, hcx, hx.1, hx.2]
    · have hmem : o.1.X ∉ Set.Icc 0 t ∪ Set.Icc c 1 := by
        simp only [Set.mem_union, Set.mem_Icc, not_or]
        exact ⟨fun h => hxt h.2, fun h => hcx h.1⟩
      simp [Set.indicator, hxt, hcx, hx.1, hx.2]

/-- Exact representation of the upper opposite-orientation branch. -/
lemma witnessComparison_left_above (P : RowLaw) (a c t : ℝ) (ht : c ≤ t) :
    (fun o : SupportedObservation =>
      witnessComparisonIntegrand P a (rightThr c) (leftThr t) o.1) =
      (leftAboveSet c t).indicator (rightOracleWeight P a c) := by
  funext o
  unfold witnessComparisonIntegrand rightOracleWeight leftAboveSet
  rw [rightOracle_left_above_coefficient c t o.1.X ht]
  have hx := o.2.1
  by_cases hxc : o.1.X < c
  · have htx : ¬ t < o.1.X := by linarith
    have hmem : o.1.X ∈ Set.Ico 0 c ∪ Set.Ioc t 1 :=
      Or.inl ⟨hx.1, hxc⟩
    have hnc : ¬ c ≤ o.1.X := not_le_of_gt hxc
    simp [Set.indicator, hxc, htx, hnc, hx.1, hx.2]
  · by_cases htx : t < o.1.X
    · have hc : c ≤ o.1.X := by linarith
      have hmem : o.1.X ∈ Set.Ico 0 c ∪ Set.Ioc t 1 :=
        Or.inr ⟨htx, hx.2⟩
      simp [Set.indicator, hxc, htx, hc, hx.1, hx.2]
    · have hmem : o.1.X ∉ Set.Ico 0 c ∪ Set.Ioc t 1 := by
        simp only [Set.mem_union, Set.mem_Ico, Set.mem_Ioc, not_or]
        exact ⟨fun h => hxc h.2, fun h => htx h.1⟩
      have hc : c ≤ o.1.X := le_of_not_gt hxc
      simp [Set.indicator, hxc, htx, hc, hx.1, hx.2]

/-- Exact singleton representation of the constant-false competitor. -/
lemma witnessComparison_zero (P : RowLaw) (a c : ℝ) :
    (fun o : SupportedObservation =>
      witnessComparisonIntegrand P a (rightThr c) (fun _ => false) o.1) =
      (zeroBranchSet c).indicator (rightOracleWeight P a c) := by
  funext o
  unfold witnessComparisonIntegrand rightOracleWeight zeroBranchSet
  have hx := o.2.1
  by_cases hcx : c ≤ o.1.X
  · have hmem : o.1.X ∈ Set.Icc c 1 := ⟨hcx, hx.2⟩
    simp [Set.indicator, hcx, hx.2, rightThr]
  · have hmem : o.1.X ∉ Set.Icc c 1 := fun h => hcx h.1
    simp [Set.indicator, hcx, hx.2, rightThr]

/-- Any four countable cutoff families lying in the four right-oracle regions
produce the exact bounded class and a faithful five-branch cover. This is the
single generic helper used after each canonical-witness case has been reduced
to a right oracle (possibly by score reflection). -/
lemma exists_rightOracle_fiveChain
    {ι₀ ι₁ ι₂ ι₃ : Type}
    [Countable ι₀] [Countable ι₁] [Countable ι₂] [Countable ι₃]
    (P : RowLaw) (a c : ℝ) (includeZero : Bool) (hP : WellFormed P)
    (ha : 0 < a ∧ a ≤ 1 / 4)
    (hlogger : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      P.logger x ∈ Set.Ioo (0 : ℝ) 1)
    (t₀ : ι₀ → ℝ) (ht₀ : ∀ i, t₀ i < c)
    (t₁ : ι₁ → ℝ) (ht₁ : ∀ i, c ≤ t₁ i)
    (t₂ : ι₂ → ℝ) (ht₂ : ∀ i, t₂ i < c)
    (t₃ : ι₃ → ℝ) (ht₃ : ∀ i, c ≤ t₃ i) :
    ∃ F : Causalean.Stat.EmpiricalProcess.Countable.BoundedClass
        SupportedObservation (FiveChainIndex ι₀ ι₁ ι₂ ι₃),
      (∃ cover : Causalean.Stat.EmpiricalProcess.Countable.ChainCover F 5,
        (∀ i, F.f (.branch0 i) = fun o =>
          witnessComparisonIntegrand P a (rightThr c) (rightThr (t₀ i)) o.1) ∧
        (∀ i, F.f (.branch1 i) = fun o =>
          witnessComparisonIntegrand P a (rightThr c) (rightThr (t₁ i)) o.1) ∧
        (∀ i, F.f (.branch2 i) = fun o =>
          witnessComparisonIntegrand P a (rightThr c) (leftThr (t₂ i)) o.1) ∧
        (∀ i, F.f (.branch3 i) = fun o =>
          witnessComparisonIntegrand P a (rightThr c) (leftThr (t₃ i)) o.1) ∧
        (F.f .branch4 = fun o => witnessComparisonIntegrand P a (rightThr c)
          (if includeZero then (fun _ => false) else rightThr c) o.1) ∧
        (∀ b, cover.weight b = rightOracleWeight P a c) ∧
        (cover.containing 0 = ⋃ i, rightBelowSet c (t₀ i)) ∧
        (cover.containing 1 = ⋃ i, rightAboveSet c (t₁ i)) ∧
        (cover.containing 2 = ⋃ i, leftBelowSet c (t₂ i)) ∧
        (cover.containing 3 = ⋃ i, leftAboveSet c (t₃ i)) ∧
        (cover.containing 4 = if includeZero then zeroBranchSet c else ∅)) := by
  let B₀ : ι₀ → Set SupportedObservation := fun i => rightBelowSet c (t₀ i)
  let B₁ : ι₁ → Set SupportedObservation := fun i => rightAboveSet c (t₁ i)
  let B₂ : ι₂ → Set SupportedObservation := fun i => leftBelowSet c (t₂ i)
  let B₃ : ι₃ → Set SupportedObservation := fun i => leftAboveSet c (t₃ i)
  let B₄ : Set SupportedObservation :=
    if includeZero then zeroBranchSet c else ∅
  let weight : Fin 5 → SupportedObservation → ℝ := fun _ =>
    rightOracleWeight P a c
  let K : ℝ := 2 / a
  have hK : 0 ≤ K := div_nonneg (by norm_num) ha.1.le
  have hB₀ : ∀ i, MeasurableSet (B₀ i) := fun i => rightBelowSet_measurable _ _
  have hB₁ : ∀ i, MeasurableSet (B₁ i) := fun i => rightAboveSet_measurable _ _
  have hB₂ : ∀ i, MeasurableSet (B₂ i) := fun i => leftBelowSet_measurable _ _
  have hB₃ : ∀ i, MeasurableSet (B₃ i) := fun i => leftAboveSet_measurable _ _
  have hB₄ : MeasurableSet B₄ := by
    cases includeZero <;> simp [B₄, zeroBranchSet_measurable]
  have hw : ∀ b, Measurable (weight b) := fun _ =>
    rightOracleWeight_measurable P a c hP
  have hwK : ∀ b x, |weight b x| ≤ K := fun _ x =>
    rightOracleWeight_abs_le P a c ha hlogger x
  let F := fiveChainBoundedClass B₀ B₁ B₂ B₃ B₄ weight K hK
    hB₀ hB₁ hB₂ hB₃ hB₄ hw hwK
  let S := fiveChainSet B₀ B₁ B₂ B₃ B₄
  let U : Fin 5 → Set SupportedObservation := fun b =>
    ⋃ i : {i : FiveChainIndex ι₀ ι₁ ι₂ ι₃ // fiveChainBranch i = b}, S i.1
  have hn₀ : ∀ i k, B₀ i ⊆ B₀ k ∨ B₀ k ⊆ B₀ i := by
    intro i k
    rcases le_total (t₀ i) (t₀ k) with h | h
    · exact Or.inr (rightBelowSet_nested c _ _ h)
    · exact Or.inl (rightBelowSet_nested c _ _ h)
  have hn₁ : ∀ i k, B₁ i ⊆ B₁ k ∨ B₁ k ⊆ B₁ i := by
    intro i k
    rcases le_total (t₁ i) (t₁ k) with h | h
    · exact Or.inl (rightAboveSet_nested c _ _ h)
    · exact Or.inr (rightAboveSet_nested c _ _ h)
  have hn₂ : ∀ i k, B₂ i ⊆ B₂ k ∨ B₂ k ⊆ B₂ i := by
    intro i k
    rcases le_total (t₂ i) (t₂ k) with h | h
    · exact Or.inl (leftBelowSet_nested c _ _ h)
    · exact Or.inr (leftBelowSet_nested c _ _ h)
  have hn₃ : ∀ i k, B₃ i ⊆ B₃ k ∨ B₃ k ⊆ B₃ i := by
    intro i k
    rcases le_total (t₃ i) (t₃ k) with h | h
    · exact Or.inr (leftAboveSet_nested c _ _ h)
    · exact Or.inl (leftAboveSet_nested c _ _ h)
  have hU₀ : ∀ i, B₀ i ⊆ U 0 := fun i x hx =>
    Set.mem_iUnion_of_mem
      (⟨FiveChainIndex.branch0 i, rfl⟩ :
        {j : FiveChainIndex ι₀ ι₁ ι₂ ι₃ // fiveChainBranch j = 0}) hx
  have hU₁ : ∀ i, B₁ i ⊆ U 1 := fun i x hx =>
    Set.mem_iUnion_of_mem
      (⟨FiveChainIndex.branch1 i, rfl⟩ :
        {j : FiveChainIndex ι₀ ι₁ ι₂ ι₃ // fiveChainBranch j = 1}) hx
  have hU₂ : ∀ i, B₂ i ⊆ U 2 := fun i x hx =>
    Set.mem_iUnion_of_mem
      (⟨FiveChainIndex.branch2 i, rfl⟩ :
        {j : FiveChainIndex ι₀ ι₁ ι₂ ι₃ // fiveChainBranch j = 2}) hx
  have hU₃ : ∀ i, B₃ i ⊆ U 3 := fun i x hx =>
    Set.mem_iUnion_of_mem
      (⟨FiveChainIndex.branch3 i, rfl⟩ :
        {j : FiveChainIndex ι₀ ι₁ ι₂ ι₃ // fiveChainBranch j = 3}) hx
  have hU₄ : B₄ ⊆ U 4 := fun x hx =>
    Set.mem_iUnion_of_mem
      (⟨FiveChainIndex.branch4, rfl⟩ :
        {j : FiveChainIndex ι₀ ι₁ ι₂ ι₃ // fiveChainBranch j = 4}) hx
  refine ⟨F, ?_⟩
  let cover := fiveChainCover B₀ B₁ B₂ B₃ B₄ weight U K hK
    hB₀ hB₁ hB₂ hB₃ hB₄ hw hwK hn₀ hn₁ hn₂ hn₃
    hU₀ hU₁ hU₂ hU₃ hU₄
  refine ⟨cover, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (witnessComparison_right_below P a c (t₀ i) (ht₀ i)).symm
  · intro i
    exact (witnessComparison_right_above P a c (t₁ i) (ht₁ i)).symm
  · intro i
    exact (witnessComparison_left_below P a c (t₂ i) (ht₂ i)).symm
  · intro i
    exact (witnessComparison_left_above P a c (t₃ i) (ht₃ i)).symm
  · cases includeZero
    · funext o
      simp only [Bool.false_eq_true, ↓reduceIte]
      change (B₄.indicator (rightOracleWeight P a c)) o = _
      simp only [B₄, Bool.false_eq_true, ↓reduceIte]
      simp [witnessComparisonIntegrand]
    · change B₄.indicator (rightOracleWeight P a c) = _
      simp only [B₄, if_true]
      exact (witnessComparison_zero P a c).symm
  · intro b
    rfl
  · change U 0 = _
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
      rcases i with ⟨i, hiBranch⟩
      cases i with
      | branch0 j => exact Set.mem_iUnion_of_mem j hi
      | branch1 j => have h := congrArg Fin.val hiBranch; norm_num [fiveChainBranch] at h
      | branch2 j => have h := congrArg Fin.val hiBranch; norm_num [fiveChainBranch] at h
      | branch3 j => have h := congrArg Fin.val hiBranch; norm_num [fiveChainBranch] at h
      | branch4 => have h := congrArg Fin.val hiBranch; norm_num [fiveChainBranch] at h
    · rintro hx
      rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
      exact Set.mem_iUnion_of_mem
        (⟨FiveChainIndex.branch0 i, rfl⟩ :
          {j : FiveChainIndex ι₀ ι₁ ι₂ ι₃ // fiveChainBranch j = 0}) hi
  · change U 1 = _
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
      rcases i with ⟨i, hiBranch⟩
      cases i with
      | branch0 j => have h := congrArg Fin.val hiBranch; norm_num [fiveChainBranch] at h
      | branch1 j => exact Set.mem_iUnion_of_mem j hi
      | branch2 j => have h := congrArg Fin.val hiBranch; norm_num [fiveChainBranch] at h
      | branch3 j => have h := congrArg Fin.val hiBranch; norm_num [fiveChainBranch] at h
      | branch4 => have h := congrArg Fin.val hiBranch; norm_num [fiveChainBranch] at h
    · rintro hx
      rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
      exact Set.mem_iUnion_of_mem
        (⟨FiveChainIndex.branch1 i, rfl⟩ :
          {j : FiveChainIndex ι₀ ι₁ ι₂ ι₃ // fiveChainBranch j = 1}) hi
  · change U 2 = _
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
      rcases i with ⟨i, hiBranch⟩
      cases i with
      | branch0 j => have h := congrArg Fin.val hiBranch; norm_num [fiveChainBranch] at h
      | branch1 j => have h := congrArg Fin.val hiBranch; norm_num [fiveChainBranch] at h
      | branch2 j => exact Set.mem_iUnion_of_mem j hi
      | branch3 j => have h := congrArg Fin.val hiBranch; norm_num [fiveChainBranch] at h
      | branch4 => have h := congrArg Fin.val hiBranch; norm_num [fiveChainBranch] at h
    · rintro hx
      rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
      exact Set.mem_iUnion_of_mem
        (⟨FiveChainIndex.branch2 i, rfl⟩ :
          {j : FiveChainIndex ι₀ ι₁ ι₂ ι₃ // fiveChainBranch j = 2}) hi
  · change U 3 = _
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
      rcases i with ⟨i, hiBranch⟩
      cases i with
      | branch0 j => have h := congrArg Fin.val hiBranch; norm_num [fiveChainBranch] at h
      | branch1 j => have h := congrArg Fin.val hiBranch; norm_num [fiveChainBranch] at h
      | branch2 j => have h := congrArg Fin.val hiBranch; norm_num [fiveChainBranch] at h
      | branch3 j => exact Set.mem_iUnion_of_mem j hi
      | branch4 => have h := congrArg Fin.val hiBranch; norm_num [fiveChainBranch] at h
    · rintro hx
      rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
      exact Set.mem_iUnion_of_mem
        (⟨FiveChainIndex.branch3 i, rfl⟩ :
          {j : FiveChainIndex ι₀ ι₁ ι₂ ι₃ // fiveChainBranch j = 3}) hi
  · change U 4 = _
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
      rcases i with ⟨i, hiBranch⟩
      cases i with
      | branch0 j => have h := congrArg Fin.val hiBranch; norm_num [fiveChainBranch] at h
      | branch1 j => have h := congrArg Fin.val hiBranch; norm_num [fiveChainBranch] at h
      | branch2 j => have h := congrArg Fin.val hiBranch; norm_num [fiveChainBranch] at h
      | branch3 j => have h := congrArg Fin.val hiBranch; norm_num [fiveChainBranch] at h
      | branch4 => simpa only [S, fiveChainSet, B₄] using hi
    · intro hx
      exact Set.mem_iUnion_of_mem
        (⟨FiveChainIndex.branch4, rfl⟩ :
          {j : FiveChainIndex ι₀ ι₁ ι₂ ι₃ // fiveChainBranch j = 4}) hx

noncomputable def rightOracleOffset (P : RowLaw) (a c : ℝ)
    (o : SupportedObservation) : ℝ :=
  (if rightThr c o.1.X then (1 : ℝ) else 0) * zScore a P.logger o.1

noncomputable def rightOracleMark (P : RowLaw) (a : ℝ)
    (o : SupportedObservation) : ℝ :=
  -zScore a P.logger o.1

@[fun_prop] lemma rightOracleOffset_measurable (P : RowLaw) (a c : ℝ)
    (hP : WellFormed P) : Measurable (rightOracleOffset P a c) := by
  have hm0 : Measurable (fun o : SupportedObservation =>
      if c ≤ o.1.X then (1 : ℝ) else 0) := Measurable.ite
    (measurableSet_le measurable_const supportedObservation_X_measurable)
    measurable_const measurable_const
  have hm := hm0.mul (zScore_supported_measurable P a hP)
  have heq : rightOracleOffset P a c = fun o : SupportedObservation =>
      (if c ≤ o.1.X then (1 : ℝ) else 0) * zScore a P.logger o.1 := by
    funext o
    by_cases h : c ≤ o.1.X <;> simp [rightOracleOffset, rightThr, h]
  rw [heq]
  exact hm

@[fun_prop] lemma rightOracleMark_measurable (P : RowLaw) (a : ℝ)
    (hP : WellFormed P) : Measurable (rightOracleMark P a) :=
  (zScore_supported_measurable P a hP).neg

lemma rightOracleOffset_abs_le (P : RowLaw) (a c : ℝ)
    (ha : 0 < a ∧ a ≤ 1 / 4)
    (hlogger : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      P.logger x ∈ Set.Ioo (0 : ℝ) 1)
    (o : SupportedObservation) : |rightOracleOffset P a c o| ≤ 2 / a := by
  have hK : 0 ≤ 2 / a := div_nonneg (by norm_num) ha.1.le
  have hz := zScore_abs_le a P.logger o.1 ha (hlogger o.1.X o.2.1) o.2.2
  by_cases h : rightThr c o.1.X = true
  · simpa [rightOracleOffset, h] using hz
  · simpa [rightOracleOffset, h] using hK

lemma rightOracleMark_abs_le (P : RowLaw) (a : ℝ)
    (ha : 0 < a ∧ a ≤ 1 / 4)
    (hlogger : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      P.logger x ∈ Set.Ioo (0 : ℝ) 1)
    (o : SupportedObservation) : |rightOracleMark P a o| ≤ 2 / a := by
  simpa [rightOracleMark] using
    zScore_abs_le a P.logger o.1 ha (hlogger o.1.X o.2.1) o.2.2

lemma rightOracleOffset_integrable (P : RowLaw) (a c : ℝ)
    (hP : WellFormed P) (ha : 0 < a ∧ a ≤ 1 / 4)
    (hlogger : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      P.logger x ∈ Set.Ioo (0 : ℝ) 1)
    [IsProbabilityMeasure (supportedObsLaw P)] :
    Integrable (rightOracleOffset P a c) (supportedObsLaw P) :=
  Integrable.of_bound (rightOracleOffset_measurable P a c hP).aestronglyMeasurable
    (2 / a) (ae_of_all _ (rightOracleOffset_abs_le P a c ha hlogger))

lemma rightOracleMark_integrable (P : RowLaw) (a : ℝ)
    (hP : WellFormed P) (ha : 0 < a ∧ a ≤ 1 / 4)
    (hlogger : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      P.logger x ∈ Set.Ioo (0 : ℝ) 1)
    [IsProbabilityMeasure (supportedObsLaw P)] :
    Integrable (rightOracleMark P a) (supportedObsLaw P) :=
  Integrable.of_bound (rightOracleMark_measurable P a hP).aestronglyMeasurable
    (2 / a) (ae_of_all _ (rightOracleMark_abs_le P a ha hlogger))

/-- Both threshold orientations are exactly the affine threshold functions
used by the promoted countable-reduction theorem. -/
lemma thresholdFunction_eq_witnessComparison (P : RowLaw) (a c t : ℝ)
    (upper : Bool) :
    Causalean.Stat.EmpiricalProcess.Countable.thresholdFunction upper
      (fun o : SupportedObservation => o.1.X) (rightOracleOffset P a c)
      (rightOracleMark P a) t =
      fun o => witnessComparisonIntegrand P a (rightThr c)
        (if upper then leftThr t else rightThr t) o.1 := by
  funext o
  cases upper <;>
    simp [Causalean.Stat.EmpiricalProcess.Countable.thresholdFunction,
      rightOracleOffset, rightOracleMark, witnessComparisonIntegrand,
      leftThr, rightThr] <;>
    split_ifs <;> ring


end CausalSmith.Stat.ScorethresholdOverlapRegret
