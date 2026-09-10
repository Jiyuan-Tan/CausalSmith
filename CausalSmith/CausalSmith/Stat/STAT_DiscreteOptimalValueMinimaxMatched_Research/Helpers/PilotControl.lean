import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Helpers.Estimator
import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Helpers.FactorialProductRisk
import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Helpers.JacksonCertificate
import Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.Partition.Splitting
import Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.Depoissonization
import Causalean.Stat.Concentration.PoissonSelfNormalized.Scaling

set_option linter.style.longLine false

/-! Moment, bias, and variance control for the pilot-local factorial construction. -/

namespace CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

-- @node: canonicalJacksonTuning
/-- A concrete universal tuning with the promoted self-normalized Poisson
radius and a cutoff strictly above the smallest admissible alphabet. -/
noncomputable def canonicalJacksonTuning : JacksonTuning where
  pilotRadiusConstant :=
    Causalean.Stat.Concentration.PoissonSelfNormalized.universalH
  jacksonDegreeConstant := 1 / 100000
  boundedAlphabetCutoff := 3
  pilotRadiusConstant_pos :=
    Causalean.Stat.Concentration.PoissonSelfNormalized.universalH_pos
  jacksonDegreeConstant_pos := by norm_num
  jacksonDegreeConstant_lt_one := by norm_num

-- @node: canonicalJacksonTuning_cutoff
/-- [the canonical bounded-alphabet cutoff is strictly greater than two](goal). -/
lemma canonicalJacksonTuning_cutoff :
    2 < canonicalJacksonTuning.boundedAlphabetCutoff := by
  norm_num [canonicalJacksonTuning]

/-- Independent pilot and evaluation Poisson counts in all four coordinates. -/
noncomputable def pilotEvaluationLaw (m : ℝ) (q : Cell → ℝ) :
    Measure ((Cell → ℕ) × (Cell → ℕ)) :=
  (Measure.pi (fun j : Cell => ProbabilityTheory.poissonMeasure (m * q j).toNNReal)).prod
    (Measure.pi (fun j : Cell => ProbabilityTheory.poissonMeasure (m * q j).toNNReal))

/-- A complete table of pilot and evaluation counts, before the fixed-sample cap is imposed. -/
abbrev UncappedCountTable (d : ℕ) :=
  (Fin d → Cell → ℕ) × (Fin d → Cell → ℕ)

/-- The fair mark law used in the uncapped Poisson comparison experiment. -/
noncomputable def uncappedFairMarkLaw : Measure Bool :=
  (PMF.uniformOfFintype Bool).toMeasure

/-- the [fair uncapped mark law is a probability measure](goal). -/
instance : IsProbabilityMeasure uncappedFairMarkLaw := by
  unfold uncappedFairMarkLaw
  infer_instance

/-- Read the total count and the pilot/evaluation cell-count tables from a marked finite sample. -/
def uncappedMarkedCountMap {d : ℕ} (s : FiniteSample (Obs d × Bool)) :
    ℕ × UncappedCountTable d :=
  (s.count,
    ((fun x j => ∑ i : Fin s.count,
        if (s.points i).2 = false ∧ (s.points i).1.1 = x ∧
            (s.points i).1.2.1 = finTwoEquiv j.1 ∧
            (s.points i).1.2.2 = finTwoEquiv j.2 then 1 else 0),
     (fun x j => ∑ i : Fin s.count,
        if (s.points i).2 = true ∧ (s.points i).1.1 = x ∧
            (s.points i).1.2.1 = finTwoEquiv j.1 ∧
            (s.points i).1.2.2 = finTwoEquiv j.2 then 1 else 0)))

-- @node: measurable_uncappedMarkedCountMap
/-- The full marked count-table readout is measurable on the finite-sample space. [The displayed identity or bound is the asserted conclusion](goal). -/
@[fun_prop] lemma measurable_uncappedMarkedCountMap {d : ℕ} :
    Measurable (uncappedMarkedCountMap (d := d)) := by
  intro s hs
  rw [MeasurableSpace.measurableSet_iInf]
  intro k
  change MeasurableSet
    ((fun x : Fin k → Obs d × Bool => uncappedMarkedCountMap ⟨k, x⟩) ⁻¹' s)
  exact hs.preimage (measurable_of_countable _)

/-- The uncapped experiment induced by `M ~ Pois(n/4)`, i.i.d. observations, and fair marks. -/
noncomputable def uncappedMarkedCountLaw {d : ℕ} (n : ℕ) (P : DiscreteLaw d) :
    Measure (ℕ × UncappedCountTable d) :=
  Measure.map uncappedMarkedCountMap
    (finitePoissonSampleLaw ((obsLaw P).prod uncappedFairMarkLaw)
      (Real.toNNReal ((n : ℝ) / 4)))

-- @node: uncappedMarkedCountLaw_count
/-- The total coordinate of the uncapped marked experiment retains its
original Poisson count law. [The displayed identity or bound is the asserted conclusion](goal). -/
lemma uncappedMarkedCountLaw_count {d : ℕ} (n : ℕ) (P : DiscreteLaw d) :
    Measure.map Prod.fst (uncappedMarkedCountLaw n P) =
      ProbabilityTheory.poissonMeasure (Real.toNNReal ((n : ℝ) / 4)) := by
  unfold uncappedMarkedCountLaw
  rw [Measure.map_map measurable_fst measurable_uncappedMarkedCountMap]
  change Measure.map FiniteSample.count
      (finitePoissonSampleLaw ((obsLaw P).prod uncappedFairMarkLaw)
        (Real.toNNReal ((n : ℝ) / 4))) = _
  exact finitePoissonSampleLaw_map_count _ _

-- @node: uncappedAtomicPartition
/-- The singleton partition of the finite marked-observation alphabet. -/
private noncomputable def uncappedAtomicPartition (d : ℕ) :
    FiniteMeasurablePartition (Obs d × Bool) (Obs d × Bool) where
  cell := id
  measurable_cell := measurable_id

-- @node: uncappedMarkedHistogram
/-- The complete histogram of marked observations in a finite sample. -/
private def uncappedMarkedHistogram {d : ℕ}
    (s : FiniteSample (Obs d × Bool)) : Obs d × Bool → ℕ :=
  fun z => Fintype.card {i : Fin s.count // s.points i = z}

-- @node: uncappedHistogramToTable
/-- Reindex the complete marked histogram as separate pilot and evaluation
tables, with the paper's `Cell` coordinates. -/
private def uncappedHistogramToTable {d : ℕ}
    (H : Obs d × Bool → ℕ) : UncappedCountTable d :=
  ((fun x j => H ((x, finTwoEquiv j.1, finTwoEquiv j.2), false)),
   (fun x j => H ((x, finTwoEquiv j.1, finTwoEquiv j.2), true)))

-- @node: uncappedTableToHistogram
/-- Inverse reindexing from the two count tables to the complete marked
histogram. -/
private def uncappedTableToHistogram {d : ℕ}
    (T : UncappedCountTable d) : Obs d × Bool → ℕ := fun z =>
  let j : Cell := (finTwoEquiv.symm z.1.2.1, finTwoEquiv.symm z.1.2.2)
  if z.2 then T.2 z.1.1 j else T.1 z.1.1 j

-- @node: uncappedHistogramTableEquiv
/-- The two histogram presentations are measurably equivalent. -/
private def uncappedHistogramTableEquiv (d : ℕ) :
    (Obs d × Bool → ℕ) ≃ᵐ UncappedCountTable d where
  toFun := uncappedHistogramToTable
  invFun := uncappedTableToHistogram
  left_inv H := by
    funext z
    rcases z with ⟨⟨x, a, y⟩, b⟩
    cases b <;> simp [uncappedHistogramToTable, uncappedTableToHistogram]
  right_inv T := by
    apply Prod.ext <;> funext x j
    · simp [uncappedHistogramToTable, uncappedTableToHistogram]
    · simp [uncappedHistogramToTable, uncappedTableToHistogram]
  measurable_toFun := by fun_prop
  measurable_invFun := by fun_prop

-- @node: measurable_uncappedHistogramToTable
/-- Reindexing a histogram into its two count tables is measurable. -/
@[fun_prop] private lemma measurable_uncappedHistogramToTable {d : ℕ} :
    Measurable (uncappedHistogramToTable (d := d)) := by
  fun_prop

-- @node: uncappedMarkedCountMap_snd
/-- The table component of the marked-count readout is exactly a reindexing
of the complete singleton histogram. -/
private lemma uncappedMarkedCountMap_snd {d : ℕ}
    (s : FiniteSample (Obs d × Bool)) :
    (uncappedMarkedCountMap s).2 =
      uncappedHistogramToTable (uncappedMarkedHistogram s) := by
  classical
  apply Prod.ext <;> funext x j
  · simp only [uncappedMarkedCountMap, uncappedHistogramToTable,
      uncappedMarkedHistogram, Prod.fst, Prod.snd]
    rw [Fintype.card_subtype]
    rw [Finset.card_eq_sum_ones]
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _hi
    by_cases h : s.points i = ((x, finTwoEquiv j.1, finTwoEquiv j.2), false)
    · simp [h]
    · simp only [if_neg h]
      split
      · rename_i hc
        exfalso
        apply h
        apply Prod.ext
        · apply Prod.ext
          · exact hc.2.1
          · exact Prod.ext hc.2.2.1 hc.2.2.2
        · exact hc.1
      · rfl
  · simp only [uncappedMarkedCountMap, uncappedHistogramToTable,
      uncappedMarkedHistogram, Prod.fst, Prod.snd]
    rw [Fintype.card_subtype]
    rw [Finset.card_eq_sum_ones]
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _hi
    by_cases h : s.points i = ((x, finTwoEquiv j.1, finTwoEquiv j.2), true)
    · simp [h]
    · simp only [if_neg h]
      split
      · rename_i hc
        exfalso
        apply h
        apply Prod.ext
        · apply Prod.ext
          · exact hc.2.1
          · exact Prod.ext hc.2.2.1 hc.2.2.2
        · exact hc.1
      · rfl

-- @node: uncappedMarkedSingletonCounts
/-- Singleton-cell counts after adjoining an auxiliary real mark. -/
private noncomputable def uncappedMarkedSingletonCounts {d : ℕ}
    (s : FiniteSample ((Obs d × Bool) × ℝ)) : Obs d × Bool → ℕ :=
  fun z => ((uncappedAtomicPartition d).restrictCell z s).count

-- @node: measurable_uncappedMarkedHistogram
/-- The complete marked histogram is measurable. -/
@[fun_prop] private lemma measurable_uncappedMarkedHistogram {d : ℕ} :
    Measurable (uncappedMarkedHistogram (d := d)) := by
  intro s hs
  rw [MeasurableSpace.measurableSet_iInf]
  intro k
  change MeasurableSet
    ((fun x : Fin k → Obs d × Bool => uncappedMarkedHistogram ⟨k, x⟩) ⁻¹' s)
  exact hs.preimage (measurable_of_countable _)

-- @node: map_finitePoissonSampleLaw_finiteSampleMap_local
/-- Mapping every point of a finite Poisson sample maps its base law. -/
private lemma map_finitePoissonSampleLaw_finiteSampleMap_local
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) [IsProbabilityMeasure P]
    (f : X → Y) (hf : Measurable f) (lam : NNReal) :
    Measure.map (finiteSampleMap f) (finitePoissonSampleLaw P lam) =
      (letI : IsProbabilityMeasure (Measure.map f P) :=
        Measure.isProbabilityMeasure_map hf.aemeasurable
       finitePoissonSampleLaw (Measure.map f P) lam) := by
  letI : IsProbabilityMeasure (Measure.map f P) :=
    Measure.isProbabilityMeasure_map hf.aemeasurable
  let F := finiteSampleMap f
  have hF : Measurable F := measurable_finiteSampleMap f hf
  let μ := Measure.map F (finitePoissonSampleLaw P lam)
  let ν := finitePoissonSampleLaw (Measure.map f P) lam
  have hrest (n : ℕ) :
      μ.restrict (FiniteSample.count ⁻¹' ({n} : Set ℕ)) =
        ν.restrict (FiniteSample.count ⁻¹' ({n} : Set ℕ)) := by
    rw [show μ = Measure.map F (finitePoissonSampleLaw P lam) by rfl,
      Measure.restrict_map hF
        (measurable_finiteSample_count (MeasurableSet.singleton n))]
    have hpre : F ⁻¹' (FiniteSample.count ⁻¹' ({n} : Set ℕ)) =
        FiniteSample.count ⁻¹' ({n} : Set ℕ) := by ext s; rfl
    rw [hpre, finitePoissonSampleLaw_restrict_count_eq,
      show ν = finitePoissonSampleLaw (Measure.map f P) lam by rfl,
      finitePoissonSampleLaw_restrict_count_eq, Measure.map_smul,
      Measure.map_map hF (measurable_fixedSizeEmbed n)]
    have hfun : F ∘ fixedSizeEmbed n =
        fixedSizeEmbed n ∘ (fun x : Fin n → X => fun i => f (x i)) := by
      funext x
      exact finiteSampleMap_fixedSizeEmbed f n x
    rw [hfun]
    congr 1
    let G : (Fin n → X) → (Fin n → Y) := fun x i => f (x i)
    have hG : Measurable G :=
      measurable_pi_lambda _ fun i => hf.comp (measurable_pi_apply i)
    change Measure.map (fixedSizeEmbed n ∘ G)
      (Measure.pi fun _ : Fin n => P) = _
    calc
      Measure.map (fixedSizeEmbed n ∘ G) (Measure.pi fun _ : Fin n => P) =
          Measure.map (fixedSizeEmbed n)
            (Measure.map G (Measure.pi fun _ : Fin n => P)) :=
        (Measure.map_map (measurable_fixedSizeEmbed n) hG).symm
      _ = Measure.map (fixedSizeEmbed n)
          (Measure.pi fun _ : Fin n => Measure.map f P) := by
        rw [show G = (fun x i => f (x i)) by rfl,
          Measure.pi_map_pi (fun _ => hf.aemeasurable)]
  have hdecomp (η : Measure (FiniteSample Y)) :
      η = Measure.sum (fun n =>
        η.restrict (FiniteSample.count ⁻¹' ({n} : Set ℕ))) := by
    have hdis : Pairwise (Function.onFun Disjoint
        (fun n : ℕ => (FiniteSample.count : FiniteSample Y → ℕ) ⁻¹'
          ({n} : Set ℕ))) := by
      intro i j hij
      apply Set.disjoint_left.2
      intro s hi hj
      apply hij
      simpa using hi.symm.trans hj
    have hcover : ⋃ n : ℕ,
        (FiniteSample.count : FiniteSample Y → ℕ) ⁻¹' ({n} : Set ℕ) =
          Set.univ := by ext s; simp
    calc
      η = η.restrict Set.univ := by rw [Measure.restrict_univ]
      _ = η.restrict (⋃ n : ℕ,
          FiniteSample.count ⁻¹' ({n} : Set ℕ)) := by rw [hcover]
      _ = Measure.sum (fun n =>
          η.restrict (FiniteSample.count ⁻¹' ({n} : Set ℕ))) := by
        exact Measure.restrict_iUnion hdis
          (fun n => measurable_finiteSample_count (MeasurableSet.singleton n))
  change μ = ν
  rw [hdecomp μ, hdecomp ν]
  congr 1
  funext n
  exact hrest n

-- @node: uncappedMarkedSingletonCounts_eq_histogram_erase
/-- Erasing the auxiliary marks turns singleton restriction counts into the
ordinary histogram. -/
private lemma uncappedMarkedSingletonCounts_eq_histogram_erase {d : ℕ}
    (s : FiniteSample ((Obs d × Bool) × ℝ)) :
    uncappedMarkedSingletonCounts s =
      uncappedMarkedHistogram (finiteSampleMap Prod.fst s) := by
  classical
  rcases s with ⟨N, points⟩
  funext z
  unfold uncappedMarkedSingletonCounts uncappedMarkedHistogram
    FiniteMeasurablePartition.restrictCell
  simp only [FiniteSample.count, finiteSampleMap, FiniteSample.points]
  unfold FiniteMeasurablePartition.cellIndices
  let p : Fin N → Prop := fun i =>
    (uncappedAtomicPartition d).cell
      (FiniteSample.points (⟨N, points⟩ : FiniteSample ((Obs d × Bool) × ℝ)) i).1 = z
  let hp : DecidablePred p := fun _ => Classical.propDecidable _
  letI : DecidablePred p := hp
  change (Finset.univ.filter p).card =
    Fintype.card {i : Fin N // (points i).1 = z}
  calc
    (Finset.univ.filter p).card = Fintype.card {i : Fin N // p i} :=
      (Fintype.card_subtype p).symm
    _ = Fintype.card {i : Fin N // (points i).1 = z} :=
      Fintype.card_congr (Equiv.subtypeEquivRight fun i => by
        simp [p, uncappedAtomicPartition, FiniteSample.points])

-- @node: uncappedMarkedHistogram_law
/-- Poissonization makes the complete marked-observation histogram a product
of independent scalar Poisson laws. -/
private lemma uncappedMarkedHistogram_law {d : ℕ}
    (P : Measure (Obs d × Bool)) [IsProbabilityMeasure P] (lam : NNReal) :
    Measure.map (uncappedMarkedHistogram (d := d))
        (finitePoissonSampleLaw P lam) =
      Measure.pi (fun z : Obs d × Bool =>
        poissonMeasure (lam * (uncappedAtomicPartition d).cellMass P z)) := by
  let p := uncappedAtomicPartition d
  let R : Measure ℝ := Measure.dirac 0
  let countFamily : ((Obs d × Bool) → FiniteSample ((Obs d × Bool) × ℝ)) →
      (Obs d × Bool) → ℕ := fun q z => (q z).count
  have hcountFamily : Measurable countFamily :=
    measurable_pi_lambda _ fun z =>
      measurable_finiteSample_count.comp (measurable_pi_apply z)
  have hmarked : Measure.map (uncappedMarkedSingletonCounts (d := d))
        (finiteMarkedPoissonSampleLaw P R lam) =
      Measure.pi (fun z : Obs d × Bool =>
        poissonMeasure (lam * p.cellMass P z)) := by
    calc
      _ = Measure.map countFamily
            (Measure.map p.restrictPartition
              (finiteMarkedPoissonSampleLaw P R lam)) := by
        rw [Measure.map_map hcountFamily p.measurable_restrictPartition]
        rfl
    _ = Measure.map countFamily
        (Measure.pi (fun z : Obs d × Bool =>
          finiteMarkedPoissonSampleLaw (p.cellObservationLaw P z) R
            (lam * p.cellMass P z))) := by
      rw [p.map_restrictPartition_finiteMarkedPoissonSampleLaw]
    _ = Measure.pi (fun z : Obs d × Bool => Measure.map FiniteSample.count
        (finiteMarkedPoissonSampleLaw (p.cellObservationLaw P z) R
          (lam * p.cellMass P z))) := by
      exact Measure.pi_map_pi
        (fun _ => measurable_finiteSample_count.aemeasurable)
    _ = Measure.pi (fun z : Obs d × Bool =>
        poissonMeasure (lam * p.cellMass P z)) := by
      congr with z
      rw [finiteMarkedPoissonSampleLaw_map_count]
  have herase := map_finitePoissonSampleLaw_finiteSampleMap_local
    (P.prod (Measure.dirac (0 : ℝ))) Prod.fst measurable_fst lam
  have hprod : Measure.map Prod.fst (P.prod (Measure.dirac (0 : ℝ))) = P := by
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have herase' :
      Measure.map (finiteSampleMap Prod.fst)
          (finitePoissonSampleLaw (P.prod (Measure.dirac (0 : ℝ))) lam) =
        finitePoissonSampleLaw P lam := by
    simpa only [hprod] using herase
  rw [← hmarked, ← herase',
    show finiteMarkedPoissonSampleLaw P (Measure.dirac (0 : ℝ)) lam =
      finitePoissonSampleLaw (P.prod (Measure.dirac (0 : ℝ))) lam by rfl,
    Measure.map_map measurable_uncappedMarkedHistogram
      (measurable_finiteSampleMap Prod.fst measurable_fst)]
  exact congrArg
    (fun f : FiniteSample ((Obs d × Bool) × ℝ) → (Obs d × Bool → ℕ) =>
      Measure.map f
        (finitePoissonSampleLaw (P.prod (Measure.dirac (0 : ℝ))) lam))
    (funext fun s => (uncappedMarkedSingletonCounts_eq_histogram_erase s).symm)

/-- Independent pilot and evaluation count tables, each having mean scale `m`. -/
noncomputable def pilotEvaluationTableLaw {d : ℕ} (m : ℝ) (P : DiscreteLaw d) :
    Measure (UncappedCountTable d) :=
  (Measure.pi (fun x : Fin d => Measure.pi (fun j : Cell =>
      ProbabilityTheory.poissonMeasure
        (m * jointMass P x (finTwoEquiv j.1) (finTwoEquiv j.2)).toNNReal))).prod
    (Measure.pi (fun x : Fin d => Measure.pi (fun j : Cell =>
      ProbabilityTheory.poissonMeasure
        (m * jointMass P x (finTwoEquiv j.1) (finTwoEquiv j.2)).toNNReal)))

-- @node: uncappedMarkedCountLaw_table
/-- The table component of the uncapped marked experiment is the full product
of independent pilot and evaluation Poisson count tables at scale `n / 8`. [The displayed identity or bound is the asserted conclusion](goal). -/
lemma uncappedMarkedCountLaw_table {d : ℕ} (n : ℕ) (P : DiscreteLaw d) :
    Measure.map Prod.snd (uncappedMarkedCountLaw n P) =
      pilotEvaluationTableLaw (n / 8) P := by
  unfold uncappedMarkedCountLaw
  rw [Measure.map_map measurable_snd measurable_uncappedMarkedCountMap]
  rw [show Prod.snd ∘ uncappedMarkedCountMap =
      uncappedHistogramToTable ∘ uncappedMarkedHistogram by
    funext s
    exact uncappedMarkedCountMap_snd s]
  rw [← Measure.map_map measurable_uncappedHistogramToTable
    measurable_uncappedMarkedHistogram]
  rw [uncappedMarkedHistogram_law]
  change Measure.map (uncappedHistogramTableEquiv d) _ = _
  apply Measure.ext_of_singleton
  intro T
  rw [Measure.map_apply (uncappedHistogramTableEquiv d).measurable
    (MeasurableSet.singleton T)]
  rw [show (uncappedHistogramTableEquiv d) ⁻¹' ({T} : Set (UncappedCountTable d)) =
      {(uncappedHistogramTableEquiv d).symm T} by
    ext H
    constructor
    · intro h
      calc
        H = (uncappedHistogramTableEquiv d).symm
            ((uncappedHistogramTableEquiv d) H) :=
          ((uncappedHistogramTableEquiv d).symm_apply_apply H).symm
        _ = (uncappedHistogramTableEquiv d).symm T := by rw [h]
    · intro h
      simp only [Set.mem_singleton_iff] at h
      subst H
      simpa only [Set.mem_preimage, Set.mem_singleton_iff] using
        (uncappedHistogramTableEquiv d).apply_symm_apply T]
  have hcellMass (x : Fin d) (a y b : Bool) :
      (uncappedAtomicPartition d).cellMass
          ((obsLaw P).prod uncappedFairMarkLaw) ((x, a, y), b) =
        (jointMass P x a y / 2).toNNReal := by
    simp only [FiniteMeasurablePartition.cellMass, FiniteMeasurablePartition.cellSet,
      uncappedAtomicPartition, id_eq, Set.preimage_id']
    rw [show ({((x, a, y), b)} : Set (Obs d × Bool)) =
        ({(x, a, y)} : Set (Obs d)) ×ˢ ({b} : Set Bool) by ext; simp]
    change (((obsLaw P).prod uncappedFairMarkLaw)
      (({(x, a, y)} : Set (Obs d)) ×ˢ ({b} : Set Bool))).toNNReal = _
    rw [Measure.prod_prod]
    simp [obsLaw, uncappedFairMarkLaw, jointMass,
      PMF.toMeasure_apply_singleton]
    apply NNReal.eq
    simp [ENNReal.coe_toNNReal_eq_toReal]
    rw [max_eq_left (div_nonneg ENNReal.toReal_nonneg (by norm_num))]
    ring
  unfold pilotEvaluationTableLaw
  rw [show ({T} : Set (UncappedCountTable d)) = {T.1} ×ˢ {T.2} by
    ext z
    simp [Prod.ext_iff], Measure.prod_prod]
  simp [Measure.pi_pi,
    uncappedHistogramTableEquiv, uncappedTableToHistogram,
    hcellMass]
  rw [Fintype.prod_prod_type]
  have hmean (x : Fin d) (a y : Bool) :
      (n / 4 : ℝ).toNNReal * (jointMass P x a y / 2).toNNReal =
        (n / 8 * jointMass P x a y : ℝ).toNNReal := by
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hq0 : 0 ≤ jointMass P x a y := ENNReal.toReal_nonneg
    apply NNReal.eq
    simp only [NNReal.coe_mul]
    rw [Real.coe_toNNReal _ (div_nonneg hn0 (by norm_num)),
      Real.coe_toNNReal _ (div_nonneg hq0 (by norm_num)),
      Real.coe_toNNReal _ (mul_nonneg (div_nonneg hn0 (by norm_num)) hq0)]
    ring
  simp_rw [hmean]
  rw [Fintype.prod_prod_type]
  simp_rw [Fintype.prod_bool]
  simp only [if_true, Bool.false_eq_true, if_false]
  simp_rw [Finset.prod_mul_distrib]
  have hreindex (R : Fin d → Cell → ℕ) (x : Fin d) :
      (∏ ay : Bool × Bool,
          poissonMeasure (n / 8 * jointMass P x ay.1 ay.2).toNNReal
            {R x (finTwoEquiv.symm ay.1, finTwoEquiv.symm ay.2)}) =
        ∏ j : Cell,
          poissonMeasure
              (n / 8 * jointMass P x (finTwoEquiv j.1) (finTwoEquiv j.2)).toNNReal
            {R x j} := by
    symm
    apply Fintype.prod_equiv (finTwoEquiv.prodCongr finTwoEquiv)
    intro j
    simp
  simp_rw [hreindex]
  ac_rfl

-- @node: pilotEvaluationTableLaw_cell
/-- Each cell projection of the full independent count table is exactly the
four-coordinate pilot/evaluation product law used by the cell statistic. [The displayed identity or bound is the asserted conclusion](goal). -/
lemma pilotEvaluationTableLaw_cell {d : ℕ} (m : ℝ) (P : DiscreteLaw d) (x : Fin d) :
    Measure.map (fun z => (z.1 x, z.2 x)) (pilotEvaluationTableLaw m P) =
      pilotEvaluationLaw m (cellVector P x) := by
  unfold pilotEvaluationTableLaw pilotEvaluationLaw
  change Measure.map (Prod.map (Function.eval x) (Function.eval x)) _ = _
  rw [← Measure.map_prod_map]
  · simp [Measure.pi_map_eval, cellVector]
  · fun_prop
  · fun_prop

/-- Conditional expectation over evaluation counts after fixing the pilot table. -/
noncomputable def conditionalEvaluationExpectation (m : ℝ) (q : Cell → ℝ)
    (_pilot : Cell → ℕ) (f : (Cell → ℕ) → ℝ) : ℝ :=
  ∫ eval, f eval ∂Measure.pi (fun j : Cell =>
    ProbabilityTheory.poissonMeasure (m * q j).toNNReal)

-- @node: conditionalEvaluationExpectation_centeredFactorial
/-- Conditional on any pilot table, a coordinatewise centered factorial lift
has the centered-power expectation under the independent evaluation law. This uses [the Poisson intensity is positive](hyp:hm), and [the cell masses satisfy their stated restrictions](hyp:hq). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma conditionalEvaluationExpectation_centeredFactorial
    (m : ℝ) (hm : 0 < m) (q : Cell → ℝ) (hq : ∀ j, 0 ≤ q j)
    (pilot : Cell → ℕ) (j : Cell) (z : ℝ) (h : ℕ) :
    conditionalEvaluationExpectation m q pilot (fun eval =>
      centeredFactorial m h (eval j) z) = (q j - z) ^ h := by
  unfold conditionalEvaluationExpectation
  change (∫ eval : Cell → ℕ, centeredFactorial m h (eval j) z
    ∂Measure.pi (fun i : Cell => poissonMeasure (m * q i).toNNReal)) = _
  calc
    _ = ∫ N : ℕ, centeredFactorial m h N z
          ∂poissonMeasure (m * q j).toNNReal := by
      exact MeasureTheory.integral_comp_eval
        (μ := fun i : Cell => poissonMeasure (m * q i).toNNReal) (i := j)
        (Measurable.of_discrete.aestronglyMeasurable :
          AEStronglyMeasurable (fun N : ℕ => centeredFactorial m h N z)
            (poissonMeasure (m * q j).toNNReal))
    _ = _ := integral_centeredFactorial_poisson m (q j) z hm (hq j) h

-- @node: conditionalEvaluationExpectation_centeredFactorial_mul_expanded
/-- Conditional on any pilot table, the product of two centered factorial
lifts has the raw finite overlap expansion inherited from its scalar Poisson
coordinate.  This is the pre-collapse form of the paper's second moment
identity. [The displayed identity or bound is the asserted conclusion](goal). -/
lemma conditionalEvaluationExpectation_centeredFactorial_mul_expanded
    (m : ℝ) (q : Cell → ℝ) (pilot : Cell → ℕ) (j : Cell) (z : ℝ) (h t : ℕ) :
    conditionalEvaluationExpectation m q pilot (fun eval =>
      centeredFactorial m h (eval j) z * centeredFactorial m t (eval j) z) =
      ∑ b ∈ Finset.range (t + 1), ∑ a ∈ Finset.range (h + 1),
        ((Nat.choose h a : ℝ) * (-z) ^ (h - a) / m ^ a) *
          ((Nat.choose t b : ℝ) * (-z) ^ (t - b) / m ^ b) *
            (∑ l ∈ Finset.range (min a b + 1),
              (Nat.choose a l : ℝ) * Nat.choose b l * Nat.factorial l *
                ((m * q j).toNNReal : ℝ) ^ (a + b - l)) := by
  unfold conditionalEvaluationExpectation
  change (∫ eval : Cell → ℕ,
      centeredFactorial m h (eval j) z * centeredFactorial m t (eval j) z
    ∂Measure.pi (fun i : Cell => poissonMeasure (m * q i).toNNReal)) = _
  calc
    _ = ∫ N : ℕ, centeredFactorial m h N z * centeredFactorial m t N z
          ∂poissonMeasure (m * q j).toNNReal := by
      exact MeasureTheory.integral_comp_eval
        (μ := fun i : Cell => poissonMeasure (m * q i).toNNReal) (i := j)
        (Measurable.of_discrete.aestronglyMeasurable :
          AEStronglyMeasurable (fun N : ℕ =>
            centeredFactorial m h N z * centeredFactorial m t N z)
            (poissonMeasure (m * q j).toNNReal))
    _ = _ := integral_centeredFactorial_mul_poisson_expanded
      (m * q j).toNNReal m z h t

/-- Conditional on the pilot table, the product of two centered factorial
lifts has the collapsed overlap expansion from the paper. This uses [the Poisson intensity is positive](hyp:hm), and [the cell masses satisfy their stated restrictions](hyp:hq). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma conditionalEvaluationExpectation_centeredFactorial_mul
    (m : ℝ) (hm : 0 < m) (q : Cell → ℝ) (hq : ∀ j, 0 ≤ q j)
    (pilot : Cell → ℕ) (j : Cell) (z : ℝ) (h t : ℕ) :
    conditionalEvaluationExpectation m q pilot (fun eval =>
      centeredFactorial m h (eval j) z * centeredFactorial m t (eval j) z) =
      ∑ l ∈ Finset.range (min h t + 1),
        (Nat.choose h l : ℝ) * Nat.choose t l * Nat.factorial l *
          (q j / m) ^ l * (q j - z) ^ (h + t - 2 * l) := by
  unfold conditionalEvaluationExpectation
  change (∫ eval : Cell → ℕ,
      centeredFactorial m h (eval j) z * centeredFactorial m t (eval j) z
    ∂Measure.pi (fun i : Cell => poissonMeasure (m * q i).toNNReal)) = _
  calc
    _ = ∫ N : ℕ, centeredFactorial m h N z * centeredFactorial m t N z
          ∂poissonMeasure (m * q j).toNNReal := by
      exact MeasureTheory.integral_comp_eval
        (μ := fun i : Cell => poissonMeasure (m * q i).toNNReal) (i := j)
        (Measurable.of_discrete.aestronglyMeasurable :
          AEStronglyMeasurable (fun N : ℕ =>
            centeredFactorial m h N z * centeredFactorial m t N z)
            (poissonMeasure (m * q j).toNNReal))
    _ = _ :=
      CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.integral_centeredFactorial_mul_poisson
        m (q j) z hm (hq j) h t

/-- For [the specified tuning rule, overlap level, alphabet size, Poisson intensity, cell-mass vector, positive-intensity certificate](hyp:tuning,epsilon,d,m,q,hm), the [cell-statistic expectation is the mean of the Jackson cell statistic under the pilot-evaluation law](goal). -/
noncomputable def cellStatisticExpectation (tuning : JacksonTuning) (epsilon : ℝ) (d : ℕ) (m : ℝ)
    (q : Cell → ℝ) (hm : 0 < m) : ℝ :=
  ∫ z, jacksonCellStatistic tuning epsilon d m z.1 z.2 hm ∂pilotEvaluationLaw m q

/-- For [the specified tuning rule, overlap level, alphabet size, Poisson intensity, cell-mass vector, positive-intensity certificate](hyp:tuning,epsilon,d,m,q,hm), the [cell-statistic variance is the mean squared deviation of the Jackson cell statistic from its expectation under the pilot-evaluation law](goal). -/
noncomputable def cellStatisticVariance (tuning : JacksonTuning) (epsilon : ℝ) (d : ℕ) (m : ℝ)
    (q : Cell → ℝ) (hm : 0 < m) : ℝ :=
  let e := cellStatisticExpectation tuning epsilon d m q hm
  ∫ z, (jacksonCellStatistic tuning epsilon d m z.1 z.2 hm - e) ^ 2 ∂pilotEvaluationLaw m q

-- @node: jacksonCellStatistic_eq_clipAround
/-- The estimator's nested maximum/minimum is exactly clipping around the
pilot-center target at the declared random radius.  This bridge lets the
generic clipping-risk inequalities apply without unfolding the estimator. This uses [the Poisson intensity is positive](hyp:hm). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma jacksonCellStatistic_eq_clipAround (tuning : JacksonTuning) (epsilon : ℝ)
    (d : ℕ) (m : ℝ) (pilot eval : Cell → ℕ) (hm : 0 < m) :
    jacksonCellStatistic tuning epsilon d m pilot eval hm =
      let Q := pilotRectangle tuning m d pilot
      let center := rectangleCenter Q
      let radius := rectangleRadius Q
      let p := jacksonTensorPolynomial epsilon (jacksonDegree tuning d)
        (jacksonDegree_ge_two tuning d) Q (pilotRectangle_valid tuning m d pilot hm)
        (pilotRectangle_nonneg tuning m d pilot)
      let centerValue := globalCellValue epsilon center
      let raw := centerValue + factorialPolynomialLift m p eval center radius centerValue
      let scale := (1 + epsilon⁻¹) * ∑ j : Cell, radius j
      clipAround centerValue (d ^ (1 / 4 : ℝ) * scale) raw := by
  simp only [jacksonCellStatistic, clipAround]
  congr 1
  ring

/-- The paper's good-pilot event
`G_x = ⋂_j {|N'_{j,x}/m - q_{j,x}| ≤ h_{j,x}/4}`.  This is deliberately
stronger than mere membership of `q_x` in the (radius-`h`) pilot rectangle. -/
def pilotGoodEvent (tuning : JacksonTuning) (m : ℝ) (d : ℕ)
    (pilot : Cell → ℕ) (q : Cell → ℝ) : Prop :=
  ∀ j, |pilotCenter m pilot j - q j| ≤ pilotRadius tuning m d pilot j / 4

-- @node: pilotGoodEvent_mem_pilotRectangle
/-- On the coordinatewise good-pilot event, the true cell vector belongs to
the random pilot rectangle.  This includes zero coordinates because the lower
endpoint is truncated at zero. This uses [the cell masses satisfy their stated restrictions](hyp:hq), and [the pilot sample lies in the good event](hyp:hgood). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma pilotGoodEvent_mem_pilotRectangle (tuning : JacksonTuning) (m : ℝ) (d : ℕ)
    (pilot : Cell → ℕ) (q : Cell → ℝ) (hq : ∀ j, 0 ≤ q j)
    (hgood : pilotGoodEvent tuning m d pilot q) :
    ∀ j, q j ∈ Set.Icc ((pilotRectangle tuning m d pilot).1 j)
      ((pilotRectangle tuning m d pilot).2 j) := by
  intro j
  have habs := hgood j
  have hr : 0 ≤ pilotRadius tuning m d pilot j := by
    nlinarith [abs_nonneg (pilotCenter m pilot j - q j)]
  have hdifference := (abs_le.mp habs).1
  have hdifference' := (abs_le.mp habs).2
  simp only [pilotRectangle]
  constructor
  · apply max_le (hq j)
    linarith
  · linarith

-- @node: pilotRectangle_radius_bounds
/-- The radius of the zero-truncated pilot interval lies between one half and
one times the untruncated radius. This uses [the Poisson intensity is positive](hyp:hm), and [the alphabet size satisfies its stated restriction](hyp:hd). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma pilotRectangle_radius_bounds (tuning : JacksonTuning) (m : ℝ) (d : ℕ)
    (pilot : Cell → ℕ) (hm : 0 < m) (hd : 1 ≤ d) :
    ∀ j, pilotRadius tuning m d pilot j / 2 ≤
        rectangleRadius (pilotRectangle tuning m d pilot) j ∧
      rectangleRadius (pilotRectangle tuning m d pilot) j ≤
        pilotRadius tuning m d pilot j := by
  intro j
  have hc : 0 ≤ pilotCenter m pilot j := by
    unfold pilotCenter
    positivity
  have hr : 0 < pilotRadius tuning m d pilot j := by
    have hrect := pilotRectangle_radius_pos tuning m d pilot hm hd j
    simp only [rectangleRadius, pilotRectangle] at hrect
    by_cases h : pilotCenter m pilot j - pilotRadius tuning m d pilot j ≤ 0
    · rw [max_eq_left h] at hrect
      linarith
    · rw [max_eq_right (le_of_not_ge h)] at hrect
      linarith
  simp only [rectangleRadius, pilotRectangle]
  by_cases h : pilotCenter m pilot j - pilotRadius tuning m d pilot j ≤ 0
  · rw [max_eq_left h]
    constructor <;> linarith
  · rw [max_eq_right (le_of_not_ge h)]
    constructor <;> linarith

-- @node: canonicalNormalizedAggregateScore_eq
/-- For the canonical tuning, the promoted normalized aggregate score is
exactly the sum of the pilot deviations and the untruncated pilot radii. This uses [the Poisson intensity is positive](hyp:hm), and [the cell masses satisfy their stated restrictions](hyp:hq). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma canonicalNormalizedAggregateScore_eq (m : ℝ) (hm : 0 < m) (d : ℕ)
    (pilot : Cell → ℕ) (q : Cell → ℝ) (hq : ∀ j, 0 ≤ q j) :
    Causalean.Stat.Concentration.PoissonSelfNormalized.normalizedAggregateScore
        (fun j (w : Cell → ℕ) => w j)
        Causalean.Stat.Concentration.PoissonSelfNormalized.universalH
        (logAlphabet d) m.toNNReal (fun j => (q j).toNNReal) pilot =
      ∑ j : Cell,
        (|pilotCenter m pilot j - q j| +
          pilotRadius canonicalJacksonTuning m d pilot j) := by
  apply Finset.sum_congr rfl
  intro j _hj
  simp only [
    Causalean.Stat.Concentration.PoissonSelfNormalized.normalizedDeviation,
    Causalean.Stat.Concentration.PoissonSelfNormalized.normalizedRadius,
    pilotCenter, pilotRadius, canonicalJacksonTuning,
    Real.coe_toNNReal m (le_of_lt hm), Real.coe_toNNReal (q j) (hq j)]
  ring_nf

-- @node: canonicalPilotGeometry_le_normalizedAggregateScore
/-- The center displacement and the sum of the actual (zero-truncated)
rectangle radii are pointwise dominated by the promoted aggregate score. This uses [the Poisson intensity is positive](hyp:hm), and [the alphabet size satisfies its stated restriction](hyp:hd), and [the cell masses satisfy their stated restrictions](hyp:hq). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma canonicalPilotGeometry_le_normalizedAggregateScore
    (m : ℝ) (hm : 0 < m) (d : ℕ) (hd : 1 ≤ d)
    (pilot : Cell → ℕ) (q : Cell → ℝ) (hq : ∀ j, 0 ≤ q j) :
    l1CellDistance (rectangleCenter (pilotRectangle canonicalJacksonTuning m d pilot)) q +
        ∑ j : Cell, rectangleRadius (pilotRectangle canonicalJacksonTuning m d pilot) j ≤
      Causalean.Stat.Concentration.PoissonSelfNormalized.normalizedAggregateScore
        (fun j (w : Cell → ℕ) => w j)
        Causalean.Stat.Concentration.PoissonSelfNormalized.universalH
        (logAlphabet d) m.toNNReal (fun j => (q j).toNNReal) pilot := by
  rw [canonicalNormalizedAggregateScore_eq m hm d pilot q hq]
  unfold l1CellDistance
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _hj
  have htriangle :
      |rectangleCenter (pilotRectangle canonicalJacksonTuning m d pilot) j - q j| ≤
        |rectangleCenter (pilotRectangle canonicalJacksonTuning m d pilot) j -
            pilotCenter m pilot j| + |pilotCenter m pilot j - q j| := by
    simpa only [sub_add_sub_cancel] using
      abs_add_le (rectangleCenter (pilotRectangle canonicalJacksonTuning m d pilot) j -
        pilotCenter m pilot j) (pilotCenter m pilot j - q j)
  have hsplit :
      |rectangleCenter (pilotRectangle canonicalJacksonTuning m d pilot) j -
          pilotCenter m pilot j| +
        rectangleRadius (pilotRectangle canonicalJacksonTuning m d pilot) j =
          pilotRadius canonicalJacksonTuning m d pilot j := by
    simp only [rectangleCenter, rectangleRadius, pilotRectangle]
    have hp : 0 ≤ pilotCenter m pilot j := by
      unfold pilotCenter
      positivity
    have hr0 : 0 ≤ pilotRadius canonicalJacksonTuning m d pilot j := by
      have hrect := pilotRectangle_radius_pos
        canonicalJacksonTuning m d pilot hm hd j
      have hlo :=
        (pilotRectangle_radius_bounds canonicalJacksonTuning m d pilot hm hd j).1
      have hhi :=
        (pilotRectangle_radius_bounds canonicalJacksonTuning m d pilot hm hd j).2
      linarith
    by_cases h : pilotCenter m pilot j -
        pilotRadius canonicalJacksonTuning m d pilot j ≤ 0
    · rw [max_eq_left h, abs_of_nonneg]
      · ring
      · linarith
    · rw [max_eq_right (le_of_not_ge h)]
      simp
  linarith

-- @node: pilotGoodEvent_compl_eq_normalizedBadAny
/-- For the canonical radius constant, failure of the paper's pilot event is
exactly the promoted self-normalized Poisson bad event. This uses [the Poisson intensity is positive](hyp:hm), and [the cell masses satisfy their stated restrictions](hyp:hq). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma pilotGoodEvent_compl_eq_normalizedBadAny (m : ℝ) (hm : 0 < m) (d : ℕ)
    (q : Cell → ℝ) (hq : ∀ j, 0 ≤ q j) :
    {pilot : Cell → ℕ | ¬ pilotGoodEvent canonicalJacksonTuning m d pilot q} =
      Causalean.Stat.Concentration.PoissonSelfNormalized.normalizedBadAny
        (fun j (pilot : Cell → ℕ) => pilot j)
        Causalean.Stat.Concentration.PoissonSelfNormalized.universalH
        (logAlphabet d) m.toNNReal (fun j => (q j).toNNReal) := by
  classical
  ext pilot
  simp only [Set.mem_setOf_eq,
    Causalean.Stat.Concentration.PoissonSelfNormalized.normalizedBadAny,
    Set.mem_ofPred_eq, pilotGoodEvent, not_forall, not_le]
  apply exists_congr
  intro j
  simp only [pilotCenter, pilotRadius,
    Causalean.Stat.Concentration.PoissonSelfNormalized.normalizedDeviation,
    Causalean.Stat.Concentration.PoissonSelfNormalized.normalizedRadius,
    canonicalJacksonTuning, Real.coe_toNNReal m (le_of_lt hm),
    Real.coe_toNNReal (q j) (hq j)]
  have hsqrt :
      Real.sqrt ((pilot j : ℝ) / m * logAlphabet d / m) =
        Real.sqrt ((pilot j : ℝ) / m * (logAlphabet d / m)) := by
    congr 1
    ring
  rw [hsqrt]
  ring_nf

-- @node: canonicalPilotBadMoment
/-- The promoted four-coordinate Poisson theorem applies directly to a pilot
array with independent coordinate laws. This uses [the Poisson intensity is positive](hyp:hm), and [the argument satisfies the stated support or positivity restriction](hyp:ht), and [the Lipschitz scale is positive](hyp:hL). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma canonicalPilotBadMoment (q : Cell → NNReal) (m : NNReal) (hm : 0 < m)
    {t : ℕ} (ht : t = 1 ∨ t = 2 ∨ t = 4) {L : ℝ} (hL : 1 ≤ L) :
    ∫ pilot : Cell → ℕ,
        (Causalean.Stat.Concentration.PoissonSelfNormalized.normalizedBadAny
          (fun j (w : Cell → ℕ) => w j)
          Causalean.Stat.Concentration.PoissonSelfNormalized.universalH L m q).indicator
          (fun pilot =>
            Causalean.Stat.Concentration.PoissonSelfNormalized.normalizedAggregateScore
              (fun j (w : Cell → ℕ) => w j)
              Causalean.Stat.Concentration.PoissonSelfNormalized.universalH L m q pilot ^ t)
        pilot
      ∂Measure.pi (fun j : Cell => ProbabilityTheory.poissonMeasure (m * q j)) ≤
      Causalean.Stat.Concentration.PoissonSelfNormalized.productMomentConstant 4 t *
        Real.exp (-20 * L) *
          (Real.sqrt (((∑ j, (q j : ℝ)) * L) / (m : ℝ)) + L / (m : ℝ)) ^ t := by
  let μ : Measure (Cell → ℕ) :=
    Measure.pi (fun j : Cell => ProbabilityTheory.poissonMeasure (m * q j))
  letI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  apply Causalean.Stat.Concentration.PoissonSelfNormalized.independent_poisson_normalized_badAny_moment
    (μ := μ) (W := fun j (w : Cell → ℕ) => w j) (q := q) (m := m) hm
  · intro j
    fun_prop
  · intro j
    exact (MeasureTheory.measurePreserving_eval
      (fun i : Cell => ProbabilityTheory.poissonMeasure (m * q i)) j).hasLaw
  · exact ProbabilityTheory.iIndepFun_pi (X := fun _ (w : ℕ) => w)
      (fun _ => aemeasurable_id)
  · simp
  · exact ht
  · exact hL

-- @node: canonicalPilot_noiseToRadius_le
/-- On a good pilot, every coordinate's Poisson noise-to-radius ratio is at
most the reciprocal logarithmic level required by the factorial L² bound. This uses [the Poisson intensity is positive](hyp:hm), and [the alphabet size satisfies its stated restriction](hyp:hd), and [the pilot sample lies in the good event](hyp:hgood). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma canonicalPilot_noiseToRadius_le (m : ℝ) (hm : 0 < m) (d : ℕ) (hd : 1 ≤ d)
    (pilot : Cell → ℕ) (q : Cell → ℝ)
    (hgood : pilotGoodEvent canonicalJacksonTuning m d pilot q) (j : Cell) :
    q j / (m * rectangleRadius
      (pilotRectangle canonicalJacksonTuning m d pilot) j ^ 2) ≤
      1 / logAlphabet d := by
  have hL : 0 < logAlphabet d := by
    rw [logAlphabet]
    apply Real.log_pos
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_left hd1 (Real.exp_nonneg 1)]
  let c := pilotCenter m pilot j
  let tau := logAlphabet d / m
  let s := Real.sqrt (c * tau)
  let h := pilotRadius canonicalJacksonTuning m d pilot j
  let r := rectangleRadius (pilotRectangle canonicalJacksonTuning m d pilot) j
  have hc : 0 ≤ c := by dsimp [c, pilotCenter]; positivity
  have htau : 0 < tau := div_pos hL hm
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = c * tau := by
    dsimp [s]; rw [Real.sq_sqrt] <;> positivity
  have hh : h = 1024 * (s + tau) := by
    simp [h, pilotRadius, canonicalJacksonTuning,
      Causalean.Stat.Concentration.PoissonSelfNormalized.universalH, s, tau, c]
    congr 2
    ring
  have hqle : q j ≤ c + h / 4 := by
    have := (abs_le.mp (hgood j)).1
    linarith
  have hrlo : h / 2 ≤ r :=
    (pilotRectangle_radius_bounds canonicalJacksonTuning m d pilot hm hd j).1
  have hrpos : 0 < r :=
    pilotRectangle_radius_pos canonicalJacksonTuning m d pilot hm hd j
  have hqbound : q j ≤ 384 * (c + tau) := by
    rw [hh] at hqle
    nlinarith [sq_nonneg (s - (c + tau) / 2)]
  have hrsq : 384 * (c + tau) * logAlphabet d ≤ m * r ^ 2 := by
    rw [hh] at hrlo
    have hm_tau : m * tau = logAlphabet d := by dsimp [tau]; field_simp
    have hst : 0 ≤ s + tau := add_nonneg hs (le_of_lt htau)
    have hr512 : 512 * (s + tau) ≤ r := by linarith
    have hr2 : (512 * (s + tau)) ^ 2 ≤ r ^ 2 :=
      (sq_le_sq₀ (mul_nonneg (by norm_num) hst) (le_of_lt hrpos)).2 hr512
    have hbase : tau * (c + tau) ≤ (s + tau) ^ 2 := by
      nlinarith [mul_nonneg hs (le_of_lt htau), hs2]
    rw [← hm_tau]
    nlinarith [mul_le_mul_of_nonneg_left hr2 (le_of_lt hm),
      mul_le_mul_of_nonneg_left hbase (le_of_lt hm)]
  apply (div_le_div_iff₀ (mul_pos hm (sq_pos_of_pos hrpos)) hL).2
  nlinarith

/-- Pilot-failure contribution, restricted to the complement of the paper's
coordinatewise good-pilot event. -/
noncomputable def pilotFailureContribution (tuning : JacksonTuning) (epsilon : ℝ) (d : ℕ) (m : ℝ)
    (q : Cell → ℝ) (hm : 0 < m) : ℝ := by
  classical
  exact ∫ z, if pilotGoodEvent tuning m d z.1 q then 0 else
        |jacksonCellStatistic tuning epsilon d m z.1 z.2 hm - globalCellValue epsilon q|
      ∂pilotEvaluationLaw m q

/-- Squared pilot-failure contribution, at the local second-moment scale. -/
noncomputable def pilotFailureSecondMomentContribution (tuning : JacksonTuning) (epsilon : ℝ)
    (d : ℕ) (m : ℝ) (q : Cell → ℝ) (hm : 0 < m) : ℝ := by
  classical
  exact ∫ z, if pilotGoodEvent tuning m d z.1 q then 0 else
        (jacksonCellStatistic tuning epsilon d m z.1 z.2 hm - globalCellValue epsilon q) ^ 2
      ∂pilotEvaluationLaw m q

end CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched
