import Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.Partition.Splitting
import Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.Depoissonization

/-! Exact histogram law for an unmarked finite Poisson sample. -/

namespace CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

-- @node: finitePoissonHistogram
/-- Counts the observations assigned to each cell by a finite classifier. -/
noncomputable def finitePoissonHistogram
    {X I : Type*} [MeasurableSpace X] [Fintype I]
    (cell : X → I) (s : FiniteSample X) : I → ℕ := by
  classical
  exact fun j ↦ (Finset.univ.filter fun k ↦ cell (s.points k) = j).card

-- @node: measurable_finitePoissonHistogram
/-- If [the stated cell condition holds](hyp:hcell), then [the stated measurable finite poisson histogram relation holds](goal). -/
@[fun_prop]
lemma measurable_finitePoissonHistogram
    {X I : Type*} [MeasurableSpace X] [Countable X]
    [MeasurableSingletonClass X] [MeasurableSingletonClass (FiniteSample X)]
    [MeasurableSpace I]
    [Fintype I] [MeasurableSingletonClass I]
    (cell : X → I) (hcell : Measurable cell) :
    Measurable (finitePoissonHistogram cell : FiniteSample X → I → ℕ) := by
  exact measurable_of_countable _

-- @node: map_finitePoissonSampleLaw_finiteSampleMap_dense
/-- Mapping every point of a finite Poisson sample maps its base law. This uses [the target function is continuous](hyp:hf). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma map_finitePoissonSampleLaw_finiteSampleMap_dense
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
  let mu := Measure.map F (finitePoissonSampleLaw P lam)
  let nu := finitePoissonSampleLaw (Measure.map f P) lam
  have hrest (m : ℕ) :
      mu.restrict (FiniteSample.count ⁻¹' ({m} : Set ℕ)) =
        nu.restrict (FiniteSample.count ⁻¹' ({m} : Set ℕ)) := by
    rw [show mu = Measure.map F (finitePoissonSampleLaw P lam) by rfl,
      Measure.restrict_map hF
        (measurable_finiteSample_count (MeasurableSet.singleton m))]
    have hpre : F ⁻¹' (FiniteSample.count ⁻¹' ({m} : Set ℕ)) =
        FiniteSample.count ⁻¹' ({m} : Set ℕ) := by ext s; rfl
    rw [hpre, finitePoissonSampleLaw_restrict_count_eq,
      show nu = finitePoissonSampleLaw (Measure.map f P) lam by rfl,
      finitePoissonSampleLaw_restrict_count_eq, Measure.map_smul,
      Measure.map_map hF (measurable_fixedSizeEmbed m)]
    have hfun : F ∘ fixedSizeEmbed m =
        fixedSizeEmbed m ∘ (fun x : Fin m → X ↦ fun i ↦ f (x i)) := by
      funext x
      exact finiteSampleMap_fixedSizeEmbed f m x
    rw [hfun]
    congr 1
    let G : (Fin m → X) → (Fin m → Y) := fun x i ↦ f (x i)
    have hG : Measurable G :=
      measurable_pi_lambda _ fun i ↦ hf.comp (measurable_pi_apply i)
    change Measure.map (fixedSizeEmbed m ∘ G)
      (Measure.pi fun _ : Fin m ↦ P) = _
    calc
      Measure.map (fixedSizeEmbed m ∘ G) (Measure.pi fun _ : Fin m ↦ P) =
          Measure.map (fixedSizeEmbed m)
            (Measure.map G (Measure.pi fun _ : Fin m ↦ P)) :=
        (Measure.map_map (measurable_fixedSizeEmbed m) hG).symm
      _ = Measure.map (fixedSizeEmbed m)
          (Measure.pi fun _ : Fin m ↦ Measure.map f P) := by
        rw [show G = (fun x i ↦ f (x i)) by rfl,
          Measure.pi_map_pi (fun _ ↦ hf.aemeasurable)]
  have hdecomp (eta : Measure (FiniteSample Y)) :
      eta = Measure.sum (fun m ↦
        eta.restrict (FiniteSample.count ⁻¹' ({m} : Set ℕ))) := by
    have hdis : Pairwise (Function.onFun Disjoint
        (fun m : ℕ ↦ (FiniteSample.count : FiniteSample Y → ℕ) ⁻¹'
          ({m} : Set ℕ))) := by
      intro i j hij
      apply Set.disjoint_left.2
      intro s hi hj
      apply hij
      simpa using hi.symm.trans hj
    have hcover : ⋃ m : ℕ,
        (FiniteSample.count : FiniteSample Y → ℕ) ⁻¹' ({m} : Set ℕ) =
          Set.univ := by ext s; simp
    calc
      eta = eta.restrict Set.univ := by rw [Measure.restrict_univ]
      _ = eta.restrict (⋃ m : ℕ,
          FiniteSample.count ⁻¹' ({m} : Set ℕ)) := by rw [hcover]
      _ = Measure.sum (fun m ↦
          eta.restrict (FiniteSample.count ⁻¹' ({m} : Set ℕ))) := by
        exact Measure.restrict_iUnion hdis
          (fun m ↦ measurable_finiteSample_count (MeasurableSet.singleton m))
  change mu = nu
  rw [hdecomp mu, hdecomp nu]
  congr 1
  funext m
  exact hrest m

-- @node: finitePoissonHistogram_law
/-- A measurable finite classifier turns a Poisson sample into independent
Poisson cell counts with the corresponding thinned means. This uses [the stated cell condition holds](hyp:hcell). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma finitePoissonHistogram_law
    {X I : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Countable X]
    [MeasurableSingletonClass X]
    [MeasurableSingletonClass (FiniteSample X)]
    [MeasurableSpace I] [Fintype I] [MeasurableSingletonClass I]
    (P : Measure X) [IsProbabilityMeasure P]
    (cell : X → I) (hcell : Measurable cell) (lam : NNReal) :
    Measure.map (finitePoissonHistogram cell)
        (finitePoissonSampleLaw P lam) =
      Measure.pi (fun j : I ↦ poissonMeasure
        (lam * (P (cell ⁻¹' {j})).toNNReal)) := by
  let p : FiniteMeasurablePartition X I := ⟨cell, hcell⟩
  let R : Measure ℝ := Measure.dirac 0
  let countFamily : (I → FiniteSample (X × ℝ)) → I → ℕ :=
    fun q j ↦ (q j).count
  have hcountFamily : Measurable countFamily :=
    measurable_pi_lambda _ fun j ↦
      measurable_finiteSample_count.comp (measurable_pi_apply j)
  have hmarked : Measure.map
      (fun s : FiniteSample (X × ℝ) ↦ fun j ↦ (p.restrictCell j s).count)
      (finiteMarkedPoissonSampleLaw P R lam) =
      Measure.pi (fun j : I ↦ poissonMeasure (lam * p.cellMass P j)) := by
    calc
      _ = Measure.map countFamily
          (Measure.map p.restrictPartition
            (finiteMarkedPoissonSampleLaw P R lam)) := by
        rw [Measure.map_map hcountFamily p.measurable_restrictPartition]
        rfl
      _ = Measure.map countFamily
          (Measure.pi (fun j : I ↦
            finiteMarkedPoissonSampleLaw (p.cellObservationLaw P j) R
              (lam * p.cellMass P j))) := by
        rw [p.map_restrictPartition_finiteMarkedPoissonSampleLaw]
      _ = Measure.pi (fun j : I ↦ Measure.map FiniteSample.count
          (finiteMarkedPoissonSampleLaw (p.cellObservationLaw P j) R
            (lam * p.cellMass P j))) := by
        exact Measure.pi_map_pi
          (fun _ ↦ measurable_finiteSample_count.aemeasurable)
      _ = Measure.pi (fun j : I ↦
          poissonMeasure (lam * p.cellMass P j)) := by
        congr with j
        rw [finiteMarkedPoissonSampleLaw_map_count]
  have herase := map_finitePoissonSampleLaw_finiteSampleMap_dense
    (P.prod (Measure.dirac (0 : ℝ))) Prod.fst measurable_fst lam
  have hprod : Measure.map Prod.fst (P.prod (Measure.dirac (0 : ℝ))) = P := by
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have herase' :
      Measure.map (finiteSampleMap Prod.fst)
          (finitePoissonSampleLaw (P.prod (Measure.dirac (0 : ℝ))) lam) =
        finitePoissonSampleLaw P lam := by
    simpa only [hprod] using herase
  have hcounts (s : FiniteSample (X × ℝ)) :
      (fun j ↦ (p.restrictCell j s).count) =
        finitePoissonHistogram cell (finiteSampleMap Prod.fst s) := by
    classical
    funext j
    rcases s with ⟨m, points⟩
    unfold FiniteMeasurablePartition.restrictCell finitePoissonHistogram
      FiniteMeasurablePartition.cellIndices
    simp only [FiniteSample.count, finiteSampleMap, FiniteSample.points]
    apply congrArg Finset.card
    ext k
    rw [show p.cell = cell by rfl]
    constructor <;> intro hk
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hk).2⟩
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hk).2⟩
  change _ = Measure.pi (fun j : I ↦
    poissonMeasure (lam * p.cellMass P j))
  rw [← hmarked, ← herase',
    show finiteMarkedPoissonSampleLaw P (Measure.dirac (0 : ℝ)) lam =
      finitePoissonSampleLaw (P.prod (Measure.dirac (0 : ℝ))) lam by rfl,
    Measure.map_map (measurable_finitePoissonHistogram cell hcell)
      (measurable_finiteSampleMap Prod.fst measurable_fst)]
  simpa [Function.comp_def] using congrArg
    (fun f : FiniteSample (X × ℝ) → I → ℕ ↦
      Measure.map f
        (finitePoissonSampleLaw (P.prod (Measure.dirac (0 : ℝ))) lam))
    (funext hcounts) |>.symm

end CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched
