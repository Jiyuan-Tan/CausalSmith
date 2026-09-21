/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.PairedHistogram.Basic
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.Partition.CellLaws
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.Depoissonization

/-!
# Independent Poisson law of a finite-sample histogram

This module defines the product law of independent singleton-cell Poisson
counts and identifies it with the histogram image of a finite Poisson sample.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram

/-- Given [a finite-alphabet probability law](hyp:P) and [a Poisson
intensity](hyp:lambda), the [independent Poisson count law](goal) is the product
over alphabet symbols of Poisson laws with rates equal to intensity times
singleton probability. -/
noncomputable def independentPoissonCountLaw
    {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] [DecidableEq X]
    (P : Measure X) [IsProbabilityMeasure P] (lambda : ℝ≥0) : Measure (X → ℕ) :=
  Measure.pi fun x : X ↦ poissonMeasure (lambda * (P {x}).toNNReal)

/-- Given [a finite-alphabet probability law](hyp:P) and [a Poisson
intensity](hyp:lambda), [the independent Poisson count law is a probability
law](goal). -/
instance independentPoissonCountLaw_isProbabilityMeasure
    {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] [DecidableEq X]
    (P : Measure X) [IsProbabilityMeasure P] (lambda : ℝ≥0) :
    IsProbabilityMeasure (independentPoissonCountLaw P lambda) := by
  unfold independentPoissonCountLaw
  infer_instance

private lemma map_finitePoissonSampleLaw_finiteSampleMap
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) [IsProbabilityMeasure P]
    (f : X → Y) (hf : Measurable f) (lambda : ℝ≥0) :
    Measure.map (finiteSampleMap f) (finitePoissonSampleLaw P lambda) =
      (letI : IsProbabilityMeasure (Measure.map f P) :=
        Measure.isProbabilityMeasure_map hf.aemeasurable
       finitePoissonSampleLaw (Measure.map f P) lambda) := by
  letI : IsProbabilityMeasure (Measure.map f P) :=
    Measure.isProbabilityMeasure_map hf.aemeasurable
  let F := finiteSampleMap f
  have hF : Measurable F := measurable_finiteSampleMap f hf
  let mu := Measure.map F (finitePoissonSampleLaw P lambda)
  let nu := finitePoissonSampleLaw (Measure.map f P) lambda
  have hrest (n : ℕ) :
      mu.restrict (FiniteSample.count ⁻¹' ({n} : Set ℕ)) =
        nu.restrict (FiniteSample.count ⁻¹' ({n} : Set ℕ)) := by
    rw [show mu = Measure.map F (finitePoissonSampleLaw P lambda) by rfl,
      Measure.restrict_map hF
        (measurable_finiteSample_count (MeasurableSet.singleton n))]
    have hpre : F ⁻¹' (FiniteSample.count ⁻¹' ({n} : Set ℕ)) =
        FiniteSample.count ⁻¹' ({n} : Set ℕ) := by ext s; rfl
    rw [hpre, finitePoissonSampleLaw_restrict_count_eq,
      show nu = finitePoissonSampleLaw (Measure.map f P) lambda by rfl,
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
  have hdecomp (eta : Measure (FiniteSample Y)) :
      eta = Measure.sum (fun n =>
        eta.restrict (FiniteSample.count ⁻¹' ({n} : Set ℕ))) := by
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
      eta = eta.restrict Set.univ := by rw [Measure.restrict_univ]
      _ = eta.restrict (⋃ n : ℕ,
          FiniteSample.count ⁻¹' ({n} : Set ℕ)) := by rw [hcover]
      _ = Measure.sum (fun n =>
          eta.restrict (FiniteSample.count ⁻¹' ({n} : Set ℕ))) := by
        exact Measure.restrict_iUnion hdis
          (fun n => measurable_finiteSample_count (MeasurableSet.singleton n))
  change mu = nu
  rw [hdecomp mu, hdecomp nu]
  congr 1
  funext n
  exact hrest n

/-- Given [a finite-alphabet probability law](hyp:P) and [a Poisson
intensity](hyp:lambda), the histogram of its finite Poisson sample [has the
product law of independent Poisson cell counts](goal). -/
theorem finitePoissonSampleLaw_map_histogram
    {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] [DecidableEq X]
    (P : Measure X) [IsProbabilityMeasure P] (lambda : ℝ≥0) :
    Measure.map (fun s : FiniteSample X ↦ finiteSampleHistogram s.points)
        (finitePoissonSampleLaw P lambda) =
      independentPoissonCountLaw P lambda := by
  let p : FiniteMeasurablePartition X X :=
    { cell := id
      measurable_cell := measurable_id }
  let R : Measure ℝ := Measure.dirac 0
  let markedCounts : FiniteSample (X × ℝ) → X → ℕ :=
    fun s x => (p.restrictCell x s).count
  let countFamily : (X → FiniteSample (X × ℝ)) → X → ℕ :=
    fun q x => (q x).count
  have hcountFamily : Measurable countFamily :=
    measurable_pi_lambda _ fun x =>
      measurable_finiteSample_count.comp (measurable_pi_apply x)
  have hmarked :
      Measure.map markedCounts (finiteMarkedPoissonSampleLaw P R lambda) =
        Measure.pi (fun x : X =>
          poissonMeasure (lambda * p.cellMass P x)) := by
    calc
      Measure.map markedCounts (finiteMarkedPoissonSampleLaw P R lambda) =
          Measure.map countFamily
            (Measure.map p.restrictPartition
              (finiteMarkedPoissonSampleLaw P R lambda)) := by
        rw [Measure.map_map hcountFamily p.measurable_restrictPartition]
        rfl
      _ = Measure.map countFamily
          (Measure.pi (fun x : X =>
            finiteMarkedPoissonSampleLaw (p.cellObservationLaw P x) R
              (lambda * p.cellMass P x))) := by
        rw [p.map_restrictPartition_finiteMarkedPoissonSampleLaw]
      _ = Measure.pi (fun x : X => Measure.map FiniteSample.count
          (finiteMarkedPoissonSampleLaw (p.cellObservationLaw P x) R
            (lambda * p.cellMass P x))) := by
        exact Measure.pi_map_pi
          (fun _ => measurable_finiteSample_count.aemeasurable)
      _ = Measure.pi (fun x : X =>
          poissonMeasure (lambda * p.cellMass P x)) := by
        congr with x
        rw [finiteMarkedPoissonSampleLaw_map_count]
  have herase := map_finitePoissonSampleLaw_finiteSampleMap
    (P.prod (Measure.dirac (0 : ℝ))) Prod.fst measurable_fst lambda
  have hprod : Measure.map Prod.fst (P.prod (Measure.dirac (0 : ℝ))) = P := by
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have herase' :
      Measure.map (finiteSampleMap Prod.fst)
          (finitePoissonSampleLaw (P.prod (Measure.dirac (0 : ℝ))) lambda) =
        finitePoissonSampleLaw P lambda := by
    simpa only [hprod] using herase
  have hcounts (s : FiniteSample (X × ℝ)) :
      markedCounts s =
        finiteSampleHistogram (finiteSampleMap Prod.fst s).points := by
    classical
    rcases s with ⟨n, points⟩
    funext x
    unfold markedCounts finiteSampleHistogram
      FiniteMeasurablePartition.restrictCell
    simp only [FiniteSample.count, finiteSampleMap, FiniteSample.points]
    unfold FiniteMeasurablePartition.cellIndices
    let q : Fin n → Prop := fun i =>
      p.cell (FiniteSample.points
        (⟨n, points⟩ : FiniteSample (X × ℝ)) i).1 = x
    let hq : DecidablePred q := fun _ => Classical.propDecidable _
    letI : DecidablePred q := hq
    change (Finset.univ.filter q).card =
      Fintype.card {i : Fin n // (points i).1 = x}
    calc
      (Finset.univ.filter q).card = Fintype.card {i : Fin n // q i} :=
        (Fintype.card_subtype q).symm
      _ = Fintype.card {i : Fin n // (points i).1 = x} :=
        Fintype.card_congr (Equiv.subtypeEquivRight fun i => by
          simp [q, p, FiniteSample.points])
  have hhist : Measurable
      (fun s : FiniteSample X => finiteSampleHistogram s.points) := by
    apply measurable_to_countable'
    intro c
    rw [MeasurableSpace.measurableSet_iInf]
    intro n
    change MeasurableSet ((Sigma.mk n) ⁻¹'
      {s : FiniteSample X | finiteSampleHistogram s.points = c})
    exact (Set.to_countable _).measurableSet
  unfold independentPoissonCountLaw
  change _ = Measure.pi (fun x : X =>
    poissonMeasure (lambda * p.cellMass P x))
  rw [← hmarked, ← herase',
    show finiteMarkedPoissonSampleLaw P (Measure.dirac (0 : ℝ)) lambda =
      finitePoissonSampleLaw (P.prod (Measure.dirac (0 : ℝ))) lambda by rfl,
    Measure.map_map hhist
      (measurable_finiteSampleMap Prod.fst measurable_fst)]
  exact congrArg
    (fun f : FiniteSample (X × ℝ) → (X → ℕ) =>
      Measure.map f
        (finitePoissonSampleLaw (P.prod (Measure.dirac (0 : ℝ))) lambda))
    (funext fun s => (hcounts s).symm)

end Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram
