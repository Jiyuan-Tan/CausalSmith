module
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.PairedHistogram.Risk
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.Partition.CellLaws
public import Causalean.Stat.Sample.PiTransport

/-! Local finite-Poisson histogram transport for the inverse-count proof. -/

@[expose] public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram

/-- Apply a measurable map to every point of a dependent finite sample.  [the stated conditions](hyp:f,s) [the stated conclusion](goal). -/
def mapFiniteSample {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (f : X → Y) (s : FiniteSample X) : FiniteSample Y :=
  ⟨s.count, fun i => f (s.points i)⟩

/-- Applying [a map](hyp:f) that [is measurable](hyp:hf) to every point of a finite sample [is measurable](goal). -/
@[fun_prop] lemma measurable_mapFiniteSample
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (f : X → Y) (hf : Measurable f) : Measurable (mapFiniteSample f) := by
  intro s hs
  rw [MeasurableSpace.measurableSet_iInf] at hs
  change @MeasurableSet (FiniteSample X)
    (⨅ n, MeasurableSpace.map (Sigma.mk n)
      (inferInstance : MeasurableSpace (Fin n → X))) (mapFiniteSample f ⁻¹' s)
  rw [MeasurableSpace.measurableSet_iInf]
  intro n
  change MeasurableSet ((fun z : Fin n → X => fun i => f (z i)) ⁻¹'
    (fixedSizeEmbed (X := Y) n ⁻¹' s))
  have hc : Measurable (fun z : Fin n → X => fun i => f (z i)) :=
    measurable_pi_lambda _ fun _ => hf.comp (measurable_pi_apply _)
  have he : @Measurable (Fin n → Y) (FiniteSample Y)
      (inferInstance : MeasurableSpace (Fin n → Y))
      (MeasurableSpace.map (Sigma.mk n)
        (inferInstance : MeasurableSpace (Fin n → Y)))
      (fixedSizeEmbed (X := Y) n) := by
    apply Measurable.of_le_map
    exact le_rfl
  exact (hs n).preimage (he.comp hc)

/-- Finite Poisson samples commute with a measurable pushforward of their
observation law.  [the stated conditions](hyp:hf) [the stated conclusion](goal). -/
lemma mapFiniteSample_finitePoissonSampleLaw
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) [IsProbabilityMeasure P] (lam : NNReal)
    (f : X → Y) (hf : Measurable f) :
    Measure.map (mapFiniteSample f) (finitePoissonSampleLaw P lam) =
      @finitePoissonSampleLaw Y _ (Measure.map f P)
        (Measure.isProbabilityMeasure_map hf.aemeasurable) lam := by
  letI : IsProbabilityMeasure (Measure.map f P) :=
    Measure.isProbabilityMeasure_map hf.aemeasurable
  unfold finitePoissonSampleLaw poissonIIDStreamLaw iidStreamLaw
  rw [Measure.map_map (measurable_mapFiniteSample f hf)
    measurable_streamToFiniteSample]
  rw [show mapFiniteSample f ∘ streamToFiniteSample =
      streamToFiniteSample ∘
        (Prod.map id (fun z : Nat → X => fun i => f (z i))) by rfl]
  rw [← Measure.map_map measurable_streamToFiniteSample (by fun_prop)]
  rw [← Measure.map_prod_map _ _ measurable_id (by fun_prop), Measure.map_id]
  rw [Measure.infinitePi_map_pi (μ := fun _ : Nat => P)
    (f := fun _ => f) (fun _ => hf)]

/-- On a finite alphabet, the histogram of a finite Poisson sample consists
of independent Poisson cell counts.  [the stated conclusion](goal). -/
lemma finitePoissonSampleLaw_map_histogram
    {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] [DecidableEq X] [StandardBorelSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (lam : NNReal) :
    Measure.map (fun s : FiniteSample X => finiteSampleHistogram s.points)
        (finitePoissonSampleLaw P lam) =
      Measure.pi fun x : X =>
        poissonMeasure (lam * (P {x}).toNNReal) := by
  classical
  let R : Measure Real := Measure.dirac 0
  let p : FiniteMeasurablePartition X X :=
    ⟨id, measurable_id⟩
  let erase : FiniteSample (X × Real) → FiniteSample X :=
    mapFiniteSample Prod.fst
  let counts : FiniteSample (X × Real) → (X → Nat) :=
    fun s x => (p.restrictCell x s).count
  have hbase : Measure.map Prod.fst (P.prod R) = P := by
    dsimp [R]
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have herase : Measure.map erase (finiteMarkedPoissonSampleLaw P R lam) =
      finitePoissonSampleLaw P lam := by
    dsimp [erase]
    change Measure.map (mapFiniteSample Prod.fst)
      (finitePoissonSampleLaw (P.prod R) lam) = _
    rw [mapFiniteSample_finitePoissonSampleLaw (P.prod R) lam Prod.fst
      measurable_fst]
    simpa only [hbase]
  have hcounts : counts =
      (fun q : X → FiniteSample (X × Real) => fun x => (q x).count) ∘
        p.restrictPartition := by rfl
  have hsplit := p.map_restrictPartition_finiteMarkedPoissonSampleLaw P R lam
  have hmapCounts : Measure.map counts (finiteMarkedPoissonSampleLaw P R lam) =
      Measure.pi fun x : X => poissonMeasure (lam * p.cellMass P x) := by
    rw [hcounts, ← Measure.map_map (by fun_prop) p.measurable_restrictPartition,
      hsplit, Measure.pi_map_pi
        (fun _ => measurable_finiteSample_count.aemeasurable)]
    congr 1
    funext x
    exact finiteMarkedPoissonSampleLaw_map_count
      (p.cellObservationLaw P x) R (lam * p.cellMass P x)
  have hhist :
      (fun s : FiniteSample X => finiteSampleHistogram s.points) ∘ erase = counts := by
    funext s x
    change finiteSampleHistogram (fun i => (s.points i).1) x =
      (p.restrictCell x s).count
    simp only [finiteSampleHistogram,
      FiniteMeasurablePartition.restrictCell,
      FiniteMeasurablePartition.cellIndices, FiniteSample.count,
      FiniteSample.points, p, id_eq]
    convert Fintype.card_subtype (fun i : Fin s.1 => (s.2 i).1 = x) using 1
    all_goals first
      | rfl
      | exact congrArg Finset.card
          (Finset.filter_congr_decidable Finset.univ
            (fun i : Fin s.1 => (s.2 i).1 = x) _)
  calc
    Measure.map (fun s : FiniteSample X => finiteSampleHistogram s.points)
        (finitePoissonSampleLaw P lam) =
        Measure.map (fun s : FiniteSample X => finiteSampleHistogram s.points)
          (Measure.map erase (finiteMarkedPoissonSampleLaw P R lam)) := by rw [herase]
    _ = Measure.map counts (finiteMarkedPoissonSampleLaw P R lam) := by
      rw [Measure.map_map measurable_finiteSampleHistogram
        (measurable_mapFiniteSample Prod.fst measurable_fst), hhist]
    _ = Measure.pi fun x : X => poissonMeasure (lam * p.cellMass P x) := hmapCounts
    _ = Measure.pi fun x : X => poissonMeasure (lam * (P {x}).toNNReal) := by
      congr 1

/-- Selecting distinct coordinates from a finite product measure retains the
corresponding independent product law.  [the stated conditions](hyp:he) [the stated conclusion](goal). -/
lemma map_pi_finProjection
    {I J : Type*} [Fintype I] [Fintype J]
    {X : I → Type*} [∀ i, MeasurableSpace (X i)]
    (mu : (i : I) → Measure (X i)) [∀ i, IsProbabilityMeasure (mu i)]
    (e : J → I) (he : Function.Injective e) :
    Measure.map (fun z => fun j => z (e j)) (Measure.pi mu) =
      Measure.pi fun j => mu (e j) := by
  classical
  have hi : iIndepFun (fun i z => z i) (Measure.pi mu) :=
    iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have hj := hi.precomp he
  have hmap := hj.map_fun_eq_pi_map
    (fun _ => (measurable_pi_apply _).aemeasurable)
  have heval (j : J) : Measure.map (fun z => z (e j)) (Measure.pi mu) =
      mu (e j) := by simpa using Measure.pi_map_eval mu (e j)
  simp_rw [heval] at hmap
  exact hmap
/-- The formal statement establishes [the stated conclusion](goal). -/

lemma map_prod_pi_pointwisePair
    {I A B : Type*} [Fintype I] [MeasurableSpace A] [MeasurableSpace B]
    (mu : I → Measure A) (nu : I → Measure B)
    [∀ i, IsProbabilityMeasure (mu i)] [∀ i, IsProbabilityMeasure (nu i)] :
    Measure.map (fun z : (I → A) × (I → B) => fun i => (z.1 i, z.2 i))
        ((Measure.pi mu).prod (Measure.pi nu)) =
      Measure.pi fun i => (mu i).prod (nu i) := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow A B I
  exact (measurePreserving_arrowProdEquivProdArrow A B I mu nu).symm e |>.map_eq

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
