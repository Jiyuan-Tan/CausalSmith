module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.HybridThreePoolReadback

/-! Histogram law of the generic three independent Poisson prefixes. -/

public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

open MeasureTheory ProbabilityTheory Causalean.Stat
open Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram
open Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix.FiniteFamily
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

/-- Mapping the three generic prefixes to the paper's count tensor gives three
independent Poisson histograms in every `(x,a)` cell.  [the stated conclusion](goal). -/
lemma hybridPrefixCounts_map_independentPoissonPrefixLaw {d : Nat}
    (P : DiscreteLaw d) (u tp t : NNReal) :
    Measure.map hybridPrefixCounts
        (independentPoissonPrefixLaw
          (threePoolObservationLaw (obsLaw P) (auxMarginal P).toMeasure)
          (threePoolIntensity u tp t)) =
      Measure.pi fun x : Fin d => Measure.pi fun a : Bool =>
        (poissonMeasure
          (u * ((obsLaw P) ({(x, a, true)} : Set (Obs d))).toNNReal)).prod
          ((poissonMeasure
            (tp * ((auxMarginal P).toMeasure
              ({(x, a)} : Set (AuxObs d))).toNNReal)).prod
           (poissonMeasure
            (t * ((auxMarginal P).toMeasure
              ({(x, a)} : Set (AuxObs d))).toNNReal))) := by
  let h0 : FiniteSample (Obs d) → (Obs d → Nat) :=
    fun s ↦ finiteSampleHistogram s.points
  let hp : FiniteSample (AuxObs d) → (AuxObs d → Nat) :=
    fun s ↦ finiteSampleHistogram s.points
  let hf : FiniteSample (AuxObs d) → (AuxObs d → Nat) :=
    fun s ↦ finiteSampleHistogram s.points
  let extract : (Obs d → Nat) → (AuxObs d → Nat) :=
    fun h xa ↦ h (xa.1, xa.2, true)
  let pairPF : (AuxObs d → Nat) × (AuxObs d → Nat) →
      (AuxObs d → Nat × Nat) := fun z xa ↦ (z.1 xa, z.2 xa)
  let pairAll : (AuxObs d → Nat) × (AuxObs d → Nat × Nat) →
      (AuxObs d → Nat × (Nat × Nat)) := fun z xa ↦ (z.1 xa, z.2 xa)
  let curryCounts : (AuxObs d → Nat × (Nat × Nat)) → HybridPoissonCounts d :=
    fun z x a ↦ z (x, a)
  let mu0 := Measure.pi fun z : Obs d =>
    poissonMeasure (u * ((obsLaw P) {z}).toNNReal)
  let mup := Measure.pi fun z : AuxObs d =>
    poissonMeasure (tp * ((auxMarginal P).toMeasure {z}).toNNReal)
  let muf := Measure.pi fun z : AuxObs d =>
    poissonMeasure (t * ((auxMarginal P).toMeasure {z}).toNNReal)
  let mu0' := Measure.pi fun xa : AuxObs d =>
    poissonMeasure (u * ((obsLaw P) {(xa.1, xa.2, true)}).toNNReal)
  let mupf := Measure.pi fun xa : AuxObs d =>
    (poissonMeasure (tp * ((auxMarginal P).toMeasure {xa}).toNNReal)).prod
      (poissonMeasure (t * ((auxMarginal P).toMeasure {xa}).toNNReal))
  let muAll := Measure.pi fun xa : AuxObs d =>
    (poissonMeasure (u * ((obsLaw P) {(xa.1, xa.2, true)}).toNNReal)).prod
      ((poissonMeasure (tp * ((auxMarginal P).toMeasure {xa}).toNNReal)).prod
       (poissonMeasure (t * ((auxMarginal P).toMeasure {xa}).toNNReal)))
  have hhist0 := finitePoissonSampleLaw_map_histogram (obsLaw P) u
  have hhistp := finitePoissonSampleLaw_map_histogram (auxMarginal P).toMeasure tp
  have hhistf := finitePoissonSampleLaw_map_histogram (auxMarginal P).toMeasure t
  have hextract : Measure.map extract mu0 = mu0' := by
    exact map_pi_finProjection _ (fun xa : AuxObs d ↦ (xa.1, xa.2, true))
      (by
        intro x y h
        apply Prod.ext
        · simpa only using congrArg Prod.fst h
        · simpa only using congrArg (fun z : Obs d ↦ z.2.1) h)
  have hpairPF : Measure.map pairPF (mup.prod muf) = mupf :=
    map_prod_pi_pointwisePair _ _
  have hpairAll : Measure.map pairAll (mu0'.prod mupf) = muAll :=
    map_prod_pi_pointwisePair _ _
  have hcurry : Measure.map curryCounts muAll =
      Measure.pi fun x : Fin d => Measure.pi fun a : Bool =>
        (poissonMeasure
          (u * ((obsLaw P) {(x, a, true)}).toNNReal)).prod
          ((poissonMeasure
            (tp * ((auxMarginal P).toMeasure {(x, a)}).toNNReal)).prod
           (poissonMeasure
            (t * ((auxMarginal P).toMeasure {(x, a)}).toNNReal))) := by
    change Measure.map (MeasurableEquiv.curry (Fin d) Bool
        (Nat × (Nat × Nat))) muAll = _
    simpa only [Measure.infinitePi_eq_pi, muAll] using
      Measure.infinitePi_map_curry (fun x : Fin d => fun a : Bool =>
        (poissonMeasure
          (u * ((obsLaw P) {(x, a, true)}).toNNReal)).prod
          ((poissonMeasure
            (tp * ((auxMarginal P).toMeasure {(x, a)}).toNNReal)).prod
           (poissonMeasure
            (t * ((auxMarginal P).toMeasure {(x, a)}).toNNReal))))
  let source0 := finitePoissonSampleLaw (obsLaw P) u
  let sourcep := finitePoissonSampleLaw (auxMarginal P).toMeasure tp
  let sourcef := finitePoissonSampleLaw (auxMarginal P).toMeasure t
  have hsource : Measure.map unpackThreePool
      (independentPoissonPrefixLaw
        (threePoolObservationLaw (obsLaw P) (auxMarginal P).toMeasure)
        (threePoolIntensity u tp t)) = source0.prod (sourcep.prod sourcef) := by
    unfold independentPoissonPrefixLaw
    simpa [threePoolObservationLaw, threePoolIntensity, source0, sourcep, sourcef]
      using map_unpackThreePool_pi (mu := fun i ↦
        finitePoissonSampleLaw
          (threePoolObservationLaw (obsLaw P) (auxMarginal P).toMeasure i)
          (threePoolIntensity u tp t i))
  let histThree := fun z : FiniteSample (Obs d) ×
      (FiniteSample (AuxObs d) × FiniteSample (AuxObs d)) ↦
    (h0 z.1, hp z.2.1, hf z.2.2)
  have hhist : Measure.map histThree (source0.prod (sourcep.prod sourcef)) =
      mu0.prod (mup.prod muf) := by
    change Measure.map (Prod.map h0 (Prod.map hp hf))
      (source0.prod (sourcep.prod sourcef)) = _
    rw [← Measure.map_prod_map _ _ (by fun_prop : Measurable h0) (by fun_prop),
      ← Measure.map_prod_map _ _ (by fun_prop : Measurable hp)
        (by fun_prop : Measurable hf), hhist0, hhistp, hhistf]
  let finish := curryCounts ∘ pairAll ∘ Prod.map extract pairPF
  have hfinish : Measure.map finish (mu0.prod (mup.prod muf)) =
      Measure.pi fun x : Fin d => Measure.pi fun a : Bool =>
        (poissonMeasure
          (u * ((obsLaw P) {(x, a, true)}).toNNReal)).prod
          ((poissonMeasure
            (tp * ((auxMarginal P).toMeasure {(x, a)}).toNNReal)).prod
           (poissonMeasure
            (t * ((auxMarginal P).toMeasure {(x, a)}).toNNReal))) := by
    rw [show Measure.map finish (mu0.prod (mup.prod muf)) =
        Measure.map curryCounts
          (Measure.map pairAll
            (Measure.map (Prod.map extract pairPF) (mu0.prod (mup.prod muf)))) by
      rw [Measure.map_map (by fun_prop) (by fun_prop),
        Measure.map_map (by fun_prop) (by fun_prop)]
      rfl]
    rw [← Measure.map_prod_map _ _ (by fun_prop : Measurable extract)
      (by fun_prop : Measurable pairPF), hextract, hpairPF, hpairAll, hcurry]
  have hfun : hybridPrefixCounts = finish ∘ histThree ∘ unpackThreePool := by
    funext z
    rfl
  rw [hfun]
  change Measure.map ((finish ∘ histThree) ∘ unpackThreePool)
      (independentPoissonPrefixLaw
        (threePoolObservationLaw (obsLaw P) (auxMarginal P).toMeasure)
        (threePoolIntensity u tp t)) = _
  calc
    _ = Measure.map finish
        (Measure.map histThree
          (Measure.map unpackThreePool
            (independentPoissonPrefixLaw
              (threePoolObservationLaw (obsLaw P) (auxMarginal P).toMeasure)
              (threePoolIntensity u tp t)))) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop),
        Measure.map_map (by fun_prop) (by fun_prop)]
    _ = Measure.map finish (Measure.map histThree
        (source0.prod (sourcep.prod sourcef))) := by rw [hsource]
    _ = Measure.map finish (mu0.prod (mup.prod muf) ) := by rw [hhist]
    _ = _ := hfinish

/-- The preceding histogram law in the paper's `markedMass`/`armMass`
parameterization.  [the stated conditions](hyp:hu,htp,ht) [the stated conclusion](goal). -/
lemma hybridPrefixCounts_map_eq_hybridPoissonCountLaw {d : Nat}
    (P : DiscreteLaw d) (u tp t : Real)
    (hu : 0 ≤ u) (htp : 0 ≤ tp) (ht : 0 ≤ t) :
    Measure.map hybridPrefixCounts
        (independentPoissonPrefixLaw
          (threePoolObservationLaw (obsLaw P) (auxMarginal P).toMeasure)
          (threePoolIntensity (Real.toNNReal u) (Real.toNNReal tp)
            (Real.toNNReal t))) =
      hybridPoissonCountLaw P u tp t := by
  rw [hybridPrefixCounts_map_independentPoissonPrefixLaw]
  unfold hybridPoissonCountLaw
  congr 1
  funext x
  congr 1
  funext a
  have haux : (auxMarginal P (x, a)).toReal = armMass P x a := by
    unfold auxMarginal armMass jointMass
    rw [PMF.map_apply, tsum_fintype]
    cases a <;> simp only [Fintype.sum_prod_type] <;> simp
    all_goals
      rw [ENNReal.toReal_add (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)]
  have hauxNN : ((auxMarginal P).toMeasure
      ({(x, a)} : Set (AuxObs d))).toNNReal = (armMass P x a).toNNReal := by
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    apply NNReal.eq
    have harm : 0 ≤ armMass P x a := by
      unfold armMass jointMass
      positivity
    rw [ENNReal.coe_toNNReal_eq_toReal,
      Real.coe_toNNReal _ harm]
    exact haux
  congr 1
  · congr 1
    unfold obsLaw markedMass jointMass
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
      Real.toNNReal_mul hu]
    congr 1
    apply NNReal.eq
    simpa [Real.coe_toNNReal] using ENNReal.coe_toNNReal_eq_toReal
      (P.pmf (x, a, true))
  · congr 1
    · congr 1
      rw [Real.toNNReal_mul htp]
      rw [hauxNN]
    · congr 1
      rw [Real.toNNReal_mul ht]
      rw [hauxNN]

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
