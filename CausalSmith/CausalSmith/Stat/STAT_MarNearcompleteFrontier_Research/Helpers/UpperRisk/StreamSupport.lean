module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.StreamMoments

/-!
# Support of the observed success count

The observed outcome mark can be true only when the outcome arrived. These
helpers express that support condition for one observed record and for the
fourth ideal Poisson stream.
-/

@[expose] public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
open Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

/-- Count arrived successes in one cell of the fourth stream. -/
noncomputable def streamArrivedSuccessCount (d : ℕ)
    (streams : Fin 4 → Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.FiniteSample (Obs d))
    (x : Fin d) (a s : Bool) : ℝ :=
  finiteStreamCount (streams 3)
    (fun o ↦ inCell o x a s ∧ o.R = true ∧ o.RY = true)

-- @node: observedLaw_RY_implies_R_ae
/-- Under the observed-data law, a true recorded outcome mark almost surely
implies that the outcome arrived. Given [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the stated mathematical conclusion holds](goal). -/
lemma observedLaw_RY_implies_R_ae {d : ℕ} (P : FullLaw d) :
    ∀ᵐ o ∂(observedLaw P).toMeasure, o.RY = true → o.R = true := by
  let _ : MeasurableSpace (FullAtom d) := ⊤
  unfold observedLaw
  rw [← PMF.toMeasure_map observe P.pmf (measurable_of_finite _)]
  rw [ae_map_iff (measurable_of_finite _).aemeasurable (by measurability)]
  exact Filter.Eventually.of_forall fun w hRY => by
    cases hR : w.R <;> simp [observe, hR] at hRY ⊢

private lemma finitePoissonSample_RY_implies_R_ae {d : ℕ}
    (P : FullLaw d) (rate : NNReal) :
    ∀ᵐ z ∂finitePoissonSampleLaw (observedLaw P).toMeasure rate,
      ∀ i : Fin z.count, (z.points i).RY = true → (z.points i).R = true := by
  let good : Obs d → Prop := fun o => o.RY = true → o.R = true
  have hgood : MeasurableSet {o : Obs d | good o} := by measurability
  have hsample : MeasurableSet
      {z : FiniteSample (Obs d) | ∀ i : Fin z.count, good (z.points i)} := by
    rw [MeasurableSpace.measurableSet_iInf]
    intro m
    change MeasurableSet {z : Fin m → Obs d | ∀ i, good (z i)}
    rw [show {z : Fin m → Obs d | ∀ i, good (z i)} =
        Set.univ.pi (fun _ : Fin m => {o | good o}) by ext z; simp]
    exact MeasurableSet.univ_pi fun _ => hgood
  unfold finitePoissonSampleLaw
  apply (mem_ae_map_iff measurable_streamToFiniteSample.aemeasurable hsample).2
  have hstream : ∀ᵐ z : ℕ → Obs d ∂iidStreamLaw (observedLaw P).toMeasure,
      ∀ i, good (z i) := by
    rw [ae_all_iff]
    intro i
    have hmarg : Measure.map (fun z : ℕ → Obs d => z i)
        (iidStreamLaw (observedLaw P).toMeasure) = (observedLaw P).toMeasure := by
      unfold iidStreamLaw
      rw [Measure.infinitePi_map_eval]
    have himage : ∀ᵐ o ∂Measure.map (fun z : ℕ → Obs d => z i)
        (iidStreamLaw (observedLaw P).toMeasure), good o := by
      simpa only [hmarg] using observedLaw_RY_implies_R_ae P
    exact (ae_map_iff (measurable_pi_apply i).aemeasurable hgood).mp himage
  have hsource : ∀ᵐ z : ℕ × (ℕ → Obs d)
      ∂poissonIIDStreamLaw (observedLaw P).toMeasure rate,
      ∀ i, good (z.2 i) := by
    unfold poissonIIDStreamLaw
    exact measurePreserving_snd.quasiMeasurePreserving.ae hstream
  exact hsource.mono fun z hz i => hz i

-- @node: streamU_eq_arrivedSuccess_ae
/-- Under the ideal four-stream law, the fourth-stream success count agrees
almost surely with the count of successes whose outcomes arrived. Given [the specified input `n`](hyp:n), [the specified input `d`](hyp:d), [the specified input `P`](hyp:P), [the specified input `x`](hyp:x), [the specified input `a`](hyp:a), [the specified input `s`](hyp:s), [the stated mathematical conclusion holds](goal). -/
lemma streamU_eq_arrivedSuccess_ae {n d : ℕ} (P : FullLaw d)
    (x : Fin d) (a s : Bool) :
    ∀ᵐ streams ∂fourStreamLaw n P,
      streamU d streams x a s =
        streamArrivedSuccessCount d streams x a s := by
  classical
  let rate : NNReal := (n : NNReal) / 2 * uniformFourMass 3
  have hindependent : fourStreamLaw n P =
      Measure.pi (fun i : Fin 4 =>
        finitePoissonSampleLaw (observedLaw P).toMeasure
          ((n : NNReal) / 2 * uniformFourMass i)) := by
    unfold fourStreamLaw
    exact labeledStreamLaw_eq_independent _ _ _ _
  have hfourth : ∀ᵐ z ∂finitePoissonSampleLaw (observedLaw P).toMeasure rate,
      ∀ i : Fin z.count, (z.points i).RY = true → (z.points i).R = true :=
    finitePoissonSample_RY_implies_R_ae P rate
  rw [hindependent]
  have hlift : ∀ᵐ streams ∂Measure.pi (fun i : Fin 4 =>
      finitePoissonSampleLaw (observedLaw P).toMeasure
        ((n : NNReal) / 2 * uniformFourMass i)),
      ∀ j : Fin (streams 3).count,
        ((streams 3).points j).RY = true → ((streams 3).points j).R = true := by
    simpa [rate] using
      (measurePreserving_eval (μ := fun i : Fin 4 =>
        finitePoissonSampleLaw (observedLaw P).toMeasure
          ((n : NNReal) / 2 * uniformFourMass i)) (3 : Fin 4)).quasiMeasurePreserving.ae
        hfourth
  filter_upwards [hlift] with streams hs
  generalize hsample : streams 3 = sample at hs ⊢
  rcases sample with ⟨N, z⟩
  unfold streamU streamArrivedSuccessCount finiteStreamCount
  rw [hsample]
  apply Finset.sum_congr rfl
  intro i hi
  simp only
  by_cases hcell : inCell (z i) x a s
  · by_cases hRY : (z i).RY = true
    · have hR : (z i).R = true := by
        simpa [FiniteSample.points] using hs i hRY
      simp [hcell, hRY, hR]
    · simp [hcell, hRY]
  · simp [hcell]

end CausalSmith.Stat.MarNearcompleteFrontier
