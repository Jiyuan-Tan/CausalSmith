module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.Representation

/-! Independence of the retained pilot statistic and post-pilot sample. -/

@[expose] public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

abbrev PilotCoord (n : ℕ) := {i : Fin n // i.val < pilotSize n}

def restrictPilot (n : ℕ) (sample : Fin n → SampleObs n) :
    PilotCoord n → SampleObs n := fun i => sample i.1

lemma measurable_restrictPilot (n : ℕ) : Measurable (restrictPilot n) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply i.1

private def fillPilot (n : ℕ) (sample : PilotCoord n → SampleObs n) :
    Fin n → SampleObs n := fun i =>
  if h : i.val < pilotSize n then sample ⟨i, h⟩
  else (⟨i, false, 0⟩ : SampleObs n)

private lemma measurable_fillPilot (n : ℕ) : Measurable (fillPilot n) := by
  apply measurable_pi_lambda
  intro i
  by_cases h : i.val < pilotSize n
  · simp only [fillPilot, h, dite_true]
    exact measurable_pi_apply (⟨i, h⟩ : PilotCoord n)
  · simp only [fillPilot, h, dite_false]
    exact measurable_const

private lemma pilotTau_fill_restrict (n : ℕ) (M : ℝ)
    (sample : Fin n → SampleObs n) :
    pilotTau n M (fillPilot n (restrictPilot n sample)) = pilotTau n M sample := by
  have hcount (a : Bool) (k : Fin n) :
      pilotCount n (fillPilot n (restrictPilot n sample)) a k =
        pilotCount n sample a k := by
    unfold pilotCount
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : i.val < pilotSize n <;> simp [fillPilot, restrictPilot, h]
  have hsum (a : Bool) (k : Fin n) :
      pilotSum n (fillPilot n (restrictPilot n sample)) a k =
        pilotSum n sample a k := by
    unfold pilotSum
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : i.val < pilotSize n <;> simp [fillPilot, restrictPilot, h]
  simp [pilotTau, pilotOccupancy, pilotMatched, pilotMean, hcount, hsum]

private def complementPilotEquivPostPilot (n : ℕ) :
    Subtype (fun i : Fin n => ¬i.val < pilotSize n) ≃ PostPilotCoord n where
  toFun i := ⟨i.1, by omega⟩
  invFun i := ⟨i.1, by omega⟩
  left_inv i := by ext; rfl
  right_inv i := by ext; rfl

private lemma map_restrictPilot_productLaw {n : ℕ} (P : Law n) :
    Measure.map (restrictPilot n)
        (DiscreteAteHeterogeneityFrontier.productLaw n P) =
      Measure.pi (fun _ : PilotCoord n => P.observedLaw) := by
  unfold DiscreteAteHeterogeneityFrontier.productLaw restrictPilot
  exact Causalean.Stat.map_pi_restrict P.observedLaw
    (fun i : Fin n => i.val < pilotSize n)

/-- The coordinate restrictions to the pilot and retained post-pilot blocks
have the exact product law. -/
lemma map_restrictPilot_restrictPostPilot_productLaw {n : ℕ} (P : Law n) :
    Measure.map (fun sample => (restrictPilot n sample, restrictPostPilot n sample))
        (DiscreteAteHeterogeneityFrontier.productLaw n P) =
      (Measure.pi fun _ : PilotCoord n => P.observedLaw).prod
        (Measure.pi fun _ : PostPilotCoord n => P.observedLaw) := by
  classical
  let ep := complementPilotEquivPostPilot n
  let hsplit := MeasureTheory.measurePreserving_piEquivPiSubtypeProd
    (μ := fun _ : Fin n => P.observedLaw) (fun i => i.val < pilotSize n)
  let hpost := MeasureTheory.measurePreserving_piCongrLeft
    (fun _ : PostPilotCoord n => P.observedLaw) ep
  have hjoint := (MeasurePreserving.prod
    (MeasurePreserving.id (Measure.pi fun _ : PilotCoord n => P.observedLaw)) hpost).comp hsplit
  unfold DiscreteAteHeterogeneityFrontier.productLaw
  rw [← hjoint.map_eq]
  congr 1

/-- The retained pilot statistic is independent of the complete post-pilot
coordinate block under the fixed i.i.d. product law. -/
lemma map_pilotTau_restrictPostPilot_productLaw {n : ℕ} (M : ℝ) (P : Law n) :
    Measure.map (fun sample => (pilotTau n M sample, restrictPostPilot n sample))
        (DiscreteAteHeterogeneityFrontier.productLaw n P) =
      (Measure.map (pilotTau n M)
        (DiscreteAteHeterogeneityFrontier.productLaw n P)).prod
        (Measure.pi fun _ : PostPilotCoord n => P.observedLaw) := by
  let f := pilotTau n M ∘ fillPilot n
  have hf : Measurable f := (pilotTau_measurable n M).comp (measurable_fillPilot n)
  have hsplit := map_restrictPilot_restrictPostPilot_productLaw P
  have hmap := congrArg (Measure.map (Prod.map f id)) hsplit
  rw [Measure.map_map (hf.prodMap measurable_id)
      ((measurable_restrictPilot n).prodMk (by
        unfold restrictPostPilot
        fun_prop)),
    ← Measure.map_prod_map _ _ hf measurable_id, Measure.map_id] at hmap
  convert hmap using 1
  · congr 1
    funext sample
    apply Prod.ext
    · exact (pilotTau_fill_restrict n M sample).symm
    · rfl
  · congr 1
    rw [← map_restrictPilot_productLaw P,
      Measure.map_map hf (measurable_restrictPilot n)]
    congr 1
    funext sample
    exact (pilotTau_fill_restrict n M sample).symm

private noncomputable def fixedPrefixSamplesOfPost (n u v : ℕ)
    (h : u + v ≤ postPilotSize n) (sample : PostPilotCoord n → SampleObs n) :
    FiniteSample (SampleObs n) × FiniteSample (SampleObs n) :=
  (fixedSizeEmbed u (fun i => sample ⟨⟨pilotSize n + i, by
      simp only [postPilotSize, pilotSize] at h ⊢
      omega⟩, by
        change pilotSize n ≤ pilotSize n + i.val
        omega⟩),
    fixedSizeEmbed v (fun i => sample ⟨⟨pilotSize n + u + i, by
      simp only [postPilotSize, pilotSize] at h ⊢
      omega⟩, by
        change pilotSize n ≤ pilotSize n + u + i.val
        omega⟩))

private lemma measurable_fixedPrefixSamplesOfPost (n u v : ℕ)
    (h : u + v ≤ postPilotSize n) :
    Measurable (fixedPrefixSamplesOfPost n u v h) := by
  apply Measurable.prodMk
  · apply (measurable_fixedSizeEmbed u).comp
    apply measurable_pi_lambda
    intro i
    exact measurable_pi_apply _
  · apply (measurable_fixedSizeEmbed v).comp
    apply measurable_pi_lambda
    intro i
    exact measurable_pi_apply _

private lemma fixedPrefixSamplesOfPost_restrict (n u v : ℕ)
    (h : u + v ≤ postPilotSize n) (sample : Fin n → SampleObs n) :
    fixedPrefixSamplesOfPost n u v h (restrictPostPilot n sample) =
      fixedPrefixSamples n u v h sample := by
  apply Prod.ext <;> rfl

/-- The retained pilot statistic is jointly independent of the two actual
fixed-size classifier and estimation prefixes. -/
lemma map_pilotTau_fixedPrefixSamples_productLaw {n u v : ℕ}
    (M : ℝ) (P : Law n) (h : u + v ≤ postPilotSize n) :
    Measure.map (fun sample => (pilotTau n M sample, fixedPrefixSamples n u v h sample))
        (DiscreteAteHeterogeneityFrontier.productLaw n P) =
      (Measure.map (pilotTau n M)
        (DiscreteAteHeterogeneityFrontier.productLaw n P)).prod
        ((Measure.map (fixedSizeEmbed u)
          (Measure.pi fun _ : Fin u => P.observedLaw)).prod
        (Measure.map (fixedSizeEmbed v)
          (Measure.pi fun _ : Fin v => P.observedLaw))) := by
  let g := fixedPrefixSamplesOfPost n u v h
  have hg : Measurable g := measurable_fixedPrefixSamplesOfPost n u v h
  have hsplit := map_pilotTau_restrictPostPilot_productLaw M P
  have hmap := congrArg (Measure.map (Prod.map id g)) hsplit
  rw [Measure.map_map (measurable_id.prodMap hg)
      ((pilotTau_measurable n M).prodMk (by
        unfold restrictPostPilot
        fun_prop)),
    ← Measure.map_prod_map _ _ measurable_id hg, Measure.map_id] at hmap
  have hgLaw : Measure.map g (Measure.pi fun _ : PostPilotCoord n => P.observedLaw) =
      (Measure.map (fixedSizeEmbed u)
        (Measure.pi fun _ : Fin u => P.observedLaw)).prod
      (Measure.map (fixedSizeEmbed v)
        (Measure.pi fun _ : Fin v => P.observedLaw)) := by
    rw [← map_restrictPostPilot_productLaw P,
      Measure.map_map hg (by
        unfold restrictPostPilot
        fun_prop)]
    convert map_fixedPrefixSamples_productLaw P h using 1
    congr 1
  rw [hgLaw] at hmap
  convert hmap using 1
  congr 1

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
