module
public import Causalean.Stat.Sample.OccupancyWeightedMean.ObservedRisk.Occupancy

/-!
# Occupancy bounds for an observed law

These lemmas transport the finite cell-arm design bounds to measurable labels
of an arbitrary observed probability space. The marks and their distribution
play no role. In particular, null cells and zero usable totals retain the
guards used by the design bounds.
-/

public section

namespace Causalean.Stat.Sample.OccupancyWeightedMean.ObservedRisk

open MeasureTheory Causalean.Stat

/-- For any observed probability law and measurable finite cell and arm labels,
occupied-cell overlap bounds the probability of no matched cell by a uniform
constant times `1/n + card(κ)/n²`. -/
theorem observed_bad_occupancy_rate (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon_half : epsilon < 1 / 2) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (Ω κ : Type) [MeasurableSpace Ω] [Fintype κ] [DecidableEq κ]
        [MeasurableSpace κ] [MeasurableSingletonClass κ]
        (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : Ω → κ) (A : Ω → Bool) (n : ℕ),
        Measurable X → Measurable A → 0 < n →
        (∀ a k, 0 < cellMass μ X k →
          epsilon * cellMass μ X k ≤ armCellMass μ X A a k) →
        ((Measure.pi (fun _ : Fin n => μ))
          {z | usableTotal X A z = 0}).toReal ≤
          B * (1 / (n : ℝ) + (Fintype.card κ : ℝ) / (n : ℝ) ^ 2) := by
  classical
  obtain ⟨B, hB, hrate⟩ := bad_occupancy_rate epsilon hepsilon hepsilon_half
  refine ⟨B, hB, ?_⟩
  intro Ω κ _ _ _ _ _ μ _ X A n hX hA hn hoverlap
  let f : Ω → κ × Bool := fun ω => (X ω, A ω)
  let ν : Measure (κ × Bool) := μ.map f
  have hf : Measurable f := hX.prodMk hA
  haveI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hf.aemeasurable
  have hcell (k : κ) : cellMass ν (fun v : κ × Bool => v.1) k =
      cellMass μ X k := by
    unfold cellMass ν
    change ((μ.map f) {v : κ × Bool | v.1 = k}).toReal =
      (μ {ω | X ω = k}).toReal
    rw [Measure.map_apply hf (measurableSet_eq_fun measurable_fst measurable_const)]
    rfl
  have harm (a : Bool) (k : κ) :
      armCellMass ν (fun v : κ × Bool => v.1) (fun v => v.2) a k =
        armCellMass μ X A a k := by
    unfold armCellMass ν
    change ((μ.map f) {v : κ × Bool | v.1 = k ∧ v.2 = a}).toReal =
      (μ {ω | X ω = k ∧ A ω = a}).toReal
    rw [Measure.map_apply hf (Set.Finite.measurableSet (Set.toFinite _))]
    rfl
  have hoverlap' : ∀ a k,
      0 < cellMass ν (fun v : κ × Bool => v.1) k →
      epsilon * cellMass ν (fun v => v.1) k ≤
        armCellMass ν (fun v => v.1) (fun v => v.2) a k := by
    intro a k hk
    rw [hcell, harm]
    exact hoverlap a k (hcell k ▸ hk)
  let F : (Fin n → Ω) → (Fin n → κ × Bool) :=
    fun z i => f (z i)
  have hF : Measurable F := measurable_pi_lambda _ (fun i => hf.comp (measurable_pi_apply i))
  have hpi : (Measure.pi (fun _ : Fin n => μ)).map F =
      Measure.pi (fun _ : Fin n => ν) := iid_design_marginal n μ X A hX hA
  have hE : MeasurableSet
      {z : Fin n → κ × Bool | usableTotal (fun v : κ × Bool => v.1)
        (fun v => v.2) z = 0} :=
    measurableSet_eq_fun
      (measurable_usableGroupTotal (fun v : κ × Bool => v.1)
        (fun v => v.2) measurable_fst measurable_snd) measurable_const
  have htransport :
      ((Measure.pi (fun _ : Fin n => μ))
        {z | usableTotal X A z = 0}).toReal =
      ((Measure.pi (fun _ : Fin n => ν))
        {z | usableTotal (fun v : κ × Bool => v.1) (fun v => v.2) z = 0}).toReal := by
    rw [← hpi, Measure.map_apply hF hE]
    rfl
  rw [htransport]
  exact hrate κ ν n hn hoverlap'

/-- An [overlap margin below one half](hyp:epsilon,hepsilon,hepsilon_half)
gives [a uniform `1/n + card(κ)/n²` bound for the mean guarded reciprocal
usable total](goal) under any observed finite-cell law satisfying occupied-cell
overlap. -/
theorem observed_reciprocal_occupancy_rate (epsilon : ℝ)
    (hepsilon : 0 < epsilon) (hepsilon_half : epsilon < 1 / 2) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (Ω κ : Type) [MeasurableSpace Ω] [Fintype κ] [DecidableEq κ]
        [MeasurableSpace κ] [MeasurableSingletonClass κ]
        (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : Ω → κ) (A : Ω → Bool) (n : ℕ),
        Measurable X → Measurable A → 0 < n →
        (∀ a k, 0 < cellMass μ X k →
          epsilon * cellMass μ X k ≤ armCellMass μ X A a k) →
        (∫ z : Fin n → Ω, inverseUsableGroupTotal X A z
          ∂Measure.pi (fun _ : Fin n => μ)) ≤
          B * (1 / (n : ℝ) + (Fintype.card κ : ℝ) / (n : ℝ) ^ 2) := by
  classical
  obtain ⟨B, hB, hrate⟩ := reciprocal_occupancy_rate epsilon hepsilon hepsilon_half
  refine ⟨B, hB, ?_⟩
  intro Ω κ _ _ _ _ _ μ _ X A n hX hA hn hoverlap
  let f : Ω → κ × Bool := fun ω => (X ω, A ω)
  let ν : Measure (κ × Bool) := μ.map f
  have hf : Measurable f := hX.prodMk hA
  haveI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hf.aemeasurable
  have hcell (k : κ) : cellMass ν (fun v : κ × Bool => v.1) k =
      cellMass μ X k := by
    unfold cellMass ν
    change ((μ.map f) {v : κ × Bool | v.1 = k}).toReal =
      (μ {ω | X ω = k}).toReal
    rw [Measure.map_apply hf (measurableSet_eq_fun measurable_fst measurable_const)]
    rfl
  have harm (a : Bool) (k : κ) :
      armCellMass ν (fun v : κ × Bool => v.1) (fun v => v.2) a k =
        armCellMass μ X A a k := by
    unfold armCellMass ν
    change ((μ.map f) {v : κ × Bool | v.1 = k ∧ v.2 = a}).toReal =
      (μ {ω | X ω = k ∧ A ω = a}).toReal
    rw [Measure.map_apply hf (Set.Finite.measurableSet (Set.toFinite _))]
    rfl
  have hoverlap' : ∀ a k,
      0 < cellMass ν (fun v : κ × Bool => v.1) k →
      epsilon * cellMass ν (fun v => v.1) k ≤
        armCellMass ν (fun v => v.1) (fun v => v.2) a k := by
    intro a k hk
    rw [hcell, harm]
    exact hoverlap a k (hcell k ▸ hk)
  let F : (Fin n → Ω) → (Fin n → κ × Bool) := fun z i => f (z i)
  have hF : Measurable F := measurable_pi_lambda _ (fun i => hf.comp (measurable_pi_apply i))
  have hpi : (Measure.pi (fun _ : Fin n => μ)).map F =
      Measure.pi (fun _ : Fin n => ν) := iid_design_marginal n μ X A hX hA
  have hkernel : Measurable
      (inverseUsableGroupTotal (fun v : κ × Bool => v.1) (fun v => v.2) :
        (Fin n → κ × Bool) → ℝ) :=
    measurable_inverseUsableGroupTotal _ _ measurable_fst measurable_snd
  have htransport :
      (∫ z : Fin n → Ω, inverseUsableGroupTotal X A z
        ∂Measure.pi (fun _ : Fin n => μ)) =
      (∫ z : Fin n → κ × Bool,
        inverseUsableGroupTotal (fun v => v.1) (fun v => v.2) z
        ∂Measure.pi (fun _ : Fin n => ν)) := by
    rw [← hpi, integral_map hF.aemeasurable hkernel.aestronglyMeasurable]
    rfl
  rw [htransport]
  exact hrate κ ν n hn hoverlap'

end Causalean.Stat.Sample.OccupancyWeightedMean.ObservedRisk
