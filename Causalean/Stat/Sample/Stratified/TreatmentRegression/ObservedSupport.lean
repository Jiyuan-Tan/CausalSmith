module
public import Causalean.Stat.Sample.Stratified.TreatmentRegression.CategoricalLaw

/-! # Almost-sure support of observed categorical designs

A finite categorical sample almost surely visits only positive-mass cells.
This supports occupied-cell assumptions in both conditional residual bounds
and risk calculations without imposing assumptions on null cells.
-/

public section

namespace Causalean.Stat.Sample.Stratified.TreatmentRegression

open MeasureTheory Set

variable {Ω κ : Type*} [MeasurableSpace Ω] [Fintype κ] [DecidableEq κ]
  [MeasurableSpace κ] [MeasurableSingletonClass κ]

omit [DecidableEq κ] in
/-- [An iid sample law and measurable cell and treatment labels](hyp:n,μ,X,A,hX,hA)
ensure [that every observed cell has positive population mass almost surely](goal).

An iid sample almost surely visits only positive-mass population cells,
so population homogeneity restricted to occupied cells applies to its labels.

Finiteness of the categorical cell type is essential here: without it an
atomless label law would have zero mass at every sampled singleton. Show the
finite union of null label events has measure zero, then lift this almost-sure
statement to every coordinate using measurePreserving_eval and ae_all_iff.
-/
lemma ae_sample_cell_positive (n : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → κ) (A : Ω → Bool) (hX : Measurable X) (hA : Measurable A) :
    ∀ᵐ z : Fin n → Ω ∂Measure.pi (fun _ : Fin n => μ),
      ∀ i, 0 < cellProbability (μ.map (fun ω => (X ω, A ω))) (X (z i)) := by
  let ν : Measure (κ × Bool) := μ.map (fun ω => (X ω, A ω))
  let : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map (hX.prodMk hA).aemeasurable
  have hv : ∀ᵐ v ∂ν, 0 < cellProbability ν v.1 := by
    apply ae_iff_of_countable.mpr
    intro v hv
    apply ENNReal.toReal_pos _ (measure_ne_top ν _)
    intro hz
    have hs : ({v} : Set (κ × Bool)) ⊆ {u | u.1 = v.1} := by
      rintro u rfl
      rfl
    exact hv (measure_mono_null hs hz)
  have hω : ∀ᵐ ω ∂μ, 0 < cellProbability ν (X ω) :=
    (Measure.tendsto_ae_map (hX.prodMk hA).aemeasurable).eventually hv
  apply ae_all_iff.mpr
  intro i
  have heval := measurePreserving_eval (fun _ : Fin n => μ) i
  have hmap : ∀ᵐ ω ∂(Measure.pi (fun _ : Fin n => μ)).map (Function.eval i),
      0 < cellProbability ν (X ω) := by
    simpa only [heval.map_eq] using hω
  exact (Measure.tendsto_ae_map heval.aemeasurable).eventually hmap

end Causalean.Stat.Sample.Stratified.TreatmentRegression
