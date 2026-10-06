module
public import Causalean.Stat.Concentration.BoundedVariation.CopyJensen
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# Sign-swap law for independent path copies

For an independent finite path family, the joint law of its differences from
an independent copy is invariant under coordinatewise sign changes.
-/

public section

open MeasureTheory ProbabilityTheory

namespace Causalean.Stat.Concentration.BoundedVariation

/-- For finitely many [measurable](hyp:hWmeas) and [mutually
independent](hyp:hind) random continuous paths, [swapping the two
independent draws in any selected coordinates leaves the joint law of the
array of differences between the draws unchanged](goal).

The statement is distributional and needs no moment assumptions.
-/
theorem independent_copy_difference_map_sign_invariant
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (W : Fin n → Ω → Path)
    (hWmeas : ∀ j, Measurable (W j))
    (hind : iIndepFun W μ) (σ : Fin n → Bool) :
    (μ.prod μ).map (fun p : Ω × Ω => fun j : Fin n => W j p.1 - W j p.2) =
      (μ.prod μ).map (fun p : Ω × Ω => fun j : Fin n =>
        if σ j then W j p.1 - W j p.2 else W j p.2 - W j p.1) := by
  let : BorelSpace Path := ⟨rfl⟩
  let ν : Fin n → Measure Path := fun j => μ.map (W j)
  let ρ : Measure (Fin n → Path × Path) := Measure.pi (fun j => (ν j).prod (ν j))
  let B : Ω × Ω → Fin n → Path × Path :=
    fun p j => (W j p.1, W j p.2)
  let S : (Fin n → Path × Path) → Fin n → Path × Path :=
    fun a j => if σ j then a j else Prod.swap (a j)
  let D : (Fin n → Path × Path) → Fin n → Path :=
    fun a j => (a j).1 - (a j).2
  have hν : ∀ j, SigmaFinite (ν j) := by
    intro j
    infer_instance
  have hW : MeasurePreserving (fun ω => fun j => W j ω) μ (Measure.pi ν) := by
    refine ⟨measurable_pi_iff.mpr (fun j => hWmeas j), ?_⟩
    exact hind.map_fun_eq_pi_map (fun j => (hWmeas j).aemeasurable)
  have hB : MeasurePreserving B (μ.prod μ) ρ := by
    have hp := hW.prod hW
    have he := (measurePreserving_arrowProdEquivProdArrow Path Path (Fin n) ν ν).symm
    convert he.comp hp using 1
    funext p j
    rfl
  have hS : MeasurePreserving S ρ ρ := by
    change MeasurePreserving (fun a j => (fun q => if σ j then q else Prod.swap q) (a j))
      (Measure.pi fun j => (ν j).prod (ν j)) (Measure.pi fun j => (ν j).prod (ν j))
    apply measurePreserving_pi (fun j => (ν j).prod (ν j))
      (fun j => (ν j).prod (ν j))
      (f := fun j q => if σ j then q else Prod.swap q)
    intro j
    by_cases hj : σ j
    · convert (MeasurePreserving.id ((ν j).prod (ν j))) using 1
      funext q
      simp [hj]
    · simpa [S, hj] using
        (Measure.measurePreserving_swap (μ := ν j) (ν := ν j))
  have hD : Measurable D := by
    apply measurable_pi_iff.mpr
    intro j
    exact continuous_sub.measurable.comp (measurable_pi_apply j)
  have hEq : ρ.map D = ρ.map (D ∘ S) := by
    rw [← Measure.map_map hD hS.measurable, hS.map_eq]
  have hleft : (μ.prod μ).map (D ∘ B) = ρ.map D := by
    rw [← Measure.map_map hD hB.measurable, hB.map_eq]
  have hright : (μ.prod μ).map ((D ∘ S) ∘ B) = ρ.map (D ∘ S) := by
    rw [← Measure.map_map (hD.comp hS.measurable) hB.measurable, hB.map_eq]
  calc
    (μ.prod μ).map (fun p : Ω × Ω => fun j : Fin n => W j p.1 - W j p.2) =
        (μ.prod μ).map (D ∘ B) := rfl
    _ = ρ.map D := hleft
    _ = ρ.map (D ∘ S) := hEq
    _ = (μ.prod μ).map ((D ∘ S) ∘ B) := hright.symm
    _ = (μ.prod μ).map (fun p : Ω × Ω => fun j : Fin n =>
        if σ j then W j p.1 - W j p.2 else W j p.2 - W j p.1) := by
          congr 1
          funext p j
          by_cases hj : σ j <;> simp [D, S, B, hj]

end Causalean.Stat.Concentration.BoundedVariation
