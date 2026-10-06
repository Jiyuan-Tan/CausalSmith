module
public import Causalean.Mathlib.Probability.Independence.Conditional.ThreeBlockShiftedProduct

/-!
# Four-coordinate shifted product moment

The training coordinate is coordinate zero, and the three held-out scores use
coordinates one, two, and three. This is a direct generic specialization of
the block formulation.
-/

public section

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability.Independence

namespace Causalean.Mathlib.Probability.Independence.Conditional.ThreeBlockShiftedProduct

/-- [A four-coordinate product probability law](hyp:ν), [three held-out coordinate
scores and three coordinate-zero shifts](hyp:f,a) with [measurability](hyp:hfmeas,hameas)
and [integrability](hyp:hf,ha), [an integrable first shifted pair](hyp:hshift01), and
[an integrable shifted three-factor product](hyp:hshiftprod) imply that [the conditional
mean of the shifted three-coordinate product is the product of its shifted means](goal). -/
theorem condExp_shiftedFourCoordinateProduct
    {X : Fin 4 → Type*} [∀ i, MeasurableSpace (X i)]
    [∀ i, StandardBorelSpace (X i)]
    (ν : (i : Fin 4) → Measure (X i)) [∀ i, IsProbabilityMeasure (ν i)]
    (f : (t : Fin 3) → X t.succ → ℝ) (a : (t : Fin 3) → X 0 → ℝ)
    (hfmeas : ∀ t, Measurable (f t)) (hameas : ∀ t, Measurable (a t))
    (hf : ∀ t, Integrable (fun x : ∀ i, X i => f t (x t.succ)) (Measure.pi ν))
    (ha : ∀ t, Integrable (fun x : ∀ i, X i => a t (x 0)) (Measure.pi ν))
    (hshift01 : Integrable (fun x : ∀ i, X i =>
      (f 0 (x 1) - a 0 (x 0)) * (f 1 (x 2) - a 1 (x 0))) (Measure.pi ν))
    (hshiftprod : Integrable (fun x : ∀ i, X i =>
      ∏ t : Fin 3, (f t (x t.succ) - a t (x 0))) (Measure.pi ν)) :
    condExp (MeasurableSpace.comap
      (finsetCoordProj (Ω := X) ({0} : Finset (Fin 4))) inferInstance)
      (Measure.pi ν)
      (fun x : ∀ i, X i => ∏ t : Fin 3, (f t (x t.succ) - a t (x 0)))
      =ᵐ[Measure.pi ν]
    (fun x => ∏ t : Fin 3,
      ((∫ y : (∀ i, X i), f t (y t.succ) ∂Measure.pi ν) - a t (x 0))) := by
  classical
  let B : Fin 3 → Finset (Fin 4) := fun t => {t.succ}
  have htrain : ∀ t, Disjoint ({0} : Finset (Fin 4)) (B t) := by
    intro t
    simpa [B] using (Fin.succ_ne_zero t).symm
  have heval : Pairwise (fun s t : Fin 3 => Disjoint (B s) (B t)) := by
    intro s t hst
    simpa [B] using (Fin.succ_injective 3).ne hst
  let f' : (t : Fin 3) → ((i : {i // i ∈ B t}) → X i.val) → ℝ :=
    fun t z => f t (z ⟨t.succ, Finset.mem_singleton_self _⟩)
  let a' : (t : Fin 3) → ((i : {i // i ∈ ({0} : Finset (Fin 4))}) → X i.val) → ℝ :=
    fun t z => a t (z ⟨0, Finset.mem_singleton_self _⟩)
  have hf'meas (t : Fin 3) : Measurable (f' t) :=
    (hfmeas t).comp (measurable_pi_apply
      (⟨t.succ, Finset.mem_singleton_self _⟩ : {i // i ∈ B t}))
  have ha'meas (t : Fin 3) : Measurable (a' t) :=
    (hameas t).comp (measurable_pi_apply
      (⟨0, Finset.mem_singleton_self _⟩ : {i // i ∈ ({0} : Finset (Fin 4))}))
  have hf' (t : Fin 3) : Integrable
      (fun x : ∀ i, X i => f' t (finsetCoordProj (B t) x)) (Measure.pi ν) := by
    exact hf t
  have ha' (t : Fin 3) : Integrable
      (fun x : ∀ i, X i => a' t (finsetCoordProj ({0} : Finset (Fin 4)) x))
      (Measure.pi ν) := by
    exact ha t
  have hshift01' : Integrable (fun x : ∀ i, X i =>
      (f' 0 (finsetCoordProj (B 0) x) -
        a' 0 (finsetCoordProj ({0} : Finset (Fin 4)) x)) *
      (f' 1 (finsetCoordProj (B 1) x) -
        a' 1 (finsetCoordProj ({0} : Finset (Fin 4)) x)))
      (Measure.pi ν) := by
    exact hshift01
  have hshiftprod' : Integrable
      (shiftedThreeBlockProduct ({0} : Finset (Fin 4)) B f' a')
      (Measure.pi ν) := by
    exact hshiftprod
  have h := condExp_shiftedThreeBlockProduct ν ({0} : Finset (Fin 4)) B
    htrain heval f' a' hf'meas ha'meas hf' ha' hshift01' hshiftprod'
  have hfun : shiftedThreeBlockProduct ({0} : Finset (Fin 4)) B f' a' =
      (fun x : ∀ i, X i => ∏ t : Fin 3, (f t (x t.succ) - a t (x 0))) := rfl
  rw [hfun] at h
  simpa only [finsetCoordProj, f', a', B] using h

end Causalean.Mathlib.Probability.Independence.Conditional.ThreeBlockShiftedProduct
