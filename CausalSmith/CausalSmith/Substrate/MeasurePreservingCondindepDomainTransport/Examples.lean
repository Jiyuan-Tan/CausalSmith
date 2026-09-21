module
public import CausalSmith.Substrate.MeasurePreservingCondindepDomainTransport.CondIndep
public import CausalSmith.Substrate.MeasurePreservingCondindepDomainTransport.WithDensity
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Examples of sample-domain transport

These compile-time examples exercise the transport API for the identity equivalence and for the
nontrivial equivalence swapping the coordinates of a product sample space.
-/

public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace CausalSmith.Substrate.MeasurePreservingCondindepDomainTransport

section Identity

variable {Ω 𝒳 𝒴 𝒵 : Type*}
  [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [MeasurableSpace 𝒳] [MeasurableSpace 𝒴] [MeasurableSpace 𝒵]
  (μ : Measure Ω) [IsFiniteMeasure μ]
  (X : Ω → 𝒳) (Y : Ω → 𝒴) (Z : Ω → 𝒵)
  (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)

example :
    CondIndepFun (MeasurableSpace.comap (Z ∘ (MeasurableEquiv.refl Ω)) inferInstance)
        (hZ.comp (MeasurableEquiv.refl Ω).measurable).comap_le
        (X ∘ (MeasurableEquiv.refl Ω)) (Y ∘ (MeasurableEquiv.refl Ω)) μ ↔
      CondIndepFun (MeasurableSpace.comap Z inferInstance) hZ.comap_le X Y μ := by
  simpa using condIndepFun_comp_measurableEquiv_iff
    (MeasurableEquiv.refl Ω) (MeasurePreserving.id μ) X Y Z hX hY hZ

end Identity

section ProductSwap

variable {A B 𝒳 𝒴 𝒵 : Type*}
  [MeasurableSpace A] [StandardBorelSpace A]
  [MeasurableSpace B] [StandardBorelSpace B]
  [MeasurableSpace 𝒳] [MeasurableSpace 𝒴] [MeasurableSpace 𝒵]
  (μA : Measure A) (μB : Measure B)
  [IsFiniteMeasure μA] [IsFiniteMeasure μB]
  (X : B × A → 𝒳) (Y : B × A → 𝒴) (Z : B × A → 𝒵)
  (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)

example :
    CondIndepFun
        (MeasurableSpace.comap (Z ∘ (MeasurableEquiv.prodComm : A × B ≃ᵐ B × A))
          inferInstance)
        (hZ.comp (MeasurableEquiv.prodComm : A × B ≃ᵐ B × A).measurable).comap_le
        (X ∘ (MeasurableEquiv.prodComm : A × B ≃ᵐ B × A))
        (Y ∘ (MeasurableEquiv.prodComm : A × B ≃ᵐ B × A))
        (μA.prod μB) ↔
      CondIndepFun (MeasurableSpace.comap Z inferInstance) hZ.comap_le X Y
        (μB.prod μA) := by
  simpa using condIndepFun_comp_measurableEquiv_iff
    (MeasurableEquiv.prodComm : A × B ≃ᵐ B × A)
    (Measure.measurePreserving_swap (μ := μA) (ν := μB)) X Y Z hX hY hZ

end ProductSwap

end CausalSmith.Substrate.MeasurePreservingCondindepDomainTransport
