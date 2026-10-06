module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Basic
public import Mathlib.Probability.Kernel.Composition.Lemmas
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel

/-!
# Common-marginal gluing needed for fixed-law endpoint attainment

This file isolates the measure-theoretic reconstruction step needed to combine
two potential-outcome laws that share the same score marginal.  The gluing is
obtained by disintegrating both laws over their first coordinate and taking the
conditional product of the resulting kernels.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- For [the specified mathematical inputs](hyp:α,β,γ,ρ₀,ρ₁), [this definition](goal) introduces the corresponding object. -/
@[no_expose]
def glueAlongFst {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace.CountablyGenerated α]
    [StandardBorelSpace β] [Nonempty β]
    [StandardBorelSpace γ] [Nonempty γ]
    (ρ₀ : Measure (α × β)) (ρ₁ : Measure (α × γ))
    [IsFiniteMeasure ρ₀] [IsFiniteMeasure ρ₁] : Measure (α × (β × γ)) :=
  ρ₀.fst ⊗ₘ (ρ₀.condKernel ×ₖ ρ₁.condKernel)

/-- Given [the stated mathematical inputs and assumptions](hyp:α,β,γ,ρ₀,ρ₁), this result [establishes the stated mathematical conclusion](goal). -/
lemma glueAlongFst_isProbabilityMeasure {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace.CountablyGenerated α]
    [StandardBorelSpace β] [Nonempty β]
    [StandardBorelSpace γ] [Nonempty γ]
    (ρ₀ : Measure (α × β)) (ρ₁ : Measure (α × γ))
    [IsProbabilityMeasure ρ₀] [IsProbabilityMeasure ρ₁] :
    IsProbabilityMeasure (glueAlongFst ρ₀ ρ₁) := by
  unfold glueAlongFst
  infer_instance

/-- Given [the stated mathematical inputs and assumptions](hyp:α,β,γ,ρ₀,ρ₁), this result [establishes the stated mathematical conclusion](goal). -/
lemma glueAlongFst_map_left {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace.CountablyGenerated α]
    [StandardBorelSpace β] [Nonempty β]
    [StandardBorelSpace γ] [Nonempty γ]
    (ρ₀ : Measure (α × β)) (ρ₁ : Measure (α × γ))
    [IsFiniteMeasure ρ₀] [IsFiniteMeasure ρ₁] :
    (glueAlongFst ρ₀ ρ₁).map (fun p => (p.1, p.2.1)) = ρ₀ := by
  rw [glueAlongFst]
  change (ρ₀.fst ⊗ₘ (ρ₀.condKernel ×ₖ ρ₁.condKernel)).map
    (Prod.map id Prod.fst) = ρ₀
  rw [← Measure.compProd_map measurable_fst]
  rw [← Kernel.fst_eq, Kernel.fst_prod]
  exact ρ₀.disintegrate ρ₀.condKernel

/-- Given [the stated mathematical inputs and assumptions](hyp:α,β,γ,ρ₀,ρ₁,hfst), this result [establishes the stated mathematical conclusion](goal). -/
lemma glueAlongFst_map_right {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace.CountablyGenerated α]
    [StandardBorelSpace β] [Nonempty β]
    [StandardBorelSpace γ] [Nonempty γ]
    (ρ₀ : Measure (α × β)) (ρ₁ : Measure (α × γ))
    [IsFiniteMeasure ρ₀] [IsFiniteMeasure ρ₁]
    (hfst : ρ₀.fst = ρ₁.fst) :
    (glueAlongFst ρ₀ ρ₁).map (fun p => (p.1, p.2.2)) = ρ₁ := by
  rw [glueAlongFst]
  change (ρ₀.fst ⊗ₘ (ρ₀.condKernel ×ₖ ρ₁.condKernel)).map
    (Prod.map id Prod.snd) = ρ₁
  rw [← Measure.compProd_map measurable_snd]
  rw [← Kernel.snd_eq, Kernel.snd_prod, hfst]
  exact ρ₁.disintegrate ρ₁.condKernel

end
end CausalSmith.PartialID.UnlinkedPropensityAte
