module
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Population mass of a countable nested union

Localization on every member of a countable nested chain passes to its
containing union without loss in the population mass budget. This is the
bridge needed before using an energy bound on that union. The empty chain
is included by requiring the budget to be nonnegative.
-/

public section

open MeasureTheory Set
namespace Causalean.Stat.EmpiricalProcess.Countable

/-- Let [a countable family of sets](hyp:B) be [measurable](hyp:hB) and
[nested, any two members being comparable by inclusion](hyp:hchain), and let
[a weight g](hyp:g) be [integrable under μ](hyp:μ,hg) and
[nonnegative](hyp:hpos). If [a nonnegative budget L](hyp:L,hL) [bounds the
integral of g over every member](hyp:hbudget), then [the union of the
family is measurable and the integral of g over the union is at most
L](goal).

The empty family is covered because the budget is nonnegative.
-/
theorem countable_chain_union_mass_le {Ω ι : Type*} [MeasurableSpace Ω]
    [Countable ι] (μ : Measure Ω) (B : ι → Set Ω)
    (hB : ∀ i, MeasurableSet (B i))
    (hchain : ∀ i k, B i ⊆ B k ∨ B k ⊆ B i)
    (g : Ω → ℝ) (hg : Integrable g μ) (hpos : ∀ x, 0 ≤ g x)
    (L : ℝ) (hL : 0 ≤ L) (hbudget : ∀ i, (∫ x in B i, g x ∂μ) ≤ L) :
    MeasurableSet (⋃ i, B i) ∧ (∫ x in ⋃ i, B i, g x ∂μ) ≤ L := by
  refine ⟨MeasurableSet.iUnion hB, ?_⟩
  have hd : Directed (· ⊆ ·) B := by
    intro i k
    rcases hchain i k with h | h
    · exact ⟨k, h, Subset.rfl⟩
    · exact ⟨i, Subset.rfl, h⟩
  have hb : (∫⁻ x in ⋃ i, B i, ENNReal.ofReal (g x) ∂μ) ≤ ENNReal.ofReal L := by
    rw [setLIntegral_iUnion_of_directed _ hd]
    refine iSup_le fun i => ?_
    rw [← ofReal_integral_eq_lintegral_ofReal hg.integrableOn
      (Filter.Eventually.of_forall hpos)]
    exact ENNReal.ofReal_le_ofReal (hbudget i)
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hpos)
    hg.integrableOn.aestronglyMeasurable]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb).trans_eq
    (ENNReal.toReal_ofReal hL)

end Causalean.Stat.EmpiricalProcess.Countable
