module
public import Causalean.Stat.EmpiricalProcess.Countable.Basic

/-!
# Coordinatewise exchange of two iid samples

A fixed Boolean sign vector selects which paired coordinates to exchange.
The exchange is an involutive measurable equivalence and preserves the
two-copy iid product law. Applied to a sample difference, it multiplies
each coordinate by the corresponding sign. This module isolates product-law
symmetry from the analytic moment comparisons in Ghost.

Mathlib already supplies measurePreserving_arrowProdEquivProdArrow for
pairing the sample coordinates and measurePreserving_pi for the coordinate
maps. Only their partial-swap composition is needed here.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators
namespace Causalean.Stat.EmpiricalProcess.Countable

/-- [The paired-sample swap](goal) determined by [a fixed sign
vector σ](hyp:σ) is the measurable involution of pairs of samples that keeps
the j-th paired coordinates in place when σ_j is positive and exchanges
them when σ_j is negative. -/
def pairedSampleSwap {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (σ : Fin n → Bool) : ((Fin n → Ω) × (Fin n → Ω)) ≃ᵐ
      ((Fin n → Ω) × (Fin n → Ω)) where
  toFun p := (fun j => if σ j then p.1 j else p.2 j,
    fun j => if σ j then p.2 j else p.1 j)
  invFun p := (fun j => if σ j then p.1 j else p.2 j,
    fun j => if σ j then p.2 j else p.1 j)
  left_inv p := by
    ext j <;> cases h : σ j <;> simp [h]
  right_inv p := by
    ext j <;> cases h : σ j <;> simp [h]
  measurable_toFun := by
    apply Measurable.prodMk <;> apply measurable_pi_lambda <;> intro j
    · cases σ j <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · exact (measurable_pi_apply j).comp measurable_snd
      · exact (measurable_pi_apply j).comp measurable_fst
    · cases σ j <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · exact (measurable_pi_apply j).comp measurable_fst
      · exact (measurable_pi_apply j).comp measurable_snd
  measurable_invFun := by
    apply Measurable.prodMk <;> apply measurable_pi_lambda <;> intro j
    · cases σ j <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · exact (measurable_pi_apply j).comp measurable_snd
      · exact (measurable_pi_apply j).comp measurable_fst
    · cases σ j <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · exact (measurable_pi_apply j).comp measurable_fst
      · exact (measurable_pi_apply j).comp measurable_snd

/-- For two independent iid samples from [a probability law μ](hyp:μ) and
[any fixed sign vector σ](hyp:σ), [the paired-sample swap selected by σ
preserves the joint product law of the two samples](goal). -/
theorem pairedSampleSwap_measurePreserving {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (σ : Fin n → Bool) :
    MeasurePreserving (pairedSampleSwap (Ω := Ω) σ)
      ((Measure.pi (fun _ : Fin n => μ)).prod (Measure.pi (fun _ : Fin n => μ)))
      ((Measure.pi (fun _ : Fin n => μ)).prod (Measure.pi (fun _ : Fin n => μ))) := by
  -- Let e = MeasurableEquiv.arrowProdEquivProdArrow Ω Ω (Fin n).
  -- Mathlib proves e preserves pi_j (μ.prod μ) to (pi_j μ).prod (pi_j μ).
  -- On paired coordinates use identity when σ j is true and Prod.swap
  -- otherwise; both preserve μ.prod μ. Apply measurePreserving_pi and
  -- conjugate with e and e.symm. This is a law identity, with no moment input.
  let e := MeasurableEquiv.arrowProdEquivProdArrow Ω Ω (Fin n)
  have he := measurePreserving_arrowProdEquivProdArrow Ω Ω (Fin n)
    (fun _ => μ) (fun _ => μ)
  let t : Fin n → Ω × Ω → Ω × Ω := fun j p => if σ j then p else p.swap
  have ht : ∀ j, MeasurePreserving (t j) (μ.prod μ) (μ.prod μ) := by
    intro j
    cases h : σ j
    · simpa [t, h] using (Measure.measurePreserving_swap (μ := μ) (ν := μ))
    · simp only [t, h, ↓reduceIte]
      exact ⟨measurable_id, Measure.map_id⟩
  have hp := measurePreserving_pi (fun _ : Fin n => μ.prod μ)
    (fun _ : Fin n => μ.prod μ) ht
  have hc := he.comp (hp.comp (he.symm e))
  convert hc using 1
  funext p
  ext j <;> cases h : σ j <;> simp [pairedSampleSwap, e, t,
    MeasurableEquiv.arrowProdEquivProdArrow, h]

/-- For [an indexed function class](hyp:f), [a sign vector σ](hyp:σ), and
[a pair of samples](hyp:p), [the ghost supremum after applying the
paired-sample swap selected by σ equals the σ-signed ghost supremum of the
original pair](goal). -/
theorem ghostSup_pairedSampleSwap {Ω ι : Type*} [MeasurableSpace Ω]
    (f : ι → Ω → ℝ) {n : ℕ} (σ : Fin n → Bool)
    (p : (Fin n → Ω) × (Fin n → Ω)) :
    ghostSup f ((pairedSampleSwap σ p).1) ((pairedSampleSwap σ p).2) =
      signedGhostSup f p.1 p.2 σ := by
  unfold ghostSup signedGhostSup
  congr 1
  funext i
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  cases h : σ j <;> simp [pairedSampleSwap, h, sub_eq_add_neg, add_comm]

end Causalean.Stat.EmpiricalProcess.Countable
