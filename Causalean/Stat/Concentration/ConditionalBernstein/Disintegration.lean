module
public import Causalean.Stat.Concentration.ConditionalBernstein.Basic
public import Causalean.Stat.Sample.PiTransport
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.Kernel.Composition.CompProd

/-!
# Design-fibre disintegration for arbitrary outcome spaces

This module exposes the generic kernel-law tensorization pattern used by
`RandomDesignWeightedHoeffding.product_observation_law_map_design_outcome`.
Unlike that conditional-distribution adapter, this kernel-native formulation accepts
arbitrary measurable outcome spaces and needs no standard-Borel hypothesis. A second
lemma integrates an almost-everywhere fibre event bound over a probability design law.
-/

public section

namespace Causalean.Stat.Concentration.ConditionalBernstein
open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

/-- Sampling [IID design/outcome pairs from an attached kernel law](hyp:Q,K) and separating
the complete design and outcome vectors yields [the design-product law attached to the
coordinatewise product outcome kernel](goal).

Generalize the rectangle proof in `RandomDesignWeightedHoeffding.Tail`'s private
`map_pi_compProd_arrowProdEquivProdArrow` from real outcomes to `Y`. Finite spanning
sets for the outcome-product pi-system can use the probability measure `K` at an
existing design point; handle an empty design type first. Alternatively use induction
on n with `piFinSuccAbove` and associativity of kernel products. No fixed outcome
reference measure or outcome-space topology should be added to the hypotheses.
-/
theorem iid_joint_map_split
    {D Y : Type*} [MeasurableSpace D] [MeasurableSpace Y] (n : ℕ)
    (Q : Measure D) [IsProbabilityMeasure Q]
    (K : Kernel D Y) [IsMarkovKernel K] :
    (Measure.pi (fun _ : Fin n => Q ⊗ₘ K)).map
        (fun z => (fun i => (z i).1, fun i => (z i).2)) =
      Measure.pi (fun _ : Fin n => Q) ⊗ₘ Causalean.Stat.finProductKernel n K := by
  classical
  let d₀ : D := Classical.choice (nonempty_of_isProbabilityMeasure Q)
  let split := MeasurableEquiv.arrowProdEquivProdArrow D Y (Fin n)
  let pairLaw : Measure (D × Y) := Q ⊗ₘ K
  let designLaw : Measure (Fin n → D) := Measure.pi (fun _ : Fin n => Q)
  let markKernel := Causalean.Stat.finProductKernel n K
  let : IsProbabilityMeasure pairLaw := by
    dsimp only [pairLaw]
    infer_instance
  let : IsProbabilityMeasure (Measure.pi (fun _ : Fin n => pairLaw)) := inferInstance
  let : IsProbabilityMeasure designLaw := by
    dsimp only [designLaw]
    infer_instance
  let : IsMarkovKernel markKernel := by
    dsimp only [markKernel]
    infer_instance
  let lhs := (Measure.pi (fun _ : Fin n => pairLaw)).map split
  let rhs := designLaw ⊗ₘ markKernel
  change lhs = rhs
  refine Measure.FiniteSpanningSetsIn.ext ?_ (isPiSystem_pi.prod isPiSystem_pi) ?_ ?_
  · refine (generateFrom_eq_prod generateFrom_pi generateFrom_pi ?_ ?_).symm
    · exact (Measure.FiniteSpanningSetsIn.pi
        (fun _ : Fin n => Q.toFiniteSpanningSetsIn)).isCountablySpanning
    · exact (Measure.FiniteSpanningSetsIn.pi
        (fun _ : Fin n => (K d₀).toFiniteSpanningSetsIn)).isCountablySpanning
  · let base := (Measure.pi (fun _ : Fin n => Q)).prod
        (Measure.pi (fun _ : Fin n => (K d₀)))
    let hbase := (Measure.FiniteSpanningSetsIn.pi
        (fun _ : Fin n => Q.toFiniteSpanningSetsIn)).prod
      (Measure.FiniteSpanningSetsIn.pi
        (fun _ : Fin n => (K d₀).toFiniteSpanningSetsIn))
    exact ⟨hbase.set, hbase.set_mem, fun i => measure_lt_top _ _, hbase.spanning⟩
  · rintro _ ⟨s, ⟨s, hs, rfl⟩, ⟨_, ⟨t, ht, rfl⟩, rfl⟩⟩
    have hs' : ∀ i, MeasurableSet (s i) := fun i => hs i (Set.mem_univ i)
    have ht' : ∀ i, MeasurableSet (t i) := fun i => ht i (Set.mem_univ i)
    have hdesignSet : MeasurableSet (Set.univ.pi s) :=
      MeasurableSet.pi Set.finite_univ.countable (fun i _ => hs' i)
    have hmarkSet : MeasurableSet (Set.univ.pi t) :=
      MeasurableSet.pi Set.finite_univ.countable (fun i _ => ht' i)
    simp only [lhs, rhs]
    rw [Measure.map_apply split.measurable (hdesignSet.prod hmarkSet)]
    rw [show split ⁻¹' (Set.univ.pi s ×ˢ Set.univ.pi t) =
        Set.univ.pi (fun i => s i ×ˢ t i) by
      ext x
      simp only [split, MeasurableEquiv.arrowProdEquivProdArrow,
        MeasurableEquiv.coe_mk, Set.mem_preimage, Set.mem_prod, Set.mem_pi,
        Set.mem_univ, true_implies, Equiv.arrowProdEquivProdArrow_apply, forall_and]]
    rw [Measure.pi_pi, Measure.compProd_apply_prod hdesignSet hmarkSet]
    simp_rw [pairLaw, Measure.compProd_apply_prod (hs' _) (ht' _)]
    simp only [markKernel]
    simp_rw [Causalean.Stat.finProductKernel_apply, Measure.pi_pi]
    let X : Fin n → (Fin n → D) → ENNReal := fun i d =>
      Set.indicator (s i) (fun x => K x (t i)) (d i)
    have hXmeas : ∀ i, Measurable (X i) := fun i =>
      ((K.measurable_coe (ht' i)).indicator (hs' i)).comp (measurable_pi_apply i)
    have hXindep : iIndepFun X designLaw := by
      have heval : iIndepFun (fun i (d : Fin n → D) => d i) designLaw := by
        simpa only [designLaw, id_eq] using
          (iIndepFun_pi (X := fun _ => id) (fun _ => measurable_id.aemeasurable))
      change iIndepFun (fun i =>
        (fun x => Set.indicator (s i) (fun z => K z (t i)) x) ∘
          fun d : Fin n → D => d i) designLaw
      exact heval.comp
        (fun i x => Set.indicator (s i) (fun z => K z (t i)) x)
        (fun i => (K.measurable_coe (ht' i)).indicator (hs' i))
    rw [← lintegral_indicator hdesignSet]
    change (∏ i, ∫⁻ x in s i, K x (t i) ∂Q) =
      ∫⁻ d, Set.indicator (Set.univ.pi s)
        (fun d => ∏ i, K (d i) (t i)) d ∂designLaw
    rw [show (fun d => Set.indicator (Set.univ.pi s)
          (fun d => ∏ i, K (d i) (t i)) d) =
        fun d => ∏ i, X i d by
      funext d
      by_cases hd : ∀ i, d i ∈ s i
      · rw [Set.indicator_of_mem (show d ∈ Set.univ.pi s from fun i _ => hd i)]
        exact Finset.prod_congr rfl fun i _ => by simp [X, hd i]
      · rw [Set.indicator_of_notMem (show d ∉ Set.univ.pi s by
          intro hmem
          exact hd fun i => hmem i (Set.mem_univ i))]
        push Not at hd
        obtain ⟨i, hi⟩ := hd
        symm
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [X, hi])]
    rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ X hXindep hXmeas]
    apply Finset.prod_congr rfl
    intro i _
    calc
      (∫⁻ x in s i, K x (t i) ∂Q) =
          ∫⁻ x, Set.indicator (s i) (fun z => K z (t i)) x ∂Q :=
        (lintegral_indicator (hs' i) _).symm
      _ = ∫⁻ d, X i d ∂designLaw :=
        ((measurePreserving_eval (fun _ : Fin n => Q) i).lintegral_comp
          ((K.measurable_coe (ht' i)).indicator (hs' i))).symm

/-- A [measurable joint event](hyp:hE) with [fibre probability at most a nonnegative
constant almost everywhere](hyp:hfibre,hA) under a [probability base and Markov
kernel](hyp:Q,K) has [attached-law probability at most that same constant](goal).

Rewrite `Measure.compProd_apply`, convert fibre real bounds to ENNReal bounds using
finiteness, and integrate the constant. This isolates measure plumbing from Bernstein.
-/
theorem compProd_real_le_of_fibre_real_le
    {D Y : Type*} [MeasurableSpace D] [MeasurableSpace Y]
    (Q : Measure D) [IsProbabilityMeasure Q]
    (K : Kernel D Y) [IsMarkovKernel K]
    {E : Set (D × Y)} (hE : MeasurableSet E) {A : ℝ} (hA : 0 ≤ A)
    (hfibre : ∀ᵐ d ∂Q, (K d).real (Prod.mk d ⁻¹' E) ≤ A) :
    (Q ⊗ₘ K).real E ≤ A := by
  have hfibreENN : ∀ᵐ d ∂Q, K d (Prod.mk d ⁻¹' E) ≤ ENNReal.ofReal A := by
    filter_upwards [hfibre] with d hd
    exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top (K d) _) hA).2 hd
  apply ENNReal.toReal_le_of_le_ofReal hA
  rw [Measure.compProd_apply hE]
  calc
    (∫⁻ d, K d (Prod.mk d ⁻¹' E) ∂Q) ≤ ∫⁻ _ : D, ENNReal.ofReal A ∂Q :=
      lintegral_mono_ae hfibreENN
    _ = ENNReal.ofReal A := by simp

end Causalean.Stat.Concentration.ConditionalBernstein
