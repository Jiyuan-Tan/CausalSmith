module
public import Causalean.Mathlib.Probability.Independence.Conditional.Transport
public import Causalean.Mathlib.Probability.Kernel.ThreeBernoulli.Marginal

/-!
# Conditional independence of the finite marks

The measurable-set identity works for an arbitrary measurable base space.
When the space is standard Borel, it is also exposed as Mathlib's the formal conditional-independence relation.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability.Independence.Conditional
open scoped ENNReal

noncomputable section

namespace Causalean.Mathlib.Probability.Kernel.ThreeBernoulli

universe u

/-- The [Bernoulli probability of a Boolean first mark set](goal) at
[first-mark probability `p`](hyp:p) for [the set `s`](hyp:s). -/
def firstMarkSetMass (p : ℝ) (s : Set Bool) : ℝ≥0∞ :=
  by classical exact ∑ a : Bool, if a ∈ s then ENNReal.ofReal (bitMass p a) else 0

/-- The [product Bernoulli probability of a remaining-mark-pair set](goal)
for [the two success probabilities](hyp:q₀,q₁) and [the set `t`](hyp:t). -/
def remainingPairSetMass (q₀ q₁ : ℝ) (t : Set (Bool × Bool)) : ℝ≥0∞ :=
  by
    classical
    exact ∑ y₀ : Bool, ∑ y₁ : Bool,
      if (y₀, y₁) ∈ t then
        ENNReal.ofReal (bitMass q₀ y₀ * bitMass q₁ y₁) else 0

/-- [The first mark and the remaining-mark pair are conditionally independent given
the base](goal): over [every measurable base set](hyp:B,hB) and
[all finite mark sets](hyp:s,t), their joint event has the integral of the
product of their conditional probabilities. Assumes a [probability base law](hyp:μ),
[measurable probabilities](hyp:he,hq₀,hq₁), and
[unit-interval bounds](hyp:he01,hq₀01,hq₁01). -/
theorem jointLaw_conditional_independent_finite {X : Type u} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (e q₀ q₁ : X → ℝ)
    (he : Measurable e) (hq₀ : Measurable q₀) (hq₁ : Measurable q₁)
    (he01 : ∀ x, e x ∈ Set.Icc (0 : ℝ) 1)
    (hq₀01 : ∀ x, q₀ x ∈ Set.Icc (0 : ℝ) 1)
    (hq₁01 : ∀ x, q₁ x ∈ Set.Icc (0 : ℝ) 1)
    (B : Set X) (hB : MeasurableSet B) (s : Set Bool) (t : Set (Bool × Bool)) :
    jointLaw μ e q₀ q₁
      {z : FullCoord X | z.1 ∈ B ∧ z.2.1 ∈ s ∧ z.2.2 ∈ t} =
    ∫⁻ x in B, firstMarkSetMass (e x) s * remainingPairSetMass (q₀ x) (q₁ x) t ∂μ := by
  classical
  let E : Set (DensityCoord X) :=
    {z | z.2.2 ∈ B ∧ z.1 ∈ s ∧ z.2.1 ∈ t}
  have hE : MeasurableSet E := by
    unfold E
    measurability
  have hF : MeasurableSet
      {z : FullCoord X | z.1 ∈ B ∧ z.2.1 ∈ s ∧ z.2.2 ∈ t} := by
    measurability
  have hbit (p : X → ℝ) (hp : Measurable p)
      (b : DensityCoord X → Bool) (hb : Measurable b) :
      Measurable (fun z : DensityCoord X => bitMass (p z.2.2) (b z)) := by
    unfold bitMass
    apply Measurable.ite
    · exact hb (MeasurableSet.singleton true)
    · exact hp.comp (by fun_prop)
    · exact measurable_const.sub (hp.comp (by fun_prop))
  have hd : Measurable (density e q₀ q₁) := by
    unfold density tripleMass
    exact ENNReal.measurable_ofReal.comp
      (((hbit e he (fun z => z.1) (by fun_prop)).mul
        (hbit q₀ hq₀ (fun z => z.2.1.1) (by fun_prop))).mul
        (hbit q₁ hq₁ (fun z => z.2.1.2) (by fun_prop)))
  rw [jointLaw, Measure.map_apply (by unfold toFull; fun_prop) hF]
  change densityLaw μ e q₀ q₁ E = _
  rw [densityLaw, withDensity_apply _ hE, ← lintegral_indicator hE]
  rw [reference, lintegral_prod_symm' _ (hd.indicator hE)]
  simp only [lintegral_count, tsum_fintype]
  rw [lintegral_prod_symm' _ (by fun_prop)]
  have hinner (x : X) :
      (∫⁻ z : Bool × Bool, ∑ a : Bool,
        E.indicator (density e q₀ q₁) (a, (z, x))
          ∂(Measure.count : Measure Bool).prod (Measure.count : Measure Bool)) =
        ∑ y₀ : Bool, ∑ y₁ : Bool, ∑ a : Bool,
          E.indicator (density e q₀ q₁) (a, ((y₀, y₁), x)) := by
    rw [lintegral_prod _ (by exact (measurable_of_finite _).aemeasurable)]
    simp only [lintegral_count, tsum_fintype]
  rw [← lintegral_indicator hB]
  apply lintegral_congr
  intro x
  rw [hinner]
  by_cases hx : x ∈ B
  · let A : Bool → ℝ≥0∞ := fun a => ENNReal.ofReal (bitMass (e x) a)
    let P : Bool → Bool → ℝ≥0∞ := fun y₀ y₁ =>
      ENNReal.ofReal (bitMass (q₀ x) y₀ * bitMass (q₁ x) y₁)
    have hterm (a y₀ y₁ : Bool) :
        E.indicator (density e q₀ q₁) (a, ((y₀, y₁), x)) =
          (if a ∈ s then A a else 0) *
            (if (y₀, y₁) ∈ t then P y₀ y₁ else 0) := by
      have hf : density e q₀ q₁ (a, ((y₀, y₁), x)) = A a * P y₀ y₁ := by
        unfold density tripleMass A P
        rw [mul_assoc, ENNReal.ofReal_mul (bitMass_nonneg _ (he01 x) _)]
      by_cases ha : a ∈ s <;> by_cases hp : (y₀, y₁) ∈ t <;>
        simp [Set.indicator, E, hx, ha, hp, hf]
    simp_rw [hterm]
    change (∑ y₀ : Bool, ∑ y₁ : Bool, ∑ a : Bool,
      (if a ∈ s then A a else 0) * (if (y₀, y₁) ∈ t then P y₀ y₁ else 0)) = _
    simp only [Set.indicator_of_mem hx]
    change (∑ y₀ : Bool, ∑ y₁ : Bool, ∑ a : Bool,
      (if a ∈ s then A a else 0) * (if (y₀, y₁) ∈ t then P y₀ y₁ else 0)) =
      (∑ a : Bool, if a ∈ s then A a else 0) *
        (∑ y₀ : Bool, ∑ y₁ : Bool, if (y₀, y₁) ∈ t then P y₀ y₁ else 0)
    simp only [Finset.mul_sum, Finset.sum_mul]
  · simp [Set.indicator, E, hx]

/-- [The first mark and the remaining-mark pair are conditionally independent
given bases in density coordinates](goal) when [the base space is
standard Borel](hyp:X), [the base law is a probability measure](hyp:μ),
[the mark probabilities are measurable](hyp:he,hq₀,hq₁), and
[they lie in `[0,1]`](hyp:he01,hq₀01,hq₁01). -/
theorem densityLaw_condIndepFun {X : Type u} [MeasurableSpace X]
    [StandardBorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (e q₀ q₁ : X → ℝ)
    (he : Measurable e) (hq₀ : Measurable q₀) (hq₁ : Measurable q₁)
    (he01 : ∀ x, e x ∈ Set.Icc (0 : ℝ) 1)
    (hq₀01 : ∀ x, q₀ x ∈ Set.Icc (0 : ℝ) 1)
    (hq₁01 : ∀ x, q₁ x ∈ Set.Icc (0 : ℝ) 1) :
    letI : IsProbabilityMeasure (densityLaw μ e q₀ q₁) :=
      densityLaw_probability μ e q₀ q₁ he hq₀ hq₁ he01 hq₀01 hq₁01
    CondIndepFun
      (MeasurableSpace.comap (fun z : DensityCoord X => z.2.2) inferInstance)
      ((measurable_snd.comp measurable_snd :
        Measurable (fun z : DensityCoord X => z.2.2)).comap_le)
      (fun z : DensityCoord X => z.1)
      (fun z : DensityCoord X => z.2.1)
      (densityLaw μ e q₀ q₁) := by
  letI : IsProbabilityMeasure (densityLaw μ e q₀ q₁) :=
    densityLaw_probability μ e q₀ q₁ he hq₀ hq₁ he01 hq₀01 hq₁01
  have hbit (p : X → ℝ) (hp : Measurable p)
      (b : DensityCoord X → Bool) (hb : Measurable b) :
      Measurable (fun z : DensityCoord X => bitMass (p z.2.2) (b z)) := by
    unfold bitMass
    apply Measurable.ite
    · exact hb (MeasurableSet.singleton true)
    · exact hp.comp (by fun_prop)
    · exact measurable_const.sub (hp.comp (by fun_prop))
  have hd : Measurable (density e q₀ q₁) := by
    unfold density tripleMass
    exact ENNReal.measurable_ofReal.comp
      (((hbit e he (fun z => z.1) (by fun_prop)).mul
        (hbit q₀ hq₀ (fun z => z.2.1.1) (by fun_prop))).mul
        (hbit q₁ hq₁ (fun z => z.2.1.2) (by fun_prop)))
  have ha : Measurable (fun z : Bool × X => ENNReal.ofReal (bitMass (e z.2) z.1)) := by
    unfold bitMass
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.ite
    · exact measurable_fst (MeasurableSet.singleton true)
    · exact he.comp measurable_snd
    · exact measurable_const.sub (he.comp measurable_snd)
  have hb : Measurable (fun z : (Bool × Bool) × X =>
      ENNReal.ofReal (bitMass (q₀ z.2) z.1.1 * bitMass (q₁ z.2) z.1.2)) := by
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.mul
    · unfold bitMass
      apply Measurable.ite
      · exact (measurable_fst.comp measurable_fst) (MeasurableSet.singleton true)
      · exact hq₀.comp measurable_snd
      · exact measurable_const.sub (hq₀.comp measurable_snd)
    · unfold bitMass
      apply Measurable.ite
      · exact (measurable_snd.comp measurable_fst) (MeasurableSet.singleton true)
      · exact hq₁.comp measurable_snd
      · exact measurable_const.sub (hq₁.comp measurable_snd)
  have hfactor : density e q₀ q₁ =ᵐ[reference μ]
      (fun z => ENNReal.ofReal (bitMass (e z.2.2) z.1) *
        ENNReal.ofReal (bitMass (q₀ z.2.2) z.2.1.1 *
          bitMass (q₁ z.2.2) z.2.1.2)) := by
    filter_upwards [] with z
    unfold density tripleMass
    rw [mul_assoc]
    rw [ENNReal.ofReal_mul (bitMass_nonneg _ (he01 _) _)]
  letI : IsFiniteMeasure ((Measure.count : Measure Bool).prod
      (((Measure.count : Measure Bool).prod (Measure.count : Measure Bool)).prod μ) |>.withDensity
        (density e q₀ q₁)) := by
    change IsFiniteMeasure (densityLaw μ e q₀ q₁)
    infer_instance
  exact condIndepFun_threeBlock_of_density_factors
    (Measure.count : Measure Bool)
    ((Measure.count : Measure Bool).prod (Measure.count : Measure Bool)) μ
    hd _ _ ha hb hfactor

/-- [The first mark and the remaining-mark pair are the formal conditional-independence relation given the
base in the public joint law](goal) for [standard Borel bases](hyp:X),
a [probability base law](hyp:μ), [measurable mark probabilities](hyp:he,hq₀,hq₁),
and [unit-interval bounds](hyp:he01,hq₀01,hq₁01). -/
theorem jointLaw_condIndepFun {X : Type u} [MeasurableSpace X]
    [StandardBorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (e q₀ q₁ : X → ℝ)
    (he : Measurable e) (hq₀ : Measurable q₀) (hq₁ : Measurable q₁)
    (he01 : ∀ x, e x ∈ Set.Icc (0 : ℝ) 1)
    (hq₀01 : ∀ x, q₀ x ∈ Set.Icc (0 : ℝ) 1)
    (hq₁01 : ∀ x, q₁ x ∈ Set.Icc (0 : ℝ) 1) :
    letI : IsProbabilityMeasure (jointLaw μ e q₀ q₁) :=
      jointLaw_probability μ e q₀ q₁ he hq₀ hq₁ he01 hq₀01 hq₁01
    CondIndepFun
      (MeasurableSpace.comap (fun z : FullCoord X => z.1) inferInstance)
      ((measurable_fst : Measurable (fun z : FullCoord X => z.1)).comap_le)
      (fun z : FullCoord X => z.2.1)
      (fun z : FullCoord X => z.2.2)
      (jointLaw μ e q₀ q₁) := by
  letI : IsProbabilityMeasure (densityLaw μ e q₀ q₁) :=
    densityLaw_probability μ e q₀ q₁ he hq₀ hq₁ he01 hq₀01 hq₁01
  letI : IsProbabilityMeasure (jointLaw μ e q₀ q₁) :=
    jointLaw_probability μ e q₀ q₁ he hq₀ hq₁ he01 hq₀01 hq₁01
  change CondIndepFun
    (MeasurableSpace.comap (fun z : FullCoord X => z.1) inferInstance)
    ((measurable_fst : Measurable (fun z : FullCoord X => z.1)).comap_le)
    (fun z : FullCoord X => z.2.1) (fun z : FullCoord X => z.2.2)
    ((densityLaw μ e q₀ q₁).map toFull)
  apply condIndepFun_of_map (φ := toFull) (by unfold toFull; fun_prop)
    (by fun_prop) (by fun_prop) (by fun_prop)
  change CondIndepFun
    (MeasurableSpace.comap (fun z : DensityCoord X => z.2.2) inferInstance)
    ((measurable_snd.comp measurable_snd :
      Measurable (fun z : DensityCoord X => z.2.2)).comap_le)
    (fun z : DensityCoord X => z.1)
    (fun z : DensityCoord X => z.2.1) (densityLaw μ e q₀ q₁)
  exact densityLaw_condIndepFun μ e q₀ q₁ he hq₀ hq₁ he01 hq₀01 hq₁01

end Causalean.Mathlib.Probability.Kernel.ThreeBernoulli
