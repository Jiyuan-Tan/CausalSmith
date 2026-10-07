module
public import Causalean.Mathlib.Probability.Independence.Conditional.ThreeBlockDensity
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Three Bernoulli marks over an arbitrary base law

The density coordinates put first mark and the remaining-mark pair before the
base. This lets the finite counting-measure construction feed the existing
three-block conditional-independence theorem when the base is standard Borel.
The public joint coordinates are `(x, (a, (y₀, y₁)))`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace Causalean.Mathlib.Probability.Kernel.ThreeBernoulli

universe u

/-- The mass of [a Boolean Bernoulli mark](goal) with [success probability `p`](hyp:p)
at [the specified Boolean value](hyp:b). -/
def bitMass (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

/-- The [selected cell mass](goal) at [first mark `a`](hyp:a) and
[selected value `y`](hyp:y), from [first-mark probability](hyp:p) and [the two remaining-mark
probabilities](hyp:q₀,q₁): the Bernoulli mass of the first mark at `a` times the Bernoulli
mass at `y` of the mark that `a` selects, whose success probability is `q₁` when `a` is true
and `q₀` when `a` is false. -/
def cellMass (p q₀ q₁ : ℝ) (a y : Bool) : ℝ :=
  bitMass p a * bitMass (if a then q₁ else q₀) y

/-- The [product mass of three independent Bernoulli marks](goal) at [the specified
triple](hyp:a,y₀,y₁), with [their three success probabilities](hyp:p,q₀,q₁). -/
def tripleMass (p q₀ q₁ : ℝ) (a y₀ y₁ : Bool) : ℝ :=
  bitMass p a * bitMass q₀ y₀ * bitMass q₁ y₁

/-- [Coordinates for the finite-count density](goal) consist of first mark, the pair of
remaining marks, and the base [space](hyp:X). -/
abbrev DensityCoord (X : Type u) := Bool × ((Bool × Bool) × X)

/-- [Coordinates for the public three-mark law](goal) consist of the base
[space](hyp:X), first mark, and both remaining marks. -/
abbrev FullCoord (X : Type u) := X × (Bool × (Bool × Bool))

/-- [Coordinates for the selected-mark law](goal) consist of the base
[space](hyp:X), first mark, and the realized selected value. -/
abbrev SelectedCoord (X : Type u) := X × (Bool × Bool)

/-- The [finite-count reference measure](goal) combines counting measures on three
Boolean marks with [a base measure](hyp:μ). -/
def reference {X : Type u} [MeasurableSpace X] (μ : Measure X) :
    Measure (DensityCoord X) :=
  (Measure.count : Measure Bool).prod
    (((Measure.count : Measure Bool).prod (Measure.count : Measure Bool)).prod μ)

/-- The [product Bernoulli density](goal) at [one three-mark point](hyp:z) uses
[three base-dependent mark probabilities](hyp:e,q₀,q₁): it is the product of the three
Bernoulli masses of the point's marks, evaluated at the point's base value and read as an
extended nonnegative number (a negative product, possible only when a probability leaves
the unit interval, is replaced by zero). -/
def density {X : Type u} (e q₀ q₁ : X → ℝ) (z : DensityCoord X) : ℝ≥0∞ :=
  ENNReal.ofReal (tripleMass (e z.2.2) (q₀ z.2.2) (q₁ z.2.2)
    z.1 z.2.1.1 z.2.1.2)

/-- The [three-mark measure in density coordinates](goal) is the product-counting
reference [measure](hyp:μ) weighted by the [three Bernoulli probabilities](hyp:e,q₀,q₁). -/
def densityLaw {X : Type u} [MeasurableSpace X] (μ : Measure X)
    (e q₀ q₁ : X → ℝ) : Measure (DensityCoord X) :=
  (reference μ).withDensity (density e q₀ q₁)

/-- The [reordering to base-first three-mark coordinates](goal) sends
[density coordinates](hyp:z) to `(x,a,y₀,y₁)`. -/
def toFull {X : Type u} (z : DensityCoord X) : FullCoord X :=
  (z.2.2, (z.1, z.2.1))

/-- The [joint law of base, first mark, and remaining marks](goal) is the
reordered [finite-count Bernoulli density law](hyp:μ,e,q₀,q₁). -/
def jointLaw {X : Type u} [MeasurableSpace X] (μ : Measure X)
    (e q₀ q₁ : X → ℝ) : Measure (FullCoord X) :=
  (densityLaw μ e q₀ q₁).map toFull

/-- [Both Bernoulli masses are nonnegative](goal) when [the probability lies in
`[0,1]`](hyp:hp). -/
theorem bitMass_nonneg (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) (b : Bool) :
    0 ≤ bitMass p b := by
  cases b <;> simp [bitMass, hp.1, sub_nonneg.mpr hp.2]

/-- [The two Bernoulli masses sum to one](goal) for [any real parameter](hyp:p). -/
theorem bitMass_sum (p : ℝ) : bitMass p false + bitMass p true = 1 := by
  simp [bitMass]

/-- [The eight product Bernoulli masses sum to one](goal) for [any three real
parameters](hyp:p,q₀,q₁). -/
theorem tripleMass_sum (p q₀ q₁ : ℝ) :
    (∑ a : Bool, ∑ y₀ : Bool, ∑ y₁ : Bool,
      tripleMass p q₀ q₁ a y₀ y₁) = 1 := by
  simp [tripleMass, bitMass]
  ring

/-- Summing the latent remaining marks whose selected selected value is `y` gives
the selected cell cell mass. -/
theorem tripleMass_selected_sum (p q₀ q₁ : ℝ) (a y : Bool) :
    (∑ y₀ : Bool, ∑ y₁ : Bool,
      if (if a then y₁ else y₀) = y then tripleMass p q₀ q₁ a y₀ y₁ else 0) =
      cellMass p q₀ q₁ a y := by
  cases a <;> cases y <;>
    simp [tripleMass, cellMass, bitMass] <;> ring

/-- [The finite-count density law is a probability measure](goal) for a
[probability base measure](hyp:μ), [measurable mark probabilities](hyp:he,hq₀,hq₁),
and [pointwise unit-interval bounds](hyp:he01,hq₀01,hq₁01). -/
theorem densityLaw_probability {X : Type u} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (e q₀ q₁ : X → ℝ)
    (he : Measurable e) (hq₀ : Measurable q₀) (hq₁ : Measurable q₁)
    (he01 : ∀ x, e x ∈ Set.Icc (0 : ℝ) 1)
    (hq₀01 : ∀ x, q₀ x ∈ Set.Icc (0 : ℝ) 1)
    (hq₁01 : ∀ x, q₁ x ∈ Set.Icc (0 : ℝ) 1) :
    IsProbabilityMeasure (densityLaw μ e q₀ q₁) := by
  -- Expand `withDensity_apply'` on `univ`, use Tonelli on the three finite
  -- counting factors, and rewrite the innermost sum by `tripleMass_sum`.
  -- Pointwise bounds turn `ofReal` of each product into a nonnegative real cast.
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
  have hn (x : X) (a y₀ y₁ : Bool) :
      0 ≤ tripleMass (e x) (q₀ x) (q₁ x) a y₀ y₁ := by
    unfold tripleMass
    exact mul_nonneg (mul_nonneg (bitMass_nonneg _ (he01 x) _)
      (bitMass_nonneg _ (hq₀01 x) _)) (bitMass_nonneg _ (hq₁01 x) _)
  have hsum (x : X) :
      (∑ a : Bool, ∑ y₀ : Bool, ∑ y₁ : Bool,
        density e q₀ q₁ (a, ((y₀, y₁), x))) = 1 := by
    simp only [density]
    calc
      (∑ a : Bool, ∑ y₀ : Bool, ∑ y₁ : Bool,
          ENNReal.ofReal (tripleMass (e x) (q₀ x) (q₁ x) a y₀ y₁))
          = ∑ a : Bool, ∑ y₀ : Bool,
              ENNReal.ofReal (∑ y₁ : Bool, tripleMass (e x) (q₀ x) (q₁ x) a y₀ y₁) := by
            apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro y₀ _
            exact (ENNReal.ofReal_sum_of_nonneg (fun y₁ _ => hn x a y₀ y₁)).symm
      _ = ∑ a : Bool, ENNReal.ofReal
            (∑ y₀ : Bool, ∑ y₁ : Bool, tripleMass (e x) (q₀ x) (q₁ x) a y₀ y₁) := by
          apply Finset.sum_congr rfl
          intro a _
          exact (ENNReal.ofReal_sum_of_nonneg (fun y₀ _ =>
            Finset.sum_nonneg fun y₁ _ => hn x a y₀ y₁)).symm
      _ = ENNReal.ofReal (∑ a : Bool, ∑ y₀ : Bool, ∑ y₁ : Bool,
            tripleMass (e x) (q₀ x) (q₁ x) a y₀ y₁) := by
          exact (ENNReal.ofReal_sum_of_nonneg (fun a _ =>
            Finset.sum_nonneg fun y₀ _ => Finset.sum_nonneg fun y₁ _ =>
              hn x a y₀ y₁)).symm
      _ = 1 := by rw [tripleMass_sum]; norm_num
  refine ⟨?_⟩
  rw [densityLaw, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  rw [reference, lintegral_prod_symm' _ hd]
  simp only [lintegral_count, tsum_fintype]
  rw [lintegral_prod_symm' _ (by fun_prop)]
  have hinner (x : X) :
      (∫⁻ z : Bool × Bool, ∑ a : Bool, density e q₀ q₁ (a, (z, x))
          ∂(Measure.count : Measure Bool).prod (Measure.count : Measure Bool)) =
        ∑ y₀ : Bool, ∑ y₁ : Bool, ∑ a : Bool,
          density e q₀ q₁ (a, ((y₀, y₁), x)) := by
    rw [lintegral_prod _ (by exact (measurable_of_finite _).aemeasurable)]
    simp only [lintegral_count, tsum_fintype]
  have hsum' (x : X) :
      (∑ y₀ : Bool, ∑ y₁ : Bool, ∑ a : Bool,
        density e q₀ q₁ (a, ((y₀, y₁), x))) = 1 := by
    calc
      _ = ∑ a : Bool, ∑ y₀ : Bool, ∑ y₁ : Bool,
            density e q₀ q₁ (a, ((y₀, y₁), x)) := by
          simp only [Fintype.sum_bool]
          ac_rfl
      _ = 1 := hsum x
  calc
    _ = ∫⁻ x, (∑ y₀ : Bool, ∑ y₁ : Bool, ∑ a : Bool,
          density e q₀ q₁ (a, ((y₀, y₁), x))) ∂μ := by
        apply lintegral_congr
        intro x
        exact hinner x
    _ = ∫⁻ _ : X, (1 : ℝ≥0∞) ∂μ := by
        apply lintegral_congr
        intro x
        exact hsum' x
    _ = 1 := by simp

/-- [The base-first joint law is a probability measure](goal) under a
[probability base law](hyp:μ), [measurable mark probabilities](hyp:he,hq₀,hq₁),
and [unit-interval bounds](hyp:he01,hq₀01,hq₁01). -/
theorem jointLaw_probability {X : Type u} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (e q₀ q₁ : X → ℝ)
    (he : Measurable e) (hq₀ : Measurable q₀) (hq₁ : Measurable q₁)
    (he01 : ∀ x, e x ∈ Set.Icc (0 : ℝ) 1)
    (hq₀01 : ∀ x, q₀ x ∈ Set.Icc (0 : ℝ) 1)
    (hq₁01 : ∀ x, q₁ x ∈ Set.Icc (0 : ℝ) 1) :
    IsProbabilityMeasure (jointLaw μ e q₀ q₁) := by
  -- Transport `densityLaw_probability` through measurable `toFull` and
  -- simplify the measure of `univ` under `Measure.map`.
  haveI : IsProbabilityMeasure (densityLaw μ e q₀ q₁) :=
    densityLaw_probability μ e q₀ q₁ he hq₀ hq₁ he01 hq₀01 hq₁01
  exact Measure.isProbabilityMeasure_map (by
    unfold toFull
    fun_prop)

end Causalean.Mathlib.Probability.Kernel.ThreeBernoulli
