module
public import Causalean.Mathlib.Probability.Kernel.ThreeBernoulli.Independence

/-!
# Selected Bernoulli cells

The selected law is an independent four-cell density over first mark and the
realized selected value. Its equality with the three-mark observation pushforward and
the four measurable base-cell integrals are stated here.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace Causalean.Mathlib.Probability.Kernel.ThreeBernoulli

universe u

/-- The [selected observation of a three-mark point](goal) retains the base and first
mark of [that point](hyp:z) and keeps only the remaining mark that the first mark selects:
the second remaining mark when the first mark is true, the first remaining mark when it
is false. -/
def selectMark {X : Type u} (z : FullCoord X) : SelectedCoord X :=
  (z.1, (z.2.1, if z.2.1 then z.2.2.2 else z.2.2.1))

/-- The [selected four-cell density](goal) at [a cell (first mark, selected value) and
base value](hyp:z) uses [first-mark probability and remaining-mark probabilities](hyp:e,q₀,q₁):
it is the selected cell mass of that cell at that base value, read as an extended
nonnegative number (a negative value is replaced by zero). -/
def selectedDensity {X : Type u} (e q₀ q₁ : X → ℝ)
    (z : (Bool × Bool) × X) : ℝ≥0∞ :=
  ENNReal.ofReal (cellMass (e z.2) (q₀ z.2) (q₁ z.2) z.1.1 z.1.2)

/-- The [explicit selected four-cell law](goal) weights the product of counting measure
on the four cells and the [base measure](hyp:μ) by the [selected cell
probabilities](hyp:e,q₀,q₁), then reorders coordinates to put the base first. -/
def selectedLaw {X : Type u} [MeasurableSpace X] (μ : Measure X)
    (e q₀ q₁ : X → ℝ) : Measure (SelectedCoord X) :=
  (((Measure.count : Measure Bool).prod (Measure.count : Measure Bool)).prod μ).withDensity
    (selectedDensity e q₀ q₁) |>.map (fun z => (z.2, z.1))

/-- [The pushforward of the three-mark law under observation is the explicit
four-cell selected law](goal) for [a probability base measure](hyp:μ),
[measurable mark probabilities](hyp:he,hq₀,hq₁), and
[unit-interval bounds](hyp:he01,hq₀01,hq₁01). -/
theorem jointLaw_selectMark_map {X : Type u} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (e q₀ q₁ : X → ℝ)
    (he : Measurable e) (hq₀ : Measurable q₀) (hq₁ : Measurable q₁)
    (he01 : ∀ x, e x ∈ Set.Icc (0 : ℝ) 1)
    (hq₀01 : ∀ x, q₀ x ∈ Set.Icc (0 : ℝ) 1)
    (hq₁01 : ∀ x, q₁ x ∈ Set.Icc (0 : ℝ) 1) :
    (jointLaw μ e q₀ q₁).map selectMark = selectedLaw μ e q₀ q₁ := by
  classical
  have hTo : Measurable (toFull (X := X)) := by
    unfold toFull
    fun_prop
  have hObs : Measurable (selectMark (X := X)) := by
    unfold selectMark
    apply Measurable.prodMk
    · fun_prop
    · apply Measurable.prodMk
      · fun_prop
      · apply Measurable.ite
        · measurability
        · fun_prop
        · fun_prop
  have hComp : Measurable (selectMark ∘ toFull : DensityCoord X → SelectedCoord X) :=
    hObs.comp hTo
  apply Measure.ext
  intro S hS
  let E : Set (DensityCoord X) :=
    {z | (z.2.2, (z.1, if z.1 then z.2.1.2 else z.2.1.1)) ∈ S}
  let F : Set ((Bool × Bool) × X) := {z | (z.2, z.1) ∈ S}
  have hE : MeasurableSet E := by
    unfold E
    exact hS.preimage hComp
  have hF : MeasurableSet F := by
    unfold F
    exact hS.preimage (by fun_prop)
  have hd : Measurable (density e q₀ q₁) := by
    have hbit (p : X → ℝ) (hp : Measurable p)
        (b : DensityCoord X → Bool) (hb : Measurable b) :
        Measurable (fun z : DensityCoord X => bitMass (p z.2.2) (b z)) := by
      unfold bitMass
      apply Measurable.ite
      · exact hb (MeasurableSet.singleton true)
      · exact hp.comp (by fun_prop)
      · exact measurable_const.sub (hp.comp (by fun_prop))
    unfold density tripleMass
    exact ENNReal.measurable_ofReal.comp
      (((hbit e he (fun z => z.1) (by fun_prop)).mul
        (hbit q₀ hq₀ (fun z => z.2.1.1) (by fun_prop))).mul
        (hbit q₁ hq₁ (fun z => z.2.1.2) (by fun_prop)))
  have hD : Measurable (selectedDensity e q₀ q₁) := by
    unfold selectedDensity cellMass bitMass
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.mul
    · apply Measurable.ite
      · measurability
      · exact he.comp (by fun_prop)
      · exact measurable_const.sub (he.comp (by fun_prop))
    · apply Measurable.ite
      · measurability
      · apply Measurable.ite
        · measurability
        · exact hq₁.comp (by fun_prop)
        · exact hq₀.comp (by fun_prop)
      · exact measurable_const.sub (by
          apply Measurable.ite
          · measurability
          · exact hq₁.comp (by fun_prop)
          · exact hq₀.comp (by fun_prop))
  rw [jointLaw, Measure.map_map hObs hTo]
  rw [Measure.map_apply hComp hS]
  change densityLaw μ e q₀ q₁ E = _
  rw [selectedLaw, Measure.map_apply (by fun_prop) hS]
  change densityLaw μ e q₀ q₁ E =
    (((Measure.count : Measure Bool).prod (Measure.count : Measure Bool)).prod μ).withDensity
      (selectedDensity e q₀ q₁) F
  rw [densityLaw, withDensity_apply _ hE, ← lintegral_indicator hE]
  rw [withDensity_apply _ hF, ← lintegral_indicator hF]
  rw [reference, lintegral_prod_symm' _ (hd.indicator hE)]
  simp only [lintegral_count, tsum_fintype]
  conv_lhs => rw [lintegral_prod_symm' _ (by fun_prop)]
  conv_rhs => rw [lintegral_prod_symm' _ (hD.indicator hF)]
  have hleft (x : X) :
      (∫⁻ z : Bool × Bool, ∑ a : Bool, E.indicator (density e q₀ q₁) (a, (z, x))
          ∂(Measure.count : Measure Bool).prod (Measure.count : Measure Bool)) =
        ∑ y₀ : Bool, ∑ y₁ : Bool, ∑ a : Bool,
          E.indicator (density e q₀ q₁) (a, ((y₀, y₁), x)) := by
    rw [lintegral_prod _ (by exact (measurable_of_finite _).aemeasurable)]
    simp only [lintegral_count, tsum_fintype]
  have hright (x : X) :
      (∫⁻ z : Bool × Bool, F.indicator (selectedDensity e q₀ q₁) (z, x)
          ∂(Measure.count : Measure Bool).prod (Measure.count : Measure Bool)) =
        ∑ a : Bool, ∑ y : Bool,
          F.indicator (selectedDensity e q₀ q₁) ((a, y), x) := by
    rw [lintegral_prod _ (by exact (measurable_of_finite _).aemeasurable)]
    simp only [lintegral_count, tsum_fintype]
  have hnonneg (x : X) (a y₀ y₁ : Bool) :
      0 ≤ tripleMass (e x) (q₀ x) (q₁ x) a y₀ y₁ := by
    unfold tripleMass
    exact mul_nonneg (mul_nonneg (bitMass_nonneg _ (he01 x) _)
      (bitMass_nonneg _ (hq₀01 x) _)) (bitMass_nonneg _ (hq₁01 x) _)
  have hcollapse (x : X) (a y : Bool) :
      (∑ y₀ : Bool, ∑ y₁ : Bool,
        if (if a then y₁ else y₀) = y then
          density e q₀ q₁ (a, ((y₀, y₁), x)) else 0) =
        selectedDensity e q₀ q₁ ((a, y), x) := by
    have hterm (y₀ y₁ : Bool) :
        (if (if a then y₁ else y₀) = y then
          density e q₀ q₁ (a, ((y₀, y₁), x)) else 0) =
        ENNReal.ofReal (if (if a then y₁ else y₀) = y then
          tripleMass (e x) (q₀ x) (q₁ x) a y₀ y₁ else 0) := by
      split_ifs <;> simp [density]
    simp_rw [hterm]
    calc
      (∑ y₀ : Bool, ∑ y₁ : Bool,
        ENNReal.ofReal (if (if a then y₁ else y₀) = y then
          tripleMass (e x) (q₀ x) (q₁ x) a y₀ y₁ else 0)) =
        ∑ y₀ : Bool, ENNReal.ofReal (∑ y₁ : Bool,
          if (if a then y₁ else y₀) = y then
            tripleMass (e x) (q₀ x) (q₁ x) a y₀ y₁ else 0) := by
        apply Finset.sum_congr rfl
        intro y₀ _
        exact (ENNReal.ofReal_sum_of_nonneg (fun y₁ _ => by
          split_ifs <;> first | exact hnonneg x a y₀ y₁ | exact le_rfl)).symm
      _ = ENNReal.ofReal (∑ y₀ : Bool, ∑ y₁ : Bool,
          if (if a then y₁ else y₀) = y then
            tripleMass (e x) (q₀ x) (q₁ x) a y₀ y₁ else 0) := by
        exact (ENNReal.ofReal_sum_of_nonneg (fun y₀ _ =>
          Finset.sum_nonneg fun y₁ _ => by
            split_ifs <;> first | exact hnonneg x a y₀ y₁ | exact le_rfl)).symm
      _ = selectedDensity e q₀ q₁ ((a, y), x) := by
        rw [tripleMass_selected_sum]
        rfl
  apply lintegral_congr
  intro x
  rw [hleft x, hright x]
  calc
    (∑ y₀ : Bool, ∑ y₁ : Bool, ∑ a : Bool,
        E.indicator (density e q₀ q₁) (a, ((y₀, y₁), x))) =
      ∑ a : Bool, ∑ y₀ : Bool, ∑ y₁ : Bool,
        E.indicator (density e q₀ q₁) (a, ((y₀, y₁), x)) := by
      simp only [Fintype.sum_bool]
      ac_rfl
    _ = ∑ a : Bool, ∑ y : Bool,
        if (x, (a, y)) ∈ S then selectedDensity e q₀ q₁ ((a, y), x) else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      simp only [Fintype.sum_bool]
      rw [← hcollapse x a false, ← hcollapse x a true]
      cases a
      · by_cases h0 : (x, (false, false)) ∈ S <;>
          by_cases h1 : (x, (false, true)) ∈ S <;>
          simp [E, Set.indicator, h0, h1]
      · by_cases h0 : (x, (true, false)) ∈ S <;>
          by_cases h1 : (x, (true, true)) ∈ S <;>
          simp [E, Set.indicator, h0, h1] <;> ac_rfl
    _ = ∑ a : Bool, ∑ y : Bool,
        F.indicator (selectedDensity e q₀ q₁) ((a, y), x) := by
      simp [F, Set.indicator]

/-- [The explicit selected law is a probability measure](goal) for a
[probability base law](hyp:μ), [measurable mark probabilities](hyp:he,hq₀,hq₁),
and [unit-interval bounds](hyp:he01,hq₀01,hq₁01). -/
theorem selectedLaw_probability {X : Type u} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (e q₀ q₁ : X → ℝ)
    (he : Measurable e) (hq₀ : Measurable q₀) (hq₁ : Measurable q₁)
    (he01 : ∀ x, e x ∈ Set.Icc (0 : ℝ) 1)
    (hq₀01 : ∀ x, q₀ x ∈ Set.Icc (0 : ℝ) 1)
    (hq₁01 : ∀ x, q₁ x ∈ Set.Icc (0 : ℝ) 1) :
    IsProbabilityMeasure (selectedLaw μ e q₀ q₁) := by
  rw [← jointLaw_selectMark_map μ e q₀ q₁ he hq₀ hq₁ he01 hq₀01 hq₁01]
  letI : IsProbabilityMeasure (jointLaw μ e q₀ q₁) :=
    jointLaw_probability μ e q₀ q₁ he hq₀ hq₁ he01 hq₀01 hq₁01
  have hObs : Measurable (selectMark (X := X)) := by
    unfold selectMark
    apply Measurable.prodMk
    · fun_prop
    · apply Measurable.prodMk
      · fun_prop
      · apply Measurable.ite
        · measurability
        · fun_prop
        · fun_prop
  exact Measure.isProbabilityMeasure_map hObs.aemeasurable

/-- [An selected cell cell over a measurable base set has
the integral of its Bernoulli cell mass](goal), for [a base law](hyp:μ),
[measurable mark probabilities](hyp:he,hq₀,hq₁), [a measurable base set](hyp:B,hB),
and [the specified cell](hyp:a,y). -/
theorem selectedLaw_cell {X : Type u} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (e q₀ q₁ : X → ℝ)
    (he : Measurable e) (hq₀ : Measurable q₀) (hq₁ : Measurable q₁)
    (B : Set X) (hB : MeasurableSet B) (a y : Bool) :
    selectedLaw μ e q₀ q₁
      {z : SelectedCoord X | z.1 ∈ B ∧ z.2.1 = a ∧ z.2.2 = y} =
    ∫⁻ x in B, ENNReal.ofReal (cellMass (e x) (q₀ x) (q₁ x) a y) ∂μ := by
  classical
  let E : Set ((Bool × Bool) × X) :=
    {z | z.2 ∈ B ∧ z.1.1 = a ∧ z.1.2 = y}
  have hE : MeasurableSet E := by
    unfold E
    measurability
  have hF : MeasurableSet
      {z : SelectedCoord X | z.1 ∈ B ∧ z.2.1 = a ∧ z.2.2 = y} := by
    measurability
  have hd : Measurable (selectedDensity e q₀ q₁) := by
    unfold selectedDensity cellMass bitMass
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.mul
    · apply Measurable.ite
      · measurability
      · exact he.comp (by fun_prop)
      · exact measurable_const.sub (he.comp (by fun_prop))
    · apply Measurable.ite
      · measurability
      · apply Measurable.ite
        · measurability
        · exact hq₁.comp (by fun_prop)
        · exact hq₀.comp (by fun_prop)
      · exact measurable_const.sub (by
          apply Measurable.ite
          · measurability
          · exact hq₁.comp (by fun_prop)
          · exact hq₀.comp (by fun_prop))
  rw [selectedLaw, Measure.map_apply (by fun_prop) hF]
  change (((Measure.count : Measure Bool).prod (Measure.count : Measure Bool)).prod μ).withDensity
    (selectedDensity e q₀ q₁) E = _
  rw [withDensity_apply _ hE, ← lintegral_indicator hE]
  rw [lintegral_prod_symm' _ (hd.indicator hE)]
  have hinner (x : X) :
      (∫⁻ z : Bool × Bool, E.indicator (selectedDensity e q₀ q₁) (z, x)
          ∂(Measure.count : Measure Bool).prod (Measure.count : Measure Bool)) =
        ∑ a' : Bool, ∑ y' : Bool,
          E.indicator (selectedDensity e q₀ q₁) ((a', y'), x) := by
    rw [lintegral_prod _ (by exact (measurable_of_finite _).aemeasurable)]
    simp only [lintegral_count, tsum_fintype]
  rw [← lintegral_indicator hB]
  apply lintegral_congr
  intro x
  rw [hinner]
  by_cases hx : x ∈ B
  · cases a <;> cases y <;> simp [E, Set.indicator, hx, selectedDensity]
  · simp [E, Set.indicator, hx]

/-- [The untreated, selected-failure cell integral](goal) holds over
[a measurable base set](hyp:B,hB) under [a probability base law](hyp:μ),
and [measurable mark probabilities](hyp:he,hq₀,hq₁). -/
theorem selectedLaw_cell_00 {X : Type u} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (e q₀ q₁ : X → ℝ)
    (he : Measurable e) (hq₀ : Measurable q₀) (hq₁ : Measurable q₁)
    (B : Set X) (hB : MeasurableSet B) :
    selectedLaw μ e q₀ q₁
      {z : SelectedCoord X | z.1 ∈ B ∧ z.2.1 = false ∧ z.2.2 = false} =
    ∫⁻ x in B, ENNReal.ofReal ((1 - e x) * (1 - q₀ x)) ∂μ := by
  simpa [cellMass, bitMass] using
    selectedLaw_cell μ e q₀ q₁ he hq₀ hq₁ B hB false false

/-- [The untreated, selected-success cell integral](goal) holds over
[a measurable base set](hyp:B,hB) under [a probability base law](hyp:μ),
and [measurable mark probabilities](hyp:he,hq₀,hq₁). -/
theorem selectedLaw_cell_01 {X : Type u} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (e q₀ q₁ : X → ℝ)
    (he : Measurable e) (hq₀ : Measurable q₀) (hq₁ : Measurable q₁)
    (B : Set X) (hB : MeasurableSet B) :
    selectedLaw μ e q₀ q₁
      {z : SelectedCoord X | z.1 ∈ B ∧ z.2.1 = false ∧ z.2.2 = true} =
    ∫⁻ x in B, ENNReal.ofReal ((1 - e x) * q₀ x) ∂μ := by
  simpa [cellMass, bitMass] using
    selectedLaw_cell μ e q₀ q₁ he hq₀ hq₁ B hB false true

/-- [The treated, selected-failure cell integral](goal) holds over
[a measurable base set](hyp:B,hB) under [a probability base law](hyp:μ),
and [measurable mark probabilities](hyp:he,hq₀,hq₁). -/
theorem selectedLaw_cell_10 {X : Type u} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (e q₀ q₁ : X → ℝ)
    (he : Measurable e) (hq₀ : Measurable q₀) (hq₁ : Measurable q₁)
    (B : Set X) (hB : MeasurableSet B) :
    selectedLaw μ e q₀ q₁
      {z : SelectedCoord X | z.1 ∈ B ∧ z.2.1 = true ∧ z.2.2 = false} =
    ∫⁻ x in B, ENNReal.ofReal (e x * (1 - q₁ x)) ∂μ := by
  simpa [cellMass, bitMass] using
    selectedLaw_cell μ e q₀ q₁ he hq₀ hq₁ B hB true false

/-- [The treated, selected-success cell integral](goal) holds over
[a measurable base set](hyp:B,hB) under [a probability base law](hyp:μ),
and [measurable mark probabilities](hyp:he,hq₀,hq₁). -/
theorem selectedLaw_cell_11 {X : Type u} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (e q₀ q₁ : X → ℝ)
    (he : Measurable e) (hq₀ : Measurable q₀) (hq₁ : Measurable q₁)
    (B : Set X) (hB : MeasurableSet B) :
    selectedLaw μ e q₀ q₁
      {z : SelectedCoord X | z.1 ∈ B ∧ z.2.1 = true ∧ z.2.2 = true} =
    ∫⁻ x in B, ENNReal.ofReal (e x * q₁ x) ∂μ := by
  simpa [cellMass, bitMass] using
    selectedLaw_cell μ e q₀ q₁ he hq₀ hq₁ B hB true true

end Causalean.Mathlib.Probability.Kernel.ThreeBernoulli
