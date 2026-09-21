module
public import Mathlib.Logic.Function.DependsOn
public import Mathlib.MeasureTheory.Integral.Marginal
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Finite coordinate dependence and density marginalization

This module provides measure theory on dependent products indexed by a type, relative to a finite
set of coordinates.  It defines what it means for a function of an assignment to depend only on
those coordinates, the measurable restriction and extension maps between full and restricted
assignments, and the analytic bridge from equality of `lmarginal` densities to equality of the
projected `withDensity` measures.

The declarations live in the `FiniteCoordinate` sub-namespace so that opening
`Causalean.Mathlib.MeasureTheory` does not overload Mathlib's root `DependsOn` (which uses a
`Set` of coordinates and the opposite argument order).
-/

@[expose] public section

open scoped ENNReal
open Set Function
open MeasureTheory

noncomputable section

namespace Causalean.Mathlib.MeasureTheory.FiniteCoordinate

variable {V : Type*} [DecidableEq V]
variable {X : V → Type*} [∀ i, MeasurableSpace (X i)]

/-- A [finite coordinate set](hyp:S) and an [assignment-valued function](hyp:f) determine
[the property that the function is unchanged whenever two assignments agree on that set](goal). -/
abbrev DependsOn {Y : Type*} (S : Finset V) (f : (∀ i, X i) → Y) : Prop :=
  _root_.DependsOn f (S : Set V)

/-- A function [depending on a smaller coordinate set](hyp:hf) and [that set's inclusion in a
larger one](hyp:hST) [also depends only on the larger set](goal). -/
@[deprecated _root_.DependsOn.mono (since := "2026-09-15")]
theorem DependsOn.mono {Y : Type*} {S T : Finset V} {f : (∀ i, X i) → Y}
    (hf : DependsOn S f) (hST : S ⊆ T) : DependsOn T f :=
  _root_.DependsOn.mono (by simpa using hST) hf

/-- A [chosen coordinate](hyp:i) [can be read from an assignment using only that coordinate](goal). -/
theorem dependsOn_apply (i : V) :
    DependsOn (X := X) {i} (fun x : ∀ k, X k ↦ x i) :=
  fun _ _ hxy ↦ hxy i (by simp)

/-- Two functions [depending on the same coordinate set](hyp:hf,hg), combined through a [fixed
binary operation](hyp:op), [still depend only on that set](goal). -/
theorem DependsOn.combine {Y Z W : Type*} {S : Finset V}
    {f : (∀ i, X i) → Y} {g : (∀ i, X i) → Z}
    (hf : DependsOn S f) (hg : DependsOn S g) (op : Y → Z → W) :
    DependsOn S (fun x ↦ op (f x) (g x)) := by
  intro x y hxy
  change op (f x) (g x) = op (f y) (g y)
  exact congrArg₂ op (hf hxy) (hg hxy)

/-- A [finite coordinate set](hyp:S) and a [full assignment](hyp:x) determine [its restriction to
those coordinates](goal). -/
def coordinateProjection (S : Finset V) (x : ∀ i, X i) : ∀ i : S, X i :=
  fun i ↦ x i

/-- A [finite coordinate set](hyp:S) [has a measurable assignment-restriction map](goal). -/
@[fun_prop]
theorem measurable_coordinateProjection (S : Finset V) :
    Measurable (coordinateProjection (X := X) S) := by
  refine measurable_pi_iff.mpr fun i ↦ ?_
  simpa only [coordinateProjection] using
    (measurable_pi_apply (i : V) : Measurable (fun x : ∀ i, X i ↦ x (i : V)))

/-- A [finite coordinate set](hyp:S), an [anchor assignment](hyp:x₀), and a [restricted
assignment](hyp:z) determine [the full assignment that uses the restriction on the set and the
anchor elsewhere](goal). -/
def coordinateExtension (S : Finset V) (x₀ : ∀ i, X i) (z : ∀ i : S, X i) : ∀ i, X i :=
  fun i ↦ if hi : i ∈ S then z ⟨i, hi⟩ else x₀ i

/-- A [finite coordinate set](hyp:S) and an [anchor assignment](hyp:x₀) [have a measurable
extension map from restricted to full assignments](goal). -/
@[fun_prop]
theorem measurable_coordinateExtension (S : Finset V) (x₀ : ∀ i, X i) :
    Measurable (coordinateExtension (X := X) S x₀) := by
  refine measurable_pi_iff.mpr fun i ↦ ?_
  by_cases hi : i ∈ S
  · simp only [coordinateExtension, hi, ↓reduceDIte]
    exact measurable_pi_apply (⟨i, hi⟩ : S)
  · simp only [coordinateExtension, hi, ↓reduceDIte]
    exact measurable_const

/-- A [finite coordinate set](hyp:S), an [anchor assignment](hyp:x₀), and a [restricted
assignment](hyp:z) [are recovered unchanged after extension followed by restriction](goal). -/
@[simp]
theorem coordinateProjection_extension (S : Finset V) (x₀ : ∀ i, X i)
    (z : ∀ i : S, X i) :
    coordinateProjection (X := X) S (coordinateExtension S x₀ z) = z := by
  funext i
  simp [coordinateProjection, coordinateExtension, i.property]

/-- A function [depending only on a coordinate set](hyp:hf), together with an [anchor
assignment](hyp:x₀) and a [full assignment](hyp:x), [has the same value after restricting and
then extending that assignment](goal). -/
theorem DependsOn.coordinateExtension_projection {Y : Type*} {S : Finset V}
    {f : (∀ i, X i) → Y} (hf : DependsOn S f) (x₀ x : ∀ i, X i) :
    f (coordinateExtension S x₀ (coordinateProjection S x)) = f x := by
  apply hf
  intro i hi
  have hi' : i ∈ S := hi
  simp [coordinateExtension, coordinateProjection, hi']

/-- An [anchor assignment](hyp:x₀), a [measurable outcome map](hyp:hf), its [dependence only on a
finite coordinate set](hyp:hdepends), and [equality of the two corresponding coordinate
marginals](hyp:hproj) [imply equality of the outcome laws under the two measures](goal). -/
theorem map_eq_of_map_coordinateProjection_eq
    {Y : Type*} [MeasurableSpace Y] {S : Finset V}
    {μ ν : Measure (∀ i, X i)} {f : (∀ i, X i) → Y}
    (x₀ : ∀ i, X i) (hf : Measurable f) (hdepends : DependsOn S f)
    (hproj : Measure.map (coordinateProjection (X := X) S) μ =
      Measure.map (coordinateProjection (X := X) S) ν) :
    Measure.map f μ = Measure.map f ν := by
  let e := coordinateExtension (X := X) S x₀
  have he : Measurable e := measurable_coordinateExtension S x₀
  calc
    Measure.map f μ = Measure.map (f ∘ e ∘ coordinateProjection S) μ := by
      congr 1
      funext x
      exact (hdepends.coordinateExtension_projection x₀ x).symm
    _ = Measure.map (f ∘ e) (Measure.map (coordinateProjection S) μ) := by
      simpa only [Function.comp_def] using
        (Measure.map_map (hf.comp he) (measurable_coordinateProjection S) (μ := μ)).symm
    _ = Measure.map (f ∘ e) (Measure.map (coordinateProjection S) ν) := by rw [hproj]
    _ = Measure.map (f ∘ e ∘ coordinateProjection S) ν := by
      simpa only [Function.comp_def] using
        Measure.map_map (hf.comp he) (measurable_coordinateProjection S) (μ := ν)
    _ = Measure.map f ν := by
      congr 1
      funext x
      exact hdepends.coordinateExtension_projection x₀ x

/-- A [measurable source map](hyp:hf), a [measurable common downstream map](hyp:hmix), and
[equality of the source laws](hyp:hlaw) [imply equality after the common downstream mapping](goal). -/
theorem map_comp_eq_of_map_eq
    {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    {μ ν : Measure (∀ i, X i)} {f : (∀ i, X i) → Y} {mix : Y → Z}
    (hf : Measurable f) (hmix : Measurable mix)
    (hlaw : Measure.map f μ = Measure.map f ν) :
    Measure.map (mix ∘ f) μ = Measure.map (mix ∘ f) ν := by
  calc
    Measure.map (mix ∘ f) μ = Measure.map mix (Measure.map f μ) :=
      (Measure.map_map hmix hf (μ := μ)).symm
    _ = Measure.map mix (Measure.map f ν) := by rw [hlaw]
    _ = Measure.map (mix ∘ f) ν := Measure.map_map hmix hf (μ := ν)

/-- A [finite coordinate set](hyp:S), [measurable observational density](hyp:hf), [measurable
comparison density](hyp:hg), and [equality after integrating out all complementary coordinates](hyp:hmarginal)
[imply equality of the projected measures induced by those densities](goal). -/
theorem map_coordinateProjection_withDensity_eq_of_lmarginal_eq
    [Fintype V] {μ : ∀ i, Measure (X i)} [∀ i, SigmaFinite (μ i)]
    (S : Finset V) {f g : (∀ i, X i) → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g)
    (hmarginal : (∫⋯∫⁻_(Finset.univ \ S), f ∂μ) =
      (∫⋯∫⁻_(Finset.univ \ S), g ∂μ)) :
    Measure.map (coordinateProjection (X := X) S) ((Measure.pi μ).withDensity f) =
      Measure.map (coordinateProjection (X := X) S) ((Measure.pi μ).withDensity g) := by
  ext A hA
  have hproj : Measurable (coordinateProjection (X := X) S) :=
    measurable_coordinateProjection S
  have hpre : MeasurableSet (coordinateProjection (X := X) S ⁻¹' A) := hproj hA
  rw [Measure.map_apply hproj hA, Measure.map_apply hproj hA,
    withDensity_apply _ hpre, withDensity_apply _ hpre]
  rw [← lintegral_indicator hpre, ← lintegral_indicator hpre]
  apply lintegral_eq_of_lmarginal_eq (Finset.univ \ S)
    (hf.indicator hpre) (hg.indicator hpre)
  funext x
  simp only [lmarginal]
  have hupdate (y : ∀ i : ↥(Finset.univ \ S), X i) :
      coordinateProjection (X := X) S (updateFinset x (Finset.univ \ S) y) =
        coordinateProjection S x := by
    funext i
    simp [coordinateProjection, updateFinset_def, i.property]
  have hmem (y : ∀ i : ↥(Finset.univ \ S), X i) :
      updateFinset x (Finset.univ \ S) y ∈ coordinateProjection (X := X) S ⁻¹' A ↔
        x ∈ coordinateProjection (X := X) S ⁻¹' A := by
    change coordinateProjection S (updateFinset x (Finset.univ \ S) y) ∈ A ↔
      coordinateProjection S x ∈ A
    rw [hupdate y]
  by_cases hx : x ∈ coordinateProjection (X := X) S ⁻¹' A
  · have hm := congrFun hmarginal x
    simp only [lmarginal] at hm
    simpa only [Set.indicator, hmem, hx, if_pos] using hm
  · simp only [Set.indicator, hmem, hx, if_false]

end Causalean.Mathlib.MeasureTheory.FiniteCoordinate
