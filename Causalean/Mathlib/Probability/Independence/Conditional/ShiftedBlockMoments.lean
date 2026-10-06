module
public import Causalean.Mathlib.Probability.Independence.Conditional.ThreeBlockProduct

/-!
# Conditional moments of a training-shifted held-out block

A score on a held-out coordinate block has constant conditional mean given a
disjoint training block. Subtracting a measurable training-block shift subtracts
that shift from the conditional mean.
-/

public section

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability.Independence

namespace Causalean.Mathlib.Probability.Independence.Conditional

variable {ι : Type*} [Fintype ι]
variable {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
  [∀ i, StandardBorelSpace (Ω i)]

/-- [A finite product probability law](hyp:μ), [a training block and held-out
block](hyp:B0,B1) with [disjointness](hyp:hdisj), [a measurable score](hyp:f,hfmeas),
and [an integrable pulled-back score](hyp:hf) imply that [its conditional mean given
the training block is its unconditional mean](goal). -/
theorem condExp_heldoutBlock_eq_integral
    (μ : (i : ι) → Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (B0 B1 : Finset ι) (hdisj : Disjoint B0 B1)
    (f : ((i : {i // i ∈ B1}) → Ω i.val) → ℝ)
    (hfmeas : Measurable f)
    (hf : Integrable (fun x : ∀ i, Ω i => f (finsetCoordProj B1 x))
      (Measure.pi μ)) :
    condExp (MeasurableSpace.comap (finsetCoordProj (Ω := Ω) B0) inferInstance)
      (Measure.pi μ) (fun x : ∀ i, Ω i => f (finsetCoordProj B1 x))
      =ᵐ[Measure.pi μ]
    (fun _ => ∫ x : (∀ i, Ω i), f (finsetCoordProj B1 x) ∂Measure.pi μ) := by
  have hproj := indepFun_pi_of_disjoint (Ω := Ω) μ hdisj.symm
  have hF : (Fintype.ofFinite ι) = (inferInstance : Fintype ι) :=
    Subsingleton.elim _ _
  have hpi : @Measure.pi ι Ω (Fintype.ofFinite ι) _ μ = Measure.pi μ :=
    congrArg (fun fi : Fintype ι => @Measure.pi ι Ω fi _ μ) hF
  have hindep : IndepFun (finsetCoordProj (Ω := Ω) B1)
      (finsetCoordProj (Ω := Ω) B0) (Measure.pi μ) := by
    change IndepFun (fun x : ∀ i, Ω i => fun i : {i // i ∈ B1} => x i.val)
      (fun x : ∀ i, Ω i => fun i : {i // i ∈ B0} => x i.val) (Measure.pi μ)
    simpa only [hpi] using hproj
  have hmeas : Measurable (fun x : ∀ i, Ω i => f (finsetCoordProj B1 x)) :=
    hfmeas.comp (measurable_finsetCoordProj B1)
  have hle₁ := (measurable_finsetCoordProj (Ω := Ω) B1).comap_le
  have hle₂ := (measurable_finsetCoordProj (Ω := Ω) B0).comap_le
  haveI : IsFiniteMeasure (Measure.pi μ) := inferInstance
  haveI : IsFiniteMeasure ((Measure.pi μ).trim hle₂) := isFiniteMeasure_trim hle₂
  have hsm : StronglyMeasurable[MeasurableSpace.comap
      (finsetCoordProj (Ω := Ω) B1) inferInstance]
      (fun x : ∀ i, Ω i => f (finsetCoordProj B1 x)) := by
    have hp : Measurable[MeasurableSpace.comap
        (finsetCoordProj (Ω := Ω) B1) inferInstance]
        (finsetCoordProj (Ω := Ω) B1) := measurable_iff_comap_le.mpr le_rfl
    exact (hfmeas.comp hp).stronglyMeasurable
  exact condExp_indep_eq hle₁ hle₂ hsm
    ((IndepFun_iff_Indep _ _ _).mp hindep)

/-- [A finite product probability law](hyp:μ), [a disjoint training and held-out
block](hyp:B0,B1,hdisj), [a held-out score and training shift](hyp:f,a) with
[measurability](hyp:hfmeas,hameas) and [integrability](hyp:hf,ha) imply that [the
conditional mean of their difference is the held-out mean minus the same training
shift](goal). -/
theorem condExp_shiftedBlock_eq_integral_sub
    (μ : (i : ι) → Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (B0 B1 : Finset ι) (hdisj : Disjoint B0 B1)
    (f : ((i : {i // i ∈ B1}) → Ω i.val) → ℝ)
    (a : ((i : {i // i ∈ B0}) → Ω i.val) → ℝ)
    (hfmeas : Measurable f) (hameas : Measurable a)
    (hf : Integrable (fun x : ∀ i, Ω i => f (finsetCoordProj B1 x))
      (Measure.pi μ))
    (ha : Integrable (fun x : ∀ i, Ω i => a (finsetCoordProj B0 x))
      (Measure.pi μ)) :
    condExp (MeasurableSpace.comap (finsetCoordProj (Ω := Ω) B0) inferInstance)
      (Measure.pi μ)
      (fun x : ∀ i, Ω i => f (finsetCoordProj B1 x) - a (finsetCoordProj B0 x))
      =ᵐ[Measure.pi μ]
    (fun x => (∫ y : (∀ i, Ω i), f (finsetCoordProj B1 y) ∂Measure.pi μ) -
      a (finsetCoordProj B0 x)) := by
  have hle := (measurable_finsetCoordProj (Ω := Ω) B0).comap_le
  haveI : IsFiniteMeasure (Measure.pi μ) := inferInstance
  haveI : IsFiniteMeasure ((Measure.pi μ).trim hle) := isFiniteMeasure_trim hle
  have hsm : StronglyMeasurable[MeasurableSpace.comap
      (finsetCoordProj (Ω := Ω) B0) inferInstance]
      (fun x : ∀ i, Ω i => a (finsetCoordProj B0 x)) := by
    have hp : Measurable[MeasurableSpace.comap
        (finsetCoordProj (Ω := Ω) B0) inferInstance]
        (finsetCoordProj (Ω := Ω) B0) := measurable_iff_comap_le.mpr le_rfl
    exact (hameas.comp hp).stronglyMeasurable
  have hshift := condExp_of_stronglyMeasurable hle hsm ha
  have hfirst := condExp_heldoutBlock_eq_integral μ B0 B1 hdisj f hfmeas hf
  refine (condExp_sub hf ha _).trans ?_
  rw [hshift]
  filter_upwards [hfirst] with x hx
  exact congrArg (fun z : ℝ => z - a (finsetCoordProj B0 x)) hx

end Causalean.Mathlib.Probability.Independence.Conditional
