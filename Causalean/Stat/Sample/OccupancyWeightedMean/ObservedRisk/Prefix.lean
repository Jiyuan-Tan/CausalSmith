module
public import Causalean.Stat.Sample.OccupancyWeightedMean.ObservedRisk.RiskAlgebra
public import Causalean.Stat.Sample.PiTransport

/-!
# Deterministic iid pilot prefixes

A deterministic prefix of a larger iid sample has the finite product law used
by the observed collision-risk theorem. The squared-risk identity records the
transport needed by a paper-local pilot estimator.
-/

public section

namespace Causalean.Stat.Sample.OccupancyWeightedMean.ObservedRisk

open MeasureTheory

/-- Selecting the first `n` coordinates of an `N`-observation iid sample
pushes its law forward to the `n`-fold observed product law. -/
theorem iid_prefix_map {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n N : ℕ} (hnN : n ≤ N) :
    (Measure.pi (fun _ : Fin N => μ)).map
      (fun z : Fin N → Ω => fun i : Fin n => z (Fin.castLE hnN i)) =
      Measure.pi (fun _ : Fin n => μ) := by
  let e : {i : Fin N // (i : ℕ) < n} ≃ Fin n := (Fin.castLEquiv hnN).symm
  have h₁ := Causalean.Stat.measurePreserving_pi_restrict μ
    (fun i : Fin N => (i : ℕ) < n)
  have h₂ := measurePreserving_piCongrLeft
    (α := fun _ : Fin n => Ω) (fun _ : Fin n => μ) e
  have h := h₂.comp h₁
  convert h.map_eq using 1
  congr 1

/-- Given [an observed probability law and finite cell setting](hyp:Ω,κ,μ),
[measurable cell, arm, and outcome maps with centers](hyp:X,A,Y,center,hX,hA,hY),
and [sample sizes n ≤ N](hyp:n,N,hnN), [the expected squared difference between
the collision estimator and the population contrast is the same whether the
estimator is computed from the first n observations of N independent draws or
from n independent draws](goal). -/
theorem integral_prefix_collision_error_sq
    {Ω κ : Type} [MeasurableSpace Ω] [Fintype κ] [DecidableEq κ]
    [MeasurableSpace κ] [MeasurableSingletonClass κ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → κ) (A : Ω → Bool) (Y : Ω → ℝ)
    (center : Bool → κ → ℝ)
    (hX : Measurable X) (hA : Measurable A) (hY : Measurable Y)
    {n N : ℕ} (hnN : n ≤ N) :
    (∫ z : Fin N → Ω,
      (collisionEstimator X A Y (fun i : Fin n => z (Fin.castLE hnN i)) -
        populationContrast μ X center) ^ 2
      ∂Measure.pi (fun _ : Fin N => μ)) =
    ∫ z : Fin n → Ω,
      (collisionEstimator X A Y z - populationContrast μ X center) ^ 2
      ∂Measure.pi (fun _ : Fin n => μ) := by
  have hprefix : Measurable
      (fun z : Fin N → Ω => fun i : Fin n => z (Fin.castLE hnN i)) := by
    fun_prop
  have herror : Measurable (fun z : Fin n → Ω =>
      (collisionEstimator X A Y z - populationContrast μ X center) ^ 2) :=
    ((measurable_collisionEstimator X A Y hX hA hY).sub measurable_const).pow_const 2
  calc
    _ = ∫ z : Fin n → Ω,
        (collisionEstimator X A Y z - populationContrast μ X center) ^ 2
        ∂(Measure.pi (fun _ : Fin N => μ)).map
          (fun z : Fin N → Ω => fun i : Fin n => z (Fin.castLE hnN i)) := by
          exact (integral_map hprefix.aemeasurable herror.aestronglyMeasurable).symm
    _ = _ := by rw [iid_prefix_map μ hnN]

end Causalean.Stat.Sample.OccupancyWeightedMean.ObservedRisk
