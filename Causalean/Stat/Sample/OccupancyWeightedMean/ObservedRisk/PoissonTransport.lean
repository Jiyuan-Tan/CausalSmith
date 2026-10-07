module
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.Partition.Splitting
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.PairedHistogram.HistogramReconstruction.CountLaw
public import Causalean.Stat.Sample.OccupancyWeightedMean.ObservedRisk.Basic

/-!
# Poisson sample to independent arm-cell counts

The count-law identity transports an observed finite Poisson sample to its
independent Poisson arm-cell histogram, including cells of zero mass.
-/

public section

namespace Causalean.Stat.Sample.OccupancyWeightedMean.ObservedRisk

open MeasureTheory ProbabilityTheory Causalean.Stat
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram
open scoped NNReal

/-- Given [a finite cell count](hyp:d), [an observed probability law](hyp:ν),
and [a nonnegative Poisson mean λ](hyp:lam), draw a Poisson(λ) number of
independent observations from the law. Then [the table of control and treated
counts in each cell has independent entries across cells and arms, the count of
each arm-cell pair being Poisson with mean λ times that pair's
probability](goal); a pair of zero probability has the degenerate Poisson law
with mean zero. -/
theorem poisson_arm_cell_count_law {d : ℕ}
    (ν : Measure (Fin d × Bool)) [IsProbabilityMeasure ν]
    (lam : ℝ≥0) :
    (finitePoissonSampleLaw ν lam).map
      (fun s : FiniteSample (Fin d × Bool) =>
        fun k : Fin d =>
          (groupArmCount (fun v : Fin d × Bool => v.1) (fun v => v.2)
            s.2 false k,
           groupArmCount (fun v : Fin d × Bool => v.1) (fun v => v.2)
            s.2 true k)) =
    Measure.pi (fun k : Fin d =>
      (poissonMeasure (lam * (ν {(k, false)}).toNNReal)).prod
        (poissonMeasure (lam * (ν {(k, true)}).toNNReal))) := by
  classical
  let μ : Fin d × Bool → Measure ℕ :=
    fun p => poissonMeasure (lam * (ν {p}).toNNReal)
  let regroup : (Fin d × Bool → ℕ) → Fin d → ℕ × ℕ :=
    fun h k => (h (k, false), h (k, true))
  have hregroup : Measurable regroup := by
    apply measurable_pi_lambda
    intro k
    exact (measurable_pi_apply (k, false)).prodMk
      (measurable_pi_apply (k, true))
  have hhist : (fun s : FiniteSample (Fin d × Bool) =>
      fun k : Fin d =>
        (groupArmCount (fun v : Fin d × Bool => v.1) (fun v => v.2)
          s.2 false k,
         groupArmCount (fun v : Fin d × Bool => v.1) (fun v => v.2)
          s.2 true k)) =
      regroup ∘ (fun s : FiniteSample (Fin d × Bool) =>
        finiteSampleHistogram s.points) := by
    funext s k
    rcases s with ⟨n, z⟩
    have hcount (a : Bool) :
        groupArmCount (fun v : Fin d × Bool => v.1) (fun v => v.2) z a k =
          finiteSampleHistogram z (k, a) := by
      rw [finiteSampleHistogram, Fintype.card_subtype]
      unfold groupArmCount
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      cases h : z i with
      | mk x b => simp
    exact Prod.ext (hcount false) (hcount true)
  have hhistMeas : Measurable (fun s : FiniteSample (Fin d × Bool) =>
      finiteSampleHistogram s.points) := by
    apply measurable_to_countable'
    intro c
    rw [MeasurableSpace.measurableSet_iInf]
    intro n
    change MeasurableSet ((Sigma.mk n) ⁻¹'
      {s : FiniteSample (Fin d × Bool) |
        finiteSampleHistogram s.points = c})
    exact (Set.to_countable _).measurableSet
  rw [hhist, ← Measure.map_map hregroup hhistMeas]
  rw [finitePoissonSampleLaw_map_histogram]
  change Measure.map regroup (Measure.pi μ) = _
  have hcurry : Measure.map (MeasurableEquiv.curry (Fin d) Bool ℕ)
      (Measure.pi μ) = Measure.pi (fun k : Fin d =>
        Measure.pi (fun a : Bool => μ (k, a))) := by
    simpa only [Measure.infinitePi_eq_pi] using
      (Measure.infinitePi_map_curry (fun k : Fin d => fun a : Bool => μ (k, a)))
  have hpair (k : Fin d) :
      Measure.map (fun f : Bool → ℕ => (f false, f true))
        (Measure.pi (fun a : Bool => μ (k, a))) =
        (μ (k, false)).prod (μ (k, true)) := by
    let e : Bool ≃ Fin 2 := finTwoEquiv.symm
    let m : Fin 2 → Measure ℕ := fun i => μ (k, finTwoEquiv i)
    have hreindex : Measure.map
        (MeasurableEquiv.piCongrLeft (fun _ : Fin 2 => ℕ) e)
        (Measure.pi (fun a : Bool => μ (k, a))) = Measure.pi m := by
      simpa [m, e] using Measure.pi_map_piCongrLeft e m
    have htwo := (measurePreserving_piFinTwo m).map_eq
    calc
      _ = Measure.map (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℕ))
          (Measure.map (MeasurableEquiv.piCongrLeft (fun _ : Fin 2 => ℕ) e)
            (Measure.pi (fun a : Bool => μ (k, a)))) := by
              rw [Measure.map_map]
              · congr 1
              · exact (MeasurableEquiv.piFinTwo _).measurable
              · exact (MeasurableEquiv.piCongrLeft _ e).measurable
      _ = (μ (k, false)).prod (μ (k, true)) := by
        rw [hreindex, htwo]
        simp [m, finTwoEquiv]
  have hmap : Measure.map regroup (Measure.pi μ) =
      Measure.pi (fun k : Fin d =>
        (μ (k, false)).prod (μ (k, true))) := by
    let pair : (Fin d → Bool → ℕ) → Fin d → ℕ × ℕ :=
      fun f k => (f k false, f k true)
    have hpairMeas : Measurable pair := by fun_prop
    calc
      _ = Measure.map pair
          (Measure.map (MeasurableEquiv.curry (Fin d) Bool ℕ)
            (Measure.pi μ)) := by
              rw [Measure.map_map hpairMeas (MeasurableEquiv.curry _ _ _).measurable]
              rfl
      _ = Measure.map pair (Measure.pi (fun k : Fin d =>
          Measure.pi (fun a : Bool => μ (k, a)))) := by rw [hcurry]
      _ = Measure.pi (fun k : Fin d =>
          Measure.map (fun f : Bool → ℕ => (f false, f true))
            (Measure.pi (fun a : Bool => μ (k, a)))) := by
              simpa [pair] using (Measure.pi_map_pi
                (μ := fun k : Fin d => Measure.pi (fun a : Bool => μ (k, a)))
                (f := fun _ : Fin d => fun f : Bool → ℕ => (f false, f true))
                (fun _ => by fun_prop))
      _ = _ := by simp_rw [hpair]
  exact hmap

end Causalean.Stat.Sample.OccupancyWeightedMean.ObservedRisk
