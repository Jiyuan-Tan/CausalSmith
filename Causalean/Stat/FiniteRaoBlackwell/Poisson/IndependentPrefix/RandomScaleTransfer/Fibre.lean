module
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.IndependentPrefix.RandomScaleTransfer.Basic
public import Causalean.Stat.Minimax.TotalVariation

/-!
# One-pool ordered-prefix fibre transfer

This module turns a finite marked-Poisson sample into a fixed iid prefix with
one parameter-independent fallback map.  It gives the exact pushforward
decomposition and the resulting total-variation error paid only by the
short-count event.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix.RandomScaleMinimaxTransfer

namespace Causalean.Stat.FiniteRaoBlackwell.Poisson.IndependentPrefix.RandomScaleTransfer

variable {X : Type*} [MeasurableSpace X] {n : ℕ}

/-- For [a probability mark law](hyp:P), [a nonnegative intensity](hyp:lam), and
[a fixed fallback array](hyp:fallback), [the full ordered-prefix law is the
success-weighted iid law plus the failure-weighted fallback law](goal).

The successful summand is the existing successful-count fibre identity
`map_orderedPrefix_restrict_count_ge`; on the short-count fibre the ordered
prefix is the fallback. -/
theorem map_orderedPrefix_finitePoissonSampleLaw
    (P : Measure X) [IsProbabilityMeasure P] (lam : ℝ≥0)
    (fallback : Fin n → X) :
    Measure.map (orderedPrefix fallback) (finitePoissonSampleLaw P lam) =
      poissonMeasure lam (Set.Ici n) • Measure.pi (fun _ : Fin n => P) +
        poissonMeasure lam (Set.Iio n) • Measure.dirac fallback := by
  let μ := finitePoissonSampleLaw P lam
  let good : Set (FiniteSample X) := FiniteSample.count ⁻¹' Set.Ici n
  let bad : Set (FiniteSample X) := FiniteSample.count ⁻¹' Set.Iio n
  have hgood_meas : MeasurableSet good :=
    (by measurability : MeasurableSet (Set.Ici n)).preimage measurable_finiteSample_count
  have hbad_meas : MeasurableSet bad :=
    (by measurability : MeasurableSet (Set.Iio n)).preimage measurable_finiteSample_count
  have hgood : Measure.map (orderedPrefix fallback) (μ.restrict good) =
      poissonMeasure lam (Set.Ici n) • Measure.pi (fun _ : Fin n => P) :=
    map_orderedPrefix_restrict_count_ge P lam fallback
  have hbad : Measure.map (orderedPrefix fallback) (μ.restrict bad) =
      poissonMeasure lam (Set.Iio n) • Measure.dirac fallback := by
    have heq : orderedPrefix fallback =ᵐ[μ.restrict bad] fun _ => fallback := by
      apply ae_restrict_of_forall_mem hbad_meas
      intro s hs
      have hlt : s.count < n := hs
      simp [orderedPrefix, not_le.mpr hlt]
    rw [Measure.map_congr heq, Measure.map_const]
    congr 1
    rw [Measure.restrict_apply_univ]
    change μ (FiniteSample.count ⁻¹' Set.Iio n) = _
    rw [show μ = finitePoissonSampleLaw P lam by rfl,
      ← finitePoissonSampleLaw_map_count P lam,
      Measure.map_apply measurable_finiteSample_count (by measurability)]
  have hcompl : bad = goodᶜ := by
    ext s
    simp [good, bad]
  change Measure.map (orderedPrefix fallback) μ = _
  rw [← (Measure.restrict_add_restrict_compl hgood_meas :
    μ.restrict good + μ.restrict goodᶜ = μ), ← hcompl,
    Measure.map_add _ _ (measurable_orderedPrefix fallback), hgood, hbad]

/-- For [a probability mark law](hyp:P), [a nonnegative intensity](hyp:lam), and
[a fixed fallback array](hyp:fallback), [the total-variation distance between the iid law of a
fixed-length sample and the law of the ordered prefix of that length taken from a finite Poisson
sample, with the fallback array substituted when the Poisson sample is too short, is at most the
Poisson probability that the count is below that length](goal).

This bound does not divide by the success probability, so it also covers zero
intensity and a zero-length prefix. -/
theorem tvDist_iid_map_orderedPrefix_le
    (P : Measure X) [IsProbabilityMeasure P] (lam : ℝ≥0)
    (fallback : Fin n → X) :
    Causalean.Stat.tvDist (Measure.pi (fun _ : Fin n => P))
        (Measure.map (orderedPrefix fallback) (finitePoissonSampleLaw P lam)) ≤
      (poissonMeasure lam (Set.Iio n)).toReal := by
  have hsum : (poissonMeasure lam (Set.Ici n)).toReal +
      (poissonMeasure lam (Set.Iio n)).toReal = 1 := by
    have hcompl : (Set.Ici n : Set ℕ)ᶜ = Set.Iio n := by
      ext k
      simp
    simpa [hcompl, measureReal_def] using
      (measureReal_add_measureReal_compl (μ := poissonMeasure lam)
        (by measurability : MeasurableSet (Set.Ici n)))
  rw [map_orderedPrefix_finitePoissonSampleLaw]
  unfold Causalean.Stat.tvDist
  apply ciSup_le
  rintro ⟨A, hA⟩
  rw [measureReal_add_apply
    (by simp only [Measure.smul_apply, smul_eq_mul]; finiteness)
    (by simp only [Measure.smul_apply, smul_eq_mul]; finiteness),
    measureReal_ennreal_smul_apply, measureReal_ennreal_smul_apply]
  have hgap :
      (Measure.pi (fun _ : Fin n => P)).real A -
          ((poissonMeasure lam (Set.Ici n)).toReal *
              (Measure.pi (fun _ : Fin n => P)).real A +
            (poissonMeasure lam (Set.Iio n)).toReal *
              (Measure.dirac fallback).real A) =
        (poissonMeasure lam (Set.Iio n)).toReal *
          ((Measure.pi (fun _ : Fin n => P)).real A -
            (Measure.dirac fallback).real A) := by
    have hq : (poissonMeasure lam (Set.Ici n)).toReal =
        1 - (poissonMeasure lam (Set.Iio n)).toReal := by linarith
    rw [hq]
    ring
  rw [hgap, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
  calc
    _ ≤ (poissonMeasure lam (Set.Iio n)).toReal * 1 :=
      mul_le_mul_of_nonneg_left
        (Causalean.Stat.abs_measureReal_sub_le_one
          (μ := Measure.pi (fun _ : Fin n => P))
          (ν := Measure.dirac fallback) A) ENNReal.toReal_nonneg
    _ = _ := mul_one _

end Causalean.Stat.FiniteRaoBlackwell.Poisson.IndependentPrefix.RandomScaleTransfer
