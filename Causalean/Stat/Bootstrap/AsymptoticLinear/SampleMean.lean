module

public import Causalean.Stat.Bootstrap.AsymptoticLinear.Main

/-!
# Sample-mean bootstrap validity

This module supplies the canonical constructor for the real sample mean.  A square-integrable,
nondegenerate real observation has influence function equal to the centered observation, and both
the sampling and Efron-bootstrap linearizations are exact finite-sample identities.
-/

@[expose] public section

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]
  {mu : Measure Omega} {P : Measure ℝ}

/-- The [sample-mean statistic](goal) at [a sample size](hyp:n) sends [a finite real data
vector](hyp:x) to its arithmetic mean. -/
def sampleMeanStatistic (n : ℕ) (x : Fin n -> ℝ) : ℝ :=
  finMean x

/-- For [an independent, identically distributed real sample](hyp:S) whose observation has [an
integrable square](hyp:hX2) and [strictly positive variance](hyp:hvar), [the sample mean is
bootstrap asymptotically linear at the population mean, with the centered observation as
influence function](goal); both linearization remainders vanish exactly. -/
theorem BootstrapAsymLinear.sampleMean
    (S : IIDSample Omega ℝ mu P)
    (hX2 : Integrable (fun x : ℝ => x ^ 2) P)
    (hvar : 0 < ProbabilityTheory.variance (fun x : ℝ => x) P) :
    BootstrapAsymLinear S sampleMeanStatistic (∫ x, x ∂P)
      (fun x => x - ∫ y, y ∂P) := by
  letI : IsProbabilityMeasure mu := S.indep.isProbabilityMeasure
  letI : IsProbabilityMeasure P := by
    rw [← S.law]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  have hIdL2 : MemLp (fun x : ℝ => x) 2 P :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2 hX2
  have hIdInt : Integrable (fun x : ℝ => x) P := hIdL2.integrable (by norm_num)
  have hCenterL2 : MemLp (fun x : ℝ => x - ∫ y, y ∂P) 2 P := by
    convert hIdL2.sub (memLp_const (∫ y, y ∂P)) using 1
    ext x
    rfl
  refine
    { meas := ?_
      mean_zero := ?_
      var_pos_finite := ?_
      linear := ?_
      boot_linear := ?_ }
  · constructor
    · intro n
      unfold sampleMeanStatistic finMean
      fun_prop
    · fun_prop
  · rw [integral_sub hIdInt (integrable_const _)]
    simp
  · constructor
    · rw [← ProbabilityTheory.variance_eq_integral
        (X := fun x : ℝ => x) measurable_id.aemeasurable]
      exact hvar
    · exact hCenterL2.integrable_sq
  · unfold Tendsto_inProb
    refine TendstoInMeasure.congr'
      (f := fun _ (_ : Omega) => (0 : ℝ))
      (f' := fun (n : ℕ) (omega : Omega) =>
        Real.sqrt (n : ℝ) *
            (sampleMeanStatistic n (S.sampleVector n omega) - ∫ x, x ∂P) -
          IsAsymLinear.normalizedSum S (fun x => x - ∫ y, y ∂P)
            (fun m => Finset.range m) n omega)
      ?_ Filter.EventuallyEq.rfl ?_
    · exact Filter.eventually_atTop.2 ⟨1, fun n hn =>
        Filter.Eventually.of_forall fun omega => by
          have hn0 : n ≠ 0 := Nat.ne_of_gt hn
          simp only
          unfold sampleMeanStatistic finMean IIDSample.sampleVector
            IsAsymLinear.normalizedSum
          simp only [Finset.card_range, Finset.sum_sub_distrib, Finset.sum_const,
            nsmul_eq_mul, smul_eq_mul]
          have hsum : (∑ i : Fin n, S.Z i omega) =
              ∑ i ∈ Finset.range n, S.Z i omega :=
            Fin.sum_univ_eq_sum_range (fun i => S.Z i omega) n
          rw [hsum]
          have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
          have hsqrt : Real.sqrt (n : ℝ) ≠ 0 :=
            Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr hn)
          have hsqrt_sq : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) :=
            Real.sq_sqrt (Nat.cast_nonneg n)
          field_simp
          rw [hsqrt_sq]
          ring⟩
    · exact tendstoInMeasure_of_tendsto_ae
        (fun _ => measurable_const.aestronglyMeasurable)
        (Filter.Eventually.of_forall fun _ => tendsto_const_nhds)
  · intro epsilon hepsilon
    have hev :
        (fun n => mu.real {omega |
          epsilon < (bootstrapResample (S.sampleVector n omega)).real
            {xstar | epsilon < abs
              (centeredEstimatorBootstrapStatistic sampleMeanStatistic n
                  (S.sampleVector n omega) xstar -
                centeredBootstrapSum
                  (fun x => x - ∫ y, y ∂P)
                  (S.sampleVector n omega) xstar)}})
          =ᶠ[Filter.atTop] fun _ : ℕ => (0 : ℝ) := by
      exact Filter.eventually_atTop.2 ⟨1, fun n hn => by
        have hn0 : n ≠ 0 := Nat.ne_of_gt hn
        have hrem (omega : Omega) (xstar : Fin n → ℝ) :
            centeredEstimatorBootstrapStatistic sampleMeanStatistic n
                  (S.sampleVector n omega) xstar -
                centeredBootstrapSum
                  (fun x => x - ∫ y, y ∂P)
                  (S.sampleVector n omega) xstar = 0 := by
          rw [centeredBootstrapSum_eq_sqrt_mul_finAverage_sub
            hn0 (fun x : ℝ => x - ∫ y, y ∂P) (S.sampleVector n omega) xstar]
          unfold centeredEstimatorBootstrapStatistic sampleMeanStatistic
            finMean
          simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
          field_simp
          ring
        simp_rw [hrem]
        simp [not_lt_of_ge hepsilon.le]⟩
    exact Filter.Tendsto.congr' hev.symm tendsto_const_nhds

end

end Causalean.Stat
