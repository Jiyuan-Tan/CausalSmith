module
public import Causalean.Stat.CLT.BerryEsseen.CDFDifferenceIntegrable
public import Mathlib.Probability.CentralLimitTheorem

/-! # Translation of a CDF difference Fourier integral

Reflection around a fixed point converts the spatial integral arising from
convolution into the ordinary Fourier transform of a CDF difference.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory ProbabilityTheory

/-- For [two probability laws with finite first moments](hyp:hμ,hν),
[the integral of exp(−ity) times their CDF difference evaluated at z − y
equals the phase exp(−itz) times the Fourier integral at frequency t of their
CDF difference](goal): reflecting the argument about z extracts that
phase. -/
theorem cdf_difference_fourier_shift
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun y : ℝ => y) μ)
    (hν : Integrable (fun y : ℝ => y) ν)
    (t z : ℝ) :
    (∫ y : ℝ,
      Complex.exp (((-(t * y) : ℝ) : ℂ) * Complex.I) *
        (((μ (Set.Iic (z - y))).toReal -
          (ν (Set.Iic (z - y))).toReal : ℝ) : ℂ)) =
      Complex.exp (((-(t * z) : ℝ) : ℂ) * Complex.I) *
        ∫ x : ℝ,
          Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
            (((μ (Set.Iic x)).toReal - (ν (Set.Iic x)).toReal : ℝ) : ℂ) := by
  /- The CDF difference is integrable by
  `integrable_cdf_difference_of_first_moments`; the exponential has norm one.
  Apply the volume-preserving reflection `y ↦ z - y`, then `exp_add` and
  `integral_const_mul`. -/
  have hD := integrable_cdf_difference_of_first_moments μ ν hμ hν
  have hDℂ : Integrable (fun x : ℝ =>
      (((μ (Set.Iic x)).toReal - (ν (Set.Iic x)).toReal : ℝ) : ℂ)) volume :=
    hD.ofReal
  have hF : Integrable (fun x : ℝ =>
      Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
        (((μ (Set.Iic x)).toReal - (ν (Set.Iic x)).toReal : ℝ) : ℂ)) volume := by
    apply hDℂ.bdd_mul (c := 1)
    · fun_prop
    · filter_upwards [] with x
      simpa only [← Complex.ofReal_mul] using
        (le_of_eq (Complex.norm_exp_ofReal_mul_I (t * x)))
  have hphase (x : ℝ) :
      Complex.exp (((-(t * (z - x)) : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((-(t * z) : ℝ) : ℂ) * Complex.I) *
          Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hG : Integrable (fun x : ℝ =>
      Complex.exp (((-(t * (z - x)) : ℝ) : ℂ) * Complex.I) *
        (((μ (Set.Iic x)).toReal - (ν (Set.Iic x)).toReal : ℝ) : ℂ)) volume := by
    convert hF.const_mul (Complex.exp (((-(t * z) : ℝ) : ℂ) * Complex.I)) using 1
    ext x
    rw [hphase x]
    ring
  have hmp := Measure.measurePreserving_sub_left (volume : Measure ℝ) z
  have hGmap : AEStronglyMeasurable (fun x : ℝ =>
      Complex.exp (((-(t * (z - x)) : ℝ) : ℂ) * Complex.I) *
        (((μ (Set.Iic x)).toReal - (ν (Set.Iic x)).toReal : ℝ) : ℂ))
      (Measure.map (fun y : ℝ => z - y) volume) := by
    rw [hmp.map_eq]
    exact hG.aestronglyMeasurable
  have hshift := (integral_map hmp.measurable.aemeasurable hGmap).symm
  rw [hmp.map_eq] at hshift
  calc
    _ = ∫ x : ℝ,
        Complex.exp (((-(t * (z - x)) : ℝ) : ℂ) * Complex.I) *
          (((μ (Set.Iic x)).toReal - (ν (Set.Iic x)).toReal : ℝ) : ℂ) := by
      convert hshift using 1
      · congr 1
        ext y
        simp
    _ = _ := by
      simp_rw [hphase, mul_assoc]
      rw [integral_const_mul]

end Causalean.Stat.CLT.BerryEsseen
