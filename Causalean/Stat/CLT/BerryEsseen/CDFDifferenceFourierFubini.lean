module
public import Causalean.Stat.CLT.BerryEsseen.CDFDifferenceFourierEndpoint
public import Causalean.Stat.CLT.BerryEsseen.CDFDifferenceFourierInterval
public import Causalean.Stat.CLT.BerryEsseen.CDFDifferenceFourierKernel
public import Causalean.Stat.CLT.BerryEsseen.CDFDifferenceIntegrable
public import Mathlib.Probability.CentralLimitTheorem

/-! # A Fubini bridge for Fourier transforms of CDF differences

An oriented interval between two observations has signed indicator equal to
the difference of their lower-half-line indicators. Integrating this identity
against two probability laws is the measure-theoretic step in the Fourier
identity for their CDF difference.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory ProbabilityTheory

/-- For a nonzero frequency, the oriented integral of the complex exponential
between two real points equals the difference of their endpoint exponentials
divided by the frequency, with the Fourier sign convention used here. -/
theorem fourier_oriented_interval_identity (a b t : ℝ) (ht : t ≠ 0) :
    (t : ℂ) *
      (∫ x in a..b, Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)) =
        Complex.I *
          (Complex.exp (((t * a : ℝ) : ℂ) * Complex.I) -
            Complex.exp (((t * b : ℝ) : ℂ) * Complex.I)) := by
  have hc : (t : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast ht) Complex.I_ne_zero
  have he :
      (fun x : ℝ => Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)) =
        (fun x : ℝ => Complex.exp (((t : ℂ) * Complex.I) * x)) := by
    funext x
    congr 1
    push_cast
    ring
  rw [he, integral_exp_mul_complex hc]
  push_cast
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  field_simp [htC]
  rw [Complex.I_sq]
  ring

/-- For [two probability laws μ and ν with finite first moments](hyp:hμ,hν),
[the Fourier integral at frequency t of the difference of their CDFs equals
the average, over independent draws a from μ and b from ν, of the oriented
integral of the Fourier exponential from a to b](goal). -/
theorem cdf_difference_fourier_fubini
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun y : ℝ => y) μ)
    (hν : Integrable (fun y : ℝ => y) ν)
    (t : ℝ) :
    (∫ x : ℝ,
      Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
        (((μ (Set.Iic x)).toReal - (ν (Set.Iic x)).toReal : ℝ) : ℂ)) =
      ∫ a : ℝ, ∫ b : ℝ,
        (∫ x in a..b, Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)) ∂ν ∂μ := by
  have htriple := orientedFourierKernel_integrable μ ν hμ hν t
  have hpair : Integrable
      (fun p : (ℝ × ℝ) × ℝ => orientedFourierKernel t p.1.1 p.1.2 p.2)
      ((μ.prod ν).prod volume) := by
    have h := ((measurePreserving_prodAssoc μ ν (volume : Measure ℝ)).integrable_comp_emb
      MeasurableEquiv.prodAssoc.measurableEmbedding).mpr htriple
    simpa [Function.comp_def, MeasurableEquiv.prodAssoc] using h
  have hswap : Integrable
      (fun p : ℝ × (ℝ × ℝ) => orientedFourierKernel t p.2.1 p.2.2 p.1)
      (volume.prod (μ.prod ν)) := by
    simpa [Function.comp_def, Prod.swap] using hpair.swap
  have hfiber : ∀ᵐ x ∂(volume : Measure ℝ),
      Integrable (fun p : ℝ × ℝ => orientedFourierKernel t p.1 p.2 x)
        (μ.prod ν) :=
    (integrable_prod_iff hswap.aestronglyMeasurable).mp hswap |>.1
  calc
    (∫ x : ℝ,
      Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
        (((μ (Set.Iic x)).toReal - (ν (Set.Iic x)).toReal : ℝ) : ℂ)) =
        ∫ x : ℝ, ∫ a : ℝ, ∫ b : ℝ,
          orientedFourierKernel t a b x ∂ν ∂μ := by
          simp_rw [orientedFourierKernel_endpoint_integral μ ν t]
    _ = ∫ x : ℝ, ∫ p : ℝ × ℝ,
          orientedFourierKernel t p.1 p.2 x ∂(μ.prod ν) := by
          apply integral_congr_ae
          filter_upwards [hfiber] with x hx
          exact (integral_prod _ hx).symm
    _ = ∫ p : ℝ × (ℝ × ℝ),
          orientedFourierKernel t p.2.1 p.2.2 p.1
          ∂(volume.prod (μ.prod ν)) :=
          (integral_prod _ hswap).symm
    _ = ∫ p : ℝ × ℝ, ∫ x : ℝ,
          orientedFourierKernel t p.1 p.2 x ∂(volume : Measure ℝ) ∂(μ.prod ν) :=
          integral_prod_symm _ hswap
    _ = ∫ a : ℝ, ∫ b : ℝ, ∫ x : ℝ,
          orientedFourierKernel t a b x ∂(volume : Measure ℝ) ∂ν ∂μ := by
          exact integral_prod _ hpair.integral_prod_left
    _ = ∫ a : ℝ, ∫ b : ℝ,
          (∫ x in a..b, Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)) ∂ν ∂μ := by
          simp_rw [orientedFourierKernel_interval_integral]

end Causalean.Stat.CLT.BerryEsseen
