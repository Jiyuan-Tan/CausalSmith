module
public import Causalean.Stat.CLT.BerryEsseen.CDFDifferenceFourierKernel

/-! # Endpoint average of the oriented Fourier kernel

This module evaluates the oriented interval kernel after averaging its two
endpoints over independent probability laws. It is one input to Fubini.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory

/-- For two probability laws μ and ν on the real line,
[averaging the oriented Fourier kernel at frequency t and point x over
independent draws a from μ and b from ν gives the Fourier exponential
exp(itx) times the difference of the two CDFs at x](goal). The weak endpoint
inequalities preserve this identity at atoms. -/
theorem orientedFourierKernel_endpoint_integral
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (t x : ℝ) :
    (∫ a : ℝ, ∫ b : ℝ, orientedFourierKernel t a b x ∂ν ∂μ) =
      Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
        (((μ (Set.Iic x)).toReal - (ν (Set.Iic x)).toReal : ℝ) : ℂ) := by
  /- Expand the kernel and integrate the two bounded indicator functions.
  For each probability law, the integral of `if a ≤ x then 1 else 0`
  equals the real measure of `Set.Iic x`. -/
  let E : ℂ := Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)
  let I : ℝ → ℂ := fun y => if y ≤ x then 1 else 0
  have hIint (ρ : Measure ℝ) [IsProbabilityMeasure ρ] : Integrable I ρ := by
    have h : Integrable ((Set.Iic x).indicator (fun _ : ℝ => (1 : ℂ))) ρ :=
      (integrable_const (μ := ρ) (1 : ℂ)).indicator measurableSet_Iic
    have heq : I = (Set.Iic x).indicator (fun _ : ℝ => (1 : ℂ)) := by
      funext y
      simp [I, Set.indicator_apply, Set.mem_Iic]
    rw [heq]
    exact h
  have hIeval (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
      ∫ y, I y ∂ρ = ((ρ (Set.Iic x)).toReal : ℂ) := by
    rw [show (∫ y, I y ∂ρ) = ∫ y, ((if y ≤ x then 1 else 0 : ℝ) : ℂ) ∂ρ from by
      congr 1; funext y; split_ifs <;> simp [I, *]]
    rw [integral_complex_ofReal]
    have h := integral_indicator_one (μ := ρ) (s := Set.Iic x) measurableSet_Iic
    simpa [Set.indicator_apply, Set.mem_Iic, measureReal_def] using congrArg
      (fun z : ℝ => (z : ℂ)) h
  have hker (a b : ℝ) : orientedFourierKernel t a b x = E * (I a - I b) := by
    by_cases ha : a ≤ x <;> by_cases hb : b ≤ x <;>
      simp [orientedFourierKernel, E, I, ha, hb]
  have hinner (a : ℝ) :
      (∫ b, orientedFourierKernel t a b x ∂ν) =
        E * (I a - ((ν (Set.Iic x)).toReal : ℂ)) := by
    simp_rw [hker]
    rw [integral_const_mul, integral_sub (integrable_const (μ := ν) (I a)) (hIint ν),
      integral_const, hIeval ν]
    simp
  simp_rw [hinner]
  rw [integral_const_mul, integral_sub (hIint μ)
    (integrable_const (μ := μ) (((ν (Set.Iic x)).toReal : ℂ))),
    hIeval μ, integral_const]
  simp [E]

end Causalean.Stat.CLT.BerryEsseen
