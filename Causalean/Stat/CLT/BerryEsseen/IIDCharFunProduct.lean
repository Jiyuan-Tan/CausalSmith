module
public import Mathlib.Probability.CentralLimitTheorem
public import Mathlib.Probability.Independence.CharacteristicFunction

/-! # Characteristic function of an iid finite sum

This module isolates the finite-product identity used by the scalar
Berry–Esseen argument. No moment bound or asymptotic assertion is needed.
-/

public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory ProbabilityTheory

/-- [Under the n-fold product of a real probability law, the characteristic
function of the coordinate sum at frequency t is the n-th power of the
one-coordinate characteristic function at t](goal). -/
theorem iid_sum_charFun_product
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (n : ℕ) (t : ℝ) :
    (∫ v : Fin n → ℝ,
      Complex.exp (((t * (∑ i : Fin n, v i) : ℝ) : ℂ) * Complex.I)
        ∂(Measure.pi (fun _ : Fin n => μ))) =
      (charFun μ t) ^ n := by
  /- Identify the integral with the characteristic function of the sum law,
  then apply the finite-product identity, including the empty product. -/
  have hsum : Measurable (fun v : Fin n → ℝ => ∑ i, v i) := by fun_prop
  have hchar :
      (∫ v : Fin n → ℝ,
        Complex.exp (((t * (∑ i : Fin n, v i) : ℝ) : ℂ) * Complex.I)
          ∂(Measure.pi (fun _ : Fin n => μ))) =
        charFun ((Measure.pi (fun _ : Fin n => μ)).map
          (fun v => ∑ i, v i)) t := by
    rw [charFun_apply_real, integral_map hsum.aemeasurable (by fun_prop)]
    congr 1
    funext v
    congr 1
    push_cast
    ring
  rw [hchar]
  simpa using
    congrFun (ProbabilityTheory.charFun_map_sum_pi_eq_prod
      (fun _ : Fin n => μ)) t

end Causalean.Stat.CLT.BerryEsseen
