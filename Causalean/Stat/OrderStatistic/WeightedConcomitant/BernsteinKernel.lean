module
public import Causalean.Stat.OrderStatistic.WeightedConcomitant.PowerCells
public import Mathlib.Probability.Distributions.Binomial

/-!
# Finite Bernstein cell kernels

The density kernel associated with arbitrary nonnegative cell masses, and its
normalization by the beta integral.

Proof route: use the integer-parameter beta integral to normalize each basis
term. Exchange the finite sum and integral to normalize the mixture.
-/

@[expose] public section

namespace Causalean.Stat.OrderStatistic.WeightedConcomitant

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- For a [sample size](hyp:N), [cell masses](hyp:a), and [evaluation point](hyp:u), the
 [Bernstein cell-average kernel](goal) is the degree `N-1` Bernstein mixture multiplied by `N`. -/
def bernsteinCell (N : ℕ) (a : Fin N → ℝ) (u : ℝ) : ℝ :=
  N * ∑ j : Fin N, a j * (Nat.choose (N - 1) (j : ℕ) : ℝ) *
    u ^ (j : ℕ) * (1 - u) ^ (N - 1 - (j : ℕ))

/-- For [any finite cell masses](hyp:a), [the Bernstein kernel is measurable](goal). -/
theorem measurable_bernsteinCell {N : ℕ} (a : Fin N → ℝ) :
    Measurable (bernsteinCell N a) := by
  unfold bernsteinCell
  fun_prop

/-- For [nonnegative cell masses](hyp:ha) and [a point in the unit interval](hyp:hu),
 [the Bernstein kernel is nonnegative](goal). -/
theorem bernsteinCell_nonneg {N : ℕ} {a : Fin N → ℝ}
    (ha : ∀ j, 0 ≤ a j) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ bernsteinCell N a u := by
  unfold bernsteinCell
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (mul_nonneg (mul_nonneg (ha j) (by positivity))
    (pow_nonneg hu.1 _)) (pow_nonneg (sub_nonneg.mpr hu.2) _)

/-- For a [positive sample size](hyp:hN) and [cell index](hyp:j),
 [the Bernstein basis density associated with that cell integrates to one](goal). -/
theorem integral_bernstein_basis {N : ℕ} (hN : 0 < N) (j : Fin N) :
    (∫ u in Set.Icc (0 : ℝ) 1,
      (N : ℝ) * (Nat.choose (N - 1) (j : ℕ) : ℝ) *
        u ^ (j : ℕ) * (1 - u) ^ (N - 1 - (j : ℕ)) ∂volume) = 1 := by
  let k := N - 1 - (j : ℕ)
  have hj : (j : ℕ) ≤ N - 1 := by omega
  have hsum : (j : ℕ) + k + 1 = N := by dsimp [k]; omega
  have hbeta :
      (∫ u in (0 : ℝ)..1, ((u ^ (j : ℕ) * (1 - u) ^ k : ℝ) : ℂ)) =
        Complex.betaIntegral ((j : ℕ) + 1) (k + 1) := by
    rw [Complex.betaIntegral]
    apply intervalIntegral.integral_congr
    intro u hu
    have hu0 : 0 ≤ u := by simpa using hu.1
    have hu1 : u ≤ 1 := by simpa using hu.2
    dsimp
    simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_sub,
      Complex.ofReal_one]
    simp [Complex.cpow_natCast]
  have heval := Complex.betaIntegral_eq_Gamma_mul_div
    ((j : ℕ) + 1) (k + 1)
    (by simp only [Complex.add_re, Complex.natCast_re, Complex.one_re]; positivity)
    (by simp only [Complex.add_re, Complex.natCast_re, Complex.one_re]; positivity)
  rw [← hbeta] at heval
  have hg1 : Complex.Gamma ((j : ℕ) + 1) = ((j : ℕ).factorial : ℂ) := by
    simpa using Complex.Gamma_nat_eq_factorial (j : ℕ)
  have hg2 : Complex.Gamma (k + 1) = (k.factorial : ℂ) := by
    simpa using Complex.Gamma_nat_eq_factorial k
  have hg3 : Complex.Gamma (((j : ℕ) + 1) + (k + 1)) = (N.factorial : ℂ) := by
    have harg : ((j : ℕ) : ℂ) + 1 + ((k : ℕ) : ℂ) + 1 = (N : ℂ) + 1 := by
      exact_mod_cast (show (j : ℕ) + 1 + k + 1 = N + 1 by omega)
    rw [← add_assoc, harg]
    exact Complex.Gamma_nat_eq_factorial N
  rw [hg1, hg2, hg3, intervalIntegral.integral_ofReal] at heval
  have hreal : (∫ u in (0 : ℝ)..1, u ^ (j : ℕ) * (1 - u) ^ k) =
      (j : ℕ).factorial * k.factorial / N.factorial := by
    exact Complex.ofReal_inj.mp (by simpa using heval)
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc] at hreal
  rw [show N - 1 - (j : ℕ) = k from rfl]
  simp_rw [mul_assoc]
  rw [integral_const_mul, integral_const_mul, hreal]
  have hchoose : (Nat.choose (N - 1) (j : ℕ) : ℝ) *
      (j : ℕ).factorial * k.factorial = (N - 1).factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hj
  have hfac : (N.factorial : ℝ) = N * (N - 1).factorial := by
    have : N - 1 + 1 = N := by omega
    rw [← this, Nat.factorial_succ]
    push_cast
    congr 1
  rw [hfac]
  field_simp
  nlinarith [hchoose]

/-- For a [positive sample size](hyp:hN), [cell masses](hyp:a) with [unit sum](hyp:hsum),
 [the Bernstein kernel integrates to one on the unit interval](goal). -/
theorem integral_bernsteinCell {N : ℕ} (hN : 0 < N) (a : Fin N → ℝ)
    (hsum : ∑ j : Fin N, a j = 1) :
    ∫ u in Set.Icc (0 : ℝ) 1, bernsteinCell N a u ∂volume = 1 := by
  have hint (j : Fin N) : IntegrableOn
      (fun u : ℝ => a j * ((N : ℝ) * (Nat.choose (N - 1) (j : ℕ) : ℝ) *
        u ^ (j : ℕ) * (1 - u) ^ (N - 1 - (j : ℕ))))
      (Set.Icc (0 : ℝ) 1) volume := by
    apply Continuous.integrableOn_Icc
    fun_prop
  calc
    (∫ u in Set.Icc (0 : ℝ) 1, bernsteinCell N a u ∂volume) =
        ∫ u in Set.Icc (0 : ℝ) 1, ∑ j : Fin N,
          a j * ((N : ℝ) * (Nat.choose (N - 1) (j : ℕ) : ℝ) *
            u ^ (j : ℕ) * (1 - u) ^ (N - 1 - (j : ℕ))) ∂volume := by
      congr 1
      funext u
      simp only [bernsteinCell, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ j : Fin N, a j := by
      rw [integral_finsetSum (s := Finset.univ) (fun j hj => hint j)]
      apply Finset.sum_congr rfl
      intro j hj
      rw [integral_const_mul, integral_bernstein_basis hN j, mul_one]
    _ = 1 := hsum

end
end Causalean.Stat.OrderStatistic.WeightedConcomitant
