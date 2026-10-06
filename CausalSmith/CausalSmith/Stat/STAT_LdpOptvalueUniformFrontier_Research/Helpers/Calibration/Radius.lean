module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Calibration.Global

/-!
# Calibration at an arbitrary positive radius

Scaled approximation and finite second-moment bounds for the evaluation polynomial.
The radius is unrestricted relative to the causal parameter cube.
-/

public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier
variable {m d : ℕ}

/-- Assume [the Cai–Low Chebyshev approximation theorem](hyp:hCheb), [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), [the stated ha condition](hyp:ha), [dimension at least two](hyp:hd), [the stated even condition](hyp:hEven), [polynomial degree at least two](hyp:hD), [the stated dm condition](hyp:hDm), and [the stated hx condition](hyp:hx). [The cited approximation scales to every positive window containing the contrast (C5)](goal). -/
-- @node: radius_polynomial_bias_of_gate
lemma radius_polynomial_bias_of_gate (hCheb : CaiLowChebyshevApproximation)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P)
    (eps a : ℝ) (heps : 0 < eps) (ha : 0 < a) (hd : 2 ≤ d)
    (D : ℕ) (hEven : Even D) (hD : 2 ≤ D) (hDm : D ≤ m) (j : Fin d)
    (hx : |contrast P j| ≤ a) :
    abs (blockMean (m := m) P eps (polynomialEstimate eps a D j) - abs (contrast P j)) ≤
      a / (D+1) := by
  rw [blockMean_polynomialEstimate P hP eps a heps ha.ne' hd D hDm j]
  have hunit : contrast P j / a ∈ Set.Icc (-1 : ℝ) 1 := by
    have hx' := abs_le.mp hx
    constructor
    · rw [le_div_iff₀ ha]; linarith [hx'.1]
    · rw [div_le_iff₀ ha]; simpa using hx'.2
  have happ := (hCheb D hEven hD).1 _ hunit
  have hscale : abs (a * (chebyshevAbsPoly D).eval (contrast P j / a) - abs (contrast P j)) =
      a * abs ((chebyshevAbsPoly D).eval (contrast P j / a) - abs (contrast P j / a)) := by
    have heq : a * (chebyshevAbsPoly D).eval (contrast P j / a) - abs (contrast P j) =
        a * ((chebyshevAbsPoly D).eval (contrast P j / a) - abs (contrast P j / a)) := by
      rw [mul_sub, abs_div, abs_of_pos ha, mul_div_cancel₀ _ ha.ne']
    rw [heq, abs_mul, abs_of_pos ha]
  rw [hscale]
  have hpi : (2 : ℝ) ≤ Real.pi := le_trans (by norm_num) Real.pi_gt_three.le
  have hden : (0 : ℝ) < D+1 := by positivity
  have hnum : 2 / (Real.pi * (D+1)) ≤ 1 / (D+1) := by
    rw [div_le_div_iff₀ (by positivity) hden]
    nlinarith
  exact (mul_le_mul_of_nonneg_left (happ.trans hnum) ha.le).trans_eq (by ring)

/-- Assume [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), [the stated ha condition](hyp:ha), [dimension at least two](hyp:hd), [positive block size](hyp:hm), [the stated hm d condition](hyp:hmD), and [the stated hv condition](hyp:hv). [Rescaled moment degrees share one geometric bound, without degree independence](goal). -/
-- @node: radius_scaled_moment_second_bound
lemma radius_scaled_moment_second_bound (P : Measure (FullRecord d))
    [IsProbabilityMeasure P] (hP : CausalModel P) (eps a : ℝ) (heps : 0 < eps)
    (ha : 0 < a) (hd : 2 ≤ d) (hm : 0 < m) (D v : ℕ)
    (hmD : 2*D ≤ m) (hv : v ≤ D) (j : Fin d) :
    blockMean (m := m) P eps (fun z =>
      (a^((1 : ℤ) - (v : ℤ)) * privateMoment (scaledMessages eps z) v j)^2) ≤
      a^2 * (max 1 (((contrast P j)^2 + 2*D*sigmaSquared d m eps) / a^2))^D := by
  have hsigma : 0 ≤ sigmaSquared d m eps := by unfold sigmaSquared; positivity
  have hmom := blockMean_privateMoment_sq_le P hP eps heps hd hm v (by omega) j
  have hscale (x : ℝ) : (a^((1 : ℤ) - (v : ℤ)))^2 * x^v =
      a^2 * (x/a^2)^v := by
    rw [zpow_sub₀ ha.ne', zpow_one, zpow_natCast, div_pow, pow_right_comm, div_pow]
    ring
  have hbase : ((contrast P j)^2 + 2*v*(noiseScale d eps)^2/m) / a^2 ≤
      max 1 (((contrast P j)^2 + 2*D*sigmaSquared d m eps) / a^2) := by
    apply le_trans _ (le_max_right _ _)
    apply div_le_div_of_nonneg_right _ (sq_nonneg a)
    have hvR : (v : ℝ) ≤ D := by exact_mod_cast hv
    have hh := mul_le_mul_of_nonneg_right hvR hsigma
    dsimp only [sigmaSquared] at hh ⊢
    rw [mul_div_assoc]
    nlinarith
  unfold blockMean
  simp_rw [mul_pow]
  rw [integral_const_mul]
  calc
    _ ≤ (a^((1 : ℤ) - (v : ℤ)))^2 *
        ((contrast P j)^2 + 2*v*(noiseScale d eps)^2/m)^v :=
      mul_le_mul_of_nonneg_left hmom (sq_nonneg _)
    _ = _ := hscale _
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg a)
      exact (pow_le_pow_left₀ (by positivity) hbase v).trans
        (pow_le_pow_right₀ (le_max_left _ _) hv)

/-- Assume [the Cai–Low Chebyshev approximation theorem](hyp:hCheb), [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), [the stated ha condition](hyp:ha), [dimension at least two](hyp:hd), [positive block size](hyp:hm), [the stated even condition](hyp:hEven), [polynomial degree at least two](hyp:hD), and [the stated hm d condition](hyp:hmD). [Arbitrary-radius counterpart of C1, with the sharper coefficient factor exp(5D)](goal). -/
-- @node: radius_polynomial_second_bound
lemma radius_polynomial_second_bound (hCheb : CaiLowChebyshevApproximation)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P)
    (eps a : ℝ) (heps : 0 < eps) (ha : 0 < a) (hd : 2 ≤ d) (hm : 0 < m)
    (D : ℕ) (hEven : Even D) (hD : 2 ≤ D) (hmD : 2*D ≤ m) (j : Fin d) :
    blockMean (m := m) P eps (fun z => (polynomialEstimate eps a D j z)^2) ≤
      a^2 * Real.exp (5*D) *
        (max 1 (((contrast P j)^2 + 2*D*sigmaSquared d m eps) / a^2))^D := by
  classical
  letI := vectorBlockLaw_probability P eps m
  let R := (max 1 (((contrast P j)^2 + 2*D*sigmaSquared d m eps) / a^2))^D
  have hterm (v : ℕ) (hv : v ∈ Finset.range (D+1)) :
      blockMean (m := m) P eps (fun z =>
        ((chebyshevAbsPoly D).coeff v * a^((1 : ℤ) - (v : ℤ)) *
          privateMoment (scaledMessages eps z) v j)^2) ≤ Real.exp (3*D) * (a^2 * R) := by
    have hvD : v ≤ D := by have := Finset.mem_range.mp hv; omega
    have hmom := radius_scaled_moment_second_bound P hP eps a heps ha hd hm D v hmD hvD j
    have hc := chebyshev_coefficient_sq_le_exp hCheb D v hEven hD hvD
    have heq : blockMean (m := m) P eps (fun z =>
        ((chebyshevAbsPoly D).coeff v * a^((1 : ℤ) - (v : ℤ)) *
          privateMoment (scaledMessages eps z) v j)^2) =
        ((chebyshevAbsPoly D).coeff v)^2 * blockMean (m := m) P eps (fun z =>
          (a^((1 : ℤ) - (v : ℤ)) * privateMoment (scaledMessages eps z) v j)^2) := by
      unfold blockMean
      simp only [mul_assoc, mul_pow]
      rw [integral_const_mul]
    rw [heq]
    exact mul_le_mul hc hmom (integral_nonneg (fun _ => sq_nonneg _)) (Real.exp_pos _).le
  have hcard : (D+1 : ℝ)^2 ≤ Real.exp (2*D) := by
    have hh : (D+1 : ℝ) ≤ Real.exp D := by linarith [Real.add_one_le_exp (D : ℝ)]
    have hs := mul_le_mul hh hh (by positivity : (0 : ℝ) ≤ D+1) (Real.exp_pos _).le
    rw [← Real.exp_add] at hs
    simpa [← pow_two, two_mul] using hs
  calc
    _ ≤ (D+1 : ℝ) * ∑ v ∈ Finset.range (D+1),
        blockMean P eps (fun z => ((chebyshevAbsPoly D).coeff v *
          a^((1 : ℤ) - (v : ℤ)) * privateMoment (scaledMessages eps z) v j)^2) :=
      blockMean_sum_sq_le P eps D _
    _ ≤ (D+1 : ℝ) * ∑ _v ∈ Finset.range (D+1), Real.exp (3*D) * (a^2 * R) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by positivity)
    _ = (D+1 : ℝ)^2 * Real.exp (3*D) * (a^2 * R) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      ring
    _ ≤ Real.exp (2*D) * Real.exp (3*D) * (a^2 * R) := by
      apply mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le)
      dsimp [R]; positivity
    _ = _ := by
      rw [← Real.exp_add]
      have he : 2*(D : ℝ) + 3*D = 5*D := by ring
      rw [he]
      ring

end CausalSmith.Stat.LdpOptvalueUniformFrontier
