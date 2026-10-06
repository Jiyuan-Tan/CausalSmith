module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.CitedGates
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.MomentDependence.Covariance
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.RateAlgebra
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Helpers/Calibration/Global

Finite original-record private value frontiers: Helpers/Calibration/Global.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

namespace CausalSmith.Stat.LdpOptvalueUniformFrontier


variable {n m d : ℕ}
/-- Fix [the privacy budget and the amplitude](hyp:eps,a), [the natural-number parameter D](hyp:D), [the coordinate index](hyp:j), and [the function z](hyp:z). [Scaled explicit polynomial, lifted through distinct-person moments](goal). -/
def polynomialEstimate (eps a : ℝ) (D : ℕ) (j : Fin d)
    (z : Fin m → Fin d → Bool) : ℝ :=
  ∑ v ∈ Finset.range (D+1), (chebyshevAbsPoly D).coeff v *
    a^((1 : ℤ) - (v : ℤ)) * privateMoment (scaledMessages eps z) v j
/-- Fix [the dimension and the block size](hyp:d,m) and [the privacy budget](hyp:eps). [Squared-noise scale for one evaluation block](goal). -/
def sigmaSquared (d m : ℕ) (eps : ℝ) : ℝ := (noiseScale d eps)^2 / m
/-- [The explicit truncated Chebyshev approximation has no coefficients above its degree](goal). -/
-- @node: chebyshevAbsPoly_natDegree_le
lemma chebyshevAbsPoly_natDegree_le (D : ℕ) : (chebyshevAbsPoly D).natDegree ≤ D := by
  unfold chebyshevAbsPoly
  apply Polynomial.natDegree_add_le_of_degree_le
  · simp
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro v hv
    apply (Polynomial.natDegree_C_mul_le _ _).trans
    rw [Polynomial.Chebyshev.natDegree_T]
    have hvD := (Finset.mem_Icc.mp hv).2
    norm_cast
    omega

/-- Assume [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), [the stated ha condition](hyp:ha), [dimension at least two](hyp:hd), and [the stated dm condition](hyp:hDm). [Moment unbiasedness evaluates the finite polynomial at the true scaled contrast](goal). -/
-- @node: blockMean_polynomialEstimate
lemma blockMean_polynomialEstimate (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (hP : CausalModel P) (eps a : ℝ) (heps : 0 < eps) (ha : a ≠ 0)
    (hd : 2 ≤ d) (D : ℕ) (hDm : D ≤ m) (j : Fin d) :
    blockMean (m := m) P eps (polynomialEstimate eps a D j) =
      a * (chebyshevAbsPoly D).eval (contrast P j / a) := by
  classical
  letI := vectorBlockLaw_probability P eps m
  unfold blockMean polynomialEstimate
  rw [integral_finset_sum _ (fun _ _ => Integrable.of_finite)]
  simp_rw [integral_const_mul]
  have hmom : ∀ v ∈ Finset.range (D+1),
      (∫ z, privateMoment (scaledMessages eps z) v j ∂vectorBlockLaw P eps m) =
        (contrast P j)^v := by
    intro v hv
    change blockMean P eps (fun z => privateMoment (scaledMessages eps z) v j) = _
    rw [blockMean_privateMoment_eq_rowMean_pow P eps v (by
      have := Finset.mem_range.mp hv
      omega) j, vectorMessageLaw_scaled_sign_integral P hP eps heps hd j]
  rw [Finset.sum_congr rfl (fun v hv => congrArg
    (fun x => (chebyshevAbsPoly D).coeff v * a ^ ((1 : ℤ) - (v : ℤ)) * x) (hmom v hv))]
  rw [Polynomial.eval_eq_sum_range' (n := D+1) (by
    have := chebyshevAbsPoly_natDegree_le D
    omega), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  rw [zpow_sub₀ ha, zpow_one, zpow_natCast, div_pow]
  ring

/-- Assume [the Cai–Low Chebyshev approximation theorem](hyp:hCheb), [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), [dimension at least two](hyp:hd), [the stated even condition](hyp:hEven), [polynomial degree at least two](hyp:hD), and [the stated dm condition](hyp:hDm). [On the global radius one half, the cited approximation controls the bias](goal). -/
-- @node: global_polynomial_bias_of_gate
lemma global_polynomial_bias_of_gate (hCheb : CaiLowChebyshevApproximation)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P)
    (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d)
    (D : ℕ) (hEven : Even D) (hD : 2 ≤ D) (hDm : D ≤ m) (j : Fin d) :
    abs (blockMean (m := m) P eps (polynomialEstimate eps (1/2) D j) -
      abs (contrast P j)) ≤ 1/(D+1) := by
  rw [blockMean_polynomialEstimate P hP eps (1/2) heps (by norm_num) hd D hDm j]
  have hx := contrast_mem_parameterCube P hP j
  have happ := (hCheb D hEven hD).1 (contrast P j / (1/2)) (by
    constructor <;> norm_num <;> linarith [hx.1, hx.2])
  have habs : abs (contrast P j / (1/2)) = 2 * abs (contrast P j) := by
    rw [div_eq_mul_inv, abs_mul]
    norm_num
    ring
  rw [habs] at happ
  have hfactor : abs ((1/2 : ℝ) * (chebyshevAbsPoly D).eval
      (contrast P j / (1/2)) - abs (contrast P j)) =
      (1/2 : ℝ) * abs ((chebyshevAbsPoly D).eval
        (contrast P j / (1/2)) - 2 * abs (contrast P j)) := by
    rw [← abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2), ← abs_mul]
    congr 1
    ring
  rw [hfactor]
  have hden : (0 : ℝ) < D+1 := by positivity
  have hpi : (1 : ℝ) ≤ Real.pi := le_trans (by norm_num) (Real.pi_gt_three).le
  have hnum : 2 / (Real.pi * (D+1)) ≤ 2 / (D+1) := by
    apply div_le_div_of_nonneg_left (by norm_num) hden
    nlinarith
  calc
    _ ≤ (1/2 : ℝ) * (2 / (D+1)) := mul_le_mul_of_nonneg_left
      (happ.trans hnum) (by norm_num)
    _ = _ := by ring

/-- [Finite Cauchy--Schwarz controls a sum of possibly dependent statistics](goal). -/
-- @node: blockMean_sum_sq_le
lemma blockMean_sum_sq_le (P : Measure (FullRecord d)) [IsProbabilityMeasure P]
    (eps : ℝ) (D : ℕ) (f : ℕ → (Fin m → Fin d → Bool) → ℝ) :
    blockMean P eps (fun z => (∑ v ∈ Finset.range (D+1), f v z)^2) ≤
      (D+1 : ℝ) * ∑ v ∈ Finset.range (D+1), blockMean P eps (fun z => (f v z)^2) := by
  letI := vectorBlockLaw_probability P eps m
  unfold blockMean
  calc
    _ ≤ ∫ z, (D+1 : ℝ) * ∑ v ∈ Finset.range (D+1), (f v z)^2
        ∂vectorBlockLaw P eps m := by
      apply integral_mono (Integrable.of_finite) (Integrable.of_finite)
      intro z
      simpa using Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (D+1))
        (fun _ => (1 : ℝ)) (fun v => f v z)
    _ = _ := by
      rw [integral_const_mul, integral_finset_sum _ (fun _ _ => Integrable.of_finite)]

/-- Assume [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), [dimension at least two](hyp:hd), [positive block size](hyp:hm), [the stated hm d condition](hyp:hmD), and [the stated hv condition](hyp:hv). [Half-radius rescaling converts the private moment bound to a common geometric bound](goal). -/
-- @node: global_scaled_moment_second_bound
lemma global_scaled_moment_second_bound (P : Measure (FullRecord d))
    [IsProbabilityMeasure P] (hP : CausalModel P) (eps : ℝ) (heps : 0 < eps)
    (hd : 2 ≤ d) (hm : 0 < m) (D v : ℕ) (hmD : 2*D ≤ m) (hv : v ≤ D)
    (j : Fin d) :
    blockMean (m := m) P eps (fun z =>
      ((1/2 : ℝ)^((1 : ℤ) - (v : ℤ)) * privateMoment (scaledMessages eps z) v j)^2) ≤
      (1/4 : ℝ) * (1 + 8*D*sigmaSquared d m eps)^D := by
  have hsigma : 0 ≤ sigmaSquared d m eps := by unfold sigmaSquared; positivity
  have hx := contrast_mem_parameterCube P hP j
  have hx2 : (contrast P j)^2 ≤ (1/4 : ℝ) := by
    nlinarith [hx.1, hx.2]
  have hmom := blockMean_privateMoment_sq_le P hP eps heps hd hm v (by omega) j
  have hscale (x : ℝ) : ((1/2 : ℝ)^((1 : ℤ) - (v : ℤ)))^2 * x^v =
      (1/4 : ℝ) * (4*x)^v := by
    rw [zpow_sub₀ (by norm_num : (1/2 : ℝ) ≠ 0), zpow_one, zpow_natCast,
      div_pow, pow_right_comm]
    norm_num
    rw [div_mul_eq_mul_div, mul_div_assoc, ← div_pow]
    congr 1
    congr 1
    ring
  have hbase : 4*((contrast P j)^2 + 2*v*(noiseScale d eps)^2/m) ≤
      1 + 8*D*sigmaSquared d m eps := by
    have hvR : (v : ℝ) ≤ D := by exact_mod_cast hv
    rw [mul_div_assoc]
    dsimp only [sigmaSquared] at hsigma ⊢
    nlinarith [mul_le_mul_of_nonneg_right hvR hsigma]
  have hnonneg : 0 ≤ 4*((contrast P j)^2 + 2*v*(noiseScale d eps)^2/m) := by positivity
  have hone : 1 ≤ 1 + 8*D*sigmaSquared d m eps := by
    linarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 8*D) hsigma]
  unfold blockMean
  simp_rw [mul_pow]
  rw [integral_const_mul]
  change _ ≤ _
  calc
    _ ≤ ((1/2 : ℝ)^((1 : ℤ) - (v : ℤ)))^2 *
        ((contrast P j)^2 + 2*v*(noiseScale d eps)^2/m)^v :=
      mul_le_mul_of_nonneg_left hmom (sq_nonneg _)
    _ = _ := hscale _
    _ ≤ (1/4 : ℝ) * (1 + 8*D*sigmaSquared d m eps)^D := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact (pow_le_pow_left₀ hnonneg hbase v).trans (pow_le_pow_right₀ hone hv)

/-- Assume [the Cai–Low Chebyshev approximation theorem](hyp:hCheb), [the stated even condition](hyp:hEven), [polynomial degree at least two](hyp:hD), and [the stated hv condition](hyp:hv). [The cited coefficient bound has a convenient squared exponential form](goal). -/
-- @node: chebyshev_coefficient_sq_le_exp
lemma chebyshev_coefficient_sq_le_exp (hCheb : CaiLowChebyshevApproximation)
    (D v : ℕ) (hEven : Even D) (hD : 2 ≤ D) (hv : v ≤ D) :
    ((chebyshevAbsPoly D).coeff v)^2 ≤ Real.exp (3*D) := by
  have hc := (hCheb D hEven hD).2 v hv
  have hlog : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  rw [Real.rpow_def_of_pos (by norm_num)] at hc
  have hc' : |(chebyshevAbsPoly D).coeff v| ≤ Real.exp (3*D/2) :=
    hc.trans (Real.exp_le_exp.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) D]))
  have hs := mul_le_mul hc' hc' (abs_nonneg _) (Real.exp_pos _).le
  rw [← pow_two, sq_abs, ← Real.exp_add] at hs
  have he : 3*(D : ℝ)/2 + 3*D/2 = 3*D := by ring
  rw [he] at hs
  exact hs

/-- Assume [the Cai–Low Chebyshev approximation theorem](hyp:hCheb), [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), [dimension at least two](hyp:hd), [positive block size](hyp:hm), [the stated even condition](hyp:hEven), [polynomial degree at least two](hyp:hD), and [the stated hm d condition](hyp:hmD). [A finite polynomial second moment uses no independence between moment degrees](goal). -/
-- @node: global_polynomial_second_bound
lemma global_polynomial_second_bound (hCheb : CaiLowChebyshevApproximation)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P)
    (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d) (hm : 0 < m)
    (D : ℕ) (hEven : Even D) (hD : 2 ≤ D) (hmD : 2*D ≤ m) (j : Fin d) :
    blockMean (m := m) P eps (fun z => (polynomialEstimate eps (1/2) D j z)^2) ≤
      (1/4 : ℝ) * Real.exp (5*D) * (1 + 8*D*sigmaSquared d m eps)^D := by
  classical
  letI := vectorBlockLaw_probability P eps m
  have hsigma : 0 ≤ sigmaSquared d m eps := by unfold sigmaSquared; positivity
  have hterm (v : ℕ) (hv : v ∈ Finset.range (D+1)) :
      blockMean (m := m) P eps (fun z =>
        ((chebyshevAbsPoly D).coeff v * (1/2 : ℝ)^((1 : ℤ) - (v : ℤ)) *
          privateMoment (scaledMessages eps z) v j)^2) ≤
        Real.exp (3*D) * ((1/4 : ℝ) * (1 + 8*D*sigmaSquared d m eps)^D) := by
    have hvD : v ≤ D := by have := Finset.mem_range.mp hv; omega
    have hmoment := global_scaled_moment_second_bound P hP eps heps hd hm D v hmD hvD j
    have hc := chebyshev_coefficient_sq_le_exp hCheb D v hEven hD hvD
    have heq : blockMean (m := m) P eps (fun z =>
        ((chebyshevAbsPoly D).coeff v * (1/2 : ℝ)^((1 : ℤ) - (v : ℤ)) *
          privateMoment (scaledMessages eps z) v j)^2) =
        ((chebyshevAbsPoly D).coeff v)^2 * blockMean (m := m) P eps (fun z =>
          ((1/2 : ℝ)^((1 : ℤ) - (v : ℤ)) * privateMoment (scaledMessages eps z) v j)^2) := by
      unfold blockMean
      simp only [mul_assoc, mul_pow]
      rw [integral_const_mul]
    rw [heq]
    exact mul_le_mul hc hmoment (integral_nonneg (fun _ => sq_nonneg _)) (Real.exp_pos _).le
  have hcard : (D+1 : ℝ)^2 ≤ Real.exp (2*D) := by
    have hh : (D+1 : ℝ) ≤ Real.exp D := by
      linarith [Real.add_one_le_exp (D : ℝ)]
    have hs := mul_le_mul hh hh (by positivity : (0 : ℝ) ≤ D+1) (Real.exp_pos _).le
    rw [← Real.exp_add] at hs
    simpa [← pow_two, two_mul] using hs
  calc
    _ ≤ (D+1 : ℝ) * ∑ v ∈ Finset.range (D+1),
        blockMean P eps (fun z => ((chebyshevAbsPoly D).coeff v *
          (1/2 : ℝ)^((1 : ℤ) - (v : ℤ)) * privateMoment (scaledMessages eps z) v j)^2) :=
      blockMean_sum_sq_le P eps D _
    _ ≤ (D+1 : ℝ) * ∑ _v ∈ Finset.range (D+1),
        Real.exp (3*D) * ((1/4 : ℝ) * (1 + 8*D*sigmaSquared d m eps)^D) := by
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by positivity)
    _ = (D+1 : ℝ)^2 * Real.exp (3*D) *
        ((1/4 : ℝ) * (1 + 8*D*sigmaSquared d m eps)^D) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      ring
    _ ≤ Real.exp (2*D) * Real.exp (3*D) *
        ((1/4 : ℝ) * (1 + 8*D*sigmaSquared d m eps)^D) := by
      gcongr
    _ = _ := by
      rw [← Real.exp_add]
      have he : 2*(D : ℝ) + 3*D = 5*D := by ring
      rw [he]
      ring

/-- Assume [dimension at least two](hyp:hd) and [the stated degree condition](hyp:hDegree). [The degree restriction converts the geometric second-moment bound to the paper's exponent](goal). -/
-- @node: global_calibration_exponential_bound
lemma global_calibration_exponential_bound (d m D : ℕ) (eps : ℝ) (hd : 2 ≤ d)
    (hDegree : (D : ℝ) ≤ (1/1024 : ℝ) * logDim d /
      Real.log (Real.exp 1 + sigmaSquared d m eps * logDim d)) :
    Real.exp (5*D) * (1 + 8*D*sigmaSquared d m eps)^D ≤
      Real.exp (9*D*Real.log (Real.exp 1 + sigmaSquared d m eps * logDim d)) := by
  let H := Real.log (Real.exp 1 + sigmaSquared d m eps * logDim d)
  have hL := (logDim_bounds d hd).1
  have hsigma : 0 ≤ sigmaSquared d m eps := by unfold sigmaSquared; positivity
  have harg : Real.exp 1 ≤ Real.exp 1 + sigmaSquared d m eps * logDim d := by
    nlinarith
  have hH : 1 ≤ H := by
    have := Real.log_le_log (Real.exp_pos 1) harg
    simpa [H] using this
  have hDL : (D : ℝ) ≤ logDim d := by
    have hh := (le_div_iff₀ (show 0 < H by linarith)).mp hDegree
    have hDH : (D : ℝ) ≤ D*H := by nlinarith [Nat.cast_nonneg (α := ℝ) D]
    linarith
  have heH : Real.exp H = Real.exp 1 + sigmaSquared d m eps * logDim d := by
    exact Real.exp_log ((Real.exp_pos 1).trans_le harg)
  have he1 : 1 ≤ Real.exp 1 := (Real.one_le_exp_iff).mpr (by norm_num)
  have hbase : 1 + 8*D*sigmaSquared d m eps ≤ 8*Real.exp H := by
    rw [heH]
    nlinarith [mul_le_mul_of_nonneg_right hDL hsigma]
  have h8 : (8 : ℝ) ≤ Real.exp 3 := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by
      linarith [Real.add_one_le_exp (1 : ℝ)]
    have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2 3
    rw [← Real.exp_nat_mul] at hpow
    norm_num at hpow ⊢
    exact hpow
  have h8H : (8 : ℝ) ≤ Real.exp (3*H) :=
    h8.trans (Real.exp_le_exp.mpr (by linarith))
  have hbase' : 1 + 8*D*sigmaSquared d m eps ≤ Real.exp (4*H) := by
    calc
      _ ≤ 8*Real.exp H := hbase
      _ ≤ Real.exp (3*H) * Real.exp H :=
        mul_le_mul_of_nonneg_right h8H (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hpow : (1 + 8*D*sigmaSquared d m eps)^D ≤ Real.exp (4*D*H) := by
    have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤
      1 + 8*D*sigmaSquared d m eps) hbase' D
    rw [← Real.exp_nat_mul] at hh
    have he : (D : ℝ) * (4*H) = 4*D*H := by ring
    rwa [he] at hh
  calc
    _ ≤ Real.exp (5*D) * Real.exp (4*D*H) :=
      mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
    _ = Real.exp (5*D + 4*D*H) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (9*D*H) := by
      apply Real.exp_le_exp.mpr
      nlinarith [Nat.cast_nonneg (α := ℝ) D]

/-- Assume [the Cai–Low Chebyshev approximation theorem](hyp:hCheb), [the causal-model conditions for the data law](hyp:hP), [a positive privacy budget](hyp:heps), [dimension at least two](hyp:hd), [positive block size](hyp:hm), [the stated even condition](hyp:hEven), [polynomial degree at least two](hyp:hD), [the stated hm d condition](hyp:hmD), and [the stated degree condition](hyp:hDegree). [The global polynomial's second moment is at most one quarter of the calibrated exponent](goal). -/
-- @node: global_polynomial_second_calibrated
lemma global_polynomial_second_calibrated (hCheb : CaiLowChebyshevApproximation)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P)
    (eps : ℝ) (heps : 0 < eps) (hd : 2 ≤ d) (hm : 0 < m)
    (D : ℕ) (hEven : Even D) (hD : 2 ≤ D) (hmD : 2*D ≤ m)
    (hDegree : (D : ℝ) ≤ (1/1024 : ℝ) * logDim d /
      Real.log (Real.exp 1 + sigmaSquared d m eps * logDim d)) (j : Fin d) :
    blockMean (m := m) P eps (fun z => (polynomialEstimate eps (1/2) D j z)^2) ≤
      (1/4 : ℝ) * Real.exp (9*D*Real.log (Real.exp 1 + sigmaSquared d m eps * logDim d)) := by
  refine (global_polynomial_second_bound hCheb P hP eps heps hd hm D hEven hD hmD j).trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (global_calibration_exponential_bound d m D eps hd hDegree) (by norm_num)

/-- Assume [the Cai–Low Chebyshev approximation theorem](hyp:hCheb_of_gate), [the bounded-mean concentration inequality](hyp:hMean_of_gate), [independent and identically distributed participant records](hyp:hIID), [the causal-model conditions for the data law](hyp:hP), [an admissible sample size, dimension, and privacy budget](hyp:hAllowed), [positive block size](hyp:hm), [a block no larger than the sample](hyp:hmn), [the stated even condition](hyp:hEven), [polynomial degree at least two](hyp:hD), [the stated hm d condition](hyp:hmD), and [the stated degree condition](hyp:hDegree). [Global-radius calibration from the explicit approximation and bounded-mean gates](goal). -/
-- @node: global_polynomial_calibration_of_gate
lemma global_polynomial_calibration_of_gate
    (hCheb_of_gate : CaiLowChebyshevApproximation) (hMean_of_gate : BoundedMeanConcentration)
    (S : SamplingScheme n d) (hIID : IidPeople S)
    (P : Measure (FullRecord d)) [IsProbabilityMeasure P] (hP : CausalModel P)
    (eps : ℝ) (hAllowed : Allowed n d eps) (hm : 0 < m) (hmn : m ≤ n)
    (D : ℕ) (hEven : Even D) (hD : 2 ≤ D) (hmD : 2*D ≤ m)
    (hDegree : (D : ℝ) ≤ (1/1024 : ℝ) * logDim d /
      Real.log (Real.exp 1 + sigmaSquared d m eps * logDim d)) :
    (∀ j : Fin d, abs (blockMean (m := m) P eps (polynomialEstimate eps (1/2) D j) - abs
      (contrast P j)) ≤
      1/(D+1)) ∧
    blockVar (m := m) P eps (fun z => (d : ℝ)⁻¹ * ∑ j, polynomialEstimate eps (1/2) D j z) ≤
      Real.exp (9*D*Real.log (Real.exp 1 + sigmaSquared d m eps * logDim d))/(2*d) := by
  constructor
  · intro j
    exact global_polynomial_bias_of_gate hCheb_of_gate P hP eps hAllowed.2.2.1
      hAllowed.2.1 D hEven hD (by omega) j
  · classical
    letI := vectorBlockLaw_probability P eps m
    let E := Real.exp (9*D*Real.log (Real.exp 1 + sigmaSquared d m eps * logDim d))
    let g : Fin d → (Fin m → ℝ) → ℝ := fun j w =>
      ∑ v ∈ Finset.range (D+1), (chebyshevAbsPoly D).coeff v *
        (1/2 : ℝ)^((1 : ℤ) - (v : ℤ)) * privateMoment (fun i _ => w i) v j
    have hg : ∀ j, Measurable (g j) := by
      intro j
      dsimp only [g]
      unfold privateMoment
      fun_prop
    have hcol : columnStatistic eps g = fun j => polynomialEstimate eps (1/2) D j := by
      funext j z
      unfold columnStatistic polynomialEstimate g privateMoment
      rfl
    have hvar (j : Fin d) : blockVar (m := m) P eps (polynomialEstimate eps (1/2) D j) ≤
        (1/4 : ℝ)*E := by
      calc
        _ ≤ blockMean P eps (fun z => (polynomialEstimate eps (1/2) D j z)^2) := by
          rw [blockVar_eq_variance]
          exact variance_le_expectation_sq (by fun_prop)
        _ ≤ _ := global_polynomial_second_calibrated hCheb_of_gate P hP eps
          hAllowed.2.2.1 hAllowed.2.1 hm D hEven hD hmD hDegree j
    have hmax : sSup (Set.range (fun j : Fin d =>
        blockVar (m := m) P eps (polynomialEstimate eps (1/2) D j))) ≤ (1/4 : ℝ)*E := by
      apply csSup_le
      · have hdpos : 0 < d := by have := hAllowed.2.1; omega
        exact ⟨_, Set.mem_range_self (⟨0, hdpos⟩ : Fin d)⟩
      · rintro _ ⟨j,rfl⟩
        exact hvar j
    have hdep := (private_moment_and_dependence S hIID P hP eps hAllowed.2.2
      hAllowed.2.1 hm hmn).2.2.2.2.2 g hg
    rw [hcol] at hdep
    calc
      _ ≤ (2/(d : ℝ)) * sSup (Set.range (fun j : Fin d =>
          blockVar (m := m) P eps (polynomialEstimate eps (1/2) D j))) := hdep.2
      _ ≤ (2/(d : ℝ)) * ((1/4 : ℝ)*E) :=
        mul_le_mul_of_nonneg_left hmax (by positivity)
      _ = E/(2*d) := by ring


end CausalSmith.Stat.LdpOptvalueUniformFrontier
