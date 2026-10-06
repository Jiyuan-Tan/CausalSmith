module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Basic
public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Causalean.Stat.UStatistic.OrderM.Basic
public import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.ChebyshevCertificate
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.PoissonFallingFactorial
public import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Helpers.FactorialRisk

/-! Chebyshev continuations and their explicit factorial-moment calibration. -/

@[expose] public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

open Polynomial ProbabilityTheory MeasureTheory
open scoped BigOperators

/-- The shifted Chebyshev polynomial `Q_L(z)=T_L(1-2z)`.  [the stated conditions](hyp:L) [the stated conclusion](goal). -/
noncomputable def chebQ (L : Nat) : Polynomial Real :=
  (Polynomial.Chebyshev.T Real L).comp (1 - 2 * Polynomial.X)

/-- Polynomial continuation of `(1-Q_L)/(2L²)`.  [the stated conditions](hyp:L) [the stated conclusion](goal). -/
noncomputable def chebH (L : Nat) : Polynomial Real :=
  (2 * (L : Real) ^ 2)⁻¹ • (1 - chebQ L)

/-- Polynomial continuation of `H_L(z)/z`.  [the stated conditions](hyp:L) [the stated conclusion](goal). -/
noncomputable def chebE (L : Nat) : Polynomial Real :=
  (chebH L).divByMonic Polynomial.X

/-- Polynomial continuation of `(1-E_L(z))/z`.  [the stated conditions](hyp:L) [the stated conclusion](goal). -/
noncomputable def chebG (L : Nat) : Polynomial Real :=
  (1 - chebE L).divByMonic Polynomial.X

/-- Coefficient ℓ¹ norm of a real polynomial.  [the stated conditions](hyp:p) [the stated conclusion](goal). -/
noncomputable def coefficientL1 (p : Polynomial Real) : Real :=
  ∑ i ∈ p.support, |p.coeff i|

/-- Coefficientwise bivariate falling-factorial lift of
`(s₀+s₁)G_L(s_a/B)/B`.  Each monomial is lifted separately, so the
same-arm contribution uses `(K_a)_{j+1}` rather than `K_a (K_a)_j`.  [the stated conditions](hyp:a,L,B,t,k0,k1) [the stated conclusion](goal). -/
noncomputable def factorialLift (a : Bool) (L : Nat) (B t : Real)
    (k0 k1 : Nat) : Real :=
  ∑ j ∈ (chebG L).support,
    let ka := if a then k1 else k0
    let kb := if a then k0 else k1
    (chebG L).coeff j *
      ((((ka.descFactorial (j + 1) : Nat) : Real) +
          (kb : Real) * ((ka.descFactorial j : Nat) : Real)) /
        (t * B) ^ (j + 1))

/-- The explicit second moment under independent Poisson cell counts.  [the stated conditions](hyp:a,L,B,t,s0,s1) [the stated conclusion](goal). -/
noncomputable def factorialLiftSecondMoment (a : Bool) (L : Nat)
    (B t s0 s1 : Real) : Real :=
  ∫ K : Nat × Nat, factorialLift a L B t K.1 K.2 ^ 2 ∂
    (poissonMeasure (Real.toNNReal (t * s0))).prod
      (poissonMeasure (Real.toNNReal (t * s1)))

/-- All coefficient, factorial-moment, and interval inequalities (C7)--(C9).  [the stated conditions](hyp:L) [the stated conclusion](goal). -/
def ChebyshevCalibration (L : Nat) : Prop :=
  coefficientL1 (chebQ L) ≤ 7 ^ L ∧
  2 * coefficientL1 (chebG L) ≤ 14 ^ L ∧
  (∀ (a : Bool) (t B s0 s1 : Real),
    0 < t → 0 < B → 0 ≤ s0 → 0 ≤ s1 → (L : Real) ≤ t * B →
    let p := s0 + s1
    factorialLiftSecondMoment a L B t s0 s1 ≤
      (7056 : Real) ^ L * (1 + p / B) ^ (2 * L) ∧
    (p ≤ B → factorialLiftSecondMoment a L B t s0 s1 ≤ (7056 : Real) ^ L)) ∧
  ∀ z : Real, z ∈ Set.Icc (0 : Real) 1 →
    0 ≤ (chebE L).eval z ∧
    (chebE L).eval z ≤ 1 ∧
    (0 < z → (chebE L).eval z ≤ ((L : Real) ^ 2 * z)⁻¹) ∧
    z * (chebG L).eval z + (chebE L).eval z = 1

private lemma chebQ_eval_zero (L : Nat) : (chebQ L).eval 0 = 1 := by
  simp [chebQ]

private lemma X_mul_chebE (L : Nat) : X * chebE L = chebH L := by
  rw [chebE]
  simpa using
    (Polynomial.mul_divByMonic_eq_iff_isRoot (p := chebH L) (a := (0 : Real))).2 (by
      simp [Polynomial.IsRoot, chebH, chebQ_eval_zero])

private lemma chebH_derivative_eval_zero (L : Nat) (hL : 0 < L) :
    (chebH L).derivative.eval 0 = 1 := by
  rw [chebH, derivative_smul, eval_smul]
  simp only [derivative_sub, derivative_one, zero_sub, smul_eq_mul, eval_neg]
  rw [chebQ, derivative_comp, eval_mul, eval_comp]
  simp only [derivative_sub, derivative_one, derivative_mul, derivative_ofNat,
    zero_mul, derivative_X, mul_one, zero_sub, eval_neg, eval_ofNat]
  norm_num
  rw [Polynomial.Chebyshev.derivative_T_eval_one]
  push_cast
  have hne : (L : Real) ≠ 0 := by positivity
  field_simp

private lemma chebE_eval_zero (L : Nat) (hL : 0 < L) :
    (chebE L).eval 0 = 1 := by
  have hc := congrArg (fun p : Polynomial Real ↦ p.coeff 1) (X_mul_chebE L)
  rw [coeff_X_mul] at hc
  rw [← coeff_zero_eq_eval_zero, hc]
  have hd := chebH_derivative_eval_zero L hL
  rw [← coeff_zero_eq_eval_zero, coeff_derivative] at hd
  simpa using hd

private lemma X_mul_chebG (L : Nat) (hL : 0 < L) :
    X * chebG L = 1 - chebE L := by
  rw [chebG]
  simpa using
    (Polynomial.mul_divByMonic_eq_iff_isRoot (p := 1 - chebE L) (a := (0 : Real))).2 (by
      simp [Polynomial.IsRoot, chebE_eval_zero L hL])

private lemma chebG_defining_identity (L : Nat) (hL : 0 < L) (z : Real) :
    z * (chebG L).eval z + (chebE L).eval z = 1 := by
  have h := congrArg (Polynomial.eval z) (X_mul_chebG L hL)
  simp only [eval_mul, eval_X, eval_sub, eval_one] at h
  linarith

private noncomputable def explicitG (L : Nat) : Polynomial Real :=
  ∑ j ∈ Finset.range (L - 1),
    Polynomial.C
      (DiscreteAteMinimaxLoggap.gCoefficient L j) * Polynomial.X ^ j

private lemma eval_explicitG (L : Nat) (z : Real) :
    (explicitG L).eval z = DiscreteAteMinimaxLoggap.gPolynomial L z := by
  unfold explicitG DiscreteAteMinimaxLoggap.gPolynomial
  simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]

private lemma chebQ_eq_explicit (L : Nat) (hL : 0 < L) :
    chebQ L = 1 - Polynomial.C (2 * (L : Real) ^ 2) * Polynomial.X +
      Polynomial.C (2 * (L : Real) ^ 2) * Polynomial.X ^ 2 * explicitG L := by
  apply Polynomial.funext
  intro z
  simp only [chebQ, eval_comp, eval_sub, eval_one, eval_mul, eval_ofNat, eval_X,
    eval_add, eval_C, eval_pow, eval_explicitG]
  simpa [mul_comm] using
    DiscreteAteMinimaxLoggap.chebyshev_gPolynomial_identity hL z

private lemma chebG_eq_explicit (L : Nat) (hL : 0 < L) :
    chebG L = explicitG L := by
  apply mul_left_cancel₀ (show (Polynomial.X : Polynomial Real) ≠ 0 by simp)
  rw [X_mul_chebG L hL]
  have hE : Polynomial.X * chebE L =
      Polynomial.X * (1 - Polynomial.X * explicitG L) := by
    rw [X_mul_chebE, chebH, chebQ_eq_explicit L hL]
    apply Polynomial.funext
    intro z
    simp only [eval_smul, smul_eq_mul, eval_sub, eval_one, eval_add, eval_mul,
      eval_C, eval_X, eval_pow, eval_explicitG]
    have hne : (L : Real) ≠ 0 := by positivity
    field_simp
    ring
  have hE' := mul_left_cancel₀
    (show (Polynomial.X : Polynomial Real) ≠ 0 by simp) hE
  rw [hE']
  ring

private lemma abs_sin_nat_mul_le (n : Nat) (x : Real) :
    |Real.sin ((n : Real) * x)| ≤ (n : Real) * |Real.sin x| := by
  induction n with
  | zero => simp
  | succ n ih =>
      push_cast
      rw [add_mul, one_mul, Real.sin_add]
      calc
        |Real.sin ((n : Real) * x) * Real.cos x +
            Real.cos ((n : Real) * x) * Real.sin x|
            ≤ |Real.sin ((n : Real) * x) * Real.cos x| +
                |Real.cos ((n : Real) * x) * Real.sin x| := abs_add_le _ _
        _ = |Real.sin ((n : Real) * x)| * |Real.cos x| +
              |Real.cos ((n : Real) * x)| * |Real.sin x| := by rw [abs_mul, abs_mul]
        _ ≤ |Real.sin ((n : Real) * x)| + |Real.sin x| := by
              apply add_le_add
              · simpa using mul_le_mul_of_nonneg_left
                  (abs_le.2 ⟨Real.neg_one_le_cos x, Real.cos_le_one x⟩)
                  (abs_nonneg (Real.sin ((n : Real) * x)))
              · simpa using mul_le_mul_of_nonneg_right
                  (abs_le.2 ⟨Real.neg_one_le_cos ((n : Real) * x),
                    Real.cos_le_one ((n : Real) * x)⟩) (abs_nonneg (Real.sin x))
        _ ≤ (n : Real) * |Real.sin x| + |Real.sin x| := by
              simpa [add_comm] using add_le_add_right ih |Real.sin x|
        _ = ((n : Real) + 1) * |Real.sin x| := by ring

private lemma one_sub_cos_nat_mul_le (n : Nat) (x : Real) :
    1 - Real.cos ((n : Real) * x) ≤ (n : Real) ^ 2 * (1 - Real.cos x) := by
  have hs := abs_sin_nat_mul_le n (x / 2)
  have hs2 := pow_le_pow_left₀ (abs_nonneg _) hs 2
  simp only [mul_pow, sq_abs] at hs2
  rw [show (n : Real) * (x / 2) = ((n : Real) * x) / 2 by ring,
    Real.sin_sq_eq_half_sub] at hs2
  rw [Real.sin_sq_eq_half_sub] at hs2
  ring_nf at hs2 ⊢
  nlinarith

private lemma chebQ_eval_cos (L : Nat) {z : Real} (hz : z ∈ Set.Icc (0 : Real) 1) :
    (chebQ L).eval z = Real.cos ((L : Real) * Real.arccos (1 - 2 * z)) := by
  have hlo : (-1 : Real) ≤ 1 - 2 * z := by linarith [hz.2]
  have hhi : 1 - 2 * z ≤ (1 : Real) := by linarith [hz.1]
  calc
    (chebQ L).eval z =
        (Polynomial.Chebyshev.T Real L).eval (1 - 2 * z) := by
          simp [chebQ]
    _ = (Polynomial.Chebyshev.T Real L).eval
        (Real.cos (Real.arccos (1 - 2 * z))) := by
          rw [Real.cos_arccos hlo hhi]
    _ = Real.cos ((L : Real) * Real.arccos (1 - 2 * z)) := by
          simpa using Polynomial.Chebyshev.T_real_cos
            (Real.arccos (1 - 2 * z)) (L : Int)

private lemma chebQ_gap_le (L : Nat) {z : Real} (hz : z ∈ Set.Icc (0 : Real) 1) :
    1 - (chebQ L).eval z ≤ 2 * (L : Real) ^ 2 * z := by
  rw [chebQ_eval_cos L hz]
  have h := one_sub_cos_nat_mul_le L (Real.arccos (1 - 2 * z))
  rw [Real.cos_arccos (by linarith [hz.2]) (by linarith [hz.1])] at h
  nlinarith

private lemma chebE_scaled_identity (L : Nat) (z : Real) :
    z * (chebE L).eval z =
      (2 * (L : Real) ^ 2)⁻¹ * (1 - (chebQ L).eval z) := by
  have h := congrArg (Polynomial.eval z) (X_mul_chebE L)
  simpa [chebH] using h

private lemma chebE_interval_bounds (L : Nat) (hL : 0 < L) {z : Real}
    (hz : z ∈ Set.Icc (0 : Real) 1) :
    0 ≤ (chebE L).eval z ∧
      (chebE L).eval z ≤ 1 ∧
      (0 < z → (chebE L).eval z ≤ ((L : Real) ^ 2 * z)⁻¹) := by
  have hy : |1 - 2 * z| ≤ (1 : Real) := by
    rw [abs_le]
    constructor <;> linarith [hz.1, hz.2]
  have hQ := Polynomial.Chebyshev.abs_eval_T_real_le_one (L : Int) hy
  have hQ' : |(chebQ L).eval z| ≤ (1 : Real) := by
    simpa [chebQ] using hQ
  have hQlo : (-1 : Real) ≤ (chebQ L).eval z := (abs_le.mp hQ').1
  have hQhi : (chebQ L).eval z ≤ (1 : Real) := (abs_le.mp hQ').2
  have hL2 : 0 < (L : Real) ^ 2 := by positivity
  have hden : 0 < 2 * (L : Real) ^ 2 := mul_pos (by norm_num) hL2
  have hscaled := chebE_scaled_identity L z
  by_cases hz0 : z = 0
  · subst z
    simp [chebE_eval_zero L hL]
  · have hzpos : 0 < z := lt_of_le_of_ne hz.1 (Ne.symm hz0)
    have hnonnegScaled : 0 ≤ z * (chebE L).eval z := by
      rw [hscaled]
      exact mul_nonneg (le_of_lt (inv_pos.mpr hden)) (by linarith)
    have hE0 : 0 ≤ (chebE L).eval z := by nlinarith
    have hgap := chebQ_gap_le L hz
    have hscaledOne : z * (chebE L).eval z ≤ z := by
      calc
        z * (chebE L).eval z =
            (2 * (L : Real) ^ 2)⁻¹ * (1 - (chebQ L).eval z) := hscaled
        _ ≤ (2 * (L : Real) ^ 2)⁻¹ *
            (2 * (L : Real) ^ 2 * z) :=
              mul_le_mul_of_nonneg_left hgap (le_of_lt (inv_pos.mpr hden))
        _ = z := by field_simp
    have hE1 : (chebE L).eval z ≤ 1 := by nlinarith
    have hscaledInv : z * (chebE L).eval z ≤ ((L : Real) ^ 2)⁻¹ := by
      calc
        z * (chebE L).eval z =
            (2 * (L : Real) ^ 2)⁻¹ * (1 - (chebQ L).eval z) := hscaled
        _ ≤ (2 * (L : Real) ^ 2)⁻¹ * 2 :=
              mul_le_mul_of_nonneg_left (by linarith)
                (le_of_lt (inv_pos.mpr hden))
        _ = ((L : Real) ^ 2)⁻¹ := by field_simp
    refine ⟨hE0, hE1, fun _ ↦ ?_⟩
    rw [inv_eq_one_div]
    apply (le_div_iff₀ (mul_pos hL2 hzpos)).2
    calc
      (chebE L).eval z * ((L : Real) ^ 2 * z) =
          (L : Real) ^ 2 * (z * (chebE L).eval z) := by ring
      _ ≤ (L : Real) ^ 2 * ((L : Real) ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_left hscaledInv (le_of_lt hL2)
      _ = 1 := by field_simp

private noncomputable def sameArmMonomial
    (a : Bool) (r : Nat) (D : Real) (K : Nat × Nat) : Real :=
  let ka := if a then K.2 else K.1
  (ka.descFactorial r : Real) / D ^ r

private noncomputable def crossArmMonomial
    (a : Bool) (r : Nat) (D : Real) (K : Nat × Nat) : Real :=
  let ka := if a then K.2 else K.1
  let kb := if a then K.1 else K.2
  (kb : Real) * (ka.descFactorial r : Real) / D ^ (r + 1)

private lemma sameArmMonomial_sq_le
    (a : Bool) {L r : Nat} {D B s0 s1 : Real}
    (hD : 0 < D) (hB : 0 < B) (hs0 : 0 ≤ s0) (hs1 : 0 ≤ s1)
    (hLD : (L : Real) ≤ D) (hr : r ≤ L) :
    (∫ K : Nat × Nat, sameArmMonomial a r D K ^ 2 ∂
      (poissonMeasure (Real.toNNReal (D * (s0 / B)))).prod
        (poissonMeasure (Real.toNNReal (D * (s1 / B))))) ≤
      (3 : Real) ^ L * (1 + (s0 + s1) / B) ^ (2 * L) := by
  have hz0 : 0 ≤ s0 / B := div_nonneg hs0 hB.le
  have hz1 : 0 ≤ s1 / B := div_nonneg hs1 hB.le
  have hbase0 : 1 + s0 / B ≤ 1 + (s0 + s1) / B := by
    have : s0 / B ≤ (s0 + s1) / B :=
      div_le_div_of_nonneg_right (le_add_of_nonneg_right hs1) hB.le
    linarith
  have hbase1 : 1 + s1 / B ≤ 1 + (s0 + s1) / B := by
    have : s1 / B ≤ (s0 + s1) / B :=
      div_le_div_of_nonneg_right (le_add_of_nonneg_left hs0) hB.le
    linarith
  have hexp : 2 * r ≤ 2 * L := Nat.mul_le_mul_left 2 hr
  cases a
  · have hfactor := integral_normalized_descFactorial_cross_le
        hD hz0 hLD hr hr
    have heq : (∫ n : Nat,
        ((n.descFactorial r : Real) / D ^ r) ^ 2
          ∂poissonMeasure (Real.toNNReal (D * (s0 / B)))) =
        ∫ n : Nat,
          ((n.descFactorial r : Real) * n.descFactorial r) / D ^ (r + r)
            ∂poissonMeasure (Real.toNNReal (D * (s0 / B))) := by
      apply integral_congr_ae
      filter_upwards with n
      field_simp
      rw [pow_add, pow_two]
      ring
    rw [show (∫ K : Nat × Nat, sameArmMonomial false r D K ^ 2 ∂
        (poissonMeasure (Real.toNNReal (D * (s0 / B)))).prod
          (poissonMeasure (Real.toNNReal (D * (s1 / B))))) =
        (∫ n : Nat, ((n.descFactorial r : Real) / D ^ r) ^ 2
          ∂poissonMeasure (Real.toNNReal (D * (s0 / B)))) by
          rw [show (∫ K : Nat × Nat, sameArmMonomial false r D K ^ 2 ∂
              (poissonMeasure (Real.toNNReal (D * (s0 / B)))).prod
                (poissonMeasure (Real.toNNReal (D * (s1 / B))))) =
              (∫ n : Nat, ((n.descFactorial r : Real) / D ^ r) ^ 2
                ∂poissonMeasure (Real.toNNReal (D * (s0 / B)))) *
                ∫ _n : Nat, (1 : Real)
                  ∂poissonMeasure (Real.toNNReal (D * (s1 / B))) by
            simpa [sameArmMonomial] using integral_prod_mul
              (μ := poissonMeasure (Real.toNNReal (D * (s0 / B))))
              (ν := poissonMeasure (Real.toNNReal (D * (s1 / B))))
              (fun n : Nat ↦ ((n.descFactorial r : Real) / D ^ r) ^ 2)
              (fun _n : Nat ↦ (1 : Real))]
          simp]
    rw [heq]
    calc
      _ ≤ (3 : Real) ^ L * (1 + s0 / B) ^ (r + r) := hfactor
      _ ≤ (3 : Real) ^ L * (1 + (s0 + s1) / B) ^ (2 * L) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [show r + r = 2 * r by omega]
        exact (pow_le_pow_left₀ (by linarith) hbase0 _).trans
          (pow_le_pow_right₀ (by linarith) hexp)
  · have hfactor := integral_normalized_descFactorial_cross_le
        hD hz1 hLD hr hr
    have heq : (∫ n : Nat,
        ((n.descFactorial r : Real) / D ^ r) ^ 2
          ∂poissonMeasure (Real.toNNReal (D * (s1 / B)))) =
        ∫ n : Nat,
          ((n.descFactorial r : Real) * n.descFactorial r) / D ^ (r + r)
            ∂poissonMeasure (Real.toNNReal (D * (s1 / B))) := by
      apply integral_congr_ae
      filter_upwards with n
      field_simp
      rw [pow_add, pow_two]
      ring
    rw [show (∫ K : Nat × Nat, sameArmMonomial true r D K ^ 2 ∂
        (poissonMeasure (Real.toNNReal (D * (s0 / B)))).prod
          (poissonMeasure (Real.toNNReal (D * (s1 / B))))) =
        (∫ n : Nat, ((n.descFactorial r : Real) / D ^ r) ^ 2
          ∂poissonMeasure (Real.toNNReal (D * (s1 / B)))) by
          rw [show (∫ K : Nat × Nat, sameArmMonomial true r D K ^ 2 ∂
              (poissonMeasure (Real.toNNReal (D * (s0 / B)))).prod
                (poissonMeasure (Real.toNNReal (D * (s1 / B))))) =
              (∫ _n : Nat, (1 : Real)
                ∂poissonMeasure (Real.toNNReal (D * (s0 / B)))) *
                ∫ n : Nat, ((n.descFactorial r : Real) / D ^ r) ^ 2
                  ∂poissonMeasure (Real.toNNReal (D * (s1 / B))) by
            simpa [sameArmMonomial] using integral_prod_mul
              (μ := poissonMeasure (Real.toNNReal (D * (s0 / B))))
              (ν := poissonMeasure (Real.toNNReal (D * (s1 / B))))
              (fun _n : Nat ↦ (1 : Real))
              (fun n : Nat ↦ ((n.descFactorial r : Real) / D ^ r) ^ 2)]
          simp]
    rw [heq]
    calc
      _ ≤ (3 : Real) ^ L * (1 + s1 / B) ^ (r + r) := hfactor
      _ ≤ (3 : Real) ^ L * (1 + (s0 + s1) / B) ^ (2 * L) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [show r + r = 2 * r by omega]
        exact (pow_le_pow_left₀ (by linarith) hbase1 _).trans
          (pow_le_pow_right₀ (by linarith) hexp)

private lemma crossArmMonomial_sq_le
    (a : Bool) {L r : Nat} {D B s0 s1 : Real}
    (hD : 0 < D) (hB : 0 < B) (hs0 : 0 ≤ s0) (hs1 : 0 ≤ s1)
    (hLD : (L : Real) ≤ D) (hr : r + 1 ≤ L) :
    (∫ K : Nat × Nat, crossArmMonomial a r D K ^ 2 ∂
      (poissonMeasure (Real.toNNReal (D * (s0 / B)))).prod
        (poissonMeasure (Real.toNNReal (D * (s1 / B))))) ≤
      (9 : Real) ^ L * (1 + (s0 + s1) / B) ^ (2 * L) := by
  have hrL : r ≤ L := le_trans (Nat.le_add_right r 1) hr
  have h1L : 1 ≤ L := le_trans (by omega : 1 ≤ r + 1) hr
  have hz0 : 0 ≤ s0 / B := div_nonneg hs0 hB.le
  have hz1 : 0 ≤ s1 / B := div_nonneg hs1 hB.le
  let q : Real := 1 + (s0 + s1) / B
  have hq : 1 ≤ q := by
    dsimp [q]
    exact le_add_of_nonneg_right (div_nonneg (add_nonneg hs0 hs1) hB.le)
  have hb0 : 1 + s0 / B ≤ q := by
    dsimp [q]
    have hdiv : s0 / B ≤ (s0 + s1) / B :=
      div_le_div_of_nonneg_right (le_add_of_nonneg_right hs1) hB.le
    linarith
  have hb1 : 1 + s1 / B ≤ q := by
    dsimp [q]
    have hdiv : s1 / B ≤ (s0 + s1) / B :=
      div_le_div_of_nonneg_right (le_add_of_nonneg_left hs0) hB.le
    linarith
  have hmoment0 (u : Nat) (hu : u ≤ L) :
      (∫ n : Nat, ((n.descFactorial u : Real) / D ^ u) ^ 2
        ∂poissonMeasure (Real.toNNReal (D * (s0 / B)))) ≤
        (3 : Real) ^ L * (1 + s0 / B) ^ (2 * u) := by
    have h := integral_normalized_descFactorial_cross_le hD hz0 hLD hu hu
    have heq : (∫ n : Nat, ((n.descFactorial u : Real) / D ^ u) ^ 2
        ∂poissonMeasure (Real.toNNReal (D * (s0 / B)))) =
        ∫ n : Nat, ((n.descFactorial u : Real) * n.descFactorial u) /
          D ^ (u + u) ∂poissonMeasure (Real.toNNReal (D * (s0 / B))) := by
      apply integral_congr_ae
      filter_upwards with n
      field_simp
      rw [pow_add, pow_two]
      ring
    rw [heq]
    simpa [two_mul] using h
  have hmoment1 (u : Nat) (hu : u ≤ L) :
      (∫ n : Nat, ((n.descFactorial u : Real) / D ^ u) ^ 2
        ∂poissonMeasure (Real.toNNReal (D * (s1 / B)))) ≤
        (3 : Real) ^ L * (1 + s1 / B) ^ (2 * u) := by
    have h := integral_normalized_descFactorial_cross_le hD hz1 hLD hu hu
    have heq : (∫ n : Nat, ((n.descFactorial u : Real) / D ^ u) ^ 2
        ∂poissonMeasure (Real.toNNReal (D * (s1 / B)))) =
        ∫ n : Nat, ((n.descFactorial u : Real) * n.descFactorial u) /
          D ^ (u + u) ∂poissonMeasure (Real.toNNReal (D * (s1 / B))) := by
      apply integral_congr_ae
      filter_upwards with n
      field_simp
      rw [pow_add, pow_two]
      ring
    rw [heq]
    simpa [two_mul] using h
  have hcombine {x y : Real} (hx : x ≤ (3 : Real) ^ L * (1 + s0 / B) ^ (2 * r))
      (hy : y ≤ (3 : Real) ^ L * (1 + s1 / B) ^ 2)
      (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) :
      x * y ≤ (9 : Real) ^ L * q ^ (2 * L) := by
    calc
      x * y ≤ ((3 : Real) ^ L * (1 + s0 / B) ^ (2 * r)) *
          ((3 : Real) ^ L * (1 + s1 / B) ^ 2) := by
            exact mul_le_mul hx hy hy0 (by positivity)
      _ ≤ ((3 : Real) ^ L * q ^ (2 * r)) *
          ((3 : Real) ^ L * q ^ 2) := by
            gcongr
      _ = (9 : Real) ^ L * q ^ (2 * (r + 1)) := by
            rw [show (9 : Real) = 3 * 3 by norm_num, mul_pow]
            have hpow : q ^ (2 * r) * q ^ 2 = q ^ (2 * (r + 1)) := by
              rw [← pow_add]
              congr 1
            rw [← hpow]
            ring
      _ ≤ (9 : Real) ^ L * q ^ (2 * L) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact pow_le_pow_right₀ hq (Nat.mul_le_mul_left 2 hr)
  have hcombine' {x y : Real} (hx : x ≤ (3 : Real) ^ L * (1 + s0 / B) ^ 2)
      (hy : y ≤ (3 : Real) ^ L * (1 + s1 / B) ^ (2 * r))
      (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) :
      x * y ≤ (9 : Real) ^ L * q ^ (2 * L) := by
    calc
      x * y ≤ ((3 : Real) ^ L * (1 + s0 / B) ^ 2) *
          ((3 : Real) ^ L * (1 + s1 / B) ^ (2 * r)) := by
            exact mul_le_mul hx hy hy0 (by positivity)
      _ ≤ ((3 : Real) ^ L * q ^ 2) *
          ((3 : Real) ^ L * q ^ (2 * r)) := by gcongr
      _ = (9 : Real) ^ L * q ^ (2 * (r + 1)) := by
            rw [show (9 : Real) = 3 * 3 by norm_num, mul_pow]
            have hpow : q ^ 2 * q ^ (2 * r) = q ^ (2 * (r + 1)) := by
              rw [← pow_add]
              congr 1
              omega
            rw [← hpow]
            ring
      _ ≤ (9 : Real) ^ L * q ^ (2 * L) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact pow_le_pow_right₀ hq (Nat.mul_le_mul_left 2 hr)
  cases a
  · rw [show (∫ K : Nat × Nat, crossArmMonomial false r D K ^ 2 ∂
        (poissonMeasure (Real.toNNReal (D * (s0 / B)))).prod
          (poissonMeasure (Real.toNNReal (D * (s1 / B))))) =
        (∫ n : Nat, ((n.descFactorial r : Real) / D ^ r) ^ 2
          ∂poissonMeasure (Real.toNNReal (D * (s0 / B)))) *
        (∫ n : Nat, ((n.descFactorial 1 : Real) / D) ^ 2
          ∂poissonMeasure (Real.toNNReal (D * (s1 / B)))) by
      rw [show (∫ K : Nat × Nat, crossArmMonomial false r D K ^ 2 ∂
          (poissonMeasure (Real.toNNReal (D * (s0 / B)))).prod
            (poissonMeasure (Real.toNNReal (D * (s1 / B))))) =
          ∫ K : Nat × Nat,
            ((K.1.descFactorial r : Real) / D ^ r) ^ 2 *
              ((K.2.descFactorial 1 : Real) / D) ^ 2 ∂
            (poissonMeasure (Real.toNNReal (D * (s0 / B)))).prod
              (poissonMeasure (Real.toNNReal (D * (s1 / B)))) by
        apply integral_congr_ae
        filter_upwards with K
        simp only [crossArmMonomial, Bool.false_eq_true, ↓reduceIte,
          Nat.descFactorial_one]
        field_simp
        rw [pow_add, pow_two]
        ring]
      exact integral_prod_mul
        (fun n : Nat ↦ ((n.descFactorial r : Real) / D ^ r) ^ 2)
        (fun n : Nat ↦ ((n.descFactorial 1 : Real) / D) ^ 2)]
    apply hcombine (hmoment0 r hrL) (by simpa using hmoment1 1 h1L)
    · exact integral_nonneg (fun _ ↦ sq_nonneg _)
    · exact integral_nonneg (fun _ ↦ sq_nonneg _)
  · rw [show (∫ K : Nat × Nat, crossArmMonomial true r D K ^ 2 ∂
        (poissonMeasure (Real.toNNReal (D * (s0 / B)))).prod
          (poissonMeasure (Real.toNNReal (D * (s1 / B))))) =
        (∫ n : Nat, ((n.descFactorial 1 : Real) / D) ^ 2
          ∂poissonMeasure (Real.toNNReal (D * (s0 / B)))) *
        (∫ n : Nat, ((n.descFactorial r : Real) / D ^ r) ^ 2
          ∂poissonMeasure (Real.toNNReal (D * (s1 / B)))) by
      rw [show (∫ K : Nat × Nat, crossArmMonomial true r D K ^ 2 ∂
          (poissonMeasure (Real.toNNReal (D * (s0 / B)))).prod
            (poissonMeasure (Real.toNNReal (D * (s1 / B))))) =
          ∫ K : Nat × Nat,
            ((K.1.descFactorial 1 : Real) / D) ^ 2 *
              ((K.2.descFactorial r : Real) / D ^ r) ^ 2 ∂
            (poissonMeasure (Real.toNNReal (D * (s0 / B)))).prod
              (poissonMeasure (Real.toNNReal (D * (s1 / B)))) by
        apply integral_congr_ae
        filter_upwards with K
        simp only [crossArmMonomial, ↓reduceIte, Nat.descFactorial_one]
        field_simp
        rw [pow_add, pow_two]
        ring]
      exact integral_prod_mul
        (fun n : Nat ↦ ((n.descFactorial 1 : Real) / D) ^ 2)
        (fun n : Nat ↦ ((n.descFactorial r : Real) / D ^ r) ^ 2)]
    exact hcombine' (by simpa using hmoment0 1 h1L) (hmoment1 r hrL)
      (integral_nonneg (fun _ ↦ sq_nonneg _))
      (integral_nonneg (fun _ ↦ sq_nonneg _))

private lemma explicitG_support_subset (L : Nat) :
    (explicitG L).support ⊆ Finset.range (L - 1) := by
  intro j hj
  by_contra hj'
  have hc : (explicitG L).coeff j = 0 := by
    simp [explicitG, hj']
  exact (Polynomial.mem_support_iff.mp hj) hc

/-- For a [positive polynomial degree](hyp:hL), the coefficient ℓ¹ norm of
the shifted Chebyshev quotient [is at most six to that degree](goal). -/
lemma coefficientL1_chebG_le (L : Nat) (hL : 0 < L) :
    coefficientL1 (chebG L) ≤ (6 : Real) ^ L := by
  rw [chebG_eq_explicit L hL]
  calc
    coefficientL1 (explicitG L) =
        ∑ j ∈ (explicitG L).support, |(explicitG L).coeff j| := rfl
    _ ≤ ∑ j ∈ Finset.range (L - 1), |(explicitG L).coeff j| := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (explicitG_support_subset L)
      intro j _ _
      exact abs_nonneg _
    _ = DiscreteAteMinimaxLoggap.gpos L 1 := by
      unfold DiscreteAteMinimaxLoggap.gpos
      apply Finset.sum_congr rfl
      intro j hj
      simp [explicitG, Finset.mem_range.mp hj]
    _ ≤ (6 : Real) ^ L := by
      simpa using DiscreteAteMinimaxLoggap.gpos_bound hL (z := (1 : Real)) (by norm_num)

private noncomputable def qCoefficient (L j : Nat) : Real :=
  (-1 : Real) ^ j * (L : Real) / (L + j) *
    Nat.choose (L + j) (2 * j) * 4 ^ j

private noncomputable def explicitQ (L : Nat) : Polynomial Real :=
  1 + ∑ j ∈ Finset.Icc 1 L,
    Polynomial.C (qCoefficient L j) * Polynomial.X ^ j

private lemma chebQ_eq_explicitQ (L : Nat) : chebQ L = explicitQ L := by
  apply Polynomial.funext
  intro z
  rw [chebQ, eval_comp]
  simp only [eval_sub, eval_one, eval_mul, eval_ofNat, eval_X, explicitQ,
    eval_add, eval_finsetSum, eval_C, eval_pow]
  simpa [qCoefficient] using
    DiscreteAteMinimaxLoggap.shifted_chebyshev_expansion L z

private lemma explicitQ_support_subset (L : Nat) :
    (explicitQ L).support ⊆ insert 0 (Finset.Icc 1 L) := by
  intro j hj
  by_contra hj'
  have hj0 : j ≠ 0 := fun h ↦ hj' (by simp [h])
  have hjI : j ∉ Finset.Icc 1 L := fun h ↦ hj' (by simp [h])
  have hc : (explicitQ L).coeff j = 0 := by
    simp [explicitQ, hj0, hjI, Polynomial.coeff_one]
  exact (Polynomial.mem_support_iff.mp hj) hc

private lemma abs_qCoefficient (L : Nat) (hL : 0 < L) (j : Nat) :
    |qCoefficient L j| = (-1 : Real) ^ j * qCoefficient L j := by
  let b : Real := (L : Real) / (L + j) * Nat.choose (L + j) (2 * j) * 4 ^ j
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hq : qCoefficient L j = (-1 : Real) ^ j * b := by
    dsimp [qCoefficient, b]
    ring
  have hs : (-1 : Real) ^ j * (-1 : Real) ^ j = 1 := by
    rw [← pow_add]
    rw [show j + j = 2 * j by omega, pow_mul]
    simp
  rw [hq, abs_mul, abs_of_nonneg hb]
  rw [abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [← mul_assoc, hs, one_mul]

private lemma coefficientL1_chebQ_le (L : Nat) (hL : 0 < L) :
    coefficientL1 (chebQ L) ≤ (7 : Real) ^ L := by
  rw [chebQ_eq_explicitQ]
  have hcoeff (j : Nat) (hj : j ∈ insert 0 (Finset.Icc 1 L)) :
      |(explicitQ L).coeff j| = if j = 0 then 1 else |qCoefficient L j| := by
    by_cases hj0 : j = 0
    · subst j
      simp [explicitQ]
    · have hjI : j ∈ Finset.Icc 1 L := by simpa [hj0] using hj
      simp [explicitQ, hj0, hjI, Polynomial.coeff_one]
  calc
    coefficientL1 (explicitQ L) ≤
        ∑ j ∈ insert 0 (Finset.Icc 1 L), |(explicitQ L).coeff j| := by
      unfold coefficientL1
      exact Finset.sum_le_sum_of_subset_of_nonneg (explicitQ_support_subset L)
        (fun j _ _ ↦ abs_nonneg _)
    _ = 1 + ∑ j ∈ Finset.Icc 1 L, |qCoefficient L j| := by
      rw [Finset.sum_insert (by simp)]
      rw [hcoeff 0 (by simp)]
      simp only [if_pos]
      apply congrArg (1 + ·)
      apply Finset.sum_congr rfl
      intro j hj
      rw [hcoeff j (by simp [hj])]
      have hj0 : j ≠ 0 := Nat.ne_of_gt
        (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hj).1)
      simp only [if_neg hj0]
    _ = (Polynomial.Chebyshev.T Real L).eval 3 := by
      have h := DiscreteAteMinimaxLoggap.shifted_chebyshev_expansion L (-1 : Real)
      norm_num at h
      rw [h]
      apply congrArg (1 + ·)
      apply Finset.sum_congr rfl
      intro j hj
      rw [abs_qCoefficient L hL]
      simp [qCoefficient]
      ring
    _ ≤ (6 : Real) ^ L := DiscreteAteMinimaxLoggap.chebyshev_three_le L
    _ ≤ (7 : Real) ^ L := pow_le_pow_left₀ (by norm_num) (by norm_num) L

private lemma armMonomial_sum_memLp (a : Bool) (r : Nat) {D z0 z1 : Real}
    (hD : 0 < D) :
    MemLp (fun K : Nat × Nat ↦
      sameArmMonomial a (r + 1) D K + crossArmMonomial a r D K) 2
      ((poissonMeasure (Real.toNNReal (D * z0))).prod
        (poissonMeasure (Real.toNNReal (D * z1)))) := by
  let μ0 := poissonMeasure (Real.toNNReal (D * z0))
  let μ1 := poissonMeasure (Real.toNNReal (D * z1))
  have hs0 (u : Nat) : Integrable
      (fun n : Nat ↦ ((n.descFactorial u : Real) / D ^ u) ^ 2) μ0 := by
    have h := (integrable_descFactorial_mul_poisson
      (Real.toNNReal (D * z0)) u u).const_mul (D ^ (u + u))⁻¹
    apply h.congr
    filter_upwards with n
    field_simp
    rw [pow_add, pow_two]
    ring
  have hs1 (u : Nat) : Integrable
      (fun n : Nat ↦ ((n.descFactorial u : Real) / D ^ u) ^ 2) μ1 := by
    have h := (integrable_descFactorial_mul_poisson
      (Real.toNNReal (D * z1)) u u).const_mul (D ^ (u + u))⁻¹
    apply h.congr
    filter_upwards with n
    field_simp
    rw [pow_add, pow_two]
    ring
  cases a
  · have hsame := (hs0 (r + 1)).mul_prod
      (integrable_const (1 : Real) : Integrable (fun _ : Nat ↦ (1 : Real)) μ1)
    have hcross := (hs0 r).mul_prod (hs1 1)
    have hsame' : Integrable (fun K : Nat × Nat ↦
        sameArmMonomial false (r + 1) D K ^ 2) (μ0.prod μ1) := by
      simpa [sameArmMonomial] using hsame
    have hcross' : Integrable (fun K : Nat × Nat ↦
        crossArmMonomial false r D K ^ 2) (μ0.prod μ1) := by
      apply hcross.congr
      filter_upwards with K
      simp only [crossArmMonomial, Bool.false_eq_true, ↓reduceIte,
        Nat.descFactorial_one]
      field_simp
      rw [pow_add, pow_two]
      ring
    exact ((memLp_two_iff_integrable_sq
      (measurable_of_countable _).aestronglyMeasurable).2 hsame').add
        ((memLp_two_iff_integrable_sq
          (measurable_of_countable _).aestronglyMeasurable).2 hcross')
  · have hsame :=
      (integrable_const (1 : Real) : Integrable (fun _ : Nat ↦ (1 : Real)) μ0).mul_prod
        (hs1 (r + 1))
    have hcross := (hs0 1).mul_prod (hs1 r)
    have hsame' : Integrable (fun K : Nat × Nat ↦
        sameArmMonomial true (r + 1) D K ^ 2) (μ0.prod μ1) := by
      simpa [sameArmMonomial] using hsame
    have hcross' : Integrable (fun K : Nat × Nat ↦
        crossArmMonomial true r D K ^ 2) (μ0.prod μ1) := by
      apply hcross.congr
      filter_upwards with K
      simp only [crossArmMonomial, ↓reduceIte, Nat.descFactorial_one]
      field_simp
      rw [pow_add, pow_two]
      ring
    exact ((memLp_two_iff_integrable_sq
      (measurable_of_countable _).aestronglyMeasurable).2 hsame').add
        ((memLp_two_iff_integrable_sq
          (measurable_of_countable _).aestronglyMeasurable).2 hcross')

private lemma armMonomial_sum_sq_le (a : Bool) {L r : Nat} {D B s0 s1 : Real}
    (hD : 0 < D) (hB : 0 < B) (hs0 : 0 ≤ s0) (hs1 : 0 ≤ s1)
    (hLD : (L : Real) ≤ D) (hr : r + 1 ≤ L) :
    (∫ K : Nat × Nat,
      (sameArmMonomial a (r + 1) D K + crossArmMonomial a r D K) ^ 2 ∂
        (poissonMeasure (Real.toNNReal (D * (s0 / B)))).prod
          (poissonMeasure (Real.toNNReal (D * (s1 / B))))) ≤
      (36 : Real) ^ L * (1 + (s0 + s1) / B) ^ (2 * L) := by
  let μ := (poissonMeasure (Real.toNNReal (D * (s0 / B)))).prod
    (poissonMeasure (Real.toNNReal (D * (s1 / B))))
  have hsame := sameArmMonomial_sq_le a hD hB hs0 hs1 hLD hr
  have hcross := crossArmMonomial_sq_le a hD hB hs0 hs1 hLD hr
  have hmem := armMonomial_sum_memLp a r (D := D) (z0 := s0 / B)
    (z1 := s1 / B) hD
  have hiSame : Integrable (fun K : Nat × Nat ↦
      sameArmMonomial a (r + 1) D K ^ 2) μ := by
    cases a
    · have hc := (integrable_descFactorial_mul_poisson
          (Real.toNNReal (D * (s0 / B))) (r + 1) (r + 1)).const_mul
          (D ^ ((r + 1) + (r + 1)))⁻¹
      have hp := hc.mul_prod
        (integrable_const (1 : Real) : Integrable (fun _ : Nat ↦ (1 : Real))
          (poissonMeasure (Real.toNNReal (D * (s1 / B)))))
      apply hp.congr
      filter_upwards with K
      simp only [sameArmMonomial, Bool.false_eq_true, ↓reduceIte]
      field_simp
      rw [pow_add, pow_two]
      ring
    · have hc := (integrable_descFactorial_mul_poisson
          (Real.toNNReal (D * (s1 / B))) (r + 1) (r + 1)).const_mul
          (D ^ ((r + 1) + (r + 1)))⁻¹
      have hp :=
        (integrable_const (1 : Real) : Integrable (fun _ : Nat ↦ (1 : Real))
          (poissonMeasure (Real.toNNReal (D * (s0 / B))))).mul_prod hc
      apply hp.congr
      filter_upwards with K
      simp only [sameArmMonomial, ↓reduceIte]
      field_simp
      rw [pow_add, pow_two]
      ring
  have hiCross : Integrable (fun K : Nat × Nat ↦
      crossArmMonomial a r D K ^ 2) μ := by
    cases a
    · have h0 := (integrable_descFactorial_mul_poisson
          (Real.toNNReal (D * (s0 / B))) r r).const_mul (D ^ (r + r))⁻¹
      have h1 := (integrable_descFactorial_mul_poisson
          (Real.toNNReal (D * (s1 / B))) 1 1).const_mul (D ^ 2)⁻¹
      apply (h0.mul_prod h1).congr
      filter_upwards with K
      simp only [crossArmMonomial, Bool.false_eq_true, ↓reduceIte,
        Nat.descFactorial_one]
      field_simp
      rw [pow_add, pow_two]
      ring
    · have h0 := (integrable_descFactorial_mul_poisson
          (Real.toNNReal (D * (s0 / B))) 1 1).const_mul (D ^ 2)⁻¹
      have h1 := (integrable_descFactorial_mul_poisson
          (Real.toNNReal (D * (s1 / B))) r r).const_mul (D ^ (r + r))⁻¹
      apply (h0.mul_prod h1).congr
      filter_upwards with K
      simp only [crossArmMonomial, ↓reduceIte, Nat.descFactorial_one]
      field_simp
      rw [pow_add, pow_two]
      ring
  have hpoint (K : Nat × Nat) :
      (sameArmMonomial a (r + 1) D K + crossArmMonomial a r D K) ^ 2 ≤
        2 * sameArmMonomial a (r + 1) D K ^ 2 +
          2 * crossArmMonomial a r D K ^ 2 := by
    have hsq := sq_nonneg
      (sameArmMonomial a (r + 1) D K - crossArmMonomial a r D K)
    nlinarith
  have hmono := integral_mono_ae hmem.integrable_sq
    ((hiSame.const_mul 2).add (hiCross.const_mul 2))
    (Filter.Eventually.of_forall hpoint)
  simp only [Pi.add_apply] at hmono
  rw [integral_add (hiSame.const_mul 2) (hiCross.const_mul 2),
    integral_const_mul, integral_const_mul] at hmono
  calc
    _ ≤ 2 * ((3 : Real) ^ L * (1 + (s0 + s1) / B) ^ (2 * L)) +
        2 * ((9 : Real) ^ L * (1 + (s0 + s1) / B) ^ (2 * L)) := by
      exact hmono.trans (add_le_add (mul_le_mul_of_nonneg_left hsame (by norm_num))
        (mul_le_mul_of_nonneg_left hcross (by norm_num)))
    _ ≤ (36 : Real) ^ L * (1 + (s0 + s1) / B) ^ (2 * L) := by
      have hq : 0 ≤ (1 + (s0 + s1) / B) ^ (2 * L) := by positivity
      have hnum : 2 * (3 : Real) ^ L + 2 * (9 : Real) ^ L ≤ 36 ^ L := by
        have hL1 : 1 ≤ L := le_trans (by omega : 1 ≤ r + 1) hr
        have hfour : (4 : Real) ≤ 4 ^ L := by
          calc
            (4 : Real) = 4 ^ (1 : Nat) := by norm_num
            _ ≤ 4 ^ L := pow_le_pow_right₀ (by norm_num) hL1
        have h39 := pow_le_pow_left₀ (by norm_num : (0 : Real) ≤ 3)
          (by norm_num : (3 : Real) ≤ 9) L
        calc
          2 * (3 : Real) ^ L + 2 * (9 : Real) ^ L ≤ 4 * 9 ^ L := by linarith
          _ ≤ 4 ^ L * 9 ^ L :=
            mul_le_mul_of_nonneg_right hfour (by positivity)
          _ = 36 ^ L := by rw [← mul_pow]; norm_num
      nlinarith

-- @node: lem:explicit-chebyshev-calibration
/-- The explicit shifted-Chebyshev construction satisfies (C7)--(C9).  [the stated conditions](hyp:hL) [the stated conclusion](goal). -/
lemma explicit_chebyshev_calibration (L : Nat) (hL : 2 ≤ L) :
    ChebyshevCalibration L := by
  have hLpos : 0 < L := by omega
  refine ⟨coefficientL1_chebQ_le L hLpos, ?_, ?_, ?_⟩
  · have hg := coefficientL1_chebG_le L hLpos
    have hpow : (6 : Real) ^ L ≤ 7 ^ L :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) L
    have htwo : (2 : Real) ≤ 2 ^ L := by
      calc
        (2 : Real) = 2 ^ (1 : Nat) := by norm_num
        _ ≤ 2 ^ L := pow_le_pow_right₀ (by norm_num) (by omega)
    calc
      2 * coefficientL1 (chebG L) ≤ 2 * 6 ^ L := by gcongr
      _ ≤ 2 ^ L * 7 ^ L := mul_le_mul htwo hpow (by positivity) (by positivity)
      _ = 14 ^ L := by rw [← mul_pow]; norm_num
  · intro a t B s0 s1 ht hB hs0 hs1 hLD
    dsimp only
    let D := t * B
    let p := s0 + s1
    let q := 1 + p / B
    have hD : 0 < D := mul_pos ht hB
    have hrate0 : D * (s0 / B) = t * s0 := by
      dsimp [D]
      field_simp
    have hrate1 : D * (s1 / B) = t * s1 := by
      dsimp [D]
      field_simp
    have hsupp : (chebG L).support ⊆ Finset.range (L - 1) := by
      rw [chebG_eq_explicit L hLpos]
      exact explicitG_support_subset L
    let Xj : Nat → Nat × Nat → Real := fun j K ↦
      sameArmMonomial a (j + 1) D K + crossArmMonomial a j D K
    let μ := (poissonMeasure (Real.toNNReal (D * (s0 / B)))).prod
      (poissonMeasure (Real.toNNReal (D * (s1 / B))))
    have hjOrder (j : Nat) (hj : j ∈ (chebG L).support) : j + 1 ≤ L := by
      have hjr := Finset.mem_range.mp (hsupp hj)
      omega
    have hXmem (j : Nat) (hj : j ∈ (chebG L).support) : MemLp (Xj j) 2 μ := by
      exact armMonomial_sum_memLp a j (D := D) (z0 := s0 / B)
        (z1 := s1 / B) hD
    have hXsq (j : Nat) (hj : j ∈ (chebG L).support) :
        (∫ K, Xj j K ^ 2 ∂μ) ≤ ((6 : Real) ^ L * q ^ L) ^ 2 := by
      have h := armMonomial_sum_sq_le a hD hB hs0 hs1 hLD (hjOrder j hj)
      dsimp [Xj, μ, q, p] at h ⊢
      calc
        _ ≤ (36 : Real) ^ L * (1 + (s0 + s1) / B) ^ (2 * L) := h
        _ = ((6 : Real) ^ L * (1 + (s0 + s1) / B) ^ L) ^ 2 := by
          rw [show (36 : Real) = 6 * 6 by norm_num, mul_pow]
          rw [show 2 * L = L + L by omega, pow_add, mul_pow, pow_two]
          ring
    have houter :=
      DiscreteOptimalValueMinimaxMatched.integral_sq_finset_sum_le_coeffL1
        μ (chebG L).support (chebG L).coeff Xj
        ((6 : Real) ^ L * q ^ L) (by positivity) hXmem hXsq
    have hlift : (fun K : Nat × Nat ↦ factorialLift a L B t K.1 K.2) =
        fun K ↦ ∑ j ∈ (chebG L).support, (chebG L).coeff j * Xj j K := by
      funext K
      unfold factorialLift
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [Xj, D, sameArmMonomial, crossArmMonomial]
      cases a <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> ring
    have hmoment : factorialLiftSecondMoment a L B t s0 s1 ≤
        coefficientL1 (chebG L) ^ 2 * ((6 : Real) ^ L * q ^ L) ^ 2 := by
      unfold factorialLiftSecondMoment
      dsimp [μ] at houter
      rw [hrate0, hrate1] at houter
      rw [show (fun K : Nat × Nat ↦ factorialLift a L B t K.1 K.2 ^ 2) =
          (fun K ↦ (∑ j ∈ (chebG L).support,
            (chebG L).coeff j * Xj j K) ^ 2) by
        funext K
        rw [congrFun hlift K]]
      simpa only [coefficientL1] using houter
    have hg := coefficientL1_chebG_le L hLpos
    have hq0 : 0 ≤ q := by
      dsimp [q, p]
      have := div_nonneg (add_nonneg hs0 hs1) hB.le
      linarith
    have hg0 : 0 ≤ coefficientL1 (chebG L) := by
      unfold coefficientL1
      exact Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
    have hmain : factorialLiftSecondMoment a L B t s0 s1 ≤
        (1296 : Real) ^ L * q ^ (2 * L) := by
      calc
        _ ≤ coefficientL1 (chebG L) ^ 2 * ((6 : Real) ^ L * q ^ L) ^ 2 := hmoment
        _ ≤ ((6 : Real) ^ L) ^ 2 * ((6 : Real) ^ L * q ^ L) ^ 2 := by
          exact mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ hg0 hg 2) (sq_nonneg _)
        _ = (1296 : Real) ^ L * q ^ (2 * L) := by
          norm_num [pow_two, pow_mul, Nat.mul_comm]
          rw [show (1296 : Real) = 6 * 6 * 6 * 6 by norm_num,
            mul_pow, mul_pow, mul_pow]
          ring
    constructor
    · dsimp [p, q] at hmain ⊢
      exact hmain.trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by norm_num) (by norm_num : (1296 : Real) ≤ 7056) L)
        (by positivity))
    · intro hpB
      have hq2 : q ≤ 2 := by
        dsimp [q, p]
        have : (s0 + s1) / B ≤ 1 := (div_le_one hB).2 hpB
        linarith
      calc
        factorialLiftSecondMoment a L B t s0 s1 ≤
            (1296 : Real) ^ L * q ^ (2 * L) := hmain
        _ ≤ (1296 : Real) ^ L * 2 ^ (2 * L) := by
          gcongr
        _ = (5184 : Real) ^ L := by
          rw [show (5184 : Real) = 1296 * 4 by norm_num, mul_pow,
            show (2 : Real) ^ (2 * L) = 4 ^ L by
              rw [show (4 : Real) = 2 ^ 2 by norm_num, pow_mul]]
        _ ≤ (7056 : Real) ^ L :=
          pow_le_pow_left₀ (by norm_num) (by norm_num) L
  · intro z hz
    rcases chebE_interval_bounds L hLpos hz with ⟨h0, h1, hinv⟩
    exact ⟨h0, h1, hinv, chebG_defining_identity L hLpos z⟩

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
