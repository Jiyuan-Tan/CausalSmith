module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.DictionaryScore.InverseHeat
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.PolynomialOneNorm
/-!
# Exponential polynomial variance envelope

Finite coefficient algebra completes roadmap S13 for the declared polynomial localization
weights. The second-kind Chebyshev recurrence bounds coefficient mass by an exponential;
the quadratic substitution and sixth power preserve an exponential degree bound. Combining
this with the exact Gaussian second-moment calculation gives a public variance envelope.
-/
public section
set_option linter.style.longLine false
open MeasureTheory Set
open Polynomial
open Causalean.Mathlib.Analysis.Approximation.Chebyshev
open Causalean.Mathlib.Analysis.JacksonApproximation
open scoped BigOperators
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition

/-- The coefficient norm may be computed over any range beyond the degree. [Under the stated conditions](hyp:hp). [This is the stated conclusion](goal). -/
-- @node: coeffOneNorm_range
lemma coeffOneNorm_range (p : ℝ[X]) (D : ℕ) (hp : p.natDegree ≤ D) :
    polynomialCoeffOneNorm p = ∑ i ∈ Finset.range (D+1), |p.coeff i| := by
  exact p.sum_over_range' (fun _ => abs_zero) (D+1) (by omega)

/-- The coefficient norm is nonnegative. [This is the stated conclusion](goal). -/
-- @node: coeffOneNorm_nonneg
lemma coeffOneNorm_nonneg (p : ℝ[X]) : 0 ≤ polynomialCoeffOneNorm p := by
  exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

/-- Coefficientwise triangle inequalities control sums and differences. [This is the stated conclusion](goal). -/
-- @node: coeffOneNorm_add_le
lemma coeffOneNorm_add_le (p q : ℝ[X]) :
    polynomialCoeffOneNorm (p+q) ≤ polynomialCoeffOneNorm p + polynomialCoeffOneNorm q := by
  rw [coeffOneNorm_range (p+q) _ (natDegree_add_le _ _),
    coeffOneNorm_range p _ (le_max_left _ _), coeffOneNorm_range q _ (le_max_right _ _),
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i _ => by simpa using abs_add_le (p.coeff i) (q.coeff i))

/-- Differences obey the same coefficientwise triangle inequality. [This is the stated conclusion](goal). -/
-- @node: coeffOneNorm_sub_le
lemma coeffOneNorm_sub_le (p q : ℝ[X]) :
    polynomialCoeffOneNorm (p-q) ≤ polynomialCoeffOneNorm p + polynomialCoeffOneNorm q := by
  rw [coeffOneNorm_range (p-q) _ (natDegree_sub_le _ _),
    coeffOneNorm_range p _ (le_max_left _ _), coeffOneNorm_range q _ (le_max_right _ _),
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i _ => by simpa using abs_sub (p.coeff i) (q.coeff i))

/-- Constant multiplication scales coefficient mass exactly. [This is the stated conclusion](goal). -/
-- @node: coeffOneNorm_C_mul
lemma coeffOneNorm_C_mul (c : ℝ) (p : ℝ[X]) :
    polynomialCoeffOneNorm (C c * p) = |c| * polynomialCoeffOneNorm p := by
  rw [coeffOneNorm_range (C c * p) _ (natDegree_C_mul_le _ _),
    coeffOneNorm_range p _ le_rfl]
  simp only [coeff_C_mul, abs_mul, Finset.mul_sum]

/-- Finite sums preserve the coefficient triangle inequality. [Under the stated conditions](hyp:f). [This is the stated conclusion](goal). -/
-- @node: coeffOneNorm_sum_le
lemma coeffOneNorm_sum_le (s : Finset ℕ) (f : ℕ → ℝ[X]) :
    polynomialCoeffOneNorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, polynomialCoeffOneNorm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [polynomialCoeffOneNorm, polyCoeffL1]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (coeffOneNorm_add_le _ _).trans (add_le_add_right ih _)

/-- Submultiplicativity iterates to every finite power. [This is the stated conclusion](goal). -/
-- @node: coeffOneNorm_pow_le
lemma coeffOneNorm_pow_le (p : ℝ[X]) (j : ℕ) :
    polynomialCoeffOneNorm (p^j) ≤ (polynomialCoeffOneNorm p)^j := by
  induction j with
  | zero =>
      rw [pow_zero, pow_zero, coeffOneNorm_range 1 0 (by simp)]
      norm_num
  | succ j ih =>
      rw [pow_succ, pow_succ]
      exact (polynomialCoeffOneNorm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right ih (coeffOneNorm_nonneg p))

/-- The second-kind Chebyshev recurrence gives an exponential coefficient envelope. [This is the stated conclusion](goal). -/
-- @node: chebyshevU_coeffOneNorm_le
lemma chebyshevU_coeffOneNorm_le (n : ℕ) :
    polynomialCoeffOneNorm (Chebyshev.U ℝ (n : ℤ)) ≤ (3 : ℝ)^n := by
  have hX : polynomialCoeffOneNorm (X : ℝ[X]) = 1 := by
    rw [coeffOneNorm_range X 1 (by simp)]
    norm_num [Finset.sum_range_succ, coeff_X]
  induction n using Nat.twoStepInduction with
  | zero =>
      rw [Nat.cast_zero, Chebyshev.U_zero, coeffOneNorm_range 1 0 (by simp)]
      norm_num
  | one =>
      rw [Nat.cast_one, Chebyshev.U_one, ← C_ofNat, coeffOneNorm_C_mul, hX]
      norm_num
  | more n hn hn1 =>
      have heq : Chebyshev.U ℝ ((n+2 : ℕ) : ℤ) =
          C 2 * (X * Chebyshev.U ℝ ((n+1 : ℕ) : ℤ)) - Chebyshev.U ℝ (n : ℤ) := by
        convert Chebyshev.U_add_two ℝ (n : ℤ) using 1 <;> norm_num <;>
          simp only [C_ofNat] <;> ring
      rw [heq]
      calc
        _ ≤ polynomialCoeffOneNorm (C 2 * (X * Chebyshev.U ℝ ((n+1 : ℕ) : ℤ))) +
            polynomialCoeffOneNorm (Chebyshev.U ℝ (n : ℤ)) := coeffOneNorm_sub_le _ _
        _ ≤ 2 * (polynomialCoeffOneNorm X *
            polynomialCoeffOneNorm (Chebyshev.U ℝ ((n+1 : ℕ) : ℤ))) +
            polynomialCoeffOneNorm (Chebyshev.U ℝ (n : ℤ)) := by
          rw [coeffOneNorm_C_mul]; norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
          gcongr
          exact polynomialCoeffOneNorm_mul_le _ _
        _ ≤ 2 * (3 : ℝ)^(n+1) + (3 : ℝ)^n := by rw [hX, one_mul]; gcongr
        _ ≤ (3 : ℝ)^(n+2) := by
          rw [show n+2 = (n+1)+1 by omega]
          simp only [pow_succ]
          nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) n]

/-- Each coefficient is bounded by the whole coefficient mass. [This is the stated conclusion](goal). -/
-- @node: abs_coeff_le_coeffOneNorm
lemma abs_coeff_le_coeffOneNorm (p : ℝ[X]) (i : ℕ) :
    |p.coeff i| ≤ polynomialCoeffOneNorm p := by
  by_cases hi : i ∈ p.support
  · change |p.coeff i| ≤ ∑ j ∈ p.support, |p.coeff j|
    exact Finset.single_le_sum (f := fun j => |p.coeff j|) (fun _ _ => abs_nonneg _) hi
  · simp only [mem_support_iff, not_not] at hi
    rw [hi, abs_zero]
    exact coeffOneNorm_nonneg p

/-- The quadratic substitution in the declared localization weight has coefficient mass five. [This is the stated conclusion](goal). -/
-- @node: localizationQuadratic_coeffOneNorm
lemma localizationQuadratic_coeffOneNorm :
    polynomialCoeffOneNorm (1 - C 4 * X^2 : ℝ[X]) = 5 := by
  rw [coeffOneNorm_range _ 2 (by compute_degree)]
  norm_num [Finset.sum_range_succ, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_one]

/-- Direct finite Chebyshev algebra bounds the declared sixth-power weight exponentially in its degree. [Under the stated conditions](hyp:hm). [This is the stated conclusion](goal). -/
-- @node: qMPoly_coeffOneNorm_le
lemma qMPoly_coeffOneNorm_le (m : ℕ) (hm : 0 < m) :
    polynomialCoeffOneNorm (qMPoly m) ≤ (15 : ℝ)^(6*(m-1)) := by
  have hmreal : 0 < (m : ℝ) := by exact_mod_cast hm
  let f : ℕ → ℝ[X] := fun k => C ((Chebyshev.U ℝ (m-1 : ℕ)).coeff (2*k) / (m : ℝ)) *
    (1 - C 4 * X^2)^k
  have hterm : ∀ k ∈ Finset.range m,
      polynomialCoeffOneNorm (f k) ≤ (15 : ℝ)^(m-1) / m := by
    intro k hk
    have hk' : k ≤ m-1 := by have := Finset.mem_range.mp hk; omega
    have hc := (abs_coeff_le_coeffOneNorm (Chebyshev.U ℝ (m-1 : ℕ)) (2*k)).trans
      (chebyshevU_coeffOneNorm_le (m-1))
    dsimp [f]
    rw [coeffOneNorm_C_mul, abs_div, abs_of_pos hmreal]
    calc
      _ ≤ ((3 : ℝ)^(m-1) / m) * 5^k := by
        exact mul_le_mul (div_le_div_of_nonneg_right hc hmreal.le)
          ((coeffOneNorm_pow_le _ k).trans_eq (by rw [localizationQuadratic_coeffOneNorm]))
          (coeffOneNorm_nonneg _) (by positivity)
      _ ≤ ((3 : ℝ)^(m-1) / m) * 5^(m-1) := by gcongr; norm_num
      _ = (15 : ℝ)^(m-1) / m := by rw [div_mul_eq_mul_div, ← mul_pow]; norm_num
  have hbase : polynomialCoeffOneNorm (∑ k ∈ Finset.range m, f k) ≤ (15 : ℝ)^(m-1) := by
    apply (coeffOneNorm_sum_le _ _).trans
    calc
      _ ≤ ∑ k ∈ Finset.range m, (15 : ℝ)^(m-1) / m := Finset.sum_le_sum hterm
      _ = _ := by simp; field_simp
  change polynomialCoeffOneNorm ((∑ k ∈ Finset.range m, f k)^6) ≤ _
  apply (coeffOneNorm_pow_le _ 6).trans
  have hb := pow_le_pow_left₀ (coeffOneNorm_nonneg _) hbase 6
  simpa only [← pow_mul, Nat.mul_comm] using hb

/-- The declared polynomial's finite coefficient sum has the exponential degree envelope in S13. [Under the stated conditions](hyp:hm). [This is the stated conclusion](goal). -/
-- @node: qMPoly_coeff_mass_le
lemma qMPoly_coeff_mass_le (m : ℕ) (hm : 0 < m) :
    (∑ i ∈ Finset.range (6*(m-1)+1), |(qMPoly m).coeff i|) ≤
      (15 : ℝ)^(6*(m-1)) := by
  rw [← coeffOneNorm_range (qMPoly m) _ (qMPoly_natDegree_le m)]
  exact qMPoly_coeffOneNorm_le m hm

/-- The exact inverse-heat variance has a public exponential envelope, without a derivative premise. [Under the stated conditions](hyp:hkappa,hm). [This is the stated conclusion](goal). -/
-- @node: ellM_Vq_exponential_envelope
lemma ellM_Vq_exponential_envelope (kappa sigma : ℝ) (hkappa : 0 ≤ kappa)
    (m : ℕ) (hm : 0 < m) :
    Vq kappa sigma (ellM sigma m) ≤
      16 * weightMoment kappa (fun _ => 1) *
        ((15 : ℝ)^(2*(6*(m-1))) *
          (1 + (6*(m-1) : ℕ)*sigma^2)^(6*(m-1))) := by
  have hw : 0 ≤ weightMoment kappa (fun _ => 1) :=
    integral_nonneg (fun t => mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (by norm_num))
  apply (ellM_Vq_le_coeff_mass kappa sigma hkappa m).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hw)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have hb := pow_le_pow_left₀
    (Finset.sum_nonneg (fun i (_ : i ∈ Finset.range (6*(m-1)+1)) => abs_nonneg ((qMPoly m).coeff i)))
    (qMPoly_coeff_mass_le m hm) 2
  simpa only [← pow_mul, Nat.mul_comm] using hb

/-- The unit latent weight has weighted mass at most one for nonnegative design exponents. [Under the stated conditions](hyp:hkappa). [This is the stated conclusion](goal). -/
-- @node: constant_weightMoment_le_one
lemma constant_weightMoment_le_one (kappa : ℝ) (hkappa : 0 ≤ kappa) :
    weightMoment kappa (fun _ => 1) ≤ 1 := by
  have hi : Integrable (fun t : ℝ => |t| ^ kappa)
      (volume.restrict (Icc (-1/2 : ℝ) (1/2))) := by
    simpa only [qM_one, mul_one] using qM_weighted_integrable kappa hkappa 1
  have hb : ∀ᵐ t ∂volume.restrict (Icc (-1/2 : ℝ) (1/2)), |t| ^ kappa ≤ 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    apply Real.rpow_le_one (abs_nonneg _) _ hkappa
    rw [abs_le]
    constructor <;> linarith [ht.1, ht.2]
  have h := integral_mono_ae hi (integrable_const (1 : ℝ)) hb
  norm_num [weightMoment, Real.volume_Icc] at h ⊢
  exact h

/-- S13 holds with explicit universal coefficient base and prefactor. [Under the stated conditions](hyp:hkappa,hm). [This is the stated conclusion](goal). -/
-- @node: ellM_Vq_explicit_bound
lemma ellM_Vq_explicit_bound (kappa sigma : ℝ) (hkappa : 0 ≤ kappa)
    (m : ℕ) (hm : 0 < m) :
    Vq kappa sigma (ellM sigma m) ≤
      16 * (15 : ℝ)^(2*(6*(m-1))) *
        (1 + (6*(m-1) : ℕ)*sigma^2)^(6*(m-1)) := by
  apply (ellM_Vq_exponential_envelope kappa sigma hkappa m hm).trans
  calc
    _ ≤ 16 * 1 * ((15 : ℝ)^(2*(6*(m-1))) *
        (1 + (6*(m-1) : ℕ)*sigma^2)^(6*(m-1))) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left (constant_weightMoment_le_one kappa hkappa) (by norm_num)
    _ = _ := by ring

end CausalSmith.Stat.NoisydoseWeakdesignTransition
