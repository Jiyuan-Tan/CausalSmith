module
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.CitedGates
public import Mathlib.Algebra.Polynomial.Sequence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Shifted Legendre basis and derivative coefficients

Polynomial spanning, orthogonality, and integration by parts for the endpoint witnesses.
-/

@[expose] public section

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology

namespace CausalSmith.Stat.RdTruesideNoiseFrontier

/-- The usual forward shifted Legendre polynomial. Given [the displayed inputs and assumptions](hyp:j,t), [this definition specifies the stated object](goal). -/
def shiftedLegendre (j : ℕ) (t : ℝ) : ℝ := legendreP j (2*t - 1)
/-- Given the [Legendre degree](hyp:j), Legendre evaluation is [continuous on the real line](goal). -/
@[fun_prop] lemma legendreP_continuous (j : ℕ) : Continuous (legendreP j) := by
  unfold legendreP
  fun_prop
/-- Affine substitution transfers cited Legendre orthogonality to the unit interval. Given [the displayed inputs and assumptions](hyp:hleg,j,k), [the stated mathematical conclusion holds](goal). -/
lemma shiftedLegendre_orthogonal (hleg : ClassicalLegendreFacts) (j k : ℕ) :
    (∫ t in (0 : ℝ)..1, legendreP j (2*t-1) * legendreP k (2*t-1)) =
      if j = k then 1 / (2 * (j : ℝ) + 1) else 0 := by
  have h := intervalIntegral.integral_comp_mul_add
    (fun t => legendreP j t * legendreP k t) (a := (0 : ℝ)) (b := 1)
    (c := 2) (by norm_num) (-1)
  norm_num only [mul_zero, zero_add, mul_one, add_neg_cancel,
    show (2 : ℝ) + -1 = 1 by norm_num, smul_eq_mul] at h
  simp only [sub_eq_add_neg] at ⊢
  rw [h, (hleg j k).1]
  split_ifs <;> ring
/-- Real coefficient versions of the reversed shifted Legendre polynomials form a
polynomial sequence, with the polynomial at index j having degree j. Given the displayed inputs, [this definition specifies the stated object](goal). -/
def reversedLegendreSequence : Polynomial.Sequence ℝ where
  elems' j := (Polynomial.shiftedLegendre j).map (Int.castRingHom ℝ)
  degree_eq' j := by
    rw [Polynomial.degree_map_eq_of_injective (Int.cast_injective),
      Polynomial.degree_shiftedLegendre]

/-- Reflection relates the polynomial sequence to the forward shifted Legendre functions. Given [the displayed inputs and assumptions](hyp:j,t), [the stated mathematical conclusion holds](goal). -/
lemma reversedLegendreSequence_eval (j : ℕ) (t : ℝ) :
    (reversedLegendreSequence j).eval t = (-1 : ℝ)^j * legendreP j (2*t-1) := by
  change Polynomial.eval t ((Polynomial.shiftedLegendre j).map (Int.castRingHom ℝ)) = _
  rw [Polynomial.eval_map]
  change Polynomial.aeval t (Polynomial.shiftedLegendre j) = _
  have h := Polynomial.shiftedLegendre_eval_symm j t
  simpa only [legendreP, show (1 - (2*t-1))/2 = 1-t by ring] using h

/-- Cited Legendre orthogonality and the polynomial-sequence spanning theorem make
any polynomial of degree below j orthogonal to the jth shifted Legendre function. Given [the displayed inputs and assumptions](hyp:hleg,p,j,hp), [the stated mathematical conclusion holds](goal). -/
lemma polynomial_shiftedLegendre_orthogonal (hleg : ClassicalLegendreFacts)
    (p : Polynomial ℝ) (j : ℕ) (hp : p.degree < j) :
    (∫ t in (0 : ℝ)..1, p.eval t * legendreP j (2*t-1)) = 0 := by
  have hspan : p ∈ Submodule.span ℝ (reversedLegendreSequence '' Iio j) := by
    rw [Polynomial.Sequence.span_degreeLT]
    · exact Polynomial.mem_degreeLT.mpr hp
    · intro i hi
      exact isUnit_iff_ne_zero.mpr
        (Polynomial.leadingCoeff_ne_zero.mpr (reversedLegendreSequence.ne_zero i))
  clear hp
  induction hspan using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨k, hk, rfl⟩ := hq
    simp_rw [reversedLegendreSequence_eval, mul_assoc]
    rw [intervalIntegral.integral_const_mul, shiftedLegendre_orthogonal hleg]
    simp [show k ≠ j by exact ne_of_lt hk]
  | zero => simp
  | add p q _ _ hp hq =>
    simp only [Polynomial.eval_add, add_mul]
    rw [intervalIntegral.integral_add, hp, hq, add_zero]
    all_goals apply Continuous.intervalIntegrable; fun_prop
  | smul c p _ hp =>
    simp only [Polynomial.eval_smul, smul_eq_mul, mul_assoc]
    rw [intervalIntegral.integral_const_mul, hp, mul_zero]

/-- Given the [Legendre degree](hyp:j), shifted Legendre evaluation is [differentiable on the real line](goal). -/
@[fun_prop] lemma shiftedLegendre_differentiable (j : ℕ) :
    Differentiable ℝ (shiftedLegendre j) := by
  unfold shiftedLegendre legendreP
  have hp : Differentiable ℝ (fun x : ℝ =>
      Polynomial.aeval x (Polynomial.shiftedLegendre j)) :=
    Polynomial.differentiable_aeval _
  exact hp.comp (show Differentiable ℝ (fun t : ℝ => (1 - (2*t-1))/2) by fun_prop)


/-- Orthogonal projection reconstructs every polynomial of degree below the cutoff. Given [the displayed inputs and assumptions](hyp:hleg,p,j,hp,t), [the stated mathematical conclusion holds](goal). -/
lemma polynomial_shiftedLegendre_expansion (hleg : ClassicalLegendreFacts)
    (p : Polynomial ℝ) (j : ℕ) (hp : p.degree < j) (t : ℝ) :
    p.eval t = ∑ k ∈ Finset.range j, (2*(k : ℝ)+1) *
      (∫ x in (0 : ℝ)..1, p.eval x * shiftedLegendre k x) * shiftedLegendre k t := by
  have hspan : p ∈ Submodule.span ℝ (reversedLegendreSequence '' Iio j) := by
    rw [Polynomial.Sequence.span_degreeLT]
    · exact Polynomial.mem_degreeLT.mpr hp
    · intro i hi
      exact isUnit_iff_ne_zero.mpr
        (Polynomial.leadingCoeff_ne_zero.mpr (reversedLegendreSequence.ne_zero i))
  clear hp
  induction hspan using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨i, hi, rfl⟩ := hq
    simp_rw [reversedLegendreSequence_eval, mul_assoc]
    simp_rw [shiftedLegendre, intervalIntegral.integral_const_mul,
      shiftedLegendre_orthogonal hleg]
    have hw : 2*(i : ℝ)+1 ≠ 0 := by positivity
    have hil : i < j := hi
    simp [Finset.sum_ite_eq, Finset.mem_range, hil, mul_ite, ite_mul]
    field_simp [hw]
  | zero => simp
  | add p q _ _ hp hq =>
    simp only [Polynomial.eval_add, add_mul]
    have hint (r : Polynomial ℝ) (k : ℕ) : IntervalIntegrable
        (fun x => r.eval x * shiftedLegendre k x) volume 0 1 := by
      apply Continuous.intervalIntegrable
      unfold shiftedLegendre
      fun_prop
    simp_rw [intervalIntegral.integral_add (hint p _) (hint q _)]
    rw [hp, hq, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  | smul c p _ hp =>
    simp only [Polynomial.eval_smul, smul_eq_mul, mul_assoc]
    simp_rw [intervalIntegral.integral_const_mul]
    rw [hp, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring

/-- A real polynomial realizing the forward shifted Legendre function. Given [the displayed inputs and assumptions](hyp:j), [this definition specifies the stated object](goal). -/
def forwardLegendrePolynomial (j : ℕ) : Polynomial ℝ :=
  Polynomial.C ((-1 : ℝ)^j) * reversedLegendreSequence j

/-- The two orientation signs cancel in the forward polynomial evaluation. Given [the displayed inputs and assumptions](hyp:j,t), [the stated mathematical conclusion holds](goal). -/
lemma forwardLegendrePolynomial_eval (j : ℕ) (t : ℝ) :
    (forwardLegendrePolynomial j).eval t = shiftedLegendre j t := by
  simp only [forwardLegendrePolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    reversedLegendreSequence_eval, ← mul_assoc, ← mul_pow]
  norm_num [shiftedLegendre]

/-- Multiplying by the nonzero orientation sign preserves degree. Given [the displayed inputs and assumptions](hyp:j), [the stated mathematical conclusion holds](goal). -/
lemma forwardLegendrePolynomial_degree (j : ℕ) :
    (forwardLegendrePolynomial j).degree = j := by
  rw [forwardLegendrePolynomial, Polynomial.degree_C_mul (by positivity)]
  exact reversedLegendreSequence.degree_eq j

/-- Differentiation lowers the forward polynomial degree strictly below its index. Given [the displayed inputs and assumptions](hyp:j), [the stated mathematical conclusion holds](goal). -/
lemma forwardLegendrePolynomial_derivative_degree (j : ℕ) :
    (forwardLegendrePolynomial j).derivative.degree < j := by
  rw [← forwardLegendrePolynomial_degree j]
  apply Polynomial.degree_derivative_lt
  intro hz
  have hd := forwardLegendrePolynomial_degree j
  rw [hz, Polynomial.degree_zero] at hd
  exact (WithBot.bot_ne_coe hd)

/-- The forward polynomial derivative is the ordinary function derivative. Given [the displayed inputs and assumptions](hyp:j,t), [the stated mathematical conclusion holds](goal). -/
lemma forwardLegendrePolynomial_derivative_eval (j : ℕ) (t : ℝ) :
    (forwardLegendrePolynomial j).derivative.eval t = deriv (shiftedLegendre j) t := by
  rw [← Polynomial.deriv]
  congr 1
  funext x
  exact forwardLegendrePolynomial_eval j x

/-- The cited reflection symmetry and left endpoint fix both shifted endpoint values. Given [the displayed inputs and assumptions](hyp:hleg,j), [the stated mathematical conclusion holds](goal). -/
lemma shiftedLegendre_endpoints (hleg : ClassicalLegendreFacts) (j : ℕ) :
    shiftedLegendre j 0 = (-1 : ℝ)^j ∧ shiftedLegendre j 1 = 1 := by
  constructor
  · simpa [shiftedLegendre] using (hleg j 0).2.2.2
  · have h := (hleg j 0).2.1 (-1)
    rw [(hleg j 0).2.2.2, ← mul_pow] at h
    norm_num at h
    norm_num [shiftedLegendre] at ⊢
    exact h

/-- The endpoint term selects exactly the odd derivative modes. Given [the displayed inputs and assumptions](hyp:j,k,hk), [the stated mathematical conclusion holds](goal). -/
lemma legendre_endpoint_parity (j k : ℕ) (hk : k < j) :
    1 - (-1 : ℝ)^k * (-1 : ℝ)^j = if Odd (j-k) then 2 else 0 := by
  have hjpow : (-1 : ℝ)^j = (-1 : ℝ)^(j-k) * (-1 : ℝ)^k := by
    rw [← pow_add, Nat.sub_add_cancel hk.le]
  rw [hjpow]
  have hs : (-1 : ℝ)^k * ((-1 : ℝ)^(j-k) * (-1 : ℝ)^k) = (-1 : ℝ)^(j-k) := by
    calc
      _ = (-1 : ℝ)^(j-k) * ((-1 : ℝ)^k * (-1 : ℝ)^k) := by ring
      _ = _ := by rw [← mul_pow]; norm_num
  rw [hs]
  rcases Nat.even_or_odd (j-k) with he | ho
  · rw [if_neg (by exact Nat.not_odd_iff_even.mpr he), he.neg_one_pow]; norm_num
  · rw [if_pos ho, ho.neg_one_pow]; norm_num

/-- Integration by parts removes the lower-degree differentiated mode and leaves the
    parity-selected boundary coefficient of the forward Legendre derivative. Given [the displayed inputs and assumptions](hyp:hleg,j,k,hk), [the stated mathematical conclusion holds](goal). -/
lemma shiftedLegendre_derivative_inner (hleg : ClassicalLegendreFacts)
    (j k : ℕ) (hk : k < j) :
    (∫ x in (0 : ℝ)..1,
      (forwardLegendrePolynomial j).derivative.eval x * shiftedLegendre k x) =
      if Odd (j-k) then 2 else 0 := by
  have hz : (∫ x in (0 : ℝ)..1,
      (forwardLegendrePolynomial k).derivative.eval x * shiftedLegendre j x) = 0 :=
    polynomial_shiftedLegendre_orthogonal hleg _ j
      ((forwardLegendrePolynomial_derivative_degree k).trans (by exact_mod_cast hk))
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (b := 1)
    (u := fun x => (forwardLegendrePolynomial k).eval x)
    (v := fun x => (forwardLegendrePolynomial j).eval x)
    (fun x hx => (forwardLegendrePolynomial k).hasDerivAt x)
    (fun x hx => (forwardLegendrePolynomial j).hasDerivAt x)
    ((forwardLegendrePolynomial k).derivative.continuous.intervalIntegrable 0 1)
    ((forwardLegendrePolynomial j).derivative.continuous.intervalIntegrable 0 1)
  simp_rw [forwardLegendrePolynomial_eval] at hparts
  rw [hz, (shiftedLegendre_endpoints hleg k).1, (shiftedLegendre_endpoints hleg k).2,
    (shiftedLegendre_endpoints hleg j).1, (shiftedLegendre_endpoints hleg j).2] at hparts
  simp only [one_mul, sub_zero] at hparts
  rw [legendre_endpoint_parity j k hk] at hparts
  simpa only [mul_comm] using hparts

/-- Expansion of the lower-degree derivative in the orthogonal shifted basis. Given [the displayed inputs and assumptions](hyp:hleg,j,t), [the stated mathematical conclusion holds](goal). -/
lemma shiftedLegendre_derivative_expansion (hleg : ClassicalLegendreFacts)
    (j : ℕ) (t : ℝ) :
    deriv (shiftedLegendre j) t =
      2 * ∑ k ∈ (Finset.range j).filter (fun k => Odd (j-k)),
        (2*(k : ℝ)+1) * shiftedLegendre k t := by
  rw [← forwardLegendrePolynomial_derivative_eval,
    polynomial_shiftedLegendre_expansion hleg _ j
      (forwardLegendrePolynomial_derivative_degree j)]
  rw [Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [shiftedLegendre_derivative_inner hleg j k (Finset.mem_range.mp hk)]
  split_ifs <;> ring

end CausalSmith.Stat.RdTruesideNoiseFrontier
