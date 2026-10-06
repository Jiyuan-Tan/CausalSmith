module
public import Causalean.Mathlib.Analysis.SpecialFunctions.Jacobi.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.RingTheory.Polynomial.Pochhammer

/-! Standard Jacobi normalization, explicit smooth filtering, and the two packet constructions. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory Set
open scoped BigOperators
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition
open Causalean.Mathlib.Analysis.SpecialFunctions.Jacobi
-- @env: S4
variable (kappa : ℝ) (m : ℕ)

/-- DLMF 18.5.7 normalization of the reused shifted hypergeometric polynomial. -/
def stdJacobi (a b : ℝ) (j : ℕ) (z : ℝ) : ℝ :=
  rising (a+1) j / (j.factorial : ℝ) * jacobiShifted j a b ((1-z)/2)
/-- Generalized real binomial coefficient defined by the falling factorial divided by the integer factorial. -/
def genBinom (v : ℝ) (i : ℕ) : ℝ := (descPochhammer ℝ i).eval v / (i.factorial : ℝ)
open Polynomial

/-- The local falling-factorial binomial agrees with the binomial-ring coefficient. [This is the stated conclusion](goal). [This is the stated conclusion](goal). [This is the stated conclusion](goal). [This is the stated conclusion](goal). -/
-- @node: genBinom_eq_choose
lemma genBinom_eq_choose (v : ℝ) (i : ℕ) : genBinom v i = Ring.choose v i := by
  rw [Ring.choose_eq_smul, smul_eq_mul, Polynomial.descPochhammer_smeval_eq_ascPochhammer,
    Polynomial.ascPochhammer_smeval_eq_eval, genBinom, descPochhammer_eval_eq_ascPochhammer]
  ring
/-- Vandermonde convolution for the local generalized real binomial coefficients. [This is the stated conclusion](goal). -/
-- @node: genBinom_vandermonde
lemma genBinom_vandermonde (A B : ℝ) (m : ℕ) :
    genBinom (A+B) m = ∑ i ∈ Finset.range (m+1), genBinom A i * genBinom B (m-i) := by
  simp_rw [genBinom_eq_choose]
  simpa only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Nat.succ_eq_add_one] using
    Ring.add_choose_eq m (Commute.all A B)
/-- Choosing a second subset factors a generalized binomial coefficient. [Under the stated conditions](hyp:hm,hi). [This is the stated conclusion](goal). -/
-- @node: genBinom_choose_product
lemma genBinom_choose_product (A : ℝ) (j m i : ℕ) (hm : m ≤ j) (hi : i ≤ m) :
    genBinom A (j-i) * ((j-i).choose (m-i) : ℝ) =
      genBinom A (j-m) * genBinom (A-(j-m : ℕ)) (m-i) := by
  simp_rw [genBinom_eq_choose]
  have h := Ring.choose_smul_choose A (show j-m ≤ j-i by omega)
  have he : (j-i) - (j-m) = m-i := by omega
  rw [nsmul_eq_mul, ← Nat.choose_symm (show j-m ≤ j-i by omega), he] at h
  simpa only [mul_comm] using h
/-- Expanding the Bernstein basis gives a Vandermonde convolution in each coefficient. [This is the stated conclusion](goal). -/
-- @node: genBinom_bernstein_poly
lemma genBinom_bernstein_poly (A B : ℝ) (j : ℕ) :
    (∑ i ∈ Finset.range (j+1), C (genBinom A (j-i) * genBinom B i) *
      (X ^ i * (X+1)^(j-i)) : ℝ[X]) =
    ∑ m ∈ Finset.range (j+1), C (genBinom A (j-m) * genBinom (A+B-(j-m : ℕ)) m) * X^m := by
  ext m
  have hr : (∑ k ∈ Finset.range (j+1),
      C (genBinom A (j-k) * genBinom (A+B-(j-k : ℕ)) k) * X^k).coeff m =
      if m ≤ j then genBinom A (j-m) * genBinom (A+B-(j-m : ℕ)) m else 0 := by
    simp only [finsetSum_coeff, coeff_C_mul_X_pow]
    simp [Finset.mem_range, Nat.lt_succ_iff]
  rw [hr]
  simp only [finsetSum_coeff, coeff_C_mul, coeff_X_pow_mul', coeff_X_add_one_pow]
  by_cases hm : m ≤ j
  · rw [if_pos hm]
    have htrim :
        (∑ i ∈ Finset.range (j+1), genBinom A (j-i) * genBinom B i *
          (if i ≤ m then ((j-i).choose (m-i) : ℝ) else 0)) =
        ∑ i ∈ Finset.range (m+1), genBinom A (j-i) * genBinom B i *
          ((j-i).choose (m-i) : ℝ) := by
      symm
      calc
        _ = ∑ i ∈ Finset.range (m+1), genBinom A (j-i) * genBinom B i *
            (if i ≤ m then ((j-i).choose (m-i) : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [if_pos (by have := Finset.mem_range.mp hi; omega)]
        _ = _ := Finset.sum_subset (Finset.range_mono (by omega)) (by
          intro i hi hin
          rw [if_neg (by simp only [Finset.mem_range] at hin; omega), mul_zero])
    rw [htrim]
    calc
      _ = ∑ i ∈ Finset.range (m+1), genBinom A (j-m) *
          (genBinom B i * genBinom (A-(j-m : ℕ)) (m-i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' : i ≤ m := by have := Finset.mem_range.mp hi; omega
        calc
          _ = (genBinom A (j-i) * ((j-i).choose (m-i) : ℝ)) * genBinom B i := by ring
          _ = _ := by rw [genBinom_choose_product A j m i hm hi']; ring
      _ = _ := by
        rw [← Finset.mul_sum, ← genBinom_vandermonde]
        congr 2
        ring
  · have hm' : j < m := by omega
    rw [if_neg hm]
    apply Finset.sum_eq_zero
    intro i hi
    have hi' : i ≤ j := by have := Finset.mem_range.mp hi; omega
    rw [if_pos (by omega), Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]
/-- Split a rising factorial at an index no larger than its order. [Under the stated conditions](hyp:hm). [This is the stated conclusion](goal). -/
-- @node: rising_split
lemma rising_split (a : ℝ) (j m : ℕ) (hm : m ≤ j) :
    rising a m * rising (a+m) (j-m) = rising a j := by
  have h := congrArg (Polynomial.eval a) (ascPochhammer_mul ℝ m (j-m))
  simpa only [eval_mul, eval_comp, eval_add, eval_X, eval_natCast, rising,
    Nat.add_sub_of_le hm] using h
/-- The normalized hypergeometric coefficient equals the corresponding binomial product. [Under the stated conditions](hyp:ha,hm). [This is the stated conclusion](goal). -/
-- @node: jacobi_coefficient_binomial
lemma jacobi_coefficient_binomial (a b : ℝ) (ha : -1/2 < a) (j m : ℕ) (hm : m ≤ j) :
    rising (a+1) j / (j.factorial : ℝ) * (j.choose m : ℝ) *
      (rising (j+a+b+1) m / rising (a+1) m) =
    genBinom (j+a) (j-m) * genBinom (j+a+b+m) m := by
  have hpos : 0 < a+1 := by linarith
  have hden : rising (a+1) m ≠ 0 := ne_of_gt (rising_pos _ _ hpos)
  have hfac (n : ℕ) : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hsplit := rising_split (a+1) j m hm
  have hchoose := congrArg (fun n : ℕ => (n : ℝ)) (Nat.choose_mul_factorial_mul_factorial hm)
  push_cast at hchoose
  have he1 : (j : ℝ)+a-(j-m : ℕ)+1 = (a+1)+m := by rw [Nat.cast_sub hm]; ring
  have he2 : (j : ℝ)+a+b+m-(m : ℝ)+1 = (j : ℝ)+a+b+1 := by ring
  simp only [genBinom, descPochhammer_eval_eq_ascPochhammer, he1, he2]
  change _ = rising ((a+1)+m) (j-m) / ((j-m).factorial : ℝ) *
    (rising (j+a+b+1) m / (m.factorial : ℝ))
  field_simp [hden, hfac]
  rw [← hchoose]
  rw [← hsplit]
  ring

/-- Standard Jacobi's generalized binomial representation (NIST DLMF 18.5.8).
This discharged citation is a build-inline algebraic obligation, not a gate. [Under the stated conditions](hyp:ha,hb). [This is the stated conclusion](goal). -/
-- @node: lem:jacobi-binomial
lemma stdJacobi_binomial_repr (a b : ℝ) (ha : -1/2 < a) (hb : -1/2 < b) (j : ℕ) (z : ℝ) :
    stdJacobi a b j z = (2 : ℝ)^(-(j : ℤ)) *
      ∑ i ∈ Finset.range (j+1), genBinom (j+a) i * genBinom (j+b) (j-i) *
        (z-1)^(j-i) * (z+1)^i := by
  let y : ℝ := (z-1)/2
  have hstd : stdJacobi a b j z =
      ∑ m ∈ Finset.range (j+1),
        genBinom (j+a) (j-m) * genBinom (j+a+b+m) m * y^m := by
    unfold stdJacobi jacobiShifted
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    have hm' : m ≤ j := by have := Finset.mem_range.mp hm; omega
    have hsign : (-1 : ℝ)^m * ((1-z)/2)^m = y^m := by
      rw [← mul_pow]
      congr 1
      dsimp [y]
      ring
    calc
      _ = (rising (a+1) j / (j.factorial : ℝ) * (j.choose m : ℝ) *
          (rising (j+a+b+1) m / rising (a+1) m)) *
          ((-1 : ℝ)^m * ((1-z)/2)^m) := by ring
      _ = _ := by rw [hsign, jacobi_coefficient_binomial a b ha j m hm']
  have hpoly := congrArg (Polynomial.eval y) (genBinom_bernstein_poly (j+a) (j+b) j)
  simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, eval_add, eval_one] at hpoly
  have hcoeff (m : ℕ) (hm : m ≤ j) :
      (j : ℝ)+a+((j : ℝ)+b)-(j-m : ℕ) = (j : ℝ)+a+b+m := by
    rw [Nat.cast_sub hm]
    ring
  have hbern : stdJacobi a b j z =
      ∑ i ∈ Finset.range (j+1), genBinom (j+a) (j-i) * genBinom (j+b) i *
        (y^i * (y+1)^(j-i)) := by
    rw [hstd, hpoly]
    apply Finset.sum_congr rfl
    intro m hm
    rw [hcoeff m (by have := Finset.mem_range.mp hm; omega)]
  have hreflect := Finset.sum_range_reflect
    (fun i => genBinom (j+a) (j-i) * genBinom (j+b) i * (y^i * (y+1)^(j-i))) (j+1)
  simp only [Nat.add_sub_cancel] at hreflect
  rw [hbern, ← hreflect, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ j := by have := Finset.mem_range.mp hi; omega
  rw [Nat.sub_sub_self hi']
  have hy : y+1 = (z+1)/2 := by dsimp [y]; ring
  have hp : (2 : ℝ)^(j-i) * 2^i = 2^j := by
    rw [← pow_add, Nat.sub_add_cancel hi']
  rw [hy]
  dsimp [y]
  rw [div_pow, div_pow, zpow_neg, zpow_natCast]
  field_simp
  rw [← hp]
  ring

/-- Standard Jacobi weight on the unit symmetric interval. -/
def jacobiWeight (a b z : ℝ) : ℝ := (1-z)^a * (1+z)^b
/-- Squared Lebesgue norm of the standard Jacobi polynomial under its Jacobi weight. -/
def jacobiSqNorm (a b : ℝ) (j : ℕ) : ℝ :=
  ∫ z in Icc (-1 : ℝ) 1, jacobiWeight a b z * (stdJacobi a b j z)^2
/-- A concrete nonnegative smooth bump supported inside (1,2), positive on [5/4,7/4]. -/
def packetFilter (s : ℝ) : ℝ :=
  if s ∈ Ioo (9/8 : ℝ) (15/8) then Real.exp (-1/((s-9/8)*(15/8-s))) else 0

/-- Finite spectral kernel of the standard Jacobi polynomials with a smooth cutoff and their integral norms. -/
def filteredJacobiKernel (a b : ℝ) (eta : ℝ → ℝ) (m : ℕ) (x y : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (2*m+1), eta ((j : ℝ)/m) * stdJacobi a b j x * stdJacobi a b j y /
    jacobiSqNorm a b j

/-- Endpoint kernel at positive degeneracy, and the symmetric interior kernel at zero degeneracy. -/
def packetKernel (kappa : ℝ) (m : ℕ) (z : ℝ) : ℝ :=
  if 0 < kappa then filteredJacobiKernel 4 ((kappa-1)/2) packetFilter m (-1) z
  else filteredJacobiKernel 4 4 packetFilter m 0 z -- @realizes PacketHandle(filtered endpoint or symmetric interior kernel)
/-- The normalized tapered packet, zero outside its support; denominator positivity is a theorem. -/
-- @node: def:packet-handle
def packetPsi (kappa : ℝ) (m : ℕ) (u : ℝ) : ℝ :=
  if u ∈ Icc (-1 : ℝ) 1 then
    (1-u^2)^4 * (if 0 < kappa then packetKernel kappa m (2*u^2-1) / packetKernel kappa m (-1)
      else packetKernel kappa m u / packetKernel kappa m 0)
  else 0 -- @realizes psim(explicit even zero-extended filtered-Jacobi sequence)

/-- Full packet conclusion, including positive normalization and all raw cancellations. -/
def PacketBounds (kappa C c : ℝ) (m : ℕ) : Prop :=
  (0 < (if 0 < kappa then packetKernel kappa m (-1) else packetKernel kappa m 0)) ∧
  Function.Even (packetPsi kappa m) ∧ ContDiff ℝ 1 (packetPsi kappa m) ∧
  (∀ u, u ∉ Icc (-1 : ℝ) 1 → packetPsi kappa m u = 0) ∧
  packetPsi kappa m 0 = 1 ∧
  (∀ u, |packetPsi kappa m u| ≤ C) ∧
  (∀ u, |deriv (packetPsi kappa m) u| ≤ C*m) ∧
  (∫ u in Icc (-1 : ℝ) 1, |u|^kappa * |packetPsi kappa m u|) ≤ C*(m : ℝ)^(-kappa-1) ∧
  (∫ u in Icc (-1 : ℝ) 1, |u|^kappa * (packetPsi kappa m u)^2) ≤ C*(m : ℝ)^(-kappa-1) ∧
  (∀ j : ℕ, (j : ℝ) < c*m → ∫ u in Icc (-1 : ℝ) 1, |u|^kappa * u^j * packetPsi kappa m u = 0)
end CausalSmith.Stat.NoisydoseWeakdesignTransition
