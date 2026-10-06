module
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.Procedure
public import Mathlib.RingTheory.Polynomial.Hermite.Basic

/-!
# Finite coefficient algebra for the inverse heat transform

The transform is linear, its truncation is independent of an upper degree bound,
and its action on every monomial has explicit descending-factorial coefficients.
These facts reduce the covariance roadmap's finite Hermite identity to monomials.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace CausalSmith.Stat.RdTruesideNoiseFrontier

/-- The inverse heat operator with an arbitrary public degree cutoff. Given [the displayed inputs and assumptions](hyp:m,σ,p), [this definition specifies the stated object](goal). -/
def finiteInverseHeat (m : ℕ) (σ : ℝ) (p : Polynomial ℝ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (m / 2 + 1),
    Polynomial.C ((-σ^2/2)^k / (Nat.factorial k : ℝ)) * polyDeriv (2*k) p

/-- Iterated polynomial differentiation distributes over finite sums. Given [the displayed inputs and assumptions](hyp:ι,j,s,p), [the stated mathematical conclusion holds](goal). -/
lemma polyDeriv_sum {ι : Type*} (j : ℕ) (s : Finset ι) (p : ι → Polynomial ℝ) :
    polyDeriv j (∑ i ∈ s, p i) = ∑ i ∈ s, polyDeriv j (p i) := by
  exact Polynomial.iterate_derivative_sum j s p

/-- Scalar polynomial coefficients commute with iterated differentiation. Given [the displayed inputs and assumptions](hyp:j,a,p), [the stated mathematical conclusion holds](goal). -/
lemma polyDeriv_C_mul (j : ℕ) (a : ℝ) (p : Polynomial ℝ) :
    polyDeriv j (Polynomial.C a * p) = Polynomial.C a * polyDeriv j p := by
  exact Polynomial.iterate_derivative_C_mul a p j

/-- Every monomial derivative has its descending-factorial coefficient, including
zero derivatives above the monomial degree. Given [the displayed inputs and assumptions](hyp:j,n), [the stated mathematical conclusion holds](goal). -/
lemma polyDeriv_X_pow (j n : ℕ) :
    polyDeriv j (Polynomial.X^n : Polynomial ℝ) =
      Polynomial.C (Nat.descFactorial n j : ℝ) * Polynomial.X^(n-j) := by
  exact Polynomial.iterate_derivative_X_pow_eq_C_mul n j

/-- Derivatives above any upper degree bound vanish. Given [the displayed inputs and assumptions](hyp:p,j,m,hp,hj), [the stated mathematical conclusion holds](goal). -/
lemma polyDeriv_eq_zero_of_degree_lt (p : Polynomial ℝ) (j m : ℕ)
    (hp : p.natDegree ≤ m) (hj : m < j) : polyDeriv j p = 0 := by
  exact Polynomial.iterate_derivative_eq_zero (hp.trans_lt hj)

/-- The finite heat operator distributes over finite polynomial sums. Given [the displayed inputs and assumptions](hyp:ι,m,σ,s,p), [the stated mathematical conclusion holds](goal). -/
lemma finiteInverseHeat_sum {ι : Type*} (m : ℕ) (σ : ℝ) (s : Finset ι)
    (p : ι → Polynomial ℝ) :
    finiteInverseHeat m σ (∑ i ∈ s, p i) = ∑ i ∈ s, finiteInverseHeat m σ (p i) := by
  simp only [finiteInverseHeat, polyDeriv_sum, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- The finite heat operator commutes with scalar polynomial coefficients. Given [the displayed inputs and assumptions](hyp:m,σ,a,p), [the stated mathematical conclusion holds](goal). -/
lemma finiteInverseHeat_C_mul (m : ℕ) (σ a : ℝ) (p : Polynomial ℝ) :
    finiteInverseHeat m σ (Polynomial.C a * p) =
      Polynomial.C a * finiteInverseHeat m σ p := by
  simp only [finiteInverseHeat, polyDeriv_C_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- Enlarging a degree cutoff adds only identically zero heat terms. Given [the displayed inputs and assumptions](hyp:p,σ,m,M,hp,hmM), [the stated mathematical conclusion holds](goal). -/
lemma finiteInverseHeat_cutoff (p : Polynomial ℝ) (σ : ℝ) (m M : ℕ)
    (hp : p.natDegree ≤ m) (hmM : m ≤ M) :
    finiteInverseHeat M σ p = finiteInverseHeat m σ p := by
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega : m/2+1 ≤ M/2+1))
  intro k hk hknot
  have hj : m < 2*k := by
    have hnot : ¬ k < m/2+1 := by simpa using hknot
    omega
  rw [polyDeriv_eq_zero_of_degree_lt p (2*k) m hp hj, mul_zero]

/-- The exact scalar action of inverse heat on a monomial is a finite sum with
no convergence assumptions. Given [the displayed inputs and assumptions](hyp:m,n,σ,w), [the stated mathematical conclusion holds](goal). -/
lemma finiteInverseHeat_X_pow_eval (m n : ℕ) (σ w : ℝ) :
    (finiteInverseHeat m σ (Polynomial.X^n)).eval w =
      ∑ k ∈ Finset.range (m/2+1),
        ((-σ^2/2)^k / (Nat.factorial k : ℝ)) *
          (Nat.descFactorial n (2*k) : ℝ) * w^(n-2*k) := by
  simp only [finiteInverseHeat, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, polyDeriv_X_pow, Polynomial.eval_pow, Polynomial.eval_X]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- The public transform is exactly the general finite operator at the declared
kernel degree. Given [the displayed inputs and assumptions](hyp:L,σ), [the stated mathematical conclusion holds](goal). -/
lemma inverseHeat_eq_finiteInverseHeat (L : ℕ) (σ : ℝ) :
    inverseHeat L σ = finiteInverseHeat (kernelDegree L) σ (endpointKernel L) := by
  rfl

/-- Applying inverse heat coefficientwise gives the finite monomial decomposition
prescribed in the covariance proof roadmap. Given [the displayed inputs and assumptions](hyp:p,m,σ,hp), [the stated mathematical conclusion holds](goal). -/
lemma finiteInverseHeat_coeff_decomposition (p : Polynomial ℝ) (m : ℕ) (σ : ℝ)
    (hp : p.natDegree ≤ m) :
    finiteInverseHeat m σ p = ∑ n ∈ Finset.range (m+1),
      Polynomial.C (p.coeff n) * finiteInverseHeat m σ (Polynomial.X^n) := by
  have he := p.as_sum_range_C_mul_X_pow' (by omega : p.natDegree < m+1)
  calc
    _ = finiteInverseHeat m σ (∑ n ∈ Finset.range (m+1),
        Polynomial.C (p.coeff n) * Polynomial.X^n) := congrArg _ he
    _ = _ := by simp only [finiteInverseHeat_sum, finiteInverseHeat_C_mul]

/-- Evaluating the coefficientwise heat decomposition reduces the transform to
its explicit finite descending-factorial sums. Given [the displayed inputs and assumptions](hyp:p,m,σ,w,hp), [the stated mathematical conclusion holds](goal). -/
lemma finiteInverseHeat_eval_coeff_decomposition (p : Polynomial ℝ) (m : ℕ)
    (σ w : ℝ) (hp : p.natDegree ≤ m) :
    (finiteInverseHeat m σ p).eval w = ∑ n ∈ Finset.range (m+1), p.coeff n *
      (∑ k ∈ Finset.range (m/2+1), ((-σ^2/2)^k / (Nat.factorial k : ℝ)) *
        (Nat.descFactorial n (2*k) : ℝ) * w^(n-2*k)) := by
  rw [finiteInverseHeat_coeff_decomposition p m σ hp]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    finiteInverseHeat_X_pow_eval]

/-- The finite Hermite expression is likewise coefficientwise linear in the
input polynomial. This is the other half of the monomial reduction. Given [the displayed inputs and assumptions](hyp:p,m,σ,x,z,hp), [the stated mathematical conclusion holds](goal). -/
lemma finiteHermite_coeff_decomposition (p : Polynomial ℝ) (m : ℕ) (σ x z : ℝ)
    (hp : p.natDegree ≤ m) :
    (∑ j ∈ Finset.range (m+1),
      (σ^j * (polyDeriv j p).eval x / (Nat.factorial j : ℝ)) *
        (Polynomial.aeval z (Polynomial.hermite j) : ℝ)) =
    ∑ n ∈ Finset.range (m+1), p.coeff n *
      (∑ j ∈ Finset.range (m+1),
        (σ^j * (Nat.descFactorial n j : ℝ) * x^(n-j) / (Nat.factorial j : ℝ)) *
          (Polynomial.aeval z (Polynomial.hermite j) : ℝ)) := by
  have he := p.as_sum_range_C_mul_X_pow' (by omega : p.natDegree < m+1)
  conv_lhs => rw [he]
  simp only [polyDeriv_sum, Polynomial.eval_finsetSum, polyDeriv_C_mul,
    Polynomial.eval_mul, Polynomial.eval_C, polyDeriv_X_pow,
    Polynomial.eval_pow, Polynomial.eval_X]
  simp only [Finset.mul_sum, Finset.sum_div, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro j hj
  ring

end CausalSmith.Stat.RdTruesideNoiseFrontier
