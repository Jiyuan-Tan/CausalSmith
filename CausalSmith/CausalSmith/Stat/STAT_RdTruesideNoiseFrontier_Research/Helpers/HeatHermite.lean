module
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.HeatAlgebra
public import Mathlib.Algebra.Polynomial.Taylor
/-!
# Finite Hermite expansion of inverse heat

Coefficient comparison identifies inverse heat on monomials with Hermite
polynomials. Affine substitution and the finite Taylor formula extend this
identity to arbitrary polynomials, without any infinite-series interchange.
-/
public section
noncomputable section
open scoped BigOperators
namespace CausalSmith.Stat.RdTruesideNoiseFrontier
/-- The even factorial splits into its even and odd double-factorial products. Given [the displayed inputs and assumptions](hyp:k), [the stated mathematical conclusion holds](goal). -/
lemma heat_even_factorial (k : ℕ) :
    Nat.factorial (2*k) = 2^k * Nat.factorial k * Nat.doubleFactorial (2*k-1) := by
  cases k with
  | zero => norm_num [Nat.doubleFactorial]
  | succ k =>
    have h := Nat.factorial_eq_mul_doubleFactorial (2*(k+1)-1)
    rw [show 2*(k+1)-1+1 = 2*(k+1) by omega] at h
    rw [h, Nat.doubleFactorial_two_mul]
/-- Each nonzero Hermite coefficient equals the corresponding inverse-heat coefficient. Given [the displayed inputs and assumptions](hyp:k,j), [the stated mathematical conclusion holds](goal). -/
lemma hermite_heat_coefficient (k j : ℕ) :
    ((Polynomial.hermite (2*k+j)).coeff j : ℝ) =
      (-1/2 : ℝ)^k / (Nat.factorial k : ℝ) *
        (Nat.descFactorial (2*k+j) (2*k) : ℝ) := by
  rw [Polynomial.coeff_hermite_explicit]
  push_cast
  have hdesc := Nat.factorial_mul_descFactorial (show 2*k ≤ 2*k+j by omega)
  have hchoose := Nat.choose_mul_factorial_mul_factorial (show j ≤ 2*k+j by omega)
  rw [show 2*k+j-2*k = j by omega] at hdesc
  rw [show 2*k+j-j = 2*k by omega, heat_even_factorial] at hchoose
  have hd : (Nat.factorial j : ℝ) * (Nat.descFactorial (2*k+j) (2*k) : ℝ) =
      (Nat.factorial (2*k+j) : ℝ) := by exact_mod_cast hdesc
  have hc : (Nat.choose (2*k+j) j : ℝ) * (Nat.factorial j : ℝ) *
      (2^k * (Nat.factorial k : ℝ) * (Nat.doubleFactorial (2*k-1) : ℝ)) =
      (Nat.factorial (2*k+j) : ℝ) := by exact_mod_cast hchoose
  have hj : (Nat.factorial j : ℝ) ≠ 0 := by positivity
  have hk : (Nat.factorial k : ℝ) ≠ 0 := by positivity
  have he : (Nat.descFactorial (2*k+j) (2*k) : ℝ) =
      (Nat.choose (2*k+j) j : ℝ) *
        (2^k * (Nat.factorial k : ℝ) * (Nat.doubleFactorial (2*k-1) : ℝ)) := by
    apply mul_left_cancel₀ hj
    nlinarith [hd, hc]
  rw [he, div_pow]
  field_simp
/-- Unit-noise inverse heat maps a monomial to the corresponding Hermite polynomial. Given [the displayed inputs and assumptions](hyp:n), [the stated mathematical conclusion holds](goal). -/
lemma finiteInverseHeat_unit_monomial (n : ℕ) :
    finiteInverseHeat n 1 (Polynomial.X^n) =
      (Polynomial.hermite n).map (Int.castRingHom ℝ) := by
  ext j
  simp only [finiteInverseHeat, polyDeriv_X_pow, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_map,
    Int.castRingHom]
  by_cases hj : j ≤ n
  · by_cases heven : Even (n-j)
    · obtain ⟨k, hk⟩ := heven
      have hn : n = 2*k+j := by omega
      subst n
      rw [Finset.sum_eq_single k]
      · simp only [show 2*k+j-2*k = j by omega, if_true]
        norm_num only [one_pow, neg_div, neg_one_sq, one_mul]
        simpa [div_eq_mul_inv] using (hermite_heat_coefficient k j).symm
      · intro l hl hne
        by_cases hlbig : 2*k+j < 2*l
        · rw [Nat.descFactorial_of_lt hlbig]
          simp
        · have hne' : 2*k+j-2*l ≠ j := by omega
          simp [hne', Ne.symm hne']
      · intro hnot
        have : k < (2*k+j)/2+1 := by omega
        exact (hnot (Finset.mem_range.mpr this)).elim
    · rw [Polynomial.coeff_hermite_of_odd_add (by
        apply Nat.not_even_iff_odd.mp
        intro h
        obtain ⟨r, hr⟩ := h
        apply heven
        exact ⟨r-j, by omega⟩)]
      simp only [map_zero]
      apply Finset.sum_eq_zero
      intro l hl
      by_cases hlbig : n < 2*l
      · rw [Nat.descFactorial_of_lt hlbig]
        simp
      · have hne : n-2*l ≠ j := by
          intro h
          apply heven
          exact ⟨l, by omega⟩
        simp [hne, Ne.symm hne]
  · rw [Polynomial.coeff_hermite_of_lt (by omega)]
    simp only [map_zero]
    apply Finset.sum_eq_zero
    intro l hl
    simp [show j ≠ n-2*l by omega]
/-- Affine substitution multiplies the iterated derivative by the appropriate power of its slope. Given [the displayed inputs and assumptions](hyp:p,x,σ,j), [the stated mathematical conclusion holds](goal). -/
lemma polyDeriv_affine (p : Polynomial ℝ) (x σ : ℝ) (j : ℕ) :
    polyDeriv j (p.comp (Polynomial.C x + Polynomial.C σ * Polynomial.X)) =
      Polynomial.C (σ^j) *
        (polyDeriv j p).comp (Polynomial.C x + Polynomial.C σ * Polynomial.X) := by
  induction j generalizing p with
  | zero => simp [polyDeriv]
  | succ j ih =>
    simp only [polyDeriv, Function.iterate_succ_apply'] at ih ⊢
    rw [ih, Polynomial.derivative_C_mul, Polynomial.derivative_comp]
    simp only [Polynomial.derivative_add, Polynomial.derivative_C,
      Polynomial.derivative_C_mul, Polynomial.derivative_X, mul_one, zero_add]
    rw [pow_succ, Polynomial.C_mul]
    ring
/-- The coefficients after affine substitution are the scaled finite Taylor coefficients. Given [the displayed inputs and assumptions](hyp:p,x,σ,j), [the stated mathematical conclusion holds](goal). -/
lemma affine_coeff_derivative (p : Polynomial ℝ) (x σ : ℝ) (j : ℕ) :
    (p.comp (Polynomial.C x + Polynomial.C σ * Polynomial.X)).coeff j =
      σ^j * (polyDeriv j p).eval x / (Nat.factorial j : ℝ) := by
  have ht := Polynomial.taylor_coeff (r := x) (f := p) j
  have hd := congrArg (fun f : Polynomial ℝ → Polynomial ℝ => (f p).eval x)
    (Polynomial.factorial_smul_hasseDeriv (R := ℝ) (k := j))
  simp only [LinearMap.smul_apply, map_nsmul, nsmul_eq_mul] at hd
  have hf : (Nat.factorial j : ℝ) ≠ 0 := by positivity
  have he : (Polynomial.hasseDeriv j p).eval x =
      (polyDeriv j p).eval x / (Nat.factorial j : ℝ) := by
    apply (eq_div_iff hf).mpr
    simpa [polyDeriv, mul_comm] using hd
  have ha : p.comp (Polynomial.C x + Polynomial.C σ * Polynomial.X) =
      (Polynomial.taylor x p).comp (Polynomial.C σ * Polynomial.X) := by
    simp only [Polynomial.taylor_apply, Polynomial.comp_assoc, Polynomial.add_comp,
      Polynomial.X_comp, Polynomial.C_comp]
    congr 1
    ring
  rw [ha, Polynomial.comp_C_mul_X_coeff, ht, he]
  ring
/-- Translation and scaling reduce inverse heat evaluation to the unit-noise operator. Given [the displayed inputs and assumptions](hyp:p,m,x,σ,z), [the stated mathematical conclusion holds](goal). -/
lemma finiteInverseHeat_affine_eval (p : Polynomial ℝ) (m : ℕ) (x σ z : ℝ) :
    (finiteInverseHeat m σ p).eval (x+σ*z) =
      (finiteInverseHeat m 1
        (p.comp (Polynomial.C x + Polynomial.C σ * Polynomial.X))).eval z := by
  simp only [finiteInverseHeat, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, polyDeriv_affine, Polynomial.eval_comp,
    Polynomial.eval_add, Polynomial.eval_X]
  apply Finset.sum_congr rfl
  intro k hk
  rw [show -σ^2/2 = (-1/2 : ℝ)*σ^2 by ring, mul_pow, pow_mul]
  norm_num only [one_pow]
  ring
/-- A polynomial of bounded degree has the exact finite inverse-heat Hermite expansion. Given [the displayed inputs and assumptions](hyp:p,m,hp,x,σ,z), [the stated mathematical conclusion holds](goal). -/
lemma finiteInverseHeat_hermite_expansion (p : Polynomial ℝ) (m : ℕ)
    (hp : p.natDegree ≤ m) (x σ z : ℝ) :
    (finiteInverseHeat m σ p).eval (x+σ*z) =
      ∑ j ∈ Finset.range (m+1),
        (σ^j * (polyDeriv j p).eval x / (Nat.factorial j : ℝ)) *
          (Polynomial.aeval z (Polynomial.hermite j) : ℝ) := by
  let q := p.comp (Polynomial.C x + Polynomial.C σ * Polynomial.X)
  have hq : q.natDegree ≤ m := by
    apply (Polynomial.natDegree_comp_le).trans
    have ha : (Polynomial.C x + Polynomial.C σ * Polynomial.X).natDegree ≤ 1 := by
      apply (Polynomial.natDegree_add_le _ _).trans
      simp only [Polynomial.natDegree_C]
      exact max_le (by omega) ((Polynomial.natDegree_C_mul_le _ _).trans (by simp))
    exact (Nat.mul_le_mul_left _ ha).trans (by simpa using hp)
  rw [finiteInverseHeat_affine_eval, finiteInverseHeat_coeff_decomposition q m 1 hq]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]
  apply Finset.sum_congr rfl
  intro j hj
  rw [finiteInverseHeat_cutoff (Polynomial.X^j) 1 j m (by simp)
    (by have := Finset.mem_range.mp hj; omega), finiteInverseHeat_unit_monomial]
  rw [show q.coeff j = σ^j * (polyDeriv j p).eval x / (Nat.factorial j : ℝ) from
    affine_coeff_derivative p x σ j]
  have hcast : Int.castRingHom ℝ = algebraMap ℤ ℝ := by
    ext n
    simp
  rw [hcast, Polynomial.eval_map_algebraMap]
end CausalSmith.Stat.RdTruesideNoiseFrontier
