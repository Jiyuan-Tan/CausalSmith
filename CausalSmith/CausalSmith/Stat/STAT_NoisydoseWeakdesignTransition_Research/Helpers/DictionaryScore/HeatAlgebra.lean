module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.Estimator
public import Causalean.Mathlib.Probability.HermiteGaussian
public import Mathlib.Algebra.Polynomial.Taylor

/-! Finite inverse-heat algebra and its Gaussian Hermite expansion (roadmap S12).
All coefficient comparisons are finite; the shared Hermite substrate supplies Gaussian means. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition

/-- Iterated polynomial derivative used in finite heat coefficient comparisons. -/
-- @node: polyDeriv
abbrev polyDeriv (j : ℕ) (p : Polynomial ℝ) : Polynomial ℝ :=
  (Polynomial.derivative^[j]) p

/-- The inverse heat operator with an arbitrary public degree cutoff. -/
-- @node: finiteInverseHeat
def finiteInverseHeat (m : ℕ) (σ : ℝ) (p : Polynomial ℝ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (m / 2 + 1),
    Polynomial.C ((-σ^2/2)^k / (Nat.factorial k : ℝ)) * polyDeriv (2*k) p

/-- Iterated polynomial differentiation distributes over finite sums. [This is the stated conclusion](goal). [This is the stated conclusion](goal). [This is the stated conclusion](goal). [This is the stated conclusion](goal). -/
-- @node: polyDeriv_sum
lemma polyDeriv_sum {ι : Type*} (j : ℕ) (s : Finset ι) (p : ι → Polynomial ℝ) :
    polyDeriv j (∑ i ∈ s, p i) = ∑ i ∈ s, polyDeriv j (p i) := by
  exact Polynomial.iterate_derivative_sum j s p

/-- Scalar polynomial coefficients commute with iterated differentiation. [This is the stated conclusion](goal). -/
-- @node: polyDeriv_C_mul
lemma polyDeriv_C_mul (j : ℕ) (a : ℝ) (p : Polynomial ℝ) :
    polyDeriv j (Polynomial.C a * p) = Polynomial.C a * polyDeriv j p := by
  exact Polynomial.iterate_derivative_C_mul a p j

/-- Every monomial derivative has its descending-factorial coefficient, including
zero derivatives above the monomial degree. [This is the stated conclusion](goal). -/
-- @node: polyDeriv_X_pow
lemma polyDeriv_X_pow (j n : ℕ) :
    polyDeriv j (Polynomial.X^n : Polynomial ℝ) =
      Polynomial.C (Nat.descFactorial n j : ℝ) * Polynomial.X^(n-j) := by
  exact Polynomial.iterate_derivative_X_pow_eq_C_mul n j

/-- Derivatives above any upper degree bound vanish. [Under the stated conditions](hyp:hp,hj). [This is the stated conclusion](goal). -/
-- @node: polyDeriv_eq_zero_of_degree_lt
lemma polyDeriv_eq_zero_of_degree_lt (p : Polynomial ℝ) (j m : ℕ)
    (hp : p.natDegree ≤ m) (hj : m < j) : polyDeriv j p = 0 := by
  exact Polynomial.iterate_derivative_eq_zero (hp.trans_lt hj)

/-- The finite heat operator distributes over finite polynomial sums. [This is the stated conclusion](goal). -/
-- @node: finiteInverseHeat_sum
lemma finiteInverseHeat_sum {ι : Type*} (m : ℕ) (σ : ℝ) (s : Finset ι)
    (p : ι → Polynomial ℝ) :
    finiteInverseHeat m σ (∑ i ∈ s, p i) = ∑ i ∈ s, finiteInverseHeat m σ (p i) := by
  simp only [finiteInverseHeat, polyDeriv_sum, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- The finite heat operator commutes with scalar polynomial coefficients. [This is the stated conclusion](goal). -/
-- @node: finiteInverseHeat_C_mul
lemma finiteInverseHeat_C_mul (m : ℕ) (σ a : ℝ) (p : Polynomial ℝ) :
    finiteInverseHeat m σ (Polynomial.C a * p) =
      Polynomial.C a * finiteInverseHeat m σ p := by
  simp only [finiteInverseHeat, polyDeriv_C_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- Enlarging a degree cutoff adds only identically zero heat terms. [Under the stated conditions](hyp:hp,hmM). [This is the stated conclusion](goal). -/
-- @node: finiteInverseHeat_cutoff
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

/-- Applying inverse heat coefficientwise gives the finite monomial decomposition
prescribed in the covariance proof roadmap. [Under the stated conditions](hyp:hp). [This is the stated conclusion](goal). -/
-- @node: finiteInverseHeat_coeff_decomposition
lemma finiteInverseHeat_coeff_decomposition (p : Polynomial ℝ) (m : ℕ) (σ : ℝ)
    (hp : p.natDegree ≤ m) :
    finiteInverseHeat m σ p = ∑ n ∈ Finset.range (m+1),
      Polynomial.C (p.coeff n) * finiteInverseHeat m σ (Polynomial.X^n) := by
  have he := p.as_sum_range_C_mul_X_pow' (by omega : p.natDegree < m+1)
  calc
    _ = finiteInverseHeat m σ (∑ n ∈ Finset.range (m+1),
        Polynomial.C (p.coeff n) * Polynomial.X^n) := congrArg _ he
    _ = _ := by simp only [finiteInverseHeat_sum, finiteInverseHeat_C_mul]

/-- The even factorial splits into its even and odd double-factorial products. [This is the stated conclusion](goal). -/
-- @node: heat_even_factorial
lemma heat_even_factorial (k : ℕ) :
    Nat.factorial (2*k) = 2^k * Nat.factorial k * Nat.doubleFactorial (2*k-1) := by
  cases k with
  | zero => norm_num [Nat.doubleFactorial]
  | succ k =>
    have h := Nat.factorial_eq_mul_doubleFactorial (2*(k+1)-1)
    rw [show 2*(k+1)-1+1 = 2*(k+1) by omega] at h
    rw [h, Nat.doubleFactorial_two_mul]
/-- Each nonzero Hermite coefficient equals the corresponding inverse-heat coefficient. [This is the stated conclusion](goal). -/
-- @node: hermite_heat_coefficient
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
/-- Unit-noise inverse heat maps a monomial to the corresponding Hermite polynomial. [This is the stated conclusion](goal). -/
-- @node: finiteInverseHeat_unit_monomial
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
/-- Affine substitution multiplies the iterated derivative by the appropriate power of its slope. [This is the stated conclusion](goal). -/
-- @node: polyDeriv_affine
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
/-- The coefficients after affine substitution are the scaled finite Taylor coefficients. [This is the stated conclusion](goal). -/
-- @node: affine_coeff_derivative
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
/-- Translation and scaling reduce inverse heat evaluation to the unit-noise operator. [This is the stated conclusion](goal). -/
-- @node: finiteInverseHeat_affine_eval
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
/-- A polynomial of bounded degree has the exact finite inverse-heat Hermite expansion. [Under the stated conditions](hyp:hp). [This is the stated conclusion](goal). -/
-- @node: finiteInverseHeat_hermite_expansion
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


/-- The constant Hermite mode extracts each Gaussian mean. [This is the stated conclusion](goal). -/
-- @node: hermite_gaussian_mean
lemma hermite_gaussian_mean (j : ℕ) :
    (∫ z, (Polynomial.aeval z (Polynomial.hermite j) : ℝ) ∂gaussianReal 0 1) =
      if j = 0 then 1 else 0 := by
  have h := Causalean.Mathlib.Probability.integral_hermite_mul j 0
  by_cases hj : j = 0
  · subst j
    simpa [Polynomial.hermite_zero] using h
  · simpa [Polynomial.hermite_zero, hj] using h

/-- Finite Hermite sums have Gaussian mean equal to their constant coefficient. [Under the stated conditions](hyp:hN). [This is the stated conclusion](goal). -/
-- @node: hermite_finite_sum_mean
lemma hermite_finite_sum_mean (c : ℕ → ℝ) (N : ℕ) (hN : 0 < N) :
    (∫ z, ∑ j ∈ Finset.range N,
      c j * (Polynomial.aeval z (Polynomial.hermite j) : ℝ) ∂gaussianReal 0 1) = c 0 := by
  rw [integral_finset_sum]
  · simp_rw [integral_const_mul, hermite_gaussian_mean]
    simp [mul_ite, hN]
  · intro j hj
    have hi := Causalean.Mathlib.Probability.integrable_hermite_mul j 0
    simp only [Polynomial.hermite_zero, map_one, mul_one] at hi
    exact hi.const_mul _

/-- Finite coefficient comparison and Hermite means prove exact polynomial Gaussian inversion. [Under the stated conditions](hyp:hp). [This is the stated conclusion](goal). -/
-- @node: finiteInverseHeat_gaussian_mean
lemma finiteInverseHeat_gaussian_mean (p : Polynomial ℝ) (D : ℕ)
    (hp : p.natDegree ≤ D) (t sigma : ℝ) :
    (∫ z, (finiteInverseHeat D sigma p).eval (t+sigma*z) ∂gaussianReal 0 1) = p.eval t := by
  simp_rw [finiteInverseHeat_hermite_expansion p D hp t sigma]
  simpa [polyDeriv] using hermite_finite_sum_mean
    (fun j => sigma^j * (polyDeriv j p).eval t / (Nat.factorial j : ℝ)) (D+1) (by omega)

/-- The even Chebyshev expansion has degree at most six times the original index. [This is the stated conclusion](goal). -/
-- @node: qMPoly_natDegree_le
lemma qMPoly_natDegree_le (m : ℕ) : (qMPoly m).natDegree ≤ 6*(m-1) := by
  have hbase : (1 - Polynomial.C (4 : ℝ) * Polynomial.X^2).natDegree ≤ 2 := by
    apply (Polynomial.natDegree_sub_le _ _).trans
    exact max_le (by simp) ((Polynomial.natDegree_C_mul_le _ _).trans (by simp))
  have hsum : (∑ k ∈ Finset.range m,
      Polynomial.C ((Polynomial.Chebyshev.U ℝ (m-1 : ℕ)).coeff (2*k) / (m : ℝ)) *
        (1 - Polynomial.C 4 * Polynomial.X^2)^k).natDegree ≤ m-1 := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro k hk
    by_cases hdeg : 2*k ≤ m-1
    · apply (Polynomial.natDegree_C_mul_le _ _).trans
      rw [Polynomial.natDegree_pow]
      exact (Nat.mul_le_mul_left k hbase).trans (by omega)
    · have hz : (Polynomial.Chebyshev.U ℝ (m-1 : ℕ)).coeff (2*k) = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        rw [Polynomial.Chebyshev.natDegree_U_natCast]
        omega
      simp [hz]
  unfold qMPoly
  rw [Polynomial.natDegree_pow]
  exact Nat.mul_le_mul_left 6 hsum

/-- The declared inverse weight evaluates the finite heat transform at its valid degree cutoff. [This is the stated conclusion](goal). -/
-- @node: ellM_eq_finiteInverseHeat
lemma ellM_eq_finiteInverseHeat (sigma : ℝ) (m : ℕ) (v : ℝ) :
    ellM sigma m v = (finiteInverseHeat (6*(m-1)) sigma (qMPoly m)).eval v := by
  simp only [ellM, finiteInverseHeat, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, polyDeriv]
  congr 1
  congr 1
  omega

/-- Gaussian expectation of every polynomial dictionary inverse equals its latent weight. [This is the stated conclusion](goal). -/
-- @node: ellM_gaussian_inverse
lemma ellM_gaussian_inverse (sigma : ℝ) (m : ℕ) (t : ℝ) :
    (∫ z, ellM sigma m (t+sigma*z) ∂gaussianReal 0 1) = qM m t := by
  simp_rw [ellM_eq_finiteInverseHeat]
  exact finiteInverseHeat_gaussian_mean (qMPoly m) (6*(m-1))
    (qMPoly_natDegree_le m) t sigma

/-- Orthogonality removes all mixed modes from a finite Hermite square. [This is the stated conclusion](goal). -/
-- @node: hermite_finite_sum_square
lemma hermite_finite_sum_square (c : ℕ → ℝ) (N : ℕ) :
    (∫ z, (∑ j ∈ Finset.range N,
      c j * (Polynomial.aeval z (Polynomial.hermite j) : ℝ))^2 ∂gaussianReal 0 1) =
      ∑ j ∈ Finset.range N, (c j)^2 * (Nat.factorial j : ℝ) := by
  have hi (j k : ℕ) : Integrable (fun z =>
      (c j * c k) * ((Polynomial.aeval z (Polynomial.hermite j) : ℝ) *
        Polynomial.aeval z (Polynomial.hermite k))) (gaussianReal 0 1) :=
    (Causalean.Mathlib.Probability.integrable_hermite_mul j k).const_mul _
  have heq (z : ℝ) :
      (∑ j ∈ Finset.range N, c j * (Polynomial.aeval z (Polynomial.hermite j) : ℝ))^2 =
        ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
          (c j * c k) * ((Polynomial.aeval z (Polynomial.hermite j) : ℝ) *
            Polynomial.aeval z (Polynomial.hermite k)) := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  simp_rw [heq]
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hi j k))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_finsetSum _ (fun k _ => hi j k)]
  simp_rw [integral_const_mul, Causalean.Mathlib.Probability.integral_hermite_mul]
  simp [mul_ite, ← pow_two, hj]

/-- The finite inverse-heat expansion has the exact derivative-square second moment. [Under the stated conditions](hyp:hp). [This is the stated conclusion](goal). -/
-- @node: finiteInverseHeat_gaussian_second_moment
lemma finiteInverseHeat_gaussian_second_moment (p : Polynomial ℝ) (D : ℕ)
    (hp : p.natDegree ≤ D) (t sigma : ℝ) :
    (∫ z, ((finiteInverseHeat D sigma p).eval (t+sigma*z))^2 ∂gaussianReal 0 1) =
      ∑ j ∈ Finset.range (D+1),
        sigma^(2*j) * ((polyDeriv j p).eval t)^2 / (Nat.factorial j : ℝ) := by
  simp_rw [finiteInverseHeat_hermite_expansion p D hp t sigma]
  rw [hermite_finite_sum_square]
  apply Finset.sum_congr rfl
  intro j hj
  have hf : (Nat.factorial j : ℝ) ≠ 0 := by positivity
  rw [pow_mul]
  field_simp
  ring

/-- Every polynomial dictionary inverse satisfies the exact identity in S12, at zero noise too. [This is the stated conclusion](goal). -/
-- @node: ellM_gaussian_second_moment
lemma ellM_gaussian_second_moment (sigma : ℝ) (m : ℕ) (t : ℝ) :
    (∫ z, (ellM sigma m (t+sigma*z))^2 ∂gaussianReal 0 1) =
      ∑ j ∈ Finset.range (6*(m-1)+1),
        sigma^(2*j) * ((polyDeriv j (qMPoly m)).eval t)^2 / (Nat.factorial j : ℝ) := by
  simp_rw [ellM_eq_finiteInverseHeat]
  exact finiteInverseHeat_gaussian_second_moment (qMPoly m) (6*(m-1))
    (qMPoly_natDegree_le m) t sigma

/-- One falling-factorial square is bounded by a binomial coefficient times a degree power. [This is the stated conclusion](goal). -/
-- @node: descFactorial_square_div_factorial_le
lemma descFactorial_square_div_factorial_le (D j : ℕ) :
    (D.descFactorial j : ℝ)^2 / (j.factorial : ℝ) ≤
      (D.choose j : ℝ) * (D : ℝ)^j := by
  have hf : (j.factorial : ℝ) ≠ 0 := by positivity
  have hid : (D.descFactorial j : ℝ) = (j.factorial : ℝ) * (D.choose j : ℝ) := by
    exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose D j
  have hpow : (D.descFactorial j : ℝ) ≤ (D : ℝ)^j := by
    exact_mod_cast Nat.descFactorial_le_pow D j
  calc
    _ = (D.choose j : ℝ) * (D.descFactorial j : ℝ) := by rw [hid]; field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)

/-- Derivative bounds give the binomial second-moment envelope in roadmap S13. [Under the stated conditions](hyp:hp,hC,hderiv). [This is the stated conclusion](goal). -/
-- @node: finiteInverseHeat_gaussian_second_moment_le
lemma finiteInverseHeat_gaussian_second_moment_le (p : Polynomial ℝ) (D : ℕ)
    (hp : p.natDegree ≤ D) (t sigma C : ℝ) (hC : 0 ≤ C)
    (hderiv : ∀ j ≤ D, |(polyDeriv j p).eval t| ≤ C * (D.descFactorial j : ℝ)) :
    (∫ z, ((finiteInverseHeat D sigma p).eval (t+sigma*z))^2 ∂gaussianReal 0 1) ≤
      C^2 * (1 + (D : ℝ)*sigma^2)^D := by
  rw [finiteInverseHeat_gaussian_second_moment, add_comm 1, add_pow, Finset.mul_sum]
  · apply Finset.sum_le_sum
    intro j hj
    have hs : 0 ≤ sigma^(2*j) := by
      rw [pow_mul]
      exact pow_nonneg (sq_nonneg sigma) j
    have hjD : j ≤ D := by have := Finset.mem_range.mp hj; omega
    have hd : ((polyDeriv j p).eval t)^2 ≤ C^2 * (D.descFactorial j : ℝ)^2 := by
      have h := pow_le_pow_left₀ (abs_nonneg _) (hderiv j hjD) 2
      simpa only [sq_abs, mul_pow] using h
    calc
      _ ≤ sigma^(2*j) * (C^2 * (D.descFactorial j : ℝ)^2) / (j.factorial : ℝ) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hd hs) (by positivity)
      _ = (C^2 * sigma^(2*j)) * ((D.descFactorial j : ℝ)^2 / (j.factorial : ℝ)) := by ring
      _ ≤ (C^2 * sigma^(2*j)) * ((D.choose j : ℝ) * (D : ℝ)^j) :=
        mul_le_mul_of_nonneg_left (descFactorial_square_div_factorial_le D j) (mul_nonneg (sq_nonneg C) hs)
      _ = _ := by simp only [one_pow, mul_one, mul_pow, pow_mul]; ring
  · exact hp

end CausalSmith.Stat.NoisydoseWeakdesignTransition
