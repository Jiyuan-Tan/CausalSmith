module
public import CausalSmith.Stat.STAT_PomdpBinaryhiddenRate_Research.Basic
public import CausalSmith.Stat.STAT_PomdpBinaryhiddenRate_Research.Helpers.ComplexOscillation
public import CausalSmith.Stat.STAT_PomdpBinaryhiddenRate_Research.Helpers.PairPolynomialBounds
public import Mathlib.LinearAlgebra.Eigenspace.Zero

/-!
# Seven-moment pair-polynomial stability

The four-state transient characteristic factors yield an exact stationary-value
identity and a uniform seven-moment modulus under Dobrushin contraction,
including complex and defective transient modes.
-/

@[expose] public section

namespace CausalSmith.Stat.PomdpBinaryhiddenRate

open scoped BigOperators
open Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation

/-- The moment of a row vector, transition matrix, and reward vector. -/
noncomputable def matrixMoment (nu : JointState 2 2 → ℝ) (P : FourMatrix)
    (r : JointState 2 2 → ℝ) (k : Nat) : ℝ :=
  ∑ s, (Matrix.vecMul nu (P ^ k)) s * r s

/-- The stationary value of a finite reward vector. -/
noncomputable def matrixValue (pi r : JointState 2 2 → ℝ) : ℝ :=
  ∑ s, pi s * r s

/-- Stationarity is preserved by every matrix power. [Under the listed formal conditions](hyp:hpi), [the stated conclusion holds](goal).-/
-- @node: stationary_vecMul_pow
lemma stationary_vecMul_pow (P : FourMatrix) (pi : JointState 2 2 → ℝ)
    (hpi : IsStationary P pi) (k : ℕ) : Matrix.vecMul pi (P ^ k) = pi := by
  have hfix : Matrix.vecMul pi P = pi := hpi.2
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, hfix]

/-- Left evaluation of a polynomial against a stationary law evaluates at one. [Under the listed formal conditions](hyp:hpi), [the stated conclusion holds](goal).-/
-- @node: stationary_vecMul_aeval
lemma stationary_vecMul_aeval (P : FourMatrix) (pi : JointState 2 2 → ℝ)
    (hpi : IsStationary P pi) (f : Polynomial ℝ) :
    Matrix.vecMul pi (Polynomial.aeval P f) = f.eval 1 • pi := by
  classical
  rw [Polynomial.aeval_eq_sum_range, Matrix.vecMul_sum]
  simp_rw [Matrix.vecMul_smul, stationary_vecMul_pow P pi hpi]
  rw [← Finset.sum_smul]
  congr 1
  simp [Polynomial.eval_eq_sum_range]

/-- The constant right vector witnesses the stationary characteristic root. [Under the listed formal conditions](hyp:hP), [the stated conclusion holds](goal).-/
-- @node: stochastic_charpoly_isRoot_one
lemma stochastic_charpoly_isRoot_one (P : FourMatrix) (hP : IsStochasticMatrix P) :
    Polynomial.IsRoot (Matrix.charpoly P) 1 := by
  have hconst : Matrix.mulVec P (fun _ => (1 : ℝ)) = fun _ => 1 := by
    ext i
    simpa [Matrix.mulVec, dotProduct] using hP.2 i
  have hzero : Matrix.mulVec (Matrix.scalar _ (1 : ℝ) - P) (fun _ => (1 : ℝ)) = 0 := by
    simp [Matrix.sub_mulVec, hconst, Matrix.scalar]
  rw [Polynomial.IsRoot, Matrix.eval_charpoly]
  exact Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors hzero
    (i := ((0 : Fin 2), (0 : Fin 2))) (by simp)

/-- Exact characteristic factorization, independent of diagonalizability. [Under the listed formal conditions](hyp:hP), [the stated conclusion holds](goal).-/
-- @node: stochastic_charpoly_factor
lemma stochastic_charpoly_factor (P : FourMatrix) (hP : IsStochasticMatrix P) :
    (Polynomial.X - Polynomial.C 1) * transientPoly P = Matrix.charpoly P := by
  exact Polynomial.mul_divByMonic_eq_iff_isRoot.mpr
    (stochastic_charpoly_isRoot_one P hP)

/-- Cayley–Hamilton puts the transient polynomial's image in the fixed space. [Under the listed formal conditions](hyp:hP), [the stated conclusion holds](goal).-/
-- @node: transientPoly_aeval_annihilated
lemma transientPoly_aeval_annihilated (P : FourMatrix) (hP : IsStochasticMatrix P) :
    (P - 1) * Polynomial.aeval P (transientPoly P) = 0 := by
  have h := congrArg (Polynomial.aeval P) (stochastic_charpoly_factor P hP)
  simpa using h.trans (Matrix.aeval_self_charpoly P)

/-- Polynomial matrix evaluation is the corresponding finite moment sum. [Under the listed formal conditions](hyp:hf), [the stated conclusion holds](goal).-/
-- @node: matrixMoment_polynomial_sum
lemma matrixMoment_polynomial_sum (nu r : JointState 2 2 → ℝ) (P : FourMatrix)
    (f : Polynomial ℝ) (hf : f.natDegree < 7) :
    (∑ s, (Matrix.vecMul nu (Polynomial.aeval P f)) s * r s) =
      ∑ k : Fin 7, f.coeff k.val * matrixMoment nu P r k.val := by
  classical
  rw [Polynomial.aeval_eq_sum_range' hf, Matrix.vecMul_sum]
  simp_rw [Finset.sum_apply, Matrix.vecMul_smul, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  exact (Fin.sum_univ_eq_sum_range _ 7).symm

/-- Centering at the midpoint gives TV duality for any bounded real vector. [Under the listed formal conditions](hyp:hp,hq,hf), [the stated conclusion holds](goal).-/
-- @node: probability_mean_tv_interval
lemma probability_mean_tv_interval {S : Type*} [Fintype S]
    {p q f : S → ℝ} (hp : IsProbabilityVector p) (hq : IsProbabilityVector q)
    {lo hi : ℝ} (hf : ∀ i, f i ∈ Set.Icc lo hi) :
    |(∑ i, p i * f i) - ∑ i, q i * f i| ≤
      ((1 / 2 : ℝ) * ∑ i, |p i - q i|) * (hi - lo) := by
  have hz : ∑ i, (p i - q i) = 0 := by
    rw [Finset.sum_sub_distrib, hp.2, hq.2]; ring
  have he : (∑ i, p i * f i) - ∑ i, q i * f i =
      ∑ i, (p i - q i) * (f i - (lo + hi) / 2) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hz, zero_mul, sub_zero,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  calc
    _ ≤ ∑ i, |(p i - q i) * (f i - (lo + hi) / 2)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |p i - q i| * ((hi - lo) / 2) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (abs_le.mpr ⟨by linarith [(hf i).1], by linarith [(hf i).2]⟩) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- Dobrushin contraction below one leaves only constant right fixed vectors. [Under the listed formal conditions](hyp:hP,hα,hδ,hfix), [the stated conclusion holds](goal).-/
-- @node: dobrushin_fixedVector_constant
lemma dobrushin_fixedVector_constant (P : FourMatrix) (hP : IsStochasticMatrix P)
    {alpha : ℝ} (hα : alpha < 1) (hδ : dobrushin P ≤ alpha)
    (f : JointState 2 2 → ℝ) (hfix : Matrix.mulVec P f = f) :
    ∃ c : ℝ, f = fun _ => c := by
  classical
  obtain ⟨imin, hmin⟩ := Finite.exists_min f
  obtain ⟨imax, hmax⟩ := Finite.exists_max f
  have hrows (i : JointState 2 2) : IsProbabilityVector (P i) :=
    ⟨hP.1 i, hP.2 i⟩
  have htv : (1 / 2 : ℝ) * ∑ s, |P imax s - P imin s| ≤ alpha := by
    have hj : (1 / 2 : ℝ) * ∑ s, |P imax s - P imin s| ≤
        ⨆ j : JointState 2 2, (1 / 2 : ℝ) * ∑ s, |P imax s - P j s| :=
      le_ciSup (f := fun j : JointState 2 2 => (1 / 2 : ℝ) * ∑ s, |P imax s - P j s|)
        (Finite.bddAbove_range _) imin
    have hi : (⨆ j : JointState 2 2, (1 / 2 : ℝ) * ∑ s, |P imax s - P j s|) ≤
        dobrushin P := le_ciSup
          (f := fun i : JointState 2 2 => ⨆ j : JointState 2 2,
            (1 / 2 : ℝ) * ∑ s, |P i s - P j s|)
          (Finite.bddAbove_range _) imax
    exact hj.trans (hi.trans hδ)
  have hmean := probability_mean_tv_interval (hrows imax) (hrows imin)
    (f := f) (fun i => ⟨hmin i, hmax i⟩)
  have hmaxfix : (∑ i, P imax i * f i) = f imax := congrFun hfix imax
  have hminfix : (∑ i, P imin i * f i) = f imin := congrFun hfix imin
  rw [hmaxfix, hminfix, abs_of_nonneg (sub_nonneg.mpr (hmin imax))] at hmean
  have hbound := hmean.trans (mul_le_mul_of_nonneg_right htv
    (sub_nonneg.mpr (hmin imax)))
  have heq : f imax = f imin := by nlinarith [hmin imax]
  refine ⟨f imin, funext fun i => ?_⟩
  exact le_antisymm (heq ▸ hmax i) (hmin i)

/-- Stationarity rules out a nonzero constant in the image of the shifted operator. [Under the listed formal conditions](hyp:hpi,hw), [the stated conclusion holds](goal).-/
-- @node: stationary_shift_constant_eq_zero
lemma stationary_shift_constant_eq_zero (P : FourMatrix) (pi w : JointState 2 2 → ℝ)
    (hpi : IsStationary P pi) (c : ℝ)
    (hw : Matrix.mulVec (P - 1) w = fun _ => c) : c = 0 := by
  have hfix : Matrix.vecMul pi P = pi := hpi.2
  have hmean : dotProduct pi (Matrix.mulVec (P - 1) w) = 0 := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_sub, hfix, Matrix.vecMul_one,
      sub_self, zero_dotProduct]
  rw [hw] at hmean
  simpa [dotProduct, ← Finset.sum_mul, hpi.1.2] using hmean

/-- No nontrivial Jordan chain can end in the eigenspace at one. [Under the listed formal conditions](hyp:hP,hpi,hα,hδ,hw), [the stated conclusion holds](goal).-/
-- @node: dobrushin_shift_sq_kernel
lemma dobrushin_shift_sq_kernel (P : FourMatrix) (pi w : JointState 2 2 → ℝ)
    (hP : IsStochasticMatrix P) (hpi : IsStationary P pi)
    {alpha : ℝ} (hα : alpha < 1) (hδ : dobrushin P ≤ alpha)
    (hw : Matrix.mulVec (P - 1) (Matrix.mulVec (P - 1) w) = 0) :
    Matrix.mulVec (P - 1) w = 0 := by
  let u := Matrix.mulVec (P - 1) w
  have hfix : Matrix.mulVec P u = u := by
    have h : Matrix.mulVec (P - 1) u = 0 := hw
    simpa [Matrix.sub_mulVec, sub_eq_zero] using h
  obtain ⟨c, hc⟩ := dobrushin_fixedVector_constant P hP hα hδ u hfix
  have hz := stationary_shift_constant_eq_zero P pi w hpi c hc
  simpa [u, hz, Pi.zero_def] using hc

/-- Every positive power of the shifted operator has the same kernel. [Under the listed formal conditions](hyp:hP,hpi,hα,hδ,hw), [the stated conclusion holds](goal).-/
-- @node: dobrushin_shift_pow_kernel
lemma dobrushin_shift_pow_kernel (P : FourMatrix) (pi w : JointState 2 2 → ℝ)
    (hP : IsStochasticMatrix P) (hpi : IsStationary P pi)
    {alpha : ℝ} (hα : alpha < 1) (hδ : dobrushin P ≤ alpha)
    (n : ℕ) (hw : Matrix.mulVec ((P - 1) ^ n) w = 0) :
    Matrix.mulVec (P - 1) w = 0 := by
  induction n generalizing w with
  | zero =>
      have hz : w = 0 := by simpa using hw
      simp [hz]
  | succ n ih =>
      have h := ih (Matrix.mulVec (P - 1) w) (by
        simpa [pow_succ, Matrix.mulVec_mulVec] using hw)
      exact dobrushin_shift_sq_kernel P pi w hP hpi hα hδ h

/-- The entire generalized eigenspace at one is the line of constant vectors. [Under the listed formal conditions](hyp:hP,hpi,hα,hδ), [the stated conclusion holds](goal).-/
-- @node: dobrushin_maxGenEigenspace_one
lemma dobrushin_maxGenEigenspace_one (P : FourMatrix) (pi : JointState 2 2 → ℝ)
    (hP : IsStochasticMatrix P) (hpi : IsStationary P pi)
    {alpha : ℝ} (hα : alpha < 1) (hδ : dobrushin P ≤ alpha) :
    Module.End.maxGenEigenspace P.mulVecLin 1 =
      Submodule.span ℝ {fun _ : JointState 2 2 => (1 : ℝ)} := by
  ext w
  rw [Module.End.mem_maxGenEigenspace, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨n, hn⟩
    have hpow : Matrix.mulVec ((P - 1) ^ n) w = 0 := by
      change (Matrix.toLin' ((P - 1) ^ n)) w = 0
      rw [Matrix.toLin'_pow, map_sub, Matrix.toLin'_one]
      simpa only [one_smul, Matrix.toLin'_apply', Module.End.one_eq_id] using hn
    have hz := dobrushin_shift_pow_kernel P pi w hP hpi hα hδ n hpow
    have hfix : Matrix.mulVec P w = w := by
      simpa [Matrix.sub_mulVec, sub_eq_zero] using hz
    obtain ⟨c, hc⟩ := dobrushin_fixedVector_constant P hP hα hδ w hfix
    refine ⟨c, ?_⟩
    ext i
    simpa using congrFun hc.symm i
  · rintro ⟨c, rfl⟩
    refine ⟨1, ?_⟩
    ext i
    simp [Matrix.mulVecLin, Matrix.mulVec, dotProduct, hP.2 i]

/-- Strict Dobrushin contraction makes the stationary characteristic root simple. [Under the listed formal conditions](hyp:hP,hpi,hα,hδ), [the stated conclusion holds](goal).-/
-- @node: dobrushin_charpoly_rootMultiplicity_one
lemma dobrushin_charpoly_rootMultiplicity_one (P : FourMatrix)
    (pi : JointState 2 2 → ℝ) (hP : IsStochasticMatrix P) (hpi : IsStationary P pi)
    {alpha : ℝ} (hα : alpha < 1) (hδ : dobrushin P ≤ alpha) :
    Polynomial.rootMultiplicity 1 (Matrix.charpoly P) = 1 := by
  rw [← Matrix.charpoly_mulVecLin,
    ← LinearMap.finrank_maxGenEigenspace_eq,
    dobrushin_maxGenEigenspace_one P pi hP hpi hα hδ]
  exact finrank_span_singleton (by
    intro h
    have := congrFun h ((0 : Fin 2), (0 : Fin 2))
    norm_num at this)

/-- Algebraic simplicity makes the transient characteristic factor nonzero at one. [Under the listed formal conditions](hyp:hP,hpi,hα,hδ), [the stated conclusion holds](goal).-/
-- @node: transientPoly_eval_one_ne_zero
lemma transientPoly_eval_one_ne_zero (P : FourMatrix) (pi : JointState 2 2 → ℝ)
    (hP : IsStochasticMatrix P) (hpi : IsStationary P pi)
    {alpha : ℝ} (hα : alpha < 1) (hδ : dobrushin P ≤ alpha) :
    (transientPoly P).eval 1 ≠ 0 := by
  have hfactor := stochastic_charpoly_factor P hP
  have hnz : (Polynomial.X - Polynomial.C 1) * transientPoly P ≠ 0 := by
    rw [hfactor]
    exact (Matrix.charpoly_monic P).ne_zero
  have hmult := dobrushin_charpoly_rootMultiplicity_one P pi hP hpi hα hδ
  rw [← hfactor, Polynomial.rootMultiplicity_mul hnz,
    Polynomial.rootMultiplicity_X_sub_C_self] at hmult
  have hzero : Polynomial.rootMultiplicity 1 (transientPoly P) = 0 := by omega
  have hq : transientPoly P ≠ 0 := (mul_ne_zero_iff.mp hnz).2
  intro hroot
  exact hq (Polynomial.rootMultiplicity_eq_zero_iff.mp hzero hroot)

/-- The pair polynomial has a nonzero denominator at the stationary root. [Under the listed formal conditions](hyp:hP,hP',hpi,hpi',hα,hδ,hδ'), [the stated conclusion holds](goal).-/
-- @node: pairPoly_eval_one_ne_zero
lemma pairPoly_eval_one_ne_zero (P P' : FourMatrix) (pi pi' : JointState 2 2 → ℝ)
    (hP : IsStochasticMatrix P) (hP' : IsStochasticMatrix P')
    (hpi : IsStationary P pi) (hpi' : IsStationary P' pi')
    {alpha : ℝ} (hα : alpha < 1)
    (hδ : dobrushin P ≤ alpha) (hδ' : dobrushin P' ≤ alpha) :
    (pairPoly P P').eval 1 ≠ 0 := by
  simpa [pairPoly, Polynomial.eval_mul] using
    mul_ne_zero (transientPoly_eval_one_ne_zero P pi hP hpi hα hδ)
    (transientPoly_eval_one_ne_zero P' pi' hP' hpi' hα hδ')

/-- The transient polynomial is exactly the stationary rank-one projection. [Under the listed formal conditions](hyp:hP,hpi,hα,hδ), [the stated conclusion holds](goal).-/
-- @node: transientPoly_aeval_projection
lemma transientPoly_aeval_projection (P : FourMatrix) (pi : JointState 2 2 → ℝ)
    (hP : IsStochasticMatrix P) (hpi : IsStationary P pi)
    {alpha : ℝ} (hα : alpha < 1) (hδ : dobrushin P ≤ alpha) :
    Polynomial.aeval P (transientPoly P) =
      fun _ j => (transientPoly P).eval 1 * pi j := by
  classical
  let A := Polynomial.aeval P (transientPoly P)
  have hPA : P * A = A := by
    have h := transientPoly_aeval_annihilated P hP
    rw [sub_mul, one_mul, sub_eq_zero] at h
    exact h
  have hleft := stationary_vecMul_aeval P pi hpi (transientPoly P)
  ext i j
  have hfixed : Matrix.mulVec P (fun k => A k j) = fun k => A k j := by
    ext k
    exact congrFun (congrFun hPA k) j
  obtain ⟨c, hc⟩ := dobrushin_fixedVector_constant P hP hα hδ _ hfixed
  have hcol (k) : A k j = c := congrFun hc k
  have hcval : c = (transientPoly P).eval 1 * pi j := by
    have h := congrFun hleft j
    change (∑ k, pi k * A k j) = _ at h
    simp_rw [hcol] at h
    rw [← Finset.sum_mul, hpi.1.2, one_mul] at h
    exact h
  exact (hcol i).trans hcval

/-- A stochastic matrix's transient characteristic factor is monic. [Under the listed formal conditions](hyp:hP), [the stated conclusion holds](goal).-/
-- @node: transientPoly_monic
lemma transientPoly_monic (P : FourMatrix) (hP : IsStochasticMatrix P) :
    (transientPoly P).Monic := by
  apply (Polynomial.monic_X_sub_C (1 : ℝ)).of_mul_monic_left
  rw [stochastic_charpoly_factor P hP]
  exact Matrix.charpoly_monic P

/-- The four-state transient characteristic factor has degree three. [the stated conclusion holds](goal).-/
-- @node: transientPoly_natDegree_three
lemma transientPoly_natDegree_three (P : FourMatrix) :
    (transientPoly P).natDegree = 3 := by
  change (Matrix.charpoly P /ₘ (Polynomial.X - Polynomial.C 1)).natDegree = 3
  rw [Polynomial.natDegree_divByMonic (Matrix.charpoly P)
    (Polynomial.monic_X_sub_C (1 : ℝ)), Polynomial.natDegree_X_sub_C]
  simp [Matrix.charpoly_natDegree_eq_dim, JointState, Fintype.card_prod]

/-- The product of stochastic transient factors is monic. [Under the listed formal conditions](hyp:hP,hP'), [the stated conclusion holds](goal).-/
-- @node: pairPoly_monic
lemma pairPoly_monic (P P' : FourMatrix)
    (hP : IsStochasticMatrix P) (hP' : IsStochasticMatrix P') :
    (pairPoly P P').Monic :=
  (transientPoly_monic P hP).mul (transientPoly_monic P' hP')

/-- The pair factor has exactly six roots counted with algebraic multiplicity. [Under the listed formal conditions](hyp:hP,hP'), [the stated conclusion holds](goal).-/
-- @node: pairPoly_natDegree_six
lemma pairPoly_natDegree_six (P P' : FourMatrix)
    (hP : IsStochasticMatrix P) (hP' : IsStochasticMatrix P') :
    (pairPoly P P').natDegree = 6 := by
  rw [pairPoly, Polynomial.natDegree_mul
    (transientPoly_monic P hP).ne_zero (transientPoly_monic P' hP').ne_zero,
    transientPoly_natDegree_three P, transientPoly_natDegree_three P']

/-- Transient roots exclude one and inherit the complex Dobrushin disk bound. [Under the listed formal conditions](hyp:hP,hpi,hα,hδ,hz), [the stated conclusion holds](goal).-/
-- @node: transientPoly_complex_root_norm_le
lemma transientPoly_complex_root_norm_le (P : FourMatrix) (pi : JointState 2 2 → ℝ)
    (hP : IsStochasticMatrix P) (hpi : IsStationary P pi)
    {alpha : ℝ} (hα : alpha < 1) (hδ : dobrushin P ≤ alpha)
    {z : ℂ} (hz : z ∈ ((transientPoly P).map (algebraMap ℝ ℂ)).roots) :
    ‖z‖ ≤ alpha := by
  have hq : ((transientPoly P).map (algebraMap ℝ ℂ)).IsRoot z :=
    Polynomial.isRoot_of_mem_roots hz
  have hne : z ≠ 1 := by
    intro heq
    subst z
    have hzero : (((transientPoly P).eval (1 : ℝ) : ℝ) : ℂ) = 0 := by
      simpa [Polynomial.IsRoot, Polynomial.eval_map] using hq
    exact transientPoly_eval_one_ne_zero P pi hP hpi hα hδ
      (Complex.ofReal_eq_zero.mp hzero)
  apply dobrushin_complex_charpoly_root_norm_le P hP hδ hne
  rw [← stochastic_charpoly_factor P hP, Polynomial.map_mul]
  simp only [Polynomial.IsRoot, Polynomial.eval_mul] at hq ⊢
  rw [hq, mul_zero]

/-- Every root of the pair factor belongs to one of its two transient factors. [Under the listed formal conditions](hyp:hP,hP',hpi,hpi',hα,hδ,hδ'), [the stated conclusion holds](goal).-/
-- @node: pairPoly_complex_roots_norm_le
lemma pairPoly_complex_roots_norm_le (P P' : FourMatrix)
    (pi pi' : JointState 2 2 → ℝ) (hP : IsStochasticMatrix P)
    (hP' : IsStochasticMatrix P') (hpi : IsStationary P pi) (hpi' : IsStationary P' pi')
    {alpha : ℝ} (hα : alpha < 1) (hδ : dobrushin P ≤ alpha) (hδ' : dobrushin P' ≤ alpha) :
    ∀ z ∈ ((pairPoly P P').map (algebraMap ℝ ℂ)).roots, ‖z‖ ≤ alpha := by
  intro z hz
  have hnz : ((pairPoly P P').map (algebraMap ℝ ℂ)) ≠ 0 :=
    ((pairPoly_monic P P' hP hP').map _).ne_zero
  rw [pairPoly, Polynomial.map_mul] at hz hnz
  rw [Polynomial.roots_mul hnz, Multiset.mem_add] at hz
  rcases hz with hz | hz
  · exact transientPoly_complex_root_norm_le P pi hP hpi hα hδ hz
  · exact transientPoly_complex_root_norm_le P' pi' hP' hpi' hα hδ' hz

/-- The pair factor has degree at most six on the four-state carrier. [the stated conclusion holds](goal).-/
-- @node: pairPoly_natDegree_lt_seven
lemma pairPoly_natDegree_lt_seven (P P' : FourMatrix) :
    (pairPoly P P').natDegree < 7 := by
  have hdeg (R : FourMatrix) : (transientPoly R).natDegree = 3 := by
    change (Matrix.charpoly R /ₘ (Polynomial.X - Polynomial.C 1)).natDegree = 3
    rw [Polynomial.natDegree_divByMonic (Matrix.charpoly R)
      (Polynomial.monic_X_sub_C (1 : ℝ)), Polynomial.natDegree_X_sub_C]
    simp [Matrix.charpoly_natDegree_eq_dim, JointState, Fintype.card_prod]
  have h := Polynomial.natDegree_mul_le (p := transientPoly P) (q := transientPoly P')
  rw [hdeg P, hdeg P'] at h
  exact lt_of_le_of_lt h (by norm_num)

/-- Multiplying by any other polynomial preserves the stationary projection. [Under the listed formal conditions](hyp:hP,hpi,hα,hδ), [the stated conclusion holds](goal).-/
-- @node: transientPoly_mul_aeval_projection
lemma transientPoly_mul_aeval_projection (P : FourMatrix) (pi : JointState 2 2 → ℝ)
    (hP : IsStochasticMatrix P) (hpi : IsStationary P pi)
    {alpha : ℝ} (hα : alpha < 1) (hδ : dobrushin P ≤ alpha) (f : Polynomial ℝ) :
    Polynomial.aeval P (transientPoly P * f) =
      fun _ j => (transientPoly P * f).eval 1 * pi j := by
  rw [map_mul, transientPoly_aeval_projection P pi hP hpi hα hδ]
  have hleft := stationary_vecMul_aeval P pi hpi f
  ext i j
  change (∑ k, ((transientPoly P).eval 1 * pi k) *
    (Polynomial.aeval P f) k j) = _
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  change (transientPoly P).eval 1 * (Matrix.vecMul pi (Polynomial.aeval P f)) j = _
  rw [hleft]
  simp [mul_assoc]

/-- Averaging the projection by any initial law gives the stationary value. [Under the listed formal conditions](hyp:hnu,hproj), [the stated conclusion holds](goal).-/
-- @node: polynomial_projection_value
lemma polynomial_projection_value (nu pi r : JointState 2 2 → ℝ)
    (hnu : IsProbabilityVector nu) (f : Polynomial ℝ) (P : FourMatrix)
    (hproj : Polynomial.aeval P f = fun _ j => f.eval 1 * pi j) :
    (∑ s, (Matrix.vecMul nu (Polynomial.aeval P f)) s * r s) =
      f.eval 1 * matrixValue pi r := by
  rw [hproj]
  simp only [Matrix.vecMul, dotProduct]
  simp_rw [← Finset.sum_mul, hnu.2, one_mul, mul_assoc]
  exact (Finset.mul_sum _ _ _).symm

/-- The exact seven-moment identity follows without choosing an eigenbasis. [Under the listed formal conditions](hyp:hα,hP,hP',hnu,hnu',hpi,hpi',hδ,hδ'), [the stated conclusion holds](goal).-/
-- @node: pairPolynomial_value_identity
lemma pairPolynomial_value_identity
    (P P' : FourMatrix) (nu nu' pi pi' r r' : JointState 2 2 → ℝ)
    {alpha : ℝ} (hα : alpha < 1)
    (hP : IsStochasticMatrix P) (hP' : IsStochasticMatrix P')
    (hnu : IsProbabilityVector nu) (hnu' : IsProbabilityVector nu')
    (hpi : IsStationary P pi) (hpi' : IsStationary P' pi')
    (hδ : dobrushin P ≤ alpha) (hδ' : dobrushin P' ≤ alpha) :
    (pairPoly P P').eval 1 * (matrixValue pi r - matrixValue pi' r') =
      ∑ k : Fin 7, (pairPoly P P').coeff k.val *
        (matrixMoment nu P r k.val - matrixMoment nu' P' r' k.val) := by
  have hproj := transientPoly_mul_aeval_projection P pi hP hpi hα hδ (transientPoly P')
  have hproj' := transientPoly_mul_aeval_projection P' pi' hP' hpi' hα hδ'
    (transientPoly P)
  rw [mul_comm (transientPoly P') (transientPoly P)] at hproj'
  have hsum := matrixMoment_polynomial_sum nu r P (pairPoly P P')
    (pairPoly_natDegree_lt_seven P P')
  have hsum' := matrixMoment_polynomial_sum nu' r' P' (pairPoly P P')
    (pairPoly_natDegree_lt_seven P P')
  rw [polynomial_projection_value nu pi r hnu (pairPoly P P') P hproj] at hsum
  rw [polynomial_projection_value nu' pi' r' hnu' (pairPoly P P') P' hproj'] at hsum'
  rw [mul_sub, hsum, hsum', ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  exact (mul_sub _ _ _).symm

/-- The exact identity transfers moment error with the actual polynomial coefficient ratio. [Under the listed formal conditions](hyp:hα,hP,hP',hnu,hnu',hpi,hpi',hδ,hδ'), [the stated conclusion holds](goal).-/
-- @node: pairPolynomial_value_coefficient_modulus
lemma pairPolynomial_value_coefficient_modulus
    (P P' : FourMatrix) (nu nu' pi pi' r r' : JointState 2 2 → ℝ)
    {alpha : ℝ} (hα : alpha < 1)
    (hP : IsStochasticMatrix P) (hP' : IsStochasticMatrix P')
    (hnu : IsProbabilityVector nu) (hnu' : IsProbabilityVector nu')
    (hpi : IsStationary P pi) (hpi' : IsStationary P' pi')
    (hδ : dobrushin P ≤ alpha) (hδ' : dobrushin P' ≤ alpha) :
    |matrixValue pi r - matrixValue pi' r'| ≤
      ((∑ k : Fin 7, |(pairPoly P P').coeff k.val|) / |(pairPoly P P').eval 1|) *
        (⨆ k : Fin 7, |matrixMoment nu P r k.val - matrixMoment nu' P' r' k.val|) := by
  classical
  let err := fun k : Fin 7 => |matrixMoment nu P r k.val - matrixMoment nu' P' r' k.val|
  have hidentity := pairPolynomial_value_identity P P' nu nu' pi pi' r r'
    hα hP hP' hnu hnu' hpi hpi' hδ hδ'
  have hweighted : |(pairPoly P P').eval 1| * |matrixValue pi r - matrixValue pi' r'| ≤
      (∑ k : Fin 7, |(pairPoly P P').coeff k.val|) * (⨆ k, err k) := by
    calc
      _ = |(pairPoly P P').eval 1 * (matrixValue pi r - matrixValue pi' r')| :=
        (abs_mul _ _).symm
      _ = |∑ k : Fin 7, (pairPoly P P').coeff k.val *
          (matrixMoment nu P r k.val - matrixMoment nu' P' r' k.val)| :=
        congrArg abs hidentity
      _ ≤ ∑ k : Fin 7, |(pairPoly P P').coeff k.val *
          (matrixMoment nu P r k.val - matrixMoment nu' P' r' k.val)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k : Fin 7, |(pairPoly P P').coeff k.val| * (⨆ j, err j) := by
        apply Finset.sum_le_sum
        intro k _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left
          (le_ciSup (Finite.bddAbove_range err) k) (abs_nonneg _)
      _ = _ := (Finset.sum_mul _ _ _).symm
  have hpos : 0 < |(pairPoly P P').eval 1| := abs_pos.mpr
    (pairPoly_eval_one_ne_zero P P' pi pi' hP hP' hpi hpi' hα hδ hδ')
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hpos).mpr
  simpa only [mul_comm] using hweighted

-- @node: lem:pair-polynomial-modulus
/-- Exact pair-polynomial identity and seven-moment modulus, including defective
and complex transient modes. [Under the listed formal conditions](hyp:hα0,hα1,hP,hP',hν,hν',hπ,hπ',hr,hr',hδ,hδ'), [the stated conclusion holds](goal).-/
lemma pairPolynomial_value_modulus
    (P P' : FourMatrix) (nu nu' pi pi' r r' : JointState 2 2 → ℝ)
    (alpha : ℝ)
    (hα0 : 0 < alpha) (hα1 : alpha < 1)
    (hP : IsStochasticMatrix P) (hP' : IsStochasticMatrix P')
    (hν : IsProbabilityVector nu) (hν' : IsProbabilityVector nu')
    (hπ : IsStationary P pi) (hπ' : IsStationary P' pi')
    (hr : ∀ s, r s ∈ Set.Icc (0 : ℝ) 1)
    (hr' : ∀ s, r' s ∈ Set.Icc (0 : ℝ) 1)
    (hδ : dobrushin P ≤ alpha) (hδ' : dobrushin P' ≤ alpha) :
    Polynomial.rootMultiplicity 1 (Matrix.charpoly P) = 1 ∧
    Polynomial.rootMultiplicity 1 (Matrix.charpoly P') = 1 ∧
    (pairPoly P P').eval 1 * (matrixValue pi r - matrixValue pi' r') =
      ∑ k : Fin 7, (pairPoly P P').coeff k.val *
        (matrixMoment nu P r k.val - matrixMoment nu' P' r' k.val) ∧
    |matrixValue pi r - matrixValue pi' r'| ≤
      stabilityFactor alpha *
        (⨆ k : Fin 7, |matrixMoment nu P r k.val - matrixMoment nu' P' r' k.val|) := by
  have hidentity := pairPolynomial_value_identity P P' nu nu' pi pi' r r'
    hα1 hP hP' hν hν' hπ hπ' hδ hδ'
  have hsimp := dobrushin_charpoly_rootMultiplicity_one P pi hP hπ hα1 hδ
  have hsimp' := dobrushin_charpoly_rootMultiplicity_one P' pi' hP' hπ' hα1 hδ'
  refine ⟨hsimp, hsimp', hidentity, ?_⟩
  have hdata := pairPolynomial_value_coefficient_modulus P P' nu nu' pi pi' r r'
    hα1 hP hP' hν hν' hπ hπ' hδ hδ'
  have hcoeff :
      (∑ k : Fin 7, |(pairPoly P P').coeff k.val|) / |(pairPoly P P').eval 1| ≤
        stabilityFactor alpha := by
    have hroots : ∀ z ∈ ((pairPoly P P').map (algebraMap ℝ ℂ)).roots,
        ‖z‖ ≤ alpha := by
      exact pairPoly_complex_roots_norm_le P P' pi pi' hP hP' hπ hπ' hα1 hδ hδ'
    exact degreeSix_coefficient_ratio_le_of_roots_le (pairPoly P P') alpha
      (pairPoly_monic P P' hP hP') (pairPoly_natDegree_six P P' hP hP') hα1 hroots
  have hmax0 : 0 ≤ (⨆ k : Fin 7,
      |matrixMoment nu P r k.val - matrixMoment nu' P' r' k.val|) := by
    exact (abs_nonneg (matrixMoment nu P r 0 - matrixMoment nu' P' r' 0)).trans
      (le_ciSup (f := fun k : Fin 7 =>
        |matrixMoment nu P r k.val - matrixMoment nu' P' r' k.val|)
        (Finite.bddAbove_range _) (0 : Fin 7))
  exact hdata.trans (mul_le_mul_of_nonneg_right hcoeff hmax0)
  -- @realizes \(P\)(stochastic contracted first kernel) @realizes \(P'\)(second kernel)
  -- @realizes \(\nu\)(probability law) @realizes \(\nu'\)(second law)
  -- @realizes \(\pi\)(stationary law) @realizes \(\pi'\)(second stationary law)
  -- @realizes \(r\)(unit-range reward) @realizes \(r'\)(second reward)

end CausalSmith.Stat.PomdpBinaryhiddenRate
