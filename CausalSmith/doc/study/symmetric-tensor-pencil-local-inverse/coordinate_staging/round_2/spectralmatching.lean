import Causalean.Mathlib.Analysis.SymmetricTensorPencil.Pencil

/-!
# Spectral localization and finite matching

This module isolates the two ingredients that precede spectral-projector perturbation: a
finite-dimensional Bauer--Fike localization theorem for explicitly diagonalized real matrices,
and the finite matching argument that turns one-sided localization into a permutation under a
separation margin.  It also records the elementary condition-number bound for coordinate
projectors.  The localization convention is the spectral-norm Bauer--Fike bound used in the
robust simultaneous-diagonalization analysis of Goyal--Vempala--Xiao, arXiv:1306.5825,
`perturbation.tex`, Theorem `thm:bauer`.
-/

namespace Causalean.Mathlib.Analysis.SymmetricTensorPencil

open scoped Matrix.Norms.L2Operator

/-- A finite real scalar family has pairwise gap at least `gap`. With [its explicit inputs](hyp:values,gap), [the defined object](goal) is [given by the displayed formula](step:1). -/
def PairwiseGap {ι : Type*} (values : ι → ℝ) (gap : ℝ) : Prop :=
  ∀ i j, i ≠ j → gap ≤ |values i - values j|

/-- The matrix diagonalized by `S` with the prescribed real diagonal entries. With [its explicit inputs](hyp:S,values), [the defined object](goal) is [given by the displayed formula](step:1). -/
noncomputable def diagonalizableMatrix {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ)
    (values : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  S * Matrix.diagonal values * S⁻¹

/-- The rank-one spectral projector selected by coordinate `j` of an invertible diagonalizer. With [its explicit inputs](hyp:S,j), [the defined object](goal) is [given by the displayed formula](step:1). -/
noncomputable def coordinateProjector {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) :
    Matrix (Fin n) (Fin n) ℝ :=
  S * Matrix.diagonal (fun k => if k = j then 1 else 0) * S⁻¹

/-- Every coordinate projector of a diagonalizer has Euclidean operator norm at most the
declared condition-number envelope. Under [the listed assumptions](hyp:hS,hcondition), [the stated conclusion follows](goal). -/
-- Proof route: use submultiplicativity twice, the fact that the one-coordinate diagonal
-- projector has operator norm one, and the supplied bound on `‖S‖₂ ‖S⁻¹‖₂`.
theorem coordinateProjector_operatorNorm_le {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) {chi : ℝ}
    (hS : IsUnit S.det)
    (hcondition : squareOperatorNorm S * squareOperatorNorm S⁻¹ ≤ chi) :
    squareOperatorNorm (coordinateProjector S j) ≤ chi := by
  let _ : Nonempty (Fin n) := ⟨j⟩
  unfold coordinateProjector squareOperatorNorm
  rw [Matrix.l2_opNorm_toEuclideanCLM]
  calc
    ‖S * Matrix.diagonal (fun k => if k = j then (1 : ℝ) else 0) * S⁻¹‖
        ≤ ‖S * Matrix.diagonal (fun k => if k = j then (1 : ℝ) else 0)‖ * ‖S⁻¹‖ :=
      Matrix.l2_opNorm_mul _ _
    _ ≤ (‖S‖ * ‖Matrix.diagonal
        (fun k => if k = j then (1 : ℝ) else 0)‖) * ‖S⁻¹‖ := by
      gcongr
      exact Matrix.l2_opNorm_mul _ _
    _ = ‖S‖ * ‖S⁻¹‖ := by
      rw [Matrix.l2_opNorm_diagonal]
      have hnorm : ‖(fun k : Fin n => if k = j then (1 : ℝ) else 0)‖ = 1 := by
        apply le_antisymm
        · apply (pi_norm_le_iff_of_nonempty _).2
          intro k
          split <;> norm_num
        · simpa using norm_le_pi_norm
            (fun k : Fin n => if k = j then (1 : ℝ) else 0) j
      rw [hnorm, mul_one]
    _ ≤ chi := hcondition

private theorem min_abs_mul_euclidean_norm_le_diagonal_mulVec_norm {n : ℕ}
    (d x : Fin n → ℝ) (j : Fin n) (hj : ∀ k, |d j| ≤ |d k|) :
    |d j| * ‖WithLp.toLp 2 x‖ ≤
      ‖WithLp.toLp 2 ((Matrix.diagonal d).mulVec x)‖ := by
  apply (sq_le_sq₀ (mul_nonneg (abs_nonneg _) (norm_nonneg _)) (norm_nonneg _)).mp
  rw [mul_pow, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp only [Matrix.mulVec_diagonal]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  rw [mul_pow, ← sq_abs (d k)]
  exact mul_le_mul_of_nonneg_right
    ((sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr (hj k))
    (sq_nonneg (x k))

/-- Every prescribed eigenvalue of a nearby explicitly diagonalized matrix lies within
`chi * delta` of some eigenvalue of the reference diagonalization. Under [the listed assumptions](hyp:hS,hS',hcondition,hclose), [the stated conclusion follows](goal). -/
-- Proof route: take the corresponding nonzero column of `S'` as an eigenvector of the
-- perturbed matrix, conjugate its residual by `S⁻¹`, choose a largest coordinate, and compare
-- that coordinate against the Euclidean norm.  This is the finite-dimensional Bauer--Fike
-- argument and uses no normality assumption.
theorem diagonalizableMatrix_eigenvalue_localization {n : ℕ} [NeZero n]
    (S S' : Matrix (Fin n) (Fin n) ℝ) (values values' : Fin n → ℝ)
    {chi delta : ℝ}
    (hS : IsUnit S.det) (hS' : IsUnit S'.det)
    (hcondition : squareOperatorNorm S * squareOperatorNorm S⁻¹ ≤ chi)
    (hclose : squareOperatorNorm
      (diagonalizableMatrix S' values' - diagonalizableMatrix S values) ≤ delta) :
    ∀ j', ∃ j, |values' j' - values j| ≤ chi * delta := by
  classical
  intro j'
  obtain ⟨j, _, hj⟩ := Finset.exists_min_image Finset.univ
    (fun k => |values' j' - values k|) Finset.univ_nonempty
  refine ⟨j, ?_⟩
  let v : Fin n → ℝ := S'.col j'
  let x : Fin n → ℝ := (S⁻¹).mulVec v
  have hv_ne : v ≠ 0 := by
    intro hv
    apply hS'.ne_zero
    apply Matrix.det_eq_zero_of_column_eq_zero j'
    intro i
    exact congrFun hv i
  have hv_recover : S.mulVec x = v := by
    simp [x, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv S hS]
  have hx_ne : x ≠ 0 := by
    intro hx
    apply hv_ne
    rw [← hv_recover, hx, Matrix.mulVec_zero]
  have hinvcol : (S'⁻¹).mulVec v = Pi.single j' 1 := by
    rw [show v = S'.mulVec (Pi.single j' 1) by simp [v]]
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul S' hS', Matrix.one_mulVec]
  have heigen :
      (diagonalizableMatrix S' values').mulVec v = values' j' • v := by
    calc
      _ = S'.mulVec ((Matrix.diagonal values').mulVec ((S'⁻¹).mulVec v)) := by
        rw [diagonalizableMatrix, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      _ = S'.mulVec ((Matrix.diagonal values').mulVec (Pi.single j' 1)) := by
        rw [hinvcol]
      _ = S'.mulVec (values' j' • Pi.single j' 1) := by
        congr 1
        ext k
        by_cases hk : k = j'
        · subst k
          simp [Matrix.mulVec_diagonal]
        · simp [Matrix.mulVec_diagonal, hk]
      _ = values' j' • S'.mulVec (Pi.single j' 1) :=
        Matrix.mulVec_smul S' (values' j') (Pi.single j' (1 : ℝ))
      _ = values' j' • v := by rw [Matrix.mulVec_single_one]
  have hreference :
      (diagonalizableMatrix S values).mulVec v =
        S.mulVec ((Matrix.diagonal values).mulVec x) := by
    rw [diagonalizableMatrix, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  let E := diagonalizableMatrix S' values' - diagonalizableMatrix S values
  let d : Fin n → ℝ := fun k => values' j' - values k
  have hcancel (z : Fin n → ℝ) : (S⁻¹).mulVec (S.mulVec z) = z := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul S hS, Matrix.one_mulVec]
  have hres : (Matrix.diagonal d).mulVec x = (S⁻¹).mulVec (E.mulVec v) := by
    rw [show E = diagonalizableMatrix S' values' -
      diagonalizableMatrix S values by rfl]
    rw [Matrix.sub_mulVec, heigen, hreference, Matrix.mulVec_sub, Matrix.mulVec_smul]
    change (Matrix.diagonal d).mulVec x =
      values' j' • x - (S⁻¹).mulVec (S.mulVec ((Matrix.diagonal values).mulVec x))
    rw [hcancel]
    ext k
    simp [d, Matrix.mulVec_diagonal]
    ring
  have hlower :
      |values' j' - values j| * ‖WithLp.toLp 2 x‖ ≤
        ‖WithLp.toLp 2 ((Matrix.diagonal d).mulVec x)‖ := by
    apply min_abs_mul_euclidean_norm_le_diagonal_mulVec_norm d x j
    intro k
    exact hj k (Finset.mem_univ k)
  have hu1 :
      ‖WithLp.toLp 2 ((Matrix.diagonal d).mulVec x)‖ ≤
        ‖S⁻¹‖ * ‖WithLp.toLp 2 (E.mulVec v)‖ := by
    rw [hres]
    exact Matrix.l2_opNorm_mulVec S⁻¹ (WithLp.toLp 2 (E.mulVec v))
  have hu2 :
      ‖WithLp.toLp 2 (E.mulVec v)‖ ≤ ‖E‖ * ‖WithLp.toLp 2 v‖ :=
    Matrix.l2_opNorm_mulVec E (WithLp.toLp 2 v)
  have hvnorm :
      ‖WithLp.toLp 2 v‖ ≤ ‖S‖ * ‖WithLp.toLp 2 x‖ := by
    rw [← hv_recover]
    exact Matrix.l2_opNorm_mulVec S (WithLp.toLp 2 x)
  have hxnorm_pos : 0 < ‖WithLp.toLp 2 x‖ := norm_pos_iff.mpr (by
    exact fun hx => hx_ne (WithLp.toLp_injective 2 hx))
  have hE : ‖E‖ ≤ delta := by
    rw [← Matrix.l2_opNorm_toEuclideanCLM]
    simpa [E, squareOperatorNorm] using hclose
  have hdelta : 0 ≤ delta := (norm_nonneg E).trans hE
  have hcond : ‖S‖ * ‖S⁻¹‖ ≤ chi := by
    simpa only [squareOperatorNorm, Matrix.l2_opNorm_toEuclideanCLM] using hcondition
  have hupper :
      ‖WithLp.toLp 2 ((Matrix.diagonal d).mulVec x)‖ ≤
        (chi * delta) * ‖WithLp.toLp 2 x‖ := by
    calc
      _ ≤ ‖S⁻¹‖ * ‖WithLp.toLp 2 (E.mulVec v)‖ := hu1
      _ ≤ ‖S⁻¹‖ * (‖E‖ * ‖WithLp.toLp 2 v‖) :=
        mul_le_mul_of_nonneg_left hu2 (norm_nonneg _)
      _ ≤ ‖S⁻¹‖ * (delta * ‖WithLp.toLp 2 v‖) := by
        gcongr
      _ ≤ ‖S⁻¹‖ * (delta * (‖S‖ * ‖WithLp.toLp 2 x‖)) := by
        gcongr
      _ = ((‖S‖ * ‖S⁻¹‖) * delta) * ‖WithLp.toLp 2 x‖ := by ring
      _ ≤ (chi * delta) * ‖WithLp.toLp 2 x‖ := by
        gcongr
  exact le_of_mul_le_mul_right (hlower.trans hupper) hxnorm_pos

/-- One-sided localization between two equally sized finite scalar families becomes a
permutation matching when the source family is separated by more than twice the localization
radius. Under [the listed assumptions](hyp:hradius,hgap',hlocal,hsmall), [the stated conclusion follows](goal). -/
-- Proof route: choose for every primed index one nearby unprimed index.  Two primed indices
-- with the same choice would violate separation by the triangle inequality, so the choice map
-- is injective, hence bijective on the finite type; its inverse is the required permutation.
theorem exists_permutation_matching_of_localization {n : ℕ}
    (values values' : Fin n → ℝ) {gap radius : ℝ}
    (hradius : 0 ≤ radius) (hgap' : PairwiseGap values' gap)
    (hlocal : ∀ j', ∃ j, |values' j' - values j| ≤ radius)
    (hsmall : 2 * radius < gap) :
    ∃ pi : Equiv.Perm (Fin n), ∀ j, |values' (pi j) - values j| ≤ radius := by
  classical
  choose f hf using hlocal
  have hinj : Function.Injective f := by
    intro a b hab
    by_contra hne
    have hgapab : gap ≤ |values' a - values' b| := hgap' a b hne
    have hdist : |values' a - values' b| ≤ 2 * radius := by
      calc
        |values' a - values' b|
            = |(values' a - values (f a)) + (values (f b) - values' b)| := by
                rw [hab]
                congr 1
                ring
        _ ≤ |values' a - values (f a)| + |values (f b) - values' b| :=
          abs_add_le _ _
        _ = |values' a - values (f a)| + |values' b - values (f b)| := by
              rw [abs_sub_comm (values (f b)) (values' b)]
        _ ≤ radius + radius := add_le_add (hf a) (hf b)
        _ = 2 * radius := by ring
    exact (not_lt_of_ge (hgapab.trans hdist)) hsmall
  have hbij : Function.Bijective f := hinj.bijective_of_finite
  let e : Equiv.Perm (Fin n) := Equiv.ofBijective f hbij
  refine ⟨e.symm, ?_⟩
  intro j
  change |values' ((Equiv.ofBijective f hbij).symm j) - values j| ≤ radius
  have hfj : f ((Equiv.ofBijective f hbij).symm j) = j :=
    Equiv.ofBijective_apply_symm_apply f hbij j
  simpa [hfj] using hf ((Equiv.ofBijective f hbij).symm j)

end Causalean.Mathlib.Analysis.SymmetricTensorPencil
