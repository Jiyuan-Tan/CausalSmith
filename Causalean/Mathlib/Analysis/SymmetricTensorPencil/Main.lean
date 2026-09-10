import Causalean.Mathlib.Analysis.SymmetricTensorPencil.Recovery

/-!
# Quantitative local inverse for symmetric tensor pencils

This module assembles contraction, lifted conditioning, pencil perturbation, spectral-projector
matching, trace-coordinate recovery, and normalization into a permutation-aligned local inverse
for finite symmetric rank-one tensor decompositions.
-/

namespace Causalean.Mathlib.Analysis.SymmetricTensorPencil

open scoped Matrix.Norms.L2Operator

/-- The contracted denominator singular-value margin assembled from coefficient, probe, and
lifted-factor margins. With [its explicit inputs](hyp:q,sigma,kappa), [the defined object](goal) is [given by the displayed formula](step:1). -/
noncomputable def contractedMargin (q : ℕ) (sigma kappa : ℝ) : ℝ :=
  kappa * sigma ^ (q + 2)

/-- The condition-number envelope for a lifted matrix with `n` unit columns and least singular
value at least `sigma`. With [its explicit inputs](hyp:n,sigma), [the defined object](goal) is [given by the displayed formula](step:1). -/
noncomputable def liftedConditionEnvelope (n : ℕ) (sigma : ℝ) : ℝ :=
  Real.sqrt n / sigma

/-- The admissible tensor perturbation radius for the quantitative tensor-pencil inverse. With [its explicit inputs](hyp:n,q,sigma,kappa,Lambda), [the defined object](goal) is [given by the displayed formula](step:1). -/
noncomputable def localInverseRadius (n q : ℕ) (sigma kappa Lambda : ℝ) : ℝ :=
  let eta := contractedMargin q sigma kappa
  let chi := liftedConditionEnvelope n sigma
  let h := pencilPerturbationConstant n eta Lambda
  min (eta / 2) (sigma / (6 * chi * h))

/-- The coordinatewise trace-recovery Lipschitz factor for the quantitative tensor-pencil inverse. With [its explicit inputs](hyp:n,q,sigma,kappa,Lambda), [the defined object](goal) is [given by the displayed formula](step:1). -/
noncomputable def traceRecoveryConstant (n q : ℕ)
    (sigma kappa Lambda : ℝ) : ℝ :=
  let eta := contractedMargin q sigma kappa
  let chi := liftedConditionEnvelope n sigma
  let h := pencilPerturbationConstant n eta Lambda
  n * h * (2 * chi + 6 * n * Lambda * chi ^ 2 / (eta * sigma))

/-- The final factor-matrix Frobenius Lipschitz factor for the quantitative tensor-pencil
inverse. With [its explicit inputs](hyp:p,n,q,sigma,kappa,Lambda), [the defined object](goal) is [given by the displayed formula](step:1). -/
noncomputable def factorRecoveryConstant (p n q : ℕ)
    (sigma kappa Lambda : ℝ) : ℝ :=
  2 * Real.sqrt (n * p) * traceRecoveryConstant n q sigma kappa Lambda

private theorem exists_orthonormalColumns_sameColumnSpace
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℝ) (hinj : Function.Injective A.toEuclideanLin) :
    ∃ U : Matrix ι (Fin n) ℝ, OrthonormalColumns U ∧ SameColumnSpace U A := by
  classical
  have hrank : Module.finrank ℝ A.toEuclideanLin.range = n := by
    rw [LinearMap.finrank_range_of_inj hinj]
    simp [finrank_euclideanSpace]
  let b : OrthonormalBasis (Fin n) ℝ A.toEuclideanLin.range :=
    (stdOrthonormalBasis ℝ A.toEuclideanLin.range).reindex (finCongr hrank)
  let U : Matrix ι (Fin n) ℝ := fun i j =>
    WithLp.ofLp (((b j : A.toEuclideanLin.range) : EuclideanSpace ℝ ι)) i
  have hU (z : EuclideanSpace ℝ (Fin n)) :
      U.toEuclideanLin z =
        (↑((b.repr).symm z) : EuclideanSpace ℝ ι) := by
    rw [Matrix.toEuclideanLin_apply]
    apply PiLp.ext
    intro i
    have hb := congrArg
      (fun x : A.toEuclideanLin.range =>
        WithLp.ofLp (x : EuclideanSpace ℝ ι) i)
      (b.sum_repr_symm z)
    change (∑ j, U i j * WithLp.ofLp z j) =
      WithLp.ofLp (↑((b.repr).symm z) : EuclideanSpace ℝ ι) i
    simpa [U, mul_comm] using hb
  refine ⟨U, ?_, ?_⟩
  · unfold OrthonormalColumns
    ext i j
    have hb := b.inner_eq_ite i j
    change (∑ x, U x i * U x j) = if i = j then 1 else 0
    rw [← hb]
    change (∑ x, _ * _) = inner ℝ
      (↑(b i) : EuclideanSpace ℝ ι) (↑(b j) : EuclideanSpace ℝ ι)
    rw [PiLp.inner_apply]
    simp [U, RCLike.inner_apply, mul_comm]
  · unfold SameColumnSpace
    apply le_antisymm
    · rintro x ⟨z, rfl⟩
      rw [hU]
      exact ((b.repr).symm z).property
    · intro x hx
      let xs : A.toEuclideanLin.range := ⟨x, hx⟩
      refine ⟨b.repr xs, ?_⟩
      rw [hU, LinearIsometryEquiv.symm_apply_apply]

private theorem finiteFrobeniusNorm_smul_eq_abs {p : ℕ} (a : ℝ) (x : Vec p) :
    finiteFrobeniusNorm (a • x) = |a| * finiteFrobeniusNorm x := by
  unfold finiteFrobeniusNorm
  rw [← Real.sqrt_sq_eq_abs a, ← Real.sqrt_mul (sq_nonneg a)]
  congr 1
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

private theorem abs_dot_le_one_of_unit {p : ℕ} (x y : Vec p)
    (hx : finiteFrobeniusNorm x = 1) (hy : finiteFrobeniusNorm y = 1) :
    |dot x y| ≤ 1 := by
  have hsx : ∑ i, x i ^ 2 = 1 := by
    have h := congrArg (fun z : ℝ => z ^ 2) hx
    simpa [finiteFrobeniusNorm,
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)] using h
  have hsy : ∑ i, y i ^ 2 = 1 := by
    have h := congrArg (fun z : ℝ => z ^ 2) hy
    simpa [finiteFrobeniusNorm,
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)] using h
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin p)) x y
  rw [hsx, hsy, mul_one] at hcs
  apply (sq_le_sq₀ (abs_nonneg _) zero_le_one).mp
  simpa [dot, sq_abs] using hcs

/-- For positive dimensions and admissible positive margins, the contracted margin, lifted
condition envelope, pencil constant, local radius, trace constant, and factor constant are all
strictly positive. Under [the listed assumptions](hyp:hp,hn,hq,hsigma,hkappa,hkappaLambda), [the stated conclusion follows](goal). -/
-- Proof route: unfold the six constants in dependency order.  `Real.sqrt_pos.2` handles the
-- two dimension square roots; `pow_pos`, division positivity, and `min_pos` handle the remaining
-- arithmetic.  Derive `0 < Lambda` from `hkappa` and `hkappaLambda` before proving positivity of
-- `pencilPerturbationConstant`.
theorem localInverse_constants_pos {p n q : ℕ}
    (hp : 0 < p) (hn : 0 < n) (hq : 0 < q)
    {sigma kappa Lambda : ℝ} (hsigma : 0 < sigma)
    (hkappa : 0 < kappa) (hkappaLambda : kappa ≤ Lambda) :
    0 < contractedMargin q sigma kappa ∧
    0 < liftedConditionEnvelope n sigma ∧
    0 < pencilPerturbationConstant n (contractedMargin q sigma kappa) Lambda ∧
    0 < localInverseRadius n q sigma kappa Lambda ∧
    0 < traceRecoveryConstant n q sigma kappa Lambda ∧
    0 < factorRecoveryConstant p n q sigma kappa Lambda := by
  have hLambda : 0 < Lambda := lt_of_lt_of_le hkappa hkappaLambda
  have heta : 0 < contractedMargin q sigma kappa := by
    unfold contractedMargin
    exact mul_pos hkappa (pow_pos hsigma _)
  have hsqrtn : 0 < Real.sqrt n := Real.sqrt_pos.2 (Nat.cast_pos.2 hn)
  have hchi : 0 < liftedConditionEnvelope n sigma := by
    unfold liftedConditionEnvelope
    exact div_pos hsqrtn hsigma
  have hh : 0 < pencilPerturbationConstant n
      (contractedMargin q sigma kappa) Lambda := by
    unfold pencilPerturbationConstant
    positivity
  have hradius : 0 < localInverseRadius n q sigma kappa Lambda := by
    unfold localInverseRadius
    exact lt_min (div_pos heta (by norm_num))
      (div_pos hsigma (mul_pos (mul_pos (by norm_num) hchi) hh))
  have htrace : 0 < traceRecoveryConstant n q sigma kappa Lambda := by
    unfold traceRecoveryConstant
    positivity
  have hfactor : 0 < factorRecoveryConstant p n q sigma kappa Lambda := by
    unfold factorRecoveryConstant
    have hsqrtnp : 0 < Real.sqrt (n * p) :=
      Real.sqrt_pos.2 (mul_pos (Nat.cast_pos.2 hn) (Nat.cast_pos.2 hp))
    positivity
  exact ⟨heta, hchi, hh, hradius, htrace, hfactor⟩

/-- **Quantitative symmetric-tensor-pencil local inverse.** Given two finite factor matrices,
their coefficient vectors, two probes, the gap and coefficient margins,
positive ambient dimensions and degrees, an admissible singular-value margin,
positive and compatible coefficient bounds, unit probes,
unit factor columns, two-sided coefficient bounds, positive denominator
loadings, well-conditioned lifted directions, separated pencil ratios,
and a tensor perturbation below the explicit local radius, one column permutation makes
the factor-matrix Frobenius error at most the stated Lipschitz factor times the tensor Frobenius error. Under [the listed assumptions](hyp:hp,hn,hd,hq,hsigma,hkappa,hkappaLambda,hu,hv,hunit,hlam,hprobe,hlift,hgap,hclose), [the stated conclusion follows](goal). -/
-- Proof route: contract and compress using one orthonormal basis for the unprimed lifted range;
-- the denominator margin is `eta`, every coordinate pencil moves by at most `h*e`, and the
-- Riesz-projector theorem supplies one common permutation.  Trace coordinates then move by
-- `Lz*e`; positive probe orientation makes their normalization equal the original columns.
--
-- A convenient detailed assembly is as follows.
-- 1. Put `V = liftedDirections d C`, choose an orthonormal basis of `V.toEuclideanLin.range`
--    (use `stdOrthonormalBasis` on the range subtype and reindex using the finrank equality from
--    injectivity), and write its ambient coordinate columns as `U`.  Prove `OrthonormalColumns U`
--    and `SameColumnSpace U V`; put `S = U.transpose * V` and similarly `S'` for `C'`.
-- 2. Compress the `u` denominator contractions and coordinate numerator contractions by `U`.
--    The exact contraction identity identifies them with `S * diagonal * S.transpose` (and the
--    primed analogue).  Contraction plus `squareOperatorNorm_compress_le` bounds every difference
--    by the tensor error `e`.  The denominator theorem gives least singular value `eta`; inverse
--    perturbation makes the primed denominator invertible, and determinant multiplicativity then
--    makes `S'` invertible.
-- 3. Define the right pencils `G w` and `G' w`.  `rightPencil_eq_diagonalization` identifies them
--    with the loading-ratio diagonalizations.  For every standard basis probe,
--    `rightPencil_perturbation_bound` gives error `h*e`; the unprimed pencil norm is at most
--    `n*Lambda/eta` by numerator and inverse bounds.
-- 4. From `e < min (eta/2) (sigma/(6*chi*h))`, derive both smallness inequalities and apply
--    `exists_permutation_projector_matching` once.  Feed that common permutation and its
--    projector bounds into `traceCoordinates_perturbation_bound`; after
--    `finiteFrobeniusNorm_sub_le_sqrt_mul`, each trace vector has error at most
--    `sqrt p * traceRecoveryConstant ... * e`.
-- 5. Exact trace diagonalization says those vectors are the positively rescaled columns.
--    Cauchy--Schwarz and the unit hypotheses make their norms at least one.  Apply
--    `normalizeVec_sub_normalizeVec_le`, rewrite both normalizations with
--    `normalizeVec_inv_smul_eq`, and combine the column estimates using
--    `matrixFrobeniusNorm_le_sqrt_mul_of_columns`.  Finish with
--    `Real.sqrt_mul` on the nonnegative natural casts and the definition of
--    `factorRecoveryConstant`.
theorem exists_permutation_factorMatrix_frobeniusNorm_le
    {p n d q : ℕ} (C C' : FactorMatrix p n) (lam lam' : Fin n → ℝ)
    (u v : Vec p) (sigma kappa Lambda : ℝ)
    (hp : 0 < p) (hn : 0 < n) (hd : 0 < d) (hq : 0 < q)
    (hsigma : 0 < sigma ∧ sigma ≤ 1) (hkappa : 0 < kappa)
    (hkappaLambda : kappa ≤ Lambda)
    (hu : finiteFrobeniusNorm u = 1) (hv : finiteFrobeniusNorm v = 1)
    (hunit : (∀ j, finiteFrobeniusNorm (C.col j) = 1) ∧
      ∀ j, finiteFrobeniusNorm (C'.col j) = 1)
    (hlam : (∀ j, kappa ≤ |lam j| ∧ |lam j| ≤ Lambda) ∧
      ∀ j, kappa ≤ |lam' j| ∧ |lam' j| ≤ Lambda)
    (hprobe : (∀ j, sigma ≤ dot u (C.col j)) ∧
      ∀ j, sigma ≤ dot u (C'.col j))
    (hlift : sigma ≤ leastColumnSingularValue (liftedDirections d C) ∧
      sigma ≤ leastColumnSingularValue (liftedDirections d C'))
    (hgap : PairwiseGap (fun j => dot v (C.col j) / dot u (C.col j)) sigma ∧
      PairwiseGap (fun j => dot v (C'.col j) / dot u (C'.col j)) sigma)
    (hclose : finiteFrobeniusNorm
      (decompositionTensor (d + d + q) C' lam' -
        decompositionTensor (d + d + q) C lam) <
      localInverseRadius n q sigma kappa Lambda) :
    ∃ pi : Equiv.Perm (Fin n),
      matrixFrobeniusNorm (permuteColumns C' pi - C) ≤
        factorRecoveryConstant p n q sigma kappa Lambda *
          finiteFrobeniusNorm
            (decompositionTensor (d + d + q) C' lam' -
              decompositionTensor (d + d + q) C lam) := by
  classical
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let T := decompositionTensor (d + d + q) C lam
  let T' := decompositionTensor (d + d + q) C' lam'
  let e := finiteFrobeniusNorm (T' - T)
  let eta := contractedMargin q sigma kappa
  let chi := liftedConditionEnvelope n sigma
  let h := pencilPerturbationConstant n eta Lambda
  let Lz := traceRecoveryConstant n q sigma kappa Lambda
  have hLambda : 0 < Lambda := lt_of_lt_of_le hkappa hkappaLambda
  obtain ⟨heta, hchi, hh, hradius, hLz, _hfactor⟩ :=
    localInverse_constants_pos hp hn hq hsigma.1 hkappa hkappaLambda
  change 0 < eta at heta
  change 0 < chi at hchi
  change 0 < h at hh
  change 0 < Lz at hLz
  have he : 0 ≤ e := Real.sqrt_nonneg _
  have heRadius : e < localInverseRadius n q sigma kappa Lambda := hclose
  have heSmall : e < eta / 2 := by
    exact heRadius.trans_le (min_le_left _ _)
  have heProjector : 6 * chi * (h * e) < sigma := by
    have heSecond : e < sigma / (6 * chi * h) :=
      heRadius.trans_le (min_le_right _ _)
    have hden : 0 < 6 * chi * h := mul_pos (mul_pos (by norm_num) hchi) hh
    apply (lt_div_iff₀ hden).mp at heSecond
    nlinarith
  let V := liftedDirections d C
  let V' := liftedDirections d C'
  have hinjV : Function.Injective V.toEuclideanLin :=
    injective_of_pos_le_leastColumnSingularValue V hsigma.1 hlift.1
  obtain ⟨U, hUorth, hUspace⟩ :=
    exists_orthonormalColumns_sameColumnSpace V hinjV
  let S := U.transpose * V
  let S' := U.transpose * V'
  let Au := U.transpose * contractLast T (pencilProbes u u) * U
  let Au' := U.transpose * contractLast T' (pencilProbes u u) * U
  let Aw : Vec p → Matrix (Fin n) (Fin n) ℝ := fun w =>
    U.transpose * contractLast T (pencilProbes u w) * U
  let Aw' : Vec p → Matrix (Fin n) (Fin n) ℝ := fun w =>
    U.transpose * contractLast T' (pencilProbes u w) * U
  have hpencilProbes (w : Vec p) (hw : finiteFrobeniusNorm w = 1) :
      ∀ a : Fin q, finiteFrobeniusNorm (pencilProbes u w a) ≤ 1 := by
    intro a
    simp only [pencilProbes]
    split <;> simp_all
  have hcompressedPert (w : Vec p) (hw : finiteFrobeniusNorm w = 1) :
      squareOperatorNorm (Aw' w - Aw w) ≤ e := by
    have hcontract : contractLast T' (pencilProbes u w) -
        contractLast T (pencilProbes u w) =
          contractLast (T' - T) (pencilProbes u w) := by
      ext i j
      simp only [contractLast, Matrix.sub_apply, Pi.sub_apply]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro K _
      ring
    have hmatrix : Aw' w - Aw w =
        U.transpose * contractLast (T' - T) (pencilProbes u w) * U := by
      dsimp only [Aw, Aw']
      rw [← Matrix.sub_mul, ← Matrix.mul_sub, hcontract]
    rw [hmatrix]
    exact (squareOperatorNorm_compress_le U
      (contractLast (T' - T) (pencilProbes u w)) hUorth).trans
      (contractLast_operatorNorm_le (T' - T) (pencilProbes u w)
        (hpencilProbes w hw))
  have hAuPert : squareOperatorNorm (Au' - Au) ≤ e := by
    simpa only [Au, Au', Aw, Aw'] using hcompressedPert u hu
  have hAuFactor : Au = S * Matrix.diagonal
      (fun j => lam j * dot u (C.col j) ^ q) * S.transpose := by
    dsimp only [Au, T]
    rw [contractLast_decompositionTensor hq]
    have hdiag : Matrix.diagonal (fun j =>
        lam j * dot u (C.col j) ^ (q - 1) * dot u (C.col j)) =
        Matrix.diagonal (fun j => lam j * dot u (C.col j) ^ q) := by
      congr 1
      funext j
      rw [mul_assoc, pow_sub_one_mul (Nat.ne_of_gt hq)]
    rw [hdiag]
    simp only [S, V, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  have hAuFactor' : Au' = S' * Matrix.diagonal
      (fun j => lam' j * dot u (C'.col j) ^ q) * S'.transpose := by
    dsimp only [Au', T']
    rw [contractLast_decompositionTensor hq]
    have hdiag : Matrix.diagonal (fun j =>
        lam' j * dot u (C'.col j) ^ (q - 1) * dot u (C'.col j)) =
        Matrix.diagonal (fun j => lam' j * dot u (C'.col j) ^ q) := by
      congr 1
      funext j
      rw [mul_assoc, pow_sub_one_mul (Nat.ne_of_gt hq)]
    rw [hdiag]
    simp only [S', V', Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  have hAuSv : eta ≤ leastColumnSingularValue Au := by
    rw [hAuFactor]
    exact compressedDenominator_leastSingularValue C lam u U hq hsigma.1 hkappa
      hUorth hUspace hlift.1 (fun j => hlam.1 j |>.1) hprobe.1
  obtain ⟨hAuUnit, hAuInv⟩ := inverse_operatorNorm_le_reciprocal Au heta hAuSv
  obtain ⟨hAuUnit', hAuInv', hAuInvPert⟩ :=
    inverse_perturbation_bound Au Au' heta he hAuSv hAuPert heSmall
  have hSsv : sigma ≤ leastColumnSingularValue S :=
    compressedLift_leastSingularValue C U hsigma.1 hlift.1 hUorth hUspace
  obtain ⟨hS, _hSinv⟩ := inverse_operatorNorm_le_reciprocal S hsigma.1 hSsv
  have hS' : IsUnit S'.det := by
    apply isUnit_iff_ne_zero.mpr
    intro hzero
    have hdetzero : Au'.det = 0 := by
      rw [hAuFactor', Matrix.det_mul, Matrix.det_mul, hzero]
      simp
    exact (isUnit_iff_ne_zero.mp hAuUnit') hdetzero
  have hcondition : squareOperatorNorm S * squareOperatorNorm S⁻¹ ≤ chi := by
    exact compressedLift_condition_le C U hd hsigma.1 hunit.1 hlift.1 hUorth hUspace
  have hstandard (i : Fin p) : finiteFrobeniusNorm (standardBasis p i) = 1 := by
    unfold finiteFrobeniusNorm standardBasis
    simp
  have hAwNorm (i : Fin p) : squareOperatorNorm (Aw (standardBasis p i)) ≤
      n * Lambda := by
    exact compressedNumerator_operatorNorm_le C lam u (standardBasis p i) U hd hq
      hLambda.le hUorth hunit.1 hu (hstandard i) (fun j => hlam.1 j |>.2)
  let G : Vec p → Matrix (Fin n) (Fin n) ℝ := fun w => rightPencil (Aw w) Au
  let G' : Vec p → Matrix (Fin n) (Fin n) ℝ := fun w => rightPencil (Aw' w) Au'
  let values : Fin n → ℝ := fun j => dot v (C.col j) / dot u (C.col j)
  let values' : Fin n → ℝ := fun j => dot v (C'.col j) / dot u (C'.col j)
  have hprobePos (j : Fin n) : 0 < dot u (C.col j) :=
    hsigma.1.trans_le (hprobe.1 j)
  have hprobePos' (j : Fin n) : 0 < dot u (C'.col j) :=
    hsigma.1.trans_le (hprobe.2 j)
  have hload (j : Fin n) : lam j * dot u (C.col j) ^ q ≠ 0 :=
    mul_ne_zero (abs_pos.mp (lt_of_lt_of_le hkappa (hlam.1 j).1))
      (pow_ne_zero _ (hprobePos j).ne')
  have hload' (j : Fin n) : lam' j * dot u (C'.col j) ^ q ≠ 0 :=
    mul_ne_zero (abs_pos.mp (lt_of_lt_of_le hkappa (hlam.2 j).1))
      (pow_ne_zero _ (hprobePos' j).ne')
  have hAwFactor (w : Vec p) : Aw w = S * Matrix.diagonal (fun j =>
      lam j * (dot u (C.col j) ^ (q - 1) * dot w (C.col j))) * S.transpose := by
    dsimp only [Aw, T]
    rw [contractLast_decompositionTensor hq]
    have hdiag : Matrix.diagonal (fun j =>
        lam j * dot u (C.col j) ^ (q - 1) * dot w (C.col j)) =
        Matrix.diagonal (fun j =>
          lam j * (dot u (C.col j) ^ (q - 1) * dot w (C.col j))) := by
      congr 1
      funext j
      ring
    rw [hdiag]
    simp only [S, V, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  have hAwFactor' (w : Vec p) : Aw' w = S' * Matrix.diagonal (fun j =>
      lam' j * (dot u (C'.col j) ^ (q - 1) * dot w (C'.col j))) * S'.transpose := by
    dsimp only [Aw', T']
    rw [contractLast_decompositionTensor hq]
    have hdiag : Matrix.diagonal (fun j =>
        lam' j * dot u (C'.col j) ^ (q - 1) * dot w (C'.col j)) =
        Matrix.diagonal (fun j =>
          lam' j * (dot u (C'.col j) ^ (q - 1) * dot w (C'.col j))) := by
      congr 1
      funext j
      ring
    rw [hdiag]
    simp only [S', V', Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  have hGdiag (w : Vec p) : G w = diagonalizableMatrix S
      (fun j => dot w (C.col j) / dot u (C.col j)) := by
    dsimp only [G]
    rw [hAwFactor, hAuFactor]
    rw [rightPencil_eq_diagonalization S lam
      (fun j => dot u (C.col j) ^ q)
      (fun j => dot u (C.col j) ^ (q - 1) * dot w (C.col j)) hS hload]
    have hratio : (fun j => dot u (C.col j) ^ (q - 1) * dot w (C.col j) /
        dot u (C.col j) ^ q) =
        (fun j => dot w (C.col j) / dot u (C.col j)) := by
      funext j
      field_simp [(hprobePos j).ne']
      calc
        _ = (dot u (C.col j) ^ (q - 1) * dot u (C.col j)) *
            dot w (C.col j) := by ring
        _ = dot u (C.col j) ^ q * dot w (C.col j) := by
          rw [pow_sub_one_mul (Nat.ne_of_gt hq)]
        _ = _ := by ring
    rw [hratio]
    rfl
  have hGdiag' (w : Vec p) : G' w = diagonalizableMatrix S'
      (fun j => dot w (C'.col j) / dot u (C'.col j)) := by
    dsimp only [G']
    rw [hAwFactor', hAuFactor']
    rw [rightPencil_eq_diagonalization S' lam'
      (fun j => dot u (C'.col j) ^ q)
      (fun j => dot u (C'.col j) ^ (q - 1) * dot w (C'.col j)) hS' hload']
    have hratio : (fun j => dot u (C'.col j) ^ (q - 1) * dot w (C'.col j) /
        dot u (C'.col j) ^ q) =
        (fun j => dot w (C'.col j) / dot u (C'.col j)) := by
      funext j
      field_simp [(hprobePos' j).ne']
      calc
        _ = (dot u (C'.col j) ^ (q - 1) * dot u (C'.col j)) *
            dot w (C'.col j) := by ring
        _ = dot u (C'.col j) ^ q * dot w (C'.col j) := by
          rw [pow_sub_one_mul (Nat.ne_of_gt hq)]
        _ = _ := by ring
    rw [hratio]
    rfl
  have hGpencil (i : Fin p) : squareOperatorNorm
      (G' (standardBasis p i) - G (standardBasis p i)) ≤ h * e := by
    exact (rightPencil_perturbation_bound
      (Aw (standardBasis p i)) Au (Aw' (standardBasis p i)) Au'
      heta hLambda.le he hAuSv (hAwNorm i)
      (hcompressedPert (standardBasis p i) (hstandard i)) hAuPert heSmall).2.2
  have hGv : squareOperatorNorm (G' v - G v) ≤ h * e := by
    exact (rightPencil_perturbation_bound (Aw v) Au (Aw' v) Au'
      heta hLambda.le he hAuSv
      (compressedNumerator_operatorNorm_le C lam u v U hd hq hLambda.le hUorth
        hunit.1 hu hv (fun j => hlam.1 j |>.2))
      (hcompressedPert v hv) hAuPert heSmall).2.2
  obtain ⟨pi, hpi⟩ := exists_permutation_projector_matching S S' values values'
    hS hS' hsigma.1 hchi (mul_nonneg hh.le he) hgap.1 hgap.2 hcondition
    (by simpa [values, values', hGdiag, hGdiag'] using hGv) heProjector
  let P : Fin n → Matrix (Fin n) (Fin n) ℝ := coordinateProjector S
  let P' : Fin n → Matrix (Fin n) (Fin n) ℝ :=
    fun j => coordinateProjector S' (pi j)
  have hprojector (j : Fin n) : squareOperatorNorm (P' j - P j) ≤
      6 * chi ^ 2 * (h * e) / sigma := by
    exact (hpi j).2.1
  have hprojectorNorm (j : Fin n) : squareOperatorNorm (P' j) ≤ 2 * chi := by
    exact (hpi j).2.2.2
  have hGpencilNorm (i : Fin p) : squareOperatorNorm (G (standardBasis p i)) ≤
      n * Lambda / eta := by
    change squareOperatorNorm
      (Aw (standardBasis p i) * Au⁻¹) ≤ n * Lambda / eta
    change ‖Aw (standardBasis p i) * Au⁻¹‖ ≤ n * Lambda / eta
    calc
      _ ≤ ‖Aw (standardBasis p i)‖ * ‖Au⁻¹‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (n * Lambda) * eta⁻¹ :=
        mul_le_mul (hAwNorm i) hAuInv (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hLambda.le)
      _ = n * Lambda / eta := by rw [div_eq_mul_inv]
  let z : Fin n → Vec p := traceCoordinates G P
  let z' : Fin n → Vec p := traceCoordinates G' P'
  have htraceCoord (i : Fin p) (j : Fin n) :
      |z' j i - z j i| ≤ Lz * e := by
    have ht := traceCoordinates_perturbation_bound G G' P P'
      (pencilError := h * e)
      (projectorError := 6 * chi ^ 2 * (h * e) / sigma)
      (projectorNorm := 2 * chi) (pencilNorm := n * Lambda / eta)
      hGpencil hprojector hprojectorNorm hGpencilNorm i j
    calc
      |z' j i - z j i| ≤ n * ((h * e) * (2 * chi) +
          (n * Lambda / eta) * (6 * chi ^ 2 * (h * e) / sigma)) := ht
      _ = Lz * e := by
        dsimp only [Lz, traceRecoveryConstant, h, chi, eta]
        field_simp [hsigma.1.ne',
          (show contractedMargin q sigma kappa ≠ 0 from
            (localInverse_constants_pos hp hn hq hsigma.1 hkappa hkappaLambda).1.ne')]
  have hzError (j : Fin n) : finiteFrobeniusNorm (z' j - z j) ≤
      Real.sqrt p * (Lz * e) := by
    exact finiteFrobeniusNorm_sub_le_sqrt_mul (z' j) (z j)
      (mul_nonneg hLz.le he) (fun i => htraceCoord i j)
  have hGall : G = fun w => diagonalizableMatrix S
      (fun j => dot w (C.col j) / dot u (C.col j)) := funext hGdiag
  have hGall' : G' = fun w => diagonalizableMatrix S'
      (fun j => dot w (C'.col j) / dot u (C'.col j)) := funext hGdiag'
  have hz (j : Fin n) : z j = (dot u (C.col j))⁻¹ • C.col j := by
    have hall := traceCoordinates_diagonalization C u S hS
      (fun k => (hprobePos k).ne')
    simpa only [z, P, hGall] using congrFun hall j
  have hz' (j : Fin n) : z' j =
      (dot u (C'.col (pi j)))⁻¹ • C'.col (pi j) := by
    have hall := traceCoordinates_diagonalization C' u S' hS'
      (fun k => (hprobePos' k).ne')
    change traceCoordinates G' (coordinateProjector S') (pi j) = _
    rw [hGall']
    exact congrFun hall (pi j)
  have hzNorm (j : Fin n) : 1 ≤ finiteFrobeniusNorm (z j) := by
    rw [hz, finiteFrobeniusNorm_smul_eq_abs, hunit.1 j, mul_one,
      abs_of_pos (inv_pos.mpr (hprobePos j))]
    apply (one_le_inv₀ (hprobePos j)).2
    simpa [abs_of_pos (hprobePos j)] using abs_dot_le_one_of_unit u (C.col j) hu (hunit.1 j)
  have hzNorm' (j : Fin n) : 1 ≤ finiteFrobeniusNorm (z' j) := by
    rw [hz', finiteFrobeniusNorm_smul_eq_abs, hunit.2 (pi j), mul_one,
      abs_of_pos (inv_pos.mpr (hprobePos' (pi j)))]
    apply (one_le_inv₀ (hprobePos' (pi j))).2
    simpa [abs_of_pos (hprobePos' (pi j))] using
      abs_dot_le_one_of_unit u (C'.col (pi j)) hu (hunit.2 (pi j))
  have hnormalize (j : Fin n) : finiteFrobeniusNorm
      (normalizeVec (z' j) - normalizeVec (z j)) ≤
        2 * Real.sqrt p * Lz * e := by
    have hzpos : 0 < finiteFrobeniusNorm (z j) := zero_lt_one.trans_le (hzNorm j)
    have hzpos' : 0 < finiteFrobeniusNorm (z' j) := zero_lt_one.trans_le (hzNorm' j)
    have hmin : 1 ≤ min (finiteFrobeniusNorm (z' j))
        (finiteFrobeniusNorm (z j)) := le_min (hzNorm' j) (hzNorm j)
    have hminpos : 0 < min (finiteFrobeniusNorm (z' j))
        (finiteFrobeniusNorm (z j)) := zero_lt_one.trans_le hmin
    have hnorm := normalizeVec_sub_normalizeVec_le (z' j) (z j) hzpos' hzpos
    calc
      finiteFrobeniusNorm (normalizeVec (z' j) - normalizeVec (z j)) ≤
          2 * finiteFrobeniusNorm (z' j - z j) /
            min (finiteFrobeniusNorm (z' j)) (finiteFrobeniusNorm (z j)) := hnorm
      _ ≤ 2 * finiteFrobeniusNorm (z' j - z j) := by
        apply (div_le_iff₀ hminpos).2
        nlinarith [show 0 ≤ finiteFrobeniusNorm (z' j - z j) from Real.sqrt_nonneg _]
      _ ≤ 2 * (Real.sqrt p * (Lz * e)) := by
        gcongr
        exact hzError j
      _ = 2 * Real.sqrt p * Lz * e := by ring
  have hnormExact (j : Fin n) : normalizeVec (z j) = C.col j := by
    rw [hz]
    exact normalizeVec_inv_smul_eq (C.col j) (dot u (C.col j))
      (hunit.1 j) (hprobePos j)
  have hnormExact' (j : Fin n) : normalizeVec (z' j) = C'.col (pi j) := by
    rw [hz']
    exact normalizeVec_inv_smul_eq (C'.col (pi j)) (dot u (C'.col (pi j)))
      (hunit.2 (pi j)) (hprobePos' (pi j))
  refine ⟨pi, ?_⟩
  have hcolumns (j : Fin n) : finiteFrobeniusNorm
      ((permuteColumns C' pi).col j - C.col j) ≤
        2 * Real.sqrt p * Lz * e := by
    change finiteFrobeniusNorm (C'.col (pi j) - C.col j) ≤ _
    rw [← hnormExact' j, ← hnormExact j]
    exact hnormalize j
  calc
    matrixFrobeniusNorm (permuteColumns C' pi - C) ≤
        Real.sqrt n * (2 * Real.sqrt p * Lz * e) :=
      matrixFrobeniusNorm_le_sqrt_mul_of_columns _ _
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hLz.le) he)
        hcolumns
    _ = factorRecoveryConstant p n q sigma kappa Lambda * e := by
      rw [factorRecoveryConstant]
      have hsqrt : Real.sqrt (n * p) = Real.sqrt n * Real.sqrt p := by
        rw [show (n * p : ℝ) = (n : ℝ) * (p : ℝ) by norm_num,
          Real.sqrt_mul (Nat.cast_nonneg n)]
      rw [hsqrt]
      change Real.sqrt n * (2 * Real.sqrt p * Lz * e) =
        (2 * (Real.sqrt n * Real.sqrt p) * Lz) * e
      ring
    _ = factorRecoveryConstant p n q sigma kappa Lambda *
        finiteFrobeniusNorm
          (decompositionTensor (d + d + q) C' lam' -
            decompositionTensor (d + d + q) C lam) := by rfl

end Causalean.Mathlib.Analysis.SymmetricTensorPencil
