import Causalean.Mathlib.Analysis.SymmetricTensorPencil.Basic

/-!
# Conditioning of compressed lifted factors

This module records how an orthonormal basis of the lifted column space preserves the signal
singular values.  It then derives explicit lower and upper bounds for the contracted matrices
which form the denominator and numerators of a tensor pencil.
-/

namespace Causalean.Mathlib.Analysis.SymmetricTensorPencil

open scoped BigOperators

/-- A finite matrix has orthonormal columns when its transpose times itself is the identity. With [its explicit inputs](hyp:U), [the defined object](goal) is [given by the displayed formula](step:1). -/
def OrthonormalColumns {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (U : Matrix ι κ ℝ) : Prop :=
  U.transpose * U = 1

/-- Two finite matrices have the same column space when their associated Euclidean linear maps
have equal ranges. With [its explicit inputs](hyp:U,V), [the defined object](goal) is [given by the displayed formula](step:1). -/
def SameColumnSpace {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (U V : Matrix ι κ ℝ) : Prop :=
  U.toEuclideanLin.range = V.toEuclideanLin.range

private noncomputable def orthonormalColumnsLinearIsometry {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (U : Matrix ι κ ℝ) (horth : OrthonormalColumns U) :
    EuclideanSpace ℝ κ →ₗᵢ[ℝ] EuclideanSpace ℝ ι := by
  refine LinearIsometry.mk U.toEuclideanLin ?_
  intro x
  have hadj : U.toEuclideanLin.adjoint = U.transpose.toEuclideanLin := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    congr 1
  have hleft : U.toEuclideanLin.adjoint (U.toEuclideanLin x) = x := by
    rw [hadj]
    apply PiLp.ext
    intro i
    simp only [Matrix.toEuclideanLin_apply, WithLp.ofLp_toLp, Matrix.mulVec_mulVec,
      ← Matrix.mul_apply]
    rw [horth]
    simp
  have hsq : ‖U.toEuclideanLin x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      ← U.toEuclideanLin.adjoint_inner_left, hleft]
  nlinarith [norm_nonneg x, norm_nonneg (U.toEuclideanLin x)]

private theorem orthonormalColumns_l2OpNorm_le_one {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (U : Matrix ι κ ℝ) (horth : OrthonormalColumns U) :
    @norm (Matrix ι κ ℝ) Matrix.instL2OpNormedAddCommGroup.toNorm U ≤ 1 := by
  open scoped Matrix.Norms.L2Operator in
    rw [Matrix.l2_opNorm_def]
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    have hx := (orthonormalColumnsLinearIsometry U horth).norm_map x
    change ‖U.toEuclideanLin x‖ = ‖x‖ at hx
    change ‖U.toEuclideanLin x‖ ≤ 1 * ‖x‖
    rw [hx, one_mul]

private theorem rectangularOperatorNorm_le_matrixFrobenius {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq κ] (A : Matrix ι κ ℝ) :
    @norm (Matrix ι κ ℝ) Matrix.instL2OpNormedAddCommGroup.toNorm A ≤
      matrixFrobeniusNorm A := by
  open scoped Matrix.Norms.L2Operator in
    rw [Matrix.l2_opNorm_def]
    calc
      _ ≤ @norm (Matrix ι κ ℝ) Matrix.frobeniusNormedAddCommGroup.toNorm A := by
        open scoped Matrix.Norms.Frobenius in
          refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A) fun x => ?_
          have hmul := Matrix.frobenius_norm_mul A
            (Matrix.replicateCol Unit (WithLp.ofLp x))
          have heq :
              A * Matrix.replicateCol Unit (WithLp.ofLp x) =
                Matrix.replicateCol Unit (Matrix.mulVec A (WithLp.ofLp x)) := by
            ext i u
            simp [Matrix.mul_apply, Matrix.mulVec, Matrix.replicateCol, dotProduct]
          rw [heq, Matrix.frobenius_norm_replicateCol] at hmul
          change ‖WithLp.toLp 2 (A.mulVec x.ofLp)‖ ≤
            @norm (Matrix ι κ ℝ) Matrix.frobeniusNormedAddCommGroup.toNorm A * ‖x‖
          simpa using hmul
      _ = matrixFrobeniusNorm A := by
        rw [Matrix.frobenius_norm_def, matrixFrobeniusNorm, finiteFrobeniusNorm,
          Real.sqrt_eq_rpow, Fintype.sum_prod_type]
        simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs]

/-- Compressing a full-column-rank matrix in an orthonormal basis of its column space preserves
its least column singular value. Under [the listed assumptions](hyp:horth,hspace,hinj), [the stated conclusion follows](goal). -/
-- Proof route: turn `U` into a `LinearIsometry` using `UᵀU = I`, rewrite the transpose product
-- as composition with that isometry, and apply
-- `singularValues_comp_linearIsometry_last` to the adjoint/range equality induced by `hspace`.
theorem leastColumnSingularValue_transpose_mul_eq {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] [Nonempty κ]
    (U V : Matrix ι κ ℝ) (horth : OrthonormalColumns U)
    (hspace : SameColumnSpace U V) (hinj : Function.Injective V.toEuclideanLin) :
    leastColumnSingularValue (U.transpose * V) = leastColumnSingularValue V := by
  let W := orthonormalColumnsLinearIsometry U horth
  let S := (U.transpose * V).toEuclideanLin
  let M := V.toEuclideanLin
  have hS : S = W.toLinearMap.adjoint ∘ₗ M := by
    apply LinearMap.ext
    intro x
    apply PiLp.ext
    intro i
    simp [S, M, W, orthonormalColumnsLinearIsometry,
      Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec,
      ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  have hfactor (x : EuclideanSpace ℝ κ) : W (S x) = M x := by
    have hx : M x ∈ W.toLinearMap.range := by
      change V.toEuclideanLin x ∈ U.toEuclideanLin.range
      rw [hspace]
      exact LinearMap.mem_range_self V.toEuclideanLin x
    rcases hx with ⟨z, hz⟩
    rw [hS, LinearMap.comp_apply, ← hz]
    have hleft := W.adjoint_comp_self
    have hleft_apply := congrArg (fun f => f z) hleft
    change W (W.toLinearMap.adjoint (W z)) = W z
    congr 1
  have hgram : S.adjoint ∘ₗ S = M.adjoint ∘ₗ M := by
    apply LinearMap.ext
    intro x
    apply ext_inner_right ℝ
    intro y
    rw [LinearMap.comp_apply, LinearMap.comp_apply,
      S.adjoint_inner_left, M.adjoint_inner_left]
    rw [← W.inner_map_map (S x) (S y), hfactor x, hfactor y]
  have hsv : S.singularValues = M.singularValues := by
    simp only [LinearMap.singularValues, hgram]
  change S.singularValues (Fintype.card κ - 1) =
    M.singularValues (Fintype.card κ - 1)
  exact DFunLike.congr_fun hsv (Fintype.card κ - 1)

/-- An orthonormal compression cannot increase the Euclidean operator norm of a square matrix. Under [the listed assumptions](hyp:horth), [the stated conclusion follows](goal). -/
-- Proof route: interpret the product as the composition `U† ∘ A ∘ U`.  Derive
-- `‖U x‖ = ‖x‖` directly from `UᵀU = I`; use it for `‖U‖ ≤ 1`, and use Cauchy--Schwarz
-- plus the same identity for the restricted adjoint estimate needed by the compression.
theorem squareOperatorNorm_compress_le {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (U : Matrix ι κ ℝ) (A : Matrix ι ι ℝ) (horth : OrthonormalColumns U) :
    squareOperatorNorm (U.transpose * A * U) ≤ squareOperatorNorm A := by
  open scoped Matrix.Norms.L2Operator in
    change ‖U.transpose * A * U‖ ≤ ‖A‖
    have hU := orthonormalColumns_l2OpNorm_le_one U horth
    have hUt : ‖U.transpose‖ ≤ 1 := by
      rw [show U.transpose = U.conjTranspose by ext i j; simp,
        Matrix.l2_opNorm_conjTranspose]
      exact hU
    calc
      ‖U.transpose * A * U‖ ≤ ‖U.transpose * A‖ * ‖U‖ :=
        Matrix.l2_opNorm_mul _ _
      _ ≤ (‖U.transpose‖ * ‖A‖) * ‖U‖ := by
        gcongr
        exact Matrix.l2_opNorm_mul _ _
      _ ≤ (1 * ‖A‖) * 1 := by gcongr
      _ = ‖A‖ := by ring

/-- A positive lower bound for the last column singular value implies full column rank. Under [the listed assumptions](hyp:hsigma,hsv), [the stated conclusion follows](goal). -/
-- Proof route: positivity rules out
-- `singularValues_eq_zero_iff_le_finrank_range` at the last domain index.  Hence the range has
-- full domain finrank, so rank--nullity makes the kernel trivial.  (The existing expansion lemma
-- itself assumes injectivity, so it cannot be used contrapositively here.)
theorem injective_of_pos_le_leastColumnSingularValue {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (A : Matrix ι κ ℝ) {sigma : ℝ} (hsigma : 0 < sigma)
    (hsv : sigma ≤ leastColumnSingularValue A) :
    Function.Injective A.toEuclideanLin := by
  let T := A.toEuclideanLin
  have hpos : 0 < T.singularValues (Fintype.card κ - 1) :=
    lt_of_lt_of_le hsigma hsv
  have hrank_not : ¬ Module.finrank ℝ T.range ≤ Fintype.card κ - 1 := by
    intro hrank
    have hz := T.singularValues_eq_zero_iff_le_finrank_range.mpr hrank
    rw [hz] at hpos
    exact lt_irrefl 0 hpos
  have hcard_le : Fintype.card κ ≤ Module.finrank ℝ T.range := by omega
  have hrank_le : Module.finrank ℝ T.range ≤ Fintype.card κ := by
    simpa [T, finrank_euclideanSpace] using T.finrank_range_le
  have hker : Module.finrank ℝ T.ker = 0 := by
    have hrank_null : Module.finrank ℝ T.range + Module.finrank ℝ T.ker =
        Fintype.card κ := by
      simpa [finrank_euclideanSpace] using T.finrank_range_add_finrank_ker
    omega
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.finrank_eq_zero.mp hker

private theorem squareInverse_operatorNorm_le_reciprocal {κ : Type*}
    [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (A : Matrix κ κ ℝ) {sigma : ℝ} (hsigma : 0 < sigma)
    (hsv : sigma ≤ leastColumnSingularValue A) :
    squareOperatorNorm A⁻¹ ≤ sigma⁻¹ := by
  have hinj := injective_of_pos_le_leastColumnSingularValue A hsigma hsv
  have hmulVec : Function.Injective A.mulVec := by
    intro x y hxy
    have hlp : A.toEuclideanLin (WithLp.toLp 2 x) =
        A.toEuclideanLin (WithLp.toLp 2 y) := by
      simpa [Matrix.toEuclideanLin_apply] using congrArg (WithLp.toLp 2) hxy
    have := hinj hlp
    simpa using congrArg WithLp.ofLp this
  have hunitA : IsUnit A := Matrix.mulVec_injective_iff_isUnit.mp hmulVec
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hunitA
  rw [squareOperatorNorm]
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hsigma.le)
  intro x
  let e := (Matrix.toEuclideanCLM (n := κ) (𝕜 := ℝ))
  have hcancel : e A (e A⁻¹ x) = x := by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, Matrix.mul_nonsing_inv A hdet,
      map_one, ContinuousLinearMap.one_apply]
  have hleast := Causalean.Mathlib.Analysis.least_singularValue_mul_norm_le
    A.toEuclideanLin hinj (e A⁻¹ x)
  have hsigma_mul : sigma * ‖e A⁻¹ x‖ ≤ ‖x‖ := by
    calc
      sigma * ‖e A⁻¹ x‖ ≤ leastColumnSingularValue A * ‖e A⁻¹ x‖ :=
        mul_le_mul_of_nonneg_right hsv (norm_nonneg _)
      _ ≤ ‖A.toEuclideanLin (e A⁻¹ x)‖ := by
        simpa [leastColumnSingularValue, finrank_euclideanSpace] using hleast
      _ = ‖x‖ := by
        change ‖e A (e A⁻¹ x)‖ = ‖x‖
        rw [hcancel]
  rw [inv_mul_eq_div]
  exact (le_div_iff₀ hsigma).2 (by simpa [mul_comm] using hsigma_mul)

/-- If a lifted factor has least singular value at least `sigma`, then its coordinates in any
orthonormal basis of its column space have the same lower singular-value bound. Under [the listed assumptions](hyp:hsigma,hlift,horth,hspace), [the stated conclusion follows](goal). -/
theorem compressedLift_leastSingularValue {p n d : ℕ} [NeZero n]
    (C : FactorMatrix p n) (U : Matrix (LiftIndex p d) (Fin n) ℝ)
    {sigma : ℝ} (hsigma : 0 < sigma)
    (hlift : sigma ≤ leastColumnSingularValue (liftedDirections d C))
    (horth : OrthonormalColumns U)
    (hspace : SameColumnSpace U (liftedDirections d C)) :
    sigma ≤ leastColumnSingularValue (U.transpose * liftedDirections d C) := by
  have hinj := injective_of_pos_le_leastColumnSingularValue
    (liftedDirections d C) hsigma hlift
  rw [leastColumnSingularValue_transpose_mul_eq U (liftedDirections d C)
    horth hspace hinj]
  exact hlift

/-- The square coordinate matrix of a degree lift with unit columns has operator norm at most
the square root of the number of factor columns. Under [the listed assumptions](hyp:hd,horth,hunit), [the stated conclusion follows](goal). -/
theorem compressedLift_operatorNorm_le_sqrt {p n d : ℕ}
    (C : FactorMatrix p n) (U : Matrix (LiftIndex p d) (Fin n) ℝ)
    (hd : 0 < d) (horth : OrthonormalColumns U)
    (hunit : ∀ j, finiteFrobeniusNorm (C.col j) = 1) :
    squareOperatorNorm (U.transpose * liftedDirections d C) ≤ Real.sqrt n := by
  open scoped Matrix.Norms.L2Operator in
    change ‖U.transpose * liftedDirections d C‖ ≤ Real.sqrt n
    have hU := orthonormalColumns_l2OpNorm_le_one U horth
    have hUt : ‖U.transpose‖ ≤ 1 := by
      rw [show U.transpose = U.conjTranspose by ext i j; simp,
        Matrix.l2_opNorm_conjTranspose]
      exact hU
    have hV : ‖liftedDirections d C‖ ≤ Real.sqrt n :=
      (rectangularOperatorNorm_le_matrixFrobenius (liftedDirections d C)).trans_eq
        (matrixFrobeniusNorm_liftedDirections hd C hunit)
    calc
      ‖U.transpose * liftedDirections d C‖ ≤
          ‖U.transpose‖ * ‖liftedDirections d C‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ 1 * Real.sqrt n := mul_le_mul hUt hV (norm_nonneg _) zero_le_one
      _ = Real.sqrt n := one_mul _

/-- The inverse of the square coordinate matrix of a well-conditioned degree lift has operator
norm at most the reciprocal of the lifted least-singular-value margin. Under [the listed assumptions](hyp:hsigma,hlift,horth,hspace), [the stated conclusion follows](goal). -/
theorem compressedLift_inverse_operatorNorm_le {p n d : ℕ} [NeZero n]
    (C : FactorMatrix p n) (U : Matrix (LiftIndex p d) (Fin n) ℝ)
    {sigma : ℝ} (hsigma : 0 < sigma)
    (hlift : sigma ≤ leastColumnSingularValue (liftedDirections d C))
    (horth : OrthonormalColumns U)
    (hspace : SameColumnSpace U (liftedDirections d C)) :
    squareOperatorNorm (U.transpose * liftedDirections d C)⁻¹ ≤ sigma⁻¹ := by
  apply squareInverse_operatorNorm_le_reciprocal _ hsigma
  exact compressedLift_leastSingularValue C U hsigma hlift horth hspace

/-- A degree lift with unit columns and least singular value at least `sigma` has compressed
diagonalizer condition number at most `sqrt n / sigma`. Under [the listed assumptions](hyp:hd,hsigma,hunit,hlift,horth,hspace), [the stated conclusion follows](goal). -/
theorem compressedLift_condition_le {p n d : ℕ} [NeZero n]
    (C : FactorMatrix p n) (U : Matrix (LiftIndex p d) (Fin n) ℝ)
    {sigma : ℝ} (hd : 0 < d) (hsigma : 0 < sigma)
    (hunit : ∀ j, finiteFrobeniusNorm (C.col j) = 1)
    (hlift : sigma ≤ leastColumnSingularValue (liftedDirections d C))
    (horth : OrthonormalColumns U)
    (hspace : SameColumnSpace U (liftedDirections d C)) :
    squareOperatorNorm (U.transpose * liftedDirections d C) *
    squareOperatorNorm (U.transpose * liftedDirections d C)⁻¹ ≤
      Real.sqrt n / sigma := by
  have hop := compressedLift_operatorNorm_le_sqrt C U hd horth hunit
  have hinv := compressedLift_inverse_operatorNorm_le C U hsigma hlift horth hspace
  calc
    squareOperatorNorm (U.transpose * liftedDirections d C) *
          squareOperatorNorm (U.transpose * liftedDirections d C)⁻¹ ≤
        Real.sqrt n * sigma⁻¹ :=
      mul_le_mul hop hinv (norm_nonneg _) (Real.sqrt_nonneg _)
    _ = Real.sqrt n / sigma := by rw [div_eq_mul_inv]

/-- Given a factor matrix, its coefficients, a denominator probe,
orthonormal lifted coordinates, positive degree and margins,
a lifted singular-value margin, coefficient lower bounds, and
probe-loading lower bounds, the compressed denominator contraction has least singular
value at least the assembled margin. Under [the listed assumptions](hyp:hq,hsigma,hkappa,horth,hspace,hlift,hlam,hprobe), [the stated conclusion follows](goal). -/
-- Proof route: use `Matrix.singularValues_mul_mul_transpose_lower_bound`; the diagonal core
-- expands by `kappa * sigma^q`, while each compressed lifted factor expands by `sigma`.
theorem compressedDenominator_leastSingularValue {p n d q : ℕ} [NeZero n]
    (C : FactorMatrix p n) (lam : Fin n → ℝ) (u : Vec p)
    (U : Matrix (LiftIndex p d) (Fin n) ℝ) {sigma kappa : ℝ}
    (hq : 0 < q) (hsigma : 0 < sigma) (hkappa : 0 < kappa)
    (horth : OrthonormalColumns U)
    (hspace : SameColumnSpace U (liftedDirections d C))
    (hlift : sigma ≤ leastColumnSingularValue (liftedDirections d C))
    (hlam : ∀ j, kappa ≤ |lam j|)
    (hprobe : ∀ j, sigma ≤ dot u (C.col j)) :
    kappa * sigma ^ (q + 2) ≤ leastColumnSingularValue
      ((U.transpose * liftedDirections d C) *
        Matrix.diagonal (fun j => lam j * dot u (C.col j) ^ q) *
        (U.transpose * liftedDirections d C).transpose) := by
  let S := U.transpose * liftedDirections d C
  let D := Matrix.diagonal (fun j => lam j * dot u (C.col j) ^ q)
  have hSsv : sigma ≤ leastColumnSingularValue S :=
    compressedLift_leastSingularValue C U hsigma hlift horth hspace
  have hSinj : Function.Injective S.toEuclideanLin :=
    injective_of_pos_le_leastColumnSingularValue S hsigma hSsv
  have hload (j : Fin n) : kappa * sigma ^ q ≤
      |lam j * dot u (C.col j) ^ q| := by
    have huj : 0 < dot u (C.col j) := hsigma.trans_le (hprobe j)
    rw [abs_mul, abs_pow, abs_of_pos huj]
    exact mul_le_mul (hlam j) (pow_le_pow_left₀ hsigma.le (hprobe j) q)
      (pow_nonneg hsigma.le q) (abs_nonneg _)
  have hDinj : Function.Injective D.toEuclideanLin := by
    intro x y hxy
    apply PiLp.ext
    intro j
    have hj := congrArg
      (fun z : EuclideanSpace ℝ (Fin n) => WithLp.ofLp z j) hxy
    simp only [D, Matrix.toEuclideanLin_apply, WithLp.ofLp_toLp,
      Matrix.mulVec_diagonal] at hj
    have hne : lam j * dot u (C.col j) ^ q ≠ 0 := by
      intro hz
      have := hload j
      rw [hz, abs_zero] at this
      have hcpos : 0 < kappa * sigma ^ q :=
        mul_pos hkappa (pow_pos hsigma q)
      linarith
    exact mul_left_cancel₀ hne hj
  have hDsv : kappa * sigma ^ q ≤ leastColumnSingularValue D := by
    apply Causalean.Mathlib.Analysis.le_singularValues_of_subspace
      D.toEuclideanLin ⊤
    · exact mul_nonneg hkappa.le (pow_nonneg hsigma.le q)
    · simp only [finrank_euclideanSpace, finrank_top]
      exact Nat.sub_lt (Fintype.card_pos) (by omega)
    · intro x _hx
      apply (sq_le_sq₀
        (mul_nonneg (mul_nonneg hkappa.le (pow_nonneg hsigma.le q)) (norm_nonneg x))
        (norm_nonneg (D.toEuclideanLin x))).mp
      rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
        Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      simp only [D, Matrix.toEuclideanLin_apply, WithLp.ofLp_toLp,
        Matrix.mulVec_diagonal, Real.norm_eq_abs, PiLp.inner_apply,
        RCLike.inner_apply, conj_trivial, mul_pow]
      rw [abs_mul, mul_pow]
      convert mul_le_mul_of_nonneg_right
        ((sq_le_sq₀ (mul_nonneg hkappa.le (pow_nonneg hsigma.le q))
          (abs_nonneg _)).2 (hload j)) (sq_nonneg (WithLp.ofLp x j)) using 1 <;>
        simp only [sq_abs] <;> ring
  have hprod := Causalean.Mathlib.Analysis.Matrix.singularValues_mul_mul_transpose_lower_bound
    S D S hSinj hDinj hSinj
  have hS0 := S.toEuclideanLin.singularValues_nonneg (Fintype.card (Fin n) - 1)
  have hD0 := D.toEuclideanLin.singularValues_nonneg (Fintype.card (Fin n) - 1)
  calc
    kappa * sigma ^ (q + 2) = sigma * (kappa * sigma ^ q) * sigma := by
      rw [pow_add]
      ring
    _ ≤ leastColumnSingularValue S * leastColumnSingularValue D *
          leastColumnSingularValue S := by
      exact mul_le_mul
        (mul_le_mul hSsv hDsv (mul_nonneg hkappa.le (pow_nonneg hsigma.le q)) hS0)
        hSsv hsigma.le (mul_nonneg hS0 hD0)
    _ ≤ leastColumnSingularValue (S * D * S.transpose) := by
      simpa [leastColumnSingularValue] using hprod

/-- Every compressed numerator contraction has operator norm at most `n * Lambda` when the
factor columns and the contraction probe are unit and the coefficients are bounded by `Lambda`. Under [the listed assumptions](hyp:hd,hq,hLambda,horth,hunitC,hu,hw,hlam), [the stated conclusion follows](goal). -/
-- Proof route: use the exact contraction factorization, Cauchy--Schwarz for both loadings,
-- `‖S‖ ≤ ‖S‖F = sqrt n`, and submultiplicativity.
theorem compressedNumerator_operatorNorm_le {p n d q : ℕ}
    (C : FactorMatrix p n) (lam : Fin n → ℝ) (u w : Vec p)
    (U : Matrix (LiftIndex p d) (Fin n) ℝ) {Lambda : ℝ}
    (hd : 0 < d) (hq : 0 < q) (hLambda : 0 ≤ Lambda)
    (horth : OrthonormalColumns U)
    (hunitC : ∀ j, finiteFrobeniusNorm (C.col j) = 1)
    (hu : finiteFrobeniusNorm u = 1) (hw : finiteFrobeniusNorm w = 1)
    (hlam : ∀ j, |lam j| ≤ Lambda) :
    squareOperatorNorm
      (U.transpose * contractLast (decompositionTensor (d + d + q) C lam)
        (pencilProbes u w) * U) ≤ n * Lambda := by
  by_cases hn : n = 0
  · subst n
    simp [squareOperatorNorm]
  letI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  have hdot (x y : Vec p) (hx : finiteFrobeniusNorm x = 1)
      (hy : finiteFrobeniusNorm y = 1) : |dot x y| ≤ 1 := by
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
  have hload (j : Fin n) :
      |lam j * dot u (C.col j) ^ (q - 1) * dot w (C.col j)| ≤ Lambda := by
    have huj := hdot u (C.col j) hu (hunitC j)
    have hwj := hdot w (C.col j) hw (hunitC j)
    rw [abs_mul, abs_mul, abs_pow]
    calc
      |lam j| * |dot u (C.col j)| ^ (q - 1) * |dot w (C.col j)| ≤
          Lambda * 1 ^ (q - 1) * 1 := by
        gcongr
        exact hlam j
      _ = Lambda := by ring
  let S := U.transpose * liftedDirections d C
  let D := Matrix.diagonal (fun j =>
    lam j * dot u (C.col j) ^ (q - 1) * dot w (C.col j))
  have hS : squareOperatorNorm S ≤ Real.sqrt n :=
    compressedLift_operatorNorm_le_sqrt C U hd horth hunitC
  open scoped Matrix.Norms.L2Operator in
    change ‖S‖ ≤ Real.sqrt n at hS
    have hD : ‖D‖ ≤ Lambda := by
      change ‖Matrix.diagonal (fun j =>
        lam j * dot u (C.col j) ^ (q - 1) * dot w (C.col j))‖ ≤ Lambda
      rw [Matrix.l2_opNorm_diagonal]
      apply (pi_norm_le_iff_of_nonempty _).2
      intro j
      simpa [Real.norm_eq_abs] using hload j
    have hSt : ‖S.transpose‖ ≤ Real.sqrt n := by
      rw [show S.transpose = S.conjTranspose by ext i j; simp,
        Matrix.l2_opNorm_conjTranspose]
      exact hS
    rw [contractLast_decompositionTensor hq]
    change ‖U.transpose *
      (liftedDirections d C * D * (liftedDirections d C).transpose) * U‖ ≤
        n * Lambda
    rw [show U.transpose *
        (liftedDirections d C * D * (liftedDirections d C).transpose) * U =
          S * D * S.transpose by
      simp [S, Matrix.transpose_mul, Matrix.mul_assoc]]
    have hn0 : (0 : ℝ) ≤ n := by positivity
    calc
      ‖S * D * S.transpose‖ ≤ ‖S * D‖ * ‖S.transpose‖ :=
        Matrix.l2_opNorm_mul _ _
      _ ≤ (‖S‖ * ‖D‖) * ‖S.transpose‖ := by
        gcongr
        exact Matrix.l2_opNorm_mul _ _
      _ ≤ (Real.sqrt n * Lambda) * Real.sqrt n := by
        gcongr
      _ = n * Lambda := by
        rw [mul_assoc, mul_comm Lambda, ← mul_assoc, Real.mul_self_sqrt hn0]

end Causalean.Mathlib.Analysis.SymmetricTensorPencil
