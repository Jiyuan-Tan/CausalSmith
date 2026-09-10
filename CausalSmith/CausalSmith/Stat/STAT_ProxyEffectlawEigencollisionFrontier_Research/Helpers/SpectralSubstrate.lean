import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.PiL2
import Causalean.Mathlib.Analysis.SingularValueWeyl
import CausalSmith.Substrate.CollisionSafeSpectralLaw.MoorePenrose

/-!
Rectangular finite-dimensional spectral helpers used by the proxy-effect-law construction.
-/

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open scoped BigOperators

abbrev Euc (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev RectMatrix (rows cols : ℕ) := Matrix (Fin rows) (Fin cols) ℝ

noncomputable def matrixCLM {rows cols : ℕ} (A : RectMatrix rows cols) :
    Euc cols →L[ℝ] Euc rows :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)

-- @node: matrixCLM_continuous
@[fun_prop] lemma matrixCLM_continuous {rows cols : ℕ} :
    Continuous (@matrixCLM rows cols) := by
  let f : RectMatrix rows cols →ₗ[ℝ] (Euc cols →L[ℝ] Euc rows) :=
    { toFun := matrixCLM
      map_add' := by
        intro A B
        ext x i
        simp [matrixCLM, Matrix.toEuclideanLin_apply]
      map_smul' := by
        intro c A
        ext x i
        simp [matrixCLM, Matrix.toEuclideanLin_apply] }
  exact f.continuous_of_finiteDimensional

/-- The singular value with zero-based index `j`. -/
noncomputable def singularValue {rows cols : ℕ} (A : RectMatrix rows cols) (j : ℕ) : ℝ :=
  (LinearMap.singularValues (Matrix.toEuclideanLin A)) j

/-- The last signal singular value for a `rows × k` matrix. -/
noncomputable def signalMinSingular {rows k : ℕ} (A : RectMatrix rows k) : ℝ :=
  singularValue A (k - 1)

/-- Moore--Penrose formula for a full-column-rank rectangular matrix. -/
noncomputable def penroseInverse {rows cols : ℕ} (A : RectMatrix rows cols) :
    RectMatrix cols rows :=
  ((A.transpose * A)⁻¹) * A.transpose

/-- A genuine real thin singular-value decomposition.  Besides reconstruction, the right
singular vectors are orthonormal and every retained positive singular direction satisfies both
singular-vector equations; these conditions prevent the thresholded inverse from using an
arbitrary rank-one reconstruction. -/
structure SingularSystem {rows cols : ℕ} (A : RectMatrix rows cols) where
  sigma : Fin cols → ℝ
  left : Fin cols → Fin rows → ℝ
  right : Fin cols → Fin cols → ℝ
  sigma_eq : ∀ j, sigma j = singularValue A j
  sigma_nonneg : ∀ j, 0 ≤ sigma j
  right_orthonormal : ∀ r s, ∑ i, right r i * right s i = if r = s then 1 else 0
  left_orthonormal_of_pos : ∀ r s, 0 < sigma r → 0 < sigma s →
    ∑ i, left r i * left s i = if r = s then 1 else 0
  apply_right : ∀ r i, ∑ j, A i j * right r j = sigma r * left r i
  apply_left_transpose : ∀ r j, ∑ i, A i j * left r i = sigma r * right r j
  expansion : ∀ i j, A i j = ∑ r, sigma r * left r i * right r j

-- @node: singularSystem_exists
lemma singularSystem_exists {rows cols : ℕ} (A : RectMatrix rows cols) :
    Nonempty (SingularSystem A) := by
  let T : Euc cols →ₗ[ℝ] Euc rows := Matrix.toEuclideanLin A
  let S : Euc cols →ₗ[ℝ] Euc cols := LinearMap.adjoint T ∘ₗ T
  have hS : S.IsSymmetric := T.isSymmetric_adjoint_comp_self
  let b : OrthonormalBasis (Fin cols) ℝ (Euc cols) := hS.eigenvectorBasis (by simp)
  let sigma : Fin cols → ℝ := fun r => T.singularValues r
  let right : Fin cols → Fin cols → ℝ := fun r => b r
  let left : Fin cols → Euc rows := fun r =>
    if sigma r = 0 then 0 else (sigma r)⁻¹ • T (b r)
  have heigen (r : Fin cols) : S (b r) = (sigma r) ^ 2 • b r := by
    rw [hS.apply_eigenvectorBasis (by simp)]
    rw [T.sq_singularValues_fin (by simp) r]
    rfl
  have happly (r : Fin cols) : T (b r) = sigma r • left r := by
    by_cases hr : sigma r = 0
    · have hrker : T (b r) = 0 := by
        rw [← @inner_self_eq_zero ℝ]
        rw [← LinearMap.adjoint_inner_right]
        change inner ℝ (b r) (S (b r)) = 0
        rw [heigen, hr]
        simp
      simp [left, hr, hrker]
    · ext i
      simp [left, hr]
  have hadjoint (r : Fin cols) : LinearMap.adjoint T (left r) = sigma r • b r := by
    by_cases hr : sigma r = 0
    · simp [left, hr]
    · rw [show left r = (sigma r)⁻¹ • T (b r) by simp [left, hr]]
      rw [LinearMap.map_smul, ← LinearMap.comp_apply]
      change (sigma r)⁻¹ • S (b r) = _
      rw [heigen]
      rw [smul_smul]
      congr 1
      field_simp
  refine ⟨{
    sigma := sigma
    left := fun r i => left r i
    right := right
    sigma_eq := fun _ => rfl
    sigma_nonneg := fun r => T.singularValues_nonneg r
    right_orthonormal := ?_
    left_orthonormal_of_pos := ?_
    apply_right := ?_
    apply_left_transpose := ?_
    expansion := ?_ }⟩
  · intro r s
    by_cases hrs : r = s
    · subst s
      rw [if_pos rfl]
      have hinner : inner ℝ (b r) (b r) = 1 := by
        rw [real_inner_self_eq_norm_sq, b.orthonormal.1 r]
        norm_num
      simpa only [right, PiLp.inner_apply, RCLike.inner_apply, conj_trivial] using hinner
    · rw [if_neg hrs]
      have horth := b.orthonormal.2 hrs
      calc
        ∑ i, right r i * right s i = ∑ i, right s i * right r i := by
          apply Finset.sum_congr rfl
          intro i _
          exact mul_comm _ _
        _ = 0 := by
          simpa only [right, PiLp.inner_apply, RCLike.inner_apply, conj_trivial] using horth
  · intro r s hr hs
    have hr0 : sigma r ≠ 0 := ne_of_gt hr
    have hs0 : sigma s ≠ 0 := ne_of_gt hs
    have hinner : inner ℝ (left r) (left s) = if r = s then 1 else 0 := by
      rw [show left r = (sigma r)⁻¹ • T (b r) by simp [left, hr0],
        show left s = (sigma s)⁻¹ • T (b s) by simp [left, hs0]]
      rw [inner_smul_left, inner_smul_right]
      rw [← LinearMap.adjoint_inner_left]
      rw [show LinearMap.adjoint T (T (b r)) = S (b r) by rfl]
      simp only [map_inv₀, RCLike.conj_to_real]
      rw [heigen, inner_smul_left]
      simp only [map_pow, RCLike.conj_to_real]
      by_cases hrs : r = s
      · subst s
        rw [if_pos rfl, real_inner_self_eq_norm_sq, b.orthonormal.1 r]
        field_simp
      · rw [if_neg hrs, b.orthonormal.2 hrs]
        ring
    calc
      ∑ i, (left r).ofLp i * (left s).ofLp i =
          ∑ i, (left s).ofLp i * (left r).ofLp i := by
        apply Finset.sum_congr rfl
        intro i _
        exact mul_comm _ _
      _ = if r = s then 1 else 0 := by
        simpa only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial] using hinner
  · intro r i
    simpa [right, Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct, T] using
      congrArg (fun x : Euc rows => x.ofLp i) (happly r)
  · intro r j
    have h := congrArg (fun x : Euc cols => x.ofLp j) (hadjoint r)
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint] at h
    simpa [right, Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct, T,
      Matrix.conjTranspose_apply, Matrix.transpose_apply] using h
  · intro i j
    have hb := b.sum_repr' (EuclideanSpace.single j (1 : ℝ))
    have hTb := congrArg T hb
    have hj (r : Fin cols) : inner ℝ (b r) (EuclideanSpace.single j (1 : ℝ)) = b r j := by
      simp [PiLp.inner_apply]
    have hi : (T (EuclideanSpace.single j (1 : ℝ))) i = A i j := by
      simp [T, Matrix.toEuclideanLin_apply]
    simp_rw [map_sum, map_smul] at hTb
    calc
      A i j = (T (EuclideanSpace.single j (1 : ℝ))).ofLp i := hi.symm
      _ = (∑ r, inner ℝ (b r) (EuclideanSpace.single j (1 : ℝ)) • T (b r)).ofLp i :=
        congrArg (fun x : Euc rows => x.ofLp i) hTb.symm
      _ = ∑ r, sigma r * left r i * right r j := by
        have coord_sum (f : Fin cols → Euc rows) :
            (∑ r, f r).ofLp i = ∑ r, (f r).ofLp i := by
          induction (Finset.univ : Finset (Fin cols)) using Finset.induction_on with
          | empty => simp
          | insert a s ha ih => simp [ha, ih]
        rw [coord_sum]
        apply Finset.sum_congr rfl
        intro r _
        rw [hj, happly]
        simp only [right, smul_smul, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
        ring

/-- A fixed real SVD of a rectangular matrix. -/
noncomputable def singularSystem {rows cols : ℕ} (A : RectMatrix rows cols) :
    SingularSystem A := Classical.choice (singularSystem_exists A)

/-- The genuine SVD-thresholded Moore--Penrose inverse
`sum_{sigma_j >= threshold} sigma_j^{-1} v_j u_j^T`. -/
noncomputable def thresholdedPenroseInverse {rows cols : ℕ}
    (threshold : ℝ) (A : RectMatrix rows cols) : RectMatrix cols rows :=
  fun i j => ∑ r : Fin cols,
    if threshold ≤ (singularSystem A).sigma r then
      ((singularSystem A).sigma r)⁻¹ *
        (singularSystem A).right r i * (singularSystem A).left r j
    else 0

/-- The Moore--Penrose inverse of an arbitrary real rectangular matrix.  This local spelling
delegates to the paper-independent substrate construction, which satisfies all four Penrose
equations without a rank assumption. -/
-- @node: genuinePenroseInverse
noncomputable def genuinePenroseInverse {rows cols : ℕ} (A : RectMatrix rows cols) :
    RectMatrix cols rows :=
  CausalSmith.Substrate.CollisionSafeSpectralLaw.moorePenroseInverse A

-- @node: singular_value_variational_lower
lemma singular_value_variational_lower {rows cols : ℕ} (A : RectMatrix rows cols)
    (hA : Function.Injective (Matrix.toEuclideanLin A)) (x : Euc cols) :
    signalMinSingular A * ‖x‖ ≤ ‖Matrix.toEuclideanLin A x‖ := by
  let T : Euc cols →ₗ[ℝ] Euc rows := Matrix.toEuclideanLin A
  by_cases hc : cols = 0
  · subst cols
    change T.singularValues 0 * ‖x‖ ≤ ‖T x‖
    rw [T.singularValues_of_finrank_le (by simp)]
    simp
  have hcpos : 0 < cols := Nat.pos_of_ne_zero hc
  let S : Euc cols →ₗ[ℝ] Euc cols := LinearMap.adjoint T ∘ₗ T
  have hS : S.IsSymmetric := T.isSymmetric_adjoint_comp_self
  let b : OrthonormalBasis (Fin cols) ℝ (Euc cols) := hS.eigenvectorBasis (by simp)
  have hmin : ∀ i : Fin cols,
      (T.singularValues (cols - 1)) ^ 2 ≤ hS.eigenvalues (by simp) i := by
    intro i
    rw [T.sq_singularValues_of_lt (by simp) (Nat.sub_lt hcpos Nat.zero_lt_one)]
    exact hS.eigenvalues_antitone (by simp) (Nat.le_sub_one_of_lt i.isLt)
  have hquad : ‖T x‖ ^ 2 =
      ∑ i : Fin cols, hS.eigenvalues (by simp) i * (inner ℝ (b i) x) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    rw [← LinearMap.adjoint_inner_right]
    change inner ℝ x (S x) = _
    rw [← b.sum_inner_mul_inner x (S x)]
    apply Finset.sum_congr rfl
    intro i hi
    have heig := hS.eigenvectorBasis_apply_self_apply (by simp) x i
    have heig' : inner ℝ (b i) (S x) =
        hS.eigenvalues (by simp) i * inner ℝ (b i) x := by
      simpa [b, OrthonormalBasis.repr_apply_apply, RCLike.ofReal] using heig
    rw [heig', real_inner_comm]
    ring
  have hsq : (T.singularValues (cols - 1) * ‖x‖) ^ 2 ≤ ‖T x‖ ^ 2 := by
    rw [hquad, mul_pow, ← b.sum_sq_inner_right x, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (hmin i) (sq_nonneg _)
  exact (sq_le_sq₀ (mul_nonneg (T.singularValues_nonneg _) (norm_nonneg _))
    (norm_nonneg _)).mp hsq

-- @node: singular_value_weyl
lemma singular_value_weyl {rows cols j : ℕ} (A H : RectMatrix rows cols) :
    |singularValue (A + H) j - singularValue A j| ≤
      ‖matrixCLM H‖ := by
  have hadd : Matrix.toEuclideanLin (A + H) =
      Matrix.toEuclideanLin A + Matrix.toEuclideanLin H := by
    ext x i
    simp [Matrix.toEuclideanLin_apply]
  simpa only [singularValue, hadd, matrixCLM] using
    Causalean.Mathlib.Analysis.abs_singularValues_add_sub_singularValues_le_opNorm
      (Matrix.toEuclideanLin A) (Matrix.toEuclideanLin H) j

open scoped Matrix.Norms.L2Operator

-- @node: signalMinSingular_pos_injective
private lemma signalMinSingular_pos_injective {rows cols : ℕ} (A : RectMatrix rows cols)
    (h : 0 < signalMinSingular A) :
    Function.Injective (Matrix.toEuclideanLin A) := by
  apply (LinearMap.injective_iff_forall_lt_finrank_singularValues_pos _).2
  intro i hi
  rw [show Module.finrank ℝ (Euc cols) = cols by simp] at hi
  have hc : 0 < cols := lt_of_le_of_lt (Nat.zero_le i) hi
  exact lt_of_lt_of_le h
    ((Matrix.toEuclideanLin A).singularValues_antitone (Nat.le_sub_one_of_lt hi))

-- @node: gram_det_isUnit_of_injective
private lemma gram_det_isUnit_of_injective {rows cols : ℕ} (A : RectMatrix rows cols)
    (hA : Function.Injective (Matrix.toEuclideanLin A)) :
    IsUnit (A.transpose * A).det := by
  let T := Matrix.toEuclideanLin A
  have hgram : Function.Injective
      (Matrix.toEuclideanLin (A.transpose * A)) := by
    have hc : Matrix.toEuclideanLin (A.transpose * A) =
        LinearMap.adjoint T ∘ₗ T := by
      calc
        Matrix.toEuclideanLin (A.transpose * A) =
            Matrix.toEuclideanLin A.transpose ∘ₗ T := by
          ext x i
          simp [T, Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec]
        _ = LinearMap.adjoint T ∘ₗ T := by
          rw [← Matrix.conjTranspose_eq_transpose_of_trivial A,
            Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    rw [hc]
    exact (LinearMap.adjoint_comp_self_injective_iff T).2 hA
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y hxy
  have he : Matrix.toEuclideanLin (A.transpose * A) (WithLp.toLp 2 x) =
      Matrix.toEuclideanLin (A.transpose * A) (WithLp.toLp 2 y) := by
    simpa [Matrix.toEuclideanLin_apply] using congrArg (WithLp.toLp 2) hxy
  have := hgram he
  simpa using congrArg WithLp.ofLp this

-- @node: penrose_left_inverse
private lemma penrose_left_inverse {rows cols : ℕ} (A : RectMatrix rows cols)
    (hunit : IsUnit (A.transpose * A).det) :
    penroseInverse A * A = 1 := by
  letI := Matrix.invertibleOfIsUnitDet (A.transpose * A) hunit
  simp only [penroseInverse]
  rw [Matrix.mul_assoc, Matrix.inv_mul_of_invertible]

/-- On the full-column-rank domain, the canonical Moore--Penrose inverse agrees with
the Gram formula used by the perturbation and moment-identity proofs. -/
-- @node: genuinePenroseInverse_eq_penroseInverse_of_injective
lemma genuinePenroseInverse_eq_penroseInverse_of_injective {rows cols : ℕ}
    (A : RectMatrix rows cols) (hA : Function.Injective (Matrix.toEuclideanLin A)) :
    genuinePenroseInverse A = penroseInverse A := by
  let hunit := gram_det_isUnit_of_injective A hA
  letI := Matrix.invertibleOfIsUnitDet (A.transpose * A) hunit
  have hleft : penroseInverse A * A = 1 := penrose_left_inverse A hunit
  have hgram_symm : (A.transpose * A).transpose = A.transpose * A := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hinv_symm : ((A.transpose * A)⁻¹).transpose = (A.transpose * A)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hgram_symm]
  have hproj_symm : (A * penroseInverse A).transpose = A * penroseInverse A := by
    simp only [penroseInverse, Matrix.transpose_mul, Matrix.transpose_transpose, hinv_symm]
    rw [Matrix.mul_assoc]
  apply CausalSmith.Substrate.CollisionSafeSpectralLaw.isMoorePenroseInverse_unique
    (CausalSmith.Substrate.CollisionSafeSpectralLaw.moorePenroseInverse_spec A)
  refine ⟨?_, ?_, hproj_symm, ?_⟩
  · rw [Matrix.mul_assoc, hleft, Matrix.mul_one]
  · rw [hleft, Matrix.one_mul]
  · rw [hleft, Matrix.transpose_one]

-- @node: penrose_projection_contracts
private lemma penrose_projection_contracts {rows cols : ℕ} (A : RectMatrix rows cols)
    (hunit : IsUnit (A.transpose * A).det) (y : Euc rows) :
    ‖matrixCLM (A * penroseInverse A) y‖ ≤ ‖y‖ ∧
      ‖matrixCLM (1 - A * penroseInverse A) y‖ ≤ ‖y‖ := by
  letI := Matrix.invertibleOfIsUnitDet (A.transpose * A) hunit
  let T : Euc cols →ₗ[ℝ] Euc rows := Matrix.toEuclideanLin A
  let Q : Euc rows →ₗ[ℝ] Euc cols := Matrix.toEuclideanLin (penroseInverse A)
  let p : Euc rows := T (Q y)
  let r : Euc rows := y - p
  have hnormal : LinearMap.adjoint T r = 0 := by
    have hmat : A.transpose * (1 - A * penroseInverse A) = 0 := by
      simp only [Matrix.mul_sub, Matrix.mul_one, penroseInverse]
      rw [← Matrix.mul_assoc A.transpose A,
        ← Matrix.mul_assoc (A.transpose * A), Matrix.mul_inv_of_invertible,
        Matrix.one_mul, sub_self]
    have hr : r = Matrix.toEuclideanLin (1 - A * penroseInverse A) y := by
      ext i
      simp [r, p, T, Q, Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec]
    rw [hr, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    have hv : A.transpose.mulVec
      ((1 - A * penroseInverse A).mulVec y.ofLp) = 0 := by
      rw [Matrix.mulVec_mulVec, hmat]
      simp
    ext i
    simpa [Matrix.toEuclideanLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec] using
      congrArg (fun v => v i) hv
  have hortho : inner ℝ p r = 0 := by
    rw [show p = T (Q y) by rfl, ← LinearMap.adjoint_inner_right, hnormal]
    simp
  have hsq := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero p r hortho
  have hsum : p + r = y := by simp [r]
  rw [hsum] at hsq
  have hsquares : ‖p‖ ^ 2 ≤ ‖y‖ ^ 2 := by nlinarith [sq_nonneg ‖r‖]
  have hrsquares : ‖r‖ ^ 2 ≤ ‖y‖ ^ 2 := by nlinarith [sq_nonneg ‖p‖]
  have hp : ‖p‖ ≤ ‖y‖ := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsquares
  have hrle : ‖r‖ ≤ ‖y‖ := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hrsquares
  constructor
  · simpa [matrixCLM, p, T, Q, Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec] using hp
  · simpa [matrixCLM, r, p, T, Q, Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec,
      Matrix.sub_mulVec, Matrix.one_mulVec] using hrle

-- @node: penrose_norm_le
private lemma penrose_norm_le {rows cols : ℕ} {s : ℝ} (A : RectMatrix rows cols)
    (hs : 0 < s) (hlower : ∀ x : Euc cols, s * ‖x‖ ≤ ‖Matrix.toEuclideanLin A x‖) :
    ‖matrixCLM (penroseInverse A)‖ ≤ s⁻¹ := by
  have hinj : Function.Injective (Matrix.toEuclideanLin A) := by
    intro x y hxy
    have hz : Matrix.toEuclideanLin A (x - y) = 0 := by simp [hxy]
    have := hlower (x - y)
    rw [hz, norm_zero] at this
    have : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y)]
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  have hu := gram_det_isUnit_of_injective A hinj
  apply ContinuousLinearMap.opNorm_le_bound _ (le_of_lt (inv_pos.mpr hs))
  intro y
  have hc := (penrose_projection_contracts A hu y).1
  have hlo := hlower (matrixCLM (penroseInverse A) y)
  have himage : Matrix.toEuclideanLin A (matrixCLM (penroseInverse A) y) =
      matrixCLM (A * penroseInverse A) y := by
    ext i
    simp [matrixCLM, Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec]
  rw [himage] at hlo
  exact (le_inv_mul_iff₀ hs).2 (hlo.trans hc)

-- @node: gram_inverse_norm_le
private lemma gram_inverse_norm_le {rows cols : ℕ} {s : ℝ} (A : RectMatrix rows cols)
    (hs : 0 < s) (hlower : ∀ x : Euc cols, s * ‖x‖ ≤ ‖Matrix.toEuclideanLin A x‖) :
    ‖matrixCLM ((A.transpose * A)⁻¹)‖ ≤ s⁻¹ ^ 2 := by
  have hinj : Function.Injective (Matrix.toEuclideanLin A) := by
    intro x y hxy
    have hz : Matrix.toEuclideanLin A (x - y) = 0 := by simp [hxy]
    have := hlower (x - y)
    rw [hz, norm_zero] at this
    have : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y)]
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  have hu := gram_det_isUnit_of_injective A hinj
  letI := Matrix.invertibleOfIsUnitDet (A.transpose * A) hu
  have hid : penroseInverse A * (penroseInverse A).transpose = (A.transpose * A)⁻¹ := by
    simp only [penroseInverse, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_nonsing_inv, Matrix.transpose_mul, Matrix.mul_assoc]
    have hsymm : (A.transpose * A).transpose = A.transpose * A := by
      rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [← Matrix.mul_assoc A.transpose A,
      ← Matrix.mul_assoc (A.transpose * A)⁻¹, Matrix.inv_mul_of_invertible,
      Matrix.one_mul]
  have hpn := penrose_norm_le A hs hlower
  change ‖penroseInverse A‖ ≤ s⁻¹ at hpn
  change ‖(A.transpose * A)⁻¹‖ ≤ s⁻¹ ^ 2
  rw [← hid]
  have hcstar := Matrix.l2_opNorm_conjTranspose_mul_self (penroseInverse A).transpose
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose,
    Matrix.l2_opNorm_conjTranspose] at hcstar
  rw [hcstar]
  have htrans : ‖(penroseInverse A).transpose‖ = ‖penroseInverse A‖ := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.l2_opNorm_conjTranspose]
  rw [htrans]
  simpa [pow_two] using
    (pow_le_pow_left₀ (norm_nonneg _) hpn 2)

-- keep: generic rectangular Penrose-inverse perturbation bound for later spectral-law runs
lemma penrose_perturbation {rows cols : ℕ} {s₀ : ℝ}
    (A B : RectMatrix rows cols)
    (hA : s₀ ≤ signalMinSingular A) (hB : s₀ ≤ signalMinSingular B)
    (hs : 0 < s₀) :
    ‖matrixCLM (penroseInverse A - penroseInverse B)‖ ≤
      3 * s₀⁻¹ ^ 2 * ‖matrixCLM (A - B)‖ := by
  have hApos : 0 < signalMinSingular A := hs.trans_le hA
  have hBpos : 0 < signalMinSingular B := hs.trans_le hB
  have hAi := signalMinSingular_pos_injective A hApos
  have hBi := signalMinSingular_pos_injective B hBpos
  have hAlower (x : Euc cols) :
      s₀ * ‖x‖ ≤ ‖Matrix.toEuclideanLin A x‖ :=
    (mul_le_mul_of_nonneg_right hA (norm_nonneg x)).trans
      (singular_value_variational_lower A hAi x)
  have hBlower (x : Euc cols) :
      s₀ * ‖x‖ ≤ ‖Matrix.toEuclideanLin B x‖ :=
    (mul_le_mul_of_nonneg_right hB (norm_nonneg x)).trans
      (singular_value_variational_lower B hBi x)
  have hAu := gram_det_isUnit_of_injective A hAi
  have hBu := gram_det_isUnit_of_injective B hBi
  letI := Matrix.invertibleOfIsUnitDet (A.transpose * A) hAu
  letI := Matrix.invertibleOfIsUnitDet (B.transpose * B) hBu
  have hPA := penrose_norm_le A hs hAlower
  have hPB := penrose_norm_le B hs hBlower
  have hGA := gram_inverse_norm_le A hs hAlower
  have hresB : ‖matrixCLM (1 - B * penroseInverse B)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro y
    simpa using (penrose_projection_contracts B hBu y).2
  have hnormalB : B.transpose * (1 - B * penroseInverse B) = 0 := by
    simp only [Matrix.mul_sub, Matrix.mul_one, penroseInverse]
    rw [← Matrix.mul_assoc B.transpose B,
      ← Matrix.mul_assoc (B.transpose * B), Matrix.mul_inv_of_invertible,
      Matrix.one_mul, sub_self]
  have hid : penroseInverse A - penroseInverse B =
      penroseInverse A * (B - A) * penroseInverse B +
        (A.transpose * A)⁻¹ * (A - B).transpose *
          (1 - B * penroseInverse B) := by
    have hleftA := penrose_left_inverse A hAu
    have hzero : (A.transpose * A)⁻¹ * B.transpose *
        (1 - B * penroseInverse B) = 0 := by
      rw [Matrix.mul_assoc, hnormalB, Matrix.mul_zero]
    have hdiff : (A.transpose * A)⁻¹ * (A.transpose - B.transpose) =
        (A.transpose * A)⁻¹ * A.transpose -
          (A.transpose * A)⁻¹ * B.transpose := Matrix.mul_sub _ _ _
    rw [Matrix.transpose_sub, Matrix.mul_sub]
    symm
    rw [Matrix.sub_mul, hdiff, Matrix.sub_mul]
    rw [hleftA, Matrix.one_mul]
    rw [show (A.transpose * A)⁻¹ * A.transpose = penroseInverse A by rfl]
    rw [hzero, sub_zero, Matrix.mul_sub, Matrix.mul_one,
      Matrix.mul_assoc (penroseInverse A) B]
    abel
  open scoped Matrix.Norms.L2Operator in
    change ‖penroseInverse A - penroseInverse B‖ ≤
      3 * s₀⁻¹ ^ 2 * ‖A - B‖
  rw [hid]
  change ‖penroseInverse A‖ ≤ s₀⁻¹ at hPA
  change ‖penroseInverse B‖ ≤ s₀⁻¹ at hPB
  change ‖(A.transpose * A)⁻¹‖ ≤ s₀⁻¹ ^ 2 at hGA
  change ‖1 - B * penroseInverse B‖ ≤ 1 at hresB
  have ht1 : ‖penroseInverse A * (B - A) * penroseInverse B‖ ≤
      (s₀⁻¹ * ‖A - B‖) * s₀⁻¹ := by
    calc
      _ ≤ ‖penroseInverse A * (B - A)‖ * ‖penroseInverse B‖ :=
        Matrix.l2_opNorm_mul _ _
      _ ≤ (‖penroseInverse A‖ * ‖B - A‖) * ‖penroseInverse B‖ := by
        gcongr
        exact Matrix.l2_opNorm_mul _ _
      _ ≤ (s₀⁻¹ * ‖A - B‖) * s₀⁻¹ := by
        rw [norm_sub_rev B A]
        gcongr
  have ht2 : ‖(A.transpose * A)⁻¹ * (A - B).transpose *
      (1 - B * penroseInverse B)‖ ≤
      (s₀⁻¹ ^ 2 * ‖A - B‖) * 1 := by
    calc
      _ ≤ ‖(A.transpose * A)⁻¹ * (A - B).transpose‖ *
          ‖1 - B * penroseInverse B‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖(A.transpose * A)⁻¹‖ * ‖(A - B).transpose‖) *
          ‖1 - B * penroseInverse B‖ := by
        gcongr
        exact Matrix.l2_opNorm_mul _ _
      _ ≤ (s₀⁻¹ ^ 2 * ‖A - B‖) * 1 := by
        have htrans : ‖(A - B).transpose‖ = ‖A - B‖ := by
          rw [← Matrix.conjTranspose_eq_transpose_of_trivial,
            Matrix.l2_opNorm_conjTranspose]
        rw [htrans]
        gcongr
  calc
    ‖penroseInverse A * (B - A) * penroseInverse B +
        (A.transpose * A)⁻¹ * (A - B).transpose *
          (1 - B * penroseInverse B)‖
        ≤ ‖penroseInverse A * (B - A) * penroseInverse B‖ +
          ‖(A.transpose * A)⁻¹ * (A - B).transpose *
            (1 - B * penroseInverse B)‖ := norm_add_le _ _
    _ ≤ (s₀⁻¹ * ‖A - B‖) * s₀⁻¹ +
          (s₀⁻¹ ^ 2 * ‖A - B‖) * 1 := add_le_add ht1 ht2
    _ ≤ 3 * s₀⁻¹ ^ 2 * ‖A - B‖ := by
      have hi : 0 ≤ s₀⁻¹ := inv_nonneg.mpr hs.le
      have hn : 0 ≤ ‖A - B‖ := norm_nonneg _
      nlinarith


end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
