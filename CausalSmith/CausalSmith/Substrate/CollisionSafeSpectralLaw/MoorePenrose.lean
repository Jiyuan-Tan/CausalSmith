import CausalSmith.Substrate.CollisionSafeSpectralLaw.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Moore--Penrose inverses and moving-range perturbations

This module gives a paper-independent Moore--Penrose inverse for every finite real rectangular
matrix.  It exposes the Penrose equations, the two associated orthogonal projections, the exact
ambient perturbation identity, and its operator-norm and singular-margin consequences.  Neither
the row space nor the column space is fixed.
-/

namespace CausalSmith.Substrate.CollisionSafeSpectralLaw

open scoped BigOperators Matrix.Norms.L2Operator

open Module InnerProductSpace

private def restrictKerOrth {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] (T : E →ₗ[ℝ] F) :
    T.kerᗮ →ₗ[ℝ] T.range where
  toFun x := ⟨T x, ⟨x, rfl⟩⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

private theorem restrictKerOrth_bijective {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (T : E →ₗ[ℝ] F) :
    Function.Bijective (restrictKerOrth T) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    have hk : (x : E) - y ∈ T.ker := by
      rw [LinearMap.mem_ker]
      have hxy' := congr_arg Subtype.val hxy
      simp only [restrictKerOrth] at hxy'
      simpa [sub_eq_zero] using hxy'
    have ho : (x : E) - y ∈ T.kerᗮ := T.kerᗮ.sub_mem x.property y.property
    have hz : (x : E) - y = 0 := T.ker.orthogonal_disjoint.le_bot ⟨hk, ho⟩
    exact sub_eq_zero.mp hz
  · rintro ⟨z, x, rfl⟩
    let p : T.kerᗮ := T.kerᗮ.orthogonalProjectionOnto x
    refine ⟨p, ?_⟩
    apply Subtype.ext
    change T p = T x
    rw [← sub_eq_zero, ← map_sub]
    have hm : x - (p : E) ∈ T.ker := by
      simpa only [p, Submodule.coe_orthogonalProjectionOnto_apply,
        Submodule.orthogonal_orthogonal] using
        T.kerᗮ.sub_starProjection_mem_orthogonal x
    rw [LinearMap.mem_ker] at hm
    simpa [map_sub] using congr_arg Neg.neg hm

private noncomputable def mpLinear {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (T : E →ₗ[ℝ] F) : F →ₗ[ℝ] E :=
  T.kerᗮ.subtype.comp
    ((LinearEquiv.ofBijective
      (restrictKerOrth T) (restrictKerOrth_bijective T)).symm.toLinearMap.comp
        T.range.orthogonalProjectionOnto.toLinearMap)

private theorem comp_mpLinear {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (T : E →ₗ[ℝ] F) :
    T.comp (mpLinear T) = T.range.starProjection.toLinearMap := by
  ext y
  simp only [LinearMap.comp_apply, mpLinear, Submodule.coe_subtype, ContinuousLinearMap.coe_coe]
  let e := LinearEquiv.ofBijective (restrictKerOrth T) (restrictKerOrth_bijective T)
  have he : restrictKerOrth T (e.symm (T.range.orthogonalProjectionOnto y)) =
      T.range.orthogonalProjectionOnto y := e.apply_symm_apply _
  have he' := congr_arg Subtype.val he
  simp only [restrictKerOrth] at he'
  exact he'

private theorem mpLinear_comp {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (T : E →ₗ[ℝ] F) :
    (mpLinear T).comp T = T.kerᗮ.starProjection.toLinearMap := by
  ext x
  let p : T.kerᗮ := T.kerᗮ.orthogonalProjectionOnto x
  have hTp : T p = T x := by
    rw [← sub_eq_zero, ← map_sub]
    have hm : x - (p : E) ∈ T.ker := by
      simpa only [p, Submodule.coe_orthogonalProjectionOnto_apply,
        Submodule.orthogonal_orthogonal] using
        T.kerᗮ.sub_starProjection_mem_orthogonal x
    rw [LinearMap.mem_ker] at hm
    exact sub_eq_zero.mp (by simpa [map_sub] using congr_arg Neg.neg hm)
  let e := LinearEquiv.ofBijective (restrictKerOrth T) (restrictKerOrth_bijective T)
  have he : e.symm ⟨T x, ⟨x, rfl⟩⟩ = p := by
    apply e.injective
    rw [e.apply_symm_apply]
    apply Subtype.ext
    exact hTp.symm
  change ((LinearEquiv.ofBijective (restrictKerOrth T) (restrictKerOrth_bijective T)).symm
      (T.range.orthogonalProjectionOnto (T x)) : E) = T.kerᗮ.starProjection x
  have hproj : T.range.orthogonalProjectionOnto (T x) = ⟨T x, ⟨x, rfl⟩⟩ :=
    T.range.orthogonalProjectionOnto_mem_subspace_eq_self ⟨T x, ⟨x, rfl⟩⟩
  rw [hproj, he]
  rfl

private theorem toEuclideanLin_mul {l m n : ℕ}
    (A : RectMatrix l m) (B : RectMatrix m n) :
    Matrix.toEuclideanLin (A * B) =
      (Matrix.toEuclideanLin A).comp (Matrix.toEuclideanLin B) := by
  exact Matrix.toLin_mul (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin l) ℝ).toBasis A B

private theorem symmetricIdempotent_norms_le_one {n : ℕ} (P : RectMatrix n n)
    (hi : P * P = P) (hs : P.transpose = P) :
    ‖P‖ ≤ 1 ∧ ‖(1 : RectMatrix n n) - P‖ ≤ 1 := by
  have hp : IsStarProjection P := by
    rw [isStarProjection_iff']
    refine ⟨hi, ?_⟩
    rw [Matrix.star_eq_conjTranspose]
    ext i j
    simpa [Matrix.conjTranspose_apply] using congr_fun (congr_fun hs i) j
  exact ⟨hp.norm_le P, hp.one_sub.norm_le _⟩

private theorem l2_opNorm_transpose {m n : ℕ} (A : RectMatrix m n) :
    ‖A.transpose‖ = ‖A‖ := by
  have hreal : A.transpose = A.conjTranspose := by ext; simp
  rw [hreal, Matrix.l2_opNorm_conjTranspose]

private theorem l2_opNorm_mul_three {a b c d : ℕ} (A : RectMatrix a b)
    (B : RectMatrix b c) (C : RectMatrix c d) :
    ‖A * B * C‖ ≤ ‖A‖ * ‖B‖ * ‖C‖ := by
  exact (Matrix.l2_opNorm_mul (A * B) C).trans
    (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul A B) (norm_nonneg C))

private theorem l2_opNorm_mul_four {a b c d e : ℕ} (A : RectMatrix a b)
    (B : RectMatrix b c) (C : RectMatrix c d) (D : RectMatrix d e) :
    ‖A * B * C * D‖ ≤ ‖A‖ * ‖B‖ * ‖C‖ * ‖D‖ := by
  exact (Matrix.l2_opNorm_mul (A * B * C) D).trans
    (mul_le_mul_of_nonneg_right (l2_opNorm_mul_three A B C) (norm_nonneg D))

private theorem singularValues_mul_norm_le_of_mem_ker_orthogonal
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (T : E →ₗ[ℝ] F) {r : ℕ}
    (hr : finrank ℝ T.range = r) (hrpos : 0 < r) (x : E) (hx : x ∈ T.kerᗮ) :
    T.singularValues (r - 1) * ‖x‖ ≤ ‖T x‖ := by
  let hself := T.isSymmetric_adjoint_comp_self
  let b := hself.eigenvectorBasis rfl
  have hrle : r ≤ finrank ℝ E := by
    rw [← hr]
    exact LinearMap.finrank_range_le T
  have hj : r - 1 < finrank ℝ E := lt_of_lt_of_le (by omega) hrle
  have hof (z : ℝ) : (RCLike.ofReal z : ℝ) = z := by
    calc
      (RCLike.ofReal z : ℝ) = RCLike.re (RCLike.ofReal z : ℝ) :=
        (RCLike.re_to_real).symm
      _ = z := RCLike.ofReal_re z
  have hnorm_sq :
      ‖T x‖ ^ 2 =
        ∑ i : Fin (finrank ℝ E),
          hself.eigenvalues rfl i * ‖inner ℝ (b i) x‖ ^ 2 := by
    calc
      ‖T x‖ ^ 2 = inner ℝ (T x) (T x) := (real_inner_self_eq_norm_sq _).symm
      _ = inner ℝ x ((T.adjoint ∘ₗ T) x) := by
        exact (T.adjoint_inner_right x (T x)).symm
      _ = ∑ i, inner ℝ x (b i) * inner ℝ (b i) ((T.adjoint ∘ₗ T) x) :=
        (b.sum_inner_mul_inner x ((T.adjoint ∘ₗ T) x)).symm
      _ = ∑ i, hself.eigenvalues rfl i * ‖inner ℝ (b i) x‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← hself (b i) x, hself.apply_eigenvectorBasis]
        simp only [real_inner_smul_left, hof]
        rw [real_inner_comm x (b i)]
        simp only [Real.norm_eq_abs, sq_abs]
        ring
  have hterm (i : Fin (finrank ℝ E)) :
      T.singularValues (r - 1) ^ 2 * ‖inner ℝ (b i) x‖ ^ 2 ≤
        hself.eigenvalues rfl i * ‖inner ℝ (b i) x‖ ^ 2 := by
    by_cases hi : (i : ℕ) < r
    · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      rw [T.sq_singularValues_fin rfl ⟨r - 1, hj⟩]
      exact hself.eigenvalues_antitone rfl
        (Fin.le_iff_val_le_val.mpr (Nat.le_sub_one_of_lt hi))
    · have hir : r ≤ (i : ℕ) := Nat.le_of_not_gt hi
      have hsig : T.singularValues (i : ℕ) = 0 := by
        apply T.singularValues_eq_zero_iff_le_finrank_range.mpr
        simpa [hr] using hir
      have hlam : hself.eigenvalues rfl i = 0 := by
        rw [← T.sq_singularValues_fin rfl i, hsig]
        norm_num
      have hbker : (b i : E) ∈ T.ker := by
        rw [← T.ker_adjoint_comp_self, LinearMap.mem_ker]
        rw [hself.apply_eigenvectorBasis, hlam, hof, zero_smul]
      have hinter : inner ℝ (b i) x = 0 := by
        rw [real_inner_comm]
        exact (T.ker.mem_orthogonal' x).mp hx _ hbker
      simp [hinter]
  apply (sq_le_sq₀
    (mul_nonneg (T.singularValues_nonneg _) (norm_nonneg _))
    (norm_nonneg _)).mp
  rw [mul_pow, hnorm_sq, ← b.sum_sq_norm_inner_right x, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => hterm i

/-- `G` is a Moore--Penrose inverse of `A` when the four real Penrose equations hold. -/
def IsMoorePenroseInverse {rows cols : ℕ}
    (A : RectMatrix rows cols) (G : RectMatrix cols rows) : Prop :=
  A * G * A = A ∧ G * A * G = G ∧
    (A * G).transpose = A * G ∧ (G * A).transpose = G * A

private noncomputable def constructedMP {rows cols : ℕ} (A : RectMatrix rows cols) :
    RectMatrix cols rows :=
  Matrix.toEuclideanLin.symm (mpLinear (Matrix.toEuclideanLin A))

private theorem constructedMP_spec {rows cols : ℕ} (A : RectMatrix rows cols) :
    IsMoorePenroseInverse A (constructedMP A) := by
  let T := Matrix.toEuclideanLin A
  let G : RectMatrix cols rows := constructedMP A
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Matrix.toEuclideanLin.injective
    rw [toEuclideanLin_mul, toEuclideanLin_mul]
    simp only [constructedMP, LinearEquiv.apply_symm_apply]
    change (T.comp (mpLinear T)).comp T = T
    rw [comp_mpLinear]
    apply LinearMap.ext
    intro x
    exact T.range.starProjection_eq_self_iff.mpr ⟨x, rfl⟩
  · apply Matrix.toEuclideanLin.injective
    rw [toEuclideanLin_mul, toEuclideanLin_mul]
    simp only [constructedMP, LinearEquiv.apply_symm_apply]
    change ((mpLinear T).comp T).comp (mpLinear T) = mpLinear T
    rw [mpLinear_comp]
    apply LinearMap.ext
    intro y
    apply T.kerᗮ.starProjection_eq_self_iff.mpr
    change mpLinear T y ∈ T.kerᗮ
    exact ((LinearEquiv.ofBijective (restrictKerOrth T) (restrictKerOrth_bijective T)).symm
      (T.range.orthogonalProjectionOnto y)).property
  · apply Matrix.toEuclideanLin.injective
    have hreal : (A * G).transpose = (A * G).conjTranspose := by ext; simp
    rw [hreal, Matrix.toEuclideanLin_conjTranspose_eq_adjoint, toEuclideanLin_mul]
    simp only [G, constructedMP, LinearEquiv.apply_symm_apply]
    change LinearMap.adjoint (T.comp (mpLinear T)) = T.comp (mpLinear T)
    rw [comp_mpLinear]
    exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (isSelfAdjoint_starProjection T.range)).adjoint_eq
  · apply Matrix.toEuclideanLin.injective
    have hreal : (G * A).transpose = (G * A).conjTranspose := by ext; simp
    rw [hreal, Matrix.toEuclideanLin_conjTranspose_eq_adjoint, toEuclideanLin_mul]
    simp only [G, constructedMP, LinearEquiv.apply_symm_apply]
    change LinearMap.adjoint ((mpLinear T).comp T) = (mpLinear T).comp T
    rw [mpLinear_comp]
    exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (isSelfAdjoint_starProjection T.kerᗮ)).adjoint_eq

/-- Every finite real rectangular matrix has a Moore--Penrose inverse. -/
theorem exists_moorePenroseInverse {rows cols : ℕ} (A : RectMatrix rows cols) :
    ∃ G : RectMatrix cols rows, IsMoorePenroseInverse A G :=
  ⟨constructedMP A, constructedMP_spec A⟩

/-- A Moore--Penrose inverse of a fixed real matrix is unique. -/
theorem isMoorePenroseInverse_unique {rows cols : ℕ} {A : RectMatrix rows cols}
    {G H : RectMatrix cols rows} (hG : IsMoorePenroseInverse A G)
    (hH : IsMoorePenroseInverse A H) : G = H := by
  have hGAHA : (G * A) * (H * A) = G * A := by
    calc
      (G * A) * (H * A) = G * (A * H * A) := by simp only [Matrix.mul_assoc]
      _ = G * A := by rw [hH.1]
  have hHAGA : (H * A) * (G * A) = H * A := by
    calc
      (H * A) * (G * A) = H * (A * G * A) := by simp only [Matrix.mul_assoc]
      _ = H * A := by rw [hG.1]
  have hGAeqHA : G * A = H * A := by
    have ht := congr_arg Matrix.transpose hGAHA
    have ht' : (H * A) * (G * A) = G * A := by
      simpa only [Matrix.transpose_mul, hH.2.2.2, hG.2.2.2] using ht
    exact (hHAGA.symm.trans ht').symm
  have hAGAH : (A * G) * (A * H) = A * H := by
    calc
      (A * G) * (A * H) = (A * G * A) * H := by simp only [Matrix.mul_assoc]
      _ = A * H := by rw [hG.1]
  have hAHAG : (A * H) * (A * G) = A * G := by
    calc
      (A * H) * (A * G) = (A * H * A) * G := by simp only [Matrix.mul_assoc]
      _ = A * G := by rw [hH.1]
  have hAGeqAH : A * G = A * H := by
    have ht := congr_arg Matrix.transpose hAGAH
    have ht' : (A * H) * (A * G) = A * H := by
      simpa only [Matrix.transpose_mul, hH.2.2.1, hG.2.2.1] using ht
    exact hAHAG.symm.trans ht'
  calc
    G = G * A * G := hG.2.1.symm
    _ = H * A * G := by rw [hGAeqHA]
    _ = H * (A * G) := Matrix.mul_assoc _ _ _
    _ = H * (A * H) := by rw [hAGeqAH]
    _ = H * A * H := (Matrix.mul_assoc _ _ _).symm
    _ = H := hH.2.1

/-- The canonical Moore--Penrose inverse of a finite real rectangular matrix. -/
noncomputable def moorePenroseInverse {rows cols : ℕ}
    (A : RectMatrix rows cols) : RectMatrix cols rows :=
  Classical.choose (exists_moorePenroseInverse A)

postfix:max "†" => moorePenroseInverse

/-- The canonical inverse satisfies all four Penrose equations. -/
theorem moorePenroseInverse_spec {rows cols : ℕ} (A : RectMatrix rows cols) :
    IsMoorePenroseInverse A A† := by
  exact Classical.choose_spec (exists_moorePenroseInverse A)

/-- The product `A A†` is the orthogonal projector onto the moving column space of `A`. -/
theorem rangeProjection_penrose {rows cols : ℕ} (A : RectMatrix rows cols) :
    (A * A†) * (A * A†) = A * A† ∧ (A * A†).transpose = A * A† := by
  have h := moorePenroseInverse_spec A
  constructor
  · rw [← Matrix.mul_assoc, h.1]
  · exact h.2.2.1

/-- The product `A† A` is the orthogonal projector onto the moving row space of `A`. -/
theorem rowProjection_penrose {rows cols : ℕ} (A : RectMatrix rows cols) :
    (A† * A) * (A† * A) = A† * A ∧ (A† * A).transpose = A† * A := by
  have h := moorePenroseInverse_spec A
  constructor
  · rw [← Matrix.mul_assoc, h.2.1]
  · exact h.2.2.2

/-- A Penrose range projector and its orthogonal complement both have norm at most one. -/
theorem rangeProjection_norms_le_one {rows cols : ℕ} (A : RectMatrix rows cols) :
    ‖A * A†‖ ≤ 1 ∧ ‖(1 : RectMatrix rows rows) - A * A†‖ ≤ 1 := by
  exact symmetricIdempotent_norms_le_one (A * A†)
    (rangeProjection_penrose A).1 (rangeProjection_penrose A).2

/-- A Penrose row projector and its orthogonal complement both have norm at most one. -/
theorem rowProjection_norms_le_one {rows cols : ℕ} (A : RectMatrix rows cols) :
    ‖A† * A‖ ≤ 1 ∧ ‖(1 : RectMatrix cols cols) - A† * A‖ ≤ 1 := by
  exact symmetricIdempotent_norms_le_one (A† * A)
    (rowProjection_penrose A).1 (rowProjection_penrose A).2

/-- Exact ambient Moore--Penrose difference identity.  It permits both ranges to move; the
equal-rank hypothesis records the perturbative stratum used by the norm corollaries. -/
theorem moorePenrose_sub_eq {rows cols : ℕ} (A B : RectMatrix rows cols)
    (hrank : A.rank = B.rank) :
    B† - A† =
      -B† * (B - A) * A† +
      B† * B†.transpose * (B - A).transpose * ((1 : RectMatrix rows rows) - A * A†) +
      ((1 : RectMatrix cols cols) - B† * B) * (B - A).transpose * A†.transpose * A† := by
  clear hrank
  have hA := moorePenroseInverse_spec A
  have hB := moorePenroseInverse_spec B
  have hBBtBt : B† * B†.transpose * B.transpose = B† := by
    calc
      B† * B†.transpose * B.transpose = B† * (B†.transpose * B.transpose) :=
        Matrix.mul_assoc _ _ _
      _ = B† * (B * B†) := by rw [← hB.2.2.1, Matrix.transpose_mul]
      _ = B† := by rw [← Matrix.mul_assoc, hB.2.1]
  have hAtAtA : A.transpose * A†.transpose * A† = A† := by
    calc
      A.transpose * A†.transpose * A† = (A† * A) * A† := by
        rw [← hA.2.2.2, Matrix.transpose_mul]
      _ = A† := hA.2.1
  have hAtQ :
      A.transpose * ((1 : RectMatrix rows rows) - A * A†) = 0 := by
    have ht := congr_arg Matrix.transpose hA.1
    have ht' : A.transpose * (A†.transpose * A.transpose) = A.transpose := by
      simpa only [Matrix.transpose_mul] using ht
    have hs : A†.transpose * A.transpose = A * A† := by
      simpa only [Matrix.transpose_mul] using hA.2.2.1
    have hh : A.transpose * (A * A†) = A.transpose := by rw [← hs, ht']
    rw [Matrix.mul_sub, Matrix.mul_one, hh, sub_self]
  have hQB :
      ((1 : RectMatrix cols cols) - B† * B) * B.transpose = 0 := by
    have ht := congr_arg Matrix.transpose hB.1
    have ht' : B.transpose * (B†.transpose * B.transpose) = B.transpose := by
      simpa only [Matrix.transpose_mul] using ht
    have hs : B.transpose * B†.transpose = B† * B := by
      simpa only [Matrix.transpose_mul] using hB.2.2.2
    have hh : (B† * B) * B.transpose = B.transpose := by
      rw [← hs, Matrix.mul_assoc, ht']
    rw [Matrix.sub_mul, Matrix.one_mul, hh, sub_self]
  rw [Matrix.transpose_sub]
  have hterm2 :
      B† * B†.transpose * (B.transpose - A.transpose) *
          ((1 : RectMatrix rows rows) - A * A†) =
        B† - B† * A * A† := by
    let Q : RectMatrix rows rows := 1 - A * A†
    change B† * B†.transpose * (B.transpose - A.transpose) * Q =
      B† - B† * A * A†
    calc
      _ = (B† * B†.transpose * B.transpose) * Q -
          B† * B†.transpose * (A.transpose * Q) := by
            rw [Matrix.mul_assoc (B† * B†.transpose) (B.transpose - A.transpose) Q,
              Matrix.sub_mul B.transpose A.transpose Q,
              Matrix.mul_sub (B† * B†.transpose), Matrix.mul_assoc (B† * B†.transpose)]
      _ = B† * Q := by rw [hBBtBt, show A.transpose * Q = 0 by exact hAtQ]; simp
      _ = B† - B† * A * A† := by
        rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc]
  have hterm3 :
      ((1 : RectMatrix cols cols) - B† * B) *
          (B.transpose - A.transpose) * A†.transpose * A† =
        -(A† - B† * B * A.transpose * A†.transpose * A†) := by
    let Q : RectMatrix cols cols := 1 - B† * B
    change Q * (B.transpose - A.transpose) * A†.transpose * A† =
      -(A† - B† * B * A.transpose * A†.transpose * A†)
    have hAtAtA' : A.transpose * (A†.transpose * A†) = A† := by
      rw [← Matrix.mul_assoc, hAtAtA]
    calc
      _ = (Q * B.transpose) * A†.transpose * A† -
          (Q * A.transpose) * A†.transpose * A† := by
            rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul]
      _ = -(Q * A.transpose * A†.transpose * A†) := by
        rw [show Q * B.transpose = 0 by exact hQB]; simp
      _ = -(A† - B† * B * A.transpose * A†.transpose * A†) := by
        congr 1
        rw [Matrix.sub_mul (1 : RectMatrix cols cols) (B† * B) A.transpose,
          Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul]
        simp only [Matrix.mul_assoc]
        rw [hAtAtA']
  rw [hterm2, hterm3]
  have hAtAtA' : A.transpose * (A†.transpose * A†) = A† := by
    rw [← Matrix.mul_assoc, hAtAtA]
  have hcross : B† * B * A.transpose * A†.transpose * A† = B† * B * A† := by
    simp only [Matrix.mul_assoc]
    rw [hAtAtA']
  have hterm1 : -B† * (B - A) * A† = -(B† * B * A†) + B† * A * A† := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
    simp only [Matrix.neg_mul]
    abel
  rw [hterm1, hcross]
  abel

/-- Equal-rank Moore--Penrose inverses are Lipschitz with the explicit symmetric maximum of
their squared inverse norms. -/
theorem norm_moorePenrose_sub_le {rows cols : ℕ} (A B : RectMatrix rows cols)
    (hrank : A.rank = B.rank) :
    ‖A† - B†‖ ≤
      3 * max (‖A†‖ ^ 2) (‖B†‖ ^ 2) * ‖A - B‖ := by
  let M := max (‖A†‖ ^ 2) (‖B†‖ ^ 2)
  let d := ‖A - B‖
  have hAM : ‖A†‖ ^ 2 ≤ M := le_max_left _ _
  have hBM : ‖B†‖ ^ 2 ≤ M := le_max_right _ _
  have hABM : ‖A†‖ * ‖B†‖ ≤ M := by
    nlinarith [sq_nonneg (‖A†‖ - ‖B†‖)]
  have hd : 0 ≤ d := norm_nonneg _
  have ht1 : ‖-A† * (A - B) * B†‖ ≤ M * d := by
    calc
      ‖-A† * (A - B) * B†‖ = ‖A† * (A - B) * B†‖ := by
        rw [Matrix.neg_mul, Matrix.neg_mul, norm_neg]
      _ ≤ ‖A†‖ * ‖A - B‖ * ‖B†‖ := l2_opNorm_mul_three _ _ _
      _ = (‖A†‖ * ‖B†‖) * d := by dsimp [d]; ring
      _ ≤ M * d := mul_le_mul_of_nonneg_right hABM hd
  have ht2 :
      ‖A† * A†.transpose * (A - B).transpose *
          ((1 : RectMatrix rows rows) - B * B†)‖ ≤ M * d := by
    calc
      _ ≤ ‖A†‖ * ‖A†.transpose‖ * ‖(A - B).transpose‖ *
          ‖(1 : RectMatrix rows rows) - B * B†‖ := l2_opNorm_mul_four _ _ _ _
      _ = ‖A†‖ * ‖A†‖ * d * ‖(1 : RectMatrix rows rows) - B * B†‖ := by
        rw [l2_opNorm_transpose, l2_opNorm_transpose]
      _ ≤ ‖A†‖ * ‖A†‖ * d * 1 := by
        gcongr
        exact (rangeProjection_norms_le_one B).2
      _ = ‖A†‖ ^ 2 * d := by ring
      _ ≤ M * d := mul_le_mul_of_nonneg_right hAM hd
  have ht3 :
      ‖((1 : RectMatrix cols cols) - A† * A) * (A - B).transpose *
          B†.transpose * B†‖ ≤ M * d := by
    calc
      _ ≤ ‖(1 : RectMatrix cols cols) - A† * A‖ * ‖(A - B).transpose‖ *
          ‖B†.transpose‖ * ‖B†‖ := l2_opNorm_mul_four _ _ _ _
      _ = ‖(1 : RectMatrix cols cols) - A† * A‖ * d * ‖B†‖ * ‖B†‖ := by
        rw [l2_opNorm_transpose, l2_opNorm_transpose]
      _ ≤ 1 * d * ‖B†‖ * ‖B†‖ := by
        gcongr
        exact (rowProjection_norms_le_one A).2
      _ = ‖B†‖ ^ 2 * d := by ring
      _ ≤ M * d := mul_le_mul_of_nonneg_right hBM hd
  rw [moorePenrose_sub_eq B A hrank.symm]
  calc
    _ ≤ ‖-A† * (A - B) * B† +
          A† * A†.transpose * (A - B).transpose *
            ((1 : RectMatrix rows rows) - B * B†)‖ +
        ‖((1 : RectMatrix cols cols) - A† * A) * (A - B).transpose *
            B†.transpose * B†‖ := norm_add_le _ _
    _ ≤ (‖-A† * (A - B) * B†‖ +
          ‖A† * A†.transpose * (A - B).transpose *
            ((1 : RectMatrix rows rows) - B * B†)‖) +
        ‖((1 : RectMatrix cols cols) - A† * A) * (A - B).transpose *
            B†.transpose * B†‖ := by
      gcongr
      exact norm_add_le _ _
    _ ≤ (M * d + M * d) + M * d := add_le_add (add_le_add ht1 ht2) ht3
    _ = 3 * M * d := by ring

/-- A positive lower bound on the last nonzero singular value bounds the pseudoinverse norm. -/
theorem norm_moorePenroseInverse_le_inv {rows cols r : ℕ}
    (A : RectMatrix rows cols) {s : ℝ} (hrank : A.rank = r)
    (hs : 0 < s) (hmargin : s ≤ singularValue A (r - 1)) :
    ‖A†‖ ≤ s⁻¹ := by
  let T := Matrix.toEuclideanLin A
  have hrT : finrank ℝ T.range = r := by
    have h := A.rank_eq_finrank_range_toLin
      (EuclideanSpace.basisFun (Fin rows) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin cols) ℝ).toBasis
    rw [hrank] at h
    exact h.symm
  have hrpos : 0 < r := by
    by_contra hr0
    have hre : r = 0 := Nat.eq_zero_of_not_pos hr0
    have hz : singularValue A (r - 1) = 0 := by
      unfold singularValue
      apply T.singularValues_eq_zero_iff_le_finrank_range.mpr
      rw [hrT, hre]
    linarith
  have hcanon : A† = constructedMP A :=
    isMoorePenroseInverse_unique (moorePenroseInverse_spec A) (constructedMP_spec A)
  have hbound : ‖LinearMap.toContinuousLinearMap (mpLinear T)‖ ≤ s⁻¹ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (le_of_lt (inv_pos.mpr hs))
    intro y
    have hxmem : mpLinear T y ∈ T.kerᗮ :=
      ((LinearEquiv.ofBijective (restrictKerOrth T) (restrictKerOrth_bijective T)).symm
        (T.range.orthogonalProjectionOnto y)).property
    have hlower := singularValues_mul_norm_le_of_mem_ker_orthogonal
      T hrT hrpos (mpLinear T y) hxmem
    have hmarginT : s ≤ T.singularValues (r - 1) := hmargin
    have hsx : s * ‖mpLinear T y‖ ≤ ‖T (mpLinear T y)‖ :=
      (mul_le_mul_of_nonneg_right hmarginT (norm_nonneg _)).trans hlower
    have hTx : T (mpLinear T y) = T.range.starProjection y :=
      DFunLike.congr_fun (comp_mpLinear T) y
    have hproj : ‖T.range.starProjection y‖ ≤ ‖y‖ :=
      T.range.norm_starProjection_apply_le y
    rw [hTx] at hsx
    have hsy : s * ‖mpLinear T y‖ ≤ ‖y‖ := hsx.trans hproj
    rw [inv_mul_eq_div, le_div_iff₀ hs]
    simpa [mul_comm] using hsy
  change ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A†)‖ ≤ s⁻¹
  rw [hcanon, constructedMP, LinearEquiv.apply_symm_apply]
  exact hbound

/-- Equal rank and a common positive singular margin give the moving-range perturbation bound
`3 s⁻² ‖A-B‖`, with no fixed-row-space or fixed-column-space premise. -/
theorem norm_moorePenrose_sub_le_of_singularMargin {rows cols r : ℕ}
    (A B : RectMatrix rows cols) {s : ℝ}
    (hrankA : A.rank = r) (hrankB : B.rank = r) (hs : 0 < s)
    (hmarginA : s ≤ singularValue A (r - 1))
    (hmarginB : s ≤ singularValue B (r - 1)) :
    ‖A† - B†‖ ≤ 3 * s⁻¹ ^ 2 * ‖A - B‖ := by
  have hAinv := norm_moorePenroseInverse_le_inv A hrankA hs hmarginA
  have hBinv := norm_moorePenroseInverse_le_inv B hrankB hs hmarginB
  have hAsq : ‖A†‖ ^ 2 ≤ s⁻¹ ^ 2 := by
    nlinarith [norm_nonneg A†]
  have hBsq : ‖B†‖ ^ 2 ≤ s⁻¹ ^ 2 := by
    nlinarith [norm_nonneg B†]
  calc
    ‖A† - B†‖ ≤ 3 * max (‖A†‖ ^ 2) (‖B†‖ ^ 2) * ‖A - B‖ :=
      norm_moorePenrose_sub_le A B (hrankA.trans hrankB.symm)
    _ ≤ 3 * s⁻¹ ^ 2 * ‖A - B‖ := by
      gcongr
      exact max_le hAsq hBsq

end CausalSmith.Substrate.CollisionSafeSpectralLaw
