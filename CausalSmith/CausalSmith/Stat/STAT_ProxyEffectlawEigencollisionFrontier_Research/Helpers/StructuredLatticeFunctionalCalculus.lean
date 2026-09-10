import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.StructuredLatticePopulation
import CausalSmith.Substrate.CollisionSafeSpectralLaw.Composition
import CausalSmith.Substrate.CollisionSafeSpectralLaw.SharpComposition

/-! # Collision-safe functional calculus for selected structured-lattice tuples -/

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

noncomputable section

open scoped Matrix.Norms.L2Operator
open CausalSmith.Substrate.CollisionSafeSpectralLaw

/-- Extending an operator on an orthonormal signal frame by the identity on its orthogonal
complement has norm at most the larger of the signal-block norm and one. -/
lemma SignalBasis.blockExtension_norm_le_max
    {dx k : ℕ} (V : SignalBasis dx k) (C : RectMatrix k k) :
    ‖V.V * C * V.V.transpose + (1 - V.V * V.V.transpose)‖ ≤ max ‖C‖ 1 := by
  let T : Euc k →ₗ[ℝ] Euc dx := Matrix.toEuclideanLin V.V
  let S : Euc k →ₗ[ℝ] Euc k := Matrix.toEuclideanLin C
  have hTadj : LinearMap.adjoint T = Matrix.toEuclideanLin V.V.transpose := by
    dsimp [T]
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    rfl
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  let y : Euc k := LinearMap.adjoint T x
  let p : Euc dx := T y
  let r : Euc dx := x - p
  let z : Euc dx := T (S y)
  have hTT : LinearMap.adjoint T ∘ₗ T = LinearMap.id := by
    rw [hTadj]
    ext u
    simp [T, Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec,
      V.transpose_mul_self]
  have hrnormal : LinearMap.adjoint T r = 0 := by
    have hy : LinearMap.adjoint T (T y) = y := by
      exact LinearMap.congr_fun hTT y
    simp [r, p, y, hy]
  have hpr : inner ℝ p r = 0 := by
    rw [show p = T y by rfl, ← LinearMap.adjoint_inner_right, hrnormal]
    simp
  have hzr : inner ℝ z r = 0 := by
    rw [show z = T (S y) by rfl, ← LinearMap.adjoint_inner_right, hrnormal]
    simp
  have hTnorm (u : Euc k) : ‖T u‖ = ‖u‖ := by
    exact (signalBasisLinearIsometry V).norm_map u
  have hdecomp :
      Matrix.toEuclideanLin
          (V.V * C * V.V.transpose + (1 - V.V * V.V.transpose)) x = z + r := by
    ext i
    simp [z, r, p, y, T, S, hTadj, Matrix.toEuclideanLin_apply,
      Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.sub_mulVec,
      Matrix.one_mulVec]
  change ‖Matrix.toEuclideanLin
      (V.V * C * V.V.transpose + (1 - V.V * V.V.transpose)) x‖ ≤ _
  rw [hdecomp]
  have hxsum : p + r = x := by simp [r]
  have hxSq := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero p r hpr
  rw [hxsum] at hxSq
  have hxSq' : ‖x‖ ^ 2 = ‖p‖ ^ 2 + ‖r‖ ^ 2 := by
    simpa [pow_two] using hxSq
  have hzSq := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero z r hzr
  have hzSq' : ‖z + r‖ ^ 2 = ‖z‖ ^ 2 + ‖r‖ ^ 2 := by
    simpa [pow_two] using hzSq
  have hzle : ‖z‖ ≤ max ‖C‖ 1 * ‖y‖ := by
    rw [show ‖z‖ = ‖S y‖ by simp [z, hTnorm]]
    calc
      ‖S y‖ ≤ ‖C‖ * ‖y‖ := Matrix.l2_opNorm_mulVec C y
      _ ≤ max ‖C‖ 1 * ‖y‖ := by gcongr; exact le_max_left _ _
  have hM1 : 1 ≤ max ‖C‖ 1 := le_max_right _ _
  have hM0 : 0 ≤ max ‖C‖ 1 := le_trans zero_le_one hM1
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM0 (norm_nonneg _))).mp
  rw [hzSq']
  have hzSqLe : ‖z‖ ^ 2 ≤ (max ‖C‖ 1) ^ 2 * ‖y‖ ^ 2 := by
    simpa [mul_pow] using (sq_le_sq₀ (norm_nonneg z)
      (mul_nonneg hM0 (norm_nonneg y))).2 hzle
  have hrSqLe : ‖r‖ ^ 2 ≤ (max ‖C‖ 1) ^ 2 * ‖r‖ ^ 2 := by
    nlinarith [sq_nonneg ‖r‖, sq_nonneg (max ‖C‖ 1 - 1)]
  calc
    ‖z‖ ^ 2 + ‖r‖ ^ 2 ≤
        (max ‖C‖ 1) ^ 2 * ‖y‖ ^ 2 +
          (max ‖C‖ 1) ^ 2 * ‖r‖ ^ 2 := add_le_add hzSqLe hrSqLe
    _ = (max ‖C‖ 1) ^ 2 * ‖x‖ ^ 2 := by
      have hpNorm : ‖p‖ = ‖y‖ := by exact hTnorm y
      rw [← hpNorm, ← mul_add, ← hxSq']
    _ = (max ‖C‖ 1 * ‖x‖) ^ 2 := by ring

private lemma orthonormalBasis_basisMatrix_norm_le_one {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ (Euc n)) : ‖basisMatrix b.toBasis‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  have haction : Matrix.toEuclideanLin (basisMatrix b.toBasis) x = b.repr.symm x := by
    apply PiLp.ext
    intro i
    have h := congrArg (fun y : Euc n => y.ofLp i) (b.sum_repr_symm x)
    simpa [basisMatrix, Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct,
      Finset.sum_apply, mul_comm] using h
  change ‖Matrix.toEuclideanLin (basisMatrix b.toBasis) x‖ ≤ _
  rw [haction, b.repr.symm.norm_map, one_mul]

private lemma orthonormalBasis_basisInvMatrix_norm_le_one {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ (Euc n)) : ‖basisInvMatrix b.toBasis‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  have haction : Matrix.toEuclideanLin (basisInvMatrix b.toBasis) x = b.repr x := by
    apply PiLp.ext
    intro i
    rw [b.repr_apply_apply]
    have hcoord (j : Fin n) :
        b.toBasis.repr (EuclideanSpace.single j (1 : ℝ)) i = (b i).ofLp j := by
      rw [b.coe_toBasis_repr_apply, b.repr_apply_apply]
      simp [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    simp [basisInvMatrix, Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct,
      PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mul_comm, hcoord]
  change ‖Matrix.toEuclideanLin (basisInvMatrix b.toBasis) x‖ ≤ _
  rw [haction, b.repr.norm_map, one_mul]

/-- The ambient diagonalizer induced by a thin signal factorization has condition number at
most the product of the sharp signal/complement extension bounds. -/
lemma ThinSignalFactorization.realDiagonalization_conditionNumber_le_max
    {dx k : ℕ} [Nonempty (Fin k)] {B : RectMatrix dx k}
    (F : ThinSignalFactorization B) (tau : Fin k → ℝ) :
    (F.realDiagonalization tau).conditionNumber ≤
      max ‖F.coordInv‖ 1 * max ‖F.coord‖ 1 := by
  let b := F.V.ambientExtension.basis
  have hBasisEq : (F.realDiagonalization tau).basis =
      F.forward * basisMatrix b.toBasis := by
    ext i j
    change (F.eigenbasis j).ofLp i = _
    rw [ThinSignalFactorization.eigenbasis, Module.Basis.map_apply]
    dsimp [b]
    simp [ThinSignalFactorization.linearEquiv, Matrix.toEuclideanLin_apply,
      basisMatrix, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have hInvEq : (F.realDiagonalization tau).basisInv =
      basisInvMatrix b.toBasis * F.backward := by
    ext i j
    change F.eigenbasis.repr (EuclideanSpace.single j (1 : ℝ)) i = _
    rw [ThinSignalFactorization.eigenbasis, Module.Basis.map_repr]
    change b.toBasis.repr
      (Matrix.toEuclideanLin F.backward (EuclideanSpace.single j (1 : ℝ))) i = _
    rw [b.coe_toBasis_repr_apply]
    simp [basisInvMatrix, Matrix.mul_apply, Matrix.toEuclideanLin_apply,
      Matrix.mulVec, dotProduct, b.repr_apply_apply,
      PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mul_comm]
  have hCoordInvTranspose : ‖F.coordInv.transpose‖ = ‖F.coordInv‖ := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.l2_opNorm_conjTranspose]
  have hCoordTranspose : ‖F.coord.transpose‖ = ‖F.coord‖ := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.l2_opNorm_conjTranspose]
  have hForward : ‖F.forward‖ ≤ max ‖F.coordInv‖ 1 := by
    simpa [ThinSignalFactorization.forward, hCoordInvTranspose] using
      F.V.blockExtension_norm_le_max F.coordInv.transpose
  have hBackward : ‖F.backward‖ ≤ max ‖F.coord‖ 1 := by
    simpa [ThinSignalFactorization.backward, hCoordTranspose] using
      F.V.blockExtension_norm_le_max F.coord.transpose
  rw [RealDiagonalization.conditionNumber, hBasisEq, hInvEq]
  calc
    ‖F.forward * basisMatrix b.toBasis‖ *
        ‖basisInvMatrix b.toBasis * F.backward‖ ≤
      (‖F.forward‖ * ‖basisMatrix b.toBasis‖) *
        (‖basisInvMatrix b.toBasis‖ * ‖F.backward‖) := by
          gcongr <;> exact Matrix.l2_opNorm_mul _ _
    _ ≤ (max ‖F.coordInv‖ 1 * 1) *
        (1 * max ‖F.coord‖ 1) := by
          gcongr
          · exact orthonormalBasis_basisMatrix_norm_le_one b
          · exact orthonormalBasis_basisInvMatrix_norm_le_one b
    _ = _ := by ring

/-- Regard a well-conditioned structured tuple as a thin signal factorization of its
reconstructed feature matrix. -/
noncomputable def structuredLatticeThinSignalFactorization
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (theta : StructuredLatticePoint k dx (effectRadius dz L sigma0))
    (htheta : theta.WellFormed (dz := dz) (n := n) (L := L)
      (pi0 := pi0) (sigma0 := sigma0))
    (hsigma : 0 < sigma0) :
    ThinSignalFactorization (theta.V * theta.R.transpose) := by
  let V : SignalBasis dx k := ⟨theta.V, htheta.2.2.1⟩
  have hRpos : 0 < signalMinSingular theta.R :=
    (by positivity : 0 < sigma0 / 2).trans_le htheta.2.2.2.2.1
  have hdet := matrix_det_isUnit_of_signalMinSingular_pos theta.R hRpos
  refine
    { V := V
      coord := theta.R.transpose
      coordInv := theta.R⁻¹.transpose
      factor := rfl
      coord_mul_inv := ?_
      inv_mul_coord := ?_ }
  · rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul theta.R hdet,
      Matrix.transpose_one]
  · rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv theta.R hdet,
      Matrix.transpose_one]

/-- Ambient diagonalization of the selected candidate operator, including zero on the
orthogonal complement of the reconstructed signal space. -/
noncomputable def structuredLatticeRealDiagonalization
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (theta : StructuredLatticePoint k dx (effectRadius dz L sigma0))
    (htheta : theta.WellFormed (dz := dz) (n := n) (L := L)
      (pi0 := pi0) (sigma0 := sigma0))
    (hsigma : 0 < sigma0) [Nonempty (Fin k)] :
    RealDiagonalization (structuredCandidateOperator theta) := by
  let F := structuredLatticeThinSignalFactorization theta htheta hsigma
  have hop : F.factorOperator theta.effect = structuredCandidateOperator theta := by
    simp only [F, structuredLatticeThinSignalFactorization,
      ThinSignalFactorization.factorOperator, structuredCandidateOperator]
    rw [Matrix.transpose_transpose, Matrix.transpose_transpose]
  rw [← hop]
  exact F.realDiagonalization theta.effect

/-- Under the paper's parameter domain, every selected structured-lattice diagonalizer has
condition number at most the frozen sharp value `4 * sqrt k * L / sigma0`. -/
lemma structuredLatticeRealDiagonalization_conditionNumber_le
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (theta : StructuredLatticePoint k dx (effectRadius dz L sigma0))
    (htheta : theta.WellFormed (dz := dz) (n := n) (L := L)
      (pi0 := pi0) (sigma0 := sigma0))
    (hk : 2 ≤ k) (hL : 1 ≤ L) (hsigma : 0 < sigma0) (hsigmaMax : sigma0 ≤ 1)
    [Nonempty (Fin k)] :
    (structuredLatticeRealDiagonalization theta htheta hsigma).conditionNumber ≤
      4 * Real.sqrt k * L / sigma0 := by
  let F := structuredLatticeThinSignalFactorization theta htheta hsigma
  have hraw := F.realDiagonalization_conditionNumber_le_max theta.effect
  have hInv := matrix_inv_norm_le_of_signalMinSingular theta.R
    (by positivity : 0 < sigma0 / 2) htheta.2.2.2.2.1
  have hInv' : ‖theta.R⁻¹‖ ≤ 2 / sigma0 := by
    have h := hInv
    change ‖theta.R⁻¹‖ ≤ 1 / (sigma0 / 2) at h
    convert h using 1 <;> field_simp
  have hOneInv : 1 ≤ 2 / sigma0 := by
    apply (le_div_iff₀ hsigma).2
    linarith
  have hk1 : (1 : ℝ) ≤ Real.sqrt k := by
    rw [Real.one_le_sqrt]
    exact_mod_cast (show 1 ≤ k by omega)
  have hOneR : 1 ≤ 2 * Real.sqrt k * L := by nlinarith [Real.sqrt_nonneg k]
  have hRnorm : ‖theta.R‖ ≤ 2 * Real.sqrt k * L := by
    change ‖matrixCLM theta.R‖ ≤ _
    exact htheta.2.2.2.2.2.1
  have hCoordInv : max ‖F.coordInv‖ 1 ≤ 2 / sigma0 := by
    apply max_le
    · simpa [F, structuredLatticeThinSignalFactorization,
        ← Matrix.conjTranspose_eq_transpose_of_trivial,
        Matrix.l2_opNorm_conjTranspose] using hInv'
    · exact hOneInv
  have hCoord : max ‖F.coord‖ 1 ≤ 2 * Real.sqrt k * L := by
    apply max_le
    · simpa [F, structuredLatticeThinSignalFactorization,
        ← Matrix.conjTranspose_eq_transpose_of_trivial,
        Matrix.l2_opNorm_conjTranspose] using hRnorm
    · exact hOneR
  change (F.realDiagonalization theta.effect).conditionNumber ≤ _
  calc
    _ ≤ max ‖F.coordInv‖ 1 * max ‖F.coord‖ 1 := hraw
    _ ≤ (2 / sigma0) * (2 * Real.sqrt k * L) := by gcongr
    _ = 4 * Real.sqrt k * L / sigma0 := by ring

/-- The corrected right anchor changes the observed anchor only inside the selected signal
space and makes the structured feature transpose evaluate exactly to the all-ones vector. -/
noncomputable def structuredCorrectedAnchor
    {k dx : ℕ} (thetaV : RectMatrix dx k) (thetaR : RectMatrix k k) : Euc dx :=
  WithLp.toLp 2 (firstBasis dx) +
    Matrix.toEuclideanLin (thetaV * thetaR⁻¹)
      (WithLp.toLp 2 ((fun _ => (1 : ℝ)) -
        Matrix.mulVec (thetaR * thetaV.transpose) (firstBasis dx)))

lemma structuredFeature_transpose_correctedAnchor
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (theta : StructuredLatticePoint k dx (effectRadius dz L sigma0))
    (htheta : theta.WellFormed (dz := dz) (n := n) (L := L)
      (pi0 := pi0) (sigma0 := sigma0))
    (hsigma : 0 < sigma0) :
    Matrix.mulVec (theta.V * theta.R.transpose).transpose
        (structuredCorrectedAnchor theta.V theta.R).ofLp = fun _ => 1 := by
  let V : SignalBasis dx k := ⟨theta.V, htheta.2.2.1⟩
  have hRpos : 0 < signalMinSingular theta.R :=
    (by positivity : 0 < sigma0 / 2).trans_le htheta.2.2.2.2.1
  have hdet := matrix_det_isUnit_of_signalMinSingular_pos theta.R hRpos
  have hgram : theta.V.transpose * theta.V = (1 : RectMatrix k k) :=
    V.transpose_mul_self
  have hcorr : (theta.V * theta.R.transpose).transpose *
      (theta.V * theta.R⁻¹) = (1 : RectMatrix k k) := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc,
      ← Matrix.mul_assoc theta.V.transpose, hgram, Matrix.one_mul,
      Matrix.mul_nonsing_inv theta.R hdet]
  ext u
  let res : Fin k → ℝ := (fun _ => (1 : ℝ)) -
    Matrix.mulVec (theta.R * theta.V.transpose) (firstBasis dx)
  have hcvec : Matrix.mulVec (theta.V * theta.R.transpose).transpose
      (Matrix.mulVec (theta.V * theta.R⁻¹) res) = res := by
    rw [Matrix.mulVec_mulVec, hcorr, Matrix.one_mulVec]
  change Matrix.mulVec (theta.V * theta.R.transpose).transpose
      (firstBasis dx + Matrix.mulVec (theta.V * theta.R⁻¹)
        ((fun _ => (1 : ℝ)) -
          Matrix.mulVec (theta.R * theta.V.transpose) (firstBasis dx))) u = 1
  rw [Matrix.mulVec_add, show ((fun _ => (1 : ℝ)) -
      Matrix.mulVec (theta.R * theta.V.transpose) (firstBasis dx)) = res from rfl,
    hcvec]
  simp [res]

-- keep: reusable corrected-anchor stability API for alternate structured-lattice estimators
/-- The corrected-anchor displacement is controlled by the selected anchor residual and the
inverse coordinate margin, with no eigengap condition. -/
lemma structuredCorrectedAnchor_sub_norm_le
    {k dx dz n : ℕ} {L pi0 sigma0 δ : ℝ}
    (theta : StructuredLatticePoint k dx (effectRadius dz L sigma0))
    (htheta : theta.WellFormed (dz := dz) (n := n) (L := L)
      (pi0 := pi0) (sigma0 := sigma0))
    (hsigma : 0 < sigma0)
    (hanchor : Real.sqrt (∑ u, ((∑ v, theta.R u v *
      (∑ i, theta.V i v * firstBasis dx i)) - 1) ^ 2) ≤ δ) :
    ‖structuredCorrectedAnchor theta.V theta.R -
      WithLp.toLp 2 (firstBasis dx)‖ ≤ 2 / sigma0 * δ := by
  let V : SignalBasis dx k := ⟨theta.V, htheta.2.2.1⟩
  have hInv := matrix_inv_norm_le_of_signalMinSingular theta.R
    (by positivity : 0 < sigma0 / 2) htheta.2.2.2.2.1
  have hres : ‖(WithLp.toLp 2 ((fun _ => (1 : ℝ)) -
      Matrix.mulVec (theta.R * theta.V.transpose) (firstBasis dx)) : Euc k)‖ ≤ δ := by
    have hforward : ‖(WithLp.toLp 2
        (Matrix.mulVec (theta.R * theta.V.transpose) (firstBasis dx) -
          (fun _ => (1 : ℝ))) : Euc k)‖ ≤ δ := by
      have heq (u : Fin k) :
          Matrix.mulVec (theta.R * theta.V.transpose) (firstBasis dx) u =
            ∑ v, theta.R u v * (∑ i, theta.V i v * firstBasis dx i) := by
        rw [← Matrix.mulVec_mulVec]
        rfl
      rw [EuclideanSpace.norm_eq]
      simpa [Real.norm_eq_abs, sq_abs, heq] using hanchor
    calc
      _ = ‖(WithLp.toLp 2
          (Matrix.mulVec (theta.R * theta.V.transpose) (firstBasis dx) -
            (fun _ => (1 : ℝ))) : Euc k)‖ := by
        rw [show (WithLp.toLp 2 ((fun _ => (1 : ℝ)) -
            Matrix.mulVec (theta.R * theta.V.transpose) (firstBasis dx)) : Euc k) =
            -(WithLp.toLp 2
              (Matrix.mulVec (theta.R * theta.V.transpose) (firstBasis dx) -
                (fun _ => (1 : ℝ))) : Euc k) by
          apply PiLp.ext
          intro u
          simp, norm_neg]
      _ ≤ δ := hforward
  rw [structuredCorrectedAnchor, add_sub_cancel_left]
  have hInv2 : ‖theta.R⁻¹‖ ≤ 2 / sigma0 := by
    have hInv' : ‖theta.R⁻¹‖ ≤ 1 / (sigma0 / 2) := by exact hInv
    convert hInv' using 1 <;> field_simp
  calc
    _ ≤ ‖matrixCLM (theta.V * theta.R⁻¹)‖ *
        ‖(WithLp.toLp 2 ((fun _ => (1 : ℝ)) -
          Matrix.mulVec (theta.R * theta.V.transpose) (firstBasis dx)) : Euc k)‖ :=
      (matrixCLM (theta.V * theta.R⁻¹)).le_opNorm _
    _ ≤ (1 * (2 / sigma0)) * δ := by
      gcongr
      · exact (Matrix.l2_opNorm_mul theta.V theta.R⁻¹).trans <| by
          gcongr
          · exact V.matrixCLM_norm_le_one
    _ = 2 / sigma0 * δ := by ring

/-- The selected labelled atomic law is represented exactly by its ambient collision-safe
functional calculus at the reconstructed mean and corrected anchor. -/
-- keep: reusable representation certificate connecting structured lattices to atomic laws
lemma structuredLattice_represents_effectLaw
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (theta : StructuredLatticePoint k dx (effectRadius dz L sigma0))
    (htheta : theta.WellFormed (dz := dz) (n := n) (L := L)
      (pi0 := pi0) (sigma0 := sigma0))
    (hsigma : 0 < sigma0) [Nonempty (Fin k)] :
    RepresentsAtomicLaw (structuredLatticeRealDiagonalization theta htheta hsigma)
      (Matrix.toEuclideanLin (theta.V * theta.R.transpose)
        (WithLp.toLp 2 theta.weight))
      (structuredCorrectedAnchor theta.V theta.R)
      (GapFreeModulusBridge.asNeutral
        ({ weight := theta.weight, atom := theta.effect } : AtomicLaw k
          (effectRadius dz L sigma0))) := by
  let F := structuredLatticeThinSignalFactorization theta htheta hsigma
  apply AmbientOperatorBridge.represents_raw_quotientLaw
    (structuredLatticeRealDiagonalization theta htheta hsigma)
    (theta.V * theta.R.transpose) theta.weight theta.effect
  · rfl
  · exact structuredFeature_transpose_correctedAnchor theta htheta hsigma
  · intro f hf0
    change (F.realDiagonalization theta.effect).applyFunction f = _
    rw [realDiagonalization_applyFunction_moorePenrose F theta.effect f hf0]
  · apply AmbientOperatorBridge.moorePenroseInverse_mul_eq_one_of_injective
    intro x y hxy
    have hRpos : 0 < signalMinSingular theta.R :=
      (by positivity : 0 < sigma0 / 2).trans_le htheta.2.2.2.2.1
    have hdet := matrix_det_isUnit_of_signalMinSingular_pos theta.R hRpos
    let V : SignalBasis dx k := ⟨theta.V, htheta.2.2.1⟩
    have hgram : theta.V.transpose * theta.V = (1 : RectMatrix k k) :=
      V.transpose_mul_self
    have hxRt : Matrix.toEuclideanLin theta.R.transpose x =
        Matrix.toEuclideanLin theta.R.transpose y := by
      have hx' := congrArg
        (fun z : Euc dx => Matrix.toEuclideanLin theta.V.transpose z) hxy
      have hmat : theta.V.transpose * (theta.V * theta.R.transpose) =
          theta.R.transpose := by
        rw [← Matrix.mul_assoc, hgram, Matrix.one_mul]
      simpa [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec, hmat] using hx'
    have hx' := congrArg
      (fun y : Euc k => Matrix.toEuclideanLin theta.R⁻¹.transpose y) hxRt
    have hinv : theta.R⁻¹.transpose * theta.R.transpose = (1 : RectMatrix k k) := by
      rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv theta.R hdet,
        Matrix.transpose_one]
    simpa [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec, hinv] using hx'

/-- A signal frame and a square coordinate factor with a positive singular margin determine
the thin factorization used for the exact population tuple. -/
noncomputable def signalTupleThinFactorization
    {k dx : ℕ} (V : SignalBasis dx k) (R : RectMatrix k k)
    {s : ℝ} (hs : 0 < s) (hR : s ≤ signalMinSingular R) :
    ThinSignalFactorization (V.V * R.transpose) := by
  have hdet := matrix_det_isUnit_of_signalMinSingular_pos R (hs.trans_le hR)
  refine
    { V := V
      coord := R.transpose
      coordInv := R⁻¹.transpose
      factor := rfl
      coord_mul_inv := ?_
      inv_mul_coord := ?_ }
  · rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul R hdet, Matrix.transpose_one]
  · rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv R hdet, Matrix.transpose_one]

/-- Exact ambient real diagonalization of a population signal tuple. -/
noncomputable def signalTupleRealDiagonalization
    {k dx : ℕ} (V : SignalBasis dx k) (R : RectMatrix k k) (tau : Fin k → ℝ)
    {s : ℝ} (hs : 0 < s) (hR : s ≤ signalMinSingular R) [Nonempty (Fin k)] :
    RealDiagonalization (V.V * R⁻¹ * Matrix.diagonal tau * R * V.V.transpose) := by
  let F := signalTupleThinFactorization V R hs hR
  have hop : F.factorOperator tau =
      V.V * R⁻¹ * Matrix.diagonal tau * R * V.V.transpose := by
    simp only [F, signalTupleThinFactorization, ThinSignalFactorization.factorOperator]
    rw [Matrix.transpose_transpose, Matrix.transpose_transpose]
  rw [← hop]
  exact F.realDiagonalization tau

/-- The exact population tuple has condition number at most the same frozen sharp value used
for every selected lattice point. -/
lemma signalTupleRealDiagonalization_conditionNumber_le
    {k dx : ℕ} (V : SignalBasis dx k) (R : RectMatrix k k) (tau : Fin k → ℝ)
    {L sigma0 : ℝ} (hk : 2 ≤ k) (hL : 1 ≤ L) (hsigma : 0 < sigma0)
    (hsigmaMax : sigma0 ≤ 1) (hRmin : sigma0 ≤ signalMinSingular R)
    (hRnorm : ‖matrixCLM R‖ ≤ Real.sqrt k * L) [Nonempty (Fin k)] :
    (signalTupleRealDiagonalization V R tau hsigma hRmin).conditionNumber ≤
      4 * Real.sqrt k * L / sigma0 := by
  let F := signalTupleThinFactorization V R hsigma hRmin
  have hraw := F.realDiagonalization_conditionNumber_le_max tau
  have hInv := matrix_inv_norm_le_of_signalMinSingular R hsigma hRmin
  have hInv' : ‖R⁻¹‖ ≤ 1 / sigma0 := by
    change ‖matrixCLM R⁻¹‖ ≤ _
    exact hInv
  have hOneInv : 1 ≤ 2 / sigma0 := by
    apply (le_div_iff₀ hsigma).2
    linarith
  have hk1 : (1 : ℝ) ≤ Real.sqrt k := by
    rw [Real.one_le_sqrt]
    exact_mod_cast (show 1 ≤ k by omega)
  have hOneR : 1 ≤ 2 * Real.sqrt k * L := by nlinarith [Real.sqrt_nonneg k]
  have hRnorm' : ‖R‖ ≤ Real.sqrt k * L := by
    change ‖matrixCLM R‖ ≤ _
    exact hRnorm
  have hCoordInv : max ‖F.coordInv‖ 1 ≤ 2 / sigma0 := by
    apply max_le
    · calc
        ‖F.coordInv‖ = ‖R⁻¹‖ := by
          simp [F, signalTupleThinFactorization,
            ← Matrix.conjTranspose_eq_transpose_of_trivial,
            Matrix.l2_opNorm_conjTranspose]
        _ ≤ 1 / sigma0 := hInv'
        _ ≤ 2 / sigma0 := by
          apply (div_le_div_iff_of_pos_right hsigma).2
          norm_num
    · exact hOneInv
  have hCoord : max ‖F.coord‖ 1 ≤ 2 * Real.sqrt k * L := by
    apply max_le
    · calc
        ‖F.coord‖ = ‖R‖ := by
          simp [F, signalTupleThinFactorization,
            ← Matrix.conjTranspose_eq_transpose_of_trivial,
            Matrix.l2_opNorm_conjTranspose]
        _ ≤ Real.sqrt k * L := hRnorm'
        _ ≤ 2 * Real.sqrt k * L := by
          nlinarith [Real.sqrt_nonneg k]
    · exact hOneR
  change (F.realDiagonalization tau).conditionNumber ≤ _
  calc
    _ ≤ max ‖F.coordInv‖ 1 * max ‖F.coord‖ 1 := hraw
    _ ≤ (2 / sigma0) * (2 * Real.sqrt k * L) := by gcongr
    _ = 4 * Real.sqrt k * L / sigma0 := by ring

/-- Support membership of the signal atoms bounds the full ambient spectrum, including the
zero eigenvalues on the orthogonal complement. -/
lemma signalTupleRealDiagonalization_spectrumBound
    {k dx : ℕ} (V : SignalBasis dx k) (R : RectMatrix k k) (tau : Fin k → ℝ)
    {s radius : ℝ} (hs : 0 < s) (hR : s ≤ signalMinSingular R)
    (hradius : 0 ≤ radius) (htau : ∀ u, tau u ∈ Set.Icc (-radius) radius)
    [Nonempty (Fin k)] :
    (signalTupleRealDiagonalization V R tau hs hR).SpectrumBound radius := by
  intro i
  change |ambientEigenvalue V tau i| ≤ radius
  by_cases hi : i ∈ Set.range V.ambientExtension.signalIndex
  · obtain ⟨u, rfl⟩ := hi
    rw [ambientEigenvalue_signal]
    exact (abs_le).2 (htau u)
  · rw [ambientEigenvalue_nonsignal V tau i hi, abs_zero]
    exact hradius

/-- Every selected structured-lattice diagonalizer has its full ambient spectrum in the
prescribed effect interval. -/
lemma structuredLatticeRealDiagonalization_spectrumBound
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (theta : StructuredLatticePoint k dx (effectRadius dz L sigma0))
    (htheta : theta.WellFormed (dz := dz) (n := n) (L := L)
      (pi0 := pi0) (sigma0 := sigma0))
    (hsigma : 0 < sigma0) (hradius : 0 ≤ effectRadius dz L sigma0)
    [Nonempty (Fin k)] :
    (structuredLatticeRealDiagonalization theta htheta hsigma).SpectrumBound
      (effectRadius dz L sigma0) := by
  intro i
  change |ambientEigenvalue
      (structuredLatticeThinSignalFactorization theta htheta hsigma).V theta.effect i| ≤ _
  by_cases hi : i ∈ Set.range
      (structuredLatticeThinSignalFactorization theta htheta hsigma).V.ambientExtension.signalIndex
  · obtain ⟨u, rfl⟩ := hi
    rw [ambientEigenvalue_signal]
    exact (abs_le).2 (htheta.2.2.2.2.2.2.2 u).1
  · rw [ambientEigenvalue_nonsignal _ _ i hi, abs_zero]
    exact hradius

/-- The exact population tuple represents its labelled atomic law at the factorized mean and
the uncorrected first-coordinate anchor. -/
lemma signalTuple_represents_atomicLaw
    {k dx : ℕ} (V : SignalBasis dx k) (R : RectMatrix k k) (p tau : Fin k → ℝ)
    {s : ℝ} (hs : 0 < s) (hR : s ≤ signalMinSingular R)
    (hanchor : Matrix.mulVec (R * V.V.transpose) (firstBasis dx) = fun _ => 1)
    [Nonempty (Fin k)] :
    RepresentsAtomicLaw (signalTupleRealDiagonalization V R tau hs hR)
      (Matrix.toEuclideanLin (V.V * R.transpose) (WithLp.toLp 2 p))
      (WithLp.toLp 2 (firstBasis dx))
      ({ weight := p, atom := tau } :
        CausalSmith.Substrate.CollisionSafeSpectralLaw.AtomicLaw (Fin k)) := by
  let F := signalTupleThinFactorization V R hs hR
  apply AmbientOperatorBridge.represents_raw_quotientLaw
    (signalTupleRealDiagonalization V R tau hs hR)
    (V.V * R.transpose) p tau
  · rfl
  · simpa [Matrix.transpose_mul] using hanchor
  · intro f hf0
    change (F.realDiagonalization tau).applyFunction f = _
    rw [realDiagonalization_applyFunction_moorePenrose F tau f hf0]
  · apply AmbientOperatorBridge.moorePenroseInverse_mul_eq_one_of_injective
    intro x y hxy
    have hdet := matrix_det_isUnit_of_signalMinSingular_pos R (hs.trans_le hR)
    have hgram : V.V.transpose * V.V = (1 : RectMatrix k k) := V.transpose_mul_self
    have hxRt : Matrix.toEuclideanLin R.transpose x =
        Matrix.toEuclideanLin R.transpose y := by
      have hx' := congrArg
        (fun z : Euc dx => Matrix.toEuclideanLin V.V.transpose z) hxy
      have hmat : V.V.transpose * (V.V * R.transpose) = R.transpose := by
        rw [← Matrix.mul_assoc, hgram, Matrix.one_mul]
      simpa [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec, hmat] using hx'
    have hx' := congrArg
      (fun z : Euc k => Matrix.toEuclideanLin R⁻¹.transpose z) hxRt
    have hinv : R⁻¹.transpose * R.transpose = (1 : RectMatrix k k) := by
      rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv R hdet, Matrix.transpose_one]
    simpa [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec, hinv] using hx'

private lemma structuredLattice_uncorrectedAnchor_error_eq
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (theta : StructuredLatticePoint k dx (effectRadius dz L sigma0))
    (htheta : theta.WellFormed (dz := dz) (n := n) (L := L)
      (pi0 := pi0) (sigma0 := sigma0))
    (hsigma : 0 < sigma0) [Nonempty (Fin k)]
    (f : ℝ → ℝ) (hf0 : f 0 = 0) :
    ({ weight := theta.weight, atom := theta.effect } :
        CausalSmith.Substrate.CollisionSafeSpectralLaw.AtomicLaw (Fin k)).integral f -
      anchorEval
        (Matrix.toEuclideanLin (theta.V * theta.R.transpose)
          (WithLp.toLp 2 theta.weight))
        (WithLp.toLp 2 (firstBasis dx))
        ((structuredLatticeRealDiagonalization theta htheta hsigma).applyFunction f) =
      ∑ u, theta.weight u * f (theta.effect u) *
        (1 - Matrix.mulVec (theta.R * theta.V.transpose) (firstBasis dx) u) := by
  let F := structuredLatticeThinSignalFactorization theta htheta hsigma
  have hdet := matrix_det_isUnit_of_signalMinSingular_pos theta.R
    ((by positivity : 0 < sigma0 / 2).trans_le htheta.2.2.2.2.1)
  have hgram : theta.V.transpose * theta.V = (1 : RectMatrix k k) :=
    (show SignalBasis dx k from ⟨theta.V, htheta.2.2.1⟩).transpose_mul_self
  change _ - anchorEval _ _ ((F.realDiagonalization theta.effect).applyFunction f) = _
  rw [realDiagonalization_applyFunction F theta.effect f hf0]
  unfold CausalSmith.Substrate.CollisionSafeSpectralLaw.AtomicLaw.integral anchorEval
  simp only [F, structuredLatticeThinSignalFactorization,
    ThinSignalFactorization.factorOperator, Matrix.transpose_transpose]
  have hcancel : theta.R * theta.R⁻¹ = (1 : RectMatrix k k) :=
    Matrix.mul_nonsing_inv theta.R hdet
  let VB : SignalBasis dx k := ⟨theta.V, htheta.2.2.1⟩
  let a : Euc k := WithLp.toLp 2 (Matrix.mulVec theta.R.transpose theta.weight)
  let q : Fin k → ℝ := Matrix.mulVec (theta.R * theta.V.transpose) (firstBasis dx)
  let b : Euc k := WithLp.toLp 2 (Matrix.mulVec theta.R⁻¹
    (Matrix.mulVec (Matrix.diagonal (f ∘ theta.effect)) q))
  have hleft : Matrix.toEuclideanLin (theta.V * theta.R.transpose)
      (WithLp.toLp 2 theta.weight) = Matrix.toEuclideanLin theta.V a := by
    apply PiLp.ext
    intro i
    simp [a, Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec]
  have hright : CausalSmith.Substrate.CollisionSafeSpectralLaw.matrixCLM
      (theta.V * theta.R⁻¹ * Matrix.diagonal (f ∘ theta.effect) * theta.R *
        theta.V.transpose) (WithLp.toLp 2 (firstBasis dx)) =
      Matrix.toEuclideanLin theta.V b := by
    apply PiLp.ext
    intro i
    simp [b, q, CausalSmith.Substrate.CollisionSafeSpectralLaw.matrixCLM,
      Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec]
  have hVinner : inner ℝ (Matrix.toEuclideanLin theta.V a)
      (Matrix.toEuclideanLin theta.V b) = inner ℝ a b := by
    exact (signalBasisLinearIsometry VB).inner_map_map a b
  rw [hleft, hright]
  change (∑ x, theta.weight x * f (theta.effect x)) -
      inner ℝ (Matrix.toEuclideanLin theta.V a)
        (Matrix.toEuclideanLin theta.V b) = _
  rw [hVinner]
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  change (∑ x, theta.weight x * f (theta.effect x)) -
      dotProduct
        (Matrix.mulVec theta.R⁻¹
          (Matrix.mulVec (Matrix.diagonal (f ∘ theta.effect)) q))
        (Matrix.mulVec theta.R.transpose theta.weight) = _
  rw [Matrix.dotProduct_transpose_mulVec]
  have hcancelVec (v : Fin k → ℝ) :
      Matrix.mulVec theta.R (Matrix.mulVec theta.R⁻¹ v) = v := by
    rw [Matrix.mulVec_mulVec, hcancel, Matrix.one_mulVec]
  rw [hcancelVec]
  simp only [dotProduct, Matrix.mulVec_diagonal, Function.comp_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro u _
  dsimp [q]
  ring

/-- The uncorrected first-coordinate anchor costs at most the spectral radius times its
Euclidean anchor residual. -/
lemma structuredLattice_uncorrectedAnchor_error_le
    {k dx dz n : ℕ} {L pi0 sigma0 delta : ℝ}
    (theta : StructuredLatticePoint k dx (effectRadius dz L sigma0))
    (htheta : theta.WellFormed (dz := dz) (n := n) (L := L)
      (pi0 := pi0) (sigma0 := sigma0))
    (hL : 0 ≤ L) (hsigma : 0 < sigma0) [Nonempty (Fin k)]
    (f : ℝ → ℝ) (hf : LipschitzWith 1 f) (hf0 : f 0 = 0)
    (hanchor : Real.sqrt (∑ u, ((∑ v, theta.R u v *
      (∑ i, theta.V i v * firstBasis dx i)) - 1) ^ 2) ≤ delta) :
    |({ weight := theta.weight, atom := theta.effect } :
        CausalSmith.Substrate.CollisionSafeSpectralLaw.AtomicLaw (Fin k)).integral f -
      anchorEval
        (Matrix.toEuclideanLin (theta.V * theta.R.transpose)
          (WithLp.toLp 2 theta.weight))
        (WithLp.toLp 2 (firstBasis dx))
        ((structuredLatticeRealDiagonalization theta htheta hsigma).applyFunction f)| ≤
      effectRadius dz L sigma0 * delta := by
  let radius := effectRadius dz L sigma0
  let q : Fin k → ℝ := Matrix.mulVec (theta.R * theta.V.transpose) (firstBasis dx)
  let c : Euc k := WithLp.toLp 2 (fun u => theta.weight u * f (theta.effect u))
  let r : Euc k := WithLp.toLp 2 (fun u => 1 - q u)
  have hradius : 0 ≤ radius := by
    dsimp [radius, effectRadius]
    positivity
  have hfbound (u : Fin k) : |f (theta.effect u)| ≤ radius := by
    calc
      |f (theta.effect u)| = ‖f (theta.effect u) - f 0‖ := by
        simp [hf0, Real.norm_eq_abs]
      _ ≤ ‖theta.effect u - 0‖ := by
        simpa using hf.norm_sub_le (theta.effect u) 0
      _ = |theta.effect u| := by simp [Real.norm_eq_abs]
      _ ≤ radius := by
        exact abs_le.mpr (theta.lawValid.2.2 u)
  let p : Euc k := WithLp.toLp 2 theta.weight
  have hp : ‖p‖ ≤ 1 :=
    probabilityVector_euc_norm_le_one theta.weight theta.lawValid.1 theta.lawValid.2.1
  have hdiag : ‖Matrix.diagonal (f ∘ theta.effect)‖ ≤ radius := by
    rw [Matrix.l2_opNorm_diagonal, pi_norm_le_iff_of_nonneg hradius]
    intro u
    simpa [Function.comp_apply, Real.norm_eq_abs] using hfbound u
  have hc_eq : c = Matrix.toEuclideanLin (Matrix.diagonal (f ∘ theta.effect)) p := by
    apply PiLp.ext
    intro u
    simp [c, p, Matrix.toEuclideanLin_apply, Matrix.mulVec_diagonal, mul_comm]
  have hc : ‖c‖ ≤ radius := by
    rw [hc_eq]
    calc
      ‖Matrix.toEuclideanLin (Matrix.diagonal (f ∘ theta.effect)) p‖ ≤
          ‖Matrix.diagonal (f ∘ theta.effect)‖ * ‖p‖ := by
        simpa [Matrix.toEuclideanLin_apply] using
          Matrix.l2_opNorm_mulVec (Matrix.diagonal (f ∘ theta.effect)) p
      _ ≤ radius * 1 := mul_le_mul hdiag hp (norm_nonneg _) hradius
      _ = radius := mul_one _
  have hr : ‖r‖ ≤ delta := by
    rw [EuclideanSpace.norm_eq]
    have hsquares : (∑ u, ‖r u‖ ^ 2) = ∑ u, (q u - 1) ^ 2 := by
      apply Finset.sum_congr rfl
      intro u _
      change |1 - q u| ^ 2 = (q u - 1) ^ 2
      rw [sq_abs]
      ring
    rw [hsquares]
    have hq (u : Fin k) : q u =
        ∑ v, theta.R u v * (∑ i, theta.V i v * firstBasis dx i) := by
      change Matrix.mulVec (theta.R * theta.V.transpose) (firstBasis dx) u = _
      rw [← Matrix.mulVec_mulVec]
      simp [Matrix.mulVec, dotProduct]
    simpa only [hq] using hanchor
  rw [structuredLattice_uncorrectedAnchor_error_eq theta htheta hsigma f hf0]
  change |inner ℝ r c| ≤ radius * delta
  calc
    |inner ℝ r c| ≤ ‖r‖ * ‖c‖ := abs_real_inner_le_norm _ _
    _ ≤ delta * radius :=
      mul_le_mul hr hc (norm_nonneg _) (le_trans (norm_nonneg _) hr)
    _ = radius * delta := mul_comm _ _

set_option maxHeartbeats 800000

/-- Exact small-error Wasserstein estimate (paper display (102)) for the selected prescribed
structured-lattice law. -/
theorem selected_structuredLattice_wass1_le
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (P : MeasureTheory.Measure (FullData k dx dz)) [MeasureTheory.IsProbabilityMeasure P]
    (A : LatticeEstimator k dx dz n (effectRadius dz L sigma0))
    (hA : IsPrescribedStructuredLattice (L := L) (pi0 := pi0) (sigma0 := sigma0) A)
    (sample : Fin n → Obs dx dz)
    (hk : 2 ≤ k) (hkx : k ≤ dx) (hkz : k ≤ dz) (hL : 1 ≤ L)
    (hpi : 0 < pi0) (hpiMax : pi0 ≤ 1 / (2 * k : ℝ))
    (hsigma : 0 < sigma0) (hsigmaMax : sigma0 ≤ 1)
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P)
    (hsmall : dS (empSummary sample) (obsSummary P) < pi0 * sigma0 ^ 2 / 4) :
    AtomicLaw.LawModulo.wass1 (A.estimate sample) (quotientLaw P hM) ≤
      (effectRadius dz L sigma0 +
        4 * Real.sqrt k * L * effectRadius dz L sigma0 / sigma0 +
        L * (16 * Real.sqrt dx * k * L ^ 2 / sigma0 ^ 2)) *
      structuredLatticePathCoefficient k dx dz L pi0 sigma0 *
      (dS (empSummary sample) (obsSummary P) + latticeMesh k dx n pi0 sigma0) := by
  let radius := effectRadius dz L sigma0
  let kappa := 4 * Real.sqrt k * L / sigma0
  let B := structuredLatticePathCoefficient k dx dz L pi0 sigma0
  let eps := dS (empSummary sample) (obsSummary P) + latticeMesh k dx n pi0 sigma0
  obtain ⟨theta, htheta, hestimate, hop, hmean, hanchor⟩ :=
    selected_structuredLattice_population_residuals_le P A hA sample hk hkx hkz hL hpi
      hpiMax hsigma hsigmaMax hM hsmall
  obtain ⟨V, R, p, tau, hm, hb, hD, hRmin, hRnorm, hp, hpSum, htau, hlaw⟩ :=
    population_structured_tuple_exists P hk hkx hL hpi hsigma hM
  letI : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  let muHat : CausalSmith.Substrate.CollisionSafeSpectralLaw.AtomicLaw (Fin k) :=
    ⟨theta.weight, theta.effect⟩
  let muPop : CausalSmith.Substrate.CollisionSafeSpectralLaw.AtomicLaw (Fin k) := ⟨p, tau⟩
  let DHat := structuredLatticeRealDiagonalization theta htheta hsigma
  let DPop := signalTupleRealDiagonalization V R tau hsigma hRmin
  let mHat : Euc dx := Matrix.toEuclideanLin (theta.V * theta.R.transpose)
    (WithLp.toLp 2 theta.weight)
  let mPop : Euc dx := Matrix.toEuclideanLin (V.V * R.transpose) (WithLp.toLp 2 p)
  let e1 : Euc dx := WithLp.toLp 2 (firstBasis dx)
  have hradius : 0 ≤ radius := by dsimp [radius, effectRadius]; positivity
  have hkappa : 0 ≤ kappa := by dsimp [kappa]; positivity
  have hdx : 0 < dx := by omega
  have he1 : ‖e1‖ = 1 := by
    exact AmbientOperatorBridge.norm_firstBasis hdx
  have hmuHat : muHat.Valid := ⟨theta.lawValid.1, theta.lawValid.2.1⟩
  have hmuPop : muPop.Valid := by
    refine ⟨?_, hpSum⟩
    intro u
    linarith [hp u, hpi]
  have hcondHat : DHat.conditionNumber ≤ kappa := by
    exact structuredLatticeRealDiagonalization_conditionNumber_le theta htheta hk hL hsigma
      hsigmaMax
  have hcondPop : DPop.conditionNumber ≤ kappa := by
    exact signalTupleRealDiagonalization_conditionNumber_le V R tau hk hL hsigma hsigmaMax
      hRmin hRnorm
  have hspecHat : DHat.SpectrumBound radius := by
    exact structuredLatticeRealDiagonalization_spectrumBound theta htheta hsigma hradius
  have hspecPop : DPop.SpectrumBound radius := by
    exact signalTupleRealDiagonalization_spectrumBound V R tau hsigma hRmin hradius htau
  have hrepPop : RepresentsAtomicLaw DPop mPop e1 muPop := by
    exact signalTuple_represents_atomicLaw V R p tau hsigma hRmin hb
  have hmPop : mPop = WithLp.toLp 2 (obsSummary P).mX := by
    apply PiLp.ext
    intro i
    simpa [mPop, Matrix.toEuclideanLin_apply] using congrFun hm.symm i
  have hmHatCoord : mHat = WithLp.toLp 2 (fun i =>
      ∑ u, theta.V i u * (∑ v, theta.R v u * theta.weight v)) := by
    apply PiLp.ext
    intro i
    change Matrix.mulVec (theta.V * theta.R.transpose) theta.weight i = _
    rw [← Matrix.mulVec_mulVec]
    simp [Matrix.mulVec, dotProduct]
  have hmean' : ‖mHat - mPop‖ ≤ B * eps := by
    rw [hmHatCoord, hmPop, EuclideanSpace.norm_eq]
    simpa [B, eps, Real.norm_eq_abs, sq_abs] using hmean
  have hop' : ‖structuredCandidateOperator theta -
      (V.V * R⁻¹ * Matrix.diagonal tau * R * V.V.transpose)‖ ≤ B * eps := by
    change ‖matrixCLM (structuredCandidateOperator theta -
      (V.V * R⁻¹ * Matrix.diagonal tau * R * V.V.transpose))‖ ≤ B * eps
    simpa [B, eps, hD] using hop
  have hmPopNorm : ‖mPop‖ ≤ L := by
    rw [hmPop]
    exact (AmbientOperatorBridge.model_summary_ambient_bounds P hk hkx hkz hL hpi hpiMax
      hsigma hsigmaMax hM).2
  let f := CausalSmith.Substrate.CollisionSafeSpectralLaw.AtomicLaw.krPotential muHat muPop
  have hf : LipschitzWith 1 f :=
    (CausalSmith.Substrate.CollisionSafeSpectralLaw.AtomicLaw.krPotential_attains
      muHat muPop hmuHat hmuPop).1
  have hf0 : f 0 = 0 :=
    CausalSmith.Substrate.CollisionSafeSpectralLaw.AtomicLaw.krPotential_zero muHat muPop
  have hatt : CausalSmith.Substrate.CollisionSafeSpectralLaw.AtomicLaw.w1 muHat muPop =
      |muHat.integral f - muPop.integral f| :=
    (CausalSmith.Substrate.CollisionSafeSpectralLaw.AtomicLaw.krPotential_attains
      muHat muPop hmuHat hmuPop).2
  have hanchorErr : |muHat.integral f - anchorEval mHat e1 (DHat.applyFunction f)| ≤
      radius * (B * eps) := by
    exact structuredLattice_uncorrectedAnchor_error_le theta htheta
      (le_trans zero_le_one hL) hsigma f hf hf0
      (by simpa [B, eps] using hanchor)
  have hcompare : |anchorEval mHat e1 (DHat.applyFunction f) -
      anchorEval mPop e1 (DPop.applyFunction f)| ≤
      (B * eps) * (kappa * radius) +
        L * (Real.sqrt dx * kappa * kappa * (B * eps)) := by
    have hsharp := abs_anchorEval_applyFunction_sub_le_sqrt_dim
      DHat DPop mHat mPop e1 e1 f hf hf0 hcondHat hcondPop hradius hspecHat hspecPop
    rw [he1, sub_self, norm_zero, mul_one, mul_zero, add_zero] at hsharp
    calc
      _ ≤ ‖mHat - mPop‖ * (kappa * radius) +
          ‖mPop‖ * (Real.sqrt dx * kappa * kappa *
            ‖structuredCandidateOperator theta -
              (V.V * R⁻¹ * Matrix.diagonal tau * R * V.V.transpose)‖) := by
        simpa only [mul_one] using hsharp
      _ ≤ _ := by gcongr
  have hwraw : CausalSmith.Substrate.CollisionSafeSpectralLaw.AtomicLaw.w1 muHat muPop ≤
      (radius + kappa * radius + L * (Real.sqrt dx * kappa * kappa)) * B * eps := by
    rw [hatt, hrepPop f hf hf0]
    calc
      |muHat.integral f - anchorEval mPop e1 (DPop.applyFunction f)| ≤
          |muHat.integral f - anchorEval mHat e1 (DHat.applyFunction f)| +
            |anchorEval mHat e1 (DHat.applyFunction f) -
              anchorEval mPop e1 (DPop.applyFunction f)| := by
        rw [show muHat.integral f - anchorEval mPop e1 (DPop.applyFunction f) =
            (muHat.integral f - anchorEval mHat e1 (DHat.applyFunction f)) +
              (anchorEval mHat e1 (DHat.applyFunction f) -
                anchorEval mPop e1 (DPop.applyFunction f)) by ring]
        exact abs_add_le _ _
      _ ≤ radius * (B * eps) +
          ((B * eps) * (kappa * radius) +
            L * (Real.sqrt dx * kappa * kappa * (B * eps))) :=
        add_le_add hanchorErr hcompare
      _ = _ := by ring
  rw [hestimate, StructuredLatticePoint.effectLaw, quotientLaw,
    AtomicLaw.LawModulo.wass1_ofProbabilityLaw]
  rw [GapFreeModulusBridge.wass1_eq_neutralW1 theta.lawValid
    (quotientLawRaw_valid P hM)]
  change CausalSmith.Substrate.CollisionSafeSpectralLaw.AtomicLaw.w1 muHat
      (GapFreeModulusBridge.asNeutral (quotientLawRaw P radius)) ≤ _
  rw [← hlaw]
  change CausalSmith.Substrate.CollisionSafeSpectralLaw.AtomicLaw.w1 muHat muPop ≤ _
  calc
    _ ≤ (radius + kappa * radius + L * (Real.sqrt dx * kappa * kappa)) * B * eps := hwraw
    _ = _ := by
      dsimp [radius, kappa, B, eps]
      have hkroot : (Real.sqrt (k : ℝ)) ^ 2 = k := Real.sq_sqrt (by positivity)
      field_simp [ne_of_gt hsigma]
      rw [hkroot]
      ring

/-- The small- and large-summary-error branches combine into the deterministic all-sample
oracle bound with the frozen displayed lattice constant. -/
theorem prescribedEstimator_wass1_le
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (P : MeasureTheory.Measure (FullData k dx dz)) [MeasureTheory.IsProbabilityMeasure P]
    (A : LatticeEstimator k dx dz n (effectRadius dz L sigma0))
    (hA : IsPrescribedStructuredLattice (L := L) (pi0 := pi0) (sigma0 := sigma0) A)
    (sample : Fin n → Obs dx dz) (hn : 1 ≤ n)
    (hk : 2 ≤ k) (hkx : k ≤ dx) (hkz : k ≤ dz) (hL : 1 ≤ L)
    (hpi : 0 < pi0) (hpiMax : pi0 ≤ 1 / (2 * k : ℝ))
    (hsigma : 0 < sigma0) (hsigmaMax : sigma0 ≤ 1)
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P) :
    AtomicLaw.LawModulo.wass1 (A.estimate sample) (quotientLaw P hM) ≤
      prescribedLatticeConstant k dx dz L pi0 sigma0 *
        (dS (empSummary sample) (obsSummary P) + (Real.sqrt n)⁻¹) := by
  let smallCoeff :=
    (effectRadius dz L sigma0 +
      4 * Real.sqrt k * L * effectRadius dz L sigma0 / sigma0 +
      L * (16 * Real.sqrt dx * k * L ^ 2 / sigma0 ^ 2)) *
      structuredLatticePathCoefficient k dx dz L pi0 sigma0
  let largeCoeff := 8 * effectRadius dz L sigma0 / (pi0 * sigma0 ^ 2)
  have hmesh := latticeMesh_le_sqrt_inv k dx n pi0 sigma0 hn
  have hClat0 : 0 ≤ prescribedLatticeConstant k dx dz L pi0 sigma0 :=
    (prescribedLatticeConstant_pos k dx dz L pi0 sigma0 hk hkx hkz hL hpi hsigma).le
  have hsmallCoeff0 : 0 ≤ smallCoeff := by
    dsimp [smallCoeff, structuredLatticePathCoefficient,
      populationOperatorCoefficient, structuredGridCriterionCoefficient,
      structuredGridOperatorCoefficient, structuredGridMeanCoefficient,
      structuredGridAnchorCoefficient, structuredGridVConstant, effectRadius]
    positivity
  have hsmallCoeff : smallCoeff ≤ prescribedLatticeConstant k dx dz L pi0 sigma0 := by
    unfold prescribedLatticeConstant
    exact le_max_right _ _
  have hlargeCoeff : largeCoeff ≤ prescribedLatticeConstant k dx dz L pi0 sigma0 := by
    unfold prescribedLatticeConstant
    exact le_max_left _ _
  by_cases hsmall : dS (empSummary sample) (obsSummary P) < pi0 * sigma0 ^ 2 / 4
  · have hw := selected_structuredLattice_wass1_le P A hA sample hk hkx hkz hL hpi
      hpiMax hsigma hsigmaMax hM hsmall
    change _ ≤ smallCoeff *
      (dS (empSummary sample) (obsSummary P) + latticeMesh k dx n pi0 sigma0) at hw
    calc
      _ ≤ smallCoeff *
          (dS (empSummary sample) (obsSummary P) + latticeMesh k dx n pi0 sigma0) := hw
      _ ≤ smallCoeff *
          (dS (empSummary sample) (obsSummary P) + (Real.sqrt n)⁻¹) := by
        gcongr
      _ ≤ prescribedLatticeConstant k dx dz L pi0 sigma0 *
          (dS (empSummary sample) (obsSummary P) + (Real.sqrt n)⁻¹) := by
        apply mul_le_mul_of_nonneg_right hsmallCoeff
        unfold dS
        positivity
  · have hw := prescribedEstimator_wass1_le_of_large_summary_error hk hkz hL hpi hsigma
      A P hM sample (le_of_not_gt hsmall)
    change _ ≤ largeCoeff * dS (empSummary sample) (obsSummary P) at hw
    calc
      _ ≤ largeCoeff * dS (empSummary sample) (obsSummary P) := hw
      _ ≤ prescribedLatticeConstant k dx dz L pi0 sigma0 *
          dS (empSummary sample) (obsSummary P) := by
        apply mul_le_mul_of_nonneg_right hlargeCoeff
        unfold dS
        positivity
      _ ≤ prescribedLatticeConstant k dx dz L pi0 sigma0 *
          (dS (empSummary sample) (obsSummary P) + (Real.sqrt n)⁻¹) := by
        apply mul_le_mul_of_nonneg_left _ hClat0
        exact le_add_of_nonneg_right (inv_nonneg.mpr (Real.sqrt_nonneg _))

end

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
