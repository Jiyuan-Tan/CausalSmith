import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.SummaryClosure
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.ModelRealDiagonalization
import CausalSmith.Substrate.CollisionSafeSpectralLaw.Enumeration

/-!
# Model certificates for collision-safe representative spectra

This file extracts from one model law a signal basis, its exact threshold rank, a real
diagonalization of the compressed operator, and the two anchor-coordinate identities required by
the generic collision-safe spectral enumeration theorem.
-/

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open MeasureTheory Set
open CausalSmith.Substrate.CollisionSafeSpectralLaw

/-- The model-generated facts needed to turn a compressed operator into collision-safe polynomial
projector masses. -/
structure ModelCompressedSpectralFacts {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (Q : ModelLaw k dx dz L pi0 sigma0) where
  basis : SignalBasis dx k
  spans : basis.SpansSignal Q.summary
  armwiseFullRank : ∀ t : Bool, Function.Injective (Matrix.toEuclideanLin
    (observedProxyMoment Q.summary t * basis.V))
  stackedRank : Module.finrank ℝ
    (LinearMap.range (Matrix.toEuclideanLin (stackedProxyMoment Q.summary))) = k
  thresholdRetainsExactlySignal : ∀ j,
    pi0 * sigma0 ^ 2 / 2 ≤ singularValue (stackedProxyMoment Q.summary) j ↔ j < k
  diagonalization : RealDiagonalization (compressedOperator Q.summary basis spans)
  eigenvalue_coordinates : diagonalization.eigenvalue = latentEffect Q.P
  left_coordinates : leftAnchor Q.summary basis =
    Matrix.mulVec diagonalization.basisInv.transpose (latentMass Q.P)
  right_coordinates : Matrix.mulVec diagonalization.basisInv (rightAnchor basis) = fun _ => 1

/-- Every model law supplies a compressed real diagonalization in latent-effect coordinates,
together with an observable signal basis and exact threshold-rank certificates. -/
theorem modelCompressedSpectralFacts_exists
    {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (Q : ModelLaw k dx dz L pi0 sigma0) :
    Nonempty (ModelCompressedSpectralFacts Q) := by
  classical
  letI := Q.prob
  rcases Q.model.coreDomain with
    ⟨hk, hkx, _hkz, hL, hpi, _hpiMax, hsigma, _hsigmaMax⟩
  let B := targetFeature Q.P
  have hBpos (r : Fin k) : 0 < (singularSystem B).sigma r := by
    rw [(singularSystem B).sigma_eq]
    exact lt_of_lt_of_le hsigma <| Q.model.proxyRankMargin.2.2.trans <|
      (Matrix.toEuclideanLin B).singularValues_antitone <| by
        simpa using Nat.le_sub_one_of_lt r.isLt
  let F := thinSignalFactorization B hBpos
  let V := F.V
  let R : RectMatrix k k := B.transpose * V.V
  let Rinv : RectMatrix k k := F.coordInv.transpose
  let C : Bool → RectMatrix dz k := fun t =>
    referenceFeature Q.P t * latentArmWeights Q.P t
  have hR : R = F.coord.transpose := by
    calc
      R = B.transpose * V.V := rfl
      _ = (V.V * F.coord).transpose * V.V := by rw [← F.factor]
      _ = F.coord.transpose * (V.V.transpose * V.V) := by
        simp [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = F.coord.transpose := by rw [V.transpose_mul_self, Matrix.mul_one]
  have hRRinv : R * Rinv = 1 := by
    rw [hR]
    simpa [Rinv, Matrix.transpose_mul] using congrArg Matrix.transpose F.inv_mul_coord
  have hRinvR : Rinv * R = 1 := by
    rw [hR]
    simpa [Rinv, Matrix.transpose_mul] using congrArg Matrix.transpose F.coord_mul_inv
  have hMfac (t : Bool) : observedProxyMoment Q.summary t * V.V = C t * R := by
    rw [show Q.summary = obsSummary Q.P from rfl,
      observedProxyMoment_factorization Q.P hk hkx hL hpi Q.model t]
    simp only [C, R, B, Matrix.mul_assoc]
  have hNfac (t : Bool) : observedOutcomeProxyMoment Q.summary t * V.V =
      C t * Matrix.diagonal (latentMean Q.P t) * R := by
    rw [show Q.summary = obsSummary Q.P from rfl,
      observedOutcomeProxyMoment_factorization Q.P hk hpi Q.model t]
    simp only [C, R, B, Matrix.mul_assoc]
  have hMtranspose_sub (t : Bool) :
      LinearMap.range (Matrix.toEuclideanLin (observedProxyMoment Q.summary t).transpose) ≤
        LinearMap.range (Matrix.toEuclideanLin V.V) := by
    intro x hx
    rcases hx with ⟨y, rfl⟩
    refine ⟨Matrix.toEuclideanLin
      (F.coord * (C t).transpose) y, ?_⟩
    apply PiLp.ext
    intro i
    rw [show (observedProxyMoment Q.summary t).transpose =
        V.V * (F.coord * (C t).transpose) by
      calc
        _ = (C t * B.transpose).transpose := by
          rw [show Q.summary = obsSummary Q.P from rfl]
          rw [observedProxyMoment_factorization Q.P hk hkx hL hpi Q.model t]
        _ = B * (C t).transpose := by simp [Matrix.transpose_mul]
        _ = (V.V * F.coord) * (C t).transpose := by rw [← F.factor]
        _ = _ := by simp [Matrix.mul_assoc]]
    simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec]
  have hVrank : Module.finrank ℝ (LinearMap.range (Matrix.toEuclideanLin V.V)) = k := by
    change Module.finrank ℝ (LinearMap.range (signalBasisLinearIsometry V).toLinearMap) = k
    rw [(signalBasisLinearIsometry V).toLinearMap.finrank_range_of_inj
      (signalBasisLinearIsometry V).injective, finrank_euclideanSpace]
    simp
  have hM0rank : Module.finrank ℝ
      (LinearMap.range (Matrix.toEuclideanLin
        (observedProxyMoment Q.summary false).transpose)) = k := by
    have hadj : Matrix.toEuclideanLin (observedProxyMoment Q.summary false).transpose =
        (Matrix.toEuclideanLin (observedProxyMoment Q.summary false)).adjoint := by
      rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
      rfl
    rw [hadj]
    rw [(Matrix.toEuclideanLin
      (observedProxyMoment Q.summary false)).finrank_range_adjoint]
    have hfac := observedProxyMoment_factorization Q.P hk hkx hL hpi Q.model false
    have hmargin := observedProxyMoment_minSingular_of_factorization
      Q.P hk hpi hsigma Q.model false hfac
    have hpos : 0 < singularValue (observedProxyMoment Q.summary false) (k - 1) := by
      rw [show Q.summary = obsSummary Q.P from rfl]
      exact (mul_pos hpi (sq_pos_of_pos hsigma)).trans_le hmargin
    have hlower := (Matrix.toEuclideanLin
      (observedProxyMoment Q.summary false)).singularValues_pos_iff_lt_finrank_range.mp hpos
    have hupper : Module.finrank ℝ
        (LinearMap.range (Matrix.toEuclideanLin (observedProxyMoment Q.summary false))) ≤ k := by
      rw [← (Matrix.toEuclideanLin
        (observedProxyMoment Q.summary false)).finrank_range_adjoint]
      rw [← show Matrix.toEuclideanLin
          (observedProxyMoment Q.summary false).transpose =
          (Matrix.toEuclideanLin (observedProxyMoment Q.summary false)).adjoint by
        rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
        rfl]
      exact (Submodule.finrank_mono (hMtranspose_sub false)).trans_eq hVrank
    omega
  have hspans : V.SpansSignal Q.summary := by
    unfold SignalBasis.SpansSignal signalRowspace
    have hM0eq : LinearMap.range (Matrix.toEuclideanLin
        (observedProxyMoment Q.summary false).transpose) =
        LinearMap.range (Matrix.toEuclideanLin V.V) := by
      apply Submodule.eq_of_le_of_finrank_le (hMtranspose_sub false)
      rw [hVrank, hM0rank]
    apply le_antisymm
    · rw [← hM0eq]
      exact le_sup_left
    · apply sup_le (hMtranspose_sub false) (hMtranspose_sub true)
  have hAinj (t : Bool) : Function.Injective (Matrix.toEuclideanLin
      (observedProxyMoment Q.summary t * V.V)) := by
    have hm := observedProxyMoment_compression_margin Q.P hk hkx hL hpi hsigma
      Q.model t V hspans
    apply publishedMomentIdentity_injective_of_signalMinSingular_pos
    exact (mul_pos hpi (sq_pos_of_pos hsigma)).trans_le hm.2
  have hterm (t : Bool) :
      penroseInverse (observedProxyMoment Q.summary t * V.V) *
          (observedOutcomeProxyMoment Q.summary t * V.V) =
        Rinv * Matrix.diagonal (latentMean Q.P t) * R := by
    have hNrewrite : observedOutcomeProxyMoment Q.summary t * V.V =
        (observedProxyMoment Q.summary t * V.V) *
          (Rinv * Matrix.diagonal (latentMean Q.P t) * R) := by
      rw [hMfac t, hNfac t]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc R Rinv, hRRinv, Matrix.one_mul]
    rw [hNrewrite, ← Matrix.mul_assoc,
      publishedMomentIdentity_penrose_left_inverse_of_injective _ (hAinj t), Matrix.one_mul]
  have hD : compressedOperator Q.summary V hspans =
      Rinv * Matrix.diagonal (latentEffect Q.P) * R := by
    unfold compressedOperator
    change genuinePenroseInverse (observedProxyMoment Q.summary true * V.V) *
        (observedOutcomeProxyMoment Q.summary true * V.V) -
      genuinePenroseInverse (observedProxyMoment Q.summary false * V.V) *
        (observedOutcomeProxyMoment Q.summary false * V.V) = _
    rw [genuinePenroseInverse_eq_penroseInverse_of_injective _ (hAinj true),
      genuinePenroseInverse_eq_penroseInverse_of_injective _ (hAinj false),
      hterm true, hterm false, ← Matrix.sub_mul, ← Matrix.mul_sub]
    congr 2
    ext a b
    by_cases hab : a = b <;>
      simp [Matrix.diagonal_apply, hab, latentEffect]
  let D : RealDiagonalization (compressedOperator Q.summary V hspans) :=
    { basis := Rinv
      basisInv := R
      eigenvalue := latentEffect Q.P
      basis_mul_inv := hRinvR
      inv_mul_basis := hRRinv
      reconstruct := hD }
  have hmX : Q.summary.mX = Matrix.mulVec B (latentMass Q.P) :=
    publishedMomentIdentity_obsSummary_mX_factorization Q.P hpi Q.model
  have hanchor : Matrix.mulVec B.transpose (firstBasis dx) = fun _ => 1 :=
    publishedMomentIdentity_targetFeature_transpose_firstBasis Q.P hk hkx hpi Q.model
  have hleft : leftAnchor Q.summary V =
      Matrix.mulVec R.transpose (latentMass Q.P) := by
    have hleftAnchor : leftAnchor Q.summary V =
        Matrix.mulVec V.V.transpose Q.summary.mX := by
      funext a
      simp [leftAnchor, Matrix.mulVec, dotProduct, mul_comm]
    have hRt : R.transpose = V.V.transpose * B := by
      simp [R, Matrix.transpose_mul]
    rw [hleftAnchor, hmX, Matrix.mulVec_mulVec, hRt]
  have hright : Matrix.mulVec R (rightAnchor V) = fun _ => 1 := by
    have hproj : V.V * V.V.transpose * B = B := by
      calc
        V.V * V.V.transpose * B = V.V * (V.V.transpose * B) := by
          simp only [Matrix.mul_assoc]
        _ = V.V * (V.V.transpose * (V.V * F.coord)) := by rw [← F.factor]
        _ = V.V * ((V.V.transpose * V.V) * F.coord) := by
          simp only [Matrix.mul_assoc]
        _ = V.V * F.coord := by rw [V.transpose_mul_self, Matrix.one_mul]
        _ = B := F.factor.symm
    have hBt : B.transpose = R * V.V.transpose := by
      have ht := congrArg Matrix.transpose hproj
      simpa [R, Matrix.transpose_mul, Matrix.mul_assoc] using ht.symm
    change Matrix.mulVec R (Matrix.mulVec V.V.transpose (firstBasis dx)) = _
    rw [Matrix.mulVec_mulVec, ← hBt, hanchor]
  have hstackLower : pi0 * sigma0 ^ 2 ≤
      singularValue (stackedProxyMoment Q.summary) (k - 1) := by
    rw [show Q.summary = obsSummary Q.P from rfl]
    exact stackedProxyMoment_minSingular Q.P hk hkx hL hpi hsigma Q.model
  have hstackRank : Module.finrank ℝ
      (LinearMap.range (Matrix.toEuclideanLin (stackedProxyMoment Q.summary))) = k := by
    have hlower : k ≤ Module.finrank ℝ
        (LinearMap.range (Matrix.toEuclideanLin (stackedProxyMoment Q.summary))) := by
      have hp : 0 < singularValue (stackedProxyMoment Q.summary) (k - 1) :=
        (mul_pos hpi (sq_pos_of_pos hsigma)).trans_le hstackLower
      have := (Matrix.toEuclideanLin
        (stackedProxyMoment Q.summary)).singularValues_pos_iff_lt_finrank_range.mp hp
      omega
    have hupper : Module.finrank ℝ
        (LinearMap.range (Matrix.toEuclideanLin (stackedProxyMoment Q.summary))) ≤ k := by
      let Cstack : RectMatrix (2 * dz) k := fun i u =>
        if hi : i.val < dz then C false ⟨i.val, hi⟩ u
        else C true ⟨i.val - dz, by omega⟩ u
      have hstackFac : stackedProxyMoment Q.summary = Cstack * B.transpose := by
        ext i j
        by_cases hi : i.val < dz
        · have hfac := congrArg (fun M : RectMatrix dz dx => M ⟨i.val, hi⟩ j)
              (observedProxyMoment_factorization Q.P hk hkx hL hpi Q.model false)
          rw [show Q.summary = obsSummary Q.P from rfl]
          unfold stackedProxyMoment
          rw [dif_pos hi]
          rw [Matrix.mul_apply]
          have hc (u : Fin k) : Cstack i u = C false ⟨i.val, hi⟩ u := by
            simp [Cstack, hi]
          simp_rw [hc]
          change (obsSummary Q.P).M0 ⟨i.val, hi⟩ j =
            (C false * B.transpose) ⟨i.val, hi⟩ j at hfac
          rw [Matrix.mul_apply] at hfac
          exact hfac
        · have hfac := congrArg (fun M : RectMatrix dz dx =>
              M ⟨i.val - dz, by omega⟩ j)
              (observedProxyMoment_factorization Q.P hk hkx hL hpi Q.model true)
          rw [show Q.summary = obsSummary Q.P from rfl]
          unfold stackedProxyMoment
          rw [dif_neg hi]
          rw [Matrix.mul_apply]
          have hc (u : Fin k) : Cstack i u = C true ⟨i.val - dz, by omega⟩ u := by
            simp [Cstack, hi]
          simp_rw [hc]
          change (obsSummary Q.P).M1 ⟨i.val - dz, by omega⟩ j =
            (C true * B.transpose) ⟨i.val - dz, by omega⟩ j at hfac
          rw [Matrix.mul_apply] at hfac
          exact hfac
      have hrange : LinearMap.range
          (Matrix.toEuclideanLin (stackedProxyMoment Q.summary)) ≤
          LinearMap.range (Matrix.toEuclideanLin Cstack) := by
        intro x hx
        rcases hx with ⟨y, rfl⟩
        refine ⟨Matrix.toEuclideanLin B.transpose y, ?_⟩
        rw [hstackFac]
        apply PiLp.ext
        intro i
        simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec]
      exact (Submodule.finrank_mono hrange).trans <|
        (Matrix.toEuclideanLin Cstack).finrank_range_le.trans (by simp)
    omega
  have hthreshold (j : ℕ) :
      pi0 * sigma0 ^ 2 / 2 ≤ singularValue (stackedProxyMoment Q.summary) j ↔ j < k := by
    constructor
    · intro hj
      by_contra hjk
      have hk_le : k ≤ j := by omega
      have hz := (Matrix.toEuclideanLin
        (stackedProxyMoment Q.summary)).singularValues_eq_zero_iff_le_finrank_range
          (n := j) |>.mpr
          (by rw [hstackRank]; exact hk_le)
      have htpos : 0 < pi0 * sigma0 ^ 2 / 2 := by positivity
      change pi0 * sigma0 ^ 2 / 2 ≤
        (Matrix.toEuclideanLin (stackedProxyMoment Q.summary)).singularValues j at hj
      rw [hz] at hj
      linarith
    · intro hj
      have hant := (Matrix.toEuclideanLin
        (stackedProxyMoment Q.summary)).singularValues_antitone
          (Nat.le_sub_one_of_lt hj)
      exact (by nlinarith [hpi.le, sq_nonneg sigma0] :
        pi0 * sigma0 ^ 2 / 2 ≤ pi0 * sigma0 ^ 2).trans
        (hstackLower.trans hant)
  exact ⟨⟨V, hspans, hAinj, hstackRank, hthreshold, D, rfl, hleft, hright⟩⟩

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
