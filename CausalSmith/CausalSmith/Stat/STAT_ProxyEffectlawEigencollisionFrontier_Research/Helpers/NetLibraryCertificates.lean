import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.Concentration
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.LatticeEstimator
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.TGapFreePositiveMeasureModulus
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.TCollisionUniformRootN

/-! # Derived certificates for the advised finite summary library -/

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open MeasureTheory Set

noncomputable section

/-- The coordinates actually stored in a summary (excluding the two empirical arm counts). -/
inductive NetSummaryCoord (dx dz : ℕ)
  | M0 (i : Fin dz) (j : Fin dx)
  | M1 (i : Fin dz) (j : Fin dx)
  | N0 (i : Fin dz) (j : Fin dx)
  | N1 (i : Fin dz) (j : Fin dx)
  | mean (j : Fin dx)
  deriving Fintype, DecidableEq

def netSummaryCoord {dx dz : ℕ} (s : SummarySpace dx dz) : NetSummaryCoord dx dz → ℝ
  | .M0 i j => s.M0 i j
  | .M1 i j => s.M1 i j
  | .N0 i j => s.N0 i j
  | .N1 i j => s.N1 i j
  | .mean j => s.mX j

lemma netSummaryCoord_ext {dx dz : ℕ} {s q : SummarySpace dx dz}
    (h : ∀ c, netSummaryCoord s c = netSummaryCoord q c) : s = q := by
  cases s
  cases q
  congr
  · ext i j; exact h (.M0 i j)
  · ext i j; exact h (.M1 i j)
  · ext i j; exact h (.N0 i j)
  · ext i j; exact h (.N1 i j)
  · funext j; exact h (.mean j)

lemma netSummaryCoord_card (dx dz : ℕ) :
    Fintype.card (NetSummaryCoord dx dz) = 4 * dz * dx + dx := by
  rw [Fintype.card_congr (NetSummaryCoord.proxyTypeEquiv dx dz).symm]
  simp
  ring

private lemma NetLibrary.cubeLower_injective
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (A : NetLibrary k dx dz n L pi0 sigma0) : Function.Injective A.cubeLower := by
  intro i j hij
  by_contra hne
  have hdis := A.cubes_disjoint (Set.mem_univ i) (Set.mem_univ j) hne
  change Disjoint (A.cube i) (A.cube j) at hdis
  rw [A.cube_eq_halfOpen i, A.cube_eq_halfOpen j, hij] at hdis
  have hi := A.representative_in_cube i
  rw [A.cube_eq_halfOpen i, hij] at hi
  exact Set.disjoint_left.mp hdis hi hi

private noncomputable def NetLibrary.gridInteger
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (A : NetLibrary k dx dz n L pi0 sigma0) (i : A.index)
    (c : NetSummaryCoord dx dz) : ℤ := by
  cases c with
  | M0 a j => exact Classical.choose ((A.cubeLower_on_grid i).1 a j)
  | M1 a j => exact Classical.choose ((A.cubeLower_on_grid i).2.1 a j)
  | N0 a j => exact Classical.choose ((A.cubeLower_on_grid i).2.2.1 a j)
  | N1 a j => exact Classical.choose ((A.cubeLower_on_grid i).2.2.2.1 a j)
  | mean j => exact Classical.choose ((A.cubeLower_on_grid i).2.2.2.2 j)

private lemma NetLibrary.gridInteger_spec
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (A : NetLibrary k dx dz n L pi0 sigma0) (i : A.index)
    (c : NetSummaryCoord dx dz) :
    netSummaryCoord (A.cubeLower i) c = -L + A.scale * A.gridInteger i c := by
  cases c with
  | M0 a j => exact Classical.choose_spec ((A.cubeLower_on_grid i).1 a j)
  | M1 a j => exact Classical.choose_spec ((A.cubeLower_on_grid i).2.1 a j)
  | N0 a j => exact Classical.choose_spec ((A.cubeLower_on_grid i).2.2.1 a j)
  | N1 a j => exact Classical.choose_spec ((A.cubeLower_on_grid i).2.2.2.1 a j)
  | mean j => exact Classical.choose_spec ((A.cubeLower_on_grid i).2.2.2.2 j)

private lemma NetLibrary.gridInteger_injective
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (A : NetLibrary k dx dz n L pi0 sigma0) :
    Function.Injective (fun i => A.gridInteger i) := by
  intro i j hij
  apply A.cubeLower_injective
  apply netSummaryCoord_ext
  intro c
  rw [A.gridInteger_spec i c, A.gridInteger_spec j c]
  exact congrArg (fun z : ℤ => -L + A.scale * z) (congrFun hij c)

private lemma netSummaryCoord_box {dx dz : ℕ} {L : ℝ} {s : SummarySpace dx dz}
    (hs : InSummaryBox L s) (c : NetSummaryCoord dx dz) :
    netSummaryCoord s c ∈ Set.Icc (-L) L := by
  rcases hs with ⟨hM0, hM1, hN0, hN1, hm⟩
  cases c with
  | M0 i j => exact hM0 i j
  | M1 i j => exact hM1 i j
  | N0 i j => exact hN0 i j
  | N1 i j => exact hN1 i j
  | mean j => exact hm j

private lemma netSummaryCoord_halfOpen {dx dz : ℕ} {scale : ℝ}
    {lo s : SummarySpace dx dz} (hs : InHalfOpenSummaryCube scale lo s)
    (c : NetSummaryCoord dx dz) :
    netSummaryCoord lo c ≤ netSummaryCoord s c ∧
      netSummaryCoord s c < netSummaryCoord lo c + scale := by
  rcases hs with ⟨hM0, hM1, hN0, hN1, hm⟩
  cases c with
  | M0 i j => exact hM0 i j
  | M1 i j => exact hM1 i j
  | N0 i j => exact hN0 i j
  | N1 i j => exact hN1 i j
  | mean j => exact hm j

private lemma NetLibrary.scale_pos
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (A : NetLibrary k dx dz n L pi0 sigma0)
    (hn : 1 ≤ n) (hdx : 0 < dx) (hdz : 0 < dz) : 0 < A.scale := by
  rw [A.scale_eq]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hprod : (0 : ℝ) < dz * dx := by positivity
  positivity

private lemma NetLibrary.gridInteger_nonneg
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (A : NetLibrary k dx dz n L pi0 sigma0) (hscale : 0 < A.scale)
    (i : A.index) (c : NetSummaryCoord dx dz) : 0 ≤ A.gridInteger i c := by
  have hmem := A.representative_in_cube i
  rw [A.cube_eq_halfOpen i] at hmem
  have hbox := netSummaryCoord_box hmem.1 c
  have hcube := netSummaryCoord_halfOpen hmem.2 c
  rw [A.gridInteger_spec i c] at hcube
  have hz : (-1 : ℝ) < (A.gridInteger i c : ℝ) := by
    by_contra h
    have hzleZ : A.gridInteger i c ≤ (-1 : ℤ) := by
      have hzleR : (A.gridInteger i c : ℝ) ≤ -1 := le_of_not_gt h
      exact_mod_cast hzleR
    have hzleR : (A.gridInteger i c : ℝ) ≤ -1 := by exact_mod_cast hzleZ
    have hmul := mul_le_mul_of_nonneg_left hzleR hscale.le
    linarith [hbox.1, hcube.2]
  exact_mod_cast (show (-1 : ℤ) < A.gridInteger i c by exact_mod_cast hz)

private lemma NetLibrary.gridInteger_le
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (A : NetLibrary k dx dz n L pi0 sigma0) (hscale : 0 < A.scale)
    (i : A.index) (c : NetSummaryCoord dx dz) :
    (A.gridInteger i c : ℝ) ≤ 2 * L / A.scale := by
  have hmem := A.representative_in_cube i
  rw [A.cube_eq_halfOpen i] at hmem
  have hbox := netSummaryCoord_box hmem.1 c
  have hcube := netSummaryCoord_halfOpen hmem.2 c
  rw [A.gridInteger_spec i c] at hcube
  apply (le_div_iff₀ hscale).2
  calc
    (A.gridInteger i c : ℝ) * A.scale =
        A.scale * (A.gridInteger i c : ℝ) := mul_comm _ _
    _ ≤ 2 * L := by linarith [hbox.2, hcube.1]

private noncomputable def NetLibrary.gridCode
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (A : NetLibrary k dx dz n L pi0 sigma0) (hscale : 0 < A.scale) :
    A.index → (NetSummaryCoord dx dz → Fin (⌈2 * L / A.scale⌉₊ + 1)) :=
  fun i c => ⟨(A.gridInteger i c).toNat, by
    have hz0 := A.gridInteger_nonneg hscale i c
    have hz := A.gridInteger_le hscale i c
    have hnat : ((A.gridInteger i c).toNat : ℝ) ≤ 2 * L / A.scale := by
      rw [show ((A.gridInteger i c).toNat : ℝ) =
          (A.gridInteger i c : ℝ) by
        exact_mod_cast Int.toNat_of_nonneg hz0]
      exact hz
    have hreal := hnat.trans (Nat.le_ceil (2 * L / A.scale))
    have hnatle : (A.gridInteger i c).toNat ≤ ⌈2 * L / A.scale⌉₊ := by
      exact_mod_cast hreal
    exact Nat.lt_succ_of_le hnatle⟩

private lemma NetLibrary.gridCode_injective
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (A : NetLibrary k dx dz n L pi0 sigma0) (hscale : 0 < A.scale) :
    Function.Injective (A.gridCode hscale) := by
  intro i j hij
  apply A.gridInteger_injective
  funext c
  have hc := congrArg (fun f => (f c).val) hij
  have hi := A.gridInteger_nonneg hscale i c
  have hj := A.gridInteger_nonneg hscale j c
  calc
    A.gridInteger i c = ((A.gridInteger i c).toNat : ℤ) :=
      (Int.toNat_of_nonneg hi).symm
    _ = ((A.gridInteger j c).toNat : ℤ) := congrArg Int.ofNat hc
    _ = A.gridInteger j c := Int.toNat_of_nonneg hj

/-- The half-open grid certificate bounds every advised library by a fixed polynomial in `n`. -/
theorem netLibrary_card_polynomial_bound
    (k dx dz : ℕ) (L pi0 sigma0 : ℝ)
    (hk : 2 ≤ k) (hkx : k ≤ dx) (hkz : k ≤ dz) (hL : 1 ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ∀ A : NetLibrary k dx dz n L pi0 sigma0,
        ((@Fintype.card A.index A.finiteIndex : ℕ) : ℝ) ≤
          C * Real.rpow (n : ℝ) ((4 * dz * dx + dx : ℝ) / 2) := by
  let D : ℝ := 4 * Real.sqrt (dz * dx) + Real.sqrt dx
  let K : ℝ := 2 * L * D + 2
  let m : ℕ := 4 * dz * dx + dx
  refine ⟨K ^ m, ?_, ?_⟩
  · have hD : 0 < D := by
      dsimp [D]
      have hdx : 0 < dx := lt_of_lt_of_le (by omega : 0 < k) hkx
      positivity
    have hK : 0 < K := by dsimp [K]; nlinarith
    positivity
  · intro n hn A
    letI : Fintype A.index := A.finiteIndex
    have hdx : 0 < dx := lt_of_lt_of_le (by omega : 0 < k) hkx
    have hdz : 0 < dz := lt_of_lt_of_le (by omega : 0 < k) hkz
    have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast Nat.zero_lt_of_lt hn)
    have hsqrt1 : 1 ≤ Real.sqrt (n : ℝ) :=
      Real.one_le_sqrt.mpr (by exact_mod_cast hn)
    have hscale := A.scale_pos hn hdx hdz
    have hcardNat : Fintype.card A.index ≤
        (⌈2 * L / A.scale⌉₊ + 1) ^ Fintype.card (NetSummaryCoord dx dz) := by
      calc
        Fintype.card A.index ≤
            Fintype.card (NetSummaryCoord dx dz → Fin (⌈2 * L / A.scale⌉₊ + 1)) :=
          Fintype.card_le_of_injective _ (A.gridCode_injective hscale)
        _ = _ := by rw [Fintype.card_fun, Fintype.card_fin]
    have hscaleForm : 2 * L / A.scale = 2 * L * D * Real.sqrt (n : ℝ) := by
      rw [A.scale_eq]
      dsimp [D]
      field_simp
    have hx0 : 0 ≤ 2 * L / A.scale := by positivity
    have hceil : ((⌈2 * L / A.scale⌉₊ + 1 : ℕ) : ℝ) ≤
        K * Real.sqrt (n : ℝ) := by
      rw [hscaleForm]
      have hc := Nat.ceil_lt_add_one hx0
      rw [hscaleForm] at hc
      dsimp [K]
      norm_num at hc ⊢
      nlinarith
    have hm : Fintype.card (NetSummaryCoord dx dz) = m := by
      simpa [m] using netSummaryCoord_card dx dz
    have hpow : (((⌈2 * L / A.scale⌉₊ + 1 : ℕ) : ℝ) ^ m) ≤
        (K * Real.sqrt (n : ℝ)) ^ m := by gcongr
    calc
      ((Fintype.card A.index : ℕ) : ℝ) ≤
          (((⌈2 * L / A.scale⌉₊ + 1 : ℕ) : ℝ) ^ m) := by
        exact_mod_cast (hm ▸ hcardNat)
      _ ≤ (K * Real.sqrt (n : ℝ)) ^ m := hpow
      _ = K ^ m * Real.rpow (n : ℝ) ((m : ℝ) / 2) := by
        rw [mul_pow, Real.sqrt_eq_rpow]
        rw [← Real.rpow_mul_natCast (by positivity)]
        congr 2
        ring
      _ = K ^ m * Real.rpow (n : ℝ) ((4 * dz * dx + dx : ℝ) / 2) := by
        simp [m]

/-- Every signal basis at a model summary supplies latent-effect diagonal coordinates and the
corresponding left/right anchor coordinates. -/
theorem modelCompressedCoordinates_exists
    {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (Q : ModelLaw k dx dz L pi0 sigma0) (V : SignalBasis dx k)
    (hV : V.SpansSignal Q.summary) :
    ∃ D : CausalSmith.Substrate.CollisionSafeSpectralLaw.RealDiagonalization
        (compressedOperator Q.summary V hV),
      D.eigenvalue = latentEffect Q.P ∧
      leftAnchor Q.summary V = Matrix.mulVec D.basisInv.transpose (latentMass Q.P) ∧
      Matrix.mulVec D.basisInv (rightAnchor V) = fun _ => 1 := by
  classical
  letI := Q.prob
  rcases Q.model.coreDomain with
    ⟨hk, hkx, _hkz, hL, hpi, _hpiMax, hsigma, _hsigmaMax⟩
  let B := targetFeature Q.P
  let R : RectMatrix k k := B.transpose * V.V
  let C : Bool → RectMatrix dz k := fun t =>
    referenceFeature Q.P t * latentArmWeights Q.P t
  have hMfac (t : Bool) : observedProxyMoment Q.summary t * V.V = C t * R := by
    rw [show Q.summary = obsSummary Q.P from rfl,
      observedProxyMoment_factorization Q.P hk hkx hL hpi Q.model t]
    simp only [C, R, B, Matrix.mul_assoc]
  have hNfac (t : Bool) : observedOutcomeProxyMoment Q.summary t * V.V =
      C t * Matrix.diagonal (latentMean Q.P t) * R := by
    rw [show Q.summary = obsSummary Q.P from rfl,
      observedOutcomeProxyMoment_factorization Q.P hk hpi Q.model t]
    simp only [C, R, B, Matrix.mul_assoc]
  have hAinj (t : Bool) : Function.Injective (Matrix.toEuclideanLin
      (observedProxyMoment Q.summary t * V.V)) := by
    have hm := observedProxyMoment_compression_margin Q.P hk hkx hL hpi hsigma
      Q.model t V hV
    apply publishedMomentIdentity_injective_of_signalMinSingular_pos
    exact (mul_pos hpi (sq_pos_of_pos hsigma)).trans_le hm.2
  have hRinj : Function.Injective (Matrix.toEuclideanLin R) := by
    intro x y hxy
    apply hAinj false
    rw [hMfac false]
    simpa [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec] using
      congrArg (Matrix.toEuclideanLin (C false)) hxy
  have hRunit : IsUnit R.det := by
    apply (Matrix.isUnit_iff_isUnit_det _).mp
    apply Matrix.mulVec_injective_iff_isUnit.mp
    intro x y hxy
    apply congrArg WithLp.ofLp
    apply hRinj
    simpa [Matrix.toEuclideanLin_apply] using congrArg (WithLp.toLp 2) hxy
  letI := Matrix.invertibleOfIsUnitDet R hRunit
  have hterm (t : Bool) :
      penroseInverse (observedProxyMoment Q.summary t * V.V) *
          (observedOutcomeProxyMoment Q.summary t * V.V) =
        R⁻¹ * Matrix.diagonal (latentMean Q.P t) * R := by
    have hNrewrite : observedOutcomeProxyMoment Q.summary t * V.V =
        (observedProxyMoment Q.summary t * V.V) *
          (R⁻¹ * Matrix.diagonal (latentMean Q.P t) * R) := by
      rw [hMfac t, hNfac t]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc R R⁻¹, Matrix.mul_inv_of_invertible, Matrix.one_mul]
    rw [hNrewrite, ← Matrix.mul_assoc,
      publishedMomentIdentity_penrose_left_inverse_of_injective _ (hAinj t), Matrix.one_mul]
  have hD : compressedOperator Q.summary V hV =
      R⁻¹ * Matrix.diagonal (latentEffect Q.P) * R := by
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
    by_cases hab : a = b <;> simp [Matrix.diagonal_apply, hab, latentEffect]
  let D : CausalSmith.Substrate.CollisionSafeSpectralLaw.RealDiagonalization
      (compressedOperator Q.summary V hV) :=
    { basis := R⁻¹
      basisInv := R
      eigenvalue := latentEffect Q.P
      basis_mul_inv := Matrix.inv_mul_of_invertible R
      inv_mul_basis := Matrix.mul_inv_of_invertible R
      reconstruct := hD }
  have hCinj : Function.Injective (Matrix.toEuclideanLin (C false)) := by
    intro x y hxy
    have hpre : Matrix.toEuclideanLin (observedProxyMoment Q.summary false * V.V)
        (Matrix.toEuclideanLin R⁻¹ x) =
        Matrix.toEuclideanLin (observedProxyMoment Q.summary false * V.V)
          (Matrix.toEuclideanLin R⁻¹ y) := by
      rw [hMfac false]
      apply PiLp.ext
      intro i
      simpa [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec] using
        congrArg (fun z : Euc dz => z i) hxy
    have hxy' := hAinj false hpre
    have h := congrArg (Matrix.toEuclideanLin R) hxy'
    simpa [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec,
      Matrix.mul_inv_of_invertible] using h
  have hMraw : observedProxyMoment Q.summary false = C false * B.transpose := by
    rw [show Q.summary = obsSummary Q.P from rfl,
      observedProxyMoment_factorization Q.P hk hkx hL hpi Q.model false]
  have hBt : penroseInverse (C false) * observedProxyMoment Q.summary false =
      B.transpose := by
    rw [hMraw, ← Matrix.mul_assoc,
      publishedMomentIdentity_penrose_left_inverse_of_injective _ hCinj, Matrix.one_mul]
  have hBfac : B = (observedProxyMoment Q.summary false).transpose *
      (penroseInverse (C false)).transpose := by
    have ht := congrArg Matrix.transpose hBt
    simpa [Matrix.transpose_mul] using ht.symm
  have hBmem (x : Euc k) : Matrix.toEuclideanLin B x ∈
      LinearMap.range (Matrix.toEuclideanLin V.V) := by
    rw [hV]
    apply show LinearMap.range (Matrix.toEuclideanLin
      (observedProxyMoment Q.summary false).transpose) ≤ signalRowspace Q.summary from
        le_sup_left
    refine ⟨Matrix.toEuclideanLin (penroseInverse (C false)).transpose x, ?_⟩
    rw [hBfac]
    apply PiLp.ext
    intro i
    simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec]
  have hproj : V.V * V.V.transpose * B = B := by
    apply Matrix.toEuclideanLin.injective
    apply LinearMap.ext
    intro x
    rcases hBmem x with ⟨y, hy⟩
    have hgram : V.V.transpose * V.V = (1 : RectMatrix k k) := by
      ext a b
      simpa [Matrix.mul_apply, Matrix.one_apply] using V.orthonormal a b
    apply PiLp.ext
    intro i
    change ((V.V * V.V.transpose * B).mulVec x.ofLp) i = (B.mulVec x.ofLp) i
    have hyfun : V.V.mulVec y.ofLp = B.mulVec x.ofLp := by
      simpa [Matrix.toEuclideanLin_apply] using congrArg WithLp.ofLp hy
    calc
      _ = ((V.V * V.V.transpose).mulVec (B.mulVec x.ofLp)) i := by
        exact congrFun (Matrix.mulVec_mulVec x.ofLp (V.V * V.V.transpose) B).symm i
      _ = (V.V.mulVec (V.V.transpose.mulVec (B.mulVec x.ofLp))) i := by
        exact congrFun (Matrix.mulVec_mulVec (B.mulVec x.ofLp) V.V V.V.transpose).symm i
      _ = (V.V.mulVec (V.V.transpose.mulVec (V.V.mulVec y.ofLp))) i := by rw [hyfun]
      _ = (V.V.mulVec ((V.V.transpose * V.V).mulVec y.ofLp)) i := by
        exact congrArg (fun z : Fin k → ℝ => (V.V.mulVec z) i)
          (Matrix.mulVec_mulVec y.ofLp V.V.transpose V.V)
      _ = (V.V.mulVec y.ofLp) i := by rw [hgram, Matrix.one_mulVec]
      _ = (B.mulVec x.ofLp) i := congrFun hyfun i
  have hBfactor : B = V.V * R.transpose := by
    rw [show R.transpose = V.V.transpose * B by simp [R, Matrix.transpose_mul]]
    simpa [Matrix.mul_assoc] using hproj.symm
  have hmX : Q.summary.mX = Matrix.mulVec B (latentMass Q.P) :=
    publishedMomentIdentity_obsSummary_mX_factorization Q.P hpi Q.model
  have hanchor : Matrix.mulVec B.transpose (firstBasis dx) = fun _ => 1 :=
    publishedMomentIdentity_targetFeature_transpose_firstBasis Q.P hk hkx hpi Q.model
  have hRt : R.transpose = V.V.transpose * B := by simp [R, Matrix.transpose_mul]
  have hBt' : B.transpose = R * V.V.transpose := by
    have ht := congrArg Matrix.transpose hBfactor
    simpa [Matrix.transpose_mul] using ht
  have hleft : leftAnchor Q.summary V = Matrix.mulVec R.transpose (latentMass Q.P) := by
    calc
      leftAnchor Q.summary V = Matrix.mulVec V.V.transpose Q.summary.mX := by
        funext a
        simp [leftAnchor, Matrix.mulVec, dotProduct, mul_comm]
      _ = Matrix.mulVec V.V.transpose (Matrix.mulVec B (latentMass Q.P)) := by rw [hmX]
      _ = Matrix.mulVec (V.V.transpose * B) (latentMass Q.P) :=
        Matrix.mulVec_mulVec _ _ _
      _ = _ := by rw [← hRt]
  have hright : Matrix.mulVec R (rightAnchor V) = fun _ => 1 := by
    rw [show rightAnchor V = Matrix.mulVec V.V.transpose (firstBasis dx) by
      funext a
      simp [rightAnchor, Matrix.mulVec, dotProduct]]
    rw [Matrix.mulVec_mulVec, ← hBt', hanchor]
  exact ⟨D, rfl, hleft, hright⟩

/-- Any valid complete projector enumeration gives the same extensional law as the positive
diagonal-coordinate law, even when eigenvalues collide and the list contains dummy slots. -/
theorem complete_projectorLaw_eq
    {k : ℕ} {radius : ℝ} {A : RectMatrix k k}
    (D : CausalSmith.Substrate.CollisionSafeSpectralLaw.RealDiagonalization A)
    (mass value left right : Fin k → ℝ)
    (hmasspos : ∀ u, 0 < mass u)
    (htrue : AtomicLaw.Valid
      ({ weight := mass, atom := D.eigenvalue } : AtomicLaw k radius))
    (hcomplete : ∀ u, ∃ i, value i = D.eigenvalue u)
    (hleft : left = Matrix.mulVec D.basisInv.transpose mass)
    (hright : Matrix.mulVec D.basisInv right = fun _ => 1)
    (hout : AtomicLaw.Valid
      (⟨fun i => ∑ a, left a * (∑ b,
          polynomialAggregateProjector A value i a b * right b), value⟩ :
        AtomicLaw k radius)) :
    AtomicLaw.LawModulo.ofProbabilityLaw ⟨_, hout⟩ =
      AtomicLaw.LawModulo.ofProbabilityLaw ⟨_, htrue⟩ := by
  classical
  let out : AtomicLaw k radius :=
    ⟨fun i => ∑ a, left a * (∑ b,
      polynomialAggregateProjector A value i a b * right b), value⟩
  let trueLaw : AtomicLaw k radius := ⟨mass, D.eigenvalue⟩
  have hw (i : Fin k) : out.weight i =
      ∑ u, if D.eigenvalue u = value i then mass u else 0 := by
    dsimp [out]
    rw [show polynomialAggregateProjector A value i =
        if value i ∈ D.spectralValues then D.projector (value i) else 0 by
      change CausalSmith.Substrate.CollisionSafeSpectralLaw.polynomialSpectralProjector
        A value i = _
      exact
        CausalSmith.Substrate.CollisionSafeSpectralLaw.polynomialSpectralProjector_eq_projector_or_zero_of_complete
          D value hcomplete i]
    split_ifs with hi
    · exact CausalSmith.Substrate.CollisionSafeSpectralLaw.anchor_projector_eq_clusterMass
        D mass left right hleft hright (value i)
    · have hn (u : Fin k) : D.eigenvalue u ≠ value i := by
        intro h
        apply hi
        simp [CausalSmith.Substrate.CollisionSafeSpectralLaw.RealDiagonalization.spectralValues,
          ← h]
      simp [hn]
  have hintegral :=
    CausalSmith.Substrate.CollisionSafeSpectralLaw.complete_clusterMass_integral_eq
      mass D.eigenvalue value hmasspos htrue.2.1 (fun u => by
        obtain ⟨i, hi⟩ := hcomplete u
        exact ⟨i, hi.symm⟩) (by simpa [← hw] using hout.2.1)
  apply Quotient.sound
  change AtomicLaw.ProbabilityLaw.MeasureEquivalent ⟨out, hout⟩ ⟨trueLaw, htrue⟩
  unfold AtomicLaw.ProbabilityLaw.MeasureEquivalent
  ext s hs
  simp only [AtomicLaw.ProbabilityLaw.toMeasure, AtomicLaw.toMeasure,
    Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    Measure.dirac_apply' _ hs]
  have hreal := hintegral (fun x => s.indicator 1 x)
  change (∑ i, ENNReal.ofReal (out.weight i) • s.indicator 1 (out.atom i)) =
    ∑ i, ENNReal.ofReal (trueLaw.weight i) • s.indicator 1 (trueLaw.atom i)
  simp_rw [hw]
  dsimp [out, trueLaw] at hreal ⊢
  have hcluster (i : Fin k) :
      0 ≤ ∑ u, if D.eigenvalue u = value i then mass u else 0 := by
    rw [← hw i]
    exact hout.1 i
  calc
    (∑ i, ENNReal.ofReal (∑ u, if D.eigenvalue u = value i then mass u else 0) *
        s.indicator 1 (value i)) =
        ENNReal.ofReal (∑ i, (∑ u, if D.eigenvalue u = value i then mass u else 0) *
          s.indicator 1 (value i)) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by
        exact mul_nonneg (hcluster i) (Set.indicator_nonneg (fun _ _ => zero_le_one) _))]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : value i ∈ s <;> simp [Set.indicator, hi]
    _ = ENNReal.ofReal (∑ i, mass i * s.indicator 1 (D.eigenvalue i)) :=
      congrArg ENNReal.ofReal hreal
    _ = ∑ i, ENNReal.ofReal (mass i) * s.indicator 1 (D.eigenvalue i) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by
        exact mul_nonneg (hmasspos i).le (Set.indicator_nonneg (fun _ _ => zero_le_one) _))]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : D.eigenvalue i ∈ s <;> simp [Set.indicator, hi]

private lemma net_latentMass_pos
    {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (Q : ModelLaw k dx dz L pi0 sigma0) (u : Fin k) : 0 < latentMass Q.P u := by
  letI := Q.prob
  have hp := Q.model.latentArmPositivity u false
  have hle : Q.P.real (latentCell u false) ≤ Q.P.real (latentClass u) :=
    measureReal_mono (fun _ h => h.1)
  rcases Q.model.coreDomain with ⟨_, _, _, _, hpi, _⟩
  exact hpi.trans_le (hp.trans hle)

private lemma exactRealSpectralRun_effectLaw_congr
    {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (primitives : ExactRealPrimitives) {s q : SummarySpace dx dz}
    (h : s = q) (hs : s ∈ admissibleImage k dx dz L pi0 sigma0)
    (hq : q ∈ admissibleImage k dx dz L pi0 sigma0) :
    (exactRealSpectralRun primitives s hs).output.effectLaw =
      (exactRealSpectralRun primitives q hq).output.effectLaw := by
  subst q
  rfl

private theorem exactRealSpectralRun_eq_quotient_of_model
    {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (primitives : ExactRealPrimitives) (Q : ModelLaw k dx dz L pi0 sigma0)
    (hs : Q.summary ∈ admissibleImage k dx dz L pi0 sigma0) :
    (exactRealSpectralRun primitives Q.summary hs).output.effectLaw = by
      letI := Q.prob
      exact quotientLaw Q.P Q.model := by
  classical
  letI := Q.prob
  let run := exactRealSpectralRun primitives Q.summary hs
  obtain ⟨D, hEig, hleft, hright⟩ :=
    modelCompressedCoordinates_exists Q run.output.basis run.output.spans
  have hcomplete (u : Fin k) : ∃ i, run.output.eigenvalue i = D.eigenvalue u := by
    have hz : MatrixEigenvalue
        (compressedOperator Q.summary run.output.basis run.output.spans)
        (D.eigenvalue u) :=
      D.diagonal_eigenvalue_is_complexEigenvalue u
    obtain ⟨i, hi⟩ := run.output.eigenvalue_complete _ hz
    refine ⟨i, ?_⟩
    exact_mod_cast hi.symm
  have htrue := quotientLawRaw_valid Q.P Q.model
  have heq := complete_projectorLaw_eq D (latentMass Q.P) run.output.eigenvalue
    (leftAnchor Q.summary run.output.basis) (rightAnchor run.output.basis)
    (net_latentMass_pos Q) (by simpa [quotientLawRaw, hEig] using htrue)
    hcomplete hleft hright
    run.output.lawValid
  simpa [run, RepresentativeSpectralData.effectLaw, quotientLaw, quotientLawRaw, hEig] using heq

/-- An arbitrary result-bearing primitive run at a feasible summary denotes its model quotient
law; no canonical choice of signal basis or root enumeration is assumed. -/
theorem exactRealSpectralRun_eq_quotient
    {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (primitives : ExactRealPrimitives) (s : SummarySpace dx dz)
    (hs : s ∈ admissibleImage k dx dz L pi0 sigma0) :
    ∃ Q : ModelLaw k dx dz L pi0 sigma0, Q.summary = s ∧
      (exactRealSpectralRun primitives s hs).output.effectLaw = by
        letI := Q.prob
        exact quotientLaw Q.P Q.model := by
  let Q : ModelLaw k dx dz L pi0 sigma0 := Classical.choose hs
  have hQs : Q.summary = s := Classical.choose_spec hs
  let hsQ : Q.summary ∈ admissibleImage k dx dz L pi0 sigma0 := ⟨Q, rfl⟩
  refine Exists.intro Q (And.intro hQs ?_)
  exact (exactRealSpectralRun_effectLaw_congr primitives hQs.symm hs hsQ).trans
    (exactRealSpectralRun_eq_quotient_of_model primitives Q hsQ)

/-- The exhaustive finite fold is Borel measurable, and hence so is the law returned by the
result-bearing program. -/
theorem netLawEstimator_measurable
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (primitives : ExactRealPrimitives) (A : NetLibrary k dx dz n L pi0 sigma0) :
    Measurable (netLawEstimator primitives A) := by
  classical
  letI : Fintype A.index := A.finiteIndex
  letI : MeasurableSpace A.index := ⊤
  letI : MeasurableSpace (Option A.index) := ⊤
  have hsummary : Measurable A.summary := measurable_of_finite _
  have hrank : Measurable A.lexRank := measurable_of_finite _
  have hdist (f : SummarySpace dx dz → A.index) (hf : Measurable f) :
      Measurable (fun s => dS (A.summary (f s)) s) := by
    let g : SummarySpace dx dz → ℝ := fun s =>
      ∑ i, {q | f q = i}.indicator (fun q => dS (A.summary i) q) s
    have hg : Measurable g := by
      dsimp [g]
      apply Finset.measurable_sum
      intro i _
      apply Measurable.indicator
      · exact ((dS_continuous dx dz).uncurry_left (A.summary i)).measurable
      · exact hf (measurableSet_singleton i)
    convert hg using 1
    funext s
    simp [g, Set.indicator]
  have hbetter (f : SummarySpace dx dz → A.index) (hf : Measurable f) (j : A.index) :
      Measurable (fun s => A.betterIndex s (f s) j) := by
    unfold NetLibrary.betterIndex
    apply Measurable.ite
    · exact measurableSet_lt (by fun_prop) (hdist f hf)
    · exact measurable_const
    · apply Measurable.ite
      · exact measurableSet_lt (hdist f hf) (by fun_prop)
      · exact hf
      · apply Measurable.ite
        · exact measurableSet_lt (by fun_prop) (hrank.comp hf)
        · exact measurable_const
        · exact hf
  have hfold (l : List A.index) (i : A.index) :
      Measurable (fun s : SummarySpace dx dz => l.foldl (A.betterIndex s) i) := by
    induction l using List.reverseRecOn with
    | nil => exact measurable_const
    | append_singleton l j ih =>
        simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
        exact hbetter _ ih j
  have hsel : Measurable (nearestLibraryIndex A) := by
    unfold nearestLibraryIndex
    split
    · exact measurable_const
    · exact (measurable_of_finite (fun i : A.index => some i)).comp (hfold _ _)
  let out : Option A.index → AtomicLaw.LawModulo k (effectRadius dz L sigma0)
    | none => AtomicLaw.LawModulo.deltaZeroLaw A.k_pos A.radius_nonneg
    | some i => (exactRealSpectralRun primitives (A.summary i)
        (A.representative_feasible i)).output.effectLaw
  have hout : Measurable out := measurable_of_finite _
  have heq : netLawEstimator primitives A = out ∘ nearestLibraryIndex A ∘ empSummary := by
    funext sample
    unfold netLawEstimator netExactRealProgram
    split <;> simp [out, Function.comp_def, *]
  rw [heq]
  exact hout.comp (hsel.comp empSummary_measurable)

private lemma netTraceCost_total_aux (trace : List NetPrimitiveOperation)
    (cost : NetOperationCount) :
    (trace.foldl (fun c op => c.add op.cost) cost).total = cost.total + trace.length := by
  induction trace generalizing cost with
  | nil => simp
  | cons op trace ih =>
      rw [List.foldl_cons, ih]
      cases op <;> simp [NetOperationCount.add, NetOperationCount.total,
        NetPrimitiveOperation.cost] <;> omega

lemma netTraceCost_total_eq_length (trace : List NetPrimitiveOperation) :
    (netTraceCost trace).total = trace.length := by
  simpa [netTraceCost, NetOperationCount.total] using
    netTraceCost_total_aux trace ⟨0, 0, 0, 0⟩

/-- Exact trace accounting bounds the program work by the summary scan, the exhaustive library
scan, and the fixed five-operation spectral tail. -/
lemma netOperationCount_le
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (primitives : ExactRealPrimitives) (A : NetLibrary k dx dz n L pi0 sigma0)
    (sample : Fin n → Obs dx dz) :
    (netOperationCount primitives A sample).total ≤
      n * (4 * dz * dx + dx) +
        @Fintype.card A.index A.finiteIndex * (4 * dz * dx + dx + 5) + 5 := by
  letI : Fintype A.index := A.finiteIndex
  rw [show (netOperationCount primitives A sample).total =
      (netExactRealProgram primitives A sample).trace.length by
    exact netTraceCost_total_eq_length _]
  rw [netExactRealProgram_trace_eq]
  simp only [List.length_append, netSummaryTrace, List.length_replicate,
    netSearchTrace, List.length_flatMap]
  simp only [List.length_singleton]
  have hindex : A.indexList.length = Fintype.card A.index := by
    simp [NetLibrary.indexList]
  have hscalar : 4 * dz * dx + dx + 4 + 1 = 4 * dz * dx + dx + 5 := by omega
  have hsum : ∀ xs : List A.index,
      (xs.map (fun _ => 4 * dz * dx + dx + 4 + 1)).sum =
        xs.length * (4 * dz * dx + dx + 5) := by
    intro xs
    simp [hscalar]
  rw [hsum A.indexList]
  rw [hindex]
  split
  · simp only [List.length_nil]
    omega
  · rw [ExactRealSpectralRun.trace_eq_fixed]
    simp

/-- The exact trace accounting and the grid-cardinality certificate combine into the displayed
polynomial work bound with one class-dependent positive constant. -/
theorem netOperationCount_polynomial_bound
    (k dx dz : ℕ) (L pi0 sigma0 : ℝ)
    (hk : 2 ≤ k) (hkx : k ≤ dx) (hkz : k ≤ dz) (hL : 1 ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ∀ primitives : ExactRealPrimitives,
      ∀ A : NetLibrary k dx dz n L pi0 sigma0,
      ∀ sample : Fin n → Obs dx dz,
        ((netOperationCount primitives A sample).total : ℝ) ≤
          C * ((n : ℝ) + Real.rpow (n : ℝ) ((4 * dz * dx + dx : ℝ) / 2)) := by
  obtain ⟨Ccard, hCcard, hcard⟩ :=
    netLibrary_card_polynomial_bound k dx dz L pi0 sigma0 hk hkx hkz hL
  let m : ℝ := 4 * dz * dx + dx
  let Cwork : ℝ := m + Ccard * (m + 5) + 5
  have hmpos : 0 < m := by
    dsimp [m]
    have hdx : 0 < dx := lt_of_lt_of_le (by omega : 0 < k) hkx
    positivity
  have hCwork : 0 < Cwork := by dsimp [Cwork]; positivity
  refine ⟨Cwork, hCwork, ?_⟩
  intro n hn primitives A sample
  let r : ℝ := Real.rpow (n : ℝ) ((4 * dz * dx + dx : ℝ) / 2)
  have hr0 : 0 ≤ r := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hexp0 : 0 ≤ ((4 * dz * dx + dx : ℝ) / 2) := by positivity
  have hr1 : 1 ≤ r := by
    exact Real.one_le_rpow (by exact_mod_cast hn) hexp0
  have hopNat := netOperationCount_le primitives A sample
  have hopConcrete : ((netOperationCount primitives A sample).total : ℝ) ≤
      (n : ℝ) * (4 * dz * dx + dx : ℕ) +
        ((@Fintype.card A.index A.finiteIndex : ℕ) : ℝ) *
          (4 * dz * dx + dx + 5 : ℕ) + 5 := by
    exact_mod_cast hopNat
  have hop : ((netOperationCount primitives A sample).total : ℝ) ≤
      (n : ℝ) * m + ((@Fintype.card A.index A.finiteIndex : ℕ) : ℝ) *
        (m + 5) + 5 := by
    simpa [m, Nat.cast_add, Nat.cast_mul] using hopConcrete
  have hcardA := hcard n hn A
  have hm5 : 0 ≤ m + 5 := by positivity
  have hM : m ≤ Cwork := by dsimp [Cwork]; nlinarith [hCcard.le, hmpos.le]
  have htail : Ccard * (m + 5) + 5 ≤ Cwork := by
    dsimp [Cwork]
    linarith [hmpos.le]
  calc
    ((netOperationCount primitives A sample).total : ℝ)
        ≤ (n : ℝ) * m + ((@Fintype.card A.index A.finiteIndex : ℕ) : ℝ) *
            (m + 5) + 5 := hop
    _ ≤ (n : ℝ) * m + (Ccard * r) * (m + 5) + 5 * r := by
      gcongr
      nlinarith
    _ = m * (n : ℝ) + (Ccard * (m + 5) + 5) * r := by ring
    _ ≤ Cwork * (n : ℝ) + Cwork * r := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hM (Nat.cast_nonneg n))
        (mul_le_mul_of_nonneg_right htail hr0)
    _ = Cwork * ((n : ℝ) + r) := by ring

lemma netProgram_selected_eq_nearest
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (primitives : ExactRealPrimitives) (A : NetLibrary k dx dz n L pi0 sigma0)
    (sample : Fin n → Obs dx dz) :
    (netExactRealProgram primitives A sample).selected =
      nearestLibraryIndex A (empSummary sample) := by
  unfold netExactRealProgram
  split <;> simp_all

/-- A rank-`r` comparison with last signal singular value at least `s0` remains exactly
`r`-dimensional after thresholding at `s0 / 2` under any perturbation strictly below that
threshold. -/
lemma thresholdRecoversMatrixDimension_of_rank_perturbation_half
    {rows cols r : ℕ} {s0 e : ℝ} (A M : RectMatrix rows cols)
    (hrpos : 0 < r) (hs0 : 0 < s0) (hrank : M.rank = r)
    (hmargin : s0 ≤ singularValue M (r - 1))
    (hAM : ‖matrixCLM (A - M)‖ ≤ e) (hsmall : e < s0 / 2) :
    ThresholdRecoversMatrixDimension r (s0 / 2) A := by
  have hkth : s0 / 2 < singularValue A (r - 1) := by
    have h := singularValue_lower_of_perturbation A M hmargin hAM
    linarith
  constructor
  · intro j hj
    have hanti := (Matrix.toEuclideanLin A).singularValues_antitone
      (Nat.le_sub_one_of_lt hj)
    change s0 / 2 ≤ (Matrix.toEuclideanLin A).singularValues j
    change s0 / 2 < (Matrix.toEuclideanLin A).singularValues (r - 1) at hkth
    exact hkth.le.trans hanti
  · intro j hj
    have hz : singularValue M j = 0 := by
      unfold singularValue
      apply (Matrix.toEuclideanLin M).singularValues_eq_zero_iff_le_finrank_range.mpr
      have hrange : Module.finrank ℝ (Matrix.toEuclideanLin M).range = M.rank :=
        (M.rank_eq_finrank_range_toLin
          (EuclideanSpace.basisFun (Fin rows) ℝ).toBasis
          (EuclideanSpace.basisFun (Fin cols) ℝ).toBasis).symm
      rw [hrange, hrank]
      exact hj
    have hadd : M + (A - M) = A := by abel
    have hw := singular_value_weyl (j := j) M (A - M)
    rw [hadd, hz, sub_zero] at hw
    have hnonneg : 0 ≤ singularValue A j :=
      (Matrix.toEuclideanLin A).singularValues_nonneg _
    rw [abs_of_nonneg hnonneg] at hw
    exact lt_of_le_of_lt (hw.trans hAM) hsmall

/-- The quantitative model rank certificate gives the perturbation clause required by every
stored representative summary. -/
lemma modelSummary_thresholdRecovers_of_perturbation
    {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (Q : ModelLaw k dx dz L pi0 sigma0) (H : RectMatrix (2 * dz) dx)
    (hH : ‖matrixCLM H‖ < pi0 * sigma0 ^ 2 / 2) :
    ThresholdRecoversMatrixDimension k (pi0 * sigma0 ^ 2 / 2)
      (stackedProxyMoment Q.summary + H) := by
  letI := Q.prob
  rcases Q.model.coreDomain with ⟨hk, hkx, _hkz, hL, hpi, _hpiMax, hsigma, _hsigmaMax⟩
  obtain ⟨facts⟩ := modelCompressedSpectralFacts_exists Q
  have hrank : (stackedProxyMoment Q.summary).rank = k := by
    rw [(stackedProxyMoment Q.summary).rank_eq_finrank_range_toLin
      (EuclideanSpace.basisFun (Fin (2 * dz)) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin dx) ℝ).toBasis]
    exact facts.stackedRank
  apply thresholdRecoversMatrixDimension_of_rank_perturbation_half
    (e := ‖matrixCLM H‖) (stackedProxyMoment Q.summary + H) (stackedProxyMoment Q.summary)
    (by omega) (mul_pos hpi (sq_pos_of_pos hsigma)) hrank
  · rw [show Q.summary = obsSummary Q.P from rfl]
    exact stackedProxyMoment_minSingular Q.P hk hkx hL hpi hsigma Q.model
  · rw [show stackedProxyMoment Q.summary + H - stackedProxyMoment Q.summary = H by abel]
  · exact hH

private lemma nearestLibraryIndex_exists_of_model
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (A : NetLibrary k dx dz n L pi0 sigma0)
    (Q : ModelLaw k dx dz L pi0 sigma0) (s : SummarySpace dx dz) :
    ∃ i, nearestLibraryIndex A s = some i := by
  classical
  have himage : (admissibleImage k dx dz L pi0 sigma0).Nonempty :=
    ⟨Q.summary, ⟨Q, rfl⟩⟩
  have hnonempty : Nonempty A.index :=
    A.index_nonempty_iff.mpr (Set.nonempty_iff_ne_empty.mp himage)
  let i0 : A.index := Classical.choice hnonempty
  unfold nearestLibraryIndex
  cases hlist : A.indexList with
  | nil =>
      exfalso
      have : i0 ∈ A.indexList := by simp [NetLibrary.indexList]
      simp [hlist] at this
  | cons i is => exact ⟨is.foldl (A.betterIndex s) i, rfl⟩

/-- Nearest-library selection plus the gap-free model modulus gives the deterministic advised
estimator bound. -/
theorem netEstimator_wass1_le
    {k dx dz n : ℕ} {L pi0 sigma0 Cmod : ℝ}
    (primitives : ExactRealPrimitives) (A : NetLibrary k dx dz n L pi0 sigma0)
    (hCmod : 0 ≤ Cmod)
    (hmodel : ∀ (P Q : ModelLaw k dx dz L pi0 sigma0),
      AtomicLaw.LawModulo.wass1 (by letI := P.prob; exact quotientLaw P.P P.model)
          (by letI := Q.prob; exact quotientLaw Q.P Q.model) ≤
        Cmod * dS P.summary Q.summary)
    (P : Measure (FullData k dx dz)) (hP : IsProbabilityMeasure P)
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P)
    (sample : Fin n → Obs dx dz) :
    AtomicLaw.LawModulo.wass1 (netLawEstimator primitives A sample)
      (by letI := hP; exact quotientLaw P hM) ≤
      Cmod * (2 * dS (empSummary sample) (obsSummary P) + (Real.sqrt n)⁻¹) := by
  letI := hP
  let QP : ModelLaw k dx dz L pi0 sigma0 := ⟨P, hP, hM⟩
  obtain ⟨i, hi⟩ := nearestLibraryIndex_exists_of_model A QP (empSummary sample)
  have hsel : (netExactRealProgram primitives A sample).selected = some i := by
    rw [netProgram_selected_eq_nearest, hi]
  have hnear := (nearestLibraryIndex_spec A (empSummary sample) i hi).1
  obtain ⟨j, hj⟩ := A.covers QP.summary ⟨QP, rfl⟩
  obtain ⟨Qi, hQi, hrun⟩ :=
    exactRealSpectralRun_eq_quotient primitives (A.summary i) (A.representative_feasible i)
  have hdist : dS Qi.summary QP.summary ≤
      2 * dS (empSummary sample) QP.summary + (Real.sqrt n)⁻¹ := by
    rw [hQi]
    calc
      dS (A.summary i) QP.summary ≤
          dS (A.summary i) (empSummary sample) +
            dS (empSummary sample) QP.summary := dS_triangle _ _ _
      _ ≤ dS (A.summary j) (empSummary sample) +
            dS (empSummary sample) QP.summary := by gcongr; exact hnear j
      _ ≤ (dS (A.summary j) QP.summary + dS QP.summary (empSummary sample)) +
            dS (empSummary sample) QP.summary := by
          gcongr
          exact dS_triangle _ _ _
      _ ≤ (Real.sqrt n)⁻¹ + dS (empSummary sample) QP.summary +
            dS (empSummary sample) QP.summary := by
          rw [dS_symm QP.summary (empSummary sample)]
          gcongr
      _ = 2 * dS (empSummary sample) QP.summary + (Real.sqrt n)⁻¹ := by ring
  have hout := netLawEstimator_eq_of_selected primitives A sample i hsel
  rw [hout, hrun]
  have hw := hmodel Qi QP
  exact hw.trans (mul_le_mul_of_nonneg_left hdist hCmod)

end

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
