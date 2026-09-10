import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.StructuredLatticeRounding

/-! # Stability of the prescribed polar factor -/

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

noncomputable section

open scoped Matrix.Norms.L2Operator

/-- The prescribed polar factor is Lipschitz at an orthonormal basis.  The factor `2` is stronger
than the factor `4` used in the frozen comparator estimate. -/
lemma prescribedPolarFactor_sub_signalBasis_norm_le
    {dx k : ℕ} (V : SignalBasis dx k) (G : RectMatrix dx k)
    (hG : 1 / 2 ≤ signalMinSingular G) {e : ℝ}
    (hclose : ‖matrixCLM (G - V.V)‖ ≤ e) :
    ‖matrixCLM (prescribedPolarFactor G hG - V.V)‖ ≤ 2 * e := by
  classical
  let H := inverseGramSqrt G hG
  let gram := G.transpose * G
  let P := prescribedPolarFactor G hG
  let S := gram * H
  have hpos : 0 < signalMinSingular G := lt_of_lt_of_le (by norm_num) hG
  have hinj := publishedMomentIdentity_injective_of_signalMinSingular_pos G hpos
  have hdet : IsUnit gram.det := by
    exact publishedMomentIdentity_gram_det_isUnit_of_injective G hinj
  have hHpsd : H.PosSemidef := (inverseGramSqrt_spec G hG).1
  have hHsq : H * H = gram⁻¹ := (inverseGramSqrt_spec G hG).2
  have hgram_inv : gram * gram⁻¹ = 1 := Matrix.mul_nonsing_inv gram hdet
  have hinv_gram : gram⁻¹ * gram = 1 := Matrix.nonsing_inv_mul gram hdet
  have hleft : (gram * H) * H = 1 := by
    rw [Matrix.mul_assoc, hHsq, hgram_inv]
  have hright : H * (H * gram) = 1 := by
    rw [← Matrix.mul_assoc, hHsq, hinv_gram]
  have hcomm : gram * H = H * gram := by
    calc
      gram * H = (gram * H) * 1 := by rw [Matrix.mul_one]
      _ = (gram * H) * (H * (H * gram)) := by rw [hright]
      _ = ((gram * H) * H) * (H * gram) := by simp only [Matrix.mul_assoc]
      _ = H * gram := by rw [hleft, Matrix.one_mul]
  have hmiddle : H * gram * H = 1 := by
    calc
      H * gram * H = H * (gram * H) := by rw [Matrix.mul_assoc]
      _ = H * (H * gram) := by rw [hcomm]
      _ = (H * H) * gram := by rw [Matrix.mul_assoc]
      _ = gram⁻¹ * gram := by rw [hHsq]
      _ = 1 := hinv_gram
  have hgramPsd : gram.PosSemidef := by
    dsimp [gram]
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial G]
    exact Matrix.posSemidef_conjTranspose_mul_self G
  have hSpsd : S.PosSemidef := by
    have hSinv : S = H⁻¹ := by
      exact hcomm.trans (Matrix.inv_eq_left_inv hmiddle).symm
    rw [hSinv]
    exact hHpsd.inv
  have hPS : P * S = G := by
    change (G * H) * (gram * H) = G
    calc
      (G * H) * (gram * H) = G * (H * gram * H) := by
        simp only [Matrix.mul_assoc]
      _ = G * (1 : RectMatrix k k) := by rw [hmiddle]
      _ = G := by rw [Matrix.mul_one]
  have hPorth : P.transpose * P = 1 := by
    exact prescribedPolarFactor_transpose_mul_self G hG
  let VP : SignalBasis dx k :=
    ⟨P, fun i j => by
      have hij := congr_fun (congr_fun hPorth i) j
      simpa [Matrix.mul_apply, Matrix.one_apply] using hij⟩
  have hHerm : S.IsHermitian := hSpsd.isHermitian
  let b := hHerm.eigenvectorBasis
  have heig_abs (i : Fin k) : |hHerm.eigenvalues i - 1| ≤ e := by
    let x : Euc k := b i
    have hxnorm : ‖x‖ = 1 := b.orthonormal.1 i
    have hlam0 : 0 ≤ hHerm.eigenvalues i := by
      simpa only [hHerm] using hSpsd.eigenvalues_nonneg i
    have hSx : Matrix.toEuclideanLin S x =
        hHerm.eigenvalues i • x := by
      apply PiLp.ext
      intro j
      simpa [x, b, Matrix.toEuclideanLin_apply] using
        congr_fun (hHerm.mulVec_eigenvectorBasis i) j
    have hGnorm : ‖Matrix.toEuclideanLin G x‖ = hHerm.eigenvalues i := by
      calc
        ‖Matrix.toEuclideanLin G x‖ = ‖Matrix.toEuclideanLin P (Matrix.toEuclideanLin S x)‖ := by
          rw [← hPS]
          simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec]
        _ = ‖Matrix.toEuclideanLin S x‖ := by
          have hn := (signalBasisLinearIsometry VP).norm_map
            (Matrix.toEuclideanLin S x)
          simpa [VP, signalBasisLinearIsometry] using hn
        _ = ‖hHerm.eigenvalues i • x‖ := by rw [hSx]
        _ = hHerm.eigenvalues i := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hlam0, hxnorm, mul_one]
    have hVnorm : ‖Matrix.toEuclideanLin V.V x‖ = 1 := by
      have hn := (signalBasisLinearIsometry V).norm_map x
      simpa [signalBasisLinearIsometry, hxnorm] using hn
    calc
      |hHerm.eigenvalues i - 1| =
          |‖Matrix.toEuclideanLin G x‖ - ‖Matrix.toEuclideanLin V.V x‖| := by
            rw [hGnorm, hVnorm]
      _ ≤ ‖Matrix.toEuclideanLin G x - Matrix.toEuclideanLin V.V x‖ :=
        abs_norm_sub_norm_le _ _
      _ = ‖matrixCLM (G - V.V) x‖ := by
        congr 1
        simp [matrixCLM, Matrix.toEuclideanLin_apply]
      _ ≤ ‖matrixCLM (G - V.V)‖ * ‖x‖ :=
        (matrixCLM (G - V.V)).le_opNorm x
      _ ≤ e := by rw [hxnorm, mul_one]; exact hclose
  have hSsub : ‖matrixCLM (S - 1)‖ ≤ e := by
    have hspectral := hHerm.spectral_theorem
    let U := hHerm.eigenvectorUnitary
    have hconj : S - 1 = (U : RectMatrix k k) *
        Matrix.diagonal (fun i => hHerm.eigenvalues i - 1) * star (U : RectMatrix k k) := by
      calc
        S - 1 =
            ((Unitary.conjStarAlgAut ℝ (RectMatrix k k)) U)
                (Matrix.diagonal (RCLike.ofReal ∘ hHerm.eigenvalues)) - 1 := by
              exact congrArg (fun A : RectMatrix k k => A - 1) hspectral
        _ = (U : RectMatrix k k) *
            Matrix.diagonal (fun i => hHerm.eigenvalues i - 1) *
              star (U : RectMatrix k k) := by
          rw [Unitary.conjStarAlgAut_apply]
          have hUstar : (U : RectMatrix k k) * star (U : RectMatrix k k) = 1 :=
            Unitary.coe_mul_star_self U
          rw [show (1 : RectMatrix k k) =
              (U : RectMatrix k k) * 1 * star (U : RectMatrix k k) by
            rw [Matrix.mul_one, hUstar]]
          rw [← Matrix.sub_mul, ← Matrix.mul_sub]
          congr 2
          ext i j
          by_cases hij : i = j
          · subst j
            simp
          · simp [Matrix.diagonal, hij]
    change ‖S - 1‖ ≤ e
    rw [hconj]
    calc
      ‖(U : RectMatrix k k) * Matrix.diagonal (fun i => hHerm.eigenvalues i - 1) *
          star (U : RectMatrix k k)‖ =
          ‖(U : RectMatrix k k) * Matrix.diagonal (fun i => hHerm.eigenvalues i - 1)‖ := by
            simpa using CStarRing.norm_mul_coe_unitary
              ((U : RectMatrix k k) * Matrix.diagonal (fun i => hHerm.eigenvalues i - 1))
              (star U)
      _ = ‖Matrix.diagonal (fun i => hHerm.eigenvalues i - 1)‖ := by
        exact CStarRing.norm_coe_unitary_mul U _
      _ = ‖fun i => hHerm.eigenvalues i - 1‖ := Matrix.l2_opNorm_diagonal _
      _ ≤ e := by
        apply (pi_norm_le_iff_of_nonneg (le_trans (norm_nonneg _) hclose)).2
        intro i
        simpa [Real.norm_eq_abs] using heig_abs i
  have hPG : ‖matrixCLM (P - G)‖ ≤ e := by
    have hdiff : P - G = P * (1 - S) := by rw [Matrix.mul_sub, Matrix.mul_one, hPS]
    rw [hdiff]
    apply le_trans (Matrix.l2_opNorm_mul _ _)
    have hPnorm : ‖P‖ ≤ 1 := by
      apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
      intro x
      have hn := (signalBasisLinearIsometry VP).norm_map x
      simpa [VP, signalBasisLinearIsometry] using hn.le
    calc
      ‖P‖ * ‖1 - S‖ ≤ 1 * ‖1 - S‖ := mul_le_mul_of_nonneg_right hPnorm (norm_nonneg _)
      _ = ‖S - 1‖ := by rw [one_mul, norm_sub_rev]
      _ ≤ e := hSsub
  have hdecomp : P - V.V = (P - G) + (G - V.V) := by abel
  rw [show prescribedPolarFactor G hG = P by rfl, hdecomp]
  calc
    ‖matrixCLM ((P - G) + (G - V.V))‖
        ≤ ‖matrixCLM (P - G)‖ + ‖matrixCLM (G - V.V)‖ := by
          change ‖(P - G) + (G - V.V)‖ ≤ ‖P - G‖ + ‖G - V.V‖
          exact norm_add_le _ _
    _ ≤ e + e := add_le_add hPG hclose
    _ = 2 * e := by ring

/-- The rounded grid and its prescribed polar factor satisfy the exact `cV = 4 * sqrt (dx*k)`
comparator bound used in the frozen proof. -/
lemma SignalBasis.exists_rounded_prescribedPolarFactor
    {dx k H : ℕ} (V : SignalBasis dx k) (hk : 0 < k) (hH : 0 < H)
    (hmesh : Real.sqrt (dx * k) * (H : ℝ)⁻¹ ≤ 1 / 4) :
    ∃ (G : RectMatrix dx k) (hG : 1 / 2 ≤ signalMinSingular G),
      (∀ i j, ∃ z : ℤ, G i j = (H : ℝ)⁻¹ * z ∧ |G i j| ≤ 1) ∧
      ‖matrixCLM (G - V.V)‖ ≤ Real.sqrt (dx * k) * (H : ℝ)⁻¹ ∧
      ‖matrixCLM (prescribedPolarFactor G hG - V.V)‖ ≤
        4 * Real.sqrt (dx * k) * (H : ℝ)⁻¹ := by
  obtain ⟨G, hgrid, hclose, hG⟩ := V.exists_rounded_gridBasis hk hH hmesh
  refine ⟨G, hG, hgrid, hclose, ?_⟩
  have hp := prescribedPolarFactor_sub_signalBasis_norm_le V G hG hclose
  have hq : 0 ≤ Real.sqrt (dx * k) * (H : ℝ)⁻¹ := by positivity
  calc
    ‖matrixCLM (prescribedPolarFactor G hG - V.V)‖
        ≤ 2 * (Real.sqrt (dx * k) * (H : ℝ)⁻¹) := hp
    _ ≤ 4 * Real.sqrt (dx * k) * (H : ℝ)⁻¹ := by nlinarith

end

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
