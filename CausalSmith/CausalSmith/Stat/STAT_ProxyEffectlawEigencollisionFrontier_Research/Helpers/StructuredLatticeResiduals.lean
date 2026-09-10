import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.StructuredLatticeComparator

/-! # Factorwise residual estimates for the rounded comparator -/

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

noncomputable section

open scoped Matrix.Norms.L2Operator

lemma SignalBasis.matrixCLM_norm_le_one {dx k : ℕ} (V : SignalBasis dx k) :
    ‖matrixCLM V.V‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  have hn := (signalBasisLinearIsometry V).norm_map x
  rw [one_mul]
  change ‖Matrix.toEuclideanLin V.V x‖ ≤ ‖x‖
  exact hn.le

/-- A positive square signal margin makes the ordinary nonsingular inverse available. -/
lemma matrix_det_isUnit_of_signalMinSingular_pos {k : ℕ} (A : RectMatrix k k)
    (hA : 0 < signalMinSingular A) : IsUnit A.det := by
  have hinj := publishedMomentIdentity_injective_of_signalMinSingular_pos A hA
  have hgram := publishedMomentIdentity_gram_det_isUnit_of_injective A hinj
  apply isUnit_iff_ne_zero.mpr
  intro hdet
  apply hgram.ne_zero
  rw [Matrix.det_mul, Matrix.det_transpose, hdet, mul_zero]

/-- The inverse norm is the reciprocal of any certified lower singular margin. -/
lemma matrix_inv_norm_le_of_signalMinSingular {k : ℕ} (A : RectMatrix k k)
    {s : ℝ} (hs : 0 < s) (hA : s ≤ signalMinSingular A) :
    ‖matrixCLM A⁻¹‖ ≤ 1 / s := by
  have hpos : 0 < signalMinSingular A := hs.trans_le hA
  have hinj := publishedMomentIdentity_injective_of_signalMinSingular_pos A hpos
  have hdet := matrix_det_isUnit_of_signalMinSingular_pos A hpos
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro y
  have hlo := singular_value_variational_lower A hinj (matrixCLM A⁻¹ y)
  have hlower : s * ‖matrixCLM A⁻¹ y‖ ≤
      ‖Matrix.toEuclideanLin A (matrixCLM A⁻¹ y)‖ :=
    (mul_le_mul_of_nonneg_right hA (norm_nonneg _)).trans hlo
  have himage : Matrix.toEuclideanLin A (matrixCLM A⁻¹ y) = y := by
    apply PiLp.ext
    intro i
    simp [matrixCLM, Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv A hdet]
  rw [himage] at hlower
  simpa [one_div] using (le_inv_mul_iff₀ hs).2 hlower

/-- The exact inverse perturbation estimate used by the frozen operator coefficient. -/
lemma matrix_inv_sub_inv_norm_le_of_signalMinSingular
    {k : ℕ} (R Rn : RectMatrix k k) {sigma0 q : ℝ}
    (hsigma0 : 0 < sigma0)
    (hRmin : sigma0 ≤ signalMinSingular R)
    (hRnmin : sigma0 / 2 ≤ signalMinSingular Rn)
    (hR : ‖matrixCLM (Rn - R)‖ ≤ (k : ℝ) * q) (hq : 0 ≤ q) :
    ‖matrixCLM (Rn⁻¹ - R⁻¹)‖ ≤ 2 * k * q / sigma0 ^ 2 := by
  have hhalf : 0 < sigma0 / 2 := by positivity
  have hRnInv := matrix_inv_norm_le_of_signalMinSingular Rn hhalf hRnmin
  have hRInv := matrix_inv_norm_le_of_signalMinSingular R hsigma0 hRmin
  have hRdet := matrix_det_isUnit_of_signalMinSingular_pos R (hsigma0.trans_le hRmin)
  have hRndet := matrix_det_isUnit_of_signalMinSingular_pos Rn (hhalf.trans_le hRnmin)
  have hid : Rn⁻¹ - R⁻¹ = Rn⁻¹ * (R - Rn) * R⁻¹ := by
    calc
      Rn⁻¹ - R⁻¹ = Rn⁻¹ * R * R⁻¹ - Rn⁻¹ * Rn * R⁻¹ := by
        simp [Matrix.mul_assoc, Matrix.nonsing_inv_mul Rn hRndet,
          Matrix.mul_nonsing_inv R hRdet]
      _ = Rn⁻¹ * (R - Rn) * R⁻¹ := by noncomm_ring
  change ‖Rn⁻¹ - R⁻¹‖ ≤ _
  change ‖Rn⁻¹‖ ≤ _ at hRnInv
  change ‖R⁻¹‖ ≤ _ at hRInv
  change ‖Rn - R‖ ≤ _ at hR
  rw [hid]
  calc
    ‖Rn⁻¹ * (R - Rn) * R⁻¹‖ ≤ ‖Rn⁻¹‖ * ‖R - Rn‖ * ‖R⁻¹‖ := by
      exact (Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ (2 / sigma0) * ((k : ℝ) * q) * (1 / sigma0) := by
      rw [norm_sub_rev]
      gcongr
      simpa [div_eq_mul_inv] using hRnInv
    _ = 2 * k * q / sigma0 ^ 2 := by field_simp

/-- A finite probability vector has Euclidean norm at most one. -/
lemma probabilityVector_euc_norm_le_one {k : ℕ} (p : Fin k → ℝ)
    (hp : ∀ u, 0 ≤ p u) (hsum : ∑ u, p u = 1) :
    ‖(WithLp.toLp 2 p : Euc k)‖ ≤ 1 := by
  have hple (u : Fin k) : p u ≤ 1 := by
    calc
      p u ≤ ∑ v, p v := Finset.single_le_sum (fun v _ => hp v) (Finset.mem_univ u)
      _ = 1 := hsum
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num)).1
  rw [EuclideanSpace.real_norm_sq_eq, one_pow]
  calc
    ∑ u, ((WithLp.toLp 2 p : Euc k) u) ^ 2 ≤ ∑ u, p u := by
      apply Finset.sum_le_sum
      intro u _
      change p u ^ 2 ≤ p u
      nlinarith [hp u, hple u]
    _ = 1 := hsum

/-- Factorwise perturbation of the observable mean reconstruction.  Substituting
`cV = 4*sqrt(dx*k)` gives exactly the frozen `cm` coefficient. -/
lemma rounded_mean_factorization_residual_le
    {dx k : ℕ} {L q cV : ℝ}
    (V Vn : SignalBasis dx k) (R Rn : RectMatrix k k) (p pn : Fin k → ℝ)
    (hp : ∀ u, 0 ≤ p u) (hpSum : ∑ u, p u = 1)
    (hpn : ∀ u, 0 ≤ pn u) (hpnSum : ∑ u, pn u = 1)
    (hV : ‖matrixCLM (Vn.V - V.V)‖ ≤ cV * q)
    (hR : ‖matrixCLM (Rn - R)‖ ≤ (k : ℝ) * q)
    (hRn : ‖matrixCLM Rn‖ ≤ 2 * Real.sqrt k * L)
    (hR0 : ‖matrixCLM R‖ ≤ Real.sqrt k * L)
    (hweight : ‖(WithLp.toLp 2 (pn - p) : Euc k)‖ ≤ Real.sqrt k * q)
    (hL : 0 ≤ L) (hq : 0 ≤ q) :
    ‖Matrix.toEuclideanLin (Vn.V * Rn.transpose) (WithLp.toLp 2 pn) -
        Matrix.toEuclideanLin (V.V * R.transpose) (WithLp.toLp 2 p)‖ ≤
      (2 * Real.sqrt k * L * cV + k + k * L) * q := by
  let pnE : Euc k := WithLp.toLp 2 pn
  let pE : Euc k := WithLp.toLp 2 p
  let dE : Euc k := WithLp.toLp 2 (pn - p)
  have hpnNorm : ‖pnE‖ ≤ 1 := probabilityVector_euc_norm_le_one pn hpn hpnSum
  change ‖Vn.V - V.V‖ ≤ cV * q at hV
  change ‖Rn - R‖ ≤ (k : ℝ) * q at hR
  change ‖Rn‖ ≤ 2 * Real.sqrt k * L at hRn
  change ‖R‖ ≤ Real.sqrt k * L at hR0
  have hfirst :
      Matrix.toEuclideanLin ((Vn.V - V.V) * Rn.transpose) pnE =
        Matrix.toEuclideanLin (Vn.V * Rn.transpose) pnE -
          Matrix.toEuclideanLin (V.V * Rn.transpose) pnE := by
    apply PiLp.ext
    intro i
    simp [Matrix.toEuclideanLin_apply, Matrix.sub_mul, Matrix.sub_mulVec]
  have hsecond :
      Matrix.toEuclideanLin (V.V * (Rn - R).transpose) pnE =
        Matrix.toEuclideanLin (V.V * Rn.transpose) pnE -
          Matrix.toEuclideanLin (V.V * R.transpose) pnE := by
    apply PiLp.ext
    intro i
    simp [Matrix.toEuclideanLin_apply, Matrix.transpose_sub, Matrix.mul_sub,
      Matrix.sub_mulVec]
  have hthird :
      Matrix.toEuclideanLin (V.V * R.transpose) dE =
        Matrix.toEuclideanLin (V.V * R.transpose) pnE -
          Matrix.toEuclideanLin (V.V * R.transpose) pE := by
    apply PiLp.ext
    intro i
    simp [pnE, pE, dE, Matrix.toEuclideanLin_apply, Matrix.mulVec_sub]
  have hdecomp :
      Matrix.toEuclideanLin (Vn.V * Rn.transpose) pnE -
          Matrix.toEuclideanLin (V.V * R.transpose) pE =
        Matrix.toEuclideanLin ((Vn.V - V.V) * Rn.transpose) pnE +
        Matrix.toEuclideanLin (V.V * (Rn - R).transpose) pnE +
        Matrix.toEuclideanLin (V.V * R.transpose) dE := by
    rw [hfirst, hsecond, hthird]
    abel
  rw [hdecomp]
  calc
    ‖Matrix.toEuclideanLin ((Vn.V - V.V) * Rn.transpose) pnE +
        Matrix.toEuclideanLin (V.V * (Rn - R).transpose) pnE +
        Matrix.toEuclideanLin (V.V * R.transpose) dE‖ ≤
      ‖Matrix.toEuclideanLin ((Vn.V - V.V) * Rn.transpose) pnE‖ +
      ‖Matrix.toEuclideanLin (V.V * (Rn - R).transpose) pnE‖ +
      ‖Matrix.toEuclideanLin (V.V * R.transpose) dE‖ := by
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (cV * q) * (2 * Real.sqrt k * L) * 1 +
        (1 * ((k : ℝ) * q)) * 1 +
        (1 * (Real.sqrt k * L)) * (Real.sqrt k * q) := by
      have ht (A : RectMatrix k k) : ‖A.transpose‖ = ‖A‖ := by
        simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
          Matrix.l2_opNorm_conjTranspose A
      have hmul (A : RectMatrix dx k) (B : RectMatrix k k) (x : Euc k) :
          ‖Matrix.toEuclideanLin (A * B) x‖ ≤ ‖A‖ * ‖B‖ * ‖x‖ := by
        exact (Matrix.l2_opNorm_mulVec (A * B) x).trans
          (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul A B) (norm_nonneg x))
      apply add_le_add
      · apply add_le_add
        · exact (hmul (Vn.V - V.V) Rn.transpose pnE).trans (by
            rw [ht Rn]
            have hV0 : 0 ≤ cV * q := (norm_nonneg _).trans hV
            gcongr)
        · exact (hmul V.V (Rn - R).transpose pnE).trans (by
            rw [ht (Rn - R)]
            gcongr
            exact V.matrixCLM_norm_le_one)
      · exact (hmul V.V R.transpose dE).trans (by
          rw [ht R]
          gcongr
          exact V.matrixCLM_norm_le_one)
    _ = (2 * Real.sqrt k * L * cV + k + k * L) * q := by
      have hs : Real.sqrt k * Real.sqrt k = (k : ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg k)
      calc
        cV * q * (2 * Real.sqrt k * L) * 1 + 1 * ((k : ℝ) * q) * 1 +
            1 * (Real.sqrt k * L) * (Real.sqrt k * q) =
          2 * Real.sqrt k * L * cV * q + (k : ℝ) * q +
            (Real.sqrt k * Real.sqrt k) * L * q := by ring
        _ = (2 * Real.sqrt k * L * cV + k + k * L) * q := by rw [hs]; ring

/-- Factorwise perturbation of the anchor reconstruction.  This is the exact frozen `cb`
coefficient after substituting `cV = 4*sqrt(dx*k)`. -/
lemma rounded_anchor_factorization_residual_le
    {dx k : ℕ} {L q cV : ℝ} (hdx : 0 < dx)
    (V Vn : SignalBasis dx k) (R Rn : RectMatrix k k)
    (hV : ‖matrixCLM (Vn.V - V.V)‖ ≤ cV * q)
    (hR : ‖matrixCLM (Rn - R)‖ ≤ (k : ℝ) * q)
    (hRn : ‖matrixCLM Rn‖ ≤ 2 * Real.sqrt k * L)
    (hL : 0 ≤ L) (hq : 0 ≤ q) :
    ‖Matrix.toEuclideanLin (Rn * Vn.V.transpose) (WithLp.toLp 2 (firstBasis dx)) -
        Matrix.toEuclideanLin (R * V.V.transpose) (WithLp.toLp 2 (firstBasis dx))‖ ≤
      ((k : ℝ) + 2 * Real.sqrt k * L * cV) * q := by
  let e1 : Euc dx := WithLp.toLp 2 (firstBasis dx)
  have he1 : ‖e1‖ = 1 := by
    cases dx with
    | zero => omega
    | succ d =>
        rw [EuclideanSpace.norm_eq, Fin.sum_univ_succ]
        simp [e1, firstBasis]
  change ‖Vn.V - V.V‖ ≤ cV * q at hV
  change ‖Rn - R‖ ≤ (k : ℝ) * q at hR
  change ‖Rn‖ ≤ 2 * Real.sqrt k * L at hRn
  have hfirst :
      Matrix.toEuclideanLin ((Rn - R) * V.V.transpose) e1 =
        Matrix.toEuclideanLin (Rn * V.V.transpose) e1 -
          Matrix.toEuclideanLin (R * V.V.transpose) e1 := by
    apply PiLp.ext
    intro i
    simp [Matrix.toEuclideanLin_apply, Matrix.sub_mul]
  have hsecond :
      Matrix.toEuclideanLin (Rn * (Vn.V - V.V).transpose) e1 =
        Matrix.toEuclideanLin (Rn * Vn.V.transpose) e1 -
          Matrix.toEuclideanLin (Rn * V.V.transpose) e1 := by
    apply PiLp.ext
    intro i
    simp [Matrix.toEuclideanLin_apply, Matrix.transpose_sub, Matrix.mul_sub]
  have hdecomp :
      Matrix.toEuclideanLin (Rn * Vn.V.transpose) e1 -
          Matrix.toEuclideanLin (R * V.V.transpose) e1 =
        Matrix.toEuclideanLin ((Rn - R) * V.V.transpose) e1 +
          Matrix.toEuclideanLin (Rn * (Vn.V - V.V).transpose) e1 := by
    rw [hfirst, hsecond]
    abel
  rw [show (WithLp.toLp 2 (firstBasis dx) : Euc dx) = e1 by rfl, hdecomp]
  calc
    ‖Matrix.toEuclideanLin ((Rn - R) * V.V.transpose) e1 +
        Matrix.toEuclideanLin (Rn * (Vn.V - V.V).transpose) e1‖ ≤
      ‖Matrix.toEuclideanLin ((Rn - R) * V.V.transpose) e1‖ +
        ‖Matrix.toEuclideanLin (Rn * (Vn.V - V.V).transpose) e1‖ := norm_add_le _ _
    _ ≤ (((k : ℝ) * q) * 1) * 1 +
        ((2 * Real.sqrt k * L) * (cV * q)) * 1 := by
      have htV : ‖V.V.transpose‖ = ‖V.V‖ := by
        simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
          Matrix.l2_opNorm_conjTranspose V.V
      have htD : ‖(Vn.V - V.V).transpose‖ = ‖Vn.V - V.V‖ := by
        simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
          Matrix.l2_opNorm_conjTranspose (Vn.V - V.V)
      have hmul (A : RectMatrix k k) (B : RectMatrix k dx) :
          ‖Matrix.toEuclideanLin (A * B) e1‖ ≤ ‖A‖ * ‖B‖ * ‖e1‖ := by
        exact (Matrix.l2_opNorm_mulVec (A * B) e1).trans
          (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul A B) (norm_nonneg e1))
      apply add_le_add
      · exact (hmul (Rn - R) V.V.transpose).trans (by
          rw [htV, he1]
          gcongr
          exact V.matrixCLM_norm_le_one)
      · exact (hmul Rn (Vn.V - V.V).transpose).trans (by
          rw [htD, he1]
          have hV0 : 0 ≤ cV * q := (norm_nonneg _).trans hV
          gcongr)
    _ = ((k : ℝ) + 2 * Real.sqrt k * L * cV) * q := by ring

/-- Factorwise perturbation of the similarity-transformed diagonal operator.  The
hypotheses expose the three analytic ingredients needed downstream: inverse
stability, inverse norm control, and coordinatewise effect rounding.  With
`KD = 4 * sqrt k * L * Ltau / sigma0`, the conclusion is the frozen `cD`
coefficient. -/
lemma rounded_operator_factorization_residual_le
    {dx k : ℕ} {L Ltau sigma0 q cV KD : ℝ}
    (V Vn : SignalBasis dx k) (R Rn : RectMatrix k k)
    (tau taun : Fin k → ℝ)
    (hV : ‖matrixCLM (Vn.V - V.V)‖ ≤ cV * q)
    (hR : ‖matrixCLM (Rn - R)‖ ≤ (k : ℝ) * q)
    (hRn : ‖matrixCLM Rn‖ ≤ 2 * Real.sqrt k * L)
    (hR0 : ‖matrixCLM R‖ ≤ Real.sqrt k * L)
    (hRinv : ‖matrixCLM R⁻¹‖ ≤ 1 / sigma0)
    (hRninv : ‖matrixCLM Rn⁻¹‖ ≤ 2 / sigma0)
    (hInvDiff : ‖matrixCLM (Rn⁻¹ - R⁻¹)‖ ≤ 2 * k * q / sigma0 ^ 2)
    (htau : ∀ u, |tau u| ≤ Ltau) (htaun : ∀ u, |taun u| ≤ Ltau)
    (htauDiff : ∀ u, |taun u - tau u| ≤ q)
    (hL : 0 ≤ L) (hLtau : 0 ≤ Ltau) (hsigma0 : 0 < sigma0)
    (hq : 0 ≤ q) (hcV : 0 ≤ cV)
    (hKD : KD = 4 * Real.sqrt k * L * Ltau / sigma0) :
    ‖matrixCLM
        (Vn.V * Rn⁻¹ * Matrix.diagonal taun * Rn * Vn.V.transpose -
          V.V * R⁻¹ * Matrix.diagonal tau * R * V.V.transpose)‖ ≤
      (2 * KD * cV + 4 * k * Real.sqrt k * L * Ltau / sigma0 ^ 2 +
        2 * Real.sqrt k * L / sigma0 + k * Ltau / sigma0) * q := by
  change ‖Vn.V - V.V‖ ≤ cV * q at hV
  change ‖Rn - R‖ ≤ (k : ℝ) * q at hR
  change ‖Rn‖ ≤ 2 * Real.sqrt k * L at hRn
  change ‖R‖ ≤ Real.sqrt k * L at hR0
  change ‖R⁻¹‖ ≤ 1 / sigma0 at hRinv
  change ‖Rn⁻¹‖ ≤ 2 / sigma0 at hRninv
  change ‖Rn⁻¹ - R⁻¹‖ ≤ 2 * k * q / sigma0 ^ 2 at hInvDiff
  have hVnNorm : ‖Vn.V‖ ≤ 1 := Vn.matrixCLM_norm_le_one
  have hVNorm : ‖V.V‖ ≤ 1 := V.matrixCLM_norm_le_one
  have htVn : ‖Vn.V.transpose‖ = ‖Vn.V‖ := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.l2_opNorm_conjTranspose Vn.V
  have htV : ‖V.V.transpose‖ = ‖V.V‖ := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.l2_opNorm_conjTranspose V.V
  have htDiff : ‖(Vn.V - V.V).transpose‖ = ‖Vn.V - V.V‖ := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.l2_opNorm_conjTranspose (Vn.V - V.V)
  have hDn : ‖Matrix.diagonal taun‖ ≤ Ltau := by
    rw [Matrix.l2_opNorm_diagonal, pi_norm_le_iff_of_nonneg hLtau]
    intro u
    simpa [Real.norm_eq_abs] using htaun u
  have hD : ‖Matrix.diagonal tau‖ ≤ Ltau := by
    rw [Matrix.l2_opNorm_diagonal, pi_norm_le_iff_of_nonneg hLtau]
    intro u
    simpa [Real.norm_eq_abs] using htau u
  have hDdiff : ‖Matrix.diagonal taun - Matrix.diagonal tau‖ ≤ q := by
    have hdiagSub : Matrix.diagonal taun - Matrix.diagonal tau =
        Matrix.diagonal (taun - tau) := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.diagonal_apply, hij]
    rw [hdiagSub, Matrix.l2_opNorm_diagonal,
      pi_norm_le_iff_of_nonneg hq]
    intro u
    simpa [Real.norm_eq_abs] using htauDiff u
  let a := (Vn.V - V.V) * Rn⁻¹ * Matrix.diagonal taun * Rn * Vn.V.transpose
  let b := V.V * (Rn⁻¹ - R⁻¹) * Matrix.diagonal taun * Rn * Vn.V.transpose
  let c := V.V * R⁻¹ * (Matrix.diagonal taun - Matrix.diagonal tau) * Rn *
    Vn.V.transpose
  let d := V.V * R⁻¹ * Matrix.diagonal tau * (Rn - R) * Vn.V.transpose
  let e := V.V * R⁻¹ * Matrix.diagonal tau * R *
    (Vn.V - V.V).transpose
  have hdecomp :
      Vn.V * Rn⁻¹ * Matrix.diagonal taun * Rn * Vn.V.transpose -
          V.V * R⁻¹ * Matrix.diagonal tau * R * V.V.transpose =
        a + b + c + d + e := by
    have ha : a =
        Vn.V * Rn⁻¹ * Matrix.diagonal taun * Rn * Vn.V.transpose -
          V.V * Rn⁻¹ * Matrix.diagonal taun * Rn * Vn.V.transpose := by
      simp [a, Matrix.sub_mul]
    have hb : b =
        V.V * Rn⁻¹ * Matrix.diagonal taun * Rn * Vn.V.transpose -
          V.V * R⁻¹ * Matrix.diagonal taun * Rn * Vn.V.transpose := by
      simp [b, Matrix.mul_sub, Matrix.sub_mul]
    have hc : c =
        V.V * R⁻¹ * Matrix.diagonal taun * Rn * Vn.V.transpose -
          V.V * R⁻¹ * Matrix.diagonal tau * Rn * Vn.V.transpose := by
      change V.V * R⁻¹ * (Matrix.diagonal taun - Matrix.diagonal tau) * Rn *
          Vn.V.transpose = _
      simp only [Matrix.mul_sub, Matrix.sub_mul]
    have hd : d =
        V.V * R⁻¹ * Matrix.diagonal tau * Rn * Vn.V.transpose -
          V.V * R⁻¹ * Matrix.diagonal tau * R * Vn.V.transpose := by
      simp [d, Matrix.mul_sub, Matrix.sub_mul]
    have he : e =
        V.V * R⁻¹ * Matrix.diagonal tau * R * Vn.V.transpose -
          V.V * R⁻¹ * Matrix.diagonal tau * R * V.V.transpose := by
      simp [e, Matrix.transpose_sub, Matrix.mul_sub]
    rw [ha, hb, hc, hd, he]
    abel
  rw [hdecomp]
  have hsum : ‖a + b + c + d + e‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ := by
    calc
      ‖a + b + c + d + e‖ ≤ ‖a + b + c + d‖ + ‖e‖ := norm_add_le _ _
      _ ≤ (‖a + b + c‖ + ‖d‖) + ‖e‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ((‖a + b‖ + ‖c‖) + ‖d‖) + ‖e‖ := by gcongr; exact norm_add_le _ _
      _ ≤ (((‖a‖ + ‖b‖) + ‖c‖) + ‖d‖) + ‖e‖ := by
        gcongr; exact norm_add_le _ _
  apply hsum.trans
  have hmul (A : RectMatrix dx k) (B C D : RectMatrix k k)
      (E : RectMatrix k dx) : ‖A * B * C * D * E‖ ≤ ‖A‖ * ‖B‖ * ‖C‖ * ‖D‖ * ‖E‖ := by
    calc
      ‖A * B * C * D * E‖ ≤ ‖A * B * C * D‖ * ‖E‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖A * B * C‖ * ‖D‖) * ‖E‖ := by
        gcongr; exact Matrix.l2_opNorm_mul _ _
      _ ≤ ((‖A * B‖ * ‖C‖) * ‖D‖) * ‖E‖ := by
        gcongr; exact Matrix.l2_opNorm_mul _ _
      _ ≤ (((‖A‖ * ‖B‖) * ‖C‖) * ‖D‖) * ‖E‖ := by
        gcongr; exact Matrix.l2_opNorm_mul _ _
  have hsqrt : 0 ≤ Real.sqrt k := Real.sqrt_nonneg _
  have hsigmaInv : 0 ≤ 1 / sigma0 := by positivity
  have hsigmaSq : 0 < sigma0 ^ 2 := sq_pos_of_pos hsigma0
  calc
    ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ ≤
        (cV * q) * (2 / sigma0) * Ltau * (2 * Real.sqrt k * L) * 1 +
        1 * (2 * k * q / sigma0 ^ 2) * Ltau * (2 * Real.sqrt k * L) * 1 +
        1 * (1 / sigma0) * q * (2 * Real.sqrt k * L) * 1 +
        1 * (1 / sigma0) * Ltau * ((k : ℝ) * q) * 1 +
        1 * (1 / sigma0) * Ltau * (Real.sqrt k * L) * (cV * q) := by
      apply add_le_add
      · apply add_le_add
        · apply add_le_add
          · apply add_le_add
            · exact (hmul _ _ _ _ _).trans (by rw [htVn]; gcongr)
            · exact (hmul _ _ _ _ _).trans (by rw [htVn]; gcongr)
          · exact (hmul _ _ _ _ _).trans (by rw [htVn]; gcongr)
        · exact (hmul _ _ _ _ _).trans (by rw [htVn]; gcongr)
      · exact (hmul _ _ _ _ _).trans (by rw [htDiff]; gcongr)
    _ ≤ (2 * KD * cV + 4 * k * Real.sqrt k * L * Ltau / sigma0 ^ 2 +
        2 * Real.sqrt k * L / sigma0 + k * Ltau / sigma0) * q := by
      rw [hKD]
      have hslack : 0 ≤
          q * Real.sqrt k * L * Ltau * cV * sigma0 := by positivity
      field_simp
      ring_nf
      nlinarith [hslack]

/-- Signal-margin form of `rounded_operator_factorization_residual_le`, discharging all
ordinary-inverse hypotheses from the ideal and rounded singular-value certificates. -/
lemma rounded_operator_factorization_residual_le_of_signalMinSingular
    {dx k : ℕ} {L Ltau sigma0 q cV KD : ℝ}
    (V Vn : SignalBasis dx k) (R Rn : RectMatrix k k)
    (tau taun : Fin k → ℝ)
    (hV : ‖matrixCLM (Vn.V - V.V)‖ ≤ cV * q)
    (hR : ‖matrixCLM (Rn - R)‖ ≤ (k : ℝ) * q)
    (hRn : ‖matrixCLM Rn‖ ≤ 2 * Real.sqrt k * L)
    (hR0 : ‖matrixCLM R‖ ≤ Real.sqrt k * L)
    (hRmin : sigma0 ≤ signalMinSingular R)
    (hRnmin : sigma0 / 2 ≤ signalMinSingular Rn)
    (htau : ∀ u, |tau u| ≤ Ltau) (htaun : ∀ u, |taun u| ≤ Ltau)
    (htauDiff : ∀ u, |taun u - tau u| ≤ q)
    (hL : 0 ≤ L) (hLtau : 0 ≤ Ltau) (hsigma0 : 0 < sigma0)
    (hq : 0 ≤ q) (hcV : 0 ≤ cV)
    (hKD : KD = 4 * Real.sqrt k * L * Ltau / sigma0) :
    ‖matrixCLM
        (Vn.V * Rn⁻¹ * Matrix.diagonal taun * Rn * Vn.V.transpose -
          V.V * R⁻¹ * Matrix.diagonal tau * R * V.V.transpose)‖ ≤
      (2 * KD * cV + 4 * k * Real.sqrt k * L * Ltau / sigma0 ^ 2 +
        2 * Real.sqrt k * L / sigma0 + k * Ltau / sigma0) * q := by
  have hRinv := matrix_inv_norm_le_of_signalMinSingular R hsigma0 hRmin
  have hhalf : 0 < sigma0 / 2 := by positivity
  have hRninv0 := matrix_inv_norm_le_of_signalMinSingular Rn hhalf hRnmin
  have hRninv : ‖matrixCLM Rn⁻¹‖ ≤ 2 / sigma0 := by
    convert hRninv0 using 1 <;> field_simp
  have hInvDiff := matrix_inv_sub_inv_norm_le_of_signalMinSingular
    R Rn hsigma0 hRmin hRnmin hR hq
  exact rounded_operator_factorization_residual_le V Vn R Rn tau taun hV hR hRn hR0
    hRinv hRninv hInvDiff htau htaun htauDiff hL hLtau hsigma0 hq hcV hKD

end

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
