import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.LatticeEstimator

/-!
# Quantitative facts for the paper's structured lattice

This module collects the paper-local numerical and model consequences used by the explicit
structured-lattice estimator.  It is intentionally separate from the reusable collision-safe
spectral substrate: the lattice height and its constants belong to this paper's construction.
-/

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open MeasureTheory Set
open scoped Matrix.Norms.L2Operator

/-- The displayed lattice constant is strictly positive throughout the core parameter domain. -/
lemma prescribedLatticeConstant_pos
    (k dx dz : ℕ) (L pi0 sigma0 : ℝ)
    (hk : 2 ≤ k) (_hkx : k ≤ dx) (hkz : k ≤ dz) (hL : 1 ≤ L)
    (hpi : 0 < pi0) (hsigma : 0 < sigma0) :
    0 < prescribedLatticeConstant k dx dz L pi0 sigma0 := by
  unfold prescribedLatticeConstant effectRadius
  apply lt_of_lt_of_le (b := 8 * (4 * L * Real.sqrt dz / sigma0) /
    (pi0 * sigma0 ^ 2))
  · have hdz : 0 < dz := lt_of_lt_of_le (by omega : 0 < k) hkz
    positivity
  · exact le_max_left _ _

/-- The prescribed inverse-Gram square root has the two defining square-root properties. -/
lemma inverseGramSqrt_spec {k dx : ℕ} (G : RectMatrix dx k)
    (hG : 1 / 2 ≤ signalMinSingular G) :
    (inverseGramSqrt G hG).PosSemidef ∧
      inverseGramSqrt G hG * inverseGramSqrt G hG = (G.transpose * G)⁻¹ :=
  Classical.choose_spec (inverseGramSqrt_exists G hG)

/-- The prescribed polar factor has orthonormal columns whenever its asserted singular margin is
positive.  This is the algebraic fact used for every rounded grid basis. -/
lemma prescribedPolarFactor_transpose_mul_self {k dx : ℕ} (G : RectMatrix dx k)
    (hG : 1 / 2 ≤ signalMinSingular G) :
    (prescribedPolarFactor G hG).transpose * prescribedPolarFactor G hG = 1 := by
  let H := inverseGramSqrt G hG
  let gram := G.transpose * G
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
  have hHt : H.transpose = H := by
    have hh := hHpsd.isHermitian.eq
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hh
  unfold prescribedPolarFactor
  rw [Matrix.transpose_mul, Matrix.mul_assoc, hHt]
  simpa only [gram, Matrix.mul_assoc] using hmiddle

/-- At every model-generated summary, thresholding at half the population margin retains exactly
the `k` signal singular values. -/
lemma model_thresholdRecoversDimension
    {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P) :
    ThresholdRecoversDimension k (pi0 * sigma0 ^ 2 / 2) (obsSummary P) := by
  let Q : ModelLaw k dx dz L pi0 sigma0 := ⟨P, inferInstance, hM⟩
  obtain ⟨facts⟩ := modelCompressedSpectralFacts_exists Q
  constructor
  · intro j hj
    exact (facts.thresholdRetainsExactlySignal j).2 hj
  · intro j hj
    have hnot : ¬j < k := Nat.not_lt.mpr hj
    exact lt_of_not_ge (fun h => hnot ((facts.thresholdRetainsExactlySignal j).1 h))

/-- The operator norm of a perturbation of the vertically stacked proxy block is bounded by the
two proxy-block terms already present in the summary metric. -/
lemma stackedProxyMoment_sub_norm_le {dx dz : ℕ} (s q : SummarySpace dx dz) :
    ‖matrixCLM (stackedProxyMoment s - stackedProxyMoment q)‖ ≤
      ‖matrixCLM (s.M0 - q.M0)‖ + ‖matrixCLM (s.M1 - q.M1)‖ := by
  let H := stackedProxyMoment s - stackedProxyMoment q
  let A0 := s.M0 - q.M0
  let A1 := s.M1 - q.M1
  apply ContinuousLinearMap.opNorm_le_bound _ (add_nonneg (norm_nonneg _) (norm_nonneg _))
  intro x
  have hsplit : (∑ i : Fin (2 * dz),
      ((Matrix.toEuclideanLin H x) i) ^ 2) =
      (∑ i : Fin dz, ((Matrix.toEuclideanLin A0 x) i) ^ 2) +
      ∑ i : Fin dz, ((Matrix.toEuclideanLin A1 x) i) ^ 2 := by
    let e : (Fin dz ⊕ Fin dz) ≃ Fin (2 * dz) :=
      finSumFinEquiv.trans (finCongr (two_mul dz).symm)
    rw [← Equiv.sum_comp e, Fintype.sum_sum_type]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      congr 1
      have hi : e (Sum.inl i) = ⟨i.val, by omega⟩ := by
        apply Fin.ext
        simp [e]
      rw [hi]
      simp only [H, A0, Matrix.toEuclideanLin_apply, Matrix.mulVec, Matrix.sub_apply,
        stackedProxyMoment]
      apply Finset.sum_congr rfl
      intro j _
      simp [i.isLt]
    · apply Finset.sum_congr rfl
      intro i _
      congr 1
      have hi : e (Sum.inr i) = ⟨i.val + dz, by omega⟩ := by
        apply Fin.ext
        simp [e]
      rw [hi]
      simp only [H, A1, Matrix.toEuclideanLin_apply, Matrix.mulVec, Matrix.sub_apply,
        stackedProxyMoment]
      apply Finset.sum_congr rfl
      intro j _
      simp
  let a : ℝ := ∑ i : Fin dz, ((Matrix.toEuclideanLin A0 x) i) ^ 2
  let b : ℝ := ∑ i : Fin dz, ((Matrix.toEuclideanLin A1 x) i) ^ 2
  have ha : 0 ≤ a := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hb : 0 ≤ b := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsqrt : Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
    rw [Real.sq_sqrt (add_nonneg ha hb), add_sq, Real.sq_sqrt ha, Real.sq_sqrt hb]
    nlinarith [mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]
  calc
    ‖Matrix.toEuclideanLin H x‖ = Real.sqrt (a + b) := by
      rw [EuclideanSpace.norm_eq]
      simp only [Real.norm_eq_abs, sq_abs]
      rw [hsplit]
    _ ≤ Real.sqrt a + Real.sqrt b := hsqrt
    _ = ‖Matrix.toEuclideanLin A0 x‖ + ‖Matrix.toEuclideanLin A1 x‖ := by
      rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
      simp only [Real.norm_eq_abs, sq_abs]
      rfl
    _ ≤ ‖A0‖ * ‖x‖ + ‖A1‖ * ‖x‖ :=
      add_le_add (Matrix.l2_opNorm_mulVec A0 x) (Matrix.l2_opNorm_mulVec A1 x)
    _ = (‖matrixCLM (s.M0 - q.M0)‖ + ‖matrixCLM (s.M1 - q.M1)‖) * ‖x‖ := by
      have h0 : ‖A0‖ = ‖matrixCLM (s.M0 - q.M0)‖ := by rfl
      have h1 : ‖A1‖ = ‖matrixCLM (s.M1 - q.M1)‖ := by rfl
      rw [h0, h1]
      ring

/-- The stacked proxy perturbation is controlled without an extra dimension factor by the summary
metric used in the theorem. -/
lemma stackedProxyMoment_sub_norm_le_dS {dx dz : ℕ} (s q : SummarySpace dx dz) :
    ‖matrixCLM (stackedProxyMoment s - stackedProxyMoment q)‖ ≤ dS s q := by
  calc
    _ ≤ ‖matrixCLM (s.M0 - q.M0)‖ + ‖matrixCLM (s.M1 - q.M1)‖ :=
      stackedProxyMoment_sub_norm_le s q
    _ ≤ dS s q := by
      unfold dS
      have hN0 : 0 ≤ ‖matrixCLM (s.N0 - q.N0)‖ := norm_nonneg _
      have hN1 : 0 ≤ ‖matrixCLM (s.N1 - q.N1)‖ := norm_nonneg _
      have hm : 0 ≤ Real.sqrt (∑ i, (s.mX i - q.mX i) ^ 2) := Real.sqrt_nonneg _
      linarith

/-- Any summary lying strictly inside half the population singular margin has exactly the same
thresholded signal dimension. -/
lemma model_thresholdRecoversDimension_of_dS_lt
    {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P)
    (s : SummarySpace dx dz)
    (hs : dS s (obsSummary P) < pi0 * sigma0 ^ 2 / 2) :
    ThresholdRecoversDimension k (pi0 * sigma0 ^ 2 / 2) s := by
  rcases hM.coreDomain with ⟨hk, hkx, _hkz, hL, hpi, _hpiMax, hsigma, _hsigmaMax⟩
  let Q : ModelLaw k dx dz L pi0 sigma0 := ⟨P, inferInstance, hM⟩
  obtain ⟨facts⟩ := modelCompressedSpectralFacts_exists Q
  let threshold := pi0 * sigma0 ^ 2 / 2
  have htpos : 0 < threshold := by
    dsimp [threshold]
    positivity
  have hpert : ∀ j, |singularValue (stackedProxyMoment s) j -
      singularValue (stackedProxyMoment Q.summary) j| < threshold := by
    intro j
    have hadd : stackedProxyMoment Q.summary +
        (stackedProxyMoment s - stackedProxyMoment Q.summary) = stackedProxyMoment s := by
      abel
    have hw := singular_value_weyl (j := j) (stackedProxyMoment Q.summary)
      (stackedProxyMoment s - stackedProxyMoment Q.summary)
    rw [hadd] at hw
    exact lt_of_le_of_lt hw <| lt_of_le_of_lt
      (stackedProxyMoment_sub_norm_le_dS s Q.summary) hs
  constructor
  · intro j hj
    have hjle := (Matrix.toEuclideanLin (stackedProxyMoment Q.summary)).singularValues_antitone
      (Nat.le_sub_one_of_lt hj)
    have hlower : pi0 * sigma0 ^ 2 ≤
        singularValue (stackedProxyMoment Q.summary) j := by
      exact (stackedProxyMoment_minSingular P hk hkx hL hpi hsigma hM).trans hjle
    have hp := hpert j
    rw [abs_lt] at hp
    dsimp [threshold] at hp ⊢
    linarith
  · intro j hj
    have hz : singularValue (stackedProxyMoment Q.summary) j = 0 := by
      exact (Matrix.toEuclideanLin
        (stackedProxyMoment Q.summary)).singularValues_eq_zero_iff_le_finrank_range.mpr <| by
          rw [facts.stackedRank]
          exact hj
    have hp := hpert j
    rw [hz, sub_zero, abs_lt] at hp
    exact hp.2

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
