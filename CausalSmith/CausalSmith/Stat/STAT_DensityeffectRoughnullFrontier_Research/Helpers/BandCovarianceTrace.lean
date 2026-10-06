module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.MatrixTraceComparison

/-! Matrix realization and exact traces of the orthogonal outcome histogram bands. -/

@[expose] public section

noncomputable section
open scoped RealInnerProductSpace
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- Matrix of the coarse histogram projection in the final orthonormal basis. -/
-- @node: histogramProjectionMatrix
def histogramProjectionMatrix (j J : ℕ) : Matrix (Fin J) (Fin J) ℝ :=
  fun i l => (j : ℝ) / J * if cell j (midpoint J l) = cell j (midpoint J i) then 1 else 0

/-- The concrete projection matrix acts as the histogram projection. -/
-- @node: histogramProjectionMatrix_mulVec
lemma histogramProjectionMatrix_mulVec (j J : ℕ) (f : Hj J) :
    (histogramProjectionMatrix j J).mulVec f = (coefficientProjection j J f).ofLp := by
  funext i
  simp only [histogramProjectionMatrix, Matrix.mulVec, dotProduct, coefficientProjection]
  change _ = (j : ℝ) / J * ∑ l, if cell j (midpoint J l) = cell j (midpoint J i) then f l else 0
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  split_ifs <;> simp

/-- The projection matrix has trace equal to its rank. -/
-- @node: histogramProjectionMatrix_trace
lemma histogramProjectionMatrix_trace (j J : ℕ) (hJ : 0 < J) :
    (histogramProjectionMatrix j J).trace = j := by
  simp only [Matrix.trace, Matrix.diag_apply, histogramProjectionMatrix, ite_true, mul_one,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hJr : (J : ℝ) ≠ 0 := by positivity
  field_simp

/-- Coarse histogram projection matrices are symmetric. -/
-- @node: histogramProjectionMatrix_isHermitian
lemma histogramProjectionMatrix_isHermitian (j J : ℕ) :
    (histogramProjectionMatrix j J).IsHermitian := by
  ext i l
  simp [Matrix.conjTranspose, Matrix.transpose, histogramProjectionMatrix, eq_comm]

/-- Matrix of an outcome histogram band. -/
-- @node: histogramBandMatrix
def histogramBandMatrix (L J t : ℕ) : Matrix (Fin J) (Fin J) ℝ :=
  if t = 0 then histogramProjectionMatrix L J else
    histogramProjectionMatrix (2 ^ t * L) J - histogramProjectionMatrix (2 ^ (t - 1) * L) J

/-- Band matrices act as the public band projections. -/
-- @node: histogramBandMatrix_mulVec
lemma histogramBandMatrix_mulVec (L J t : ℕ) (f : Hj J) :
    (histogramBandMatrix L J t).mulVec f = (Qband L J t f).ofLp := by
  unfold histogramBandMatrix Qband
  split_ifs
  · exact histogramProjectionMatrix_mulVec _ _ f
  · rw [Matrix.sub_mulVec, histogramProjectionMatrix_mulVec, histogramProjectionMatrix_mulVec]
    rfl

/-- Band matrices are symmetric. -/
-- @node: histogramBandMatrix_isHermitian
lemma histogramBandMatrix_isHermitian (L J t : ℕ) :
    (histogramBandMatrix L J t).IsHermitian := by
  unfold histogramBandMatrix
  split_ifs
  · exact histogramProjectionMatrix_isHermitian _ _
  · exact (histogramProjectionMatrix_isHermitian _ _).sub
      (histogramProjectionMatrix_isHermitian _ _)

/-- The trace of a dyadic band matrix is its public dimension. -/
-- @node: histogramBandMatrix_trace
lemma histogramBandMatrix_trace (L J t : ℕ) (hJ : 0 < J) :
    (histogramBandMatrix L J t).trace = (bandDimension L t : ℝ) := by
  unfold histogramBandMatrix bandDimension
  split_ifs with ht
  · exact histogramProjectionMatrix_trace _ _ hJ
  · rw [Matrix.trace_sub, histogramProjectionMatrix_trace _ _ hJ,
      histogramProjectionMatrix_trace _ _ hJ]
    have he : t = (t - 1) + 1 := by omega
    conv_lhs => lhs; rw [he, pow_succ]
    push_cast
    ring

/-- The concrete band matrices are orthogonal idempotents. -/
-- @node: histogramBandMatrix_mul
lemma histogramBandMatrix_mul (L T s t : ℕ) (hL : 0 < L)
    (hs : s ≤ T) (ht : t ≤ T) :
    histogramBandMatrix L (2 ^ T * L) s * histogramBandMatrix L (2 ^ T * L) t =
      if s = t then histogramBandMatrix L (2 ^ T * L) t else 0 := by
  apply Matrix.ext_iff_mulVec.mpr
  intro x
  let f : Hj (2 ^ T * L) := WithLp.toLp 2 x
  change _ = _
  rw [← Matrix.mulVec_mulVec]
  change (histogramBandMatrix L (2 ^ T * L) s).mulVec
      ((histogramBandMatrix L (2 ^ T * L) t).mulVec f) = _
  rw [histogramBandMatrix_mulVec, histogramBandMatrix_mulVec]
  by_cases hst : s = t
  · subst s
    rw [if_pos rfl, histogramBandMatrix_mulVec, Qband_idempotent_ladder L T t hL ht]
  · rw [if_neg hst, Matrix.zero_mulVec]
    have hz : Qband L (2 ^ T * L) s (Qband L (2 ^ T * L) t f) = 0 := by
      rcases lt_or_gt_of_ne hst with h | h
      · exact Qband_annihilation_ladder L T s t hL h ht f
      · have hh : inner ℝ (Qband L (2 ^ T * L) s (Qband L (2 ^ T * L) t f))
            (Qband L (2 ^ T * L) s (Qband L (2 ^ T * L) t f)) = 0 := by
          rw [Qband_inner, Qband_inner L (2 ^ T * L) t,
            Qband_annihilation_ladder L T t s hL h hs]
          simp
        exact inner_self_eq_zero.mp hh
    rw [hz]
    rfl

/-- Matrix envelope with a separate eigenvalue on each histogram band. -/
-- @node: weightedHistogramBandMatrix
def weightedHistogramBandMatrix (L J T : ℕ) (w : ℕ → ℝ) : Matrix (Fin J) (Fin J) ℝ :=
  ∑ t ∈ Finset.range (T + 1), w t • histogramBandMatrix L J t

/-- A weighted band envelope is symmetric. -/
-- @node: weightedHistogramBandMatrix_isHermitian
lemma weightedHistogramBandMatrix_isHermitian (L J T : ℕ) (w : ℕ → ℝ) :
    (weightedHistogramBandMatrix L J T w).IsHermitian := by
  unfold weightedHistogramBandMatrix
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro t ht
  exact ((histogramBandMatrix_isHermitian L J t).smul (IsSelfAdjoint.all _)).eq

/-- The matrix quadratic form agrees with the histogram inner product. -/
-- @node: covarianceForm_eq_inner_mulVec
lemma covarianceForm_eq_inner_mulVec {J : ℕ} (A : Matrix (Fin J) (Fin J) ℝ) (f : Hj J) :
    covarianceForm A f = inner ℝ f (WithLp.toLp 2 (A.mulVec f)) := by
  simp only [covarianceForm, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    Matrix.mulVec, dotProduct, Finset.sum_mul]
  congr 1
  ext i
  congr 1
  ext j
  ring

/-- An orthogonal band contributes its projected squared norm to a quadratic form. -/
-- @node: covarianceForm_histogramBandMatrix
lemma covarianceForm_histogramBandMatrix (L T t : ℕ) (hL : 0 < L) (ht : t ≤ T)
    (f : Hj (2 ^ T * L)) :
    covarianceForm (histogramBandMatrix L (2 ^ T * L) t) f =
      ‖Qband L (2 ^ T * L) t f‖ ^ 2 := by
  rw [covarianceForm_eq_inner_mulVec, histogramBandMatrix_mulVec]
  change inner ℝ f (Qband L (2 ^ T * L) t f) = _
  rw [← Qband_idempotent_ladder L T t hL ht f, ← Qband_inner,
    Qband_idempotent_ladder L T t hL ht f, real_inner_self_eq_norm_sq]

/-- The weighted band matrix has exactly the multiband quadratic form. -/
-- @node: covarianceForm_weightedHistogramBandMatrix
lemma covarianceForm_weightedHistogramBandMatrix (L T : ℕ) (hL : 0 < L)
    (w : ℕ → ℝ) (f : Hj (2 ^ T * L)) :
    covarianceForm (weightedHistogramBandMatrix L (2 ^ T * L) T w) f =
      ∑ t ∈ Finset.range (T + 1), w t * ‖Qband L (2 ^ T * L) t f‖ ^ 2 := by
  have hlin : covarianceForm (weightedHistogramBandMatrix L (2 ^ T * L) T w) f =
      ∑ t ∈ Finset.range (T + 1), w t *
        covarianceForm (histogramBandMatrix L (2 ^ T * L) t) f := by
    simp only [covarianceForm, weightedHistogramBandMatrix, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
    simp_rw [Finset.sum_comm (s := Finset.univ) (t := Finset.range (T + 1))]
    apply Finset.sum_congr rfl
    intro t ht
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hlin]
  apply Finset.sum_congr rfl
  intro t ht
  rw [covarianceForm_histogramBandMatrix L T t hL (by
    have := Finset.mem_range.mp ht; omega)]

/-- Squaring a weighted envelope squares its band eigenvalues, with no cross terms. -/
-- @node: weightedHistogramBandMatrix_square
lemma weightedHistogramBandMatrix_square (L T : ℕ) (hL : 0 < L) (w : ℕ → ℝ) :
    weightedHistogramBandMatrix L (2 ^ T * L) T w *
      weightedHistogramBandMatrix L (2 ^ T * L) T w =
    weightedHistogramBandMatrix L (2 ^ T * L) T (fun t => (w t) ^ 2) := by
  unfold weightedHistogramBandMatrix
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.mul_sum, Finset.sum_eq_single s]
  · rw [smul_mul_smul_comm, histogramBandMatrix_mul L T s s hL
      (by have := Finset.mem_range.mp hs; omega)
      (by have := Finset.mem_range.mp hs; omega), if_pos rfl]
    simp only [pow_two]
  · intro t ht hts
    rw [smul_mul_smul_comm, histogramBandMatrix_mul L T s t hL
      (by have := Finset.mem_range.mp hs; omega)
      (by have := Finset.mem_range.mp ht; omega), if_neg (Ne.symm hts), smul_zero]
  · exact fun h => (h hs).elim

/-- Exact square trace of the multiband envelope. -/
-- @node: weightedHistogramBandMatrix_square_trace
lemma weightedHistogramBandMatrix_square_trace (L T : ℕ) (hL : 0 < L) (w : ℕ → ℝ) :
    (weightedHistogramBandMatrix L (2 ^ T * L) T w *
      weightedHistogramBandMatrix L (2 ^ T * L) T w).trace =
    ∑ t ∈ Finset.range (T + 1), (w t) ^ 2 * (bandDimension L t : ℝ) := by
  rw [weightedHistogramBandMatrix_square L T hL, weightedHistogramBandMatrix, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Matrix.trace_smul, histogramBandMatrix_trace L _ t (by positivity), smul_eq_mul]

/-- The dimensions of the dyadic bands add up to the final histogram rank. -/
-- @node: sum_bandDimension
lemma sum_bandDimension (L T : ℕ) :
    ∑ t ∈ Finset.range (T + 1), bandDimension L t = 2 ^ T * L := by
  induction T with
  | zero => simp [bandDimension]
  | succ T ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [bandDimension, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, pow_succ]
    ring

/-- The public multiband envelope, represented by its band eigenvalues. -/
-- @node: multibandEnvelopeMatrix
def multibandEnvelopeMatrix (C : ℝ) (m L T : ℕ) (kt : ℕ → ℕ) :
    Matrix (Fin (2 ^ T * L)) (Fin (2 ^ T * L)) ℝ :=
  weightedHistogramBandMatrix L (2 ^ T * L) T
    (fun t => C * ((m : ℝ)⁻¹ + (m : ℝ) ^ (-2 : ℤ) * (kt t : ℝ)))

/-- The envelope realizes the exact upper quadratic form in (17). -/
-- @node: multibandEnvelopeMatrix_form
lemma multibandEnvelopeMatrix_form (C : ℝ) (m L T : ℕ) (hL : Dyadic L)
    (kt : ℕ → ℕ) (f : Hj (2 ^ T * L)) :
    covarianceForm (multibandEnvelopeMatrix C m L T kt) f =
      C * ((m : ℝ)⁻¹ * ‖f‖ ^ 2 + (m : ℝ) ^ (-2 : ℤ) *
        ∑ t ∈ Finset.range (T + 1), (kt t : ℝ) * ‖Qband L (2 ^ T * L) t f‖ ^ 2) := by
  have hLpos : 0 < L := by obtain ⟨l, rfl⟩ := hL; positivity
  rw [multibandEnvelopeMatrix, covarianceForm_weightedHistogramBandMatrix L T hLpos]
  simp only [mul_add, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  rw [sum_band_norm_sq L T hL]

/-- The eigenvalue square inequality yields exactly the public trace allowance (19). -/
-- @node: multibandEnvelopeMatrix_square_trace_le_VAllow
lemma multibandEnvelopeMatrix_square_trace_le_VAllow (C : ℝ) (m L T : ℕ)
    (hm : 1 ≤ m) (hL : 0 < L) (kt : ℕ → ℕ) :
    (multibandEnvelopeMatrix C m L T kt * multibandEnvelopeMatrix C m L T kt).trace ≤
      VAllow C m (2 ^ T * L) L T kt := by
  have hm0 : m ≠ 0 := by omega
  rw [multibandEnvelopeMatrix, weightedHistogramBandMatrix_square_trace L T hL]
  calc
    _ ≤ ∑ t ∈ Finset.range (T + 1),
        2 * C ^ 2 * ((m : ℝ)⁻¹ ^ 2 +
          ((m : ℝ) ^ (-2 : ℤ)) ^ 2 * (kt t : ℝ) ^ 2) * (bandDimension L t : ℝ) := by
      apply Finset.sum_le_sum
      intro t ht
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      rw [mul_pow]
      have hi : ((m : ℝ)⁻¹ + (m : ℝ) ^ (-2 : ℤ) * (kt t : ℝ)) ^ 2 ≤
          2 * ((m : ℝ)⁻¹ ^ 2 + ((m : ℝ) ^ (-2 : ℤ)) ^ 2 * (kt t : ℝ) ^ 2) := by
        nlinarith [sq_nonneg ((m : ℝ)⁻¹ - (m : ℝ) ^ (-2 : ℤ) * (kt t : ℝ))]
      calc
        _ ≤ C ^ 2 * (2 * ((m : ℝ)⁻¹ ^ 2 +
            ((m : ℝ) ^ (-2 : ℤ)) ^ 2 * (kt t : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hi (sq_nonneg C)
        _ = _ := by ring
    _ = 2 * C ^ 2 * ((m : ℝ)⁻¹ ^ 2 *
        (∑ t ∈ Finset.range (T + 1), (bandDimension L t : ℝ)) +
        ((m : ℝ) ^ (-2 : ℤ)) ^ 2 *
          ∑ t ∈ Finset.range (T + 1), (bandDimension L t : ℝ) * (kt t : ℝ) ^ 2) := by
      simp only [mul_add, add_mul, Finset.sum_add_distrib]
      rw [← Finset.mul_sum]
      have hterm : ∀ t, 2 * C ^ 2 * (((m : ℝ) ^ (-2 : ℤ)) ^ 2 * (kt t : ℝ) ^ 2) *
          (bandDimension L t : ℝ) =
          (2 * C ^ 2 * ((m : ℝ) ^ (-2 : ℤ)) ^ 2) *
            ((bandDimension L t : ℝ) * (kt t : ℝ) ^ 2) := by intro t; ring
      simp_rw [hterm]
      rw [← Finset.mul_sum]
      ring
    _ = _ := by
      have hdim : (∑ t ∈ Finset.range (T + 1), (bandDimension L t : ℝ)) =
          (2 ^ T * L : ℕ) := by exact_mod_cast sum_bandDimension L T
      rw [hdim, VAllow, if_neg hm0]
      simp only [zpow_neg, zpow_ofNat, inv_pow, ← pow_mul]
      ring

/-- A symmetric positive covariance dominated by (17) satisfies the trace allowance. -/
-- @node: covarianceSquareTrace_le_VAllow_of_multiband
lemma covarianceSquareTrace_le_VAllow_of_multiband (C : ℝ) (m L T : ℕ)
    (hm : 1 ≤ m) (hL : Dyadic L) (kt : ℕ → ℕ)
    (sigma : Matrix (Fin (2 ^ T * L)) (Fin (2 ^ T * L)) ℝ)
    (hpos : sigma.PosSemidef)
    (hform : ∀ f : Hj (2 ^ T * L), covarianceForm sigma f ≤
      C * ((m : ℝ)⁻¹ * ‖f‖ ^ 2 + (m : ℝ) ^ (-2 : ℤ) *
        ∑ t ∈ Finset.range (T + 1), (kt t : ℝ) * ‖Qband L (2 ^ T * L) t f‖ ^ 2)) :
    covarianceSquareTrace sigma ≤ VAllow C m (2 ^ T * L) L T kt := by
  have hLpos : 0 < L := by obtain ⟨l, rfl⟩ := hL; positivity
  have hdiff : (multibandEnvelopeMatrix C m L T kt - sigma).PosSemidef := by
    apply posSemidef_of_covarianceForm_nonneg
    · exact (weightedHistogramBandMatrix_isHermitian _ _ _ _).sub hpos.isHermitian
    · intro f
      have h := hform f
      rw [← multibandEnvelopeMatrix_form C m L T hL kt f] at h
      have hsub : covarianceForm (multibandEnvelopeMatrix C m L T kt - sigma) f =
          covarianceForm (multibandEnvelopeMatrix C m L T kt) f - covarianceForm sigma f := by
        simp only [covarianceForm, Matrix.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]
      rw [hsub]
      exact sub_nonneg.mpr h
  rw [covarianceSquareTrace_eq_trace]
  exact (trace_square_le_of_posSemidef_sub sigma _ hpos hdiff).trans
    (multibandEnvelopeMatrix_square_trace_le_VAllow C m L T hm hLpos kt)

end CausalSmith.Stat.DensityEffectRoughNull
