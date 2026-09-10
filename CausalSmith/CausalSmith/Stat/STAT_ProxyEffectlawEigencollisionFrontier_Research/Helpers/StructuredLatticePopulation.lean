import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.StructuredLatticeResiduals
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.AmbientOperatorBridge
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.ModelSpectralConstruction
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.StructuredLatticeOracle
import CausalSmith.Substrate.CollisionSafeSpectralLaw.RetainedSVD

/-! # Population tuple and ideal-to-summary residual bridges -/

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

noncomputable section

open scoped Matrix.Norms.L2Operator

open CausalSmith.Substrate.CollisionSafeSpectralLaw
open Causalean.Mathlib.Probability
open MeasureTheory

/-- The first `r` positive directions of the paper-local singular system, packaged for the
neutral retained-SVD substrate. -/
noncomputable def singularSystemRetainedSVD
    {rows cols r : ℕ} (A : RectMatrix rows cols) (hrc : r ≤ cols)
    (hpos : ∀ a : Fin r, 0 < (singularSystem A).sigma (Fin.castLE hrc a)) :
    RetainedSVD r rows cols where
  sigma a := (singularSystem A).sigma (Fin.castLE hrc a)
  left i a := (singularSystem A).left (Fin.castLE hrc a) i
  right a j := (singularSystem A).right (Fin.castLE hrc a) j
  sigma_pos := hpos
  left_orthonormal := by
    ext a b
    change (∑ i, (singularSystem A).left (Fin.castLE hrc a) i *
      (singularSystem A).left (Fin.castLE hrc b) i) = if a = b then 1 else 0
    simpa using
      (singularSystem A).left_orthonormal_of_pos (Fin.castLE hrc a) (Fin.castLE hrc b)
        (hpos a) (hpos b)
  right_orthonormal := by
    ext a b
    change (∑ i, (singularSystem A).right (Fin.castLE hrc a) i *
      (singularSystem A).right (Fin.castLE hrc b) i) = if a = b then 1 else 0
    simpa using
      (singularSystem A).right_orthonormal (Fin.castLE hrc a) (Fin.castLE hrc b)

/-- Matrix obtained by retaining exactly the singular directions at or above a threshold. -/
noncomputable def thresholdSingularTruncation {rows cols : ℕ} (threshold : ℝ)
    (A : RectMatrix rows cols) : RectMatrix rows cols :=
  fun i j => ∑ x, if threshold ≤ (singularSystem A).sigma x then
    (singularSystem A).sigma x * (singularSystem A).left x i *
      (singularSystem A).right x j else 0

lemma thresholdSingularTruncation_eq_retained
    {rows cols r : ℕ} {threshold : ℝ} (A : RectMatrix rows cols)
    (hrc : r ≤ cols) (hthreshold : 0 < threshold)
    (hrec : ThresholdRecoversMatrixDimension r threshold A) :
    thresholdSingularTruncation threshold A =
      (singularSystemRetainedSVD A hrc (fun a => hthreshold.trans_le
        (by simpa [(singularSystem A).sigma_eq] using hrec.1 (a : ℕ) a.isLt))).matrix := by
  let hpos : ∀ a : Fin r, 0 < (singularSystem A).sigma (Fin.castLE hrc a) :=
    fun a => hthreshold.trans_le
      (by simpa [(singularSystem A).sigma_eq] using hrec.1 (a : ℕ) a.isLt)
  let S := singularSystemRetainedSVD A hrc hpos
  ext i j
  have hsel (x : Fin cols) : threshold ≤ (singularSystem A).sigma x ↔ (x : ℕ) < r := by
    rw [(singularSystem A).sigma_eq]
    exact ⟨fun hx => by by_contra hn; exact (not_le_of_gt (hrec.2 x (by omega))) hx,
      hrec.1 x⟩
  change (∑ x, if threshold ≤ (singularSystem A).sigma x then
      (singularSystem A).sigma x * (singularSystem A).left x i *
        (singularSystem A).right x j else 0) = _
  rw [S.matrix_apply]
  simp only [S, singularSystemRetainedSVD]
  simp_rw [hsel]
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun a _ => Fin.castLE hrc a)
  · intro a _; simp
  · intro a _ b _ hab; exact Fin.castLE_injective hrc hab
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    let a : Fin r := ⟨b, hb⟩
    exact ⟨a, Finset.mem_univ a, Fin.ext rfl⟩
  · intro a _
    simp_all only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, mul_eq_mul_right_iff]

/-- An upper bound on every discarded singular coefficient controls the truncation error. -/
lemma thresholdSingularTruncation_error_le_of_discardedBound
    {rows cols : ℕ} {threshold bound : ℝ} (A : RectMatrix rows cols)
    (hthreshold : 0 < threshold) (hbound0 : 0 ≤ bound)
    (hdiscard : ∀ a, ¬ threshold ≤ (singularSystem A).sigma a →
      (singularSystem A).sigma a ≤ bound) :
    ‖matrixCLM (A - thresholdSingularTruncation threshold A)‖ ≤ bound := by
  let ss := singularSystem A
  let active : Type := {a : Fin cols // ¬ threshold ≤ ss.sigma a ∧ 0 < ss.sigma a}
  let u : active → Euc rows := fun a => WithLp.toLp 2 (ss.left a)
  let v : Fin cols → Euc cols := fun a => WithLp.toLp 2 (ss.right a)
  have hu : Orthonormal ℝ u := by
    rw [orthonormal_iff_ite]
    intro a b
    simpa only [u, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      Subtype.coe_eta, Subtype.coe_inj, eq_comm] using
      ss.left_orthonormal_of_pos b a b.property.2 a.property.2
  have hv : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    intro a b
    simpa only [v, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, eq_comm] using
      ss.right_orthonormal b a
  apply ContinuousLinearMap.opNorm_le_bound _ hbound0
  intro x
  let c : active → ℝ := fun a => ss.sigma a * inner ℝ (v a) x
  have haction : matrixCLM (A - thresholdSingularTruncation threshold A) x =
      ∑ a : active, c a • u a := by
    ext i
    simp [matrixCLM, Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct, c, u, v,
      PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      thresholdSingularTruncation]
    simp_rw [ss.expansion]
    simp_rw [Finset.sum_mul]
    have hsub : (∑ a : active,
        (ss.sigma a * ∑ j, x.ofLp j * ss.right a j) * ss.left a i) =
        ∑ a ∈ Finset.univ.filter
          (fun a => ¬ threshold ≤ ss.sigma a ∧ 0 < ss.sigma a),
          (ss.sigma a * ∑ j, x.ofLp j * ss.right a j) * ss.left a i := by
      symm
      apply Finset.sum_subtype
      intro a
      simp
    rw [hsub]
    rw [show singularSystem A = ss from rfl]
    have hcomm₁ : (∑ j : Fin cols, ∑ a : Fin cols,
        ss.sigma a * ss.left a i * ss.right a j * x.ofLp j) =
        ∑ a : Fin cols, ∑ j : Fin cols,
          ss.sigma a * ss.left a i * ss.right a j * x.ofLp j := by
      rw [Finset.sum_comm]
    have hcomm₂ : (∑ j : Fin cols, ∑ a : Fin cols,
        (if threshold ≤ ss.sigma a then
          ss.sigma a * ss.left a i * ss.right a j else 0) * x.ofLp j) =
        ∑ a : Fin cols, ∑ j : Fin cols,
          (if threshold ≤ ss.sigma a then
            ss.sigma a * ss.left a i * ss.right a j else 0) * x.ofLp j := by
      rw [Finset.sum_comm]
    rw [hcomm₁, hcomm₂, ← Finset.sum_sub_distrib, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a _
    by_cases hkeep : threshold ≤ ss.sigma a
    · simp_rw [hkeep]
      simp
    · by_cases hz : ss.sigma a = 0
      · simp [hz]
      · have hp : 0 < ss.sigma a := lt_of_le_of_ne (ss.sigma_nonneg a) (Ne.symm hz)
        simp_rw [hkeep]
        simp [hp]
        rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring
  rw [haction]
  have hinner := hu.inner_sum c c Finset.univ
  have hsq : ‖∑ a : active, c a • u a‖ ^ 2 ≤
      bound ^ 2 * ‖x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    rw [hinner]
    calc
      (∑ a : active, c a * c a) ≤
          ∑ a : active, bound ^ 2 * ‖inner ℝ (v a) x‖ ^ 2 := by
        change Finset.univ.sum (fun a => c a * c a) ≤
          Finset.univ.sum (fun a : active =>
            bound ^ 2 * ‖inner ℝ (v (a : Fin cols)) x‖ ^ 2)
        apply Finset.sum_le_sum (s := (Finset.univ : Finset active))
        intro a _
        have hsle : ss.sigma a ≤ bound := hdiscard a a.property.1
        have hs0 : 0 ≤ ss.sigma a := ss.sigma_nonneg a
        have hs2 : ss.sigma a ^ 2 ≤ bound ^ 2 := by nlinarith
        dsimp [c]
        calc
          ss.sigma a * inner ℝ (v a) x * (ss.sigma a * inner ℝ (v a) x) =
              ss.sigma a ^ 2 * inner ℝ (v a) x ^ 2 := by ring
          _ ≤ bound ^ 2 * inner ℝ (v a) x ^ 2 :=
            mul_le_mul_of_nonneg_right hs2 (sq_nonneg _)
          _ = bound ^ 2 * ‖inner ℝ (v a) x‖ ^ 2 := by
            rw [Real.norm_eq_abs, sq_abs]
      _ = bound ^ 2 * ∑ a : active, ‖inner ℝ (v a) x‖ ^ 2 := by
        rw [Finset.mul_sum]
      _ ≤ bound ^ 2 * ‖x‖ ^ 2 := by
        gcongr
        have hsub : (∑ a : active, ‖inner ℝ (v a) x‖ ^ 2) =
            ∑ a ∈ Finset.univ.filter
              (fun a => ¬ threshold ≤ ss.sigma a ∧ 0 < ss.sigma a),
              ‖inner ℝ (v a) x‖ ^ 2 := by
          symm
          apply Finset.sum_subtype
          intro a
          simp
        rw [hsub]
        exact hv.sum_inner_products_le x
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hbound0 (norm_nonneg _))).mp
    (by simpa [mul_pow] using hsq)

/-- Discarding singular directions below a positive threshold changes the matrix by at most
the threshold in operator norm. -/
lemma thresholdSingularTruncation_error_le
    {rows cols : ℕ} {threshold : ℝ} (A : RectMatrix rows cols)
    (hthreshold : 0 < threshold) :
    ‖matrixCLM (A - thresholdSingularTruncation threshold A)‖ ≤ threshold := by
  apply thresholdSingularTruncation_error_le_of_discardedBound A hthreshold
    (le_of_lt hthreshold)
  intro a ha
  exact le_of_lt (lt_of_not_ge ha)

/-- Dimension recovery makes the thresholded singular truncation have exactly the target rank. -/
lemma thresholdSingularTruncation_rank
    {rows cols r : ℕ} {threshold : ℝ} (A : RectMatrix rows cols)
    (hrc : r ≤ cols) (hthreshold : 0 < threshold)
    (hrec : ThresholdRecoversMatrixDimension r threshold A) :
    (thresholdSingularTruncation threshold A).rank = r := by
  rw [thresholdSingularTruncation_eq_retained A hrc hthreshold hrec]
  exact RetainedSVD.rank_matrix _

-- keep: generic thresholded-SVD perturbation estimate for future finite-dimensional models
/-- Truncation costs at most one cutoff radius in addition to the original perturbation. -/
lemma thresholdSingularTruncation_sub_norm_le
    {rows cols : ℕ} {threshold e : ℝ} (A M : RectMatrix rows cols)
    (hthreshold : 0 < threshold) (hAM : ‖matrixCLM (A - M)‖ ≤ e) :
    ‖matrixCLM (thresholdSingularTruncation threshold A - M)‖ ≤ threshold + e := by
  have hsplit : thresholdSingularTruncation threshold A - M =
      -(A - thresholdSingularTruncation threshold A) + (A - M) := by abel
  rw [hsplit]
  calc
    ‖matrixCLM (-(A - thresholdSingularTruncation threshold A) + (A - M))‖ ≤
        ‖matrixCLM (-(A - thresholdSingularTruncation threshold A))‖ +
          ‖matrixCLM (A - M)‖ := by
      simpa only [matrixCLM, map_add] using norm_add_le
        (matrixCLM (-(A - thresholdSingularTruncation threshold A)))
        (matrixCLM (A - M))
    _ = ‖matrixCLM (A - thresholdSingularTruncation threshold A)‖ +
          ‖matrixCLM (A - M)‖ := by simp only [matrixCLM, map_neg, norm_neg]
    _ ≤ threshold + e := add_le_add
      (thresholdSingularTruncation_error_le A hthreshold) hAM

/-- Weyl's inequality transfers a last-signal singular margin to a nearby empirical matrix. -/
lemma singularValue_lower_of_perturbation
    {rows cols r : ℕ} {s e : ℝ} (A M : RectMatrix rows cols)
    (hmargin : s ≤ singularValue M (r - 1))
    (hAM : ‖matrixCLM (A - M)‖ ≤ e) :
    s - e ≤ singularValue A (r - 1) := by
  have hadd : M + (A - M) = A := by abel
  have hw := singular_value_weyl (j := r - 1) M (A - M)
  rw [hadd] at hw
  rw [abs_le] at hw
  linarith

/-- If the comparison matrix has rank `r` and recovery retains the first `r` directions, the
discarded empirical tail is bounded by the original perturbation radius. -/
lemma thresholdSingularTruncation_error_le_of_rank_perturbation
    {rows cols r : ℕ} {threshold e : ℝ} (A M : RectMatrix rows cols)
    (hthreshold : 0 < threshold)
    (hrec : ThresholdRecoversMatrixDimension r threshold A)
    (hrank : M.rank = r) (hAM : ‖matrixCLM (A - M)‖ ≤ e) :
    ‖matrixCLM (A - thresholdSingularTruncation threshold A)‖ ≤ e := by
  have he0 : 0 ≤ e := (norm_nonneg (matrixCLM (A - M))).trans hAM
  apply thresholdSingularTruncation_error_le_of_discardedBound A hthreshold he0
  intro a hdrop
  have har : r ≤ (a : ℕ) := by
    by_contra hnot
    exact hdrop (by
      rw [(singularSystem A).sigma_eq]
      exact hrec.1 a (Nat.lt_of_not_ge hnot))
  have hz : singularValue M a = 0 := by
    unfold singularValue
    apply (Matrix.toEuclideanLin M).singularValues_eq_zero_iff_le_finrank_range.mpr
    have hrange : Module.finrank ℝ (Matrix.toEuclideanLin M).range = M.rank :=
      (M.rank_eq_finrank_range_toLin
        (EuclideanSpace.basisFun (Fin rows) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin cols) ℝ).toBasis).symm
    rw [hrange, hrank]
    exact har
  have hadd : M + (A - M) = A := by abel
  have hw := singular_value_weyl (j := (a : ℕ)) M (A - M)
  rw [hadd, hz, sub_zero] at hw
  change |(Matrix.toEuclideanLin A).singularValues (a : ℕ)| ≤ _ at hw
  rw [abs_of_nonneg ((Matrix.toEuclideanLin A).singularValues_nonneg _)] at hw
  rw [(singularSystem A).sigma_eq]
  exact hw.trans hAM

/-- Rank-aware truncation stays within twice the original perturbation radius of the rank-`r`
comparison matrix. -/
lemma thresholdSingularTruncation_sub_norm_le_two_mul
    {rows cols r : ℕ} {threshold e : ℝ} (A M : RectMatrix rows cols)
    (hthreshold : 0 < threshold)
    (hrec : ThresholdRecoversMatrixDimension r threshold A)
    (hrank : M.rank = r) (hAM : ‖matrixCLM (A - M)‖ ≤ e) :
    ‖matrixCLM (thresholdSingularTruncation threshold A - M)‖ ≤ 2 * e := by
  have hsplit : thresholdSingularTruncation threshold A - M =
      -(A - thresholdSingularTruncation threshold A) + (A - M) := by abel
  rw [hsplit]
  calc
    _ ≤ ‖matrixCLM (A - thresholdSingularTruncation threshold A)‖ +
          ‖matrixCLM (A - M)‖ := by
      simpa only [matrixCLM, map_add, map_neg, norm_neg] using norm_add_le
        (matrixCLM (-(A - thresholdSingularTruncation threshold A)))
        (matrixCLM (A - M))
    _ ≤ e + e := add_le_add
      (thresholdSingularTruncation_error_le_of_rank_perturbation
        A M hthreshold hrec hrank hAM) hAM
    _ = 2 * e := by ring

/-- Dimension recovery identifies the paper's thresholded reciprocal expansion with the
neutral Moore--Penrose inverse of the retained rank-`r` SVD matrix. -/
lemma thresholdedPenroseInverse_eq_retained_moorePenrose
    {rows cols r : ℕ} {threshold : ℝ} (A : RectMatrix rows cols)
    (hrc : r ≤ cols) (hthreshold : 0 < threshold)
    (hrec : ThresholdRecoversMatrixDimension r threshold A) :
    thresholdedPenroseInverse threshold A =
      moorePenroseInverse
        ((singularSystemRetainedSVD A hrc (fun a => hthreshold.trans_le
          (by simpa [(singularSystem A).sigma_eq] using hrec.1 (a : ℕ) a.isLt))).matrix) := by
  let hpos : ∀ a : Fin r, 0 < (singularSystem A).sigma (Fin.castLE hrc a) :=
    fun a => hthreshold.trans_le
      (by simpa [(singularSystem A).sigma_eq] using hrec.1 (a : ℕ) a.isLt)
  let S := singularSystemRetainedSVD A hrc hpos
  rw [← S.inverse_eq_moorePenroseInverse]
  ext i j
  have hsel (x : Fin cols) : threshold ≤ (singularSystem A).sigma x ↔ (x : ℕ) < r := by
    rw [(singularSystem A).sigma_eq]
    exact ⟨fun hx => by by_contra hn; exact (not_le_of_gt (hrec.2 x (by omega))) hx,
      hrec.1 x⟩
  change (∑ x, if threshold ≤ (singularSystem A).sigma x then
      ((singularSystem A).sigma x)⁻¹ * (singularSystem A).right x i *
        (singularSystem A).left x j else 0) = _
  rw [RetainedSVD.inverse]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal_apply]
  simp only [S, singularSystemRetainedSVD]
  simp_rw [hsel]
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun a _ => Fin.castLE hrc a)
  · intro a _
    simp
  · intro a _ b _ hab
    exact Fin.castLE_injective hrc hab
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    let a : Fin r := ⟨b, hb⟩
    refine ⟨a, Finset.mem_univ a, ?_⟩
    exact Fin.ext rfl
  · intro a _
    simp_all
    apply Or.inl
    ring

/-- The thresholded reciprocal expansion inherits any lower bound on the last retained
singular coefficient. -/
lemma thresholdedPenroseInverse_norm_le_of_recovery
    {rows cols r : ℕ} {threshold s : ℝ} (A : RectMatrix rows cols)
    (hrc : r ≤ cols) (_hrpos : 0 < r) (hthreshold : 0 < threshold)
    (hrec : ThresholdRecoversMatrixDimension r threshold A)
    (hs : 0 < s) (hmargin : s ≤ singularValue A (r - 1)) :
    ‖thresholdedPenroseInverse threshold A‖ ≤ s⁻¹ := by
  let hpos : ∀ a : Fin r, 0 < (singularSystem A).sigma (Fin.castLE hrc a) :=
    fun a => hthreshold.trans_le
      (by simpa [(singularSystem A).sigma_eq] using hrec.1 (a : ℕ) a.isLt)
  let S := singularSystemRetainedSVD A hrc hpos
  rw [thresholdedPenroseInverse_eq_retained_moorePenrose A hrc hthreshold hrec,
    ← S.inverse_eq_moorePenroseInverse]
  apply S.norm_inverse_le hs
  intro a
  have hanti := (Matrix.toEuclideanLin A).singularValues_antitone
    (Nat.le_sub_one_of_lt a.isLt)
  exact hmargin.trans (by
    simpa [S, singularSystemRetainedSVD, (singularSystem A).sigma_eq,
      singularValue] using hanti)

/-- One arm of the empirical thresholded product is stable with the constants used by the
frozen structured-lattice modulus. -/
lemma thresholded_product_perturbation_le
    {rows cols r : ℕ} {s0 L eM eN : ℝ}
    (A M N N₀ : RectMatrix rows cols)
    (hrc : r ≤ cols) (hrpos : 0 < r) (hs0 : 0 < s0) (hL0 : 0 ≤ L)
    (hsmall : eM < s0 / 4)
    (hrec : ThresholdRecoversMatrixDimension r (s0 / 2) A)
    (hrank : M.rank = r) (hmargin : s0 ≤ singularValue M (r - 1))
    (hN₀ : ‖N₀‖ ≤ L)
    (hMdiff : ‖matrixCLM (A - M)‖ ≤ eM)
    (hNdiff : ‖matrixCLM (N - N₀)‖ ≤ eN) :
    ‖thresholdedPenroseInverse (s0 / 2) A * N - moorePenroseInverse M * N₀‖ ≤
      16 * L / s0 ^ 2 * eM + 4 / (3 * s0) * eN := by
  let T := thresholdSingularTruncation (s0 / 2) A
  have hthreshold : 0 < s0 / 2 := by positivity
  have heM0 : 0 ≤ eM := (norm_nonneg (matrixCLM (A - M))).trans hMdiff
  have hs34 : 0 < 3 * s0 / 4 := by positivity
  have hmarginA : 3 * s0 / 4 ≤ singularValue A (r - 1) := by
    have hweyl := singularValue_lower_of_perturbation A M hmargin hMdiff
    linarith
  have hrankT : T.rank = r := by
    exact thresholdSingularTruncation_rank A hrc hthreshold hrec
  have hTdiff : ‖matrixCLM (T - M)‖ ≤ 2 * eM := by
    exact thresholdSingularTruncation_sub_norm_le_two_mul
      A M hthreshold hrec hrank hMdiff
  let hpos : ∀ a : Fin r, 0 < (singularSystem A).sigma (Fin.castLE hrc a) :=
    fun a => hthreshold.trans_le
      (by simpa [(singularSystem A).sigma_eq] using hrec.1 (a : ℕ) a.isLt)
  let R := singularSystemRetainedSVD A hrc hpos
  have htr : T = R.matrix := by
    simpa [T, R, hpos] using
      thresholdSingularTruncation_eq_retained A hrc hthreshold hrec
  have heq : thresholdedPenroseInverse (s0 / 2) A = moorePenroseInverse T := by
    calc
      _ = moorePenroseInverse R.matrix := by
        simpa [R, hpos] using
          thresholdedPenroseInverse_eq_retained_moorePenrose A hrc hthreshold hrec
      _ = moorePenroseInverse T := congrArg moorePenroseInverse htr.symm
  have hinvT : ‖moorePenroseInverse T‖ ≤ 4 / (3 * s0) := by
    rw [← heq]
    have h := thresholdedPenroseInverse_norm_le_of_recovery
      A hrc hrpos hthreshold hrec hs34 hmarginA
    convert h using 1 <;> field_simp
  have hinvM0 : ‖moorePenroseInverse M‖ ≤ s0⁻¹ :=
    norm_moorePenroseInverse_le_inv M hrank hs0 hmargin
  have hinvM : ‖moorePenroseInverse M‖ ≤ 4 / (3 * s0) := by
    have hs0ne : s0 ≠ 0 := ne_of_gt hs0
    rw [inv_eq_one_div] at hinvM0
    exact hinvM0.trans (by
      apply (div_le_div_iff₀ hs0 (mul_pos (by norm_num) hs0)).2
      nlinarith)
  have hmp : ‖moorePenroseInverse T - moorePenroseInverse M‖ ≤
      16 / s0 ^ 2 * eM := by
    have hraw := norm_moorePenrose_sub_le T M (hrankT.trans hrank.symm)
    calc
      _ ≤ 3 * max (‖moorePenroseInverse T‖ ^ 2)
          (‖moorePenroseInverse M‖ ^ 2) * ‖T - M‖ := hraw
      _ ≤ 3 * (4 / (3 * s0)) ^ 2 * (2 * eM) := by
        gcongr
        · exact max_le (by nlinarith [norm_nonneg (moorePenroseInverse T)])
            (by nlinarith [norm_nonneg (moorePenroseInverse M)])
        · exact hTdiff
      _ ≤ 16 / s0 ^ 2 * eM := by
        field_simp [ne_of_gt hs0]
        nlinarith
  have hsplit : thresholdedPenroseInverse (s0 / 2) A * N -
      moorePenroseInverse M * N₀ =
      (moorePenroseInverse T - moorePenroseInverse M) * N₀ +
        thresholdedPenroseInverse (s0 / 2) A * (N - N₀) := by
    rw [heq, Matrix.sub_mul, Matrix.mul_sub]
    abel
  rw [hsplit]
  have hNdiff' : ‖N - N₀‖ ≤ eN := by
    change ‖matrixCLM (N - N₀)‖ ≤ eN
    exact hNdiff
  calc
    _ ≤ ‖(moorePenroseInverse T - moorePenroseInverse M) * N₀‖ +
        ‖thresholdedPenroseInverse (s0 / 2) A * (N - N₀)‖ := norm_add_le _ _
    _ ≤ ‖moorePenroseInverse T - moorePenroseInverse M‖ * ‖N₀‖ +
        ‖thresholdedPenroseInverse (s0 / 2) A‖ * ‖N - N₀‖ :=
      add_le_add (Matrix.l2_opNorm_mul _ _) (Matrix.l2_opNorm_mul _ _)
    _ ≤ (16 / s0 ^ 2 * eM) * L + (4 / (3 * s0)) * eN := by
      rw [heq]
      gcongr
    _ = 16 * L / s0 ^ 2 * eM + 4 / (3 * s0) * eN := by ring

/-- The two empirical arms obey the exact operator coefficient used in the frozen theorem. -/
lemma empiricalCompressedOperator_sub_ambientEffectOperator_norm_le
    {dx dz r : ℕ} {s0 L : ℝ} (s p : SummarySpace dx dz)
    (hrc : r ≤ dx) (hrpos : 0 < r) (hs0 : 0 < s0) (hL0 : 0 ≤ L)
    (hsmall : dS s p < s0 / 4)
    (hrec0 : ThresholdRecoversMatrixDimension r (s0 / 2) s.M0)
    (hrec1 : ThresholdRecoversMatrixDimension r (s0 / 2) s.M1)
    (hrank0 : p.M0.rank = r) (hrank1 : p.M1.rank = r)
    (hmargin0 : s0 ≤ singularValue p.M0 (r - 1))
    (hmargin1 : s0 ≤ singularValue p.M1 (r - 1))
    (hN0 : ‖p.N0‖ ≤ L) (hN1 : ‖p.N1‖ ≤ L) :
    ‖matrixCLM (empiricalCompressedOperator (s0 / 2) s -
      AmbientOperatorBridge.ambientEffectOperator p)‖ ≤
      (8 / (3 * s0) + 32 * L / s0 ^ 2) * dS s p := by
  let e := dS s p
  have he0 : 0 ≤ e := by dsimp [e]; unfold dS; positivity
  have block_le (B : ℝ) (hB : B = ‖matrixCLM (s.M0 - p.M0)‖ ∨
      B = ‖matrixCLM (s.M1 - p.M1)‖ ∨
      B = ‖matrixCLM (s.N0 - p.N0)‖ ∨
      B = ‖matrixCLM (s.N1 - p.N1)‖) : B ≤ e := by
    rcases hB with rfl | rfl | rfl | rfl <;>
      dsimp [e] <;> unfold dS <;>
      have h0 : 0 ≤ ‖matrixCLM (s.M0 - p.M0)‖ := norm_nonneg _ <;>
      have h1 : 0 ≤ ‖matrixCLM (s.M1 - p.M1)‖ := norm_nonneg _ <;>
      have h2 : 0 ≤ ‖matrixCLM (s.N0 - p.N0)‖ := norm_nonneg _ <;>
      have h3 : 0 ≤ ‖matrixCLM (s.N1 - p.N1)‖ := norm_nonneg _ <;>
      have hsqrt : 0 ≤ Real.sqrt (∑ i, (s.mX i - p.mX i) ^ 2) := Real.sqrt_nonneg _ <;>
      linarith
  have hM0 : ‖matrixCLM (s.M0 - p.M0)‖ ≤ e := by
    exact block_le _ (Or.inl rfl)
  have hM1 : ‖matrixCLM (s.M1 - p.M1)‖ ≤ e := by
    exact block_le _ (Or.inr (Or.inl rfl))
  have hN0' : ‖matrixCLM (s.N0 - p.N0)‖ ≤ e := by
    exact block_le _ (Or.inr (Or.inr (Or.inl rfl)))
  have hN1' : ‖matrixCLM (s.N1 - p.N1)‖ ≤ e := by
    exact block_le _ (Or.inr (Or.inr (Or.inr rfl)))
  have hsmall' : e < s0 / 4 := hsmall
  have harm0 := thresholded_product_perturbation_le s.M0 p.M0 s.N0 p.N0
    hrc hrpos hs0 hL0 hsmall' hrec0 hrank0 hmargin0 hN0 hM0 hN0'
  have harm1 := thresholded_product_perturbation_le s.M1 p.M1 s.N1 p.N1
    hrc hrpos hs0 hL0 hsmall' hrec1 hrank1 hmargin1 hN1 hM1 hN1'
  have hsplit : empiricalCompressedOperator (s0 / 2) s -
      AmbientOperatorBridge.ambientEffectOperator p =
      (thresholdedPenroseInverse (s0 / 2) s.M1 * s.N1 -
        moorePenroseInverse p.M1 * p.N1) -
      (thresholdedPenroseInverse (s0 / 2) s.M0 * s.N0 -
        moorePenroseInverse p.M0 * p.N0) := by
    simp only [empiricalCompressedOperator, AmbientOperatorBridge.ambientEffectOperator]
    abel
  rw [hsplit]
  calc
    _ ≤ ‖thresholdedPenroseInverse (s0 / 2) s.M1 * s.N1 -
          moorePenroseInverse p.M1 * p.N1‖ +
        ‖thresholdedPenroseInverse (s0 / 2) s.M0 * s.N0 -
          moorePenroseInverse p.M0 * p.N0‖ := norm_sub_le _ _
    _ ≤ (16 * L / s0 ^ 2 * e + 4 / (3 * s0) * e) +
        (16 * L / s0 ^ 2 * e + 4 / (3 * s0) * e) := add_le_add harm1 harm0
    _ = (8 / (3 * s0) + 32 * L / s0 ^ 2) * dS s p := by
      dsimp [e]
      ring

/-- Each proxy-moment arm is dominated by the full summary distance. -/
lemma observedProxyMoment_sub_norm_le_dS {dx dz : ℕ}
    (s p : SummarySpace dx dz) (t : Bool) :
    ‖matrixCLM (observedProxyMoment s t - observedProxyMoment p t)‖ ≤ dS s p := by
  cases t <;> simp [observedProxyMoment] <;> unfold dS
  · have h1 : 0 ≤ ‖matrixCLM (s.M1 - p.M1)‖ := norm_nonneg _
    have h2 : 0 ≤ ‖matrixCLM (s.N0 - p.N0)‖ := norm_nonneg _
    have h3 : 0 ≤ ‖matrixCLM (s.N1 - p.N1)‖ := norm_nonneg _
    have hs : 0 ≤ Real.sqrt (∑ i, (s.mX i - p.mX i) ^ 2) := Real.sqrt_nonneg _
    linarith
  · have h0 : 0 ≤ ‖matrixCLM (s.M0 - p.M0)‖ := norm_nonneg _
    have h2 : 0 ≤ ‖matrixCLM (s.N0 - p.N0)‖ := norm_nonneg _
    have h3 : 0 ≤ ‖matrixCLM (s.N1 - p.N1)‖ := norm_nonneg _
    have hs : 0 ≤ Real.sqrt (∑ i, (s.mX i - p.mX i) ^ 2) := Real.sqrt_nonneg _
    linarith

-- keep: generic selector characterization for the thresholded Penrose-inverse API
/-- Under the dimension-recovery certificate, the custom thresholded SVD retains exactly the
first `k` singular directions. -/
lemma thresholdedPenroseInverse_select_iff
    {rows cols k : ℕ} {threshold : ℝ} (A : RectMatrix rows cols)
    (hrec : ThresholdRecoversMatrixDimension k threshold A) (r : Fin cols) :
    threshold ≤ (singularSystem A).sigma r ↔ (r : ℕ) < k := by
  rw [(singularSystem A).sigma_eq]
  constructor
  · intro hr
    by_contra hnot
    exact (not_le_of_gt (hrec.2 r (by omega))) hr
  · exact hrec.1 r

-- keep: generic rank-to-zero-singular-value bridge used by future truncation arguments
/-- Every direction discarded after the recovered rank is genuinely a zero singular direction
of the rank-`k` comparison matrix. -/
lemma singularSystem_sigma_eq_zero_of_rank
    {rows cols k : ℕ} (A : RectMatrix rows cols) (hrank : A.rank = k)
    (r : Fin cols) (hr : k ≤ (r : ℕ)) :
    (singularSystem A).sigma r = 0 := by
  rw [(singularSystem A).sigma_eq]
  unfold singularValue
  apply (Matrix.toEuclideanLin A).singularValues_eq_zero_iff_le_finrank_range.mpr
  have hrange : Module.finrank ℝ (Matrix.toEuclideanLin A).range = A.rank :=
    (A.rank_eq_finrank_range_toLin
      (EuclideanSpace.basisFun (Fin rows) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin cols) ℝ).toBasis).symm
  rw [hrange, hrank]
  exact hr

/-- A rank-`r` comparison with margin `s0`, perturbed by less than `s0/4`, is recovered by
thresholding at `s0/2`. -/
lemma thresholdRecoversMatrixDimension_of_rank_perturbation
    {rows cols r : ℕ} {s0 e : ℝ} (A M : RectMatrix rows cols)
    (hrpos : 0 < r) (hs0 : 0 < s0) (hrank : M.rank = r)
    (hmargin : s0 ≤ singularValue M (r - 1))
    (hAM : ‖matrixCLM (A - M)‖ ≤ e) (hsmall : e < s0 / 4) :
    ThresholdRecoversMatrixDimension r (s0 / 2) A := by
  have hkth : 3 * s0 / 4 ≤ singularValue A (r - 1) := by
    have h := singularValue_lower_of_perturbation A M hmargin hAM
    linarith
  constructor
  · intro j hj
    have hanti := (Matrix.toEuclideanLin A).singularValues_antitone
      (Nat.le_sub_one_of_lt hj)
    change s0 / 2 ≤ (Matrix.toEuclideanLin A).singularValues j
    change 3 * s0 / 4 ≤ (Matrix.toEuclideanLin A).singularValues (r - 1) at hkth
    linarith
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
    exact lt_of_le_of_lt (hw.trans hAM) (hsmall.trans (by linarith))

/-- Model membership specializes the two-arm perturbation certificate, including deriving
threshold recovery rather than assuming it. -/
lemma empiricalCompressedOperator_model_norm_le
    {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (P : MeasureTheory.Measure (FullData k dx dz)) [MeasureTheory.IsProbabilityMeasure P]
    (s : SummarySpace dx dz)
    (hk : 2 ≤ k) (hkx : k ≤ dx) (hkz : k ≤ dz) (hL : 1 ≤ L)
    (hpi : 0 < pi0) (hpiMax : pi0 ≤ 1 / (2 * k : ℝ))
    (hsigma : 0 < sigma0) (hsigmaMax : sigma0 ≤ 1)
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P)
    (hsmall : dS s (obsSummary P) < pi0 * sigma0 ^ 2 / 4) :
    ‖matrixCLM (empiricalCompressedOperator (pi0 * sigma0 ^ 2 / 2) s -
      AmbientOperatorBridge.ambientEffectOperator (obsSummary P))‖ ≤
      (8 / (3 * (pi0 * sigma0 ^ 2)) +
        32 * L / (pi0 * sigma0 ^ 2) ^ 2) * dS s (obsSummary P) := by
  let p := obsSummary P
  let s0 := pi0 * sigma0 ^ 2
  have hs0 : 0 < s0 := by dsimp [s0]; positivity
  have hb := AmbientOperatorBridge.model_summary_ambient_bounds
    P hk hkx hkz hL hpi hpiMax hsigma hsigmaMax hM
  have hrec (t : Bool) : ThresholdRecoversMatrixDimension k (s0 / 2)
      (observedProxyMoment s t) := by
    apply thresholdRecoversMatrixDimension_of_rank_perturbation
      (observedProxyMoment s t) (observedProxyMoment p t)
      (by omega) hs0 (by simpa [p] using (hb.1 t).1)
      (by simpa [s0, p] using (hb.1 t).2.1)
      (observedProxyMoment_sub_norm_le_dS s p t)
    simpa [s0, p] using hsmall
  apply empiricalCompressedOperator_sub_ambientEffectOperator_norm_le s p
    hkx (by omega) hs0 (le_trans zero_le_one hL)
  · simpa [s0, p] using hsmall
  · simpa [observedProxyMoment] using hrec false
  · simpa [observedProxyMoment] using hrec true
  · exact (hb.1 false).1
  · exact (hb.1 true).1
  · exact (hb.1 false).2.1
  · exact (hb.1 true).2.1
  · exact (hb.1 false).2.2
  · exact (hb.1 true).2.2

/-- Each latent-class conditional target-feature column retains the model's Euclidean envelope. -/
lemma targetFeature_column_norm_le
    {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (P : MeasureTheory.Measure (FullData k dx dz)) [MeasureTheory.IsProbabilityMeasure P]
    (hpi : 0 < pi0)
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P)
    (u : Fin k) :
    ‖(WithLp.toLp 2 (fun i => targetFeature P i u) : Euc dx)‖ ≤ L := by
  have hclass : 0 < P (latentClass u) :=
    lt_of_lt_of_le
      (latentCell_pos_of_latentArmPositivity P hpi hM.latentArmPositivity u false)
      (MeasureTheory.measure_mono fun _ hw => hw.1)
  let mu := normalizedRestrict P (latentClass u)
  let _ : MeasureTheory.IsProbabilityMeasure mu :=
    normalizedRestrict_isProbabilityMeasure (measurableSet_latentClass u) hclass
  have hXMeas : Measurable (fun w : FullData k dx dz =>
      (WithLp.toLp 2 w.X : Euc dx)) :=
    (WithLp.measurable_toLp 2 (Fin dx → ℝ)).comp measurable_fullData_X
  have hbound : ∀ᵐ w ∂mu, ‖(WithLp.toLp 2 w.X : Euc dx)‖ ≤ L :=
    (ae_normalizedRestrict_iff hclass).mpr <|
      MeasureTheory.ae_restrict_of_ae <| hM.boundedX.mono fun w hw => by
        simpa only [EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs] using hw
  have hXint : MeasureTheory.Integrable (fun w : FullData k dx dz =>
      (WithLp.toLp 2 w.X : Euc dx)) mu :=
    MeasureTheory.Integrable.of_bound hXMeas.aestronglyMeasurable L hbound
  have heq : (WithLp.toLp 2 (fun i => targetFeature P i u) : Euc dx) =
      ∫ w, (WithLp.toLp 2 w.X : Euc dx) ∂mu := by
    apply PiLp.ext
    intro i
    rw [eval_integral_piLp (fun j => hXint.eval_piLp j) i]
    change targetFeature P i u = _
    rw [targetFeature, conditionalMean_eq_normalizedRestrictedIntegral hclass]
    rfl
  rw [heq]
  calc
    ‖∫ w, (WithLp.toLp 2 w.X : Euc dx) ∂mu‖ ≤
        ∫ w, ‖(WithLp.toLp 2 w.X : Euc dx)‖ ∂mu :=
      MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ _w, L ∂mu :=
      MeasureTheory.integral_mono_ae hXint.norm
        (MeasureTheory.integrable_const _) hbound
    _ = L := by simp

/-- A matrix whose columns obey a common Euclidean envelope has the corresponding
square-root-of-cardinality operator envelope. -/
lemma matrixCLM_norm_le_sqrt_card_mul_of_column_norm_le
    {rows cols : ℕ} {L : ℝ} (hL : 0 ≤ L) (A : RectMatrix rows cols)
    (hcol : ∀ j, ‖(WithLp.toLp 2 (fun i => A i j) : Euc rows)‖ ≤ L) :
    ‖matrixCLM A‖ ≤ Real.sqrt cols * L := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Real.sqrt_nonneg _) hL)
  intro x
  let c : Fin cols → Euc rows := fun j => WithLp.toLp 2 (fun i => A i j)
  have haction : Matrix.toEuclideanLin A x = ∑ j, x j • c j := by
    apply PiLp.ext
    intro i
    simp [Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct, c, mul_comm]
  change ‖Matrix.toEuclideanLin A x‖ ≤ _
  rw [haction]
  calc
    ‖∑ j, x j • c j‖ ≤ ∑ j, ‖x j • c j‖ := by
      exact norm_sum_le Finset.univ _
    _ ≤ ∑ j, |x j| * L := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hcol j) (abs_nonneg _)
    _ = L * ∑ j, |x j| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ L * (Real.sqrt cols * ‖x‖) := by
      gcongr
      let one : Euc cols := WithLp.toLp 2 (fun _ => (1 : ℝ))
      let ax : Euc cols := WithLp.toLp 2 (fun j => |x j|)
      have hinner : ∑ j, |x j| = inner ℝ one ax := by
        simp [one, ax, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
      rw [hinner]
      calc
        inner ℝ one ax ≤ |inner ℝ one ax| := le_abs_self _
        _ ≤ ‖one‖ * ‖ax‖ := abs_real_inner_le_norm _ _
        _ = Real.sqrt cols * ‖x‖ := by
          congr 1
          · rw [EuclideanSpace.norm_eq]
            simp [one]
          · rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
            simp [ax, Real.norm_eq_abs]
    _ = (Real.sqrt cols * L) * ‖x‖ := by ring

/-- The coordinate factor has no larger operator norm than the original matrix because its
left factor has orthonormal columns. -/
lemma thinSignalFactorization_coord_transpose_norm_le
    {dx k : ℕ} {L : ℝ} (B : RectMatrix dx k)
    (hpos : ∀ r : Fin k, 0 < (singularSystem B).sigma r)
    (hL : 0 ≤ L)
    (hcol : ∀ j, ‖(WithLp.toLp 2 (fun i => B i j) : Euc dx)‖ ≤ L) :
    ‖matrixCLM (thinSignalFactorization B hpos).coord.transpose‖ ≤
      Real.sqrt k * L := by
  let F := thinSignalFactorization B hpos
  have hB : ‖matrixCLM B‖ ≤ Real.sqrt k * L :=
    matrixCLM_norm_le_sqrt_card_mul_of_column_norm_le hL B hcol
  have hcoord : ‖matrixCLM F.coord‖ ≤ Real.sqrt k * L := by
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Real.sqrt_nonneg _) hL)
    intro x
    change ‖Matrix.toEuclideanLin F.coord x‖ ≤ _
    have hiso := (signalBasisLinearIsometry F.V).norm_map
      (Matrix.toEuclideanLin F.coord x)
    change ‖Matrix.toEuclideanLin F.V.V (Matrix.toEuclideanLin F.coord x)‖ = _ at hiso
    rw [← hiso]
    have hfactor : Matrix.toEuclideanLin F.V.V (Matrix.toEuclideanLin F.coord x) =
        Matrix.toEuclideanLin B x := by
      have hf := congrArg (fun A : RectMatrix dx k => Matrix.toEuclideanLin A x) F.factor
      rw [show Matrix.toEuclideanLin (F.V.V * F.coord) x =
          Matrix.toEuclideanLin F.V.V (Matrix.toEuclideanLin F.coord x) by
        apply PiLp.ext
        intro i
        simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec]] at hf
      exact hf.symm
    rw [hfactor]
    exact (Matrix.l2_opNorm_mulVec B x).trans
      (mul_le_mul_of_nonneg_right hB (norm_nonneg x))
  change ‖F.coord.transpose‖ ≤ _
  change ‖F.coord‖ ≤ _ at hcoord
  rw [show ‖F.coord.transpose‖ = ‖F.coord‖ by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.l2_opNorm_conjTranspose F.coord]
  exact hcoord

/-- The transposed coordinate factor in the thin SVD inherits the certified lower singular
margin of every retained direction. -/
lemma thinSignalFactorization_coord_transpose_signalMinSingular
    {dx k : ℕ} (B : RectMatrix dx k)
    (hk : 0 < k) {s : ℝ} (hs : 0 ≤ s)
    (hpos : ∀ r : Fin k, 0 < (singularSystem B).sigma r)
    (hsle : ∀ r : Fin k, s ≤ (singularSystem B).sigma r) :
    s ≤ signalMinSingular (thinSignalFactorization B hpos).coord.transpose := by
  let S := singularSystem B
  let W : SignalBasis k k :=
    { V := fun i r => S.right r i
      orthonormal := fun r t => S.right_orthonormal r t }
  have hcoord : (thinSignalFactorization B hpos).coord.transpose =
      W.V * Matrix.diagonal S.sigma := by
    ext i j
    change (singularSystem B).sigma j * (singularSystem B).right j i = _
    rw [Matrix.mul_apply]
    simp [W, S, Matrix.diagonal_apply, mul_comm]
  apply Causalean.Mathlib.Analysis.le_singularValues_of_subspace
      (Matrix.toEuclideanLin (thinSignalFactorization B hpos).coord.transpose) ⊤ hs
  · simpa using hk
  · intro x _hx
    rw [hcoord]
    have hW := (signalBasisLinearIsometry W).norm_map
      (Matrix.toEuclideanLin (Matrix.diagonal S.sigma) x)
    change ‖Matrix.toEuclideanLin W.V
        (Matrix.toEuclideanLin (Matrix.diagonal S.sigma) x)‖ = _ at hW
    rw [show Matrix.toEuclideanLin (W.V * Matrix.diagonal S.sigma) x =
        Matrix.toEuclideanLin W.V
          (Matrix.toEuclideanLin (Matrix.diagonal S.sigma) x) by
      apply PiLp.ext
      intro i
      simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec]]
    rw [hW]
    apply (sq_le_sq₀ (mul_nonneg hs (norm_nonneg _)) (norm_nonneg _)).1
    rw [mul_pow, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    rw [Finset.mul_sum]
    simp only [Matrix.toEuclideanLin_apply]
    simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply]
    apply Finset.sum_le_sum
    intro r _
    change s ^ 2 * x r ^ 2 ≤ (S.sigma r * x r) ^ 2
    have hsigma : 0 ≤ S.sigma r := (S.sigma_nonneg r)
    have hsq : s ^ 2 ≤ (S.sigma r) ^ 2 := by nlinarith [hsle r]
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)

/-- The model supplies one common latent tuple whose mean, anchor, and ambient effect operator
have exactly the factorizations used by the structured lattice criterion. -/
lemma population_structured_tuple_exists
    {k dx dz : ℕ} {L pi0 sigma0 : ℝ}
    (P : MeasureTheory.Measure (FullData k dx dz)) [MeasureTheory.IsProbabilityMeasure P]
    (hk : 2 ≤ k) (hkx : k ≤ dx) (hL : 1 ≤ L) (hpi : 0 < pi0)
    (hsigma : 0 < sigma0)
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P) :
    ∃ (V : SignalBasis dx k) (R : RectMatrix k k) (p tau : Fin k → ℝ),
      (obsSummary P).mX = Matrix.mulVec (V.V * R.transpose) p ∧
      Matrix.mulVec (R * V.V.transpose) (firstBasis dx) = (fun _ => (1 : ℝ)) ∧
      AmbientOperatorBridge.ambientEffectOperator (obsSummary P) =
        V.V * R⁻¹ * Matrix.diagonal tau * R * V.V.transpose ∧
      sigma0 ≤ signalMinSingular R ∧
      ‖matrixCLM R‖ ≤ Real.sqrt k * L ∧
      (∀ u, 2 * pi0 ≤ p u) ∧ (∑ u, p u = 1) ∧
      (∀ u, tau u ∈ Set.Icc (-effectRadius dz L sigma0) (effectRadius dz L sigma0)) ∧
      ({ weight := p, atom := tau } : AtomicLaw k (effectRadius dz L sigma0)) =
        quotientLawRaw P (effectRadius dz L sigma0) := by
  let B := targetFeature P
  have hsle (r : Fin k) : sigma0 ≤ (singularSystem B).sigma r := by
    rw [(singularSystem B).sigma_eq]
    exact hM.proxyRankMargin.2.2.trans
      ((Matrix.toEuclideanLin B).singularValues_antitone (by
        simpa using Nat.le_sub_one_of_lt r.isLt))
  have hpos (r : Fin k) : 0 < (singularSystem B).sigma r := hsigma.trans_le (hsle r)
  let F := thinSignalFactorization B hpos
  let R : RectMatrix k k := F.coord.transpose
  have hRt : R.transpose = F.coord := by simp [R]
  have hRinv : R⁻¹ = F.coordInv.transpose := by
    apply Matrix.inv_eq_left_inv
    simpa [R, Matrix.transpose_mul] using congrArg Matrix.transpose F.coord_mul_inv
  have hRmin : sigma0 ≤ signalMinSingular R := by
    exact thinSignalFactorization_coord_transpose_signalMinSingular B (by omega)
      hsigma.le hpos hsle
  have hRnorm : ‖matrixCLM R‖ ≤ Real.sqrt k * L := by
    exact thinSignalFactorization_coord_transpose_norm_le B hpos (by linarith)
      (targetFeature_column_norm_le P hpi hM)
  have hp (u : Fin k) : 2 * pi0 ≤ latentMass P u := by
    rw [latentMass, show latentClass u = ⋃ t : Bool, latentCell u t by
      ext w
      simp [latentClass, latentCell]]
    rw [MeasureTheory.measureReal_iUnion_fintype
      (h' := fun t => MeasureTheory.measure_ne_top P (latentCell u t))]
    · rw [Fintype.sum_bool]
      simpa [two_mul] using add_le_add
        (hM.latentArmPositivity u true) (hM.latentArmPositivity u false)
    · intro t s hts
      unfold Function.onFun
      rw [Set.disjoint_left]
      intro w hwt hws
      exact hts (hwt.2.symm.trans hws.2)
    · exact fun t => measurableSet_latentCell u t
  have hvalid := quotientLawRaw_valid P hM
  refine ⟨F.V, R, latentMass P, latentEffect P, ?_, ?_, ?_, hRmin, hRnorm,
    hp, ?_, ?_, rfl⟩
  · rw [AmbientOperatorBridge.obsSummary_mX_factorization P hpi hM, hRt]
    exact congrArg (fun A => Matrix.mulVec A (latentMass P)) F.factor
  · have hanchor := AmbientOperatorBridge.targetFeature_transpose_firstBasis P hk hkx hpi hM
    rw [show R * F.V.V.transpose = B.transpose by
      rw [show R = F.coord.transpose by rfl, ← Matrix.transpose_mul, ← F.factor]]
    exact hanchor
  · rw [AmbientOperatorBridge.model_ambientEffectOperator_factorization
      P hk hkx hL hpi hsigma hM, hRinv]
    have hmp := factorOperator_eq_moorePenrose F (latentEffect P)
    rw [← hmp]
    rfl
  · simpa [quotientLawRaw] using hvalid.2.1
  · exact hvalid.2.2

/-- The exact population tuple admits a well-formed prescribed-grid comparator, retaining both
its factorization identities and all four frozen rounding estimates. -/
lemma population_structuredLatticeComparator_exists
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (P : MeasureTheory.Measure (FullData k dx dz)) [MeasureTheory.IsProbabilityMeasure P]
    (hk : 2 ≤ k) (hkx : k ≤ dx) (hL : 1 ≤ L) (hpi : 0 < pi0)
    (hsigma : 0 < sigma0)
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P) :
    ∃ (V : SignalBasis dx k) (R : RectMatrix k k) (p tau : Fin k → ℝ)
      (theta : StructuredLatticePoint k dx (effectRadius dz L sigma0)),
      theta.WellFormed (dz := dz) (n := n) (L := L) (pi0 := pi0) (sigma0 := sigma0) ∧
      (obsSummary P).mX = Matrix.mulVec (V.V * R.transpose) p ∧
      Matrix.mulVec (R * V.V.transpose) (firstBasis dx) = (fun _ => (1 : ℝ)) ∧
      AmbientOperatorBridge.ambientEffectOperator (obsSummary P) =
        V.V * R⁻¹ * Matrix.diagonal tau * R * V.V.transpose ∧
      sigma0 ≤ signalMinSingular R ∧
      ‖matrixCLM R‖ ≤ Real.sqrt k * L ∧
      (∀ u, 2 * pi0 ≤ p u) ∧ (∑ u, p u = 1) ∧
      (∀ u, tau u ∈ Set.Icc (-effectRadius dz L sigma0) (effectRadius dz L sigma0)) ∧
      ‖matrixCLM (theta.V - V.V)‖ ≤
        4 * Real.sqrt (dx * k) * latticeMesh k dx n pi0 sigma0 ∧
      ‖matrixCLM (theta.R - R)‖ ≤
        (k : ℝ) * latticeMesh k dx n pi0 sigma0 ∧
      Real.sqrt (∑ u, (theta.weight u - p u) ^ 2) ≤
        Real.sqrt k * latticeMesh k dx n pi0 sigma0 ∧
      ∀ u, |theta.effect u - tau u| ≤ latticeMesh k dx n pi0 sigma0 := by
  obtain ⟨V, R, p, tau, hm, hb, hD, hRmin, hRnorm, hp, hpSum, htau, _hlaw⟩ :=
    population_structured_tuple_exists P hk hkx hL hpi hsigma hM
  obtain ⟨theta, htheta, hV, hR, hweight, heffect⟩ :=
    structuredLatticeComparator_exists (n := n) hk hL hpi hsigma
      (by unfold effectRadius; positivity) V R p tau hRmin hRnorm hp hpSum htau
  exact ⟨V, R, p, tau, theta, htheta, hm, hb, hD, hRmin, hRnorm, hp, hpSum,
    htau, hV, hR, hweight, heffect⟩

noncomputable def populationOperatorCoefficient (L pi0 sigma0 : ℝ) : ℝ :=
  8 / (3 * (pi0 * sigma0 ^ 2)) + 32 * L / (pi0 * sigma0 ^ 2) ^ 2

noncomputable def structuredGridVConstant (k dx : ℕ) : ℝ :=
  4 * Real.sqrt (dx * k)

noncomputable def structuredGridMeanCoefficient (k dx : ℕ) (L : ℝ) : ℝ :=
  2 * Real.sqrt k * L * structuredGridVConstant k dx + k + k * L

noncomputable def structuredGridAnchorCoefficient (k dx : ℕ) (L : ℝ) : ℝ :=
  k + 2 * Real.sqrt k * L * structuredGridVConstant k dx

noncomputable def structuredGridOperatorCoefficient
    (k dx dz : ℕ) (L sigma0 : ℝ) : ℝ :=
  let Ltau := effectRadius dz L sigma0
  let KD := 4 * Real.sqrt k * L * Ltau / sigma0
  2 * KD * structuredGridVConstant k dx +
    4 * k * Real.sqrt k * L * Ltau / sigma0 ^ 2 +
    2 * Real.sqrt k * L / sigma0 + k * Ltau / sigma0

noncomputable def structuredGridCriterionCoefficient
    (k dx dz : ℕ) (L sigma0 : ℝ) : ℝ :=
  structuredGridOperatorCoefficient k dx dz L sigma0 +
    structuredGridMeanCoefficient k dx L + structuredGridAnchorCoefficient k dx L

/-- Model-specialized oracle inequality for the selected structured-lattice point, with the
population perturbation and grid approximation contributions kept additively separate. -/
lemma selected_structuredLatticeCriterion_model_le
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
    ∃ thetaHat : StructuredLatticePoint k dx (effectRadius dz L sigma0),
      thetaHat.WellFormed (dz := dz) (n := n) (L := L)
        (pi0 := pi0) (sigma0 := sigma0) ∧
      A.estimate sample = thetaHat.effectLaw ∧
      structuredLatticeCriterion (pi0 * sigma0 ^ 2 / 2) (empSummary sample) thetaHat ≤
        (populationOperatorCoefficient L pi0 sigma0 + 1) *
            dS (empSummary sample) (obsSummary P) +
          structuredGridCriterionCoefficient k dx dz L sigma0 *
            latticeMesh k dx n pi0 sigma0 := by
  let s := empSummary sample
  let p0 := obsSummary P
  let q := latticeMesh k dx n pi0 sigma0
  let e := dS s p0
  let cV := structuredGridVConstant k dx
  let Ltau := effectRadius dz L sigma0
  let KD := 4 * Real.sqrt k * L * Ltau / sigma0
  obtain ⟨V, R, p, tau, theta, htheta, hm0, hb0, hD0, hRmin, hRnorm,
      hp, hpSum, htau, hV, hR, hweight, heffect⟩ :=
    population_structuredLatticeComparator_exists (n := n) P hk hkx hL hpi hsigma hM
  let Vn : SignalBasis dx k := ⟨theta.V, htheta.2.2.1⟩
  have hq : 0 ≤ q := by dsimp [q, latticeMesh]; positivity
  have hp0 (u : Fin k) : 0 ≤ p u := by linarith [hp u]
  have hweight' : ‖(WithLp.toLp 2 (theta.weight - p) : Euc k)‖ ≤ Real.sqrt k * q := by
    rw [EuclideanSpace.norm_eq]
    simpa [q, Real.norm_eq_abs, sq_abs] using hweight
  have hRn : ‖matrixCLM theta.R‖ ≤ 2 * Real.sqrt k * L := htheta.2.2.2.2.2.1
  have hRnmin : sigma0 / 2 ≤ signalMinSingular theta.R := htheta.2.2.2.2.1
  have hmeanRound := rounded_mean_factorization_residual_le
    V Vn R theta.R p theta.weight hp0 hpSum theta.lawValid.1 theta.lawValid.2.1
    (by simpa [Vn, cV, structuredGridVConstant, q] using hV)
    (by simpa [q] using hR) hRn hRnorm hweight' (by linarith) hq
  have hmeanPop :
      ‖Matrix.toEuclideanLin (V.V * R.transpose) (WithLp.toLp 2 p) -
          WithLp.toLp 2 s.mX‖ ≤ e := by
    have heq : Matrix.toEuclideanLin (V.V * R.transpose) (WithLp.toLp 2 p) =
        WithLp.toLp 2 p0.mX := by
      apply PiLp.ext
      intro i
      simpa [Matrix.toEuclideanLin_apply, hm0, p0]
    rw [heq]
    have hb := AmbientOperatorBridge.norm_mX_sub_le_dS s p0
    calc
      ‖WithLp.toLp 2 p0.mX - WithLp.toLp 2 s.mX‖ =
          ‖WithLp.toLp 2 s.mX - WithLp.toLp 2 p0.mX‖ := norm_sub_rev _ _
      _ = ‖(WithLp.toLp 2 (s.mX - p0.mX) : Euc dx)‖ := by
        congr 1
      _ ≤ e := hb
  have hmeanRound' :
      ‖Matrix.toEuclideanLin (Vn.V * theta.R.transpose) (WithLp.toLp 2 theta.weight) -
          Matrix.toEuclideanLin (V.V * R.transpose) (WithLp.toLp 2 p)‖ ≤
        structuredGridMeanCoefficient k dx L * q := by
    simpa [structuredGridMeanCoefficient, structuredGridVConstant] using hmeanRound
  have hmeanVec :
      ‖Matrix.toEuclideanLin (Vn.V * theta.R.transpose) (WithLp.toLp 2 theta.weight) -
          WithLp.toLp 2 s.mX‖ ≤
        e + structuredGridMeanCoefficient k dx L * q := by
    have hdecomp :
        Matrix.toEuclideanLin (Vn.V * theta.R.transpose) (WithLp.toLp 2 theta.weight) -
            WithLp.toLp 2 s.mX =
          (Matrix.toEuclideanLin (Vn.V * theta.R.transpose) (WithLp.toLp 2 theta.weight) -
            Matrix.toEuclideanLin (V.V * R.transpose) (WithLp.toLp 2 p)) +
          (Matrix.toEuclideanLin (V.V * R.transpose) (WithLp.toLp 2 p) -
            WithLp.toLp 2 s.mX) := by abel
    rw [hdecomp]
    calc
      _ ≤ ‖Matrix.toEuclideanLin (Vn.V * theta.R.transpose) (WithLp.toLp 2 theta.weight) -
          Matrix.toEuclideanLin (V.V * R.transpose) (WithLp.toLp 2 p)‖ +
          ‖Matrix.toEuclideanLin (V.V * R.transpose) (WithLp.toLp 2 p) -
            WithLp.toLp 2 s.mX‖ := norm_add_le _ _
      _ ≤ structuredGridMeanCoefficient k dx L * q + e := add_le_add hmeanRound' hmeanPop
      _ = e + structuredGridMeanCoefficient k dx L * q := by ring
  have hmean : Real.sqrt (∑ i, ((∑ u, theta.V i u *
      (∑ v, theta.R v u * theta.weight v)) - s.mX i) ^ 2) ≤
      e + structuredGridMeanCoefficient k dx L * q := by
    have hmeanEq : ‖Matrix.toEuclideanLin (Vn.V * theta.R.transpose)
        (WithLp.toLp 2 theta.weight) - WithLp.toLp 2 s.mX‖ =
        Real.sqrt (∑ i, ((∑ u, theta.V i u *
          (∑ v, theta.R v u * theta.weight v)) - s.mX i) ^ 2) := by
      rw [EuclideanSpace.norm_eq]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      simp only [Real.norm_eq_abs, sq_abs]
      congr 1
      simp only [Matrix.toEuclideanLin_apply, PiLp.sub_apply]
      change ((Vn.V * theta.R.transpose).mulVec theta.weight) i - s.mX i = _
      rw [← Matrix.mulVec_mulVec]
      simp only [Vn, Matrix.transpose_apply, Matrix.mulVec, dotProduct]
    rw [← hmeanEq]
    exact hmeanVec
  have hanchorRound := rounded_anchor_factorization_residual_le (by omega)
    V Vn R theta.R (by simpa [Vn, cV, structuredGridVConstant, q] using hV)
    (by simpa [q] using hR) hRn (by linarith) hq
  have hanchor : Real.sqrt (∑ u, ((∑ v, theta.R u v *
      (∑ i, theta.V i v * firstBasis dx i)) - 1) ^ 2) ≤
      structuredGridAnchorCoefficient k dx L * q := by
    have hanchorEq : ‖Matrix.toEuclideanLin (theta.R * Vn.V.transpose)
        (WithLp.toLp 2 (firstBasis dx)) -
        Matrix.toEuclideanLin (R * V.V.transpose)
          (WithLp.toLp 2 (firstBasis dx))‖ =
        Real.sqrt (∑ u, ((∑ v, theta.R u v *
          (∑ i, theta.V i v * firstBasis dx i)) - 1) ^ 2) := by
      rw [EuclideanSpace.norm_eq]
      congr 1
      apply Finset.sum_congr rfl
      intro u _
      simp only [Real.norm_eq_abs, sq_abs]
      congr 1
      simp only [Matrix.toEuclideanLin_apply, PiLp.sub_apply]
      rw [show (Matrix.mulVec (R * V.V.transpose) (firstBasis dx)) u = 1 by
        simpa using congrFun hb0 u]
      rw [← Matrix.mulVec_mulVec]
      simp [Vn, Matrix.mulVec, dotProduct, Finset.mul_sum]
    rw [← hanchorEq]
    simpa [structuredGridAnchorCoefficient, structuredGridVConstant] using hanchorRound
  have hDround := rounded_operator_factorization_residual_le_of_signalMinSingular
    V Vn R theta.R tau theta.effect
    (by simpa [Vn, cV, structuredGridVConstant, q] using hV)
    (by simpa [q] using hR) hRn hRnorm hRmin hRnmin
    (fun u => (abs_le.mpr (htau u)))
    (fun u => abs_le.mpr (theta.lawValid.2.2 u))
    heffect (by linarith) (by unfold effectRadius; positivity) hsigma hq
    (by positivity) rfl
  have hDemp := empiricalCompressedOperator_model_norm_le P s hk hkx hkz hL hpi hpiMax
    hsigma hsigmaMax hM (by simpa [s, p0] using hsmall)
  have hD : ‖matrixCLM (structuredCandidateOperator theta -
      empiricalCompressedOperator (pi0 * sigma0 ^ 2 / 2) s)‖ ≤
      populationOperatorCoefficient L pi0 sigma0 * e +
        structuredGridOperatorCoefficient k dx dz L sigma0 * q := by
    have hsplit : structuredCandidateOperator theta -
        empiricalCompressedOperator (pi0 * sigma0 ^ 2 / 2) s =
        (structuredCandidateOperator theta - AmbientOperatorBridge.ambientEffectOperator p0) +
        (AmbientOperatorBridge.ambientEffectOperator p0 -
          empiricalCompressedOperator (pi0 * sigma0 ^ 2 / 2) s) := by abel
    rw [hsplit]
    calc
      _ ≤ ‖matrixCLM (structuredCandidateOperator theta -
          AmbientOperatorBridge.ambientEffectOperator p0)‖ +
          ‖matrixCLM (AmbientOperatorBridge.ambientEffectOperator p0 -
            empiricalCompressedOperator (pi0 * sigma0 ^ 2 / 2) s)‖ := by
            simpa only [matrixCLM, map_add] using norm_add_le
              (matrixCLM (structuredCandidateOperator theta -
                AmbientOperatorBridge.ambientEffectOperator p0))
              (matrixCLM (AmbientOperatorBridge.ambientEffectOperator p0 -
                empiricalCompressedOperator (pi0 * sigma0 ^ 2 / 2) s))
      _ ≤ structuredGridOperatorCoefficient k dx dz L sigma0 * q +
          populationOperatorCoefficient L pi0 sigma0 * e := by
        apply add_le_add
        · simpa [structuredCandidateOperator, Vn, hD0, p0, cV, q, Ltau, KD,
            structuredGridOperatorCoefficient, structuredGridVConstant] using hDround
        · have hrev : ‖matrixCLM (AmbientOperatorBridge.ambientEffectOperator p0 -
              empiricalCompressedOperator (pi0 * sigma0 ^ 2 / 2) s)‖ =
              ‖matrixCLM (empiricalCompressedOperator (pi0 * sigma0 ^ 2 / 2) s -
                AmbientOperatorBridge.ambientEffectOperator p0)‖ := by
              change ‖AmbientOperatorBridge.ambientEffectOperator p0 -
                empiricalCompressedOperator (pi0 * sigma0 ^ 2 / 2) s‖ = _
              exact norm_sub_rev _ _
          rw [hrev]
          simpa [populationOperatorCoefficient, s, p0, e] using hDemp
      _ = _ := by ring
  obtain ⟨thetaHat, hthetaHat, hestimate, hmin⟩ :=
    isPrescribedStructuredLattice_selected_criterion_le A hA sample theta htheta
  refine ⟨thetaHat, hthetaHat, hestimate, hmin.trans ?_⟩
  unfold structuredLatticeCriterion
  change _ ≤ _
  simp only [s, p0, e, q] at hD hmean hanchor ⊢
  unfold structuredGridCriterionCoefficient
  linarith

/-- The single frozen path coefficient used to dominate all three selected population
residuals after adding the empirical-to-population bridge. -/
noncomputable def structuredLatticePathCoefficient
    (k dx dz : ℕ) (L pi0 sigma0 : ℝ) : ℝ :=
  2 * (populationOperatorCoefficient L pi0 sigma0 + 1) +
    structuredGridCriterionCoefficient k dx dz L sigma0

/-- The selected grid point obeys the common paper-local path envelope against the population
operator, population mean, and exact population anchor. -/
lemma selected_structuredLattice_population_residuals_le
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
    ∃ thetaHat : StructuredLatticePoint k dx (effectRadius dz L sigma0),
      thetaHat.WellFormed (dz := dz) (n := n) (L := L)
        (pi0 := pi0) (sigma0 := sigma0) ∧
      A.estimate sample = thetaHat.effectLaw ∧
      ‖matrixCLM (structuredCandidateOperator thetaHat -
        AmbientOperatorBridge.ambientEffectOperator (obsSummary P))‖ ≤
          structuredLatticePathCoefficient k dx dz L pi0 sigma0 *
            (dS (empSummary sample) (obsSummary P) + latticeMesh k dx n pi0 sigma0) ∧
      Real.sqrt (∑ i, ((∑ u, thetaHat.V i u *
        (∑ v, thetaHat.R v u * thetaHat.weight v)) - (obsSummary P).mX i) ^ 2) ≤
          structuredLatticePathCoefficient k dx dz L pi0 sigma0 *
            (dS (empSummary sample) (obsSummary P) + latticeMesh k dx n pi0 sigma0) ∧
      Real.sqrt (∑ u, ((∑ v, thetaHat.R u v *
        (∑ i, thetaHat.V i v * firstBasis dx i)) - 1) ^ 2) ≤
          structuredLatticePathCoefficient k dx dz L pi0 sigma0 *
            (dS (empSummary sample) (obsSummary P) + latticeMesh k dx n pi0 sigma0) := by
  let s := empSummary sample
  let p0 := obsSummary P
  let e := dS s p0
  let q := latticeMesh k dx n pi0 sigma0
  let AD := populationOperatorCoefficient L pi0 sigma0
  let cg := structuredGridCriterionCoefficient k dx dz L sigma0
  let B := structuredLatticePathCoefficient k dx dz L pi0 sigma0
  obtain ⟨thetaHat, htheta, hestimate, hcrit⟩ :=
    selected_structuredLatticeCriterion_model_le P A hA sample hk hkx hkz hL hpi
      hpiMax hsigma hsigmaMax hM hsmall
  have hAD0 : 0 ≤ AD := by
    dsimp [AD, populationOperatorCoefficient]
    positivity
  have hcg0 : 0 ≤ cg := by
    dsimp [cg, structuredGridCriterionCoefficient, structuredGridOperatorCoefficient,
      structuredGridMeanCoefficient, structuredGridAnchorCoefficient,
      structuredGridVConstant]
    unfold effectRadius
    positivity
  have hB : B = 2 * (AD + 1) + cg := rfl
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have he0 : 0 ≤ e := by dsimp [e]; unfold dS; positivity
  have hq0 : 0 ≤ q := by dsimp [q, latticeMesh]; positivity
  have hcrit' : structuredLatticeCriterion (pi0 * sigma0 ^ 2 / 2) s thetaHat ≤
      (AD + 1) * e + cg * q := by simpa [s, p0, e, q, AD, cg] using hcrit
  have hopEmp := structuredLatticeCriterion_operator_le
    (tau := pi0 * sigma0 ^ 2 / 2) s thetaHat
  have hmEmp := structuredLatticeCriterion_mean_le
    (tau := pi0 * sigma0 ^ 2 / 2) s thetaHat
  have hb := structuredLatticeCriterion_anchor_le
    (tau := pi0 * sigma0 ^ 2 / 2) s thetaHat
  have hDemp := empiricalCompressedOperator_model_norm_le P s hk hkx hkz hL hpi hpiMax
    hsigma hsigmaMax hM (by simpa [s, p0] using hsmall)
  have hDemp' : ‖matrixCLM (empiricalCompressedOperator (pi0 * sigma0 ^ 2 / 2) s -
      AmbientOperatorBridge.ambientEffectOperator p0)‖ ≤ AD * e := by
    simpa [AD, e, s, p0, populationOperatorCoefficient] using hDemp
  have hopRaw : ‖matrixCLM (structuredCandidateOperator thetaHat -
      AmbientOperatorBridge.ambientEffectOperator p0)‖ ≤
      (2 * AD + 1) * e + cg * q := by
    have hsplit : structuredCandidateOperator thetaHat -
        AmbientOperatorBridge.ambientEffectOperator p0 =
      (structuredCandidateOperator thetaHat -
        empiricalCompressedOperator (pi0 * sigma0 ^ 2 / 2) s) +
      (empiricalCompressedOperator (pi0 * sigma0 ^ 2 / 2) s -
        AmbientOperatorBridge.ambientEffectOperator p0) := by abel
    rw [hsplit]
    calc
      _ ≤ ‖matrixCLM (structuredCandidateOperator thetaHat -
          empiricalCompressedOperator (pi0 * sigma0 ^ 2 / 2) s)‖ +
          ‖matrixCLM (empiricalCompressedOperator (pi0 * sigma0 ^ 2 / 2) s -
            AmbientOperatorBridge.ambientEffectOperator p0)‖ := by
          simpa only [matrixCLM, map_add] using norm_add_le
            (matrixCLM (structuredCandidateOperator thetaHat -
              empiricalCompressedOperator (pi0 * sigma0 ^ 2 / 2) s))
            (matrixCLM (empiricalCompressedOperator (pi0 * sigma0 ^ 2 / 2) s -
              AmbientOperatorBridge.ambientEffectOperator p0))
      _ ≤ ((AD + 1) * e + cg * q) + AD * e :=
        add_le_add (hopEmp.trans hcrit') hDemp'
      _ = (2 * AD + 1) * e + cg * q := by ring
  have hmBlock := AmbientOperatorBridge.norm_mX_sub_le_dS s p0
  have hmRaw : Real.sqrt (∑ i, ((∑ u, thetaHat.V i u *
      (∑ v, thetaHat.R v u * thetaHat.weight v)) - p0.mX i) ^ 2) ≤
      (AD + 2) * e + cg * q := by
    let mhat : Fin dx → ℝ := fun i => ∑ u, thetaHat.V i u *
      (∑ v, thetaHat.R v u * thetaHat.weight v)
    have hmEmpVec : ‖(WithLp.toLp 2 (mhat - s.mX) : Euc dx)‖ ≤
        (AD + 1) * e + cg * q := by
      rw [EuclideanSpace.norm_eq]
      simpa [mhat, Real.norm_eq_abs, sq_abs] using hmEmp.trans hcrit'
    have hmBlock' : ‖(WithLp.toLp 2 (s.mX - p0.mX) : Euc dx)‖ ≤ e := hmBlock
    have hdecomp : (WithLp.toLp 2 (mhat - p0.mX) : Euc dx) =
        WithLp.toLp 2 (mhat - s.mX) + WithLp.toLp 2 (s.mX - p0.mX) := by
      apply PiLp.ext
      intro i
      simp
    have hmEq : ‖(WithLp.toLp 2 (mhat - p0.mX) : Euc dx)‖ =
        Real.sqrt (∑ i, ((∑ u, thetaHat.V i u *
          (∑ v, thetaHat.R v u * thetaHat.weight v)) - p0.mX i) ^ 2) := by
      rw [EuclideanSpace.norm_eq]
      simp [mhat, Real.norm_eq_abs, sq_abs]
    rw [← hmEq]
    rw [hdecomp]
    exact (norm_add_le _ _).trans <| by
      calc
        _ ≤ ((AD + 1) * e + cg * q) + e := add_le_add hmEmpVec hmBlock'
        _ = (AD + 2) * e + cg * q := by ring
  have hAD2B : AD + 2 ≤ B := by rw [hB]; linarith
  have h2AD1B : 2 * AD + 1 ≤ B := by rw [hB]; linarith
  have hcgB : cg ≤ B := by rw [hB]; linarith
  have hopenv : (2 * AD + 1) * e + cg * q ≤ B * (e + q) := by
    calc
      _ ≤ B * e + B * q := add_le_add
        (mul_le_mul_of_nonneg_right h2AD1B he0)
        (mul_le_mul_of_nonneg_right hcgB hq0)
      _ = _ := by ring
  have hmenv : (AD + 2) * e + cg * q ≤ B * (e + q) := by
    calc
      _ ≤ B * e + B * q := add_le_add
        (mul_le_mul_of_nonneg_right hAD2B he0)
        (mul_le_mul_of_nonneg_right hcgB hq0)
      _ = _ := by ring
  have hbenv : (AD + 1) * e + cg * q ≤ B * (e + q) := by
    have hADB : AD + 1 ≤ B := by rw [hB]; linarith
    calc
      _ ≤ B * e + B * q := add_le_add
        (mul_le_mul_of_nonneg_right hADB he0)
        (mul_le_mul_of_nonneg_right hcgB hq0)
      _ = _ := by ring
  refine ⟨thetaHat, htheta, hestimate, ?_, ?_, ?_⟩
  · simpa [B, e, q, s, p0] using hopRaw.trans hopenv
  · simpa [B, e, q, s, p0] using hmRaw.trans hmenv
  · simpa [B, e, q, s, p0] using hb.trans (hcrit'.trans hbenv)

-- keep: reusable population mean-residual adapter for alternate structured comparators
/-- The population mean factorization leaves only the mean block of the summary distance. -/
lemma population_mean_residual_le_dS
    {k dx dz : ℕ} (s s0 : SummarySpace dx dz)
    (V : SignalBasis dx k) (R : RectMatrix k k) (p : Fin k → ℝ)
    (hm : s0.mX = Matrix.mulVec (V.V * R.transpose) p) :
    ‖Matrix.toEuclideanLin (V.V * R.transpose) (WithLp.toLp 2 p) -
        WithLp.toLp 2 s.mX‖ ≤ dS s s0 := by
  have hblock := AmbientOperatorBridge.norm_mX_sub_le_dS s s0
  have heq : Matrix.toEuclideanLin (V.V * R.transpose) (WithLp.toLp 2 p) =
      WithLp.toLp 2 s0.mX := by
    apply PiLp.ext
    intro i
    simpa [Matrix.toEuclideanLin_apply, hm]
  rw [heq]
  calc
    ‖WithLp.toLp 2 s0.mX - WithLp.toLp 2 s.mX‖ =
        ‖WithLp.toLp 2 s.mX - WithLp.toLp 2 s0.mX‖ := norm_sub_rev _ _
    _ ≤ dS s s0 := hblock

-- keep: reusable exact-anchor-to-zero-residual adapter for structured lattice comparators
/-- Criterion-coordinate form of the exact population anchor residual. -/
lemma population_anchor_residual_eq_zero
    {k dx : ℕ} (V : SignalBasis dx k) (R : RectMatrix k k)
    (hanchor : Matrix.mulVec (R * V.V.transpose) (firstBasis dx) =
      (fun _ => (1 : ℝ))) :
    Real.sqrt (∑ u, ((∑ v, R u v * (∑ i, V.V i v * firstBasis dx i)) - 1) ^ 2) = 0 := by
  have hu (u : Fin k) :
      (∑ v, R u v * (∑ i, V.V i v * firstBasis dx i)) = 1 := by
    have := congrFun hanchor u
    change (R.mulVec (V.V.transpose.mulVec (firstBasis dx))) u = 1
    simpa only [Matrix.mulVec_mulVec] using this
  simp_rw [hu, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  simp

end

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
