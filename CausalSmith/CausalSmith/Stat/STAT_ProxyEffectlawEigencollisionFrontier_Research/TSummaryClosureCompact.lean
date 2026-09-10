import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.SummaryClosure
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.TObservedVMWMarginInclusion
import Mathlib.Topology.Compactness.Compact

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open Set

/-- Every matrix entry is bounded by the Euclidean operator norm. -/
-- @node: matrixEntry_abs_le_operatorNorm
lemma matrixEntry_abs_le_operatorNorm {rows cols : ℕ} (A : RectMatrix rows cols)
    (i : Fin rows) (j : Fin cols) : |A i j| ≤ ‖matrixCLM A‖ := by
  let x : Euc cols := EuclideanSpace.single j 1
  calc
    |A i j| = ‖(matrixCLM A x) i‖ := by
      simp [x, matrixCLM, Matrix.toEuclideanLin_apply, Real.norm_eq_abs]
    _ ≤ ‖matrixCLM A x‖ := PiLp.norm_apply_le _ _
    _ ≤ ‖matrixCLM A‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖matrixCLM A‖ := by simp [x]

/-- The entrywise closed cube of rectangular matrices. -/
-- @node: summaryMatrixBox
def summaryMatrixBox (rows cols : ℕ) (L : ℝ) : Set (RectMatrix rows cols) :=
  {A | ∀ i j, A i j ∈ Icc (-L) L}

/-- The entrywise matrix cube is compact in the finite product topology. -/
-- @node: summaryMatrixBox_compact
lemma summaryMatrixBox_compact (rows cols : ℕ) (L : ℝ) :
    IsCompact (summaryMatrixBox rows cols L) := by
  exact isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => isCompact_Icc

/-- The coordinatewise closed cube for the unconditional proxy mean. -/
-- @node: summaryVectorBox
def summaryVectorBox (d : ℕ) (L : ℝ) : Set (Fin d → ℝ) :=
  {x | ∀ i, x i ∈ Icc (-L) L}

/-- The proxy-mean cube is compact in the finite product topology. -/
-- @node: summaryVectorBox_compact
lemma summaryVectorBox_compact (d : ℕ) (L : ℝ) :
    IsCompact (summaryVectorBox d L) := by
  exact isCompact_pi_infinite fun _ => isCompact_Icc

/-- Product cube containing every admissible five-block summary. -/
-- @node: summaryCoordinateBox
def summaryCoordinateBox (dx dz : ℕ) (L : ℝ) : Set (SummaryCoordinates dx dz) :=
  summaryMatrixBox dz dx L ×ˢ summaryMatrixBox dz dx L ×ˢ
    summaryMatrixBox dz dx L ×ˢ summaryMatrixBox dz dx L ×ˢ summaryVectorBox dx L

/-- The five-block coordinate cube is compact. -/
-- @node: summaryCoordinateBox_compact
lemma summaryCoordinateBox_compact (dx dz : ℕ) (L : ℝ) :
    IsCompact (summaryCoordinateBox dx dz L) := by
  exact (summaryMatrixBox_compact dz dx L).prod ((summaryMatrixBox_compact dz dx L).prod
    ((summaryMatrixBox_compact dz dx L).prod ((summaryMatrixBox_compact dz dx L).prod
      (summaryVectorBox_compact dx L))))

/-- The summary record is topologically identical to its five-coordinate product. -/
-- @node: summarySpaceEquivCoordinates
def summarySpaceEquivCoordinates (dx dz : ℕ) :
    SummarySpace dx dz ≃ SummaryCoordinates dx dz where
  toFun := SummarySpace.toCoordinates
  invFun := fun c => ⟨c.1, c.2.1, c.2.2.1, c.2.2.2.1, c.2.2.2.2⟩
  left_inv := by rintro ⟨M0, M1, N0, N1, mX⟩; rfl
  right_inv := by rintro ⟨M0, M1, N0, N1, mX⟩; rfl

/-- The coordinate equivalence respects the induced summary topology. -/
-- @node: summarySpaceHomeomorphCoordinates
def summarySpaceHomeomorphCoordinates (dx dz : ℕ) :
    SummarySpace dx dz ≃ₜ SummaryCoordinates dx dz where
  toEquiv := summarySpaceEquivCoordinates dx dz
  continuous_toFun := continuous_induced_dom
  continuous_invFun := by
    rw [continuous_induced_rng]
    change Continuous fun x : SummaryCoordinates dx dz => x
    exact continuous_id

/-- The summary-space cube corresponding to the coordinate product cube. -/
-- @node: summarySpaceBox
def summarySpaceBox (dx dz : ℕ) (L : ℝ) : Set (SummarySpace dx dz) :=
  SummarySpace.toCoordinates ⁻¹' summaryCoordinateBox dx dz L

/-- The summary-space cube is compact. -/
-- @node: summarySpaceBox_compact
lemma summarySpaceBox_compact (dx dz : ℕ) (L : ℝ) :
    IsCompact (summarySpaceBox dx dz L) := by
  let e := summarySpaceHomeomorphCoordinates dx dz
  have heq : summarySpaceBox dx dz L = e.symm '' summaryCoordinateBox dx dz L := by
    ext s
    constructor
    · intro hs
      exact ⟨e s, hs, e.symm_apply_apply s⟩
    · rintro ⟨q, hq, rfl⟩
      change e (e.symm q) ∈ summaryCoordinateBox dx dz L
      simpa using hq
  rw [heq]
  exact (summaryCoordinateBox_compact dx dz L).image e.symm.continuous

/-- Observable block envelopes place the admissible image in the finite coordinate cube. -/
-- @node: admissibleImage_subset_summarySpaceBox
lemma admissibleImage_subset_summarySpaceBox (k dx dz : ℕ) (L pi0 sigma0 : ℝ)
    (hk : 2 ≤ k) (hkx : k ≤ dx) (hkz : k ≤ dz) (hL : 1 ≤ L)
    (hpi : 0 < pi0) (hpiMax : pi0 ≤ 1 / (2 * k : ℝ))
    (hsigma : 0 < sigma0) (hsigmaMax : sigma0 ≤ 1) :
    admissibleImage k dx dz L pi0 sigma0 ⊆ summarySpaceBox dx dz L := by
  intro s hs
  rcases hs with ⟨Q, rfl⟩
  letI := Q.prob
  have h := observed_summary_block_bounds Q.P hk hkx hkz hL hpi hpiMax hsigma hsigmaMax
    Q.model
  change SummarySpace.toCoordinates Q.summary ∈ summaryCoordinateBox dx dz L
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    exact abs_le.mp ((matrixEntry_abs_le_operatorNorm Q.summary.M0 i j).trans (by
      simpa [ModelLaw.summary] using h.1))
  · intro i j
    exact abs_le.mp ((matrixEntry_abs_le_operatorNorm Q.summary.M1 i j).trans (by
      simpa [ModelLaw.summary] using h.2.1))
  · intro i j
    exact abs_le.mp ((matrixEntry_abs_le_operatorNorm Q.summary.N0 i j).trans (by
      simpa [ModelLaw.summary] using h.2.2.1))
  · intro i j
    exact abs_le.mp ((matrixEntry_abs_le_operatorNorm Q.summary.N1 i j).trans (by
      simpa [ModelLaw.summary] using h.2.2.2.1))
  · intro i
    have hi : |Q.summary.mX i| ≤ ‖Q.summary.mX‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm Q.summary.mX i
    exact abs_le.mp (hi.trans (by simpa [ModelLaw.summary] using h.2.2.2.2))

/-- The closure of an admissible image contained in the summary cube is compact. -/
-- @node: summaryClosure_compact_of_block_bounds
lemma summaryClosure_compact_of_block_bounds (k dx dz : ℕ) (L pi0 sigma0 : ℝ)
    (hsub : admissibleImage k dx dz L pi0 sigma0 ⊆ summarySpaceBox dx dz L) :
    IsCompact (summaryClosure k dx dz L pi0 sigma0) := by
  have hK := summarySpaceBox_compact dx dz L
  apply hK.of_isClosed_subset isClosed_closure
  exact closure_minimal hsub
    ((summaryCoordinateBox_compact dx dz L).isClosed.preimage continuous_induced_dom)

/-- Observable block bounds give a uniform bound for the continuous summary loss. -/
-- @node: admissibleImage_dS_bounded
lemma admissibleImage_dS_bounded (k dx dz : ℕ) (L pi0 sigma0 : ℝ)
    (hk : 2 ≤ k) (hkx : k ≤ dx) (hkz : k ≤ dz) (hL : 1 ≤ L)
    (hpi : 0 < pi0) (hpiMax : pi0 ≤ 1 / (2 * k : ℝ))
    (hsigma : 0 < sigma0) (hsigmaMax : sigma0 ≤ 1) :
    ∃ B : ℝ, ∀ s ∈ admissibleImage k dx dz L pi0 sigma0, dS s 0 ≤ B := by
  refine ⟨(4 + dx) * L, ?_⟩
  intro s hs
  rcases hs with ⟨Q, rfl⟩
  letI := Q.prob
  have h := observed_summary_block_bounds Q.P hk hkx hkz hL hpi hpiMax hsigma hsigmaMax
    Q.model
  let x : Euc dx := WithLp.toLp 2 Q.summary.mX
  have hx : x = ∑ i, EuclideanSpace.single i (Q.summary.mX i) := by
    ext i
    simp [x]
  have hm : Real.sqrt (∑ i, Q.summary.mX i ^ 2) ≤ dx * L := by
    calc
      Real.sqrt (∑ i, Q.summary.mX i ^ 2) = ‖x‖ := by
        rw [EuclideanSpace.norm_eq]
        simp [x, Real.norm_eq_abs, sq_abs]
      _ = ‖∑ i, EuclideanSpace.single i (Q.summary.mX i)‖ := by rw [← hx]
      _ ≤ ∑ i, ‖EuclideanSpace.single i (Q.summary.mX i)‖ := norm_sum_le _ _
      _ = ∑ i, |Q.summary.mX i| := by simp [Real.norm_eq_abs]
      _ ≤ ∑ _i : Fin dx, L := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : |Q.summary.mX i| ≤ ‖Q.summary.mX‖ := by
          simpa [Real.norm_eq_abs] using norm_le_pi_norm Q.summary.mX i
        exact hi'.trans (by simpa [ModelLaw.summary] using h.2.2.2.2)
      _ = dx * L := by simp
  change dS Q.summary (⟨0, 0, 0, 0, 0⟩ : SummarySpace dx dz) ≤ (4 + dx) * L
  simp only [dS, Pi.zero_apply, sub_zero]
  have h' : ‖matrixCLM Q.summary.M0‖ ≤ L ∧ ‖matrixCLM Q.summary.M1‖ ≤ L ∧
      ‖matrixCLM Q.summary.N0‖ ≤ L ∧ ‖matrixCLM Q.summary.N1‖ ≤ L ∧
      ‖Q.summary.mX‖ ≤ L := by
    simpa [ModelLaw.summary] using h
  nlinarith [h'.1, h'.2.1, h'.2.2.1, h'.2.2.2.1, hm]

/-- The admissible image is uniformly `dS`-bounded, its closure is compact, and closure
nonemptiness is equivalent to model nonemptiness. -/
-- @node: prop:summary-closure-compact
theorem summary_closure_compact (k dx dz : ℕ) (L pi0 sigma0 : ℝ)
    (hk : 2 ≤ k) (hkx : k ≤ dx) (hkz : k ≤ dz) (hL : 1 ≤ L)
    (hpi : 0 < pi0) (hpiMax : pi0 ≤ 1 / (2 * k : ℝ))
    (hsigma : 0 < sigma0) (hsigmaMax : sigma0 ≤ 1) :
    (∃ B : ℝ, ∀ s ∈ admissibleImage k dx dz L pi0 sigma0, dS s 0 ≤ B) ∧
    IsCompact (summaryClosure k dx dz L pi0 sigma0) ∧
    ((summaryClosure k dx dz L pi0 sigma0).Nonempty ↔
      Nonempty (ModelLaw k dx dz L pi0 sigma0)) := by
  have hsub := admissibleImage_subset_summarySpaceBox k dx dz L pi0 sigma0 hk hkx hkz hL
    hpi hpiMax hsigma hsigmaMax
  refine ⟨admissibleImage_dS_bounded k dx dz L pi0 sigma0 hk hkx hkz hL hpi hpiMax
      hsigma hsigmaMax,
    summaryClosure_compact_of_block_bounds k dx dz L pi0 sigma0 hsub, ?_⟩
  rw [summaryClosure, closure_nonempty_iff]
  constructor
  · rintro ⟨s, Q, hQs⟩
    exact ⟨Q⟩
  · rintro ⟨Q⟩
    exact ⟨Q.summary, Q, rfl⟩


end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
