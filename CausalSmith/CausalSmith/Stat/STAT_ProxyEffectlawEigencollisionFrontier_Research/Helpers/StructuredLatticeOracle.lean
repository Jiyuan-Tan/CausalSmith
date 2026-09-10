import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.StructuredLatticeCardinality
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.QuotientLaw

/-! # Deterministic oracle interfaces for the structured lattice -/

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open MeasureTheory

noncomputable section

/-- Exhaustive minimization compares the selected point with every well-formed lattice point,
including points represented by a different harmless grid-basis witness. -/
lemma isPrescribedStructuredLattice_selected_criterion_le
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (A : LatticeEstimator k dx dz n (effectRadius dz L sigma0))
    (hA : IsPrescribedStructuredLattice (L := L) (pi0 := pi0) (sigma0 := sigma0) A)
    (sample : Fin n → Obs dx dz)
    (theta : StructuredLatticePoint k dx (effectRadius dz L sigma0))
    (htheta : theta.WellFormed (dz := dz) (n := n) (L := L)
      (pi0 := pi0) (sigma0 := sigma0)) :
    ∃ thetaHat : StructuredLatticePoint k dx (effectRadius dz L sigma0),
      thetaHat.WellFormed (dz := dz) (n := n) (L := L)
        (pi0 := pi0) (sigma0 := sigma0) ∧
      A.estimate sample = thetaHat.effectLaw ∧
      structuredLatticeCriterion (pi0 * sigma0 ^ 2 / 2) (empSummary sample) thetaHat ≤
        structuredLatticeCriterion (pi0 * sigma0 ^ 2 / 2) (empSummary sample) theta := by
  obtain ⟨candidate, first, hwf, hcomplete, _hinj, _horder, hmin, _htie,
    hestimate⟩ := hA
  obtain ⟨i, hV, hR, hweight, heffect⟩ := hcomplete theta htheta
  refine ⟨candidate (first sample), hwf _, ?_, ?_⟩
  · rw [hestimate]
  · calc
      structuredLatticeCriterion (pi0 * sigma0 ^ 2 / 2) (empSummary sample)
          (candidate (first sample)) ≤
          structuredLatticeCriterion (pi0 * sigma0 ^ 2 / 2) (empSummary sample)
            (candidate i) := hmin sample i
      _ = structuredLatticeCriterion (pi0 * sigma0 ^ 2 / 2) (empSummary sample)
          theta := by
        simp only [structuredLatticeCriterion, structuredCandidateOperator]
        rw [hV, hR, hweight, heffect]

/-- The three coordinate/operator residual estimates combine to the displayed grid criterion
constant, with no hidden multiplicative loss. -/
lemma structuredLatticeCriterion_le_of_residuals
    {k dx dz : ℕ} {radius tau q cD cm cb : ℝ}
    (s : SummarySpace dx dz) (theta : StructuredLatticePoint k dx radius)
    (hD : ‖matrixCLM (structuredCandidateOperator theta -
      empiricalCompressedOperator tau s)‖ ≤ cD * q)
    (hm : Real.sqrt (∑ i, ((∑ u, theta.V i u *
      (∑ v, theta.R v u * theta.weight v)) - s.mX i) ^ 2) ≤ cm * q)
    (hb : Real.sqrt (∑ u, ((∑ v, theta.R u v *
      (∑ i, theta.V i v * firstBasis dx i)) - 1) ^ 2) ≤ cb * q) :
    structuredLatticeCriterion tau s theta ≤ (cD + cm + cb) * q := by
  unfold structuredLatticeCriterion
  linarith

/-- Each of the three nonnegative residuals is bounded by the full criterion. -/
lemma structuredLatticeCriterion_operator_le
    {k dx dz : ℕ} {radius tau : ℝ} (s : SummarySpace dx dz)
    (theta : StructuredLatticePoint k dx radius) :
    ‖matrixCLM (structuredCandidateOperator theta - empiricalCompressedOperator tau s)‖ ≤
      structuredLatticeCriterion tau s theta := by
  unfold structuredLatticeCriterion
  have hm : 0 ≤ Real.sqrt (∑ i, ((∑ u, theta.V i u *
      (∑ v, theta.R v u * theta.weight v)) - s.mX i) ^ 2) := Real.sqrt_nonneg _
  have hb : 0 ≤ Real.sqrt (∑ u, ((∑ v, theta.R u v *
      (∑ i, theta.V i v * firstBasis dx i)) - 1) ^ 2) := Real.sqrt_nonneg _
  linarith

lemma structuredLatticeCriterion_mean_le
    {k dx dz : ℕ} {radius tau : ℝ} (s : SummarySpace dx dz)
    (theta : StructuredLatticePoint k dx radius) :
    Real.sqrt (∑ i, ((∑ u, theta.V i u *
      (∑ v, theta.R v u * theta.weight v)) - s.mX i) ^ 2) ≤
      structuredLatticeCriterion tau s theta := by
  unfold structuredLatticeCriterion
  have hop : 0 ≤ ‖matrixCLM
      (structuredCandidateOperator theta - empiricalCompressedOperator tau s)‖ := norm_nonneg _
  have hb : 0 ≤ Real.sqrt (∑ u, ((∑ v, theta.R u v *
      (∑ i, theta.V i v * firstBasis dx i)) - 1) ^ 2) := Real.sqrt_nonneg _
  linarith

lemma structuredLatticeCriterion_anchor_le
    {k dx dz : ℕ} {radius tau : ℝ} (s : SummarySpace dx dz)
    (theta : StructuredLatticePoint k dx radius) :
    Real.sqrt (∑ u, ((∑ v, theta.R u v *
      (∑ i, theta.V i v * firstBasis dx i)) - 1) ^ 2) ≤
      structuredLatticeCriterion tau s theta := by
  unfold structuredLatticeCriterion
  have hop : 0 ≤ ‖matrixCLM
      (structuredCandidateOperator theta - empiricalCompressedOperator tau s)‖ := norm_nonneg _
  have hm : 0 ≤ Real.sqrt (∑ i, ((∑ u, theta.V i u *
      (∑ v, theta.R v u * theta.weight v)) - s.mX i) ^ 2) := Real.sqrt_nonneg _
  linarith

-- keep: reusable oracle transfer from comparator residuals to exhaustive lattice selection
/-- Once a rounded well-formed comparator has the three frozen residual bounds at the empirical
summary, exhaustive minimization transfers their exact `c_grid` sum to the selected point. -/
lemma isPrescribedStructuredLattice_selected_criterion_le_grid
    {k dx dz n : ℕ} {L pi0 sigma0 cD cm cb q : ℝ}
    (A : LatticeEstimator k dx dz n (effectRadius dz L sigma0))
    (hA : IsPrescribedStructuredLattice (L := L) (pi0 := pi0) (sigma0 := sigma0) A)
    (sample : Fin n → Obs dx dz)
    (theta : StructuredLatticePoint k dx (effectRadius dz L sigma0))
    (htheta : theta.WellFormed (dz := dz) (n := n) (L := L)
      (pi0 := pi0) (sigma0 := sigma0))
    (hD : ‖matrixCLM (structuredCandidateOperator theta -
      empiricalCompressedOperator (pi0 * sigma0 ^ 2 / 2) (empSummary sample))‖ ≤ cD * q)
    (hm : Real.sqrt (∑ i, ((∑ u, theta.V i u *
      (∑ v, theta.R v u * theta.weight v)) - (empSummary sample).mX i) ^ 2) ≤ cm * q)
    (hb : Real.sqrt (∑ u, ((∑ v, theta.R u v *
      (∑ i, theta.V i v * firstBasis dx i)) - 1) ^ 2) ≤ cb * q) :
    ∃ thetaHat : StructuredLatticePoint k dx (effectRadius dz L sigma0),
      thetaHat.WellFormed (dz := dz) (n := n) (L := L)
        (pi0 := pi0) (sigma0 := sigma0) ∧
      A.estimate sample = thetaHat.effectLaw ∧
      structuredLatticeCriterion (pi0 * sigma0 ^ 2 / 2) (empSummary sample) thetaHat ≤
        (cD + cm + cb) * q := by
  obtain ⟨thetaHat, hthetaHat, hestimate, hmin⟩ :=
    isPrescribedStructuredLattice_selected_criterion_le A hA sample theta htheta
  refine ⟨thetaHat, hthetaHat, hestimate, hmin.trans ?_⟩
  exact structuredLatticeCriterion_le_of_residuals (empSummary sample) theta hD hm hb

/-- The mesh is no larger than the nominal root-`n` scale. -/
lemma latticeMesh_le_sqrt_inv (k dx n : ℕ) (pi0 sigma0 : ℝ) (hn : 1 ≤ n) :
    latticeMesh k dx n pi0 sigma0 ≤ (Real.sqrt n)⁻¹ := by
  unfold latticeMesh latticeHeight
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < n))
  have hceil : 1 ≤ ⌈Real.sqrt n⌉₊ := by
    have hsqrtOne : (1 : ℝ) ≤ Real.sqrt n :=
      Real.one_le_sqrt.mpr (by exact_mod_cast hn)
    exact_mod_cast (hsqrtOne.trans (Nat.le_ceil (Real.sqrt n)))
  have hheight : (0 : ℝ) <
      (⌈Real.sqrt n⌉₊ + ⌈pi0⁻¹⌉₊ + 2 * k + ⌈4 * Real.sqrt (dx * k)⌉₊ +
        ⌈2 * k / sigma0⌉₊ : ℕ) := by
    exact_mod_cast (by omega : 0 < ⌈Real.sqrt n⌉₊ + ⌈pi0⁻¹⌉₊ + 2 * k +
      ⌈4 * Real.sqrt (dx * k)⌉₊ + ⌈2 * k / sigma0⌉₊)
  apply (inv_le_inv₀ hheight hsqrt).2
  calc
    Real.sqrt n ≤ (⌈Real.sqrt n⌉₊ : ℝ) := Nat.le_ceil _
    _ ≤ (⌈Real.sqrt n⌉₊ + ⌈pi0⁻¹⌉₊ + 2 * k +
      ⌈4 * Real.sqrt (dx * k)⌉₊ + ⌈2 * k / sigma0⌉₊ : ℕ) := by
        exact_mod_cast (by omega : ⌈Real.sqrt n⌉₊ ≤
          ⌈Real.sqrt n⌉₊ + ⌈pi0⁻¹⌉₊ + 2 * k +
            ⌈4 * Real.sqrt (dx * k)⌉₊ + ⌈2 * k / sigma0⌉₊)

/-- Two probability laws supported in the same radius interval are at Wasserstein distance at
most the interval diameter. -/
lemma AtomicLaw.LawModulo.wass1_le_two_radius {k : ℕ} {radius : ℝ}
    (hradius : 0 ≤ radius) (nu xi : AtomicLaw.LawModulo k radius) :
    nu.wass1 xi ≤ 2 * radius := by
  let gamma : AtomicLaw.TransportPlan nu.representative.1 xi.representative.1 :=
    { mass := fun i j => nu.representative.1.weight i * xi.representative.1.weight j
      nonneg := fun i j => mul_nonneg (nu.representative.2.1 i) (xi.representative.2.1 j)
      fst_marginal := by
        intro i
        rw [← Finset.mul_sum, xi.representative.2.2.1, mul_one]
      snd_marginal := by
        intro j
        rw [← Finset.sum_mul, nu.representative.2.2.1, one_mul] }
  calc
    nu.wass1 xi ≤ AtomicLaw.transportCost gamma := AtomicLaw.wass1_le_of_plan gamma
    _ ≤ ∑ i, ∑ j, gamma.mass i j * (2 * radius) := by
      unfold AtomicLaw.transportCost
      apply Finset.sum_le_sum
      intro i _hi
      apply Finset.sum_le_sum
      intro j _hj
      apply mul_le_mul_of_nonneg_left _ (gamma.nonneg i j)
      have hi := nu.representative.2.2.2 i
      have hj := xi.representative.2.2.2 j
      have hiL : -radius ≤ nu.representative.1.atom i := hi.1
      have hiU : nu.representative.1.atom i ≤ radius := hi.2
      have hjL : -radius ≤ xi.representative.1.atom j := hj.1
      have hjU : xi.representative.1.atom j ≤ radius := hj.2
      exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
    _ = 2 * radius := by
      simp only [gamma, ← Finset.mul_sum, xi.representative.2.2.1,
        mul_one, ← Finset.sum_mul, nu.representative.2.2.1, one_mul]

/-- The large-summary-error branch of the deterministic oracle inequality. -/
lemma prescribedEstimator_wass1_le_of_large_summary_error
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (hk : 2 ≤ k) (hkz : k ≤ dz) (hL : 1 ≤ L) (hpi : 0 < pi0)
    (hsigma : 0 < sigma0)
    (A : LatticeEstimator k dx dz n (effectRadius dz L sigma0))
    (P : Measure (FullData k dx dz)) [IsProbabilityMeasure P]
    (hM : UCVMWModel (L := L) (pi0 := pi0) (sigma0 := sigma0) P)
    (sample : Fin n → Obs dx dz)
    (he : pi0 * sigma0 ^ 2 / 4 ≤ dS (empSummary sample) (obsSummary P)) :
    AtomicLaw.LawModulo.wass1 (A.estimate sample) (quotientLaw P hM) ≤
      (8 * effectRadius dz L sigma0 / (pi0 * sigma0 ^ 2)) *
        dS (empSummary sample) (obsSummary P) := by
  have hradius : 0 ≤ effectRadius dz L sigma0 := by
    unfold effectRadius
    have hdz : 0 < dz := lt_of_lt_of_le (by omega : 0 < k) hkz
    positivity
  have hdiam := AtomicLaw.LawModulo.wass1_le_two_radius hradius
    (A.estimate sample) (quotientLaw P hM)
  have hs0 : 0 < pi0 * sigma0 ^ 2 := mul_pos hpi (sq_pos_of_pos hsigma)
  calc
    AtomicLaw.LawModulo.wass1 (A.estimate sample) (quotientLaw P hM) ≤
        2 * effectRadius dz L sigma0 := hdiam
    _ ≤ (8 * effectRadius dz L sigma0 / (pi0 * sigma0 ^ 2)) *
        dS (empSummary sample) (obsSummary P) := by
      have hcoeff : 0 ≤ 8 * effectRadius dz L sigma0 / (pi0 * sigma0 ^ 2) := by
        positivity
      calc
        2 * effectRadius dz L sigma0 =
            (8 * effectRadius dz L sigma0 / (pi0 * sigma0 ^ 2)) *
              (pi0 * sigma0 ^ 2 / 4) := by field_simp; ring
        _ ≤ (8 * effectRadius dz L sigma0 / (pi0 * sigma0 ^ 2)) *
            dS (empSummary sample) (obsSummary P) :=
          mul_le_mul_of_nonneg_left he hcoeff

end

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
