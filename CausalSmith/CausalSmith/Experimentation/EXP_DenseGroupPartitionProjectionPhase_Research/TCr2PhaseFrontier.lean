import CausalSmith.Experimentation.EXP_DenseGroupPartitionProjectionPhase_Research.Helpers.Cr2Ratio

/-!
# CR2 dense-regime phase frontier
-/

open scoped Topology
open Filter

namespace CausalSmith.Experimentation.DenseGroupPartitionProjectionPhase

open Causalean.Experimentation.DesignBased

-- @node: thm:cr2-phase-frontier
/-- Given [the stated population sizes, design objects, functions, and conditions](hyp:M,hM,A,p,rho,B,cSigma,J,hClass,hJohnsonOrthogonalDecomposition_of_gate,hKneserAdjacencySpectrum_of_gate), [the cr2 phase frontier result holds](goal). -/
theorem cr2_phase_frontier {M : ℕ} (hM : 2 ≤ M) (A : ScheduleArray M)
    (p rho B cSigma : ℝ) (J : ∀ r, JohnsonProjections (A.popSize r) M)
    (hClass : DenseScheduleClass A p rho B cSigma)
    (hJohnsonOrthogonalDecomposition_of_gate :
      ∀ r, JohnsonOrthogonalDecomposition (A.popSize r) M (J r))
    (hKneserAdjacencySpectrum_of_gate :
      ∀ r, KneserAdjacencySpectrum (A.popSize r) M) :
    FiniteDesign.TendstoInProb A.design
      (fun r w => (A.groups r : ℝ) * A.cr2 r w - A.leadingVariance r)
      (fun _ => 0) ∧
    FiniteDesign.TendstoInProb A.design
      (fun r w => (A.groups r : ℝ) * (A.cr2 r w - A.variance r) -
        rho * A.degreeOne (by omega) J r)
      (fun _ => 0) ∧
    (∀ ε : ℝ, 0 < ε → Tendsto (fun r =>
      (A.design r).Pr (fun w => A.cr2 r w / A.variance r < 1 - ε))
        atTop (nhds 0)) ∧
    (FiniteDesign.TendstoInProb A.design
      (fun r w => A.cr2 r w / A.variance r) (fun _ => 1) ↔
      Tendsto (fun r =>
        rho * A.degreeOne (by omega) J r /
        (A.leadingVariance r - rho * A.degreeOne (by omega) J r))
        atTop (nhds 0)) := by
  let d : ℕ → ℝ := fun r =>
    A.leadingVariance r - rho * A.degreeOne (by omega) J r
  let q : ℕ → ℝ := fun r => rho * A.degreeOne (by omega) J r / d r
  let a : ℕ → ℝ := fun r => A.leadingVariance r / d r
  have hfirst := cr2_centered_tendstoInProb hM A p B J hClass.growth hClass.fraction
    hClass.bounded hJohnsonOrthogonalDecomposition_of_gate hKneserAdjacencySpectrum_of_gate
  have hsecond := cr2_variance_gap_tendstoInProb hM A p rho B J hClass.growth
    hClass.fraction hClass.sampling hClass.bounded
    hJohnsonOrthogonalDecomposition_of_gate hKneserAdjacencySpectrum_of_gate
  have hratio : FiniteDesign.TendstoInProb A.design
      (fun r w => A.cr2 r w / A.variance r) a := by
    simpa [a, d] using cr2_ratio_leading_tendstoInProb hM A p rho B cSigma J hClass
      hJohnsonOrthogonalDecomposition_of_gate hKneserAdjacencySpectrum_of_gate
  obtain ⟨C0, hC0, hdense⟩ := dense_projection_limit hM p rho B
  have hv := (hdense A J hClass.growth hClass.fraction hClass.sampling hClass.bounded
    hJohnsonOrthogonalDecomposition_of_gate hKneserAdjacencySpectrum_of_gate).1
  have hxlow := scaledVariance_eventually_lower A cSigma hClass.nondegenerate
  have herr : ∀ᶠ r in atTop,
      |(A.groups r : ℝ) * A.variance r - d r| < cSigma / 4 := by
    have heps : 0 < cSigma / 4 := by linarith [hClass.nondegenerate.1]
    simpa [Real.dist_eq, d] using (Metric.tendsto_atTop.1 hv (cSigma / 4) heps)
  have hdlow : ∀ᶠ r in atTop, cSigma / 4 < d r := by
    filter_upwards [hxlow, herr] with r hx he
    have hab := (le_abs_self ((A.groups r : ℝ) * A.variance r - d r)).trans_lt he
    linarith
  have haq : ∀ᶠ r in atTop, a r = 1 + q r := by
    filter_upwards [hdlow] with r hd
    have hdne : d r ≠ 0 := ne_of_gt (by linarith [hClass.nondegenerate.1])
    have hdenne : A.leadingVariance r -
        rho * A.degreeOne (by omega) J r ≠ 0 := by
      simpa [d] using hdne
    dsimp [a, q, d]
    field_simp [hdenne]
    ring
  have haOne : ∀ᶠ r in atTop, 1 ≤ a r := by
    filter_upwards [haq, hdlow] with r heq hd
    rw [heq]
    have hrho : 0 ≤ rho := hClass.sampling.1
    have henergy : 0 ≤ A.degreeOne (by omega) J r := by
      unfold ScheduleArray.degreeOne degreeOneEnergy
      positivity
    have hd0 : 0 ≤ d r := by linarith [hClass.nondegenerate.1]
    exact le_add_of_nonneg_right (div_nonneg (mul_nonneg hrho henergy) hd0)
  refine ⟨hfirst, hsecond, lower_tail_vanishes_of_tendstoInProb hratio haOne, ?_⟩
  constructor
  · intro hratioOne
    have ha := tendstoInProb_target_unique hratio hratioOne
    have hsub := ha.sub_const 1
    have heq : ∀ᶠ r in atTop, a r - 1 = q r := by
      filter_upwards [haq] with r hr
      linarith
    simpa [q, d] using hsub.congr' heq
  · intro hq
    have ha : Tendsto a atTop (nhds 1) := by
      have hs := (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).add hq
      have heq : ∀ᶠ r in atTop, 1 + q r = a r := by
        filter_upwards [haq] with r hr
        exact hr.symm
      simpa using hs.congr' heq
    exact FiniteDesign.TendstoInProb.retarget hratio ha

end CausalSmith.Experimentation.DenseGroupPartitionProjectionPhase
