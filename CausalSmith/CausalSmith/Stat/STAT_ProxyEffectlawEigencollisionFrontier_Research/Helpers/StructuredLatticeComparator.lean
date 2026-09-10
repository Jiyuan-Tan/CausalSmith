import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.StructuredLatticePolar

/-! # Assembly of the rounded structured-lattice comparator -/

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

noncomputable section

open scoped Matrix.Norms.L2Operator

/-- Assemble coordinate, polar, matrix, simplex, and effect rounding into one well-formed lattice
point.  The conclusion records the four approximation estimates used factorwise in (91). -/
lemma structuredLatticeComparator_exists
    {k dx dz n : ℕ} {L pi0 sigma0 : ℝ}
    (hk : 2 ≤ k) (hL : 1 ≤ L) (hpi : 0 < pi0) (hsigma : 0 < sigma0)
    (hradius : 0 ≤ effectRadius dz L sigma0)
    (V : SignalBasis dx k) (R : RectMatrix k k) (p tau : Fin k → ℝ)
    (hRmin : sigma0 ≤ signalMinSingular R)
    (hRnorm : ‖matrixCLM R‖ ≤ Real.sqrt k * L)
    (hp : ∀ u, 2 * pi0 ≤ p u) (hpSum : ∑ u, p u = 1)
    (htau : ∀ u, tau u ∈ Set.Icc (-effectRadius dz L sigma0) (effectRadius dz L sigma0)) :
    ∃ theta : StructuredLatticePoint k dx (effectRadius dz L sigma0),
      theta.WellFormed (dz := dz) (n := n) (L := L) (pi0 := pi0) (sigma0 := sigma0) ∧
      ‖matrixCLM (theta.V - V.V)‖ ≤
        4 * Real.sqrt (dx * k) * latticeMesh k dx n pi0 sigma0 ∧
      ‖matrixCLM (theta.R - R)‖ ≤
        (k : ℝ) * latticeMesh k dx n pi0 sigma0 ∧
      Real.sqrt (∑ u, (theta.weight u - p u) ^ 2) ≤
        Real.sqrt k * latticeMesh k dx n pi0 sigma0 ∧
      ∀ u, |theta.effect u - tau u| ≤ latticeMesh k dx n pi0 sigma0 := by
  classical
  let H := latticeHeight k dx n pi0 sigma0
  let q := latticeMesh k dx n pi0 sigma0
  have hkpos : 0 < k := by omega
  have hH : 0 < H := latticeHeight_pos hkpos
  have hmesh : Real.sqrt (dx * k) * (H : ℝ)⁻¹ ≤ 1 / 4 := by
    simpa [q, latticeMesh, H] using
      (sqrt_card_mul_latticeMesh_le_quarter (k := k) (dx := dx) (n := n)
        (pi0 := pi0) (sigma0 := sigma0) hkpos)
  obtain ⟨G, hG, hgrid, hGclose, hVclose⟩ :=
    V.exists_rounded_prescribedPolarFactor hkpos hH hmesh
  let Vn := prescribedPolarFactor G hG
  have hmargin : (k : ℝ) * (H : ℝ)⁻¹ ≤ sigma0 / 2 := by
    simpa [q, latticeMesh, H] using
      (k_mul_latticeMesh_le_half_sigma (k := k) (dx := dx) (n := n)
        (pi0 := pi0) (sigma0 := sigma0) hkpos hsigma)
  have hbudget : (k : ℝ) * (H : ℝ)⁻¹ ≤ Real.sqrt k * L := by
    simpa [q, latticeMesh, H] using
      (k_mul_latticeMesh_le_sqrt_mul (k := k) (dx := dx) (n := n)
        (pi0 := pi0) (sigma0 := sigma0) hk hL)
  obtain ⟨Rn, hRgrid, hRclose, hRnmin, hRnnorm⟩ :=
    exists_rounded_conditioned_matrix hH (by linarith) hsigma.le R hRmin hRnorm
      hmargin hbudget
  have hHpi : ⌈pi0⁻¹⌉₊ ≤ H := by
    simpa [H] using ceil_inv_le_latticeHeight k dx n pi0 sigma0
  obtain ⟨a, haFloor, haClose, haSum⟩ :=
    simplex_largestRemainder_round_with_floor_l2 hkpos hH hpi hHpi p hp hpSum
  let pn : Fin k → ℝ := fun u => (a u : ℝ) / H
  obtain ⟨taun, htauGrid, htauClose⟩ :=
    clipped_lattice_round_vector hH hradius tau htau
  have hpnNonneg (u : Fin k) : 0 ≤ pn u := by
    dsimp [pn]
    positivity
  have hpnSum : ∑ u, pn u = 1 := by
    dsimp [pn]
    rw [← Finset.sum_div]
    have hcast : ∑ u, (a u : ℝ) = (H : ℝ) := by exact_mod_cast haSum
    rw [hcast, div_self]
    exact_mod_cast hH.ne'
  have hVorth : ∀ i j, ∑ b, Vn b i * Vn b j = if i = j then 1 else 0 := by
    have hm := prescribedPolarFactor_transpose_mul_self G hG
    intro i j
    have hij := congr_fun (congr_fun hm i) j
    simpa [Vn, Matrix.mul_apply, Matrix.one_apply] using hij
  let theta : StructuredLatticePoint k dx (effectRadius dz L sigma0) :=
    { gridBasis := G
      V := Vn
      R := Rn
      weight := pn
      effect := taun
      lawValid := ⟨hpnNonneg, hpnSum, fun u => (htauGrid u).1⟩ }
  refine ⟨theta, ?_, ?_, ?_, ?_, ?_⟩
  · unfold StructuredLatticePoint.WellFormed
    change
      (∀ i j, ∃ z : ℤ, G i j = (H : ℝ)⁻¹ * z ∧ |G i j| ≤ 1) ∧
      (∃ hG' : 1 / 2 ≤ signalMinSingular G, Vn = prescribedPolarFactor G hG') ∧
      (∀ i j, ∑ b, Vn b i * Vn b j = if i = j then 1 else 0) ∧
      (∀ i j, ∃ z : ℤ, Rn i j = (H : ℝ)⁻¹ * z) ∧
      sigma0 / 2 ≤ signalMinSingular Rn ∧
      ‖matrixCLM Rn‖ ≤ 2 * Real.sqrt k * L ∧
      (∃ a' : Fin k → ℕ,
        (∀ u, ⌈pi0 * H⌉₊ ≤ a' u ∧ pn u = (a' u : ℝ) / H) ∧
        ∑ u, a' u = H) ∧
      ∀ u, taun u ∈ Set.Icc (-effectRadius dz L sigma0) (effectRadius dz L sigma0) ∧
        ∃ z : ℤ, taun u = (H : ℝ)⁻¹ * z
    refine ⟨hgrid, ⟨hG, rfl⟩, hVorth, hRgrid, hRnmin, hRnnorm, ?_, htauGrid⟩
    exact ⟨a, fun u => ⟨haFloor u, rfl⟩, haSum⟩
  · simpa [theta, Vn, q, latticeMesh, H] using hVclose
  · simpa [theta, q, latticeMesh, H] using hRclose
  · simpa [theta, pn, q, latticeMesh, H] using haClose
  · intro u
    simpa [theta, q, latticeMesh, H] using htauClose u

end

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
