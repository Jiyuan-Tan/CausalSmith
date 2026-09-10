import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.SpectralSubstrate

/-! A two-dimensional variational certificate for the explicit witness proxy matrices. -/

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open scoped BigOperators

/-- A coordinatewise quadratic lower bound certifies the last singular value of a real
two-by-two matrix. -/
-- @node: signalMinSingular_lower_fin_two
lemma signalMinSingular_lower_fin_two (A : RectMatrix 2 2) (s : ℝ) (hs : 0 < s)
    (hquad : ∀ x : Fin 2 → ℝ,
      s ^ 2 * (∑ j, x j ^ 2) ≤ ∑ i, (∑ j, A i j * x j) ^ 2) :
    s ≤ signalMinSingular A := by
  let S := singularSystem A
  let r : Fin 2 := 1
  let v : Fin 2 → ℝ := S.right r
  have hv : ∑ j, S.right r j ^ 2 = 1 := by
    simpa [pow_two] using S.right_orthonormal r r
  have hsigma : 0 < S.sigma r := by
    by_contra hn
    have hz : S.sigma r = 0 := le_antisymm (le_of_not_gt hn) (S.sigma_nonneg r)
    have h := hquad v
    dsimp [v] at h
    simp_rw [S.apply_right] at h
    rw [hv] at h
    simp [hz] at h
    nlinarith
  have hleft : ∑ i, S.left r i ^ 2 = 1 := by
    simpa [pow_two] using S.left_orthonormal_of_pos r r hsigma hsigma
  have h := hquad v
  dsimp [v] at h
  simp_rw [S.apply_right] at h
  rw [hv] at h
  simp only [mul_pow] at h
  rw [← Finset.mul_sum, hleft, mul_one, mul_one] at h
  have hle : s ≤ S.sigma r := (sq_le_sq₀ hs.le hsigma.le).mp h
  rw [S.sigma_eq r] at hle
  simpa [signalMinSingular, singularValue, r] using hle

/-- The target-proxy matrix of the collision witness has singular-value margin one tenth. -/
-- @node: witnessTargetMatrix_signalMinSingular
lemma witnessTargetMatrix_signalMinSingular :
    (1 / 10 : ℝ) ≤ signalMinSingular (fun i j : Fin 2 =>
      if i.val = 0 then 1 else if j.val = 0 then 1 / 5 else 4 / 5) := by
  apply signalMinSingular_lower_fin_two _ _ (by norm_num)
  intro x
  simp [Fin.sum_univ_two]
  nlinarith [sq_nonneg (3 * x 0 - 4 * x 1)]

/-- The control-arm reference-proxy matrix has singular-value margin one tenth. -/
-- @node: witnessReferenceMatrix_false_signalMinSingular
lemma witnessReferenceMatrix_false_signalMinSingular :
    (1 / 10 : ℝ) ≤ signalMinSingular (fun i j : Fin 2 =>
      if i.val = 0 then 1 else if j.val = 0 then 3 / 10 else 7 / 10) := by
  apply signalMinSingular_lower_fin_two _ _ (by norm_num)
  intro x
  simp [Fin.sum_univ_two]
  nlinarith [sq_nonneg (3 * x 0 - 7 * x 1)]

/-- The treated-arm reference-proxy matrix has singular-value margin one tenth. -/
-- @node: witnessReferenceMatrix_true_signalMinSingular
lemma witnessReferenceMatrix_true_signalMinSingular :
    (1 / 10 : ℝ) ≤ signalMinSingular (fun i j : Fin 2 =>
      if i.val = 0 then 1 else if j.val = 0 then 7 / 20 else 3 / 4) := by
  apply signalMinSingular_lower_fin_two _ _ (by norm_num)
  intro x
  simp [Fin.sum_univ_two]
  nlinarith [sq_nonneg (7 * x 0 - 15 * x 1)]

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
