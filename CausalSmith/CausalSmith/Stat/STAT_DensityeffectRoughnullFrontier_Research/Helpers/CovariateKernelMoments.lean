module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.KernelDesignMeans

/-! Exact squared-kernel masses for the uniform design. These are the cell
identities used in the full two-role and three-role overlap moment estimates. -/

public section

noncomputable section
open MeasureTheory
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- Squaring a histogram kernel multiplies it by its rank. -/
-- @node: covariateKernel_sq
lemma covariateKernel_sq (k : ℕ) (x z : ℝ) :
    (covariateKernel k x z) ^ 2 = (k : ℝ) * covariateKernel k x z := by
  unfold covariateKernel
  split_ifs <;> ring

/-- Each positive-rank kernel row has mass one, even for a boundary covariate. -/
-- @node: integral_covariateKernel
lemma integral_covariateKernel (k : ℕ) (hk : 0 < k) (x : ℝ) :
    (∫ z, covariateKernel k x z ∂unitVolume) = 1 := by
  have hi := cell_index_mem k hk x
  let i : Fin k := ⟨cell k x - 1, by omega⟩
  have hx : cell k x = i.val + 1 := by dsimp [i]; omega
  let := correctionCellLaw_probability k hk i
  have h := cellAverage_eq_correctionCellLaw k i (fun _ => (1 : ℝ)) x hx
  simpa [cellAverage, smul_eq_mul, measureReal_def] using h

/-- A squared kernel row integrates to its rank. -/
-- @node: integral_covariateKernel_sq
lemma integral_covariateKernel_sq (k : ℕ) (hk : 0 < k) (x : ℝ) :
    (∫ z, (covariateKernel k x z) ^ 2 ∂unitVolume) = k := by
  simp_rw [covariateKernel_sq]
  rw [integral_const_mul, integral_covariateKernel k hk, mul_one]

/-- The full two-covariate squared-kernel mass equals its rank. -/
-- @node: integral_pair_covariateKernel_sq
lemma integral_pair_covariateKernel_sq (k : ℕ) (hk : 0 < k) :
    (∫ x, ∫ z, (covariateKernel k x z) ^ 2 ∂unitVolume ∂unitVolume) = k := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  simp_rw [integral_covariateKernel_sq k hk]
  simp

/-- Integrating a squared kernel against a weight yields its rank times the cell mean. -/
-- @node: integral_covariateKernel_sq_mul
lemma integral_covariateKernel_sq_mul (k : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    (∫ z, (covariateKernel k x z) ^ 2 * f z ∂unitVolume) =
      (k : ℝ) * cellAverage k f x := by
  simp_rw [covariateKernel_sq, mul_assoc]
  rw [integral_const_mul]
  rfl

/-- The two-role weighted squared mass depends only on the integrated weight. -/
-- @node: integral_pair_covariateKernel_sq_mul
lemma integral_pair_covariateKernel_sq_mul (k : ℕ) (hk : 0 < k)
    (f : ℝ → ℝ) (hf : Integrable f unitVolume) :
    (∫ x, ∫ z, (covariateKernel k x z) ^ 2 * f z ∂unitVolume ∂unitVolume) =
      (k : ℝ) * ∫ z, f z ∂unitVolume := by
  simp_rw [integral_covariateKernel_sq_mul]
  rw [integral_const_mul, integral_cellAverage_vector k hk f hf]

/-- The full three-role overlap has squared design mass q squared, with no sparse-rank loss. -/
-- @node: integral_triple_covariateKernel_sq
lemma integral_triple_covariateKernel_sq (q : ℕ) (hq : 0 < q) :
    (∫ x, ∫ z, ∫ w, (covariateKernel q x z) ^ 2 *
      (covariateKernel q z w) ^ 2 ∂unitVolume ∂unitVolume ∂unitVolume) = (q : ℝ) ^ 2 := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  simp_rw [integral_const_mul, integral_covariateKernel_sq q hq]
  simp_rw [integral_mul_const, integral_covariateKernel_sq q hq]
  simp [pow_two]

end CausalSmith.Stat.DensityEffectRoughNull
