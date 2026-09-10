import CausalSmith.ExactID.EID_RobustBackshiftUniformDistance_Research.Helpers.ContractionUniformExclusion
import Causalean.Discovery.LinearDisentanglement.Quantitative.PairwiseAffine.Definitions

/-!
# Residuals for the uniform contraction compactification
-/

namespace CausalSmith.ExactID.RobustBackshiftUniformDistance

open Set
open scoped Matrix.Norms.L2Operator

noncomputable section
open Causalean.Discovery.LinearDisentanglement.Quantitative.PairwiseAffine

/-- Sum of selected covariance perturbations.  A sum is used instead of a maximum because it is
continuous without requiring a nonempty selected set and still controls every summand. -/
def uniformContractionResidual {p m : ℕ} (S : Finset (Environment m))
    (z : UniformContractionAmbient p m) : ℝ :=
  ∑ e ∈ S, ‖z.selectedCovariance e - z.trueCovariance e‖

/-- For a fixed retained set, [the summed covariance residual varies continuously with the ambient candidate](goal). -/
lemma continuous_uniformContractionResidual {p m : ℕ} (S : Finset (Environment m)) :
    Continuous (uniformContractionResidual (p := p) S) := by
  unfold uniformContractionResidual
  fun_prop

/-- [The summed covariance residual is nonnegative](goal). -/
lemma uniformContractionResidual_nonneg {p m : ℕ} (S : Finset (Environment m))
    (z : UniformContractionAmbient p m) : 0 ≤ uniformContractionResidual S z := by
  exact Finset.sum_nonneg fun _ _ ↦ norm_nonneg _

/-- For every [retained environment](hyp:he), [its covariance discrepancy is no larger than the summed residual](goal). -/
lemma norm_selected_sub_true_le_residual {p m : ℕ} (S : Finset (Environment m))
    (z : UniformContractionAmbient p m) {e : Environment m} (he : e ∈ S) :
    ‖z.selectedCovariance e - z.trueCovariance e‖ ≤ uniformContractionResidual S z := by
  unfold uniformContractionResidual
  exact Finset.single_le_sum
    (fun (i : Environment m) _ ↦
      norm_nonneg (z.selectedCovariance i - z.trueCovariance i)) he

/-- If [the summed residual is zero](hyp:hzero), then at every [retained environment](hyp:he), [selected and true covariances agree](goal). -/
lemma selected_eq_true_of_residual_eq_zero {p m : ℕ} (S : Finset (Environment m))
    (z : UniformContractionAmbient p m) (hzero : uniformContractionResidual S z = 0)
    {e : Environment m} (he : e ∈ S) :
    z.selectedCovariance e = z.trueCovariance e := by
  have hle := norm_selected_sub_true_le_residual S z he
  rw [hzero] at hle
  exact sub_eq_zero.mp (norm_eq_zero.mp
    (le_antisymm hle (norm_nonneg (z.selectedCovariance e - z.trueCovariance e))))

/-- The entrywise-L² distance between candidate and reference is continuous on the ambient tuple. [This is the asserted conclusion](goal). -/
lemma continuous_uniformContractionEntryDistance {p m : ℕ} :
    Continuous (fun z : UniformContractionAmbient p m ↦
      entryL2 (z.candidate - z.structural)) := by
  unfold entryL2
  apply Continuous.sqrt
  fun_prop

end

end CausalSmith.ExactID.RobustBackshiftUniformDistance
