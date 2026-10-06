module

public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.Helpers.MomentBridge
public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.Helpers.Triangular
public import Mathlib.Probability.Distributions.Gaussian.Fernique

/-! The observable Gaussian mean agrees with the structural mean. -/

public section

open MeasureTheory ProbabilityTheory Matrix

namespace CausalSmith.ExactID.EIDCountshiftUnlabeledMatching

-- @node: obsMean_eq_structural_mean
lemma obsMean_eq_structural_mean {p M : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (𝔐 : AtomicCountModel p M Ω μ)
    (m : Fin (M + 1)) :
    obsMean μ 𝔐 m = totalEffect 𝔐.A *ᵥ 𝔐.η m := by
  letI : IsProbabilityMeasure μ :=
    ((𝔐.gaussian 0).2.isProbabilityMeasure_iff).2 inferInstance
  have hbridge := (observable_moment_bridge μ 𝔐).1 m
  have hξ : ∫ ω, WithLp.toLp 2 (𝔐.ξ m ω) ∂μ = 0 := by
    simpa using (𝔐.gaussian m).2.integral_eq
  have hξint : Integrable (fun ω => WithLp.toLp 2 (𝔐.ξ m ω)) μ := by
    have hmap := (𝔐.gaussian m).2.map_eq
    have h := IsGaussian.integrable_id (μ := multivariateGaussian 0 (𝔐.Ωc m))
    rw [← hmap] at h
    exact (integrable_map_measure aestronglyMeasurable_id (𝔐.gaussian m).2.aemeasurable).mp h
  have hstate : (∫ ω, WithLp.toLp 2 (latentState 𝔐.A 𝔐.η 𝔐.ξ m ω) ∂μ) =
      WithLp.toLp 2 (totalEffect 𝔐.A *ᵥ 𝔐.η m) := by
    let L := (Matrix.toEuclideanCLM (n := Fin p) (𝕜 := ℝ)).toFun (totalEffect 𝔐.A)
    have heq (ω : Ω) :
        WithLp.toLp 2 (latentState 𝔐.A 𝔐.η 𝔐.ξ m ω) =
          L (WithLp.toLp 2 (𝔐.η m) + WithLp.toLp 2 (𝔐.ξ m ω)) := by
      change WithLp.toLp 2 (totalEffect 𝔐.A *ᵥ (𝔐.η m + 𝔐.ξ m ω)) =
        (Matrix.toEuclideanCLM (n := Fin p) (𝕜 := ℝ)).toFun (totalEffect 𝔐.A)
          (WithLp.toLp 2 (𝔐.η m + 𝔐.ξ m ω))
      exact (Matrix.toEuclideanCLM_toLp (totalEffect 𝔐.A) _).symm
    simp_rw [heq]
    have hsum : Integrable (fun ω =>
        WithLp.toLp 2 (𝔐.η m) + WithLp.toLp 2 (𝔐.ξ m ω)) μ :=
      (integrable_const _).add hξint
    rw [L.integral_comp_comm hsum]
    have hadd : (∫ ω, WithLp.toLp 2 (𝔐.η m) +
        WithLp.toLp 2 (𝔐.ξ m ω) ∂μ) =
        WithLp.toLp 2 (𝔐.η m) +
          ∫ ω, WithLp.toLp 2 (𝔐.ξ m ω) ∂μ := by
      exact (integral_add (integrable_const _) hξint).trans (by simp)
    rw [hadd, hξ]
    simp only [add_zero]
    change (Matrix.toEuclideanCLM (n := Fin p) (𝕜 := ℝ)).toFun (totalEffect 𝔐.A)
        (WithLp.toLp 2 (𝔐.η m)) = WithLp.toLp 2 (totalEffect 𝔐.A *ᵥ 𝔐.η m)
    exact Matrix.toEuclideanCLM_toLp (totalEffect 𝔐.A) (𝔐.η m)
  funext j
  rw [hbridge j]
  have hstateint : Integrable
      (fun ω => WithLp.toLp 2 (latentState 𝔐.A 𝔐.η 𝔐.ξ m ω)) μ := by
    let L := (Matrix.toEuclideanCLM (n := Fin p) (𝕜 := ℝ)).toFun (totalEffect 𝔐.A)
    have hsum : Integrable (fun ω =>
        WithLp.toLp 2 (𝔐.η m) + WithLp.toLp 2 (𝔐.ξ m ω)) μ :=
      (integrable_const _).add hξint
    have h := L.integrable_comp hsum
    have heq : (fun ω => WithLp.toLp 2 (latentState 𝔐.A 𝔐.η 𝔐.ξ m ω)) =
        (fun ω => L (WithLp.toLp 2 (𝔐.η m) + WithLp.toLp 2 (𝔐.ξ m ω))) := by
      funext ω
      change WithLp.toLp 2 (totalEffect 𝔐.A *ᵥ (𝔐.η m + 𝔐.ξ m ω)) =
        L (WithLp.toLp 2 (𝔐.η m + 𝔐.ξ m ω))
      exact (Matrix.toEuclideanCLM_toLp (totalEffect 𝔐.A) _).symm
    rw [heq]
    exact h
  have hproj := (EuclideanSpace.proj (𝕜 := ℝ) j).integral_comp_comm hstateint
  have hcoord : (∫ ω, latentState 𝔐.A 𝔐.η 𝔐.ξ m ω j ∂μ) =
      (∫ ω, WithLp.toLp 2 (latentState 𝔐.A 𝔐.η 𝔐.ξ m ω) ∂μ) j := by
    simpa using hproj
  rw [hcoord, hstate]

end CausalSmith.ExactID.EIDCountshiftUnlabeledMatching
