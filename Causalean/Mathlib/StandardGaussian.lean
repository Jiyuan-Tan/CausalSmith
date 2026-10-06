/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Mathlib.Probability.Distributions.Gaussian.Basic
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Moments.CovarianceBilin
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-! # Standard Gaussian Measures

This file retains compatibility names for Mathlib's standard Gaussian measure on a
finite-dimensional real inner-product space. It also identifies the law of the squared norm with
the sum of squared independent one-dimensional standard Gaussians.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InnerProductSpace WithLp
open scoped RealInnerProductSpace

namespace Causalean.Mathlib

attribute [local instance] Fintype.ofFinite

section CompatibilityCoordinateModels

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The chosen orthonormal basis of `E`. -/
@[deprecated stdOrthonormalBasis (since := "2026-09-15")]
noncomputable def onb : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E :=
  stdOrthonormalBasis ℝ E

/-- For every [real normed inner-product space](hyp:E), the [coordinate product Gaussian
measure](goal) is the product of independent standard normal laws, with one real-valued coordinate
for every element of the finite index set whose size is the space's real rank.

The product measure of independent standard normal laws, with one real-valued coordinate
for each dimension of a finite-dimensional real inner-product space. -/
noncomputable def piGaussian : Measure (Fin (Module.finrank ℝ E) → ℝ) :=
  Measure.pi (fun _ : Fin (Module.finrank ℝ E) => gaussianReal 0 1)

/-- The product standard Gaussian transported to `EuclideanSpace ℝ (Fin n)`. -/
@[deprecated ProbabilityTheory.stdGaussian (since := "2026-09-15")]
noncomputable def euclideanStdGaussian :
    Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
  ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))

end CompatibilityCoordinateModels

/-- The standard Gaussian measure on a finite-dimensional real inner-product space.

This compatibility definition is retained because banked statements use its qualified name; its
value is Mathlib's `ProbabilityTheory.stdGaussian`. -/
noncomputable def stdGaussian (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] : Measure E :=
  ProbabilityTheory.stdGaussian E

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- For every [real normed inner-product space](hyp:E), [the coordinate product of independent one-dimensional standard Gaussian laws is a probability measure](goal). -/
instance isProbabilityMeasure_piGaussian : IsProbabilityMeasure (piGaussian E) := by
  unfold piGaussian
  infer_instance

/-- For every [real normed inner-product space](hyp:E), [the coordinate product of independent one-dimensional standard Gaussian laws is a Gaussian probability law](goal). -/
instance isGaussian_piGaussian : IsGaussian (piGaussian E) := by
  have hIndep : iIndepFun (fun (i : Fin (Module.finrank ℝ E))
      (ω : Fin (Module.finrank ℝ E) → ℝ) => ω i) (piGaussian E) :=
    iIndepFun_pi (X := fun _ => (id : ℝ → ℝ)) (fun _ => aemeasurable_id)
  have hLaw : ∀ i, HasGaussianLaw
      (fun ω : Fin (Module.finrank ℝ E) → ℝ => ω i) (piGaussian E) := by
    intro i
    classical
    have hmap : (piGaussian E).map (fun ω => ω i) = gaussianReal 0 1 := by
      unfold piGaussian
      rw [show (fun ω : Fin (Module.finrank ℝ E) → ℝ => ω i)
          = Function.eval i from rfl, Measure.pi_map_eval]
      simp
    refine ⟨?_⟩
    rw [hmap]
    infer_instance
  have hJoint : IsGaussian
      ((piGaussian E).map (fun ω => (fun i => ω i :
        Fin (Module.finrank ℝ E) → ℝ))) :=
    (hIndep.hasGaussianLaw hLaw).isGaussian_map
  simpa using hJoint

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Each coordinate is `MemLp` of order 2 under the product measure. -/
lemma memLp_eval (i : Fin (Module.finrank ℝ E)) :
    MemLp (fun ω : Fin (Module.finrank ℝ E) → ℝ => ω i) 2 (piGaussian E) := by
  have h : MemLp id 2 (gaussianReal (0 : ℝ) 1) := memLp_id_gaussianReal' 2 (by simp)
  exact h.comp_measurePreserving (measurePreserving_eval _ i)

/-- For every [real normed inner-product space](hyp:E), [the transported coordinate-product standard Gaussian law on the associated Euclidean space is a probability measure](goal). -/
@[deprecated ProbabilityTheory.isProbabilityMeasure_stdGaussian (since := "2026-09-15")]
instance isProbabilityMeasure_euclideanStdGaussian :
    IsProbabilityMeasure (euclideanStdGaussian E) := by
  rw [euclideanStdGaussian]
  infer_instance

/-- For every [real normed inner-product space](hyp:E), [the transported coordinate-product standard Gaussian law on the associated Euclidean space is a Gaussian probability law](goal). -/
@[deprecated ProbabilityTheory.isGaussian_stdGaussian (since := "2026-09-15")]
instance isGaussian_euclideanStdGaussian : IsGaussian (euclideanStdGaussian E) := by
  rw [euclideanStdGaussian]
  infer_instance

/-- Transporting a measure through a continuous linear equivalence transports its vector integral
through the same equivalence. -/
lemma integral_id_map_equiv {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G]
    {μ : Measure F} (L : F ≃L[ℝ] G) :
    ∫ x, x ∂(μ.map L) = L (∫ x, x ∂μ) := by
  rw [integral_map (φ := L) (f := fun x => x) (by fun_prop)
    (aestronglyMeasurable_id.congr (by rfl))]
  exact L.integral_comp_comm (fun x => x)

/-- The standard Gaussian measure is a probability measure. -/
@[deprecated ProbabilityTheory.isProbabilityMeasure_stdGaussian (since := "2026-09-15")]
instance isProbabilityMeasure_stdGaussian : IsProbabilityMeasure (stdGaussian E) := by
  change IsProbabilityMeasure (ProbabilityTheory.stdGaussian E)
  infer_instance

/-- The standard Gaussian measure is Gaussian. -/
@[deprecated ProbabilityTheory.isGaussian_stdGaussian (since := "2026-09-15")]
instance isGaussian_stdGaussian : IsGaussian (stdGaussian E) := by
  change IsGaussian (ProbabilityTheory.stdGaussian E)
  infer_instance

/-- The standard Gaussian measure on a finite-dimensional real inner-product space has mean
zero. -/
@[deprecated ProbabilityTheory.integral_id_stdGaussian (since := "2026-09-15")]
theorem stdGaussian_mean : ∫ x, x ∂(stdGaussian E) = 0 := by
  simpa only [stdGaussian] using (ProbabilityTheory.integral_id_stdGaussian (E := E))

/-- The covariance bilinear form of the standard Gaussian measure is the ambient inner
product. -/
@[deprecated ProbabilityTheory.covarianceBilin_stdGaussian (since := "2026-09-15")]
theorem covarianceBilin_stdGaussian (u v : E) :
    covarianceBilin (stdGaussian E) u v = (inner ℝ u v : ℝ) := by
  rw [stdGaussian, ProbabilityTheory.covarianceBilin_stdGaussian]
  rfl

/-- **Product-of-1-D-Gaussians model for the squared norm.** [The law of the squared norm
under the standard Gaussian measure on `E` equals the law of the sum of squared
coordinates under a product of `finrank ℝ E` independent standard real Gaussians](goal).

This exposes the explicit product structure needed to prove atomlessness of the χ² law. -/
theorem stdGaussian_map_normSq_eq_pi :
    (stdGaussian E).map (fun x => ‖x‖ ^ 2)
      = (Measure.pi (fun _ : Fin (Module.finrank ℝ E) => gaussianReal 0 1)).map
          (fun w => ∑ i, (w i) ^ 2) := by
  rw [stdGaussian,
    ProbabilityTheory.stdGaussian_eq_map_pi_orthonormalBasis (stdOrthonormalBasis ℝ E),
    Measure.map_map (by fun_prop) (by fun_prop)]
  refine Measure.map_congr (ae_of_all _ fun w => ?_)
  simp only [Function.comp_apply]
  rw [← (stdOrthonormalBasis ℝ E).equiv_apply_euclideanSpace (toLp 2 w),
    LinearIsometryEquiv.norm_map, EuclideanSpace.norm_eq,
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.norm_eq_abs, sq_abs]

end Causalean.Mathlib
