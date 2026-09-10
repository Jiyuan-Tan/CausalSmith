/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Minimax.ChiSquared
import Mathlib.Probability.Kernel.CompProdEqIff

/-!
# Chi-squared divergence for retained-design kernel laws

This module constructs a marked law that retains its base coordinate and samples its
mark from a probability kernel.  It states the chi-squared disintegration formula for
two such laws with the same base marginal.
-/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Given [a measurable design space](hyp:D), [a measurable mark space](hyp:M),
[a measure on the design space](hyp:m), and [a probability kernel from design points to mark
laws](hyp:kappa), the [attached marked-observation law](goal) draws a design point from the
measure and then a mark from the corresponding kernel, retaining both coordinates. -/
noncomputable def attachKernel {D M : Type*} [MeasurableSpace D] [MeasurableSpace M]
    (m : Measure D) (kappa : Kernel D M) : Measure (D × M) :=
  m ⊗ₘ kappa

/-- A marked-observation law formed from a probability base and a probability kernel is itself
a probability law. -/
noncomputable instance attachKernel.instIsProbabilityMeasure
    {D M : Type*} [MeasurableSpace D] [MeasurableSpace M]
    (m : Measure D) (kappa : Kernel D M)
    [IsProbabilityMeasure m] [IsMarkovKernel kappa] :
    IsProbabilityMeasure (attachKernel m kappa) := by
  unfold attachKernel
  infer_instance

/-- For [a probability design law](hyp:m),
[two measurable probability marking kernels](hyp:kappa,eta),
[pointwise absolute continuity of the first mark law with respect to the second](hyp:hac),
and [integrability of their jointly measurable squared density deviation](hyp:hint), [one plus
the χ²-divergence of the resulting marked laws equals the design-average of one plus the
conditional χ²-divergences](goal).

The pointwise absolute-continuity condition identifies Mathlib's joint kernel
Radon--Nikodym derivative with both the fibre derivatives and the density of the attached
laws; the integrability condition justifies the Fubini step. -/
theorem one_add_chiSqDiv_attachKernel
    {D M : Type*} [MeasurableSpace D] [MeasurableSpace M]
    [MeasurableSpace.CountableOrCountablyGenerated D M]
    (m : Measure D) [IsProbabilityMeasure m]
    (kappa eta : Kernel D M) [IsMarkovKernel kappa] [IsMarkovKernel eta]
    (hac : forall x, kappa x ≪ eta x)
    (hint : Integrable
      (fun p : D × M =>
        ((kappa.rnDeriv eta p.1 p.2).toReal - 1) ^ 2)
      (attachKernel m eta)) :
    1 + Causalean.Stat.chiSqDiv (attachKernel m kappa) (attachKernel m eta) =
      ∫ x, (1 + Causalean.Stat.chiSqDiv (kappa x) (eta x)) ∂m := by
  let f : D × M → ℝ := fun p => ((kappa.rnDeriv eta p.1 p.2).toReal - 1) ^ 2
  have hmeas : Measurable (fun p : D × M => kappa.rnDeriv eta p.1 p.2) := by
    fun_prop
  have hattach : attachKernel m kappa =
      (attachKernel m eta).withDensity (fun p => kappa.rnDeriv eta p.1 p.2) := by
    unfold attachKernel
    calc
      m ⊗ₘ kappa = m ⊗ₘ eta.withDensity (kappa.rnDeriv eta) :=
        Measure.compProd_congr <| Filter.Eventually.of_forall fun x =>
          (Kernel.withDensity_rnDeriv_eq (hac x)).symm
      _ = (m ⊗ₘ eta).withDensity (fun p => kappa.rnDeriv eta p.1 p.2) :=
        Measure.compProd_withDensity hmeas
  have hrn : (attachKernel m kappa).rnDeriv (attachKernel m eta) =ᵐ[attachKernel m eta]
      fun p => kappa.rnDeriv eta p.1 p.2 := by
    rw [hattach]
    exact Measure.rnDeriv_withDensity _ hmeas
  have hchiJoint : Causalean.Stat.chiSqDiv (attachKernel m kappa) (attachKernel m eta) =
      ∫ p, f p ∂(attachKernel m eta) := by
    rw [Causalean.Stat.chiSqDiv]
    exact integral_congr_ae (hrn.mono fun p hp => by simp only [f, hp])
  have hfiber (x : D) : Causalean.Stat.chiSqDiv (kappa x) (eta x) =
      ∫ y, f (x, y) ∂(eta x) := by
    rw [Causalean.Stat.chiSqDiv]
    exact integral_congr_ae
      ((Kernel.rnDeriv_eq_rnDeriv_measure (κ := kappa) (η := eta) (a := x)).mono
        fun y hy => by simp only [f, hy]) |>.symm
  have hintf : Integrable f (m ⊗ₘ eta) := by
    simpa only [f, attachKernel] using hint
  have hinner : Integrable (fun x => ∫ y, f (x, y) ∂(eta x)) m := by
    have hnorm := (Measure.integrable_compProd_iff hintf.aestronglyMeasurable).mp hintf |>.2
    simpa [f, Real.norm_eq_abs, abs_of_nonneg] using hnorm
  calc
    1 + Causalean.Stat.chiSqDiv (attachKernel m kappa) (attachKernel m eta) =
        1 + ∫ p, f p ∂(attachKernel m eta) := by rw [hchiJoint]
    _ = 1 + ∫ x, ∫ y, f (x, y) ∂(eta x) ∂m := by
      exact congrArg (fun z => 1 + z) (Measure.integral_compProd hintf)
    _ = ∫ x, (1 + ∫ y, f (x, y) ∂(eta x)) ∂m := by
      rw [integral_add (integrable_const 1) hinner]
      simp
    _ = ∫ x, (1 + Causalean.Stat.chiSqDiv (kappa x) (eta x)) ∂m := by
      exact integral_congr_ae <| Filter.Eventually.of_forall fun x => by
        dsimp
        rw [← hfiber x]

end Causalean.Stat
