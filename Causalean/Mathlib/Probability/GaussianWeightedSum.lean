/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Mathlib.Probability.Distributions.Gaussian.Real

/-! # Weighted sums of independent standard Gaussians

A fixed linear combination `∑ i, a i * ξ i` of independent standard Gaussian random
variables has exactly the centred Gaussian law whose variance is `∑ i, (a i)²`.
The main result is `map_weighted_sum_gaussian`. -/

public section

namespace Causalean.Mathlib

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- [A weighted sum of independent standard Gaussians with fixed weights has the centred
Gaussian law whose variance is the sum of the squared weights](goal), provided [the
family is mutually independent](hyp:hindep), [each variable is measurable](hyp:hmeas),
and [each has the standard Gaussian law](hyp:hlaw).

The proof peels one summand at a time over a `Finset`: each `a i * ξ i` is
Gaussian with variance `(a i)²` (`gaussianReal_map_const_mul`), and the partial
sum is independent of the new term
(`iIndepFun.indepFun_finset_sum_of_notMem`), so their laws convolve to a
Gaussian with variances adding (`gaussianReal_add_gaussianReal_of_indepFun`). -/
theorem map_weighted_sum_gaussian {n : ℕ} (ξ : Fin n → Ω → ℝ)
    (hindep : iIndepFun ξ μ) (hmeas : ∀ i, Measurable (ξ i))
    (hlaw : ∀ i, μ.map (ξ i) = gaussianReal 0 1) (a : Fin n → ℝ) :
    μ.map (fun ω => ∑ i, a i * ξ i ω)
      = gaussianReal 0 ⟨∑ i, (a i) ^ 2, by positivity⟩ := by
  -- The summands `g i ω = a i * ξ i ω`.
  set g : Fin n → Ω → ℝ := fun i ω => a i * ξ i ω with hg
  -- Each summand is measurable, independent, and Gaussian with variance `(a i)²`.
  have hg_meas : ∀ i, Measurable (g i) := fun i => (hmeas i).const_mul (a i)
  have hg_indep : iIndepFun g μ := by
    have : g = fun i => (fun x => a i * x) ∘ ξ i := by
      funext i ω; simp [hg, Function.comp]
    rw [this]
    exact hindep.comp _ (fun i => measurable_const_mul (a i))
  have hg_law : ∀ i, μ.map (g i) = gaussianReal 0 ⟨(a i) ^ 2, sq_nonneg _⟩ := by
    intro i
    have hgi : g i = (fun x => a i * x) ∘ ξ i := rfl
    have hmap : μ.map (g i) = (gaussianReal 0 1).map (fun x => a i * x) := by
      rw [hgi, ← Measure.map_map (measurable_const_mul (a i)) (hmeas i), hlaw i]
    rw [hmap, gaussianReal_map_const_mul (a i)]
    congr 1
    · ring
    · ext; simp; rfl
  -- General `Finset`-indexed statement, then specialise to `Finset.univ`.
  have key : ∀ s : Finset (Fin n),
      μ.map (fun ω => ∑ i ∈ s, g i ω)
        = gaussianReal 0 ⟨∑ i ∈ s, (a i) ^ 2, by positivity⟩ := by
    intro s
    induction s using Finset.induction with
    | empty =>
        simp only [Finset.sum_empty]
        rw [Measure.map_const]
        simp only [measure_univ, one_smul]
        rw [show (⟨(0 : ℝ), by positivity⟩ : NNReal) = 0 from rfl]
        exact (gaussianReal_zero_var 0).symm
    | insert j s hj ih =>
        -- Split off the `j`-th summand: rewrite as the Pi-sum `(partial sum) + g j`.
        have hsum : (fun ω => ∑ i ∈ insert j s, g i ω)
            = (fun ω => ∑ i ∈ s, g i ω) + g j := by
          funext ω; rw [Finset.sum_insert hj]; simp [Pi.add_apply]; ring
        rw [hsum]
        -- Independence of the partial sum and the new term.
        have hindepFun : IndepFun (fun ω => ∑ i ∈ s, g i ω) (g j) μ := by
          have h := hg_indep.indepFun_finset_sum_of_notMem hg_meas (s := s) (i := j) hj
          have heq : (∑ i ∈ s, g i) = (fun ω => ∑ i ∈ s, g i ω) := by
            funext ω; simp [Finset.sum_apply]
          rwa [heq] at h
        -- Convolution of the two Gaussian laws.
        have hconv :=
          gaussianReal_add_gaussianReal_of_indepFun hindepFun ih (hg_law j)
        rw [hconv]
        congr 1
        · simp
        · ext
          show (∑ i ∈ s, a i ^ 2) + a j ^ 2 = ∑ i ∈ insert j s, a i ^ 2
          rw [Finset.sum_insert hj]
          ring
  have := key Finset.univ
  simpa using this

end Causalean.Mathlib
