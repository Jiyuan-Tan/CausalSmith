/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# Finite-measure integration under uniform convergence

This file packages continuity of set integration directly from the topology of uniform
convergence on the integration set. The parameter space need not be locally compact.
-/

open Filter Set MeasureTheory
open scoped Topology UniformConvergence

namespace Causalean.Mathlib.MeasureTheory

/-- For a [measure](hyp:mu), a [finite-measure integration set](hyp:K,hmu), and an
[integrable family of functions](hyp:F,hInt) that [varies continuously in the topology of uniform
convergence on that set](hyp:hF), [the corresponding set integrals vary continuously](goal). -/
lemma continuous_setIntegral_of_continuous_uniformOn
    {X Y E : Type*} [TopologicalSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (mu : Measure Y) (K : Set Y) (hmu : mu K < ⊤)
    (F : X → Y → E)
    (hF : Continuous (fun x ↦ UniformOnFun.ofFun {K} (F x)))
    (hInt : ∀ x, IntegrableOn (F x) K mu) :
    Continuous (fun x ↦ ∫ y in K, F x y ∂mu) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro epsilon hepsilon
  let delta := epsilon / (mu.real K + 1)
  have hdelta : 0 < delta := div_pos hepsilon (by positivity)
  have hgen : {g : UniformOnFun Y E {K} | ∀ y ∈ K,
      dist (UniformOnFun.toFun {K} (UniformOnFun.ofFun {K} (F x)) y)
        (UniformOnFun.toFun {K} g y) < delta} ∈
      nhds (UniformOnFun.ofFun {K} (F x)) := by
    apply UniformOnFun.gen_mem_nhds E {K} (UniformOnFun.ofFun {K} (F x))
      (s := K) (V := {p : E × E | dist p.1 p.2 < delta}) (by simp)
    exact Metric.uniformity_basis_dist.mem_iff.mpr ⟨delta, hdelta, by simp⟩
  have hev := hF.continuousAt hgen
  filter_upwards [hev] with z hz
  rw [dist_eq_norm, ← integral_sub (hInt z) (hInt x)]
  calc
    ‖∫ y in K, F z y - F x y ∂mu‖ ≤ delta * mu.real K :=
      norm_setIntegral_le_of_norm_le_const hmu fun y hy ↦ by
        exact (show ‖F z y - F x y‖ < delta by
          simpa only [UniformOnFun.toFun_ofFun, dist_eq_norm, norm_sub_rev] using hz y hy).le
    _ < epsilon := by
      dsimp [delta]
      have hm : 0 ≤ mu.real K := measureReal_nonneg
      calc
        epsilon / (mu.real K + 1) * mu.real K <
            epsilon / (mu.real K + 1) * (mu.real K + 1) :=
          mul_lt_mul_of_pos_left (lt_add_of_pos_right _ zero_lt_one)
            (div_pos hepsilon (by positivity))
        _ = epsilon := by field_simp

end Causalean.Mathlib.MeasureTheory
