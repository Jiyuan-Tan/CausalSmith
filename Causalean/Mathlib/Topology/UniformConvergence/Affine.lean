/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# Affine paths in the topology of uniform convergence

This file proves continuity of affine interpolation paths in the topology of uniform convergence
on a nonempty compact set.
-/

open Set
open scoped Topology UniformConvergence

namespace Causalean.Mathlib.Topology

/-- For a [compact set](hyp:hK) that is [nonempty](hyp:hKne), the affine interpolation between
[two endpoint functions continuous on that set](hyp:hf,hg) is [continuous in the topology of
uniform convergence on the set](goal). -/
lemma continuous_uniformOnFun_affine_of_compact
    {α E : Type*} [TopologicalSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set α} (hK : IsCompact K) (hKne : K.Nonempty) {f g : α → E}
    (hf : ContinuousOn f K) (hg : ContinuousOn g K) :
    Continuous (fun t : ℝ => UniformOnFun.ofFun {K}
      (fun x => (1 - t) • f x + t • g x)) := by
  rcases hK.exists_isMaxOn hKne (hg.sub hf).norm with ⟨x₀, hx₀, hmax⟩
  let L : NNReal := ⟨‖g x₀ - f x₀‖, norm_nonneg _⟩
  apply UniformOnFun.continuous_of_forall_lipschitzWith (fun _ => L)
  intro S hS x hx
  simp only [Set.mem_singleton_iff] at hS
  subst S
  rw [lipschitzWith_iff_dist_le_mul]
  intro t u
  rw [dist_eq_norm, Real.dist_eq]
  have hbound : ‖g x - f x‖ ≤ ‖g x₀ - f x₀‖ := by
    have hxmax := hmax hx
    change ‖(g - f) x‖ ≤ ‖(g - f) x₀‖ at hxmax
    simpa only [Pi.sub_apply] using hxmax
  change ‖((1 - t) • f x + t • g x) - ((1 - u) • f x + u • g x)‖ ≤
    ‖g x₀ - f x₀‖ * |t - u|
  rw [show ((1 - t) • f x + t • g x) - ((1 - u) • f x + u • g x) =
      (t - u) • (g x - f x) by module, norm_smul, Real.norm_eq_abs]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hbound (abs_nonneg (t - u))

/-- For a [compact set](hyp:hK) that is [nonempty](hyp:hKne), a [path](hyp:path) that
[agrees there with the affine interpolation](hyp:hpath) of [two endpoint functions continuous on
the set](hyp:hf,hg) is [continuous in the topology of uniform convergence on the set](goal). -/
lemma continuous_uniformOnFun_of_eq_affine_on_compact
    {α E : Type*} [TopologicalSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set α} (hK : IsCompact K) (hKne : K.Nonempty) {f g : α → E}
    (hf : ContinuousOn f K) (hg : ContinuousOn g K) (path : ℝ → α → E)
    (hpath : ∀ t x, x ∈ K → path t x = (1 - t) • f x + t • g x) :
    Continuous (fun t : ℝ => UniformOnFun.ofFun {K} (path t)) := by
  rcases hK.exists_isMaxOn hKne (hg.sub hf).norm with ⟨x₀, hx₀, hmax⟩
  let L : NNReal := ⟨‖g x₀ - f x₀‖, norm_nonneg _⟩
  apply UniformOnFun.continuous_of_forall_lipschitzWith (fun _ => L)
  intro S hS x hx
  simp only [Set.mem_singleton_iff] at hS
  subst S
  rw [lipschitzWith_iff_dist_le_mul]
  intro t u
  rw [dist_eq_norm, Real.dist_eq]
  change ‖path t x - path u x‖ ≤ (L : ℝ) * |t - u|
  rw [hpath t x hx, hpath u x hx]
  have hbound : ‖g x - f x‖ ≤ ‖g x₀ - f x₀‖ := by
    have hxmax := hmax hx
    change ‖(g - f) x‖ ≤ ‖(g - f) x₀‖ at hxmax
    simpa only [Pi.sub_apply] using hxmax
  change ‖((1 - t) • f x + t • g x) - ((1 - u) • f x + u • g x)‖ ≤
    ‖g x₀ - f x₀‖ * |t - u|
  rw [show ((1 - t) • f x + t • g x) - ((1 - u) • f x + u • g x) =
      (t - u) • (g x - f x) by module, norm_smul, Real.norm_eq_abs]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hbound (abs_nonneg (t - u))

end Causalean.Mathlib.Topology
