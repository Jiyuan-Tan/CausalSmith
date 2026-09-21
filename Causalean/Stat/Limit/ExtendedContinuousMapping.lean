/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.Limit.ConvergenceVec

/-! # Extended continuous mapping for varying maps

This file proves a finite-dimensional extended continuous mapping principle.
If random elements converge weakly and a sequence of maps converges uniformly
to a continuous map on every norm-bounded set, applying the varying maps
preserves weak convergence to the pushforward under the limiting map.

The result isolates the probabilistic tightness argument used by the
Hadamard-directional functional delta method. -/

public section

namespace Causalean.Stat

open Filter MeasureTheory Topology

/-- Suppose [measurable random elements `Xn`](hyp:hXn) [converge weakly to `Q`](hyp:hX),
[the limiting map `g` is continuous](hyp:hg), [the transformed random elements are
measurable](hyp:hYn), and [the
varying maps `fn n` approach `g` uniformly on every norm-bounded set](hyp:hUniform). Then
[`fn n (Xn n)` converges weakly to the pushforward of `Q` under `g`](goal).

This is the extended continuous mapping theorem in the uniform-on-bounded-sets
form. Weak convergence supplies tightness of `Xn`; on a sufficiently large
ball the two transforms are uniformly close, and vector Slutsky absorbs the
remaining error. -/
theorem Tendsto_dist_vec.map_varying_of_uniform_on_bounded
    {Ω E F : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F]
    {Xn : ℕ → Ω → E} {Q : Measure E} [IsProbabilityMeasure Q]
    {fn : ℕ → E → F} {g : E → F}
    (hg : Continuous g)
    (hXn : ∀ n, AEMeasurable (Xn n) μ)
    (hYn : ∀ n, AEMeasurable (fun omega => fn n (Xn n omega)) μ)
    (hX : Tendsto_dist_vec Xn Q μ hXn)
    (hUniform : ∀ (M : ℝ) (epsilon : ℝ), 0 < epsilon →
      ∀ᶠ n in atTop, ∀ x : E, ‖x‖ ≤ M → ‖fn n x - g x‖ < epsilon) :
    Tendsto (β := ProbabilityMeasure F)
      (fun n =>
        ⟨μ.map (fun omega => fn n (Xn n omega)),
          Measure.isProbabilityMeasure_map (hYn n)⟩)
      atTop
      (𝓝 ⟨Q.map g,
        Measure.isProbabilityMeasure_map hg.measurable.aemeasurable⟩) := by
  let Zn : ℕ → Ω → F := fun n omega => g (Xn n omega)
  let Yn : ℕ → Ω → F := fun n omega => fn n (Xn n omega)
  let _ : IsProbabilityMeasure (Q.map g) :=
    Measure.isProbabilityMeasure_map hg.measurable.aemeasurable
  let _ : IsProbabilityMeasure (Q.map fun x : E => ‖x‖) :=
    Measure.isProbabilityMeasure_map continuous_norm.measurable.aemeasurable
  have hZn : ∀ n, AEMeasurable (Zn n) μ := fun n =>
    hg.measurable.comp_aemeasurable (hXn n)
  have hNormXn : ∀ n, AEMeasurable (fun omega => ‖Xn n omega‖) μ := fun n =>
    continuous_norm.measurable.comp_aemeasurable (hXn n)
  have hNormDist : Tendsto_dist
      (fun n omega => ‖Xn n omega‖) (Q.map fun x : E => ‖x‖) μ hNormXn := by
    have hvec := Tendsto_dist_vec.map_continuous
      (Q := Q) (g := fun x : E => ‖x‖) continuous_norm hXn hX
    exact (Tendsto_dist_iff _ _ _ hNormXn).2 hvec
  have hTight : IsBigOp (fun n omega => ‖Xn n omega‖) (fun _ => (1 : ℝ)) μ :=
    Tendsto_dist.tightness hNormXn hNormDist
  have hRem : IsLittleOp (fun n omega => ‖Yn n omega - Zn n omega‖)
      (fun _ => (1 : ℝ)) μ := by
    intro epsilon hepsilon
    rw [ENNReal.tendsto_nhds_zero]
    intro delta hdelta
    rcases hTight delta hdelta with ⟨M, hMpos, hAevent⟩
    let A : ℕ → Set Ω := fun n => {omega | M ≤ ‖Xn n omega‖}
    have hUevent := hUniform M epsilon hepsilon
    filter_upwards [hAevent, hUevent] with n hAn hUn
    have hsubset :
        {omega | epsilon * (fun _ => (1 : ℝ)) n ≤ |‖Yn n omega - Zn n omega‖|}
          ⊆ A n := by
      intro omega homega
      simp only [mul_one, abs_of_nonneg (norm_nonneg _)] at homega
      by_contra hnot
      have hbound : ‖Xn n omega‖ ≤ M := (lt_of_not_ge hnot).le
      exact (not_lt_of_ge homega) (hUn (Xn n omega) hbound)
    have hAn' : μ (A n) ≤ delta := by simpa [A, abs_of_nonneg] using hAn
    exact (measure_mono hsubset).trans hAn'
  have hZdist : Tendsto_dist_vec Zn (Q.map g) μ hZn := by
    exact (Tendsto_dist_vec_iff _ _ _ hZn).2
      (Tendsto_dist_vec.map_continuous hg hXn hX)
  exact (Tendsto_dist_vec_iff _ _ _ hYn).1
    (Tendsto_dist_vec.add_isLittleOp_one hZn hYn hZdist hRem)

end Causalean.Stat
