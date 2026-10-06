/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.CLT.HadamardDeriv
public import Causalean.Stat.Limit.ExtendedContinuousMapping
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Functional delta method for Hadamard directional derivatives

This file proves the finite-dimensional functional delta method for the
library's sequential `HasHadamardDirDerivAt` predicate. The deterministic core
upgrades its pointwise sequential expansion to uniform approximation on
bounded sets. The extended continuous mapping theorem then transports an input
weak limit through the continuous, possibly nonlinear directional derivative.

The max/min corollaries apply at every base point, including ties, and therefore
cover intersection-bound endpoints without restricting attention to the
binding case.

The nonlinear directional theorem formalized here is a finite-dimensional,
whole-space specialization of Shapiro (1991), Theorem 2.1, and Fang and Santos
(2019), Theorem 2.1, with continuity of the directional derivative required
explicitly. Van der Vaart (1998), Theorem 20.8 is the fully Hadamard-
differentiable linear special case and supplies the classical proof template. -/

@[expose] public section

namespace Causalean.Stat

open Filter MeasureTheory Topology

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- If [a map has Hadamard directional derivative `φ'` at `θ`](hyp:hφ), [that derivative is
continuous](hyp:hφ'), and [a rate `r` diverges](hyp:hr), then [the corresponding
rescaled increment maps converge to `φ'` uniformly on every norm-bounded set](goal).

Finite dimensionality turns each closed ball into a compact set. If uniform
convergence failed, a violating sequence of directions would have a convergent
subsequence, contradicting the defining sequential Hadamard expansion. -/
theorem HasHadamardDirDerivAt.uniform_on_bounded
    [FiniteDimensional ℝ E]
    {φ : E → F} {φ' : E → F} {θ : E}
    (hφ : HasHadamardDirDerivAt φ φ' θ)
    (hφ' : Continuous φ')
    (r : ℕ → ℝ) (hr : Tendsto r atTop atTop) :
    ∀ (M : ℝ) (epsilon : ℝ), 0 < epsilon →
      ∀ᶠ n in atTop, ∀ h : E, ‖h‖ ≤ M →
        ‖r n • (φ (θ + (r n)⁻¹ • h) - φ θ) - φ' h‖ < epsilon := by
  intro M epsilon hepsilon
  by_contra hfail
  rw [Filter.eventually_atTop] at hfail
  push Not at hfail
  obtain ⟨Npos, hNpos⟩ := Filter.eventually_atTop.mp
    (Filter.tendsto_atTop.mp hr 1)
  choose k hk x hx hbad using fun N => hfail (max Npos N)
  have hkN : ∀ n, n ≤ k n := fun n =>
    (le_max_right Npos n).trans (hk n)
  have hkpos : ∀ n, 0 < r (k n) := fun n =>
    lt_of_lt_of_le zero_lt_one (hNpos _ ((le_max_left Npos n).trans (hk n)))
  have hk_tendsto : Tendsto k atTop atTop := by
    rw [Filter.tendsto_atTop]
    intro N
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    exact hn.trans (hkN n)
  have hxball : ∀ n, x n ∈ Metric.closedBall (0 : E) M := by
    intro n
    simpa [Metric.mem_closedBall, dist_zero_right] using hx n
  obtain ⟨x0, _hx0, psi, hpsi, hxconv⟩ :=
    (ProperSpace.isCompact_closedBall (0 : E) M).tendsto_subseq hxball
  have hindex : Tendsto (fun n => k (psi n)) atTop atTop :=
    hk_tendsto.comp hpsi.tendsto_atTop
  have hrsub : Tendsto (fun n => r (k (psi n))) atTop atTop :=
    hr.comp hindex
  have hinv : Tendsto (fun n => (r (k (psi n)))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hrsub
  have hinvpos : ∀ n, 0 < (r (k (psi n)))⁻¹ := fun n => inv_pos.mpr (hkpos _)
  have hquot := hφ x0 (x ∘ psi) (fun n => (r (k (psi n)))⁻¹)
    hxconv hinv hinvpos
  have hquot' : Tendsto
      (fun n => r (k (psi n)) •
        (φ (θ + (r (k (psi n)))⁻¹ • x (psi n)) - φ θ))
      atTop (𝓝 (φ' x0)) := by
    simpa [Function.comp_def] using hquot
  have hderiv : Tendsto (fun n => φ' (x (psi n))) atTop (𝓝 (φ' x0)) :=
    (hφ'.tendsto x0).comp hxconv
  have hdiff : Tendsto
      (fun n => r (k (psi n)) •
        (φ (θ + (r (k (psi n)))⁻¹ • x (psi n)) - φ θ) - φ' (x (psi n)))
      atTop (𝓝 0) := by
    simpa using hquot'.sub hderiv
  have hsmall : ∀ᶠ n in atTop,
      ‖r (k (psi n)) •
        (φ (θ + (r (k (psi n)))⁻¹ • x (psi n)) - φ θ) - φ' (x (psi n))‖ <
        epsilon :=
    (NormedAddGroup.tendsto_nhds_zero.mp hdiff) epsilon hepsilon
  obtain ⟨n, hn⟩ := hsmall.exists
  exact (not_lt_of_ge (hbad (psi n))) hn

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Given [a finite-dimensional estimator sequence and target](hyp:Tn,θ), [a diverging
rate](hyp:r,hr), [measurable rescaled input and transformed deviations](hyp:hTn,hφTn),
[a continuous Hadamard directional derivative `φ'` of `φ` at `θ`](hyp:hφ,hφ'), and [weak
convergence of the rescaled input deviations to `Q`](hyp:hCLT), [the rescaled transformed
deviations converge weakly to the pushforward of `Q` under `φ'`](goal).

This is the finite-dimensional, all-directions specialization of the nonlinear
Hadamard directional delta method in Shapiro (1991), Theorem 2.1, and
Fang--Santos (2019), Theorem 2.1. The directional derivative may be nonlinear,
but this formal statement assumes its continuity separately. Van der Vaart
(1998), Theorem 20.8 covers the fully Hadamard-differentiable linear special
case, not this nonlinear extension. The conclusion is definitionally the
library's `Tendsto_dist_vec` form, so it composes directly with Slutsky and
continuous-mapping results. -/
theorem functionalDeltaMethod
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (Tn : ℕ → Ω → E) (θ : E) (φ : E → F) (φ' : E → F)
    (Q : Measure E) [IsProbabilityMeasure Q]
    (r : ℕ → ℝ) (hr : Tendsto r atTop atTop)
    (hTn : ∀ n, AEMeasurable (fun omega => r n • (Tn n omega - θ)) μ)
    (hφTn : ∀ n, AEMeasurable (fun omega => r n • (φ (Tn n omega) - φ θ)) μ)
    (hφ : HasHadamardDirDerivAt φ φ' θ) (hφ' : Continuous φ')
    (hCLT : Tendsto_dist_vec (fun n omega => r n • (Tn n omega - θ)) Q μ hTn) :
    Tendsto (β := ProbabilityMeasure F)
      (fun n =>
        ⟨μ.map (fun omega => r n • (φ (Tn n omega) - φ θ)),
          Measure.isProbabilityMeasure_map (hφTn n)⟩)
      atTop
      (𝓝 ⟨Q.map φ',
        Measure.isProbabilityMeasure_map hφ'.measurable.aemeasurable⟩) := by
  let Sn : ℕ → Ω → E := fun n omega => r n • (Tn n omega - θ)
  let fn : ℕ → E → F := fun n h =>
    r n • (φ (θ + (r n)⁻¹ • h) - φ θ)
  have hrecover : ∀ n omega, fn n (Sn n omega) =
      r n • (φ (Tn n omega) - φ θ) := by
    intro n omega
    by_cases hrzero : r n = 0
    · simp [fn, Sn, hrzero]
    · simp only [fn, Sn, smul_smul, inv_mul_cancel₀ hrzero, one_smul,
        add_sub_cancel]
  have hfnSn : ∀ n, AEMeasurable (fun omega => fn n (Sn n omega)) μ := fun n =>
    (hφTn n).congr (ae_of_all _ fun omega => (hrecover n omega).symm)
  have hSn : ∀ n, AEMeasurable (Sn n) μ := by
    simpa [Sn] using hTn
  have hSnCLT : Tendsto_dist_vec Sn Q μ hSn := by
    simpa [Sn] using hCLT
  have hUniform : ∀ (M : ℝ) (epsilon : ℝ), 0 < epsilon →
      ∀ᶠ n in atTop, ∀ h : E, ‖h‖ ≤ M → ‖fn n h - φ' h‖ < epsilon := by
    simpa [fn] using hφ.uniform_on_bounded hφ' r hr
  have hmap := Tendsto_dist_vec.map_varying_of_uniform_on_bounded
    hφ' hSn hfnSn hSnCLT hUniform
  refine hmap.congr' ?_
  filter_upwards with n
  apply Subtype.ext
  exact Measure.map_congr (ae_of_all _ fun omega => hrecover n omega)

/-! ## Maximum and minimum at arbitrary base points -/

/-- Given [a probability law on pairs](hyp:Q) and [a base point](hyp:a,b), [the pushforward
under the maximum's directional derivative is a probability law](goal). -/
instance instIsProbabilityMeasure_map_maxDirDeriv
    (Q : Measure (ℝ × ℝ)) [IsProbabilityMeasure Q] (a b : ℝ) :
    IsProbabilityMeasure (Q.map (maxDirDeriv a b)) :=
  Measure.isProbabilityMeasure_map
    (continuous_maxDirDeriv a b).measurable.aemeasurable

/-- Given [a probability law on pairs](hyp:Q) and [a base point](hyp:a,b), [the pushforward
under the minimum's directional derivative is a probability law](goal). -/
instance instIsProbabilityMeasure_map_minDirDeriv
    (Q : Measure (ℝ × ℝ)) [IsProbabilityMeasure Q] (a b : ℝ) :
    IsProbabilityMeasure (Q.map (minDirDeriv a b)) :=
  Measure.isProbabilityMeasure_map
    (continuous_minDirDeriv a b).measurable.aemeasurable

/-- Given [two estimator sequences and their target coordinates](hyp:an,bn,a,b), [a diverging
rate](hyp:r,hr), [measurable rescaled input and maximum deviations](hyp:hSn,hMax), and [weak
convergence of the rescaled input pair to `Q`](hyp:hCLT), [the rescaled maximum converges to
the pushforward of `Q` under the maximum's directional derivative at `(a,b)`](goal).

This includes ties, where the derivative is coordinatewise maximum, and
off-diagonal points, where it selects the locally larger coordinate. -/
theorem deltaMethod_max_rate
    (an bn : ℕ → Ω → ℝ) (a b : ℝ) (r : ℕ → ℝ)
    (hr : Tendsto r atTop atTop)
    (Q : Measure (ℝ × ℝ)) [IsProbabilityMeasure Q]
    (hSn : ∀ n, AEMeasurable
      (fun omega => r n • ((an n omega, bn n omega) - (a, b))) μ)
    (hMax : ∀ n, AEMeasurable
      (fun omega => r n * (max (an n omega) (bn n omega) - max a b)) μ)
    (hCLT : Tendsto_dist_vec
      (fun n omega => r n • ((an n omega, bn n omega) - (a, b))) Q μ hSn) :
    Tendsto_dist
      (fun n omega => r n * (max (an n omega) (bn n omega) - max a b))
      (Q.map (maxDirDeriv a b)) μ hMax := by
  apply (Tendsto_dist_iff _ _ _ hMax).2
  simpa [smul_eq_mul] using functionalDeltaMethod
    (Tn := fun n omega => (an n omega, bn n omega))
    (θ := (a, b)) (φ := fun z : ℝ × ℝ => max z.1 z.2)
    (φ' := maxDirDeriv a b) Q r hr hSn hMax
    (hasHadamardDirDerivAt_max a b) (continuous_maxDirDeriv a b) hCLT

/-- Given [two estimator sequences and their target coordinates](hyp:an,bn,a,b), [a diverging
rate](hyp:r,hr), [measurable rescaled input and minimum deviations](hyp:hSn,hMin), and [weak
convergence of the rescaled input pair to `Q`](hyp:hCLT), [the rescaled minimum converges to
the pushforward of `Q` under the minimum's directional derivative at `(a,b)`](goal).

This includes ties, where the derivative is coordinatewise minimum, and
off-diagonal points, where it selects the locally smaller coordinate. -/
theorem deltaMethod_min_rate
    (an bn : ℕ → Ω → ℝ) (a b : ℝ) (r : ℕ → ℝ)
    (hr : Tendsto r atTop atTop)
    (Q : Measure (ℝ × ℝ)) [IsProbabilityMeasure Q]
    (hSn : ∀ n, AEMeasurable
      (fun omega => r n • ((an n omega, bn n omega) - (a, b))) μ)
    (hMin : ∀ n, AEMeasurable
      (fun omega => r n * (min (an n omega) (bn n omega) - min a b)) μ)
    (hCLT : Tendsto_dist_vec
      (fun n omega => r n • ((an n omega, bn n omega) - (a, b))) Q μ hSn) :
    Tendsto_dist
      (fun n omega => r n * (min (an n omega) (bn n omega) - min a b))
      (Q.map (minDirDeriv a b)) μ hMin := by
  apply (Tendsto_dist_iff _ _ _ hMin).2
  simpa [smul_eq_mul] using functionalDeltaMethod
    (Tn := fun n omega => (an n omega, bn n omega))
    (θ := (a, b)) (φ := fun z : ℝ × ℝ => min z.1 z.2)
    (φ' := minDirDeriv a b) Q r hr hSn hMin
    (hasHadamardDirDerivAt_min a b) (continuous_minDirDeriv a b) hCLT

/-- Given [two estimator sequences and their target coordinates](hyp:an,bn,a,b), [measurable
square-root-rescaled input and maximum deviations](hyp:hSn,hMax), and [weak convergence of the
rescaled input pair to `Q`](hyp:hCLT), [the square-root-rescaled maximum converges to the
pushforward of `Q` under the maximum's directional derivative at `(a,b)`](goal). -/
theorem deltaMethod_max
    (an bn : ℕ → Ω → ℝ) (a b : ℝ)
    (Q : Measure (ℝ × ℝ)) [IsProbabilityMeasure Q]
    (hSn : ∀ (n : ℕ), AEMeasurable
      (fun omega => Real.sqrt (n : ℝ) • ((an n omega, bn n omega) - (a, b))) μ)
    (hMax : ∀ (n : ℕ), AEMeasurable (fun omega =>
      Real.sqrt (n : ℝ) * (max (an n omega) (bn n omega) - max a b)) μ)
    (hCLT : Tendsto_dist_vec
      (fun (n : ℕ) omega =>
        Real.sqrt (n : ℝ) • ((an n omega, bn n omega) - (a, b)))
      Q μ hSn) :
    Tendsto_dist (fun (n : ℕ) omega =>
      Real.sqrt (n : ℝ) * (max (an n omega) (bn n omega) - max a b))
      (Q.map (maxDirDeriv a b)) μ hMax := by
  exact deltaMethod_max_rate an bn a b (fun n => Real.sqrt (n : ℝ))
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop) Q hSn hMax hCLT

/-- Given [two estimator sequences and their target coordinates](hyp:an,bn,a,b), [measurable
square-root-rescaled input and minimum deviations](hyp:hSn,hMin), and [weak convergence of the
rescaled input pair to `Q`](hyp:hCLT), [the square-root-rescaled minimum converges to the
pushforward of `Q` under the minimum's directional derivative at `(a,b)`](goal). -/
theorem deltaMethod_min
    (an bn : ℕ → Ω → ℝ) (a b : ℝ)
    (Q : Measure (ℝ × ℝ)) [IsProbabilityMeasure Q]
    (hSn : ∀ (n : ℕ), AEMeasurable
      (fun omega => Real.sqrt (n : ℝ) • ((an n omega, bn n omega) - (a, b))) μ)
    (hMin : ∀ (n : ℕ), AEMeasurable (fun omega =>
      Real.sqrt (n : ℝ) * (min (an n omega) (bn n omega) - min a b)) μ)
    (hCLT : Tendsto_dist_vec
      (fun (n : ℕ) omega =>
        Real.sqrt (n : ℝ) • ((an n omega, bn n omega) - (a, b)))
      Q μ hSn) :
    Tendsto_dist (fun (n : ℕ) omega =>
      Real.sqrt (n : ℝ) * (min (an n omega) (bn n omega) - min a b))
      (Q.map (minDirDeriv a b)) μ hMin := by
  exact deltaMethod_min_rate an bn a b (fun n => Real.sqrt (n : ℝ))
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop) Q hSn hMin hCLT

end Causalean.Stat
