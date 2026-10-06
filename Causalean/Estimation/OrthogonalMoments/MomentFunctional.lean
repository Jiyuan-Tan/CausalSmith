/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Abstract moment functional bundle for the general DML framework

This file defines the abstract `GeneralMoment` structure which packages a
moment functional `m : H → Z → ℝ → ℝ` together with the truth nuisance
`η₀ : H`, the target parameter `θ₀ : ℝ`, the perturbation set `H_ε ⊆ H`,
and the bilinear seminorm pair `(ρ₁, ρ₂)` used to express product-rate
remainders.

-/

module
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.Algebra.Module.Basic

/-! # Abstract Moment Functionals

This file defines the moment-functional interface used by the double machine
learning layer. The interface records the observed-data moment, the true
nuisance and scalar target, the local perturbation set, bilinear seminorms for
product-rate bounds, and a nonzero linearization scale. Concrete
double-machine-learning instances reduce to filling this interface, which
centralizes the generic asymptotic-linearity machinery. -/

@[expose] public section

namespace Causalean
namespace Estimation
namespace OrthogonalMoments

open MeasureTheory

/-- For [randomness and observed-data spaces with measures and a real nuisance
vector space](hyp:Ω,μ,Z,P_Z,H), a general scaled moment system
bundles [a score function](hyp:m), [a truth nuisance](hyp:η₀), [a truth
parameter](hyp:θ₀), [an admissible perturbation set](hyp:H_ε), [two
error gauges](hyp:ρ₁,ρ₂), and [a caller-supplied linearization
scale](hyp:linScale), subject to [score measurability](hyp:m_meas), [truth
membership in the perturbation set](hyp:η₀_mem), and [nonvanishing of the
scale](hyp:linScale_ne_zero).

The interface is algebraic: `linScale` is a caller-supplied scale and is not
asserted here to be a derivative of the population moment. `LinearMoment`
below adds an equality that identifies this scale with the coefficient mean.

* `m η z θ`     — the moment functional, parametric in nuisance `η`, data `z`,
                  and parameter `θ`.
* `η₀`          — the truth nuisance.
* `θ₀`          — the truth parameter.
* `H_ε`         — perturbation set; nuisance estimates are required to live here.
* `ρ₁ η η'`     — first bilinear seminorm slot (e.g., outcome-regression L²).
* `ρ₂ η η'`     — second bilinear seminorm slot (e.g., propensity L²).
* `m_meas`      — joint measurability witness for `m η · θ`.
* `η₀_mem`      — `η₀ ∈ H_ε`.
* `linScale`          — caller-supplied scale used by the one-step formulas.
* `linScale_ne_zero`  — nonzero witness, so its reciprocal is well-defined. -/
structure GeneralMoment
    (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (Z : Type*) [MeasurableSpace Z] (P_Z : MeasureTheory.Measure Z)
    (H : Type*) [AddCommGroup H] [Module ℝ H] where
  m : H → Z → ℝ → ℝ
  η₀ : H
  θ₀ : ℝ
  H_ε : Set H
  ρ₁ : H → H → NNReal
  ρ₂           : H → H → NNReal
  m_meas       : ∀ η θ, Measurable (fun z => m η z θ)
  η₀_mem       : η₀ ∈ H_ε
  linScale         : ℝ
  linScale_ne_zero : linScale ≠ 0

namespace GeneralMoment

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
         {Z : Type*} [MeasurableSpace Z] {P_Z : MeasureTheory.Measure Z}
         {H : Type*} [AddCommGroup H] [Module ℝ H]

/-- For [a general moment system](hyp:M), the [inverse linearization scale](goal)
is the reciprocal of the system's nonzero caller-supplied scale.

For the AIPW linear score, the identified scale is minus one, so its reciprocal
is also minus one. -/
noncomputable def linScaleInv (M : GeneralMoment Ω μ Z P_Z H) : ℝ :=
  M.linScale⁻¹

/-- For [a general orthogonal-moment system](hyp:M), [its linearization scale
times its reciprocal equals one](goal). -/
@[simp] lemma linScale_mul_inv (M : GeneralMoment Ω μ Z P_Z H) :
    M.linScale * M.linScaleInv = 1 := by
  unfold linScaleInv
  exact mul_inv_cancel₀ M.linScale_ne_zero

end GeneralMoment

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
         {Z : Type*} [MeasurableSpace Z] {P_Z : MeasureTheory.Measure Z}
         {H : Type*} [AddCommGroup H] [Module ℝ H]

/-- For [a general moment system](hyp:M), [the mean-zero condition](goal) states
that the population expectation of its score at the true nuisance and true scalar
target is zero. -/
def MeanZero (M : GeneralMoment Ω μ Z P_Z H) : Prop :=
  ∫ z, M.m M.η₀ z M.θ₀ ∂P_Z = 0

/-- For [a general moment system](hyp:M), [perturbation-set segment closure](goal)
states that, for every nuisance value in its admissible perturbation set and every
weight in the closed unit interval, the corresponding point on the line segment
from the true nuisance to that value also belongs to the admissible set. -/
def H_ε_PerturbClosed (M : GeneralMoment Ω μ Z P_Z H) : Prop :=
  ∀ η ∈ M.H_ε, ∀ t ∈ Set.Icc (0 : ℝ) 1, M.η₀ + t • (η - M.η₀) ∈ M.H_ε

/-- For [randomness and observed-data spaces with measures and a real nuisance
vector space](hyp:Ω,μ,Z,P_Z,H), a linear moment system is a general
moment with [coefficient and constant score terms](hyp:m_a,m_b),
[measurability of those terms](hyp:m_a_meas,m_b_meas), [an affine score
decomposition](hyp:m_decomp), and [identification of the linearization scale
with the population coefficient mean](hyp:linScale_eq).

It carries the coefficient and constant terms of the linear-score
decomposition, their measurability, and the consistency condition saying that
the linearization scale is the population mean of the coefficient at the truth. AIPW is the
canonical instance with constant coefficient minus one. -/
structure LinearMoment
    (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (Z : Type*) [MeasurableSpace Z] (P_Z : MeasureTheory.Measure Z)
    (H : Type*) [AddCommGroup H] [Module ℝ H]
    extends GeneralMoment Ω μ Z P_Z H where
  m_a : H → Z → ℝ
  m_b : H → Z → ℝ
  m_a_meas : ∀ η, Measurable (m_a η)
  m_b_meas : ∀ η, Measurable (m_b η)
  m_decomp : ∀ η z θ, m η z θ = m_a η z * θ + m_b η z
  /-- The linearization scale is the population mean of the linear coefficient:
  `linScale = ∫ m_a(η₀, z) dP_Z`. -/
  linScale_eq : linScale = ∫ z, m_a η₀ z ∂P_Z

end OrthogonalMoments
end Estimation
end Causalean
