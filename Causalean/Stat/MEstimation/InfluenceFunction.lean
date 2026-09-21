/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Influence Functions (data layer)

Shared data structure packaging three regularity properties commonly imposed on
an influence function: measurability, mean-zero, and finite second moment. Mirrors
`def:sp-pathwise-diff` from `doc/basic_concepts/Semi-parametric Inference/
semi_parametric_inference.tex` at the *assumption* level: pathwise
differentiability and efficient-influence-function derivations are supplied by
the caller rather than derived in this data-layer structure.

Z-estimator, smooth Z-estimator, and GMM regularity packages construct this
predicate for their canonical influence functions; family-specific covariance
identities remain beside the corresponding estimator theory.
-/

module
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-!
# Influence-function data layer

This module defines `InfluenceFunction`, the common data-layer predicate used
by estimator families to record measurability, mean zero, and an integrable
squared norm. It does not encode pathwise differentiability or efficiency.
-/

@[expose] public section

namespace Causalean.Stat

open MeasureTheory

variable {X : Type*} [MeasurableSpace X]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- For [a sampling law](hyp:P) and [a candidate function](hyp:ψ), the
influence-function regularity predicate records that the candidate is
measurable, mean-zero, and square-integrable.

This is a data structure, not a derivation: the user supplies `ψ` and the
witnesses. Pathwise differentiability and the EIF characterisation are
deferred. -/
structure InfluenceFunction (P : Measure X) (ψ : X → E) : Prop where
  /-- `ψ` is measurable. -/
  measurable : Measurable ψ
  /-- `ψ` has mean zero under `P`. -/
  mean_zero  : ∫ x, ψ x ∂P = 0
  /-- `ψ` has finite second moment: `‖ψ‖² ∈ L¹(P)`. -/
  finite_var : Integrable (fun x => ‖ψ x‖^2) P

end Causalean.Stat
