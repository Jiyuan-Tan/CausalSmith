/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Topology.Order.Compact

/-!
# Uniform compact-correspondence exclusion

This module gives a compactness argument for a family of feasible candidate sets indexed by a
parameter.  A continuous residual that can vanish only at the parameter's reference candidate has
a single positive tolerance excluding every candidate outside the parameter-dependent reference
neighborhood; the result also specializes to finite real square matrices with their Euclidean
operator-norm metric.
-/

noncomputable section

open Set
open scoped Matrix.Norms.L2Operator

namespace Causalean.Mathlib.Topology

/-- The feasible parameter-candidate pairs whose candidate lies at least its parameter's prescribed
distance from the reference candidate. -/
def farFeasibleSet {P X : Type*} [TopologicalSpace P] [PseudoMetricSpace X]
    (K : Set (P × X)) (x₀ : P → X) (ρ : P → ℝ) : Set (P × X) :=
  {z | z ∈ K ∧ ρ z.1 ≤ dist z.2 (x₀ z.1)}

/-- A positive residual threshold attained on the far part of a parameter-indexed feasible
correspondence and valid uniformly over all its far pairs. -/
structure UniformPositiveExclusionRadius {P X : Type*} [TopologicalSpace P]
    [PseudoMetricSpace X] (K : Set (P × X)) (x₀ : P → X) (ρ : P → ℝ)
    (r : P × X → ℝ) where
  /-- The parameter of a pair attaining the minimum residual. -/
  parameter : P
  /-- The candidate of a pair attaining the minimum residual. -/
  candidate : X
  /-- The attaining pair is feasible and lies outside its reference neighborhood. -/
  mem_far : (parameter, candidate) ∈ farFeasibleSet K x₀ ρ
  /-- The uniform positive residual threshold. -/
  radius : ℝ
  /-- The residual threshold is strictly positive. -/
  radius_pos : 0 < radius
  /-- The residual at the attaining pair equals the threshold. -/
  attained : r (parameter, candidate) = radius
  /-- Every feasible pair outside its reference neighborhood has residual at least the threshold. -/
  lower_bound : ∀ z ∈ farFeasibleSet K x₀ ρ, radius ≤ r z

/-- For [a feasible correspondence](hyp:K), [a reference section](hyp:x₀), and [a radius
function](hyp:ρ), if [the correspondence is compact](hyp:hK), [the reference section is
continuous](hyp:hx₀), and [the radius function is continuous](hyp:hρ), then [the feasible pairs
outside their reference neighborhoods form a closed set](goal). -/
theorem isClosed_farFeasibleSet {P X : Type*} [TopologicalSpace P] [T2Space P]
    [MetricSpace X] (K : Set (P × X)) (x₀ : P → X) (ρ : P → ℝ)
    (hK : IsCompact K) (hx₀ : Continuous x₀) (hρ : Continuous ρ) :
    IsClosed (farFeasibleSet K x₀ ρ) := by
  exact hK.isClosed.inter <|
    isClosed_le (hρ.comp continuous_fst) <|
      continuous_snd.dist (hx₀.comp continuous_fst)

/-- For [a feasible correspondence](hyp:K), [a reference section](hyp:x₀), and [a radius
function](hyp:ρ), if [the correspondence is compact](hyp:hK) and [its far part is closed]
(hyp:hfar), then [the far part is compact](goal). -/
theorem isCompact_farFeasibleSet_of_isClosed {P X : Type*} [TopologicalSpace P]
    [PseudoMetricSpace X] (K : Set (P × X)) (x₀ : P → X) (ρ : P → ℝ)
    (hK : IsCompact K) (hfar : IsClosed (farFeasibleSet K x₀ ρ)) :
    IsCompact (farFeasibleSet K x₀ ρ) := by
  exact hK.of_isClosed_subset hfar fun _ hz => hz.1

/-- For [a feasible correspondence](hyp:K), [a reference section](hyp:x₀), [a residual
function](hyp:r), and [a radius function](hyp:ρ), if [the correspondence is compact](hyp:hK),
[its far part is closed](hyp:hfar_closed), [that far part is nonempty](hyp:hfar_nonempty), [the
residual is continuous](hyp:hr_cont), [the residual is nonnegative on feasible pairs](hyp:hr_nonneg),
[a zero residual identifies the reference candidate](hyp:hr_zero), and [every radius is strictly
positive](hyp:hρ_pos), then [the far part has a strictly positive attained residual minimum](goal). -/
theorem exists_uniformPositiveExclusionRadius_of_isClosed
    {P X : Type*} [TopologicalSpace P] [PseudoMetricSpace X]
    (K : Set (P × X)) (x₀ : P → X) (r : P × X → ℝ) (ρ : P → ℝ)
    (hK : IsCompact K) (hfar_closed : IsClosed (farFeasibleSet K x₀ ρ))
    (hfar_nonempty : (farFeasibleSet K x₀ ρ).Nonempty)
    (hr_cont : Continuous r) (hr_nonneg : ∀ z ∈ K, 0 ≤ r z)
    (hr_zero : ∀ p x, (p, x) ∈ K → r (p, x) = 0 → x = x₀ p)
    (hρ_pos : ∀ p, 0 < ρ p) :
    Nonempty (UniformPositiveExclusionRadius K x₀ ρ r) := by
  have hcompact : IsCompact (farFeasibleSet K x₀ ρ) :=
    isCompact_farFeasibleSet_of_isClosed K x₀ ρ hK hfar_closed
  obtain ⟨⟨p, x⟩, hx, hmin⟩ :=
    hcompact.exists_isMinOn hfar_nonempty hr_cont.continuousOn
  have hnonneg : 0 ≤ r (p, x) := hr_nonneg (p, x) hx.1
  have hpos : 0 < r (p, x) := lt_of_le_of_ne hnonneg fun hzero => by
    have heq : x = x₀ p := hr_zero p x hx.1 hzero.symm
    have hnonpos : ρ p ≤ 0 := by
      simpa [heq] using hx.2
    exact (not_lt_of_ge hnonpos) (hρ_pos p)
  exact ⟨{
    parameter := p
    candidate := x
    mem_far := hx
    radius := r (p, x)
    radius_pos := hpos
    attained := rfl
    lower_bound := fun z hz => hmin hz
  }⟩

/-- For [a feasible correspondence](hyp:K), [a reference section](hyp:x₀), [a residual
function](hyp:r), and [a radius function](hyp:ρ), if [the correspondence is compact](hyp:hK),
[the reference section is continuous](hyp:hx₀), [the residual is continuous](hyp:hr_cont), [the
radius function is continuous](hyp:hρ_cont), [every radius is strictly positive](hyp:hρ_pos), [the
residual is nonnegative on feasible pairs](hyp:hr_nonneg), and [a zero residual identifies the
reference candidate](hyp:hr_zero), then [either no feasible pair is outside its reference
neighborhood or that far part has a strictly positive attained residual minimum](goal). -/
theorem uniformCompactCorrespondence_dichotomy
    {P X : Type*} [TopologicalSpace P] [T2Space P] [MetricSpace X]
    (K : Set (P × X)) (x₀ : P → X) (r : P × X → ℝ) (ρ : P → ℝ)
    (hK : IsCompact K) (hx₀ : Continuous x₀) (hr_cont : Continuous r)
    (hρ_cont : Continuous ρ) (hρ_pos : ∀ p, 0 < ρ p)
    (hr_nonneg : ∀ z ∈ K, 0 ≤ r z)
    (hr_zero : ∀ p x, (p, x) ∈ K → r (p, x) = 0 → x = x₀ p) :
    farFeasibleSet K x₀ ρ = ∅ ∨
      Nonempty (UniformPositiveExclusionRadius K x₀ ρ r) := by
  have hfar_closed : IsClosed (farFeasibleSet K x₀ ρ) :=
    isClosed_farFeasibleSet K x₀ ρ hK hx₀ hρ_cont
  rcases eq_empty_or_nonempty (farFeasibleSet K x₀ ρ) with hfar | hfar
  · exact Or.inl hfar
  · exact Or.inr <|
      exists_uniformPositiveExclusionRadius_of_isClosed K x₀ r ρ hK hfar_closed hfar
        hr_cont hr_nonneg hr_zero hρ_pos

/-- For [a feasible correspondence](hyp:K), [a reference section](hyp:x₀), [a residual
function](hyp:r), and [a radius function](hyp:ρ), if [the correspondence is compact](hyp:hK),
[the reference section is continuous](hyp:hx₀), [the residual is continuous](hyp:hr_cont), [the
radius function is continuous](hyp:hρ_cont), [every radius is strictly positive](hyp:hρ_pos), [the
residual is nonnegative on feasible pairs](hyp:hr_nonneg), and [a zero residual identifies the
reference candidate](hyp:hr_zero), then [either the far part is empty or a far pair and its
strictly positive attained residual minimum are supplied explicitly](goal). -/
theorem uniformCompactCorrespondence_dichotomy_explicit
    {P X : Type*} [TopologicalSpace P] [T2Space P] [MetricSpace X]
    (K : Set (P × X)) (x₀ : P → X) (r : P × X → ℝ) (ρ : P → ℝ)
    (hK : IsCompact K) (hx₀ : Continuous x₀) (hr_cont : Continuous r)
    (hρ_cont : Continuous ρ) (hρ_pos : ∀ p, 0 < ρ p)
    (hr_nonneg : ∀ z ∈ K, 0 ≤ r z)
    (hr_zero : ∀ p x, (p, x) ∈ K → r (p, x) = 0 → x = x₀ p) :
    farFeasibleSet K x₀ ρ = ∅ ∨
      ∃ pStar xStar ε₀, (pStar, xStar) ∈ farFeasibleSet K x₀ ρ ∧ 0 < ε₀ ∧
        r (pStar, xStar) = ε₀ ∧ ∀ z ∈ farFeasibleSet K x₀ ρ, ε₀ ≤ r z := by
  rcases uniformCompactCorrespondence_dichotomy K x₀ r ρ hK hx₀ hr_cont hρ_cont
      hρ_pos hr_nonneg hr_zero with hfar | hNonempty
  · exact Or.inl hfar
  · obtain ⟨h⟩ := hNonempty
    exact Or.inr ⟨h.parameter, h.candidate, h.radius, h.mem_far, h.radius_pos,
      h.attained, h.lower_bound⟩

/-- If [a uniform positive exclusion radius is available](hyp:h), [a candidate pair is feasible]
(hyp:hK), and [its residual is below that radius](hyp:hr), then [the candidate lies strictly
inside its parameter-dependent reference neighborhood](goal). -/
theorem UniformPositiveExclusionRadius.dist_lt_of_residual_lt
    {P X : Type*} [TopologicalSpace P] [PseudoMetricSpace X]
    {K : Set (P × X)} {x₀ : P → X} {ρ : P → ℝ} {r : P × X → ℝ}
    (h : UniformPositiveExclusionRadius K x₀ ρ r) {p : P} {x : X}
    (hK : (p, x) ∈ K) (hr : r (p, x) < h.radius) :
    dist x (x₀ p) < ρ p := by
  by_contra hdist
  have hfar : (p, x) ∈ farFeasibleSet K x₀ ρ := ⟨hK, le_of_not_gt hdist⟩
  exact (not_lt_of_ge (h.lower_bound (p, x) hfar)) hr

/-- If [a uniform positive exclusion radius is available](hyp:h), [a candidate pair is feasible]
(hyp:hK), and [its residual is at most half that radius](hyp:hr), then [the candidate lies strictly
inside its parameter-dependent reference neighborhood](goal). -/
theorem UniformPositiveExclusionRadius.dist_lt_of_residual_le_half
    {P X : Type*} [TopologicalSpace P] [PseudoMetricSpace X]
    {K : Set (P × X)} {x₀ : P → X} {ρ : P → ℝ} {r : P × X → ℝ}
    (h : UniformPositiveExclusionRadius K x₀ ρ r) {p : P} {x : X}
    (hK : (p, x) ∈ K) (hr : r (p, x) ≤ h.radius / 2) :
    dist x (x₀ p) < ρ p := by
  apply h.dist_lt_of_residual_lt hK
  exact lt_of_le_of_lt hr (div_lt_self h.radius_pos (by norm_num))

/-- For [a feasible correspondence](hyp:K), [a reference section](hyp:x₀), [a residual
function](hyp:r), and [a radius function](hyp:ρ), if [the correspondence is compact](hyp:hK),
[the reference section is continuous](hyp:hx₀), [the residual is continuous](hyp:hr_cont), [the
radius function is continuous](hyp:hρ_cont), [every radius is strictly positive](hyp:hρ_pos), [the
residual is nonnegative on feasible pairs](hyp:hr_nonneg), and [a zero residual identifies the
reference candidate](hyp:hr_zero), then [one positive tolerance makes every feasible pair with
smaller residual lie strictly inside its own reference neighborhood](goal). -/
theorem exists_uniformExclusionTolerance_lt
    {P X : Type*} [TopologicalSpace P] [T2Space P] [MetricSpace X]
    (K : Set (P × X)) (x₀ : P → X) (r : P × X → ℝ) (ρ : P → ℝ)
    (hK : IsCompact K) (hx₀ : Continuous x₀) (hr_cont : Continuous r)
    (hρ_cont : Continuous ρ) (hρ_pos : ∀ p, 0 < ρ p)
    (hr_nonneg : ∀ z ∈ K, 0 ≤ r z)
    (hr_zero : ∀ p x, (p, x) ∈ K → r (p, x) = 0 → x = x₀ p) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ p x, (p, x) ∈ K → r (p, x) < ε₀ →
      dist x (x₀ p) < ρ p := by
  rcases uniformCompactCorrespondence_dichotomy K x₀ r ρ hK hx₀ hr_cont hρ_cont
      hρ_pos hr_nonneg hr_zero with hfar | hNonempty
  · refine ⟨1, by norm_num, ?_⟩
    intro p x hpx _
    by_contra hdist
    have hx : (p, x) ∈ farFeasibleSet K x₀ ρ := ⟨hpx, le_of_not_gt hdist⟩
    rw [hfar] at hx
    exact hx.elim
  · obtain ⟨h⟩ := hNonempty
    exact ⟨h.radius, h.radius_pos, fun p x hpx hr =>
      h.dist_lt_of_residual_lt hpx hr⟩

/-- For [a feasible correspondence](hyp:K), [a reference section](hyp:x₀), [a residual
function](hyp:r), and [a radius function](hyp:ρ), if [the correspondence is compact](hyp:hK),
[the reference section is continuous](hyp:hx₀), [the residual is continuous](hyp:hr_cont), [the
radius function is continuous](hyp:hρ_cont), [every radius is strictly positive](hyp:hρ_pos), [the
residual is nonnegative on feasible pairs](hyp:hr_nonneg), and [a zero residual identifies the
reference candidate](hyp:hr_zero), then [one positive tolerance makes every feasible pair with
residual at most that tolerance lie strictly inside its own reference neighborhood](goal). -/
theorem exists_uniformExclusionTolerance_le
    {P X : Type*} [TopologicalSpace P] [T2Space P] [MetricSpace X]
    (K : Set (P × X)) (x₀ : P → X) (r : P × X → ℝ) (ρ : P → ℝ)
    (hK : IsCompact K) (hx₀ : Continuous x₀) (hr_cont : Continuous r)
    (hρ_cont : Continuous ρ) (hρ_pos : ∀ p, 0 < ρ p)
    (hr_nonneg : ∀ z ∈ K, 0 ≤ r z)
    (hr_zero : ∀ p x, (p, x) ∈ K → r (p, x) = 0 → x = x₀ p) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ p x, (p, x) ∈ K → r (p, x) ≤ ε₀ →
      dist x (x₀ p) < ρ p := by
  rcases uniformCompactCorrespondence_dichotomy K x₀ r ρ hK hx₀ hr_cont hρ_cont
      hρ_pos hr_nonneg hr_zero with hfar | hNonempty
  · refine ⟨1, by norm_num, ?_⟩
    intro p x hpx _
    by_contra hdist
    have hx : (p, x) ∈ farFeasibleSet K x₀ ρ := ⟨hpx, le_of_not_gt hdist⟩
    rw [hfar] at hx
    exact hx.elim
  · obtain ⟨h⟩ := hNonempty
    refine ⟨h.radius / 2, half_pos h.radius_pos, ?_⟩
    intro p x hpx hr
    exact h.dist_lt_of_residual_le_half hpx hr

/-- A finite real square matrix, equipped in this module with the Euclidean operator norm and its
induced metric. -/
abbrev RealSquareMatrix (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

/-- For [a parameter-indexed matrix correspondence](hyp:K), [a reference matrix section](hyp:B₀),
[a matrix residual](hyp:r), and [a radius function](hyp:ρ), if [the correspondence is compact]
(hyp:hK), [the reference matrices vary continuously](hyp:hB₀), [the residual is continuous]
(hyp:hr_cont), [the radius function is continuous](hyp:hρ_cont), [every radius is strictly
positive](hyp:hρ_pos), [the residual is nonnegative on feasible pairs](hyp:hr_nonneg), and [a
zero residual identifies the reference matrix](hyp:hr_zero), then [either no feasible matrix is
operator-norm far from its reference or the far matrices have a strictly positive attained uniform
residual minimum](goal). -/
theorem realSquareMatrix_uniformCompactCorrespondence_dichotomy
    {P : Type*} [TopologicalSpace P] [T2Space P] {d : ℕ}
    (K : Set (P × RealSquareMatrix d)) (B₀ : P → RealSquareMatrix d)
    (r : P × RealSquareMatrix d → ℝ) (ρ : P → ℝ)
    (hK : IsCompact K) (hB₀ : Continuous B₀) (hr_cont : Continuous r)
    (hρ_cont : Continuous ρ) (hρ_pos : ∀ p, 0 < ρ p)
    (hr_nonneg : ∀ z ∈ K, 0 ≤ r z)
    (hr_zero : ∀ p B, (p, B) ∈ K → r (p, B) = 0 → B = B₀ p) :
    farFeasibleSet K B₀ ρ = ∅ ∨
      Nonempty (UniformPositiveExclusionRadius K B₀ ρ r) := by
  exact uniformCompactCorrespondence_dichotomy K B₀ r ρ hK hB₀ hr_cont hρ_cont hρ_pos
    hr_nonneg hr_zero

/-- For [a parameter-indexed matrix correspondence](hyp:K), [a reference matrix section](hyp:B₀),
[a matrix residual](hyp:r), and [a radius function](hyp:ρ), if [the correspondence is compact]
(hyp:hK), [the reference matrices vary continuously](hyp:hB₀), [the residual is continuous]
(hyp:hr_cont), [the radius function is continuous](hyp:hρ_cont), [every radius is strictly
positive](hyp:hρ_pos), [the residual is nonnegative on feasible pairs](hyp:hr_nonneg), and [a
zero residual identifies the reference matrix](hyp:hr_zero), then [one positive residual tolerance
makes every feasible matrix within that tolerance lie strictly inside its parameter-dependent
operator-norm reference ball](goal). -/
theorem exists_realSquareMatrix_uniformExclusionTolerance
    {P : Type*} [TopologicalSpace P] [T2Space P] {d : ℕ}
    (K : Set (P × RealSquareMatrix d)) (B₀ : P → RealSquareMatrix d)
    (r : P × RealSquareMatrix d → ℝ) (ρ : P → ℝ)
    (hK : IsCompact K) (hB₀ : Continuous B₀) (hr_cont : Continuous r)
    (hρ_cont : Continuous ρ) (hρ_pos : ∀ p, 0 < ρ p)
    (hr_nonneg : ∀ z ∈ K, 0 ≤ r z)
    (hr_zero : ∀ p B, (p, B) ∈ K → r (p, B) = 0 → B = B₀ p) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ p B, (p, B) ∈ K → r (p, B) ≤ ε₀ →
      ‖B - B₀ p‖ < ρ p := by
  simpa only [dist_eq_norm] using
    (exists_uniformExclusionTolerance_le K B₀ r ρ hK hB₀ hr_cont hρ_cont hρ_pos
      hr_nonneg hr_zero)

end Causalean.Mathlib.Topology
