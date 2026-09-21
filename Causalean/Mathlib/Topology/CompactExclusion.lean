/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.MetricSpace.Pseudo.Constructions
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Compact exclusion away from an isolated zero

This module provides the non-effective compactness argument that turns "the only zero of a
residual is the reference point" into a positive residual margin away from that point.

* For a single problem: a continuous residual that is nonnegative on a compact candidate set and
  vanishes there only at a reference point has a strictly positive, attained minimum on the
  candidates outside any open neighborhood of that point, provided such candidates exist
  (`PositiveExclusionRadius`, `exists_positiveExclusionRadius`).
* Uniformly over a compact correspondence of parameter--candidate pairs with a continuous
  reference section and a continuous positive radius function: either no feasible pair is far
  from its reference, or a single strictly positive residual tolerance forces every feasible pair
  with smaller residual into its own reference ball (`farFeasibleSet`,
  `UniformPositiveExclusionRadius`, `uniformCompactCorrespondence_dichotomy`,
  `exists_uniformExclusionTolerance_lt`, `exists_uniformExclusionTolerance_le`).

The statements quantify over arbitrary topological parameter spaces and
(pseudo)metric candidate spaces.
-/

@[expose] public section

noncomputable section

namespace Causalean.Mathlib.Topology.CompactExclusion

/-- A positive exclusion radius is a positive lower bound for a residual on the part of
`K` outside `U`, together with a candidate where that lower bound is attained. -/
structure PositiveExclusionRadius {X : Type*} (K U : Set X) (r : X → ℝ) where
  /-- The strictly positive residual radius. -/
  radius : ℝ
  /-- The exclusion radius is strictly positive. -/
  radius_pos : 0 < radius
  /-- Every candidate in `K` outside `U` has residual at least the radius. -/
  lower_bound : ∀ x, x ∈ K → x ∉ U → radius ≤ r x
  /-- Some candidate in `K` outside `U` attains the radius. -/
  attained : ∃ x, x ∈ K ∧ x ∉ U ∧ r x = radius

/-- For [a compact candidate set](hyp:K), [an open local neighborhood](hyp:U), [a continuous
residual](hyp:r), and [a reference point](hyp:x₀), if [the candidate set is compact](hyp:hK),
[the neighborhood is open](hyp:hU), [the reference belongs to the candidate set](hyp:hxK),
[the reference belongs to the neighborhood](hyp:hxU), [the far set is nonempty](hyp:hfar),
[the residual is continuous](hyp:hr_cont),
[the residual is nonnegative on candidates](hyp:hr_nonneg),
and [its only zero among candidates is the reference](hyp:hr_zero), then [the far set has a
strictly positive attained residual minimum](goal). -/
-- Proof route: `K \ U = K ∩ Uᶜ` is compact.  Apply `IsCompact.exists_isMinOn` to `r`
-- on this nonempty far set.  Nonnegativity makes the minimum nonnegative; equality to
-- zero forces its minimizer to be `x₀`, contradicting `x₀ ∈ U`.
theorem exists_positiveExclusionRadius {X : Type*} [TopologicalSpace X]
    (K U : Set X) (r : X → ℝ) (x₀ : X)
    (hK : IsCompact K) (hU : IsOpen U) (hxK : x₀ ∈ K) (hxU : x₀ ∈ U)
    (hfar : (K \ U).Nonempty) (hr_cont : Continuous r)
    (hr_nonneg : ∀ x ∈ K, 0 ≤ r x)
    (hr_zero : ∀ x ∈ K, r x = 0 → x = x₀) :
    Nonempty (PositiveExclusionRadius K U r) := by
  have hcompact : IsCompact (K \ U) := by
    rw [Set.sdiff_eq]
    exact hK.inter_right hU.isClosed_compl
  obtain ⟨x, hx, hmin⟩ :=
    hcompact.exists_isMinOn hfar hr_cont.continuousOn
  have hxK' : x ∈ K := hx.1
  have hxU' : x ∉ U := hx.2
  have hnonneg : 0 ≤ r x := hr_nonneg x hxK'
  have hpos : 0 < r x := lt_of_le_of_ne hnonneg fun hzero => by
    have heq : x = x₀ := hr_zero x hxK' hzero.symm
    exact hxU' (heq ▸ hxU)
  exact ⟨{
    radius := r x
    radius_pos := hpos
    lower_bound := by
      intro y hyK hyU
      exact hmin ⟨hyK, hyU⟩
    attained := ⟨x, hxK', hxU', rfl⟩
  }⟩

/-! ## Uniform compact-correspondence exclusion

The declarations below extend compact exclusion from one fixed reference point to a compact
family of parameter-dependent feasible problems.  They are useful when a single residual
tolerance must keep every feasible parameter-candidate pair inside its own reference
neighborhood.
-/

/-- For [a parameter space](hyp:P), [a candidate pseudometric space](hyp:X),
[a set of feasible parameter--candidate pairs](hyp:K), [a reference candidate
assigned to each parameter](hyp:x₀), and [a real-valued radius assigned to each
parameter](hyp:ρ), the [far feasible set](goal) consists exactly of the feasible
pairs whose candidate is at least that parameter's assigned radius from its
reference candidate. -/
def farFeasibleSet {P X : Type*} [TopologicalSpace P] [PseudoMetricSpace X]
    (K : Set (P × X)) (x₀ : P → X) (ρ : P → ℝ) : Set (P × X) :=
  {z | z ∈ K ∧ ρ z.1 ≤ dist z.2 (x₀ z.1)}

/-- A uniform positive exclusion radius records a far feasible pair where the residual reaches
a strictly positive value that lower-bounds its value at every far feasible pair. -/
structure UniformPositiveExclusionRadius {P X : Type*} [TopologicalSpace P]
    [PseudoMetricSpace X] (K : Set (P × X)) (x₀ : P → X) (ρ : P → ℝ)
    (r : P × X → ℝ) where
  /-- The parameter at which the uniform residual minimum is attained. -/
  parameter : P
  /-- The candidate at which the uniform residual minimum is attained. -/
  candidate : X
  /-- The attaining parameter-candidate pair belongs to the far feasible set. -/
  mem_far : (parameter, candidate) ∈ farFeasibleSet K x₀ ρ
  /-- The uniform residual tolerance. -/
  radius : ℝ
  /-- The uniform residual tolerance is strictly positive. -/
  radius_pos : 0 < radius
  /-- The residual at the attaining pair equals the uniform residual tolerance. -/
  attained : r (parameter, candidate) = radius
  /-- The uniform residual tolerance lower-bounds the residual on the far feasible set. -/
  lower_bound : ∀ z ∈ farFeasibleSet K x₀ ρ, radius ≤ r z

/-- Given [a feasible correspondence](hyp:K), [a reference section](hyp:x₀), and
[a radius function](hyp:ρ), if [the correspondence is compact](hyp:hK),
[the reference section is continuous](hyp:hx₀), and [the radius function is continuous](hyp:hρ),
then [the parameter-dependent far feasible set is closed](goal). -/
theorem isClosed_farFeasibleSet {P X : Type*} [TopologicalSpace P] [T2Space P]
    [MetricSpace X] (K : Set (P × X)) (x₀ : P → X) (ρ : P → ℝ)
    (hK : IsCompact K) (hx₀ : Continuous x₀) (hρ : Continuous ρ) :
    IsClosed (farFeasibleSet K x₀ ρ) := by
  exact hK.isClosed.inter <|
    isClosed_le (hρ.comp continuous_fst) <|
      continuous_snd.dist (hx₀.comp continuous_fst)

/-- Given [a feasible correspondence](hyp:K), [a reference section](hyp:x₀), and
[a radius function](hyp:ρ), if [the correspondence is compact](hyp:hK) and
[its far feasible set is closed](hyp:hfar), then [the far feasible set is compact](goal). -/
theorem isCompact_farFeasibleSet_of_isClosed {P X : Type*} [TopologicalSpace P]
    [PseudoMetricSpace X] (K : Set (P × X)) (x₀ : P → X) (ρ : P → ℝ)
    (hK : IsCompact K) (hfar : IsClosed (farFeasibleSet K x₀ ρ)) :
    IsCompact (farFeasibleSet K x₀ ρ) := by
  exact hK.of_isClosed_subset hfar fun _ hz => hz.1

/-- Given [a feasible correspondence](hyp:K), [a reference section](hyp:x₀),
[a residual](hyp:r), and [a positive-radius function](hyp:ρ), if
[the correspondence is compact](hyp:hK), [the far feasible set is closed](hyp:hfar_closed),
[the far feasible set is nonempty](hyp:hfar_nonempty), [the residual is continuous](hyp:hr_cont),
[the residual is nonnegative on feasible pairs](hyp:hr_nonneg),
[only the reference candidate has zero residual among feasible pairs](hyp:hr_zero), and
[every radius is strictly positive](hyp:hρ_pos), then [some far pair attains a strictly
positive residual minimum on the far feasible set](goal). -/
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

/-- Given [a feasible correspondence](hyp:K), [a reference section](hyp:x₀),
[a residual](hyp:r), and [a radius function](hyp:ρ), if [the correspondence is compact](hyp:hK),
[the reference section is continuous](hyp:hx₀), [the residual is continuous](hyp:hr_cont),
[the radius function is continuous](hyp:hρ_cont), [every radius is strictly positive](hyp:hρ_pos),
[the residual is nonnegative on feasible pairs](hyp:hr_nonneg), and
[only the reference candidate has zero residual among feasible pairs](hyp:hr_zero), then
[either no far feasible pair exists or one attains a strictly positive uniform residual
minimum](goal). -/
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
  rcases Set.eq_empty_or_nonempty (farFeasibleSet K x₀ ρ) with hfar | hfar
  · exact Or.inl hfar
  · exact Or.inr <|
      exists_uniformPositiveExclusionRadius_of_isClosed K x₀ r ρ hK hfar_closed hfar
        hr_cont hr_nonneg hr_zero hρ_pos

/-- Given [a feasible correspondence](hyp:K), [a reference section](hyp:x₀),
[a residual](hyp:r), and [a radius function](hyp:ρ), if [the correspondence is compact](hyp:hK),
[the reference section is continuous](hyp:hx₀), [the residual is continuous](hyp:hr_cont),
[the radius function is continuous](hyp:hρ_cont), [every radius is strictly positive](hyp:hρ_pos),
[the residual is nonnegative on feasible pairs](hyp:hr_nonneg), and
[only the reference candidate has zero residual among feasible pairs](hyp:hr_zero), then
[either the far feasible set is empty or a far pair and its strictly positive attained residual
minimum can be exhibited explicitly](goal). -/
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
      hρ_pos hr_nonneg hr_zero with hfar | hnonempty
  · exact Or.inl hfar
  · obtain ⟨h⟩ := hnonempty
    exact Or.inr ⟨h.parameter, h.candidate, h.radius, h.mem_far, h.radius_pos,
      h.attained, h.lower_bound⟩

/-- Given [a uniform positive exclusion radius](hyp:h), [a feasible pair](hyp:hK), and
[a residual strictly below that radius](hyp:hr), then [the candidate lies strictly inside its
parameter-dependent reference neighborhood](goal). -/
theorem UniformPositiveExclusionRadius.dist_lt_of_residual_lt
    {P X : Type*} [TopologicalSpace P] [PseudoMetricSpace X]
    {K : Set (P × X)} {x₀ : P → X} {ρ : P → ℝ} {r : P × X → ℝ}
    (h : UniformPositiveExclusionRadius K x₀ ρ r) {p : P} {x : X}
    (hK : (p, x) ∈ K) (hr : r (p, x) < h.radius) :
    dist x (x₀ p) < ρ p := by
  by_contra hdist
  have hfar : (p, x) ∈ farFeasibleSet K x₀ ρ := ⟨hK, le_of_not_gt hdist⟩
  exact (not_lt_of_ge (h.lower_bound (p, x) hfar)) hr

/-- Given [a uniform positive exclusion radius](hyp:h), [a feasible pair](hyp:hK), and
[a residual at most half that radius](hyp:hr), then [the candidate lies strictly inside its
parameter-dependent reference neighborhood](goal). -/
theorem UniformPositiveExclusionRadius.dist_lt_of_residual_le_half
    {P X : Type*} [TopologicalSpace P] [PseudoMetricSpace X]
    {K : Set (P × X)} {x₀ : P → X} {ρ : P → ℝ} {r : P × X → ℝ}
    (h : UniformPositiveExclusionRadius K x₀ ρ r) {p : P} {x : X}
    (hK : (p, x) ∈ K) (hr : r (p, x) ≤ h.radius / 2) :
    dist x (x₀ p) < ρ p := by
  apply h.dist_lt_of_residual_lt hK
  exact lt_of_le_of_lt hr (div_lt_self h.radius_pos (by norm_num))

/-- Given [a feasible correspondence](hyp:K), [a reference section](hyp:x₀),
[a residual](hyp:r), and [a radius function](hyp:ρ), if [the correspondence is compact](hyp:hK),
[the reference section is continuous](hyp:hx₀), [the residual is continuous](hyp:hr_cont),
[the radius function is continuous](hyp:hρ_cont), [every radius is strictly positive](hyp:hρ_pos),
[the residual is nonnegative on feasible pairs](hyp:hr_nonneg), and
[only the reference candidate has zero residual among feasible pairs](hyp:hr_zero), then
[one strictly positive tolerance sends every feasible pair with smaller residual inside its
own reference neighborhood](goal). -/
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
      hρ_pos hr_nonneg hr_zero with hfar | hnonempty
  · refine ⟨1, by norm_num, ?_⟩
    intro p x hpx _
    by_contra hdist
    have hx : (p, x) ∈ farFeasibleSet K x₀ ρ := ⟨hpx, le_of_not_gt hdist⟩
    rw [hfar] at hx
    exact hx.elim
  · obtain ⟨h⟩ := hnonempty
    exact ⟨h.radius, h.radius_pos, fun p x hpx hr =>
      h.dist_lt_of_residual_lt hpx hr⟩

/-- Given [a feasible correspondence](hyp:K), [a reference section](hyp:x₀),
[a residual](hyp:r), and [a radius function](hyp:ρ), if [the correspondence is compact](hyp:hK),
[the reference section is continuous](hyp:hx₀), [the residual is continuous](hyp:hr_cont),
[the radius function is continuous](hyp:hρ_cont), [every radius is strictly positive](hyp:hρ_pos),
[the residual is nonnegative on feasible pairs](hyp:hr_nonneg), and
[only the reference candidate has zero residual among feasible pairs](hyp:hr_zero), then
[one strictly positive tolerance sends every feasible pair with residual at most that tolerance
inside its own reference neighborhood](goal). -/
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
      hρ_pos hr_nonneg hr_zero with hfar | hnonempty
  · refine ⟨1, by norm_num, ?_⟩
    intro p x hpx _
    by_contra hdist
    have hx : (p, x) ∈ farFeasibleSet K x₀ ρ := ⟨hpx, le_of_not_gt hdist⟩
    rw [hfar] at hx
    exact hx.elim
  · obtain ⟨h⟩ := hnonempty
    refine ⟨h.radius / 2, half_pos h.radius_pos, ?_⟩
    intro p x hpx hr
    exact h.dist_lt_of_residual_le_half hpx hr

end Causalean.Mathlib.Topology.CompactExclusion
