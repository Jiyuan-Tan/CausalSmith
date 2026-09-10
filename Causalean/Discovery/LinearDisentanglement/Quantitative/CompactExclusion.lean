/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Discovery.LinearDisentanglement.Quantitative.Definitions

/-!
# Compact exclusion away from an isolated exact solution

This module packages the non-effective compactness argument used after a local quantitative
estimate: a continuous nonnegative residual with a unique zero on a compact normalized
candidate set has a strictly positive, attained minimum outside any open neighborhood of
that zero, provided the outside set is nonempty.
-/

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator

namespace Causalean.Discovery.LinearDisentanglement.Quantitative

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
[the residual is continuous](hyp:hr_cont), [the residual is nonnegative on candidates](hyp:hr_nonneg),
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

/-- For [a finite real matrix family](hyp:A) and [its prescribed diagonal shifts](hyp:s),
[the simultaneous-congruence residual is continuous as a function of the candidate
matrix](goal). -/
-- Proof route: matrix multiplication, transpose, subtraction, diagonal constants, and
-- the norm are continuous in finite dimension; close under the finite nonempty `sup'`.
theorem continuous_simultaneousCongruenceResidual {d : ℕ} {E : Type*}
    [Fintype E] [Nonempty E]
    (A : E → SqMatrix d) (s : E → Fin d → ℝ) :
    Continuous (simultaneousCongruenceResidual A s) := by
  classical
  unfold simultaneousCongruenceResidual
  have h : Continuous
      (Finset.univ.sup' Finset.univ_nonempty
        (fun e B => ‖congruenceDefect (A e) (s e) B‖)) := by
    apply Continuous.finset_sup' Finset.univ_nonempty
    intro e _
    apply Continuous.norm
    unfold congruenceDefect
    fun_prop
  rw [show (fun B => Finset.univ.sup' Finset.univ_nonempty
      (fun e => ‖congruenceDefect (A e) (s e) B‖)) =
      Finset.univ.sup' Finset.univ_nonempty
        (fun e B => ‖congruenceDefect (A e) (s e) B‖) by
    funext B
    exact (Finset.sup'_apply Finset.univ_nonempty
      (fun e B => ‖congruenceDefect (A e) (s e) B‖) B).symm]
  exact h

/-- For [a finite real matrix family](hyp:A), [its diagonal shifts](hyp:s), [a compact
normalized candidate set](hyp:K), [an open local chart](hyp:U), and [a reference matrix](hyp:B₀),
if [the candidate set is compact](hyp:hK), [the chart is open](hyp:hU), [the reference is a
candidate](hyp:hB₀K), [the reference lies in the chart](hyp:hB₀U), [the far candidates are
nonempty](hyp:hfar), and [only the reference has zero residual among candidates](hyp:hzero),
then [the far candidates have a strictly positive attained simultaneous-congruence residual
minimum](goal). -/
theorem exists_simultaneousCongruence_exclusionRadius {d : ℕ} {E : Type*}
    [Fintype E] [Nonempty E]
    (A : E → SqMatrix d) (s : E → Fin d → ℝ)
    (K U : Set (SqMatrix d)) (B₀ : SqMatrix d)
    (hK : IsCompact K) (hU : IsOpen U) (hB₀K : B₀ ∈ K) (hB₀U : B₀ ∈ U)
    (hfar : (K \ U).Nonempty)
    (hzero : ∀ B ∈ K, simultaneousCongruenceResidual A s B = 0 → B = B₀) :
    Nonempty (PositiveExclusionRadius K U (simultaneousCongruenceResidual A s)) := by
  exact exists_positiveExclusionRadius K U
    (simultaneousCongruenceResidual A s) B₀
    hK hU hB₀K hB₀U hfar
    (continuous_simultaneousCongruenceResidual A s)
    (fun B _ => simultaneousCongruenceResidual_nonneg A s B)
    hzero
/-! ## Uniform compact-correspondence exclusion

The declarations below extend compact exclusion from one fixed reference point to a compact
family of parameter-dependent feasible problems.  They are useful when a single residual
tolerance must keep every feasible parameter-candidate pair inside its own reference
neighborhood.
-/

/-- For [a parameter space](hyp:P), [a candidate pseudometric space](hyp:X), [a set of feasible parameter--candidate pairs](hyp:K), [a reference candidate assigned to each parameter](hyp:x₀), and [a real-valued radius assigned to each parameter](hyp:ρ), the [far feasible set](goal) consists exactly of the feasible pairs whose candidate is at least that parameter's assigned radius from its reference candidate. -/
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

/-- Given [a parameter-matrix correspondence](hyp:K), [a reference matrix section](hyp:B₀),
[a residual](hyp:r), and [a radius function](hyp:ρ), if [the correspondence is compact](hyp:hK),
[the reference matrix section is continuous](hyp:hB₀), [the residual is continuous](hyp:hr_cont),
[the radius function is continuous](hyp:hρ_cont), [every radius is strictly positive](hyp:hρ_pos),
[the residual is nonnegative on feasible pairs](hyp:hr_nonneg), and
[only the reference matrix has zero residual among feasible pairs](hyp:hr_zero), then
[either no operator-norm-far pair exists or one attains a strictly positive uniform residual
minimum](goal). -/
theorem sqMatrix_uniformCompactCorrespondence_dichotomy
    {P : Type*} [TopologicalSpace P] [T2Space P] {d : ℕ}
    (K : Set (P × SqMatrix d)) (B₀ : P → SqMatrix d)
    (r : P × SqMatrix d → ℝ) (ρ : P → ℝ)
    (hK : IsCompact K) (hB₀ : Continuous B₀) (hr_cont : Continuous r)
    (hρ_cont : Continuous ρ) (hρ_pos : ∀ p, 0 < ρ p)
    (hr_nonneg : ∀ z ∈ K, 0 ≤ r z)
    (hr_zero : ∀ p B, (p, B) ∈ K → r (p, B) = 0 → B = B₀ p) :
    farFeasibleSet K B₀ ρ = ∅ ∨
      Nonempty (UniformPositiveExclusionRadius K B₀ ρ r) := by
  exact uniformCompactCorrespondence_dichotomy K B₀ r ρ hK hB₀ hr_cont hρ_cont hρ_pos
    hr_nonneg hr_zero

/-- Given [a parameter-matrix correspondence](hyp:K), [a reference matrix section](hyp:B₀),
[a residual](hyp:r), and [a radius function](hyp:ρ), if [the correspondence is compact](hyp:hK),
[the reference matrix section is continuous](hyp:hB₀), [the residual is continuous](hyp:hr_cont),
[the radius function is continuous](hyp:hρ_cont), [every radius is strictly positive](hyp:hρ_pos),
[the residual is nonnegative on feasible pairs](hyp:hr_nonneg), and
[only the reference matrix has zero residual among feasible pairs](hyp:hr_zero), then
[one positive residual tolerance puts every feasible pair at or below it strictly inside its
parameter-dependent Euclidean operator-norm reference ball](goal). -/
theorem exists_sqMatrix_uniformExclusionTolerance
    {P : Type*} [TopologicalSpace P] [T2Space P] {d : ℕ}
    (K : Set (P × SqMatrix d)) (B₀ : P → SqMatrix d)
    (r : P × SqMatrix d → ℝ) (ρ : P → ℝ)
    (hK : IsCompact K) (hB₀ : Continuous B₀) (hr_cont : Continuous r)
    (hρ_cont : Continuous ρ) (hρ_pos : ∀ p, 0 < ρ p)
    (hr_nonneg : ∀ z ∈ K, 0 ≤ r z)
    (hr_zero : ∀ p B, (p, B) ∈ K → r (p, B) = 0 → B = B₀ p) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ p B, (p, B) ∈ K → r (p, B) ≤ ε₀ →
      ‖B - B₀ p‖ < ρ p := by
  simpa only [dist_eq_norm] using
    (exists_uniformExclusionTolerance_le K B₀ r ρ hK hB₀ hr_cont hρ_cont hρ_pos
      hr_nonneg hr_zero)


end Causalean.Discovery.LinearDisentanglement.Quantitative
