/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Estimation.Efficiency.TangentProjection
public import Causalean.Mathlib.MeasureTheory.RadonNikodymSqrt
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# DQM submodels, tangent spaces, and pathwise gradients

This module implements the standard semiparametric framework of van der Vaart
(1998), §25.3. A regular submodel is a path of probability laws dominated by
the base law whose square-root Radon--Nikodym densities are differentiable in
quadratic mean. Its score is therefore determined by its path.

A model is represented by a chosen family of regular submodels. Its tangent
space is the closed linear span of their scores. A pathwise gradient represents
the derivative of the functional along every member of that family, and its
orthogonal projection onto the tangent space is the canonical gradient, or
efficient influence function.

The restriction `P_t ≪ P` does not shrink the tangent space of the
nonparametric model: `TiltTangent.lean` constructs dominated bounded
exponential tilts whose scores already span a dense subspace of `L²₀(P)`.

Paths are indexed by all `t ∈ ℝ`, and derivatives at zero are two-sided. This
is the usual nonparametric or regular-parametric setting with the base law at
an interior parameter value. One-sided tangent cones and boundary models are
not represented by this interface.
-/

@[expose] public section

noncomputable section

namespace Causalean.Estimation.Efficiency

open Filter MeasureTheory Topology
open Causalean.Mathlib.MeasureTheory
open scoped InnerProductSpace RealInnerProductSpace

variable {Z : Type*} [MeasurableSpace Z]

/-- Given [a base probability law `P`](hyp:P), [a probability law `Q`](hyp:Q),
and [a perturbation parameter `t`](hyp:t), the [DQM square-root-density
quotient](goal) is `t⁻¹(sqrt(dQ/dP) - 1)` as an element of `L²(P)`. -/
noncomputable def dqmQuotient (P Q : Measure Z) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (t : ℝ) : Lp ℝ 2 P :=
  t⁻¹ • (rnSqrtDensityLp P Q - lpOne P)

private theorem dqmQuotient_congr (P Q R : Measure Z) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] [IsProbabilityMeasure R] (t : ℝ) (h : Q = R) :
    dqmQuotient P Q t = dqmQuotient P R t := by
  subst R
  rfl

/-- A regular submodel through [a probability law `P`](hyp:P) consists of [a path
of probability laws](hyp:path) [passing through `P` at zero](hyp:path_zero),
[dominated by `P`](hyp:path_ac), and [a mean-zero square-integrable score](hyp:score)
coupled to that path by [differentiability in quadratic mean](hyp:dqm).

The DQM field is equation (25.13) of van der Vaart (1998): in `L²(P)`,
`(sqrt(dP_t/dP)-1)/t → score/2`. Squaring the L² norm gives exactly the
integral formulation. Domination is imposed for all `t`; bounded exponential
tilts satisfy it and already generate the full nonparametric tangent space. -/
structure RegularSubmodel (P : Measure Z) [IsProbabilityMeasure P] where
  /-- The two-sided one-parameter path of laws, indexed by every real `t`. -/
  path : ℝ → Measure Z
  /-- Every law on the path is a probability measure. -/
  path_probability : ∀ t, IsProbabilityMeasure (path t)
  /-- The path passes through the base law at zero. -/
  path_zero : path 0 = P
  /-- Every path law is absolutely continuous with respect to the base law. -/
  path_ac : ∀ t, path t ≪ P
  /-- The square-integrable score. -/
  score : Lp ℝ 2 P
  /-- The score has mean zero under the base law. -/
  score_meanZero : score ∈ meanZeroLp P
  /-- The square-root-density difference quotient converges in L² to half the score. -/
  dqm : Tendsto
    (fun t => letI := path_probability t; dqmQuotient P (path t) t)
    (𝓝[≠] 0) (𝓝 ((2 : ℝ)⁻¹ • score))

namespace RegularSubmodel

/-- For [a DQM regular submodel `m`](hyp:m), [the integral of the squared
square-root-density quotient error converges to zero](goal). This is the
integral form of van der Vaart's equation (25.13), with the quotient represented
canonically in `L²(P)`. -/
theorem dqm_integral_tendsto {P : Measure Z} [IsProbabilityMeasure P]
    (m : RegularSubmodel P) :
    Tendsto
      (fun t =>
        letI := m.path_probability t
        ∫ z, (dqmQuotient P (m.path t) t z -
          ((2 : ℝ)⁻¹ • m.score) z) ^ 2 ∂P)
      (𝓝[≠] 0) (𝓝 0) := by
  have hdiff := m.dqm.sub
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (2 : ℝ)⁻¹ • m.score)
      (𝓝[≠] 0) (𝓝 ((2 : ℝ)⁻¹ • m.score)))
  have hsq := hdiff.norm.pow 2
  have hsq0 : Tendsto
      (fun t =>
        letI := m.path_probability t
        ‖dqmQuotient P (m.path t) t - (2 : ℝ)⁻¹ • m.score‖ ^ 2)
      (𝓝[≠] 0) (𝓝 0) := by
    simpa only [sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] using hsq
  simp_rw [lpNorm_sq_eq_integral_sq] at hsq0
  convert hsq0 using 1
  funext t
  letI : IsProbabilityMeasure (m.path t) := m.path_probability t
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (dqmQuotient P (m.path t) t)
    ((2 : ℝ)⁻¹ • m.score)] with z hz
  rw [hz]
  rfl

/-- If [two regular submodels through `P`](hyp:m,n) have [the same law path](hyp:hpath),
then [their DQM scores are equal](goal). -/
theorem score_eq_of_path_eq {P : Measure Z} [IsProbabilityMeasure P]
    (m n : RegularSubmodel P) (hpath : m.path = n.path) : m.score = n.score := by
  have hm := m.dqm
  have hn := n.dqm
  have hcurve :
      (fun t => letI := m.path_probability t; dqmQuotient P (m.path t) t) =
        (fun t => letI := n.path_probability t; dqmQuotient P (n.path t) t) := by
    funext t
    exact @dqmQuotient_congr Z _ P (m.path t) (n.path t) _
      (m.path_probability t) (n.path_probability t) t (congrFun hpath t)
  rw [hcurve] at hm
  have hhalf : (2 : ℝ)⁻¹ • m.score = (2 : ℝ)⁻¹ • n.score :=
    tendsto_nhds_unique hm hn
  have hscaled := congrArg (fun x : Lp ℝ 2 P => (2 : ℝ) • x) hhalf
  simpa [smul_smul] using hscaled

/-- For [a base probability law `P`](hyp:P), the [constant regular submodel](goal)
keeps the law equal to `P` and has zero score. -/
noncomputable def constant (P : Measure Z) [IsProbabilityMeasure P] :
    RegularSubmodel P where
  path := fun _ => P
  path_probability := fun _ => inferInstance
  path_zero := rfl
  path_ac := fun _ => Measure.AbsolutelyContinuous.rfl
  score := 0
  score_meanZero := (meanZeroLp P).zero_mem
  dqm := by
    simpa [dqmQuotient] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : Lp ℝ 2 P)) (𝓝[≠] 0) (𝓝 0))

/-- If [a regular submodel through `P`](hyp:m) has [the constant law path](hyp:hpath),
then [its score is zero](goal). -/
theorem score_eq_zero_of_path_eq_const {P : Measure Z} [IsProbabilityMeasure P]
    (m : RegularSubmodel P) (hpath : m.path = fun _ => P) : m.score = 0 := by
  simpa [constant] using m.score_eq_of_path_eq (constant P) hpath

end RegularSubmodel

/-- Given [a probability law `P`](hyp:P) and [a chosen family `S` of regular
submodels through it](hyp:S), the [tangent score set](goal) consists of the scores
of members of `S`. -/
def scoreSet (P : Measure Z) [IsProbabilityMeasure P]
    (S : Set (RegularSubmodel P)) : Set (Lp ℝ 2 P) :=
  {g | ∃ m ∈ S, m.score = g}

/-- Given [a probability law `P`](hyp:P) and [a chosen family `S` of regular
submodels](hyp:S), the [generated tangent space](goal) is the closed linear span
of their score set. -/
noncomputable def tangentSpace (P : Measure Z) [IsProbabilityMeasure P]
    (S : Set (RegularSubmodel P)) : Submodule ℝ (Lp ℝ 2 P) :=
  (Submodule.span ℝ (scoreSet P S)).topologicalClosure

/-- Every [score of a submodel `m` belonging to `S`](hyp:hm) [lies in the tangent
space generated by `S`](goal). -/
theorem score_mem_tangentSpace {P : Measure Z} [IsProbabilityMeasure P]
    {S : Set (RegularSubmodel P)} {m : RegularSubmodel P} (hm : m ∈ S) :
    m.score ∈ tangentSpace P S := by
  apply Submodule.le_topologicalClosure (Submodule.span ℝ (scoreSet P S))
  apply Submodule.subset_span
  exact ⟨m, hm, rfl⟩

/-- For [a probability law `P`](hyp:P) and [a submodel family `S`](hyp:S), [the
closed generated tangent space has an orthogonal projection](goal). -/
noncomputable instance tangentSpaceHasOrthogonalProjection
    (P : Measure Z) [IsProbabilityMeasure P] (S : Set (RegularSubmodel P)) :
    (tangentSpace P S).HasOrthogonalProjection := by
  letI : CompleteSpace (tangentSpace P S) := by
    rw [tangentSpace]
    infer_instance
  infer_instance

/-- Given [a probability law `P`](hyp:P), [a functional `ψ`](hyp:ψ), [an L²
candidate `g`](hyp:g), and [a family `S` of regular submodels](hyp:S), [the
candidate is a pathwise gradient relative to `S`](goal) when every path derivative
equals its inner product with that path's DQM score. -/
def IsPathwiseGradient (P : Measure Z) [IsProbabilityMeasure P]
    (ψ : Measure Z → ℝ) (g : Lp ℝ 2 P) (S : Set (RegularSubmodel P)) : Prop :=
  ∀ m ∈ S, HasDerivAt (fun t => ψ (m.path t)) ⟪g, m.score⟫_ℝ 0

/-- If [two candidates are pathwise gradients relative to the same family](hyp:hg,hg'),
then [they have the same inner product](goal) with [every score in that family](hyp:hm). -/
theorem inner_score_eq_of_isPathwiseGradient
    {P : Measure Z} [IsProbabilityMeasure P] {ψ : Measure Z → ℝ}
    {S : Set (RegularSubmodel P)} {g g' : Lp ℝ 2 P}
    (hg : IsPathwiseGradient P ψ g S) (hg' : IsPathwiseGradient P ψ g' S)
    {m : RegularSubmodel P} (hm : m ∈ S) :
    ⟪g, m.score⟫_ℝ = ⟪g', m.score⟫_ℝ :=
  (hg m hm).unique (hg' m hm)

/-- If [two candidates are pathwise gradients relative to the same family](hyp:hg,hg'),
then [their difference is orthogonal to the generated tangent space](goal). -/
theorem sub_mem_orthogonal_of_isPathwiseGradient
    {P : Measure Z} [IsProbabilityMeasure P] {ψ : Measure Z → ℝ}
    {S : Set (RegularSubmodel P)} {g g' : Lp ℝ 2 P}
    (hg : IsPathwiseGradient P ψ g S) (hg' : IsPathwiseGradient P ψ g' S) :
    g - g' ∈ (tangentSpace P S)ᗮ := by
  rw [tangentSpace, Submodule.orthogonal_closure, Submodule.mem_orthogonal']
  intro u hu
  let W : Submodule ℝ (Lp ℝ 2 P) := {
    carrier := {v | ⟪g - g', v⟫_ℝ = 0}
    zero_mem' := by simp
    add_mem' := by intros; simp_all [inner_add_right]
    smul_mem' := by intros; simp_all [inner_smul_right] }
  have hspan : Submodule.span ℝ (scoreSet P S) ≤ W := by
    rw [Submodule.span_le]
    rintro _ ⟨m, hm, rfl⟩
    change ⟪g - g', m.score⟫_ℝ = 0
    rw [inner_sub_left, inner_score_eq_of_isPathwiseGradient hg hg' hm, sub_self]
  exact hspan hu

/-- Given [a probability law `P`](hyp:P), [a submodel family `S`](hyp:S), and
[a reference gradient `g`](hyp:g), the [canonical gradient](goal) is the
orthogonal projection of `g` onto the tangent space generated by `S`. -/
noncomputable def canonicalGradient (P : Measure Z) [IsProbabilityMeasure P]
    (S : Set (RegularSubmodel P)) (g : Lp ℝ 2 P) : Lp ℝ 2 P :=
  efficientIF (tangentSpace P S) g

/-- Given [a probability law `P`](hyp:P), [a functional `ψ`](hyp:ψ), [a candidate
`g`](hyp:g), and [a submodel family `S`](hyp:S), [the candidate is an efficient
influence function](goal) when it is a pathwise gradient and belongs to the
generated tangent space. -/
def IsEfficientInfluenceFunction (P : Measure Z) [IsProbabilityMeasure P]
    (ψ : Measure Z → ℝ) (g : Lp ℝ 2 P) (S : Set (RegularSubmodel P)) : Prop :=
  IsPathwiseGradient P ψ g S ∧ g ∈ tangentSpace P S

/-- If [a candidate `g` is a pathwise gradient](hyp:hg), then [its canonical
gradient is also a pathwise gradient](goal). -/
theorem canonicalGradient_isPathwiseGradient
    {P : Measure Z} [IsProbabilityMeasure P] {ψ : Measure Z → ℝ}
    {S : Set (RegularSubmodel P)} {g : Lp ℝ 2 P}
    (hg : IsPathwiseGradient P ψ g S) :
    IsPathwiseGradient P ψ (canonicalGradient P S g) S := by
  intro m hm
  have hinner : ⟪canonicalGradient P S g, m.score⟫_ℝ = ⟪g, m.score⟫_ℝ := by
    rw [canonicalGradient, efficientIF]
    exact (tangentSpace P S).inner_orthogonalProjection_eq_of_mem_right
      ⟨m.score, score_mem_tangentSpace hm⟩ g
  simpa [hinner] using hg m hm

/-- If [a candidate `g` is a pathwise gradient](hyp:hg), then [its canonical
gradient is an efficient influence function](goal). -/
theorem canonicalGradient_isEfficientInfluenceFunction
    {P : Measure Z} [IsProbabilityMeasure P] {ψ : Measure Z → ℝ}
    {S : Set (RegularSubmodel P)} {g : Lp ℝ 2 P}
    (hg : IsPathwiseGradient P ψ g S) :
    IsEfficientInfluenceFunction P ψ (canonicalGradient P S g) S :=
  ⟨canonicalGradient_isPathwiseGradient hg, efficientIF_mem g⟩

/-- If [two candidates are efficient influence functions for the same functional
and submodel family](hyp:hg,hg'), then [they are equal](goal). -/
theorem efficientInfluenceFunction_unique
    {P : Measure Z} [IsProbabilityMeasure P] {ψ : Measure Z → ℝ}
    {S : Set (RegularSubmodel P)} {g g' : Lp ℝ 2 P}
    (hg : IsEfficientInfluenceFunction P ψ g S)
    (hg' : IsEfficientInfluenceFunction P ψ g' S) : g = g' := by
  have horth := sub_mem_orthogonal_of_isPathwiseGradient hg.1 hg'.1
  have hzero : g - g' = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    exact (Submodule.mem_orthogonal' (tangentSpace P S) (g - g')).1 horth
      (g - g') ((tangentSpace P S).sub_mem hg.2 hg'.2)
  exact sub_eq_zero.mp hzero

/-- If [an efficient influence function `g` is known](hyp:hg) and [another
candidate `v` is a pathwise gradient](hyp:hv), then [the canonical gradient of
`v` equals `g`](goal). -/
theorem canonicalGradient_eq_of_isEfficientInfluenceFunction
    {P : Measure Z} [IsProbabilityMeasure P] {ψ : Measure Z → ℝ}
    {S : Set (RegularSubmodel P)} {g v : Lp ℝ 2 P}
    (hg : IsEfficientInfluenceFunction P ψ g S)
    (hv : IsPathwiseGradient P ψ v S) : canonicalGradient P S v = g := by
  exact efficientInfluenceFunction_unique
    (canonicalGradient_isEfficientInfluenceFunction hv) hg

/-- If [a candidate `g` is a pathwise gradient of `ψ` relative to `S`](hyp:hg), then
[viewing `g` as a Hilbert-space gradient of its canonical projection onto the generated
tangent space is valid](goal). This is the bridge from path derivatives to the abstract
`IsGradient`/`effBound` projection API. -/
theorem isGradient_canonicalGradient_of_isPathwiseGradient
    {P : Measure Z} [IsProbabilityMeasure P] {ψ : Measure Z → ℝ}
    {S : Set (RegularSubmodel P)} {g : Lp ℝ 2 P}
    (hg : IsPathwiseGradient P ψ g S) :
    IsGradient (tangentSpace P S) (canonicalGradient P S g) g := by
  intro s hs
  rw [canonicalGradient, efficientIF]
  exact ((tangentSpace P S).inner_orthogonalProjection_eq_of_mem_right ⟨s, hs⟩ g).symm

/-- If [a candidate `g` is a pathwise gradient of `ψ` relative to `S`](hyp:hg), then
[the squared norm of its canonical gradient is no larger than the squared norm of
`g`](goal), the Hilbert-space efficiency bound. The corresponding statistical
lower bound is
`AsymptoticLanConvolution.regular_asymptoticVariance_ge_gradientNormSq`, which
shows that a regular estimator's asymptotic variance cannot fall below the
canonical-gradient norm squared. -/
theorem canonicalGradient_normSq_le
    {P : Measure Z} [IsProbabilityMeasure P] {ψ : Measure Z → ℝ}
    {S : Set (RegularSubmodel P)} {g : Lp ℝ 2 P}
    (hg : IsPathwiseGradient P ψ g S) :
    ‖canonicalGradient P S g‖ ^ 2 ≤ ‖g‖ ^ 2 := by
  have hbound := effBound_le_normSq
    (isGradient_canonicalGradient_of_isPathwiseGradient hg)
  have hmem : canonicalGradient P S g ∈ tangentSpace P S := by
    exact efficientIF_mem g
  rw [effBound, efficientIF_eq_self_of_mem (tangentSpace P S) hmem] at hbound
  exact hbound

/-- Let [a smaller regular-submodel family `S` be contained in `S'`](hyp:hSS') and
suppose [both families generate the same tangent space](hyp:hT). If [`g` is the efficient
influence function relative to `S`](hyp:hg) and [`ψ` has some pathwise gradient `v` along
the enlarged family `S'`](hyp:hv), then [`g` remains the efficient influence function
relative to `S'`](goal). -/
theorem IsEfficientInfluenceFunction.mono_of_tangentSpace_eq
    {P : Measure Z} [IsProbabilityMeasure P] {ψ : Measure Z → ℝ}
    {S S' : Set (RegularSubmodel P)} {g v : Lp ℝ 2 P}
    (hg : IsEfficientInfluenceFunction P ψ g S)
    (hSS' : S ⊆ S') (hT : tangentSpace P S = tangentSpace P S')
    (hv : IsPathwiseGradient P ψ v S') :
    IsEfficientInfluenceFunction P ψ g S' := by
  have hvS : IsPathwiseGradient P ψ v S := fun m hm => hv m (hSS' hm)
  have hcanon : canonicalGradient P S v = g :=
    canonicalGradient_eq_of_isEfficientInfluenceFunction hg hvS
  constructor
  · intro m hm
    have hscore : m.score ∈ tangentSpace P S := by
      rw [hT]
      exact score_mem_tangentSpace hm
    have hinner : ⟪g, m.score⟫_ℝ = ⟪v, m.score⟫_ℝ := by
      rw [← hcanon, canonicalGradient, efficientIF]
      exact (tangentSpace P S).inner_orthogonalProjection_eq_of_mem_right
        ⟨m.score, hscore⟩ v
    simpa only [hinner] using hv m hm
  · rw [← hT]
    exact hg.2

end Causalean.Estimation.Efficiency
