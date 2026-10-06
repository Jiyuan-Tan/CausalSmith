module
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.Tangent
public import Mathlib.Geometry.Manifold.SmoothEmbedding

/-!
# Full extrinsic tangent and orthogonal normal spaces

The full tangent is the range of the manifold differential of the embedding.
An admissible parametrization is the embedding composed with the inverse of
any extended chart in the maximal C² atlas. Derivatives are taken within the
extended chart target; this includes boundary points and never substitutes a
one-sided tangent cone for the full tangent space.

Federer, *Curvature Measures* (1959), §§2.8, 4.3–4.6, distinguishes intrinsic
tangents from set tangent cones. His normal cone at a boundary is not the
orthogonal normal subspace constructed here. Reach results are downstream.
-/
@[expose] public section

open Manifold Set
open scoped ContDiff Topology

namespace Causalean.Mathlib.Geometry.Manifold.EmbeddedNormalGeometry

private theorem gram_isInvertible {G E : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (D : G →L[ℝ] E) (hD : Function.Injective D) :
    ((ContinuousLinearMap.adjoint D).comp D).IsInvertible := by
  have hi : Function.Injective ((ContinuousLinearMap.adjoint D).comp D) :=
    (D.adjoint_comp_self_injective_iff).mpr hD
  exact ⟨ContinuousLinearEquiv.ofBijective _ (LinearMap.ker_eq_bot.mpr hi)
    (LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp hi)), rfl⟩

private theorem starProjection_range_eq {G E : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (D : G →L[ℝ] E) (hD : Function.Injective D) :
    D.range.starProjection = D.comp
      (((ContinuousLinearMap.adjoint D).comp D).inverse.comp
        (ContinuousLinearMap.adjoint D)) := by
  have hi := gram_isInvertible D hD
  ext v
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact ⟨_, rfl⟩
  · rw [D.orthogonal_range]
    change (ContinuousLinearMap.adjoint D)
      (v - D (((ContinuousLinearMap.adjoint D).comp D).inverse
        ((ContinuousLinearMap.adjoint D) v))) = 0
    rw [map_sub]
    change (ContinuousLinearMap.adjoint D) v -
      ((ContinuousLinearMap.adjoint D).comp D)
        (((ContinuousLinearMap.adjoint D).comp D).inverse
          ((ContinuousLinearMap.adjoint D) v)) = 0
    rw [hi.self_apply_inverse, sub_self]

variable {F E H M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] (I : ModelWithCorners ℝ F H) [IsManifold I 2 M]

/-- The full extrinsic tangent space is the image of the differential of the embedding. -/
noncomputable def tangentSpace (f : M → E) (x : M) : Submodule ℝ E :=
  (mfderiv I (modelWithCornersSelf ℝ E) f x).toLinearMap.range

/-- The normal space is the orthogonal complement of the full tangent space. -/
noncomputable def normalSpace (f : M → E) (x : M) : Submodule ℝ E :=
  (tangentSpace I f x)ᗮ

/-- The chart differential is the derivative within the chart target of its local parametrization.
-/
noncomputable def chartDifferential (f : M → E) (φ : OpenPartialHomeomorph M H)
    (x : M) : F →L[ℝ] E :=
  fderivWithin ℝ (f ∘ (φ.extend I).symm) (φ.extend I).target ((φ.extend I) x)

/-- A smooth embedding has an injective manifold differential, including at boundary points.

Prove from immersion normal-form charts, differentiating the inclusion and using invertible
chart changes; do not add derivative injectivity as a premise. -/
theorem embedding_mfderiv_injective (f : M → E)
    (hf : IsSmoothEmbedding I (modelWithCornersSelf ℝ E) 2 f) (x : M) :
    Function.Injective (mfderiv I (modelWithCornersSelf ℝ E) f x) := by
  let h := hf.isImmersion.isImmersionAt x
  let p : E →L[ℝ] F :=
    (ContinuousLinearMap.fst ℝ F h.complement).comp h.equiv.symm.toContinuousLinearMap
  let g : E → F := p ∘ (h.codChart.extend (modelWithCornersSelf ℝ E))
  have hd : h.domChart.MDifferentiable I I :=
    ⟨(contMDiffOn_of_mem_maximalAtlas h.domChart_mem_maximalAtlas).mdifferentiableOn
        (by norm_num),
      (contMDiffOn_symm_of_mem_maximalAtlas h.domChart_mem_maximalAtlas).mdifferentiableOn
        (by norm_num)⟩
  have hg : MDifferentiableAt (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ F) g (f x) :=
    p.hasMFDerivAt.mdifferentiableAt.comp _
      ((h.codChart.contMDiffAt_extend h.codChart_mem_maximalAtlas
        h.mem_codChart_source).mdifferentiableAt (by norm_num))
  have heq : g ∘ f =ᶠ[𝓝 x] h.domChart.extend I := by
    filter_upwards [h.domChart.open_source.mem_nhds h.mem_domChart_source] with y hy
    have hy' : y ∈ (h.domChart.extend I).source := by simpa using hy
    have hw := h.writtenInCharts ((h.domChart.extend I).map_source hy')
    rw [Function.comp_apply, Function.comp_apply,
      (h.domChart.extend I).left_inv hy'] at hw
    change p ((h.codChart.extend (modelWithCornersSelf ℝ E)) (f y)) = _
    rw [hw]
    simp [p]
  have hder : mfderiv I (modelWithCornersSelf ℝ F) (h.domChart.extend I) x =
      mfderiv I I h.domChart x := by
    exact (I.hasMFDerivAt.comp x (hd.mdifferentiableAt h.mem_domChart_source).hasMFDerivAt
      |>.mfderiv).trans (ContinuousLinearMap.id_comp _)
  have hi : Function.Injective
      (mfderiv I (modelWithCornersSelf ℝ F) (g ∘ f) x) := by
    rw [heq.mfderiv_eq, hder]
    exact hd.mfderiv_injective h.mem_domChart_source
  rw [mfderiv_comp x hg (hf.contMDiff.mdifferentiable (by norm_num) x)] at hi
  intro u v huv
  apply hi
  change mfderiv (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ F) g (f x)
      (mfderiv I (modelWithCornersSelf ℝ E) f x u) = _
  rw [huv]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Within-target differentiation of a parametrization factors through the inverse chart. -/
private theorem chartDifferential_eq (f : M → E)
    (hf : IsSmoothEmbedding I (modelWithCornersSelf ℝ E) 2 f)
    (φ : OpenPartialHomeomorph M H) (hφ : φ ∈ IsManifold.maximalAtlas I 2 M)
    (x : M) (hx : x ∈ φ.source) :
    chartDifferential I f φ x =
      (mfderiv I (modelWithCornersSelf ℝ E) f x).comp
        (mfderiv I I φ.symm (φ x)) := by
  have hd : φ.MDifferentiable I I :=
    ⟨(contMDiffOn_of_mem_maximalAtlas hφ).mdifferentiableOn (by norm_num),
      (contMDiffOn_symm_of_mem_maximalAtlas hφ).mdifferentiableOn (by norm_num)⟩
  have hx' : x ∈ (φ.extend I).source := by simpa using hx
  have hu : UniqueDiffWithinAt ℝ (φ.extend I).target ((φ.extend I) x) := by
    rw [φ.extend_target]
    exact I.uniqueDiffOn_preimage φ.open_target _
      (by simpa only [φ.extend_target] using (φ.extend I).map_source hx')
  have hI := (I.hasMFDerivWithinAt_symm
    (φ.extend_target_subset_range ((φ.extend I).map_source hx'))).mono
    φ.extend_target_subset_range
  have hi := (hd.mdifferentiableAt_symm (φ.map_source hx)).hasMFDerivAt
  have hi' : HasMFDerivAt I I φ.symm (I.symm ((φ.extend I) x))
      (mfderiv I I φ.symm (φ x)) := by
    change HasMFDerivAt I I φ.symm (I.symm (I (φ x))) _
    rw [I.left_inv]
    exact hi
  have hinv : HasMFDerivWithinAt (modelWithCornersSelf ℝ F) I (φ.extend I).symm
      (φ.extend I).target ((φ.extend I) x) (mfderiv I I φ.symm (φ x)) := by
    exact (hi'.comp_hasMFDerivWithinAt ((φ.extend I) x) hI).congr_mfderiv
      (ContinuousLinearMap.comp_id _)
  have hfx : HasMFDerivAt I (modelWithCornersSelf ℝ E) f
      ((φ.extend I).symm ((φ.extend I) x))
      (mfderiv I (modelWithCornersSelf ℝ E) f x) := by
    rw [(φ.extend I).left_inv hx']
    exact (hf.contMDiff.mdifferentiable (by norm_num) x).hasMFDerivAt
  have hc := hfx.comp_hasMFDerivWithinAt ((φ.extend I) x) hinv
  have heq : chartDifferential I f φ x =
      (mfderiv I (modelWithCornersSelf ℝ E) f x).comp
        (mfderiv I I φ.symm (φ x)) := by
    exact hc.hasFDerivWithinAt.fderivWithin hu
  exact heq

set_option backward.isDefEq.respectTransparency false in
/-- An [embedding `f`](hyp:f) satisfying [the smooth-embedding condition
`hf`](hyp:hf), described by [the model with corners `I`](hyp:I), has the
property that the derivative of every admissible chart `φ` at the point `x`,
under [its atlas condition `hφ`](hyp:hφ) and [source condition `hx`](hyp:hx),
[has range equal to the full extrinsic tangent space](goal).

Use the MFDeriv chain rule and the inverse chart derivative equivalence. The within-target
formulation retains the full model-space domain at boundary points. -/
theorem chartDifferential_range (f : M → E)
    (hf : IsSmoothEmbedding I (modelWithCornersSelf ℝ E) 2 f)
    (φ : OpenPartialHomeomorph M H) (hφ : φ ∈ IsManifold.maximalAtlas I 2 M)
    (x : M) (hx : x ∈ φ.source) :
    (chartDifferential I f φ x).toLinearMap.range = tangentSpace I f x := by
  have hd : φ.MDifferentiable I I :=
    ⟨(contMDiffOn_of_mem_maximalAtlas hφ).mdifferentiableOn (by norm_num),
      (contMDiffOn_symm_of_mem_maximalAtlas hφ).mdifferentiableOn (by norm_num)⟩
  rw [chartDifferential_eq I f hf φ hφ x hx]
  exact LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr (hd.symm.mfderiv_surjective (φ.map_source hx)))

/-- The differential of an admissible chart parametrization is injective on the full model
space, including at boundary points. -/
theorem chartDifferential_injective (f : M → E)
    (hf : IsSmoothEmbedding I (modelWithCornersSelf ℝ E) 2 f)
    (φ : OpenPartialHomeomorph M H) (hφ : φ ∈ IsManifold.maximalAtlas I 2 M)
    (x : M) (hx : x ∈ φ.source) :
    Function.Injective (chartDifferential I f φ x) := by
  have hd : φ.MDifferentiable I I :=
    ⟨(contMDiffOn_of_mem_maximalAtlas hφ).mdifferentiableOn (by norm_num),
      (contMDiffOn_symm_of_mem_maximalAtlas hφ).mdifferentiableOn (by norm_num)⟩
  rw [chartDifferential_eq I f hf φ hφ x hx]
  exact (embedding_mfderiv_injective I f hf x).comp
    (hd.symm.mfderiv_injective (φ.map_source hx))

/-- The dimension of the full tangent space equals the model dimension. -/
theorem tangentSpace_finrank (f : M → E)
    (hf : IsSmoothEmbedding I (modelWithCornersSelf ℝ E) 2 f) (x : M) :
    Module.finrank ℝ (tangentSpace I f x) = Module.finrank ℝ F := by
  exact LinearMap.finrank_range_of_inj
    (f := (mfderiv I (modelWithCornersSelf ℝ E) f x).toLinearMap)
    (embedding_mfderiv_injective I f hf x)

omit [FiniteDimensional ℝ F] [IsManifold I 2 M] in
/-- Tangent and normal spaces are complementary subspaces of the ambient Euclidean space. -/
theorem tangent_normal_isCompl (f : M → E) (x : M) :
    IsCompl (tangentSpace I f x) (normalSpace I f x) :=
  (tangentSpace I f x).isCompl_orthogonal

/-- Addition identifies the product of the full tangent and orthogonal normal with the ambient
space. -/
noncomputable def tangentNormalEquiv (f : M → E) (x : M) :
    (tangentSpace I f x × normalSpace I f x) ≃ₗ[ℝ] E :=
  (tangentSpace I f x).prodEquivOfIsCompl (normalSpace I f x)
    (tangent_normal_isCompl I f x)

omit [FiniteDimensional ℝ F] [IsManifold I 2 M] in
/-- The tangent-normal decomposition equivalence sends a pair to the sum of its ambient vectors. -/
theorem tangentNormalEquiv_apply (f : M → E) (x : M)
    (z : tangentSpace I f x × normalSpace I f x) :
    tangentNormalEquiv I f x z = (z.1 : E) + (z.2 : E) := rfl

omit [FiniteDimensional ℝ F] [IsManifold I 2 M] in
/-- Tangent and normal dimensions add to the ambient dimension. -/
theorem tangent_normal_finrank (f : M → E) (x : M) :
    Module.finrank ℝ (tangentSpace I f x) + Module.finrank ℝ (normalSpace I f x) =
      Module.finrank ℝ E :=
  (tangentSpace I f x).finrank_add_finrank_orthogonal

/-- The normal dimension is the ambient dimension minus the manifold dimension. -/
theorem normalSpace_finrank (f : M → E)
    (hf : IsSmoothEmbedding I (modelWithCornersSelf ℝ E) 2 f) (x : M) :
    Module.finrank ℝ (normalSpace I f x) = Module.finrank ℝ E - Module.finrank ℝ F := by
  have h := tangent_normal_finrank I f x
  rw [tangentSpace_finrank I f hf x] at h
  omega

set_option backward.isDefEq.respectTransparency false in
/-- The ambient orthogonal projection onto the full tangent varies continuously with the base
point.

In a local chart, use the injective derivative matrix D and the formula D (D* D)⁻¹ D*.
Continuity of the C¹ differential and inversion gives the result. -/
theorem continuous_tangentProjection (f : M → E)
    (hf : IsSmoothEmbedding I (modelWithCornersSelf ℝ E) 2 f) :
    Continuous (fun x => (tangentSpace I f x).starProjection) := by
  classical
  rw [continuous_iff_continuousAt]
  intro x
  let φ := chartAt H x
  have hφ : φ ∈ IsManifold.maximalAtlas I 2 M := IsManifold.chart_mem_maximalAtlas x
  have hx : x ∈ φ.source := mem_chart_source H x
  let A : F →L[ℝ] E := mfderiv I (modelWithCornersSelf ℝ E) f x
  -- Use the fixed tangent fiber as an inner-product domain without changing the norm on F.
  let V := A.range
  let e : F ≃L[ℝ] V :=
    (LinearEquiv.ofInjective A.toLinearMap
      (embedding_mfderiv_injective I f hf x)).toContinuousLinearEquiv
  let D : M → V →L[ℝ] E := fun y => (chartDifferential I f φ y).comp e.symm.toContinuousLinearMap
  have hd : φ.MDifferentiable I I :=
    ⟨(contMDiffOn_of_mem_maximalAtlas hφ).mdifferentiableOn (by norm_num),
      (contMDiffOn_symm_of_mem_maximalAtlas hφ).mdifferentiableOn (by norm_num)⟩
  have hinj : ∀ y ∈ φ.source, Function.Injective (D y) := by
    intro y hy
    dsimp only [D]
    rw [chartDifferential_eq I f hf φ hφ y hy]
    exact (embedding_mfderiv_injective I f hf y).comp
      ((hd.symm.mfderiv_injective (φ.map_source hy)).comp e.symm.injective)
  have hu : UniqueDiffOn ℝ (φ.extend I).target := by
    rw [φ.extend_target]
    exact I.uniqueDiffOn_preimage φ.open_target
  have hp : ContDiffOn ℝ 2 (f ∘ (φ.extend I).symm) (φ.extend I).target := by
    apply ContMDiffOn.contDiffOn
    rw [φ.extend_target']
    exact hf.contMDiff.comp_contMDiffOn (contMDiffOn_extend_symm hφ)
  have hc : ContinuousOn (fun y => chartDifferential I f φ y) φ.source :=
    (hp.continuousOn_fderivWithin hu (by norm_num)).comp
      (φ.contMDiffOn_extend hφ).continuousOn
      (fun y hy => (φ.extend I).map_source (by simpa using hy))
  have hD : ContinuousAt D x := by
    exact ((hc.clm_comp (show ContinuousOn (fun _ : M => e.symm.toContinuousLinearMap)
      φ.source from continuousOn_const)) x hx).continuousAt (φ.open_source.mem_nhds hx)
  have ha : ContinuousAt (fun y => ContinuousLinearMap.adjoint (D y)) x :=
    ContinuousLinearMap.adjoint.continuous.continuousAt.comp hD
  have hg := ha.clm_comp hD
  have hi : ContinuousAt
      (fun y => ((ContinuousLinearMap.adjoint (D y)).comp (D y)).inverse) x :=
    ((gram_isInvertible (D x) (hinj x hx)).contDiffAt_map_inverse (n := 0)).continuousAt.comp
      (f := fun y => (ContinuousLinearMap.adjoint (D y)).comp (D y)) hg
  apply (hD.clm_comp (hi.clm_comp ha)).congr_of_eventuallyEq
  filter_upwards [φ.open_source.mem_nhds hx] with y hy
  have hr : (D y).range = tangentSpace I f y := by
    change ((chartDifferential I f φ y).comp e.symm.toContinuousLinearMap).range = _
    rw [ContinuousLinearMap.toLinearMap_comp]
    exact (LinearMap.range_comp_of_range_eq_top (chartDifferential I f φ y).toLinearMap
      (LinearMap.range_eq_top.mpr e.symm.surjective)).trans
      (chartDifferential_range I f hf φ hφ y hy)
  rw [← hr, starProjection_range_eq (D y) (hinj y hy)]

set_option backward.isDefEq.respectTransparency false in
/-- The ambient orthogonal projection onto the normal varies continuously with the base point. -/
theorem continuous_normalProjection (f : M → E)
    (hf : IsSmoothEmbedding I (modelWithCornersSelf ℝ E) 2 f) :
    Continuous (fun x => (normalSpace I f x).starProjection) := by
  simp_rw [normalSpace, Submodule.starProjection_orthogonal]
  convert ((continuous_const (y := ContinuousLinearMap.id ℝ E)).sub
    (continuous_tangentProjection I f hf)) using 1
  rfl

end Causalean.Mathlib.Geometry.Manifold.EmbeddedNormalGeometry
