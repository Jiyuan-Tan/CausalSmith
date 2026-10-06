module
public import Causalean.Mathlib.Geometry.Manifold.EmbeddedNormalGeometry.Tangent
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Second fundamental forms and shape operators

This module develops the normal-valued second fundamental form of a
finite-dimensional Euclidean C² embedded manifold, including model-with-corners
boundary points. It also provides the algebraic shape operator and its
determinant interface. All constructions are chart independent.
-/
@[expose] public section

open Module
open Manifold Set
open scoped ContDiff InnerProductSpace Topology

namespace Causalean.Mathlib.Geometry.Manifold.EmbeddedNormalGeometry

section ShapeAlgebra
variable {T N : Type*} [NormedAddCommGroup T] [InnerProductSpace ℝ T]
  [FiniteDimensional ℝ T] [NormedAddCommGroup N] [InnerProductSpace ℝ N]

/-- Pairing a normal-valued bilinear form with a normal vector gives a scalar bilinear form. -/
noncomputable def scalarSecondForm (B : T →L[ℝ] T →L[ℝ] N) (u : N) :
    T →L[ℝ] T →L[ℝ] ℝ :=
  ((innerSL ℝ u).postcomp T).comp B

/-- The shape operator is the Riesz representative of the scalar second form in its second
argument. -/
noncomputable def shapeOperator (B : T →L[ℝ] T →L[ℝ] N) (u : N) : T →L[ℝ] T :=
  InnerProductSpace.continuousLinearMapOfBilin (scalarSecondForm B u)

/-- The shape operator satisfies its defining inner-product identity. -/
theorem shapeOperator_inner (B : T →L[ℝ] T →L[ℝ] N) (u : N) (v w : T) :
    ⟪shapeOperator B u v, w⟫_ℝ = ⟪u, B v w⟫_ℝ := by
  exact InnerProductSpace.continuousLinearMapOfBilin_apply _ _ _

/-- Shape operators depend additively on the indexing normal vector. -/
theorem shapeOperator_add (B : T →L[ℝ] T →L[ℝ] N) (u z : N) :
    shapeOperator B (u + z) = shapeOperator B u + shapeOperator B z := by
  ext v
  apply ext_inner_right ℝ
  intro w
  simp [shapeOperator_inner, inner_add_left]

/-- Shape operators depend linearly on real rescaling of the indexing normal vector. -/
theorem shapeOperator_smul (B : T →L[ℝ] T →L[ℝ] N) (a : ℝ) (u : N) :
    shapeOperator B (a • u) = a • shapeOperator B u := by
  ext v
  apply ext_inner_right ℝ
  intro w
  simp [shapeOperator_inner, inner_smul_left]

/-- A symmetric normal-valued bilinear form gives self-adjoint shape operators. -/
theorem shapeOperator_selfAdjoint (B : T →L[ℝ] T →L[ℝ] N)
    (hB : ∀ v w, B v w = B w v) (u : N) : IsSelfAdjoint (shapeOperator B u) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro v w
  change ⟪shapeOperator B u v, w⟫_ℝ = ⟪v, shapeOperator B u w⟫_ℝ
  rw [shapeOperator_inner, ← real_inner_comm v (shapeOperator B u w), shapeOperator_inner, hB v w]

/-- The signed normal tube factor is the intrinsic determinant of identity minus the scaled shape
operator. -/
noncomputable def tubeDeterminant (B : T →L[ℝ] T →L[ℝ] N) (a : ℝ) (u : N) : ℝ :=
  LinearMap.det (LinearMap.id - a • (shapeOperator B u).toLinearMap)

/-- The tube determinant can be computed in any tangent basis without changing its value. -/
theorem tubeDeterminant_eq_matrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℝ T) (B : T →L[ℝ] T →L[ℝ] N) (a : ℝ) (u : N) :
    tubeDeterminant B a u =
      Matrix.det (LinearMap.toMatrix b b (LinearMap.id - a • (shapeOperator B u).toLinearMap)) := by
  exact (LinearMap.det_toMatrix b _).symm

/-- The tube determinant equals one at zero displacement. -/
theorem tubeDeterminant_zero (B : T →L[ℝ] T →L[ℝ] N) (u : N) :
    tubeDeterminant B 0 u = 1 := by
  simp [tubeDeterminant]

end ShapeAlgebra

section SecondFundamentalForm

variable {F E H M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] (I : ModelWithCorners ℝ F H) [IsManifold I 2 M]

omit [FiniteDimensional ℝ F] [ChartedSpace H M] [IsManifold I 2 M] in
/-- Every extended chart target is contained in the closure of its interior, including its
boundary points. -/
theorem extendedChart_target_subset_closure_interior (φ : OpenPartialHomeomorph M H) :
    (φ.extend I).target ⊆ closure (interior (φ.extend I).target) := by
  intro y hy
  have ho : IsOpen (I.symm ⁻¹' φ.target) := φ.open_target.preimage I.continuous_symm
  have hy' : y ∈ I.symm ⁻¹' φ.target ∩ Set.range I := by
    simpa only [φ.extend_target] using hy
  rw [mem_closure_iff_nhds]
  intro t ht
  obtain ⟨z, ⟨hzt, hzo⟩, hzi⟩ := mem_closure_iff_nhds.mp
    (I.range_subset_closure_interior hy'.2) _ (Filter.inter_mem ht (ho.mem_nhds hy'.1))
  refine ⟨z, hzt, ?_⟩
  rw [φ.extend_target, interior_inter, ho.interior_eq]
  exact ⟨hzo, hzi⟩

omit [FiniteDimensional ℝ F] [FiniteDimensional ℝ E] [IsManifold I 2 M] in
/-- Composing a C² embedding with an admissible inverse extended chart gives a C²
parametrization on the full chart target. -/
theorem contDiffOn_chartParametrization (f : M → E)
    (hf : IsSmoothEmbedding I (modelWithCornersSelf ℝ E) 2 f)
    (φ : OpenPartialHomeomorph M H) (hφ : φ ∈ IsManifold.maximalAtlas I 2 M) :
    ContDiffOn ℝ 2 (f ∘ (φ.extend I).symm) (φ.extend I).target := by
  apply ContMDiffOn.contDiffOn
  rw [φ.extend_target']
  exact hf.contMDiff.comp_contMDiffOn (contMDiffOn_extend_symm hφ)

/-- The local parametrization Hessian is its iterated derivative within the extended chart target.
-/
noncomputable def chartHessian (f : M → E) (φ : OpenPartialHomeomorph M H)
    (x : M) : F →L[ℝ] F →L[ℝ] E :=
  fderivWithin ℝ
    (fun y => fderivWithin ℝ (f ∘ (φ.extend I).symm) (φ.extend I).target y)
    (φ.extend I).target ((φ.extend I) x)

omit [FiniteDimensional ℝ F] [FiniteDimensional ℝ E] [IsManifold I 2 M] in
/-- Admissible C² local parametrizations have symmetric Hessians at every chart point. -/
theorem chartHessian_symmetric (f : M → E)
    (hf : IsSmoothEmbedding I (modelWithCornersSelf ℝ E) 2 f)
    (φ : OpenPartialHomeomorph M H) (hφ : φ ∈ IsManifold.maximalAtlas I 2 M)
    (x : M) (hx : x ∈ φ.source) (v w : F) :
    chartHessian I f φ x v w = chartHessian I f φ x w v := by
  have hx' : x ∈ (φ.extend I).source := by simpa using hx
  have hy := (φ.extend I).map_source hx'
  have hu : UniqueDiffOn ℝ (φ.extend I).target := by
    rw [φ.extend_target]
    exact I.uniqueDiffOn_preimage φ.open_target
  exact ((contDiffOn_chartParametrization I f hf φ hφ _ hy).isSymmSndFDerivWithinAt
    (by simp) hu (extendedChart_target_subset_closure_interior I φ hy) hy) v w

omit [FiniteDimensional ℝ F] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [IsManifold I 2 M] in
/-- On a chart overlap the transition is C² on the full second target locally, maps
locally into the first target, and identifies the two parametrizations. -/
private theorem chart_transition_data (f : M → E)
    (φ ψ : OpenPartialHomeomorph M H)
    (hφ : φ ∈ IsManifold.maximalAtlas I 2 M)
    (hψ : ψ ∈ IsManifold.maximalAtlas I 2 M)
    (x : M) (hxφ : x ∈ φ.source) (hxψ : x ∈ ψ.source) :
    let q := (φ.extend I) ∘ (ψ.extend I).symm
    let s := (ψ.extend I).target
    let y := (ψ.extend I) x
    ContDiffWithinAt ℝ 2 q s y ∧
      (∀ᶠ z in 𝓝[s] y, q z ∈ (φ.extend I).target) ∧
      (f ∘ (ψ.extend I).symm =ᶠ[𝓝[s] y] (f ∘ (φ.extend I).symm) ∘ q) := by
  dsimp only
  have hxψ' : x ∈ (ψ.extend I).source := by simpa using hxψ
  have hlocal : ∀ᶠ z in 𝓝[(ψ.extend I).target] ((ψ.extend I) x),
      (ψ.extend I).symm z ∈ φ.source := by
    have hc := (ψ.continuousAt_extend_symm (I := I) hxψ).continuousWithinAt
      (s := (ψ.extend I).target)
    have hn := hc.preimage_mem_nhdsWithin
      (φ.open_source.mem_nhds (by simpa only [(ψ.extend I).left_inv hxψ'] using hxφ))
    exact hn
  refine ⟨?_, ?_, ?_⟩
  · exact (I.contDiffWithinAt_extendCoordChange' hψ hφ hxψ hxφ).mono
      ψ.extend_target_subset_range
  · filter_upwards [hlocal] with z hz
    exact (φ.extend I).map_source (by simpa using hz)
  · filter_upwards [hlocal] with z hz
    dsimp only [Function.comp_apply]
    rw [(φ.extend I).left_inv (by simpa using hz)]

omit [FiniteDimensional ℝ F] [FiniteDimensional ℝ E] [IsManifold I 2 M] in
/-- The first derivative of a parametrization transforms by the derivative of the
chart transition, with derivatives taken on the full targets. -/
private theorem chartDifferential_change (f : M → E)
    (hf : IsSmoothEmbedding I (modelWithCornersSelf ℝ E) 2 f)
    (φ ψ : OpenPartialHomeomorph M H)
    (hφ : φ ∈ IsManifold.maximalAtlas I 2 M)
    (hψ : ψ ∈ IsManifold.maximalAtlas I 2 M)
    (x : M) (hxφ : x ∈ φ.source) (hxψ : x ∈ ψ.source) :
    chartDifferential I f ψ x = (chartDifferential I f φ x).comp
      (fderivWithin ℝ ((φ.extend I) ∘ (ψ.extend I).symm)
        (ψ.extend I).target ((ψ.extend I) x)) := by
  let q := (φ.extend I) ∘ (ψ.extend I).symm
  let s := (ψ.extend I).target
  let y := (ψ.extend I) x
  have hxψ' : x ∈ (ψ.extend I).source := by simpa using hxψ
  have hxφ' : x ∈ (φ.extend I).source := by simpa using hxφ
  have hy : y ∈ s := (ψ.extend I).map_source hxψ'
  have hqy : q y = (φ.extend I) x := by
    dsimp only [q, y, Function.comp_apply]; rw [(ψ.extend I).left_inv hxψ']
  obtain ⟨hq, hmap, heq⟩ := chart_transition_data I f φ ψ hφ hψ x hxφ hxψ
  have hu : UniqueDiffOn ℝ s := by
    dsimp only [s]; rw [ψ.extend_target]; exact I.uniqueDiffOn_preimage ψ.open_target
  have hdq := hq.differentiableWithinAt (by norm_num)
  have hg := (contDiffOn_chartParametrization I f hf φ hφ).differentiableOn
    (by norm_num) ((φ.extend I) x) ((φ.extend I).map_source hxφ')
  rw [← hqy] at hg
  have ht := tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within q
    hdq.continuousWithinAt hmap
  have hc := hg.hasFDerivWithinAt.comp_of_tendsto y hdq.hasFDerivWithinAt ht
  have heqy := heq.self_of_nhdsWithin hy
  have hd := (hc.congr_of_eventuallyEq heq heqy).fderivWithin (hu y hy)
  simpa only [chartDifferential, hqy] using hd

/-- The Hessian chart-change law has exactly one additional tangent-valued first-derivative term.

Differentiate the within-target chain rule for the transition map twice. The model with
corners supplies unique differentiability at boundary points. Work on the inverse image of
the chart-source overlap in the second chart target, which is a relative neighborhood of
the chart point. The transition need not map the entire second target into the first.
Use neighborhood congruence to return both derivatives to the displayed full targets.
`contDiffOn_chartParametrization` supplies the embedding regularity; the atlas supplies
transition regularity. The extra term must remain the actual transition Hessian, not an
unspecified tangent error. -/
theorem chartHessian_change (f : M → E)
    (hf : IsSmoothEmbedding I (modelWithCornersSelf ℝ E) 2 f)
    (φ ψ : OpenPartialHomeomorph M H)
    (hφ : φ ∈ IsManifold.maximalAtlas I 2 M)
    (hψ : ψ ∈ IsManifold.maximalAtlas I 2 M)
    (x : M) (hxφ : x ∈ φ.source) (hxψ : x ∈ ψ.source) (v w : F) :
    let q := (φ.extend I) ∘ (ψ.extend I).symm
    let s := (ψ.extend I).target
    let y := (ψ.extend I) x
    let D := fderivWithin ℝ q s y
    let Hq := fderivWithin ℝ (fun z => fderivWithin ℝ q s z) s y
    chartHessian I f ψ x v w = chartHessian I f φ x (D v) (D w) +
      chartDifferential I f φ x (Hq v w) := by
  let q := (φ.extend I) ∘ (ψ.extend I).symm
  let s := (ψ.extend I).target
  let t := (φ.extend I).target
  let y := (ψ.extend I) x
  let g := f ∘ (φ.extend I).symm
  let p := f ∘ (ψ.extend I).symm
  have hxψ' : x ∈ (ψ.extend I).source := by simpa using hxψ
  have hxφ' : x ∈ (φ.extend I).source := by simpa using hxφ
  have hy : y ∈ s := (ψ.extend I).map_source hxψ'
  have hqy : q y = (φ.extend I) x := by
    dsimp only [q, y, Function.comp_apply]; rw [(ψ.extend I).left_inv hxψ']
  have hqt : q y ∈ t := hqy ▸ (φ.extend I).map_source hxφ'
  have hs : UniqueDiffOn ℝ s := by
    dsimp only [s]; rw [ψ.extend_target]; exact I.uniqueDiffOn_preimage ψ.open_target
  have ht : UniqueDiffOn ℝ t := by
    dsimp only [t]; rw [φ.extend_target]; exact I.uniqueDiffOn_preimage φ.open_target
  obtain ⟨hq, hmap, _⟩ := chart_transition_data I f φ ψ hφ hψ x hxφ hxψ
  have hdq := hq.differentiableWithinAt (by norm_num)
  have hqder : DifferentiableWithinAt ℝ (fderivWithin ℝ q s) s y :=
    (hq.fderivWithin_right hs (m := 1) (by norm_num) hy).differentiableWithinAt
      (by norm_num)
  have hg : ContDiffOn ℝ 2 g t := contDiffOn_chartParametrization I f hf φ hφ
  have hgder := ((hg.fderivWithin ht (m := 1) (by norm_num)).differentiableOn
    (by norm_num) (q y) hqt).hasFDerivWithinAt
  have hto := tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within q
    hdq.continuousWithinAt hmap
  have houter := hgder.comp_of_tendsto y hdq.hasFDerivWithinAt hto
  have hc := houter.clm_comp hqder.hasFDerivWithinAt
  have heq : fderivWithin ℝ p s =ᶠ[𝓝[s] y]
      (fun z => (fderivWithin ℝ g t (q z)).comp (fderivWithin ℝ q s z)) := by
    have hlocal : ∀ᶠ z in 𝓝[s] y, (ψ.extend I).symm z ∈ φ.source :=
      (ψ.continuousAt_extend_symm (I := I) hxψ).continuousWithinAt.preimage_mem_nhdsWithin
        (φ.open_source.mem_nhds
          (by simpa only [(ψ.extend I).left_inv hxψ'] using hxφ))
    filter_upwards [hlocal, self_mem_nhdsWithin] with z hz hzs
    have hzψ : (ψ.extend I).symm z ∈ ψ.source := by
      simpa using (ψ.extend I).map_target hzs
    have hid := chartDifferential_change I f hf φ ψ hφ hψ
      ((ψ.extend I).symm z) hz hzψ
    simpa only [chartDifferential, (ψ.extend I).right_inv hzs,
      q, s, t, g, p, Function.comp_apply] using hid
  have hder := (hc.congr_of_eventuallyEq heq (heq.self_of_nhdsWithin hy)).fderivWithin
    (hs y hy)
  have happ := congrArg (fun L : F →L[ℝ] F →L[ℝ] E => L v w) hder
  change fderivWithin ℝ (fderivWithin ℝ p s) s y v w =
    fderivWithin ℝ (fderivWithin ℝ g t) t ((φ.extend I) x)
      (fderivWithin ℝ q s y v) (fderivWithin ℝ q s y w) +
      fderivWithin ℝ g t ((φ.extend I) x)
        (fderivWithin ℝ (fderivWithin ℝ q s) s y v w)
  simpa only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply, Function.comp_apply, hqy, add_comm] using happ

/-- Normal projection of the Hessian depends only on the two ambient tangent vectors, not on the
chart.

First obtain the within-target first-derivative chart-change identity. Injectivity from
`chartDifferential_injective` identifies the input vectors after the transition derivative.
Apply `chartHessian_change`, then remove its last term using `chartDifferential_range` and
orthogonality. These are conclusions of the existing embedding and atlas hypotheses. -/
theorem chart_normalHessian_congr (f : M → E)
    (hf : IsSmoothEmbedding I (modelWithCornersSelf ℝ E) 2 f)
    (φ ψ : OpenPartialHomeomorph M H)
    (hφ : φ ∈ IsManifold.maximalAtlas I 2 M)
    (hψ : ψ ∈ IsManifold.maximalAtlas I 2 M)
    (x : M) (hxφ : x ∈ φ.source) (hxψ : x ∈ ψ.source)
    (v w v' w' : F)
    (hv : chartDifferential I f φ x v = chartDifferential I f ψ x v')
    (hw : chartDifferential I f φ x w = chartDifferential I f ψ x w') :
    (normalSpace I f x).orthogonalProjectionOnto (chartHessian I f φ x v w) =
      (normalSpace I f x).orthogonalProjectionOnto (chartHessian I f ψ x v' w') := by
  let q := (φ.extend I) ∘ (ψ.extend I).symm
  let s := (ψ.extend I).target
  let y := (ψ.extend I) x
  let D := fderivWithin ℝ q s y
  have hD := chartDifferential_change I f hf φ ψ hφ hψ x hxφ hxψ
  have hvD : v = D v' := by
    apply chartDifferential_injective I f hf φ hφ x hxφ
    rw [hv, hD]
    rfl
  have hwD : w = D w' := by
    apply chartDifferential_injective I f hf φ hφ x hxφ
    rw [hw, hD]
    rfl
  have hchange := chartHessian_change I f hf φ ψ hφ hψ x hxφ hxψ v' w'
  dsimp only at hchange
  rw [← hvD, ← hwD] at hchange
  rw [hchange, map_add]
  have hzero : (normalSpace I f x).orthogonalProjectionOnto
      (chartDifferential I f φ x
        (fderivWithin ℝ (fderivWithin ℝ q s) s y v' w')) = 0 := by
    apply Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr
    rw [normalSpace, Submodule.orthogonal_orthogonal,
      ← chartDifferential_range I f hf φ hφ x hxφ]
    exact ⟨_, rfl⟩
  rw [hzero, add_zero]

/-- A chart model vector maps to a vector of the full extrinsic tangent space. -/
noncomputable def chartTangentVector (f : M → E)
    (hf : IsSmoothEmbedding I (modelWithCornersSelf ℝ E) 2 f)
    (φ : OpenPartialHomeomorph M H) (hφ : φ ∈ IsManifold.maximalAtlas I 2 M)
    (x : M) (hx : x ∈ φ.source) (v : F) : tangentSpace I f x :=
  ⟨chartDifferential I f φ x v, by
    rw [← chartDifferential_range I f hf φ hφ x hx]
    exact ⟨v, rfl⟩⟩

/-- Every full tangent vector is represented by a model vector in any admissible chart. -/
theorem chartTangentVector_surjective (f : M → E)
    (hf : IsSmoothEmbedding I (modelWithCornersSelf ℝ E) 2 f)
    (φ : OpenPartialHomeomorph M H) (hφ : φ ∈ IsManifold.maximalAtlas I 2 M)
    (x : M) (hx : x ∈ φ.source) :
    Function.Surjective (chartTangentVector I f hf φ hφ x hx) := by
  intro v
  have hv : (v : E) ∈ (chartDifferential I f φ x).toLinearMap.range := by
    simpa only [chartDifferential_range I f hf φ hφ x hx] using v.property
  obtain ⟨w, hw⟩ := hv
  exact ⟨w, Subtype.ext hw⟩

/-- An admissible parametrization differential continuously identifies the full model space
with the full extrinsic tangent space. -/
noncomputable def chartTangentEquiv (f : M → E)
    (hf : IsSmoothEmbedding I (modelWithCornersSelf ℝ E) 2 f)
    (φ : OpenPartialHomeomorph M H) (hφ : φ ∈ IsManifold.maximalAtlas I 2 M)
    (x : M) (hx : x ∈ φ.source) : F ≃L[ℝ] tangentSpace I f x := by
  let L : F →ₗ[ℝ] tangentSpace I f x :=
    (chartDifferential I f φ x).toLinearMap.codRestrict (tangentSpace I f x)
      (fun v => (chartTangentVector I f hf φ hφ x hx v).property)
  exact (LinearEquiv.ofBijective L
    ⟨fun v w h => chartDifferential_injective I f hf φ hφ x hx (congrArg Subtype.val h),
      chartTangentVector_surjective I f hf φ hφ x hx⟩).toContinuousLinearEquiv

/-- The chart tangent equivalence applies the parametrization differential. -/
theorem chartTangentEquiv_apply (f : M → E)
    (hf : IsSmoothEmbedding I (modelWithCornersSelf ℝ E) 2 f)
    (φ : OpenPartialHomeomorph M H) (hφ : φ ∈ IsManifold.maximalAtlas I 2 M)
    (x : M) (hx : x ∈ φ.source) (v : F) :
    chartTangentEquiv I f hf φ hφ x hx v = chartTangentVector I f hf φ hφ x hx v := rfl

/-- A symmetric normal-valued bilinear form simultaneously represents the Hessian in every
admissible chart.

Construct from one chart using its derivative equivalence onto the tangent range;
chart_normalHessian_congr and chartHessian_symmetric give all other charts. -/
theorem exists_secondFundamentalForm (f : M → E)
    (hf : IsSmoothEmbedding I (modelWithCornersSelf ℝ E) 2 f) (x : M) :
    ∃ B : tangentSpace I f x →L[ℝ] tangentSpace I f x →L[ℝ] normalSpace I f x,
      (∀ v w, B v w = B w v) ∧
      ∀ (φ : OpenPartialHomeomorph M H) (hφ : φ ∈ IsManifold.maximalAtlas I 2 M)
        (hx : x ∈ φ.source) (v w : F),
        B (chartTangentVector I f hf φ hφ x hx v)
          (chartTangentVector I f hf φ hφ x hx w) =
        (normalSpace I f x).orthogonalProjectionOnto (chartHessian I f φ x v w) := by
  let φ := chartAt H x
  have hφ : φ ∈ IsManifold.maximalAtlas I 2 M := IsManifold.chart_mem_maximalAtlas x
  have hx : x ∈ φ.source := mem_chart_source H x
  let e := chartTangentEquiv I f hf φ hφ x hx
  let H := (chartHessian I f φ x).bilinearComp e.symm.toContinuousLinearMap
    e.symm.toContinuousLinearMap
  let B := ((normalSpace I f x).orthogonalProjectionOnto.postcomp (tangentSpace I f x)).comp H
  refine ⟨B, ?_, ?_⟩
  · intro v w
    change (normalSpace I f x).orthogonalProjectionOnto
      (chartHessian I f φ x (e.symm v) (e.symm w)) = _
    rw [chartHessian_symmetric I f hf φ hφ x hx]
    rfl
  · intro ψ hψ hxψ v w
    change (normalSpace I f x).orthogonalProjectionOnto
      (chartHessian I f φ x (e.symm (chartTangentVector I f hf ψ hψ x hxψ v))
        (e.symm (chartTangentVector I f hf ψ hψ x hxψ w))) = _
    apply chart_normalHessian_congr I f hf φ ψ hφ hψ x hx hxψ
    · exact congrArg Subtype.val (e.apply_symm_apply _)
    · exact congrArg Subtype.val (e.apply_symm_apply _)

/-- The second fundamental form is the chart-independent normal-valued bilinear form of the
embedding. -/
noncomputable def secondFundamentalForm (f : M → E)
    (hf : IsSmoothEmbedding I (modelWithCornersSelf ℝ E) 2 f) (x : M) :
    tangentSpace I f x →L[ℝ] tangentSpace I f x →L[ℝ] normalSpace I f x :=
  Classical.choose (exists_secondFundamentalForm I f hf x)

/-- The second fundamental form is symmetric in its full tangent arguments. -/
theorem secondFundamentalForm_symmetric (f : M → E)
    (hf : IsSmoothEmbedding I (modelWithCornersSelf ℝ E) 2 f) (x : M)
    (v w : tangentSpace I f x) :
    secondFundamentalForm I f hf x v w = secondFundamentalForm I f hf x w v :=
  (Classical.choose_spec (exists_secondFundamentalForm I f hf x)).1 v w

/-- A [smooth Euclidean embedding `f`](hyp:f) with [embedding certificate
`hf`](hyp:hf), [model with corners `I`](hyp:I), and [an admissible chart `φ` at
`x` with atlas and source conditions `hφ` and `hx`](hyp:φ,hφ,x,hx), has [a
second fundamental form whose value on the indicated directions `v` and
`w`](hyp:v,w) equal to [the normal component of its chart Hessian](goal). -/
theorem secondFundamentalForm_chart (f : M → E)
    (hf : IsSmoothEmbedding I (modelWithCornersSelf ℝ E) 2 f) (x : M)
    (φ : OpenPartialHomeomorph M H) (hφ : φ ∈ IsManifold.maximalAtlas I 2 M)
    (hx : x ∈ φ.source) (v w : F) :
    secondFundamentalForm I f hf x (chartTangentVector I f hf φ hφ x hx v)
      (chartTangentVector I f hf φ hφ x hx w) =
    (normalSpace I f x).orthogonalProjectionOnto (chartHessian I f φ x v w) :=
  (Classical.choose_spec (exists_secondFundamentalForm I f hf x)).2 φ hφ hx v w

/-- Any bilinear form representing all chart normal Hessians equals the second fundamental form. -/
theorem secondFundamentalForm_unique (f : M → E)
    (hf : IsSmoothEmbedding I (modelWithCornersSelf ℝ E) 2 f) (x : M)
    (B : tangentSpace I f x →L[ℝ] tangentSpace I f x →L[ℝ] normalSpace I f x)
    (hB : ∀ (φ : OpenPartialHomeomorph M H) (hφ : φ ∈ IsManifold.maximalAtlas I 2 M)
      (hx : x ∈ φ.source) (v w : F),
      B (chartTangentVector I f hf φ hφ x hx v)
        (chartTangentVector I f hf φ hφ x hx w) =
      (normalSpace I f x).orthogonalProjectionOnto (chartHessian I f φ x v w)) :
    B = secondFundamentalForm I f hf x := by
  let φ := chartAt H x
  have hφ : φ ∈ IsManifold.maximalAtlas I 2 M := IsManifold.chart_mem_maximalAtlas x
  have hx : x ∈ φ.source := mem_chart_source H x
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  obtain ⟨v', rfl⟩ := chartTangentVector_surjective I f hf φ hφ x hx v
  obtain ⟨w', rfl⟩ := chartTangentVector_surjective I f hf φ hφ x hx w
  exact (hB φ hφ hx v' w').trans
    (secondFundamentalForm_chart I f hf x φ hφ hx v' w').symm

/-- The extrinsic shape operator uses the full tangent metric and is indexed by a normal vector. -/
noncomputable def embeddingShapeOperator (f : M → E)
    (hf : IsSmoothEmbedding I (modelWithCornersSelf ℝ E) 2 f) (x : M)
    (u : normalSpace I f x) : tangentSpace I f x →L[ℝ] tangentSpace I f x :=
  shapeOperator (secondFundamentalForm I f hf x) u

/-- The extrinsic shape operator satisfies the geometric inner-product identity. -/
theorem embeddingShapeOperator_inner (f : M → E)
    (hf : IsSmoothEmbedding I (modelWithCornersSelf ℝ E) 2 f) (x : M)
    (u : normalSpace I f x) (v w : tangentSpace I f x) :
    ⟪embeddingShapeOperator I f hf x u v, w⟫_ℝ =
      ⟪u, secondFundamentalForm I f hf x v w⟫_ℝ :=
  shapeOperator_inner _ _ _ _

/-- Every extrinsic shape operator is self-adjoint, including at boundary points. -/
theorem embeddingShapeOperator_selfAdjoint (f : M → E)
    (hf : IsSmoothEmbedding I (modelWithCornersSelf ℝ E) 2 f) (x : M)
    (u : normalSpace I f x) : IsSelfAdjoint (embeddingShapeOperator I f hf x u) :=
  shapeOperator_selfAdjoint _ (secondFundamentalForm_symmetric I f hf x) u

end SecondFundamentalForm

end Causalean.Mathlib.Geometry.Manifold.EmbeddedNormalGeometry
