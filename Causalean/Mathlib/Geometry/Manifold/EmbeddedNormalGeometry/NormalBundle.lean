module
public import Causalean.Mathlib.Geometry.Manifold.EmbeddedNormalGeometry.Tangent
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.Analysis.InnerProductSpace.Orthonormal
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.Probability.Kernel.MeasurableLIntegral

/-!
# Normal disk bundles and fiber volume

This module supplies closed normal disk bundles, normal coordinates, and
ambient Euclidean volume measures on varying finite-dimensional normal fibers.
Continuous projection families yield measurable finite kernels and iterated
integration formulas; the embedded-manifold interface specializes these results
to C² Euclidean embeddings, including boundary and zero-codimension cases.
-/
@[expose] public section

open Manifold MeasureTheory ProbabilityTheory Set
open scoped ContDiff ENNReal EuclideanGeometry

namespace Causalean.Mathlib.Geometry.Manifold.EmbeddedNormalGeometry

section ProjectionFrames

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A projection close to the identity on a subspace is injective on that subspace. -/
private theorem projection_restriction_injective (P Q : Submodule ℝ E)
    (h : ‖P.starProjection - Q.starProjection‖ < 1) :
    Function.Injective (Q.orthogonalProjectionOnto.comp P.subtypeL) := by
  apply (injective_iff_map_eq_zero (Q.orthogonalProjectionOnto.comp P.subtypeL)).mpr
  intro v hv
  have hz : Q.starProjection (v : E) = 0 := by
    change Q.orthogonalProjectionOnto (v : E) = 0 at hv
    exact congrArg (fun w : Q => (w : E)) hv
  have hn := (P.starProjection - Q.starProjection).le_opNorm (v : E)
  rw [sub_apply, P.starProjection_mem_subspace_eq_self, hz, sub_zero] at hn
  have he : (v : E) = 0 := by
    by_contra he
    have hp : 0 < ‖(v : E)‖ := norm_pos_iff.mpr he
    have hlt := mul_lt_mul_of_pos_right h hp
    rw [one_mul] at hlt
    exact (not_lt_of_ge hn) hlt
  exact Subtype.ext he

/-- Orthogonal projections less than one apart in operator norm have subspaces of equal dimension.

Restrict each projection to the other subspace: distance less than one
forces injectivity, giving both dimension inequalities. -/
theorem finrank_eq_of_projection_close (P Q : Submodule ℝ E)
    (h : ‖P.starProjection - Q.starProjection‖ < 1) :
    Module.finrank ℝ P = Module.finrank ℝ Q := by
  apply Nat.le_antisymm
  · exact LinearMap.finrank_le_finrank_of_injective
      (projection_restriction_injective P Q h)
  · exact LinearMap.finrank_le_finrank_of_injective
      (projection_restriction_injective Q P (by simpa [norm_sub_rev] using h))

variable {X : Type*} [TopologicalSpace X]

omit [FiniteDimensional ℝ E] in
/-- Gram-Schmidt is continuous on a set where all input families are independent. -/
private theorem continuousOn_gramSchmidt {n : ℕ} (f : X → Fin n → E)
    {U : Set X} (hf : ∀ i, ContinuousOn (fun y => f y i) U)
    (hi : ∀ y ∈ U, LinearIndependent ℝ (f y)) (i : Fin n) :
    ContinuousOn (fun y => InnerProductSpace.gramSchmidt ℝ (f y) i) U := by
  classical
  refine (wellFounded_lt (α := Fin n)).induction
    (C := fun i => ContinuousOn (fun y => InnerProductSpace.gramSchmidt ℝ (f y) i) U)
    i (fun i ih => ?_)
  have he : (fun y => InnerProductSpace.gramSchmidt ℝ (f y) i) =
      (fun y => f y i - ∑ j ∈ Finset.Iio i,
        (ℝ ∙ InnerProductSpace.gramSchmidt ℝ (f y) j).starProjection (f y i)) :=
    funext fun y => InnerProductSpace.gramSchmidt_def ℝ (f y) i
  rw [he]
  simp_rw [Submodule.starProjection_singleton]
  apply (hf i).sub
  apply continuousOn_finsetSum
  intro j hj
  have hc := ih j (Finset.mem_Iio.mp hj)
  apply ContinuousOn.smul
  · apply ContinuousOn.div
    · exact hc.inner (hf i)
    · exact hc.norm.pow 2
    · intro y hy
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr
        (InnerProductSpace.gramSchmidt_ne_zero j (hi y hy)))
  · exact hc

omit [FiniteDimensional ℝ E] in
/-- Normalizing Gram-Schmidt preserves continuity on independent input families. -/
private theorem continuousOn_gramSchmidtNormed {n : ℕ} (f : X → Fin n → E)
    {U : Set X} (hf : ∀ i, ContinuousOn (fun y => f y i) U)
    (hi : ∀ y ∈ U, LinearIndependent ℝ (f y)) (i : Fin n) :
    ContinuousOn (fun y => InnerProductSpace.gramSchmidtNormed ℝ (f y) i) U := by
  have hc := continuousOn_gramSchmidt f hf hi i
  unfold InnerProductSpace.gramSchmidtNormed
  exact (hc.norm.inv₀ (fun y hy => norm_ne_zero_iff.mpr
    (InnerProductSpace.gramSchmidt_ne_zero i (hi y hy)))).smul hc

/-- A continuous projection family admits a local continuous isometric frame
onto each fiber.

Project a reference orthonormal basis onto nearby fibers, use the close-projection
rank lemma and Gram-Schmidt to orthonormalize continuously. Only local continuity
is asserted; the frame is unrestricted outside the neighborhood. -/
theorem exists_local_isometricFrame (P : X → Submodule ℝ E)
    (hP : Continuous (fun x => (P x).starProjection)) (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ e : X → ((P x) →L[ℝ] E), ContinuousOn e U ∧
        ∀ y ∈ U, Isometry (e y) ∧ (e y).toLinearMap.range = P y := by
  classical
  let U : Set X := {y | ‖(P x).starProjection - (P y).starProjection‖ < 1}
  have hU : IsOpen U := isOpen_lt (continuous_const.sub hP).norm continuous_const
  have hx : x ∈ U := by simp [U]
  let b := stdOrthonormalBasis ℝ (P x)
  let f : X → Fin (Module.finrank ℝ (P x)) → E :=
    fun y i => (P y).starProjection (b i : E)
  have hf : ∀ i, ContinuousOn (fun y => f y i) U := fun i =>
    (hP.clm_apply continuous_const).continuousOn
  have hi : ∀ y ∈ U, LinearIndependent ℝ (f y) := by
    intro y hy
    let L := (P y).orthogonalProjectionOnto.comp (P x).subtypeL
    have hL := projection_restriction_injective (P x) (P y) hy
    have hli := b.toBasis.linearIndependent.map' L.toLinearMap
      (LinearMap.ker_eq_bot.mpr hL)
    exact hli.map' (P y).subtype (LinearMap.ker_eq_bot.mpr (Submodule.injective_subtype _))
  let g := fun y => InnerProductSpace.gramSchmidtNormed ℝ (f y)
  let e : X → ((P x) →L[ℝ] E) :=
    fun y => (b.toBasis.constr ℝ (g y)).toContinuousLinearMap
  refine ⟨U, hU, hx, e, ?_, ?_⟩
  · apply continuousOn_clm_apply.mpr
    intro v
    change ContinuousOn (fun y => b.toBasis.constr ℝ (g y) v) U
    simp_rw [Module.Basis.constr_apply_fintype]
    apply continuousOn_finsetSum
    intro i _
    exact continuousOn_const.smul (continuousOn_gramSchmidtNormed f hf hi i)
  · intro y hy
    have ho := InnerProductSpace.gramSchmidtNormed_orthonormal (hi y hy)
    have heiso : Isometry (e y) := by
      have horth : Orthonormal ℝ ((b.toBasis.constr ℝ (g y)) ∘ b.toBasis) := by
        simpa only [Function.comp_def, Module.Basis.constr_basis] using ho
      exact ((b.toBasis.constr ℝ (g y)).isometryOfOrthonormal
        b.orthonormal horth).isometry
    refine ⟨heiso, ?_⟩
    have hspan : (e y).toLinearMap.range = Submodule.span ℝ (Set.range (f y)) := by
      change (b.toBasis.constr ℝ (g y)).range = _
      rw [Module.Basis.constr_range, InnerProductSpace.span_gramSchmidtNormed_range,
        InnerProductSpace.span_gramSchmidt]
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [hspan]
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact (P y).starProjection_apply_mem _
    · rw [LinearMap.finrank_range_of_inj heiso.injective]
      exact finrank_eq_of_projection_close (P x) (P y) hy

end ProjectionFrames

section NormalDiskBundle
variable {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The closed unit normal disk bundle consists of orthogonal normal vectors of norm at most one. -/
def normalDiskSet (T : X → Submodule ℝ E) : Set (X × E) :=
  {z | z.2 ∈ (T z.1)ᗮ ∧ ‖z.2‖ ≤ 1}

/-- The normal disk bundle carries the topology inherited from base times ambient space. -/
abbrev NormalDiskBundle (T : X → Submodule ℝ E) := {z : X × E // z ∈ normalDiskSet T}

/-- A continuous tangent projection makes the unit normal disk bundle closed in base times ambient
space.

Rewrite normal membership as `T(x).starProjection u = 0`; continuity of operator evaluation
gives a closed zero locus, intersected with the closed norm constraint. -/
theorem isClosed_normalDiskSet (T : X → Submodule ℝ E)
    (hT : Continuous (fun x => (T x).starProjection)) : IsClosed (normalDiskSet T) := by
  have hp : Continuous (fun z : X × E => (T z.1).starProjection z.2) :=
    (hT.comp continuous_fst).clm_apply continuous_snd
  have hn : Continuous (fun z : X × E => ‖z.2‖) := continuous_snd.norm
  convert (isClosed_eq hp (continuous_const (y := (0 : E)))).inter
    (isClosed_le hn (continuous_const (y := (1 : ℝ)))) using 1
  ext z
  simp only [normalDiskSet, Set.mem_ofPred_eq, Set.mem_inter_iff,
    Submodule.starProjection_apply_eq_zero_iff]

/-- Normal coordinates add a scaled fiber vector to the embedded base point. -/
def normalCoordinate (T : X → Submodule ℝ E) (f : X → E) (a : ℝ)
    (z : NormalDiskBundle T) : E :=
  f z.val.1 + a • z.val.2

omit [FiniteDimensional ℝ E] in
/-- The normal-coordinate map is continuous for every real scaling parameter. -/
@[fun_prop] theorem continuous_normalCoordinate (T : X → Submodule ℝ E) (f : X → E)
    (hf : Continuous f) (a : ℝ) : Continuous (normalCoordinate T f a) := by
  exact (hf.comp (continuous_fst.comp continuous_subtype_val)).add
    ((continuous_snd.comp continuous_subtype_val).const_smul a)

variable [MeasurableSpace X] [BorelSpace X] [MeasurableSpace E] [BorelSpace E]

/-- The unit normal disk bundle is a Borel subset of base times ambient space. -/
theorem measurableSet_normalDiskSet (T : X → Submodule ℝ E)
    (hT : Continuous (fun x => (T x).starProjection)) : MeasurableSet (normalDiskSet T) :=
  (isClosed_normalDiskSet T hT).measurableSet

/-- Continuous normal coordinates are Borel measurable on the normal disk bundle. -/
@[fun_prop] theorem measurable_normalCoordinate (T : X → Submodule ℝ E) (f : X → E)
    (hf : Continuous f) (a : ℝ) : Measurable (normalCoordinate T f a) :=
  (continuous_normalCoordinate T f hf a).measurable

end NormalDiskBundle

section FiberVolume
open scoped ENNReal EuclideanGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Intrinsic Euclidean volume on a plane is its normalized Hausdorff measure of the plane
dimension. -/
theorem plane_volume_eq_hausdorff (K : Submodule ℝ E) :
    (volume : Measure K) = Measure.euclideanHausdorffMeasure (Module.finrank ℝ K) :=
  InnerProductSpace.euclideanHausdorffMeasure_eq_volume.symm

/-- Fiber volume is intrinsic Euclidean volume pushed forward by inclusion into the ambient space.
-/
noncomputable def fiberVolume (K : Submodule ℝ E) : Measure E :=
  Measure.map (fun v : K => (v : E)) volume

/-- The ambient fiber volume is normalized Hausdorff measure restricted to the isometric plane. -/
theorem fiberVolume_eq_hausdorff (K : Submodule ℝ E) :
    fiberVolume K =
      (Measure.euclideanHausdorffMeasure (Module.finrank ℝ K) : Measure E).restrict K := by
  unfold fiberVolume
  rw [plane_volume_eq_hausdorff]
  have h : Isometry (fun v : K => (v : E)) := fun _ _ => rfl
  simpa using h.map_euclideanHausdorffMeasure (d := Module.finrank ℝ K)

/-- Zero-dimensional normal volume is the unit point mass at the zero vector. -/
theorem fiberVolume_bot : fiberVolume (⊥ : Submodule ℝ E) = Measure.dirac 0 := by
  rw [fiberVolume_eq_hausdorff]
  simp only [finrank_bot, Measure.euclideanHausdorffMeasure_zero,
    Submodule.bot_coe, Measure.restrict_singleton, Measure.hausdorffMeasure_zero_singleton,
    one_smul]

/-- The fiber disk volume restricts intrinsic fiber volume to the ambient closed unit ball. -/
noncomputable def fiberDiskVolume (K : Submodule ℝ E) : Measure E :=
  (fiberVolume K).restrict (Metric.closedBall 0 1)

/-- Every closed unit fiber disk has finite Euclidean volume, including the zero-dimensional disk.
-/
theorem fiberDiskVolume_finite (K : Submodule ℝ E) : fiberDiskVolume K Set.univ < ⊤ := by
  unfold fiberDiskVolume fiberVolume
  rw [Measure.restrict_apply_univ,
    Measure.map_apply continuous_subtype_val.measurable measurableSet_closedBall]
  have hpre : (fun v : K => (v : E)) ⁻¹' Metric.closedBall 0 1 =
      Metric.closedBall (0 : K) 1 := by
    ext v
    simp [Metric.mem_closedBall, dist_zero_right]
  rw [hpre]
  exact (isCompact_closedBall (0 : K) 1).measure_lt_top

/-- Fiber disk volume is supported on vectors in the fiber with norm at most one. -/
theorem fiberDiskVolume_ae_mem (K : Submodule ℝ E) :
    ∀ᵐ u ∂fiberDiskVolume K, u ∈ K ∧ ‖u‖ ≤ 1 := by
  have hK : ∀ᵐ u ∂fiberVolume K, u ∈ K := by
    rw [fiberVolume_eq_hausdorff]
    exact ae_restrict_mem K.closed_of_finiteDimensional.measurableSet
  filter_upwards [ae_restrict_of_ae hK,
    ae_restrict_mem (μ := fiberVolume K) measurableSet_closedBall] with u hu hball
  exact ⟨hu, by simpa [Metric.mem_closedBall, dist_zero_right] using hball⟩

/-- The volumes of unit disks in all subspaces have one finite ambient-dimension bound.

Each fiber is isometric to Euclidean space of its finrank; take the maximum of unit-ball
volumes over the finitely many dimensions up to ambient finrank. -/
theorem fiberDiskVolume_uniform_bound :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ K : Submodule ℝ E, fiberDiskVolume K Set.univ ≤ C := by
  classical
  let V : ℕ → ℝ≥0∞ := fun d =>
    volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)
  have hV (d : ℕ) : V d < ⊤ :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) 1).measure_lt_top
  have hmass (K : Submodule ℝ E) : fiberDiskVolume K Set.univ =
      V (Module.finrank ℝ K) := by
    unfold fiberDiskVolume fiberVolume
    rw [Measure.restrict_apply_univ,
      Measure.map_apply continuous_subtype_val.measurable measurableSet_closedBall]
    have hpre : (fun v : K => (v : E)) ⁻¹' Metric.closedBall 0 1 =
        Metric.closedBall (0 : K) 1 := by
      ext v
      simp [Metric.mem_closedBall, dist_zero_right]
    rw [hpre, ← (stdOrthonormalBasis ℝ K).measurePreserving_repr_symm.measure_preimage
      measurableSet_closedBall.nullMeasurableSet]
    simp only [LinearIsometryEquiv.preimage_closedBall, LinearIsometryEquiv.symm_symm,
      map_zero]
    rfl
  refine ⟨∑ d : Fin (Module.finrank ℝ E + 1), V d, ?_, ?_⟩
  · exact ENNReal.sum_lt_top.mpr fun d _ => hV d
  · intro K
    rw [hmass K]
    let d : Fin (Module.finrank ℝ E + 1) :=
      ⟨Module.finrank ℝ K, Nat.lt_succ_of_le K.finrank_le⟩
    change V (d : ℕ) ≤ ∑ i : Fin (Module.finrank ℝ E + 1), V (i : ℕ)
    exact Finset.single_le_sum (s := Finset.univ) (a := d)
      (f := fun i : Fin (Module.finrank ℝ E + 1) => V (i : ℕ))
      (fun _ _ => zero_le) (Finset.mem_univ d)

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Continuous orthogonal projections give a measurable family of intrinsic ambient fiber volumes.

Use `exists_local_isometricFrame` to reduce locally to a fixed Euclidean
fiber; no global frame or chosen orientation is assumed. Alternatively prove continuity of
integrals of compactly supported continuous test functions and use the measurable structure on
Radon measures. -/
@[fun_prop] theorem measurable_fiberVolume (P : X → Submodule ℝ E)
    (hP : Continuous (fun x => (P x).starProjection)) :
    Measurable (fun x => fiberVolume (P x)) := by
  classical
  -- Work on the second-countable image of the projection operator, rather than X.
  let S : Set (E →L[ℝ] E) := Set.range (fun K : Submodule ℝ E => K.starProjection)
  let : MeasurableSpace (E →L[ℝ] E) := borel (E →L[ℝ] E)
  have : BorelSpace (E →L[ℝ] E) := ⟨rfl⟩
  let Q : S → Submodule ℝ E := fun y => y.property.choose
  have hQ (y : S) : (Q y).starProjection = y.val := y.property.choose_spec
  have hQc : Continuous (fun y => (Q y).starProjection) := by
    simpa only [hQ] using (continuous_subtype_val : Continuous (fun y : S => y.val))
  have hlocal (x : S) : ∃ U : Set S, IsOpen U ∧ x ∈ U ∧
      Measurable (fun y : U => fiberVolume (Q y)) := by
    obtain ⟨U, hU, hx, e, he, heiso⟩ := exists_local_isometricFrame Q hQc x
    refine ⟨U, hU, hx, ?_⟩
    have hmap (y : U) : Measure.map (e y) volume = fiberVolume (Q y) := by
      obtain ⟨hi, hr⟩ := heiso y y.property
      have hd : Module.finrank ℝ (Q x) = Module.finrank ℝ (Q y) := by
        rw [← hr, LinearMap.finrank_range_of_inj hi.injective]
      rw [plane_volume_eq_hausdorff, hi.map_euclideanHausdorffMeasure,
        fiberVolume_eq_hausdorff, hd]
      congr 1
      exact congrArg (fun K : Submodule ℝ E => (K : Set E)) hr
    have hj : Measurable (fun z : U × Q x => e z.1 z.2) :=
      ((he.domRestrict.comp continuous_fst).clm_apply continuous_snd).measurable
    apply Measure.measurable_of_measurable_coe
    intro A hA
    have hm := measurable_measure_prodMk_left (ν := (volume : Measure (Q x)))
      (hA.preimage hj)
    have hemeas (y : U) : Measurable (e y) := (e y).continuous.measurable
    simpa only [← hmap, Measure.map_apply (hemeas _) hA, Set.preimage_preimage,
      Function.comp_def] using hm
  choose U hU hx hmeas using hlocal
  obtain ⟨t, ht, hcover⟩ := countable_cover_nhds (fun x => (hU x).mem_nhds (hx x))
  have hmeasQ : Measurable (fun y => fiberVolume (Q y)) := by
    intro A hA
    have hpre : (fun y => fiberVolume (Q y)) ⁻¹' A =
        ⋃ x ∈ t, ((↑) : U x → S) ''
          ((fun y : U x => fiberVolume (Q y)) ⁻¹' A) := by
      ext y
      constructor
      · intro hy
        have hycover : y ∈ ⋃ x ∈ t, U x := by rw [hcover]; trivial
        obtain ⟨x, hxt, hyU⟩ := Set.mem_iUnion₂.mp hycover
        exact Set.mem_iUnion₂.mpr ⟨x, hxt, ⟨⟨y, hyU⟩, hy, rfl⟩⟩
      · intro hy
        obtain ⟨x, _, z, hz, rfl⟩ := Set.mem_iUnion₂.mp hy
        exact hz
    rw [hpre]
    exact MeasurableSet.biUnion ht (fun x _ => (hU x).measurableSet.subtype_image
      (hmeas x hA))
  let f : X → S := fun x => ⟨(P x).starProjection, ⟨P x, rfl⟩⟩
  have hf : Measurable f := hP.measurable.subtype_mk
  have hQP (x : X) : Q (f x) = P x := by
    have hh : (Q (f x)).starProjection = (P x).starProjection := hQ (f x)
    have hr := congrArg (fun L : E →L[ℝ] E => L.toLinearMap.range) hh
    simpa only [Submodule.range_starProjection] using hr
  simpa only [Function.comp_def, hQP] using hmeasQ.comp hf

/-- Continuous orthogonal projections give a measurable family of closed unit fiber disk volumes. -/
@[fun_prop] theorem measurable_fiberDiskVolume (P : X → Submodule ℝ E)
    (hP : Continuous (fun x => (P x).starProjection)) :
    Measurable (fun x => fiberDiskVolume (P x)) := by
  apply Measure.measurable_of_measurable_coe
  intro A hA
  simpa only [fiberDiskVolume, Measure.restrict_apply hA, Function.comp_def] using
    (Measure.measurable_coe (hA.inter measurableSet_closedBall)).comp
      (measurable_fiberVolume P hP)

/-- The varying Euclidean fiber volumes form a measurable kernel into the ambient space. -/
noncomputable def fiberVolumeKernel (P : X → Submodule ℝ E)
    (hP : Continuous (fun x => (P x).starProjection)) : Kernel X E :=
  ⟨fun x => fiberVolume (P x), measurable_fiberVolume P hP⟩

/-- The varying unit fiber disks form a measurable kernel into the ambient space. -/
noncomputable def fiberDiskVolumeKernel (P : X → Submodule ℝ E)
    (hP : Continuous (fun x => (P x).starProjection)) : Kernel X E :=
  ⟨fun x => fiberDiskVolume (P x), measurable_fiberDiskVolume P hP⟩

/-- The disk-volume kernel is uniformly finite and hence supports kernel Fubini integration. -/
noncomputable instance fiberDiskVolumeKernel_isFinite (P : X → Submodule ℝ E)
    (hP : Continuous (fun x => (P x).starProjection)) :
    IsFiniteKernel (fiberDiskVolumeKernel P hP) := by
  obtain ⟨C, hC, hbound⟩ := fiberDiskVolume_uniform_bound (E := E)
  exact ⟨⟨C, hC, fun x => hbound (P x)⟩⟩

/-- Integrating a nonnegative jointly measurable function over varying fiber disks gives a
measurable base function. -/
theorem measurable_lintegral_fiberDiskVolume (P : X → Submodule ℝ E)
    (hP : Continuous (fun x => (P x).starProjection))
    (g : X × E → ℝ≥0∞) (hg : Measurable g) :
    Measurable (fun x => ∫⁻ u, g (x, u) ∂fiberDiskVolume (P x)) := by
  exact hg.lintegral_kernel_prod_right' (κ := fiberDiskVolumeKernel P hP)

/-- Integration over the base-disk measure equals iterated integration over base and normal
fibers. -/
theorem lintegral_fiberDiskVolume_compProd (P : X → Submodule ℝ E)
    (hP : Continuous (fun x => (P x).starProjection)) (μ : Measure X) [SFinite μ]
    (g : X × E → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ z, g z ∂(μ ⊗ₘ fiberDiskVolumeKernel P hP) =
      ∫⁻ x, ∫⁻ u, g (x, u) ∂fiberDiskVolume (P x) ∂μ := by
  exact Measure.lintegral_compProd hg

end FiberVolume

section EmbeddedIntegration

variable {F E H M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] (I : ModelWithCorners ℝ F H) [IsManifold I 2 M]
  [MeasurableSpace M] [BorelSpace M] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace M] [BorelSpace M] [MeasurableSpace E] [BorelSpace E] in
/-- The normal disk bundle of a C² embedding is closed relative to manifold times ambient space. -/
theorem embedding_normalDiskSet_isClosed (f : M → E)
    (hf : IsSmoothEmbedding I (modelWithCornersSelf ℝ E) 2 f) :
    IsClosed (normalDiskSet (tangentSpace I f)) :=
  isClosed_normalDiskSet _ (continuous_tangentProjection I f hf)

/-- The embedded normal disk bundle is a Borel subset of manifold times ambient space. -/
theorem embedding_normalDiskSet_measurable (f : M → E)
    (hf : IsSmoothEmbedding I (modelWithCornersSelf ℝ E) 2 f) :
    MeasurableSet (normalDiskSet (tangentSpace I f)) :=
  (embedding_normalDiskSet_isClosed I f hf).measurableSet

omit [FiniteDimensional ℝ F] [FiniteDimensional ℝ E] [IsManifold I 2 M]
  [MeasurableSpace M] [BorelSpace M] [MeasurableSpace E] [BorelSpace E] in
/-- Normal coordinates of a C² embedding are continuous on its unit normal disk bundle. -/
theorem embedding_normalCoordinate_continuous (f : M → E)
    (hf : IsSmoothEmbedding I (modelWithCornersSelf ℝ E) 2 f) (a : ℝ) :
    Continuous (normalCoordinate (tangentSpace I f) f a) :=
  continuous_normalCoordinate _ f hf.contMDiff.continuous a

omit [FiniteDimensional ℝ F] [IsManifold I 2 M] in
/-- Normal coordinates of a C² embedding are Borel measurable on its unit normal disk bundle. -/
theorem embedding_normalCoordinate_measurable (f : M → E)
    (hf : IsSmoothEmbedding I (modelWithCornersSelf ℝ E) 2 f) (a : ℝ) :
    Measurable (normalCoordinate (tangentSpace I f) f a) :=
  (embedding_normalCoordinate_continuous I f hf a).measurable

/-- Intrinsic Euclidean volumes of all normal fibers form a measurable kernel. -/
noncomputable def normalFiberVolumeKernel (f : M → E)
    (hf : IsSmoothEmbedding I (modelWithCornersSelf ℝ E) 2 f) : Kernel M E :=
  fiberVolumeKernel (normalSpace I f) (continuous_normalProjection I f hf)

/-- Euclidean volumes on the closed unit normal fibers form a measurable finite kernel. -/
noncomputable def normalDiskVolumeKernel (f : M → E)
    (hf : IsSmoothEmbedding I (modelWithCornersSelf ℝ E) 2 f) : Kernel M E :=
  fiberDiskVolumeKernel (normalSpace I f) (continuous_normalProjection I f hf)

/-- The normal disk kernel is uniformly finite over the embedded manifold. -/
noncomputable instance normalDiskVolumeKernel_isFinite (f : M → E)
    (hf : IsSmoothEmbedding I (modelWithCornersSelf ℝ E) 2 f) :
    IsFiniteKernel (normalDiskVolumeKernel I f hf) :=
  fiberDiskVolumeKernel_isFinite _ _

/-- The tube reference measure is the base measure combined with Euclidean unit normal disk
volumes. -/
noncomputable def normalDiskReferenceMeasure (f : M → E)
    (hf : IsSmoothEmbedding I (modelWithCornersSelf ℝ E) 2 f) (μ : Measure M) :
    Measure (M × E) := μ ⊗ₘ normalDiskVolumeKernel I f hf

/-- A [model with corners `I`](hyp:I), [a smooth Euclidean embedding `f` with
certificate `hf`](hyp:f,hf), [a base measure `μ`](hyp:μ), and [a nonnegative
measurable integrand `g` with measurability certificate `hg`](hyp:g,hg) give
[integration against the normal-disk reference measure equal to iterated
integration over the base and its normal fibers](goal). -/
theorem lintegral_normalDiskReferenceMeasure (f : M → E)
    (hf : IsSmoothEmbedding I (modelWithCornersSelf ℝ E) 2 f) (μ : Measure M) [SFinite μ]
    (g : M × E → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ z, g z ∂normalDiskReferenceMeasure I f hf μ =
      ∫⁻ x, ∫⁻ u, g (x, u) ∂fiberDiskVolume (normalSpace I f x) ∂μ :=
  lintegral_fiberDiskVolume_compProd _ _ μ g hg

end EmbeddedIntegration

end Causalean.Mathlib.Geometry.Manifold.EmbeddedNormalGeometry
