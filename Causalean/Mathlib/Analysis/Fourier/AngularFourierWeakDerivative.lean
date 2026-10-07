module
public import Causalean.Mathlib.Analysis.Fourier.AngularFourier
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Weak coordinate derivatives for angular Fourier transforms

This module supplies the spatial weak-derivative interface and proves the angular Fourier
multiplier identity. It also turns real coordinate-slice integration by parts into that
interface using the exact Euclidean/product-Lebesgue coordinate equivalence.
-/

public section

noncomputable section
open MeasureTheory
open scoped ContDiff Topology ENNReal

namespace Causalean.Mathlib.Analysis.Fourier
variable {p : ℕ}

/-- An integrable weak coordinate derivative of a function vanishes almost
everywhere outside the topological support of that function.

The function itself is not assumed locally integrable: where the product of the function with
a test-function derivative is not integrable, the weak-derivative hypothesis reads that integral
as zero, by the convention that the integral of a non-integrable function is zero.

Test in the open complement of `tsupport G` and reuse the open-set version of
`ae_eq_zero_of_integral_contDiff_smul_eq_zero`, complexifying real scalar tests.
The derivative itself need not have pointwise compact support. -/
theorem weakDerivative_zero_off_support (G D : Space p → ℂ) (r : Fin p)
    (hD : Integrable D volume)
    (hweak : HasWeakCoordinateDerivative G D r) :
    ∀ᵐ x ∂volume, x ∉ tsupport G → D x = 0 := by
  apply (isClosed_tsupport G).isOpen_compl.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hD.locallyIntegrable.locallyIntegrableOn _)
  intro g hg hgc hgs
  let ψ : Space p → ℂ := fun x => (g x : ℂ)
  have hψ : ContDiff ℝ ∞ ψ := Complex.ofRealCLM.contDiff.comp hg
  have hψc : HasCompactSupport ψ := hgc.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  have hψs : tsupport ψ ⊆ tsupport g :=
    tsupport_comp_subset (g := Complex.ofReal) Complex.ofReal_zero g
  have hz : (∫ x, G x * coordinateDerivative ψ r x) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [] with x
    by_cases hx : x ∈ tsupport G
    · have hn : x ∉ tsupport ψ := fun h => hgs (hψs h) hx
      simp [coordinateDerivative, fderiv_of_notMem_tsupport ℝ hn]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hw := hweak ψ hψ hψc
  have hi : (∫ x, D x * ψ x) = 0 := neg_eq_zero.mp (hw.symm.trans hz)
  simpa [ψ, mul_comm, Complex.real_smul] using hi

/-- A compact spatial support admits a smooth complex cutoff equal to one nearby. -/
private theorem exists_spatial_cutoff (G : Space p → ℂ) (hGc : HasCompactSupport G) :
    ∃ χ : Space p → ℂ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      ∀ x ∈ tsupport G, χ =ᶠ[𝓝 x] (fun _ => 1) := by
  obtain ⟨R, hR, hsub⟩ := hGc.isBounded.subset_ball_lt 0 (0 : Space p)
  let b : ContDiffBump (0 : Space p) :=
    { rIn := R, rOut := R + 1, rIn_pos := hR, rIn_lt_rOut := lt_add_one R }
  refine ⟨fun x => (b x : ℂ), Complex.ofRealCLM.contDiff.comp b.contDiff,
    b.hasCompactSupport.comp_left (g := Complex.ofReal) Complex.ofReal_zero, ?_⟩
  intro x hx
  filter_upwards [b.eventuallyEq_one_of_mem_ball (hsub hx)] with y hy
  simp only [hy, Pi.one_apply, Complex.ofReal_one]

/-- Products with an arbitrary smooth test and its coordinate derivative are
integrable for a compactly supported L1 function and its L1 weak derivative. -/
theorem integrable_weak_test_products (G D : Space p → ℂ) (r : Fin p)
    (hG : Integrable G volume) (hD : Integrable D volume)
    (hGc : HasCompactSupport G) (hweak : HasWeakCoordinateDerivative G D r)
    (φ : Space p → ℂ) (hφ : ContDiff ℝ ∞ φ) :
    Integrable (fun x => G x * coordinateDerivative φ r x) volume ∧
      Integrable (fun x => D x * φ x) volume := by
  obtain ⟨χ, hχ, hχc, hχone⟩ := exists_spatial_cutoff G hGc
  have hc : Continuous (coordinateDerivative φ r) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hGprod : Integrable (fun x => G x * (χ x * coordinateDerivative φ r x)) volume := by
    simpa only [smul_eq_mul, Pi.mul_apply] using
      hG.locallyIntegrable.integrable_smul_right_of_hasCompactSupport
        (hχ.continuous.mul hc) hχc.mul_right
  have hDprod : Integrable (fun x => D x * (χ x * φ x)) volume := by
    simpa only [smul_eq_mul, Pi.mul_apply] using
      hD.locallyIntegrable.integrable_smul_right_of_hasCompactSupport
        (hχ.continuous.mul hφ.continuous) hχc.mul_right
  constructor
  · apply hGprod.congr
    filter_upwards [] with x
    by_cases hx : x ∈ tsupport G
    · simp [(hχone x hx).eq_of_nhds]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  · apply hDprod.congr
    filter_upwards [weakDerivative_zero_off_support G D r hD hweak] with x hxD
    by_cases hx : x ∈ tsupport G
    · simp [(hχone x hx).eq_of_nhds]
    · simp [hxD hx]

/-- Spatial integration by parts extends from compact smooth tests to every
smooth test when the function has compact support and its weak
derivative is integrable.

The function itself is not assumed integrable: when its product with the test-function
derivative is not integrable, the left-hand integral, like the corresponding integrals in the
weak-derivative hypothesis, is zero by the convention that the integral of a non-integrable
function is zero.

Choose a smooth cutoff equal to one on a neighborhood of `tsupport G`, use
the product rule, and discard the outside-support derivative term using
`weakDerivative_zero_off_support`. This is a spatial statement, not a
Fourier multiplier premise. -/
theorem weakIBP_smooth_test (G D : Space p → ℂ) (r : Fin p)
    (hD : Integrable D volume)
    (hGc : HasCompactSupport G) (hweak : HasWeakCoordinateDerivative G D r)
    (φ : Space p → ℂ) (hφ : ContDiff ℝ ∞ φ) :
    (∫ x, G x * coordinateDerivative φ r x) = -(∫ x, D x * φ x) := by
  obtain ⟨χ, hχ, hχc, hχone⟩ := exists_spatial_cutoff G hGc
  have hw := hweak (fun x => χ x * φ x) (hχ.mul hφ) hχc.mul_right
  have hleft : (fun x => G x * coordinateDerivative (fun y => χ y * φ y) r x) =ᵐ[volume]
      (fun x => G x * coordinateDerivative φ r x) := by
    filter_upwards [] with x
    by_cases hx : x ∈ tsupport G
    · have hχx : χ x = 1 := (hχone x hx).eq_of_nhds
      have hχd : fderiv ℝ χ x = 0 := by
        simpa using (hχone x hx).fderiv_eq (𝕜 := ℝ)
      simp only [coordinateDerivative,
        fderiv_fun_mul ((hχ.differentiable (by simp)).differentiableAt)
          ((hφ.differentiable (by simp)).differentiableAt),
        hχx, hχd, add_apply, smul_apply, zero_apply, smul_zero, add_zero, one_smul]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hright : (fun x => D x * (χ x * φ x)) =ᵐ[volume] (fun x => D x * φ x) := by
    filter_upwards [weakDerivative_zero_off_support G D r hD hweak] with x hxD
    by_cases hx : x ∈ tsupport G
    · simp [(hχone x hx).eq_of_nhds]
    · simp [hxD hx]
  rw [integral_congr_ae hleft, integral_congr_ae hright] at hw
  exact hw

variable {p : ℕ}

/-- The angular exponential phase is smooth as a function of spatial position.

Use the smooth real-linear coordinate pairing, complex inclusion, and complex
exponential. Equivalently rewrite the phase as Mathlib's Fourier character at
the normalized inner-product frequency; no regularity of G is involved. -/
theorem contDiff_angular_phase (w : Space p) :
    ContDiff ℝ ∞ (fun u : Space p =>
      Complex.exp (-Complex.I * ((∑ r, w r * u r : ℝ) : ℂ))) := by
  have h : ContDiff ℝ ∞ (fun u : Space p => (innerSL ℝ w) u) :=
    (innerSL ℝ w).contDiff
  have hs : (fun u : Space p => (innerSL ℝ w) u) =
      (fun u => ∑ r, w r * u r) := by
    funext u
    simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]
  rw [hs] at h
  exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp h)).cexp

/-- Differentiating the angular exponential phase along a coordinate produces
minus the imaginary unit times that frequency coordinate times the phase.

The real-linear pairing evaluated at `coordinateVector r` is w r. Compose its
Fréchet derivative with complex inclusion, multiplication by -I, and exp.
Mathlib's `Real.fderiv_fourierChar_neg_bilinear_right_apply` is an alternative
after the same frequency-dilation kernel rewrite used in Geometry. -/
theorem coordinateDerivative_angular_phase (w : Space p) (r : Fin p) (u : Space p) :
    coordinateDerivative
      (fun x : Space p => Complex.exp (-Complex.I * ((∑ s, w s * x s : ℝ) : ℂ)))
      r u = -Complex.I * (w r : ℂ) *
        Complex.exp (-Complex.I * ((∑ s, w s * u s : ℝ) : ℂ)) := by
  have hs : (innerSL ℝ w : Space p → ℝ) =
      (fun x => ∑ s, w s * x s) := by
    funext x
    simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]
  have hr := (innerSL ℝ w).hasFDerivAt (x := u)
  rw [hs] at hr
  have h := ((Complex.ofRealCLM.hasFDerivAt.comp u hr).const_mul (-Complex.I)).cexp
  simp only [Function.comp_def, Complex.ofRealCLM_apply] at h
  rw [coordinateDerivative, h.fderiv]
  simp [ContinuousLinearMap.comp_apply, coordinateVector,
    PiLp.inner_apply, RCLike.inner_apply, mul_comm]

/-- The angular transform of an integrable weak coordinate derivative equals
the imaginary unit times that frequency coordinate times the transform of the
compactly supported spatial function, at every frequency.

The spatial function is not assumed integrable: when it is not, its transform and the integrals
in the weak-derivative hypothesis are zero by the convention that the integral of a
non-integrable function is zero.

Apply `weakIBP_smooth_test` to the angular exponential and use its explicit
coordinate derivative. Compact support of the derivative is derived almost
everywhere in `WeakTests`, not assumed here. -/
theorem angularFourier_weakDerivative (G D : Space p → ℂ) (r : Fin p)
    (hD : Integrable D volume)
    (hGc : HasCompactSupport G) (hweak : HasWeakCoordinateDerivative G D r)
    (w : Space p) :
    angularFourier D w = Complex.I * (w r : ℂ) * angularFourier G w := by
  have hw := weakIBP_smooth_test G D r hD hGc hweak _
    (contDiff_angular_phase w)
  simp_rw [coordinateDerivative_angular_phase] at hw
  have hi : (∫ u, Complex.exp (-Complex.I * ((∑ s, w s * u s : ℝ) : ℂ)) * D u) =
      Complex.I * (w r : ℂ) *
        (∫ u, Complex.exp (-Complex.I * ((∑ s, w s * u s : ℝ) : ℂ)) * G u) := by
    calc
      _ = - (∫ u, G u * (-Complex.I * (w r : ℂ) *
          Complex.exp (-Complex.I * ((∑ s, w s * u s : ℝ) : ℂ)))) := by
        simpa only [mul_comm, neg_neg] using (congrArg Neg.neg hw).symm
      _ = _ := by
        simp_rw [show ∀ u : Space p, G u * (-Complex.I * (w r : ℂ) *
            Complex.exp (-Complex.I * ((∑ s, w s * u s : ℝ) : ℂ))) =
            (-Complex.I * (w r : ℂ)) *
              (Complex.exp (-Complex.I * ((∑ s, w s * u s : ℝ) : ℂ)) * G u) by
          intro u; ring]
        rw [integral_const_mul]
        ring
  unfold angularFourier
  rw [hi]
  simp only [Complex.real_smul]
  ring

variable {p : ℕ}

/-- Complexification preserves L1 integrability of a real spatial function. -/
theorem integrable_complexify (G : Space p → ℝ) (hG : Integrable G volume) :
    Integrable (complexify G) volume := by
  exact hG.ofReal

/-- Complexification preserves L2 membership of a real spatial function. -/
theorem memLp_complexify (G : Space p → ℝ) (hG : MemLp G 2 volume) :
    MemLp (complexify G) 2 volume := by
  exact hG.ofReal

/-- Complexification preserves compact support of a real spatial function. -/
theorem hasCompactSupport_complexify (G : Space p → ℝ) (hG : HasCompactSupport G) :
    HasCompactSupport (complexify G) := by
  exact hG.comp_left (g := Complex.ofReal) Complex.ofReal_zero

/-- Complexification leaves squared spatial energy unchanged. -/
theorem l2Energy_complexify (G : Space p → ℝ) :
    l2Energy (complexify G) = l2Energy G := by
  simp only [l2Energy, complexify, Complex.norm_real, Real.norm_eq_abs]

/-- An integrable spatial function and an integrable proposed derivative have
integrable products with a compact smooth test and its coordinate derivative.

Use continuity of the derivative, `HasCompactSupport.fderiv_apply`, and
`LocallyIntegrable.integrable_smul_right_of_hasCompactSupport`. This statement
does not assume any weak-derivative identity. -/
theorem integrable_compact_test_products (G D : Space p → ℂ) (r : Fin p)
    (hG : Integrable G volume) (hD : Integrable D volume)
    (φ : Space p → ℂ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    Integrable (fun x => G x * coordinateDerivative φ r x) volume ∧
      Integrable (fun x => D x * φ x) volume := by
  have hc : Continuous (coordinateDerivative φ r) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  constructor
  · simpa only [smul_eq_mul] using
      hG.locallyIntegrable.integrable_smul_right_of_hasCompactSupport hc
        (hφc.fderiv_apply (𝕜 := ℝ) (coordinateVector r))
  · simpa only [smul_eq_mul] using
      hD.locallyIntegrable.integrable_smul_right_of_hasCompactSupport hφ.continuous hφc

/-- Restricting a smooth complex scalar test to a canonical coordinate line
gives a differentiable one-dimensional test with the specified coordinate derivative.

Reuse `hasFDerivAt_update`, compose with the continuous linear coordinate
conversion to Euclidean space, and then apply the chain rule to the test.
The line derivative evaluated at one is exactly `coordinateVector r`.
-/
theorem hasDerivAt_test_coordinate_slice (φ : Space p → ℂ)
    (hφ : ContDiff ℝ ∞ φ) (x : Space p) (r : Fin p) (t : ℝ) :
    HasDerivAt (fun s => φ (updateCoordinate x r s))
      (coordinateDerivative φ r (updateCoordinate x r t)) t := by
  let L : (Fin p → ℝ) →L[ℝ] Space p :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin p => ℝ)).symm.toContinuousLinearMap
  have hu := (L.hasFDerivAt.comp t (hasFDerivAt_update (fun s => x s) (i := r) t)).hasDerivAt
  have he : (L ∘L ContinuousLinearMap.pi
      (Pi.single r (ContinuousLinearMap.id ℝ ℝ))) 1 = coordinateVector r := by
    apply PiLp.ext
    intro s
    by_cases hs : s = r <;>
      simp [L, coordinateVector, Pi.single_apply, hs]
  rw [he] at hu
  exact (hφ.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt t hu

/-- The coordinate derivative of a smooth test remains continuous when
restricted to a coordinate line.

Compose `hφ.continuous_fderiv` evaluated at the constant coordinate vector
with continuity of `updateCoordinate`; no smoothness of the spatial data is used.
-/
@[fun_prop]
theorem continuous_test_coordinate_slice_derivative (φ : Space p → ℂ)
    (hφ : ContDiff ℝ ∞ φ) (x : Space p) (r : Fin p) :
    Continuous (fun t => coordinateDerivative φ r (updateCoordinate x r t)) := by
  have hc : Continuous (coordinateDerivative φ r) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  apply hc.comp
  unfold updateCoordinate
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin p => ℝ)).symm.continuous.comp
  exact (continuous_update (A := fun _ : Fin p => ℝ) r).comp
    ((continuous_const (y := fun s => x s)).prodMk continuous_id)

/-- A globally integrable Euclidean scalar function is integrable on almost
every coordinate slice with respect to the exact remaining-coordinate volume.

First establish measurability of coordinate insertion as in Geometry, combine
it with `map_insertCoordinate_volume` to obtain a measure-preserving map, and
apply `Integrable.prod_right_ae` to its pullback. Do not claim every slice is integrable.
-/
theorem integrable_coordinate_slices_ae (F : Space p → ℂ)
    (hF : Integrable F volume) (r : Fin p) :
    ∀ᵐ z : RemainingCoordinates r ∂volume,
      Integrable (fun t : ℝ => F (insertCoordinate r z t)) volume := by
  have hm : Measurable (fun zt : RemainingCoordinates r × ℝ =>
      insertCoordinate r zt.1 zt.2) := by
    unfold insertCoordinate
    apply (WithLp.measurable_toLp 2 (Fin p → ℝ)).comp
    apply measurable_pi_lambda
    intro s
    split_ifs <;> fun_prop
  have hp : MeasurePreserving (fun zt : RemainingCoordinates r × ℝ =>
      insertCoordinate r zt.1 zt.2) (volume.prod volume) volume :=
    ⟨hm, map_insertCoordinate_volume r⟩
  exact (hp.integrable_comp_of_integrable hF).prod_right_ae

/-- Real coordinate-slice integration by parts also holds for complex C1
test pairs whenever the two complex slice products are integrable.

Apply the real hypothesis to the real and imaginary parts of the test pair.
Use `integral_re` and `integral_im` with the explicit integrability premises,
then complex extensionality. The derivative and continuity of the projected
tests follow by composition with `Complex.reCLM` and `Complex.imCLM`.
-/
theorem realSliceIBP_complex_test (G : Space p → ℝ) (D : Fin p → Space p → ℝ)
    (hslice : HasRealSliceIBP G D) (r : Fin p) (x : Space p) (v v' : ℝ → ℂ)
    (hv : ∀ t, HasDerivAt v (v' t) t) (hv' : Continuous v')
    (hGv' : Integrable (fun t => (G (updateCoordinate x r t) : ℂ) * v' t) volume)
    (hDv : Integrable (fun t => (D r (updateCoordinate x r t) : ℂ) * v t) volume) :
    (∫ t : ℝ, (G (updateCoordinate x r t) : ℂ) * v' t) =
      -(∫ t : ℝ, (D r (updateCoordinate x r t) : ℂ) * v t) := by
  have hre := hslice r x (fun t => (v t).re) (fun t => (v' t).re)
    (fun t => Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hv t))
    (Complex.reCLM.continuous.comp hv')
  have him := hslice r x (fun t => (v t).im) (fun t => (v' t).im)
    (fun t => Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hv t))
    (Complex.imCLM.continuous.comp hv')
  apply Complex.ext
  · change RCLike.re (∫ t : ℝ, (G (updateCoordinate x r t) : ℂ) * v' t) =
      -RCLike.re (∫ t : ℝ, (D r (updateCoordinate x r t) : ℂ) * v t)
    rw [← integral_re hGv', ← integral_re hDv]
    simpa only [RCLike.re_eq_complex_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] using hre
  · change RCLike.im (∫ t : ℝ, (G (updateCoordinate x r t) : ℂ) * v' t) =
      -RCLike.im (∫ t : ℝ, (D r (updateCoordinate x r t) : ℂ) * v t)
    rw [← integral_im hGv', ← integral_im hDv]
    simpa only [RCLike.im_eq_complex_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero] using him

variable {p : ℕ}

/-- [An integrable real spatial function and integrable proposed coordinate derivatives](hyp:hG,hD) satisfying [real slice integration by parts](hyp:hslice) give [in each coordinate the complex weak derivative: the complexified proposed derivative is the weak coordinate derivative of the complexified function](goal).

Real slice integration by parts for integrable spatial
data yields the standard complex weak derivative in each coordinate.

Use `integrable_compact_test_products` and `integrable_coordinate_slices_ae`
for the two products. Apply `realSliceIBP_complex_test` on that full-measure
set with `hasDerivAt_test_coordinate_slice` and
`continuous_test_coordinate_slice_derivative`. Reconstruct both global
integrals using `integral_coordinate_slices` and `integral_neg`.
For a remaining-coordinate vector z, take x = insertCoordinate r z 0;
updating its r-th coordinate to t yields insertCoordinate r z t. -/
theorem sliceIBP_to_weakDerivative (G : Space p → ℝ) (D : Fin p → Space p → ℝ)
    (hG : Integrable G volume) (hD : ∀ r, Integrable (D r) volume)
    (hslice : HasRealSliceIBP G D) (r : Fin p) :
    HasWeakCoordinateDerivative (complexify G) (complexify (D r)) r := by
  intro φ hφ hφc
  obtain ⟨hleft, hright⟩ := integrable_compact_test_products
    (complexify G) (complexify (D r)) r (integrable_complexify G hG)
    (integrable_complexify (D r) (hD r)) φ hφ hφc
  have hupdate (z : RemainingCoordinates r) (t : ℝ) :
      updateCoordinate (insertCoordinate r z 0) r t = insertCoordinate r z t := by
    apply PiLp.ext
    intro s
    by_cases hs : s = r
    · subst s
      simp [updateCoordinate, insertCoordinate]
    · simp [updateCoordinate, insertCoordinate, hs]
  rw [integral_coordinate_slices r _ hleft, integral_coordinate_slices r _ hright,
    ← integral_neg]
  apply integral_congr_ae
  filter_upwards [integrable_coordinate_slices_ae _ hleft r,
    integrable_coordinate_slices_ae _ hright r] with z hzleft hzright
  have h := realSliceIBP_complex_test G D hslice r (insertCoordinate r z 0)
    (fun t => φ (updateCoordinate (insertCoordinate r z 0) r t))
    (fun t => coordinateDerivative φ r (updateCoordinate (insertCoordinate r z 0) r t))
    (hasDerivAt_test_coordinate_slice φ hφ (insertCoordinate r z 0) r)
    (continuous_test_coordinate_slice_derivative φ hφ (insertCoordinate r z 0) r)
    (by simpa only [hupdate, complexify] using hzleft)
    (by simpa only [hupdate, complexify] using hzright)
  simpa only [hupdate, complexify] using h

/-- The Euclidean slice interface is exactly the ordinary coordinate-update
interface on the finite product, with no change of constants or measure.

This lets a consumer whose spatial functions are written on `Fin p → ℝ`
instantiate the Euclidean theorem by composing with the coordinate projection.

Unfold `HasRealSliceIBP` and `updateCoordinate`. For the forward implication
choose `WithLp.toLp 2 x` for each finite-product point; in the reverse implication
use the coordinates of the given Euclidean point. Coordinate extensionality
and the toLp/apply simp rules identify the two update operations pointwise.
-/
theorem realSliceIBP_coordinates_iff (G : (Fin p → ℝ) → ℝ)
    (D : Fin p → (Fin p → ℝ) → ℝ) :
    HasRealSliceIBP (fun x : Space p => G (fun s => x s))
      (fun r x => D r (fun s => x s)) ↔
    (∀ (r : Fin p) (x : Fin p → ℝ) (v v' : ℝ → ℝ),
      (∀ t, HasDerivAt v (v' t) t) → Continuous v' →
      (∫ t : ℝ, G (Function.update x r t) * v' t) =
        -(∫ t : ℝ, D r (Function.update x r t) * v t)) := by
  constructor
  · intro h r x v v' hv hv'
    simpa only [updateCoordinate, PiLp.toLp_apply] using
      h r (WithLp.toLp 2 x) v v' hv hv'
  · intro h r x v v' hv hv'
    simpa only [updateCoordinate, PiLp.toLp_apply] using
      h r (fun s => x s) v v' hv hv'

end Causalean.Mathlib.Analysis.Fourier
