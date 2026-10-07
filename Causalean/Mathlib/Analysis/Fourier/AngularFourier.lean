module
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Finite-dimensional angular Fourier transforms

This module defines the unitary angular-frequency Fourier integral on finite-dimensional
real Euclidean space and proves its compatibility with Mathlib's L² transform. It records
the exact dilation normalization, Euclidean-coordinate volume identities, and Plancherel
without any compact-support or derivative assumption.
-/

@[expose] public section

noncomputable section
open MeasureTheory
open scoped FourierTransform ContDiff ENNReal

namespace Causalean.Mathlib.Analysis.Fourier
variable {p : ℕ}

/-- The [Euclidean space](goal) with [dimension](hyp:p) and its canonical coordinates. -/
abbrev Space (p : ℕ) : Type := EuclideanSpace ℝ (Fin p)

/-- The [angular unitary prefactor](goal) in [dimension](hyp:p) is the negative half-dimensional
power of two pi. -/
def angularPrefactor (p : ℕ) : ℝ := (2 * Real.pi) ^ (-(p : ℝ) / 2)

/-- The [angular Fourier transform](goal) of a [complex spatial function](hyp:G) at a
[frequency](hyp:w) is (2π)^(−p/2) times the integral over u of exp(−i·⟨w, u⟩)·G(u), where p is
the dimension and ⟨w, u⟩ is the sum of coordinate products. -/
def angularFourier {p : ℕ} (G : Space p → ℂ) (w : Space p) : ℂ :=
  angularPrefactor p •
    ∫ u, Complex.exp (-Complex.I * ((∑ r, w r * u r : ℝ) : ℂ)) * G u

/-- The [canonical coordinate vector](goal) for [coordinate](hyp:r) has value one in that
coordinate and zero in the others. -/
def coordinateVector {p : ℕ} (r : Fin p) : Space p :=
  WithLp.toLp 2 (Pi.single r 1)

/-- The [coordinate derivative](goal) of a [scalar test function](hyp:φ) in a
[coordinate](hyp:r) at a [point](hyp:x) is its real Fréchet derivative evaluated on the
canonical coordinate vector. -/
def coordinateDerivative {p : ℕ} (φ : Space p → ℂ) (r : Fin p) (x : Space p) : ℂ :=
  fderiv ℝ φ x (coordinateVector r)

/-- [Spatial weak differentiation](goal) of [a function](hyp:G) by [a proposed
derivative](hyp:D) in [one coordinate](hyp:r) means integration by parts against every
smooth compactly supported complex scalar test. -/
def HasWeakCoordinateDerivative {p : ℕ} (G D : Space p → ℂ) (r : Fin p) : Prop :=
  ∀ φ : Space p → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (∫ x, G x * coordinateDerivative φ r x) = -(∫ x, D x * φ x)

/-- The [coordinate update](goal) of a [point](hyp:x) changes [one coordinate](hyp:r) to [a real
value](hyp:t). -/
def updateCoordinate {p : ℕ} (x : Space p) (r : Fin p) (t : ℝ) : Space p :=
  WithLp.toLp 2 (Function.update (fun s => x s) r t)

/-- The [remaining-coordinate space](goal) omits [one coordinate](hyp:r) from a finite product. -/
abbrev RemainingCoordinates {p : ℕ} (r : Fin p) : Type := {s : Fin p // s ≠ r} → ℝ

/-- [Coordinate insertion](goal) combines [the omitted coordinate](hyp:r), [the remaining
values](hyp:z), and [one real value](hyp:t) into a Euclidean point. -/
def insertCoordinate {p : ℕ} (r : Fin p) (z : RemainingCoordinates r) (t : ℝ) : Space p :=
  WithLp.toLp 2 (fun s => if h : s = r then t else z ⟨s, h⟩)

/-- [Real slice integration by parts](goal) for [a real function G and a family D of proposed
coordinate derivatives](hyp:G,D) means: for every coordinate r, every base point x, and every
real function v that is differentiable everywhere with continuous derivative v′, the integral
over real t of G(x with coordinate r set to t)·v′(t) equals minus the integral over t of
D_r(x with coordinate r set to t)·v(t). The identity is required on every coordinate line (not
only almost every one) and for every such test function, with no support or decay condition on
v; integrals of non-integrable functions are read as zero. -/
def HasRealSliceIBP {p : ℕ} (G : Space p → ℝ) (D : Fin p → Space p → ℝ) : Prop :=
  ∀ (r : Fin p) (x : Space p) (v v' : ℝ → ℝ),
    (∀ t, HasDerivAt v (v' t) t) → Continuous v' →
    (∫ t : ℝ, G (updateCoordinate x r t) * v' t) =
      -(∫ t : ℝ, D r (updateCoordinate x r t) * v t)

/-- The [complexification](goal) of a [real spatial function](hyp:G) is its pointwise inclusion
into the complex numbers. -/
def complexify {p : ℕ} (G : Space p → ℝ) : Space p → ℂ := fun x => (G x : ℂ)

/-- The [squared spatial energy](goal) of a [function](hyp:G) is the nonnegative Lebesgue
integral of its squared norm. -/
def l2Energy {p : ℕ} {F : Type*} [NormedAddCommGroup F] (G : Space p → F) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (‖G x‖ ^ 2)

/-- The [zero-order angular energy](goal) of a [function](hyp:G) is the squared energy of its
normalized angular Fourier integral. -/
def zeroEnergy {p : ℕ} (G : Space p → ℂ) : ℝ≥0∞ := l2Energy (angularFourier G)

/-- The [first-order angular energy](goal) of a [function](hyp:G) weights its squared angular
Fourier integral by one plus squared frequency divided by the dimension. -/
def firstEnergy {p : ℕ} (G : Space p → ℂ) : ℝ≥0∞ :=
  ∫⁻ w, ENNReal.ofReal (‖angularFourier G w‖ ^ 2 * (1 + ‖w‖ ^ 2 / (p : ℝ)))

variable {p : ℕ}

/-- The squared Euclidean norm is the sum of squared real coordinates. -/
theorem norm_sq_eq_sum_coordinates (x : Space p) :
    ‖x‖ ^ 2 = ∑ r, (x r) ^ 2 := by
  simpa using EuclideanSpace.real_norm_sq_eq x

/-- The angular prefactor is strictly positive in every finite dimension. -/
theorem angularPrefactor_pos (p : ℕ) : 0 < angularPrefactor p := by
  exact Real.rpow_pos_of_pos (by positivity) _

/-- The squared prefactor cancels the angular dilation's volume factor exactly. -/
theorem angularPrefactor_sq_mul_volumeFactor (p : ℕ) :
    angularPrefactor p ^ 2 * (2 * Real.pi) ^ p = 1 := by
  unfold angularPrefactor
  have h : 0 < 2 * Real.pi := by positivity
  rw [← Real.rpow_natCast, ← Real.rpow_mul h.le, ← Real.rpow_natCast,
    ← Real.rpow_add h]
  have he : -(p : ℝ) / 2 * (2 : ℝ) + (p : ℝ) = 0 := by ring
  norm_num only [Nat.cast_ofNat] at *
  rw [he, Real.rpow_zero]

/-- Dividing frequency by two pi multiplies the pushed-forward volume by
two pi to the dimension. -/
theorem map_angularDilation_volume (p : ℕ) :
    Measure.map (fun w : Space p => (2 * Real.pi)⁻¹ • w) volume =
      ENNReal.ofReal ((2 * Real.pi) ^ p) • volume := by
  rw [Measure.map_addHaar_smul volume (inv_ne_zero (by positivity))]
  simp only [Space, finrank_euclideanSpace, Fintype.card_fin, inv_pow, inv_inv]
  rw [abs_of_pos (pow_pos (by positivity : 0 < 2 * Real.pi) p)]

/-- Normalized angular dilation preserves the squared energy of a complex
function, even when its energy is infinite.

Use the preceding exact Jacobian and scalar cancellation. No measurability,
integrability or Fourier estimate is a premise here. -/
theorem l2Energy_normalized_dilation (F : Space p → ℂ) :
    l2Energy (fun w => angularPrefactor p • F ((2 * Real.pi)⁻¹ • w)) =
      l2Energy F := by
  have hd : MeasurableEmbedding (fun w : Space p => (2 * Real.pi)⁻¹ • w) :=
    measurableEmbedding_const_smul₀ (inv_ne_zero (by positivity))
  unfold l2Energy
  simp_rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    ENNReal.ofReal_mul (sq_nonneg _)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← hd.lintegral_map (fun x => ENNReal.ofReal (‖F x‖ ^ 2)), map_angularDilation_volume, lintegral_smul_measure]
  rw [smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg _),
    angularPrefactor_sq_mul_volumeFactor, ENNReal.ofReal_one, one_mul]

/-- The angular exponential integral equals Mathlib's two-pi Fourier integral
at frequency divided by two pi, with precisely the unitary prefactor.

This is a kernel rewrite and holds even without integrability, since both
integrals use the same total Bochner integral convention. -/
theorem angularFourier_eq_mathlib (G : Space p → ℂ) (w : Space p) :
    angularFourier G w = angularPrefactor p • (𝓕 G) ((2 * Real.pi)⁻¹ • w) := by
  unfold angularFourier
  rw [Real.fourier_eq']
  congr 1
  apply integral_congr_ae
  filter_upwards [] with u
  congr 1
  rw [inner_smul_right, PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  push_cast
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hc : (2 * (Real.pi : ℂ)) ≠ 0 := by exact_mod_cast hpi
  congr 1
  field_simp

/-- Integrating in Euclidean coordinates agrees exactly with product Lebesgue
integration; the canonical coordinate conversion has Jacobian one. -/
theorem integral_coordinates (F : Space p → ℂ) :
    (∫ x, F x) = ∫ z : Fin p → ℝ, F (WithLp.toLp 2 z) := by
  exact ((PiLp.volume_preserving_toLp (Fin p)).integral_comp
    (MeasurableEquiv.toLp 2 (Fin p → ℝ)).measurableEmbedding F).symm

/-- Coordinate insertion sends the product of the remaining-coordinate
Lebesgue measure and one-dimensional Lebesgue measure to Euclidean volume. -/
theorem map_insertCoordinate_volume (r : Fin p) :
    Measure.map (fun zt : RemainingCoordinates r × ℝ =>
      insertCoordinate r zt.1 zt.2) (volume.prod volume) =
      (volume : Measure (Space p)) := by
  let : Unique {s : Fin p // ¬s ≠ r} :=
    { default := ⟨r, by simp⟩
      uniq := fun s => Subtype.ext (not_not.mp s.property) }
  have hs := (volume_preserving_piEquivPiSubtypeProd
    (fun _ : Fin p => ℝ) (fun s => s ≠ r)).symm
  have hu := (volume_preserving_piUnique (fun _ : {s : Fin p // ¬s ≠ r} => ℝ)).symm
  have hm := (PiLp.volume_preserving_toLp (Fin p)).comp
    (hs.comp ((MeasurePreserving.id volume).prod hu))
  convert hm.map_eq using 1
  congr 1
  funext zt
  apply PiLp.ext
  intro s
  by_cases h : s = r
  · subst s
    simp [insertCoordinate, Function.comp_def, MeasurableEquiv.piEquivPiSubtypeProd,
      Equiv.piEquivPiSubtypeProd, MeasurableEquiv.piUnique, Equiv.piUnique]
  · simp [insertCoordinate, Function.comp_def, MeasurableEquiv.piEquivPiSubtypeProd,
      Equiv.piEquivPiSubtypeProd, h]

/-- An integrable Euclidean function may be integrated one coordinate at a
time with the exact product measure normalization. -/
theorem integral_coordinate_slices (r : Fin p) (F : Space p → ℂ)
    (hF : Integrable F volume) :
    (∫ x, F x) = ∫ z : RemainingCoordinates r, ∫ t : ℝ, F (insertCoordinate r z t) := by
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
  rw [← hp.map_eq, integral_map hp.measurable.aemeasurable
    (hp.map_eq.symm ▸ hF.aestronglyMeasurable)]
  exact integral_prod _ (hp.integrable_comp_of_integrable hF)

variable {p : ℕ}

/-- An integrable function and a Schwartz test have integrable products in
both sides of the Fourier pairing. -/
theorem integrable_fourier_test_products (G : Space p → ℂ)
    (hG : Integrable G volume) (φ : SchwartzMap (Space p) ℂ) :
    Integrable (fun w => φ w * (𝓕 G) w) volume ∧
      Integrable (fun x => (𝓕 φ) x * G x) volume := by
  have hcont : Continuous (𝓕 G) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      continuous_inner hG
  constructor
  · exact φ.integrable.mul_bdd hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun w =>
        VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ G w)
  · exact hG.bdd_mul (𝓕 φ).continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => (𝓕 φ).norm_le_seminorm ℝ x)

/-- The Fourier integral of an L1 function pairs with a Schwartz test by
transferring the Fourier transform to the test function.

Reuse `VectorFourier.integral_fourierIntegral_smul_eq_flip`, with the symmetric
inner-product pairing, rather than rebuilding the full double integral. -/
theorem integral_fourier_pairing (G : Space p → ℂ) (hG : Integrable G volume)
    (φ : SchwartzMap (Space p) ℂ) :
    (∫ w, φ w * (𝓕 G) w) = ∫ x, (𝓕 φ) x * G x := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := innerₗ (Space p)) (μ := volume) (ν := volume) Real.continuous_fourierChar
    continuous_inner φ.integrable hG
  simpa using! h.symm

/-- Mathlib's Fourier L2 isometry pairs with a Schwartz test by transferring
the Fourier transform to that test.

Reuse `Lp.fourier_toTemperedDistribution_eq`,
`Lp.toTemperedDistribution_apply`, and `hG.coeFn_toLp`. No Fourier integral/L2
compatibility needs to have been proved to establish this identity. -/
theorem l2_fourier_pairing (G : Space p → ℂ) (hG : MemLp G 2 volume)
    (φ : SchwartzMap (Space p) ℂ) :
    (∫ w, φ w *
      (Lp.fourierTransformₗᵢ (Space p) ℂ (hG.toLp G)) w) =
      ∫ x, (𝓕 φ) x * G x := by
  have h := congrArg (fun T : TemperedDistribution (Space p) ℂ => T φ)
    (Lp.fourier_toTemperedDistribution_eq (hG.toLp G))
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply,
    smul_eq_mul] at h
  change (∫ x, (𝓕 φ) x * (hG.toLp G) x) =
    (∫ w, φ w * (Lp.fourierTransformₗᵢ (Space p) ℂ (hG.toLp G)) w) at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards [hG.coeFn_toLp] with x hx
  rw [hx]

/-- For an L1 and L2 function, Mathlib's pointwise Fourier integral and the
representative of its Fourier L2 isometry agree almost everywhere.

Use the two pairing identities and
`ae_eq_of_integral_contDiff_smul_eq`; promote compact smooth real tests to
complex Schwartz tests with `HasCompactSupport.toSchwartzMap`. The integral
transform is continuous/bounded, hence locally integrable. -/
theorem fourierIntegral_ae_L2 (G : Space p → ℂ)
    (hG1 : Integrable G volume) (hG2 : MemLp G 2 volume) :
    (𝓕 G) =ᵐ[volume]
      (fun w => (Lp.fourierTransformₗᵢ (Space p) ℂ (hG2.toLp G)) w) := by
  have hcont : Continuous (𝓕 G) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      continuous_inner hG1
  apply ae_eq_of_integral_contDiff_smul_eq hcont.locallyIntegrable
    (Lp.memLp _ |>.locallyIntegrable (by norm_num))
  intro g hg hs
  let φ : SchwartzMap (Space p) ℂ :=
    (hs.comp_left (show Complex.ofRealCLM 0 = 0 from rfl)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hg)
  have h := (integral_fourier_pairing G hG1 φ).trans
    (l2_fourier_pairing G hG2 φ).symm
  change (∫ w, Complex.ofRealCLM (g w) * (𝓕 G) w) =
    (∫ w, Complex.ofRealCLM (g w) *
      (Lp.fourierTransformₗᵢ (Space p) ℂ (hG2.toLp G)) w) at h
  simpa only [Complex.ofRealCLM_apply, Complex.real_smul] using h

/-- The Fourier integral of an L1 and L2 function belongs to L2. -/
theorem mathlib_fourier_memLp (G : Space p → ℂ)
    (hG1 : Integrable G volume) (hG2 : MemLp G 2 volume) :
    MemLp (𝓕 G) 2 volume := by
  exact (memLp_congr_ae (fourierIntegral_ae_L2 G hG1 hG2)).2 (Lp.memLp _)

/-- Mathlib's Fourier integral preserves the nonnegative squared energy of
an L1 and L2 function, with no support or derivative assumptions.

After identifying representatives, use `Lp.norm_fourier_eq` and the L2
norm/lintegral formula. Do not assume Plancherel for the integral transform. -/
theorem mathlib_integral_plancherel (G : Space p → ℂ)
    (hG1 : Integrable G volume) (hG2 : MemLp G 2 volume) :
    l2Energy (𝓕 G) = l2Energy G := by
  have hn : eLpNorm (𝓕 G) 2 volume = eLpNorm G 2 volume := calc
    _ = eLpNorm (fun w =>
        (Lp.fourierTransformₗᵢ (Space p) ℂ (hG2.toLp G)) w) 2 volume :=
      eLpNorm_congr_ae (fourierIntegral_ae_L2 G hG1 hG2)
    _ = ‖𝓕 (hG2.toLp G)‖ₑ := (Lp.enorm_def _).symm
    _ = ‖hG2.toLp G‖ₑ := by
      simpa only [ofReal_norm] using
        congrArg ENNReal.ofReal (Lp.norm_fourier_eq (hG2.toLp G))
    _ = eLpNorm G 2 volume := Lp.enorm_toLp hG2
  have henergy (f : Space p → ℂ) : l2Energy f = eLpNorm f 2 volume ^ 2 := by
    simpa only [l2Energy, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm,
      ENNReal.rpow_two, NNReal.coe_ofNat, ENNReal.coe_ofNat] using
      (eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := volume)
        (p := 2) (by norm_num)).symm
  rw [henergy, henergy, hn]

variable {p : ℕ}

/-- Every frequency kernel times an L1 spatial function is Bochner integrable.

The complex exponential has norm one because its argument is purely imaginary.
Use measurability of the phase and domination by the integrable spatial norm,
or rewrite to Mathlib's Fourier-character integrand. -/
theorem integrable_angular_kernel (G : Space p → ℂ) (hG : Integrable G volume)
    (w : Space p) :
    Integrable (fun u =>
      Complex.exp (-Complex.I * ((∑ r, w r * u r : ℝ) : ℂ)) * G u) volume := by
  have hc : Continuous (fun u : Space p =>
      Complex.exp (-Complex.I * ((∑ r, w r * u r : ℝ) : ℂ))) := by
    fun_prop
  exact hG.bdd_mul (c := 1) hc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => by simp [Complex.norm_exp])

/-- The angular Fourier integral of an L1 function is continuous.

Rewrite pointwise using `angularFourier_eq_mathlib`, then compose
`VectorFourier.fourierIntegral_continuous` with the continuous dilation and
constant real scalar multiplication. -/
@[fun_prop]
theorem angularFourier_continuous (G : Space p → ℂ) (hG : Integrable G volume) :
    Continuous (angularFourier G) := by
  have hc : Continuous (𝓕 G) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      continuous_inner hG
  have hd : Continuous (fun w : Space p => (2 * Real.pi)⁻¹ • w) := by fun_prop
  have he : angularFourier G = (fun w =>
      angularPrefactor p • (𝓕 G) ((2 * Real.pi)⁻¹ • w)) :=
    funext (angularFourier_eq_mathlib G)
  rw [he]
  exact (continuous_const (y := angularPrefactor p)).smul (hc.comp hd)

/-- The angular Fourier integral of an L1 function is measurable. -/
@[fun_prop]
theorem angularFourier_measurable (G : Space p → ℂ) (hG : Integrable G volume) :
    Measurable (angularFourier G) :=
  (angularFourier_continuous G hG).measurable

/-- For an L1 and L2 spatial function, the angular integral agrees almost
everywhere with the normalized frequency dilation of Mathlib's L2 transform.

Pull back `fourierIntegral_ae_L2` through the nonzero dilation. Its exact
volume map in Geometry proves that this pullback preserves null sets; ordinary
pointwise rewriting alone does not justify pulling back an a.e. equality. -/
theorem angularFourier_ae_L2 (G : Space p → ℂ)
    (hG1 : Integrable G volume) (hG2 : MemLp G 2 volume) :
    angularFourier G =ᵐ[volume] (fun w => angularPrefactor p •
      (Lp.fourierTransformₗᵢ (Space p) ℂ (hG2.toLp G)) ((2 * Real.pi)⁻¹ • w)) := by
  have hd : Measurable (fun w : Space p => (2 * Real.pi)⁻¹ • w) := by fun_prop
  have he : (𝓕 G) =ᵐ[Measure.map (fun w : Space p => (2 * Real.pi)⁻¹ • w) volume]
      (fun w => (Lp.fourierTransformₗᵢ (Space p) ℂ (hG2.toLp G)) w) := by
    rw [map_angularDilation_volume]
    exact Measure.ae_smul_measure (fourierIntegral_ae_L2 G hG1 hG2) _
  have hpull := ae_of_ae_map hd.aemeasurable he
  filter_upwards [hpull] with w hw
  rw [angularFourier_eq_mathlib, hw]

/-- [An integrable and square-integrable spatial function](hyp:hG1,hG2) has [equal angular Fourier and spatial squared energies](goal).

Angular Plancherel equates the squared Fourier and spatial energies of
an L1 and L2 function, with no compact support or derivative assumptions.

Use `angularFourier_eq_mathlib`, `l2Energy_normalized_dilation` applied to the
continuous Mathlib integral transform, and `mathlib_integral_plancherel`.
The separate angular a.e. compatibility theorem is not needed for this chain. -/
theorem angular_plancherel (G : Space p → ℂ)
    (hG1 : Integrable G volume) (hG2 : MemLp G 2 volume) :
    zeroEnergy G = l2Energy G := by
  have hn := l2Energy_normalized_dilation (p := p) (𝓕 G)
  calc
    zeroEnergy G = l2Energy (fun w : Space p =>
        angularPrefactor p • (𝓕 G) ((2 * Real.pi)⁻¹ • w)) := by
      unfold zeroEnergy
      congr 1
      exact funext (angularFourier_eq_mathlib G)
    _ = l2Energy (𝓕 G) := hn
    _ = l2Energy G := mathlib_integral_plancherel G hG1 hG2

/-- Angular Plancherel is available directly as the equality of the two
nonnegative Lebesgue integrals, for every L1 and L2 spatial function. -/
theorem angular_plancherel_integral (G : Space p → ℂ)
    (hG1 : Integrable G volume) (hG2 : MemLp G 2 volume) :
    (∫⁻ w, ENNReal.ofReal (‖angularFourier G w‖ ^ 2)) =
      ∫⁻ x, ENNReal.ofReal (‖G x‖ ^ 2) :=
  angular_plancherel G hG1 hG2

/-- An L2 function has finite squared spatial energy.

Reuse `MemLp.integrable_norm_pow` and the nonnegative-integral finiteness
criterion, or the `eLpNorm_nnreal_pow_eq_lintegral` formula used in IntegralL2. -/
theorem l2Energy_lt_top_of_memLp {F : Type*} [NormedAddCommGroup F]
    (G : Space p → F) (hG : MemLp G 2 volume) : l2Energy G < ⊤ := by
  exact (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall fun x => sq_nonneg ‖G x‖)).1
      (hG.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).hasFiniteIntegral

/-- The angular Fourier integral of an L1 and L2 function belongs to L2.

Combine continuity, angular Plancherel, and spatial squared-energy finiteness
with the squared-norm characterization of MemLp. Avoid assuming preservation
of MemLp under a dilation without its change-of-measure argument. -/
theorem angularFourier_memLp (G : Space p → ℂ)
    (hG1 : Integrable G volume) (hG2 : MemLp G 2 volume) :
    MemLp (angularFourier G) 2 volume := by
  have hc := angularFourier_continuous G hG1
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).2
  refine ⟨hc.norm.pow 2 |>.aestronglyMeasurable, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall fun w => sq_nonneg ‖angularFourier G w‖)).2
  change zeroEnergy G < ⊤
  rw [angular_plancherel G hG1 hG2]
  exact l2Energy_lt_top_of_memLp G hG2

/-- The squared norm of the angular transform of an L1 and L2 function is
an integrable real function.

Apply `MemLp.integrable_norm_pow` to `angularFourier_memLp`. -/
theorem integrable_angular_norm_sq (G : Space p → ℂ)
    (hG1 : Integrable G volume) (hG2 : MemLp G 2 volume) :
    Integrable (fun w => ‖angularFourier G w‖ ^ 2) volume := by
  exact (angularFourier_memLp G hG1 hG2).integrable_norm_pow
    (by norm_num : (2 : ℕ) ≠ 0)

/-- The zero-order angular energy of an L1 and L2 function is finite. -/
theorem zeroEnergy_lt_top (G : Space p → ℂ)
    (hG1 : Integrable G volume) (hG2 : MemLp G 2 volume) : zeroEnergy G < ⊤ := by
  rw [angular_plancherel G hG1 hG2]
  exact l2Energy_lt_top_of_memLp G hG2

/-- Every upper bound in the nonnegative extended reals on spatial squared
energy also bounds zero-order angular Fourier energy exactly. -/
theorem zeroEnergy_le_ennreal (G : Space p → ℂ)
    (hG1 : Integrable G volume) (hG2 : MemLp G 2 volume)
    (A : ℝ≥0∞) (hA : l2Energy G ≤ A) : zeroEnergy G ≤ A := by
  rw [angular_plancherel G hG1 hG2]
  exact hA

/-- Every finite real upper bound on spatial squared energy also bounds
zero-order angular Fourier energy exactly. -/
theorem zeroEnergy_le (G : Space p → ℂ)
    (hG1 : Integrable G volume) (hG2 : MemLp G 2 volume)
    (A : ℝ) (hA : l2Energy G ≤ ENNReal.ofReal A) :
    zeroEnergy G ≤ ENNReal.ofReal A := by
  rw [angular_plancherel G hG1 hG2]
  exact hA

end Causalean.Mathlib.Analysis.Fourier
