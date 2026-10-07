module
public import Causalean.Mathlib.Analysis.Fourier.AngularFourier
public import Causalean.Mathlib.Analysis.Fourier.AngularFourierWeakDerivative

/-!
# Angular Fourier Sobolev energies

This module combines angular Plancherel with weak coordinate multipliers to identify the
zero- and first-order Fourier energies of compactly supported functions. It includes the
real slice interface, finite energy bounds, and exact dimension-two specializations.
-/

public section

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Causalean.Mathlib.Analysis.Fourier
variable {p : ℕ}

/-- The first-order angular density of an L1 function is a nonnegative
measurable real function. -/
@[fun_prop]
theorem firstEnergy_density_measurable (G : Space p → ℂ) (hG : Integrable G volume) :
    Measurable (fun w => ‖angularFourier G w‖ ^ 2 * (1 + ‖w‖ ^ 2 / (p : ℝ))) := by
  have hF := angularFourier_measurable G hG
  fun_prop

/-- A coordinate-weighted squared Fourier energy equals the spatial squared
energy of the corresponding L1 and L2 weak derivative.

Rewrite the integrand as the squared norm of the derivative transform using
`angularFourier_weakDerivative`, `norm_mul`, `Complex.norm_I`, and
`Complex.norm_real`; its remaining absolute-value square is the coordinate
square. Then apply `angular_plancherel D hD1 hD2`. No L2 premise on G is needed.
-/
theorem angular_coordinate_energy (G D : Space p → ℂ) (r : Fin p)
    (hD1 : Integrable D volume)
    (hD2 : MemLp D 2 volume) (hGc : HasCompactSupport G)
    (hweak : HasWeakCoordinateDerivative G D r) :
    (∫⁻ w, ENNReal.ofReal (‖angularFourier G w‖ ^ 2 * (w r) ^ 2)) = l2Energy D := by
  calc
    _ = zeroEnergy D := by
      apply lintegral_congr
      intro w
      congr 1
      rw [angularFourier_weakDerivative G D r hD1 hGc hweak w]
      simp only [norm_mul, Complex.norm_I, Complex.norm_real, one_mul, mul_pow,
        Real.norm_eq_abs, sq_abs]
      ring
    _ = l2Energy D := angular_plancherel D hD1 hD2

/-- The first-order angular energy splits into zero-order energy plus the
dimensionally averaged sum of coordinate-weighted energies, including infinite
energies; only L1 and positive dimension are needed for this splitting.

Use `norm_sq_eq_sum_coordinates` and distribute multiplication by the squared
transform norm. Convert the pointwise nonnegative identity with
`ENNReal.ofReal_add`, `ENNReal.ofReal_mul`, and
`ENNReal.ofReal_sum_of_nonneg`. Commute the finite sum and integral with
`lintegral_finsetSum`, the constant with `lintegral_const_mul'`, and the
addition with `lintegral_add_left`. Continuity from L1 supplies every
measurability premise. Do not require finite energies for this splitting.
-/
theorem firstEnergy_eq_coordinate_sum (hp : 1 ≤ p) (G : Space p → ℂ)
    (hG : Integrable G volume) :
    firstEnergy G = zeroEnergy G + ENNReal.ofReal ((p : ℝ)⁻¹) *
      ∑ r : Fin p, ∫⁻ w, ENNReal.ofReal (‖angularFourier G w‖ ^ 2 * (w r) ^ 2) := by
  classical
  have hF := angularFourier_measurable G hG
  have hzero : Measurable (fun w => ENNReal.ofReal (‖angularFourier G w‖ ^ 2)) := by
    fun_prop
  have hcoord (r : Fin p) : Measurable (fun w : Space p =>
      ENNReal.ofReal (‖angularFourier G w‖ ^ 2 * (w r) ^ 2)) := by
    fun_prop
  have hdensity (w : Space p) :
      ‖angularFourier G w‖ ^ 2 * (1 + ‖w‖ ^ 2 / (p : ℝ)) =
      ‖angularFourier G w‖ ^ 2 + (p : ℝ)⁻¹ *
        ∑ r : Fin p, ‖angularFourier G w‖ ^ 2 * (w r) ^ 2 := by
    rw [norm_sq_eq_sum_coordinates, ← Finset.mul_sum]
    ring
  have henn (w : Space p) :
      ENNReal.ofReal (‖angularFourier G w‖ ^ 2 * (1 + ‖w‖ ^ 2 / (p : ℝ))) =
      ENNReal.ofReal (‖angularFourier G w‖ ^ 2) + ENNReal.ofReal ((p : ℝ)⁻¹) *
        ∑ r : Fin p, ENNReal.ofReal (‖angularFourier G w‖ ^ 2 * (w r) ^ 2) := by
    rw [hdensity, ENNReal.ofReal_add (sq_nonneg _) (by positivity),
      ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_sum_of_nonneg (fun r _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  unfold firstEnergy zeroEnergy l2Energy
  simp_rw [henn]
  rw [lintegral_add_left hzero,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_finsetSum Finset.univ (fun r _ => hcoord r)]

variable {p : ℕ}

/-- In [a positive dimension p](hyp:hp), for [an integrable, square-integrable](hyp:hG1,hG2), [compactly supported](hyp:hGc) complex function G whose [weak coordinate derivatives D_r](hyp:hweak) are [integrable and square-integrable](hyp:hD1,hD2), [the first-order angular Fourier energy of G — the integral of |Ĝ(w)|²·(1 + ‖w‖²/p) — equals the squared L² energy of G plus 1/p times the sum over coordinates of the squared L² energies of the D_r](goal).

The exact first-order angular Fourier energy of a compactly supported L1
and L2 function with L1 and L2 weak coordinate derivatives equals its spatial
energy plus the average of the derivative energies.

Use `firstEnergy_eq_coordinate_sum`, `angular_plancherel`, and
`angular_coordinate_energy`. Derivatives need no pointwise compact support. -/
theorem angular_first_energy (hp : 1 ≤ p) (G : Space p → ℂ)
    (D : Fin p → Space p → ℂ)
    (hG1 : Integrable G volume) (hG2 : MemLp G 2 volume)
    (hGc : HasCompactSupport G)
    (hD1 : ∀ r, Integrable (D r) volume) (hD2 : ∀ r, MemLp (D r) 2 volume)
    (hweak : ∀ r, HasWeakCoordinateDerivative G (D r) r) :
    firstEnergy G = l2Energy G + ENNReal.ofReal ((p : ℝ)⁻¹) *
      ∑ r, l2Energy (D r) := by
  rw [firstEnergy_eq_coordinate_sum hp G hG1, angular_plancherel G hG1 hG2]
  have hc : ∀ r : Fin p,
      (∫⁻ w, ENNReal.ofReal (‖angularFourier G w‖ ^ 2 * (w r) ^ 2)) =
        l2Energy (D r) := fun r =>
    angular_coordinate_energy G (D r) r (hD1 r) (hD2 r) hGc (hweak r)
  simp_rw [hc]

/-- The exact first-order identity is also available as a literal nonnegative
integral equality with the angular frequency weight. -/
theorem angular_first_energy_integral (hp : 1 ≤ p) (G : Space p → ℂ)
    (D : Fin p → Space p → ℂ)
    (hG1 : Integrable G volume) (hG2 : MemLp G 2 volume)
    (hGc : HasCompactSupport G)
    (hD1 : ∀ r, Integrable (D r) volume) (hD2 : ∀ r, MemLp (D r) 2 volume)
    (hweak : ∀ r, HasWeakCoordinateDerivative G (D r) r) :
    (∫⁻ w, ENNReal.ofReal
      (‖angularFourier G w‖ ^ 2 * (1 + ‖w‖ ^ 2 / (p : ℝ)))) =
      (∫⁻ x, ENNReal.ofReal (‖G x‖ ^ 2)) + ENNReal.ofReal ((p : ℝ)⁻¹) *
        ∑ r, ∫⁻ x, ENNReal.ofReal (‖D r x‖ ^ 2) :=
  angular_first_energy hp G D hG1 hG2 hGc hD1 hD2 hweak

/-- Under the spatial weak-derivative hypotheses, the first-order angular
Fourier energy is finite. -/
theorem firstEnergy_lt_top (hp : 1 ≤ p) (G : Space p → ℂ)
    (D : Fin p → Space p → ℂ)
    (hG1 : Integrable G volume) (hG2 : MemLp G 2 volume)
    (hGc : HasCompactSupport G)
    (hD1 : ∀ r, Integrable (D r) volume) (hD2 : ∀ r, MemLp (D r) 2 volume)
    (hweak : ∀ r, HasWeakCoordinateDerivative G (D r) r) :
    firstEnergy G < ⊤ := by
  rw [angular_first_energy hp G D hG1 hG2 hGc hD1 hD2 hweak]
  exact ENNReal.add_lt_top.mpr ⟨l2Energy_lt_top_of_memLp G hG2,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.sum_lt_top.mpr fun r _ => l2Energy_lt_top_of_memLp (D r) (hD2 r))⟩

/-- Under the spatial weak-derivative hypotheses, the weighted squared angular
Fourier norm is Bochner integrable as a real function. -/
theorem integrable_firstEnergy_density (hp : 1 ≤ p) (G : Space p → ℂ)
    (D : Fin p → Space p → ℂ)
    (hG1 : Integrable G volume) (hG2 : MemLp G 2 volume)
    (hGc : HasCompactSupport G)
    (hD1 : ∀ r, Integrable (D r) volume) (hD2 : ∀ r, MemLp (D r) 2 volume)
    (hweak : ∀ r, HasWeakCoordinateDerivative G (D r) r) :
    Integrable (fun w => ‖angularFourier G w‖ ^ 2 * (1 + ‖w‖ ^ 2 / (p : ℝ)))
      volume := by
  refine ⟨(firstEnergy_density_measurable G hG1).aestronglyMeasurable, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun w =>
    mul_nonneg (sq_nonneg _) (add_nonneg zero_le_one
      (div_nonneg (sq_nonneg _) (Nat.cast_nonneg p))))).2
  exact firstEnergy_lt_top hp G D hG1 hG2 hGc hD1 hD2 hweak

/-- Spatial energy bounds in the nonnegative extended reals give the exact upper
bound A plus B divided by dimension for first-order angular Fourier energy. -/
theorem firstEnergy_le_ennreal (hp : 1 ≤ p) (G : Space p → ℂ)
    (D : Fin p → Space p → ℂ)
    (hG1 : Integrable G volume) (hG2 : MemLp G 2 volume)
    (hGc : HasCompactSupport G)
    (hD1 : ∀ r, Integrable (D r) volume) (hD2 : ∀ r, MemLp (D r) 2 volume)
    (hweak : ∀ r, HasWeakCoordinateDerivative G (D r) r)
    (A B : ℝ≥0∞) (hA : l2Energy G ≤ A) (hB : (∑ r, l2Energy (D r)) ≤ B) :
    firstEnergy G ≤ A + ENNReal.ofReal ((p : ℝ)⁻¹) * B := by
  rw [angular_first_energy hp G D hG1 hG2 hGc hD1 hD2 hweak]
  exact add_le_add hA (mul_le_mul_right hB _)

/-- Finite nonnegative real spatial energy bounds A and B give the exact upper
bound A plus B divided by dimension for first-order angular Fourier energy. -/
theorem firstEnergy_le (hp : 1 ≤ p) (G : Space p → ℂ)
    (D : Fin p → Space p → ℂ)
    (hG1 : Integrable G volume) (hG2 : MemLp G 2 volume)
    (hGc : HasCompactSupport G)
    (hD1 : ∀ r, Integrable (D r) volume) (hD2 : ∀ r, MemLp (D r) 2 volume)
    (hweak : ∀ r, HasWeakCoordinateDerivative G (D r) r)
    (A B : ℝ) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : l2Energy G ≤ ENNReal.ofReal A)
    (hB : (∑ r, l2Energy (D r)) ≤ ENNReal.ofReal B) :
    firstEnergy G ≤ ENNReal.ofReal (A + (p : ℝ)⁻¹ * B) := by
  have hb := firstEnergy_le_ennreal hp G D hG1 hG2 hGc hD1 hD2 hweak
    (ENNReal.ofReal A) (ENNReal.ofReal B) hA hB
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (Nat.cast_nonneg p)),
    ← ENNReal.ofReal_add hA0 (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p)) hB0)] at hb
  exact hb

/-- A real compactly supported L1 and L2 function with L1 and L2 proposed
derivatives satisfying coordinate-slice integration by parts obeys the exact
complexified angular energy identity. -/
theorem angular_first_energy_of_real_slices (hp : 1 ≤ p) (G : Space p → ℝ)
    (D : Fin p → Space p → ℝ)
    (hG1 : Integrable G volume) (hG2 : MemLp G 2 volume)
    (hGc : HasCompactSupport G)
    (hD1 : ∀ r, Integrable (D r) volume) (hD2 : ∀ r, MemLp (D r) 2 volume)
    (hslice : HasRealSliceIBP G D) :
    firstEnergy (complexify G) = l2Energy G + ENNReal.ofReal ((p : ℝ)⁻¹) *
      ∑ r, l2Energy (D r) := by
  have h := angular_first_energy hp (complexify G) (fun r => complexify (D r))
    (integrable_complexify G hG1) (memLp_complexify G hG2)
    (hasCompactSupport_complexify G hGc)
    (fun r => integrable_complexify (D r) (hD1 r))
    (fun r => memLp_complexify (D r) (hD2 r))
    (sliceIBP_to_weakDerivative G D hG1 hD1 hslice)
  simpa only [l2Energy_complexify] using h

/-- The complexified first-order angular energy from real coordinate-slice
integration by parts is finite. -/
theorem firstEnergy_lt_top_of_real_slices (hp : 1 ≤ p) (G : Space p → ℝ)
    (D : Fin p → Space p → ℝ)
    (hG1 : Integrable G volume) (hG2 : MemLp G 2 volume)
    (hGc : HasCompactSupport G)
    (hD1 : ∀ r, Integrable (D r) volume) (hD2 : ∀ r, MemLp (D r) 2 volume)
    (hslice : HasRealSliceIBP G D) :
    firstEnergy (complexify G) < ⊤ := by
  rw [angular_first_energy_of_real_slices hp G D hG1 hG2 hGc hD1 hD2 hslice]
  exact ENNReal.add_lt_top.mpr ⟨l2Energy_lt_top_of_memLp G hG2,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.sum_lt_top.mpr fun r _ => l2Energy_lt_top_of_memLp (D r) (hD2 r))⟩

/-- Spatial bounds for real slice data give simultaneous finite zero-order
and first-order angular energy bounds, with the exact reciprocal dimension. -/
theorem energy_bounds_of_real_slices (hp : 1 ≤ p) (G : Space p → ℝ)
    (D : Fin p → Space p → ℝ)
    (hG1 : Integrable G volume) (hG2 : MemLp G 2 volume)
    (hGc : HasCompactSupport G)
    (hD1 : ∀ r, Integrable (D r) volume) (hD2 : ∀ r, MemLp (D r) 2 volume)
    (hslice : HasRealSliceIBP G D)
    (A B : ℝ) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : l2Energy G ≤ ENNReal.ofReal A)
    (hB : (∑ r, l2Energy (D r)) ≤ ENNReal.ofReal B) :
    zeroEnergy (complexify G) ≤ ENNReal.ofReal A ∧
      firstEnergy (complexify G) ≤ ENNReal.ofReal (A + (p : ℝ)⁻¹ * B) := by
  constructor
  · apply zeroEnergy_le (complexify G) (integrable_complexify G hG1)
      (memLp_complexify G hG2) A
    simpa only [l2Energy_complexify] using hA
  · apply firstEnergy_le hp (complexify G) (fun r => complexify (D r))
      (integrable_complexify G hG1) (memLp_complexify G hG2)
      (hasCompactSupport_complexify G hGc)
      (fun r => integrable_complexify (D r) (hD1 r))
      (fun r => memLp_complexify (D r) (hD2 r))
      (sliceIBP_to_weakDerivative G D hG1 hD1 hslice) A B hA0 hB0
    · simpa only [l2Energy_complexify] using hA
    · simpa only [l2Energy_complexify] using hB

/-- In dimension two, every L1 and L2 complex function has equal spatial and
angular Fourier squared energies. -/
theorem angular_plancherel_two (G : Space 2 → ℂ)
    (hG1 : Integrable G volume) (hG2 : MemLp G 2 volume) :
    (∫⁻ w, ENNReal.ofReal (‖angularFourier G w‖ ^ 2)) =
      ∫⁻ x, ENNReal.ofReal (‖G x‖ ^ 2) :=
  angular_plancherel G hG1 hG2

/-- In dimension two, the first-order energy is exactly the spatial energy
plus one half of the sum of the two weak derivative energies. -/
theorem angular_first_energy_two (G : Space 2 → ℂ) (D : Fin 2 → Space 2 → ℂ)
    (hG1 : Integrable G volume) (hG2 : MemLp G 2 volume)
    (hGc : HasCompactSupport G)
    (hD1 : ∀ r, Integrable (D r) volume) (hD2 : ∀ r, MemLp (D r) 2 volume)
    (hweak : ∀ r, HasWeakCoordinateDerivative G (D r) r) :
    (∫⁻ w, ENNReal.ofReal (‖angularFourier G w‖ ^ 2 * (1 + ‖w‖ ^ 2 / 2))) =
      l2Energy G + ENNReal.ofReal (1 / 2 : ℝ) *
        (l2Energy (D 0) + l2Energy (D 1)) := by
  simpa [firstEnergy, Fin.sum_univ_two, one_div] using
    angular_first_energy (p := 2) (by decide) G D hG1 hG2 hGc hD1 hD2 hweak

/-- In dimension two, real slice integration by parts supplies exactly the
same energy identity, with the sum of the two real derivative energies. -/
theorem angular_first_energy_two_real_slices (G : Space 2 → ℝ)
    (D : Fin 2 → Space 2 → ℝ)
    (hG1 : Integrable G volume) (hG2 : MemLp G 2 volume)
    (hGc : HasCompactSupport G)
    (hD1 : ∀ r, Integrable (D r) volume) (hD2 : ∀ r, MemLp (D r) 2 volume)
    (hslice : HasRealSliceIBP G D) :
    firstEnergy (complexify G) = l2Energy G + ENNReal.ofReal (1 / 2 : ℝ) *
      (l2Energy (D 0) + l2Energy (D 1)) := by
  simpa [Fin.sum_univ_two, one_div] using
    angular_first_energy_of_real_slices (p := 2) (by decide)
      G D hG1 hG2 hGc hD1 hD2 hslice

/-- In dimension two, spatial bounds A and B yield the exact angular upper
bounds A and A plus one half B for real coordinate-slice data. -/
theorem energy_bounds_two_real_slices (G : Space 2 → ℝ)
    (D : Fin 2 → Space 2 → ℝ)
    (hG1 : Integrable G volume) (hG2 : MemLp G 2 volume)
    (hGc : HasCompactSupport G)
    (hD1 : ∀ r, Integrable (D r) volume) (hD2 : ∀ r, MemLp (D r) 2 volume)
    (hslice : HasRealSliceIBP G D)
    (A B : ℝ) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : l2Energy G ≤ ENNReal.ofReal A)
    (hB : l2Energy (D 0) + l2Energy (D 1) ≤ ENNReal.ofReal B) :
    zeroEnergy (complexify G) ≤ ENNReal.ofReal A ∧
      firstEnergy (complexify G) ≤ ENNReal.ofReal (A + (1 / 2 : ℝ) * B) := by
  have hB' : (∑ r, l2Energy (D r)) ≤ ENNReal.ofReal B := by
    simpa [Fin.sum_univ_two] using hB
  simpa [one_div] using energy_bounds_of_real_slices (p := 2) (by decide)
    G D hG1 hG2 hGc hD1 hD2 hslice A B hA0 hB0 hA hB'

end Causalean.Mathlib.Analysis.Fourier
