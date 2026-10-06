module
public import Causalean.Stat.Minimax.HellingerAffinity
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Sharp Hellinger comparisons

This module develops the sharp total-variation/Hellinger comparison for probability laws, beginning with Radon–Nikodym densities against their sum and ending with binary-testing inequalities in real and extended-nonnegative forms.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace Causalean.Stat.Minimax


variable {X : Type*} [MeasurableSpace X]

/-- The [unhalved squared Hellinger distance](goal) of [two laws](hyp:B,C) uses their
Radon–Nikodym densities relative to their sum as the common reference measure. -/
noncomputable def hellingerSqMeasure (B C : Measure X) : ℝ :=
  Causalean.Stat.hellingerSqDensity (B + C)
    (fun x => (B.rnDeriv (B + C) x).toReal)
    (fun x => (C.rnDeriv (B + C) x).toReal)

/-- A probability law's density relative to the sum with another probability law is
[integrable, nonnegative and normalized](goal), and its set integrals recover event masses. -/
theorem sum_reference_density (B C : Measure X)
    [IsProbabilityMeasure B] [IsProbabilityMeasure C] :
    Integrable (fun x => (B.rnDeriv (B + C) x).toReal) (B + C) ∧
    (∀ x, 0 ≤ (B.rnDeriv (B + C) x).toReal) ∧
    (∫ x, (B.rnDeriv (B + C) x).toReal ∂(B + C)) = 1 ∧
    (∀ E : Set X, ∫ x in E, (B.rnDeriv (B + C) x).toReal ∂(B + C) = B.real E) := by
  have hac : B ≪ B + C :=
    Measure.AbsolutelyContinuous.add_right Measure.AbsolutelyContinuous.rfl C
  refine ⟨Measure.integrable_toReal_rnDeriv, fun _ => ENNReal.toReal_nonneg, ?_, ?_⟩
  · rw [Measure.integral_toReal_rnDeriv hac]
    simp [measureReal_def]
  · exact fun E => Measure.setIntegral_toReal_rnDeriv hac E

/-- The square root of an [integrable](hyp:hf), [nonnegative density](hyp:hf0)
is [square integrable](goal). -/
theorem sqrt_density_memLp (μ : Measure X) (f : X → ℝ)
    (hf : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x) :
    MemLp (fun x => Real.sqrt (f x)) 2 μ := by
  have hm : AEStronglyMeasurable (fun x => Real.sqrt (f x)) μ :=
    (Real.continuous_sqrt.measurable.comp_aemeasurable
      hf.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hm]
  simpa only [Real.sq_sqrt (hf0 _)] using hf

/-- [Integrable nonnegative densities](hyp:hf,hg,hf0,hg0) have [integrable squared
square-root sums and differences](goal). -/
theorem integrable_sqrt_sum_sub_sq (μ : Measure X) (f g : X → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    Integrable (fun x => (Real.sqrt (f x) + Real.sqrt (g x)) ^ 2) μ ∧
    Integrable (fun x => (Real.sqrt (f x) - Real.sqrt (g x)) ^ 2) μ := by
  exact ⟨((sqrt_density_memLp μ f hf hf0).add
    (sqrt_density_memLp μ g hg hg0)).integrable_sq,
    ((sqrt_density_memLp μ f hf hf0).sub
    (sqrt_density_memLp μ g hg hg0)).integrable_sq⟩

/-- For [integrable nonnegative probability densities](hyp:hf,hg,hf0,hg0,hf1,hg1),
the [square-root-sum energy is exactly four minus unhalved squared Hellinger](goal).

Expand both squares; their pointwise sum is twice f plus twice g. Integrate using
`integrable_sqrt_sum_sub_sq`, normalization and `integral_add`. -/
theorem integral_sqrt_sum_sq_eq_four_sub (μ : Measure X) (f g : X → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hf1 : ∫ x, f x ∂μ = 1) (hg1 : ∫ x, g x ∂μ = 1) :
    (∫ x, (Real.sqrt (f x) + Real.sqrt (g x)) ^ 2 ∂μ) =
      4 - Causalean.Stat.hellingerSqDensity μ f g := by
  obtain ⟨hsum, hsub⟩ := integrable_sqrt_sum_sub_sq μ f g hf hg hf0 hg0
  have henergy :
      (∫ x, (Real.sqrt (f x) + Real.sqrt (g x)) ^ 2 ∂μ) +
        Causalean.Stat.hellingerSqDensity μ f g = 4 := by
    rw [Causalean.Stat.hellingerSqDensity, ← integral_add hsum hsub]
    have hpoint :
        (fun x => (Real.sqrt (f x) + Real.sqrt (g x)) ^ 2 +
          (Real.sqrt (f x) - Real.sqrt (g x)) ^ 2) =
        (fun x => 2 * f x + 2 * g x) := by
      funext x
      nlinarith [Real.sq_sqrt (hf0 x), Real.sq_sqrt (hg0 x)]
    rw [hpoint, integral_add (hf.const_mul 2) (hg.const_mul 2),
      integral_const_mul, integral_const_mul, hf1, hg1]
    norm_num
  linarith

/-- The unhalved squared Hellinger distance between [normalized nonnegative
integrable densities](hyp:hf,hg,hf0,hg0,hf1,hg1) [lies between zero and two](goal).

Nonnegativity is integral nonnegativity; the upper bound follows pointwise from
the nonnegative cross term and normalization. -/
theorem hellingerSqDensity_bounds (μ : Measure X) (f g : X → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hf1 : ∫ x, f x ∂μ = 1) (hg1 : ∫ x, g x ∂μ = 1) :
    0 ≤ Causalean.Stat.hellingerSqDensity μ f g ∧
      Causalean.Stat.hellingerSqDensity μ f g ≤ 2 := by
  constructor
  · exact integral_nonneg fun x => sq_nonneg _
  · calc
      Causalean.Stat.hellingerSqDensity μ f g ≤ ∫ x, f x + g x ∂μ := by
        apply integral_mono_ae
          (integrable_sqrt_sum_sub_sq μ f g hf hg hf0 hg0).2 (hf.add hg)
        exact Filter.Eventually.of_forall fun x => by
          change (Real.sqrt (f x) - Real.sqrt (g x)) ^ 2 ≤ f x + g x
          nlinarith [Real.sq_sqrt (hf0 x), Real.sq_sqrt (hg0 x),
            mul_nonneg (Real.sqrt_nonneg (f x)) (Real.sqrt_nonneg (g x))]
      _ = 2 := by rw [integral_add hf hg, hf1, hg1]; norm_num

/-- The L¹ difference of [normalized nonnegative integrable densities](hyp:hf,hg,hf0,hg0,hf1,hg1)
is [at most the square root of Hellinger squared times its complementary energy](goal).

Factor |f-g| as |sqrt f-sqrt g|*|sqrt f+sqrt g| and use Holder with exponents
two and two. Reuse the Causalean HellingerAffinity proof's MemLp/Holder steps,
but substitute the exact energy identity instead of its coarse bound by four. -/
theorem integral_abs_sub_le_sqrt_hellinger_energy (μ : Measure X) (f g : X → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hf1 : ∫ x, f x ∂μ = 1) (hg1 : ∫ x, g x ∂μ = 1) :
    (∫ x, |f x - g x| ∂μ) ≤ Real.sqrt
      (Causalean.Stat.hellingerSqDensity μ f g *
        (4 - Causalean.Stat.hellingerSqDensity μ f g)) := by
  let u : X → ℝ := fun x => Real.sqrt (f x) - Real.sqrt (g x)
  let v : X → ℝ := fun x => Real.sqrt (f x) + Real.sqrt (g x)
  have hu : MemLp u 2 μ :=
    (sqrt_density_memLp μ f hf hf0).sub (sqrt_density_memLp μ g hg hg0)
  have hv : MemLp v 2 μ :=
    (sqrt_density_memLp μ f hf hf0).add (sqrt_density_memLp μ g hg hg0)
  have hfact : (fun x => |f x - g x|) = (fun x => |u x| * |v x|) := by
    funext x
    rw [← abs_mul]
    dsimp [u, v]
    congr 1
    nlinarith [Real.sq_sqrt (hf0 x), Real.sq_sqrt (hg0 x)]
  have hholder :
      ∫ x, |u x| * |v x| ∂μ ≤
        (∫ x, |u x| ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
          (∫ x, |v x| ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
    apply integral_mul_le_Lp_mul_Lq_of_nonneg (p := (2 : ℝ)) (q := (2 : ℝ))
    · exact Real.HolderConjugate.two_two
    · exact Filter.Eventually.of_forall fun x => abs_nonneg _
    · exact Filter.Eventually.of_forall fun x => abs_nonneg _
    · rw [show (ENNReal.ofReal 2 : ℝ≥0∞) = 2 from by norm_num]
      exact hu.abs
    · rw [show (ENNReal.ofReal 2 : ℝ≥0∞) = 2 from by norm_num]
      exact hv.abs
  have hu_sq : ∫ x, |u x| ^ (2 : ℝ) ∂μ =
      Causalean.Stat.hellingerSqDensity μ f g := by
    simp only [Real.rpow_two, sq_abs]
    rfl
  have hv_sq : ∫ x, |v x| ^ (2 : ℝ) ∂μ =
      4 - Causalean.Stat.hellingerSqDensity μ f g := by
    simp only [Real.rpow_two, sq_abs]
    exact integral_sqrt_sum_sq_eq_four_sub μ f g hf hg hf0 hg0 hf1 hg1
  rw [hfact]
  calc
    ∫ x, |u x| * |v x| ∂μ ≤
        Real.sqrt (Causalean.Stat.hellingerSqDensity μ f g) *
          Real.sqrt (4 - Causalean.Stat.hellingerSqDensity μ f g) := by
      simpa only [hu_sq, hv_sq, ← Real.sqrt_eq_rpow] using hholder
    _ = Real.sqrt (Causalean.Stat.hellingerSqDensity μ f g *
        (4 - Causalean.Stat.hellingerSqDensity μ f g)) :=
      (Real.sqrt_mul (hellingerSqDensity_bounds μ f g hf hg hf0 hg0 hf1 hg1).1 _).symm

/-- The unhalved squared Hellinger distance of two probability laws
[lies in the interval from zero to two](goal). -/
theorem hellingerSqMeasure_bounds (B C : Measure X)
    [IsProbabilityMeasure B] [IsProbabilityMeasure C] :
    0 ≤ hellingerSqMeasure B C ∧ hellingerSqMeasure B C ≤ 2 := by
  obtain ⟨hf, hf0, hf1, _⟩ := sum_reference_density B C
  obtain ⟨hg, hg0, hg1, _⟩ := sum_reference_density C B
  simp only [add_comm C B] at hg hg0 hg1
  exact hellingerSqDensity_bounds (B + C) _ _ hf hg hf0 hg0 hf1 hg1

/-- [Two probability laws](hyp:B,C) assign a [measurable event](hyp:hE) an
[absolute probability gap bounded by the sharp Hellinger expression](goal).

Recover both real event masses from RN set integrals. The integral of f-g is zero;
reuse `abs_setIntegral_le_half_integral_abs_of_integral_eq_zero` for the factor
one half, then `integral_abs_sub_le_sqrt_hellinger_energy`. Square-root algebra
converts half*sqrt(H2*(4-H2)) into sqrt(H2*(1-H2/4)). -/
theorem measure_event_gap_le_sharp_hellinger (B C : Measure X)
    [IsProbabilityMeasure B] [IsProbabilityMeasure C]
    {E : Set X} (hE : MeasurableSet E) :
    |B.real E - C.real E| ≤
      Real.sqrt (hellingerSqMeasure B C * (1 - hellingerSqMeasure B C / 4)) := by
  obtain ⟨hf, hf0, hf1, hfE⟩ := sum_reference_density B C
  obtain ⟨hg, hg0, hg1, hgE⟩ := sum_reference_density C B
  simp only [add_comm C B] at hg hg0 hg1 hgE
  let f : X → ℝ := fun x => (B.rnDeriv (B + C) x).toReal
  let g : X → ℝ := fun x => (C.rnDeriv (B + C) x).toReal
  have hzero : ∫ x, (f x - g x) ∂(B + C) = 0 := by
    rw [integral_sub hf hg, hf1, hg1]
    norm_num
  have hgap : |B.real E - C.real E| ≤
      (1 / 2 : ℝ) * ∫ x, |f x - g x| ∂(B + C) := by
    rw [← hfE E, ← hgE E, ← integral_sub hf.integrableOn hg.integrableOn]
    exact Causalean.Stat.abs_setIntegral_le_half_integral_abs_of_integral_eq_zero
      (hf.sub hg) hzero hE
  have hl1 := integral_abs_sub_le_sqrt_hellinger_energy
    (B + C) f g hf hg hf0 hg0 hf1 hg1
  calc
    |B.real E - C.real E| ≤
        (1 / 2 : ℝ) * Real.sqrt
          (hellingerSqMeasure B C * (4 - hellingerSqMeasure B C)) :=
      hgap.trans (mul_le_mul_of_nonneg_left hl1 (by norm_num))
    _ = Real.sqrt (hellingerSqMeasure B C *
        (1 - hellingerSqMeasure B C / 4)) := by
      rw [show hellingerSqMeasure B C * (1 - hellingerSqMeasure B C / 4) =
        (1 / 2 : ℝ) ^ 2 *
          (hellingerSqMeasure B C * (4 - hellingerSqMeasure B C)) by ring,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
      norm_num

/-- The total variation distance of two probability laws is [bounded by the sharp
unhalved Hellinger expression](goal). -/
theorem tvDist_le_sharp_hellinger (B C : Measure X)
    [IsProbabilityMeasure B] [IsProbabilityMeasure C] :
    Causalean.Stat.tvDist B C ≤
      Real.sqrt (hellingerSqMeasure B C * (1 - hellingerSqMeasure B C / 4)) := by
  unfold Causalean.Stat.tvDist
  exact ciSup_le fun E => measure_event_gap_le_sharp_hellinger B C E.property

/-- The sharp Hellinger comparison function is [monotone below two](goal) under
[ordered nonnegative arguments](hyp:_ha,hab,hb). -/
theorem sharp_hellinger_mono {a b : ℝ} (_ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 2) :
    Real.sqrt (a * (1 - a / 4)) ≤ Real.sqrt (b * (1 - b / 4)) := by
  apply Real.sqrt_le_sqrt
  nlinarith [mul_nonneg (sub_nonneg.mpr hab) (show 0 ≤ 4 - a - b by linarith)]

/-- The sum of the two real error probabilities of any [measurable binary test](hyp:hE)
is [at least one minus the sharp Hellinger bound](goal). -/
theorem binary_test_error_ge_sharp_hellinger_real (B C : Measure X)
    [IsProbabilityMeasure B] [IsProbabilityMeasure C]
    {E : Set X} (hE : MeasurableSet E) :
    1 - Real.sqrt (hellingerSqMeasure B C * (1 - hellingerSqMeasure B C / 4)) ≤
      B.real E + C.real Eᶜ := by
  exact (sub_le_sub_left (tvDist_le_sharp_hellinger B C) 1).trans
    (Causalean.Stat.one_sub_tvDist_le_test (μ := B) (ν := C) hE)

/-- The extended-nonnegative error sum of a [measurable binary test](hyp:hE) is
[at least the positive part of one minus the sharp Hellinger bound](goal).

Convert the real theorem using finiteness of event masses, `ofReal_add`, and
`ofReal_toReal`; no `toReal` of an infinite risk is used. -/
theorem binary_test_error_ge_sharp_hellinger (B C : Measure X)
    [IsProbabilityMeasure B] [IsProbabilityMeasure C]
    {E : Set X} (hE : MeasurableSet E) :
    ENNReal.ofReal (1 - Real.sqrt
      (hellingerSqMeasure B C * (1 - hellingerSqMeasure B C / 4))) ≤ B E + C Eᶜ := by
  have h := ENNReal.ofReal_le_ofReal
    (binary_test_error_ge_sharp_hellinger_real B C hE)
  simpa only [measureReal_def, ENNReal.ofReal_add ENNReal.toReal_nonneg
    ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (measure_ne_top B E),
    ENNReal.ofReal_toReal (measure_ne_top C Eᶜ)] using h

/-- Complementing a [measurable binary test](hyp:hE) gives the [opposite orientation
of the same sharp testing bound](goal). -/
theorem binary_test_error_ge_sharp_hellinger_compl (B C : Measure X)
    [IsProbabilityMeasure B] [IsProbabilityMeasure C]
    {E : Set X} (hE : MeasurableSet E) :
    ENNReal.ofReal (1 - Real.sqrt
      (hellingerSqMeasure B C * (1 - hellingerSqMeasure B C / 4))) ≤ B Eᶜ + C E := by
  simpa only [compl_compl] using binary_test_error_ge_sharp_hellinger B C hE.compl

/-- A [nonnegative Hellinger budget strictly below two](hyp:_hu0,hu2,hH) gives
the [sharp testing lower bound in terms of that budget](goal) for every
[measurable test](hyp:hE). -/
theorem binary_test_error_ge_of_hellinger_budget (B C : Measure X)
    [IsProbabilityMeasure B] [IsProbabilityMeasure C]
    {u : ℝ} (_hu0 : 0 ≤ u) (hu2 : u < 2) (hH : hellingerSqMeasure B C ≤ u)
    {E : Set X} (hE : MeasurableSet E) :
    ENNReal.ofReal (1 - Real.sqrt (u * (1 - u / 4))) ≤ B E + C Eᶜ := by
  exact (ENNReal.ofReal_le_ofReal (sub_le_sub_left
    (sharp_hellinger_mono (hellingerSqMeasure_bounds B C).1 hH hu2.le) 1)).trans
      (binary_test_error_ge_sharp_hellinger B C hE)


end Causalean.Stat.Minimax
