module
public import Causalean.Stat.Privacy.LaplaceCoordinateMoments
public import Causalean.Stat.Privacy.LaplaceKernel
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Exact moments under randomized inputs

A probability input law and a measurable query with a square-integrable
selected coordinate give an integrable released-coordinate square and the
exact decomposition into input squared displacement plus `2 * b^2`.
Both measure-kernel composition and joint input-release cross terms are covered.
The nonnegative extended identity also holds without any moment assumption.
-/

public section

namespace Causalean.Stat.Privacy

open MeasureTheory ProbabilityTheory Causalean.Stat.Privacy
open scoped ENNReal

variable {D ι : Type*} [MeasurableSpace D] [Fintype ι]

/-- At [a real scale](hyp:b) with [a positive-scale certificate](hyp:hb), [a
query](hyp:q), [its measurability certificate](hyp:hq), [a probability input law](hyp:μ),
[a coordinate](hyp:i), and [a real center](hyp:c), [mixing the release gives the exact
nonnegative extended squared-displacement identity](goal), even for infinite input moments.

Use `Measure.lintegral_bind` and the conditional nonnegative moment in
`LaplaceCoordinateMoments.lean`. Split the nonnegative sum and use input mass one.

The notation `κ ∘ₘ μ` is definitionally `μ.bind κ`: apply
`Measure.lintegral_bind κ.aemeasurable` to the measurable nonnegative square.
Rewrite each inner integral with `laplaceMechPiKernel_apply` and
`laplaceMechPi_lintegral_coord_sub_sq`, split `ENNReal.ofReal_add` using
`sq_nonneg` and `mul_nonneg`, and use `lintegral_add` and `lintegral_const`.
No nonexistent `Measure.lintegral_comp` lemma is needed.
-/
theorem laplaceMechPiKernel_lintegral_coord_sub_sq (b : ℝ) (hb : 0 < b)
    (q : D → ι → ℝ) (hq : Measurable q)
    (μ : Measure D) [IsProbabilityMeasure μ] (i : ι) (c : ℝ) :
    ∫⁻ y, ENNReal.ofReal ((y i - c) ^ 2) ∂(laplaceMechPiKernel b hb q hq ∘ₘ μ) =
      (∫⁻ d, ENNReal.ofReal ((q d i - c) ^ 2) ∂μ) +
        ENNReal.ofReal (2 * b ^ 2) := by
  have hy : Measurable (fun y : ι → ℝ => ENNReal.ofReal ((y i - c) ^ 2)) :=
    (((measurable_pi_apply i).sub measurable_const).pow_const 2).ennreal_ofReal
  have hd : Measurable (fun d => ENNReal.ofReal ((q d i - c) ^ 2)) :=
    ((((measurable_pi_apply i).comp hq).sub measurable_const).pow_const 2).ennreal_ofReal
  change ∫⁻ y, ENNReal.ofReal ((y i - c) ^ 2)
      ∂μ.bind (laplaceMechPiKernel b hb q hq) = _
  rw [Measure.lintegral_bind (laplaceMechPiKernel b hb q hq).measurable.aemeasurable
    hy.aemeasurable]
  simp_rw [laplaceMechPiKernel_apply, laplaceMechPi_lintegral_coord_sub_sq b hb q,
    ENNReal.ofReal_add (sq_nonneg (q _ i - c))
      (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (sq_nonneg b))]
  rw [lintegral_add_left hd]
  simp

/-- At [a real scale](hyp:b) with [a positive-scale certificate](hyp:hb), [a
query](hyp:q), [its measurability certificate](hyp:hq), [a probability input law](hyp:μ),
[a coordinate](hyp:i), [a square-integrability certificate for that coordinate](hyp:hqsq),
and [a real center](hyp:c), [the mixed release has an integrable squared displacement](goal).

Convert `hqsq` to `MemLp (fun d => q d i) 2 μ`, subtract the constant center,
and transfer finiteness through the nonnegative extended moment identity above.
Do not assume integrability of the release or its desired moment as a premise.

Mathlib already supplies `memLp_two_iff_integrable_sq` and
`MemLp.integrable_sq` in `MeasureTheory.Function.L2Space`; use these with
`MemLp.sub` and the constant's `MemLp` instance for the shifted input square.
There is no need for a new general square-integrability helper module.

The selected coordinate is measurable by `(measurable_pi_apply i).comp hq`.
Obtain its `MemLp` proof with `(memLp_two_iff_integrable_sq ...).mpr hqsq`,
then use `(hL2.sub (memLp_const c)).integrable_sq` for the input displacement.
For the output, `hasFiniteIntegral_iff_ofReal` applies because squares are
nonnegative. The preceding extended identity makes this integral finite;
both summands are below infinity. Prove output strong measurability separately.
-/
theorem laplaceMechPiKernel_integrable_coord_sub_sq (b : ℝ) (hb : 0 < b)
    (q : D → ι → ℝ) (hq : Measurable q)
    (μ : Measure D) [IsProbabilityMeasure μ] (i : ι)
    (hqsq : Integrable (fun d => (q d i) ^ 2) μ) (c : ℝ) :
    Integrable (fun y => (y i - c) ^ 2)
      (laplaceMechPiKernel b hb q hq ∘ₘ μ) := by
  have hL2 : MemLp (fun d => q d i) 2 μ :=
    (memLp_two_iff_integrable_sq
      ((measurable_pi_apply i).comp hq).aestronglyMeasurable).mpr hqsq
  have hin : Integrable (fun d => (q d i - c) ^ 2) μ :=
    (hL2.sub (memLp_const c)).integrable_sq
  refine ⟨(show Measurable (fun y : ι → ℝ => (y i - c) ^ 2) from
    ((measurable_pi_apply i).sub measurable_const).pow_const 2).aestronglyMeasurable, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun y : ι → ℝ => sq_nonneg (y i - c))).mpr
  rw [laplaceMechPiKernel_lintegral_coord_sub_sq b hb q hq μ i c]
  exact ENNReal.add_lt_top.mpr
    ⟨(hasFiniteIntegral_iff_ofReal (ae_of_all _ fun d => sq_nonneg (q d i - c))).mp
      hin.hasFiniteIntegral, ENNReal.ofReal_lt_top⟩

/-- At [a real scale](hyp:b) with [a positive-scale certificate](hyp:hb), [a
query](hyp:q), [its measurability certificate](hyp:hq), [a probability input law](hyp:μ),
[a coordinate](hyp:i), [a square-integrability certificate for that coordinate](hyp:hqsq),
and [a real center](hyp:c), [the release's squared-displacement expectation equals the
input squared displacement plus exactly twice the squared noise scale](goal).

Use the integrability theorem before converting the nonnegative extended
identity to an ordinary integral. Alternatively use the kernel Bochner/Fubini
theorems and the conditional identity; all integrability obligations must be proved.

The extended-integral route avoids a new ordinary measure-composition helper:
apply `ofReal_integral_eq_lintegral_ofReal` to the input and output squares,
rewrite `ENNReal.ofReal_add` using integral nonnegativity, and cancel `ofReal`
on nonnegative reals (or apply `ENNReal.toReal` after checking finiteness).
-/
theorem laplaceMechPiKernel_integral_coord_sub_sq (b : ℝ) (hb : 0 < b)
    (q : D → ι → ℝ) (hq : Measurable q)
    (μ : Measure D) [IsProbabilityMeasure μ] (i : ι)
    (hqsq : Integrable (fun d => (q d i) ^ 2) μ) (c : ℝ) :
    ∫ y, (y i - c) ^ 2 ∂(laplaceMechPiKernel b hb q hq ∘ₘ μ) =
      (∫ d, (q d i - c) ^ 2 ∂μ) + 2 * b ^ 2 := by
  have hL2 : MemLp (fun d => q d i) 2 μ :=
    (memLp_two_iff_integrable_sq
      ((measurable_pi_apply i).comp hq).aestronglyMeasurable).mpr hqsq
  have hin : Integrable (fun d => (q d i - c) ^ 2) μ :=
    (hL2.sub (memLp_const c)).integrable_sq
  have hout := laplaceMechPiKernel_integrable_coord_sub_sq b hb q hq μ i hqsq c
  have hid := laplaceMechPiKernel_lintegral_coord_sub_sq b hb q hq μ i c
  rw [← ofReal_integral_eq_lintegral_ofReal hout
      (ae_of_all _ fun y => sq_nonneg (y i - c)),
    ← ofReal_integral_eq_lintegral_ofReal hin
      (ae_of_all _ fun d => sq_nonneg (q d i - c)),
    ← ENNReal.ofReal_add (integral_nonneg fun d => sq_nonneg (q d i - c))
      (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (sq_nonneg b))] at hid
  exact (ENNReal.ofReal_eq_ofReal_iff
    (integral_nonneg (μ := laplaceMechPiKernel b hb q hq ∘ₘ μ)
      fun y : ι → ℝ => sq_nonneg (y i - c))
    (add_nonneg (integral_nonneg fun d => sq_nonneg (q d i - c))
      (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (sq_nonneg b)))).mp hid

/-- At [a real scale](hyp:b) with [a positive-scale certificate](hyp:hb), [a
query](hyp:q), [its measurability certificate](hyp:hq), [a probability input law](hyp:μ),
[a coordinate](hyp:i), [a square-integrability certificate for that coordinate](hyp:hqsq),
and [a real center](hyp:c), [the displacement-error cross term is integrable under the
joint input-release law](goal).

Use `Measure.integrable_compProd_iff` for the joint law. Its two obligations
are conditional integrability and input integrability of the conditional norm
integral; input and release need no product-independence assumption.

A short route uses the primary library's exact absolute moment. Transfer
`laplaceMeasure_integral_abs b hb` through
`laplaceMechPi_map_centered_coord` and `integral_map` to get
`∫ y, |y i - q d i| ∂laplaceMechPi b q d = b` at each input.
Conditional cross integrability follows from centered-coordinate integrability
by `Integrable.const_mul`. Rewrite `norm_mul` and `Real.norm_eq_abs` to see
that its conditional norm integral is `|q d i - c| * b`.
The input displacement is integrable by the same `MemLp` conversion as above
and `MemLp.integrable (by norm_num)`; its norm times `b` is therefore integrable.
This avoids introducing joint square helpers solely to bound the product.
-/
theorem laplaceMechPiKernel_integrable_cross (b : ℝ) (hb : 0 < b)
    (q : D → ι → ℝ) (hq : Measurable q)
    (μ : Measure D) [IsProbabilityMeasure μ] (i : ι)
    (hqsq : Integrable (fun d => (q d i) ^ 2) μ) (c : ℝ) :
    Integrable (fun p : D × (ι → ℝ) =>
      (q p.1 i - c) * (p.2 i - q p.1 i))
      (μ ⊗ₘ laplaceMechPiKernel b hb q hq) := by
  have hL2 : MemLp (fun d => q d i) 2 μ :=
    (memLp_two_iff_integrable_sq
      ((measurable_pi_apply i).comp hq).aestronglyMeasurable).mpr hqsq
  have hin : Integrable (fun d => q d i - c) μ :=
    (hL2.sub (memLp_const c)).integrable (by norm_num)
  have hf : Measurable (fun p : D × (ι → ℝ) =>
      (q p.1 i - c) * (p.2 i - q p.1 i)) :=
    (((measurable_pi_apply i).comp (hq.comp measurable_fst)).sub measurable_const).mul
      (((measurable_pi_apply i).comp measurable_snd).sub
        ((measurable_pi_apply i).comp (hq.comp measurable_fst)))
  apply (Measure.integrable_compProd_iff hf.aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ fun d =>
      (laplaceMechPi_integrable_centered_coord b hb q d i).const_mul (q d i - c)
  · have habs (d : D) : ∫ y, |y i - q d i| ∂laplaceMechPi b q d = b := by
      have hmap := integral_map (μ := laplaceMechPi b q d)
        (φ := fun y => y i - q d i) (f := fun x : ℝ => |x|)
        ((measurable_pi_apply i).sub measurable_const).aemeasurable (by fun_prop)
      rw [laplaceMechPi_map_centered_coord b hb q d i,
        laplaceMeasure_integral_abs b hb] at hmap
      exact hmap.symm
    simpa only [laplaceMechPiKernel_apply, norm_mul, Real.norm_eq_abs,
      integral_const_mul, habs] using hin.norm.mul_const b

/-- At [a real scale](hyp:b) with [a positive-scale certificate](hyp:hb), [a
query](hyp:q), [its measurability certificate](hyp:hq), [a probability input law](hyp:μ),
[a coordinate](hyp:i), [a square-integrability certificate for that coordinate](hyp:hqsq),
and [a real center](hyp:c), [the displacement-error cross term has integral zero](goal).

Apply `Measure.integral_compProd` after proving cross-term integrability,
then use the conditional centered coordinate mean to cancel every inner integral.

Rewrite kernel evaluation, factor the input displacement with
`integral_const_mul`, and apply `laplaceMechPi_integral_centered_coord`.
The iterated integral is then the integral of the constant zero function.
-/
theorem laplaceMechPiKernel_integral_cross (b : ℝ) (hb : 0 < b)
    (q : D → ι → ℝ) (hq : Measurable q)
    (μ : Measure D) [IsProbabilityMeasure μ] (i : ι)
    (hqsq : Integrable (fun d => (q d i) ^ 2) μ) (c : ℝ) :
    ∫ p : D × (ι → ℝ), (q p.1 i - c) * (p.2 i - q p.1 i)
      ∂(μ ⊗ₘ laplaceMechPiKernel b hb q hq) = 0 := by
  rw [Measure.integral_compProd
    (laplaceMechPiKernel_integrable_cross b hb q hq μ i hqsq c)]
  simp only [laplaceMechPiKernel_apply, integral_const_mul,
    laplaceMechPi_integral_centered_coord b hb q, mul_zero, integral_zero]

-- A type-checking witness that the general API covers Fin 2 without paper types.
example (b : ℝ) (hb : 0 < b) (q : D → Fin 2 → ℝ) (hq : Measurable q)
    (μ : Measure D) [IsProbabilityMeasure μ] (i : Fin 2)
    (hqsq : Integrable (fun d => (q d i) ^ 2) μ) (c : ℝ) :
    ∫ y, (y i - c) ^ 2 ∂(laplaceMechPiKernel b hb q hq ∘ₘ μ) =
      (∫ d, (q d i - c) ^ 2 ∂μ) + 2 * b ^ 2 :=
  laplaceMechPiKernel_integral_coord_sub_sq b hb q hq μ i hqsq c

end Causalean.Stat.Privacy
