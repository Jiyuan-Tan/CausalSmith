module
public import Causalean.Stat.Privacy.Staircase.Density

/-!
# Integrable staircase coefficients and row measures

This module separates the measure-theoretic step of staircase refinement from the
construction of its finite release and postprocessing kernels. A coefficient field
represents every row density almost everywhere; its coefficients are integrable,
reconstruct each row as a sum of density measures, and have normalized ray masses.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace Causalean.Stat.Privacy.Staircase

variable {Z : Type*} [MeasurableSpace Z]

/-- A nonnegative measurable field of fourteen ray coefficients represents all four
row densities almost everywhere under their common dominating measure. -/
structure CoefficientField (Q : Kernel (Fin 4) Z) (r : ℝ) where
  c : Z → RayIndex → ℝ
  measurable : ∀ S, Measurable fun z => c z S
  nonneg : ∀ z S, 0 ≤ c z S
  reconstruct : ∀ᵐ z ∂rowSum Q,
    ∀ i, rowDensity Q i z = ∑ S, c z S * ray r S i

/-- Every private Markov kernel has a measurable nonnegative coefficient field
representing all four row densities simultaneously. -/
theorem exists_coefficientField (Q : Kernel (Fin 4) Z) [IsMarkovKernel Q]
    (r : ℝ) (hr : 1 < r) (hpriv : SetwisePrivate Q r) :
    Nonempty (CoefficientField Q r) := by
  obtain ⟨c, hm, hn, heq⟩ := measurable_density_decomposition Q r hr hpriv
  exact ⟨⟨c, hm, hn, heq⟩⟩

/-- Each measurable ray coefficient is integrable against the finite row-sum
measure, including coefficients that vanish identically.

Proof plan: every ray coordinate is at least one for `r > 1`. At input zero,
the reconstruction therefore bounds each nonnegative coefficient by the
integrable row density. Use `Integrable.mono'` and RN reconstruction. -/
theorem coefficient_integrable (Q : Kernel (Fin 4) Z) [IsMarkovKernel Q]
    (r : ℝ) (hr : 1 < r) (D : CoefficientField Q r) (S : RayIndex) :
    Integrable (fun z => D.c z S) (rowSum Q) := by
  have hrow : Integrable (rowDensity Q 0) (rowSum Q) := by
    have hmeas : Measurable (fun z => ENNReal.ofReal (rowDensity Q 0 z)) := by
      exact ((Q 0).measurable_rnDeriv (rowSum Q)).ennreal_toReal.ennreal_ofReal
    have hfinite : Integrable (fun _ : Z => (1 : ℝ))
        ((rowSum Q).withDensity (fun z => ENNReal.ofReal (rowDensity Q 0 z))) := by
      rw [← row_eq_withDensity Q 0]
      exact integrable_const 1
    have h := (integrable_withDensity_iff hmeas (by simp)).1 hfinite
    convert h using 1
    funext z
    simpa using (ENNReal.toReal_ofReal
      (show 0 ≤ rowDensity Q 0 z from ENNReal.toReal_nonneg)).symm
  refine Integrable.mono' hrow (D.measurable S).aestronglyMeasurable ?_
  filter_upwards [D.reconstruct] with z hz
  have hbound : D.c z S ≤ rowDensity Q 0 z := by
    rw [hz 0]
    have hsum : D.c z S * ray r S 0 ≤
        ∑ T : RayIndex, D.c z T * ray r T 0 := by
      exact Finset.single_le_sum (s := Finset.univ)
        (f := fun T : RayIndex => D.c z T * ray r T 0)
        (by
          intro T _
          exact mul_nonneg (D.nonneg z T) (by
            unfold ray
            split_ifs <;> linarith)) (Finset.mem_univ S)
    have hray : 1 ≤ ray r S 0 := by
      unfold ray
      split_ifs <;> linarith
    have hcoeff := D.nonneg z S
    nlinarith
  have hrow_nonneg : 0 ≤ rowDensity Q 0 z := ENNReal.toReal_nonneg
  simpa [Real.norm_eq_abs, abs_of_nonneg (D.nonneg z S),
    abs_of_nonneg hrow_nonneg] using hbound

/-- Each Markov row is the finite sum of ray-scaled coefficient measures.

Proof plan: use `row_eq_withDensity`, rewrite its density by `D.reconstruct`,
and convert the real finite sum with `ENNReal.ofReal_sum_of_nonneg` and
`ENNReal.ofReal_mul`. Distribute the density with `withDensity_add_left`
and `withDensity_smul`; the latter needs measurability of `D.c` and the
nonnegative ray value. Alternatively prove equality on each measurable set
using `withDensity_apply`, `lintegral_finset_sum`, and `lintegral_const_mul`. -/
theorem coefficient_row_measure (Q : Kernel (Fin 4) Z) [IsMarkovKernel Q]
    (r : ℝ) (hr : 1 < r) (D : CoefficientField Q r) (i : Fin 4) :
    Q i = ∑ S : RayIndex,
      ENNReal.ofReal (ray r S i) •
        (rowSum Q).withDensity (fun z => ENNReal.ofReal (D.c z S)) := by
  let f : RayIndex → Z → ℝ≥0∞ := fun S z =>
    ENNReal.ofReal (ray r S i) * ENNReal.ofReal (D.c z S)
  have hf (S : RayIndex) : Measurable (f S) :=
    measurable_const.mul ((D.measurable S).ennreal_ofReal)
  have hpoint : (fun z => ENNReal.ofReal (rowDensity Q i z)) =ᵐ[rowSum Q]
      fun z => ∑ S : RayIndex, f S z := by
    filter_upwards [D.reconstruct] with z hz
    rw [hz i, ENNReal.ofReal_sum_of_nonneg]
    · apply Finset.sum_congr rfl
      intro S _
      rw [ENNReal.ofReal_mul (D.nonneg z S), mul_comm]
    · intro S _
      exact mul_nonneg (D.nonneg z S) (by
        unfold ray
        split_ifs <;> linarith)
  calc
    Q i = (rowSum Q).withDensity (fun z => ENNReal.ofReal (rowDensity Q i z)) :=
      row_eq_withDensity Q i
    _ = (rowSum Q).withDensity (fun z => ∑ S : RayIndex, f S z) :=
      withDensity_congr_ae hpoint
    _ = ∑ S : RayIndex, (rowSum Q).withDensity (f S) := by
      have hfun : (fun z => ∑ S : RayIndex, f S z) = (∑' S : RayIndex, f S) := by
        funext z
        rw [ENNReal.tsum_apply, tsum_fintype]
      rw [hfun, withDensity_tsum hf, Measure.sum_fintype]
    _ = ∑ S : RayIndex, ENNReal.ofReal (ray r S i) •
          (rowSum Q).withDensity (fun z => ENNReal.ofReal (D.c z S)) := by
      apply Finset.sum_congr rfl
      intro S _
      exact withDensity_smul _ ((D.measurable S).ennreal_ofReal)

/-- For [a four-input Markov kernel](hyp:Q), [a privacy ratio greater than one](hyp:hr) at
[the supplied ratio](hyp:r), [a measurable staircase coefficient field](hyp:D), and [an input
coordinate](hyp:i), the [integrated ray weights have unit weighted row sum](goal).

Integrating the coefficient field gives ray weights whose four weighted
row sums are all one.

Proof plan: integrate `D.reconstruct`, exchange the finite sum with the real
integral using `coefficient_integrable`, and apply the Markov mass of `Q i`.
`Measure.integral_toReal_rnDeriv` or `row_eq_withDensity` with
`integral_eq_lintegral_of_nonneg_ae` identifies the density integral with one. -/
theorem coefficient_normalized (Q : Kernel (Fin 4) Z) [IsMarkovKernel Q]
    (r : ℝ) (hr : 1 < r) (D : CoefficientField Q r) (i : Fin 4) :
    (∑ S : RayIndex, (∫ z, D.c z S ∂rowSum Q) * ray r S i) = 1 := by
  have hint (S : RayIndex) :
      Integrable (fun z => D.c z S * ray r S i) (rowSum Q) :=
    (coefficient_integrable Q r hr D S).mul_const _
  have : IsFiniteMeasure (rowSum Q) := rowSum_finite Q
  calc
    (∑ S : RayIndex, (∫ z, D.c z S ∂rowSum Q) * ray r S i) =
        ∫ z, ∑ S : RayIndex, D.c z S * ray r S i ∂rowSum Q := by
      rw [integral_finsetSum]
      · congr 1
        ext S
        rw [integral_mul_const]
      · intro S _
        exact hint S
    _ = ∫ z, rowDensity Q i z ∂rowSum Q := by
      apply integral_congr_ae
      filter_upwards [D.reconstruct] with z hz
      exact (hz i).symm
    _ = 1 := by
      change (∫ z, ((Q i).rnDeriv (rowSum Q) z).toReal ∂rowSum Q) = 1
      rw [Measure.integral_toReal_rnDeriv (row_absolutelyContinuous Q i)]
      simp [measureReal_def]

end Causalean.Stat.Privacy.Staircase
