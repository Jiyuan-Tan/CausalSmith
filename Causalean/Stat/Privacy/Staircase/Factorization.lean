module
public import Causalean.Stat.Privacy.Staircase.Release

/-!
# Measurable staircase refinement and exact postprocessing

Integrating the measurable ray coefficients gives a finite staircase channel. Conditional
normalization of each coefficient measure gives a Markov postprocessing kernel, including
zero-weight rays, whose composition is the original kernel.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace Causalean.Stat.Privacy.Staircase

variable {Z : Type*} [MeasurableSpace Z]

/-- A staircase refinement records normalized ray weights, the finite release, and an
output postprocessing kernel whose composition is the original four-input kernel. -/
structure Refinement (Q : Kernel (Fin 4) Z) (r : ℝ) where
  alpha : RayIndex → ℝ≥0
  T : Kernel (Fin 4) RayIndex
  K : Kernel RayIndex Z
  markovT : IsMarkovKernel T
  markovK : IsMarkovKernel K
  normalized : ∀ i, (∑ S, (alpha S : ℝ) * ray r S i) = 1
  release_singleton : ∀ i S,
    T i {S} = (alpha S : ℝ≥0∞) * ENNReal.ofReal (ray r S i)
  factorizes : Q = K ∘ₖ T

/-- If release singleton masses are the integrated ray coefficients and each
coefficient measure is its weight times a postprocessing row, the original kernel
is exactly the composition of the finite release and postprocessing kernels.

Proof plan: compare both kernels on every measurable set. Expand `Q i` with
`coefficient_row_measure`. Expand the composition using `Kernel.comp_apply'`
and the finite integral over `RayIndex`; substitute the singleton and coefficient
measure identities, and distribute scalar multiplication through the finite sum. -/
theorem coefficient_factorizes (Q : Kernel (Fin 4) Z) [IsMarkovKernel Q]
    (r : ℝ) (hr : 1 < r) (D : CoefficientField Q r)
    (α : RayIndex → ℝ≥0) (T : Kernel (Fin 4) RayIndex)
    (K : Kernel RayIndex Z)
    (hα : ∀ S, (α S : ℝ) = ∫ z, D.c z S ∂rowSum Q)
    (hT : ∀ i S, T i {S} = (α S : ℝ≥0∞) * ENNReal.ofReal (ray r S i))
    (hK : ∀ S, coefficientMeasure Q D S =
      ENNReal.ofReal (∫ z, D.c z S ∂rowSum Q) • K S) :
    Q = K ∘ₖ T := by
  ext i A hA
  rw [coefficient_row_measure Q r hr D i, Kernel.comp_apply' K T i hA,
    lintegral_fintype]
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro S _
  rw [← coefficientMeasure, hK S, hT i S]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [← hα S, ENNReal.ofReal_coe_nnreal]
  ac_rfl

/-- For [a four-input Markov kernel](hyp:Q), [a privacy ratio greater than one](hyp:hr) at
[the supplied ratio](hyp:r), and [setwise local privacy](hyp:hpriv), a [fourteen-ray
staircase refinement with exact Markov postprocessing](goal) exists on any measurable output
space.

Every setwise private four-input Markov kernel admits a fourteen-ray staircase
release followed by an exact Markov postprocessing kernel, even for an arbitrary
measurable output space.

Proof plan: integrate each nonnegative measurable coefficient against `rowSum Q`;
normalization follows by integrating the rowwise density identities. For positive
weights normalize the coefficient's with-density measure; on zero-weight rays choose
the first row as a Markov fallback. Assemble the finite release from its singleton
masses and verify composition on measurable sets. -/
theorem exists_refinement (Q : Kernel (Fin 4) Z) [IsMarkovKernel Q]
    (r : ℝ) (hr : 1 < r) (hpriv : SetwisePrivate Q r) :
    Nonempty (Refinement Q r) := by
  obtain ⟨D⟩ := exists_coefficientField Q r hr hpriv
  obtain ⟨α, T, hmarkovT, hα, hnorm, hT⟩ :=
    exists_coefficientRelease Q r hr D
  obtain ⟨K, hmarkovK, hK⟩ :=
    exists_coefficientPostprocess Q r hr D
  exact ⟨⟨α, T, K, hmarkovT, hmarkovK, hnorm, hT,
    coefficient_factorizes Q r hr D α T K hα hT hK⟩⟩

end Causalean.Stat.Privacy.Staircase
