module
public import Causalean.Stat.Privacy.Staircase.Factorization
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Fisher information monotonicity and equality rigidity

This module states the finite-dimensional conditional-variance inequality for staircase
postprocessing and its equality case: rays with distinct projected scores induce mutually
singular output laws.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace Causalean.Stat.Privacy.Staircase

variable {Z : Type*} [MeasurableSpace Z]

/-- Project a finite-dimensional input score onto one real direction. -/
def projectedScore {d : ℕ} (u : Fin 4 → Fin d → ℝ) (v : Fin d → ℝ) (i : Fin 4) : ℝ :=
  ∑ k, v k * u i k

/-- The mixture mass of a finite release atom under input probabilities `p`. -/
def releaseMass (T : Kernel (Fin 4) RayIndex) (p : Fin 4 → ℝ) (S : RayIndex) : ℝ :=
  ∑ i, p i * (T i {S}).toReal

/-- The projected score of an active finite release atom under input probabilities `p`. -/
def releaseScore (T : Kernel (Fin 4) RayIndex) (p u : Fin 4 → ℝ) (S : RayIndex) : ℝ :=
  (∑ i, p i * (T i {S}).toReal * u i) / releaseMass T p S

/-- Directional Fisher information of the finite staircase release, with zero-mass
atoms contributing zero by the division convention. -/
def finiteFisher (T : Kernel (Fin 4) RayIndex) (p u : Fin 4 → ℝ) : ℝ :=
  ∑ S, (∑ i, p i * (T i {S}).toReal * u i) ^ 2 / releaseMass T p S

/-- Directional Fisher information of the general output kernel, expressed using the
common dominating row-sum measure and its four measurable densities. -/
def outputFisher (Q : Kernel (Fin 4) Z) (p u : Fin 4 → ℝ) : ℝ :=
  ∫ z, (∑ i, p i * rowDensity Q i z * u i) ^ 2 /
    (∑ i, p i * rowDensity Q i z) ∂rowSum Q

/-- The projected score after observing the general output, defined to be zero where
the output mixture density vanishes. -/
def outputScore (Q : Kernel (Fin 4) Z) (p u : Fin 4 → ℝ) (z : Z) : ℝ :=
  (∑ i, p i * rowDensity Q i z * u i) /
    (∑ i, p i * rowDensity Q i z)

/-- The conditional-variance expression for information lost through the
postprocessing kernel. -/
def varianceGap (Q : Kernel (Fin 4) Z) (r : ℝ) (R : Refinement Q r)
    (p u : Fin 4 → ℝ) : ℝ :=
  ∑ S, releaseMass R.T p S *
    ∫ z, (releaseScore R.T p u S - outputScore Q p u z) ^ 2 ∂(R.K S)

/-- The second moment of the finite release score, integrated through each
postprocessing row, is the directional Fisher information of the release.

At a zero-mass release atom, nonnegativity of the Markov masses forces its
score numerator to vanish. At positive mass, cancel the denominator in the
definition of `releaseScore`, then use that `R.K S` is a probability measure. -/
theorem finite_score_second_moment (Q : Kernel (Fin 4) Z) [IsMarkovKernel Q]
    (r : ℝ) (R : Refinement Q r) (p u : Fin 4 → ℝ)
    (hp : ∀ i, 0 < p i) :
    (∑ S, releaseMass R.T p S *
      ∫ z : Z, (releaseScore R.T p u S) ^ 2 ∂(R.K S)) =
      finiteFisher R.T p u := by
  letI : IsMarkovKernel R.T := R.markovT
  letI : IsMarkovKernel R.K := R.markovK
  have hmass_nonneg (S : RayIndex) : 0 ≤ releaseMass R.T p S := by
    unfold releaseMass
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (le_of_lt (hp i)) ENNReal.toReal_nonneg
  have hnum_zero (S : RayIndex) (hS : releaseMass R.T p S = 0) :
      (∑ i, p i * (R.T i {S}).toReal * u i) = 0 := by
    have hterm (i : Fin 4) : p i * (R.T i {S}).toReal = 0 := by
      have hle : p i * (R.T i {S}).toReal ≤ releaseMass R.T p S := by
        unfold releaseMass
        exact Finset.single_le_sum (s := Finset.univ)
          (f := fun j : Fin 4 => p j * (R.T j {S}).toReal)
          (fun j hj => mul_nonneg (le_of_lt (hp j)) ENNReal.toReal_nonneg)
          (Finset.mem_univ i)
      have hnonneg : 0 ≤ p i * (R.T i {S}).toReal :=
        mul_nonneg (le_of_lt (hp i)) ENNReal.toReal_nonneg
      exact le_antisymm (hS ▸ hle) hnonneg
    simp [hterm]
  unfold finiteFisher
  apply Finset.sum_congr rfl
  intro S hS
  have hIntegral :
      (∫ z : Z, (releaseScore R.T p u S) ^ 2 ∂(R.K S)) =
        (releaseScore R.T p u S) ^ 2 := by
    simp
  rw [hIntegral]
  by_cases hm : releaseMass R.T p S = 0
  · rw [hm, hnum_zero S hm]
    simp [releaseScore, hm]
  · have hmpos : 0 < releaseMass R.T p S := lt_of_le_of_ne (hmass_nonneg S) (Ne.symm hm)
    unfold releaseScore
    field_simp [ne_of_gt hmpos]

private theorem outputScore_bound (Q : Kernel (Fin 4) Z) (p u : Fin 4 → ℝ)
    (hp : ∀ i, 0 ≤ p i) (z : Z) :
    |outputScore Q p u z| ≤ ∑ i, |u i| := by
  let a : Fin 4 → ℝ := fun i => p i * rowDensity Q i z
  let C : ℝ := ∑ i, |u i|
  have ha (i : Fin 4) : 0 ≤ a i :=
    mul_nonneg (hp i) ENNReal.toReal_nonneg
  have hC (i : Fin 4) : |u i| ≤ C :=
    Finset.single_le_sum (s := Finset.univ) (f := fun i : Fin 4 => |u i|)
      (fun j hj => abs_nonneg _) (Finset.mem_univ i)
  have hnum : |∑ i, a i * u i| ≤ (∑ i, a i) * C := by
    calc
      |∑ i, a i * u i| ≤ ∑ i, |a i * u i| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, a i * |u i| := by simp_rw [abs_mul, abs_of_nonneg (ha _)]
      _ ≤ ∑ i, a i * C := Finset.sum_le_sum (by
        intro i hi
        exact mul_le_mul_of_nonneg_left (hC i) (ha i))
      _ = (∑ i, a i) * C := by rw [Finset.sum_mul]
  have hden : 0 ≤ ∑ i, a i := Finset.sum_nonneg (fun i hi => ha i)
  have hzero (h : (∑ i, a i) = 0) : (∑ i, a i * u i) = 0 := by
    have hC0 : 0 ≤ C := Finset.sum_nonneg (fun i hi => abs_nonneg _)
    have := hnum
    rw [h, zero_mul] at this
    exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))
  change |(∑ i, a i * u i) / (∑ i, a i)| ≤ C
  by_cases hd : (∑ i, a i) = 0
  · simp only [hd, hzero hd, zero_div, abs_zero]
    exact Finset.sum_nonneg (fun i hi => abs_nonneg (u i))
  · have hdpos : 0 < ∑ i, a i := lt_of_le_of_ne hden (Ne.symm hd)
    rw [abs_div, abs_of_pos hdpos]
    exact (div_le_iff₀ hdpos).2 (by simpa only [mul_comm] using hnum)

private theorem weighted_release_integral (Q : Kernel (Fin 4) Z) [IsMarkovKernel Q]
    (r : ℝ) (R : Refinement Q r) (w : Fin 4 → ℝ) (f : Z → ℝ)
    (hK : ∀ S, Integrable f (R.K S)) (hQ : ∀ i, Integrable f (Q i)) :
    (∑ S, (∑ i, w i * (R.T i {S}).toReal) * ∫ z, f z ∂(R.K S)) =
      ∫ z, (∑ i, w i * rowDensity Q i z) * f z ∂rowSum Q := by
  letI : IsMarkovKernel R.T := R.markovT
  letI : IsMarkovKernel R.K := R.markovK
  have hcomp (i : Fin 4) :
      (∑ S, (R.T i {S}).toReal * ∫ z, f z ∂(R.K S)) =
        ∫ z, f z ∂(Q i) := by
    have h := ProbabilityTheory.Kernel.integral_comp (κ := R.T) (η := R.K)
      (a := i) (by simpa [← R.factorizes] using hQ i)
    have hfactor : Q i = (R.K ∘ₖ R.T) i := congrArg (fun L => L i) R.factorizes
    rw [hfactor, h, integral_fintype (Integrable.of_finite)]
    simp only [measureReal_def, smul_eq_mul]
  have hrow (i : Fin 4) :
      Integrable (fun z => rowDensity Q i z * f z) (rowSum Q) := by
    have hm : Measurable (fun z => ENNReal.ofReal (rowDensity Q i z)) := by
      exact ((Q i).measurable_rnDeriv (rowSum Q)).ennreal_toReal.ennreal_ofReal
    have ht : ∀ᵐ z ∂rowSum Q,
        ENNReal.ofReal (rowDensity Q i z) < ⊤ := by
      exact ae_of_all _ (fun z => ENNReal.ofReal_lt_top)
    have := (integrable_withDensity_iff_integrable_smul' hm ht).1
      (by simpa [row_eq_withDensity Q i] using hQ i)
    have hz (z : Z) : (ENNReal.ofReal (rowDensity Q i z)).toReal =
        rowDensity Q i z := ENNReal.toReal_ofReal ENNReal.toReal_nonneg
    simpa only [hz, smul_eq_mul] using this
  have hroweq (i : Fin 4) :
      (∫ z, f z ∂(Q i)) =
        ∫ z, rowDensity Q i z * f z ∂rowSum Q := by
    rw [row_eq_withDensity Q i]
    rw [integral_withDensity_eq_integral_toReal_smul]
    · have hz (z : Z) : (ENNReal.ofReal (rowDensity Q i z)).toReal =
          rowDensity Q i z := ENNReal.toReal_ofReal ENNReal.toReal_nonneg
      simp only [hz, smul_eq_mul]
    · exact ((Q i).measurable_rnDeriv (rowSum Q)).ennreal_toReal.ennreal_ofReal
    · exact ae_of_all _ (fun z => ENNReal.ofReal_lt_top)
  calc
    (∑ S, (∑ i, w i * (R.T i {S}).toReal) * ∫ z, f z ∂(R.K S)) =
        ∑ i, w i * ∑ S, (R.T i {S}).toReal * ∫ z, f z ∂(R.K S) := by
          simp_rw [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro S hS
          ring
    _ = ∑ i, w i * ∫ z, f z ∂(Q i) := by simp_rw [hcomp]
    _ = ∑ i, ∫ z, (w i * rowDensity Q i z) * f z ∂rowSum Q := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hroweq i, ← integral_const_mul]
      congr 1
      funext z
      ring
    _ = ∫ z, (∑ i, w i * rowDensity Q i z) * f z ∂rowSum Q := by
      rw [← integral_finsetSum]
      · congr 1
        funext z
        rw [Finset.sum_mul]
      · intro i hi
        convert (hrow i).const_mul (w i) using 1 with z
        ring

private theorem releaseMass_mul_releaseScore (T : Kernel (Fin 4) RayIndex)
    (p u : Fin 4 → ℝ) (hp : ∀ i, 0 < p i) (S : RayIndex) :
    releaseMass T p S * releaseScore T p u S =
      ∑ i, p i * (T i {S}).toReal * u i := by
  have hzero (hS : releaseMass T p S = 0) :
      (∑ i, p i * (T i {S}).toReal * u i) = 0 := by
    have hterm (i : Fin 4) : p i * (T i {S}).toReal = 0 := by
      have hle : p i * (T i {S}).toReal ≤ releaseMass T p S := by
        unfold releaseMass
        exact Finset.single_le_sum (s := Finset.univ)
          (f := fun j : Fin 4 => p j * (T j {S}).toReal)
          (fun j hj => mul_nonneg (le_of_lt (hp j)) ENNReal.toReal_nonneg)
          (Finset.mem_univ i)
      exact le_antisymm (hS ▸ hle)
        (mul_nonneg (le_of_lt (hp i)) ENNReal.toReal_nonneg)
    simp [hterm]
  by_cases hm : releaseMass T p S = 0
  · simp [hm, hzero hm]
  · unfold releaseScore
    field_simp [hm]

private theorem outputScore_integrable (Q : Kernel (Fin 4) Z) (p u : Fin 4 → ℝ)
    (hp : ∀ i, 0 ≤ p i) (μ : Measure Z) [IsFiniteMeasure μ] :
    Integrable (outputScore Q p u) μ := by
  have hm : Measurable (outputScore Q p u) := by
    unfold outputScore rowDensity
    fun_prop
  apply Integrable.of_bound hm.aestronglyMeasurable (∑ i, |u i|)
  exact ae_of_all _ (fun z => by
    simpa only [Real.norm_eq_abs] using outputScore_bound Q p u hp z)

private theorem outputScore_sq_integrable (Q : Kernel (Fin 4) Z) (p u : Fin 4 → ℝ)
    (hp : ∀ i, 0 ≤ p i) (μ : Measure Z) [IsFiniteMeasure μ] :
    Integrable (fun z => (outputScore Q p u z) ^ 2) μ := by
  have hm : Measurable (outputScore Q p u) := by
    unfold outputScore rowDensity
    fun_prop
  apply Integrable.of_bound (hm.pow_const 2).aestronglyMeasurable
    ((∑ i, |u i|) ^ 2)
  exact ae_of_all _ (fun z => by
    have hb := outputScore_bound Q p u hp z
    have hC : 0 ≤ ∑ i, |u i| := Finset.sum_nonneg (fun i hi => abs_nonneg _)
    rw [Real.norm_eq_abs, abs_pow]
    nlinarith [mul_nonneg (sub_nonneg.mpr hb)
      (add_nonneg hC (abs_nonneg (outputScore Q p u z)))])

/-- The mixed moment of the finite release score and output score is the
directional Fisher information of the postprocessed output.

Use `R.factorizes` to identify the signed score measure on `Z` from both
sides. The score is bounded by the largest absolute input score because all
four row densities and input probabilities are nonnegative. -/
theorem score_cross_moment (Q : Kernel (Fin 4) Z) [IsMarkovKernel Q]
    (r : ℝ) (R : Refinement Q r) (p u : Fin 4 → ℝ)
    (hp : ∀ i, 0 < p i) (hpsum : ∑ i, p i = 1) :
    (∑ S, releaseMass R.T p S * releaseScore R.T p u S *
      ∫ z, outputScore Q p u z ∂(R.K S)) =
      outputFisher Q p u := by
  have hK (S : RayIndex) : Integrable (outputScore Q p u) (R.K S) := by
    letI : IsMarkovKernel R.K := R.markovK
    exact outputScore_integrable Q p u (fun i => le_of_lt (hp i)) _
  have hQ (i : Fin 4) : Integrable (outputScore Q p u) (Q i) :=
    outputScore_integrable Q p u (fun i => le_of_lt (hp i)) _
  calc
    (∑ S, releaseMass R.T p S * releaseScore R.T p u S *
      ∫ z, outputScore Q p u z ∂(R.K S)) =
        ∑ S, (∑ i, (p i * u i) * (R.T i {S}).toReal) *
          ∫ z, outputScore Q p u z ∂(R.K S) := by
            apply Finset.sum_congr rfl
            intro S hS
            rw [releaseMass_mul_releaseScore R.T p u hp S]
            congr 1
            apply Finset.sum_congr rfl
            intro i hi
            ring
    _ = ∫ z, (∑ i, (p i * u i) * rowDensity Q i z) *
        outputScore Q p u z ∂rowSum Q :=
      weighted_release_integral Q r R (fun i => p i * u i)
        (outputScore Q p u) hK hQ
    _ = outputFisher Q p u := by
      unfold outputFisher
      apply integral_congr_ae
      filter_upwards [] with z
      have hs : (∑ i, (p i * u i) * rowDensity Q i z) =
          ∑ i, p i * rowDensity Q i z * u i := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [hs]
      unfold outputScore
      ring

/-- The second moment of the output score under the postprocessed release
equals the directional Fisher information of the output.

The release mixture and the output mixture are equal measures by
`R.factorizes`; their common density against `rowSum Q` is the positive
input-weighted sum of the four row densities. -/
theorem output_score_second_moment (Q : Kernel (Fin 4) Z) [IsMarkovKernel Q]
    (r : ℝ) (R : Refinement Q r) (p u : Fin 4 → ℝ)
    (hp : ∀ i, 0 < p i) (hpsum : ∑ i, p i = 1) :
    (∑ S, releaseMass R.T p S *
      ∫ z, (outputScore Q p u z) ^ 2 ∂(R.K S)) =
      outputFisher Q p u := by
  have hK (S : RayIndex) :
      Integrable (fun z => (outputScore Q p u z) ^ 2) (R.K S) := by
    letI : IsMarkovKernel R.K := R.markovK
    exact outputScore_sq_integrable Q p u (fun i => le_of_lt (hp i)) _
  have hQ (i : Fin 4) :
      Integrable (fun z => (outputScore Q p u z) ^ 2) (Q i) :=
    outputScore_sq_integrable Q p u (fun i => le_of_lt (hp i)) _
  calc
    (∑ S, releaseMass R.T p S *
      ∫ z, (outputScore Q p u z) ^ 2 ∂(R.K S)) =
        ∑ S, (∑ i, p i * (R.T i {S}).toReal) *
          ∫ z, (outputScore Q p u z) ^ 2 ∂(R.K S) := by
            rfl
    _ = ∫ z, (∑ i, p i * rowDensity Q i z) *
        (outputScore Q p u z) ^ 2 ∂rowSum Q :=
      weighted_release_integral Q r R p
        (fun z => (outputScore Q p u z) ^ 2) hK hQ
    _ = outputFisher Q p u := by
      unfold outputFisher
      apply integral_congr_ae
      filter_upwards [] with z
      unfold outputScore
      by_cases hd : (∑ i, p i * rowDensity Q i z) = 0
      · simp [hd]
      · field_simp

/-- The directional Fisher-information loss is exactly the conditional variance of
the release score given the postprocessed output.

Proof plan: expand the square, use the release-to-output factorization to identify
the output first and second score moments, and use the Markov normalization of each
postprocessing row. Handle zero release masses using the zero numerator convention. -/
theorem fisher_gap_eq_variance (Q : Kernel (Fin 4) Z) [IsMarkovKernel Q]
    (r : ℝ) (R : Refinement Q r) (p u : Fin 4 → ℝ)
    (hp : ∀ i, 0 < p i) (hpsum : ∑ i, p i = 1) :
    finiteFisher R.T p u - outputFisher Q p u = varianceGap Q r R p u := by
  letI : IsMarkovKernel R.K := R.markovK
  have hrow (S : RayIndex) :
      (∫ z, (releaseScore R.T p u S - outputScore Q p u z) ^ 2 ∂(R.K S)) =
        (∫ z, (releaseScore R.T p u S) ^ 2 ∂(R.K S)) -
        2 * releaseScore R.T p u S *
          (∫ z, outputScore Q p u z ∂(R.K S)) +
        (∫ z, (outputScore Q p u z) ^ 2 ∂(R.K S)) := by
    have hscore : Integrable (outputScore Q p u) (R.K S) :=
      outputScore_integrable Q p u (fun i => le_of_lt (hp i)) _
    have hsq : Integrable (fun z => (outputScore Q p u z) ^ 2) (R.K S) :=
      outputScore_sq_integrable Q p u (fun i => le_of_lt (hp i)) _
    calc
      (∫ z, (releaseScore R.T p u S - outputScore Q p u z) ^ 2 ∂(R.K S)) =
          ∫ z, (releaseScore R.T p u S) ^ 2 -
            (2 * releaseScore R.T p u S) * outputScore Q p u z +
            (outputScore Q p u z) ^ 2 ∂(R.K S) := by
              congr 1
              funext z
              ring
      _ = (∫ z, (releaseScore R.T p u S) ^ 2 ∂(R.K S)) -
            2 * releaseScore R.T p u S *
              (∫ z, outputScore Q p u z ∂(R.K S)) +
            (∫ z, (outputScore Q p u z) ^ 2 ∂(R.K S)) := by
              calc
                _ = (∫ z, (releaseScore R.T p u S) ^ 2 -
                    (2 * releaseScore R.T p u S) * outputScore Q p u z ∂(R.K S)) +
                    ∫ z, (outputScore Q p u z) ^ 2 ∂(R.K S) := by
                      exact integral_add
                        ((integrable_const _).sub (hscore.const_mul _)) hsq
                _ = _ := by
                  rw [integral_sub (integrable_const _) (hscore.const_mul _)]
                  rw [integral_const_mul]
  unfold varianceGap
  calc
    finiteFisher R.T p u - outputFisher Q p u =
        (∑ S, releaseMass R.T p S *
          ∫ z, (releaseScore R.T p u S) ^ 2 ∂(R.K S)) -
        2 * (∑ S, releaseMass R.T p S * releaseScore R.T p u S *
          ∫ z, outputScore Q p u z ∂(R.K S)) +
        (∑ S, releaseMass R.T p S *
          ∫ z, (outputScore Q p u z) ^ 2 ∂(R.K S)) := by
            rw [finite_score_second_moment Q r R p u hp,
              score_cross_moment Q r R p u hp hpsum,
              output_score_second_moment Q r R p u hp hpsum]
            ring
    _ = ∑ S, releaseMass R.T p S *
          ∫ z, (releaseScore R.T p u S - outputScore Q p u z) ^ 2 ∂(R.K S) := by
            rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro S hS
            rw [hrow S]
            ring

/-- Given [a four-input Markov kernel](hyp:Q), [a privacy ratio](hyp:r), [a staircase
refinement](hyp:R), [strictly positive input probabilities](hyp:hp) that [sum to one](hyp:hpsum),
[a finite-dimensional input score](hyp:u), and [a score direction](hyp:v), [the directional
Fisher-information gap is nonnegative](goal).

Postprocessing cannot increase Fisher information in any direction of a finite
dimensional input score; the directional difference is positive semidefinite.

Proof plan: use `R.factorizes` to identify the output mixture and signed score measure.
The finite score is constant on each release atom. Its conditional expectation given
the output is the output score; the difference is the integral of conditional variance.
Equivalently, prove pointwise weighted Cauchy–Schwarz using the coefficient measures. -/
theorem fisher_gap_nonneg {d : ℕ} (Q : Kernel (Fin 4) Z) [IsMarkovKernel Q]
    (r : ℝ) (R : Refinement Q r) (p : Fin 4 → ℝ)
    (hp : ∀ i, 0 < p i) (hpsum : ∑ i, p i = 1)
    (u : Fin 4 → Fin d → ℝ) (v : Fin d → ℝ) :
    0 ≤ finiteFisher R.T p (projectedScore u v) -
      outputFisher Q p (projectedScore u v) := by
  rw [fisher_gap_eq_variance Q r R p (projectedScore u v) hp hpsum]
  unfold varianceGap
  apply Finset.sum_nonneg
  intro S _
  apply mul_nonneg
  · unfold releaseMass
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (le_of_lt (hp i)) ENNReal.toReal_nonneg
  · exact integral_nonneg fun z => sq_nonneg _

/-- Given [a four-input Markov kernel](hyp:Q), [a privacy ratio](hyp:r), [a staircase
refinement](hyp:R), [strictly positive input probabilities](hyp:hp) that [sum to one](hyp:hpsum),
[a finite-dimensional input score](hyp:u), [a score direction](hyp:v), [a zero directional
Fisher gap](hyp:hgap), [two rays](hyp:S,U) with [positive release mass](hyp:hS,hU), and
[different projected scores](hyp:hdiff), the [two postprocessing laws are mutually singular](goal).

If the directional Fisher gap vanishes, any two active staircase rays with
different projected scores have mutually singular postprocessing laws. This pairwise
singularity is the form used to count stationary output atoms.

Proof plan: zero integrated conditional variance gives equality of the release score
and output score almost everywhere under every positive ray contribution. Distinct
release scores therefore live on disjoint measurable level sets. -/
theorem equality_rigidity {d : ℕ} (Q : Kernel (Fin 4) Z) [IsMarkovKernel Q]
    (r : ℝ) (R : Refinement Q r) (p : Fin 4 → ℝ)
    (hp : ∀ i, 0 < p i) (hpsum : ∑ i, p i = 1)
    (u : Fin 4 → Fin d → ℝ) (v : Fin d → ℝ)
    (hgap : finiteFisher R.T p (projectedScore u v) -
      outputFisher Q p (projectedScore u v) = 0)
    (S U : RayIndex) (hS : 0 < releaseMass R.T p S)
    (hU : 0 < releaseMass R.T p U)
    (hdiff : releaseScore R.T p (projectedScore u v) S ≠
      releaseScore R.T p (projectedScore u v) U) :
    R.K S ⟂ₘ R.K U := by
  let w := projectedScore u v
  have hvar : (∑ V, releaseMass R.T p V *
      ∫ z, (releaseScore R.T p w V - outputScore Q p w z) ^ 2 ∂(R.K V)) = 0 := by
    simpa only [varianceGap] using
      ((fisher_gap_eq_variance Q r R p w hp hpsum).symm.trans hgap)
  have hterm_nonneg (V : RayIndex) :
      0 ≤ releaseMass R.T p V *
        ∫ z, (releaseScore R.T p w V - outputScore Q p w z) ^ 2 ∂(R.K V) := by
    apply mul_nonneg
    · unfold releaseMass
      apply Finset.sum_nonneg
      intro i _
      exact mul_nonneg (le_of_lt (hp i)) ENNReal.toReal_nonneg
    · exact integral_nonneg fun z => sq_nonneg _
  have hscore (V : RayIndex) (hV : 0 < releaseMass R.T p V) :
      ∀ᵐ z ∂(R.K V), outputScore Q p w z = releaseScore R.T p w V := by
    have hterm : releaseMass R.T p V *
        ∫ z, (releaseScore R.T p w V - outputScore Q p w z) ^ 2 ∂(R.K V) = 0 :=
      ((Finset.sum_eq_zero_iff_of_nonneg
        (fun V _ => hterm_nonneg V)).mp hvar) V (Finset.mem_univ V)
    have hint : (∫ z, (releaseScore R.T p w V - outputScore Q p w z) ^ 2
        ∂(R.K V)) = 0 :=
      (mul_eq_zero.mp hterm).resolve_left (ne_of_gt hV)
    letI : IsMarkovKernel R.K := R.markovK
    have hscoreInt : Integrable (outputScore Q p w) (R.K V) :=
      outputScore_integrable Q p w (fun i => le_of_lt (hp i)) _
    have hscoreSqInt : Integrable (fun z => (outputScore Q p w z) ^ 2) (R.K V) :=
      outputScore_sq_integrable Q p w (fun i => le_of_lt (hp i)) _
    have hfi : Integrable
        (fun z => (releaseScore R.T p w V - outputScore Q p w z) ^ 2)
        (R.K V) := by
      have hfun : (fun z => (releaseScore R.T p w V - outputScore Q p w z) ^ 2) =
          (fun z => (releaseScore R.T p w V) ^ 2 -
            (2 * releaseScore R.T p w V) * outputScore Q p w z +
            (outputScore Q p w z) ^ 2) := by
        funext z
        ring
      rw [hfun]
      exact ((integrable_const _).sub (hscoreInt.const_mul _)).add hscoreSqInt
    have hae := (integral_eq_zero_iff_of_nonneg (fun z => sq_nonneg _) hfi).mp hint
    filter_upwards [hae] with z hz
    have hz' : (releaseScore R.T p w V - outputScore Q p w z) ^ 2 = 0 := by
      simpa only [Pi.zero_apply] using hz
    have hz0 : releaseScore R.T p w V - outputScore Q p w z = 0 :=
      (mul_self_eq_zero.mp (by simpa only [pow_two] using hz'))
    linarith
  have hm : Measurable (outputScore Q p w) := by
    unfold outputScore rowDensity
    fun_prop
  let s : Set Z := {z | outputScore Q p w z ≠ releaseScore R.T p w S}
  refine ⟨s, ?_, ?_, ?_⟩
  · exact (measurableSet_eq_fun hm measurable_const).compl
  · have h := ae_iff.mp (hscore S hS)
    simpa only [s, Set.compl_setOf, not_not] using h
  · have h : ∀ᵐ z ∂(R.K U),
        outputScore Q p w z ≠ releaseScore R.T p w S := by
      filter_upwards [hscore U hU] with z hz
      intro heq
      exact hdiff (heq.symm.trans hz)
    have h0 := ae_iff.mp h
    simpa only [s, Set.compl_setOf, not_not] using h0

end Causalean.Stat.Privacy.Staircase
