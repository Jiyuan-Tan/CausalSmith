module
public import Causalean.Stat.Privacy.Staircase.Basic

/-!
# Dominating measure and private row densities

The sum of the four output laws dominates every row. Radon–Nikodym reconstruction and
setwise privacy transfer the privacy inequalities to their measurable real densities.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

noncomputable section

namespace Causalean.Stat.Privacy.Staircase

variable {Z : Type*} [MeasurableSpace Z]

/-- Setwise local privacy bounds every row measure by `r` times every other row measure. -/
def SetwisePrivate (Q : Kernel (Fin 4) Z) (r : ℝ) : Prop :=
  ∀ i j s, MeasurableSet s → Q i s ≤ ENNReal.ofReal r * Q j s

/-- The sum of the four row measures is a finite common dominating measure. -/
def rowSum (Q : Kernel (Fin 4) Z) : Measure Z :=
  ∑ i : Fin 4, Q i

/-- The real Radon–Nikodym density of one row relative to the row sum. -/
def rowDensity (Q : Kernel (Fin 4) Z) (i : Fin 4) (z : Z) : ℝ :=
  ((Q i).rnDeriv (rowSum Q) z).toReal

/-- The common dominating measure has finite total mass for a Markov kernel. -/
theorem rowSum_finite (Q : Kernel (Fin 4) Z) [IsMarkovKernel Q] :
    IsFiniteMeasure (rowSum Q) := by
  unfold rowSum
  infer_instance

/-- Each row is absolutely continuous with respect to the sum of all rows. -/
theorem row_absolutelyContinuous (Q : Kernel (Fin 4) Z) (i : Fin 4) :
    Q i ≪ rowSum Q := by
  unfold rowSum
  rw [← Measure.sum_fintype]
  exact Measure.absolutelyContinuous_sum_right i (Measure.absolutelyContinuous_refl _)

/-- The Radon–Nikodym density reconstructs each Markov row exactly. -/
theorem row_eq_withDensity (Q : Kernel (Fin 4) Z) [IsMarkovKernel Q] (i : Fin 4) :
    Q i = (rowSum Q).withDensity (fun z => ENNReal.ofReal (rowDensity Q i z)) := by
  haveI : IsFiniteMeasure (rowSum Q) := rowSum_finite Q
  haveI : IsFiniteMeasure (Q i) := inferInstance
  have h : ∀ᵐ z ∂rowSum Q, (Q i).rnDeriv (rowSum Q) z ≠ ⊤ :=
    (Q i).rnDeriv_ne_top (rowSum Q)
  have heq : (fun z => ENNReal.ofReal (rowDensity Q i z)) =ᵐ[rowSum Q]
      (Q i).rnDeriv (rowSum Q) := by
    filter_upwards [h] with z hz
    simp only [rowDensity, ENNReal.ofReal_toReal hz]
  rw [← Measure.withDensity_rnDeriv_eq (Q i) (rowSum Q)
    (row_absolutelyContinuous Q i)]
  exact withDensity_congr_ae heq.symm

/-- The four real row densities satisfy the finite privacy cone almost everywhere. -/
theorem ae_privateCone (Q : Kernel (Fin 4) Z) [IsMarkovKernel Q]
    (r : ℝ) (hr : 1 < r) (hpriv : SetwisePrivate Q r) :
    ∀ᵐ z ∂rowSum Q, PrivateCone r (fun i => rowDensity Q i z) := by
  haveI : IsFiniteMeasure (rowSum Q) := rowSum_finite Q
  have hpair (i j : Fin 4) :
      ∀ᵐ z ∂rowSum Q, rowDensity Q i z ≤ r * rowDensity Q j z := by
    have hle : (Q i).rnDeriv (rowSum Q) ≤ᵐ[rowSum Q]
        fun z => ENNReal.ofReal r * (Q j).rnDeriv (rowSum Q) z := by
      apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite
        ((Q i).measurable_rnDeriv (rowSum Q))
      intro s hs _
      rw [lintegral_const_mul _ ((Q j).measurable_rnDeriv (rowSum Q))]
      have hi := Measure.withDensity_rnDeriv_eq (Q i) (rowSum Q)
        (row_absolutelyContinuous Q i)
      have hj := Measure.withDensity_rnDeriv_eq (Q j) (rowSum Q)
        (row_absolutelyContinuous Q j)
      rw [← withDensity_apply ((Q i).rnDeriv (rowSum Q)) hs, hi,
        ← withDensity_apply ((Q j).rnDeriv (rowSum Q)) hs, hj]
      exact hpriv i j s hs
    filter_upwards [hle, (Q j).rnDeriv_ne_top (rowSum Q)] with z hz hzj
    rw [← ENNReal.ofReal_toReal hzj,
      ← ENNReal.ofReal_mul (by linarith : 0 ≤ r)] at hz
    exact ENNReal.toReal_le_of_le_ofReal
      (mul_nonneg (by linarith) ENNReal.toReal_nonneg) hz
  have hpair_all : ∀ᵐ z ∂rowSum Q,
      ∀ i j : Fin 4, rowDensity Q i z ≤ r * rowDensity Q j z := by
    rw [ae_all_iff]
    intro i
    rw [ae_all_iff]
    exact hpair i
  filter_upwards [hpair_all] with z hz
  exact ⟨fun i => ENNReal.toReal_nonneg, hz⟩

/-- For [a four-input Markov kernel](hyp:Q), [a privacy ratio greater than one](hyp:hr) at
[the supplied ratio](hyp:r), and [setwise local privacy](hyp:hpriv), a [measurable
nonnegative coefficient field that decomposes all four row densities](goal) exists under their
common dominating measure.

A measurable nonnegative coefficient field decomposes all four row densities
simultaneously almost everywhere under the common dominating measure. -/
theorem measurable_density_decomposition (Q : Kernel (Fin 4) Z) [IsMarkovKernel Q]
    (r : ℝ) (hr : 1 < r) (hpriv : SetwisePrivate Q r) :
    ∃ c : Z → RayIndex → ℝ,
      (∀ S, Measurable fun z => c z S) ∧
      (∀ z S, 0 ≤ c z S) ∧
      ∀ᵐ z ∂rowSum Q, ∀ i, rowDensity Q i z = ∑ S, c z S * ray r S i := by
  let c : Z → RayIndex → ℝ := fun z S =>
    max 0 (coneRayCoeff r (fun i => rowDensity Q i z) S)
  have hdensity : Measurable (fun z => fun i : Fin 4 => rowDensity Q i z) := by
    rw [measurable_pi_iff]
    intro i
    exact ((Q i).measurable_rnDeriv (rowSum Q)).ennreal_toReal
  refine ⟨c, ?_, ?_, ?_⟩
  · intro S
    exact measurable_const.max ((measurable_coneRayCoeff r S).comp hdensity)
  · intro z S
    exact le_max_left _ _
  · filter_upwards [ae_privateCone Q r hr hpriv] with z hz
    have hcoeff := (coneRayCoeff_decomposition r hr
      (fun i => rowDensity Q i z) hz)
    intro i
    calc
      rowDensity Q i z = ∑ S, coneRayCoeff r (fun j => rowDensity Q j z) S *
          ray r S i := hcoeff.2 i
      _ = ∑ S, c z S * ray r S i := by
        apply Finset.sum_congr rfl
        intro S _
        simp only [c, max_eq_right (hcoeff.1 S)]

end Causalean.Stat.Privacy.Staircase
