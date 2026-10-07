module
public import Causalean.Stat.Concentration.Poisson.FactorialEnvelope
public import Mathlib.Probability.Independence.Integration

/-!
# Factorial products of finitely many independent Poisson coordinates

The scalar identities are transported to random counts with Poisson laws and multiplied across
independent coordinates. The four-coordinate bound isolates the paper's exponential degree cost.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Causalean.Stat.Concentration.Poisson

/-- For [a finite family of count coordinates](hyp:W), [a normalization](hyp:m), [a center and an order for each coordinate](hyp:z,h), and [a sample point](hyp:ω), [the factorial product](goal) is the product over coordinates of the centered factorial lift of that coordinate's count at the sample point, with that coordinate's center and order.

The product of normalized centered factorial lifts over a finite coordinate set.
-/
def factorialProduct {ι Ω : Type*} [Fintype ι] (W : ι → Ω → ℕ)
    (m : ℝ) (z : ι → ℝ) (h : ι → ℕ) (ω : Ω) : ℝ :=
  ∏ i, factorialLift m (z i) (W i ω) (h i)

/-- Independent Poisson coordinates make the expectation of a finite factorial product equal the
product of coordinatewise powers of the mean minus the center.

Use `iIndepFun.integral_fun_prod_comp` with measurable coordinate lifts, transport each
one-coordinate integral through `HasLaw`, and apply `poisson_factorialLift_mean`.
-/
theorem factorialProduct_mean {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : ι → Ω → ℕ)
    (rate : ι → NNReal) (hWlaw : ∀ i, HasLaw (W i) (poissonMeasure (rate i)) μ)
    (hWindep : iIndepFun W μ) (m : ℝ)
    (z : ι → ℝ) (h : ι → ℕ) :
    (∫ ω, factorialProduct W m z h ω ∂μ) =
      ∏ i, ((rate i : ℝ) / m - z i) ^ (h i) := by
  change (∫ ω, ∏ i, factorialLift m (z i) (W i ω) (h i) ∂μ) = _
  rw [hWindep.integral_fun_prod_comp
    (fun i => (hWlaw i).aemeasurable)
    (fun i => (Measurable.of_discrete : Measurable
      (fun N : ℕ => factorialLift m (z i) N (h i))).aestronglyMeasurable)]
  apply Finset.prod_congr rfl
  intro i _
  rw [show (∫ ω, factorialLift m (z i) (W i ω) (h i) ∂μ) =
    ∫ N : ℕ, factorialLift m (z i) N (h i) ∂poissonMeasure (rate i) from by
      simpa only [Function.comp_apply] using
        (hWlaw i).integral_comp (f := fun N : ℕ => factorialLift m (z i) N (h i))
          Measurable.of_discrete.aestronglyMeasurable]
  exact poisson_factorialLift_mean (rate i) m (z i) (h i)

/-- Under independent Poisson coordinates, the normalized product's square moment is at most
the exponential of the sum of coordinatewise squared degrees divided by `L`.

Factor the second moment by `iIndepFun.integral_fun_prod_comp`, use the scalar square envelope
on each coordinate, then combine the finite exponential product.
-/
theorem factorialProduct_square_envelope
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : ι → Ω → ℕ)
    (rate : ι → NNReal) (hWlaw : ∀ i, HasLaw (W i) (poissonMeasure (rate i)) μ)
    (hWindep : iIndepFun W μ) (m L : ℝ) (hm : 0 < m) (hL : 0 < L)
    (z R : ι → ℝ) (hR : ∀ i, 0 < R i)
    (hcenter : ∀ i, |(rate i : ℝ) / m - z i| ≤ R i)
    (hvariance : ∀ i, (rate i : ℝ) / (m ^ 2 * (R i) ^ 2) ≤ 1 / L)
    (h : ι → ℕ) :
    (∫ ω, (factorialProduct W m z h ω /
      ∏ i, (R i) ^ (h i)) ^ 2 ∂μ) ≤
      Real.exp ((∑ i, ((h i : ℝ) ^ 2)) / L) := by
  have hfactor :
      (∫ ω, (factorialProduct W m z h ω / ∏ i, R i ^ h i) ^ 2 ∂μ) =
        ∏ i, ∫ ω, (factorialLift m (z i) (W i ω) (h i) / R i ^ h i) ^ 2 ∂μ := by
    have hp (ω : Ω) :
        (factorialProduct W m z h ω / ∏ i, R i ^ h i) ^ 2 =
          ∏ i, (factorialLift m (z i) (W i ω) (h i) / R i ^ h i) ^ 2 := by
      simp only [factorialProduct, ← Finset.prod_div_distrib, ← Finset.prod_pow]
    simp_rw [hp]
    exact hWindep.integral_fun_prod_comp
      (fun i => (hWlaw i).aemeasurable)
      (fun i => (Measurable.of_discrete : Measurable
        (fun N : ℕ => (factorialLift m (z i) N (h i) / R i ^ h i) ^ 2)).aestronglyMeasurable)
  rw [hfactor]
  calc
    (∏ i, ∫ ω, (factorialLift m (z i) (W i ω) (h i) / R i ^ h i) ^ 2 ∂μ) ≤
        ∏ i, Real.exp ((h i : ℝ) ^ 2 / L) := by
      apply Finset.prod_le_prod
      · intro i _
        exact integral_nonneg (fun ω => sq_nonneg _)
      · intro i _
        rw [show (∫ ω, (factorialLift m (z i) (W i ω) (h i) / R i ^ h i) ^ 2 ∂μ) =
          ∫ N : ℕ, (factorialLift m (z i) N (h i) / R i ^ h i) ^ 2
            ∂poissonMeasure (rate i) from by
              simpa only [Function.comp_apply] using
                (hWlaw i).integral_comp
                  (f := fun N : ℕ => (factorialLift m (z i) N (h i) / R i ^ h i) ^ 2)
                  Measurable.of_discrete.aestronglyMeasurable]
        exact poisson_factorialLift_square_envelope (rate i) m (z i) (R i) L
          hm (hR i) hL (hcenter i) (hvariance i) (h i)
    _ = Real.exp ((∑ i, (h i : ℝ) ^ 2) / L) := by
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.sum_div]

/-- Under [a probability measure, take four count coordinates](hyp:μ,W) with [given rates](hyp:rate) that [have Poisson laws of those rates and are mutually independent](hyp:hWlaw,hWindep), [a positive normalization m and a positive scale L](hyp:m,L,hm,hL), and [centers and positive radii](hyp:z,R,hR) such that [each normalized mean rate/m is within its radius of its center and each rate/(m² R²) is at most 1/L](hyp:hcenter,hvariance). For [orders, one per coordinate, each at most D](hyp:h,D,hdegree), [the expected square of the factorial product divided by the product of the radii raised to the orders is at most exp(4D²/L)](goal).

For four Poisson coordinates and every degree at most `D`, the normalized factorial product
has square moment at most `exp(4D²/L)`.
-/
theorem factorialProduct_four_square_envelope
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : Fin 4 → Ω → ℕ)
    (rate : Fin 4 → NNReal)
    (hWlaw : ∀ i, HasLaw (W i) (poissonMeasure (rate i)) μ)
    (hWindep : iIndepFun W μ) (m L : ℝ) (hm : 0 < m) (hL : 0 < L)
    (z R : Fin 4 → ℝ) (hR : ∀ i, 0 < R i)
    (hcenter : ∀ i, |(rate i : ℝ) / m - z i| ≤ R i)
    (hvariance : ∀ i, (rate i : ℝ) / (m ^ 2 * (R i) ^ 2) ≤ 1 / L)
    (h : Fin 4 → ℕ) (D : ℕ) (hdegree : ∀ i, h i ≤ D) :
    (∫ ω, (factorialProduct W m z h ω /
      ∏ i, (R i) ^ (h i)) ^ 2 ∂μ) ≤
      Real.exp (4 * (D : ℝ) ^ 2 / L) := by
  have hs : (∑ i : Fin 4, (h i : ℝ) ^ 2) ≤ 4 * (D : ℝ) ^ 2 := by
    calc
      (∑ i : Fin 4, (h i : ℝ) ^ 2) ≤ ∑ _i : Fin 4, (D : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have hi : (h i : ℝ) ≤ D := by exact_mod_cast hdegree i
        have hnonneg : 0 ≤ (h i : ℝ) := by positivity
        nlinarith
      _ = 4 * (D : ℝ) ^ 2 := by norm_num
  exact (factorialProduct_square_envelope μ W rate hWlaw hWindep m L hm hL
    z R hR hcenter hvariance h).trans
    (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hs (le_of_lt hL)))

end Causalean.Stat.Concentration.Poisson
