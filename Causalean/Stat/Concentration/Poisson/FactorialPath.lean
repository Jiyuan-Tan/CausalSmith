module
public import Causalean.Stat.Concentration.BoundedVariation.ClippedPolynomial
public import Causalean.Stat.Concentration.Poisson.FactorialProduct
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# Four-coordinate clipped Poisson factorial paths

This module instantiates finite clipped-polynomial path estimates with four independent Poisson
counts and normalized centered falling-factorial monomials of bounded coordinatewise degree.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open Causalean.Stat.Concentration.BoundedVariation
open scoped BigOperators

namespace Causalean.Stat.Concentration.Poisson

/-- For [four count coordinates](hyp:W), [a normalization](hyp:m), [centers and radii](hyp:z,R), [a multi-degree with one degree per coordinate](hyp:a), and [a sample point](hyp:ω), [the normalized four-coordinate factorial monomial](goal) is the product over the four coordinates of the centered factorial lift of that coordinate's count, of the coordinate's degree and with the coordinate's center, divided by the product of the radii raised to those degrees.

The four-coordinate normalized centered factorial monomial indexed by a fixed tensor
multi-degree.
-/
def fourFactorialMonomial {Ω : Type*} {D : ℕ}
    (W : Fin 4 → Ω → ℕ) (m : ℝ) (z R : Fin 4 → ℝ)
    (a : Fin 4 → Fin (D + 1)) (ω : Ω) : ℝ :=
  factorialProduct W m z (fun i => (a i : ℕ)) ω /
    ∏ i, (R i) ^ (a i : ℕ)

/-- For [coefficient paths indexed by multi-degrees](hyp:c), [four count coordinates](hyp:W), [a normalization](hyp:m), [centers and radii](hyp:z,R), [a clipping radius](hyp:cap), and [a sample point](hyp:ω), [the clipped four-coordinate factorial path](goal) is the continuous path whose value at each time is the sum over multi-degrees of the normalized factorial monomial at the sample point times the coefficient path at that time, clipped to the symmetric interval of the clipping radius.

The clipped polynomial path in four independent Poisson factorial coordinates. Its finite
coefficient family is a path indexed by the fixed tensor monomial basis.
-/
def fourPoissonFactorialPath {Ω : Type*} {D : ℕ}
    (c : (Fin 4 → Fin (D + 1)) → Path)
    (W : Fin 4 → Ω → ℕ) (m : ℝ) (z R : Fin 4 → ℝ)
    (cap : ℝ) (ω : Ω) : Path :=
  clippedFinitePath c (fun ω a => fourFactorialMonomial W m z R a ω) cap ω

/-- Under [a probability measure](hyp:μ), take [coefficient paths of bounded variation, indexed by multi-degrees with each degree at most D](hyp:c,hcBV), [four measurable, mutually independent counts with Poisson laws of given rates](hyp:W,rate,hWmeas,hWlaw,hWindep), [a positive normalization m and a positive scale L](hyp:m,L,hm,hL), [centers and positive radii](hyp:z,R,hR) such that [each normalized mean rate/m is within its radius of its center and each rate/(m² R²) is at most 1/L](hyp:hcenter,hvariance), and [a nonnegative clipping radius](hyp:cap,hcap). Then [the clipped four-coordinate factorial path is a measurable random path, has bounded variation at every sample point, is Bochner-integrable, has integrable squared supremum-plus-variation size, and its expected squared size is at most the sum of the squared sizes of the coefficient paths times (D + 1)^4 exp(4D²/L)](goal).

Four independent Poisson counts yield a measurable, bounded-variation clipped factorial
polynomial path whose squared path size is integrable and bounded by the coefficient path-size
square sum times the exponential degree envelope. Bounded variation of the coefficient paths is
necessary; continuity alone does not imply bounded variation.

Use `factorialProduct_four_square_envelope` for each normalized monomial, then
`clippedFinitePath_sq_integral_le` for the path-size estimate. The same measurable monomial
functions yield path measurability; `clippedFinitePath_bv` yields samplewise variation. Square
integrability of `pathSize` implies integrability of the path norm.
-/
theorem fourPoissonFactorialPath_sq_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {D : ℕ} (c : (Fin 4 → Fin (D + 1)) → Path)
    (hcBV : ∀ a, eVariationOn (c a) Set.univ < ⊤)
    (W : Fin 4 → Ω → ℕ) (rate : Fin 4 → NNReal)
    (hWmeas : ∀ i, Measurable (W i))
    (hWlaw : ∀ i, HasLaw (W i) (poissonMeasure (rate i)) μ)
    (hWindep : iIndepFun W μ) (m L : ℝ) (hm : 0 < m) (hL : 0 < L)
    (z R : Fin 4 → ℝ) (hR : ∀ i, 0 < R i)
    (hcenter : ∀ i, |(rate i : ℝ) / m - z i| ≤ R i)
    (hvariance : ∀ i, (rate i : ℝ) / (m ^ 2 * (R i) ^ 2) ≤ 1 / L)
    (cap : ℝ) (hcap : 0 ≤ cap) :
    Measurable (fourPoissonFactorialPath c W m z R cap) ∧
      (∀ ω, eVariationOn (fourPoissonFactorialPath c W m z R cap ω)
        Set.univ < ⊤) ∧
      Integrable (fourPoissonFactorialPath c W m z R cap) μ ∧
      Integrable (fun ω => (pathSize (fourPoissonFactorialPath c W m z R cap ω)) ^ 2)
        μ ∧
      (∫ ω, (pathSize (fourPoissonFactorialPath c W m z R cap ω)) ^ 2 ∂μ) ≤
        (∑ a, (pathSize (c a)) ^ 2) *
          ∑ _a : Fin 4 → Fin (D + 1), Real.exp (4 * (D : ℝ) ^ 2 / L) := by
  let X (ω : Ω) (a : Fin 4 → Fin (D + 1)) : ℝ :=
    fourFactorialMonomial W m z R a ω
  have hXmeas (a : Fin 4 → Fin (D + 1)) : Measurable (fun ω => X ω a) := by
    dsimp [X, fourFactorialMonomial, factorialProduct]
    apply Measurable.div_const
    apply Finset.measurable_prod
    intro i _
    exact (Measurable.of_discrete : Measurable
      (fun N : ℕ => factorialLift m (z i) N (a i : ℕ))).comp (hWmeas i)
  have hraw (r : NNReal) (j k : ℕ) :
      Integrable (fun N : ℕ => (N.descFactorial j : ℝ) *
        (N.descFactorial k : ℝ)) (poissonMeasure r) := by
    have h := integrable_finsetSum (Finset.range (min j k + 1))
      (fun t _ => (poisson_descFactorial_integrable r (j + k - t)).const_mul
        ((j.choose t : ℝ) * (k.choose t : ℝ) * (Nat.factorial t : ℝ)))
    have heq : (fun N : ℕ => (N.descFactorial j : ℝ) *
        (N.descFactorial k : ℝ)) =
        (fun N : ℕ => ∑ t ∈ Finset.range (min j k + 1),
          (j.choose t : ℝ) * (k.choose t : ℝ) *
            (Nat.factorial t : ℝ) * (N.descFactorial (j + k - t) : ℝ)) := by
      funext N
      exact descFactorial_mul N j k
    rw [heq]
    exact h
  have hlift (r : NNReal) (j : ℕ) (v : ℝ) :
      Integrable (fun N : ℕ => (factorialLift m v N j) ^ 2) (poissonMeasure r) := by
    have h := integrable_finsetSum (Finset.range (j + 1)) (fun p _ =>
      integrable_finsetSum (Finset.range (j + 1)) (fun q _ =>
        (hraw r p q).const_mul
          (((j.choose p : ℝ) * (-v) ^ (j - p) / m ^ p) *
            ((j.choose q : ℝ) * (-v) ^ (j - q) / m ^ q))))
    have heq : (fun N : ℕ => (factorialLift m v N j) ^ 2) =
        (fun N : ℕ => ∑ p ∈ Finset.range (j + 1),
          ∑ q ∈ Finset.range (j + 1),
            (((j.choose p : ℝ) * (-v) ^ (j - p) / m ^ p) *
              ((j.choose q : ℝ) * (-v) ^ (j - q) / m ^ q)) *
                ((N.descFactorial p : ℝ) * (N.descFactorial q : ℝ))) := by
      funext N
      simp only [factorialLift, sq, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      ring
    rw [heq]
    exact h
  have hXsq (a : Fin 4 → Fin (D + 1)) :
      Integrable (fun ω => (X ω a) ^ 2) μ := by
    let f (i : Fin 4) (N : ℕ) : ℝ :=
      (factorialLift m (z i) N (a i : ℕ) / R i ^ (a i : ℕ)) ^ 2
    have hf (i : Fin 4) : Integrable (f i) (poissonMeasure (rate i)) := by
      simpa only [f, div_pow] using
        (hlift (rate i) (a i : ℕ) (z i)).div_const ((R i ^ (a i : ℕ)) ^ 2)
    have hpi : Integrable (fun v : Fin 4 → ℕ => ∏ i, f i (v i))
        (Measure.pi (fun i => poissonMeasure (rate i))) :=
      Integrable.fintype_prod hf
    have hmap : μ.map (fun ω i => W i ω) =
        Measure.pi (fun i => poissonMeasure (rate i)) := by
      rw [hWindep.map_fun_eq_pi_map (fun i => (hWmeas i).aemeasurable)]
      congr 1
      funext i
      exact (hWlaw i).map_eq
    have hcomp : Integrable (fun ω => ∏ i, f i (W i ω)) μ := by
      exact (hmap ▸ hpi).comp_measurable (measurable_pi_lambda _ hWmeas)
    convert hcomp using 1
    funext ω
    simp only [X, fourFactorialMonomial, factorialProduct, f,
      ← Finset.prod_div_distrib, ← Finset.prod_pow]
  have hmeas : Measurable (fourPoissonFactorialPath c W m z R cap) := by
    let : BorelSpace Path := ⟨rfl⟩
    exact measurable_clippedFinitePath c X hXmeas cap
  have hbv (ω : Ω) :
      eVariationOn (fourPoissonFactorialPath c W m z R cap ω) Set.univ < ⊤ := by
    exact clippedFinitePath_bv c X cap hcBV ω
  have hsq := clippedFinitePath_sq_integral_le μ c X cap hcap hcBV hXmeas hXsq
  have hsize_meas : Measurable (fun ω => pathSize
      (fourPoissonFactorialPath c W m z R cap ω)) := by
    let : BorelSpace Path := ⟨rfl⟩
    exact ((continuous_norm.measurable.comp hmeas).add
      (measurable_pathTV.comp hmeas))
  have hsize_int : Integrable (fun ω => pathSize
      (fourPoissonFactorialPath c W m z R cap ω)) μ := by
    apply MeasureTheory.MemLp.integrable (q := 2) (by norm_num)
    exact (MeasureTheory.memLp_two_iff_integrable_sq
      hsize_meas.aestronglyMeasurable).2 hsq.1
  have hpath_int : Integrable (fourPoissonFactorialPath c W m z R cap) μ := by
    let : BorelSpace Path := ⟨rfl⟩
    apply Integrable.mono' hsize_int hmeas.aestronglyMeasurable
    filter_upwards [] with ω
    change ‖fourPoissonFactorialPath c W m z R cap ω‖ ≤
      pathSize (fourPoissonFactorialPath c W m z R cap ω)
    unfold pathSize
    exact le_add_of_nonneg_right (pathTV_nonneg _)
  refine ⟨hmeas, hbv, hpath_int, hsq.1, ?_⟩
  calc
    (∫ ω, (pathSize (fourPoissonFactorialPath c W m z R cap ω)) ^ 2 ∂μ) ≤
        (∑ a, (pathSize (c a)) ^ 2) *
          ∑ a, (∫ ω, (X ω a) ^ 2 ∂μ) := hsq.2
    _ ≤ (∑ a, (pathSize (c a)) ^ 2) *
          ∑ _a : Fin 4 → Fin (D + 1), Real.exp (4 * (D : ℝ) ^ 2 / L) := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro a _
        exact factorialProduct_four_square_envelope μ W rate hWlaw hWindep
          m L hm hL z R hR hcenter hvariance (fun i => (a i : ℕ)) D
          (fun i => Nat.le_of_lt_succ (a i).isLt)
      · exact Finset.sum_nonneg (fun a _ => sq_nonneg _)

end Causalean.Stat.Concentration.Poisson

