module
public import Causalean.Stat.Minimax.Mixture.PoissonLatentSign.Pointwise
public import Causalean.Stat.Minimax.Mixture.PoissonLatentSign.PoissonMoments
public import Causalean.Stat.Minimax.Mixture.PoissonLatentSign.Series

/-!
# Poisson-averaged posterior subset coefficients

An arbitrary probability law of scores, assignments, and selection is supplied
separately at each count. Only almost-everywhere score bounds and selection
within positive assignments are required; dependence within each cell is unrestricted.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section
namespace Causalean.Stat.Minimax.Mixture.PoissonLatentSign

/-- The conditional order-d energy averages squared coefficients at a fixed cell count. -/
def conditionalEnergy (ν : ∀ m, Measure (Cell m)) (τ : ℝ) (m d : ℕ) : ℝ :=
  ∫ c, subsetEnergy τ c d ∂ν m

/-- The Poisson coefficient is the averaged order-d energy times the even outcome amplitude power.
-/
def coefficient (ν : ∀ m, Measure (Cell m)) (ξ : NNReal) (τ γ : ℝ) (d : ℕ) : ℝ :=
  γ ^ (2 * d) * ∫ m : ℕ, conditionalEnergy ν τ m d ∂poissonMeasure ξ

/-- Every fixed-count subset energy is integrable under an arbitrary valid conditional cell law. -/
theorem integrable_subsetEnergy (ν : ∀ m, Measure (Cell m))
    [∀ m, IsProbabilityMeasure (ν m)] {τ : ℝ} (hτ : |τ| ≤ 1 / 4)
    (hν : ∀ m, ∀ᵐ c ∂ν m, Valid c) (m d : ℕ) :
    Integrable (fun c => subsetEnergy τ c d) (ν m) := by
  -- Dominate by 4^d * choose m d, using measurable_subsetEnergy.
  refine (integrable_const ((4 : ℝ) ^ d * (m.choose d : ℝ))).mono'
    (measurable_subsetEnergy m d τ).aestronglyMeasurable ?_
  filter_upwards [hν m] with c hc
  simpa only [Real.norm_eq_abs, abs_of_nonneg (subsetEnergy_nonneg τ c d)] using
    subsetEnergy_le_choose hτ hc.1 d

/-- Averaging the fixed-count bound preserves its binomial majorant. -/
private theorem conditionalEnergy_le_choose (ν : ∀ m, Measure (Cell m))
    [∀ m, IsProbabilityMeasure (ν m)] {τ : ℝ} (hτ : |τ| ≤ 1 / 4)
    (hν : ∀ m, ∀ᵐ c ∂ν m, Valid c) (m d : ℕ) :
    conditionalEnergy ν τ m d ≤ (4 : ℝ) ^ d * (m.choose d : ℝ) := by
  unfold conditionalEnergy
  calc
    _ ≤ ∫ _c : Cell m, (4 : ℝ) ^ d * (m.choose d : ℝ) ∂ν m := by
      apply integral_mono_ae (integrable_subsetEnergy ν hτ hν m d) (integrable_const _)
      filter_upwards [hν m] with c hc
      exact subsetEnergy_le_choose hτ hc.1 d
    _ = _ := by simp

/-- The conditional energy is integrable over the Poisson count law. -/
theorem integrable_conditionalEnergy (ν : ∀ m, Measure (Cell m))
    [∀ m, IsProbabilityMeasure (ν m)] (ξ : NNReal)
    {τ : ℝ} (hτ : |τ| ≤ 1 / 4) (hν : ∀ m, ∀ᵐ c ∂ν m, Valid c) (d : ℕ) :
    Integrable (fun m => conditionalEnergy ν τ m d) (poissonMeasure ξ) := by
  -- First bound each conditional integral between zero and 4^d * choose m d.
  -- Its measurability follows from the discrete Nat domain. Apply Integrable.mono'
  -- with (integrable_poisson_choose ξ d).const_mul (4^d).
  refine ((integrable_poisson_choose ξ d).const_mul ((4 : ℝ) ^ d)).mono'
    (measurable_of_countable _).aestronglyMeasurable ?_
  apply Filter.Eventually.of_forall
  intro m
  have hn : 0 ≤ conditionalEnergy ν τ m d :=
    integral_nonneg (fun c => subsetEnergy_nonneg τ c d)
  simpa only [Real.norm_eq_abs, abs_of_nonneg hn] using
    conditionalEnergy_le_choose ν hτ hν m d

/-- Every Poisson coefficient is nonnegative, for any real outcome amplitude. -/
theorem coefficient_nonneg (ν : ∀ m, Measure (Cell m)) (ξ : NNReal)
    (τ γ : ℝ) (d : ℕ) : 0 ≤ coefficient ν ξ τ γ d := by
  unfold coefficient conditionalEnergy
  apply mul_nonneg
  · rw [mul_comm 2 d, pow_mul]
    exact sq_nonneg _
  · exact integral_nonneg (fun _ => integral_nonneg (fun _ => subsetEnergy_nonneg _ _ _))

/-- Every order has the Poisson factorial bound, including the first order. -/
theorem coefficient_le_factorial (ν : ∀ m, Measure (Cell m))
    [∀ m, IsProbabilityMeasure (ν m)] (ξ : NNReal) {τ : ℝ}
    (hτ : |τ| ≤ 1 / 4) (hν : ∀ m, ∀ᵐ c ∂ν m, Valid c) (γ : ℝ) (d : ℕ) :
    coefficient ν ξ τ γ d ≤ (4 * (ξ : ℝ) * γ ^ 2) ^ d / (d.factorial : ℝ) := by
  -- Apply integral_mono_ae at each conditional law and then at poissonMeasure ξ.
  -- Use the two integrability receipts above and integral_poisson_choose.
  -- Normalize γ^(2*d)=(γ^2)^d only after multiplying the nonnegative bound.
  have hb : (∫ m : ℕ, conditionalEnergy ν τ m d ∂poissonMeasure ξ) ≤
      (4 : ℝ) ^ d * ((ξ : ℝ) ^ d / (d.factorial : ℝ)) := by
    calc
      _ ≤ ∫ m : ℕ, (4 : ℝ) ^ d * (m.choose d : ℝ) ∂poissonMeasure ξ :=
        integral_mono_ae (integrable_conditionalEnergy ν ξ hτ hν d)
          ((integrable_poisson_choose ξ d).const_mul _) <|
          Filter.Eventually.of_forall (fun m => conditionalEnergy_le_choose ν hτ hν m d)
      _ = _ := by rw [integral_const_mul, integral_poisson_choose]
  have hg : 0 ≤ γ ^ (2 * d) := by
    rw [pow_mul]
    positivity
  unfold coefficient
  calc
    _ ≤ γ ^ (2 * d) * ((4 : ℝ) ^ d * ((ξ : ℝ) ^ d / (d.factorial : ℝ))) :=
      mul_le_mul_of_nonneg_left hb hg
    _ = _ := by rw [pow_mul, mul_pow, mul_pow]; ring

/-- Given [conditional probability laws for cells](hyp:ν), [a Poisson mean at most
one](hyp:hξ), [a bounded tilt](hyp:hτ), [almost-surely valid cells](hyp:hν), and
[an outcome amplitude](hyp:γ), [the singleton Poisson coefficient has the explicit
mean-squared, tilt-squared collision bound](goal). -/
theorem coefficient_one_le (ν : ∀ m, Measure (Cell m))
    [∀ m, IsProbabilityMeasure (ν m)] {ξ : NNReal} (hξ : (ξ : ℝ) ≤ 1)
    {τ : ℝ} (hτ : |τ| ≤ 1 / 4) (hν : ∀ m, ∀ᵐ c ∂ν m, Valid c) (γ : ℝ) :
    coefficient ν ξ τ γ 1 ≤
      (Real.exp ((5 / 3 : ℝ) ^ 2 - 1) *
        ((5 / 3 : ℝ) ^ 6 + (5 / 3 : ℝ) ^ 4)) * (ξ : ℝ) ^ 2 * τ ^ 2 * γ ^ 2 := by
  -- Integrate subsetEnergy_one_bound twice. The majorant is τ² times the
  -- collision tilt; integrable_poisson_collision_tilt supplies its receipt,
  -- and integral_poisson_collision_le supplies the explicit constant.
  let f : ℕ → ℝ := fun m => (m : ℝ) * ((m - 1 : ℕ) : ℝ) ^ 2 *
    ((5 / 3 : ℝ) ^ 2) ^ m
  have hf : Integrable f (poissonMeasure ξ) :=
    integrable_poisson_collision_tilt ξ (by positivity)
  have hb (m : ℕ) : conditionalEnergy ν τ m 1 ≤ τ ^ 2 * f m := by
    unfold conditionalEnergy
    calc
      _ ≤ ∫ _c : Cell m, τ ^ 2 * f m ∂ν m := by
        apply integral_mono_ae (integrable_subsetEnergy ν hτ hν m 1) (integrable_const _)
        filter_upwards [hν m] with c hc
        simpa only [f, mul_assoc] using subsetEnergy_one_bound hτ hc
      _ = _ := by simp
  have hi : (∫ m : ℕ, conditionalEnergy ν τ m 1 ∂poissonMeasure ξ) ≤
      τ ^ 2 * (∫ m : ℕ, f m ∂poissonMeasure ξ) := by
    calc
      _ ≤ ∫ m : ℕ, τ ^ 2 * f m ∂poissonMeasure ξ :=
        integral_mono_ae (integrable_conditionalEnergy ν ξ hτ hν 1)
          (hf.const_mul _) (Filter.Eventually.of_forall hb)
      _ = _ := integral_const_mul _ _
  have hj := mul_le_mul_of_nonneg_left
    (integral_poisson_collision_le hξ) (sq_nonneg τ)
  have hk := mul_le_mul_of_nonneg_left (hi.trans hj) (sq_nonneg γ)
  simpa only [coefficient, mul_one, one_mul, mul_assoc, mul_comm, mul_left_comm] using hk

/-- All positive-order Poisson coefficient terms are absolutely summable at any real overlap. -/
theorem coefficient_summable_abs (ν : ∀ m, Measure (Cell m))
    [∀ m, IsProbabilityMeasure (ν m)] (ξ : NNReal) {τ : ℝ}
    (hτ : |τ| ≤ 1 / 4) (hν : ∀ m, ∀ᵐ c ∂ν m, Valid c) (γ z : ℝ) :
    Summable (fun d : ℕ => |coefficient ν ξ τ γ (d + 1) * z ^ (d + 1)|) := by
  exact overlapSeries_summable_abs (b := 4 * (ξ : ℝ) * γ ^ 2) (by positivity)
    (fun d _ => ⟨coefficient_nonneg ν ξ τ γ d,
      coefficient_le_factorial ν ξ hτ hν γ d⟩) z

/-- The positive-order overlap terms have summable Poisson expectations of their
conditional absolute magnitudes, providing the interchange receipt. -/
theorem summable_integral_abs_energy_terms (ν : ∀ m, Measure (Cell m))
    [∀ m, IsProbabilityMeasure (ν m)] (ξ : NNReal) {τ : ℝ}
    (hτ : |τ| ≤ 1 / 4) (hν : ∀ m, ∀ᵐ c ∂ν m, Valid c) (γ z : ℝ) :
    Summable (fun d : ℕ => ∫ m : ℕ,
      ∫ c, |γ ^ (2 * (d + 1)) * subsetEnergy τ c (d + 1) * z ^ (d + 1)|
        ∂ν m ∂poissonMeasure ξ) := by
  -- Nonnegative energy gives |γ^(2*d)*energy*z^d| = γ^(2*d)*energy*|z|^d.
  -- Pull constants through both integrals to identify the summand with
  -- |coefficient ν ξ τ γ (d+1) * z^(d+1)|; use coefficient_summable_abs.
  apply (coefficient_summable_abs ν ξ hτ hν γ z).congr
  intro d
  have hg : 0 ≤ γ ^ (2 * (d + 1)) := by rw [pow_mul]; positivity
  have hc (m : ℕ) := integrable_subsetEnergy ν hτ hν m (d + 1)
  have hm := integrable_conditionalEnergy ν ξ hτ hν (d + 1)
  have he (m : ℕ) :
      (∫ c, |γ ^ (2 * (d + 1)) * subsetEnergy τ c (d + 1) * z ^ (d + 1)| ∂ν m) =
        |z| ^ (d + 1) * (γ ^ (2 * (d + 1)) * conditionalEnergy ν τ m (d + 1)) := by
    simp_rw [abs_mul, abs_of_nonneg hg,
      abs_of_nonneg (subsetEnergy_nonneg τ _ _), abs_pow]
    calc
      _ = ∫ c, |z| ^ (d + 1) •
          (γ ^ (2 * (d + 1)) • subsetEnergy τ c (d + 1)) ∂ν m := by
        congr 1
        funext c
        simp only [smul_eq_mul]
        ring
      _ = _ := by
        have hγ := (hc m).integral_smul (γ ^ (2 * (d + 1)))
        have hz := ((hc m).const_mul (γ ^ (2 * (d + 1)))).integral_smul
          (|z| ^ (d + 1))
        simp only [smul_eq_mul] at hγ hz ⊢
        rw [hz, hγ]
        rfl
  simp_rw [he]
  have hz := (hm.const_mul (γ ^ (2 * (d + 1)))).integral_smul (|z| ^ (d + 1))
  have hγ := hm.integral_smul (γ ^ (2 * (d + 1)))
  simp only [smul_eq_mul] at hz hγ
  rw [hz]
  change |coefficient ν ξ τ γ (d + 1) * z ^ (d + 1)| = _
  rw [abs_mul, abs_of_nonneg (coefficient_nonneg ν ξ τ γ (d + 1)), abs_pow]
  unfold coefficient
  rw [hγ]
  ring

/-- The Poisson cell overlap is positive throughout the small-radius regime. -/
theorem poisson_overlap_pos (ν : ∀ m, Measure (Cell m))
    [∀ m, IsProbabilityMeasure (ν m)] (ξ : NNReal) {τ γ z : ℝ}
    (hτ : |τ| ≤ 1 / 4) (hν : ∀ m, ∀ᵐ c ∂ν m, Valid c)
    (hr : 4 * (ξ : ℝ) * γ ^ 2 * |z| ≤ 1 / 2) :
    0 < overlapSeries (coefficient ν ξ τ γ) z := by
  exact overlapSeries_pos (b := 4 * (ξ : ℝ) * γ ^ 2) (by positivity)
    (fun d _ => ⟨coefficient_nonneg ν ξ τ γ d,
      coefficient_le_factorial ν ξ hτ hν γ d⟩) hr

/-- Given [conditional probability laws for cells](hyp:ν), [a Poisson mean](hyp:ξ),
[a bounded tilt](hyp:hτ), [almost-surely valid cells](hyp:hν), [a small overlap
radius](hyp:hr), and [a natural power](hyp:k), [the Poisson overlap power has an
exponential envelope with its exact singleton coefficient](goal). -/
theorem poisson_overlap_pow_le_exp (ν : ∀ m, Measure (Cell m))
    [∀ m, IsProbabilityMeasure (ν m)] (ξ : NNReal) {τ γ z : ℝ}
    (hτ : |τ| ≤ 1 / 4) (hν : ∀ m, ∀ᵐ c ∂ν m, Valid c)
    (hr : 4 * (ξ : ℝ) * γ ^ 2 * |z| ≤ 1 / 2) (k : ℕ) :
    overlapSeries (coefficient ν ξ τ γ) z ^ k ≤
      Real.exp (((k : ℝ) * coefficient ν ξ τ γ 1) * z +
        16 * (k : ℝ) * (ξ : ℝ) ^ 2 * γ ^ 4 * z ^ 2) := by
  -- Specialize overlapSeries_pow_le_exp with b=4ξγ². No sign assumption on z.
  have h := overlapSeries_pow_le_exp (b := 4 * (ξ : ℝ) * γ ^ 2)
    (by positivity) (fun d _ => ⟨coefficient_nonneg ν ξ τ γ d,
      coefficient_le_factorial ν ξ hτ hν γ d⟩) hr k
  convert h using 1
  congr 1
  ring

end Causalean.Stat.Minimax.Mixture.PoissonLatentSign
