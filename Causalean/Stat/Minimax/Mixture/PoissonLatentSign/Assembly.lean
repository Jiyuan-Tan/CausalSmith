module
public import Causalean.Stat.Minimax.Mixture.PoissonLatentSign.Averaging
public import Causalean.Stat.Minimax.Mixture.PoissonLatentSign.Outcome
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Poisson cell cross-moment assembly

Iterated conditional outcome, covariate, and Poisson-count integration gives
the overlap series. The finite polynomial and actual likelihood-product
interfaces both carry integrability receipts. No paper-local model is imported.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section
namespace Causalean.Stat.Minimax.Mixture.PoissonLatentSign

/-- The finite cell overlap polynomial is one plus the positive-order subset-energy terms. -/
def cellOverlap {m : ℕ} (τ γ z : ℝ) (c : Cell m) : ℝ :=
  1 + ∑ d ∈ Finset.range m, γ ^ (2 * (d + 1)) *
    subsetEnergy τ c (d + 1) * z ^ (d + 1)

/-- Subset energy vanishes at orders exceeding the number of records. -/
theorem subsetEnergy_eq_zero_of_lt {m d : ℕ} (τ : ℝ) (c : Cell m)
    (hd : m < d) : subsetEnergy τ c d = 0 := by
  have hc : (selected c).card ≤ m := by
    simpa using Finset.card_le_card (Finset.subset_univ (selected c))
  simp [subsetEnergy, Finset.powersetCard_eq_empty.mpr (lt_of_le_of_lt hc hd)]

/-- The finite overlap polynomial is integrable under each valid conditional cell law. -/
theorem integrable_cellOverlap (ν : ∀ m, Measure (Cell m))
    [∀ m, IsProbabilityMeasure (ν m)] {τ : ℝ} (hτ : |τ| ≤ 1 / 4)
    (hν : ∀ m, ∀ᵐ c ∂ν m, Valid c) (γ z : ℝ) (m : ℕ) :
    Integrable (fun c => cellOverlap τ γ z c) (ν m) := by
  unfold cellOverlap
  apply (integrable_const 1).add
  apply integrable_finsetSum
  intro d _
  exact ((integrable_subsetEnergy ν hτ hν m (d + 1)).const_mul
    (γ ^ (2 * (d + 1)))).mul_const (z ^ (d + 1))

/-- Integrating the finite polynomial gives the finite sum of conditional energies. -/
private theorem integral_cellOverlap_eq_sum (ν : ∀ m, Measure (Cell m))
    [∀ m, IsProbabilityMeasure (ν m)] {τ : ℝ} (hτ : |τ| ≤ 1 / 4)
    (hν : ∀ m, ∀ᵐ c ∂ν m, Valid c) (γ z : ℝ) (m : ℕ) :
    (∫ c, cellOverlap τ γ z c ∂ν m) =
      1 + ∑ d ∈ Finset.range m,
        γ ^ (2 * (d + 1)) * conditionalEnergy ν τ m (d + 1) * z ^ (d + 1) := by
  have hi (d : ℕ) := ((integrable_subsetEnergy ν hτ hν m (d + 1)).const_mul
    (γ ^ (2 * (d + 1)))).mul_const (z ^ (d + 1))
  unfold cellOverlap
  rw [integral_add (integrable_const 1)
    (integrable_finsetSum _ (fun d _ => hi d)), integral_finsetSum _ (fun d _ => hi d)]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro d _
  rw [integral_mul_const, integral_const_mul]
  rfl

/-- Terms above the count vanish, so the conditional polynomial is also an infinite sum. -/
private theorem integral_cellOverlap_eq_tsum (ν : ∀ m, Measure (Cell m))
    [∀ m, IsProbabilityMeasure (ν m)] {τ : ℝ} (hτ : |τ| ≤ 1 / 4)
    (hν : ∀ m, ∀ᵐ c ∂ν m, Valid c) (γ z : ℝ) (m : ℕ) :
    (∫ c, cellOverlap τ γ z c ∂ν m) =
      1 + ∑' d : ℕ,
        γ ^ (2 * (d + 1)) * conditionalEnergy ν τ m (d + 1) * z ^ (d + 1) := by
  rw [integral_cellOverlap_eq_sum ν hτ hν γ z m]
  congr 1
  symm
  apply tsum_eq_sum
  intro d hd
  have hmd : m < d + 1 := by
    simp only [Finset.mem_range] at hd
    omega
  simp [conditionalEnergy, subsetEnergy_eq_zero_of_lt τ _ hmd]

/-- The absolute conditional polynomial has the binomial exponential envelope. -/
private theorem norm_cellOverlap_le {m : ℕ} {τ : ℝ} (hτ : |τ| ≤ 1 / 4)
    (γ z : ℝ) (c : Cell m) (hc : Valid c) :
    ‖cellOverlap τ γ z c‖ ≤ (1 + 4 * γ ^ 2 * |z|) ^ m := by
  have ht (d : ℕ) :
      ‖γ ^ (2 * (d + 1)) * subsetEnergy τ c (d + 1) * z ^ (d + 1)‖ ≤
        (4 * γ ^ 2 * |z|) ^ (d + 1) * (m.choose (d + 1) : ℝ) := by
    rw [Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (by rw [pow_mul]; positivity : 0 ≤ γ ^ (2 * (d + 1))),
      abs_of_nonneg (subsetEnergy_nonneg τ c _), abs_pow]
    calc
      _ ≤ γ ^ (2 * (d + 1)) * ((4 : ℝ) ^ (d + 1) * (m.choose (d + 1) : ℝ)) *
          |z| ^ (d + 1) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left (subsetEnergy_le_choose hτ hc.1 _)
          (by rw [pow_mul]; positivity)
      _ = _ := by rw [pow_mul, mul_pow, mul_pow]; ring
  calc
    _ ≤ 1 + ∑ d ∈ Finset.range m,
        (4 * γ ^ 2 * |z|) ^ (d + 1) * (m.choose (d + 1) : ℝ) := by
      unfold cellOverlap
      calc
        _ ≤ ‖(1 : ℝ)‖ + ‖∑ d ∈ Finset.range m,
            γ ^ (2 * (d + 1)) * subsetEnergy τ c (d + 1) * z ^ (d + 1)‖ := norm_add_le _ _
        _ ≤ _ := by
          simp only [norm_one]
          exact add_le_add_right ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun d _ => ht d))) _
    _ = (1 + 4 * γ ^ 2 * |z|) ^ m := by
      have hb := add_pow (4 * γ ^ 2 * |z|) (1 : ℝ) m
      simp only [one_pow, mul_one] at hb
      rw [Finset.sum_range_succ'] at hb
      simpa [add_comm] using hb.symm

/-- The conditional mean finite overlap polynomial is integrable under the Poisson count law. -/
theorem integrable_conditional_cellOverlap (ν : ∀ m, Measure (Cell m))
    [∀ m, IsProbabilityMeasure (ν m)] (ξ : NNReal) {τ : ℝ} (hτ : |τ| ≤ 1 / 4)
    (hν : ∀ m, ∀ᵐ c ∂ν m, Valid c) (γ z : ℝ) :
    Integrable (fun m : ℕ => ∫ c, cellOverlap τ γ z c ∂ν m) (poissonMeasure ξ) := by
  have hb : Integrable (fun m : ℕ => (1 + 4 * γ ^ 2 * |z|) ^ m) (poissonMeasure ξ) := by
    simpa using integrable_poisson_tilted_factorial ξ
      (by positivity : 0 ≤ 1 + 4 * γ ^ 2 * |z|) 0
  refine hb.mono' (measurable_of_countable _).aestronglyMeasurable ?_
  apply Filter.Eventually.of_forall
  intro m
  calc
    _ ≤ ∫ c, ‖cellOverlap τ γ z c‖ ∂ν m := norm_integral_le_integral_norm _
    _ ≤ ∫ _c : Cell m, (1 + 4 * γ ^ 2 * |z|) ^ m ∂ν m := by
      apply integral_mono_ae (integrable_cellOverlap ν hτ hν γ z m).norm (integrable_const _)
      filter_upwards [hν m] with c hc
      exact norm_cellOverlap_le hτ γ z c hc
    _ = _ := by simp

/-- Poisson averaging of the finite overlap polynomial equals the absolutely convergent
  coefficient series. -/
theorem integral_cellOverlap_eq_series (ν : ∀ m, Measure (Cell m))
    [∀ m, IsProbabilityMeasure (ν m)] (ξ : NNReal) {τ : ℝ} (hτ : |τ| ≤ 1 / 4)
    (hν : ∀ m, ∀ᵐ c ∂ν m, Valid c) (γ z : ℝ) :
    (∫ m : ℕ, ∫ c, cellOverlap τ γ z c ∂ν m ∂poissonMeasure ξ) =
      overlapSeries (coefficient ν ξ τ γ) z := by
  let F : ℕ → ℕ → ℝ := fun d m =>
    γ ^ (2 * (d + 1)) * conditionalEnergy ν τ m (d + 1) * z ^ (d + 1)
  have hi (d : ℕ) : Integrable (F d) (poissonMeasure ξ) :=
    ((integrable_conditionalEnergy ν ξ hτ hν (d + 1)).const_mul
      (γ ^ (2 * (d + 1)))).mul_const (z ^ (d + 1))
  have hs : Summable (fun d => ∫ m, ‖F d m‖ ∂poissonMeasure ξ) := by
    apply (coefficient_summable_abs ν ξ hτ hν γ z).congr
    intro d
    have hg : 0 ≤ γ ^ (2 * (d + 1)) := by rw [pow_mul]; positivity
    have hn (m : ℕ) : 0 ≤ conditionalEnergy ν τ m (d + 1) :=
      integral_nonneg (fun c => subsetEnergy_nonneg τ c _)
    simp only [F, Real.norm_eq_abs, abs_mul, abs_of_nonneg hg,
      abs_of_nonneg (hn _), abs_pow]
    rw [integral_mul_const, integral_const_mul]
    rw [abs_of_nonneg (coefficient_nonneg ν ξ τ γ _)]
    rfl
  have ht : Integrable (fun m => ∑' d, F d m) (poissonMeasure ξ) := by
    apply (integrable_conditional_cellOverlap ν ξ hτ hν γ z).sub (integrable_const 1) |>.congr
    apply Filter.Eventually.of_forall
    intro m
    change (∫ c, cellOverlap τ γ z c ∂ν m) - 1 = ∑' d, F d m
    rw [integral_cellOverlap_eq_tsum ν hτ hν γ z m]
    dsimp [F]
    ring
  simp_rw [integral_cellOverlap_eq_tsum ν hτ hν γ z]
  rw [integral_add (integrable_const 1) ht]
  rw [← integral_tsum_of_summable_integral_norm hi hs]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  unfold overlapSeries
  congr 1
  apply tsum_congr
  intro d
  dsimp [F]
  rw [integral_mul_const, integral_const_mul]
  rfl

/-- The conditional cross moment integrates the two actual posterior outcome likelihoods. -/
def conditionalCrossMoment {Ω : Type*} [MeasurableSpace Ω]
    (ρ : ∀ m, Cell m → Measure Ω)
    (v w : ∀ m, Cell m → Fin m → Ω → ℝ) (τ γ : ℝ) (m : ℕ) (c : Cell m) : ℝ :=
  ∫ ω, outcomeLikelihood τ γ c (fun i => v m c i ω) *
    outcomeLikelihood τ γ c (fun i => w m c i ω) ∂ρ m c

/-- At bounded cell data, independent centered outcome pairs identify the actual
conditional likelihood cross moment with the finite overlap polynomial. -/
theorem conditionalCrossMoment_eq_cellOverlap {Ω : Type*} [MeasurableSpace Ω]
    (ρ : ∀ m, Cell m → Measure Ω) [∀ m c, IsProbabilityMeasure (ρ m c)]
    (v w : ∀ m, Cell m → Fin m → Ω → ℝ) {τ z : ℝ} (hτ : |τ| ≤ 1 / 4)
    {m : ℕ} {c : Cell m} (hu : ∀ i, |c.1 i| ≤ 1)
    (hout : CenteredOutcomePair (ρ m c) (v m c) (w m c) z) (γ : ℝ) :
    conditionalCrossMoment ρ v w τ γ m c = cellOverlap τ γ z c := by
  exact integral_outcomeLikelihood_pair_by_card hout hτ hu γ

/-- Conditional cross moments are integrable over cell data when the conditional outcome
pairs are centered and independent with common overlap. -/
theorem integrable_conditionalCrossMoment {Ω : Type*} [MeasurableSpace Ω]
    (ν : ∀ m, Measure (Cell m)) [∀ m, IsProbabilityMeasure (ν m)]
    (ρ : ∀ m, Cell m → Measure Ω) [∀ m c, IsProbabilityMeasure (ρ m c)]
    (v w : ∀ m, Cell m → Fin m → Ω → ℝ) {τ z : ℝ} (hτ : |τ| ≤ 1 / 4)
    (hν : ∀ m, ∀ᵐ c ∂ν m, Valid c)
    (hout : ∀ m, ∀ᵐ c ∂ν m, CenteredOutcomePair (ρ m c) (v m c) (w m c) z)
    (γ : ℝ) (m : ℕ) :
    Integrable (conditionalCrossMoment ρ v w τ γ m) (ν m) := by
  -- Equality almost everywhere with the measurable finite cellOverlap avoids
  -- requiring a measurable outcome kernel as an additional input.
  apply (integrable_cellOverlap ν hτ hν γ z m).congr
  filter_upwards [hν m, hout m] with c hc ho
  exact (conditionalCrossMoment_eq_cellOverlap ρ v w hτ hc.1 ho γ).symm

/-- Averaged conditional cross moments are Poisson-integrable under the same outcome assumptions. -/
theorem integrable_poisson_crossMoment {Ω : Type*} [MeasurableSpace Ω]
    (ν : ∀ m, Measure (Cell m)) [∀ m, IsProbabilityMeasure (ν m)]
    (ρ : ∀ m, Cell m → Measure Ω) [∀ m c, IsProbabilityMeasure (ρ m c)]
    (v w : ∀ m, Cell m → Fin m → Ω → ℝ) (ξ : NNReal) {τ z : ℝ}
    (hτ : |τ| ≤ 1 / 4) (hν : ∀ m, ∀ᵐ c ∂ν m, Valid c)
    (hout : ∀ m, ∀ᵐ c ∂ν m, CenteredOutcomePair (ρ m c) (v m c) (w m c) z)
    (γ : ℝ) :
    Integrable (fun m : ℕ => ∫ c, conditionalCrossMoment ρ v w τ γ m c ∂ν m)
      (poissonMeasure ξ) := by
  apply (integrable_conditional_cellOverlap ν ξ hτ hν γ z).congr
  apply Filter.Eventually.of_forall
  intro m
  apply integral_congr_ae
  filter_upwards [hν m, hout m] with c hc ho
  exact (conditionalCrossMoment_eq_cellOverlap ρ v w hτ hc.1 ho γ).symm

/-- Given [conditional probability laws for cells](hyp:ν), [conditional probability
laws for outcome scores](hyp:ρ), [two outcome-score families](hyp:v,w), [a Poisson
mean](hyp:ξ), [a bounded tilt](hyp:hτ), [almost-surely valid cells](hyp:hν),
[almost-surely centered independent outcome pairs](hyp:hout), and [an outcome
amplitude](hyp:γ), [the Poisson-integrated posterior likelihood cross moment equals
the coefficient overlap series](goal). -/
theorem poisson_crossMoment_eq_series {Ω : Type*} [MeasurableSpace Ω]
    (ν : ∀ m, Measure (Cell m)) [∀ m, IsProbabilityMeasure (ν m)]
    (ρ : ∀ m, Cell m → Measure Ω) [∀ m c, IsProbabilityMeasure (ρ m c)]
    (v w : ∀ m, Cell m → Fin m → Ω → ℝ) (ξ : NNReal) {τ z : ℝ}
    (hτ : |τ| ≤ 1 / 4) (hν : ∀ m, ∀ᵐ c ∂ν m, Valid c)
    (hout : ∀ m, ∀ᵐ c ∂ν m, CenteredOutcomePair (ρ m c) (v m c) (w m c) z)
    (γ : ℝ) :
    (∫ m : ℕ, ∫ c, conditionalCrossMoment ρ v w τ γ m c ∂ν m ∂poissonMeasure ξ) =
      overlapSeries (coefficient ν ξ τ γ) z := by
  rw [← integral_cellOverlap_eq_series ν ξ hτ hν γ z]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro m
  apply integral_congr_ae
  filter_upwards [hν m, hout m] with c hc ho
  exact conditionalCrossMoment_eq_cellOverlap ρ v w hτ hc.1 ho γ

end Causalean.Stat.Minimax.Mixture.PoissonLatentSign
