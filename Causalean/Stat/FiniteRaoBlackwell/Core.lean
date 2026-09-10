import Causalean.Experimentation.DesignBased.DesignCore

/-!
# Finite uniform experiments and guarded conditional designs

This module gives the finite-sum probability substrate for an experiment that first chooses
uniformly from a nonempty finite set of admissible allocations and then draws a finite
observation.  It defines the joint mass, the mass of a coarsening statistic, and a conditional
design on every statistic fiber.  Positive fibers use Bayes' formula; zero-mass fibers use a
fixed point mass, so the result is a genuine probability design everywhere without changing
any disintegration identity.
-/

open scoped BigOperators

namespace Causalean.Stat.FiniteRaoBlackwell

open Causalean.Experimentation.DesignBased

variable {Latent Allocation Observation Statistic : Type*}
variable [Fintype Latent] [Fintype Allocation] [Fintype Observation] [Fintype Statistic]
variable [DecidableEq Allocation] [DecidableEq Observation] [DecidableEq Statistic]

/-- A finite uniform-allocation experiment consists of a nonempty admissible allocation set,
a normalized nonnegative observation mass for every state and allocation, a finite statistic,
and a fallback observation used only to totalize conditioning on null fibers. -/
structure FiniteUniformExperiment
    (Latent Allocation Observation Statistic : Type*)
    [Fintype Latent] [Fintype Allocation] [Fintype Observation] [Fintype Statistic] where
  /-- The finite set of admissible fixed-size allocations. -/
  allocations : Finset Allocation
  /-- At least one admissible allocation is available. -/
  allocations_nonempty : allocations.Nonempty
  /-- Conditional observation mass at a latent state and allocation. -/
  observationMass : Latent → Allocation → Observation → ℝ
  /-- Every conditional observation mass is nonnegative. -/
  observationMass_nonneg : ∀ θ a x, 0 ≤ observationMass θ a x
  /-- Conditional observation masses sum to one. -/
  observationMass_sum : ∀ θ a, ∑ x, observationMass θ a x = 1
  /-- The coarsened statistic computed from allocation and observation. -/
  statistic : Allocation → Observation → Statistic
  /-- A fallback observation used to define null-fiber conditional laws. -/
  fallbackObservation : Observation

namespace FiniteUniformExperiment

variable (E : FiniteUniformExperiment Latent Allocation Observation Statistic)

/-- For [a finite uniform-allocation experiment](hyp:E), the [fallback allocation](goal) is a chosen member of its nonempty set of admissible allocations. -/
noncomputable def fallbackAllocation : Allocation :=
  E.allocations_nonempty.choose

/-- For [a finite uniform-allocation experiment](hyp:E), the [fallback full-data point](goal) pairs its fallback allocation with its fallback observation. -/
noncomputable def fallbackSample : Allocation × Observation :=
  (E.fallbackAllocation, E.fallbackObservation)

/-- For [a finite uniform-allocation experiment](hyp:E) and [a full-data point](hyp:z), the [sample statistic](goal) is the statistic computed from that point's allocation and observation. -/
def sampleStatistic (z : Allocation × Observation) : Statistic :=
  E.statistic z.1 z.2

/-- For [a finite uniform-allocation experiment](hyp:E) and [an allocation](hyp:a), the [uniform allocation mass](goal) is the reciprocal of the number of admissible allocations when that allocation is admissible, and zero otherwise. -/
noncomputable def uniformAllocationMass (a : Allocation) : ℝ :=
  by
    classical
    exact if a ∈ E.allocations then (E.allocations.card : ℝ)⁻¹ else 0

/-- For [a finite uniform-allocation experiment](hyp:E), [a latent state](hyp:θ), and [a full-data point](hyp:z), the [joint mass](goal) is the uniform allocation mass of its allocation multiplied by the conditional observation mass of its observation at that state and allocation. -/
noncomputable def jointMass (θ : Latent) (z : Allocation × Observation) : ℝ :=
  E.uniformAllocationMass z.1 * E.observationMass θ z.1 z.2

/-- The uniform allocation mass is nonnegative at every allocation. -/
theorem uniformAllocationMass_nonneg (a : Allocation) :
    0 ≤ E.uniformAllocationMass a := by
  classical
  simp only [uniformAllocationMass]
  split_ifs
  · exact inv_nonneg.mpr (Nat.cast_nonneg _)
  · exact le_rfl

/-- The full-data joint mass is nonnegative at every state and sample point. -/
theorem jointMass_nonneg (θ : Latent) (z : Allocation × Observation) :
    0 ≤ E.jointMass θ z := by
  exact mul_nonneg (E.uniformAllocationMass_nonneg z.1)
    (E.observationMass_nonneg θ z.1 z.2)

/-- At every latent state, the full-data joint mass sums to one. -/
theorem jointMass_sum (θ : Latent) :
    ∑ z : Allocation × Observation, E.jointMass θ z = 1 := by
  /- Expand the product sum, discard allocations off the support, use observationMass_sum,
  and cancel the nonzero finite support cardinality. -/
  classical
  rw [Fintype.sum_prod_type]
  simp_rw [jointMass, ← Finset.mul_sum, E.observationMass_sum, mul_one]
  simp [uniformAllocationMass, E.allocations_nonempty.card_ne_zero]

/-- For [a finite uniform-allocation experiment](hyp:E), [a latent state](hyp:θ), and [a statistic value](hyp:s), the [statistic mass](goal) is the sum of joint masses of all full-data points whose statistic equals that value. -/
noncomputable def statisticMass (θ : Latent) (s : Statistic) : ℝ :=
  by
    classical
    exact ∑ z : Allocation × Observation,
      if E.sampleStatistic z = s then E.jointMass θ z else 0

/-- Every statistic mass is nonnegative. -/
theorem statisticMass_nonneg (θ : Latent) (s : Statistic) :
    0 ≤ E.statisticMass θ s := by
  classical
  exact Finset.sum_nonneg fun z _ => by
    split_ifs
    · exact E.jointMass_nonneg θ z
    · exact le_rfl

/-- At every latent state, the statistic masses sum to one. -/
theorem statisticMass_sum (θ : Latent) :
    ∑ s : Statistic, E.statisticMass θ s = 1 := by
  /- Swap the two finite sums; for each full-data point exactly one statistic value survives. -/
  classical
  rw [← E.jointMass_sum θ]
  simp_rw [statisticMass]
  rw [Finset.sum_comm]
  simp

/-- For [a finite uniform-allocation experiment](hyp:E), [a latent state](hyp:θ), [a statistic value](hyp:s), and [a full-data point](hyp:z), the [guarded conditional weight](goal) is the joint mass divided by the statistic mass when that mass is positive and the point has the requested statistic, is zero for other points, and is instead a point mass at the fallback sample when the statistic mass is zero. -/
noncomputable def conditionalWeight (θ : Latent) (s : Statistic)
    (z : Allocation × Observation) : ℝ :=
  by
    classical
    exact if 0 < E.statisticMass θ s then
      if E.sampleStatistic z = s then E.jointMass θ z / E.statisticMass θ s else 0
    else if z = E.fallbackSample then 1 else 0

/-- On a positive fiber, the guarded conditional weight is the usual fiber-restricted Bayes ratio. -/
theorem conditionalWeight_of_pos {θ : Latent} {s : Statistic}
    (h : 0 < E.statisticMass θ s) (z : Allocation × Observation) :
    E.conditionalWeight θ s z =
      if E.sampleStatistic z = s then E.jointMass θ z / E.statisticMass θ s else 0 := by
  classical
  simp [conditionalWeight, h]

/-- On a zero-mass fiber, the guarded conditional weight is the fallback point mass. -/
theorem conditionalWeight_of_eq_zero {θ : Latent} {s : Statistic}
    (h : E.statisticMass θ s = 0) (z : Allocation × Observation) :
    E.conditionalWeight θ s z = if z = E.fallbackSample then 1 else 0 := by
  classical
  simp [conditionalWeight, h]

/-- Every guarded conditional weight is nonnegative, including on null fibers. -/
theorem conditionalWeight_nonneg (θ : Latent) (s : Statistic)
    (z : Allocation × Observation) :
    0 ≤ E.conditionalWeight θ s z := by
  classical
  by_cases h : 0 < E.statisticMass θ s
  · simp only [E.conditionalWeight_of_pos h]
    split_ifs
    · exact div_nonneg (E.jointMass_nonneg θ z) (le_of_lt h)
    · exact le_rfl
  · have hs : E.statisticMass θ s = 0 :=
      le_antisymm (le_of_not_gt h) (E.statisticMass_nonneg θ s)
    rw [E.conditionalWeight_of_eq_zero hs]
    split_ifs <;> norm_num

/-- The guarded conditional weights sum to one on every fiber, with positive fibers normalized
by Bayes' formula and null fibers normalized by the fallback point mass. -/
theorem conditionalWeight_sum (θ : Latent) (s : Statistic) :
    ∑ z : Allocation × Observation, E.conditionalWeight θ s z = 1 := by
  /- Split on positivity of statisticMass.  In the positive branch divide the defining fiber
  sum by its mass; in the null branch sum the fallback Kronecker mass. -/
  classical
  by_cases h : 0 < E.statisticMass θ s
  · simp_rw [E.conditionalWeight_of_pos h]
    simp_rw [div_eq_mul_inv]
    have hfactor (z : Allocation × Observation) :
        (if E.sampleStatistic z = s then
            E.jointMass θ z * (E.statisticMass θ s)⁻¹ else 0) =
          (if E.sampleStatistic z = s then E.jointMass θ z else 0) *
            (E.statisticMass θ s)⁻¹ := by
      split_ifs <;> simp
    simp_rw [hfactor]
    rw [← Finset.sum_mul, show
      (∑ z : Allocation × Observation,
        if E.sampleStatistic z = s then E.jointMass θ z else 0) =
          E.statisticMass θ s from rfl]
    exact mul_inv_cancel₀ (ne_of_gt h)
  · have hs : E.statisticMass θ s = 0 :=
      le_antisymm (le_of_not_gt h) (E.statisticMass_nonneg θ s)
    simp [E.conditionalWeight_of_eq_zero hs]

/-- For [a finite uniform-allocation experiment](hyp:E), [a latent state](hyp:θ), and [a statistic value](hyp:s), the [guarded conditional full-data design](goal) is the finite probability design whose probabilities are the guarded conditional weights. -/
noncomputable def conditionalDesign (θ : Latent) (s : Statistic) :
    FiniteDesign (Allocation × Observation) where
  p := E.conditionalWeight θ s
  p_nonneg := E.conditionalWeight_nonneg θ s
  p_sum := E.conditionalWeight_sum θ s

/-- For [a finite uniform-allocation experiment](hyp:E) and [a latent state](hyp:θ), the [statistic design](goal) is the finite probability design whose probabilities are the statistic masses. -/
noncomputable def statisticDesign (θ : Latent) : FiniteDesign Statistic where
  p := E.statisticMass θ
  p_nonneg := E.statisticMass_nonneg θ
  p_sum := E.statisticMass_sum θ

/-- Multiplying a statistic marginal by its guarded conditional weight recovers the joint mass
on that fiber and zero away from it, including when the marginal is zero. -/
theorem statisticMass_mul_conditionalWeight (θ : Latent) (s : Statistic)
    (z : Allocation × Observation) :
    E.statisticMass θ s * E.conditionalWeight θ s z =
      if E.sampleStatistic z = s then E.jointMass θ z else 0 := by
  /- Positive mass is field cancellation.  If the mass is zero, nonnegativity and the fact
  that jointMass is one summand in statisticMass force every mass on the fiber to vanish. -/
  classical
  by_cases h : 0 < E.statisticMass θ s
  · rw [E.conditionalWeight_of_pos h]
    split_ifs
    · exact mul_div_cancel₀ _ (ne_of_gt h)
    · exact mul_zero _
  · have hs : E.statisticMass θ s = 0 :=
      le_antisymm (le_of_not_gt h) (E.statisticMass_nonneg θ s)
    rw [hs, zero_mul]
    split_ifs with hz
    · have hsum :
          (∑ z' : Allocation × Observation,
            if E.sampleStatistic z' = s then E.jointMass θ z' else 0) = 0 := by
          simpa [statisticMass] using hs
      have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun z' _ => by
        split_ifs
        · exact E.jointMass_nonneg θ z'
        · exact le_rfl)).mp hsum z (Finset.mem_univ z)
      simpa [hz] using hterm.symm
    · rfl

/-- Every full-data atom factors into its statistic marginal and guarded conditional weight. -/
theorem jointMass_eq_statisticMass_mul_conditionalWeight
    (θ : Latent) (z : Allocation × Observation) :
    E.jointMass θ z =
      E.statisticMass θ (E.sampleStatistic z) *
        E.conditionalWeight θ (E.sampleStatistic z) z := by
  simpa using (E.statisticMass_mul_conditionalWeight θ (E.sampleStatistic z) z).symm

/-- Every real test function has [the same joint expectation as its statistic-marginal
expectation of the guarded conditional expectation](goal); null fibers contribute exactly zero. -/
theorem disintegrate_sum (θ : Latent) (f : Allocation × Observation → ℝ) :
    ∑ z, E.jointMass θ z * f z =
      ∑ s, E.statisticMass θ s *
        (∑ z, E.conditionalWeight θ s z * f z) := by
  /- Distribute products over the inner sums, use statisticMass_mul_conditionalWeight,
  swap the finite sums, and collapse the unique statistic value of each sample point. -/
  classical
  simp_rw [Finset.mul_sum, ← mul_assoc,
    E.statisticMass_mul_conditionalWeight θ]
  rw [Finset.sum_comm]
  simp

end FiniteUniformExperiment

end Causalean.Stat.FiniteRaoBlackwell
