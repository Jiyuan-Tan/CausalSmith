module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.OracleQuadraticEnergy

/-!
# Supplied-graph score variance bound
-/

public section

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The supplied-graph additive score has variance at most five times squared augmented degree
over population size.  [For the stated data and conditions](hyp:θ,d,hn,hd,hclass), [the stated conclusion holds](goal). -/
-- @node: oracle_variance_le
lemma oracle_variance_le (θ : Schedule V) (d : ℕ) (hn : 4 ≤ Fintype.card V)
    (hd : 1 ≤ d) (hclass : ScheduleClass θ d) :
    ProbabilityTheory.variance (oracleScore θ) (halfBernoulli V) ≤
      5 * ((d : ℝ) + 1) ^ 2 / Fintype.card V  := by
  rw [ProbabilityTheory.variance_eq_integral (by fun_prop)]
  rw [integral_oracleScore_eq_tte]
  change (∫ z, (oracleScore θ z - tte θ) ^ 2 ∂halfBernoulli V) ≤ _
  simp_rw [oracleScore_centered_expansion]
  let L : Assign V → ℝ := fun z => (2 / (Fintype.card V : ℝ)) *
    (∑ i, oracleMu θ i * ∑ j ∈ oracleNbhd θ i, signOf (z j))
  let Q : Assign V → ℝ := fun z => (Fintype.card V : ℝ)⁻¹ *
    ∑ i, ∑ j ∈ oracleNbhd θ i, ∑ k ∈ (oracleNbhd θ i).erase j,
      oracleBeta θ i j * signOf (z j) * signOf (z k)
  change (∫ z, (L z + Q z) ^ 2 ∂halfBernoulli V) ≤ _
  have hsplit : (∫ z, (L z + Q z) ^ 2 ∂halfBernoulli V) =
      (∫ z, L z ^ 2 ∂halfBernoulli V) +
      (∫ z, 2 * L z * Q z ∂halfBernoulli V) +
      (∫ z, Q z ^ 2 ∂halfBernoulli V) := by
    simp_rw [show ∀ z, (L z + Q z) ^ 2 = L z ^ 2 + 2 * L z * Q z + Q z ^ 2 by
      intro z; ring]
    rw [integral_add (halfBernoulli_integrable _) (halfBernoulli_integrable _),
      integral_add (halfBernoulli_integrable _) (halfBernoulli_integrable _)]
  have hmixed : (∫ z, 2 * L z * Q z ∂halfBernoulli V) = 0 := by
    have he : (fun z => 2 * L z * Q z) = fun z =>
        (2 * (2 / (Fintype.card V : ℝ)) * (Fintype.card V : ℝ)⁻¹) *
        ((∑ i, oracleMu θ i * ∑ l ∈ oracleNbhd θ i, signOf (z l)) *
          (∑ i, ∑ j ∈ oracleNbhd θ i, ∑ k ∈ (oracleNbhd θ i).erase j,
            oracleBeta θ i j * signOf (z j) * signOf (z k))) := by
      funext z
      dsimp [L, Q]
      ring
    rw [he, integral_const_mul, oracle_mixed_second_moment_zero, mul_zero]
  rw [hsplit, hmixed, add_zero]
  refine le_trans (add_le_add
    (oracle_linear_scaled_second_moment_le θ d hn hclass) le_rfl) ?_
  change 4 * ((d : ℝ) + 1) ^ 2 / Fintype.card V +
    (∫ z, ((Fintype.card V : ℝ)⁻¹ *
      ∑ i, ∑ j ∈ oracleNbhd θ i, ∑ k ∈ (oracleNbhd θ i).erase j,
        oracleBeta θ i j * signOf (z j) * signOf (z k)) ^ 2 ∂halfBernoulli V) ≤ _
  simp_rw [mul_pow]
  rw [integral_const_mul, oracle_quadratic_second_moment]
  have hn0 : (0 : ℝ) < Fintype.card V := by
    exact_mod_cast (by omega : 0 < Fintype.card V)
  calc
    _ ≤ 4 * ((d : ℝ) + 1) ^ 2 / Fintype.card V +
        (Fintype.card V : ℝ)⁻¹ ^ 2 *
          ((Fintype.card V : ℝ) * ((d : ℝ) + 1) ^ 2) :=
      add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (oracle_quadratic_energy_le θ d hclass) (sq_nonneg _))
    _ = _ := by field_simp; ring

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
