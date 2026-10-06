module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.OracleWalsh

/-!
# Finite quadratic coefficient energy
-/

public section

noncomputable section
open scoped BigOperators
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The augmented coefficient mass is at most one.  [For the stated data and conditions](hyp:θ,d,hc,i), [the stated conclusion holds](goal). -/
-- @node: oracleBeta_mass_le
lemma oracleBeta_mass_le (θ : Schedule V) (d : ℕ) (hc : ScheduleClass θ d) (i : V) :
    (∑ j ∈ oracleNbhd θ i, |oracleBeta θ i j|) ≤ 1 := by
  rw [oracleBeta_abs_sum]
  have h := hc.coeffMass i
  linarith [abs_nonneg (θ.a i)]

/-- A pair square is bounded by its absolute coefficient mass.  [For the stated data and conditions](hyp:θ,d,hc,i,j,k,hj,hk), [the stated conclusion holds](goal). -/
-- @node: oracleBeta_pair_sq_le
lemma oracleBeta_pair_sq_le (θ : Schedule V) (d : ℕ) (hc : ScheduleClass θ d)
    (i j k : V) (hj : j ∈ oracleNbhd θ i) (hk : k ∈ (oracleNbhd θ i).erase j) :
    (oracleBeta θ i j + oracleBeta θ i k) ^ 2 ≤
      |oracleBeta θ i j| + |oracleBeta θ i k| := by
  have hkj := (Finset.mem_erase.mp hk).1
  have hk' := (Finset.mem_erase.mp hk).2
  have hp : |oracleBeta θ i j| + |oracleBeta θ i k| ≤ 1 := by
    calc
      _ = ∑ l ∈ ({j, k} : Finset V), |oracleBeta θ i l| := by
        simp [Ne.symm hkj]
      _ ≤ ∑ l ∈ oracleNbhd θ i, |oracleBeta θ i l| := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro l hl
          simp only [Finset.mem_insert, Finset.mem_singleton] at hl
          rcases hl with rfl | rfl <;> assumption
        · intro l _ _; exact abs_nonneg _
      _ ≤ 1 := oracleBeta_mass_le θ d hc i
  have ha := abs_add_le (oracleBeta θ i j) (oracleBeta θ i k)
  have hn := abs_nonneg (oracleBeta θ i j + oracleBeta θ i k)
  nlinarith [sq_abs (oracleBeta θ i j + oracleBeta θ i k)]

/-- Swapping the two coordinates preserves the row-pair incidence set.  [For the stated data and conditions](hyp:θ,j,k), [the stated conclusion holds](goal). -/
-- @node: oracle_pair_incidence_symm
lemma oracle_pair_incidence_symm (θ : Schedule V) (j k : V) :
    (Finset.univ.filter fun i => k ∈ oracleNbhd θ i ∧ j ∈ (oracleNbhd θ i).erase k) =
      (Finset.univ.filter fun i => j ∈ oracleNbhd θ i ∧ k ∈ (oracleNbhd θ i).erase j) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
  constructor <;> rintro ⟨h₁, h₂, h₃⟩ <;> exact ⟨h₃, Ne.symm h₂, h₁⟩

/-- The symmetrized collected coefficient is the rowwise pair-coefficient sum.  [For the stated data and conditions](hyp:θ,j,k), [the stated conclusion holds](goal). -/
-- @node: oracle_pair_coefficient_sum
lemma oracle_pair_coefficient_sum (θ : Schedule V) (j k : V) :
    oracleQuadraticCoefficient θ j k + oracleQuadraticCoefficient θ k j =
      ∑ i ∈ Finset.univ.filter
        (fun i => j ∈ oracleNbhd θ i ∧ k ∈ (oracleNbhd θ i).erase j),
        (oracleBeta θ i j + oracleBeta θ i k) := by
  unfold oracleQuadraticCoefficient
  rw [oracle_pair_incidence_symm, Finset.sum_add_distrib]

/-- Out-degree bounds the number of rows sharing a coordinate pair.  [For the stated data and conditions](hyp:θ,d,hc,j,k), [the stated conclusion holds](goal). -/
-- @node: oracle_pair_coefficient_sq_le
lemma oracle_pair_coefficient_sq_le (θ : Schedule V) (d : ℕ) (hc : ScheduleClass θ d)
    (j k : V) :
    (oracleQuadraticCoefficient θ j k + oracleQuadraticCoefficient θ k j) ^ 2 ≤
      ((d : ℝ) + 1) * ∑ i ∈ Finset.univ.filter
        (fun i => j ∈ oracleNbhd θ i ∧ k ∈ (oracleNbhd θ i).erase j),
        (oracleBeta θ i j + oracleBeta θ i k) ^ 2 := by
  rw [oracle_pair_coefficient_sum]
  have hcard : ((Finset.univ.filter
      (fun i => j ∈ oracleNbhd θ i ∧ k ∈ (oracleNbhd θ i).erase j)).card : ℝ) ≤
      (d : ℝ) + 1 := by
    have hs : (Finset.univ.filter
        (fun i => j ∈ oracleNbhd θ i ∧ k ∈ (oracleNbhd θ i).erase j)).card ≤ d + 1 :=
      (Finset.card_le_card (by
        intro i hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2.1⟩)).trans
          (oracleNbhd_blockDegree θ d hc j)
    exact_mod_cast hs
  exact sq_sum_le_card_mul_sum_sq.trans
    (mul_le_mul_of_nonneg_right hcard (Finset.sum_nonneg fun _ _ => sq_nonneg _))

/-- Summing the absolute pair masses over a row uses at most twice its augmented degree.  [For the stated data and conditions](hyp:θ,d,hc,i), [the stated conclusion holds](goal). -/
-- @node: oracle_row_pair_energy_le
lemma oracle_row_pair_energy_le (θ : Schedule V) (d : ℕ) (hc : ScheduleClass θ d) (i : V) :
    (∑ j ∈ oracleNbhd θ i, ∑ k ∈ (oracleNbhd θ i).erase j,
      (oracleBeta θ i j + oracleBeta θ i k) ^ 2) ≤ 2 * ((d : ℝ) + 1) := by
  calc
    _ ≤ ∑ j ∈ oracleNbhd θ i, ∑ k ∈ (oracleNbhd θ i).erase j,
        (|oracleBeta θ i j| + |oracleBeta θ i k|) := by
      apply Finset.sum_le_sum
      intro j hj
      exact Finset.sum_le_sum fun k hk => oracleBeta_pair_sq_le θ d hc i j k hj hk
    _ ≤ ∑ j ∈ oracleNbhd θ i, ∑ k ∈ oracleNbhd θ i,
        (|oracleBeta θ i j| + |oracleBeta θ i k|) := by
      apply Finset.sum_le_sum
      intro j _
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (by
        intro k _ _; positivity)
    _ = 2 * (oracleNbhd θ i).card * (∑ j ∈ oracleNbhd θ i, |oracleBeta θ i j|) := by
      simp_rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      rw [← Finset.mul_sum]
      ring
    _ ≤ 2 * ((d : ℝ) + 1) := by
      have hcard : ((oracleNbhd θ i).card : ℝ) ≤ (d : ℝ) + 1 := by
        exact_mod_cast oracleNbhd_card_le θ d hc i
      calc
        _ ≤ 2 * ((oracleNbhd θ i).card : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left (oracleBeta_mass_le θ d hc i) (by positivity)
        _ ≤ 2 * ((d : ℝ) + 1) := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hcard (by norm_num : (0:ℝ) ≤ 2)

/-- Reindexing pairwise row energies preserves all neighborhood coordinates.  [For the stated data and conditions](hyp:θ), [the stated conclusion holds](goal). -/
-- @node: oracle_pair_energy_reindex
lemma oracle_pair_energy_reindex (θ : Schedule V) :
    (∑ j, ∑ k, ∑ i ∈ Finset.univ.filter
      (fun i => j ∈ oracleNbhd θ i ∧ k ∈ (oracleNbhd θ i).erase j),
      (oracleBeta θ i j + oracleBeta θ i k) ^ 2) =
      ∑ i, ∑ j ∈ oracleNbhd θ i, ∑ k ∈ (oracleNbhd θ i).erase j,
      (oracleBeta θ i j + oracleBeta θ i k) ^ 2 := by
  simp only [Finset.sum_filter]
  have hswap (j : V) :
      (∑ k, ∑ i, if j ∈ oracleNbhd θ i ∧ k ∈ (oracleNbhd θ i).erase j then
        (oracleBeta θ i j + oracleBeta θ i k) ^ 2 else 0) =
      ∑ i, ∑ k, if j ∈ oracleNbhd θ i ∧ k ∈ (oracleNbhd θ i).erase j then
        (oracleBeta θ i j + oracleBeta θ i k) ^ 2 else 0 := Finset.sum_comm
  simp_rw [hswap]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have hs (s : Finset V) (f : V → ℝ) :
      (∑ j ∈ s, f j) = ∑ j : V, if j ∈ s then f j else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp
  rw [hs (oracleNbhd θ i)]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j ∈ oracleNbhd θ i
  · simp only [hj, true_and, if_true]
    exact (hs _ _).symm
  · simp [hj]

/-- Ordered pairs count each symmetrized quadratic coefficient twice.  [For the stated data and conditions](hyp:θ), [the stated conclusion holds](goal). -/
-- @node: oracle_quadratic_energy_symmetrize
lemma oracle_quadratic_energy_symmetrize (θ : Schedule V) :
    (∑ j, ∑ k, (oracleQuadraticCoefficient θ j k + oracleQuadraticCoefficient θ k j) ^ 2) =
      2 * ∑ j, ∑ k, oracleQuadraticCoefficient θ j k *
        (oracleQuadraticCoefficient θ j k + oracleQuadraticCoefficient θ k j) := by
  have he (j k : V) :
      (oracleQuadraticCoefficient θ j k + oracleQuadraticCoefficient θ k j) ^ 2 =
      oracleQuadraticCoefficient θ j k *
        (oracleQuadraticCoefficient θ j k + oracleQuadraticCoefficient θ k j) +
      oracleQuadraticCoefficient θ k j *
        (oracleQuadraticCoefficient θ k j + oracleQuadraticCoefficient θ j k) := by ring
  simp_rw [he, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun j k => oracleQuadraticCoefficient θ k j *
    (oracleQuadraticCoefficient θ k j + oracleQuadraticCoefficient θ j k))]
  ring

/-- Finite Cauchy–Schwarz, out-degree multiplicity and row mass control the quadratic energy.  [For the stated data and conditions](hyp:θ,d,hc), [the stated conclusion holds](goal). -/
-- @node: oracle_quadratic_energy_le
lemma oracle_quadratic_energy_le (θ : Schedule V) (d : ℕ) (hc : ScheduleClass θ d) :
    (∑ j, ∑ k, oracleQuadraticCoefficient θ j k *
      (oracleQuadraticCoefficient θ j k + oracleQuadraticCoefficient θ k j)) ≤
      (Fintype.card V : ℝ) * ((d : ℝ) + 1) ^ 2 := by
  have h : (∑ j, ∑ k,
      (oracleQuadraticCoefficient θ j k + oracleQuadraticCoefficient θ k j) ^ 2) ≤
      2 * (Fintype.card V : ℝ) * ((d : ℝ) + 1) ^ 2 := by
    calc
      _ ≤ ∑ j, ∑ k, ((d : ℝ) + 1) * ∑ i ∈ Finset.univ.filter
          (fun i => j ∈ oracleNbhd θ i ∧ k ∈ (oracleNbhd θ i).erase j),
          (oracleBeta θ i j + oracleBeta θ i k) ^ 2 :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ =>
          oracle_pair_coefficient_sq_le θ d hc j k
      _ = ((d : ℝ) + 1) * ∑ i, ∑ j ∈ oracleNbhd θ i,
          ∑ k ∈ (oracleNbhd θ i).erase j,
          (oracleBeta θ i j + oracleBeta θ i k) ^ 2 := by
        simp_rw [← Finset.mul_sum]
        rw [oracle_pair_energy_reindex]
      _ ≤ ((d : ℝ) + 1) * ∑ _i : V, 2 * ((d : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun i _ => oracle_row_pair_energy_le θ d hc i) (by positivity)
      _ = _ := by simp; ring
  rw [oracle_quadratic_energy_symmetrize] at h
  linarith

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
