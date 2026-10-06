module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.DeathKMOracleTransport
public import Causalean.Mathlib.Probability.BernoulliMeasure

/-!
# Second reciprocal moments for binomial risk counts
-/

public section

open scoped BigOperators
open Causalean.Mathlib.Probability

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier.DeathCP

/-- A zero-safe squared reciprocal count is controlled by the second shifted
factorial reciprocal. -/
lemma totalized_inverse_count_sq_le (j : ℕ) :
    (if 0 < j then (j : ℝ)⁻¹ ^ 2 else 0) ≤
      6 * (((j : ℝ) + 1) * ((j : ℝ) + 2))⁻¹ := by
  by_cases hj : 0 < j
  · rw [if_pos hj]
    have hjR : (0 : ℝ) < j := by exact_mod_cast hj
    have hjge : (1 : ℝ) ≤ j := by exact_mod_cast hj
    have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hj2 : (0 : ℝ) < (j : ℝ) + 2 := by positivity
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (mul_pos hj1 hj2)).2
    have hjge : (1 : ℝ) ≤ j := by exact_mod_cast hj
    field_simp
    nlinarith
  · simp [hj]
    positivity

/-- The refined shifted reciprocal comparison retains the cancellation needed
for the centered inverse-count coefficient. -/
lemma totalized_inverse_count_le_shifted (j : ℕ) :
    (if 0 < j then (j : ℝ)⁻¹ else 0) ≤
      ((j : ℝ) + 1)⁻¹ +
        3 * (((j : ℝ) + 1) * ((j : ℝ) + 2))⁻¹ := by
  by_cases hj : 0 < j
  · rw [if_pos hj]
    have hjR : (0 : ℝ) < j := by exact_mod_cast hj
    have hjge : (1 : ℝ) ≤ j := by exact_mod_cast hj
    have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hj2 : (0 : ℝ) < (j : ℝ) + 2 := by positivity
    field_simp
    nlinarith
  · simp [hj]
    positivity

/-- Countwise algebra behind the centered coefficient expansion. -/
lemma weighted_scaledInverse_center_sq_eq (n k : ℕ) (q : ℝ)
    (hn : 0 < n) (hq : 0 < q) :
    ((k : ℝ) / n) *
        ((if 0 < k then (n : ℝ) / k else 0) - 1 / q) ^ 2 =
      (if 0 < k then (n : ℝ) / k else 0) -
        (2 / q) * (if 0 < k then 1 else 0) +
        (k : ℝ) / ((n : ℝ) * q ^ 2) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  by_cases hk : 0 < k
  · rw [if_pos hk, if_pos hk]
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    field_simp
    ring
  · have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
    subst k
    simp

/-- The binomial mean of the zero-safe squared reciprocal count has the
factorial-moment envelope needed for fixed-horizon KM coefficient control. -/
lemma binomial_totalized_inverse_count_sq_le (m : ℕ) (p : ℝ)
    (hp : 0 < p) (hp1 : p ≤ 1) :
    (∑ j ∈ Finset.range (m + 1), binomialWeight m p j *
      (if 0 < j then (j : ℝ)⁻¹ ^ 2 else 0)) ≤
      6 / (((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) * p ^ 2) := by
  let d : ℝ := ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) * p ^ 2
  have hq : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hweight (j : ℕ) : 0 ≤ binomialWeight m p j := by
    unfold binomialWeight
    positivity
  have hterm (j : ℕ) (hj : j ∈ Finset.range (m + 1)) :
      d * (binomialWeight m p j *
        (((j : ℝ) + 1) * ((j : ℝ) + 2))⁻¹) =
      binomialWeight (m + 2) p (j + 2) := by
    have hjlt : j < m + 1 := Finset.mem_range.mp hj
    have hsub : (m + 2) - (j + 2) = m - j := by omega
    have hc1 := Nat.add_one_mul_choose_eq m j
    have hc2 := Nat.add_one_mul_choose_eq (m + 1) (j + 1)
    have hc2' : (m + 2) * Nat.choose (m + 1) (j + 1) =
        Nat.choose (m + 2) (j + 2) * (j + 2) := by
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hc2
    have hc : ((m + 1 : ℕ) * (m + 2) * Nat.choose m j : ℕ) =
        Nat.choose (m + 2) (j + 2) * ((j + 1) * (j + 2)) := by
      calc
        (m + 1) * (m + 2) * Nat.choose m j =
            (m + 2) * ((m + 1) * Nat.choose m j) := by ring
        _ = (m + 2) * (Nat.choose (m + 1) (j + 1) * (j + 1)) := by rw [hc1]
        _ = ((m + 2) * Nat.choose (m + 1) (j + 1)) * (j + 1) := by ring
        _ = (Nat.choose (m + 2) (j + 2) * (j + 2)) * (j + 1) := by rw [hc2']
        _ = Nat.choose (m + 2) (j + 2) * ((j + 1) * (j + 2)) := by ring
    have hcR : (((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) *
        (Nat.choose m j : ℝ)) =
        (Nat.choose (m + 2) (j + 2) : ℝ) *
          (((j : ℝ) + 1) * ((j : ℝ) + 2)) := by exact_mod_cast hc
    dsimp [d]
    rw [binomialWeight, binomialWeight, hsub, pow_add]
    field_simp
    rw [hcR]
    ring
  have hshift : d * (∑ j ∈ Finset.range (m + 1),
      binomialWeight m p j * (((j : ℝ) + 1) * ((j : ℝ) + 2))⁻¹) ≤ 1 := by
    calc
      d * (∑ j ∈ Finset.range (m + 1),
          binomialWeight m p j * (((j : ℝ) + 1) * ((j : ℝ) + 2))⁻¹) =
          ∑ j ∈ Finset.range (m + 1),
            d * (binomialWeight m p j *
              (((j : ℝ) + 1) * ((j : ℝ) + 2))⁻¹) := by rw [Finset.mul_sum]
      _ = ∑ j ∈ Finset.range (m + 1), binomialWeight (m + 2) p (j + 2) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hterm j hj
      (∑ j ∈ Finset.range (m + 1), binomialWeight (m + 2) p (j + 2)) ≤
          ∑ j ∈ Finset.range (m + 3), binomialWeight (m + 2) p j := by
        rw [← Finset.sum_image (s := Finset.range (m + 1))
          (g := fun j : ℕ => j + 2) (f := binomialWeight (m + 2) p) (by
            intro i hi j hj hij
            exact Nat.add_right_cancel hij)]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro j hj
          simp only [Finset.mem_image, Finset.mem_range] at hj ⊢
          obtain ⟨i, hi, rfl⟩ := hj
          omega
        · intro j hj hnot
          unfold binomialWeight
          positivity
      _ = 1 := by
        rw [show ∑ j ∈ Finset.range (m + 3), binomialWeight (m + 2) p j =
            (p + (1 - p)) ^ (m + 2) by
          rw [add_pow]
          apply Finset.sum_congr rfl
          intro j hj
          unfold binomialWeight
          ring]
        simp
  calc
    _ ≤ ∑ j ∈ Finset.range (m + 1),
        binomialWeight m p j *
          (6 * (((j : ℝ) + 1) * ((j : ℝ) + 2))⁻¹) := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (totalized_inverse_count_sq_le j) (hweight j)
    _ = 6 * (∑ j ∈ Finset.range (m + 1),
        binomialWeight m p j *
          (((j : ℝ) + 1) * ((j : ℝ) + 2))⁻¹) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ 6 * (1 / d) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact (le_div_iff₀ hd).2 (by simpa [mul_comm] using hshift)
    _ = _ := by
      dsimp [d]
      ring

end CausalSmith.Stat.RecurrentEndpointCensorFrontier.DeathCP


open MeasureTheory
open Causalean.Mathlib.Probability

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier.DeathCP

open Classical in
private lemma eventIndicator_measurePreserving {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Set Ω) (hA : MeasurableSet A) :
    MeasurePreserving (fun z => decide (z ∈ A)) μ (bernoulliBool (μ.real A)) := by
  have hf : Measurable (fun z => decide (z ∈ A)) := by
    simpa using (Measurable.ite hA measurable_const measurable_const :
      Measurable (fun z => if z ∈ A then true else false))
  let : IsProbabilityMeasure (bernoulliBool (μ.real A)) :=
    bernoulliBool_isProbabilityMeasure ENNReal.toReal_nonneg measureReal_le_one
  refine ⟨hf, Measure.ext_of_singleton fun b => ?_⟩
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change (μ.map (fun z => decide (z ∈ A))).real {b} = _
  rw [map_measureReal_apply hf (measurableSet_singleton b)]
  cases b
  · have hcompl : μ.real {z | z ∉ A} = 1 - μ.real A := by
      change μ.real Aᶜ = 1 - μ.real A
      simpa using measureReal_compl (μ := μ) hA
    simpa [bernoulliBool, sub_nonneg.mpr measureReal_le_one, Set.preimage] using hcompl
  · simp [bernoulliBool, Set.preimage]
    rfl

private lemma integral_boolCount_eq_binomial (n : ℕ) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (F : ℕ → ℝ) :
    (∫ b : Fin n → Bool, F (Finset.univ.filter fun i => b i = true).card
      ∂Measure.pi (fun _ => bernoulliBool p)) =
      ∑ k ∈ Finset.range (n + 1), binomialWeight n p k * F k := by
  let : IsProbabilityMeasure (bernoulliBool p) :=
    bernoulliBool_isProbabilityMeasure hp0 hp1
  rw [integral_fintype Integrable.of_finite]
  have hmass (b : Fin n → Bool) :
      (Measure.pi (fun _ : Fin n => bernoulliBool p)).real {b} =
        ∏ i, if b i then p else 1 - p := by
    simp only [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
    apply Finset.prod_congr rfl
    intro i hi
    cases b i <;> simp [bernoulliBool, hp0, sub_nonneg.mpr hp1]
  simp_rw [hmass, smul_eq_mul]
  simpa using sum_bernoulli_eq_binomial (ι := Fin n) p F

open Classical in
lemma integral_eventCount_eq_binomial {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Set Ω) (hA : MeasurableSet A)
    (n : ℕ) (F : ℕ → ℝ) :
    (∫ z : Fin n → Ω, F (Finset.univ.filter fun i => z i ∈ A).card
      ∂Measure.pi (fun _ => μ)) =
      ∑ k ∈ Finset.range (n + 1), binomialWeight n (μ.real A) k * F k := by
  let : IsProbabilityMeasure (bernoulliBool (μ.real A)) :=
    bernoulliBool_isProbabilityMeasure ENNReal.toReal_nonneg measureReal_le_one
  have hmp := measurePreserving_pi (fun _ : Fin n => μ)
    (fun _ => bernoulliBool (μ.real A))
    (fun _ => eventIndicator_measurePreserving μ A hA)
  rw [← integral_boolCount_eq_binomial n (μ.real A)
    ENNReal.toReal_nonneg measureReal_le_one F]
  rw [← hmp.map_eq, integral_map_of_stronglyMeasurable hmp.measurable
    (Measurable.of_discrete.stronglyMeasurable)]
  simp

end CausalSmith.Stat.RecurrentEndpointCensorFrontier.DeathCP
