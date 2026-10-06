module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Basic
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Alternation
public import Causalean.Stat.Minimax.Mixture.MomentMatched.MarkedPoisson.Certificate
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! Finite reciprocal-moment priors from the alternation dual and the cited gate. -/

public section

open MeasureTheory Set
open Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality
open Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture

namespace CausalSmith.Stat.MarRareqLogfrontier

-- @node: reciprocal_ratio_power_lower
/-- Given [the specified inputs and assumptions](hyp:K,hK), [the stated mathematical conclusion holds](goal). -/
lemma reciprocal_ratio_power_lower (K : ℕ) (hK : 3 ≤ K) :
    (3 / 32 : ℝ) ≤ (((K : ℝ) - 1) / ((K : ℝ) + 1)) ^ K := by
  let k : ℝ := K
  have hk : (3 : ℝ) ≤ k := by
    change (3 : ℝ) ≤ (K : ℝ)
    exact_mod_cast hK
  have hk0 : 0 < k := by linarith
  let x : ℝ := k⁻¹
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx1 : x < 1 := by
    dsimp [x]
    have h : 1 / k < 1 := (div_lt_iff₀ hk0).2 (by linarith)
    simpa only [one_div] using h
  have hlog := Real.log_div_le_sum_range_add hx0 hx1 0
  simp only [Finset.range_zero, Finset.sum_empty, zero_add, pow_one,
    mul_zero] at hlog
  have hk1 : 0 < k - 1 := by linarith
  have hk2 : 0 < k + 1 := by linarith
  have hr : 0 < (k - 1) / (k + 1) := div_pos hk1 hk2
  have hratio : (1 + x) / (1 - x) = ((k - 1) / (k + 1))⁻¹ := by
    dsimp [x]
    field_simp
  rw [hratio, Real.log_inv] at hlog
  have hbound : k * Real.log ((k - 1) / (k + 1)) ≥ -(9 / 4 : ℝ) := by
    have hx : x = 1 / k := by simp [x]
    rw [hx] at hlog
    have hden : 0 < 1 - (1 / k)^2 := by
      have : (1 / k : ℝ) < 1 := by simpa [x] using hx1
      nlinarith [sq_nonneg (1 - 1 / k)]
    have hsq : 8 * k^2 ≤ 9 * (k^2 - 1) := by nlinarith
    have hfrac : 2 * k^2 / (k^2 - 1) ≤ 9 / 4 := by
      apply (div_le_iff₀ (by nlinarith : 0 < k^2 - 1)).2
      nlinarith
    have heq : k * (2 * (1 / k) / (1 - (1 / k)^2)) =
        2 * k^2 / (k^2 - 1) := by field_simp
    have hlog2 : -Real.log ((k - 1) / (k + 1)) ≤
        2 * (1 / k) / (1 - (1 / k)^2) := by
      have h := mul_le_mul_of_nonneg_left hlog (by norm_num : (0 : ℝ) ≤ 2)
      simpa [div_eq_mul_inv, mul_assoc] using h
    have h := mul_le_mul_of_nonneg_left hlog2 hk0.le
    nlinarith
  have hpow : Real.log (((k - 1) / (k + 1)) ^ K) =
      k * Real.log ((k - 1) / (k + 1)) := by
    rw [Real.log_pow]
  have hExp : Real.exp (-(9 / 4 : ℝ)) ≤ ((k - 1) / (k + 1)) ^ K := by
    calc
      _ ≤ Real.exp (k * Real.log ((k - 1) / (k + 1))) :=
        Real.exp_monotone hbound
      _ = _ := by rw [← hpow, Real.exp_log (pow_pos hr _)]
  have hnum : Real.exp (9 / 4 : ℝ) ≤ 32 / 3 := by
    have h1 : Real.exp 1 ≤ 11 / 4 :=
      le_of_lt (Real.exp_one_lt_d9.trans (by norm_num))
    have hq : Real.exp (1 / 4 : ℝ) ≤ 9 / 7 := by
      convert Real.exp_le_two_add_div_two_sub (x := (1 / 4 : ℝ))
        (by norm_num) (by norm_num) using 1
      norm_num
    have he : Real.exp (9 / 4 : ℝ) =
        (Real.exp 1)^2 * Real.exp (1 / 4 : ℝ) := by
      rw [show (9 / 4 : ℝ) = 1 + 1 + 1 / 4 by norm_num,
        Real.exp_add, Real.exp_add]
      ring
    rw [he]
    nlinarith [Real.exp_pos (1 / 4 : ℝ), Real.exp_pos 1]
  have hnum2 : (3 / 32 : ℝ) ≤ Real.exp (-(9 / 4 : ℝ)) := by
    rw [Real.exp_neg]
    have hh : (3 / 32 : ℝ) ≤ 1 / Real.exp (9 / 4 : ℝ) :=
      (le_div_iff₀ (Real.exp_pos _)).2 (by nlinarith)
    simpa only [one_div] using hh
  exact hnum2.trans hExp

-- @node: reciprocal_best_error_lower
/-- Given [the specified inputs and assumptions](hyp:K,hK), [the stated mathematical conclusion holds](goal). -/
lemma reciprocal_best_error_lower (K : ℕ) (hK : 2 ≤ K) :
    (1 / 12 : ℝ) ≤
      2 * bestUniformApproxError (fun z : ℝ => z⁻¹) 1 ((K : ℝ)^2) K := by
  rw [reciprocalBestApproximation_proved K hK]
  by_cases h2 : K = 2
  · subst K
    norm_num
  · have h3 : 3 ≤ K := by omega
    have hk : (3 : ℝ) ≤ K := by exact_mod_cast h3
    have hcoeff : (4 / 9 : ℝ) ≤
        (((K : ℝ)^2 - 1) / (2 * (K : ℝ)^2)) := by
      apply (le_div_iff₀ (by positivity : 0 < 2 * (K : ℝ)^2)).2
      nlinarith
    calc
      (1 / 12 : ℝ) = 2 * ((4 / 9 : ℝ) * (3 / 32 : ℝ)) := by norm_num
      _ ≤ 2 * ((((K : ℝ)^2 - 1) / (2 * (K : ℝ)^2)) *
        (((K : ℝ) - 1) / ((K : ℝ) + 1)) ^ K) := by
          gcongr
          exact reciprocal_ratio_power_lower K h3

-- @node: lem:moment-matched-reciprocal-priors
/-- Given [the specified inputs and assumptions](hyp:K,hK), [the stated mathematical conclusion holds](goal). -/
lemma moment_matched_reciprocal_priors
    (K : ℕ) (hK : 2 ≤ K) :
    ∃ prior0 prior1 : Measure ℝ,
      IsProbabilityMeasure prior0 ∧ IsProbabilityMeasure prior1 ∧
      (∃ s₀ s₁ : Finset ℝ,
        prior0 (s₀ : Set ℝ) = 1 ∧ prior1 (s₁ : Set ℝ) = 1 ∧
        (∀ z ∈ s₀, 1 ≤ z ∧ z ≤ (K : ℝ) ^ 2) ∧
        (∀ z ∈ s₁, 1 ≤ z ∧ z ≤ (K : ℝ) ^ 2)) ∧
      (∀ v : ℕ, v ≤ K →
        (∫ z, z ^ v ∂prior0) = ∫ z, z ^ v ∂prior1) ∧
      1 / 12 ≤ |(∫ z, z⁻¹ ∂prior1) - (∫ z, z⁻¹ ∂prior0)| := by
  classical
  have hKreal : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hrs : (1 : ℝ) < (K : ℝ)^2 := by nlinarith
  have hcont : ContinuousOn (fun z : ℝ => z⁻¹) (Icc 1 ((K : ℝ)^2)) := by
    apply continuousOn_id.inv₀
    intro z hz
    have hz1 : 1 ≤ z := hz.1
    simpa only [id_eq] using (ne_of_gt (lt_of_lt_of_le zero_lt_one hz1))
  obtain ⟨D⟩ := exists_finiteMomentDual hrs hcont K
  let C := NormalizedFiniteSignedMomentCertificate.ofFiniteMomentDual D
  let p₀ := C.orientedPrior0 (fun z : ℝ => z⁻¹)
  let p₁ := C.orientedPrior1 (fun z : ℝ => z⁻¹)
  have hp₀ : IsProbabilityMeasure p₀ := inferInstance
  have hp₁ : IsProbabilityMeasure p₁ := inferInstance
  let s : Finset ℝ := (Set.finite_range C.node).toFinset
  have hs : (s : Set ℝ) = Set.range C.node := Set.Finite.coe_toFinset _
  have h0 : C.positivePrior (s : Set ℝ) = 1 := by
    rw [hs]
    calc
      _ = C.positivePrior Set.univ :=
        (ae_mem_iff_measure_eq
          (Set.finite_range C.node).measurableSet.nullMeasurableSet).1
          C.jordanPriors_ae_mem_range.1
      _ = 1 := measure_univ
  have h1 : C.negativePrior (s : Set ℝ) = 1 := by
    rw [hs]
    calc
      _ = C.negativePrior Set.univ :=
        (ae_mem_iff_measure_eq
          (Set.finite_range C.node).measurableSet.nullMeasurableSet).1
          C.jordanPriors_ae_mem_range.2
      _ = 1 := measure_univ
  have hs₀ : p₀ (s : Set ℝ) = 1 := by
    dsimp [p₀, NormalizedFiniteSignedMomentCertificate.orientedPrior0]
    split_ifs <;> assumption
  have hs₁ : p₁ (s : Set ℝ) = 1 := by
    dsimp [p₁, NormalizedFiniteSignedMomentCertificate.orientedPrior1]
    split_ifs <;> assumption
  have hmem : ∀ z ∈ s, 1 ≤ z ∧ z ≤ (K : ℝ)^2 := by
    intro z hz
    have hz' : z ∈ (s : Set ℝ) := hz
    rw [hs] at hz'
    obtain ⟨i, rfl⟩ := hz'
    exact D.nodes_mem i
  refine ⟨p₀, p₁, hp₀, hp₁, ⟨s, s, hs₀, hs₁, hmem, hmem⟩,
    (fun v hv => C.orientedPriors_moments_eq _ v hv), ?_⟩
  have hsep := C.orientedPrior_target_separation (fun z : ℝ => z⁻¹)
  have htarget : |∑ i, C.weight i * (C.node i)⁻¹| =
      bestUniformApproxError (fun z : ℝ => z⁻¹) 1 ((K : ℝ)^2) K :=
    D.target_abs_eq
  rw [htarget] at hsep
  change (1 / 12 : ℝ) ≤ |(∫ z, z⁻¹ ∂p₁) - (∫ z, z⁻¹ ∂p₀)|
  rw [show (∫ z, z⁻¹ ∂p₁) - (∫ z, z⁻¹ ∂p₀) =
    2 * bestUniformApproxError (fun z : ℝ => z⁻¹) 1 ((K : ℝ)^2) K from hsep]
  exact (reciprocal_best_error_lower K hK).trans (le_abs_self _)

end CausalSmith.Stat.MarRareqLogfrontier
