module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.CenterMass
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.Fourier

/-!
# Center size of the Jackson antiderivative packet

At the center all cosine modes align, so the antiderivative has a uniform
lower and upper bound proportional to the reciprocal of its order.
-/

public section

namespace Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson

/-- [There are positive constants c and C, with c at most C, such that for every order N at least
two the absolute value of the packet antiderivative at angle zero lies between c / N and C /
N](goal). -/
theorem packet_center_bounds :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ N : ℕ, 2 ≤ N →
        c / (N : ℝ) ≤ |packetAntideriv N 0| ∧
        |packetAntideriv N 0| ≤ C / (N : ℝ) := by
  refine ⟨1 / 72, 1 / 2, by norm_num, by norm_num, ?_⟩
  intro N hN
  let s : Finset ℤ := Finset.Icc (-((2 * N - 2 : ℕ) : ℤ)) ((2 * N - 2 : ℕ) : ℤ)
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hnorm (j : ℤ) : 0 ≤ normalizedCoeff N j := by
    unfold normalizedCoeff convolution
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro k hk
      exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · exact le_of_lt (convolution_zero_pos N (by omega))
  have hfreq (j : ℤ) (hj : j ∈ s) :
      2 * (N : ℝ) ≤ 4 * (N : ℝ) + (j : ℝ) ∧
      4 * (N : ℝ) + (j : ℝ) ≤ 6 * (N : ℝ) ∧
      2 * (N : ℝ) ≤ 4 * (N : ℝ) - (j : ℝ) ∧
      4 * (N : ℝ) - (j : ℝ) ≤ 6 * (N : ℝ) := by
    have hj' : -((2 * N - 2 : ℕ) : ℤ) ≤ j ∧
        j ≤ ((2 * N - 2 : ℕ) : ℤ) := Finset.mem_Icc.mp hj
    have hsub : 2 * N - 2 ≤ 2 * N := Nat.sub_le _ _
    have hlo : -(2 * (N : ℤ)) ≤ j := by omega
    have hhi : j ≤ 2 * (N : ℤ) := by omega
    have hlo' : -(2 * (N : ℝ)) ≤ (j : ℝ) := by exact_mod_cast hlo
    have hhi' : (j : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hhi
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  have hrec (j : ℤ) (hj : j ∈ s) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
      1 / (36 * (N : ℝ) ^ 2) ≤ reciprocalSquare N σ j ∧
      reciprocalSquare N σ j ≤ 1 / (4 * (N : ℝ) ^ 2) := by
    obtain ⟨hp1, hp2, hm1, hm2⟩ := hfreq j hj
    have hp0 : 0 < 4 * (N : ℝ) + (j : ℝ) := by linarith
    have hm0 : 0 < 4 * (N : ℝ) - (j : ℝ) := by linarith
    rcases hσ with rfl | rfl
    · unfold reciprocalSquare
      simp only [one_mul]
      constructor
      · apply one_div_le_one_div_of_le (by positivity)
        nlinarith [mul_nonneg (show 0 ≤ 6 * (N : ℝ) - (4 * (N : ℝ) + (j : ℝ)) by linarith)
          (show 0 ≤ 6 * (N : ℝ) + (4 * (N : ℝ) + (j : ℝ)) by linarith)]
      · apply one_div_le_one_div_of_le (by positivity)
        nlinarith [mul_nonneg (show 0 ≤ (4 * (N : ℝ) + (j : ℝ)) - 2 * (N : ℝ) by linarith)
          (show 0 ≤ (4 * (N : ℝ) + (j : ℝ)) + 2 * (N : ℝ) by linarith)]
    · unfold reciprocalSquare
      simp only [neg_mul, one_mul]
      constructor
      · apply one_div_le_one_div_of_le (by positivity)
        nlinarith [mul_nonneg (show 0 ≤ 6 * (N : ℝ) - (4 * (N : ℝ) - (j : ℝ)) by linarith)
          (show 0 ≤ 6 * (N : ℝ) + (4 * (N : ℝ) - (j : ℝ)) by linarith)]
      · apply one_div_le_one_div_of_le (by positivity)
        nlinarith [mul_nonneg (show 0 ≤ (4 * (N : ℝ) - (j : ℝ)) - 2 * (N : ℝ) by linarith)
          (show 0 ≤ (4 * (N : ℝ) - (j : ℝ)) + 2 * (N : ℝ) by linarith)]
  have hterm (j : ℤ) (hj : j ∈ s) :
      normalizedCoeff N j * (1 / (18 * (N : ℝ) ^ 2)) ≤
        packetCoeffPlus N j + packetCoeffMinus N j ∧
      packetCoeffPlus N j + packetCoeffMinus N j ≤
        normalizedCoeff N j * (1 / (2 * (N : ℝ) ^ 2)) := by
    obtain ⟨hpL, hpU⟩ := hrec j hj 1 (Or.inl rfl)
    obtain ⟨hmL, hmU⟩ := hrec j hj (-1) (Or.inr rfl)
    have ha := hnorm j
    simp only [packetCoeffPlus, packetCoeffMinus, weightedCoeff]
    constructor
    · calc
        _ = normalizedCoeff N j * (1 / (36 * (N : ℝ) ^ 2)) +
              normalizedCoeff N j * (1 / (36 * (N : ℝ) ^ 2)) := by ring
        _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hpL ha)
          (mul_le_mul_of_nonneg_left hmL ha)
    · calc
        _ ≤ normalizedCoeff N j * (1 / (4 * (N : ℝ) ^ 2)) +
              normalizedCoeff N j * (1 / (4 * (N : ℝ) ^ 2)) :=
          add_le_add (mul_le_mul_of_nonneg_left hpU ha)
            (mul_le_mul_of_nonneg_left hmU ha)
        _ = _ := by ring
  have hmass : (∑ j ∈ s, normalizedCoeff N j) =
      ∑' j : ℤ, |normalizedCoeff N j| := by
    rw [tsum_eq_sum (s := s)]
    · simp_rw [abs_of_nonneg (hnorm _)]
    · intro j hj
      have hfar : ((2 * N - 2 : ℕ) : ℤ) < |j| := by
        simp only [s, Finset.mem_Icc] at hj
        rcases le_total j 0 with h | h
        · rw [abs_of_nonpos h]; omega
        · rw [abs_of_nonneg h]; omega
      simp [normalizedCoeff_support N j hfar]
  have hsumL : (∑ j ∈ s, normalizedCoeff N j * (1 / (18 * (N : ℝ) ^ 2))) ≤
      ∑ j ∈ s, (packetCoeffPlus N j + packetCoeffMinus N j) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hterm j hj).1
  have hsumU : (∑ j ∈ s, (packetCoeffPlus N j + packetCoeffMinus N j)) ≤
      ∑ j ∈ s, normalizedCoeff N j * (1 / (2 * (N : ℝ) ^ 2)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact (hterm j hj).2
  have hsum0 : 0 ≤ ∑ j ∈ s, (packetCoeffPlus N j + packetCoeffMinus N j) := by
    apply Finset.sum_nonneg
    intro j hj
    exact le_trans (mul_nonneg (hnorm j) (by positivity)) (hterm j hj).1
  have hcenter : |packetAntideriv N 0| =
      (1 / 2 : ℝ) * ∑ j ∈ s, (packetCoeffPlus N j + packetCoeffMinus N j) := by
    simp only [packetAntideriv, mul_zero, Real.cos_zero, mul_one]
    change |-(1 / 2 : ℝ) * (∑ j ∈ s,
      (packetCoeffPlus N j + packetCoeffMinus N j))| = _
    rw [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
      abs_of_nonneg hsum0]
  rw [hcenter]
  have hmL := normalizedCoeff_l1_lower N hN
  have hmU := normalizedCoeff_l1 N (by omega)
  rw [← hmass] at hmL hmU
  rw [← Finset.sum_mul] at hsumL hsumU
  constructor
  · calc
      (1 / 72 : ℝ) / N ≤ (1 / 2 : ℝ) *
          ((∑ j ∈ s, normalizedCoeff N j) * (1 / (18 * (N : ℝ) ^ 2))) := by
        calc
          _ = (1 / 2 : ℝ) * ((N / 2) * (1 / (18 * (N : ℝ) ^ 2))) := by
            field_simp
            ring
          _ ≤ _ := by
            gcongr
      _ ≤ _ := mul_le_mul_of_nonneg_left hsumL (by norm_num)
  · calc
      _ ≤ (1 / 2 : ℝ) *
          ((∑ j ∈ s, normalizedCoeff N j) * (1 / (2 * (N : ℝ) ^ 2))) :=
        mul_le_mul_of_nonneg_left hsumU (by norm_num)
      _ ≤ (1 / 2 : ℝ) / N := by
        calc
          _ ≤ (1 / 2 : ℝ) * ((2 * N) * (1 / (2 * (N : ℝ) ^ 2))) := by
            gcongr
          _ = _ := by
            field_simp

end Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson

