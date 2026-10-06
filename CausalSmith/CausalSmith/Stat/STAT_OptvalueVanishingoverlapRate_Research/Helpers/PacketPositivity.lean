module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.PacketLowerOrder

/-! # Strict positivity of the explicit packet normalization

Nonnegative Fourier coefficients, including a strictly positive coefficient at
frequency one, make the Jackson kernel strictly maximal at its center. The
other translated wave therefore cannot cancel the centered wave at the kink.
Continuity then gives strictly positive weighted variation.
-/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory
open scoped BigOperators

-- @node: packetNormalizedCoeff_nonneg
/-- Every normalized Jackson coefficient is nonnegative. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma packetNormalizedCoeff_nonneg (N : ℕ) (j : ℤ) :
    0 ≤ Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.normalizedCoeff N j := by
  unfold Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.normalizedCoeff
  apply div_nonneg <;>
    unfold Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.convolution <;>
    apply Finset.sum_nonneg <;> intros <;>
    unfold Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.triangle <;>
    positivity

-- @node: packetNormalizedCoeff_one_pos
/-- At order at least two, the frequency-one coefficient is strictly positive. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hN), the [stated conclusion](goal) holds. -/
lemma packetNormalizedCoeff_one_pos {N : ℕ} (hN : 2 ≤ N) :
    0 < Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.normalizedCoeff N 1 := by
  open Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson in
  apply div_pos ?_ (convolution_zero_pos N (by omega))
  unfold Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.convolution
  apply Finset.sum_pos'
  · intro j hj
    unfold triangle
    positivity
  · refine ⟨0, by simp, ?_⟩
    simp only [triangle, Int.natAbs_zero, Nat.sub_zero, sub_zero, Int.natAbs_one]
    have h0 : 0 < N := by omega
    have h1 : 0 < N - 1 := by omega
    exact mul_pos (by exact_mod_cast h0) (by exact_mod_cast h1)

-- @node: packetKernel_lt_center
/-- A cosine strictly below one forces a strict drop from the kernel's center. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hN,hu), the [stated conclusion](goal) holds. -/
lemma packetKernel_lt_center {N : ℕ} (hN : 2 ≤ N) {u : ℝ}
    (hu : Real.cos u < 1) : packetKernel N u < packetKernel N 0 := by
  open Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson in
  have hN0 : 0 < N := by omega
  change kernel N u < kernel N 0
  rw [kernel_fourier N hN0 u, kernel_fourier N hN0 0]
  simp only [mul_zero, Real.cos_zero, mul_one]
  apply Finset.sum_lt_sum
  · intro j hj
    exact mul_le_of_le_one_right (packetNormalizedCoeff_nonneg N j) (Real.cos_le_one _)
  · refine ⟨1, ?_, ?_⟩
    · simp only [Finset.mem_Icc]
      constructor <;> omega
    · simpa using mul_lt_of_lt_one_right (packetNormalizedCoeff_one_pos hN) hu

-- @node: packetWave_at_kink_pos
/-- At the kink, the centered wave dominates the other translated wave. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hA,hK,hM), the [stated conclusion](goal) holds. -/
lemma packetWave_at_kink_pos {A₀ K : ℕ} (hA : 1 ≤ A₀) (hK : 2 ≤ K)
    {M : ℝ} (hM : 2 ≤ M) :
    0 < packetWave A₀ K M (Real.arccos (2 / M - 1)) := by
  let θ := Real.arccos (2 / M - 1)
  have hM0 : 0 < M := by linarith
  have hratio : 0 < 2 / M := div_pos (by norm_num) hM0
  have hratio_le : 2 / M ≤ 1 := (div_le_one hM0).2 hM
  have hcos : Real.cos θ = 2 / M - 1 :=
    Real.cos_arccos (by linarith) (by linarith)
  have hcos2 : Real.cos (2 * θ) < 1 := by
    rw [Real.cos_two_mul, hcos]
    nlinarith
  have hN : 2 ≤ A₀ * K := by nlinarith
  have hdrop := packetKernel_lt_center hN hcos2
  have hker : 0 ≤ packetKernel (A₀ * K) (2 * θ) := by
    unfold packetKernel
    exact mul_nonneg (by positivity)
      (Causalean.Mathlib.Analysis.JacksonApproximation.jackson_nonneg _ (by omega) _)
  have hw : -packetKernel (A₀ * K) (2 * θ) ≤ packetOscillation (A₀ * K) (2 * θ) := by
    unfold packetOscillation
    simpa using mul_le_mul_of_nonneg_left
      (Real.neg_one_le_cos (4 * (↑(A₀ * K) : ℝ) * (2 * θ))) hker
  change 0 < packetOscillation (A₀ * K) (θ - θ) + packetOscillation (A₀ * K) (θ + θ)
  rw [sub_self, show θ + θ = 2 * θ by ring]
  simp only [packetOscillation, mul_zero, Real.cos_zero, mul_one] at *
  linarith

-- @node: packetWeight_pos
/-- The explicit packet weight is positive throughout the paper's support range. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hA,hK,hM), the [stated conclusion](goal) holds. -/
lemma packetWeight_pos {A₀ K : ℕ} (hA : 1 ≤ A₀) (hK : 2 ≤ K)
    {M : ℝ} (hM : 2 ≤ M) : 0 < packetWeight A₀ K M := by
  let f : ℝ → ℝ := fun t =>
    (1 + packetIntensity M t) * |packetWave A₀ K M t| / (2 * Real.pi)
  have hf : Continuous f := by
    dsimp [f]
    fun_prop
  have hnonneg (t : ℝ) : 0 ≤ f t := by
    have hz := (packetIntensity_mem_Icc (by linarith : 0 ≤ M) t).1
    dsimp [f]
    exact div_nonneg (mul_nonneg (by linarith) (abs_nonneg _)) (by positivity)
  have hpos : 0 < f (Real.arccos (2 / M - 1)) := by
    have hz := (packetIntensity_mem_Icc (by linarith : 0 ≤ M)
      (Real.arccos (2 / M - 1))).1
    have hw := packetWave_at_kink_pos hA hK hM
    dsimp [f]
    exact div_pos (mul_pos (by linarith) (abs_pos.mpr (ne_of_gt hw))) (by positivity)
  have hi := intervalIntegral.integral_pos (by linarith [Real.pi_pos] : -Real.pi < Real.pi)
    hf.continuousOn (fun t _ => hnonneg t)
    ⟨Real.arccos (2 / M - 1),
      ⟨by linarith [Real.arccos_nonneg (2 / M - 1), Real.pi_pos],
        Real.arccos_le_pi _⟩, hpos⟩
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    ← integral_Icc_eq_integral_Ioc] at hi
  exact hi

end CausalSmith.Stat.OptvalueVanishingoverlapRate
