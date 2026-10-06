module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.PacketPositivity

/-! # Uniform weighted variation of the Jackson packet

Roadmap (18)--(19): translating the two positive kernel envelopes together
cancels their sine terms. The second Jackson moment then bounds the weight
uniformly, including the endpoint M = K².
-/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory
open scoped BigOperators

-- @node: packetKernel_periodic
/-- Fourier reconstruction gives the kernel period needed for circle translation. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hN), the [stated conclusion](goal) holds. -/
lemma packetKernel_periodic {N : ℕ} (hN : 0 < N) :
    Function.Periodic (packetKernel N) (2 * Real.pi) := by
  intro t
  change Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.kernel N
    (t + 2 * Real.pi) = Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.kernel N t
  rw [Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.kernel_fourier N hN,
    Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.kernel_fourier N hN]
  apply Finset.sum_congr rfl
  intro j hj
  exact congrArg (fun x =>
    Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson.normalizedCoeff N j * x)
      (packet_cos_periodic j t)

-- @node: packetIntensity_translate_sum
/-- The sum of the translated weights has no sine term; both centers are at z = 1. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hM), the [stated conclusion](goal) holds. -/
lemma packetIntensity_translate_sum {M : ℝ} (hM : 2 ≤ M) (t : ℝ) :
    packetIntensity M (t + Real.arccos (2 / M - 1)) +
      packetIntensity M (t - Real.arccos (2 / M - 1)) =
        2 + (M - 2) * (1 - Real.cos t) := by
  have hM0 : 0 < M := by linarith
  have hr : 2 / M ≤ 1 := (div_le_one hM0).2 hM
  have hc := Real.cos_arccos (x := 2 / M - 1)
    (by linarith [div_pos (by norm_num : (0 : ℝ) < 2) hM0]) (by linarith)
  simp only [packetIntensity, Real.cos_add, Real.cos_sub, hc]
  field_simp
  <;> ring

-- @node: packetWave_abs_le_kernels
/-- Positive kernel envelopes dominate the absolute modulated packet pointwise. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hN), the [stated conclusion](goal) holds. -/
lemma packetWave_abs_le_kernels {A₀ K : ℕ} (hN : 0 < A₀ * K) (M t : ℝ) :
    |packetWave A₀ K M t| ≤
      packetKernel (A₀ * K) (t - Real.arccos (2 / M - 1)) +
        packetKernel (A₀ * K) (t + Real.arccos (2 / M - 1)) := by
  have he (u : ℝ) : |packetOscillation (A₀ * K) u| ≤ packetKernel (A₀ * K) u := by
    have hn : 0 ≤ packetKernel (A₀ * K) u :=
      mul_nonneg (by positivity)
        (Causalean.Mathlib.Analysis.JacksonApproximation.jackson_nonneg _ hN u)
    rw [packetOscillation, abs_mul, abs_of_nonneg hn]
    exact mul_le_of_le_one_right hn (Real.abs_cos_le_one _)
  exact (abs_add_le _ _).trans (add_le_add (he _) (he _))

-- @node: packetKernel_weight_translate
/-- A translated weighted kernel integral can be moved back to its center. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hN), the [stated conclusion](goal) holds. -/
lemma packetKernel_weight_translate {N : ℕ} (hN : 0 < N) (M θ : ℝ) :
    (∫ t in Set.Icc (-Real.pi) Real.pi,
      (1 + packetIntensity M t) * packetKernel N (t - θ) / (2 * Real.pi)) =
    ∫ t in Set.Icc (-Real.pi) Real.pi,
      (1 + packetIntensity M (t + θ)) * packetKernel N t / (2 * Real.pi) := by
  let f := fun t => (1 + packetIntensity M (t + θ)) * packetKernel N t / (2 * Real.pi)
  have hp : Function.Periodic f (2 * Real.pi) := by
    intro t
    dsimp [f]
    rw [packetKernel_periodic hN t]
    unfold packetIntensity
    rw [show t + 2 * Real.pi + θ = (t + θ) + 2 * Real.pi by ring,
      Real.cos_add_two_pi]
  convert packet_periodic_integral_translate f hp θ using 1 <;>
    simp [f]

-- @node: packetWeight_le
/-- The normalizing weighted variation is universally bounded throughout the paper's full range. This is roadmap (19), with the explicit constant 36. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hA,hK,hM,hMhi), the [stated conclusion](goal) holds. -/
lemma packetWeight_le {A₀ K : ℕ} (hA : 1 ≤ A₀) (hK : 2 ≤ K)
    {M : ℝ} (hM : 2 ≤ M) (hMhi : M ≤ (K : ℝ) ^ 2) :
    packetWeight A₀ K M ≤ 36 := by
  let N := A₀ * K
  let θ := Real.arccos (2 / M - 1)
  have hN : 0 < N := by dsimp [N]; nlinarith
  have hc : Continuous (packetKernel N) := by unfold packetKernel; fun_prop
  have hi (s : ℝ) : IntegrableOn (fun t =>
      (1 + packetIntensity M t) * packetKernel N (t - s) / (2 * Real.pi))
      (Set.Icc (-Real.pi) Real.pi) :=
    (by fun_prop : Continuous (fun t =>
      (1 + packetIntensity M t) * packetKernel N (t - s) / (2 * Real.pi))).continuousOn.integrableOn_compact isCompact_Icc
  have hj (s : ℝ) : IntegrableOn (fun t =>
      (1 + packetIntensity M (t + s)) * packetKernel N t / (2 * Real.pi))
      (Set.Icc (-Real.pi) Real.pi) :=
    (by fun_prop : Continuous (fun t =>
      (1 + packetIntensity M (t + s)) * packetKernel N t / (2 * Real.pi))).continuousOn.integrableOn_compact isCompact_Icc
  have hf : IntegrableOn (fun t =>
      (1 + packetIntensity M t) * |packetWave A₀ K M t| / (2 * Real.pi))
      (Set.Icc (-Real.pi) Real.pi) :=
    (by fun_prop : Continuous (fun t =>
      (1 + packetIntensity M t) * |packetWave A₀ K M t| / (2 * Real.pi))).continuousOn.integrableOn_compact isCompact_Icc
  have he : packetWeight A₀ K M ≤
      ∫ t in Set.Icc (-Real.pi) Real.pi,
        (4 + (M - 2) * (1 - Real.cos t)) *
          Causalean.Mathlib.Analysis.JacksonApproximation.jackson N t := by
    calc
      _ ≤ ∫ t in Set.Icc (-Real.pi) Real.pi,
          ((1 + packetIntensity M t) * packetKernel N (t - θ) / (2 * Real.pi) +
           (1 + packetIntensity M t) * packetKernel N (t - (-θ)) / (2 * Real.pi)) := by
        apply integral_mono hf ((hi θ).add (hi (-θ)))
        intro t
        have hz := (packetIntensity_mem_Icc (by linarith : 0 ≤ M) t).1
        have hw := packetWave_abs_le_kernels hN M t
        dsimp [N, θ] at *
        simpa only [sub_neg_eq_add, ← add_div, ← mul_add] using
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hw (by linarith))
            (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
      _ = _ := by
        rw [integral_add (hi θ) (hi (-θ)),
          packetKernel_weight_translate hN M θ, packetKernel_weight_translate hN M (-θ),
          ← integral_add (hj θ) (hj (-θ))]
        apply integral_congr_ae
        filter_upwards with t
        have hs := packetIntensity_translate_sum hM t
        dsimp [θ] at *
        simp only [← sub_eq_add_neg] at *
        unfold packetKernel
        have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
        have halg (a b j : ℝ) : a * (2 * Real.pi * j) / (2 * Real.pi) +
            b * (2 * Real.pi * j) / (2 * Real.pi) = (a + b) * j := by
          field_simp
          <;> ring
        rw [halg]
        congr 1
        linarith [hs]
  have hm := Causalean.Mathlib.Analysis.JacksonApproximation.jackson_second_moment N hN
  have hu := Causalean.Mathlib.Analysis.JacksonApproximation.jackson_integral_eq_one N hN
  have hbound : (∫ t in Set.Icc (-Real.pi) Real.pi,
      (4 + (M - 2) * (1 - Real.cos t)) *
        Causalean.Mathlib.Analysis.JacksonApproximation.jackson N t) ≤
      4 + 32 * (M - 2) / (N : ℝ) ^ 2 := by
    calc
      _ ≤ ∫ t in Set.Icc (-Real.pi) Real.pi,
          (4 + (M - 2) * (t ^ 2 / 2)) *
            Causalean.Mathlib.Analysis.JacksonApproximation.jackson N t := by
        apply integral_mono
          ((by fun_prop : Continuous (fun t => (4 + (M - 2) * (1 - Real.cos t)) *
            Causalean.Mathlib.Analysis.JacksonApproximation.jackson N t)).continuousOn.integrableOn_compact isCompact_Icc)
          ((by fun_prop : Continuous (fun t => (4 + (M - 2) * (t ^ 2 / 2)) *
            Causalean.Mathlib.Analysis.JacksonApproximation.jackson N t)).continuousOn.integrableOn_compact isCompact_Icc)
        intro t
        apply mul_le_mul_of_nonneg_right ?_
          (Causalean.Mathlib.Analysis.JacksonApproximation.jackson_nonneg N hN t)
        have hcos := Real.one_sub_sq_div_two_le_cos (x := t)
        nlinarith
      _ = 4 + ((M - 2) / 2) * (∫ t in Set.Icc (-Real.pi) Real.pi,
          t ^ 2 * Causalean.Mathlib.Analysis.JacksonApproximation.jackson N t) := by
        simp_rw [show ∀ t : ℝ, (4 + (M - 2) * (t ^ 2 / 2)) *
            Causalean.Mathlib.Analysis.JacksonApproximation.jackson N t =
            4 * Causalean.Mathlib.Analysis.JacksonApproximation.jackson N t +
            ((M - 2) / 2) * (t ^ 2 * Causalean.Mathlib.Analysis.JacksonApproximation.jackson N t) by intro t; ring]
        rw [integral_add, integral_const_mul, integral_const_mul, hu]
        · ring
        · exact ((by fun_prop : Continuous (fun t : ℝ =>
            4 * Causalean.Mathlib.Analysis.JacksonApproximation.jackson N t)).continuousOn.integrableOn_compact isCompact_Icc)
        · exact ((by fun_prop : Continuous (fun t : ℝ => ((M - 2) / 2) *
            (t ^ 2 * Causalean.Mathlib.Analysis.JacksonApproximation.jackson N t))).continuousOn.integrableOn_compact isCompact_Icc)
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left hm (show 0 ≤ (M - 2) / 2 by positivity)
        convert add_le_add_left hh 4 using 1 <;> first | rfl | ring
  have hNK : (K : ℝ) ≤ N := by dsimp [N]; exact_mod_cast (show K ≤ A₀ * K by nlinarith)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hratio : (M - 2) / (N : ℝ) ^ 2 ≤ 1 := by
    apply (div_le_one (by positivity : (0 : ℝ) < (N : ℝ) ^ 2)).2
    nlinarith [sq_nonneg ((N : ℝ) - K)]
  have hh := mul_le_mul_of_nonneg_left hratio (by norm_num : (0 : ℝ) ≤ 32)
  have := he.trans hbound
  rw [mul_div_assoc] at this
  linarith

end CausalSmith.Stat.OptvalueVanishingoverlapRate
