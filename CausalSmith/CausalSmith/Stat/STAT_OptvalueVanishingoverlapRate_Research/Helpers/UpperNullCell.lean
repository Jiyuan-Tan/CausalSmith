module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperJacksonOscillation
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperPilotMoments

/-! # Null-cell Jackson bias

The null-cell case following roadmap equation (11) uses the quadratic cosine
displacement at the lower corner and the kernel's second moment. No inverse
arm mass is introduced. The bound applies to the exact factorial mean.
-/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory
open Causalean.Mathlib.Analysis.JacksonApproximation
open Causalean.Mathlib.Analysis.Approximation.Chebyshev
open scoped BigOperators


-- @node: nullCorner_affine_cos_bounds
/-- At a zero lower corner, each displaced coordinate has a quadratic envelope. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hr), the [stated conclusion](goal) holds. -/
lemma nullCorner_affine_cos_bounds (r u : Fin 4 → ℝ) (hr : ∀ j, 0 ≤ r j)
    (j : Fin 4) :
    0 ≤ affinePoint r r (cosPoint ((fun _ => Real.pi) - u)) j ∧
      affinePoint r r (cosPoint ((fun _ => Real.pi) - u)) j ≤ r j / 2 * (u j) ^ 2 := by
  have he : affinePoint r r (cosPoint ((fun _ => Real.pi) - u)) j =
      r j * (1 - Real.cos (u j)) := by
    simp only [affinePoint, cosPoint, Pi.sub_apply, Real.cos_sub,
      Real.cos_pi, Real.sin_pi, neg_one_mul, zero_mul, add_zero]
    ring
  rw [he]
  constructor
  · exact mul_nonneg (hr j) (sub_nonneg.mpr (Real.cos_le_one _))
  · have h := mul_le_mul_of_nonneg_left
      (show 1 - Real.cos (u j) ≤ (u j) ^ 2 / 2 by
        linarith [Real.one_sub_sq_div_two_le_cos (x := u j)]) (hr j)
    nlinarith

/-- The Jackson convolution at a zero lower corner is controlled solely by the second kernel moment, including when the target functional has a tie. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hε,hK,hr), the [stated conclusion](goal) holds. -/
lemma nullCorner_tensorConvolution_le (ε : ℝ) (hε : 0 < ε)
    (K : ℕ) (hK : 0 < K) (r : Fin 4 → ℝ) (hr : ∀ j, 0 < r j) :
    |tensorConvolution K (fun z => armwiseExtensionFormula ε (affinePoint r r z))
      (fun _ => Real.pi)| ≤ 32 * (∑ j, r j) / (K : ℝ) ^ 2 := by
  have hQ : ∀ v ∈ centeredRectangle r r, ∀ j, 0 ≤ v j := by
    intro v hv j
    have h := (abs_le.mp (hv j)).1
    linarith
  have haff : Continuous (affinePoint r r) := by unfold affinePoint; fun_prop
  have hf : ContinuousOn (fun z => armwiseExtensionFormula ε (affinePoint r r z))
      (normalizedCube 4) :=
    (armwise_continuousOn_rectangle ε hε r r hr hQ).comp haff.continuousOn
      (fun z hz => affinePoint_mem_centeredRectangle r r z hr hz)
  have hc : Continuous (fun u : Fin 4 → ℝ =>
      armwiseExtensionFormula ε (affinePoint r r (cosPoint ((fun _ => Real.pi) - u)))) := by
    apply hf.comp_continuous
    · unfold cosPoint; fun_prop
    · exact fun u => cosPoint_mem_normalizedCube _
  have hk : Continuous (tensorJackson K 4) := by unfold tensorJackson; fun_prop
  have hcompact : IsCompact (periodBox 4) := isCompact_pi_infinite fun _ => isCompact_Icc
  have hi : IntegrableOn (fun u : Fin 4 → ℝ => armwiseExtensionFormula ε
      (affinePoint r r (cosPoint ((fun _ => Real.pi) - u))) * tensorJackson K 4 u)
      (periodBox 4) := (hc.mul hk).continuousOn.integrableOn_compact hcompact
  have hj (j : Fin 4) : IntegrableOn
      (fun u => r j / 2 * ((u j) ^ 2 * tensorJackson K 4 u)) (periodBox 4) := by
    have hcont : Continuous (fun u : Fin 4 → ℝ =>
        r j / 2 * ((u j) ^ 2 * tensorJackson K 4 u)) := by fun_prop
    exact hcont.continuousOn.integrableOn_compact hcompact
  unfold tensorConvolution
  calc
    _ ≤ ∫ u in periodBox 4, |armwiseExtensionFormula ε
        (affinePoint r r (cosPoint ((fun _ => Real.pi) - u))) * tensorJackson K 4 u| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ u in periodBox 4, ∑ j, r j / 2 * ((u j) ^ 2 * tensorJackson K 4 u) := by
      apply setIntegral_mono hi.abs (integrable_finsetSum _ (fun j _ => hj j))
      intro u
      dsimp only
      have hF := armwiseExtension_nonneg_le_totalMassVec hε
        (fun j => (nullCorner_affine_cos_bounds r u (fun j => (hr j).le) j).1)
      rw [abs_mul, abs_of_nonneg hF.1, abs_of_nonneg (tensorJackson_nonneg hK u),
        ]
      simp_rw [← mul_assoc]
      rw [← Finset.sum_mul]
      apply mul_le_mul_of_nonneg_right _ (tensorJackson_nonneg hK u)
      apply hF.2.trans
      rw [totalMassVec_eq_sum_coordinates]
      exact Finset.sum_le_sum fun j _ =>
        (nullCorner_affine_cos_bounds r u (fun j => (hr j).le) j).2
    _ = ∑ j, r j / 2 * (∫ u in periodBox 4, (u j) ^ 2 * tensorJackson K 4 u) := by
      rw [integral_finsetSum _ (fun j _ => hj j)]
      simp only [integral_const_mul]
    _ ≤ ∑ j, r j / 2 * (64 / (K : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (div_nonneg (hr j).le (by norm_num))
      exact (tensorJackson_second_moment_eq hK j).le.trans (jackson_second_moment K hK)
    _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_div]; ring

/-- The exact coefficient expression used by the factorial mean has the null-cell second-order bias bound; polynomial uniqueness and convolution evaluation link the bound to the estimator's chosen polynomial. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hε,hK,hr), the [stated conclusion](goal) holds. -/
lemma nullCorner_jacksonCoeff_mean_le (ε : ℝ) (hε : 0 < ε)
    (K : ℕ) (hK : 0 < K) (r : Fin 4 → ℝ) (hr : ∀ j, 0 < r j) :
    |armwiseExtensionFormula ε r + ∑ α : Fin 4 → Fin (2 * (K - 1) + 1),
      jacksonCoeff ε K r r α * ∏ j, (-1 : ℝ) ^ (α j).val| ≤
      32 * (∑ j, r j) / (K : ℝ) ^ 2 := by
  have hQ : ∀ v ∈ centeredRectangle r r, ∀ j, 0 ≤ v j := by
    intro v hv j
    have h := (abs_le.mp (hv j)).1
    linarith
  rw [jacksonCoeff_sum_eq_eval ε hε K hK r r hr hQ]
  have hcos : cosPoint (fun _ : Fin 4 => Real.pi) = (fun _ => (-1 : ℝ)) := by
    funext j
    simp [cosPoint]
  rw [← hcos, jacksonPolynomialPair_cos_eval ε hε K hK r r hr hQ]
  exact nullCorner_tensorConvolution_le ε hε K hK r hr

/-- Zero pilot counts put the midpoint exactly one radius above the origin. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hH,hm,hL), the [stated conclusion](goal) holds. -/
lemma zeroPilot_midpoint_eq_radius (H : ℝ) (hH : 0 < H) (m L : ℝ)
    (hm : 0 < m) (hL : 0 ≤ L) :
    pilotMidpoint H hH m L (fun _ => 0) = pilotRadiusFormula H hH m L (fun _ => 0) ∧
      ∀ j, pilotRadiusFormula H hH m L (fun _ => 0) j = H * (L / m) / 2 := by
  have hh : 0 ≤ H * (L / m) := by positivity
  constructor
  · funext j
    simp [pilotMidpoint, pilotRadiusFormula, pilotLower, pilotUpperFormula, pilotCenterFormula,
      pilotHalfWidthFormula, max_eq_left (neg_nonpos.mpr hh)]
  · intro j
    simp [pilotRadiusFormula, pilotLower, pilotUpperFormula, pilotCenterFormula,
      pilotHalfWidthFormula, max_eq_left (neg_nonpos.mpr hh)]

/-- The actual zero-count pilot's factorial mean obeys the null-cell bias bound preceding equation (20), with no division by any cell or arm mass. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hH,hm,hL,hε,hK), the [stated conclusion](goal) holds. -/
lemma zeroPilot_jacksonCoeff_mean_le (H : ℝ) (hH : 0 < H) (m L : ℝ)
    (hm : 0 < m) (hL : 0 < L) (ε : ℝ) (hε : 0 < ε)
    (K : ℕ) (hK : 0 < K) :
    let b := pilotMidpoint H hH m L (fun _ => 0)
    let r := pilotRadiusFormula H hH m L (fun _ => 0)
    |(armwiseExtensionFormula ε b + ∑ α : Fin 4 → Fin (2 * (K - 1) + 1),
      jacksonCoeff ε K b r α * ∏ j, ((0 - b j) / r j) ^ (α j).val) -
      armwiseExtensionFormula ε 0| ≤ 64 * H * L / (m * (K : ℝ) ^ 2) := by
  obtain ⟨he, hr⟩ := zeroPilot_midpoint_eq_radius H hH m L hm hL.le
  dsimp only
  rw [he]
  have hp := pilotRadius_pos H hH m L hm hL (fun _ => 0)
  have hz : armwiseExtensionFormula ε 0 = 0 := by simp [armwiseExtensionFormula]
  simp only [zero_sub, neg_div, div_self (ne_of_gt (hp _)), hz, sub_zero]
  have hb := nullCorner_jacksonCoeff_mean_le ε hε K hK
    (pilotRadiusFormula H hH m L (fun _ => 0)) hp
  apply hb.trans_eq
  simp only [hr, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- Logarithmic degree calibration gives the null-cell instance of (20). The sole inverse-overlap term is the linear normalized scale. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hH,hm,hL,hε,hε1,hK,hκ,hdegree), the [stated conclusion](goal) holds. -/
lemma zeroPilot_jacksonCoeff_mean_normalized_le (H : ℝ) (hH : 0 < H) (m L : ℝ)
    (hm : 0 < m) (hL : 0 < L) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (K : ℕ) (hK : 0 < K) (κ : ℝ) (hκ : 0 < κ) (hdegree : κ * L ≤ K) :
    let b := pilotMidpoint H hH m L (fun _ => 0)
    let r := pilotRadiusFormula H hH m L (fun _ => 0)
    |(armwiseExtensionFormula ε b + ∑ α : Fin 4 → Fin (2 * (K - 1) + 1),
      jacksonCoeff ε K b r α * ∏ j, ((0 - b j) / r j) ^ (α j).val) -
      armwiseExtensionFormula ε 0| ≤ (64 * H / κ ^ 2) * (1 / (m * ε * L)) := by
  have hsq := pow_le_pow_left₀ (mul_pos hκ hL).le hdegree 2
  have hKreal : (0 : ℝ) < K := by exact_mod_cast hK
  have he : L / (K : ℝ) ^ 2 ≤ 1 / (κ ^ 2 * L) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hKreal) (mul_pos (sq_pos_of_pos hκ) hL)).2
    nlinarith
  have hover : 1 / (m * L) ≤ 1 / (m * ε * L) := by
    apply one_div_le_one_div_of_le (mul_pos (mul_pos hm hε) hL)
    nlinarith [mul_le_mul_of_nonneg_left hε1 (mul_pos hm hL).le]
  apply (zeroPilot_jacksonCoeff_mean_le H hH m L hm hL ε hε K hK).trans
  calc
    64 * H * L / (m * (K : ℝ) ^ 2) = (64 * H / m) * (L / (K : ℝ) ^ 2) := by ring
    _ ≤ (64 * H / m) * (1 / (κ ^ 2 * L)) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = (64 * H / κ ^ 2) * (1 / (m * L)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hover (by positivity)

end CausalSmith.Stat.OptvalueVanishingoverlapRate
