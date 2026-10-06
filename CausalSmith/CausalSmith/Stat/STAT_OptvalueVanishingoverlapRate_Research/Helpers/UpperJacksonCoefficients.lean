module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperDegreeCalibration
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperJacksonOscillation
public import Causalean.Stat.Concentration.BoundedVariation.TensorCoefficient

/-! # Jackson coefficient and localized second-moment bounds

The centered Jackson polynomial's cube oscillation yields the explicit
Chebyshev coefficient envelope (14). Combining it with the localized Poisson
factorial bound proves (26) and the clipping second-moment bound (28), with
no assumed coefficient envelope.
-/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Analysis.JacksonApproximation
open Causalean.Mathlib.Analysis.Approximation.Chebyshev
open Causalean.Stat.Concentration.BoundedVariation
open scoped BigOperators


-- @node: cubePolynomial_coeff_sum_le
/-- A four-variable polynomial bounded on the cube has the sharp tensor Chebyshev coefficient envelope. Specializing the library's path result to a constant path gives a scalar bound with no variation term. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hK,hB,hdeg,hb), the [stated conclusion](goal) holds. -/
lemma cubePolynomial_coeff_sum_le {K : ℕ} (hK : 0 < K)
    (p : MvPolynomial (Fin 4) ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hdeg : ∀ i, p.degreeOf i ≤ 2 * (K - 1))
    (hb : ∀ z ∈ normalizedCube 4, |MvPolynomial.eval z p| ≤ B) :
    (∑ α : Fin 4 → Fin (2 * (K - 1) + 1), |tensorCoeffs p α|) ≤
      16 * (↑(2 * (K - 1) + 1) : ℝ) ^ 4 *
        (1 + Real.sqrt 2) ^ (4 * (2 * (K - 1))) * B := by
  have hvar (v : ℝ) : eVariationOn (fun _ : Time => v) Set.univ = 0 :=
    (eVariationOn.eq_zero_iff _).mpr (by intros; simp)
  have hsize (v : ℝ) : pathSize (ContinuousMap.const Time v) = |v| := by
    simp only [pathSize, pathTV]
    rw [show (ContinuousMap.const Time v : Time → ℝ) = (fun _ => v) from rfl,
      hvar, ENNReal.toReal_zero, add_zero]
    simp [ContinuousMap.norm_eq_iSup_norm]
  have he := tensorCoefficientPath_four_chebyshev_size_envelope hK
    (fun _ => p) B hB (fun _ => hdeg) (fun _ => continuous_const)
    (fun _ _ => continuous_const) (by
      intro z hz
      change eVariationOn (fun _ : Time => MvPolynomial.eval z p) Set.univ < ⊤
      rw [hvar]
      exact ENNReal.zero_lt_top) (by
      intro z hz
      change pathSize (ContinuousMap.const Time (MvPolynomial.eval z p)) ≤ B
      rw [hsize]
      exact hb z hz)
  change (∑ α, pathSize (ContinuousMap.const Time (tensorCoeffs p α))) ≤ _ at he
  simpa only [hsize] using he

/-- Equation (14) for the exact normalized polynomial chosen by the estimator. The coefficient norm is derived from (12), polynomial degree control, and Chebyshev extraction, including the centering constant. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hε,hK,hr,hQ), the [stated conclusion](goal) holds. -/
lemma jacksonCoeff_sum_abs_le (ε : ℝ) (hε : 0 < ε) (K : ℕ) (hK : 0 < K)
    (c r : Fin 4 → ℝ) (hr : ∀ j, 0 < r j)
    (hQ : ∀ v ∈ centeredRectangle c r, ∀ j, 0 ≤ v j) :
    (∑ α : Fin 4 → Fin (2 * (K - 1) + 1), |jacksonCoeff ε K c r α|) ≤
      16 * (↑(2 * (K - 1) + 1) : ℝ) ^ 4 *
        (1 + Real.sqrt 2) ^ (4 * (2 * (K - 1))) * clippingScaleFormula ε c r := by
  let p := (jacksonPolynomialPair ε K c r).2 - MvPolynomial.C (armwiseExtensionFormula ε c)
  have hc (j : Fin 4) : 0 ≤ c j :=
    hQ c (by intro i; simpa using (hr i).le) j
  have hs := clippingScale_nonneg ε c r hc (fun j => (hr j).le)
  apply cubePolynomial_coeff_sum_le hK p _ hs
  · intro j
    exact (MvPolynomial.degreeOf_sub_le j _ _).trans (max_le
      (jacksonPolynomialPair_normalized_degree_le ε hε K hK c r hr hQ j) (by simp))
  · intro z hz
    have hq := affinePoint_mem_centeredRectangle c r z hr hz
    have hb := jacksonCoeff_mean_oscillation_le ε hε K hK c r hr hQ
      (affinePoint c r z) hq
    rw [jacksonCoeff_sum_eq_eval ε hε K hK c r hr hQ] at hb
    have he : normalizedPoint c r (affinePoint c r z) = z := by
      funext j
      dsimp [normalizedPoint, affinePoint]
      field_simp [ne_of_gt (hr j)]
      ring
    change |MvPolynomial.eval (normalizedPoint c r (affinePoint c r z))
      (jacksonPolynomialPair ε K c r).2 - armwiseExtensionFormula ε c| ≤ _ at hb
    rw [he] at hb
    simpa only [p, map_sub, MvPolynomial.eval_C] using hb

/-- The coefficient envelope applies to every actual pilot rectangle, without localization of the true parameter or extra count regularity assumptions. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hH,hm,hL,hε,hK), the [stated conclusion](goal) holds. -/
lemma pilotJacksonCoeff_sum_abs_le (H : ℝ) (hH : 0 < H) (m L : ℝ)
    (hm : 0 < m) (hL : 0 < L) (Np : Fin 4 → ℕ)
    (ε : ℝ) (hε : 0 < ε) (K : ℕ) (hK : 0 < K) :
    let b := pilotMidpoint H hH m L Np
    let r := pilotRadiusFormula H hH m L Np
    (∑ α : Fin 4 → Fin (2 * (K - 1) + 1), |jacksonCoeff ε K b r α|) ≤
      16 * (↑(2 * (K - 1) + 1) : ℝ) ^ 4 *
        (1 + Real.sqrt 2) ^ (4 * (2 * (K - 1))) * clippingScaleFormula ε b r := by
  exact jacksonCoeff_sum_abs_le ε hε K hK _ _
    (pilotRadius_pos H hH m L hm hL Np) (pilotCenteredRectangle_nonneg H hH m L Np)


-- @node: jacksonCoeff_factor_square_le_exp
/-- Squaring the explicit coefficient factor costs only an exponential linear in the Jackson order. The coarse numerical constant is universal and is sufficient for the logarithmic degree calibration in (27). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hK), the [stated conclusion](goal) holds. -/
lemma jacksonCoeff_factor_square_le_exp (K : ℕ) (hK : 0 < K) :
    (16 * (↑(2 * (K - 1) + 1) : ℝ) ^ 4 *
      (1 + Real.sqrt 2) ^ (4 * (2 * (K - 1)))) ^ 2 ≤
      Real.exp (304 * (K : ℝ)) := by
  let D := 2 * (K - 1)
  have hd : 0 ≤ (D : ℝ) := Nat.cast_nonneg _
  have hD : (D : ℝ) ≤ 2 * (K : ℝ) := by
    exact_mod_cast (show D ≤ 2 * K by dsimp [D]; omega)
  have hk : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hr : 1 + Real.sqrt 2 ≤ Real.exp 2 := by
    have hs : Real.sqrt 2 ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
    linarith [Real.add_one_le_exp (2 : ℝ)]
  have hdim : (↑(D + 1) : ℝ) ≤ Real.exp D := by
    push_cast
    linarith [Real.add_one_le_exp (D : ℝ)]
  have hconstant : (256 : ℝ) ≤ Real.exp 256 := by
    linarith [Real.add_one_le_exp (256 : ℝ)]
  have h₁ := pow_le_pow_left₀ (by positivity : 0 ≤ (↑(D + 1) : ℝ)) hdim 8
  have h₂ := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + Real.sqrt 2) hr (8 * D)
  calc
    _ = 256 * (↑(D + 1) : ℝ) ^ 8 * (1 + Real.sqrt 2) ^ (8 * D) := by
      dsimp only [D]
      rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]
      rw [show 4 * (2 * (K - 1)) * 2 = 8 * (2 * (K - 1)) by omega]
      norm_num
    _ ≤ Real.exp 256 * (Real.exp D) ^ 8 * (Real.exp 2) ^ (8 * D) := by
      gcongr
    _ = Real.exp (256 + 24 * (D : ℝ)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      push_cast
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

/-- Equations (14) and (25) give the full coefficient-times-factorial envelope in (26), with fixed universal linear and quadratic growth constants. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hε,hK,hr,hQ,hL), the [stated conclusion](goal) holds. -/
lemma jacksonCoeff_square_exp_le (ε : ℝ) (hε : 0 < ε) (K : ℕ) (hK : 0 < K)
    (c r : Fin 4 → ℝ) (hr : ∀ j, 0 < r j)
    (hQ : ∀ v ∈ centeredRectangle c r, ∀ j, 0 ≤ v j)
    (L : ℝ) (hL : 0 < L) :
    (∑ α : Fin 4 → Fin (2 * (K - 1) + 1), |jacksonCoeff ε K c r α|) ^ 2 *
        Real.exp (32 * (2 * (K - 1) : ℕ) ^ 2 / L) ≤
      clippingScaleFormula ε c r ^ 2 * Real.exp (304 * (K : ℝ) + 128 * (K : ℝ) ^ 2 / L) := by
  let A := 16 * (↑(2 * (K - 1) + 1) : ℝ) ^ 4 *
    (1 + Real.sqrt 2) ^ (4 * (2 * (K - 1)))
  have hc := jacksonCoeff_sum_abs_le ε hε K hK c r hr hQ
  have hcsq := pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => abs_nonneg _) hc 2
  have hfactor := jacksonCoeff_factor_square_le_exp K hK
  have hD : (↑(2 * (K - 1)) : ℝ) ≤ 2 * (K : ℝ) := by
    exact_mod_cast (show 2 * (K - 1) ≤ 2 * K by omega)
  have hDs := pow_le_pow_left₀ (Nat.cast_nonneg (2 * (K - 1))) hD 2
  have hquad : 32 * (↑(2 * (K - 1)) : ℝ) ^ 2 / L ≤ 128 * (K : ℝ) ^ 2 / L := by
    apply div_le_div_of_nonneg_right _ hL.le
    nlinarith
  calc
    _ ≤ (A * clippingScaleFormula ε c r) ^ 2 *
        Real.exp (32 * (↑(2 * (K - 1)) : ℝ) ^ 2 / L) :=
      mul_le_mul_of_nonneg_right hcsq (Real.exp_pos _).le
    _ = clippingScaleFormula ε c r ^ 2 *
        (A ^ 2 * Real.exp (32 * (↑(2 * (K - 1)) : ℝ) ^ 2 / L)) := by ring
    _ ≤ clippingScaleFormula ε c r ^ 2 *
        (Real.exp (304 * (K : ℝ)) * Real.exp (128 * (K : ℝ) ^ 2 / L)) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact mul_le_mul hfactor (Real.exp_le_exp.mpr hquad)
        (Real.exp_pos _).le (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]

/-- The actual localized factorial statistic satisfies equation (26) with its random armwise scale and universal exponential growth constants. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hqnonneg,hH,hHlarge,hm,hL,hWlaw,hind,hq,hε,hK), the [stated conclusion](goal) holds. -/
lemma pilotFactorialCellValue_square_exp_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : Fin 4 → Ω → ℕ)
    (q : Fin 4 → ℝ) (hqnonneg : ∀ j, 0 ≤ q j)
    (H : ℝ) (hH : 0 < H) (hHlarge : 1 ≤ H) (m L : ℝ)
    (hm : 0 < m) (hL : 0 < L) (Np : Fin 4 → ℕ)
    (hWlaw : ∀ j, HasLaw (W j)
      (poissonMeasure ⟨m * q j, mul_nonneg hm.le (hqnonneg j)⟩) μ)
    (hind : iIndepFun W μ)
    (hq : q ∈ pilotRectangle (pilotLower H hH m L Np) (pilotUpperFormula H hH m L Np))
    (ε : ℝ) (hε : 0 < ε) (K : ℕ) (hK : 0 < K) :
    let b := pilotMidpoint H hH m L Np
    let r := pilotRadiusFormula H hH m L Np
    (∫ ω, (factorialCellValue ε K m b r (fun j => W j ω) - armwiseExtensionFormula ε b) ^ 2 ∂μ) ≤
      clippingScaleFormula ε b r ^ 2 * Real.exp (304 * (K : ℝ) + 128 * (K : ℝ) ^ 2 / L) := by
  exact (pilotFactorialCellValue_square_envelope μ W q hqnonneg H hH hHlarge m L
    hm hL Np hWlaw hind hq ε K).trans
    (jacksonCoeff_square_exp_le ε hε K hK _ _ (pilotRadius_pos H hH m L hm hL Np)
      (pilotCenteredRectangle_nonneg H hH m L Np) L hL)

/-- The clipping contraction in (28) has the same derived exponential scale as (26). Localization supplies mean containment through the Jackson construction. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hqnonneg,hH,hHlarge,hm,hL,hWlaw,hind,hq,hε,hK,hd), the [stated conclusion](goal) holds. -/
lemma pilotClippedCellValue_square_exp_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : Fin 4 → Ω → ℕ)
    (q : Fin 4 → ℝ) (hqnonneg : ∀ j, 0 ≤ q j)
    (H : ℝ) (hH : 0 < H) (hHlarge : 1 ≤ H) (m L : ℝ)
    (hm : 0 < m) (hL : 0 < L) (Np : Fin 4 → ℕ)
    (hWlaw : ∀ j, HasLaw (W j)
      (poissonMeasure ⟨m * q j, mul_nonneg hm.le (hqnonneg j)⟩) μ)
    (hind : iIndepFun W μ)
    (hq : q ∈ pilotRectangle (pilotLower H hH m L Np) (pilotUpperFormula H hH m L Np))
    (ε : ℝ) (hε : 0 < ε) (K d : ℕ) (hK : 0 < K) (hd : 1 ≤ d) :
    let b := pilotMidpoint H hH m L Np
    let r := pilotRadiusFormula H hH m L Np
    let p := armwiseExtensionFormula ε b + ∑ α : Fin 4 → Fin (2 * (K - 1) + 1),
      jacksonCoeff ε K b r α * ∏ j, ((q j - b j) / r j) ^ (α j).val
    (∫ ω, (clippedCellValueFormula ε K d m b r (fun j => W j ω) - p) ^ 2 ∂μ) ≤
      clippingScaleFormula ε b r ^ 2 * Real.exp (304 * (K : ℝ) + 128 * (K : ℝ) ^ 2 / L) := by
  exact (pilotClippedCellValue_square_envelope_of_localized μ W q hqnonneg H hH hHlarge
    m L hm hL Np hWlaw hind hq ε hε K d hK hd).trans
    (jacksonCoeff_square_exp_le ε hε K hK _ _ (pilotRadius_pos H hH m L hm hL Np)
      (pilotCenteredRectangle_nonneg H hH m L Np) L hL)

/-- Positive radii and nonnegative centers make the clipping scale strictly positive. Each anchored arm weight is at least one. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hc,hr), the [stated conclusion](goal) holds. -/
lemma clippingScale_pos (ε : ℝ) (c r : Fin 4 → ℝ)
    (hc : ∀ j, 0 ≤ c j) (hr : ∀ j, 0 < r j) :
    0 < clippingScaleFormula ε c r := by
  have ht : 0 ≤ totalMassVecFormula c := by
    rw [totalMassVec_eq_sum_coordinates]
    exact Finset.sum_nonneg fun j _ => hc j
  have hw (a : Bool) : 0 < armWeightFormula ε c a := by
    have hd : 0 ≤ anchoredDenomFormula ε c a :=
      (add_nonneg (hc _) (hc _)).trans (le_max_left _ _)
    exact add_pos_of_pos_of_nonneg (by norm_num) (div_nonneg ht hd)
  have hR (a : Bool) : 0 < armRadiusFormula r a := add_pos (hr _) (hr _)
  simp only [clippingScaleFormula, Fintype.sum_bool]
  exact mul_pos (by norm_num) (add_pos (mul_pos (hw true) (hR true))
    (mul_pos (hw false) (hR false)))

/-- The first assertion of (28) follows from the factorial mean identity, clipping displacement, and the derived coefficient envelope. The scale positivity needed for division is provided by the pilot construction. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hqnonneg,hH,hHlarge,hm,hL,hWlaw,hind,hq,hε,hK,hd), the [stated conclusion](goal) holds. -/
lemma pilotClippedCellValue_bias_exp_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : Fin 4 → Ω → ℕ)
    (q : Fin 4 → ℝ) (hqnonneg : ∀ j, 0 ≤ q j)
    (H : ℝ) (hH : 0 < H) (hHlarge : 1 ≤ H) (m L : ℝ)
    (hm : 0 < m) (hL : 0 < L) (Np : Fin 4 → ℕ)
    (hWlaw : ∀ j, HasLaw (W j)
      (poissonMeasure ⟨m * q j, mul_nonneg hm.le (hqnonneg j)⟩) μ)
    (hind : iIndepFun W μ)
    (hq : q ∈ pilotRectangle (pilotLower H hH m L Np) (pilotUpperFormula H hH m L Np))
    (ε : ℝ) (hε : 0 < ε) (K d : ℕ) (hK : 0 < K) (hd : 1 ≤ d) :
    let b := pilotMidpoint H hH m L Np
    let r := pilotRadiusFormula H hH m L Np
    let p := armwiseExtensionFormula ε b + ∑ α : Fin 4 → Fin (2 * (K - 1) + 1),
      jacksonCoeff ε K b r α * ∏ j, ((q j - b j) / r j) ^ (α j).val
    |(∫ ω, clippedCellValueFormula ε K d m b r (fun j => W j ω) ∂μ) - p| ≤
      clippingScaleFormula ε b r * Real.exp (304 * (K : ℝ) + 128 * (K : ℝ) ^ 2 / L) /
        (d : ℝ) ^ (1 / 4 : ℝ) := by
  dsimp only
  have hs := clippingScale_pos ε _ _ (pilotMidpoint_nonneg H hH m L hm Np)
    (pilotRadius_pos H hH m L hm hL Np)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hw := mul_pos (Real.rpow_pos_of_pos hd0 (1 / 4 : ℝ)) hs
  apply (pilotClippedCellValue_bias_envelope μ W q hqnonneg H hH hHlarge m L
    hm hL Np hWlaw hind hq ε K d hw).trans
  calc
    _ ≤ (clippingScaleFormula ε (pilotMidpoint H hH m L Np) (pilotRadiusFormula H hH m L Np) ^ 2 *
        Real.exp (304 * (K : ℝ) + 128 * (K : ℝ) ^ 2 / L)) /
        ((d : ℝ) ^ (1 / 4 : ℝ) *
          clippingScaleFormula ε (pilotMidpoint H hH m L Np) (pilotRadiusFormula H hH m L Np)) :=
      div_le_div_of_nonneg_right
        (jacksonCoeff_square_exp_le ε hε K hK _ _ (pilotRadius_pos H hH m L hm hL Np)
          (pilotCenteredRectangle_nonneg H hH m L Np) L hL) hw.le
    _ = _ := by field_simp

/-- A universal logarithmic degree tuning absorbs the derived coefficient and factorial inflation into the `d^(1/16)` scale in (27), for every pilot rectangle. In the econometric construction, no additional assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma pilotJacksonCoeff_square_tuning_exists :
    ∃ κ A : ℝ, 0 < κ ∧ 0 < A ∧ ∀ {d : ℕ}, 1 ≤ d →
      ∀ (H : ℝ) (hH : 0 < H) (m : ℝ), 0 < m → ∀ (Np : Fin 4 → ℕ)
      (ε : ℝ), 0 < ε →
      let b := pilotMidpoint H hH m (logAlphabet d) Np
      let r := pilotRadiusFormula H hH m (logAlphabet d) Np
      let K := jacksonDegree κ d
      (∑ α : Fin 4 → Fin (2 * (K - 1) + 1), |jacksonCoeff ε K b r α|) ^ 2 *
          Real.exp (32 * (2 * (K - 1) : ℕ) ^ 2 / logAlphabet d) ≤
        A * (d : ℝ) ^ (1 / 16 : ℝ) * clippingScaleFormula ε b r ^ 2 := by
  obtain ⟨κ, A, hκ, hA, he⟩ := jacksonDegree_exponential_growth_le
    304 128 (by norm_num) (by norm_num)
  refine ⟨κ, A, hκ, hA, ?_⟩
  intro d hd H hH m hm Np ε hε
  dsimp only
  have hL := logAlphabet_pos hd
  have hK : 0 < jacksonDegree κ d := by
    unfold jacksonDegree
    omega
  apply (jacksonCoeff_square_exp_le ε hε _ hK _ _
    (pilotRadius_pos H hH m _ hm hL Np)
    (pilotCenteredRectangle_nonneg H hH m _ Np) _ hL).trans
  calc
    _ ≤ clippingScaleFormula ε (pilotMidpoint H hH m (logAlphabet d) Np)
        (pilotRadiusFormula H hH m (logAlphabet d) Np) ^ 2 *
        (A * (d : ℝ) ^ (1 / 16 : ℝ)) :=
      mul_le_mul_of_nonneg_left (he hd) (sq_nonneg _)
    _ = _ := by ring

end CausalSmith.Stat.OptvalueVanishingoverlapRate
