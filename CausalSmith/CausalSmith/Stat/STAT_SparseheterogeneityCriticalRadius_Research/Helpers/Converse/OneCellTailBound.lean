module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Converse.OneCellTail

/-! Groups the one-cell four-index Taylor remainder by total degree and
closes the calibrated one-cell chi-square estimate. -/

public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory Set
open Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality
open scoped BigOperators

/-- The quadratically weighted four-index factorial tail groups exactly by
total degree. -/
lemma finFour_highDegree_quadratic_factorial_tsum_eq
    (Lambda : ℝ) (J : ℕ) (hLambda : 0 ≤ Lambda) :
    (∑' alpha : Fin 4 → ℕ,
      if 3 * J < ∑ s, alpha s then
        ((∑ s, alpha s : ℕ) : ℝ) ^ 2 *
          Lambda ^ (∑ s, alpha s) /
            (∏ s, ((alpha s).factorial : ℝ))
      else 0) =
      ∑' k : ℕ,
        ((3 * J + 1 + k : ℕ) : ℝ) ^ 2 *
          (4 * Lambda) ^ (3 * J + 1 + k) /
            (3 * J + 1 + k).factorial := by
  classical
  let s (m : ℕ) : Finset (Fin 4 → ℕ) :=
    Finset.piAntidiag Finset.univ m
  let a (alpha : Fin 4 → ℕ) : ℝ :=
    ((∑ i, alpha i : ℕ) : ℝ) ^ 2 * Lambda ^ (∑ i, alpha i) /
      (∏ i, ((alpha i).factorial : ℝ))
  let f (alpha : Fin 4 → ℕ) : ℝ :=
    if 3 * J < ∑ i, alpha i then a alpha else 0
  let g (m : ℕ) : ℝ :=
    (m : ℝ) ^ 2 * (4 * Lambda) ^ m / m.factorial
  have hs_mem (m : ℕ) (alpha : Fin 4 → ℕ) :
      alpha ∈ s m ↔ (∑ i, alpha i) = m := by
    simp [s, Finset.mem_piAntidiag]
  have hdegree (m : ℕ) : ∑ alpha ∈ s m, a alpha = g m := by
    calc
      ∑ alpha ∈ s m, a alpha =
          (m : ℝ) ^ 2 * Lambda ^ m *
            (∑ alpha ∈ s m,
              (1 : ℝ) / ∏ i, ((alpha i).factorial : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro alpha halpha
        simp only [a]
        rw [(hs_mem m alpha).mp halpha]
        ring
      _ = (m : ℝ) ^ 2 * Lambda ^ m *
          ((4 : ℝ) ^ m / m.factorial) := by
        rw [finFour_sum_reciprocal_factorial]
      _ = g m := by
        simp only [g]
        rw [mul_pow]
        ring
  have hg : Summable g := by
    apply (Real.summable_pow_div_factorial (16 * |Lambda|)).of_norm_bounded
    intro m
    simp only [g, Real.norm_eq_abs, abs_div,
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)]
    rw [abs_mul, abs_of_nonneg (sq_nonneg _), abs_pow, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    calc
      (m : ℝ) ^ 2 * (4 * |Lambda|) ^ m ≤
          (4 : ℝ) ^ m * (4 * |Lambda|) ^ m := by
        gcongr
        exact_mod_cast nat_sq_le_four_pow m
      _ = (16 * |Lambda|) ^ m := by
        rw [← mul_pow]
        congr 1 <;> ring
  have hf_nonneg : ∀ alpha, 0 ≤ f alpha := by
    intro alpha
    dsimp [f, a]
    split_ifs
    · exact div_nonneg
        (mul_nonneg (sq_nonneg _) (pow_nonneg hLambda _)) (by positivity)
    · exact le_rfl
  have hfiber (m : ℕ) :
      ∑' alpha : {alpha // alpha ∈ s m}, f alpha =
        if 3 * J < m then g m else 0 := by
    rw [Finset.tsum_subtype (s m) f]
    by_cases hm : 3 * J < m
    · rw [if_pos hm, ← hdegree]
      apply Finset.sum_congr rfl
      intro alpha halpha
      simp [f, (hs_mem m alpha).mp halpha, hm]
    · rw [if_neg hm]
      apply Finset.sum_eq_zero
      intro alpha halpha
      simp [f, (hs_mem m alpha).mp halpha, hm]
  have htail : Summable (fun m => if 3 * J < m then g m else 0) := by
    have heq : (fun m => if 3 * J < m then g m else 0) =
        ({m : ℕ | 3 * J < m}.indicator g) := by
      funext m
      simp [Set.indicator_apply]
    rw [heq]
    exact hg.indicator {m : ℕ | 3 * J < m}
  have hf : Summable f := by
    apply (summable_partition hf_nonneg
      (s := fun m => (s m : Set (Fin 4 → ℕ))) (by
        intro alpha
        refine ⟨∑ i, alpha i, ?_, ?_⟩
        · exact (hs_mem _ _).2 rfl
        · intro m hm
          exact (hs_mem _ _).1 hm |>.symm)).2
    constructor
    · intro m
      haveI : Finite (s m : Set (Fin 4 → ℕ)) := (s m).finite_toSet.to_subtype
      exact Summable.of_finite
    · simpa only [Finset.coe_sort_coe, hfiber] using htail
  have hgroup : (∑' alpha, f alpha) =
      ∑' m, if 3 * J < m then g m else 0 := by
    have hF := hf.hasSum.tsum_fiberwise (fun alpha => ∑ i, alpha i)
    rw [← hF.tsum_eq]
    apply tsum_congr
    intro m
    rw [show (fun alpha : Fin 4 → ℕ => ∑ i, alpha i) ⁻¹' {m} =
        (s m : Set (Fin 4 → ℕ)) by ext alpha; simp [hs_mem]]
    exact hfiber m
  have hshift : (∑' m, if 3 * J < m then g m else 0) =
      ∑' k, g (3 * J + 1 + k) := by
    let p : ℕ → ℝ := fun m => if m < 3 * J + 1 then g m else 0
    have hp : Summable p := by
      apply summable_of_hasFiniteSupport
      refine Set.Finite.subset (Finset.finite_toSet (Finset.range (3 * J + 1))) ?_
      intro m hm
      simp only [Function.mem_support, p] at hm
      by_cases hlt : m < 3 * J + 1
      · exact Finset.mem_range.mpr hlt
      · simp [hlt] at hm
    have htailfun : (fun m => if 3 * J < m then g m else 0) =
        fun m => g m - p m := by
      funext m
      simp only [p]
      by_cases hm : 3 * J < m
      · rw [if_pos hm, if_neg (by omega), sub_zero]
      · rw [if_neg hm, if_pos (by omega), sub_self]
    rw [htailfun, hg.tsum_sub hp]
    have hp_tsum : (∑' m, p m) = ∑ m ∈ Finset.range (3 * J + 1), g m := by
      rw [tsum_eq_sum (s := Finset.range (3 * J + 1))]
      · apply Finset.sum_congr rfl
        intro m hm
        have hlt := Finset.mem_range.mp hm
        change (if m < 3 * J + 1 then g m else 0) = g m
        rw [if_pos hlt]
      · intro m hm
        simp only [p]
        rw [if_neg]
        simpa using hm
    rw [hp_tsum]
    have hsplit := hg.sum_add_tsum_nat_add (3 * J + 1)
    rw [show (fun k => g (3 * J + 1 + k)) =
        (fun k => g (k + (3 * J + 1))) by funext k; congr 1 <;> omega]
    linarith
  change (∑' alpha, f alpha) = _
  rw [hgroup, hshift]

/-- The exact high-degree moment expansion is bounded by the scalar
quadratic factorial tail, with its explicit signed-score prefactor. -/
lemma signedScoreMixtureLikelihood_sq_sub_integral_le_factorial_tail
    (kappa gamma rho a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (hkappa : 0 < kappa)
    (hgamma : gamma ∈ Icc (0 : ℝ) 1) (hrho : rho ∈ Icc (0 : ℝ) 2)
    (ha : 0 < a) (hJ : 1 ≤ J) :
    (∫ z, (signedScoreMixtureLikelihood (kappa * (J : ℝ))
          (signedScoreIntensityPrior kappa gamma rho a J D true) z -
        signedScoreMixtureLikelihood (kappa * (J : ℝ))
          (signedScoreIntensityPrior kappa gamma rho a J D false) z) ^ 2
        ∂signedScoreReferenceLaw (kappa * (J : ℝ))) ≤
      (gamma ^ 2 * rho ^ 2 / 64) *
        ∑' k : ℕ,
          ((3 * J + 1 + k : ℕ) : ℝ) ^ 2 *
            (4 * (kappa * (J : ℝ))) ^ (3 * J + 1 + k) /
              (3 * J + 1 + k).factorial := by
  classical
  let Lambda : ℝ := kappa * (J : ℝ)
  let c : ℝ := gamma ^ 2 * rho ^ 2 / 64
  let R (alpha : Fin 4 → ℕ) : ℝ :=
    ((∫ v, ∏ s, (v s - Lambda) ^ alpha s
          ∂signedScoreIntensityPrior kappa gamma rho a J D true) -
        (∫ v, ∏ s, (v s - Lambda) ^ alpha s
          ∂signedScoreIntensityPrior kappa gamma rho a J D false)) ^ 2 /
      ((∏ s, ((alpha s).factorial : ℝ)) *
        Lambda ^ (∑ s, alpha s))
  let A (alpha : Fin 4 → ℕ) : ℝ :=
    ((∑ s, alpha s : ℕ) : ℝ) ^ 2 * Lambda ^ (∑ s, alpha s) /
      (∏ s, ((alpha s).factorial : ℝ))
  let F (alpha : Fin 4 → ℕ) : ℝ :=
    if 3 * J < ∑ s, alpha s then R alpha else 0
  let G (alpha : Fin 4 → ℕ) : ℝ :=
    if 3 * J < ∑ s, alpha s then c * A alpha else 0
  have hLambda : 0 < Lambda := by
    dsimp [Lambda]
    positivity
  have hA_nonneg (alpha : Fin 4 → ℕ) : 0 ≤ A alpha := by
    dsimp [A]
    positivity
  let B (alpha : Fin 4 → ℕ) : ℝ :=
    ∏ s, (4 * Lambda) ^ alpha s / (alpha s).factorial
  have hB : Summable B := by
    have h := signedScoreTaylorCoefficient_summable
      (4 * Lambda) (fun _ : Fin 4 => 0) (fun _ : Fin 4 => 0)
    apply h.congr
    intro alpha
    simp only [signedScoreTaylorCoefficient, B, zero_sub, neg_mul_neg,
      mul_div_cancel_left₀ _ (by positivity : 4 * Lambda ≠ 0),
      Fin.prod_univ_four]
  have hAB (alpha : Fin 4 → ℕ) : A alpha ≤ B alpha := by
    let r := ∑ s, alpha s
    have hsq : ((r : ℕ) : ℝ) ^ 2 ≤ (4 : ℝ) ^ r := by
      exact_mod_cast nat_sq_le_four_pow r
    have hden : 0 ≤ ∏ s, ((alpha s).factorial : ℝ) := by positivity
    calc
      A alpha ≤ (4 : ℝ) ^ r * Lambda ^ r /
          (∏ s, ((alpha s).factorial : ℝ)) := by
        dsimp only [A, r]
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hsq (pow_nonneg hLambda.le _)) hden
      _ = (4 * Lambda) ^ r /
          (∏ s, ((alpha s).factorial : ℝ)) := by
        simp only [Lambda, mul_pow]
      _ = B alpha := by
        simp only [B, r, Fin.prod_univ_four, Fin.sum_univ_four, pow_add]
        ring
  have hA : Summable A :=
    Summable.of_nonneg_of_le hA_nonneg hAB hB
  have hG : Summable G := by
    have htail : Summable (fun alpha =>
        if 3 * J < ∑ s, alpha s then A alpha else 0) := by
      have heq : (fun alpha => if 3 * J < ∑ s, alpha s then A alpha else 0) =
          ({alpha : Fin 4 → ℕ | 3 * J < ∑ s, alpha s}.indicator A) := by
        funext alpha
        simp [Set.indicator_apply]
      rw [heq]
      exact hA.indicator _
    have heq : G = fun alpha => c *
        (if 3 * J < ∑ s, alpha s then A alpha else 0) := by
      funext alpha
      simp only [G]
      split_ifs <;> ring
    rw [heq]
    exact htail.mul_left c
  have hF_nonneg (alpha : Fin 4 → ℕ) : 0 ≤ F alpha := by
    dsimp only [F, R]
    split_ifs
    · positivity
    · exact le_rfl
  have hFG (alpha : Fin 4 → ℕ) : F alpha ≤ G alpha := by
    dsimp only [F, G]
    by_cases hdeg : 3 * J < ∑ s, alpha s
    · rw [if_pos hdeg, if_pos hdeg]
      have hcoef := signedScoreIntensityPrior_squared_coefficient_le
        kappa gamma rho a J D alpha hkappa hgamma hrho ha hJ
      change R alpha ≤ c * A alpha
      calc
        R alpha ≤
            (((∑ s, alpha s : ℕ) : ℝ) * (gamma * rho / 8) *
                Lambda ^ (∑ s, alpha s)) ^ 2 /
              ((∏ s, ((alpha s).factorial : ℝ)) *
                Lambda ^ (∑ s, alpha s)) := by
          simpa only [R, Lambda] using hcoef
        _ = c * A alpha := by
          have hpow : Lambda ^ (∑ s, alpha s) ≠ 0 :=
            pow_ne_zero _ hLambda.ne'
          have hprod : (∏ s, ((alpha s).factorial : ℝ)) ≠ 0 := by positivity
          dsimp only [c, A]
          field_simp [hpow, hprod]
          ring
    · rw [if_neg hdeg, if_neg hdeg]
  have hF : Summable F :=
    Summable.of_nonneg_of_le hF_nonneg hFG hG
  rw [signedScoreMixtureLikelihood_sq_sub_integral_eq_tsum_highDegree
    kappa gamma rho a J D hkappa hgamma hrho ha hJ]
  change (∑' alpha, F alpha) ≤ _
  calc
    (∑' alpha, F alpha) ≤ ∑' alpha, G alpha :=
      hF.tsum_le_tsum hFG hG
    _ = c * ∑' alpha : Fin 4 → ℕ,
        if 3 * J < ∑ s, alpha s then A alpha else 0 := by
      have hGeq : G = fun alpha => c *
          (if 3 * J < ∑ s, alpha s then A alpha else 0) := by
        funext alpha
        simp only [G]
        split_ifs <;> ring
      rw [hGeq, tsum_mul_left]
    _ = c * ∑' k : ℕ,
        ((3 * J + 1 + k : ℕ) : ℝ) ^ 2 *
          (4 * Lambda) ^ (3 * J + 1 + k) /
            (3 * J + 1 + k).factorial := by
      rw [show (fun alpha : Fin 4 → ℕ =>
          if 3 * J < ∑ s, alpha s then A alpha else 0) =
          fun alpha => if 3 * J < ∑ s, alpha s then
            ((∑ s, alpha s : ℕ) : ℝ) ^ 2 * Lambda ^ (∑ s, alpha s) /
              (∏ s, ((alpha s).factorial : ℝ)) else 0 by rfl,
        finFour_highDegree_quadratic_factorial_tsum_eq Lambda J hLambda.le]
    _ = _ := rfl

/-- If the per-cell exposure constant is at most `2⁻¹²`, the concrete
true/false one-cell mixture has the chi-square bound required by the converse. -/
lemma signedScoreMixtureLaw_intensityPrior_chiSqDiv_le_calibrated
    (kappa gamma rho a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (hkappa : 0 < kappa) (hkappaSmall : kappa ≤ (1 : ℝ) / 4096)
    (hgamma : gamma ∈ Icc (0 : ℝ) 1) (hrho : rho ∈ Icc (0 : ℝ) 2)
    (ha : 0 < a) (hJ : 1 ≤ J) :
    Causalean.Stat.chiSqDiv
        (signedScoreMixtureLaw
          (signedScoreIntensityPrior kappa gamma rho a J D true))
        (signedScoreMixtureLaw
          (signedScoreIntensityPrior kappa gamma rho a J D false)) ≤
      rho ^ 2 * (J : ℝ) ^ 3 * ((1 : ℝ) / 16) ^ J := by
  let Lambda : ℝ := kappa * (J : ℝ)
  let T : ℝ := ∑' k : ℕ,
    ((3 * J + 1 + k : ℕ) : ℝ) ^ 2 *
      (4 * Lambda) ^ (3 * J + 1 + k) /
        (3 * J + 1 + k).factorial
  have hLambda : 0 ≤ Lambda := by
    dsimp [Lambda]
    positivity
  have hsmall : Lambda ≤ (J : ℝ) / 4096 := by
    dsimp [Lambda]
    calc
      kappa * (J : ℝ) ≤ ((1 : ℝ) / 4096) * J :=
        mul_le_mul_of_nonneg_right hkappaSmall (by positivity)
      _ = (J : ℝ) / 4096 := by ring
  have hT : 0 ≤ T := by
    dsimp [T]
    exact tsum_nonneg fun k => by positivity
  have hgammaSq : gamma ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hgamma.1 (sub_nonneg.mpr hgamma.2)]
  have hcoef :
      (J : ℝ) * (gamma ^ 2 * rho ^ 2 / 64) ≤
        (J : ℝ) * rho ^ 2 / 16 := by
    rw [show (J : ℝ) * rho ^ 2 / 16 =
        (J : ℝ) * (rho ^ 2 / 16) by ring]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hmul : gamma ^ 2 * rho ^ 2 ≤ rho ^ 2 :=
      by simpa using mul_le_mul_of_nonneg_right hgammaSq (sq_nonneg rho)
    nlinarith [sq_nonneg rho]
  have hint := signedScoreMixtureLikelihood_sq_sub_integral_le_factorial_tail
    kappa gamma rho a J D hkappa hgamma hrho ha hJ
  have hchi := signedScoreMixtureLaw_intensityPrior_chiSqDiv_le
    kappa gamma rho a J D hkappa hgamma hrho ha hJ
  calc
    Causalean.Stat.chiSqDiv
        (signedScoreMixtureLaw
          (signedScoreIntensityPrior kappa gamma rho a J D true))
        (signedScoreMixtureLaw
          (signedScoreIntensityPrior kappa gamma rho a J D false)) ≤
      (J : ℝ) * ∫ z,
        (signedScoreMixtureLikelihood (kappa * (J : ℝ))
            (signedScoreIntensityPrior kappa gamma rho a J D true) z -
          signedScoreMixtureLikelihood (kappa * (J : ℝ))
            (signedScoreIntensityPrior kappa gamma rho a J D false) z) ^ 2
        ∂signedScoreReferenceLaw (kappa * (J : ℝ)) := hchi
    _ ≤ (J : ℝ) * ((gamma ^ 2 * rho ^ 2 / 64) * T) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [T, Lambda] using hint
    _ = ((J : ℝ) * (gamma ^ 2 * rho ^ 2 / 64)) * T := by ring
    _ ≤ ((J : ℝ) * rho ^ 2 / 16) * T :=
      mul_le_mul_of_nonneg_right hcoef hT
    _ ≤ rho ^ 2 * (J : ℝ) ^ 3 * ((1 : ℝ) / 16) ^ J := by
      simpa only [T] using
        signedScore_chiSquare_tail_three_mul_le rho Lambda J hJ hLambda hsmall

/-- At the fixed paper calibration `κ = 1/4096`, the one-cell chi-square
bound has no analytic side conditions beyond the construction assumptions. -/
lemma signedScoreMixtureLaw_intensityPrior_chiSqDiv_le_concrete
    (gamma rho a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (hgamma : gamma ∈ Icc (0 : ℝ) 1) (hrho : rho ∈ Icc (0 : ℝ) 2)
    (ha : 0 < a) (hJ : 1 ≤ J) :
    Causalean.Stat.chiSqDiv
        (signedScoreMixtureLaw
          (signedScoreIntensityPrior ((1 : ℝ) / 4096) gamma rho a J D true))
        (signedScoreMixtureLaw
          (signedScoreIntensityPrior ((1 : ℝ) / 4096) gamma rho a J D false)) ≤
      rho ^ 2 * (J : ℝ) ^ 3 * ((1 : ℝ) / 16) ^ J := by
  exact signedScoreMixtureLaw_intensityPrior_chiSqDiv_le_calibrated
    ((1 : ℝ) / 4096) gamma rho a J D (by norm_num) (by norm_num)
      hgamma hrho ha hJ

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
