module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.CosineEnergy
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.CosineSpatialEnergy
public import Causalean.Mathlib.Analysis.Fourier

/-! # Fourier endpoints for the explicit cosine cutoff extension

The proved slice integration-by-parts identity and nine-cell spatial bounds
instantiate angular Plancherel with the exact one-half gradient normalization.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity
open Causalean.Mathlib.Analysis.Fourier

/-- [ The paper and library angular Fourier definitions have identical normalization and kernel. This uses [the stated conclusion](goal). -/
-- @node: Fourier_eq_angularFourier
lemma Fourier_eq_angularFourier {p : ℕ} (G : Space p → ℂ) :
    Fourier G = angularFourier G := rfl

/-- Product-coordinate and Euclidean nonnegative integrals agree with Jacobian one.](goal) Under [the stated conditions](hyp:f). This uses [the stated conclusion](goal). -/
-- @node: cosine_lintegral_coordinates
lemma cosine_lintegral_coordinates (f : Cube 2 → ℝ≥0∞) :
    (∫⁻ u : Space 2, f (fun j => u j)) = ∫⁻ x : Cube 2, f x := by
  exact ((PiLp.volume_preserving_toLp (Fin 2)).lintegral_comp_emb
    (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).measurableEmbedding _).symm

/-- [ The cutoff extension obeys both angular Fourier endpoint bounds with the paper's constants.](goal) Under [the stated conditions](hyp:hL). -/
-- @node: pairCosineExtension_fourier_endpoints
lemma pairCosineExtension_fourier_endpoints {L : ℕ} (hL : 1 ≤ L)
    (h : Fin L × Fin L → ℝ) :
    extensionFourierEnergy 2 0 (cosinePairExtension (pairCosinePolynomial h)) ≤
      16 * ENNReal.ofReal (∑ α, h α ^ 2) ∧
    extensionFourierEnergy 2 1 (cosinePairExtension (pairCosinePolynomial h)) ≤
      ENNReal.ofReal (C0 ^ 2) * ENNReal.ofReal ((L : ℝ) ^ 2) *
        ENNReal.ofReal (∑ α, h α ^ 2) := by
  let G : Space 2 → ℝ := fun u => cosineCutoff (u 0) * cosineCutoff (u 1) *
    pairCosinePolynomial h (fun j => u j)
  let D : Fin 2 → Space 2 → ℝ := fun r u => pairCosineExtensionPartial h r (fun j => u j)
  have hGc : HasCompactSupport G := by
    have hs := (cosinePairExtension_hasCompactSupport (pairCosinePolynomial h)).comp_left
      (g := Complex.re) (by simp)
    simpa [G, cosinePairExtension, cosinePairCutoff, Function.comp_def] using hs
  have hGcont : Continuous G := by dsimp [G]; fun_prop
  have hD1 : ∀ r, Integrable (D r) volume := fun r =>
    (pairCosineExtensionPartial_integrable_and_memLp h r).1
  have hD2 : ∀ r, MemLp (D r) 2 volume := fun r =>
    (pairCosineExtensionPartial_integrable_and_memLp h r).2
  have hDc : ∀ r, HasCompactSupport (D r) := fun r =>
    pairCosineExtensionPartial_hasCompactSupport h r
  have hslice : HasRealSliceIBP G D := by
    apply (realSliceIBP_coordinates_iff
      (fun x => cosineCutoff (x 0) * cosineCutoff (x 1) * pairCosinePolynomial h x)
      (pairCosineExtensionPartial h)).2
    exact fun r x v v' hv hv' => pairCosineExtensionPartial_weak_slice h r x hv hv'
  have hA : l2Energy G ≤ ENNReal.ofReal (9 * ∑ α, h α ^ 2) := by
    have hec := cosine_lintegral_coordinates (fun x => ENNReal.ofReal
      ((cosineCutoff (x 0) * cosineCutoff (x 1) * pairCosinePolynomial h x) ^ 2))
    simpa only [l2Energy, G, Real.norm_eq_abs, sq_abs, hec]
      using pairCosineExtension_spatial_energy_le h
  have hB : l2Energy (D 0) + l2Energy (D 1) ≤
      ENNReal.ofReal ((36 + 36 * Real.pi ^ 2 * (L : ℝ) ^ 2) * ∑ α, h α ^ 2) := by
    rw [l2Energy, l2Energy, ← lintegral_add_left]
    · simp only [D, Real.norm_eq_abs, sq_abs, ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
      rw [cosine_lintegral_coordinates (fun x => ENNReal.ofReal
        (pairCosineExtensionPartial h 0 x ^ 2 + pairCosineExtensionPartial h 1 x ^ 2))]
      exact pairCosineExtensionPartial_spatial_energy_le h
    · dsimp [D]
      unfold pairCosineExtensionPartial pairCutoffPartial
      split_ifs <;> fun_prop
  have hb := energy_bounds_two_real_slices G D
    (hGcont.integrable_of_hasCompactSupport hGc) (hGcont.memLp_of_hasCompactSupport hGc)
    hGc hD1 hD2 hslice
    (9 * ∑ α, h α ^ 2) ((36 + 36 * Real.pi ^ 2 * (L : ℝ) ^ 2) * ∑ α, h α ^ 2)
    (by positivity) (by positivity) hA hB
  have he : complexify G = cosinePairExtension (pairCosinePolynomial h) := by
    funext u
    simp [complexify, G, cosinePairExtension, cosinePairCutoff]
  rw [he] at hb
  have hsum : 0 ≤ ∑ α, h α ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hLreal : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hC : C0 ^ 2 = 48 + 32 * Real.pi ^ 2 := by
    rw [C0, Real.sq_sqrt (by positivity)]
  constructor
  · simp only [extensionFourierEnergy, Fourier_eq_angularFourier, Real.rpow_zero, mul_one]
    change zeroEnergy (cosinePairExtension (pairCosinePolynomial h)) ≤ _
    apply hb.1.trans
    calc
      _ ≤ ENNReal.ofReal (16 * ∑ α, h α ^ 2) := ENNReal.ofReal_le_ofReal (by nlinarith)
      _ = _ := by rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16)]; norm_num
  · simp only [extensionFourierEnergy, Fourier_eq_angularFourier, Real.rpow_one]
    change firstEnergy (cosinePairExtension (pairCosinePolynomial h)) ≤ _
    apply hb.2.trans
    rw [← ENNReal.ofReal_mul (sq_nonneg C0), ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [hC]
    have hsL : 1 ≤ (L : ℝ) ^ 2 := by nlinarith
    have hp := sq_nonneg Real.pi
    have hc : 27 + 18 * Real.pi ^ 2 * (L : ℝ) ^ 2 ≤
        (48 + 32 * Real.pi ^ 2) * (L : ℝ) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hc hsum]

/-- [ The explicit cutoff certifies the pair restriction bound for arbitrary coefficients,
without any endpoint assumptions.](goal) Under [the stated conditions](hyp:hL,hs,hs1). -/
-- @node: pairCosinePolynomial_restriction_bound
lemma pairCosinePolynomial_restriction_bound {L : ℕ} (hL : 1 ≤ L)
    (h : Fin L × Fin L → ℝ) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    sobolevNormSq 2 s (pairCosinePolynomial h) ≤
      ENNReal.ofReal (C0 ^ 2 * ((L : ℝ) ^ s) ^ 2) * ENNReal.ofReal (∑ α, h α ^ 2) := by
  have he := pairCosineExtension_fourier_endpoints hL h
  exact cosinePair_restriction_bound_of_endpoints (by fun_prop) hs hs1 L _ he.1 he.2

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity

