module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.TensorChebyshev
public import Causalean.Stat.Concentration.BoundedVariation.WeightedIntegral

/-!
# Tensor Chebyshev expansion of bounded-variation polynomial paths

A continuous polynomial path in four variables whose cube evaluations have bounded variation
and path size at most `B` has a tensor Chebyshev expansion whose coefficient paths are
continuous, of bounded variation, and of size at most `16 B`. The polynomial algebra of the
tensor Chebyshev basis lives in `Causalean.Mathlib.Analysis.Approximation.Chebyshev.TensorChebyshev`.
-/

@[expose] public section

noncomputable section

open Causalean.Mathlib.Analysis.JacksonApproximation
open Causalean.Mathlib.Analysis.Approximation.Chebyshev
open Causalean.Stat.Concentration.BoundedVariation
open MeasureTheory
open scoped BigOperators

namespace Causalean.Stat.Concentration.BoundedVariation

/-- The explicit tensor Chebyshev integral coefficients of a continuous polynomial path form
continuous bounded-variation paths, each with size at most `16 B` when every cube evaluation
path has size at most `B`.

Normalize the period-box volume to a probability measure, bound the product cosine weight, and
apply `weightedPathIntegral_size_le` before taking variation suprema.
-/
theorem tensorChebyshev_coefficientPath_size {D : ℕ}
    (p : Time → MvPolynomial (Fin 4) ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hcont : ∀ x ∈ normalizedCube 4,
      Continuous (fun t => MvPolynomial.eval x (p t)))
    (hBV : ∀ x (hx : x ∈ normalizedCube 4),
      eVariationOn (⟨fun t => MvPolynomial.eval x (p t), hcont x hx⟩ : Path)
        Set.univ < ⊤)
    (hbound : ∀ x (hx : x ∈ normalizedCube 4),
      pathSize (⟨fun t => MvPolynomial.eval x (p t), hcont x hx⟩ : Path) ≤ B) :
    ∃ c : (Fin 4 → Fin (D + 1)) → Path,
      (∀ t k, c k t = tensorChebyshevCoefficient D (p t) k) ∧
      (∀ k, eVariationOn (c k) Set.univ < ⊤) ∧
      (∀ k, pathSize (c k) ≤ 16 * B) := by
  let ν : Measure (Fin 4 → ℝ) := volume.restrict (periodBox 4)
  have hbox : periodBox 4 =
      Set.Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi) := by
    ext u
    simp only [periodBox, Set.mem_ofPred_eq, Set.mem_Icc, Pi.le_def]
    constructor
    · intro h
      exact ⟨fun i => (h i).1, fun i => (h i).2⟩
    · rintro ⟨h₁, h₂⟩ i
      exact ⟨h₁ i, h₂ i⟩
  have hvol : volume (periodBox 4) = ENNReal.ofReal ((2 * Real.pi) ^ 4) := by
    rw [hbox, Real.volume_Icc_pi, Fin.prod_univ_four]
    have h : Real.pi - -Real.pi = 2 * Real.pi := by ring
    simp only [h]
    rw [ENNReal.ofReal_pow (by positivity : 0 ≤ 2 * Real.pi)]
    simp [pow_succ, mul_assoc]
  have hmass : ν Set.univ = ENNReal.ofReal ((2 * Real.pi) ^ 4) := by
    simp [ν, hvol]
  have hmass0 : ν Set.univ ≠ 0 := by rw [hmass]; positivity
  letI : IsFiniteMeasure ν := ⟨by rw [hmass]; simp⟩
  letI : NeZero ν := ⟨by intro hz; exact hmass0 (by simp [hz])⟩
  let μ : Measure (Fin 4 → ℝ) := (ν Set.univ)⁻¹ • ν
  letI : IsProbabilityMeasure μ := by
    change IsProbabilityMeasure ((ν Set.univ)⁻¹ • ν)
    infer_instance
  let f : (Fin 4 → ℝ) → Path := fun u =>
    ⟨fun t => MvPolynomial.eval (cosPoint u) (p t),
      hcont (cosPoint u) (cosPoint_mem_normalizedCube u)⟩
  have hfBV (u : Fin 4 → ℝ) : eVariationOn (f u) Set.univ < ⊤ := by
    simpa [f, cosPoint] using hBV (cosPoint u) (cosPoint_mem_normalizedCube u)
  have hfsize (u : Fin 4 → ℝ) : pathSize (f u) ≤ B := by
    simpa [f, cosPoint] using hbound (cosPoint u) (cosPoint_mem_normalizedCube u)
  have hpoly (q : MvPolynomial (Fin 4) ℝ) :
      Continuous (fun u : Fin 4 → ℝ => MvPolynomial.eval (cosPoint u) q) := by
    induction q using MvPolynomial.induction_on with
    | C a => simpa using (continuous_const : Continuous (fun _ : Fin 4 → ℝ => a))
    | add q r hq hr =>
        convert hq.add hr using 1
        funext u
        simp [MvPolynomial.eval_add]
    | mul_X q i hq =>
        convert hq.mul (by fun_prop : Continuous (fun u : Fin 4 → ℝ => Real.cos (u i))) using 1
        funext u
        simp [cosPoint, MvPolynomial.eval_mul, MvPolynomial.eval_X]
  let w (k : Fin 4 → Fin (D + 1)) (u : Fin 4 → ℝ) : ℝ :=
    ∏ i : Fin 4, (if (k i : ℕ) = 0 then (1 : ℝ) else 2) *
      Real.cos ((k i : ℕ) * u i)
  have hw (k : Fin 4 → Fin (D + 1)) (u : Fin 4 → ℝ) : |w k u| ≤ 16 := by
    have hi (i : Fin 4) :
        |(if (k i : ℕ) = 0 then (1 : ℝ) else 2) *
          Real.cos ((k i : ℕ) * u i)| ≤ 2 := by
      have ha : 0 ≤ (if (k i : ℕ) = 0 then (1 : ℝ) else 2) ∧
          (if (k i : ℕ) = 0 then (1 : ℝ) else 2) ≤ 2 := by
        split_ifs <;> norm_num
      rw [abs_mul, abs_of_nonneg ha.1]
      have hc := Real.abs_cos_le_one ((k i : ℕ) * u i)
      nlinarith [abs_nonneg (Real.cos ((k i : ℕ) * u i))]
    simp only [w, Finset.abs_prod]
    calc
      (∏ i : Fin 4, |(if (k i : ℕ) = 0 then (1 : ℝ) else 2) *
        Real.cos ((k i : ℕ) * u i)|) ≤ ∏ _i : Fin 4, (2 : ℝ) :=
          Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hi i)
      _ = 16 := by norm_num [Fin.prod_univ_four]
  have hInt (k : Fin 4 → Fin (D + 1)) (t : Time) :
      Integrable (fun u => w k u * f u t) μ := by
    have hc : Continuous (fun u : Fin 4 → ℝ => w k u * f u t) := by
      exact (by fun_prop : Continuous (w k)).mul (hpoly (p t))
    have hi : Integrable (fun u => w k u * f u t) ν := by
      change IntegrableOn (fun u => w k u * f u t) (periodBox 4)
      rw [hbox]
      exact hc.continuousOn.integrableOn_compact isCompact_Icc
    exact hi.smul_measure (by simpa only [ne_eq, ENNReal.inv_eq_top] using hmass0)
  choose c hc hcbv hcsz using fun k =>
    weightedPathIntegral_size_le μ f (w k) B 16 hB (by norm_num)
      (hInt k) (hw k) hfBV hfsize
  refine ⟨c, ?_, hcbv, hcsz⟩
  intro t k
  rw [hc k t]
  let A : ℝ := ∏ i : Fin 4,
    if (k i : ℕ) = 0 then (1 / (2 * Real.pi) : ℝ) else 1 / Real.pi
  let L : ℝ := (2 * Real.pi) ^ 4
  have hL : L ≠ 0 := by positivity
  have hfactor (u : Fin 4 → ℝ) :
      w k u = L * A * (∏ i : Fin 4, Real.cos ((k i : ℕ) * u i)) := by
    simp only [w, A, L, Finset.prod_mul_distrib]
    congr 1
    simp only [Fin.prod_univ_four]
    split_ifs <;> field_simp [Real.pi_ne_zero]
  have hweighted :
      (∫ u, w k u * f u t ∂ν) =
        L * A * ∫ u in periodBox 4,
          (∏ i : Fin 4, Real.cos ((k i : ℕ) * u i)) *
            MvPolynomial.eval (fun i => Real.cos (u i)) (p t) := by
    change (∫ u in periodBox 4, w k u * MvPolynomial.eval (cosPoint u) (p t)) = _
    simp_rw [hfactor]
    change (∫ u in periodBox 4,
      (L * A * ∏ i : Fin 4, Real.cos ((k i : ℕ) * u i)) *
        MvPolynomial.eval (fun i => Real.cos (u i)) (p t)) = _
    simp only [mul_assoc, integral_const_mul]
  calc
    (∫ u, w k u * f u t ∂μ) = (ν Set.univ)⁻¹.toReal *
        (∫ u, w k u * f u t ∂ν) := by simp [μ]
    _ = L⁻¹ * (L * A * ∫ u in periodBox 4,
          (∏ i : Fin 4, Real.cos ((k i : ℕ) * u i)) *
            MvPolynomial.eval (fun i => Real.cos (u i)) (p t)) := by
      rw [hmass, ENNReal.toReal_inv, ENNReal.toReal_ofReal (by positivity : 0 ≤ L)]
      exact congrArg _ hweighted
    _ = tensorChebyshevCoefficient D (p t) k := by
      let I : ℝ := ∫ u in periodBox 4,
        (∏ i : Fin 4, Real.cos ((k i : ℕ) * u i)) *
          MvPolynomial.eval (fun i => Real.cos (u i)) (p t)
      change L⁻¹ * (L * A * I) = A * I
      calc
        L⁻¹ * (L * A * I) = (L⁻¹ * L) * (A * I) := by ring
        _ = A * I := by rw [inv_mul_cancel₀ hL, one_mul]

/-- [A four-variable polynomial path and a nonnegative envelope](hyp:p,B,hB), [a coordinatewise degree bound](hyp:hdeg), [continuous cube evaluations](hyp:hcont), [finite variation of those evaluations](hyp:hBV), and [their path-size bound](hyp:hbound) give [a tensor Chebyshev expansion with continuous bounded-variation coefficient paths of controlled size](goal).

A continuous four-variable polynomial path of coordinatewise degree at most `D`, whose
cube evaluations have bounded variation and path size at most `B`, has a tensor Chebyshev
expansion with continuous bounded-variation coefficient paths of size at most `16 B`.

The coefficient path should be the product-cosine integral of the cube evaluation path. Prove
orthogonality to identify the expansion and use `weightedPathIntegral_size_le` for the path bound.
-/
theorem tensorChebyshevPath_expansion {D : ℕ}
    (p : Time → MvPolynomial (Fin 4) ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hdeg : ∀ t i, (p t).degreeOf i ≤ D)
    (hcont : ∀ x ∈ normalizedCube 4,
      Continuous (fun t => MvPolynomial.eval x (p t)))
    (hBV : ∀ x (hx : x ∈ normalizedCube 4),
      eVariationOn (⟨fun t => MvPolynomial.eval x (p t), hcont x hx⟩ : Path)
        Set.univ < ⊤)
    (hbound : ∀ x (hx : x ∈ normalizedCube 4),
      pathSize (⟨fun t => MvPolynomial.eval x (p t), hcont x hx⟩ : Path) ≤ B) :
    ∃ c : (Fin 4 → Fin (D + 1)) → Path,
      (∀ t, p t = tensorChebyshevPolynomial D (fun k => c k t)) ∧
      (∀ k, eVariationOn (c k) Set.univ < ⊤) ∧
      (∀ k, pathSize (c k) ≤ 16 * B) := by
  obtain ⟨c, hc, hcbv, hcsz⟩ :=
    tensorChebyshev_coefficientPath_size p B hB hcont hBV hbound
  refine ⟨c, ?_, hcbv, hcsz⟩
  intro t
  have hfun : (fun k => c k t) = tensorChebyshevCoefficient D (p t) :=
    funext (hc t)
  rw [hfun]
  exact tensorChebyshev_coeff_recovery D (p t) (hdeg t)

end Causalean.Stat.Concentration.BoundedVariation
