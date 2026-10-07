module
public import CausalSmith.Stat.STAT_DiscreteBudgetvalueCurve_Research.Helpers.CoefficientEnvelope
public import Causalean.Stat.Concentration.BoundedVariation.TensorCoefficient
public import Causalean.Stat.Concentration.Poisson.FactorialPath

/-! Products of centered factorial lifts for the four coordinates. -/

@[expose] public section

namespace CausalSmith.Stat.DiscreteBudgetvalueCurve

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open Causalean.Stat.Concentration.Poisson
open Causalean.Stat.Concentration.BoundedVariation

/-- A bounded monomial coefficient of the local Jackson polynomial, packaged
as a continuous threshold path. -/
-- @node: localJacksonCoefficientPath
noncomputable def localJacksonCoefficientPath {D : ℕ} (epsilon : ℝ) (K : ℕ)
    (center radius : Cell → ℝ) (hK : 0 < K)
    (hpull : ∀ lambda : Time, ContinuousOn
      (fun z : Fin 4 → ℝ => thresholdFunReal epsilon lambda
        (fun c => Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint
          (fun i => center (CellFourEquiv.symm i))
          (fun i => radius (CellFourEquiv.symm i)) z (CellFourEquiv c)))
      (Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube 4))
    (hD : 2 * (K - 1) ≤ D) (a : Fin 4 → Fin (D + 1)) : Path :=
  ⟨fun lambda => jacksonCoefficient epsilon lambda K center radius
      (fun i => (a i : ℕ)),
    jacksonCoefficient_continuous_time epsilon K center radius hK hpull hD a⟩

/-- Every local Jackson coefficient path has finite total variation. This is
the paper-side regularity premise required by the clipped Poisson factorial
path moment theorem. With [the specified inputs and conditions](hyp:D,epsilon,K,center,radius,hK,hpull,hD,a), [the stated relationship holds](goal). -/
-- @node: localJacksonCoefficientPath_bv
lemma localJacksonCoefficientPath_bv {D : ℕ} (epsilon : ℝ) (K : ℕ)
    (center radius : Cell → ℝ) (hK : 0 < K)
    (hpull : ∀ lambda : Time, ContinuousOn
      (fun z : Fin 4 → ℝ => thresholdFunReal epsilon lambda
        (fun c => Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint
          (fun i => center (CellFourEquiv.symm i))
          (fun i => radius (CellFourEquiv.symm i)) z (CellFourEquiv c)))
      (Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube 4))
    (hD : 2 * (K - 1) ≤ D) (a : Fin 4 → Fin (D + 1)) :
    eVariationOn
      (localJacksonCoefficientPath epsilon K center radius hK hpull hD a)
      Set.univ < ⊤ := by
  let p : Time → MvPolynomial (Fin 4) ℝ := fun lambda =>
    localJacksonPolynomial epsilon lambda K center radius
  have hdeg (lambda : Time) (i : Fin 4) : (p lambda).degreeOf i ≤ D :=
    (localJacksonPolynomial_degreeOf_le epsilon lambda K center radius hK
      (hpull lambda) i).trans hD
  have hgrid (b : Fin 4 → Fin (D + 1)) :
      Continuous (fun lambda : Time =>
        MvPolynomial.eval (fun i => (b i : ℝ)) (p lambda)) :=
    localJacksonPolynomial_fixed_eval_continuous_time epsilon K center radius hK
      hpull hD _
  have hcont (x : Fin 4 → ℝ)
      (hx : x ∈ Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube 4) :
      Continuous (fun lambda : Time => MvPolynomial.eval x (p lambda)) :=
    localJacksonPolynomial_eval_continuous_time epsilon K center radius hK hpull x hx
  have hcubeBV (x : Fin 4 → ℝ)
      (hx : x ∈ Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube 4) :
      eVariationOn
        (⟨fun lambda : Time => MvPolynomial.eval x (p lambda), hcont x hx⟩ : Path)
        Set.univ < ⊤ := by
    obtain ⟨C, hLip⟩ := localJacksonPolynomial_eval_lipschitz_time
      epsilon K center radius hK hpull x hx
    have hid : BoundedVariationOn (id : Time → Time) Set.univ := by
      have hm : Monotone (fun t : Time => (t : ℝ)) := fun s t hst => hst
      have hv : BoundedVariationOn (fun t : Time => (t : ℝ)) Set.univ :=
        MonotoneOn.boundedVariationOn (hm.monotoneOn _) (fun t _ =>
          abs_le.2 ⟨by linarith [t.property.1], t.property.2⟩)
      exact hv
    apply lt_top_iff_ne_top.mpr
    simpa [BoundedVariationOn, Function.comp_def] using
      hLip.comp_boundedVariationOn hid
  have h := tensorCoefficientPath_bv_of_cube p hdeg hgrid hcont hcubeBV a
  simpa [localJacksonCoefficientPath, tensorCoefficientPath,
    jacksonCoefficient_eq_tensorCoeffs] using h

/-- The clipped four-count factorial polynomial driven by the paper's local
Jackson coefficient paths. -/
-- @node: localJacksonFourPoissonFactorialPath
noncomputable def localJacksonFourPoissonFactorialPath {Ω : Type*} {D : ℕ}
    (epsilon : ℝ) (K : ℕ) (center radius : Cell → ℝ) (hK : 0 < K)
    (hpull : ∀ lambda : Time, ContinuousOn
      (fun z : Fin 4 → ℝ => thresholdFunReal epsilon lambda
        (fun c => Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint
          (fun i => center (CellFourEquiv.symm i))
          (fun i => radius (CellFourEquiv.symm i)) z (CellFourEquiv c)))
      (Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube 4))
    (hD : 2 * (K - 1) ≤ D) (W : Fin 4 → Ω → ℕ) (m cap : ℝ) (ω : Ω) : Path :=
  fourPoissonFactorialPath
    (localJacksonCoefficientPath epsilon K center radius hK hpull hD) W m
    (fun i => center (CellFourEquiv.symm i))
    (fun i => radius (CellFourEquiv.symm i)) cap ω

/-- Pointwise, the paper-specific factorial path is exactly the symmetric
clip of the Jackson coefficient polynomial in the normalized factorial
monomials. With [the specified inputs and conditions](hyp:D,epsilon,K,center,radius,hK,hpull,hD,W,m,cap,lambda), [the stated relationship holds](goal). -/
-- @node: localJacksonFourPoissonFactorialPath_apply
lemma localJacksonFourPoissonFactorialPath_apply {Ω : Type*} {D : ℕ}
    (epsilon : ℝ) (K : ℕ) (center radius : Cell → ℝ) (hK : 0 < K)
    (hpull : ∀ lambda : Time, ContinuousOn
      (fun z : Fin 4 → ℝ => thresholdFunReal epsilon lambda
        (fun c => Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint
          (fun i => center (CellFourEquiv.symm i))
          (fun i => radius (CellFourEquiv.symm i)) z (CellFourEquiv c)))
      (Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube 4))
    (hD : 2 * (K - 1) ≤ D) (W : Fin 4 → Ω → ℕ) (m cap : ℝ)
    (ω : Ω) (lambda : Time) :
    localJacksonFourPoissonFactorialPath epsilon K center radius hK hpull
        hD W m cap ω lambda =
      min cap (max (-cap)
        (∑ a : Fin 4 → Fin (D + 1),
          jacksonCoefficient epsilon lambda K center radius
              (fun i => (a i : ℕ)) *
            fourFactorialMonomial W m
              (fun i => center (CellFourEquiv.symm i))
              (fun i => radius (CellFourEquiv.symm i)) a ω)) := by
  simp [localJacksonFourPoissonFactorialPath, fourPoissonFactorialPath,
    clippedFinitePath, scalarClip, localJacksonCoefficientPath, mul_comm]

/-- Adding back the center threshold identifies the generic clipped factorial
path with the paper's complete clipped Jackson cell statistic. With [the specified inputs and conditions](hyp:epsilon,m,d,pilot,W,hK,hpull,lambda), [the stated relationship holds](goal). -/
-- @node: jacksonCellStatistic_eq_localJacksonFourPoissonFactorialPath
lemma jacksonCellStatistic_eq_localJacksonFourPoissonFactorialPath
    {Ω : Type*} (epsilon m : ℝ) (d : ℕ) (pilot : Cell → ℕ)
    (W : Fin 4 → Ω → ℕ) (hK : 0 < jacksonDegree d)
    (hpull : ∀ lambda : Time, ContinuousOn
      (fun z : Fin 4 → ℝ => thresholdFunReal epsilon lambda
        (fun c => Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint
          (fun i => pilotMidpoint m d pilot (CellFourEquiv.symm i))
          (fun i => pilotRadius m d pilot (CellFourEquiv.symm i)) z
          (CellFourEquiv c)))
      (Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube 4))
    (ω : Ω) (lambda : Time) :
    thresholdFunReal epsilon lambda (pilotMidpoint m d pilot) +
        localJacksonFourPoissonFactorialPath epsilon (jacksonDegree d)
          (pilotMidpoint m d pilot) (pilotRadius m d pilot) hK hpull
          (le_refl _) W m
          ((d : ℝ) ^ (1 / 4 : ℝ) * ∑ zeta : Cell,
            pilotRadius m d pilot zeta) ω lambda =
      jacksonCellStatistic epsilon lambda m d pilot
        (fun zeta => W (CellFourEquiv zeta) ω) := by
  rw [localJacksonFourPoissonFactorialPath_apply]
  unfold jacksonCellStatistic jacksonCellRaw
  dsimp only
  congr 2
  rw [add_sub_cancel_left]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  unfold fourFactorialMonomial factorialProduct centeredFactorial factorialLift
  rw [Finset.prod_div_distrib]
  simp only [Equiv.apply_symm_apply]

/-- The paper-specific local Jackson factorial path inherits measurability,
samplewise bounded variation, integrability, and the promoted exponential
square path-size estimate. With [the specified inputs and conditions](hyp:D,epsilon,K,center,radius,hK,hpull,hD,W,rate,hWmeas,hWlaw,hWindep,m,L,hm,hL,hR,hcenter,hvariance,cap,hcap), [the stated relationship holds](goal). -/
-- @node: localJacksonFourPoissonFactorialPath_sq_bound
lemma localJacksonFourPoissonFactorialPath_sq_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {D : ℕ} (epsilon : ℝ) (K : ℕ) (center radius : Cell → ℝ) (hK : 0 < K)
    (hpull : ∀ lambda : Time, ContinuousOn
      (fun z : Fin 4 → ℝ => thresholdFunReal epsilon lambda
        (fun c => Causalean.Mathlib.Analysis.JacksonApproximation.affinePoint
          (fun i => center (CellFourEquiv.symm i))
          (fun i => radius (CellFourEquiv.symm i)) z (CellFourEquiv c)))
      (Causalean.Mathlib.Analysis.JacksonApproximation.normalizedCube 4))
    (hD : 2 * (K - 1) ≤ D) (W : Fin 4 → Ω → ℕ) (rate : Fin 4 → NNReal)
    (hWmeas : ∀ i, Measurable (W i))
    (hWlaw : ∀ i, HasLaw (W i) (ProbabilityTheory.poissonMeasure (rate i)) μ)
    (hWindep : iIndepFun W μ) (m L : ℝ) (hm : 0 < m) (hL : 0 < L)
    (hR : ∀ i, 0 < radius (CellFourEquiv.symm i))
    (hcenter : ∀ i, |(rate i : ℝ) / m - center (CellFourEquiv.symm i)| ≤
      radius (CellFourEquiv.symm i))
    (hvariance : ∀ i, (rate i : ℝ) /
      (m ^ 2 * radius (CellFourEquiv.symm i) ^ 2) ≤ 1 / L)
    (cap : ℝ) (hcap : 0 ≤ cap) :
    Measurable (localJacksonFourPoissonFactorialPath epsilon K center radius hK hpull
      hD W m cap) ∧
      (∀ ω, eVariationOn
        (localJacksonFourPoissonFactorialPath epsilon K center radius hK hpull
          hD W m cap ω) Set.univ < ⊤) ∧
      Integrable (localJacksonFourPoissonFactorialPath epsilon K center radius hK hpull
        hD W m cap) μ ∧
      Integrable (fun ω => (pathSize
        (localJacksonFourPoissonFactorialPath epsilon K center radius hK hpull
          hD W m cap ω)) ^ 2) μ ∧
      (∫ ω, (pathSize
        (localJacksonFourPoissonFactorialPath epsilon K center radius hK hpull
          hD W m cap ω)) ^ 2 ∂μ) ≤
        (∑ a, (pathSize
          (localJacksonCoefficientPath epsilon K center radius hK hpull hD a)) ^ 2) *
          ∑ _a : Fin 4 → Fin (D + 1), Real.exp (4 * (D : ℝ) ^ 2 / L) := by
  unfold localJacksonFourPoissonFactorialPath
  exact fourPoissonFactorialPath_sq_bound μ
    (localJacksonCoefficientPath epsilon K center radius hK hpull hD)
    (localJacksonCoefficientPath_bv epsilon K center radius hK hpull hD)
    W rate hWmeas hWlaw hWindep m L hm hL
    (fun i => center (CellFourEquiv.symm i))
    (fun i => radius (CellFourEquiv.symm i)) hR hcenter hvariance cap hcap

/-- The paper's centered falling-factorial coordinate is exactly the generic
Poisson factorial lift. With [the specified inputs and conditions](hyp:m,z,N,h), [the stated relationship holds](goal). -/
-- @node: centeredFactorial_eq_factorialLift
lemma centeredFactorial_eq_factorialLift (m z : ℝ) (N h : ℕ) :
    centeredFactorial m z N h = factorialLift m z N h := by
  rfl

/-- A monomial's centered factorial lift on the pilot rectangle. -/
noncomputable def factorialMonomial (m : ℝ) (d : ℕ)
    (pilot eval : Cell → ℕ) (alpha : Fin 4 → ℕ) : ℝ :=
  ∏ i : Fin 4,
    centeredFactorial m (pilotMidpoint m d pilot (CellFourEquiv.symm i))
      (eval (CellFourEquiv.symm i)) (alpha i) /
      pilotRadius m d pilot (CellFourEquiv.symm i) ^ (alpha i)

/-- A paper factorial monomial is the generic normalized four-coordinate
factorial monomial after reindexing the four cells. With [the specified inputs and conditions](hyp:D,m,d,pilot,W,a), [the stated relationship holds](goal). -/
-- @node: factorialMonomial_eq_fourFactorialMonomial
lemma factorialMonomial_eq_fourFactorialMonomial {Ω : Type*} {D : ℕ}
    (m : ℝ) (d : ℕ) (pilot : Cell → ℕ) (W : Fin 4 → Ω → ℕ)
    (a : Fin 4 → Fin (D + 1)) (ω : Ω) :
    factorialMonomial m d pilot
      (fun zeta => W (CellFourEquiv zeta) ω) (fun i => (a i : ℕ)) =
      fourFactorialMonomial W m
        (fun i => pilotMidpoint m d pilot (CellFourEquiv.symm i))
        (fun i => pilotRadius m d pilot (CellFourEquiv.symm i)) a ω := by
  classical
  unfold factorialMonomial fourFactorialMonomial factorialProduct
  simp only [centeredFactorial_eq_factorialLift, Equiv.apply_symm_apply,
    Finset.prod_div_distrib]

/-- Under independent Poisson evaluation counts, the mean of a paper
factorial monomial is the corresponding normalized product of powers. With [the specified inputs and conditions](hyp:D,m,hm,d,pilot,W,rate,hWlaw,hWindep,a), [the stated relationship holds](goal). -/
-- @node: factorialMonomial_mean
lemma factorialMonomial_mean {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {D : ℕ}
    (m : ℝ) (hm : m ≠ 0) (d : ℕ) (pilot : Cell → ℕ)
    (W : Fin 4 → Ω → ℕ) (rate : Fin 4 → NNReal)
    (hWlaw : ∀ i, HasLaw (W i) (ProbabilityTheory.poissonMeasure (rate i)) μ)
    (hWindep : iIndepFun W μ) (a : Fin 4 → Fin (D + 1)) :
    (∫ ω, factorialMonomial m d pilot
      (fun zeta => W (CellFourEquiv zeta) ω) (fun i => (a i : ℕ)) ∂μ) =
      (∏ i, ((rate i : ℝ) / m -
          pilotMidpoint m d pilot (CellFourEquiv.symm i)) ^ (a i : ℕ)) /
        ∏ i, pilotRadius m d pilot (CellFourEquiv.symm i) ^ (a i : ℕ) := by
  simp_rw [factorialMonomial_eq_fourFactorialMonomial]
  unfold fourFactorialMonomial
  rw [integral_div]
  rw [factorialProduct_mean μ W rate hWlaw hWindep m]

/-- The paper's normalized four-coordinate factorial monomial inherits the
generic exponential square-moment envelope. With [the specified inputs and conditions](hyp:D,m,L,hm,hL,d,pilot,W,rate,hWlaw,hWindep,hR,hcenter,hvariance,a), [the stated relationship holds](goal). -/
-- @node: factorialMonomial_square_envelope
lemma factorialMonomial_square_envelope {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {D : ℕ}
    (m L : ℝ) (hm : 0 < m) (hL : 0 < L) (d : ℕ)
    (pilot : Cell → ℕ) (W : Fin 4 → Ω → ℕ) (rate : Fin 4 → NNReal)
    (hWlaw : ∀ i, HasLaw (W i) (ProbabilityTheory.poissonMeasure (rate i)) μ)
    (hWindep : iIndepFun W μ)
    (hR : ∀ i, 0 < pilotRadius m d pilot (CellFourEquiv.symm i))
    (hcenter : ∀ i, |(rate i : ℝ) / m -
      pilotMidpoint m d pilot (CellFourEquiv.symm i)| ≤
        pilotRadius m d pilot (CellFourEquiv.symm i))
    (hvariance : ∀ i, (rate i : ℝ) /
      (m ^ 2 * pilotRadius m d pilot (CellFourEquiv.symm i) ^ 2) ≤ 1 / L)
    (a : Fin 4 → Fin (D + 1)) :
    (∫ ω, (factorialMonomial m d pilot
      (fun zeta => W (CellFourEquiv zeta) ω) (fun i => (a i : ℕ))) ^ 2 ∂μ) ≤
      Real.exp (4 * (D : ℝ) ^ 2 / L) := by
  simp_rw [factorialMonomial_eq_fourFactorialMonomial]
  exact factorialProduct_four_square_envelope μ W rate hWlaw hWindep
    m L hm hL
    (fun i => pilotMidpoint m d pilot (CellFourEquiv.symm i))
    (fun i => pilotRadius m d pilot (CellFourEquiv.symm i))
    hR hcenter hvariance (fun i => (a i : ℕ)) D
    (fun i => Nat.le_of_lt_succ (a i).isLt)

end CausalSmith.Stat.DiscreteBudgetvalueCurve
