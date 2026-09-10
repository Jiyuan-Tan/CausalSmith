import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Helpers.FactorialRisk
import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Helpers.JacksonCertificate
import Mathlib.Algebra.MvPolynomial.Funext

/-! Product-Poisson L² control for normalized centered-factorial monomials. -/

namespace CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched

open MeasureTheory ProbabilityTheory
open scoped BigOperators

-- @node: centeredNormalizedPolynomial_eq_of_expansion
/-- A pointwise normalized-coordinate expansion identifies the actual centered
polynomial used by the factorial lift. This uses [the stated r condition holds](hyp:hr), and [the stated exp condition holds](hyp:hexp). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma centeredNormalizedPolynomial_eq_of_expansion
    (epsilon : ℝ) (Q : Rectangle) (p : MvPolynomial Cell ℝ)
    (S : Finset (Cell →₀ ℕ)) (coeff : (Cell →₀ ℕ) → ℝ)
    (hr : ∀ j, 0 < rectangleRadius Q j)
    (hexp : CenteredCoefficientExpansion epsilon Q p S coeff) :
    centeredNormalizedPolynomial p (rectangleCenter Q) (rectangleRadius Q)
        (globalCellValue epsilon (rectangleCenter Q)) =
      ∑ alpha ∈ S, MvPolynomial.monomial alpha (coeff alpha) := by
  apply MvPolynomial.funext
  intro y
  have h := hexp (fun j ↦ rectangleCenter Q j + rectangleRadius Q j * y j)
  change MvPolynomial.eval y
      (centeredNormalizedPolynomial p (rectangleCenter Q) (rectangleRadius Q)
        (globalCellValue epsilon (rectangleCenter Q))) = _
  unfold centeredNormalizedPolynomial
  rw [map_sub, MvPolynomial.eval_C]
  have heval :
      MvPolynomial.eval y
          (MvPolynomial.eval₂Hom MvPolynomial.C
            (fun j ↦ MvPolynomial.C (rectangleCenter Q j) +
              MvPolynomial.C (rectangleRadius Q j) * MvPolynomial.X j) p) =
        MvPolynomial.eval
          (fun j ↦ rectangleCenter Q j + rectangleRadius Q j * y j) p := by
    rw [MvPolynomial.map_eval₂Hom]
    apply MvPolynomial.eval₂Hom_congr
    · ext r
      simp
    · funext j
      simp
    · rfl
  rw [heval]
  simp only [map_sum, MvPolynomial.eval_monomial]
  rw [h]
  apply Finset.sum_congr rfl
  intro alpha halpha
  congr 1
  have hj (j : Cell) :
      (rectangleCenter Q j + rectangleRadius Q j * y j - rectangleCenter Q j) /
          rectangleRadius Q j = y j := by
    field_simp [ne_of_gt (hr j)]
    ring
  simp_rw [hj]
  rw [alpha.prod_fintype _ (fun _ ↦ pow_zero _)]

-- @node: centeredNormalizedPolynomial_coeffL1_le_of_expansion
/-- The coefficient envelope in a normalized pointwise expansion bounds the
coefficient ℓ1 norm of the centered polynomial actually lifted by the estimator. This uses [the stated r condition holds](hyp:hr), and [the stated exp condition holds](hyp:hexp). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma centeredNormalizedPolynomial_coeffL1_le_of_expansion
    (epsilon : ℝ) (Q : Rectangle) (p : MvPolynomial Cell ℝ)
    (S : Finset (Cell →₀ ℕ)) (coeff : (Cell →₀ ℕ) → ℝ)
    (hr : ∀ j, 0 < rectangleRadius Q j)
    (hexp : CenteredCoefficientExpansion epsilon Q p S coeff) :
    ∑ alpha ∈ (centeredNormalizedPolynomial p (rectangleCenter Q) (rectangleRadius Q)
        (globalCellValue epsilon (rectangleCenter Q))).support,
        |(centeredNormalizedPolynomial p (rectangleCenter Q) (rectangleRadius Q)
          (globalCellValue epsilon (rectangleCenter Q))).coeff alpha| ≤
      ∑ alpha ∈ S, |coeff alpha| := by
  let centered := centeredNormalizedPolynomial p (rectangleCenter Q) (rectangleRadius Q)
    (globalCellValue epsilon (rectangleCenter Q))
  have heq : centered =
      ∑ alpha ∈ S, MvPolynomial.monomial alpha (coeff alpha) :=
    centeredNormalizedPolynomial_eq_of_expansion epsilon Q p S coeff hr hexp
  have hcoeff (alpha : Cell →₀ ℕ) :
      centered.coeff alpha = if alpha ∈ S then coeff alpha else 0 := by
    rw [heq]
    simp [MvPolynomial.coeff_sum]
  have hsupport : centered.support ⊆ S := by
    intro alpha halpha
    by_contra hnot
    have hzero : centered.coeff alpha = 0 := by simp [hcoeff, hnot]
    exact (centered.mem_support_iff.mp halpha) hzero
  calc
    ∑ alpha ∈ centered.support, |centered.coeff alpha| =
        ∑ alpha ∈ centered.support, |coeff alpha| := by
      apply Finset.sum_congr rfl
      intro alpha halpha
      rw [hcoeff, if_pos (hsupport halpha)]
    _ ≤ ∑ alpha ∈ S, |coeff alpha| := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsupport
        (fun alpha _halpha _hnot ↦ abs_nonneg (coeff alpha))

-- @node: jacksonCenteredNormalizedPolynomial_coeffL1_le
/-- The chosen Jackson polynomial has the explicit normalized coefficient
envelope needed by the factorial-risk calculation. This uses [the overlap parameter satisfies its stated range restriction](hyp:hepsilon), and [the approximation degree satisfies its stated restriction](hyp:hK), and [the potential-outcome law satisfies the stated causal restrictions](hyp:hQ), and [the stated q0 condition holds](hyp:hQ0), and [the stated qr condition holds](hyp:hQr). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma jacksonCenteredNormalizedPolynomial_coeffL1_le
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (K : ℕ) (hK : 2 ≤ K)
    (Q : Rectangle) (hQ : Q.Valid) (hQ0 : ∀ j, 0 ≤ Q.1 j)
    (hQr : ∀ j, 0 < rectangleRadius Q j) :
    (∑ alpha ∈ (centeredNormalizedPolynomial
        (jacksonTensorPolynomial epsilon K hK Q hQ hQ0)
        (rectangleCenter Q) (rectangleRadius Q)
        (globalCellValue epsilon (rectangleCenter Q))).support,
      |(centeredNormalizedPolynomial
        (jacksonTensorPolynomial epsilon K hK Q hQ hQ0)
        (rectangleCenter Q) (rectangleRadius Q)
        (globalCellValue epsilon (rectangleCenter Q))).coeff alpha| ≤
      ((2 : ℝ) ^ 60) ^ K * (1 + epsilon⁻¹) *
        ∑ j : Cell, rectangleRadius Q j) ∧
    (∀ alpha ∈ (centeredNormalizedPolynomial
        (jacksonTensorPolynomial epsilon K hK Q hQ hQ0)
        (rectangleCenter Q) (rectangleRadius Q)
        (globalCellValue epsilon (rectangleCenter Q))).support,
      ∀ j, alpha j ≤ 2 * (K - 1)) := by
  classical
  let data := Classical.choice
    (jacksonTensorPolynomialData_exists epsilon K hK Q hQ0 hepsilon hQr)
  have hp : jacksonTensorPolynomial epsilon K hK Q hQ hQ0 = data.p := by
    simp only [jacksonTensorPolynomial, dif_pos hepsilon, dif_pos hQr, data]
  let qCell : MvPolynomial Cell ℝ := MvPolynomial.rename cellFinFourEquiv.symm data.q
  let g : (Fin 4 →₀ ℕ) → (Cell →₀ ℕ) := Finsupp.mapDomain cellFinFourEquiv.symm
  have hexp : CenteredCoefficientExpansion epsilon Q
      (jacksonTensorPolynomial epsilon K hK Q hQ hQ0)
      (data.q.support.image g) qCell.coeff := by
    intro v
    rw [hp, data.physicalEval]
    change MvPolynomial.eval
      ((fun j => (v j - rectangleCenter Q j) / rectangleRadius Q j) ∘
        cellFinFourEquiv.symm) data.q = _
    rw [← MvPolynomial.eval_rename]
    change MvPolynomial.eval _ qCell = _
    rw [MvPolynomial.eval_eq']
    rw [show qCell.support = data.q.support.image g by
      exact MvPolynomial.support_rename_of_injective cellFinFourEquiv.symm.injective]
  constructor
  · refine (centeredNormalizedPolynomial_coeffL1_le_of_expansion
      epsilon Q _ _ _ hQr hexp).trans ?_
    change (∑ alpha ∈ data.q.support.image g, |qCell.coeff alpha|) ≤ _
    rw [Finset.sum_image (Finsupp.mapDomain_injective
      cellFinFourEquiv.symm.injective).injOn]
    simp only [qCell, MvPolynomial.coeff_rename_mapDomain,
      cellFinFourEquiv.symm.injective]
    change Causalean.Mathlib.Analysis.JacksonApproximation.mvCoeffL1 data.q ≤ _
    refine data.coefficientBound.trans ?_
    have hpow : (2 : ℝ) ^ (40 * K + 20) ≤ ((2 : ℝ) ^ 60) ^ K := by
      rw [← pow_mul]
      exact_mod_cast Nat.pow_le_pow_right (n := 2) (by omega)
        (by omega : 40 * K + 20 ≤ 60 * K)
    gcongr
    exact Finset.sum_nonneg fun j _ => le_of_lt (hQr j)
  · have heq := centeredNormalizedPolynomial_eq_of_expansion
      epsilon Q _ _ _ hQr hexp
    intro alpha halpha j
    have halphaS : alpha ∈ data.q.support.image g := by
      by_contra hnot
      have hz : (centeredNormalizedPolynomial
          (jacksonTensorPolynomial epsilon K hK Q hQ hQ0)
          (rectangleCenter Q) (rectangleRadius Q)
          (globalCellValue epsilon (rectangleCenter Q))).coeff alpha = 0 := by
        rw [heq]
        simp [MvPolynomial.coeff_sum, hnot]
      exact (MvPolynomial.mem_support_iff.mp halpha) hz
    rw [Finset.mem_image] at halphaS
    obtain ⟨beta, hbeta, rfl⟩ := halphaS
    rw [Finsupp.mapDomain_equiv_apply]
    exact data.normalizedCoordinateDegree beta hbeta (cellFinFourEquiv j)

-- @node: normalizedCenteredFactorialMonomial
/-- The tensor monomial obtained by multiplying normalized centered-factorial
coordinates with the exponents in `alpha`. -/
noncomputable def normalizedCenteredFactorialMonomial (m : ℝ)
    (center radius : Cell → ℝ) (alpha : Cell →₀ ℕ) (eval : Cell → ℕ) : ℝ :=
  ∏ j : Cell, centeredFactorial m (alpha j) (eval j) (center j) /
    radius j ^ alpha j

-- @node: normalizedCenteredFactorialMonomial_memLp_two
/-- Every normalized centered-factorial tensor monomial is square-integrable
under a product of scalar Poisson laws when all normalization radii are nonzero. This uses [the stated r condition holds](hyp:hr). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma normalizedCenteredFactorialMonomial_memLp_two
    (m : ℝ) (q center radius : Cell → ℝ) (hr : ∀ j, 0 < radius j)
    (alpha : Cell →₀ ℕ) :
    MemLp (normalizedCenteredFactorialMonomial m center radius alpha) 2
      (Measure.pi (fun j : Cell ↦ poissonMeasure (m * q j).toNNReal)) := by
  have hcoordInt (j : Cell) : Integrable (fun N : ℕ ↦
      (centeredFactorial m (alpha j) N (center j) /
        radius j ^ alpha j) ^ 2) (poissonMeasure (m * q j).toNNReal) := by
    have hi := integrable_centeredFactorial_mul_poisson
      (m * q j).toNNReal m (center j) (alpha j) (alpha j)
    have hi' := hi.const_mul (1 / radius j ^ (2 * alpha j))
    apply hi'.congr
    filter_upwards with N
    field_simp [ne_of_gt (hr j)]
    ring
  apply (memLp_two_iff_integrable_sq (by fun_prop)).2
  have hprod := Integrable.fintype_prod hcoordInt
  convert hprod using 1
  funext eval
  simp [normalizedCenteredFactorialMonomial, Finset.prod_pow]

-- @node: integral_sq_normalizedCenteredFactorialMonomial_le_exp
/-- Coordinatewise Poisson noise-to-radius bounds tensorize: the normalized
monomial's second moment is bounded by the exponential of the sum of squared
coordinate degrees. This uses [the Poisson intensity is positive](hyp:hm), and [the cell masses satisfy their stated restrictions](hyp:hq), and [the stated r condition holds](hyp:hr), and [the centering parameters satisfy the stated bounds](hyp:hcenter), and [the intensity-to-center ratio satisfies the stated bound](hyp:hratio). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma integral_sq_normalizedCenteredFactorialMonomial_le_exp
    (m : ℝ) (q center radius : Cell → ℝ) (rho : ℝ)
    (hm : 0 < m) (hq : ∀ j, 0 ≤ q j) (hr : ∀ j, 0 < radius j)
    (hcenter : ∀ j, |q j - center j| ≤ radius j)
    (hratio : ∀ j, q j / (m * radius j ^ 2) ≤ rho)
    (alpha : Cell →₀ ℕ) :
    ∫ eval : Cell → ℕ,
        normalizedCenteredFactorialMonomial m center radius alpha eval ^ 2
      ∂Measure.pi (fun j : Cell ↦ poissonMeasure (m * q j).toNNReal) ≤
      Real.exp (rho * ∑ j : Cell, (alpha j : ℝ) ^ 2) := by
  have hcoordInt (j : Cell) : Integrable (fun N : ℕ ↦
      (centeredFactorial m (alpha j) N (center j) /
        radius j ^ alpha j) ^ 2) (poissonMeasure (m * q j).toNNReal) := by
    have hi := integrable_centeredFactorial_mul_poisson
      (m * q j).toNNReal m (center j) (alpha j) (alpha j)
    have hi' := hi.const_mul (1 / radius j ^ (2 * alpha j))
    apply hi'.congr
    filter_upwards with N
    field_simp [ne_of_gt (hr j)]
    ring
  rw [show (fun eval : Cell → ℕ ↦
      normalizedCenteredFactorialMonomial m center radius alpha eval ^ 2) =
      fun eval ↦ ∏ j : Cell,
        (centeredFactorial m (alpha j) (eval j) (center j) /
          radius j ^ alpha j) ^ 2 by
    funext eval
    simp [normalizedCenteredFactorialMonomial, Finset.prod_pow]]
  rw [MeasureTheory.integral_fintype_prod_eq_prod (fun j N ↦
    (centeredFactorial m (alpha j) N (center j) /
      radius j ^ alpha j) ^ 2)]
  calc
    ∏ j : Cell, ∫ N : ℕ,
        (centeredFactorial m (alpha j) N (center j) /
          radius j ^ alpha j) ^ 2
        ∂poissonMeasure (m * q j).toNNReal ≤
        ∏ j : Cell, Real.exp ((alpha j : ℝ) ^ 2 * rho) := by
      apply Finset.prod_le_prod
      · intro j _hj
        positivity
      · intro j _hj
        exact integral_sq_normalizedCenteredFactorial_le_exp
          m (q j) (center j) (radius j) rho hm (hq j) (hr j)
            (hcenter j) (hratio j) (alpha j)
    _ = Real.exp (rho * ∑ j : Cell, (alpha j : ℝ) ^ 2) := by
      rw [← Real.exp_sum]
      congr 1
      rw [← Finset.sum_mul]
      ring

-- @node: integral_sq_normalizedCenteredFactorialMonomial_le_exp_degree
/-- If every coordinate degree is at most `K`, the four-coordinate tensor
monomial has the uniform exponential second-moment bound used by the Jackson
coefficient envelope. This uses [the Poisson intensity is positive](hyp:hm), and [the cell masses satisfy their stated restrictions](hyp:hq), and [the stated r condition holds](hyp:hr), and [the centering parameters satisfy the stated bounds](hyp:hcenter), and [the intensity-to-center ratio satisfies the stated bound](hyp:hratio), and [the exponential-moment parameter is below one](hyp:hrho), and [the multi-index degree satisfies the stated bound](hyp:hdegree). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma integral_sq_normalizedCenteredFactorialMonomial_le_exp_degree
    (m : ℝ) (q center radius : Cell → ℝ) (rho : ℝ)
    (hm : 0 < m) (hq : ∀ j, 0 ≤ q j) (hr : ∀ j, 0 < radius j)
    (hcenter : ∀ j, |q j - center j| ≤ radius j)
    (hratio : ∀ j, q j / (m * radius j ^ 2) ≤ rho)
    (hrho : 0 ≤ rho) (alpha : Cell →₀ ℕ) (K : ℕ)
    (hdegree : ∀ j, alpha j ≤ K) :
    ∫ eval : Cell → ℕ,
        normalizedCenteredFactorialMonomial m center radius alpha eval ^ 2
      ∂Measure.pi (fun j : Cell ↦ poissonMeasure (m * q j).toNNReal) ≤
      Real.exp (4 * (K : ℝ) ^ 2 * rho) := by
  refine (integral_sq_normalizedCenteredFactorialMonomial_le_exp
    m q center radius rho hm hq hr hcenter hratio alpha).trans ?_
  apply Real.exp_le_exp.mpr
  have hsum : ∑ j : Cell, (alpha j : ℝ) ^ 2 ≤ 4 * (K : ℝ) ^ 2 := by
    calc
      ∑ j : Cell, (alpha j : ℝ) ^ 2 ≤ ∑ _j : Cell, (K : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro j _hj
        exact (sq_le_sq₀ (by positivity) (by positivity)).2 (by
          exact_mod_cast hdegree j)
      _ = 4 * (K : ℝ) ^ 2 := by norm_num [Cell]
  nlinarith

-- @node: factorialPolynomialLift_sq_le_coeffL1
/-- A centered polynomial lift inherits a product-Poisson L² bound from its
normalized coefficient ℓ1 norm and a common coordinate-degree bound. This uses [the Poisson intensity is positive](hyp:hm), and [the cell masses satisfy their stated restrictions](hyp:hq), and [the stated r condition holds](hyp:hr), and [the centering parameters satisfy the stated bounds](hyp:hcenter), and [the intensity-to-center ratio satisfies the stated bound](hyp:hratio), and [the exponential-moment parameter is below one](hyp:hrho), and [the multi-index degree satisfies the stated bound](hyp:hdegree). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma factorialPolynomialLift_sq_le_coeffL1
    (m : ℝ) (q center radius : Cell → ℝ) (rho : ℝ)
    (hm : 0 < m) (hq : ∀ j, 0 ≤ q j) (hr : ∀ j, 0 < radius j)
    (hcenter : ∀ j, |q j - center j| ≤ radius j)
    (hratio : ∀ j, q j / (m * radius j ^ 2) ≤ rho)
    (hrho : 0 ≤ rho) (p : MvPolynomial Cell ℝ) (centerValue : ℝ) (K : ℕ)
    (hdegree : ∀ alpha ∈ (centeredNormalizedPolynomial p center radius centerValue).support,
      ∀ j, alpha j ≤ K) :
    ∫ eval : Cell → ℕ,
        factorialPolynomialLift m p eval center radius centerValue ^ 2
      ∂Measure.pi (fun j : Cell ↦ poissonMeasure (m * q j).toNNReal) ≤
      (∑ alpha ∈ (centeredNormalizedPolynomial p center radius centerValue).support,
          |(centeredNormalizedPolynomial p center radius centerValue).coeff alpha|) ^ 2 *
        Real.exp (4 * (K : ℝ) ^ 2 * rho) := by
  let centered := centeredNormalizedPolynomial p center radius centerValue
  let mu := Measure.pi (fun j : Cell ↦ poissonMeasure (m * q j).toNNReal)
  let R := Real.exp (2 * (K : ℝ) ^ 2 * rho)
  have hR : 0 ≤ R := le_of_lt (Real.exp_pos _)
  have hbase := integral_sq_finset_sum_le_coeffL1 mu centered.support centered.coeff
    (fun alpha ↦ normalizedCenteredFactorialMonomial m center radius alpha) R hR
    (fun alpha _halpha ↦
      normalizedCenteredFactorialMonomial_memLp_two m q center radius hr alpha)
    (fun alpha halpha ↦ by
      have h := integral_sq_normalizedCenteredFactorialMonomial_le_exp_degree
        m q center radius rho hm hq hr hcenter hratio hrho alpha K
          (hdegree alpha halpha)
      change (∫ eval : Cell → ℕ,
          normalizedCenteredFactorialMonomial m center radius alpha eval ^ 2
        ∂Measure.pi (fun j : Cell ↦ poissonMeasure (m * q j).toNNReal)) ≤ R ^ 2
      refine h.trans_eq ?_
      dsimp [R]
      calc
        Real.exp (4 * (K : ℝ) ^ 2 * rho) =
            Real.exp (2 * (K : ℝ) ^ 2 * rho + 2 * (K : ℝ) ^ 2 * rho) := by
              congr 1
              ring
        _ = Real.exp (2 * (K : ℝ) ^ 2 * rho) ^ 2 := by
          rw [Real.exp_add]
          ring)
  have hRsq : R ^ 2 = Real.exp (4 * (K : ℝ) ^ 2 * rho) := by
    dsimp [R]
    calc
      Real.exp (2 * (K : ℝ) ^ 2 * rho) ^ 2 =
          Real.exp (2 * (K : ℝ) ^ 2 * rho + 2 * (K : ℝ) ^ 2 * rho) := by
            rw [Real.exp_add]
            ring
      _ = Real.exp (4 * (K : ℝ) ^ 2 * rho) := by
        congr 1
        ring
  rw [hRsq] at hbase
  change (∫ eval : Cell → ℕ,
      factorialPolynomialLift m p eval center radius centerValue ^ 2 ∂mu) ≤ _
  simpa only [factorialPolynomialLift, centered, mu,
    normalizedCenteredFactorialMonomial] using hbase

end CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched
