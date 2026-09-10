import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Helpers.FactorialRisk
import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Helpers.JacksonKernel
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Distributions.Uniform

set_option linter.style.longLine false
set_option linter.unusedVariables false

/-! Empirical-ratio fallback and the all-data Jackson--factorial estimator. -/

namespace CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched

open scoped BigOperators

/-- For [the specified observed sample, cell](hyp:sample,x), the [sample cell count is the number of observations in the specified alphabet cell](goal). -/
def sampleCellCount {n d : ℕ} (sample : Fin n → Obs d) (x : Fin d) : ℕ :=
  ∑ i, if (sample i).1 = x then 1 else 0

/-- For [the specified observed sample, cell, treatment arm](hyp:sample,x,a), the [sample arm count is the number of observations in the specified cell and treatment arm](goal). -/
def sampleArmCount {n d : ℕ} (sample : Fin n → Obs d) (x : Fin d) (a : Bool) : ℕ :=
  ∑ i, if (sample i).1 = x ∧ (sample i).2.1 = a then 1 else 0

/-- For [the specified observed sample, cell, treatment arm](hyp:sample,x,a), the [sample success count is the number of successful observations in the specified cell and treatment arm](goal). -/
def sampleSuccessCount {n d : ℕ} (sample : Fin n → Obs d) (x : Fin d) (a : Bool) : ℕ :=
  ∑ i, if (sample i).1 = x ∧ (sample i).2.1 = a ∧ (sample i).2.2 then 1 else 0

-- @node: def:empirical-ratio-estimator
/-- For [the specified observed sample](hyp:sample), the [empirical-ratio estimator sums empirical cell shares times the larger of the two totalized within-arm success ratios](goal). -/
noncomputable def empiricalRatioEstimator {n d : ℕ} (sample : Fin n → Obs d) : ℝ :=
  ∑ x : Fin d, (sampleCellCount sample x : ℝ) / n *
    max ((sampleSuccessCount sample x false : ℝ) / sampleArmCount sample x false)
      ((sampleSuccessCount sample x true : ℝ) / sampleArmCount sample x true)
  -- @realizes \(\widehat V_{n,d}^{\mathrm{ER}}\)(empirical cell ratios)

/-- The named universal tuning constants whose admissible values are chosen by the risk theorem. -/
structure JacksonTuning where
  pilotRadiusConstant : ℝ -- @realizes \(H_0\)(positive universal radius constant)
  jacksonDegreeConstant : ℝ -- @realizes \(\kappa\)(universal constant in (0,1))
  boundedAlphabetCutoff : ℕ -- @realizes \(D_0\)(finite-alphabet cutoff)
  pilotRadiusConstant_pos : 0 < pilotRadiusConstant
  jacksonDegreeConstant_pos : 0 < jacksonDegreeConstant
  jacksonDegreeConstant_lt_one : jacksonDegreeConstant < 1

/-- For [the specified tuning rule, alphabet size](hyp:tuning,d), the [Jackson degree is the larger of two and the integer part of the tuning constant times the logarithmic alphabet size](goal). -/
noncomputable def jacksonDegree (tuning : JacksonTuning) (d : ℕ) : ℕ :=
  max 2 ⌊tuning.jacksonDegreeConstant * logAlphabet d⌋₊
  -- @realizes \(K_d\)(max of two and scaled logarithm)

/-- [the stated jackson degree lower bound two relation holds](goal). -/
lemma jacksonDegree_ge_two (tuning : JacksonTuning) (d : ℕ) :
    2 ≤ jacksonDegree tuning d := by
  exact le_max_left 2 _

/-- Count one observed four-cell coordinate among the first `M` units carrying a given fair mark. -/
def markedCellCount {n d : ℕ} (sample : Fin n → Obs d) (M : ℕ)
    (marks : Fin n → Bool) (pilot : Bool) (x : Fin d) (j : Cell) : ℕ :=
  ∑ i, if i.1 < M ∧ marks i = pilot ∧ (sample i).1 = x ∧
      (sample i).2.1 = finTwoEquiv j.1 ∧ (sample i).2.2 = finTwoEquiv j.2 then 1 else 0
  -- @realizes \(B_i\)(Bool-valued fair mark used by the count)

/-- Coordinatewise pilot center `c_j = N'_j/m`. -/
noncomputable def pilotCenter (m : ℝ) (pilot : Cell → ℕ) (j : Cell) : ℝ :=
  (pilot j : ℝ) / m

/-- Coordinatewise pilot radius `h_j` from the frozen estimator definition. -/
noncomputable def pilotRadius (tuning : JacksonTuning) (m : ℝ) (d : ℕ)
    (pilot : Cell → ℕ) (j : Cell) : ℝ :=
  tuning.pilotRadiusConstant *
    (Real.sqrt (pilotCenter m pilot j * logAlphabet d / m) + logAlphabet d / m)

/-- Pilot-local rectangle constructed from the marked pilot counts. -/
noncomputable def pilotRectangle (tuning : JacksonTuning) (m : ℝ) (d : ℕ)
    (pilot : Cell → ℕ) : Rectangle :=
  (fun j => max 0 (pilotCenter m pilot j - pilotRadius tuning m d pilot j),
    fun j => pilotCenter m pilot j + pilotRadius tuning m d pilot j)
  -- @realizes \(Q_x\)(pilot rectangle from the displayed center and radius)

/-- If [the Poisson intensity is positive](hyp:hm), then [the stated pilot rectangle valid relation holds](goal). -/
lemma pilotRectangle_valid (tuning : JacksonTuning) (m : ℝ) (d : ℕ) (pilot : Cell → ℕ)
    (hm : 0 < m) :
    (pilotRectangle tuning m d pilot).Valid := by
  intro j
  have hlog : 0 ≤ logAlphabet d := by
    by_cases hd : d = 0
    · simp [logAlphabet, hd]
    · have hdpos : (0 : ℝ) < d := by exact_mod_cast (Nat.pos_of_ne_zero hd)
      have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hd)
      have hexp : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
      have hprod : 1 ≤ Real.exp 1 * (d : ℝ) := by nlinarith
      exact Real.log_nonneg hprod
  have hcenter : 0 ≤ pilotCenter m pilot j := by
    exact div_nonneg (Nat.cast_nonneg _) (le_of_lt hm)
  have hradius : 0 ≤ pilotRadius tuning m d pilot j := by
    unfold pilotRadius
    have hfrac : 0 ≤ pilotCenter m pilot j * logAlphabet d / m := by positivity
    have hlogdiv : 0 ≤ logAlphabet d / m := by positivity
    exact mul_nonneg (le_of_lt tuning.pilotRadiusConstant_pos)
      (add_nonneg (Real.sqrt_nonneg _) hlogdiv)
  simp only [pilotRectangle]
  exact max_le (by positivity) (by linarith)

/-- [the stated pilot rectangle nonnegativity relation holds](goal). -/
lemma pilotRectangle_nonneg (tuning : JacksonTuning) (m : ℝ) (d : ℕ)
    (pilot : Cell → ℕ) :
    ∀ j, 0 ≤ (pilotRectangle tuning m d pilot).1 j := by
  intro j
  simp [pilotRectangle]

-- @node: pilotRectangle_radius_pos
/-- In the paper's nontrivial alphabet regime, every pilot rectangle has a
strictly positive radius, including coordinates whose pilot count is zero. This uses [the Poisson intensity is positive](hyp:hm), and [the alphabet size satisfies its stated restriction](hyp:hd). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma pilotRectangle_radius_pos (tuning : JacksonTuning) (m : ℝ) (d : ℕ)
    (pilot : Cell → ℕ) (hm : 0 < m) (hd : 1 ≤ d) :
    ∀ j, 0 < rectangleRadius (pilotRectangle tuning m d pilot) j := by
  intro j
  have hdR : (0 : ℝ) < d := by positivity
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hlog : 0 < logAlphabet d := by
    rw [logAlphabet]
    apply Real.log_pos
    have hexp : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
    exact hexp.trans_le (by
      simpa using mul_le_mul_of_nonneg_left hd1 (Real.exp_nonneg 1))
  have hcenter : 0 ≤ pilotCenter m pilot j := by
    exact div_nonneg (Nat.cast_nonneg _) (le_of_lt hm)
  have hsqrt : 0 ≤ Real.sqrt (pilotCenter m pilot j * logAlphabet d / m) :=
    Real.sqrt_nonneg _
  have hradius : 0 < pilotRadius tuning m d pilot j := by
    unfold pilotRadius
    exact mul_pos tuning.pilotRadiusConstant_pos
      (add_pos_of_nonneg_of_pos hsqrt (div_pos hlog hm))
  simp only [rectangleRadius, pilotRectangle]
  by_cases h : pilotCenter m pilot j - pilotRadius tuning m d pilot j ≤ 0
  · rw [max_eq_left h]
    nlinarith
  · rw [max_eq_right (le_of_not_ge h)]
    nlinarith

/-- The clipped pilot-local cell statistic built from the Jackson polynomial and its factorial lift. -/
noncomputable def jacksonCellStatistic (tuning : JacksonTuning) (epsilon : ℝ) (d : ℕ) (m : ℝ)
    (pilot eval : Cell → ℕ) (hm : 0 < m) : ℝ :=
  let Q := pilotRectangle tuning m d pilot
  let center := rectangleCenter Q
  let radius := rectangleRadius Q
  let p := jacksonTensorPolynomial epsilon (jacksonDegree tuning d) (jacksonDegree_ge_two tuning d) Q
    (pilotRectangle_valid tuning m d pilot hm) (pilotRectangle_nonneg tuning m d pilot)
  let centerValue := globalCellValue epsilon center
  let raw := centerValue + factorialPolynomialLift m p eval center radius centerValue
  let scale := (1 + epsilon⁻¹) * ∑ j : Cell, radius j
  max (globalCellValue epsilon center - d ^ (1 / 4 : ℝ) * (1 + epsilon⁻¹) * ∑ j, radius j)
    (min raw (globalCellValue epsilon center + d ^ (1 / 4 : ℝ) * scale))
  -- @realizes \(N'_{\jmath,x}\)(pilot-count input) @realizes \(N_{\jmath,x}\)(evaluation-count input)
  -- @realizes \(Q_x\)(rectangle encoded by center and radius) @realizes \(T_x^{\mathrm{JF}}\)(clipped cell statistic)

/-- The fair product law of the Bernoulli marks. -/
noncomputable def fairMarkLaw (n : ℕ) : MeasureTheory.Measure (Fin n → Bool) :=
  (PMF.uniformOfFintype (Fin n → Bool)).toMeasure
  -- @realizes \(B_i\)(independent fair Bool marks)

/-- Randomized projected statistic before Rao--Blackwellization. -/
noncomputable def jacksonRandomizedStatistic {n d : ℕ} (tuning : JacksonTuning) (epsilon : ℝ)
    (sample : Fin n → Obs d) (M : ℕ) (marks : Fin n → Bool) : ℝ :=
  if hn : 0 < n then
    if M ≤ n then
      let m : ℝ := n / 8
      let hm : 0 < m := by positivity
      let total := ∑ x : Fin d,
        jacksonCellStatistic tuning epsilon d m
          (fun j => markedCellCount sample M marks false x j)
          (fun j => markedCellCount sample M marks true x j) hm
      max 0 (min 1 total)
    else 0
  else 0
  -- @realizes \(M\)(Poisson auxiliary count) @realizes \(B_i\)(marks marginalized below)

-- @node: def:jackson-factorial-estimator
/-- For [the specified tuning rule, overlap level, observed sample](hyp:tuning,epsilon,sample), the [Jackson factorial estimator uses the empirical ratio for small alphabets, one half in the saturated regime, and otherwise averages the randomized Jackson statistic over Poisson truncation and fair marks](goal). -/
noncomputable def jacksonFactorialEstimator {n d : ℕ} (tuning : JacksonTuning) (epsilon : ℝ)
    (sample : Fin n → Obs d) : ℝ :=
  if d < tuning.boundedAlphabetCutoff then empiricalRatioEstimator sample
  else if (n : ℝ) < d / logAlphabet d then 1 / 2
  else
    ∫ M : ℕ, (∫ marks : Fin n → Bool,
      jacksonRandomizedStatistic tuning epsilon sample M marks ∂fairMarkLaw n)
      ∂ProbabilityTheory.poissonMeasure (Real.toNNReal (n / 4))
  -- @realizes \(M\)(Pois(n/4) count integrated out) @realizes \(B_i\)(fair marks explicitly integrated out)
  -- @realizes \(\widehat V_{n,d}^{\mathrm{JF}}\)(Rao--Blackwellized all-data estimator)

end CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched
