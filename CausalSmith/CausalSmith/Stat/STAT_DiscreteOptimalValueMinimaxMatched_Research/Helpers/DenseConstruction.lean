import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Helpers.L1Embedding
import CausalSmith.Mathlib.Probability.ParameterizedFinitePoissonSample
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Probability.Kernel.Composition.CompNotation

set_option linter.style.longLine false

/-! Dense sign submodel and the quantities used in its fuzzy-hypothesis lower bound. -/

namespace CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched

open MeasureTheory
open scoped BigOperators
open scoped ProbabilityTheory

-- @env: S4
variable (n d : ℕ) -- @realizes \(n\)(Poissonized sample scale) @realizes \(d\)(dense alphabet size; restricted below)

/-- For [the specified alphabet size](hyp:d), the [dense contrast is a coordinate vector whose alphabet has at least two cells and whose entries all lie between minus one half and one half](goal). -/
abbrev DenseContrast (d : ℕ) :=
  {theta : Fin d → ℝ // 2 ≤ d ∧ ∀ x, theta x ∈ Set.Icc (-1 / 2) (1 / 2)}
  -- @realizes \(\theta\)(contrast in the coordinate cube)

/-- For [the specified contrast, data point or sample](hyp:theta,z), the [dense full-data mass is the consistency-compatible product mass with the two outcome means shifted symmetrically by the contrast, and is zero off the consistency event](goal). -/
noncomputable def denseFullMass {d : ℕ} (theta : DenseContrast d) (z : FullObs d) : ℝ :=
  let mu0 := (1 - theta.1 z.1) / 2
  let mu1 := (1 + theta.1 z.1) / 2
  if z.2.2.1 = (if z.2.1 then z.2.2.2.2 else z.2.2.2.1) then
    (d : ℝ)⁻¹ / 2 * bernoulliMass mu0 z.2.2.2.1 * bernoulliMass mu1 z.2.2.2.2
  else 0

/-- [the dense full-data masses are nonnegative and sum to one](goal). -/
lemma denseFullMass_nonneg_sum {d : ℕ} (theta : DenseContrast d) :
    (∀ z, 0 ≤ denseFullMass theta z) ∧
    ∑ z : FullObs d, ENNReal.ofReal (denseFullMass theta z) = 1 := by
  classical
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by norm_num) theta.2.1))
  have hnonneg : ∀ z, 0 ≤ denseFullMass theta z := by
    rintro ⟨x, a, y, y0, y1⟩
    have htheta := theta.2.2 x
    have hmu0 : 0 ≤ (1 - theta.1 x) / 2 := by linarith [htheta.2]
    have hmu0' : (1 - theta.1 x) / 2 ≤ 1 := by linarith [htheta.1]
    have hmu1 : 0 ≤ (1 + theta.1 x) / 2 := by linarith [htheta.1]
    have hmu1' : (1 + theta.1 x) / 2 ≤ 1 := by linarith [htheta.2]
    have hdnonneg : 0 ≤ (d : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg d)
    fin_cases a <;> fin_cases y <;> fin_cases y0 <;> fin_cases y1 <;>
      simp [denseFullMass, bernoulliMass] <;> positivity
  constructor
  · exact hnonneg
  · rw [← ENNReal.ofReal_sum_of_nonneg (fun z _hz => hnonneg z)]
    have hsum : ∑ z : FullObs d, denseFullMass theta z = 1 := by
      rw [Fintype.sum_prod_type]
      calc
        ∑ x, ∑ w, denseFullMass theta (x, w) = ∑ _x : Fin d, (d : ℝ)⁻¹ := by
          apply Finset.sum_congr rfl
          intro x _hx
          simp [denseFullMass, bernoulliMass, Fintype.sum_prod_type]
          ring
        _ = 1 := by
          simp [hd]
    rw [hsum]
    norm_num

/-- For [the specified contrast](hyp:theta), the [dense law is the potential-outcome probability law induced by the dense full-data masses](goal). -/
noncomputable def denseLaw {d : ℕ} (theta : DenseContrast d) : PotentialLaw d :=
  ⟨PMF.ofFintype (fun z => ENNReal.ofReal (denseFullMass theta z))
    (denseFullMass_nonneg_sum theta).2⟩
  -- @realizes \(P_\theta^{\mathrm{dense}}\)(equal-mass dense causal law)

/-- the [positive even degree is a positive integer that is even](goal). -/
def EvenDegree := {K : ℕ // 0 < K ∧ Even K}
  -- @realizes \(K\)(positive even polynomial degree)

/-- For [the specified degree](hyp:K), the [best even-degree approximation error is the infimum uniform error for approximating absolute value on minus one to one by a polynomial of degree at most K](goal). -/
noncomputable def bestEvenApproxError (K : ℕ) : ℝ :=
  sInf {e : ℝ | ∃ p : Polynomial ℝ, p.natDegree ≤ K ∧
    ∀ t ∈ Set.Icc (-1 : ℝ) 1, abs (abs t - p.eval t) ≤ e}
  -- @realizes \(E_K\)(best uniform absolute-value approximation error)

/-- For [the specified alphabet size](hyp:d), the [lower approximation degree is twice the ceiling of four times the logarithmic alphabet size](goal). -/
noncomputable def lowerDegree (d : ℕ) : ℕ := 2 * ⌈4 * logAlphabet d⌉₊
  -- @realizes \(K_d^{\mathrm{lb}}\)(even lower-bound degree)

/-- [the lower approximation degree is even](goal). -/
lemma lowerDegree_even (d : ℕ) : Even (lowerDegree d) := by
  exact even_two_mul _

-- @node: lowerDegree_pos
/-- In the paper's nontrivial alphabet regime, the dense lower-bound degree is positive. This uses [the alphabet size satisfies its stated restriction](hyp:hd). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma lowerDegree_pos (d : ℕ) (hd : 2 ≤ d) : 0 < lowerDegree d := by
  rw [lowerDegree]
  apply Nat.mul_pos (by norm_num)
  apply Nat.ceil_pos.mpr
  have hdR : (1 : ℝ) < d := by exact_mod_cast hd
  have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
  have : 1 < Real.exp 1 * (d : ℝ) := by nlinarith [Real.exp_pos 1]
  exact mul_pos (by norm_num) (Real.log_pos this)

/-- The lower-bound degree, packaged in the positive-even carrier in its stated alphabet regime. -/
noncomputable def lowerEvenDegree (d : ℕ) (hd : 2 ≤ d) : EvenDegree :=
  ⟨lowerDegree d, lowerDegree_pos d hd, lowerDegree_even d⟩

-- @node: lowerDegree_log_bounds
/-- Rounding the logarithmic degree to the next even integer changes it by less than two. [The displayed identity or bound is the asserted conclusion](goal). -/
lemma lowerDegree_log_bounds (d : ℕ) :
    8 * logAlphabet d ≤ lowerDegree d ∧ lowerDegree d < 8 * logAlphabet d + 2 := by
  have hnonneg : 0 ≤ 4 * logAlphabet d := by
    by_cases hd : d = 0
    · simp [hd, logAlphabet]
    · have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd
      have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
      exact mul_nonneg (by norm_num) (Real.log_nonneg (by nlinarith))
  have hlo := Nat.le_ceil (4 * logAlphabet d)
  have hhi := Nat.ceil_lt_add_one hnonneg
  rw [lowerDegree]
  constructor <;> push_cast <;> nlinarith

/-- For [the specified sample size, alphabet size](hyp:n,d), the [dense regime holds when the alphabet has at least two cells and its squared size is smaller than the sample size](goal). [The alphabet contains at least two cells](step:1), and [its squared size is below the sample size](step:2). -/
def DenseRegime (n d : ℕ) : Prop := 2 ≤ d ∧ d ^ 2 < n
  -- @realizes \(d\)(at least two) @realizes \(n\)(positive dense-range sample size)

/-- For [the specified sample size, alphabet size](hyp:n,d), the [Poisson cell intensity is twice the sample size divided by the alphabet size](goal). -/
noncomputable def poissonCellIntensity (n d : ℕ) : ℝ := 2 * n / d
  -- @realizes \(\lambda_{n,d}\)(two-n expected count per cell)

/-- For [the specified sample size, alphabet size](hyp:n,d), the [dense amplitude is the square root of the lower approximation degree divided by sixty-four times the Poisson cell intensity](goal). -/
noncomputable def denseAmplitude (n d : ℕ) : ℝ :=
  Real.sqrt (lowerDegree d / (64 * poissonCellIntensity n d))
  -- @realizes \(a_{n,d}\)(dense contrast amplitude)

-- @node: denseAmplitude_sq
/-- Squaring the dense amplitude removes the square root and gives the paper's exact scale. [The displayed identity or bound is the asserted conclusion](goal). -/
lemma denseAmplitude_sq (n d : ℕ) (h : DenseRegime n d) :
    denseAmplitude n d ^ 2 = lowerDegree d * d / (128 * n) := by
  have hdNat : 0 < d := lt_of_lt_of_le (by omega) h.1
  have hdR : (0 : ℝ) < d := by exact_mod_cast hdNat
  have hnR : (0 : ℝ) < n := by
    exact_mod_cast (lt_trans (Nat.pow_pos hdNat) h.2)
  have hintensity : 0 < poissonCellIntensity n d := by
    rw [poissonCellIntensity]
    positivity
  rw [denseAmplitude, Real.sq_sqrt (by positivity), poissonCellIntensity]
  field_simp
  ring

/-- The intrinsic domain on which the scaled priors are laws on the stated
contrast cube.  The stronger inequality `d ^ 2 < n` belongs to the lower-bound
lemma, not to the construction itself. -/
def DenseConstructionDomain (n d : ℕ) (epsilon : ℝ) : Prop :=
  2 ≤ d ∧ 0 < epsilon ∧ epsilon < 1 / 2 ∧
    0 < denseAmplitude n d ∧ denseAmplitude n d ≤ 1 / 2

/-- the [dense sign-count pair records the two nonnegative integer counts in a cell](goal). -/
abbrev DenseSignCounts := ℕ × ℕ

/-- The actual likelihood ratio for the two independent sign counts in one dense
cell, relative to independent baseline `Pois(lambda/2)` counts.  The exponential
factors cancel between the two signs. -/
noncomputable def oneCellLikelihood (_lambda theta : ℝ) (r : DenseSignCounts) : ℝ :=
  (1 + theta) ^ r.1 * (1 - theta) ^ r.2
  -- @realizes \(r\)(pair of nonnegative sign-count indices) @realizes \(L_{\theta_x}\)(two-count likelihood ratio)

/-- For [the specified lambda](hyp:lambda), the [dense sign baseline is the product of two independent Poisson laws with equal half-intensity](goal). -/
noncomputable def denseSignBaseline (lambda : ℝ) : Measure DenseSignCounts :=
  (ProbabilityTheory.poissonMeasure (lambda / 2).toNNReal).prod
    (ProbabilityTheory.poissonMeasure (lambda / 2).toNNReal)

-- @node: poisson_power_mgf
/-- The probability generating function of a scalar Poisson count, in the
real-valued form needed by the dense likelihood calculation. [The displayed identity or bound is the asserted conclusion](goal). -/
lemma poisson_power_mgf (r : NNReal) (c : ℝ) :
    (∫ N : ℕ, c ^ N ∂ProbabilityTheory.poissonMeasure r) =
      Real.exp ((r : ℝ) * (c - 1)) := by
  rw [ProbabilityTheory.integral_poissonMeasure]
  simp only [smul_eq_mul]
  rw [show (fun n : ℕ => Real.exp (-(r : ℝ)) * (r : ℝ) ^ n /
      (n.factorial : ℝ) * c ^ n) =
      fun n => Real.exp (-(r : ℝ)) * (((r : ℝ) * c) ^ n /
        (n.factorial : ℝ)) by
    funext n
    rw [mul_pow]
    ring]
  rw [tsum_mul_left]
  rw [show (∑' n : ℕ, ((r : ℝ) * c) ^ n / (n.factorial : ℝ)) =
      Real.exp ((r : ℝ) * c) by
    simpa only [Real.exp_eq_exp_ℝ] using
      (NormedSpace.expSeries_div_hasSum_exp ((r : ℝ) * c)).tsum_eq]
  rw [← Real.exp_add]
  congr 1
  ring

-- @node: oneCellLikelihood_inner
/-- The two independent Poisson sign counts have the exponential likelihood
Gram kernel used by the moment-matching substrate. This uses [the Poisson intensity is nonnegative](hyp:hlambda). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma oneCellLikelihood_inner (lambda theta theta' : ℝ) (hlambda : 0 ≤ lambda) :
    (∫ r : DenseSignCounts, oneCellLikelihood lambda theta r *
        oneCellLikelihood lambda theta' r ∂denseSignBaseline lambda) =
      Real.exp (lambda * theta * theta') := by
  let lam : NNReal := lambda.toNNReal / 2
  have hlam : (lam : ℝ) = lambda / 2 := by
    simp [lam, Real.coe_toNNReal lambda hlambda]
  have hparam : (lambda / 2).toNNReal = lam := by
    apply NNReal.eq
    rw [Real.coe_toNNReal _ (div_nonneg hlambda (by norm_num)), hlam]
  rw [show denseSignBaseline lambda =
      (ProbabilityTheory.poissonMeasure lam).prod
        (ProbabilityTheory.poissonMeasure lam) by
    simp only [denseSignBaseline, hparam]]
  rw [show (fun r : DenseSignCounts => oneCellLikelihood lambda theta r *
      oneCellLikelihood lambda theta' r) = fun r =>
        (((1 + theta) * (1 + theta')) ^ r.1) *
          (((1 - theta) * (1 - theta')) ^ r.2) by
    funext r
    simp only [oneCellLikelihood]
    rw [mul_pow, mul_pow]
    ring]
  rw [MeasureTheory.integral_prod_mul]
  rw [poisson_power_mgf, poisson_power_mgf, ← Real.exp_add, hlam]
  congr 1
  ring

/-- [the stated dense amplitude range relation holds](goal). -/
lemma denseAmplitude_range (n d : ℕ) (h : DenseRegime n d) :
    0 < denseAmplitude n d ∧ denseAmplitude n d ≤ 1 / 2 := by
  rcases h with ⟨hd, hn⟩
  have hdNat : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hdNat
  have hnR : (d : ℝ) ^ 2 < (n : ℝ) := by exact_mod_cast hn
  have hlogd : Real.log (d : ℝ) ≤ (d : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos hdR
  have hlog_eq : logAlphabet d = 1 + Real.log (d : ℝ) := by
    rw [logAlphabet, Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hdR), Real.log_exp]
  have hlog_le : logAlphabet d ≤ (d : ℝ) := by linarith
  have hlog_pos : 0 < logAlphabet d := by
    rw [logAlphabet]
    exact Real.log_pos (by
      have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
      nlinarith [show (2 : ℝ) ≤ d by exact_mod_cast hd])
  have hceil_pos : 0 < ⌈4 * logAlphabet d⌉₊ :=
    Nat.ceil_pos.mpr (mul_pos (by norm_num) hlog_pos)
  have hdegree_pos_nat : 0 < lowerDegree d := by
    rw [lowerDegree]
    exact Nat.mul_pos (by norm_num) hceil_pos
  have hdegree_pos : 0 < (lowerDegree d : ℝ) := by exact_mod_cast hdegree_pos_nat
  have hceil_le : ⌈4 * logAlphabet d⌉₊ ≤ 4 * d := by
    rw [Nat.ceil_le]
    push_cast
    linarith
  have hdegree_le : (lowerDegree d : ℝ) ≤ 8 * d := by
    rw [lowerDegree]
    push_cast
    nlinarith [show (⌈4 * logAlphabet d⌉₊ : ℝ) ≤ 4 * d by exact_mod_cast hceil_le]
  have hnNat : 0 < n := by omega
  have hnR0 : 0 < (n : ℝ) := by exact_mod_cast hnNat
  have hintensity_pos : 0 < poissonCellIntensity n d := by
    rw [poissonCellIntensity]
    exact div_pos (mul_pos (by norm_num) hnR0) hdR
  have hratio_pos : 0 < (lowerDegree d : ℝ) /
      (64 * poissonCellIntensity n d) := div_pos hdegree_pos (mul_pos (by norm_num) hintensity_pos)
  have hratio_le : (lowerDegree d : ℝ) /
      (64 * poissonCellIntensity n d) ≤ (1 / 2 : ℝ) ^ 2 := by
    rw [show (1 / 2 : ℝ) ^ 2 = 1 / 4 by norm_num]
    apply (div_le_iff₀ (mul_pos (by norm_num) hintensity_pos)).2
    rw [poissonCellIntensity]
    rw [show (1 / 4 : ℝ) * (64 * (2 * n / d)) = 32 * n / d by ring]
    apply (le_div_iff₀ hdR).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hdegree_le) (le_of_lt hdR)]
  rw [denseAmplitude]
  constructor
  · exact Real.sqrt_pos.2 hratio_pos
  · rw [Real.sqrt_le_iff]
    exact ⟨by norm_num, hratio_le⟩
  -- @realizes \(a_{n,d}\)(positive and at most one half in the dense range)

-- @node: denseConstructionDomain_of_regime
/-- The dense sample-size regime and overlap inequalities discharge the construction domain. This uses [the sample size and alphabet lie in the dense regime](hyp:hregime), and [the overlap parameter satisfies its stated range restriction](hyp:hepsilon). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma denseConstructionDomain_of_regime (n d : ℕ) (epsilon : ℝ)
    (hregime : DenseRegime n d) (hepsilon : 0 < epsilon ∧ epsilon < 1 / 2) :
    DenseConstructionDomain n d epsilon := by
  exact ⟨hregime.1, hepsilon.1, hepsilon.2,
    (denseAmplitude_range n d hregime).1, (denseAmplitude_range n d hregime).2⟩

/-- For [the specified sample size, alphabet size](hyp:n,d), the [dense prior separation is the dense amplitude times the best even-polynomial approximation error](goal). -/
noncomputable def densePriorSeparation (n d : ℕ) : ℝ :=
  denseAmplitude n d * bestEvenApproxError (lowerDegree d)
  -- @realizes \(\Delta_{n,d}^{\mathrm{dense}}\)(prior target-mean gap)

/-- If [the stated e condition holds](hyp:hE), then [the stated dense prior separation range relation holds](goal). -/
lemma densePriorSeparation_range (n d : ℕ) (h : DenseRegime n d)
    (hE : 0 < bestEvenApproxError (lowerDegree d)) :
    0 < densePriorSeparation n d ∧ densePriorSeparation n d ≤ 1 := by
  have ha := denseAmplitude_range n d h
  have hE_le : bestEvenApproxError (lowerDegree d) ≤ 1 := by
    unfold bestEvenApproxError
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro e ⟨p, hpdeg, hp⟩
      have hzero := hp 0 (by constructor <;> norm_num)
      have hzero' : |Polynomial.eval 0 p| ≤ e := by
        simpa only [abs_zero, zero_sub, abs_neg] using hzero
      exact (abs_nonneg _).trans hzero'
    · refine ⟨0, by simp, ?_⟩
      intro t ht
      simpa using (abs_le.mpr ht)
  unfold densePriorSeparation
  constructor
  · exact mul_pos ha.1 hE
  · nlinarith
  -- @realizes \(\Delta_{n,d}^{\mathrm{dense}}\)(positive and at most one in the dense range)

/-- For [the specified sample size, alphabet size, overlap level, domain certificate, coordinate prior](hyp:n,d,epsilon,hdom,nu), the [scaled dense product prior is the coordinatewise product prior, restricted to the unit cube, scaled by the dense amplitude, and mapped into the contrast class](goal). -/
noncomputable def denseScaledProductPrior (n d : ℕ)
    (epsilon : ℝ) (hdom : DenseConstructionDomain n d epsilon)
    (nu : Measure ℝ) : Measure (DenseContrast d) :=
  Measure.map (fun t =>
      if ht : ∀ j, t j ∈ Set.Icc (-1 : ℝ) 1 then
        ⟨fun j => denseAmplitude n d * t j, hdom.1, by
          intro j
          have ha0 : 0 ≤ denseAmplitude n d := le_of_lt hdom.2.2.2.1
          have hjlo := mul_le_mul_of_nonneg_left (ht j).1 ha0
          have hjhi := mul_le_mul_of_nonneg_left (ht j).2 ha0
          constructor <;> nlinarith [hdom.2.2.2.2]⟩
      else ⟨fun _ => 0, hdom.1, by intro; norm_num⟩)
    ((Measure.pi (fun _ : Fin d => nu)).restrict
      {t | ∀ j, t j ∈ Set.Icc (-1 : ℝ) 1})
  -- @realizes \(\Pi_{0,n,d}\)(first instance) @realizes \(\Pi_{1,n,d}\)(second instance)

/-- For [the specified alphabet size](hyp:d), the [dense Poisson sample is a finite marked Poisson sample on the observed-data space](goal). -/
abbrev DensePoissonSample (d : ℕ) :=
  Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.FiniteSample (Obs d)

/-- For [the specified alphabet size](hyp:d), the [dense Poisson estimator is a measurable real-valued statistic of the dense Poisson sample](goal). -/
abbrev DensePoissonEstimator (d : ℕ) :=
  {f : DensePoissonSample d → ℝ // Measurable f}

/-- For [the specified Poisson mean, estimator, discrete law](hyp:mean,est,P), the [Poisson observed risk is squared-error risk of the clipped dense estimator under the finite Poisson observed-sample law](goal). -/
noncomputable def poissonObservedRisk (mean : ℕ) {d : ℕ} {epsilon : ℝ}
    (est : DensePoissonEstimator d) (P : ModelLaw d epsilon) : ℝ :=
  Causalean.Stat.sqRisk
    (Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finitePoissonSampleLaw
      (obsLaw P.1) (Real.toNNReal mean))
    (fun sample => max 0 (min 1 (est.1 sample)))
    (observedOptimalValue P.1 P.2)

/-- Minimax squared risk in the genuine experiment with an independent Poisson
sample size having the displayed mean. -/
noncomputable def poissonOptimalValueRisk (mean d : ℕ) (epsilon : ℝ) : ℝ :=
  Causalean.Stat.minimaxValue (poissonObservedRisk mean (d := d) (epsilon := epsilon))
  -- @realizes \(\mathfrak R^{\mathrm{Pois}}_{2n,d,\epsilon}\)(genuine Poissonized comparison risk)

/-- If [the alphabet size satisfies its stated restriction](hyp:hd), then [the stated dense observation kernel exists relation holds](goal). -/
lemma denseObservationKernel_exists (n d : ℕ) (hd : 2 ≤ d) :
    ∃ K : ProbabilityTheory.Kernel (DenseContrast d) (DensePoissonSample d),
      ∀ theta,
        K theta =
          Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finitePoissonSampleLaw
            (obsLaw (observedMarginal (denseLaw theta)))
            (Real.toNNReal (2 * n)) := by
  classical
  let P : DenseContrast d → Measure (Obs d) := fun theta ↦
    obsLaw (observedMarginal (denseLaw theta))
  have hdenseMass (z : FullObs d) :
      Measurable (fun theta : DenseContrast d ↦ denseFullMass theta z) := by
    rcases z with ⟨x, a, y, y0, y1⟩
    have htheta : Measurable (fun theta : DenseContrast d ↦ theta.1 x) :=
      (measurable_pi_apply x).comp measurable_subtype_coe
    have hmu0 : Measurable (fun theta : DenseContrast d ↦ (1 - theta.1 x) / 2) :=
      (measurable_const.sub htheta).div_const 2
    have hmu1 : Measurable (fun theta : DenseContrast d ↦ (1 + theta.1 x) / 2) :=
      (measurable_const.add htheta).div_const 2
    have hb0 : Measurable (fun theta : DenseContrast d ↦
        bernoulliMass ((1 - theta.1 x) / 2) y0) := by
      cases y0
      · change Measurable ((fun _ : DenseContrast d ↦ (1 : ℝ)) -
          fun theta ↦ (1 - theta.1 x) / 2)
        exact measurable_const.sub hmu0
      · simpa [bernoulliMass] using hmu0
    have hb1 : Measurable (fun theta : DenseContrast d ↦
        bernoulliMass ((1 + theta.1 x) / 2) y1) := by
      cases y1
      · change Measurable ((fun _ : DenseContrast d ↦ (1 : ℝ)) -
          fun theta ↦ (1 + theta.1 x) / 2)
        exact measurable_const.sub hmu1
      · simpa [bernoulliMass] using hmu1
    by_cases hmatch : y = (if a then y1 else y0)
    · simp only [denseFullMass, hmatch, if_pos]
      change Measurable (((fun _ : DenseContrast d ↦ (d : ℝ)⁻¹ / 2) *
        fun theta ↦ bernoulliMass ((1 - theta.1 x) / 2) y0) *
          fun theta ↦ bernoulliMass ((1 + theta.1 x) / 2) y1)
      exact (measurable_const.mul hb0).mul hb1
    · simp [denseFullMass, hmatch]
  have hP : ∀ z, Measurable (fun theta ↦ P theta {z}) := by
    intro z
    rw [show (fun theta ↦ P theta {z}) = fun theta ↦
        (observedMarginal (denseLaw theta)).pmf z by
      funext theta
      exact PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _)]
    simp only [observedMarginal, denseLaw, PMF.map_ofFintype,
      PMF.ofFintype_apply]
    apply Finset.measurable_sum
    intro w _hw
    exact ENNReal.measurable_ofReal.comp (hdenseMass w)
  refine ⟨CausalSmith.Mathlib.Probability.parameterizedFinitePoissonSampleKernel
    P hP (Real.toNNReal (2 * n)), ?_⟩
  intro theta
  rfl

/-- For [the specified sample size, alphabet size, alphabet-size certificate](hyp:n,d,hd), the [dense observation kernel sends each contrast to its finite Poisson observed-sample law](goal). -/
noncomputable def denseObservationKernel (n d : ℕ) (hd : 2 ≤ d) :
    ProbabilityTheory.Kernel (DenseContrast d) (DensePoissonSample d) :=
  Classical.choose (denseObservationKernel_exists n d hd)

/-- Observation mixture induced by a scaled product prior and an independent `Pois(2n)` sample. -/
noncomputable def denseObservationMixture (n d : ℕ) (hd : 2 ≤ d)
    (epsilon : ℝ) (hdom : DenseConstructionDomain n d epsilon)
    (nu : Measure ℝ) : Measure (DensePoissonSample d) :=
  denseObservationKernel n d hd ∘ₘ denseScaledProductPrior n d epsilon hdom nu
  -- @realizes \(\mathbb M_{0,n,d}\)(first instance) @realizes \(\mathbb M_{1,n,d}\)(second instance)

/-- For [the specified contrast](hyp:theta), the [dense target is one half plus the average absolute contrast divided by two](goal). -/
noncomputable def denseTargetAt {d : ℕ} (theta : DenseContrast d) : ℝ :=
  1 / 2 + (∑ x : Fin d, |theta.1 x|) / (2 * d)

/-- For [the specified sample size, alphabet size, overlap level, domain certificate, coordinate prior](hyp:n,d,epsilon,hdom,nu), the [dense prior target mean is the expectation of the dense target under the scaled product prior](goal). -/
noncomputable def densePriorTargetMean (n d : ℕ) (epsilon : ℝ)
    (hdom : DenseConstructionDomain n d epsilon) (nu : Measure ℝ) : ℝ :=
  ∫ theta, denseTargetAt theta ∂denseScaledProductPrior n d epsilon hdom nu

-- @node: densePriorTargetMean_formula
/-- Under a supported probability prior, the dense target mean is the baseline
one half plus the scaled sum of the one-coordinate absolute moments. This uses [the dense construction domain conditions hold](hyp:hdom), and [the prior is supported on the unit interval](hyp:hsupp). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma densePriorTargetMean_formula (n d : ℕ) (epsilon : ℝ)
    (hdom : DenseConstructionDomain n d epsilon)
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (hsupp : nu (Set.Icc (-1) 1)ᶜ = 0) :
    densePriorTargetMean n d epsilon hdom nu =
      1 / 2 + denseAmplitude n d / (2 * d) * ∑ _x : Fin d, ∫ t, |t| ∂nu := by
  let mu : Measure (Fin d → ℝ) := Measure.pi (fun _ : Fin d => nu)
  letI : IsProbabilityMeasure mu := by dsimp [mu]; infer_instance
  have hmem : ∀ᵐ t ∂mu, ∀ j, t j ∈ Set.Icc (-1 : ℝ) 1 := by
    have hj : ∀ j : Fin d, ∀ᵐ t ∂mu, t j ∈ Set.Icc (-1 : ℝ) 1 := by
      intro j
      have hs : ∀ᵐ x ∂nu, x ∈ Set.Icc (-1 : ℝ) 1 := by
        exact mem_ae_iff.mpr hsupp
      exact (MeasureTheory.measurePreserving_eval
        (fun _ : Fin d => nu) j).quasiMeasurePreserving.ae hs
    exact ae_all_iff.mpr hj
  have hrestrict : mu.restrict {t | ∀ j, t j ∈ Set.Icc (-1 : ℝ) 1} = mu :=
    Measure.restrict_eq_self_of_ae_mem hmem
  rw [densePriorTargetMean, denseScaledProductPrior, hrestrict]
  rw [integral_map]
  · calc
      _ = ∫ t : Fin d → ℝ,
          (1 / 2 + (∑ x : Fin d, |denseAmplitude n d * t x|) / (2 * d)) ∂mu := by
        apply integral_congr_ae
        filter_upwards [hmem] with t ht
        rw [dif_pos ht]
        rfl
      _ = 1 / 2 + denseAmplitude n d / (2 * d) *
          ∑ _x : Fin d, ∫ t, |t| ∂nu := by
        have ha0 : 0 ≤ denseAmplitude n d := le_of_lt hdom.2.2.2.1
        have hcoord : ∀ x : Fin d, Integrable (fun t : Fin d → ℝ => |t x|) mu := by
          intro x
          refine (integrable_const (μ := mu) (1 : ℝ)).mono'
            (continuous_abs.measurable.comp (measurable_pi_apply x)).aestronglyMeasurable ?_
          filter_upwards [hmem] with t ht
          rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
          exact abs_le.mpr (ht x)
        have habs : ∀ x : Fin d,
            ∫ t : Fin d → ℝ, |t x| ∂mu = ∫ t : ℝ, |t| ∂nu := by
          intro x
          have hmp := MeasureTheory.measurePreserving_eval (fun _ : Fin d => nu) x
          have hsm : AEStronglyMeasurable abs
              (Measure.map (Function.eval x) (Measure.pi fun _ : Fin d => nu)) := by
            rw [hmp.map_eq]
            exact continuous_abs.measurable.aestronglyMeasurable
          have hm := integral_map hmp.aemeasurable hsm
          rw [hmp.map_eq] at hm
          exact hm.symm
        simp_rw [abs_mul, abs_of_nonneg ha0]
        rw [integral_add (integrable_const (1 / 2))
          ((integrable_finsetSum Finset.univ fun x _ =>
            (hcoord x).const_mul (denseAmplitude n d)).div_const (2 * d))]
        have hdiv : (∫ a : Fin d → ℝ,
              (∑ i, denseAmplitude n d * |a i|) / (2 * d) ∂mu) =
            (∫ a : Fin d → ℝ, ∑ i, denseAmplitude n d * |a i| ∂mu) / (2 * d) :=
          integral_div (2 * (d : ℝ)) _
        rw [hdiv, integral_finsetSum Finset.univ (fun x _ =>
          (hcoord x).const_mul (denseAmplitude n d))]
        simp only [integral_const]
        simp_rw [integral_const_mul, habs]
        rw [show mu.real Set.univ = 1 by simp [Measure.real]]
        rw [← Finset.mul_sum]
        ring
  · apply Measurable.aemeasurable
    let S : Set (Fin d → ℝ) := {t | ∀ j, t j ∈ Set.Icc (-1 : ℝ) 1}
    have htrue : Measurable (fun t : S =>
        (⟨fun j => denseAmplitude n d * t.1 j, hdom.1, by
          intro j
          have ha0 : 0 ≤ denseAmplitude n d := le_of_lt hdom.2.2.2.1
          have hjlo := mul_le_mul_of_nonneg_left (t.2 j).1 ha0
          have hjhi := mul_le_mul_of_nonneg_left (t.2 j).2 ha0
          constructor <;> nlinarith [hdom.2.2.2.2]⟩ : DenseContrast d)) := by
      apply Measurable.subtype_mk
      apply measurable_pi_lambda
      intro j
      exact measurable_const.mul ((measurable_pi_apply j).comp measurable_subtype_coe)
    have hS : MeasurableSet S := by
      dsimp [S]
      convert MeasurableSet.iInter (fun j : Fin d =>
        (measurableSet_Icc : MeasurableSet (Set.Icc (-1 : ℝ) 1)).preimage
          (measurable_pi_apply j)) using 1 <;> ext t <;> simp
    exact htrue.dite measurable_const hS
  · apply Measurable.aestronglyMeasurable
    unfold denseTargetAt
    apply Measurable.add measurable_const
    apply Measurable.div_const
    apply Finset.measurable_sum
    intro j _hj
    exact continuous_abs.measurable.comp
      ((measurable_pi_apply j).comp measurable_subtype_coe)

/-- The probability, support, symmetry, moment-matching, and absolute-gap clauses
stated for the two dense priors at the fixed lower-bound degree. -/
def DensePriorPairConditions (K : ℕ) (nu0 nu1 : Measure ℝ) : Prop :=
  IsProbabilityMeasure nu0 ∧ IsProbabilityMeasure nu1 ∧
  nu0 (Set.Icc (-1) 1)ᶜ = 0 ∧ nu1 (Set.Icc (-1) 1)ᶜ = 0 ∧
  Measure.map (fun t : ℝ => -t) nu0 = nu0 ∧
  Measure.map (fun t : ℝ => -t) nu1 = nu1 ∧
  (∀ l ≤ K, ∫ t, t ^ l ∂nu1 = ∫ t, t ^ l ∂nu0) ∧
  (∫ t, |t| ∂nu1) - ∫ t, |t| ∂nu0 =
    2 * bestEvenApproxError K

/-- An exact characterization of the Hahn--Banach prior pair at every even
degree, before the lower-bound construction specializes the family. -/
structure DensePriorFamily where
  nu0 : EvenDegree → Measure ℝ
  nu1 : EvenDegree → Measure ℝ
  conditions : ∀ K : EvenDegree, DensePriorPairConditions K.1 (nu0 K) (nu1 K)

/-- The complete dense moment-matching construction at one even degree, including
the hard submodel, two scaled priors and mixtures, the Poissonized experiment, and
the prior target-mean separation. -/
structure DenseMomentMatchingConstruction (n d : ℕ) (epsilon : ℝ) where
  domain : DenseConstructionDomain n d epsilon
  law : DenseContrast d → PotentialLaw d
  approximationError : ℝ
  degree : ℕ
  intensity : ℝ
  amplitude : ℝ
  nu0 : Measure ℝ
  nu1 : Measure ℝ
  prior0 : Measure (DenseContrast d)
  prior1 : Measure (DenseContrast d)
  mixture0 : Measure (DensePoissonSample d)
  mixture1 : Measure (DensePoissonSample d)
  poissonizedRisk : ℝ
  priorMeanSeparation : ℝ
  priorConditions : DensePriorPairConditions (lowerDegree d) nu0 nu1
  degree_eq : degree = lowerDegree d
  priorMeanSeparation_eq : priorMeanSeparation = densePriorSeparation n d

-- @node: def:dense-moment-matching-construction
/-- For [the specified sample size, alphabet size, overlap level, domain certificate, moment-matching prior family](hyp:n,d,epsilon,hdom,priors), the [dense submodel is the moment-matching construction assembled from the dense law, approximation degree, scaled priors, mixtures, target separation, and their certificates](goal). Its components are [the domain certificate](step:1), [the dense law](step:2), [the approximation error](step:3), [the approximation degree](step:4), [the Poisson intensity](step:5), [the dense amplitude](step:6), [the first coordinate prior](step:7), [the second coordinate prior](step:8), [the first scaled product prior](step:9), [the second scaled product prior](step:10), [the first observation mixture](step:11), [the second observation mixture](step:12), [the Poissonized risk](step:13), [the prior target separation](step:14), [the prior conditions](step:15), [the degree identity](step:16), [the target-separation identity](step:17). -/
noncomputable def denseSubmodel (n d : ℕ) (epsilon : ℝ)
    (hdom : DenseConstructionDomain n d epsilon)
    (priors : DensePriorFamily) :
    DenseMomentMatchingConstruction n d epsilon where
  domain := hdom
  law := denseLaw
  approximationError := bestEvenApproxError (lowerDegree d)
  degree := lowerDegree d
  intensity := poissonCellIntensity n d
  amplitude := denseAmplitude n d
  nu0 := priors.nu0 (lowerEvenDegree d hdom.1)
  nu1 := priors.nu1 (lowerEvenDegree d hdom.1)
  prior0 := denseScaledProductPrior n d epsilon hdom
    (priors.nu0 (lowerEvenDegree d hdom.1))
  prior1 := denseScaledProductPrior n d epsilon hdom
    (priors.nu1 (lowerEvenDegree d hdom.1))
  mixture0 := denseObservationMixture n d hdom.1 epsilon hdom
    (priors.nu0 (lowerEvenDegree d hdom.1))
  mixture1 := denseObservationMixture n d hdom.1 epsilon hdom
    (priors.nu1 (lowerEvenDegree d hdom.1))
  poissonizedRisk := poissonOptimalValueRisk (2 * n) d epsilon
  priorMeanSeparation :=
    densePriorTargetMean n d epsilon hdom
      (priors.nu1 (lowerEvenDegree d hdom.1)) -
      densePriorTargetMean n d epsilon hdom
        (priors.nu0 (lowerEvenDegree d hdom.1))
  priorConditions := priors.conditions (lowerEvenDegree d hdom.1)
  degree_eq := rfl
  priorMeanSeparation_eq := by
    let K : EvenDegree := lowerEvenDegree d hdom.1
    have hc := priors.conditions K
    letI : IsProbabilityMeasure (priors.nu0 K) := hc.1
    letI : IsProbabilityMeasure (priors.nu1 K) := hc.2.1
    rw [densePriorTargetMean_formula n d epsilon hdom (priors.nu1 K) hc.2.2.2.1,
      densePriorTargetMean_formula n d epsilon hdom (priors.nu0 K) hc.2.2.1]
    rcases hc with ⟨_hp0, _hp1, _hs0, _hs1, _hy0, _hy1, _hmom, hgap⟩
    have hd0 : (d : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) hdom.1))
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    unfold densePriorSeparation
    change _ = denseAmplitude n d * bestEvenApproxError K.1
    field_simp [hd0]
    linear_combination denseAmplitude n d * hgap

/-- Difference of the two target means for the priors bundled by the constructed
dense experiment, rather than for arbitrary measures. -/
noncomputable def densePriorMeanSeparation {n d : ℕ} {epsilon : ℝ}
    (C : DenseMomentMatchingConstruction n d epsilon) : ℝ :=
  C.priorMeanSeparation
  -- @realizes \(\Delta_{n,d}^{\mathrm{dense}}\)(constructed-prior target-mean gap)

/-- For [the specified sample size, alphabet size](hyp:n,d), the [dense likelihood tail is the exponential-series remainder above the lower approximation degree](goal). -/
noncomputable def denseLikelihoodTail (n d : ℕ) : ℝ :=
  ∑' r : ℕ, if lowerDegree d + 1 ≤ r then
    (poissonCellIntensity n d * denseAmplitude n d ^ 2) ^ r / Nat.factorial r
  else 0

end CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched
