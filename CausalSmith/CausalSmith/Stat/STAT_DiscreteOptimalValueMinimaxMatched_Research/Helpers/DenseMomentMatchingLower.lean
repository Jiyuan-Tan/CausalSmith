import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Helpers.CitedGates
import Causalean.Stat.Minimax.MomentMatchedMixture
import Causalean.Stat.Minimax.MomentMatchedMixture.SupportLocalized
import Causalean.Stat.Minimax.FuzzyHypotheses
import Causalean.Stat.Minimax.TotalVariation
import Causalean.Stat.Concentration.Matrix.IidSums

/-! Conditional dense moment-matching lower bound. -/

namespace CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- The Poisson sign-count likelihood is jointly measurable in its contrast
parameter and the two observed counts. [The displayed identity or bound is the asserted conclusion](goal). -/
-- @node: measurable_oneCellLikelihood
@[fun_prop] lemma measurable_oneCellLikelihood (lambda : ℝ) :
    Measurable (fun p : ℝ × DenseSignCounts =>
      oneCellLikelihood lambda p.1 p.2) := by
  apply measurable_from_prod_countable_left
  intro r
  unfold oneCellLikelihood
  fun_prop

/-- On the prior support, both sign factors in the Poisson likelihood are
nonnegative. This uses [the target or contrast satisfies the stated unit-range restriction](hyp:htheta). [The displayed identity or bound is the asserted conclusion](goal). -/
-- @node: oneCellLikelihood_nonnegative_of_abs_le_one
lemma oneCellLikelihood_nonnegative_of_abs_le_one (lambda theta : ℝ)
    (htheta : |theta| ≤ 1) (r : DenseSignCounts) :
    0 ≤ oneCellLikelihood lambda theta r := by
  have ht := (abs_le.mp htheta)
  unfold oneCellLikelihood
  exact mul_nonneg (pow_nonneg (by linarith [ht.1]) _)
    (pow_nonneg (by linarith [ht.2]) _)

/-- The likelihood ratio integrates to one under the zero-contrast sign-count
law. This uses [the Poisson intensity is nonnegative](hyp:hlambda). [The displayed identity or bound is the asserted conclusion](goal). -/
-- @node: integral_oneCellLikelihood_denseSignBaseline
lemma integral_oneCellLikelihood_denseSignBaseline (lambda theta : ℝ)
    (hlambda : 0 ≤ lambda) :
    ∫ r : DenseSignCounts, oneCellLikelihood lambda theta r
      ∂denseSignBaseline lambda = 1 := by
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
  rw [show (fun r : DenseSignCounts => oneCellLikelihood lambda theta r) =
      fun r => (1 + theta) ^ r.1 * (1 - theta) ^ r.2 by
    funext r
    rfl]
  rw [integral_prod_mul, poisson_power_mgf, poisson_power_mgf,
    ← Real.exp_add, hlam]
  rw [show lambda / 2 * (1 + theta - 1) +
      lambda / 2 * (1 - theta - 1) = 0 by ring]
  exact Real.exp_zero

-- @node: denseSignLaw
/-- The two independent Poisson sign counts at contrast `theta`. -/
noncomputable def denseSignLaw (lambda theta : ℝ) : Measure DenseSignCounts :=
  (ProbabilityTheory.poissonMeasure (lambda / 2 * (1 + theta)).toNNReal).prod
    (ProbabilityTheory.poissonMeasure (lambda / 2 * (1 - theta)).toNNReal)

-- @node: denseSignLaw_eq_withDensity
/-- On the contrast interval, the exact sign-count experiment has the
paper's likelihood ratio with respect to the zero-contrast law. This uses [the Poisson intensity is nonnegative](hyp:hlambda), and [the target or contrast satisfies the stated unit-range restriction](hyp:htheta). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma denseSignLaw_eq_withDensity (lambda theta : ℝ) (hlambda : 0 ≤ lambda)
    (htheta : |theta| ≤ 1) :
    denseSignLaw lambda theta =
      (denseSignBaseline lambda).withDensity
        (fun r => ENNReal.ofReal (oneCellLikelihood lambda theta r)) := by
  apply Measure.ext_of_singleton
  intro r
  rw [withDensity_apply _ (MeasurableSet.singleton r)]
  rw [show ({r} : Set DenseSignCounts) = {r.1} ×ˢ {r.2} by ext; simp,
    denseSignLaw, denseSignBaseline, Measure.prod_prod]
  simp [ProbabilityTheory.poissonMeasure_singleton, oneCellLikelihood]
  rw [show ({r} : Set DenseSignCounts) = {r.1} ×ˢ {r.2} by ext; simp,
    Measure.prod_prod]
  simp only [ProbabilityTheory.poissonMeasure_singleton]
  have ht := abs_le.mp htheta
  have hplus : 0 ≤ 1 + theta := by linarith [ht.1]
  have hminus : 0 ≤ 1 - theta := by linarith [ht.2]
  rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
  have h1 : 0 ≤ Real.exp (-max (lambda / 2 * (1 + theta)) 0) *
      max (lambda / 2 * (1 + theta)) 0 ^ r.1 / (r.1.factorial : ℝ) := by positivity
  have h2 : 0 ≤ Real.exp (-max (lambda / 2 * (1 - theta)) 0) *
      max (lambda / 2 * (1 - theta)) 0 ^ r.2 / (r.2.factorial : ℝ) := by positivity
  have h3 : 0 ≤ Real.exp (-((lambda / 2).toNNReal : ℝ)) *
      ((lambda / 2).toNNReal : ℝ) ^ r.1 / (r.1.factorial : ℝ) := by positivity
  have h4 : 0 ≤ Real.exp (-((lambda / 2).toNNReal : ℝ)) *
      ((lambda / 2).toNNReal : ℝ) ^ r.2 / (r.2.factorial : ℝ) := by positivity
  have h5 : 0 ≤ (1 + theta) ^ r.1 * (1 - theta) ^ r.2 :=
    mul_nonneg (pow_nonneg hplus _) (pow_nonneg hminus _)
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal h1, ENNReal.toReal_ofReal h2,
    ENNReal.toReal_ofReal h3, ENNReal.toReal_ofReal h4, ENNReal.toReal_ofReal h5]
  rw [Real.coe_toNNReal _ (div_nonneg hlambda (by norm_num))]
  rw [max_eq_left (mul_nonneg (div_nonneg hlambda (by norm_num)) hplus),
    max_eq_left (mul_nonneg (div_nonneg hlambda (by norm_num)) hminus)]
  rw [mul_pow, mul_pow]
  field_simp
  have hexp : Real.exp (-(lambda * (1 + theta) / 2)) *
      Real.exp (-(lambda * (1 - theta) / 2)) =
      Real.exp (-(lambda / 2)) ^ 2 := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    _ = (Real.exp (-(lambda * (1 + theta) / 2)) *
          Real.exp (-(lambda * (1 - theta) / 2))) *
        ((lambda / 2) ^ r.1 * (1 + theta) ^ r.1 *
          (lambda / 2) ^ r.2 * (1 - theta) ^ r.2) := by ring
    _ = Real.exp (-(lambda / 2)) ^ 2 *
        ((lambda / 2) ^ r.1 * (1 + theta) ^ r.1 *
          (lambda / 2) ^ r.2 * (1 - theta) ^ r.2) := by rw [hexp]
    _ = _ := by ring

/-- The likelihood family after scaling the Cai--Low support to the dense
amplitude. -/
-- @node: scaledDenseLikelihood
noncomputable def scaledDenseLikelihood (n d : ℕ) (t : ℝ)
    (r : DenseSignCounts) : ℝ :=
  oneCellLikelihood (poissonCellIntensity n d) (denseAmplitude n d * t) r

-- @node: scaledDenseSignLaw_eq_withDensity
/-- The scaled one-cell hard experiment has the likelihood density required
by the support-localized moment-matching theorem. This uses [the sample size and alphabet lie in the dense regime](hyp:hregime), and [the argument satisfies the stated support or positivity restriction](hyp:ht). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma scaledDenseSignLaw_eq_withDensity (n d : ℕ)
    (hregime : DenseRegime n d) (t : ℝ) (ht : |t| ≤ 1) :
    denseSignLaw (poissonCellIntensity n d) (denseAmplitude n d * t) =
      (denseSignBaseline (poissonCellIntensity n d)).withDensity
        (fun r => ENNReal.ofReal (scaledDenseLikelihood n d t r)) := by
  have hdNat : 0 < d := lt_of_lt_of_le (by omega : 0 < 2) hregime.1
  have hnNat : 0 < n := lt_trans (Nat.pow_pos hdNat) hregime.2
  have hlambda : 0 ≤ poissonCellIntensity n d := by
    unfold poissonCellIntensity
    positivity
  have ha := denseAmplitude_range n d hregime
  have hscaled : |denseAmplitude n d * t| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg (le_of_lt ha.1)]
    nlinarith [abs_nonneg t]
  simpa only [scaledDenseLikelihood] using
    denseSignLaw_eq_withDensity (poissonCellIntensity n d)
      (denseAmplitude n d * t) hlambda hscaled

/-- The scaled dense likelihood remains jointly measurable. [The displayed identity or bound is the asserted conclusion](goal). -/
-- @node: measurable_scaledDenseLikelihood
@[fun_prop] lemma measurable_scaledDenseLikelihood (n d : ℕ) :
    Measurable (fun p : ℝ × DenseSignCounts => scaledDenseLikelihood n d p.1 p.2) := by
  unfold scaledDenseLikelihood
  apply measurable_from_prod_countable_left
  intro r
  unfold oneCellLikelihood
  fun_prop

/-- The scaled likelihood is nonnegative on the Cai--Low support. This uses [the sample size and alphabet lie in the dense regime](hyp:hregime), and [the argument satisfies the stated support or positivity restriction](hyp:ht). [The displayed identity or bound is the asserted conclusion](goal). -/
-- @node: scaledDenseLikelihood_nonnegative_of_supported
lemma scaledDenseLikelihood_nonnegative_of_supported (n d : ℕ)
    (hregime : DenseRegime n d) (t : ℝ) (ht : |t| ≤ 1)
    (r : DenseSignCounts) : 0 ≤ scaledDenseLikelihood n d t r := by
  apply oneCellLikelihood_nonnegative_of_abs_le_one
  rw [abs_mul]
  have ha := (denseAmplitude_range n d hregime).2
  have ha0 := le_of_lt (denseAmplitude_range n d hregime).1
  rw [abs_of_nonneg ha0]
  nlinarith [abs_nonneg t]

/-- On the prior support, the scaled likelihood has the exponential Gram
kernel with interaction parameter `lambda * amplitude²`. This uses [the sample size and alphabet lie in the dense regime](hyp:hregime), and [the stated t condition holds](hyp:_ht), and [the stated t' condition holds](hyp:_ht'). [The displayed identity or bound is the asserted conclusion](goal). -/
-- @node: scaledDenseLikelihood_exponentialGram
lemma scaledDenseLikelihood_exponentialGram (n d : ℕ)
    (hregime : DenseRegime n d) (t : ℝ) (_ht : |t| ≤ 1)
    (t' : ℝ) (_ht' : |t'| ≤ 1) :
    (∫ r : DenseSignCounts, scaledDenseLikelihood n d t r *
        scaledDenseLikelihood n d t' r ∂denseSignBaseline (poissonCellIntensity n d)) =
      Real.exp ((poissonCellIntensity n d * denseAmplitude n d ^ 2) * t * t') := by
  have hdNat : 0 < d := lt_of_lt_of_le (by omega : 0 < 2) hregime.1
  have hd : (0 : ℝ) < d := by
    exact_mod_cast hdNat
  have hn : (0 : ℝ) < n := by
    exact_mod_cast (lt_trans (Nat.pow_pos hdNat) hregime.2)
  unfold scaledDenseLikelihood
  rw [oneCellLikelihood_inner _ _ _ (le_of_lt (by
    unfold poissonCellIntensity
    positivity : 0 < poissonCellIntensity n d))]
  congr 1
  ring

-- @node: denseLaw_jointMass
set_option maxHeartbeats 1000000 in
-- Expanding the finite five-coordinate PMF requires a larger simplifier budget.
/-- [the dense observed law has the four stated symmetric atom masses in every cell](goal). -/
lemma denseLaw_jointMass {d : ℕ} (theta : DenseContrast d) :
    (∀ x, jointMass (observedMarginal (denseLaw theta)) x true true =
      (d : ℝ)⁻¹ / 4 * (1 + theta.1 x)) ∧
    (∀ x, jointMass (observedMarginal (denseLaw theta)) x true false =
      (d : ℝ)⁻¹ / 4 * (1 - theta.1 x)) ∧
    (∀ x, jointMass (observedMarginal (denseLaw theta)) x false true =
      (d : ℝ)⁻¹ / 4 * (1 - theta.1 x)) ∧
    (∀ x, jointMass (observedMarginal (denseLaw theta)) x false false =
      (d : ℝ)⁻¹ / 4 * (1 + theta.1 x)) := by
  classical
  have ht (x : Fin d) := theta.2.2 x
  constructor
  · intro x
    have hplus : 0 ≤ 1 + theta.1 x := by linarith [(ht x).1]
    have hminus : 0 ≤ 1 - theta.1 x := by linarith [(ht x).2]
    have hmu0c : 0 ≤ 1 - (1 - theta.1 x) / 2 := by linarith
    have hmu1c : 0 ≤ 1 - (1 + theta.1 x) / 2 := by linarith
    simp [jointMass, observedMarginal, denseLaw, denseFullMass, bernoulliMass,
      PMF.ofFintype_apply, Finset.sum_filter, Fintype.sum_prod_type]
    repeat' rw [ENNReal.toReal_add (by simp) (by simp)]
    repeat' rw [ENNReal.toReal_ofReal (by positivity)]
    ring
  · constructor
    · intro x
      have hplus : 0 ≤ 1 + theta.1 x := by linarith [(ht x).1]
      have hminus : 0 ≤ 1 - theta.1 x := by linarith [(ht x).2]
      have hmu0c : 0 ≤ 1 - (1 - theta.1 x) / 2 := by linarith
      have hmu1c : 0 ≤ 1 - (1 + theta.1 x) / 2 := by linarith
      simp [jointMass, observedMarginal, denseLaw, denseFullMass, bernoulliMass,
        PMF.ofFintype_apply, Finset.sum_filter, Fintype.sum_prod_type]
      repeat' rw [ENNReal.toReal_add (by simp) (by simp)]
      repeat' rw [ENNReal.toReal_ofReal (by positivity)]
      ring
    · constructor
      · intro x
        have hplus : 0 ≤ 1 + theta.1 x := by linarith [(ht x).1]
        have hminus : 0 ≤ 1 - theta.1 x := by linarith [(ht x).2]
        have hmu0c : 0 ≤ 1 - (1 - theta.1 x) / 2 := by linarith
        have hmu1c : 0 ≤ 1 - (1 + theta.1 x) / 2 := by linarith
        simp [jointMass, observedMarginal, denseLaw, denseFullMass, bernoulliMass,
          PMF.ofFintype_apply, Finset.sum_filter, Fintype.sum_prod_type]
        repeat' rw [ENNReal.toReal_add (by simp) (by simp)]
        repeat' rw [ENNReal.toReal_ofReal (by positivity)]
        ring

      · intro x
        have hplus : 0 ≤ 1 + theta.1 x := by linarith [(ht x).1]
        have hminus : 0 ≤ 1 - theta.1 x := by linarith [(ht x).2]
        have hmu0c : 0 ≤ 1 - (1 - theta.1 x) / 2 := by linarith
        have hmu1c : 0 ≤ 1 - (1 + theta.1 x) / 2 := by linarith
        simp [jointMass, observedMarginal, denseLaw, denseFullMass, bernoulliMass,
          PMF.ofFintype_apply, Finset.sum_filter, Fintype.sum_prod_type]
        repeat' rw [ENNReal.toReal_add (by simp) (by simp)]
        repeat' rw [ENNReal.toReal_ofReal (by positivity)]
        ring

-- @node: denseZeroContrast
/-- The zero contrast is the common reference point of the dense experiment. -/
def denseZeroContrast (d : ℕ) (hd : 2 ≤ d) : DenseContrast d :=
  ⟨fun _ => 0, hd, by intro x; exact Set.mem_Icc.mpr (by norm_num)⟩

-- @node: denseLaw_atom_likelihood
/-- Relative to the zero-contrast law, one observed atom contributes the positive
or negative likelihood factor according as treatment and outcome agree or disagree. [The displayed identity or bound is the asserted conclusion](goal). -/
lemma denseLaw_atom_likelihood {d : ℕ} (theta : DenseContrast d) (x : Fin d)
    (a y : Bool) :
    jointMass (observedMarginal (denseLaw theta)) x a y =
      jointMass (observedMarginal (denseLaw (denseZeroContrast d theta.2.1))) x a y *
        (if a = y then 1 + theta.1 x else 1 - theta.1 x) := by
  have htheta := denseLaw_jointMass theta
  have hzero := denseLaw_jointMass (denseZeroContrast d theta.2.1)
  fin_cases a <;> fin_cases y
  · rw [htheta.1, hzero.1]
    simp [denseZeroContrast]
  · rw [htheta.2.1, hzero.2.1]
    simp [denseZeroContrast]
  · rw [htheta.2.2.1, hzero.2.2.1]
    simp [denseZeroContrast]
  · rw [htheta.2.2.2, hzero.2.2.2]
    simp [denseZeroContrast]

-- @node: denseLaw_observed_spec
/-- If [the overlap parameter satisfies its stated range restriction](hyp:hepsilon), then [the dense law is an overlapping observed model with uniform cell masses, propensity one half, shifted outcome means, and the stated optimal value](goal). -/
lemma denseLaw_observed_spec {d : ℕ} (epsilon : ℝ)
    (hepsilon : 0 < epsilon ∧ epsilon < 1 / 2) (theta : DenseContrast d) :
    ∃ hmodel : ObservedModelClass epsilon (observedMarginal (denseLaw theta)),
      (∀ x, cellMass (observedMarginal (denseLaw theta)) x = 1 / d) ∧
      (∀ x, propensity (observedMarginal (denseLaw theta)) x = 1 / 2) ∧
      (∀ x, outcomeMean (observedMarginal (denseLaw theta)) true x =
        (1 + theta.1 x) / 2) ∧
      (∀ x, outcomeMean (observedMarginal (denseLaw theta)) false x =
        (1 - theta.1 x) / 2) ∧
      observedOptimalValue (observedMarginal (denseLaw theta)) hmodel =
        1 / 2 + (∑ x : Fin d, |theta.1 x|) / (2 * d) := by
  classical
  let P := observedMarginal (denseLaw theta)
  have hj := denseLaw_jointMass theta
  have hd0 : (d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le (by omega) theta.2.1))
  have hcell : ∀ x, cellMass P x = 1 / d := by
    intro x
    simp [P, cellMass, hj.1 x, hj.2.1 x, hj.2.2.1 x, hj.2.2.2 x]
    field_simp [hd0]
    ring
  have harm : ∀ a x, armMass P a x = 1 / (2 * d) := by
    intro a x
    fin_cases a <;>
      simp [P, armMass, hj.1 x, hj.2.1 x, hj.2.2.1 x, hj.2.2.2 x] <;>
      field_simp [hd0] <;> ring
  have hprop : ∀ x, propensity P x = 1 / 2 := by
    intro x
    rw [propensity, harm, hcell]
    field_simp [hd0]
  have houtTrue : ∀ x, outcomeMean P true x = (1 + theta.1 x) / 2 := by
    intro x
    rw [outcomeMean, hj.1, harm]
    field_simp [hd0]
    ring
  have houtFalse : ∀ x, outcomeMean P false x = (1 - theta.1 x) / 2 := by
    intro x
    rw [outcomeMean, hj.2.2.1, harm]
    field_simp [hd0]
    ring
  have hP : ObservedModelClass epsilon P := by
    refine ⟨theta.2.1, hepsilon.1, hepsilon.2, ?_⟩
    intro x _hx
    rw [hprop]
    constructor <;> linarith
  refine ⟨hP, hcell, hprop, houtTrue, houtFalse, ?_⟩
  change observedOptimalValueRaw P = _
  rw [observedOptimalValueRaw]
  simp_rw [hcell, houtFalse, houtTrue]
  have hmax (x : Fin d) :
      max ((1 - theta.1 x) / 2) ((1 + theta.1 x) / 2) =
        (1 + |theta.1 x|) / 2 := by
    by_cases hx : 0 ≤ theta.1 x
    · rw [max_eq_right (by linarith), abs_of_nonneg hx]
    · have hx' : theta.1 x ≤ 0 := le_of_not_ge hx
      rw [max_eq_left (by linarith), abs_of_nonpos hx']
      ring
  simp_rw [hmax]
  have hterm (x : Fin d) :
      1 / (d : ℝ) * ((1 + |theta.1 x|) / 2) =
        1 / (2 * d) + |theta.1 x| / (2 * d) := by
    field_simp [hd0]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_div]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [hd0]

-- @node: denseBox_observed_spec
/-- Every contrast in the scaled dense cube gives the required observed hard-submodel law. This uses [the dense construction domain conditions hold](hyp:hdom), and [the target or contrast satisfies the stated unit-range restriction](hyp:htheta). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma denseBox_observed_spec {n d : ℕ} {epsilon : ℝ}
    (hdom : DenseConstructionDomain n d epsilon) (theta : Fin d → ℝ)
    (htheta : ∀ x, theta x ∈ Set.Icc (-denseAmplitude n d) (denseAmplitude n d)) :
    ∃ theta' : DenseContrast d, theta'.1 = theta ∧
      ∃ hmodel : ObservedModelClass epsilon (observedMarginal (denseLaw theta')),
        (∀ x, cellMass (observedMarginal (denseLaw theta')) x = 1 / d) ∧
        (∀ x, propensity (observedMarginal (denseLaw theta')) x = 1 / 2) ∧
        (∀ x, outcomeMean (observedMarginal (denseLaw theta')) true x =
          (1 + theta x) / 2) ∧
        (∀ x, outcomeMean (observedMarginal (denseLaw theta')) false x =
          (1 - theta x) / 2) ∧
        observedOptimalValue (observedMarginal (denseLaw theta')) hmodel =
          1 / 2 + (∑ x : Fin d, |theta x|) / (2 * d) := by
  let theta' : DenseContrast d := ⟨theta, hdom.1, by
    intro x
    have hx := htheta x
    have hlo : (-1 / 2 : ℝ) ≤ -denseAmplitude n d := by
      linarith [hdom.2.2.2.2]
    constructor
    · exact hlo.trans hx.1
    · exact hx.2.trans (by linarith [hdom.2.2.2.2])⟩
  obtain ⟨hmodel, hcell, hprop, hmu1, hmu0, hvalue⟩ :=
    denseLaw_observed_spec epsilon ⟨hdom.2.1, hdom.2.2.1⟩ theta'
  refine ⟨theta', rfl, hmodel, hcell, hprop, ?_, ?_, ?_⟩
  · simpa [theta'] using hmu1
  · simpa [theta'] using hmu0
  · simpa [theta'] using hvalue

/-- Cai--Low supplies the exact supported, symmetric moment-matched pair at the chosen dense degree. This uses [the Cai--Low moment-matching prior result is available](hyp:h_cai_low), and [the alphabet size satisfies its stated restriction](hyp:hd). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma densePriorPair_exists (h_cai_low : CaiLowAbsoluteMomentPriors) (d : ℕ) (hd : 2 ≤ d) :
    ∃ nu0 nu1 : Measure ℝ,
      DensePriorPairConditions (lowerDegree d) nu0 nu1 := by
  obtain ⟨nu0, nu1, hpair⟩ :=
    h_cai_low.1 (lowerDegree d) (lowerDegree_even d) (lowerDegree_pos d hd)
  exact ⟨nu0, nu1, hpair⟩

-- @node: densePriorFamily_of_caiLow
/-- Cai--Low's positive-even-degree prior pairs assemble into the family used by
the dense construction. -/
noncomputable def densePriorFamily_of_caiLow
    (h_cai_low : CaiLowAbsoluteMomentPriors) : DensePriorFamily where
  nu0 K := Classical.choose (h_cai_low.1 K.1 K.2.2 K.2.1)
  nu1 K := Classical.choose (Classical.choose_spec (h_cai_low.1 K.1 K.2.2 K.2.1))
  conditions K := by
    exact Classical.choose_spec (Classical.choose_spec
      (h_cai_low.1 K.1 K.2.2 K.2.1))

-- @node: denseScaledProductPrior_isProbability
/-- Scaling a supported probability product prior into the dense contrast cube
produces a probability measure. This uses [the dense construction domain conditions hold](hyp:hdom), and [the prior is supported on the unit interval](hyp:hsupp). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma denseScaledProductPrior_isProbability {n d : ℕ} {epsilon : ℝ}
    (hdom : DenseConstructionDomain n d epsilon) (nu : Measure ℝ)
    [IsProbabilityMeasure nu] (hsupp : nu (Set.Icc (-1) 1)ᶜ = 0) :
    IsProbabilityMeasure (denseScaledProductPrior n d epsilon hdom nu) := by
  let mu : Measure (Fin d → ℝ) := Measure.pi fun _ : Fin d => nu
  letI : IsProbabilityMeasure mu := by dsimp [mu]; infer_instance
  let S : Set (Fin d → ℝ) := {t | ∀ j, t j ∈ Set.Icc (-1 : ℝ) 1}
  have hmem : ∀ᵐ t ∂mu, t ∈ S := by
    have hj : ∀ j : Fin d, ∀ᵐ t ∂mu, t j ∈ Set.Icc (-1 : ℝ) 1 := by
      intro j
      exact (MeasureTheory.measurePreserving_eval (fun _ : Fin d => nu) j).quasiMeasurePreserving.ae
        (mem_ae_iff.mpr hsupp)
    exact ae_all_iff.mpr hj
  have hrestrict : mu.restrict S = mu := Measure.restrict_eq_self_of_ae_mem hmem
  let F : (Fin d → ℝ) → DenseContrast d := fun t =>
    if ht : ∀ j, t j ∈ Set.Icc (-1 : ℝ) 1 then
      ⟨fun j => denseAmplitude n d * t j, hdom.1, by
        intro j
        have ha0 : 0 ≤ denseAmplitude n d := le_of_lt hdom.2.2.2.1
        have hjlo := mul_le_mul_of_nonneg_left (ht j).1 ha0
        have hjhi := mul_le_mul_of_nonneg_left (ht j).2 ha0
        constructor <;> nlinarith [hdom.2.2.2.2]⟩
    else ⟨fun _ => 0, hdom.1, by intro; norm_num⟩
  have hS : MeasurableSet S := by
    dsimp [S]
    convert MeasurableSet.iInter (fun j : Fin d =>
      (measurableSet_Icc : MeasurableSet (Set.Icc (-1 : ℝ) 1)).preimage
        (measurable_pi_apply j)) using 1 <;> ext t <;> simp
  have hF : Measurable F := by
    unfold F
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
    exact htrue.dite measurable_const hS
  change IsProbabilityMeasure (Measure.map F (mu.restrict S))
  rw [hrestrict]
  exact Measure.isProbabilityMeasure_map hF.aemeasurable

/-- The dense target is measurable on the finite contrast cube. [The displayed identity or bound is the asserted conclusion](goal). -/
-- @node: measurable_denseTargetAt
@[fun_prop] lemma measurable_denseTargetAt {d : ℕ} :
    Measurable (denseTargetAt : DenseContrast d → ℝ) := by
  unfold denseTargetAt
  apply Measurable.add measurable_const
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro j _hj
  exact continuous_abs.measurable.comp
    ((measurable_pi_apply j).comp measurable_subtype_coe)

/-- Under either supported coordinate prior, the dense target has the required
`1 / d` variance gain from the independent product coordinates. This uses [the dense construction domain conditions hold](hyp:hdom), and [the prior is supported on the unit interval](hyp:hsupp). [The displayed identity or bound is the asserted conclusion](goal). -/
-- @node: densePriorTarget_variance_le
lemma densePriorTarget_variance_le {n d : ℕ} {epsilon : ℝ}
    (hdom : DenseConstructionDomain n d epsilon) (nu : Measure ℝ)
    [IsProbabilityMeasure nu] (hsupp : nu (Set.Icc (-1) 1)ᶜ = 0) :
    ∫ theta, (denseTargetAt theta -
        densePriorTargetMean n d epsilon hdom nu) ^ 2
        ∂denseScaledProductPrior n d epsilon hdom nu ≤
      denseAmplitude n d ^ 2 / (4 * d) := by
  let mu : Measure (Fin d → ℝ) := Measure.pi fun _ : Fin d => nu
  letI : IsProbabilityMeasure mu := by dsimp [mu]; infer_instance
  let S : Set (Fin d → ℝ) := {t | ∀ j, t j ∈ Set.Icc (-1 : ℝ) 1}
  have hmem : ∀ᵐ t ∂mu, t ∈ S := by
    apply ae_all_iff.mpr
    intro j
    exact (MeasureTheory.measurePreserving_eval (fun _ : Fin d => nu) j).quasiMeasurePreserving.ae
      (mem_ae_iff.mpr hsupp)
  have hrestrict : mu.restrict S = mu := Measure.restrict_eq_self_of_ae_mem hmem
  let F : (Fin d → ℝ) → DenseContrast d := fun t =>
    if ht : t ∈ S then
      ⟨fun j => denseAmplitude n d * t j, hdom.1, by
        intro j
        have ha0 : 0 ≤ denseAmplitude n d := le_of_lt hdom.2.2.2.1
        have hjlo := mul_le_mul_of_nonneg_left (ht j).1 ha0
        have hjhi := mul_le_mul_of_nonneg_left (ht j).2 ha0
        constructor <;> nlinarith [hdom.2.2.2.2]⟩
    else ⟨fun _ => 0, hdom.1, by intro; norm_num⟩
  have hSmeas : MeasurableSet S := by
    dsimp [S]
    convert MeasurableSet.iInter (fun j : Fin d =>
      (measurableSet_Icc : MeasurableSet (Set.Icc (-1 : ℝ) 1)).preimage
        (measurable_pi_apply j)) using 1 <;> ext t <;> simp
  have hF : Measurable F := by
    unfold F
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
    exact htrue.dite measurable_const hSmeas
  have habs_mem : MemLp (fun t : ℝ => |t|) 2 nu := by
    apply MemLp.of_bound continuous_abs.measurable.aestronglyMeasurable 1
    filter_upwards [mem_ae_iff.mpr hsupp] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg t)]
    exact abs_le.mpr ht
  have habs_var : Var[fun t : ℝ => |t|; nu] ≤ 1 / 4 := by
    have hbounded : ∀ᵐ t ∂nu, |t| ∈ Set.Icc (0 : ℝ) 1 := by
      filter_upwards [mem_ae_iff.mpr hsupp] with t ht
      exact ⟨abs_nonneg t, abs_le.mpr ht⟩
    convert ProbabilityTheory.variance_le_sq_of_bounded hbounded
      continuous_abs.measurable.aemeasurable using 1 <;> norm_num
  let sumAbs : (Fin d → ℝ) → ℝ := fun t => ∑ j, |t j|
  have hsum_mem : MemLp sumAbs 2 mu := by
    dsimp [sumAbs]
    rw [show (fun t : Fin d → ℝ => ∑ j : Fin d, |t j|) =
        ∑ j : Fin d, fun t => |t j| by ext t; simp [Finset.sum_apply]]
    apply MeasureTheory.memLp_finset_sum'
    intro j _hj
    exact habs_mem.comp_measurePreserving
      (MeasureTheory.measurePreserving_eval (fun _ : Fin d => nu) j)
  have hsum_integral : ∫ t, sumAbs t ∂mu = d * ∫ t, |t| ∂nu := by
    simpa [mu, sumAbs] using
      Causalean.Stat.Concentration.integral_sum_pi_eq (N := d) nu
        (fun t : ℝ => |t|) (habs_mem.integrable (by norm_num))
  have hsum_variance : Var[sumAbs; mu] = d * Var[fun t : ℝ => |t|; nu] := by
    simpa [mu, sumAbs] using
      Causalean.Stat.Concentration.variance_sum_pi_eq (N := d) nu
        (fun t : ℝ => |t|) habs_mem
  have hmean : densePriorTargetMean n d epsilon hdom nu =
      1 / 2 + denseAmplitude n d / (2 * d) *
        (d * ∫ t, |t| ∂nu) := by
    rw [densePriorTargetMean_formula n d epsilon hdom nu hsupp]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hdR : (0 : ℝ) < d := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hdom.1)
  change (∫ theta, (denseTargetAt theta -
        densePriorTargetMean n d epsilon hdom nu) ^ 2
      ∂Measure.map F (mu.restrict S)) ≤ _
  rw [hrestrict]
  have htargetStrong : AEStronglyMeasurable
      (fun theta : DenseContrast d =>
        (denseTargetAt theta - densePriorTargetMean n d epsilon hdom nu) ^ 2)
      (Measure.map F mu) :=
    ((measurable_denseTargetAt.sub measurable_const).pow_const 2).aestronglyMeasurable
  rw [integral_map hF.aemeasurable htargetStrong]
  have hpoint : ∀ᵐ t ∂mu,
      denseTargetAt (F t) =
        1 / 2 + denseAmplitude n d / (2 * d) * sumAbs t := by
    filter_upwards [hmem] with t ht
    simp only [F, ht, ↓reduceDIte, denseTargetAt, sumAbs]
    have ha0 : 0 ≤ denseAmplitude n d := le_of_lt hdom.2.2.2.1
    simp_rw [abs_mul, abs_of_nonneg ha0]
    congr 1
    rw [Finset.sum_div]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _hx
    ring
  calc
    ∫ t, (denseTargetAt (F t) - densePriorTargetMean n d epsilon hdom nu) ^ 2 ∂mu =
        ∫ t, (denseAmplitude n d / (2 * d)) ^ 2 *
          (sumAbs t - ∫ t, sumAbs t ∂mu) ^ 2 ∂mu := by
            rw [hmean]
            apply integral_congr_ae
            filter_upwards [hpoint] with t ht
            rw [ht, hsum_integral]
            ring
    _ = (denseAmplitude n d / (2 * d)) ^ 2 * Var[sumAbs; mu] := by
          rw [integral_const_mul]
          congr 1
          exact (ProbabilityTheory.variance_eq_integral hsum_mem.aemeasurable).symm
    _ = (denseAmplitude n d / (2 * d)) ^ 2 *
          (d * Var[fun t : ℝ => |t|; nu]) := by rw [hsum_variance]
    _ ≤ (denseAmplitude n d / (2 * d)) ^ 2 * (d * (1 / 4)) := by
          gcongr
    _ ≤ denseAmplitude n d ^ 2 / (4 * d) := by
          field_simp
          nlinarith [sq_nonneg (denseAmplitude n d), hdR]

/-- Chebyshev turns the product-prior variance bound into the one-eighth
concentration clause used by the standard fuzzy-hypothesis theorem. This uses [the dense construction domain conditions hold](hyp:hdom), and [the prior is supported on the unit interval](hyp:hsupp), and [the stated e condition holds](hyp:hE), and [the stated scale inequality holds](hyp:hscale). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma densePriorTarget_tail_le {n d : ℕ} {epsilon : ℝ}
    (hdom : DenseConstructionDomain n d epsilon) (nu : Measure ℝ)
    [IsProbabilityMeasure nu] (hsupp : nu (Set.Icc (-1) 1)ᶜ = 0)
    (hE : 0 < bestEvenApproxError (lowerDegree d))
    (hscale : 32 ≤ (d : ℝ) *
      bestEvenApproxError (lowerDegree d) ^ 2) :
    denseScaledProductPrior n d epsilon hdom nu
        {theta | |denseTargetAt theta -
          densePriorTargetMean n d epsilon hdom nu| >
            densePriorSeparation n d / 4} ≤ 1 / 8 := by
  let prior := denseScaledProductPrior n d epsilon hdom nu
  letI : IsProbabilityMeasure prior :=
    denseScaledProductPrior_isProbability hdom nu hsupp
  have htarget_mem : MemLp (denseTargetAt : DenseContrast d → ℝ) 2 prior := by
    apply MemLp.of_bound measurable_denseTargetAt.aestronglyMeasurable 1
    filter_upwards with theta
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · unfold denseTargetAt
      have habs (x : Fin d) : |theta.1 x| ≤ 1 / 2 := by
        apply abs_le.mpr
        constructor <;> linarith [(theta.2.2 x).1, (theta.2.2 x).2]
      calc
        1 / 2 + (∑ x, |theta.1 x|) / (2 * d) ≤
            1 / 2 + (∑ _x : Fin d, (1 / 2 : ℝ)) / (2 * d) := by
              gcongr
              exact habs x
        _ ≤ 1 := by
          have hdR : (0 : ℝ) < d := by
            exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) theta.2.1)
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          field_simp
          linarith
    · unfold denseTargetAt
      positivity
  have hsep : 0 < densePriorSeparation n d := by
    unfold densePriorSeparation
    exact mul_pos hdom.2.2.2.1 hE
  have hcheb := ProbabilityTheory.meas_ge_le_variance_div_sq htarget_mem
    (show 0 < densePriorSeparation n d / 4 by positivity)
  have hvar : Var[(denseTargetAt : DenseContrast d → ℝ); prior] ≤
      denseAmplitude n d ^ 2 / (4 * d) := by
    rw [ProbabilityTheory.variance_eq_integral
      measurable_denseTargetAt.aemeasurable]
    exact densePriorTarget_variance_le hdom nu hsupp
  have hratio : Var[(denseTargetAt : DenseContrast d → ℝ); prior] /
      (densePriorSeparation n d / 4) ^ 2 ≤ 1 / 8 := by
    have ha : 0 < denseAmplitude n d := hdom.2.2.2.1
    have hd : (0 : ℝ) < d := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hdom.1)
    calc
      _ ≤ (denseAmplitude n d ^ 2 / (4 * d)) /
          (densePriorSeparation n d / 4) ^ 2 := by gcongr
      _ ≤ 1 / 8 := by
        unfold densePriorSeparation
        field_simp
        nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hE]
  calc
    prior {theta | |denseTargetAt theta -
        densePriorTargetMean n d epsilon hdom nu| > densePriorSeparation n d / 4} ≤
        prior {theta | densePriorSeparation n d / 4 ≤
          |denseTargetAt theta - ∫ x, denseTargetAt x ∂prior|} := by
            apply measure_mono
            intro theta htheta
            change densePriorSeparation n d / 4 < _ at htheta
            exact le_of_lt htheta
    _ ≤ ENNReal.ofReal (Var[(denseTargetAt : DenseContrast d → ℝ); prior] /
          (densePriorSeparation n d / 4) ^ 2) := hcheb
    _ ≤ 1 / 8 := by
      simpa using ENNReal.ofReal_le_ofReal hratio

/-- The cited reciprocal approximation lower bound makes the chosen error strictly positive. This uses [the Cai--Low moment-matching prior result is available](hyp:h_cai_low), and [the alphabet size satisfies its stated restriction](hyp:hd). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma bestEvenApproxError_lowerDegree_pos (h_cai_low : CaiLowAbsoluteMomentPriors)
    (d : ℕ) (hd : 2 ≤ d) :
    0 < bestEvenApproxError (lowerDegree d) := by
  obtain ⟨c, C, hc, _hcC, hbounds⟩ := h_cai_low.2
  have hK : (0 : ℝ) < lowerDegree d := by exact_mod_cast lowerDegree_pos d hd
  have hlower := (hbounds (lowerDegree d) (lowerDegree_even d) (lowerDegree_pos d hd)).1
  exact lt_of_lt_of_le (div_pos hc hK) hlower

-- @node: denseLikelihoodTail_eq_exponentialSeriesTail
/-- The paper's likelihood tail is exactly the tail used by the generic
moment-matched-mixture substrate. [The displayed identity or bound is the asserted conclusion](goal). -/
lemma denseLikelihoodTail_eq_exponentialSeriesTail (n d : ℕ) :
    denseLikelihoodTail n d =
      Causalean.Stat.Minimax.MomentMatchedMixture.exponentialSeriesTail
        (lowerDegree d) (poissonCellIntensity n d * denseAmplitude n d ^ 2) := by
  simp only [denseLikelihoodTail,
    Causalean.Stat.Minimax.MomentMatchedMixture.exponentialSeriesTail,
    Nat.lt_iff_add_one_le]

-- @node: poissonCellIntensity_mul_denseAmplitude_sq
/-- In the dense regime the exponential-tail argument is the chosen degree
divided by sixty-four. [The displayed identity or bound is the asserted conclusion](goal). -/
lemma poissonCellIntensity_mul_denseAmplitude_sq (n d : ℕ) (h : DenseRegime n d) :
    poissonCellIntensity n d * denseAmplitude n d ^ 2 = lowerDegree d / 64 := by
  have hdNat : 0 < d := lt_of_lt_of_le (by omega) h.1
  have hnNat : 0 < n := lt_trans (Nat.pow_pos hdNat) h.2
  have hn : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hnNat)
  have hd : (d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hdNat)
  rw [denseAmplitude_sq n d h, poissonCellIntensity]
  field_simp
  ring

-- @node: densePriorPair_support_mass_one
/-- A probability prior whose complement of `[-1,1]` is null has unit mass on
the support set, in the form expected by the mixture substrate. This uses [the prior is supported on the unit interval](hyp:hsupp). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma densePriorPair_support_mass_one (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (hsupp : nu (Set.Icc (-1) 1)ᶜ = 0) :
    nu {t : ℝ | |t| ≤ 1} = 1 := by
  have hset : {t : ℝ | |t| ≤ 1} = Set.Icc (-1) 1 := by
    ext t
    simp [abs_le]
  rw [hset]
  have hmeas : MeasurableSet (Set.Icc (-1 : ℝ) 1) := measurableSet_Icc
  have hunion : nu (Set.Icc (-1 : ℝ) 1) + nu (Set.Icc (-1) 1)ᶜ = nu Set.univ := by
    rw [← measure_union disjoint_compl_right hmeas.compl]
    congr
    exact Set.union_compl_self _
  rw [hsupp, add_zero, measure_univ] at hunion
  exact hunion

-- @node: denseSupportedSignKernel
/-- A globally probability-valued version of the scaled sign-count experiment.
Outside the prior support it falls back to the zero-contrast baseline; on the
support it is exactly the scaled Poisson sign-count law. -/
noncomputable def denseSupportedSignKernel (n d : ℕ) : Kernel ℝ DenseSignCounts :=
  (Kernel.const ℝ (denseSignBaseline (poissonCellIntensity n d))).withDensity
    (fun t r => if |t| ≤ 1 then ENNReal.ofReal (scaledDenseLikelihood n d t r) else 1)

/-- The promoted support-localized mixture theorem gives the paper's product
sign-count total-variation bound directly from the Cai--Low prior conditions. This uses [the sample size and alphabet lie in the dense regime](hyp:hregime), and [the two priors satisfy the moment-matching certificate](hyp:hpair). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma denseMomentMatchedSignProduct_tv {n d : ℕ} (hregime : DenseRegime n d)
    (nu0 nu1 : Measure ℝ)
    (hpair : DensePriorPairConditions (lowerDegree d) nu0 nu1) :
    Causalean.Stat.tvDist
        (Causalean.Stat.Minimax.MomentMatchedMixture.productPriorPredictive d nu0
          (denseSupportedSignKernel n d))
        (Causalean.Stat.Minimax.MomentMatchedMixture.productPriorPredictive d nu1
          (denseSupportedSignKernel n d)) ≤
      d * Real.sqrt (denseLikelihoodTail n d) := by
  let Q : Measure DenseSignCounts := denseSignBaseline (poissonCellIntensity n d)
  let K : Kernel ℝ DenseSignCounts := denseSupportedSignKernel n d
  letI : IsProbabilityMeasure nu0 := hpair.1
  letI : IsProbabilityMeasure nu1 := hpair.2.1
  have hQ : IsProbabilityMeasure Q := by
    dsimp [Q, denseSignBaseline]
    infer_instance
  letI : IsProbabilityMeasure Q := hQ
  have hf : Measurable (Function.uncurry fun t r =>
      if |t| ≤ 1 then ENNReal.ofReal (scaledDenseLikelihood n d t r) else 1) := by
    exact (measurable_scaledDenseLikelihood n d).ennreal_ofReal.ite
      (measurableSet_le (continuous_abs.measurable.comp measurable_fst) measurable_const)
      measurable_const
  have hK : ∀ t, IsProbabilityMeasure (K t) := by
    intro t
    rw [isProbabilityMeasure_iff]
    by_cases ht : |t| ≤ 1
    · rw [show K t = denseSignLaw (poissonCellIntensity n d)
          (denseAmplitude n d * t) by
        dsimp [K, Q, denseSupportedSignKernel]
        rw [Kernel.withDensity_apply
          (Kernel.const ℝ (denseSignBaseline (poissonCellIntensity n d))) hf t]
        simp only [ht, ↓reduceIte]
        exact (scaledDenseSignLaw_eq_withDensity n d hregime t ht).symm]
      simp [denseSignLaw]
    · dsimp [K, denseSupportedSignKernel]
      rw [Kernel.withDensity_apply
        (Kernel.const ℝ (denseSignBaseline (poissonCellIntensity n d))) hf t]
      simp [ht, measure_univ]
  have hsupp0 : nu0 {t : ℝ | |t| ≤ 1} = 1 :=
    densePriorPair_support_mass_one nu0 hpair.2.2.1
  have hsupp1 : nu1 {t : ℝ | |t| ≤ 1} = 1 :=
    densePriorPair_support_mass_one nu1 hpair.2.2.2.1
  have hmom : ∀ r ≤ lowerDegree d, ∫ t, t ^ r ∂nu0 = ∫ t, t ^ r ∂nu1 := by
    intro r hr
    exact (hpair.2.2.2.2.2.2.1 r hr).symm
  have htv :=
    Causalean.Stat.Minimax.MomentMatchedMixture.momentMatchedProductMixture_tv_le_of_supported
      d nu0 nu1 K Q (scaledDenseLikelihood n d) hK
      (poissonCellIntensity n d * denseAmplitude n d ^ 2) 1 (lowerDegree d)
      (by rw [poissonCellIntensity_mul_denseAmplitude_sq n d hregime]; positivity)
      (by norm_num) (measurable_scaledDenseLikelihood n d)
      (scaledDenseLikelihood_nonnegative_of_supported n d hregime)
      (by
        intro t ht
        dsimp [K, Q, denseSupportedSignKernel]
        rw [Kernel.withDensity_apply
          (Kernel.const ℝ (denseSignBaseline (poissonCellIntensity n d))) hf t]
        simp [ht])
      (scaledDenseLikelihood_exponentialGram n d hregime)
      hsupp0 hsupp1 hmom
  rw [denseLikelihoodTail_eq_exponentialSeriesTail]
  simpa [K, Q] using htv

/-- The deterministic construction part of the dense certificate follows from
the degree, amplitude, observed-law, and one-cell likelihood identities. This uses [the dense construction domain conditions hold](hyp:hdom), and [the sample size satisfies its stated restriction](hyp:hn). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma denseConstructionCertificate {n d : ℕ} {epsilon : ℝ}
    (hdom : DenseConstructionDomain n d epsilon) (hn : d ^ 2 < n) :
    (8 * logAlphabet d ≤ lowerDegree d ∧ lowerDegree d < 8 * logAlphabet d + 2) ∧
    denseAmplitude n d ^ 2 = lowerDegree d * d / (128 * n) ∧
    denseAmplitude n d ≤ 1 / 2 ∧
    (∀ theta : Fin d → ℝ,
      (∀ x, theta x ∈ Set.Icc (-denseAmplitude n d) (denseAmplitude n d)) →
      ∃ theta' : DenseContrast d, theta'.1 = theta ∧
        ∃ hmodel : ObservedModelClass epsilon (observedMarginal (denseLaw theta')),
          (∀ x, cellMass (observedMarginal (denseLaw theta')) x = 1 / d) ∧
          (∀ x, propensity (observedMarginal (denseLaw theta')) x = 1 / 2) ∧
          (∀ x, outcomeMean (observedMarginal (denseLaw theta')) true x =
            (1 + theta x) / 2) ∧
          (∀ x, outcomeMean (observedMarginal (denseLaw theta')) false x =
            (1 - theta x) / 2) ∧
          observedOptimalValue (observedMarginal (denseLaw theta')) hmodel =
            1 / 2 + (∑ x : Fin d, |theta x|) / (2 * d)) ∧
    (∀ theta theta' : ℝ,
      (∫ r : DenseSignCounts, oneCellLikelihood (poissonCellIntensity n d) theta r *
          oneCellLikelihood (poissonCellIntensity n d) theta' r
        ∂denseSignBaseline (poissonCellIntensity n d)) =
        Real.exp (poissonCellIntensity n d * theta * theta')) ∧
    densePriorSeparation n d = denseAmplitude n d *
      bestEvenApproxError (lowerDegree d) := by
  have hregime : DenseRegime n d := ⟨hdom.1, hn⟩
  refine ⟨lowerDegree_log_bounds d, denseAmplitude_sq n d hregime,
    (denseAmplitude_range n d hregime).2, ?_, ?_, rfl⟩
  · intro theta htheta
    exact denseBox_observed_spec hdom theta htheta
  · intro theta theta'
    exact oneCellLikelihood_inner _ _ _ (le_of_lt (by
      unfold poissonCellIntensity
      have hn0 : 0 < n := lt_trans (Nat.pow_pos (lt_of_lt_of_le (by omega) hdom.1)) hn
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
      have hdR : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le (by omega) hdom.1)
      positivity))

end CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched
