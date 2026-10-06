module
public import Causalean.Stat.Sample.Stratified.TreatmentRegression.ClipBounds
public import Causalean.Stat.Sample.Stratified.TreatmentRegression.Concentration
public import Causalean.Stat.Sample.Stratified.TreatmentRegression.Residual
public import Mathlib.Tactic.NormNum

/-! # Finite-sample MSE of clipped within-cell regression

The good-design conditional second moment costs M²/(c n). On the bad event,
interval clipping bounds squared error by four times the squared interval
radius. Combining the derived Gram tail and residual theorem yields a uniform
1/n risk bound, including D=0, n=1, arbitrary masses, and null cells.

The general theorem allows a clipping radius R distinct from the residual
moment envelope M. With R=M and epsilon=1/4 its constant is 33152/9, less
than the reference constant 72+4(1296+729/64).
-/

public section

namespace Causalean.Stat.Sample.Stratified.TreatmentRegression

open MeasureTheory Set Causalean.Stat
open scoped BigOperators

variable {Ω κ : Type*} [MeasurableSpace Ω] [Fintype κ] [DecidableEq κ]
  [MeasurableSpace κ] [MeasurableSingletonClass κ]

/-- Clipped regression squared error is integrable under any finite iid law
when the [observation maps are measurable](hyp:hX,hA,hY), the [clipping radius
is nonnegative](hyp:hR), and the [target lies in the clipping interval](hyp:htheta).
The [integrability conclusion](goal) needs no outcome moment bound. -/
lemma integrable_clipped_error_sq (n : ℕ) (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → κ) (A : Ω → Bool) (Y : Ω → ℝ) (R theta : ℝ)
    (hX : Measurable X) (hA : Measurable A) (hY : Measurable Y)
    (hR : 0 ≤ R) (htheta : theta ∈ Icc (-R) R) :
    Integrable (fun z : Fin n → Ω => (clippedEstimator X A Y R z - theta) ^ 2)
      (Measure.pi (fun _ : Fin n => μ)) := by
  have hm : Measurable (fun z : Fin n → Ω =>
      (clippedEstimator X A Y R z - theta) ^ 2) :=
    ((measurable_clippedEstimator X A Y R hX hA hY).sub measurable_const).pow_const 2
  apply Integrable.of_bound hm.aestronglyMeasurable (4 * R ^ 2)
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact clip_sq_error_le_four R _ theta hR htheta

/-- Suppose [the observation law μ, label X, treatment A, outcome Y, centres and envelope M satisfy
the residual assumptions](hyp:μ,X,A,Y,center,M,h), [the clipping radius R is
nonnegative](hyp:R,hR), [the target θ lies between −R and R](hyp:theta,htheta), and [on every
cell of positive probability the treated centre minus the control centre equals θ](hyp:hcontrast).
Then for [every positive Gram threshold t](hyp:t,ht) and [every sample size n](hyp:n),
[the integral of the squared error of the clipped estimator about θ over samples whose Gram
denominator is at least t is at most M²/t](goal).

Use S = {z | t ≤ gram (sampleDesign X A z)} and the design weight
W d = if t ≤ gram d then 1 else 0 in
integral_weighted_residualRegression_sq_le. On S, ae_sample_cell_positive
and regression_sub_eq_residualRegression identify the un-clipped error with
the residual regression; clip_sq_error_le then gives a set-integral inequality.
Integrability comes from integrable_clipped_error_sq and
(residualRegression_memLp ...).integrable_sq. Rewrite the weighted integrals
with integral_indicator. The design-only function W d * inverseGram d lies
between zero and 1/t: on S use t>0 and reciprocal monotonicity, outside S it
is zero. Integrable.of_bound and integral_mono_ae bound its integral by 1/t.
This route avoids enumerating positive-mass fibers or introducing conditional
expectations, and applies without any sample-size or overlap assumption. -/
theorem integral_good_error_sq_le (n : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → κ) (A : Ω → Bool) (Y : Ω → ℝ) (center : Bool → κ → ℝ)
    (M R theta t : ℝ) (h : ResidualAssumptions μ X A Y center M)
    (hR : 0 ≤ R) (htheta : theta ∈ Icc (-R) R) (ht : 0 < t)
    (hcontrast : ∀ k, 0 < cellProbability (μ.map (fun ω => (X ω, A ω))) k →
      center true k - center false k = theta) :
    (∫ z in {z : Fin n → Ω | t ≤ gram (sampleDesign X A z)},
      (clippedEstimator X A Y R z - theta) ^ 2 ∂Measure.pi (fun _ : Fin n => μ)) ≤
      M ^ 2 / t := by
  classical
  let P := Measure.pi (fun _ : Fin n => μ)
  let S : Set (Fin n → Ω) := {z | t ≤ gram (sampleDesign X A z)}
  let W : (Fin n → κ × Bool) → ℝ := fun d => if t ≤ gram d then 1 else 0
  have hS : MeasurableSet S := measurableSet_le measurable_const
    ((measurable_designStatistic gram).comp
      (measurable_sampleDesign X A h.X_measurable h.A_measurable))
  have hf := integrable_clipped_error_sq n μ X A Y R theta
    h.X_measurable h.A_measurable h.Y_measurable hR htheta
  have hg := (residualRegression_memLp n μ X A Y center M h).integrable_sq
  have hgood : (∫ z in S, (clippedEstimator X A Y R z - theta) ^ 2 ∂P) ≤
      ∫ z in S, residualRegression X A Y center z ^ 2 ∂P := by
    apply setIntegral_mono_ae_restrict hf.integrableOn hg.integrableOn
    filter_upwards [ae_restrict_of_ae
      (ae_sample_cell_positive n μ X A h.X_measurable h.A_measurable),
      ae_restrict_mem hS] with z hz hzt
    have hD : 0 < gram (sampleDesign X A z) := lt_of_lt_of_le ht hzt
    have heq := regression_sub_eq_residualRegression X A Y center theta z hD
      (fun i => hcontrast _ (hz i))
    simpa only [clippedEstimator, heq] using
      clip_sq_error_le R (regression (sampleDesign X A z) (fun i => Y (z i)))
        theta hR htheta
  have hw := integral_weighted_residualRegression_sq_le n μ X A Y center M h
    W (by intro d; dsimp [W]; split_ifs <;> norm_num)
  have hleft : (fun z : Fin n → Ω => W (sampleDesign X A z) *
      residualRegression X A Y center z ^ 2) =
      S.indicator (fun z => residualRegression X A Y center z ^ 2) := by
    funext z
    by_cases hz : t ≤ gram (sampleDesign X A z) <;> simp [W, S, hz]
  rw [hleft, integral_indicator hS] at hw
  have hb (z : Fin n → Ω) :
      0 ≤ W (sampleDesign X A z) * inverseGram (sampleDesign X A z) ∧
      W (sampleDesign X A z) * inverseGram (sampleDesign X A z) ≤ 1 / t := by
    by_cases hz : t ≤ gram (sampleDesign X A z)
    · have hD := lt_of_lt_of_le ht hz
      simpa [W, hz, inverseGram, hD, one_div] using
        And.intro (inv_nonneg.mpr hD.le) (one_div_le_one_div_of_le ht hz)
    · simp [W, hz, le_of_lt ht]
  have hi : Integrable (fun z : Fin n → Ω =>
      W (sampleDesign X A z) * inverseGram (sampleDesign X A z)) P := by
    apply Integrable.of_bound
      (((measurable_designStatistic (fun d => W d * inverseGram d)).comp
        (measurable_sampleDesign X A h.X_measurable h.A_measurable)).aestronglyMeasurable)
      (1 / t)
    filter_upwards [] with z
    dsimp only [Function.comp_def]
    rw [Real.norm_eq_abs, abs_of_nonneg (hb z).1]
    exact (hb z).2
  have hbound : (∫ z : Fin n → Ω,
      W (sampleDesign X A z) * inverseGram (sampleDesign X A z) ∂P) ≤ 1 / t := by
    calc
      _ ≤ ∫ _ : Fin n → Ω, (1 / t : ℝ) ∂P :=
        integral_mono_ae hi (integrable_const _) (Filter.Eventually.of_forall (fun z => (hb z).2))
      _ = 1 / t := by simp [P]
  calc
    _ ≤ ∫ z in S, residualRegression X A Y center z ^ 2 ∂P := hgood
    _ ≤ M ^ 2 * ∫ z : Fin n → Ω,
        W (sampleDesign X A z) * inverseGram (sampleDesign X A z) ∂P := hw
    _ ≤ M ^ 2 * (1 / t) := mul_le_mul_of_nonneg_left hbound (sq_nonneg M)
    _ = M ^ 2 / t := by ring

/-- Suppose [the observation law μ, label X, treatment A, outcome Y, centres and envelope M satisfy
the residual assumptions](hyp:μ,X,A,Y,center,M,h), [the clipping radius R is
nonnegative](hyp:R,hR), [the target θ lies between −R and R](hyp:theta,htheta), and [on every
cell of positive probability the treated centre minus the control centre equals θ](hyp:hcontrast).
Then for [every positive Gram threshold t](hyp:t,ht) and [every sample size n](hyp:n),
[the mean squared error of the clipped estimator about θ is at most M²/t plus 4R² times the
probability that the Gram denominator is below t](goal). That bad-design probability is
subsequently bounded by the Gram lower tail.

The good set S is measurable by measurable_designStatistic gram composed
with measurable_sampleDesign. Apply integral_add_compl to the integrable
clipped squared error; its S contribution is integral_good_error_sq_le.
Its complementary contribution is at most the integral of the constant
4*R^2 by clip_sq_error_le_four and setIntegral_mono_ae. Rewrite that constant
integral with setIntegral_const, and identify S complement with {z | D<t}.
Keep the zero-Gram case in the complementary event; no division by D is
needed there. -/
theorem integral_clipped_error_sq_le_split (n : ℕ) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → κ) (A : Ω → Bool) (Y : Ω → ℝ)
    (center : Bool → κ → ℝ) (M R theta t : ℝ)
    (h : ResidualAssumptions μ X A Y center M)
    (hR : 0 ≤ R) (htheta : theta ∈ Icc (-R) R) (ht : 0 < t)
    (hcontrast : ∀ k, 0 < cellProbability (μ.map (fun ω => (X ω, A ω))) k →
      center true k - center false k = theta) :
    (∫ z : Fin n → Ω, (clippedEstimator X A Y R z - theta) ^ 2
      ∂Measure.pi (fun _ : Fin n => μ)) ≤
      M ^ 2 / t + 4 * R ^ 2 *
        ((Measure.pi (fun _ : Fin n => μ)) {z | gram (sampleDesign X A z) < t}).toReal := by
  let P := Measure.pi (fun _ : Fin n => μ)
  let S : Set (Fin n → Ω) := {z | t ≤ gram (sampleDesign X A z)}
  have hS : MeasurableSet S := measurableSet_le measurable_const
    ((measurable_designStatistic gram).comp
      (measurable_sampleDesign X A h.X_measurable h.A_measurable))
  have hf := integrable_clipped_error_sq n μ X A Y R theta
    h.X_measurable h.A_measurable h.Y_measurable hR htheta
  have hgood := integral_good_error_sq_le n μ X A Y center M R theta t
    h hR htheta ht hcontrast
  have hbad : (∫ z in Sᶜ, (clippedEstimator X A Y R z - theta) ^ 2 ∂P) ≤
      4 * R ^ 2 * (P Sᶜ).toReal := by
    calc
      _ ≤ ∫ _ : Fin n → Ω in Sᶜ, (4 * R ^ 2 : ℝ) ∂P := by
        apply setIntegral_mono_ae hf.integrableOn (integrable_const _)
        filter_upwards [] with z
        exact clip_sq_error_le_four R _ theta hR htheta
      _ = 4 * R ^ 2 * (P Sᶜ).toReal := by
        rw [setIntegral_const, smul_eq_mul]
        exact mul_comm _ _
  have hcompl : Sᶜ = {z | gram (sampleDesign X A z) < t} := by
    ext z
    simp [S, not_le]
  rw [← integral_add_compl hS hf]
  calc
    _ ≤ M ^ 2 / t + 4 * R ^ 2 * (P Sᶜ).toReal := add_le_add hgood hbad
    _ = _ := by rw [hcompl]

/-- Suppose [the observation law μ, label X, treatment A, outcome Y, centres and envelope M satisfy
the residual assumptions](hyp:μ,X,A,Y,center,M,h), [the sample size n is positive](hyp:n,hn) and
[at least the number of cells](hyp:hcard), [the clipping radius R is nonnegative](hyp:R,hR),
[the target θ lies between −R and R](hyp:theta,htheta), [the overlap margin ε is
positive](hyp:epsilon,hepsilon) and [at most one half](hyp:hhalf), [every cell of positive
probability has propensity between ε and 1 − ε](hyp:hoverlap), and [on every such cell the treated
centre minus the control centre equals θ](hyp:hcontrast). Then [the mean squared error of the
clipped within-cell regression estimator about θ is at most (M²/c + 4R²·C)/n, where c is the
good-design threshold and C the uniform Gram lower-tail constant at ε](goal).

Occupied-cell overlap and a common occupied-cell center contrast give
a uniform finite-sample MSE bound for clipped within-cell regression under
conditional residual second moments at most M². It applies to every positive
sample size with at most n cells, allows null cells, and includes a zero Gram.

Prove c=gramThreshold epsilon positive using hepsilon and hhalf; n is
positive after coercion. Apply integral_clipped_error_sq_le_split with t=c*n,
then observed_gram_lower_tail with h.X_measurable and h.A_measurable.
Multiply the tail inequality by the nonnegative 4*R^2 and normalize
M^2/(c*n) + 4*R^2*(C/n) to the displayed numerator divided by n.
The observed tail already handles n=1, so the n≥2 occupancy theorem is not
needed here. -/
theorem clipped_regression_mse_le (n : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → κ) (A : Ω → Bool) (Y : Ω → ℝ) (center : Bool → κ → ℝ)
    (M R theta epsilon : ℝ) (h : ResidualAssumptions μ X A Y center M)
    (hn : 0 < n) (hcard : Fintype.card κ ≤ n)
    (hR : 0 ≤ R) (htheta : theta ∈ Icc (-R) R)
    (hepsilon : 0 < epsilon) (hhalf : epsilon ≤ 1 / 2)
    (hoverlap : ∀ k, 0 < cellProbability (μ.map (fun ω => (X ω, A ω))) k →
      epsilon ≤ propensity (μ.map (fun ω => (X ω, A ω))) k ∧
        propensity (μ.map (fun ω => (X ω, A ω))) k ≤ 1 - epsilon)
    (hcontrast : ∀ k, 0 < cellProbability (μ.map (fun ω => (X ω, A ω))) k →
      center true k - center false k = theta) :
    (∫ z : Fin n → Ω, (clippedEstimator X A Y R z - theta) ^ 2
      ∂Measure.pi (fun _ : Fin n => μ)) ≤
      (M ^ 2 / gramThreshold epsilon + 4 * R ^ 2 * gramTailConstant epsilon) / n := by
  have hc : 0 < gramThreshold epsilon := by
    unfold gramThreshold
    have he : 0 < 1 - epsilon := by linarith
    exact div_pos (mul_pos hepsilon he) (by norm_num)
  have hnreal : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hsplit := integral_clipped_error_sq_le_split n μ X A Y center M R theta
    (gramThreshold epsilon * n) h hR htheta (mul_pos hc hnreal) hcontrast
  have htail := observed_gram_lower_tail n μ X A h.X_measurable h.A_measurable
    hn hcard epsilon hepsilon hhalf hoverlap
  calc
    _ ≤ M ^ 2 / (gramThreshold epsilon * n) + 4 * R ^ 2 *
        ((Measure.pi (fun _ : Fin n => μ))
          {z | gram (sampleDesign X A z) < gramThreshold epsilon * n}).toReal := hsplit
    _ ≤ M ^ 2 / (gramThreshold epsilon * n) +
        4 * R ^ 2 * (gramTailConstant epsilon / n) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left htail
        (show 0 ≤ 4 * R ^ 2 by positivity))
    _ = _ := by field_simp

/-- Suppose [the observation law μ, label X, treatment A, outcome Y, centres and envelope M satisfy
the residual assumptions](hyp:μ,X,A,Y,center,M,h), [the sample size n is positive](hyp:n,hn) and
[at least the number of cells](hyp:hcard), [the envelope M is nonnegative](hyp:hM), [the target θ
lies between −M and M](hyp:theta,htheta), [every cell of positive probability has propensity
between 1/4 and 3/4](hyp:hoverlap), and [on every such cell the treated centre minus the control
centre equals θ](hyp:hcontrast). Then [the within-cell regression estimator clipped at radius M has
mean squared error about θ at most (33152/9)·M²/n](goal), uniformly over cell masses.

Instantiate clipped_regression_mse_le with R=M and epsilon=1/4. Unfold
gramThreshold and gramTailConstant and normalize their rational values
(3/128 and 8192/9). Ring arithmetic identifies the numerator with
(33152/9)*M^2, including M=0. -/
theorem clipped_regression_mse_le_quarter (n : ℕ) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → κ) (A : Ω → Bool) (Y : Ω → ℝ)
    (center : Bool → κ → ℝ) (M theta : ℝ) (h : ResidualAssumptions μ X A Y center M)
    (hn : 0 < n) (hcard : Fintype.card κ ≤ n)
    (hM : 0 ≤ M) (htheta : theta ∈ Icc (-M) M)
    (hoverlap : ∀ k, 0 < cellProbability (μ.map (fun ω => (X ω, A ω))) k →
      (1 / 4 : ℝ) ≤ propensity (μ.map (fun ω => (X ω, A ω))) k ∧
        propensity (μ.map (fun ω => (X ω, A ω))) k ≤ 1 - (1 / 4 : ℝ))
    (hcontrast : ∀ k, 0 < cellProbability (μ.map (fun ω => (X ω, A ω))) k →
      center true k - center false k = theta) :
    (∫ z : Fin n → Ω, (clippedEstimator X A Y M z - theta) ^ 2
      ∂Measure.pi (fun _ : Fin n => μ)) ≤ (33152 / 9 : ℝ) * M ^ 2 / n := by
  have hmse := clipped_regression_mse_le n μ X A Y center M M theta (1 / 4)
    h hn hcard hM htheta (by norm_num) (by norm_num) hoverlap hcontrast
  have hconstant : M ^ 2 / gramThreshold (1 / 4) +
      4 * M ^ 2 * gramTailConstant (1 / 4) = (33152 / 9 : ℝ) * M ^ 2 := by
    norm_num [gramThreshold, gramTailConstant]
    ring
  rwa [hconstant] at hmse

/-- [The quarter-overlap risk constant 33152/9 is at most the reference constant
72 + 4(1296 + 729/64)](goal). -/
lemma quarter_constant_le_paper :
    (33152 / 9 : ℝ) ≤ 72 + 4 * (1296 + 729 / 64) := by
  norm_num

end Causalean.Stat.Sample.Stratified.TreatmentRegression
