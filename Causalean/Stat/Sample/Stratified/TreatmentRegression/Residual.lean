module
public import Causalean.Stat.Sample.OccupancyWeightedMean.MomentBounds
public import Causalean.Stat.Sample.Stratified.TreatmentRegression.CategoricalLaw
public import Causalean.Stat.Sample.Stratified.TreatmentRegression.DesignAlgebra
public import Causalean.Stat.Sample.Stratified.TreatmentRegression.ObservedSupport
public import Causalean.Stat.Sample.Stratified.TreatmentRegression.ResidualWeights

/-! # Conditional regression residual second moments

Arm-cell residuals need only be centered and square integrable with their
conditional second moments bounded by M². Arbitrary nonnegative functions
of the finite observed design can weight the residual regression square.
Cross-coordinate terms vanish, and the sum of squared residualized treatment
weights equals the Gram, leaving the guarded reciprocal Gram envelope.
Conditional moments are stated as normalized positive-mass design-fiber
integrals, rather than choosing a conditional-expectation version on null fibers.
-/

@[expose] public section

noncomputable section

namespace Causalean.Stat.Sample.Stratified.TreatmentRegression

open MeasureTheory Set Causalean.Stat
open scoped BigOperators

variable {Ω κ : Type*} [MeasurableSpace Ω] [Fintype κ] [DecidableEq κ]
  [MeasurableSpace κ] [MeasurableSingletonClass κ]

/-- The residual assumptions on [an observation law μ](hyp:μ) with [cell label X](hyp:X),
[Boolean treatment A](hyp:A), [real outcome Y](hyp:Y), [arm-and-cell centres](hyp:center) and
[second-moment envelope M](hyp:M) require that [the label](hyp:X_measurable),
[the treatment](hyp:A_measurable) and [the outcome](hyp:Y_measurable) are measurable, that
[on each arm-cell event the residual Y minus its centre is square-integrable](hyp:residual_L2),
[integrates to zero](hyp:residual_centered), and [has integral of its square at most the event's
mass times M²](hyp:residual_second_moment). Null arm-cells are allowed; outcomes need not be
bounded. -/
structure ResidualAssumptions (μ : Measure Ω) (X : Ω → κ) (A : Ω → Bool)
    (Y : Ω → ℝ) (center : Bool → κ → ℝ) (M : ℝ) : Prop where
  X_measurable : Measurable X
  A_measurable : Measurable A
  Y_measurable : Measurable Y
  residual_L2 : ∀ a k, MemLp (supportedArmGroupResidual X A Y center a k) 2 μ
  residual_centered : ∀ a k,
    ∫ ω in armGroupEvent X A a k, armGroupResidual Y center a k ω ∂μ = 0
  residual_second_moment : ∀ a k,
    ∫ ω in armGroupEvent X A a k, (armGroupResidual Y center a k ω) ^ 2 ∂μ ≤
      (μ (armGroupEvent X A a k)).toReal * M ^ 2

/-- If [the observation law μ, label X, treatment A, outcome Y, centres and envelope M satisfy the
residual assumptions](hyp:μ,X,A,Y,center,M,h), then for [every sample size n](hyp:n)
[the guarded residual regression coefficient has a finite second moment under the iid product
law](goal).

All design-dependent coefficients take finitely many real values, even the
guarded reciprocal Gram. Expand into supported residuals, use finite maxima
to bound each design coefficient, and lift each residual L2 bound to the product. -/
lemma residualRegression_memLp (n : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → κ) (A : Ω → Bool) (Y : Ω → ℝ) (center : Bool → κ → ℝ) (M : ℝ)
    (h : ResidualAssumptions μ X A Y center M) :
    MemLp (residualRegression (n := n) X A Y center) 2
      (Measure.pi (fun _ : Fin n => μ)) := by
  have hm := designWeightedResidual_memLp n μ X A Y center h.X_measurable
    h.A_measurable h.Y_measurable h.residual_L2
    (fun d i => inverseGram d * residualWeight d i)
  convert hm using 1
  funext z
  exact residualRegression_eq_designWeightedResidual X A Y center z

/-- If [the observation law μ, label X, treatment A, outcome Y, centres and envelope M satisfy the
residual assumptions](hyp:μ,X,A,Y,center,M,h) and [W is a nonnegative weight on designs of n
cell-treatment pairs](hyp:n,W,hW), then under the iid product law [the expectation of W at the
observed design times the squared residual regression coefficient is at most M² times the
expectation of W times the guarded inverse Gram](goal).

Expand the numerator square over coordinates and arm-cell labels. Use
integral_designWeight_residual_cross_coordinates_eq_zero off the coordinate
diagonal; disjoint supports remove unequal arm-cell labels on that diagonal.
Apply integral_designWeight_residual_sq_le_indicator to the remaining terms
and sum_residualWeight_sq to collapse their coefficients. At D=0 all
coefficients are zero, so no division by zero occurs in the proof. -/
theorem integral_weighted_residualRegression_sq_le (n : ℕ) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → κ) (A : Ω → Bool) (Y : Ω → ℝ)
    (center : Bool → κ → ℝ) (M : ℝ) (h : ResidualAssumptions μ X A Y center M)
    (W : (Fin n → κ × Bool) → ℝ) (hW : ∀ d, 0 ≤ W d) :
    (∫ z : Fin n → Ω, W (sampleDesign X A z) *
      residualRegression X A Y center z ^ 2 ∂Measure.pi (fun _ : Fin n => μ)) ≤
      M ^ 2 * ∫ z : Fin n → Ω, W (sampleDesign X A z) *
        inverseGram (sampleDesign X A z) ∂Measure.pi (fun _ : Fin n => μ) := by
  have hb (d : Fin n → κ × Bool) :
      (∑ i, (inverseGram d * residualWeight d i) ^ 2) = inverseGram d := by
    simp only [mul_pow, ← Finset.mul_sum, sum_residualWeight_sq]
    unfold inverseGram
    by_cases hd : 0 < gram d
    · simp only [hd, if_pos]
      field_simp [ne_of_gt hd]
    · simp [hd]
  have hv := integral_designWeightedResidual_sq_le n μ X A Y center M
    h.X_measurable h.A_measurable h.Y_measurable h.residual_L2
    h.residual_centered h.residual_second_moment
    (fun d i => inverseGram d * residualWeight d i) W hW
  simpa only [← residualRegression_eq_designWeightedResidual, hb] using hv

/-- If [the observation law μ, label X, treatment A, outcome Y, centres and envelope M satisfy the
residual assumptions](hyp:μ,X,A,Y,center,M,h), and [a design d of n cell-treatment pairs has
positive Gram denominator D](hyp:n,d,hD) and [positive probability of being observed](hyp:hd),
then [the conditional second moment of the residual regression coefficient given that the
observed design equals d is at most M²/D](goal).

Apply integral_weighted_residualRegression_sq_le with the finite-design
weight W e = if e = d then 1 else 0. Rewrite both integrals as fiber integrals;
inverseGram is constant on the fiber. Divide by its positive mass, then use
hD to unfold inverseGram. The preceding residualRegression_memLp supplies
integrability of the square without a bounded-outcome hypothesis. -/
theorem conditional_residualRegression_sq_le (n : ℕ) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → κ) (A : Ω → Bool) (Y : Ω → ℝ)
    (center : Bool → κ → ℝ) (M : ℝ) (h : ResidualAssumptions μ X A Y center M)
    (d : Fin n → κ × Bool) (hD : 0 < gram d)
    (hd : 0 < ((Measure.pi (fun _ : Fin n => μ)) {z | sampleDesign X A z = d}).toReal) :
    (∫ z in {z | sampleDesign X A z = d}, residualRegression X A Y center z ^ 2
      ∂Measure.pi (fun _ : Fin n => μ)) /
        ((Measure.pi (fun _ : Fin n => μ)) {z | sampleDesign X A z = d}).toReal ≤
      M ^ 2 / gram d := by
  classical
  let S : Set (Fin n → Ω) := {z | sampleDesign X A z = d}
  have hS : MeasurableSet S :=
    (measurable_sampleDesign X A h.X_measurable h.A_measurable)
      (measurableSet_singleton d)
  have hw := integral_weighted_residualRegression_sq_le n μ X A Y center M h
    (fun e => if e = d then 1 else 0) (by intro e; split_ifs <;> norm_num)
  have hleft : (fun z : Fin n → Ω =>
      (if sampleDesign X A z = d then (1 : ℝ) else 0) *
        residualRegression X A Y center z ^ 2) =
      S.indicator (fun z => residualRegression X A Y center z ^ 2) := by
    funext z
    by_cases hz : sampleDesign X A z = d <;> simp [S, hz]
  have hright : (fun z : Fin n → Ω =>
      (if sampleDesign X A z = d then (1 : ℝ) else 0) *
        inverseGram (sampleDesign X A z)) =
      S.indicator (fun _ => inverseGram d) := by
    funext z
    by_cases hz : sampleDesign X A z = d <;> simp [S, hz]
  rw [hleft, hright, integral_indicator hS, integral_indicator hS,
    setIntegral_const, smul_eq_mul] at hw
  apply (div_le_iff₀ hd).2
  simpa [S, Measure.real, inverseGram, hD, div_eq_mul_inv,
    mul_assoc, mul_comm, mul_left_comm] using hw

/-- For [a sample z of n observations](hyp:n,z) with [cell label X](hyp:X),
[treatment A](hyp:A), [outcome Y](hyp:Y) and [arm-and-cell centres](hyp:center), if
[the observed design has positive Gram denominator](hyp:hD) and [at every sampled cell the treated
centre minus the control centre equals a common contrast θ](hyp:theta,hcontrast), then [the
un-clipped regression coefficient minus θ equals the residual regression coefficient](goal).

Write each sampled center as center false (X (z i)) plus its Boolean treatment
indicator times theta. Partition the baseline weighted sum by cells and use
sum_residualWeight_cell to kill it. sum_residualWeight_treatment gives theta
 times the Gram for the contrast part; divide using hD. -/
lemma regression_sub_eq_residualRegression {n : ℕ} (X : Ω → κ) (A : Ω → Bool)
    (Y : Ω → ℝ) (center : Bool → κ → ℝ) (theta : ℝ) (z : Fin n → Ω)
    (hD : 0 < gram (sampleDesign X A z))
    (hcontrast : ∀ i, center true (X (z i)) - center false (X (z i)) = theta) :
    regression (sampleDesign X A z) (fun i => Y (z i)) - theta =
      residualRegression X A Y center z := by
  classical
  let d := sampleDesign X A z
  have hbase : (∑ i, residualWeight d i * center false (X (z i))) = 0 := by
    calc
      _ = ∑ k : κ, (∑ i, if (d i).1 = k then residualWeight d i else 0) *
          center false k := by
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        simp [d, sampleDesign]
      _ = 0 := by simp [sum_residualWeight_cell]
  have hc (i : Fin n) : center (A (z i)) (X (z i)) =
      center false (X (z i)) + (if (d i).2 then (1 : ℝ) else 0) * theta := by
    cases ha : A (z i) <;> simp [d, sampleDesign, ha] <;> linarith [hcontrast i]
  have hsum : (∑ i, residualWeight d i * center (A (z i)) (X (z i))) =
      gram d * theta := by
    simp_rw [hc, mul_add, ← mul_assoc]
    rw [Finset.sum_add_distrib, hbase, ← Finset.sum_mul,
      sum_residualWeight_treatment, zero_add]
  unfold residualRegression regression
  simp only [hD, if_pos]
  change numerator d (fun i => Y (z i)) / gram d - theta =
    numerator d (fun i => Y (z i) - center (A (z i)) (X (z i))) / gram d
  simp only [numerator, mul_sub, Finset.sum_sub_distrib, hsum]
  have hd0 : gram d ≠ 0 := ne_of_gt hD
  field_simp [hd0]

/-- If [the observation law μ, label X, treatment A, outcome Y, centres and envelope M satisfy the
residual assumptions](hyp:μ,X,A,Y,center,M,h), [on every cell of positive probability the treated
centre minus the control centre equals a common contrast θ](hyp:theta,hcontrast), and [a design d
of n cell-treatment pairs has positive Gram denominator D](hyp:n,d,hD) and [positive probability of
being observed](hyp:hd), then [the conditional mean squared error of the un-clipped regression
coefficient about θ, given that the observed design equals d, is at most M²/D](goal).

With a common center contrast on occupied population cells, the un-clipped
regression error has conditional second moment at most M²/D on every
positive-probability design fiber with D>0. Null cells need no center constraint.

Use ae_sample_cell_positive from ObservedSupport to apply hcontrast almost
surely at every coordinate. Restrict this AE fact to the design fiber, rewrite
the squared error using regression_sub_eq_residualRegression and hD, and
invoke conditional_residualRegression_sq_le. -/
theorem conditional_regression_error_sq_le (n : ℕ) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → κ) (A : Ω → Bool) (Y : Ω → ℝ)
    (center : Bool → κ → ℝ) (M theta : ℝ) (h : ResidualAssumptions μ X A Y center M)
    (hcontrast : ∀ k, 0 < cellProbability (μ.map (fun ω => (X ω, A ω))) k →
      center true k - center false k = theta)
    (d : Fin n → κ × Bool) (hD : 0 < gram d)
    (hd : 0 < ((Measure.pi (fun _ : Fin n => μ)) {z | sampleDesign X A z = d}).toReal) :
    (∫ z in {z | sampleDesign X A z = d},
      (regression (sampleDesign X A z) (fun i => Y (z i)) - theta) ^ 2
      ∂Measure.pi (fun _ : Fin n => μ)) /
        ((Measure.pi (fun _ : Fin n => μ)) {z | sampleDesign X A z = d}).toReal ≤
      M ^ 2 / gram d := by
  have hS : MeasurableSet {z : Fin n → Ω | sampleDesign X A z = d} :=
    (measurable_sampleDesign X A h.X_measurable h.A_measurable)
      (measurableSet_singleton d)
  have heq : (∫ z in {z | sampleDesign X A z = d},
      (regression (sampleDesign X A z) (fun i => Y (z i)) - theta) ^ 2
      ∂Measure.pi (fun _ : Fin n => μ)) =
      ∫ z in {z | sampleDesign X A z = d}, residualRegression X A Y center z ^ 2
        ∂Measure.pi (fun _ : Fin n => μ) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae
      (ae_sample_cell_positive n μ X A h.X_measurable h.A_measurable),
      ae_restrict_mem hS] with z hz hzd
    have hg : 0 < gram (sampleDesign X A z) := by rw [hzd]; exact hD
    rw [regression_sub_eq_residualRegression X A Y center theta z hg
      (fun i => hcontrast _ (hz i))]
  rw [heq]
  exact conditional_residualRegression_sq_le n μ X A Y center M h d hD hd

end Causalean.Stat.Sample.Stratified.TreatmentRegression
