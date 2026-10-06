module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.BlockChronological
public import Causalean.Tactic.IntegralLinearity

/-!
# Covariance estimates for arbitrary-start PHIW blocks

Nonnegative scores with mean at most one turn the overlapping cross-moment
bound into the sharp covariance bound in equation (8). Centering the past
score and the future state test gives the disjoint-window estimate in (9).
The trajectory conditional-mean identity remains an explicit premise of the
assembly lemma; it is not asserted for the decoded segment law here.
-/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open MeasureTheory ProbabilityTheory
open CausalSmith.Stat.PomdpLatentOverlapMinimax
open Causalean.Mathlib.Probability.FiniteMarkovOscillation

/-- Nonnegative scores of mean at most one have absolute covariance at most any cross-moment
envelope that is at least one. For [the sample space](hyp:Ω), [the measure](hyp:μ),
[the x](hyp:X), [the y](hyp:Y), [the x assumption](hyp:hX), [the y assumption](hyp:hY),
[the x0 assumption](hyp:hX0), [the y0 assumption](hyp:hY0), [the x1 assumption](hyp:hX1),
[the y1 assumption](hyp:hY1), [the second event](hyp:B), [the second event assumption](hyp:hB),
and [the cross assumption](hyp:hcross), this establishes
[the partial-history importance-weighted covariance bound of nonnegative cross moment result](goal). -/
-- @node: phiw_covariance_le_of_nonnegative_cross_moment
lemma phiw_covariance_le_of_nonnegative_cross_moment
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (hX0 : ∀ᵐ ω ∂μ, 0 ≤ X ω) (hY0 : ∀ᵐ ω ∂μ, 0 ≤ Y ω)
    (hX1 : (∫ ω, X ω ∂μ) ≤ 1) (hY1 : (∫ ω, Y ω ∂μ) ≤ 1)
    (B : ℝ) (hB : 1 ≤ B) (hcross : (∫ ω, X ω * Y ω ∂μ) ≤ B) :
    |covariance X Y μ| ≤ B := by
  have hx := integral_nonneg_of_ae hX0
  have hy := integral_nonneg_of_ae hY0
  have hxy : 0 ≤ ∫ ω, X ω * Y ω ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [hX0, hY0] with ω hx hy
    exact mul_nonneg hx hy
  have hprod : (∫ ω, X ω ∂μ) * (∫ ω, Y ω ∂μ) ≤ 1 := by
    calc
      _ ≤ 1 * 1 := mul_le_mul hX1 hY1 hy (by norm_num)
      _ = 1 := one_mul _
  rw [covariance_eq_sub hX hY]
  change |(∫ ω, X ω * Y ω ∂μ) -
    (∫ ω, X ω ∂μ) * (∫ ω, Y ω ∂μ)| ≤ B
  exact abs_le.mpr ⟨by linarith, sub_le_self _ (mul_nonneg hx hy) |>.trans hcross⟩

/-- For overlapping windows, the chronological cross-moment envelope in (7) yields precisely the
covariance envelope in (8), with no extra factor two. For [the sample space](hyp:Ω),
[the measure](hyp:μ), [the x](hyp:X), [the y](hyp:Y), [the x assumption](hyp:hX),
[the y assumption](hyp:hY), [the x0 assumption](hyp:hX0), [the y0 assumption](hyp:hY0),
[the x1 assumption](hyp:hX1), [the y1 assumption](hyp:hY1), [the action-overlap factor](hyp:L),
[the action-overlap factor assumption](hyp:hL), [the history length](hyp:k),
[the stated assumption](hyp:h), and [the cross assumption](hyp:hcross), this establishes
[the partial-history importance-weighted overlap covariance of cross moment result](goal). -/
-- @node: phiw_overlap_covariance_of_cross_moment
lemma phiw_overlap_covariance_of_cross_moment
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (hX0 : ∀ᵐ ω ∂μ, 0 ≤ X ω) (hY0 : ∀ᵐ ω ∂μ, 0 ≤ Y ω)
    (hX1 : (∫ ω, X ω ∂μ) ≤ 1) (hY1 : (∫ ω, Y ω ∂μ) ≤ 1)
    (L : ℝ) (hL : 1 ≤ L) (k h : Nat)
    (hcross : (∫ ω, X ω * Y ω ∂μ) ≤ L ^ (k + 1 - h)) :
    |covariance X Y μ| ≤ L ^ (k + 1 - h) := by
  exact phiw_covariance_le_of_nonnegative_cross_moment μ X Y hX hY hX0 hY0
    hX1 hY1 _ (one_le_pow₀ hL) hcross

/-- Centering a nonnegative integrable score costs at most twice its mean in L¹. This holds
without stationarity. For [the sample space](hyp:Ω), [the measure](hyp:μ), [the x](hyp:X),
[the x assumption](hyp:hX), and [the x0 assumption](hyp:hX0), this establishes
[the partial-history importance-weighted centered l1 bound twice mean result](goal). -/
-- @node: phiw_centered_l1_le_twice_mean
lemma phiw_centered_l1_le_twice_mean
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Integrable X μ) (hX0 : ∀ᵐ ω ∂μ, 0 ≤ X ω) :
    (∫ ω, |X ω - ∫ v, X v ∂μ| ∂μ) ≤ 2 * ∫ ω, X ω ∂μ := by
  have hx := integral_nonneg_of_ae hX0
  calc
    _ ≤ ∫ ω, X ω + (∫ v, X v ∂μ) ∂μ := by
      apply integral_mono_ae (hX.sub (integrable_const _)).abs
        (hX.add (integrable_const _))
      filter_upwards [hX0] with ω hω
      calc
        |X ω - ∫ v, X v ∂μ| ≤ |X ω| + |∫ v, X v ∂μ| := abs_sub _ _
        _ = X ω + (∫ v, X v ∂μ) := by rw [abs_of_nonneg hω, abs_of_nonneg hx]
    _ = 2 * ∫ ω, X ω ∂μ := by
      rw [integral_add hX (integrable_const _)]
      simp only [integral_const, probReal_univ, one_smul]
      ring

/-- An anchored future test with oscillation at most `D` pairs with the centered nonnegative
past score with absolute expectation at most `2D`. Only the past score's mean, rather than its
supremum, enters the estimate. For [the sample space](hyp:Ω), [the measure](hyp:μ),
[the x](hyp:X), [the event family](hyp:F), [the x assumption](hyp:hX),
[the event family assumption](hyp:hF), [the x0 assumption](hyp:hX0),
[the x1 assumption](hyp:hX1), [the c](hyp:c), [the d](hyp:D), [the d assumption](hyp:hD), and
[the fbound assumption](hyp:hFbound), this establishes
[the partial-history importance-weighted centered pairing bound result](goal). -/
-- @node: phiw_centered_pairing_le
lemma phiw_centered_pairing_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X F : Ω → ℝ) (hX : MemLp X 2 μ) (hF : MemLp F 2 μ)
    (hX0 : ∀ᵐ ω ∂μ, 0 ≤ X ω) (hX1 : (∫ ω, X ω ∂μ) ≤ 1)
    (c D : ℝ) (hD : 0 ≤ D) (hFbound : ∀ᵐ ω ∂μ, |F ω - c| ≤ D) :
    |∫ ω, (X ω - ∫ v, X v ∂μ) * (F ω - c) ∂μ| ≤ 2 * D := by
  have hXi : Integrable X μ := hX.integrable (by norm_num)
  have hcenter : MemLp (fun ω ↦ X ω - ∫ v, X v ∂μ) 2 μ :=
    hX.sub (memLp_const _)
  have hfuture : MemLp (fun ω ↦ F ω - c) 2 μ := hF.sub (memLp_const _)
  have hl1 := phiw_centered_l1_le_twice_mean μ X hXi hX0
  calc
    _ ≤ ∫ ω, |(X ω - ∫ v, X v ∂μ) * (F ω - c)| ∂μ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ ω, |X ω - ∫ v, X v ∂μ| * D ∂μ := by
      apply integral_mono_ae (hcenter.integrable_mul hfuture).abs
        ((hXi.sub (integrable_const _)).abs.mul_const D)
      filter_upwards [hFbound] with ω hω
      change |(X ω - ∫ v, X v ∂μ) * (F ω - c)| ≤
        |X ω - ∫ v, X v ∂μ| * D
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hω (abs_nonneg _)
    _ = (∫ ω, |X ω - ∫ v, X v ∂μ| ∂μ) * D := integral_mul_const _ _
    _ ≤ (2 * ∫ ω, X ω ∂μ) * D := mul_le_mul_of_nonneg_right hl1 hD
    _ ≤ 2 * D := by nlinarith

/-- Marginal and cross-moment conditional-mean identities permit centering at any constant
before bounding a disjoint-window covariance. For [the sample space](hyp:Ω),
[the measure](hyp:μ), [the x](hyp:X), [the y](hyp:Y), [the event family](hyp:F),
[the x assumption](hyp:hX), [the y assumption](hyp:hY), [the event family assumption](hyp:hF),
[the mean assumption](hyp:hmean), [the cross assumption](hyp:hcross), and [the c](hyp:c), this
establishes
[the partial-history importance-weighted covariance equality centered future result](goal). -/
-- @node: phiw_covariance_eq_centered_future
lemma phiw_covariance_eq_centered_future
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y F : Ω → ℝ) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (hF : MemLp F 2 μ)
    (hmean : (∫ ω, Y ω ∂μ) = ∫ ω, F ω ∂μ)
    (hcross : (∫ ω, X ω * Y ω ∂μ) = ∫ ω, X ω * F ω ∂μ)
    (c : ℝ) :
    covariance X Y μ = ∫ ω, (X ω - ∫ v, X v ∂μ) * (F ω - c) ∂μ := by
  rw [covariance_eq_sub hX hY]
  change (∫ ω, X ω * Y ω ∂μ) -
    (∫ ω, X ω ∂μ) * (∫ ω, Y ω ∂μ) = _
  rw [hcross, hmean]
  have hXi : Integrable X μ := hX.integrable (by norm_num)
  have hFi : Integrable F μ := hF.integrable (by norm_num)
  simp_rw [sub_mul, mul_sub]
  have hXF : Integrable (fun ω ↦ X ω * F ω) μ := hX.integrable_mul hF
  integral_linearity
  simp only [integral_const, probReal_univ, one_smul]
  ring

/-- Once the future score has its chronological conditional-mean representation, contraction
gives equation (9) for an arbitrary start. The two moment identities must be established from
the trajectory law. For [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the model](hyp:m), [the class assumption](hyp:hClass),
[the candidate index](hyp:j), [the history length](hyp:k), [the stated assumption](hyp:h),
[the h assumption](hyp:hh), [the sample space](hyp:Ω), [the measure](hyp:μ), [the x](hyp:X),
[the y](hyp:Y), [the last](hyp:last), [the x assumption](hyp:hX), [the y assumption](hyp:hY),
[the event family assumption](hyp:hF), [the x0 assumption](hyp:hX0),
[the x1 assumption](hyp:hX1), [the mean assumption](hyp:hmean), and
[the cross assumption](hyp:hcross), this establishes
[the partial-history importance-weighted disjoint covariance of future identities result](goal). -/
-- @node: phiw_disjoint_covariance_of_future_identities
lemma phiw_disjoint_covariance_of_future_identities
    {T M : Nat} (t0 zeta C : ℝ) (m : ModelIndex T M)
    (hClass : PolicyListClass t0 zeta C m) (j : Fin M) (k h : Nat) (hh : k < h)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ) (last : Ω → JointState m.nX m.nH)
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (hF : MemLp (fun ω ↦ markovOperatorIter (listPolicyKernel m m.Mx.b)
      (h - k - 1) (phiwChronologicalMean m j k) (last ω)) 2 μ)
    (hX0 : ∀ᵐ ω ∂μ, 0 ≤ X ω) (hX1 : (∫ ω, X ω ∂μ) ≤ 1)
    (hmean : (∫ ω, Y ω ∂μ) = ∫ ω,
      markovOperatorIter (listPolicyKernel m m.Mx.b) (h - k - 1)
        (phiwChronologicalMean m j k) (last ω) ∂μ)
    (hcross : (∫ ω, X ω * Y ω ∂μ) = ∫ ω, X ω *
      markovOperatorIter (listPolicyKernel m m.Mx.b) (h - k - 1)
        (phiwChronologicalMean m j k) (last ω) ∂μ) :
    |covariance X Y μ| ≤ 2 * mixingAlpha t0 ^ (h - 1) := by
  let s₀ : JointState m.nX m.nH :=
    (⟨0, hClass.finite_state.1⟩, ⟨0, hClass.finite_state.2⟩)
  let f := markovOperatorIter (listPolicyKernel m m.Mx.b) (h - k - 1)
    (phiwChronologicalMean m j k)
  rw [phiw_covariance_eq_centered_future μ X Y (fun ω ↦ f (last ω))
    hX hY hF hmean hcross (f s₀)]
  apply phiw_centered_pairing_le μ X (fun ω ↦ f (last ω)) hX hF hX0 hX1
    (f s₀) (mixingAlpha t0 ^ (h - 1)) (pow_nonneg (Real.exp_nonneg _) _)
  exact Filter.Eventually.of_forall fun ω ↦
    phiw_disjoint_future_oscillation t0 zeta C m hClass j k h hh (last ω) s₀

end CausalSmith.Stat.PomdpPolicyclassRegret
