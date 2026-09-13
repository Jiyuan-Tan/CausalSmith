import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.WitnessQuantitative
import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.GaussianRecoveryBridge
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-!
# Cancellation-witness calculus

This file isolates the fundamental-theorem-of-calculus identity behind equality
of the cancellation witness's observational and parent-interventional ratio laws.
-/

open MeasureTheory Set

noncomputable section

namespace CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

-- @node: canonicalObservedWorld_observedLawRatio_ae_eq_mechanismRatio
/-- In the canonical world, the law-defined Radon--Nikodym ratio agrees almost everywhere
under the observational law with the explicit mechanism ratio.  Given [the stated inputs and conditions](hyp:hpos), [the stated conclusion](goal) follows. -/
lemma canonicalObservedWorld_observedLawRatio_ae_eq_mechanismRatio
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (hpos : PositiveNormalizedSmoothMechanisms G θ) (π : Equiv.Perm (Fin n))
    (i : Fin n) :
    observedLawRatio (canonicalObservedWorld G θ π).law i =ᵐ[observationalLaw θ]
      fun v => θ.q (π i) (v (π i)) / θ.p (π i) v := by
  let W := canonicalObservedWorld G θ π
  have hone := canonicalObservedWorld_onePerfectInterventionPerNode hpos π
  filter_upwards [hone.2.2.1 i, observationalLaw_ae_mem_latentCube hpos] with v hrv hv
  change ((interventionalLaw θ (π i)).rnDeriv (observationalLaw θ) v).toReal = _
  calc
    _ = (ENNReal.ofReal (W.ratio i v)).toReal := congrArg ENNReal.toReal hrv.symm
    _ = W.ratio i v := ENNReal.toReal_ofReal
      (div_nonneg (hpos.2.1 _ _ (hv (π i) (Set.mem_univ _))).le
        (hpos.1 _ _ hv).le)
    _ = _ := by rfl

-- @node: canonical_observationalRatioLaw_eq_mechanismRatio_map
/-- The canonical observational ratio law is the pushforward of the observational latent
law by the explicit mechanism ratio.  Given [the stated inputs and conditions](hyp:hpos), [the stated conclusion](goal) follows. -/
lemma canonical_observationalRatioLaw_eq_mechanismRatio_map
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (hpos : PositiveNormalizedSmoothMechanisms G θ) (π : Equiv.Perm (Fin n))
    (i : Fin n) :
    observationalRatioLaw (canonicalObservedWorld G θ π) i =
      Measure.map (fun v => θ.q (π i) (v (π i)) / θ.p (π i) v)
        (observationalLaw θ) := by
  unfold observationalRatioLaw
  exact Measure.map_congr
    (canonicalObservedWorld_observedLawRatio_ae_eq_mechanismRatio hpos π i)

-- @node: canonical_interventionalRatioLaw_eq_mechanismRatio_map
/-- The canonical interventional ratio law is the pushforward of the corresponding latent
interventional law by the same explicit mechanism ratio.  Given [the stated inputs and conditions](hyp:hpos), [the stated conclusion](goal) follows. -/
lemma canonical_interventionalRatioLaw_eq_mechanismRatio_map
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (hpos : PositiveNormalizedSmoothMechanisms G θ) (π : Equiv.Perm (Fin n))
    (j i : Fin n) :
    interventionalRatioLaw (canonicalObservedWorld G θ π) j i =
      Measure.map (fun v => θ.q (π i) (v (π i)) / θ.p (π i) v)
        (interventionalLaw θ (π j)) := by
  let W := canonicalObservedWorld G θ π
  have hac : interventionalLaw θ (π j) ≪ observationalLaw θ := by
    simpa only [W, canonicalObservedWorld] using
      interventionalLaw_absolutelyContinuous_observational W hpos j
  unfold interventionalRatioLaw
  change Measure.map (observedLawRatio W.law i) (interventionalLaw θ (π j)) = _
  exact Measure.map_congr
    (hac.ae_eq
      (canonicalObservedWorld_observedLawRatio_ae_eq_mechanismRatio hpos π i))

-- @node: canonical_observationalRatioLaw_secondMoment_eq
/-- The second moment of the canonical observational ratio law is the latent observational
integral of the square of the explicit mechanism ratio.  Given [the stated inputs and conditions](hyp:hpos), [the stated conclusion](goal) follows. -/
lemma canonical_observationalRatioLaw_secondMoment_eq
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (hpos : PositiveNormalizedSmoothMechanisms G θ) (π : Equiv.Perm (Fin n))
    (i : Fin n) :
    (∫ r, r ^ 2 ∂observationalRatioLaw (canonicalObservedWorld G θ π) i) =
      ∫ v, (θ.q (π i) (v (π i)) / θ.p (π i) v) ^ 2 ∂observationalLaw θ := by
  let W := canonicalObservedWorld G θ π
  rw [observationalRatioLaw,
    MeasureTheory.integral_map (measurable_observedLawRatio W.law i).aemeasurable
      (by fun_prop)]
  apply integral_congr_ae
  filter_upwards
    [canonicalObservedWorld_observedLawRatio_ae_eq_mechanismRatio hpos π i] with v hv
  rw [hv]

-- @node: canonical_interventionalRatioLaw_secondMoment_eq
/-- The second moment of a canonical interventional ratio law is the corresponding latent
interventional integral of the square of the explicit mechanism ratio.  Given [the stated inputs and conditions](hyp:hpos), [the stated conclusion](goal) follows. -/
lemma canonical_interventionalRatioLaw_secondMoment_eq
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (hpos : PositiveNormalizedSmoothMechanisms G θ) (π : Equiv.Perm (Fin n))
    (j i : Fin n) :
    (∫ r, r ^ 2 ∂interventionalRatioLaw (canonicalObservedWorld G θ π) j i) =
      ∫ v, (θ.q (π i) (v (π i)) / θ.p (π i) v) ^ 2
        ∂interventionalLaw θ (π j) := by
  let W := canonicalObservedWorld G θ π
  have hac : interventionalLaw θ (π j) ≪ observationalLaw θ := by
    simpa only [W, canonicalObservedWorld] using
      interventionalLaw_absolutelyContinuous_observational W hpos j
  rw [interventionalRatioLaw,
    MeasureTheory.integral_map (measurable_observedLawRatio W.law i).aemeasurable
      (by fun_prop)]
  apply integral_congr_ae
  filter_upwards
    [hac.ae_eq
      (canonicalObservedWorld_observedLawRatio_ae_eq_mechanismRatio hpos π i)] with v hv
  rw [hv]

-- @node: cancellationPrimitive_hasDerivAt
/-- The cancellation primitive has derivative equal to the intervention-density tilt.  [the stated conclusion](goal) follows. -/
lemma cancellationPrimitive_hasDerivAt (x : ℝ) :
    HasDerivAt cancellationPrimitive (exponentialInterventionDensity x - 1) x := by
  change HasDerivAt
    (fun y : ℝ => (Real.exp (4 * y) - 1) / (Real.exp 4 - 1) - y)
    (exponentialInterventionDensity x - 1) x
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (4 * y))
      (4 * Real.exp (4 * x)) x := by
    simpa [Function.comp_def, mul_comm] using
      (Real.hasDerivAt_exp (4 * x)).comp x (hasDerivAt_const_mul (x := x) 4)
  have hfrac : HasDerivAt
      (fun y : ℝ => (Real.exp (4 * y) - 1) / (Real.exp 4 - 1))
      (exponentialInterventionDensity x) x := by
    simpa [exponentialInterventionDensity] using
      (hexp.sub_const 1).div_const (Real.exp 4 - 1)
  exact hfrac.sub (hasDerivAt_id x)

-- @node: cancellation_tilt_integral_comp_zero
/-- Integrating the cancellation tilt against any continuous function of the
cancellation primitive gives zero.  Given [the stated inputs and conditions](hyp:hB), [the stated conclusion](goal) follows. -/
lemma cancellation_tilt_integral_comp_zero (B : ℝ → ℝ) (hB : Continuous B) :
    ∫ x in Set.Icc (0 : ℝ) 1,
        (exponentialInterventionDensity x - 1) * B (cancellationPrimitive x) = 0 := by
  let F : ℝ → ℝ := fun u => ∫ z in (0 : ℝ)..u, B z
  have hF (u : ℝ) : HasDerivAt F (B u) u := by
    exact intervalIntegral.integral_hasDerivAt_right
      (hB.intervalIntegrable 0 u) (hB.stronglyMeasurableAtFilter volume (nhds u))
        hB.continuousAt
  have hcomp (x : ℝ) : HasDerivAt (fun x => F (cancellationPrimitive x))
      ((exponentialInterventionDensity x - 1) * B (cancellationPrimitive x)) x := by
    change HasDerivAt (F ∘ cancellationPrimitive)
      ((exponentialInterventionDensity x - 1) * B (cancellationPrimitive x)) x
    simpa only [mul_comm] using
      (hF (cancellationPrimitive x)).comp x (cancellationPrimitive_hasDerivAt x)
  have hint : IntervalIntegrable
      (fun x => (exponentialInterventionDensity x - 1) * B (cancellationPrimitive x))
      volume 0 1 := by
    apply Continuous.intervalIntegrable
    apply Continuous.mul
    · unfold exponentialInterventionDensity
      fun_prop
    · apply hB.comp
      unfold cancellationPrimitive
      fun_prop
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (show (0 : ℝ) ≤ 1 by norm_num)
    (show ContinuousOn (fun x => F (cancellationPrimitive x)) (Set.Icc 0 1) by
      exact (continuous_iff_continuousAt.mpr fun x => (hcomp x).continuousAt).continuousOn)
    (fun x _ => hcomp x) hint
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  rw [hFTC]
  simp [cancellationPrimitive_zero]

-- @node: clampCancellationRange
/-- Clamp a real argument to the range of the cancellation primitive. -/
def clampCancellationRange (u : ℝ) : ℝ := max (-1) (min 0 u)

-- @node: clampCancellationRange_eq_self
/-- If [the argument already lies in the cancellation range](hyp:hu), then [clamping leaves it
unchanged](goal). -/
@[simp] lemma clampCancellationRange_eq_self {u : ℝ} (hu : u ∈ Set.Icc (-1 : ℝ) 0) :
    clampCancellationRange u = u := by
  simp [clampCancellationRange, hu.1, hu.2]

-- @node: cancellationTestIntegrand
/-- A globally continuous extension of the one-dimensional test integrand used
to identify the cancellation ratio law. -/
def cancellationTestIntegrand (ψ : ℝ → ℝ) (y u : ℝ) : ℝ :=
  let d := 1 + (1 / 10 : ℝ) * clampCancellationRange u * centeredCoordinate y
  d * ψ (exponentialInterventionDensity y / d)

-- @node: cancellationTestIntegrand_continuous
/-- The extended cancellation test integrand is continuous when the test
function is continuous and the child coordinate lies in the unit interval.  Given [the stated inputs and conditions](hyp:hψ,hy), [the stated conclusion](goal) follows. -/
lemma cancellationTestIntegrand_continuous (ψ : ℝ → ℝ) (hψ : Continuous ψ) {y : ℝ}
    (hy : y ∈ Set.Icc (0 : ℝ) 1) : Continuous (cancellationTestIntegrand ψ y) := by
  have hcy := abs_centeredCoordinate_le_one hy
  rw [abs_le] at hcy
  have hclamp (u : ℝ) : clampCancellationRange u ∈ Set.Icc (-1 : ℝ) 0 := by
    simp only [clampCancellationRange, Set.mem_Icc]
    constructor
    · exact le_max_left _ _
    · exact max_le (by norm_num) (min_le_left _ _)
  have hden (u : ℝ) :
      1 + (1 / 10 : ℝ) * clampCancellationRange u * centeredCoordinate y ≠ 0 := by
    have hu := hclamp u
    have hab : -1 ≤ clampCancellationRange u * centeredCoordinate y := by
      apply hu.1.trans
      simpa using mul_le_mul_of_nonpos_left hcy.2 hu.2
    nlinarith
  unfold cancellationTestIntegrand
  dsimp only
  apply Continuous.mul
  · unfold clampCancellationRange centeredCoordinate
    fun_prop
  · apply hψ.comp
    apply Continuous.div continuous_const
    · unfold clampCancellationRange centeredCoordinate
      fun_prop
    · exact hden

-- @node: cancellation_test_integrand_tilt_zero
/-- The parent intervention tilt integrates to zero against the exact test
integrand that appears after fixing the cancellation witness's child coordinate.  Given [the stated inputs and conditions](hyp:hψ,hy), [the stated conclusion](goal) follows. -/
lemma cancellation_test_integrand_tilt_zero (ψ : ℝ → ℝ) (hψ : Continuous ψ)
    {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    ∫ x in Set.Icc (0 : ℝ) 1,
      (exponentialInterventionDensity x - 1) *
        ((1 + (1 / 10 : ℝ) * cancellationPrimitive x * centeredCoordinate y) *
          ψ (exponentialInterventionDensity y /
            (1 + (1 / 10 : ℝ) * cancellationPrimitive x * centeredCoordinate y))) = 0 := by
  calc
    _ = ∫ x in Set.Icc (0 : ℝ) 1,
        (exponentialInterventionDensity x - 1) *
          cancellationTestIntegrand ψ y (cancellationPrimitive x) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      simp only [cancellationTestIntegrand]
      rw [show clampCancellationRange (cancellationPrimitive x) = cancellationPrimitive x by
        exact clampCancellationRange_eq_self (cancellationPrimitive_mem_negUnitInterval hx)]
    _ = 0 := cancellation_tilt_integral_comp_zero (cancellationTestIntegrand ψ y)
      (cancellationTestIntegrand_continuous ψ hψ hy)

-- @node: cancellation_iterated_test_integral_zero
/-- The complete two-coordinate cancellation integral vanishes for every
continuous test function.  Given [the stated inputs and conditions](hyp:hψ), [the stated conclusion](goal) follows. -/
lemma cancellation_iterated_test_integral_zero (ψ : ℝ → ℝ) (hψ : Continuous ψ) :
    ∫ y in Set.Icc (0 : ℝ) 1,
      ∫ x in Set.Icc (0 : ℝ) 1,
        (exponentialInterventionDensity x - 1) *
          ((1 + (1 / 10 : ℝ) * cancellationPrimitive x * centeredCoordinate y) *
            ψ (exponentialInterventionDensity y /
              (1 + (1 / 10 : ℝ) * cancellationPrimitive x * centeredCoordinate y))) = 0 := by
  calc
    _ = ∫ _y in Set.Icc (0 : ℝ) 1, (0 : ℝ) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
      exact cancellation_test_integrand_tilt_zero ψ hψ hy
    _ = 0 := by simp

-- @node: ratioLaws_eq_of_boundedContinuous_integrals_eq
/-- Two finite ratio laws coincide when every bounded continuous real test
function has the same integral under both laws.  Given [the stated inputs and conditions](hyp:h), [the stated conclusion](goal) follows. -/
lemma ratioLaws_eq_of_boundedContinuous_integrals_eq
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (j i : Fin n)
    [IsFiniteMeasure (W.law 0)] [IsFiniteMeasure (W.law j.succ)]
    (h : ∀ ψ : BoundedContinuousFunction ℝ ℝ,
      (∫ r, ψ r ∂observationalRatioLaw W i) =
        ∫ r, ψ r ∂interventionalRatioLaw W j i) :
    observationalRatioLaw W i = interventionalRatioLaw W j i := by
  letI : IsFiniteMeasure (observationalRatioLaw W i) := by
    unfold observationalRatioLaw
    exact Measure.isFiniteMeasure_map _ _
  letI : IsFiniteMeasure (interventionalRatioLaw W j i) := by
    unfold interventionalRatioLaw
    exact Measure.isFiniteMeasure_map _ _
  exact MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure h

-- @node: populationDiscrepancy_eq_zero_of_ratioLaws_eq
/-- Equality of the observational and interventional ratio laws forces their
kernel mean discrepancy to vanish.  Given [the stated inputs and conditions](hyp:h), [the stated conclusion](goal) follows. -/
lemma populationDiscrepancy_eq_zero_of_ratioLaws_eq
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (U : UnitNormFeatureMap H) (W : ObservedWorld G θ) (j i : Fin n)
    (h : observationalRatioLaw W i = interventionalRatioLaw W j i) :
    populationDiscrepancy U W j i = 0 := by
  simp only [populationDiscrepancy, h, sub_self, norm_zero]

end CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity
