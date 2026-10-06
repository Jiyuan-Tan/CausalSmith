module

public import Causalean.Stat.Bootstrap.SmoothZEstimator.Main
public import Causalean.Stat.LinearModel.OLSAsymptotics.AsymptoticNormality

/-!
# Efron-bootstrap validity for OLS contrasts

This module realizes the generic smooth Z-estimator constructor for the heteroskedastic OLS
score.  Existing OLS results discharge smooth regularity, data consistency, and the sample normal
equations; users supply only bootstrap consistency/root validity and contrast nondegeneracy.
-/

@[expose] public section

namespace Causalean.Stat

open Filter Matrix MeasureTheory ProbabilityTheory Topology
open scoped BigOperators ENNReal RealInnerProductSpace Topology

noncomputable section

variable {Omega X K : Type*} [MeasurableSpace Omega] [MeasurableSpace X]
  [Fintype K] [DecidableEq K]
  {mu : Measure Omega} {P : Measure X}

/-- Given [regressors and an outcome](hyp:x,y) and [a finite data sample of size `n`](hyp:n,data),
[the OLS sample-function estimator](goal) applies the closed-form OLS coefficient map to the
finite average of the raw moment vector. -/
def olsSampleEstimator (x : X → EuclideanSpace ℝ K) (y : X → ℝ)
    (n : ℕ) (data : Fin n → X) : EuclideanSpace ℝ K :=
  olsBetaFromMoments (finMean (fun i ↦ olsRawMoment x y (data i)))

/-- For [measurable regressors and outcome](hyp:hx,hy), [the OLS sample-function estimator is
measurable at every sample size](goal). -/
@[fun_prop]
theorem measurable_olsSampleEstimator
    {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hy : Measurable y) (n : ℕ) :
    Measurable (olsSampleEstimator x y n) := by
  letI : MeasurableSpace (Matrix K K ℝ) := MeasurableSpace.pi
  letI : BorelSpace (Matrix K K ℝ) := ⟨by
    change MeasurableSpace.pi = borel (K → K → ℝ)
    exact BorelSpace.measurable_eq⟩
  have hM : Measurable (fun data : Fin n → X =>
      finMean (fun i ↦ olsRawMoment x y (data i))) := by
    unfold finMean
    change Measurable (fun data : Fin n → X =>
      (n : ℝ)⁻¹ • ∑ i, olsRawMoment x y (data i))
    exact (Finset.measurable_sum _ fun i _ =>
      (measurable_olsRawMoment hx hy).comp (measurable_pi_apply i)).const_smul
        ((n : ℝ)⁻¹)
  have hQ : Measurable (fun data : Fin n → X =>
      olsQFromMoments (finMean
        (fun i ↦ olsRawMoment x y (data i)))) := by
    unfold olsQFromMoments
    exact measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j =>
      (measurable_pi_apply _).comp hM
  have hR : Measurable (fun data : Fin n → X =>
      olsRFromMoments (finMean
        (fun i ↦ olsRawMoment x y (data i)))) := by
    unfold olsRFromMoments
    exact measurable_pi_lambda _ fun i => (measurable_pi_apply _).comp hM
  have hInv : Measurable (fun data : Fin n → X =>
      (olsQFromMoments (finMean
        (fun i ↦ olsRawMoment x y (data i))))⁻¹) := by
    rw [show (fun data : Fin n → X =>
        (olsQFromMoments (finMean
          (fun i ↦ olsRawMoment x y (data i))))⁻¹) =
      (fun data : Fin n → X => Ring.inverse (Matrix.det (olsQFromMoments
          (finMean (fun i ↦ olsRawMoment x y (data i))))) •
        Matrix.adjugate (olsQFromMoments
          (finMean (fun i ↦ olsRawMoment x y (data i))))) by
        funext data
        exact Matrix.inv_def _]
    change Measurable ((fun data : Fin n → X => Ring.inverse (Matrix.det
        (olsQFromMoments (finMean
          (fun i ↦ olsRawMoment x y (data i)))))) •
      (fun data : Fin n → X => Matrix.adjugate (olsQFromMoments
        (finMean (fun i ↦ olsRawMoment x y (data i))))))
    simpa [Function.comp_def] using
      (measurable_inv.comp (continuous_id.matrix_det.measurable.comp hQ)).smul
        (continuous_id.matrix_adjugate.measurable.comp hQ)
  have hV : Measurable (fun data : Fin n → X =>
      (olsQFromMoments (finMean
        (fun i ↦ olsRawMoment x y (data i))))⁻¹ *ᵥ
      olsRFromMoments (finMean
        (fun i ↦ olsRawMoment x y (data i)))) := by
    unfold Matrix.mulVec dotProduct
    exact measurable_pi_lambda _ fun i => Finset.measurable_sum _ fun j _ =>
      ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hInv)).mul
        ((measurable_pi_apply j).comp hR)
  unfold olsSampleEstimator olsBetaFromMoments
  rw [show (fun data : Fin n → X =>
      (olsQFromMoments (finMean
        (fun i ↦ olsRawMoment x y (data i))))⁻¹.toEuclideanLin
        (WithLp.toLp 2 (olsRFromMoments (finMean
          (fun i ↦ olsRawMoment x y (data i)))))) =
    (fun data : Fin n → X => WithLp.toLp 2
      ((olsQFromMoments (finMean
        (fun i ↦ olsRawMoment x y (data i))))⁻¹ *ᵥ
      olsRFromMoments (finMean
        (fun i ↦ olsRawMoment x y (data i))))) by
      funext data
      rw [Matrix.toEuclideanLin_apply]]
  exact (PiLp.continuous_toLp (2 : ℝ≥0∞) (fun _ : K => ℝ)).measurable.comp hV

/-- For [an iid sample](hyp:S), [regressors and an outcome](hyp:x,y), [the sample-function OLS
estimator evaluated on the sample vector equals the library OLS estimator](goal). -/
theorem olsSampleEstimator_sampleVector
    (S : IIDSample Omega X mu P)
    (x : X → EuclideanSpace ℝ K) (y : X → ℝ)
    (n : ℕ) (omega : Omega) :
    olsSampleEstimator x y n (S.sampleVector n omega) =
      olsBetaHat S x y n omega := by
  unfold olsSampleEstimator olsBetaHat olsEmpiricalMoments IIDSample.sampleMeanVec
    IIDSample.sampleVector finMean
  exact congrArg (fun M : OLSMoment K =>
    olsBetaFromMoments ((n : ℝ)⁻¹ • M))
      (Fin.sum_univ_eq_sum_range
        (fun i => olsRawMoment x y (S.Z i omega)) n)

/-- Under [iid sampling, regressors and an outcome, their measurability, integrable OLS raw moments,
and a positive-definite population Gram matrix](hyp:S,x,y,hx,hy,hraw,hQ), [the OLS sample-function
estimator eventually solves its score equation exactly, with probability tending to one](goal). -/
theorem olsSampleEstimator_eventuallySolvesExactly
    [IsProbabilityMeasure mu]
    (S : IIDSample Omega X mu P)
    {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hy : Measurable y)
    (hraw : Integrable (olsRawMoment x y) P)
    (hQ : (olsQ P x y).PosDef) :
    EventuallySolvesEstimatingEquationExactly S (olsScore x y)
      (olsSampleEstimator x y) := by
  have hsing := olsQHat_singular_probability_tendsto_zero S hx hy hraw hQ
  unfold EventuallySolvesEstimatingEquationExactly
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsing
    (fun _ => zero_le) (fun n => measure_mono ?_)
  intro omega homega
  simp only [Set.mem_setOf_eq] at homega ⊢
  by_contra hdet
  apply homega
  rw [olsSampleEstimator_sampleVector]
  unfold zEstimatorSampleScore finMean IIDSample.sampleVector
  rw [show (∑ i : Fin n, olsScore x y (olsBetaHat S x y n omega)
      (S.Z i omega)) = ∑ t ∈ Finset.range n,
        olsScore x y (olsBetaHat S x y n omega) (S.Z t omega) from
      Fin.sum_univ_eq_sum_range
        (fun t => olsScore x y (olsBetaHat S x y n omega) (S.Z t omega)) n,
    ols_sampleMean_score,
    ols_normalEquation S n omega hdet]
  simp

/-- Under [iid sampling, regressors and an outcome, their measurability, integrable OLS raw moments,
and a positive-definite population Gram matrix](hyp:S,x,y,hx,hy,hraw,hQ), [the OLS sample-function
estimator has a negligible root-sample-size score residual in probability](goal). -/
theorem olsSampleEstimator_solvesInProbability
    [IsProbabilityMeasure mu]
    (S : IIDSample Omega X mu P)
    {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hy : Measurable y)
    (hraw : Integrable (olsRawMoment x y) P)
    (hQ : (olsQ P x y).PosDef) :
    SolvesEstimatingEquationInProbability S (olsScore x y)
      (olsSampleEstimator x y) :=
  solvesEstimatingEquationInProbability_of_eventuallyExactly S
    (olsScore x y) (olsSampleEstimator x y)
    (olsSampleEstimator_eventuallySolvesExactly S hx hy hraw hQ)

namespace BootstrapAsymLinear

/-- Under [iid sampling, regressors and an outcome, their measurability, integrability of all their
augmented monomials through degree four, and a positive-definite population Gram
matrix](hyp:S,x,y,hx,hy,hraw,hQ), for [a continuous linear contrast](hyp:c), if [the resampled OLS
coefficient is consistent and has a negligible root-sample-size score residual in bootstrap
probability, in outer sampling probability](hyp:hBootConsistent,hBootSolve), and [the contrast has
positive influence variance](hyp:hVar), [that OLS contrast is bootstrap asymptotically
linear](goal). -/
theorem olsContrast
    [IsProbabilityMeasure mu]
    (S : IIDSample Omega X mu P)
    {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hy : Measurable y)
    (hraw : Integrable (olsRawMoment x y) P)
    (hQ : (olsQ P x y).PosDef)
    (c : EuclideanSpace ℝ K →L[ℝ] ℝ)
    (hBootConsistent : BootstrapEstimatorConsistent S
      (olsSampleEstimator x y) (olsBeta P x y))
    (hBootSolve : BootstrapSolvesEstimatingEquationInProbability S
      (olsScore x y) (olsSampleEstimator x y))
    (hVar : 0 < ∫ z, (c (olsInfluence P x y z)) ^ 2 ∂P) :
    BootstrapAsymLinear S
      (fun n data ↦ c (olsSampleEstimator x y n data))
      (c (olsBeta P x y))
      (fun z ↦ c (olsInfluence P x y z)) := by
  let _ : IsProbabilityMeasure P := by
    rw [← S.law]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  let reg := olsSmoothZRegularity hx hy hraw hQ
  have hreg : reg.influence = olsInfluence P x y := by
    dsimp [reg]
    exact olsSmoothZRegularity_influence_eq hx hy hraw hQ
  have hConsistent : ∀ epsilon > 0,
      Tendsto
        (fun n ↦ mu {omega |
          epsilon < ‖olsSampleEstimator x y n (S.sampleVector n omega) -
            olsBeta P x y‖})
        atTop (nhds 0) := by
    intro epsilon hepsilon
    simpa only [olsSampleEstimator_sampleVector] using
      olsBetaHat_consistent S hx hy hraw hQ epsilon hepsilon
  have hVar' : 0 < ∫ z,
      (c (reg.jacobianInv (olsScore x y (olsBeta P x y) z))) ^ 2 ∂P := by
    rw [← hreg] at hVar
    simpa [SmoothZEstimatorRegularity.influence] using hVar
  have hresult := zEstimator
    (olsScore x y) (olsBeta P x y) P reg S (olsSampleEstimator x y)
    (measurable_olsSampleEstimator hx hy) c hConsistent
    (olsSampleEstimator_solvesInProbability S hx hy hraw hQ)
    hBootConsistent hBootSolve hVar'
  have hinfluence :
      (fun z ↦ -c (reg.jacobianInv (olsScore x y (olsBeta P x y) z))) =
        (fun z ↦ c (olsInfluence P x y z)) := by
    funext z
    rw [← hreg]
    simp [SmoothZEstimatorRegularity.influence]
  rw [hinfluence] at hresult
  exact hresult

end BootstrapAsymLinear

end

end Causalean.Stat
