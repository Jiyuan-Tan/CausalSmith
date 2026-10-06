module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.ProjectionCrossMoments

/-! # Projection control

The cosine approximation, mean and bias identities, and sharp variance bound
follow from projection orthogonality and the exact finite-sample Hoeffding
decomposition. Both variance components have zero cross moment. -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

-- @node: lem:projection-control
/-- Jackson approximation and all three moment identities for the original ordered-pair statistic. Under the stated assumptions. Under the stated assumptions. [The stated hypotheses](hyp:hDesign) hold, and [the stated conclusion follows](goal). -/
lemma projection_control (P : ObservedLaw) (hDesign : UniformDesign P) :
  (∀ (γ : ℝ) (f : Covariate → ℝ), HolderExponentDomain γ → ContinuousFunctionDomain f → -- @realizes \gamma(generic exponent in its domain) @realizes f(generic continuous function)
    ∀ k : ℕ, 1 ≤ k →
      uniformL2Norm (fun x => f x-cosineProjection k f x) ≤
        5*holderSeminorm γ f*ENNReal.ofReal ((k : ℝ)^(-γ))) ∧
  (∀ (W V : BoundedMark) (k n : ℕ), 1 ≤ k → 2 ≤ n →
    let w := conditionalMarkMean P W
    let v := conditionalMarkMean P V
    let μ := Causalean.Stat.UStatistic.LocalizedVariance.iidLaw P.measure n
    let m := ∫ o, projectionStatistic n k W.value V.value o ∂μ
    m = uniformInner (cosineProjection k w) (cosineProjection k v) ∧
    uniformInner w v-m = uniformInner (fun x => w x-cosineProjection k w x)
      (fun x => v x-cosineProjection k v x) ∧
    (∫ o, (projectionStatistic n k W.value V.value o-m)^2 ∂μ) ≤
      4/(n : ℝ)+2*k/((n : ℝ)*((n : ℝ)-1))) := by
  constructor
  · exact cosineProjection_error_le_holderSeminorm
  · intro W V k n hk hn
    dsimp only
    refine ⟨projectionStatistic_integral P hDesign W V k n hn,
      projectionStatistic_bias P hDesign W V k n hn, ?_⟩
    exact projectionStatistic_variance_le P hDesign W V k n hn
end CausalSmith.Stat.LogoddsLowsmoothFrontier
