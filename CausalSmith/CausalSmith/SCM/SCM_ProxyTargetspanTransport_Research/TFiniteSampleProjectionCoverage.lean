import CausalSmith.SCM.SCM_ProxyTargetspanTransport_Research.TTargetSpanIff
import CausalSmith.SCM.SCM_ProxyTargetspanTransport_Research.Helpers.FiniteSampleCoverage

/-! Finite-sample uniform coverage of the concentration projection set under finite block laws. -/

open MeasureTheory

namespace CausalSmith.SCM.ProxyTargetspanTransport

variable {E U W X Y : Type*}
  [Fintype E] [Fintype U] [Fintype W] [Fintype X] [Fintype Y]
  [DecidableEq E] [DecidableEq U] [DecidableEq W] [DecidableEq X] [DecidableEq Y]
  [MeasurableSpace E] [MeasurableSpace W] [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSingletonClass E] [MeasurableSingletonClass W]
  [MeasurableSingletonClass X] [MeasurableSingletonClass Y]

-- @node: thm:finite-sample-projection-coverage
/-- Given [the positive latent-shift condition, compatibility with the observed and target laws, existence of balancing weights, positivity of the source sample size, positivity of the target sample size](hyp:hcls,hMdl,hspan,hns,hnt), [the concentration projection set covers the model's causal probability with probability at least one minus the nominal level](goal). -/
theorem finite_sample_projection_coverage
    (Mdl : LatentShiftSCM E U W X Y) (PO : E → W → X → Y → ℝ) (bvec : W → ℝ)
    (hcls : PositiveLatentShiftClass Mdl) (hMdl : Mdl ∈ compatibleFiber PO bvec)
    (x : X) (y : Y) (hspan : (balancingFiber (condProxyMatrix Mdl x) bvec).Nonempty)
    (ns nt : ℕ) (hns : 0 < ns) (hnt : 0 < nt)
    (alpha : Set.Ioo (0 : ℝ) 1) :
    1 - (alpha : ℝ) ≤ (twoSampleLaw Mdl ns nt).real {s |
      interventionalProb Mdl x y ∈
        concentrationProjectionSet (finEmpProxyMoment ns x s)
          (finEmpOutcomeMoment ns x y s) (finEmpTargetProxy nt s) ns nt alpha} := by
  have hconc := simultaneous_coordinate_concentration Mdl x y ns nt hns hnt
    (twoSampleLaw Mdl ns nt) (twoSampleLaw_sourceBlock Mdl ns nt)
      (twoSampleLaw_targetBlock Mdl ns nt) alpha
  obtain ⟨lam, hlam⟩ := hspan
  have hlam' : lam ∈ balancingFiber (condProxyMatrix Mdl x) (targetProxyVector Mdl) := by
    rw [hMdl.2.2]
    exact hlam
  exact hconc.trans (measureReal_mono fun s hs =>
    mem_concentrationProjectionSet_of_good Mdl hcls x y lam hlam' ns nt alpha s hs)

/-- Given [the positive latent-shift condition, compatibility with the observed and target laws, existence of balancing weights, positivity of the source sample size, positivity of the target sample size](hyp:hcls,hMdl,hspan,hns,hnt), [the canonical two-sample product law gives the finite-sample concentration projection set coverage of at least one minus the nominal level](goal). -/
theorem finite_sample_projection_coverage_twoSampleLaw
    (Mdl : LatentShiftSCM E U W X Y) (PO : E → W → X → Y → ℝ) (bvec : W → ℝ)
    (hcls : PositiveLatentShiftClass Mdl) (hMdl : Mdl ∈ compatibleFiber PO bvec)
    (x : X) (y : Y) (hspan : (balancingFiber (condProxyMatrix Mdl x) bvec).Nonempty)
    (ns nt : ℕ) (hns : 0 < ns) (hnt : 0 < nt)
    (alpha : Set.Ioo (0 : ℝ) 1) :
    1 - (alpha : ℝ) ≤ (twoSampleLaw Mdl ns nt).real {s |
      interventionalProb Mdl x y ∈
        concentrationProjectionSet (finEmpProxyMoment ns x s)
          (finEmpOutcomeMoment ns x y s) (finEmpTargetProxy nt s) ns nt alpha} := by
  exact finite_sample_projection_coverage Mdl PO bvec hcls hMdl x y hspan
    ns nt hns hnt alpha

end CausalSmith.SCM.ProxyTargetspanTransport
