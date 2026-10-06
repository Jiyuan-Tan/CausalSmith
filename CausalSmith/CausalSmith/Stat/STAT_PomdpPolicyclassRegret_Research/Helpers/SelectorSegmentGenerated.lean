module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SelectorSegmentFactorization
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SelectorSegmentPrefix
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SelectorSegmentAction
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SelectorSegmentKernelTransport
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SelectorTrajectoryLaw

/-!
# Certification interface for the structural stationary segment

Probability and initialization are discharged here.  The remaining inputs are
exactly the action and reward-transition history factorizations.
-/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open MeasureTheory ProbabilityTheory
open CausalSmith.Stat.PomdpLatentOverlapMinimax

/-- The two history factorizations complete the generated-law certificate for the stationary
structural segment. For [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the model](hyp:m), [the class assumption](hyp:hClass),
[the action assumption](hyp:haction), and [the kernel assumption](hyp:hkernel), this establishes
[the selector stationary segment generated of factorizations result](goal). -/
-- @node: selector_stationarySegment_generated_of_factorizations
lemma selector_stationarySegment_generated_of_factorizations {T M : Nat}
    (t0 zeta C : ℝ) (m : ModelIndex T M)
    (hClass : PolicyListClass t0 zeta C m)
    (haction : ∀ t : Fin T,
      (segmentLaw m hClass.finite_state
        (stationaryLaw (policyKernel m.Mx.toRawB m.Mx.b)) T).map
          (histActionPair t) =
      ((segmentLaw m hClass.finite_state
        (stationaryLaw (policyKernel m.Mx.toRawB m.Mx.b)) T).map
          (histStateView t)).compProd
        (Kernel.comap (behaviourKernel m.Mx.toRawB) (currentObsState t)
          (measurable_currentObsState t)))
    (hkernel : ∀ t : Fin T,
      (segmentLaw m hClass.finite_state
        (stationaryLaw (policyKernel m.Mx.toRawB m.Mx.b)) T).map
          (histNextPair t) =
      ((segmentLaw m hClass.finite_state
        (stationaryLaw (policyKernel m.Mx.toRawB m.Mx.b)) T).map
          (histView t)).compProd
        (Kernel.comap (kernelOfK m.Mx.toRawB) (currentStateAction t)
          (measurable_currentStateAction t))) :
    RawGeneratedPathLaw m.Mx.toRawB
      (segmentLaw m hClass.finite_state
        (stationaryLaw (policyKernel m.Mx.toRawB m.Mx.b)) T) := by
  have hstat := hClass.stationary_start.1
  apply rawGeneratedPathLaw_mk m.Mx.toRawB
    (segmentLaw m hClass.finite_state
      (stationaryLaw (policyKernel m.Mx.toRawB m.Mx.b)) T)
    (segmentLaw_isProbability m hClass.sequential_ignorability.1
      hClass.finite_state _ hstat.1 T)
  · intro s
    exact segmentLaw_map_initialState m hClass.finite_state
      hClass.sequential_ignorability.1 _ s
  · exact haction
  · exact hkernel

/-- Once the two structural history identities are available, the actual law equals the
stationary structural segment with no conditional-law choice. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the action assumption](hyp:haction), and
[the kernel assumption](hyp:hkernel), this establishes
[the selector actual law equality stationary segment of factorizations result](goal). -/
-- @node: selector_actual_law_eq_stationary_segment_of_factorizations
lemma selector_actual_law_eq_stationary_segment_of_factorizations {T M : Nat}
    (t0 zeta C : ℝ) (m : ModelIndex T M)
    (hClass : PolicyListClass t0 zeta C m)
    (haction : ∀ t : Fin T,
      (segmentLaw m hClass.finite_state
        (stationaryLaw (policyKernel m.Mx.toRawB m.Mx.b)) T).map
          (histActionPair t) =
      ((segmentLaw m hClass.finite_state
        (stationaryLaw (policyKernel m.Mx.toRawB m.Mx.b)) T).map
          (histStateView t)).compProd
        (Kernel.comap (behaviourKernel m.Mx.toRawB) (currentObsState t)
          (measurable_currentObsState t)))
    (hkernel : ∀ t : Fin T,
      (segmentLaw m hClass.finite_state
        (stationaryLaw (policyKernel m.Mx.toRawB m.Mx.b)) T).map
          (histNextPair t) =
      ((segmentLaw m hClass.finite_state
        (stationaryLaw (policyKernel m.Mx.toRawB m.Mx.b)) T).map
          (histView t)).compProd
        (Kernel.comap (kernelOfK m.Mx.toRawB) (currentStateAction t)
          (measurable_currentStateAction t))) :
    m.Mx.law = segmentLaw m hClass.finite_state
      (stationaryLaw (policyKernel m.Mx.toRawB m.Mx.b)) T := by
  apply selector_actual_law_eq_stationary_segment_of_generated t0 zeta C m hClass
  exact selector_stationarySegment_generated_of_factorizations t0 zeta C m hClass
    haction hkernel

/-- Terminal-epoch factorizations at every prefix horizon suffice for the full generated-law
certificate. Prefix transport supplies every epoch of the original horizon. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the action last assumption](hyp:hactionLast), and
[the kernel last assumption](hyp:hkernelLast), this establishes
[the selector stationary segment generated of terminal factorizations result](goal). -/
-- @node: selector_stationarySegment_generated_of_terminal_factorizations
lemma selector_stationarySegment_generated_of_terminal_factorizations
    {T M : Nat} (t0 zeta C : ℝ) (m : ModelIndex T M)
    (hClass : PolicyListClass t0 zeta C m)
    (hactionLast : ∀ n : Nat,
      (segmentLaw m hClass.finite_state
        (stationaryLaw (policyKernel m.Mx.toRawB m.Mx.b)) (n + 1)).map
          (histActionPair (Fin.last n)) =
      ((segmentLaw m hClass.finite_state
        (stationaryLaw (policyKernel m.Mx.toRawB m.Mx.b)) (n + 1)).map
          (histStateView (Fin.last n))).compProd
        (Kernel.comap (behaviourKernel m.Mx.toRawB)
          (currentObsState (Fin.last n))
          (measurable_currentObsState (Fin.last n))))
    (hkernelLast : ∀ n : Nat,
      (segmentLaw m hClass.finite_state
        (stationaryLaw (policyKernel m.Mx.toRawB m.Mx.b)) (n + 1)).map
          (histNextPair (Fin.last n)) =
      ((segmentLaw m hClass.finite_state
        (stationaryLaw (policyKernel m.Mx.toRawB m.Mx.b)) (n + 1)).map
          (histView (Fin.last n))).compProd
        (Kernel.comap (kernelOfK m.Mx.toRawB)
          (currentStateAction (Fin.last n))
          (measurable_currentStateAction (Fin.last n)))) :
    RawGeneratedPathLaw m.Mx.toRawB
      (segmentLaw m hClass.finite_state
        (stationaryLaw (policyKernel m.Mx.toRawB m.Mx.b)) T) := by
  apply selector_stationarySegment_generated_of_factorizations t0 zeta C m hClass
  · intro t
    rw [segmentLaw_map_histActionPair_eq_prefix m hClass.finite_state
      hClass.sequential_ignorability.1 _ t,
      segmentLaw_map_histStateView_eq_prefix m hClass.finite_state
        hClass.sequential_ignorability.1 _ t]
    exact hactionLast t.val
  · intro t
    rw [segmentLaw_map_histNextPair_eq_prefix m hClass.finite_state
      hClass.sequential_ignorability.1 _ t,
      segmentLaw_map_histActionPair_eq_prefix m hClass.finite_state
        hClass.sequential_ignorability.1 _ t]
    exact hkernelLast t.val

/-- Terminal structural identities at all finite prefix horizons identify the actual model law
with the stationary structural segment. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the action last assumption](hyp:hactionLast), and
[the kernel last assumption](hyp:hkernelLast), this establishes
[the selector actual law equality stationary segment of terminal factorizations result](goal). -/
-- @node: selector_actual_law_eq_stationary_segment_of_terminal_factorizations
lemma selector_actual_law_eq_stationary_segment_of_terminal_factorizations
    {T M : Nat} (t0 zeta C : ℝ) (m : ModelIndex T M)
    (hClass : PolicyListClass t0 zeta C m)
    (hactionLast : ∀ n : Nat,
      (segmentLaw m hClass.finite_state
        (stationaryLaw (policyKernel m.Mx.toRawB m.Mx.b)) (n + 1)).map
          (histActionPair (Fin.last n)) =
      ((segmentLaw m hClass.finite_state
        (stationaryLaw (policyKernel m.Mx.toRawB m.Mx.b)) (n + 1)).map
          (histStateView (Fin.last n))).compProd
        (Kernel.comap (behaviourKernel m.Mx.toRawB)
          (currentObsState (Fin.last n))
          (measurable_currentObsState (Fin.last n))))
    (hkernelLast : ∀ n : Nat,
      (segmentLaw m hClass.finite_state
        (stationaryLaw (policyKernel m.Mx.toRawB m.Mx.b)) (n + 1)).map
          (histNextPair (Fin.last n)) =
      ((segmentLaw m hClass.finite_state
        (stationaryLaw (policyKernel m.Mx.toRawB m.Mx.b)) (n + 1)).map
          (histView (Fin.last n))).compProd
        (Kernel.comap (kernelOfK m.Mx.toRawB)
          (currentStateAction (Fin.last n))
          (measurable_currentStateAction (Fin.last n)))) :
    m.Mx.law = segmentLaw m hClass.finite_state
      (stationaryLaw (policyKernel m.Mx.toRawB m.Mx.b)) T := by
  apply selector_actual_law_eq_stationary_segment_of_generated t0 zeta C m hClass
  exact selector_stationarySegment_generated_of_terminal_factorizations
    t0 zeta C m hClass hactionLast hkernelLast

/-- The stationary structural segment is unconditionally certified as the generated raw POMDP
path law. For [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the model](hyp:m), and [the class assumption](hyp:hClass),
this establishes [the selector stationary segment raw generated path law result](goal). -/
-- @node: selector_stationarySegment_rawGeneratedPathLaw
lemma selector_stationarySegment_rawGeneratedPathLaw {T M : Nat}
    (t0 zeta C : ℝ) (m : ModelIndex T M)
    (hClass : PolicyListClass t0 zeta C m) :
    RawGeneratedPathLaw m.Mx.toRawB
      (segmentLaw m hClass.finite_state
        (stationaryLaw (policyKernel m.Mx.toRawB m.Mx.b)) T) := by
  apply selector_stationarySegment_generated_of_terminal_factorizations
    t0 zeta C m hClass
  · intro n
    exact segmentLaw_terminal_action_factorization m hClass.finite_state
      hClass.sequential_ignorability.1 _ n
  · intro n
    exact segmentLaw_terminal_kernel_factorization m hClass.finite_state
      hClass.sequential_ignorability.1 _ n

/-- The model's actual full trajectory law equals its stationary structural segment law at the
same horizon. For [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the model](hyp:m), and [the class assumption](hyp:hClass),
this establishes [the selector actual law equality stationary segment result](goal). -/
-- @node: selector_actual_law_eq_stationary_segment
lemma selector_actual_law_eq_stationary_segment {T M : Nat}
    (t0 zeta C : ℝ) (m : ModelIndex T M)
    (hClass : PolicyListClass t0 zeta C m) :
    m.Mx.law = segmentLaw m hClass.finite_state
      (stationaryLaw (policyKernel m.Mx.toRawB m.Mx.b)) T := by
  apply selector_actual_law_eq_stationary_segment_of_generated t0 zeta C m hClass
  exact selector_stationarySegment_rawGeneratedPathLaw t0 zeta C m hClass

end CausalSmith.Stat.PomdpPolicyclassRegret
