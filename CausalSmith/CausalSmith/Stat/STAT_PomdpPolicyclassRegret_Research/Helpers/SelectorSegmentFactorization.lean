module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.BlockSegmentMoments

/-!
# One-step factorization of structural selector segments

These identities expose the action and reward-transition factors hidden in
`segmentStepLaw`.  They are the local inputs for a prefix induction on
`segmentFrom`.
-/

@[expose] public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open MeasureTheory ProbabilityTheory
open CausalSmith.Stat.PomdpLatentOverlapMinimax
open scoped ENNReal

/-- The behavior action law at a fixed full state. -/
-- @node: selectorBehaviorActionMeasure
@[no_expose]
noncomputable def selectorBehaviorActionMeasure {T M : Nat}
    (m : ModelIndex T M) (s : JointState m.nX m.nH) : Measure Bool :=
  ∑ a : Bool, ENNReal.ofReal (m.Mx.b s.1 a) • Measure.dirac a

/-- Evaluation of the raw behavior kernel is the structural action measure. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the model](hyp:m), and
[the state](hyp:s), this establishes
[the behaviour kernel apply equality selector behavior action measure result](goal). -/
-- @node: behaviourKernel_apply_eq_selectorBehaviorActionMeasure
lemma behaviourKernel_apply_eq_selectorBehaviorActionMeasure {T M : Nat}
    (m : ModelIndex T M) (s : JointState m.nX m.nH) :
    behaviourKernel m.Mx.toRawB s.1 = selectorBehaviorActionMeasure m s := by
  rfl

/-- The structural one-step law has the expected behavior-action marginal. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the model](hyp:m), and
[the state](hyp:s), this establishes [the segment step law map action result](goal). -/
-- @node: segmentStepLaw_map_action
lemma segmentStepLaw_map_action {T M : Nat} (m : ModelIndex T M)
    (s : JointState m.nX m.nH) :
    (segmentStepLaw m s).map Prod.fst = selectorBehaviorActionMeasure m s := by
  unfold segmentStepLaw selectorBehaviorActionMeasure
  rw [← Measure.sum_fintype,
    Measure.map_sum measurable_fst.aemeasurable, Measure.sum_fintype]
  apply Finset.sum_congr rfl
  intro a _
  rw [Measure.map_smul, Measure.map_map measurable_fst (by fun_prop)]
  change ENNReal.ofReal (m.Mx.b s.1 a) •
      (m.Mx.K s a).map (fun _ ↦ a) = _
  rw [Measure.map_const]
  have : IsProbabilityMeasure (m.Mx.K s a) := m.kernel_law.1 s a
  simp

/-- Given its action coordinate, the structural one-step law uses exactly the model
reward-transition kernel. For [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the model](hyp:m), and [the state](hyp:s), this establishes
[the segment step law comp prod result](goal). -/
-- @node: segmentStepLaw_compProd
lemma segmentStepLaw_compProd {T M : Nat} (m : ModelIndex T M)
    (s : JointState m.nX m.nH) :
    segmentStepLaw m s =
      (selectorBehaviorActionMeasure m s).compProd
        (Kernel.comap (kernelOfK m.Mx.toRawB) (fun a ↦ (s, a))
          (by fun_prop)) := by
  letI : IsMarkovKernel (kernelOfK m.Mx.toRawB) :=
    ⟨fun sa ↦ m.kernel_law.1 sa.1 sa.2⟩
  ext B hB
  rw [Measure.compProd_apply hB]
  unfold segmentStepLaw selectorBehaviorActionMeasure
  rw [Measure.finsetSum_apply, lintegral_finsetSum_measure]
  apply Finset.sum_congr rfl
  intro a _
  rw [lintegral_smul_measure, lintegral_dirac]
  simp only [smul_eq_mul, Kernel.comap_apply, kernelOfK]
  rw [Measure.smul_apply]
  rw [Measure.map_apply (by fun_prop) hB]
  rfl

/-- The zeroth state of an arbitrary-start structural segment has exactly the supplied initial
vector. For [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the sample size](hyp:n), [the model](hyp:m), [the finite assumption](hyp:hFinite),
[the behavior policy assumption](hyp:hb), [the initial distribution](hyp:nu), and
[the s0](hyp:s0), this establishes [the segment law map initial state result](goal). -/
-- @node: segmentLaw_map_initialState
lemma segmentLaw_map_initialState {T M n : Nat} (m : ModelIndex T M)
    (hFinite : FiniteState m) (hb : PolicyVector m.Mx.b)
    (nu : JointState m.nX m.nH → ℝ) (s0 : JointState m.nX m.nH) :
    ((segmentLaw m hFinite nu n).map (stateAt 0)) {s0} =
      ENNReal.ofReal (nu s0) := by
  let fallback : JointState m.nX m.nH :=
    (⟨0, hFinite.1⟩, ⟨0, hFinite.2⟩)
  let F : JointState m.nX m.nH →
      Measure (JointState m.nX m.nH ×
        List (Bool × ℝ × JointState m.nX m.nH)) :=
    fun s ↦ (segmentFrom m n s).map (fun path ↦ (s, path))
  have hmstate : Measurable (@stateAt n m.nX m.nH 0) := by
    unfold stateAt
    fun_prop
  have hmdecode : Measurable (decodeSegment (n := n) fallback) :=
    decodeSegment_measurable fallback
  have hF : Measurable F := measurable_of_countable F
  rw [Measure.map_apply hmstate (measurableSet_singleton s0)]
  change (((initialStateLaw m nu).bind F).map (decodeSegment fallback))
      ((@stateAt n m.nX m.nH 0) ⁻¹' {s0}) = _
  rw [Measure.map_apply hmdecode (hmstate (measurableSet_singleton s0))]
  rw [Measure.bind_apply (hmdecode (hmstate (measurableSet_singleton s0)))
    hF.aemeasurable]
  have hrow (s : JointState m.nX m.nH) :
      F s ((decodeSegment fallback) ⁻¹'
        ((@stateAt n m.nX m.nH 0) ⁻¹' {s0})) =
          if s = s0 then 1 else 0 := by
    rw [Measure.map_apply (measurable_prodMk_left (x := s))
      (hmdecode (hmstate (measurableSet_singleton s0)))]
    by_cases hs : s = s0
    · subst s
      letI : IsProbabilityMeasure (segmentFrom m n s0) :=
        segmentFrom_isProbability m hb n s0
      have hall : (fun path : List (Bool × ℝ × JointState m.nX m.nH) ↦
          (s0, path)) ⁻¹' ((decodeSegment fallback) ⁻¹'
            ((@stateAt n m.nX m.nH 0) ⁻¹' {s0})) = Set.univ := by
        ext path
        simp [fallback, decodeSegment, stateAt]
      rw [hall]
      simp only
      exact (measure_univ : (segmentFrom m n s0) Set.univ = 1)
    · have hempty : (fun path : List (Bool × ℝ × JointState m.nX m.nH) ↦
          (s, path)) ⁻¹' ((decodeSegment fallback) ⁻¹'
            ((@stateAt n m.nX m.nH 0) ⁻¹' {s0})) = ∅ := by
        ext path
        simp [fallback, decodeSegment, stateAt, hs]
      rw [hempty]
      simp [hs]
  simp_rw [hrow]
  unfold initialStateLaw
  rw [lintegral_finsetSum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac]
  rw [Finset.sum_eq_single s0]
  · simp
  · intro s _ hne
    simp [hne]
  · simp

end CausalSmith.Stat.PomdpPolicyclassRegret
