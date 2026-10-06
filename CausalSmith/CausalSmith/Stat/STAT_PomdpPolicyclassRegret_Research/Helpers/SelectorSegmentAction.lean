module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SelectorSegmentEndpoint
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SelectorSegmentFactorization
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.BlockPathSupport
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.PhiwHistory

/-!
# Terminal action factorization for structural selector segments

The endpoint extension identity implies that the terminal behavior action is
conditionally distributed according to the behavior kernel given the decoded
past and current state.
-/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open MeasureTheory ProbabilityTheory
open CausalSmith.Stat.PomdpLatentOverlapMinimax

private lemma map_bind_eq_bind_map {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure A) (κ : A → Measure B) (f : B → C)
    (hκ : AEMeasurable κ μ) (hf : Measurable f) :
    (μ.bind κ).map f = μ.bind (fun a ↦ (κ a).map f) := by
  have hdirac : Measurable (fun b ↦ Measure.dirac (f b)) := by fun_prop
  rw [← Measure.bind_dirac_eq_map _ hf, Measure.bind_bind hκ hdirac.aemeasurable]
  apply Measure.bind_congr_right
  filter_upwards [] with a
  exact Measure.bind_dirac_eq_map (κ a) hf

private lemma action_bind_compProd_const_right {X H Y : Type*}
    [MeasurableSpace X] [MeasurableSpace H] [MeasurableSpace Y]
    (ρ : Measure X) (ν : X → Measure H) (hν : Measurable ν)
    (hρ : IsProbabilityMeasure ρ) (hνp : ∀ x, IsProbabilityMeasure (ν x))
    (K : Kernel H Y) [IsSFiniteKernel K] :
    ρ.bind (fun x ↦ (ν x).compProd K) = (ρ.bind ν).compProd K := by
  let κ : Kernel X H := ⟨ν, hν⟩
  letI : IsMarkovKernel κ := ⟨hνp⟩
  letI : IsProbabilityMeasure ρ := hρ
  letI : IsProbabilityMeasure (ρ.bind ν) := by
    change IsProbabilityMeasure (κ ∘ₘ ρ)
    infer_instance
  have hfam : Measurable (fun x ↦ (ν x).compProd K) := by
    apply Measure.measurable_of_measurable_coe
    intro B hB
    let η := κ ⊗ₖ K.comap Prod.snd measurable_snd
    have hm := η.measurable_coe hB
    convert hm using 1
    funext x
    rw [Kernel.compProd_apply hB, Measure.compProd_apply hB]
    rfl
  ext B hB
  rw [Measure.bind_apply hB hfam.aemeasurable]
  rw [Measure.compProd_apply hB]
  rw [Measure.lintegral_bind]
  · apply lintegral_congr
    intro x
    rw [Measure.compProd_apply hB]
  · exact hν.aemeasurable
  · exact (Kernel.measurable_kernel_prodMk_left hB).aemeasurable

/-- At the terminal epoch of a fixed-start structural path, the action has the behavior-kernel
conditional law given the complete decoded state history. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the model](hyp:m),
[the behavior policy assumption](hyp:hb), [the sample size](hyp:n),
[the fallback state](hyp:fallback), and [the state](hyp:s), this establishes
[the segment from terminal action factorization result](goal). -/
-- @node: segmentFrom_terminal_action_factorization
lemma segmentFrom_terminal_action_factorization {T M : Nat}
    (m : ModelIndex T M) (hb : PolicyVector m.Mx.b) (n : Nat)
    (fallback : Bool × ℝ × JointState m.nX m.nH)
    (s : JointState m.nX m.nH) :
    (segmentFrom m (n + 1) s).map (fun ys ↦
      histActionPair (Fin.last n)
        (decodeSegment fallback.2.2 (s, ys))) =
      ((segmentFrom m (n + 1) s).map (fun ys ↦
        histStateView (Fin.last n)
          (decodeSegment fallback.2.2 (s, ys)))).compProd
        (Kernel.comap (behaviourKernel m.Mx.toRawB)
          (currentObsState (Fin.last n))
          (measurable_currentObsState (Fin.last n))) := by
  letI : IsMarkovKernel (behaviourKernel m.Mx.toRawB) := by
    constructor
    intro x
    constructor
    change (∑ a : Bool, ENNReal.ofReal (m.Mx.b x a) • Measure.dirac a)
      Set.univ = 1
    simp
    rw [← ENNReal.ofReal_add ((hb x).1 true) ((hb x).1 false)]
    rw [show m.Mx.b x true + m.Mx.b x false = 1 by simpa using (hb x).2]
    norm_num
  let H := fun xs : List (Bool × ℝ × JointState m.nX m.nH) ↦
    histStateView (Fin.last n) (decodeSegment fallback.2.2 (s, xs))
  have hH : Measurable H := by
    unfold H
    exact (measurable_histStateView (Fin.last n)).comp
      ((decodeSegment_measurable fallback.2.2).comp
        (measurable_const.prodMk measurable_id))
  let K : Kernel (StateHistoryView (n + 1) m.nX m.nH (Fin.last n)) Bool :=
    Kernel.comap (behaviourKernel m.Mx.toRawB)
    (currentObsState (Fin.last n))
    (measurable_currentObsState (Fin.last n))
  let μ := segmentFrom m n s
  have hμp : IsProbabilityMeasure μ := segmentFrom_isProbability m hb n s
  have hstateMap : Measurable (fun ys ↦
      histStateView (Fin.last n)
        (decodeSegment fallback.2.2 (s, ys))) := by
    exact (measurable_histStateView (Fin.last n)).comp
      ((decodeSegment_measurable fallback.2.2).comp
        (measurable_const.prodMk measurable_id))
  have hactionMap : Measurable (fun ys ↦
      histActionPair (Fin.last n)
        (decodeSegment fallback.2.2 (s, ys))) := by
    exact (measurable_histActionPair (Fin.last n)).comp
      ((decodeSegment_measurable fallback.2.2).comp
        (measurable_const.prodMk measurable_id))
  have hstate :
      (segmentFrom m (n + 1) s).map (fun ys ↦
          histStateView (Fin.last n)
            (decodeSegment fallback.2.2 (s, ys))) = μ.map H := by
    rw [segmentFrom_endpoint_extension m hb n fallback s]
    rw [map_bind_eq_bind_map _ _ _
      (segmentEndpoint_family_measurable m hb n fallback s).aemeasurable
      hstateMap]
    rw [← Measure.bind_dirac_eq_map _ hH]
    apply Measure.bind_congr_right
    filter_upwards [(segmentFrom_ae_path_support m hb fallback.2.2 n s)] with xs hxs
    have hsnoc : Measurable
        (fun step ↦ segmentSnocFixed n fallback xs step) :=
      (segmentSnocFixed_measurable n fallback).comp
        (measurable_const.prodMk measurable_id)
    rw [Measure.map_map hstateMap hsnoc]
    calc
      _ = (segmentStepLaw m (segmentPathEnd n fallback s xs)).map
          (fun _ ↦ H xs) := by
        apply Measure.map_congr
        filter_upwards [] with step
        exact segmentSnocFixed_histStateView fallback s xs step hxs.1
      _ = Measure.dirac (H xs) := by
        rw [Measure.map_const]
        · have : IsProbabilityMeasure
              (segmentStepLaw m (segmentPathEnd n fallback s xs)) :=
            segmentStepLaw_isProbability m hb _
          simp only [this.measure_univ, one_smul]
  rw [hstate]
  rw [segmentFrom_endpoint_extension m hb n fallback s]
  rw [map_bind_eq_bind_map _ _ _
    (segmentEndpoint_family_measurable m hb n fallback s).aemeasurable
    hactionMap]
  change μ.bind (fun xs ↦
      ((segmentStepLaw m (segmentPathEnd n fallback s xs)).map
        (fun step ↦ segmentSnocFixed n fallback xs step)).map
          (fun ys ↦ histActionPair (Fin.last n)
            (decodeSegment fallback.2.2 (s, ys)))) =
    (μ.map H).compProd K
  rw [← Measure.bind_dirac_eq_map μ hH]
  rw [← action_bind_compProd_const_right μ
    (fun xs ↦ Measure.dirac (H xs)) (Measure.measurable_dirac.comp hH) hμp
    (fun _ ↦ inferInstance) K]
  apply Measure.bind_congr_right
  filter_upwards [(segmentFrom_ae_path_support m hb fallback.2.2 n s)] with xs hxs
  have hsnoc : Measurable
      (fun step ↦ segmentSnocFixed n fallback xs step) :=
    (segmentSnocFixed_measurable n fallback).comp
      (measurable_const.prodMk measurable_id)
  rw [Measure.map_map hactionMap hsnoc]
  have hleft :
      (segmentStepLaw m (segmentPathEnd n fallback s xs)).map
          (fun step ↦ histActionPair (Fin.last n)
            (decodeSegment fallback.2.2
              (s, segmentSnocFixed n fallback xs step))) =
        (selectorBehaviorActionMeasure m
          (segmentPathEnd n fallback s xs)).map (Prod.mk (H xs)) := by
    rw [← segmentStepLaw_map_action m (segmentPathEnd n fallback s xs),
      Measure.map_map (measurable_prodMk_left (x := H xs)) measurable_fst]
    apply Measure.map_congr
    filter_upwards [] with step
    apply Prod.ext
    · exact segmentSnocFixed_histStateView fallback s xs step hxs.1
    · exact segmentSnocFixed_actionAt fallback s xs step
  have hK : K (H xs) =
      selectorBehaviorActionMeasure m (segmentPathEnd n fallback s xs) := by
    unfold K
    rw [Kernel.comap_apply]
    have hobs : currentObsState (Fin.last n) (H xs) =
        (segmentPathEnd n fallback s xs).1 := by
      unfold H currentObsState
      rw [segmentPathEnd_eq_decode_curState n fallback s xs]
      rfl
    rw [hobs]
    exact behaviourKernel_apply_eq_selectorBehaviorActionMeasure m
      (segmentPathEnd n fallback s xs)
  change (segmentStepLaw m (segmentPathEnd n fallback s xs)).map
      (fun step ↦ histActionPair (Fin.last n)
        (decodeSegment fallback.2.2
          (s, segmentSnocFixed n fallback xs step))) =
    (Measure.dirac (H xs)).compProd K
  rw [hleft]
  ext B hB
  rw [Measure.dirac_compProd_apply hB,
    Measure.map_apply measurable_prodMk_left hB, hK]

/-- The arbitrary-start structural segment satisfies the behavior-action factorization at its
terminal epoch. For [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the model](hyp:m), [the finite assumption](hyp:hFinite),
[the behavior policy assumption](hyp:hb), [the initial distribution](hyp:nu), and
[the sample size](hyp:n), this establishes
[the segment law terminal action factorization result](goal). -/
-- @node: segmentLaw_terminal_action_factorization
lemma segmentLaw_terminal_action_factorization {T M : Nat}
    (m : ModelIndex T M) (hFinite : FiniteState m)
    (hb : PolicyVector m.Mx.b) (nu : JointState m.nX m.nH → ℝ) (n : Nat) :
    (segmentLaw m hFinite nu (n + 1)).map
        (histActionPair (Fin.last n)) =
      ((segmentLaw m hFinite nu (n + 1)).map
        (histStateView (Fin.last n))).compProd
        (Kernel.comap (behaviourKernel m.Mx.toRawB)
          (currentObsState (Fin.last n))
          (measurable_currentObsState (Fin.last n))) := by
  let fallback : Bool × ℝ × JointState m.nX m.nH :=
    (false, 0, (⟨0, hFinite.1⟩, ⟨0, hFinite.2⟩))
  let K : Kernel (StateHistoryView (n + 1) m.nX m.nH (Fin.last n)) Bool :=
    Kernel.comap (behaviourKernel m.Mx.toRawB)
      (currentObsState (Fin.last n))
      (measurable_currentObsState (Fin.last n))
  have hA :
      (segmentLaw m hFinite nu (n + 1)).map
          (histActionPair (Fin.last n)) =
        ∑ s, ENNReal.ofReal (nu s) •
          (segmentFrom m (n + 1) s).map (fun ys ↦
            histActionPair (Fin.last n)
              (decodeSegment fallback.2.2 (s, ys))) := by
    rw [segmentLaw_eq_sum_fixed_start, ← Measure.sum_fintype,
      Measure.map_sum (measurable_histActionPair (Fin.last n)).aemeasurable,
      Measure.sum_fintype]
    apply Finset.sum_congr rfl
    intro s _
    rw [Measure.map_smul, Measure.map_map
      (measurable_histActionPair (Fin.last n)) (by fun_prop)]
    rfl
  have hS :
      (segmentLaw m hFinite nu (n + 1)).map
          (histStateView (Fin.last n)) =
        ∑ s, ENNReal.ofReal (nu s) •
          (segmentFrom m (n + 1) s).map (fun ys ↦
            histStateView (Fin.last n)
              (decodeSegment fallback.2.2 (s, ys))) := by
    rw [segmentLaw_eq_sum_fixed_start, ← Measure.sum_fintype,
      Measure.map_sum (measurable_histStateView (Fin.last n)).aemeasurable,
      Measure.sum_fintype]
    apply Finset.sum_congr rfl
    intro s _
    rw [Measure.map_smul, Measure.map_map
      (measurable_histStateView (Fin.last n)) (by fun_prop)]
    rfl
  let μS := fun s : JointState m.nX m.nH ↦
    (segmentFrom m (n + 1) s).map (fun ys ↦
      histStateView (Fin.last n)
        (decodeSegment fallback.2.2 (s, ys)))
  have hmapS (s : JointState m.nX m.nH) : Measurable
      (fun ys : List (Bool × ℝ × JointState m.nX m.nH) ↦
        histStateView (Fin.last n)
          (decodeSegment fallback.2.2 (s, ys))) :=
    (measurable_histStateView (Fin.last n)).comp
      ((decodeSegment_measurable fallback.2.2).comp
        (measurable_const.prodMk measurable_id))
  letI : ∀ s : JointState m.nX m.nH,
      SFinite (ENNReal.ofReal (nu s) • μS s) := fun s ↦ by
    letI : IsProbabilityMeasure (segmentFrom m (n + 1) s) :=
      segmentFrom_isProbability m hb (n + 1) s
    letI : IsProbabilityMeasure (μS s) :=
      Measure.isProbabilityMeasure_map (hmapS s).aemeasurable
    infer_instance
  letI : IsMarkovKernel (behaviourKernel m.Mx.toRawB) := by
    constructor
    intro x
    constructor
    change (∑ a : Bool, ENNReal.ofReal (m.Mx.b x a) • Measure.dirac a)
      Set.univ = 1
    simp
    rw [← ENNReal.ofReal_add ((hb x).1 true) ((hb x).1 false)]
    rw [show m.Mx.b x true + m.Mx.b x false = 1 by simpa using (hb x).2]
    norm_num
  letI : IsMarkovKernel K := Kernel.IsMarkovKernel.comap _ _
  rw [hA, hS, ← Measure.sum_fintype, ← Measure.sum_fintype,
    Measure.compProd_sum_left]
  congr 1
  funext s
  letI : IsProbabilityMeasure (segmentFrom m (n + 1) s) :=
    segmentFrom_isProbability m hb (n + 1) s
  letI : IsProbabilityMeasure
      ((segmentFrom m (n + 1) s).map (fun ys ↦
        histStateView (Fin.last n)
          (decodeSegment fallback.2.2 (s, ys)))) :=
    Measure.isProbabilityMeasure_map (hmapS s).aemeasurable
  rw [Measure.compProd_smul_left]
  congr 1
  exact segmentFrom_terminal_action_factorization m hb n fallback s

end CausalSmith.Stat.PomdpPolicyclassRegret
