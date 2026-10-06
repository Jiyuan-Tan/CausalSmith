module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SelectorSegmentEndpoint
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SelectorSegmentFactorization
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.PhiwHistory

/-!
# Composition-product transport through structural prefix mixtures

The terminal kernel proof needs to interchange a measurable prefix mixture
with a common conditional kernel.  This lemma records that Giry/Fubini step.
-/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open MeasureTheory ProbabilityTheory
open CausalSmith.Stat.PomdpLatentOverlapMinimax

private lemma selector_map_bind_eq_bind_map {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure A) (κ : A → Measure B) (f : B → C)
    (hκ : AEMeasurable κ μ) (hf : Measurable f) :
    (μ.bind κ).map f = μ.bind (fun a ↦ (κ a).map f) := by
  have hdirac : Measurable (fun b ↦ Measure.dirac (f b)) := by fun_prop
  rw [← Measure.bind_dirac_eq_map _ hf,
    Measure.bind_bind hκ hdirac.aemeasurable]
  apply Measure.bind_congr_right
  filter_upwards [] with a
  exact Measure.bind_dirac_eq_map (κ a) hf

/-- Under fixed-length snoc, the terminal decoded reward is the appended step's reward
coordinate. For [the sample size](hyp:n), [the observed-state count](hyp:nX),
[the hidden-state count](hyp:nH), [the fallback state](hyp:fallback), [the state](hyp:s),
[the xs](hyp:xs), [the step](hyp:step), and [the len assumption](hyp:hlen), this establishes
[the segment snoc fixed reward at result](goal). -/
-- @node: segmentSnocFixed_rewardAt
lemma segmentSnocFixed_rewardAt {n nX nH : Nat}
    (fallback : Bool × ℝ × JointState nX nH) (s : JointState nX nH)
    (xs : List (Bool × ℝ × JointState nX nH))
    (step : Bool × ℝ × JointState nX nH) (hlen : xs.length = n) :
    rewardAt (Fin.last n)
        (decodeSegment fallback.2.2
          (s, segmentSnocFixed n fallback xs step)) = step.2.1 := by
  rw [segmentSnocFixed_eq_append n fallback xs step hlen]
  unfold rewardAt decodeSegment
  simp [List.getD, hlen]

/-- Under fixed-length snoc, the terminal decoded successor is the appended step's
successor-state coordinate. For [the sample size](hyp:n), [the observed-state count](hyp:nX),
[the hidden-state count](hyp:nH), [the fallback state](hyp:fallback), [the state](hyp:s),
[the xs](hyp:xs), [the step](hyp:step), and [the len assumption](hyp:hlen), this establishes
[the segment snoc fixed next state result](goal). -/
-- @node: segmentSnocFixed_nextState
lemma segmentSnocFixed_nextState {n nX nH : Nat}
    (fallback : Bool × ℝ × JointState nX nH) (s : JointState nX nH)
    (xs : List (Bool × ℝ × JointState nX nH))
    (step : Bool × ℝ × JointState nX nH) (hlen : xs.length = n) :
    nextState (Fin.last n)
        (decodeSegment fallback.2.2
          (s, segmentSnocFixed n fallback xs step)) = step.2.2 := by
  rw [segmentSnocFixed_eq_append n fallback xs step hlen]
  unfold nextState decodeSegment
  simp [List.getD, hlen]

/-- The terminal decoded history-next coordinate separates into the prefix history, appended
action, and appended reward-successor pair. For [the sample size](hyp:n),
[the observed-state count](hyp:nX), [the hidden-state count](hyp:nH),
[the fallback state](hyp:fallback), [the state](hyp:s), [the xs](hyp:xs), [the step](hyp:step),
and [the len assumption](hyp:hlen), this establishes
[the segment snoc fixed hist next pair result](goal). -/
-- @node: segmentSnocFixed_histNextPair
lemma segmentSnocFixed_histNextPair {n nX nH : Nat}
    (fallback : Bool × ℝ × JointState nX nH) (s : JointState nX nH)
    (xs : List (Bool × ℝ × JointState nX nH))
    (step : Bool × ℝ × JointState nX nH) (hlen : xs.length = n) :
    histNextPair (Fin.last n)
        (decodeSegment fallback.2.2
          (s, segmentSnocFixed n fallback xs step)) =
      ((histStateView (Fin.last n)
          (decodeSegment fallback.2.2 (s, xs)), step.1),
        (step.2.1, step.2.2)) := by
  apply Prod.ext
  · apply Prod.ext
    · exact segmentSnocFixed_histStateView fallback s xs step hlen
    · exact segmentSnocFixed_actionAt fallback s xs step
  · apply Prod.ext
    · exact segmentSnocFixed_rewardAt fallback s xs step hlen
    · exact segmentSnocFixed_nextState fallback s xs step hlen

/-- A composition product transports through coordinate maps when the target conditional kernel
is the mapped source kernel on every fiber. For [the first event](hyp:A), [the a'](hyp:A'),
[the second event](hyp:B), [the b'](hyp:B'), [the ν](hyp:ν), [the kernel](hyp:κ),
[the κ'](hyp:κ'), [the f](hyp:f), [the f assumption](hyp:hf), [the g](hyp:g),
[the g assumption](hyp:hg), and [the kernel assumption](hyp:hκ), this establishes
[the selector map comp prod of fiber result](goal). -/
-- @node: selector_map_compProd_of_fiber
lemma selector_map_compProd_of_fiber
    {A A' B B' : Type*} [MeasurableSpace A] [MeasurableSpace A']
    [MeasurableSpace B] [MeasurableSpace B']
    (ν : Measure A) [SFinite ν]
    (κ : Kernel A B) [IsSFiniteKernel κ]
    (κ' : Kernel A' B') [IsSFiniteKernel κ']
    (f : A → A') (hf : Measurable f) (g : B → B') (hg : Measurable g)
    (hκ : ∀ a, κ' (f a) = Measure.map g (κ a)) :
    (Measure.map f ν).compProd κ' =
      Measure.map (Prod.map f g) (ν.compProd κ) := by
  ext S hS
  rw [Measure.compProd_apply hS,
    MeasureTheory.lintegral_map (Kernel.measurable_kernel_prodMk_left hS) hf,
    Measure.map_apply (hf.prodMap hg) hS,
    Measure.compProd_apply (hS.preimage (hf.prodMap hg))]
  apply lintegral_congr
  intro a
  rw [hκ a, Measure.map_apply hg (measurable_prodMk_left hS)]
  rfl

/-- Binding a probability family and then adjoining a common conditional kernel agrees with
adjoining that kernel in every fiber before binding. For [the x](hyp:X), [the h](hyp:H),
[the y](hyp:Y), [the ρ](hyp:ρ), [the ν](hyp:ν), [the ν assumption](hyp:hν),
[the ρ assumption](hyp:hρ), [the νp assumption](hyp:hνp), and [the transition kernel](hyp:K),
this establishes [the selector bind comp prod const right result](goal). -/
-- @node: selector_bind_compProd_const_right
lemma selector_bind_compProd_const_right {X H Y : Type*}
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

/-- For one fixed structural prefix, adjoining its terminal step has exactly the model
reward-transition conditional law given the decoded history and terminal action. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the model](hyp:m),
[the sample size](hyp:n), [the fallback state](hyp:fallback), [the state](hyp:s),
[the xs](hyp:xs), and [the len assumption](hyp:hlen), this establishes
[the segment endpoint terminal kernel factorization result](goal). -/
-- @node: segmentEndpoint_terminal_kernel_factorization
lemma segmentEndpoint_terminal_kernel_factorization {T M : Nat}
    (m : ModelIndex T M) (n : Nat)
    (fallback : Bool × ℝ × JointState m.nX m.nH)
    (s : JointState m.nX m.nH)
    (xs : List (Bool × ℝ × JointState m.nX m.nH))
    (hlen : xs.length = n) :
    ((segmentStepLaw m (segmentPathEnd n fallback s xs)).map
      (fun step ↦ segmentSnocFixed n fallback xs step)).map
        (fun ys ↦ histNextPair (Fin.last n)
          (decodeSegment fallback.2.2 (s, ys))) =
      (((segmentStepLaw m (segmentPathEnd n fallback s xs)).map
        (fun step ↦ segmentSnocFixed n fallback xs step)).map
          (fun ys ↦ histActionPair (Fin.last n)
            (decodeSegment fallback.2.2 (s, ys)))).compProd
        (Kernel.comap (kernelOfK m.Mx.toRawB)
          (currentStateAction (Fin.last n))
          (measurable_currentStateAction (Fin.last n))) := by
  let H := histStateView (Fin.last n)
    (decodeSegment fallback.2.2 (s, xs))
  let f : Bool → ActionHistoryView (n + 1) m.nX m.nH (Fin.last n) :=
    fun a ↦ (H, a)
  let K := Kernel.comap (kernelOfK m.Mx.toRawB)
    (currentStateAction (Fin.last n))
    (measurable_currentStateAction (Fin.last n))
  let K0 := Kernel.comap (kernelOfK m.Mx.toRawB)
    (fun a ↦ (segmentPathEnd n fallback s xs, a)) (by fun_prop)
  letI : IsMarkovKernel (kernelOfK m.Mx.toRawB) :=
    ⟨fun sa ↦ m.kernel_law.1 sa.1 sa.2⟩
  letI : IsMarkovKernel K := Kernel.IsMarkovKernel.comap _ _
  letI : IsMarkovKernel K0 := Kernel.IsMarkovKernel.comap _ _
  have hK (a : Bool) : K (f a) = Measure.map id (K0 a) := by
    have hend := segmentPathEnd_eq_decode_curState n fallback s xs
    change m.Mx.K
        ((histStateView (Fin.last n)
          (decodeSegment fallback.2.2 (s, xs))).2) a =
      Measure.map id (m.Mx.K (segmentPathEnd n fallback s xs) a)
    rw [Measure.map_id]
    exact congrArg (fun q ↦ m.Mx.K q a) hend.symm
  have htransport := selector_map_compProd_of_fiber
    (selectorBehaviorActionMeasure m (segmentPathEnd n fallback s xs))
    K0 K f (by unfold f H; fun_prop) id measurable_id hK
  rw [← segmentStepLaw_compProd m (segmentPathEnd n fallback s xs)] at htransport
  have hleft :
      ((segmentStepLaw m (segmentPathEnd n fallback s xs)).map
        (fun step ↦ segmentSnocFixed n fallback xs step)).map
          (fun ys ↦ histNextPair (Fin.last n)
            (decodeSegment fallback.2.2 (s, ys))) =
        (segmentStepLaw m (segmentPathEnd n fallback s xs)).map
          (Prod.map f id) := by
    let outer := fun ys : List (Bool × ℝ × JointState m.nX m.nH) ↦
      histNextPair (Fin.last n) (decodeSegment fallback.2.2 (s, ys))
    let inner := fun step : Bool × ℝ × JointState m.nX m.nH ↦
      segmentSnocFixed n fallback xs step
    have hdecode : Measurable
        (fun ys : List (Bool × ℝ × JointState m.nX m.nH) ↦
          decodeSegment (n := n + 1) fallback.2.2 (s, ys)) :=
      (decodeSegment_measurable fallback.2.2).comp
        (measurable_const.prodMk measurable_id)
    have houter : Measurable outer :=
      (measurable_histNextPair (Fin.last n)).comp hdecode
    have hinner : Measurable inner :=
      (segmentSnocFixed_measurable n fallback).comp
        (measurable_prodMk_left (x := xs))
    change ((segmentStepLaw m (segmentPathEnd n fallback s xs)).map inner).map
      outer = _
    rw [Measure.map_map houter hinner]
    apply Measure.map_congr
    filter_upwards [] with step
    exact segmentSnocFixed_histNextPair fallback s xs step hlen
  have hright :
      ((segmentStepLaw m (segmentPathEnd n fallback s xs)).map
        (fun step ↦ segmentSnocFixed n fallback xs step)).map
          (fun ys ↦ histActionPair (Fin.last n)
            (decodeSegment fallback.2.2 (s, ys))) =
        (selectorBehaviorActionMeasure m
          (segmentPathEnd n fallback s xs)).map f := by
    let outer := fun ys : List (Bool × ℝ × JointState m.nX m.nH) ↦
      histActionPair (Fin.last n) (decodeSegment fallback.2.2 (s, ys))
    let inner := fun step : Bool × ℝ × JointState m.nX m.nH ↦
      segmentSnocFixed n fallback xs step
    have hdecode : Measurable
        (fun ys : List (Bool × ℝ × JointState m.nX m.nH) ↦
          decodeSegment (n := n + 1) fallback.2.2 (s, ys)) :=
      (decodeSegment_measurable fallback.2.2).comp
        (measurable_const.prodMk measurable_id)
    have houter : Measurable outer :=
      (measurable_histActionPair (Fin.last n)).comp hdecode
    have hinner : Measurable inner :=
      (segmentSnocFixed_measurable n fallback).comp
        (measurable_prodMk_left (x := xs))
    change ((segmentStepLaw m (segmentPathEnd n fallback s xs)).map inner).map
      outer = _
    rw [Measure.map_map houter hinner,
      ← segmentStepLaw_map_action m (segmentPathEnd n fallback s xs),
      Measure.map_map (by unfold f H; fun_prop) measurable_fst]
    apply Measure.map_congr
    filter_upwards [] with step
    apply Prod.ext
    · exact segmentSnocFixed_histStateView fallback s xs step hlen
    · exact segmentSnocFixed_actionAt fallback s xs step
  rw [hleft, hright]
  exact htransport.symm

/-- A fixed-start structural path has the model reward-transition conditional law at its
terminal epoch. For [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the model](hyp:m), [the behavior policy assumption](hyp:hb), [the sample size](hyp:n),
[the fallback state](hyp:fallback), and [the state](hyp:s), this establishes
[the segment from terminal kernel factorization result](goal). -/
-- @node: segmentFrom_terminal_kernel_factorization
lemma segmentFrom_terminal_kernel_factorization {T M : Nat}
    (m : ModelIndex T M) (hb : PolicyVector m.Mx.b) (n : Nat)
    (fallback : Bool × ℝ × JointState m.nX m.nH)
    (s : JointState m.nX m.nH) :
    (segmentFrom m (n + 1) s).map (fun ys ↦
      histNextPair (Fin.last n)
        (decodeSegment fallback.2.2 (s, ys))) =
      ((segmentFrom m (n + 1) s).map (fun ys ↦
        histActionPair (Fin.last n)
          (decodeSegment fallback.2.2 (s, ys)))).compProd
        (Kernel.comap (kernelOfK m.Mx.toRawB)
          (currentStateAction (Fin.last n))
          (measurable_currentStateAction (Fin.last n))) := by
  let E := fun xs : List (Bool × ℝ × JointState m.nX m.nH) ↦
    (segmentStepLaw m (segmentPathEnd n fallback s xs)).map
      (fun step ↦ segmentSnocFixed n fallback xs step)
  let outerA := fun ys : List (Bool × ℝ × JointState m.nX m.nH) ↦
    histActionPair (Fin.last n) (decodeSegment fallback.2.2 (s, ys))
  let outerN := fun ys : List (Bool × ℝ × JointState m.nX m.nH) ↦
    histNextPair (Fin.last n) (decodeSegment fallback.2.2 (s, ys))
  let ν := fun xs ↦ (E xs).map outerA
  let K := Kernel.comap (kernelOfK m.Mx.toRawB)
    (currentStateAction (Fin.last n))
    (measurable_currentStateAction (Fin.last n))
  have hE : Measurable E := segmentEndpoint_family_measurable m hb n fallback s
  have houterA : Measurable outerA :=
    (measurable_histActionPair (Fin.last n)).comp
      ((decodeSegment_measurable fallback.2.2).comp
        (measurable_const.prodMk measurable_id))
  have houterN : Measurable outerN :=
    (measurable_histNextPair (Fin.last n)).comp
      ((decodeSegment_measurable fallback.2.2).comp
        (measurable_const.prodMk measurable_id))
  have hν : Measurable ν := by
    exact (Measure.measurable_map outerA houterA).comp hE
  have hνp (xs : List (Bool × ℝ × JointState m.nX m.nH)) :
      IsProbabilityMeasure (ν xs) := by
    unfold ν E
    letI : IsProbabilityMeasure
        (segmentStepLaw m (segmentPathEnd n fallback s xs)) :=
      segmentStepLaw_isProbability m hb _
    letI : IsProbabilityMeasure
        ((segmentStepLaw m (segmentPathEnd n fallback s xs)).map
          (fun step ↦ segmentSnocFixed n fallback xs step)) :=
      Measure.isProbabilityMeasure_map
        ((segmentSnocFixed_measurable n fallback).comp
          (measurable_prodMk_left (x := xs))).aemeasurable
    exact Measure.isProbabilityMeasure_map houterA.aemeasurable
  have hρp : IsProbabilityMeasure (segmentFrom m n s) :=
    segmentFrom_isProbability m hb n s
  rw [segmentFrom_endpoint_extension m hb n fallback s]
  rw [selector_map_bind_eq_bind_map _ E outerN hE.aemeasurable houterN]
  rw [selector_map_bind_eq_bind_map _ E outerA hE.aemeasurable houterA]
  letI : IsMarkovKernel (kernelOfK m.Mx.toRawB) :=
    ⟨fun sa ↦ m.kernel_law.1 sa.1 sa.2⟩
  letI : IsMarkovKernel K := Kernel.IsMarkovKernel.comap _ _
  change (segmentFrom m n s).bind (fun xs ↦ (E xs).map outerN) =
    ((segmentFrom m n s).bind ν).compProd K
  rw [← selector_bind_compProd_const_right (segmentFrom m n s) ν hν
    hρp hνp K]
  apply Measure.bind_congr_right
  filter_upwards [(segmentFrom_ae_path_support m hb fallback.2.2 n s)] with xs hxs
  exact segmentEndpoint_terminal_kernel_factorization m n fallback s xs hxs.1

/-- The arbitrary-start structural segment satisfies the reward-transition factorization at its
terminal epoch. For [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the model](hyp:m), [the finite assumption](hyp:hFinite),
[the behavior policy assumption](hyp:hb), [the initial distribution](hyp:nu), and
[the sample size](hyp:n), this establishes
[the segment law terminal kernel factorization result](goal). -/
-- @node: segmentLaw_terminal_kernel_factorization
lemma segmentLaw_terminal_kernel_factorization {T M : Nat}
    (m : ModelIndex T M) (hFinite : FiniteState m)
    (hb : PolicyVector m.Mx.b) (nu : JointState m.nX m.nH → ℝ) (n : Nat) :
    (segmentLaw m hFinite nu (n + 1)).map
        (histNextPair (Fin.last n)) =
      ((segmentLaw m hFinite nu (n + 1)).map
        (histActionPair (Fin.last n))).compProd
        (Kernel.comap (kernelOfK m.Mx.toRawB)
          (currentStateAction (Fin.last n))
          (measurable_currentStateAction (Fin.last n))) := by
  let fallback : Bool × ℝ × JointState m.nX m.nH :=
    (false, 0, (⟨0, hFinite.1⟩, ⟨0, hFinite.2⟩))
  let K := Kernel.comap (kernelOfK m.Mx.toRawB)
    (currentStateAction (Fin.last n))
    (measurable_currentStateAction (Fin.last n))
  have hN :
      (segmentLaw m hFinite nu (n + 1)).map
          (histNextPair (Fin.last n)) =
        ∑ s, ENNReal.ofReal (nu s) •
          (segmentFrom m (n + 1) s).map (fun ys ↦
            histNextPair (Fin.last n)
              (decodeSegment fallback.2.2 (s, ys))) := by
    rw [segmentLaw_eq_sum_fixed_start, ← Measure.sum_fintype,
      Measure.map_sum (measurable_histNextPair (Fin.last n)).aemeasurable,
      Measure.sum_fintype]
    apply Finset.sum_congr rfl
    intro s _
    rw [Measure.map_smul, Measure.map_map
      (measurable_histNextPair (Fin.last n)) (by fun_prop)]
    rfl
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
  let μA := fun s : JointState m.nX m.nH ↦
    (segmentFrom m (n + 1) s).map (fun ys ↦
      histActionPair (Fin.last n)
        (decodeSegment fallback.2.2 (s, ys)))
  have hmapA (s : JointState m.nX m.nH) : Measurable
      (fun ys : List (Bool × ℝ × JointState m.nX m.nH) ↦
        histActionPair (Fin.last n)
          (decodeSegment fallback.2.2 (s, ys))) :=
    (measurable_histActionPair (Fin.last n)).comp
      ((decodeSegment_measurable fallback.2.2).comp
        (measurable_const.prodMk measurable_id))
  letI hsf : ∀ s : JointState m.nX m.nH,
      SFinite (ENNReal.ofReal (nu s) • μA s) := fun s ↦ by
    letI : IsProbabilityMeasure (segmentFrom m (n + 1) s) :=
      segmentFrom_isProbability m hb (n + 1) s
    letI : IsProbabilityMeasure (μA s) :=
      Measure.isProbabilityMeasure_map (hmapA s).aemeasurable
    infer_instance
  letI : IsMarkovKernel (kernelOfK m.Mx.toRawB) :=
    ⟨fun sa ↦ m.kernel_law.1 sa.1 sa.2⟩
  letI : IsMarkovKernel K := Kernel.IsMarkovKernel.comap _ _
  rw [hN, hA, ← Measure.sum_fintype, ← Measure.sum_fintype,
    Measure.compProd_sum_left]
  congr 1
  funext s
  letI : IsProbabilityMeasure (segmentFrom m (n + 1) s) :=
    segmentFrom_isProbability m hb (n + 1) s
  letI : IsProbabilityMeasure
      ((segmentFrom m (n + 1) s).map (fun ys ↦
        histActionPair (Fin.last n)
          (decodeSegment fallback.2.2 (s, ys)))) :=
    Measure.isProbabilityMeasure_map (hmapA s).aemeasurable
  rw [Measure.compProd_smul_left]
  congr 1
  exact segmentFrom_terminal_kernel_factorization m hb n fallback s

end CausalSmith.Stat.PomdpPolicyclassRegret
