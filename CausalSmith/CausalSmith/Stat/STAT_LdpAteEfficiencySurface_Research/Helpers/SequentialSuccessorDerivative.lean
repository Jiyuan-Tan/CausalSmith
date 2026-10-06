module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.SequentialSuccessorScore

/-! # Derivative decomposition for a sequential successor event

This file records the exact product rule for the successor-prefix law.  It
keeps the derivative caused by the varying predecessor prefix law separate
from the derivative of the current four-row mixture.
-/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal Topology
open Causalean.Mathlib.Probability.Kernel.FiniteSequence

/-- The mass of a successor event in one fixed current-input row while the predecessor prefix law varies along the parameter path. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. [The varying Predecessor Row Event Mass](goal) is determined by [the displayed parameters](hyp:P,θ,v,p,n,k,hk,u,a,A). -/
def varyingPredecessorRowEventMass {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (n k : ℕ) (hk : k + 1 ≤ n) (u : ℝ) (a : Fin 4)
    (A : Set (History (Z n) k (Nat.le_of_succ_le hk) ×
      Z n (nextIndex hk))) : ℝ :=
  (sequentialJointChannel P n (nextIndex hk)
    (transcriptPrefixLaw P (parameterPath θ v u) p n k
      (Nat.le_of_succ_le hk)) a A).toReal

/-- The derivative contribution from the varying predecessor law, after mixing the four current-input rows at the base parameter. For the displayed inputs and conditions, the stated result follows. [The predecessor Successor Event Derivative](goal) is determined by [the displayed parameters](hyp:θ,p,pastRowDerivative). -/
def predecessorSuccessorEventDerivative
    (θ : TrialParameter) (p : ℝ) (pastRowDerivative : Fin 4 → ℝ) : ℝ :=
  ∑ a : Fin 4, piTheta θ p a * pastRowDerivative a

/-- The real mass of a successor-prefix event after splitting the successor history into its predecessor and final output coordinates. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. [The successor Prefix Event Mass](goal) is determined by [the displayed parameters](hyp:P,θ,v,p,n,k,hk,u,A). -/
def successorPrefixEventMass {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (n k : ℕ) (hk : k + 1 ≤ n) (u : ℝ)
    (A : Set (History (Z n) k (Nat.le_of_succ_le hk) ×
      Z n (nextIndex hk))) : ℝ :=
  (((transcriptPrefixLaw P (parameterPath θ v u) p n (k + 1) hk).map
    (fun w => (init hk w, last hk w))) A).toReal

/-- Integrating a fixed measurable function against the varying prefix law differentiates by integrating it against the explicit finite-mixture prefix derivative density. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hk,hg,hgInt), [the has Deriv At integral transcript Prefix Law](goal).

Under the stated assumptions, the has Deriv At integral transcript Prefix Law. -/
lemma hasDerivAt_integral_transcriptPrefixLaw
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (n k : ℕ) (hk : k ≤ n) (g : History (Z n) k hk → ℝ)
    (hg : Measurable g)
    (hgInt : ∀ x : Fin n → Fin 4, Integrable g
      ((P.transcript n x).map (transcriptPrefix hk))) :
    HasDerivAt (fun u => ∫ h, g h
      ∂transcriptPrefixLaw P (parameterPath θ v u) p n k hk)
      (∫ h, transcriptPrefixMixtureRealDerivative P θ v p n k hk h * g h
        ∂transcriptPrefixReferenceMeasure P n k hk) 0 := by
  let ν := transcriptPrefixReferenceMeasure P n k hk
  let μ (x : Fin n → Fin 4) :=
    (P.transcript n x).map (transcriptPrefix hk)
  letI (x : Fin n → Fin 4) : IsProbabilityMeasure (P.transcript n x) :=
    (P.factorizes n x).1
  letI (x : Fin n → Fin 4) : IsProbabilityMeasure (μ x) :=
    Measure.isProbabilityMeasure_map (measurable_transcriptPrefix hk).aemeasurable
  letI : IsFiniteMeasure ν := by
    dsimp [ν, transcriptPrefixReferenceMeasure]
    infer_instance
  have hzero : parameterPath θ v 0 = θ := by
    funext j
    simp [parameterPath]
  have hc0 : ContinuousAt (fun u => parameterPath θ v u 0) 0 := by
    unfold parameterPath
    fun_prop
  have hc1 : ContinuousAt (fun u => parameterPath θ v u 1) 0 := by
    unfold parameterPath
    fun_prop
  have hinterior : {u : ℝ | InteriorMeans (parameterPath θ v u)} ∈ nhds 0 := by
    filter_upwards
      [continuousAt_const.eventually_lt hc0 (by simpa [hzero] using hθ.1),
       hc0.eventually_lt continuousAt_const (by simpa [hzero] using hθ.2.1),
       continuousAt_const.eventually_lt hc1 (by simpa [hzero] using hθ.2.2.1),
       hc1.eventually_lt continuousAt_const (by simpa [hzero] using hθ.2.2.2)]
      with u hu00 hu01 hu10 hu11
    exact ⟨hu00, hu01, hu10, hu11⟩
  have heq : (fun u => ∫ h, g h
      ∂transcriptPrefixLaw P (parameterPath θ v u) p n k hk) =ᶠ[nhds 0]
      fun u => ∑ x : Fin n → Fin 4,
        inputPathProbability (parameterPath θ v u) p x * ∫ h, g h ∂μ x := by
    filter_upwards [hinterior] with u hu
    rw [transcriptPrefixLaw_eq_sum, integral_finset_sum_measure]
    · apply Finset.sum_congr rfl
      intro x _
      rw [integral_smul_measure, ENNReal.toReal_ofReal
        (inputPathProbability_pos_of_interior
          (parameterPath θ v u) p hp hu x).le]
      rfl
    · intro x _
      exact (hgInt x).smul_measure ENNReal.ofReal_ne_top
  have hfiniteDerivative : HasDerivAt (fun u => ∑ x : Fin n → Fin 4,
      inputPathProbability (parameterPath θ v u) p x * ∫ h, g h ∂μ x)
      (∑ x : Fin n → Fin 4,
        inputPathDirectionalDerivative θ v p x * ∫ h, g h ∂μ x) 0 := by
    simpa only [hzero] using HasDerivAt.fun_sum
      (u := (Finset.univ : Finset (Fin n → Fin 4)))
      (fun x _ => (hasDerivAt_inputPathProbability_parameterPath
        θ v p 0 x).mul_const (∫ h, g h ∂μ x))
  have hpac (x : Fin n → Fin 4) : μ x ≪ ν := by
    dsimp [μ, ν, transcriptPrefixReferenceMeasure]
    exact (transcriptComponent_ac_reference P n x).map
      (measurable_transcriptPrefix hk)
  have htermInt (x : Fin n → Fin 4) : Integrable (fun h =>
      inputPathDirectionalDerivative θ v p x *
        transcriptPrefixComponentRealDensity P n k hk x h * g h) ν := by
    have hi : Integrable (fun h =>
        transcriptPrefixComponentRealDensity P n k hk x h * g h) ν := by
      change Integrable (fun h => ((μ x).rnDeriv ν h).toReal * g h) ν
      exact (integrable_toReal_rnDeriv_mul_iff (hpac x)).2 (hgInt x)
    convert hi.const_mul (inputPathDirectionalDerivative θ v p x) using 1 <;>
      ring
  have hderivative : (∫ h,
      transcriptPrefixMixtureRealDerivative P θ v p n k hk h * g h ∂ν) =
      ∑ x : Fin n → Fin 4,
        inputPathDirectionalDerivative θ v p x * ∫ h, g h ∂μ x := by
    simp_rw [transcriptPrefixMixtureRealDerivative, Finset.sum_mul]
    rw [integral_finset_sum _ (fun x _ => htermInt x)]
    apply Finset.sum_congr rfl
    intro x _
    rw [show (fun h => inputPathDirectionalDerivative θ v p x *
        transcriptPrefixComponentRealDensity P n k hk x h * g h) =
        fun h => inputPathDirectionalDerivative θ v p x *
          (transcriptPrefixComponentRealDensity P n k hk x h * g h) by
      funext h
      ring]
    rw [integral_const_mul]
    change inputPathDirectionalDerivative θ v p x *
      (∫ h, ((μ x).rnDeriv ν h).toReal * g h ∂ν) = _
    rw [integral_toReal_rnDeriv_mul (hpac x)]
  rw [hderivative]
  exact hfiniteDerivative.congr_of_eventuallyEq heq

/-- The real event section of one fixed current-input row as a function of
the released predecessor history. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:P,n,k,hk,a,A,h), these specify the stated inputs. -/
def successorRowKernelSection {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (n k : ℕ) (hk : k + 1 ≤ n)
    (a : Fin 4)
    (A : Set (History (Z n) k (Nat.le_of_succ_le hk) ×
      Z n (nextIndex hk)))
    (h : History (Z n) k (Nat.le_of_succ_le hk)) : ℝ :=
  ((P.channel n (nextIndex hk))
    (a, fsHistoryToPrivate (nextIndex hk) h) (Prod.mk h ⁻¹' A)).toReal

/-- A fixed-row successor event section is measurable on the predecessor
history space, with no regularity assumption on the output space. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:P,n,k,hk,a,A,hA), these specify the stated inputs. -/
lemma measurable_successorRowKernelSection {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (n k : ℕ) (hk : k + 1 ≤ n)
    (a : Fin 4)
    (A : Set (History (Z n) k (Nat.le_of_succ_le hk) ×
      Z n (nextIndex hk))) (hA : MeasurableSet A) :
    Measurable (successorRowKernelSection P n k hk a A) := by
  letI : IsMarkovKernel (P.channel n (nextIndex hk)) :=
    (P.privacy n).1 (nextIndex hk)
  let K : Kernel (History (Z n) k (Nat.le_of_succ_le hk))
      (Z n (nextIndex hk)) :=
    (P.channel n (nextIndex hk)).comap
      (fun h => (a, fsHistoryToPrivate (nextIndex hk) h))
      (measurable_const.prodMk
        (measurable_fsHistoryToPrivate (nextIndex hk)))
  have hm : Measurable (fun h => K h (Prod.mk h ⁻¹' A)) :=
    K.measurable_kernel_prodMk_left hA
  exact hm.ennreal_toReal

/-- The row section is integrable under every deterministic-input predecessor
prefix component. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:P,n,k,hk,a,A,hA,x), these specify the stated inputs. -/
lemma integrable_successorRowKernelSection_component {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (n k : ℕ) (hk : k + 1 ≤ n)
    (a : Fin 4)
    (A : Set (History (Z n) k (Nat.le_of_succ_le hk) ×
      Z n (nextIndex hk))) (hA : MeasurableSet A)
    (x : Fin n → Fin 4) :
    Integrable (successorRowKernelSection P n k hk a A)
      ((P.transcript n x).map
        (transcriptPrefix (Nat.le_of_succ_le hk))) := by
  letI : IsProbabilityMeasure (P.transcript n x) := (P.factorizes n x).1
  letI : IsProbabilityMeasure ((P.transcript n x).map
      (transcriptPrefix (Nat.le_of_succ_le hk))) :=
    Measure.isProbabilityMeasure_map
      (measurable_transcriptPrefix (Nat.le_of_succ_le hk)).aemeasurable
  apply Integrable.of_bound
    (measurable_successorRowKernelSection P n k hk a A hA).aestronglyMeasurable 1
  filter_upwards [] with h
  change |((P.channel n (nextIndex hk))
    (a, fsHistoryToPrivate (nextIndex hk) h) (Prod.mk h ⁻¹' A)).toReal| ≤ 1
  rw [abs_of_nonneg ENNReal.toReal_nonneg]
  have hQ : IsMarkovKernel (P.channel n (nextIndex hk)) :=
    (P.privacy n).1 (nextIndex hk)
  letI : IsProbabilityMeasure
      ((P.channel n (nextIndex hk))
        (a, fsHistoryToPrivate (nextIndex hk) h)) :=
    hQ.isProbabilityMeasure _
  have hle : (P.channel n (nextIndex hk))
      (a, fsHistoryToPrivate (nextIndex hk) h) (Prod.mk h ⁻¹' A) ≤ 1 := by
    have hm : (P.channel n (nextIndex hk))
        (a, fsHistoryToPrivate (nextIndex hk) h) (Prod.mk h ⁻¹' A) ≤
        (P.channel n (nextIndex hk))
          (a, fsHistoryToPrivate (nextIndex hk) h) Set.univ :=
      MeasureTheory.measure_mono (Set.subset_univ _)
    simpa using hm
  simpa using ENNReal.toReal_mono ENNReal.one_ne_top hle

/-- [the sequential joint channel apply to real eq integral assertion](goal) holds. For [the displayed quantities and conditions](hyp:P,n,i,a,A,hA), these specify the stated inputs. -/
lemma sequentialJointChannel_apply_toReal_eq_integral {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (n : ℕ) (i : Fin n)
    (μ : Measure (History (Z n) i.val (Nat.le_of_lt i.isLt)))
    [IsFiniteMeasure μ]
    (a : Fin 4)
    (A : Set (History (Z n) i.val (Nat.le_of_lt i.isLt) × Z n i))
    (hA : MeasurableSet A) :
    (sequentialJointChannel P n i μ a A).toReal =
      ∫ h, ((P.channel n i)
        (a, fsHistoryToPrivate i h) (Prod.mk h ⁻¹' A)).toReal ∂μ := by
  letI : IsMarkovKernel (P.channel n i) := (P.privacy n).1 i
  unfold sequentialJointChannel releasedHistoryRowKernel
  rw [Kernel.compProd_apply hA, integral_toReal]
  · rfl
  · have hm := ((P.channel n i).comap
      (fun h => (a, fsHistoryToPrivate i h))
      (measurable_const.prodMk
        (measurable_fsHistoryToPrivate i))).measurable_kernel_prodMk_left hA
    exact hm.aemeasurable
  · filter_upwards [] with h
    exact measure_lt_top _ _

/-- The predecessor contribution for one current-input row is the prefix derivative density integrated against that row's bounded event section. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. [The predecessor Row Event Derivative](goal) is determined by [the displayed parameters](hyp:P,θ,v,p,n,k,hk,a,A). -/
def predecessorRowEventDerivative {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (n k : ℕ) (hk : k + 1 ≤ n) (a : Fin 4)
    (A : Set (History (Z n) k (Nat.le_of_succ_le hk) ×
      Z n (nextIndex hk))) : ℝ :=
  ∫ h, transcriptPrefixMixtureRealDerivative P θ v p n k
      (Nat.le_of_succ_le hk) h *
    successorRowKernelSection P n k hk a A h
    ∂transcriptPrefixReferenceMeasure P n k (Nat.le_of_succ_le hk)

/-- The derivative of a fixed current-input row is exactly the predecessor prefix derivative contribution; the current row itself is held fixed here. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hk,hA), [the has Deriv At varying Predecessor Row Event Mass](goal).

Under the stated assumptions, the has Deriv At varying Predecessor Row Event Mass. -/
lemma hasDerivAt_varyingPredecessorRowEventMass
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (n k : ℕ) (hk : k + 1 ≤ n) (a : Fin 4)
    (A : Set (History (Z n) k (Nat.le_of_succ_le hk) ×
      Z n (nextIndex hk))) (hA : MeasurableSet A) :
    HasDerivAt (fun u => varyingPredecessorRowEventMass
      P θ v p n k hk u a A)
      (predecessorRowEventDerivative P θ v p n k hk a A) 0 := by
  let g := successorRowKernelSection P n k hk a A
  have hbase := hasDerivAt_integral_transcriptPrefixLaw P θ v p hp hθ
    n k (Nat.le_of_succ_le hk) g
    (measurable_successorRowKernelSection P n k hk a A hA)
    (fun x => integrable_successorRowKernelSection_component
      P n k hk a A hA x)
  have hzero : parameterPath θ v 0 = θ := by
    funext j
    simp [parameterPath]
  have hc0 : ContinuousAt (fun u => parameterPath θ v u 0) 0 := by
    unfold parameterPath
    fun_prop
  have hc1 : ContinuousAt (fun u => parameterPath θ v u 1) 0 := by
    unfold parameterPath
    fun_prop
  have hinterior : {u : ℝ | InteriorMeans (parameterPath θ v u)} ∈ nhds 0 := by
    filter_upwards
      [continuousAt_const.eventually_lt hc0 (by simpa [hzero] using hθ.1),
       hc0.eventually_lt continuousAt_const (by simpa [hzero] using hθ.2.1),
       continuousAt_const.eventually_lt hc1 (by simpa [hzero] using hθ.2.2.1),
       hc1.eventually_lt continuousAt_const (by simpa [hzero] using hθ.2.2.2)]
      with u hu00 hu01 hu10 hu11
    exact ⟨hu00, hu01, hu10, hu11⟩
  have heq : (fun u => varyingPredecessorRowEventMass
      P θ v p n k hk u a A) =ᶠ[nhds 0] fun u => ∫ h, g h
        ∂transcriptPrefixLaw P (parameterPath θ v u) p n k
          (Nat.le_of_succ_le hk) := by
    filter_upwards [hinterior] with u hu
    have hprob : IsProbabilityMeasure
        (transcriptPrefixLaw P (parameterPath θ v u) p n k
          (Nat.le_of_succ_le hk)) :=
      transcriptPrefixLaw_isProbability P (parameterPath θ v u) p hp hu
        n k (Nat.le_of_succ_le hk)
    let μu : Measure (History (Z n) (nextIndex hk).val
        (Nat.le_of_lt (nextIndex hk).isLt)) :=
      transcriptPrefixLaw P (parameterPath θ v u) p n k
        (Nat.le_of_succ_le hk)
    letI : IsProbabilityMeasure μu := by
      constructor
      change transcriptPrefixLaw P (parameterPath θ v u) p n k
        (Nat.le_of_succ_le hk) Set.univ = 1
      exact @IsProbabilityMeasure.measure_univ _ _ _ hprob
    letI : IsFiniteMeasure μu := ⟨by
      rw [IsProbabilityMeasure.measure_univ]
      exact ENNReal.one_lt_top⟩
    unfold varyingPredecessorRowEventMass
    change (sequentialJointChannel P n (nextIndex hk) μu a A).toReal = _
    rw [sequentialJointChannel_apply_toReal_eq_integral P n (nextIndex hk)
      μu a A hA]
    rfl
  exact hbase.congr_of_eventuallyEq heq

/-- The successor-event derivative is the sum of the varying-predecessor contribution and the current joint-channel directional derivative. The row derivative premise concerns only variation of the predecessor prefix law; the current four-cell weights are differentiated explicitly here. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hk,hA,hrow), [the has Deriv At successor Prefix Event Mass of predecessor rows](goal).

Under the stated assumptions, the has Deriv At successor Prefix Event Mass of predecessor rows. -/
lemma hasDerivAt_successorPrefixEventMass_of_predecessor_rows
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (n k : ℕ) (hk : k + 1 ≤ n)
    (A : Set (History (Z n) k (Nat.le_of_succ_le hk) ×
      Z n (nextIndex hk))) (hA : MeasurableSet A)
    (pastRowDerivative : Fin 4 → ℝ)
    (hrow : ∀ a, HasDerivAt
      (fun u => varyingPredecessorRowEventMass
        P θ v p n k hk u a A) (pastRowDerivative a) 0) :
    HasDerivAt (fun u => successorPrefixEventMass
      P θ v p n k hk u A)
      (predecessorSuccessorEventDerivative θ p pastRowDerivative +
        sequentialJointEventDerivative P v p n (nextIndex hk)
          (transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk)) A) 0 := by
  have hzero : parameterPath θ v 0 = θ := by
    funext j
    simp [parameterPath]
  have hc0 : ContinuousAt (fun u => parameterPath θ v u 0) 0 := by
    unfold parameterPath
    fun_prop
  have hc1 : ContinuousAt (fun u => parameterPath θ v u 1) 0 := by
    unfold parameterPath
    fun_prop
  have hinterior : {u : ℝ | InteriorMeans (parameterPath θ v u)} ∈ nhds 0 := by
    filter_upwards
      [continuousAt_const.eventually_lt hc0 (by simpa [hzero] using hθ.1),
       hc0.eventually_lt continuousAt_const (by simpa [hzero] using hθ.2.1),
       continuousAt_const.eventually_lt hc1 (by simpa [hzero] using hθ.2.2.1),
       hc1.eventually_lt continuousAt_const (by simpa [hzero] using hθ.2.2.2)]
      with u hu00 hu01 hu10 hu11
    exact ⟨hu00, hu01, hu10, hu11⟩
  have heq : (fun u => successorPrefixEventMass P θ v p n k hk u A) =ᶠ[nhds 0]
      fun u => ∑ a : Fin 4,
        piTheta (parameterPath θ v u) p a *
          varyingPredecessorRowEventMass P θ v p n k hk u a A := by
    filter_upwards [hinterior] with u hu
    have hμprob : IsProbabilityMeasure
        (transcriptPrefixLaw P (parameterPath θ v u) p n k
          (Nat.le_of_succ_le hk)) :=
      transcriptPrefixLaw_isProbability P (parameterPath θ v u) p hp hu
        n k (Nat.le_of_succ_le hk)
    have hlaw := transcriptSuccessorLaw_eq_jointChannel P
      (parameterPath θ v u) p hp hu n k hk
    have hmix := @sequentialJoint_realMixture_eq_outputLaw_toReal Z _ ε P
      (parameterPath θ v u) p hp hu n (nextIndex hk)
      (transcriptPrefixLaw P (parameterPath θ v u) p n k
        (Nat.le_of_succ_le hk)) hμprob A hA
    unfold successorPrefixEventMass varyingPredecessorRowEventMass
    rw [hlaw]
    exact hmix.symm
  have hsum : HasDerivAt (fun u => ∑ a : Fin 4,
      piTheta (parameterPath θ v u) p a *
        varyingPredecessorRowEventMass P θ v p n k hk u a A)
      (∑ a : Fin 4,
        (inputDirectionalDerivative p v a *
          varyingPredecessorRowEventMass P θ v p n k hk 0 a A +
        piTheta θ p a * pastRowDerivative a)) 0 := by
    simpa only [Pi.mul_apply, hzero] using HasDerivAt.fun_sum
      (u := (Finset.univ : Finset (Fin 4)))
      (fun a _ => (hasDerivAt_piTheta_parameterPath θ v p 0 a).mul (hrow a))
  have hderivative : (∑ a : Fin 4,
      (inputDirectionalDerivative p v a *
        varyingPredecessorRowEventMass P θ v p n k hk 0 a A +
      piTheta θ p a * pastRowDerivative a)) =
      predecessorSuccessorEventDerivative θ p pastRowDerivative +
        sequentialJointEventDerivative P v p n (nextIndex hk)
          (transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk)) A := by
    simp only [predecessorSuccessorEventDerivative,
      sequentialJointEventDerivative, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    simp [varyingPredecessorRowEventMass, hzero]
  rw [hderivative] at hsum
  exact hsum.congr_of_eventuallyEq heq

/-- The exact successor-event derivative obtained by differentiating both the varying predecessor prefix law and the current observation-dependent row. The first summand is the finite-mixture pushforward of the prefix score; the second is the directional derivative of the current joint channel with its predecessor law fixed at the base parameter. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hk,hA), [the has Deriv At successor Prefix Event Mass](goal).

Under the stated assumptions, the has Deriv At successor Prefix Event Mass. -/
lemma hasDerivAt_successorPrefixEventMass
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (n k : ℕ) (hk : k + 1 ≤ n)
    (A : Set (History (Z n) k (Nat.le_of_succ_le hk) ×
      Z n (nextIndex hk))) (hA : MeasurableSet A) :
    HasDerivAt (fun u => successorPrefixEventMass
      P θ v p n k hk u A)
      (predecessorSuccessorEventDerivative θ p
          (fun a => predecessorRowEventDerivative P θ v p n k hk a A) +
        sequentialJointEventDerivative P v p n (nextIndex hk)
          (transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk)) A) 0 := by
  exact hasDerivAt_successorPrefixEventMass_of_predecessor_rows
    P θ v p hp hθ n k hk A hA
    (fun a => predecessorRowEventDerivative P θ v p n k hk a A)
    (fun a => hasDerivAt_varyingPredecessorRowEventMass
      P θ v p hp hθ n k hk a A hA)

end CausalSmith.Stat.LdpAteEfficiencySurface
