module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.SequentialPrefixDensity
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.SequentialJointChannel
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.SequentialObservedLaw

/-! # Successor-prefix and finite joint-channel identities -/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal
open Causalean.Mathlib.Probability.Kernel.FiniteSequence

/-- the transcript prefix law eq observed prefix law assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hk), [the transcript Prefix Law eq observed Prefix Law](goal).

Under the stated assumptions, the transcript Prefix Law eq observed Prefix Law. -/
lemma transcriptPrefixLaw_eq_observedPrefixLaw {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (n k : ℕ) (hk : k ≤ n) :
    transcriptPrefixLaw P θ p n k hk =
      prefixLaw (fun i => observedStageKernel P θ p n i)
        (fun _ => ()) k hk := by
  have hQ (i : Fin n) : IsMarkovKernel (observedStageKernel P θ p n i) :=
    observedStageKernel_isMarkov P θ p hp hθ n i
  have hpath : parameterPath θ (fun _ => 0) 0 = θ := by
    funext j
    simp [parameterPath]
  have hfull := transcriptLaw_eq_observedKernelLaw P θ (fun _ => 0) p hp n 0
    (hpath.symm ▸ hθ)
  rw [hpath] at hfull
  have hfamily : observedKernelFamily P θ (fun _ => 0) p n 0 =
      fun i => observedStageKernel P θ p n i := by
    funext i
    simp only [observedKernelFamily]
    rw [hpath]
  unfold transcriptPrefixLaw
  rw [hfull]
  unfold Causalean.Stat.Minimax.SequentialScore.law
  rw [hfamily]
  have hprefix : (transcriptPrefix hk : Transcript (Z n) → _) = take hk := by
    funext z j
    rfl
  rw [hprefix]
  exact transcriptLaw_map_prefix
    (fun i => observedStageKernel P θ p n i) hQ (fun _ => ()) k hk

/-- the transcript successor law eq joint channel assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hk), [the transcript Successor Law eq joint Channel](goal).

Under the stated assumptions, the transcript Successor Law eq joint Channel. -/
lemma transcriptSuccessorLaw_eq_jointChannel {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (n k : ℕ) (hk : k + 1 ≤ n) :
    (transcriptPrefixLaw P θ p n (k + 1) hk).map
        (fun u => (init hk u, last hk u)) =
      outputLaw θ p (sequentialJointChannel P n (nextIndex hk)
        (transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk))) := by
  let Q := fun i => observedStageKernel P θ p n i
  let μ := transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk)
  have hQ (i : Fin n) : IsMarkovKernel (Q i) :=
    observedStageKernel_isMarkov P θ p hp hθ n i
  have hμ : μ = prefixLaw Q (fun _ => ()) k (Nat.le_of_succ_le hk) :=
    transcriptPrefixLaw_eq_observedPrefixLaw P θ p hp hθ n k
      (Nat.le_of_succ_le hk)
  letI : IsProbabilityMeasure μ := by
    rw [hμ]
    exact isProbabilityMeasure_prefixLaw Q hQ (fun _ => ()) k _
  letI : IsProbabilityMeasure
      (transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk)) := by
    change IsProbabilityMeasure μ
    infer_instance
  have hμprob : IsProbabilityMeasure μ := inferInstance
  rw [transcriptPrefixLaw_eq_observedPrefixLaw P θ p hp hθ n (k + 1) hk]
  rw [prefixLaw_succ_map_init_last Q (fun _ => ()) k hk]
  rw [← hμ]
  exact (@outputLaw_sequentialJointChannel Z _ ε P θ p hp hθ n
    (nextIndex hk) μ hμprob).symm

/-- the sequential joint event derivative is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The sequential Joint Event Derivative](goal) is determined by [the displayed parameters](hyp:P,v,p,n,i,μ,A). -/
def sequentialJointEventDerivative {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (v : TrialParameter) (p : ℝ)
    (n : ℕ) (i : Fin n)
    (μ : Measure (History (Z n) i.val (Nat.le_of_lt i.isLt)))
    (A : Set (History (Z n) i.val (Nat.le_of_lt i.isLt) × Z n i)) : ℝ :=
  ∑ a : Fin 4, inputDirectionalDerivative p v a *
    (sequentialJointChannel P n i μ a A).toReal

/-- [the has deriv at sequential joint real mixture assertion](goal) holds. For [the displayed quantities and conditions](hyp:P,v,p,n,i,A), these specify the stated inputs. -/
lemma hasDerivAt_sequentialJoint_realMixture {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (n : ℕ) (i : Fin n)
    (μ : Measure (History (Z n) i.val (Nat.le_of_lt i.isLt)))
    (A : Set (History (Z n) i.val (Nat.le_of_lt i.isLt) × Z n i)) :
    HasDerivAt (fun u => ∑ a : Fin 4,
      piTheta (parameterPath θ v u) p a *
        (sequentialJointChannel P n i μ a A).toReal)
      (sequentialJointEventDerivative P v p n i μ A) 0 := by
  simpa [sequentialJointEventDerivative] using
    HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin 4)))
      (fun a _ ↦ (hasDerivAt_piTheta_parameterPath θ v p 0 a).mul_const
        (sequentialJointChannel P n i μ a A).toReal)

/-- the sequential joint real mixture eq output law to real assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hA), [the sequential Joint real Mixture eq output Law to Real](goal).

Under the stated assumptions, the sequential Joint real Mixture eq output Law to Real. -/
lemma sequentialJoint_realMixture_eq_outputLaw_toReal {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (n : ℕ) (i : Fin n)
    (μ : Measure (History (Z n) i.val (Nat.le_of_lt i.isLt)))
    [IsProbabilityMeasure μ]
    (A : Set (History (Z n) i.val (Nat.le_of_lt i.isLt) × Z n i))
    (hA : MeasurableSet A) :
    ∑ a : Fin 4, piTheta θ p a *
        (sequentialJointChannel P n i μ a A).toReal =
      (outputLaw θ p (sequentialJointChannel P n i μ) A).toReal := by
  let Q := sequentialJointChannel P n i μ
  have hQ : IsMarkovKernel Q := sequentialJointChannel_isMarkov P n i μ
  have hfinite (a : Fin 4) : Q a A ≠ ∞ := by
    letI : IsProbabilityMeasure (Q a) := hQ.isProbabilityMeasure a
    exact measure_ne_top (Q a) A
  unfold outputLaw
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.toReal_sum (fun a _ ↦
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfinite a))]
  simp_rw [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (piTheta_pos_of_interior θ p hp hθ _).le]
  rfl

-- keep: reusable sequential-law, Fisher-information, or van-Trees bridge for related adaptive experiments
/-- the has deriv at sequential joint output law assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hA), [the has Deriv At sequential Joint output Law](goal).

Under the stated assumptions, the has Deriv At sequential Joint output Law. -/
lemma hasDerivAt_sequentialJoint_outputLaw {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (n : ℕ) (i : Fin n)
    (μ : Measure (History (Z n) i.val (Nat.le_of_lt i.isLt)))
    [IsProbabilityMeasure μ]
    (A : Set (History (Z n) i.val (Nat.le_of_lt i.isLt) × Z n i))
    (hA : MeasurableSet A) :
    HasDerivAt (fun u =>
      (outputLaw (parameterPath θ v u) p
        (sequentialJointChannel P n i μ) A).toReal)
      (sequentialJointEventDerivative P v p n i μ A) 0 := by
  have hc0 : ContinuousAt (fun u => parameterPath θ v u 0) 0 := by
    unfold parameterPath
    fun_prop
  have hc1 : ContinuousAt (fun u => parameterPath θ v u 1) 0 := by
    unfold parameterPath
    fun_prop
  have h00 : (0 : ℝ) < parameterPath θ v 0 0 := by
    simpa [parameterPath] using hθ.1
  have h01 : parameterPath θ v 0 0 < (1 : ℝ) := by
    simpa [parameterPath] using hθ.2.1
  have h10 : (0 : ℝ) < parameterPath θ v 0 1 := by
    simpa [parameterPath] using hθ.2.2.1
  have h11 : parameterPath θ v 0 1 < (1 : ℝ) := by
    simpa [parameterPath] using hθ.2.2.2
  have hinterior : {u : ℝ | InteriorMeans (parameterPath θ v u)} ∈ nhds 0 := by
    filter_upwards [continuousAt_const.eventually_lt hc0 h00,
      hc0.eventually_lt continuousAt_const h01,
      continuousAt_const.eventually_lt hc1 h10,
      hc1.eventually_lt continuousAt_const h11] with u hu00 hu01 hu10 hu11
    exact ⟨hu00, hu01, hu10, hu11⟩
  have heq : Filter.EventuallyEq (nhds 0) (fun u =>
      (outputLaw (parameterPath θ v u) p
        (sequentialJointChannel P n i μ) A).toReal) (fun u =>
      ∑ a : Fin 4, piTheta (parameterPath θ v u) p a *
        (sequentialJointChannel P n i μ a A).toReal) := by
    filter_upwards [hinterior] with u hu
    exact (sequentialJoint_realMixture_eq_outputLaw_toReal P
      (parameterPath θ v u) p hp hu n i μ A hA).symm
  exact (hasDerivAt_sequentialJoint_realMixture P θ v p n i μ A).congr_of_eventuallyEq heq

end CausalSmith.Stat.LdpAteEfficiencySurface
