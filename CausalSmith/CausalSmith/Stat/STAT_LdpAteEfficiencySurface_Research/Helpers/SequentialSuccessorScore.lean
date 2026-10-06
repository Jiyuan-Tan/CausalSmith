module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.SequentialScoreProjectionInputs
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-! # Directional scores for successor joint channels

This file identifies the directional score of the four-row joint channel
which generates a released prefix together with its next output.  The score
is expressed against the finite row-sum dominating measure, so the result
does not require countable generation of the output spaces.
-/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open Causalean.Mathlib.Probability.Kernel.FiniteSequence

/-- the [channel directional derivative density](goal) is the mathematical object specified below. For [the displayed quantities and conditions](hyp:p,Q,v,z), these specify the stated inputs. -/
def channelDirectionalDerivativeDensity {Z : Type*} [MeasurableSpace Z]
    (p : ℝ) (Q : Kernel (Fin 4) Z) (v : TrialParameter) (z : Z) : ℝ :=
  ∑ k : Fin 2, v k * channelDerivativeDensity p Q k z

/-- the channel directional score is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The channel Directional Score](goal) is determined by [the displayed parameters](hyp:θ,p,Q,v,z). -/
def channelDirectionalScore {Z : Type*} [MeasurableSpace Z]
    (θ : TrialParameter) (p : ℝ) (Q : Kernel (Fin 4) Z)
    (v : TrialParameter) (z : Z) : ℝ :=
  if 0 < channelOutputDensity θ p Q z then
    channelDirectionalDerivativeDensity p Q v z /
      channelOutputDensity θ p Q z
  else 0

/-- [the channel directional derivative density eq input sum assertion](goal) holds. For [the displayed quantities and conditions](hyp:p,Q,v,z), these specify the stated inputs. -/
lemma channelDirectionalDerivativeDensity_eq_inputSum
    {Z : Type*} [MeasurableSpace Z]
    (p : ℝ) (Q : Kernel (Fin 4) Z) (v : TrialParameter) (z : Z) :
    channelDirectionalDerivativeDensity p Q v z =
      ∑ j : Fin 4, inputDirectionalDerivative p v j * channelDensity Q j z := by
  unfold channelDirectionalDerivativeDensity channelDerivativeDensity
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  unfold inputDirectionalDerivative
  simp_rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- the channel output density nonneg of interior assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ), [the channel Output Density nonneg of interior](goal).

Under the stated assumptions, the channel Output Density nonneg of interior. -/
lemma channelOutputDensity_nonneg_of_interior
    {Z : Type*} [MeasurableSpace Z]
    (θ : TrialParameter) (p : ℝ) (Q : Kernel (Fin 4) Z)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (z : Z) :
    0 ≤ channelOutputDensity θ p Q z := by
  unfold channelOutputDensity
  exact Finset.sum_nonneg fun j _ => mul_nonneg
    (piTheta_pos_of_interior θ p hp hθ j).le ENNReal.toReal_nonneg

/-- the channel directional derivative density eq zero of output density eq zero assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hz), [the channel Directional Derivative Density eq zero of output Density eq zero](goal).

Under the stated assumptions, the channel Directional Derivative Density eq zero of output Density eq zero. -/
lemma channelDirectionalDerivativeDensity_eq_zero_of_outputDensity_eq_zero
    {Z : Type*} [MeasurableSpace Z]
    (θ v : TrialParameter) (p : ℝ) (Q : Kernel (Fin 4) Z)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (z : Z)
    (hz : channelOutputDensity θ p Q z = 0) :
    channelDirectionalDerivativeDensity p Q v z = 0 := by
  have hterms : ∀ j : Fin 4,
      piTheta θ p j * channelDensity Q j z = 0 := by
    have hnonneg : ∀ j ∈ (Finset.univ : Finset (Fin 4)),
        0 ≤ piTheta θ p j * channelDensity Q j z := by
      intro j hj
      exact mul_nonneg (piTheta_pos_of_interior θ p hp hθ j).le
        ENNReal.toReal_nonneg
    exact fun j => (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hz j
      (Finset.mem_univ j)
  rw [channelDirectionalDerivativeDensity_eq_inputSum]
  apply Finset.sum_eq_zero
  intro j hj
  have hdensity : channelDensity Q j z = 0 := by
    exact (mul_eq_zero.mp (hterms j)).resolve_left
      (ne_of_gt (piTheta_pos_of_interior θ p hp hθ j))
  rw [hdensity, mul_zero]

/-- the channel directional score mul output density assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ), [the channel Directional Score mul output Density](goal).

Under the stated assumptions, the channel Directional Score mul output Density. -/
lemma channelDirectionalScore_mul_outputDensity
    {Z : Type*} [MeasurableSpace Z]
    (θ v : TrialParameter) (p : ℝ) (Q : Kernel (Fin 4) Z)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (z : Z) :
    channelDirectionalScore θ p Q v z * channelOutputDensity θ p Q z =
      channelDirectionalDerivativeDensity p Q v z := by
  unfold channelDirectionalScore
  split_ifs with hpos
  · field_simp
  · have hnonneg := channelOutputDensity_nonneg_of_interior θ p Q hp hθ z
    have hz : channelOutputDensity θ p Q z = 0 :=
      le_antisymm (le_of_not_gt hpos) hnonneg
    rw [zero_mul, channelDirectionalDerivativeDensity_eq_zero_of_outputDensity_eq_zero
      θ v p Q hp hθ z hz]

/-- [the integrable channel density dominating assertion](goal) holds. For [the displayed quantities and conditions](hyp:Q,j), these specify the stated inputs. -/
lemma integrable_channelDensity_dominating
    {Z : Type*} [MeasurableSpace Z]
    (Q : Kernel (Fin 4) Z) [IsMarkovKernel Q] (j : Fin 4) :
    Integrable (channelDensity Q j) (dominatingMeasure Q) := by
  letI : IsFiniteMeasure (Q j) := inferInstance
  letI : IsFiniteMeasure (dominatingMeasure Q) :=
    ⟨by simp [dominatingMeasure]⟩
  have h := (integrable_toReal_rnDeriv_mul_iff
    (channelRow_absolutelyContinuous_dominating Q j)
    (f := fun _ => (1 : ℝ))).2 (integrable_const (1 : ℝ))
  change Integrable
    (fun z => ((Q j).rnDeriv (dominatingMeasure Q) z).toReal)
    (dominatingMeasure Q)
  simpa only [mul_one] using h

/-- [the set integral channel directional derivative density assertion](goal) holds. For [the displayed quantities and conditions](hyp:p,Q,v,A), these specify the stated inputs. -/
lemma setIntegral_channelDirectionalDerivativeDensity
    {Z : Type*} [MeasurableSpace Z]
    (p : ℝ) (Q : Kernel (Fin 4) Z) [IsMarkovKernel Q]
    (v : TrialParameter) (A : Set Z) :
    ∫ z in A, channelDirectionalDerivativeDensity p Q v z
        ∂dominatingMeasure Q =
      ∑ j : Fin 4, inputDirectionalDerivative p v j * (Q j A).toReal := by
  letI : IsFiniteMeasure (dominatingMeasure Q) :=
    ⟨by simp [dominatingMeasure]⟩
  calc
    (∫ z in A, channelDirectionalDerivativeDensity p Q v z
        ∂dominatingMeasure Q) =
        ∫ z in A, ∑ j : Fin 4,
          inputDirectionalDerivative p v j * channelDensity Q j z
            ∂dominatingMeasure Q := by
      apply integral_congr_ae
      filter_upwards [] with z
      exact channelDirectionalDerivativeDensity_eq_inputSum p Q v z
    _ = ∑ j : Fin 4, ∫ z in A,
        inputDirectionalDerivative p v j * channelDensity Q j z
          ∂dominatingMeasure Q := by
      rw [integral_finset_sum]
      intro j hj
      exact (integrable_channelDensity_dominating Q j).integrableOn.const_mul _
    _ = ∑ j : Fin 4,
        inputDirectionalDerivative p v j * (Q j A).toReal := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [integral_const_mul]
      rw [show (∫ z in A, channelDensity Q j z ∂dominatingMeasure Q) =
          (Q j).real A by
        exact Measure.setIntegral_toReal_rnDeriv
          (channelRow_absolutelyContinuous_dominating Q j) A]
      rfl

/-- the set integral sequential joint channel directional score assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ), [the set Integral sequential Joint channel Directional Score](goal).

Under the stated assumptions, the set Integral sequential Joint channel Directional Score. -/
lemma setIntegral_sequentialJoint_channelDirectionalScore
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (n : ℕ) (i : Fin n)
    (μ : Measure (History (Z n) i.val (Nat.le_of_lt i.isLt)))
    [IsProbabilityMeasure μ]
    (A : Set (History (Z n) i.val (Nat.le_of_lt i.isLt) × Z n i)) :
    ∫ z in A,
        channelDirectionalScore θ p (sequentialJointChannel P n i μ) v z *
          channelOutputDensity θ p (sequentialJointChannel P n i μ) z
        ∂dominatingMeasure (sequentialJointChannel P n i μ) =
      sequentialJointEventDerivative P v p n i μ A := by
  let Q := sequentialJointChannel P n i μ
  letI : IsMarkovKernel Q := sequentialJointChannel_isMarkov P n i μ
  have hpoint (z) : channelDirectionalScore θ p Q v z *
      channelOutputDensity θ p Q z =
        channelDirectionalDerivativeDensity p Q v z :=
    channelDirectionalScore_mul_outputDensity θ v p Q hp hθ z
  change (∫ z in A, channelDirectionalScore θ p Q v z *
      channelOutputDensity θ p Q z ∂dominatingMeasure Q) = _
  simp_rw [hpoint]
  exact setIntegral_channelDirectionalDerivativeDensity p Q v A

/-- the channel directional score sq mul output density assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ), [the channel Directional Score sq mul output Density](goal).

Under the stated assumptions, the channel Directional Score sq mul output Density. -/
lemma channelDirectionalScore_sq_mul_outputDensity
    {Z : Type*} [MeasurableSpace Z]
    (θ v : TrialParameter) (p : ℝ) (Q : Kernel (Fin 4) Z)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (z : Z) :
    channelDirectionalScore θ p Q v z ^ 2 * channelOutputDensity θ p Q z =
      channelDirectionalDerivativeDensity p Q v z ^ 2 /
        channelOutputDensity θ p Q z := by
  unfold channelDirectionalScore
  split_ifs with hpos
  · field_simp
  · have hnonneg := channelOutputDensity_nonneg_of_interior θ p Q hp hθ z
    have hz : channelOutputDensity θ p Q z = 0 :=
      le_antisymm (le_of_not_gt hpos) hnonneg
    have hder := channelDirectionalDerivativeDensity_eq_zero_of_outputDensity_eq_zero
      θ v p Q hp hθ z hz
    simp [hz, hder]

/-- the integral sequential joint channel directional score sq assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ), [the integral sequential Joint channel Directional Score sq](goal).

Under the stated assumptions, the integral sequential Joint channel Directional Score sq. -/
lemma integral_sequentialJoint_channelDirectionalScore_sq
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (n : ℕ) (i : Fin n)
    (μ : Measure (History (Z n) i.val (Nat.le_of_lt i.isLt)))
    [IsProbabilityMeasure μ] :
    ∫ z,
        channelDirectionalScore θ p (sequentialJointChannel P n i μ) v z ^ 2 *
          channelOutputDensity θ p (sequentialJointChannel P n i μ) z
        ∂dominatingMeasure (sequentialJointChannel P n i μ) =
      informationQuadratic
        (channelFisherInfo θ p (sequentialJointChannel P n i μ)) v := by
  let Q := sequentialJointChannel P n i μ
  have hQ : StationaryLDP ε Q := sequentialJointChannel_stationaryLDP P n i μ
  change (∫ z, channelDirectionalScore θ p Q v z ^ 2 *
      channelOutputDensity θ p Q z ∂dominatingMeasure Q) = _
  calc
    (∫ z, channelDirectionalScore θ p Q v z ^ 2 *
        channelOutputDensity θ p Q z ∂dominatingMeasure Q) =
        ∫ z, channelDirectionalDerivativeDensity p Q v z ^ 2 /
          channelOutputDensity θ p Q z ∂dominatingMeasure Q := by
      apply integral_congr_ae
      filter_upwards [] with z
      exact channelDirectionalScore_sq_mul_outputDensity θ v p Q hp hθ z
    _ = informationQuadratic (channelFisherInfo θ p Q) v := by
      rw [informationQuadratic_eq_channelIntegral p θ hp hθ ε Q hQ v]
      rfl

/-- the transcript prefix law is probability assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hk), [the transcript Prefix Law is Probability](goal).

Under the stated assumptions, the transcript Prefix Law is Probability. -/
lemma transcriptPrefixLaw_isProbability
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (n k : ℕ) (hk : k ≤ n) :
    IsProbabilityMeasure (transcriptPrefixLaw P θ p n k hk) := by
  rw [transcriptPrefixLaw_eq_observedPrefixLaw P θ p hp hθ n k hk]
  exact isProbabilityMeasure_prefixLaw
    (fun i => observedStageKernel P θ p n i)
    (fun i => observedStageKernel_isMarkov P θ p hp hθ n i)
    (fun _ => ()) k hk

/-- Under the successor coordinates `(init,last)`, the exact joint-channel score identities apply to the pushed-forward prefix law. The derivative here holds the predecessor prefix law fixed; differentiation of the whole successor law additionally contains the predecessor score. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hk), [the transcript Successor Law joint Score characterization](goal).

Under the stated assumptions, the transcript Successor Law joint Score characterization. -/
lemma transcriptSuccessorLaw_jointScore_characterization
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (n k : ℕ) (hk : k + 1 ≤ n)
    (A : Set (History (Z n) k (Nat.le_of_succ_le hk) × Z n (nextIndex hk))) :
    let μ := transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk)
    let Q := sequentialJointChannel P n (nextIndex hk) μ
    (transcriptPrefixLaw P θ p n (k + 1) hk).map
        (fun u => (init hk u, last hk u)) = outputLaw θ p Q ∧
      (∫ z in A, channelDirectionalScore θ p Q v z *
          channelOutputDensity θ p Q z ∂dominatingMeasure Q) =
        sequentialJointEventDerivative P v p n (nextIndex hk) μ A ∧
      (∫ z, channelDirectionalScore θ p Q v z ^ 2 *
          channelOutputDensity θ p Q z ∂dominatingMeasure Q) =
        informationQuadratic (channelFisherInfo θ p Q) v := by
  dsimp only
  have hμ : IsProbabilityMeasure
      (transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk)) :=
    transcriptPrefixLaw_isProbability P θ p hp hθ n k (Nat.le_of_succ_le hk)
  refine ⟨transcriptSuccessorLaw_eq_jointChannel P θ p hp hθ n k hk, ?_, ?_⟩
  · exact @setIntegral_sequentialJoint_channelDirectionalScore
      Z _ ε P θ v p hp hθ n (nextIndex hk)
        (transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk)) hμ A
  · exact @integral_sequentialJoint_channelDirectionalScore_sq
      Z _ ε P θ v p hp hθ n (nextIndex hk)
        (transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk)) hμ

end CausalSmith.Stat.LdpAteEfficiencySurface
