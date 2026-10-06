module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.Refinement
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.OracleEnvelope
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotPrefix
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.SequentialObservedKernel
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-! # Joint prefix and next-release channels -/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open Causalean.Mathlib.Probability.Kernel.FiniteSequence

/-- The original next-release channel, with a finite input row and a released
finite-sequence history. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:P,n,i), these specify the stated inputs. -/
def releasedHistoryRowKernel {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (n : ℕ) (i : Fin n) :
    Kernel (Fin 4 × History (Z n) i.val (Nat.le_of_lt i.isLt)) (Z n i) :=
  (P.channel n i).comap
    (fun jh => (jh.1, fsHistoryToPrivate i jh.2))
    (measurable_fst.prodMk
      ((measurable_fsHistoryToPrivate i).comp measurable_snd))

/-- Adjoin a common random released prefix to each of the four current-input rows. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. [The sequential Joint Channel](goal) is determined by [the displayed parameters](hyp:P,n,i,μ). -/
def sequentialJointChannel {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (n : ℕ) (i : Fin n)
    (μ : Measure (History (Z n) i.val (Nat.le_of_lt i.isLt))) :
    Kernel (Fin 4) (History (Z n) i.val (Nat.le_of_lt i.isLt) × Z n i) :=
  (Kernel.const (Fin 4) μ).compProd (releasedHistoryRowKernel P n i)

/-- [the sequential joint channel is markov assertion](goal) holds. For [the displayed quantities and conditions](hyp:P,n,i), these specify the stated inputs. -/
lemma sequentialJointChannel_isMarkov {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (n : ℕ) (i : Fin n)
    (μ : Measure (History (Z n) i.val (Nat.le_of_lt i.isLt)))
    [IsProbabilityMeasure μ] : IsMarkovKernel (sequentialJointChannel P n i μ) := by
  letI : IsMarkovKernel (P.channel n i) := (P.privacy n).1 i
  letI : IsMarkovKernel (releasedHistoryRowKernel P n i) := by
    unfold releasedHistoryRowKernel
    infer_instance
  unfold sequentialJointChannel releasedHistoryRowKernel
  infer_instance

/-- [the sequential joint channel stationary ldp assertion](goal) holds. For [the displayed quantities and conditions](hyp:P,n,i), these specify the stated inputs. -/
lemma sequentialJointChannel_stationaryLDP {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (n : ℕ) (i : Fin n)
    (μ : Measure (History (Z n) i.val (Nat.le_of_lt i.isLt)))
    [IsProbabilityMeasure μ] :
    StationaryLDP (ε) (sequentialJointChannel P n i μ) := by
  letI : IsMarkovKernel (P.channel n i) := (P.privacy n).1 i
  letI : IsMarkovKernel (releasedHistoryRowKernel P n i) := by
    unfold releasedHistoryRowKernel
    infer_instance
  refine ⟨sequentialJointChannel_isMarkov P n i μ, ?_⟩
  intro A hA j j'
  rw [sequentialJointChannel, Kernel.compProd_apply hA,
    Kernel.compProd_apply hA]
  have hsection (a : Fin 4) : Measurable (fun h =>
      releasedHistoryRowKernel P n i (a, h) (Prod.mk h ⁻¹' A)) :=
    ((releasedHistoryRowKernel P n i).comap (fun h => (a, h))
      (measurable_const.prodMk measurable_id)).measurable_kernel_prodMk_left hA
  calc
    (∫⁻ h, releasedHistoryRowKernel P n i (j, h) (Prod.mk h ⁻¹' A) ∂μ) ≤
        ∫⁻ h, ENNReal.ofReal (Real.exp (ε)) *
          releasedHistoryRowKernel P n i (j', h) (Prod.mk h ⁻¹' A) ∂μ := by
      apply lintegral_mono
      intro h
      exact (P.privacy n).2 i (Prod.mk h ⁻¹' A)
        (hA.preimage (measurable_const.prodMk measurable_id)) j j'
        (fsHistoryToPrivate i h)
    _ = ENNReal.ofReal (Real.exp (ε)) *
        ∫⁻ h, releasedHistoryRowKernel P n i (j', h) (Prod.mk h ⁻¹' A) ∂μ := by
      rw [lintegral_const_mul _ (hsection j')]

/-- Mixing the four joint rows gives the prefix measure composed with the observed next-release kernel. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ), [the output Law sequential Joint Channel](goal).

Under the stated assumptions, the output Law sequential Joint Channel. -/
lemma outputLaw_sequentialJointChannel {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (n : ℕ) (i : Fin n)
    (μ : Measure (History (Z n) i.val (Nat.le_of_lt i.isLt)))
    [IsProbabilityMeasure μ] :
    outputLaw θ p (sequentialJointChannel P n i μ) =
      μ ⊗ₘ ((observedStageKernel P θ p n i).comap
        (fun h => ((), h)) (measurable_const.prodMk measurable_id)) := by
  classical
  letI : IsMarkovKernel (P.channel n i) := (P.privacy n).1 i
  letI : IsMarkovKernel (releasedHistoryRowKernel P n i) := by
    unfold releasedHistoryRowKernel
    infer_instance
  letI : IsMarkovKernel (observedStageKernel P θ p n i) :=
    observedStageKernel_isMarkov P θ p hp hθ n i
  ext A hA
  have hsection (j : Fin 4) : Measurable (fun h =>
      P.channel n i (j, fsHistoryToPrivate i h) (Prod.mk h ⁻¹' A)) :=
    ((releasedHistoryRowKernel P n i).comap (fun h => (j, h))
      (measurable_const.prodMk measurable_id)).measurable_kernel_prodMk_left hA
  simp_rw [outputLaw, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    sequentialJointChannel, Kernel.compProd_apply hA]
  rw [Measure.compProd_apply hA]
  change (∑ j : Fin 4, ENNReal.ofReal (piTheta θ p j) *
      ∫⁻ h, P.channel n i (j, fsHistoryToPrivate i h) (Prod.mk h ⁻¹' A) ∂μ) =
    ∫⁻ h, ∑ j : Fin 4, ENNReal.ofReal (piTheta θ p j) *
      P.channel n i (j, fsHistoryToPrivate i h) (Prod.mk h ⁻¹' A) ∂μ
  rw [lintegral_finset_sum]
  · apply Finset.sum_congr rfl
    intro j _
    rw [lintegral_const_mul _ (hsection j)]
  · intro j _
    exact measurable_const.mul (hsection j)

/-- The joint channel's directional Fisher information is bounded by the finite staircase envelope. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,heps), [the sequential Joint Channel fisher le upper Envelope](goal).

Under the stated assumptions, the sequential Joint Channel fisher le upper Envelope. -/
lemma sequentialJointChannel_fisher_le_upperEnvelope {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (n : ℕ) (i : Fin n)
    (μ : Measure (History (Z n) i.val (Nat.le_of_lt i.isLt)))
    [IsProbabilityMeasure μ]
    (θ : TrialParameter) (p t : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (heps : 0 < ε) :
    informationQuadratic
        (channelFisherInfo θ p (sequentialJointChannel P n i μ)) (direction t) ≤
      upperEnvelope θ p (ε) t := by
  let Q := sequentialJointChannel P n i μ
  have hQ : StationaryLDP (ε) Q :=
    sequentialJointChannel_stationaryLDP P n i μ
  obtain ⟨α, K, hα, hK, hfac, hpsd, hrigid⟩ :=
    staircase_refinement_interior p θ (ε) hp hθ
      (fun _ => ε) ⟨heps, fun _ => rfl⟩ Q hQ
  have hquad : informationQuadratic (channelFisherInfo θ p Q) (direction t) ≤
      informationQuadratic (informationMatrix θ p (ε) α)
        (direction t) := by
    have hz := hpsd.dotProduct_mulVec_nonneg (direction t)
    have hnonneg : 0 ≤ informationQuadratic
        (informationMatrix θ p ε α - channelFisherInfo θ p Q) (direction t) := by
      rw [show informationQuadratic
          (informationMatrix θ p ε α - channelFisherInfo θ p Q) (direction t) =
          star (direction t) ⬝ᵥ
            (informationMatrix θ p ε α - channelFisherInfo θ p Q).mulVec
              (direction t) by
        simp [informationQuadratic, Matrix.mulVec, dotProduct,
          Fin.sum_univ_two]
        ring]
      exact hz
    have heq : informationQuadratic
        (informationMatrix θ p ε α - channelFisherInfo θ p Q) (direction t) =
        informationQuadratic (informationMatrix θ p ε α) (direction t) -
          informationQuadratic (channelFisherInfo θ p Q) (direction t) := by
      unfold informationQuadratic
      simp [Fin.sum_univ_two]
      ring
    linarith
  calc
    informationQuadratic (channelFisherInfo θ p Q) (direction t) ≤
        informationQuadratic (informationMatrix θ p (ε) α)
          (direction t) := hquad
    _ = informationObjective θ p (ε) α t :=
      (informationObjective_eq_informationQuadratic θ p ε α t).symm
    _ ≤ upperEnvelope θ p (ε) t := by
      obtain ⟨β, hβ, hmax⟩ :=
        informationObjective_exists_maximizer θ p ε t heps.le
      have hub : upperEnvelope θ p ε t = informationObjective θ p ε β t := by
        unfold upperEnvelope
        apply IsGreatest.csSup_eq
        exact ⟨⟨β, hβ, rfl⟩, by
          rintro u ⟨γ, hγ, rfl⟩
          exact hmax γ hγ⟩
      rw [hub]
      exact hmax α hα

end CausalSmith.Stat.LdpAteEfficiencySurface
