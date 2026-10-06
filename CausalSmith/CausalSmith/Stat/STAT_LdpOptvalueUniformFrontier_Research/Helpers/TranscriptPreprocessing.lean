module
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Protocol
/-!
# Measurable transcript laws

Joint measurability of finite sequential transcript laws and their decision observations.
-/
public section
noncomputable section
open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability.Kernel.FiniteSequence
open scoped ENNReal
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier
variable {n : ℕ} {α : Type} [MeasurableSpace α]
/-- When the prefix length [does not exceed the sample size](hyp:hk), prefix laws are
[measurable in the fixed participant inputs and public seed](goal). -/
-- @node: measurable_protocol_prefixLaw
@[fun_prop] lemma measurable_protocol_prefixLaw (Q : LocalProtocol n α) (k : ℕ) (hk : k ≤ n) :
    Measurable (fun x : Fin n → α × Q.Seed => prefixLaw Q.kernels x k hk) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    let κ : Kernel (Fin n → α × Q.Seed) (ProtocolHistory Q ⟨k, by omega⟩) :=
      ⟨fun x => prefixLaw Q.kernels x k (Nat.le_of_succ_le hk), ih _⟩
    haveI : IsMarkovKernel κ := ⟨fun x => isProbabilityMeasure_prefixLaw Q.kernels Q.markov x k _⟩
    let η := (Q.kernels (nextIndex hk)).comap
      (fun w : (Fin n → α × Q.Seed) × History Q.Message k (Nat.le_of_succ_le hk) =>
        (w.1 (nextIndex hk), w.2)) (by fun_prop)
    have heq : (fun x : Fin n → α × Q.Seed => prefixLaw Q.kernels x (k+1) hk) =
        ((κ ⊗ₖ η).map (fun p => snoc hk p.1 p.2)) := by
      funext x
      haveI := isProbabilityMeasure_prefixLaw Q.kernels Q.markov x k (Nat.le_of_succ_le hk)
      rw [prefixLaw_succ, Kernel.map_apply _ (measurable_snoc hk)]
      congr 1
      ext E hE
      rw [Measure.compProd_apply hE, Kernel.compProd_apply hE]
      rfl
    rw [heq]
    exact Kernel.measurable _
/-- For every protocol, fixed transcript laws are [jointly measurable in the records and public
seed](goal). -/
-- @node: measurable_fixedTranscriptLaw
@[fun_prop] lemma measurable_fixedTranscriptLaw (Q : LocalProtocol n α) :
    Measurable (fun w : (Fin n → α) × Q.Seed => fixedTranscriptLaw Q w.1 w.2) := by
  exact (measurable_protocol_prefixLaw Q n le_rfl).comp (by fun_prop)
/-- For every protocol, appending the seed and analyst randomizer gives [jointly measurable
decision rows](goal). -/
-- @node: measurable_protocol_decisionRows
@[fun_prop] lemma measurable_protocol_decisionRows (Q : LocalProtocol n α) :
    Measurable (fun w : (Fin n → α) × Q.Seed × ℝ =>
      (fixedTranscriptLaw Q w.1 w.2.1).map (fun z => (z,w.2.1,w.2.2))) := by
  let κ : Kernel ((Fin n → α) × Q.Seed × ℝ) (ProtocolTranscript Q) :=
    ⟨fun w => fixedTranscriptLaw Q w.1 w.2.1,
      (measurable_fixedTranscriptLaw Q).comp
        (show Measurable (fun w : (Fin n → α) × Q.Seed × ℝ => (w.1,w.2.1))
          by fun_prop)⟩
  haveI : IsMarkovKernel κ := ⟨fun w => by
    exact isProbabilityMeasure_transcriptLaw Q.kernels Q.markov (fun i => (w.1 i,w.2.1))⟩
  let η : Kernel (((Fin n → α) × Q.Seed × ℝ) × ProtocolTranscript Q) (DecisionSpace Q) :=
    Kernel.deterministic (fun p => (p.2,p.1.2.1,p.1.2.2)) (by fun_prop)
  have heq : (fun w : (Fin n → α) × Q.Seed × ℝ =>
      (fixedTranscriptLaw Q w.1 w.2.1).map (fun z => (z,w.2.1,w.2.2))) =
      ((κ ⊗ₖ η).map Prod.snd) := by
    funext w
    rw [Kernel.map_apply _ measurable_snd]
    ext E hE
    rw [Measure.map_apply (by fun_prop) hE,
      Measure.map_apply measurable_snd hE, Kernel.compProd_apply (measurable_snd hE)]
    simp only [η, Kernel.deterministic_apply]
    change _ = ∫⁻ z, (Measure.dirac (z,w.2.1,w.2.2)) E ∂κ w
    simp only [Measure.dirac_apply' _ hE]
    change _ = ∫⁻ z, Set.indicator ((fun z => (z,w.2.1,w.2.2)) ⁻¹' E) 1 z ∂κ w
    rw [lintegral_indicator
      ((show Measurable (fun z : ProtocolTranscript Q => (z,w.2.1,w.2.2))
        by fun_prop) hE)]
    simp [κ]
  rw [heq]
  exact Kernel.measurable _
end CausalSmith.Stat.LdpOptvalueUniformFrontier
