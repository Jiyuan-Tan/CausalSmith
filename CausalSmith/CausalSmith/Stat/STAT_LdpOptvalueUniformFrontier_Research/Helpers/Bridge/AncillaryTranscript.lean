module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Bridge.AncillarySample

/-!
# Integrating ancillary bits through adaptive transcripts

Independent fair reconstruction bits can be averaged one stage at a time,
including when the next channel depends on the preceding messages.
-/

public section

noncomputable section
open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability.Kernel.FiniteSequence
open scoped ENNReal BigOperators
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier
variable {n d : ℕ}

/-- [Flipping any one fair assignment preserves the entire independent bit law](goal). -/
-- @node: ancillaryBits_flip_map
lemma ancillaryBits_flip_map (i : Fin n) :
    (Measure.pi (fun _ : Fin n => ancillaryBitLaw)).map
      (fun a => Function.update a i (!(a i))) =
      Measure.pi (fun _ : Fin n => ancillaryBitLaw) := by
  have hbit : ancillaryBitLaw.map Bool.not = ancillaryBitLaw := by
    apply Measure.ext_of_singleton
    intro b
    rw [Measure.map_apply (by fun_prop) (MeasurableSet.singleton _)]
    have hp : Bool.not ⁻¹' {b} = {!b} := by
      ext a
      cases a <;> cases b <;> simp
    rw [hp, ancillaryBitLaw_singleton, ancillaryBitLaw_singleton]
  have hfun : (fun a : Fin n → Bool => Function.update a i (!(a i))) =
      (fun a j => (if j = i then Bool.not else id) (a j)) := by
    funext a j
    by_cases hj : j = i <;> simp [hj]
  rw [hfun, Measure.pi_map_pi (fun j => (show Measurable
    (if j = i then Bool.not else (id : Bool → Bool)) by
      split <;> fun_prop).aemeasurable)]
  congr 1
  funext j
  split <;> simp [hbit]

/-- Assume [the function f](hyp:f). [Resampling a single independent fair bit leaves every nonnegative expectation unchanged](goal). -/
-- @node: ancillaryBits_lintegral_resample
lemma ancillaryBits_lintegral_resample (i : Fin n) (f : (Fin n → Bool) → ℝ≥0∞) :
    (∫⁻ a, f a ∂Measure.pi (fun _ : Fin n => ancillaryBitLaw)) =
      ∫⁻ a, ENNReal.ofReal (1/2 : ℝ) * f (Function.update a i false) +
        ENNReal.ofReal (1/2 : ℝ) * f (Function.update a i true)
        ∂Measure.pi (fun _ : Fin n => ancillaryBitLaw) := by
  have hm : Measurable f := measurable_of_countable _
  have hf : (∫⁻ a, f (Function.update a i (!(a i)))
      ∂Measure.pi (fun _ : Fin n => ancillaryBitLaw)) =
      ∫⁻ a, f a ∂Measure.pi (fun _ : Fin n => ancillaryBitLaw) := by
    rw [← lintegral_map hm (show Measurable
      (fun a : Fin n → Bool => Function.update a i (!(a i))) by fun_prop),
      ancillaryBits_flip_map]
  have hp (a : Fin n → Bool) :
      ENNReal.ofReal (1/2 : ℝ) * f (Function.update a i false) +
        ENNReal.ofReal (1/2 : ℝ) * f (Function.update a i true) =
      ENNReal.ofReal (1/2 : ℝ) * f a +
        ENNReal.ofReal (1/2 : ℝ) * f (Function.update a i (!(a i))) := by
    have hu : Function.update a i (a i) = a := Function.update_eq_self i a
    cases ha : a i <;> simp_all only [Bool.not_false, Bool.not_true, add_comm]
  simp_rw [hp]
  rw [lintegral_add_left (by fun_prop), lintegral_const_mul _ hm,
    lintegral_const_mul _ (by fun_prop), hf, ← add_mul]
  norm_num [← ENNReal.ofReal_add]

set_option backward.isDefEq.respectTransparency false in
/-- Assume [order no larger than the sample size](hyp:hk), [the function f](hyp:f), and [measurability of f](hyp:hf). [Averaging independent ancillary assignments commutes with every adaptive prefix](goal). -/
-- @node: averagedProtocol_prefix_lintegral
lemma averagedProtocol_prefix_lintegral (Q : LocalProtocol n (ObsRecord d))
    (v : Fin n → PairedSymbol d) (r : Q.Seed) (k : ℕ) (hk : k ≤ n)
    (f : History Q.Message k hk → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ a, ∫⁻ eta, f eta ∂prefixLaw Q.kernels
      (fun i => (recoverObs (v i) (a i),r)) k hk
      ∂Measure.pi (fun _ : Fin n => ancillaryBitLaw)) =
      ∫⁻ eta, f eta ∂prefixLaw (averagedProtocol Q).kernels
        (fun i => (v i,r)) k hk := by
  induction k with
  | zero =>
    change (∫⁻ a : Fin n → Bool, ∫⁻ eta, f eta ∂Measure.dirac (fun j : Fin 0 => j.elim0)
      ∂Measure.pi (fun _ => ancillaryBitLaw)) = _
    rw [lintegral_const, measure_univ, mul_one]
    rfl
  | succ k ih =>
    let i := nextIndex hk
    let mu (a : Fin n → Bool) := prefixLaw Q.kernels
      (fun j => (recoverObs (v j) (a j),r)) k (Nat.le_of_succ_le hk)
    haveI (a : Fin n → Bool) : IsProbabilityMeasure (mu a) :=
      isProbabilityMeasure_prefixLaw Q.kernels Q.markov _ _ _
    let K : Kernel (History Q.Message k (Nat.le_of_succ_le hk)) (Q.Message i) :=
      (averagedKernel Q i).comap (fun eta => ((v i,r),eta)) (by fun_prop)
    haveI : IsMarkovKernel K := by
      dsimp [K]; haveI := averagedKernel_markov Q i; infer_instance
    let g : History Q.Message k (Nat.le_of_succ_le hk) → ℝ≥0∞ :=
      fun eta => ∫⁻ z, f (snoc hk eta z) ∂K eta
    have hg : Measurable g := by
      exact Measurable.lintegral_kernel_prod_right' (κ := K)
        (hf.comp (measurable_snoc hk))
    rw [ancillaryBits_lintegral_resample i]
    have hstep (a : Fin n → Bool) :
        ENNReal.ofReal (1/2 : ℝ) *
          (∫⁻ eta, f eta ∂prefixLaw Q.kernels
            (fun j => (recoverObs (v j) (Function.update a i false j),r)) (k+1) hk) +
        ENNReal.ofReal (1/2 : ℝ) *
          (∫⁻ eta, f eta ∂prefixLaw Q.kernels
            (fun j => (recoverObs (v j) (Function.update a i true j),r)) (k+1) hk) =
        ∫⁻ eta, g eta ∂mu a := by
      have hu (b : Bool) :
          (fun j => (recoverObs (v j) (Function.update a i b j),r)) =
          Function.update (fun j => (recoverObs (v j) (a j),r)) i
            (recoverObs (v i) b,r) := by
        funext j
        by_cases hj : j = i <;> simp [hj]
      rw [hu false, hu true]
      have h := averagedKernel_prefix_step Q
        (fun j => (recoverObs (v j) (a j),r)) k hk (v i) r
      have hl := congrArg (fun m => ∫⁻ eta, f eta ∂m) h
      rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
        lintegral_map hf (measurable_snoc hk)] at hl
      change (∫⁻ p, f (snoc hk p.1 p.2) ∂(mu a ⊗ₘ K)) = _ at hl
      rw [Measure.lintegral_compProd (μ := mu a) (κ := K)
        (show Measurable (fun p => f (snoc hk p.1 p.2)) from hf.comp (measurable_snoc hk))] at hl
      exact hl.symm
    simp_rw [hstep]
    rw [ih (Nat.le_of_succ_le hk) g hg, prefixLaw_succ]
    change (∫⁻ eta, g eta ∂prefixLaw (averagedProtocol Q).kernels
      (fun i => (v i,r)) k (Nat.le_of_succ_le hk)) =
      ∫⁻ eta, f eta ∂(prefixLaw (averagedProtocol Q).kernels
        (fun i => (v i,r)) k (Nat.le_of_succ_le hk) ⊗ₘ K).map
          (fun p => snoc hk p.1 p.2)
    haveI := isProbabilityMeasure_prefixLaw (averagedProtocol Q).kernels
      (averagedProtocol Q).markov (fun i => (v i,r)) k (Nat.le_of_succ_le hk)
    simp only [averagedProtocol] at *
    rw [lintegral_map hf (measurable_snoc hk),
      Measure.lintegral_compProd (κ := K)
        (show Measurable (fun p => f (snoc hk p.1 p.2)) from hf.comp (measurable_snoc hk))]

/-- Assume [the function f](hyp:f) and [measurability of f](hyp:hf). [The full transcript expectation averages the independent reconstruction bits](goal). -/
-- @node: averagedProtocol_fixedTranscript_lintegral
lemma averagedProtocol_fixedTranscript_lintegral (Q : LocalProtocol n (ObsRecord d))
    (v : Fin n → PairedSymbol d) (r : Q.Seed)
    (f : ProtocolTranscript Q → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ a, ∫⁻ z, f z ∂fixedTranscriptLaw Q
      (fun i => recoverObs (v i) (a i)) r
      ∂Measure.pi (fun _ : Fin n => ancillaryBitLaw)) =
      ∫⁻ z, f z ∂fixedTranscriptLaw (averagedProtocol Q) v r :=
  averagedProtocol_prefix_lintegral Q v r n le_rfl f hf

set_option backward.isDefEq.respectTransparency false in
/-- [Averaging the ancillary bits preserves decisions jointly with both independent coins](goal). -/
-- @node: averagedProtocol_reconstructed_decisionLaw
lemma averagedProtocol_reconstructed_decisionLaw (Q : LocalProtocol n (ObsRecord d))
    (p : Measure (PairedSymbol d)) [IsProbabilityMeasure p] :
    (((Measure.pi (fun _ : Fin n => p)).prod
      (Measure.pi (fun _ : Fin n => ancillaryBitLaw))).prod
      (Q.seedLaw.prod uniform01)).bind (fun w =>
        (fixedTranscriptLaw Q (fun i => recoverObs (w.1.1 i) (w.1.2 i)) w.2.1).map
          (fun z => (z,w.2.1,w.2.2))) =
      canonicalDecisionLaw (averagedProtocol Q) p := by
  haveI : IsProbabilityMeasure uniform01 := ⟨by
    simp [uniform01, Measure.restrict_apply, Real.volume_Icc]⟩
  ext E hE
  let f (w : ((Fin n → PairedSymbol d) × (Fin n → Bool)) × Q.Seed × ℝ) :=
    (fixedTranscriptLaw Q (fun i => recoverObs (w.1.1 i) (w.1.2 i)) w.2.1).map
      (fun z => (z,w.2.1,w.2.2))
  have hf : Measurable f := (measurable_protocol_decisionRows Q).comp
    (show Measurable (fun w : ((Fin n → PairedSymbol d) × (Fin n → Bool)) × Q.Seed × ℝ =>
      ((fun i => recoverObs (w.1.1 i) (w.1.2 i)),w.2)) by fun_prop)
  rw [Measure.bind_apply hE hf.aemeasurable]
  unfold canonicalDecisionLaw
  rw [Measure.bind_apply hE (measurable_protocol_decisionRows (averagedProtocol Q)).aemeasurable]
  change (∫⁻ w, f w E ∂((Measure.pi (fun _ : Fin n => p)).prod
    (Measure.pi (fun _ : Fin n => ancillaryBitLaw))).prod (Q.seedLaw.prod uniform01)) =
    ∫⁻ w : (Fin n → PairedSymbol d) × Q.Seed × ℝ,
      ((transcriptLaw (averagedKernel Q) (fun i => (w.1 i,w.2.1))).map
        (fun z => (z,w.2.1,w.2.2))) E
      ∂(Measure.pi (fun _ : Fin n => p)).prod (Q.seedLaw.prod uniform01)
  rw [lintegral_prod (fun w => f w E) ((Measure.measurable_coe hE).comp hf).aemeasurable]
  rw [lintegral_prod _ (measurable_of_countable _).aemeasurable, lintegral_prod _ (by
    exact ((Measure.measurable_coe hE).comp
      (measurable_protocol_decisionRows (averagedProtocol Q))).aemeasurable)]
  apply lintegral_congr
  intro v
  have hswap : Measurable (fun w : (Fin n → Bool) × (Q.Seed × ℝ) => f ((v,w.1),w.2) E) :=
    ((Measure.measurable_coe hE).comp hf).comp
      (show Measurable (fun w : (Fin n → Bool) × (Q.Seed × ℝ) => ((v,w.1),w.2)) by fun_prop)
  rw [lintegral_lintegral_swap hswap.aemeasurable]
  apply lintegral_congr
  intro ru
  have hmz : Measurable (fun z : ProtocolTranscript Q => (z,ru.1,ru.2)) := by fun_prop
  simp only [f, Measure.map_apply hmz hE]
  have hm : Measurable (fun z : ProtocolTranscript Q =>
      Set.indicator ((fun z => (z,ru.1,ru.2)) ⁻¹' E) (fun _ => (1 : ℝ≥0∞)) z) := by
    exact measurable_const.indicator (hE.preimage hmz)
  have h := averagedProtocol_fixedTranscript_lintegral Q v ru.1 _ hm
  change (∫⁻ a, ∫⁻ z, Set.indicator ((fun z => (z,ru.1,ru.2)) ⁻¹' E)
    (fun _ => (1 : ℝ≥0∞)) z ∂fixedTranscriptLaw Q (fun i => recoverObs (v i) (a i)) ru.1
    ∂Measure.pi (fun _ : Fin n => ancillaryBitLaw)) =
      ∫⁻ z, Set.indicator ((fun z => (z,ru.1,ru.2)) ⁻¹' E) (fun _ => (1 : ℝ≥0∞)) z
        ∂transcriptLaw (averagedKernel Q) (fun i => (v i,ru.1)) at h
  simpa only [lintegral_indicator (hE.preimage hmz), lintegral_one,
    Measure.restrict_apply_univ] using h

end CausalSmith.Stat.LdpOptvalueUniformFrontier
