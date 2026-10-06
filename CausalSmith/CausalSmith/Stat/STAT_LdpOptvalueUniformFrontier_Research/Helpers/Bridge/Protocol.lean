module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Decision
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.PairedTV
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.SymmetricLaw
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.TranscriptPreprocessing
public import Causalean.Stat.Minimax.TotalVariation
public import Causalean.Tactic.IntegralLinearity
public import Mathlib.Probability.Kernel.Basic

/-!
# Ancillary protocol preprocessing

Causal identification, symmetric-law certificates, and private experiment equivalence.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology Classical

namespace CausalSmith.Stat.LdpOptvalueUniformFrontier


variable {n d : ℕ}
/-- Fix [the parameter v](hyp:v) and [the binary value a](hyp:a). [Reconstruct the original observation using an ancillary assignment bit](goal). -/
def recoverObs (v : PairedSymbol d) (a : Bool) : ObsRecord d :=
  (v.1,a,if v.2 then a else !a)
/-- For a protocol, participant index, and ancillary bit, the recovered-input map is
[measurable](goal). -/
-- @node: measurable_recoverInput
@[fun_prop] lemma measurable_recoverInput (Q : LocalProtocol n (ObsRecord d))
    (i : Fin n) (a : Bool) :
    Measurable (fun w : (PairedSymbol d × Q.Seed) × ProtocolHistory Q i =>
      ((recoverObs w.1.1 a,w.1.2),w.2)) := by
  fun_prop
/-- Fix [the local protocol Q](hyp:Q), [the participant index](hyp:i), and [the binary value a](hyp:a). [Original stage kernel evaluated on a recovered ancillary assignment](goal). -/
def recoveredKernel (Q : LocalProtocol n (ObsRecord d)) (i : Fin n) (a : Bool) :
    Kernel ((PairedSymbol d × Q.Seed) × ProtocolHistory Q i) (Q.Message i) :=
  (Q.kernels i).comap (fun w => ((recoverObs w.1.1 a,w.1.2),w.2))
    (measurable_recoverInput Q i a)
/-- Fix [the local protocol Q](hyp:Q), [the participant index](hyp:i), and [the parameter w](hyp:w). [Fair mixture of original-record rows at a paired input](goal). -/
def averagedRows (Q : LocalProtocol n (ObsRecord d)) (i : Fin n)
    (w : (PairedSymbol d × Q.Seed) × ProtocolHistory Q i) : Measure (Q.Message i) :=
  ENNReal.ofReal (1/2 : ℝ) • recoveredKernel Q i false w +
    ENNReal.ofReal (1/2 : ℝ) • recoveredKernel Q i true w
/-- For a protocol and participant index, the ancillary fair mixture is [jointly measurable](goal). -/
-- @node: averagedRows_measurable
@[fun_prop] lemma averagedRows_measurable (Q : LocalProtocol n (ObsRecord d)) (i : Fin n) :
    Measurable (averagedRows Q i) := by
  apply Measure.measurable_of_measurable_coe
  intro E hE
  simp only [averagedRows, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  exact (measurable_const.mul ((recoveredKernel Q i false).measurable_coe hE)).add
    (measurable_const.mul ((recoveredKernel Q i true).measurable_coe hE))
/-- Fix [the local protocol Q](hyp:Q) and [the participant index](hyp:i). [Averaged paired-input kernel with the ancillary fair bit integrated out](goal). -/
def averagedKernel (Q : LocalProtocol n (ObsRecord d)) (i : Fin n) :
    Kernel ((PairedSymbol d × Q.Seed) × ProtocolHistory Q i) (Q.Message i) :=
  ⟨averagedRows Q i, averagedRows_measurable Q i⟩
/-- [The average remains a Markov kernel](goal). -/
-- @node: averagedKernel_markov
lemma averagedKernel_markov (Q : LocalProtocol n (ObsRecord d)) (i : Fin n) :
    IsMarkovKernel (averagedKernel Q i) := by
  constructor
  intro w
  constructor
  change (ENNReal.ofReal (1/2 : ℝ) • recoveredKernel Q i false w +
    ENNReal.ofReal (1/2 : ℝ) • recoveredKernel Q i true w) Set.univ = 1
  have hfalse : IsProbabilityMeasure (recoveredKernel Q i false w) := by
    unfold recoveredKernel
    infer_instance
  have htrue : IsProbabilityMeasure (recoveredKernel Q i true w) := by
    unfold recoveredKernel
    infer_instance
  simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num
/-- Fix [the local protocol Q](hyp:Q). [Averaged paired-input protocol, retaining the same seed and message spaces](goal). -/
def averagedProtocol (Q : LocalProtocol n (ObsRecord d)) : LocalProtocol n (PairedSymbol d) where
  Seed := Q.Seed
  seedMeasurable := Q.seedMeasurable
  seedStandard := Q.seedStandard
  seedLaw := Q.seedLaw
  seedProbability := Q.seedProbability
  Message := Q.Message
  messageMeasurable := Q.messageMeasurable
  messageStandard := Q.messageStandard
  kernels := averagedKernel Q
  markov := averagedKernel_markov Q
/-- For a paired protocol and participant index, the signed-observation pullback map is
[measurable](goal). -/
-- @node: measurable_signedInput
@[fun_prop] lemma measurable_signedInput (K : LocalProtocol n (PairedSymbol d)) (i : Fin n) :
    Measurable (fun w : (ObsRecord d × K.Seed) × ProtocolHistory K i =>
      ((signedObserve w.1.1,w.1.2),w.2)) := by
  fun_prop
/-- Fix [the local protocol K](hyp:K) and [the participant index](hyp:i). [Pulled-back original-record kernel](goal). -/
def pulledKernel (K : LocalProtocol n (PairedSymbol d)) (i : Fin n) :
    Kernel ((ObsRecord d × K.Seed) × ProtocolHistory K i) (K.Message i) :=
  (K.kernels i).comap (fun w => ((signedObserve w.1.1,w.1.2),w.2))
    (measurable_signedInput K i)
/-- [Pullback Markov certificate](goal). -/
-- @node: pulledKernel_markov
lemma pulledKernel_markov (K : LocalProtocol n (PairedSymbol d)) (i : Fin n) :
    IsMarkovKernel (pulledKernel K i) := by
  unfold pulledKernel
  infer_instance
/-- Fix [the local protocol K](hyp:K). [Deterministic signed preprocessing in the reverse direction](goal). -/
def pulledProtocol (K : LocalProtocol n (PairedSymbol d)) : LocalProtocol n (ObsRecord d) where
  Seed := K.Seed
  seedMeasurable := K.seedMeasurable
  seedStandard := K.seedStandard
  seedLaw := K.seedLaw
  seedProbability := K.seedProbability
  Message := K.Message
  messageMeasurable := K.messageMeasurable
  messageStandard := K.messageStandard
  kernels := pulledKernel K
  markov := pulledKernel_markov K
/-- Assume [the full participant record](hyp:hQ). [Averaging the ancillary assignment preserves the all-history privacy inequality](goal). -/
-- @node: averagedProtocol_privacy
lemma averagedProtocol_privacy (Q : LocalProtocol n (ObsRecord d)) (eps : ℝ)
    (hQ : FullRecordPrivacy Q eps) : FullRecordPrivacy (averagedProtocol Q) eps := by
  unfold FullRecordPrivacy
  dsimp only [averagedProtocol]
  intro i v v' eta r E hE
  change (averagedRows Q i ((v,r),eta)) E ≤
    ENNReal.ofReal (Real.exp eps) * (averagedRows Q i ((v',r),eta)) E
  simp only [averagedRows, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    recoveredKernel, Kernel.comap_apply, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  have hf := hQ i (recoverObs v false) (recoverObs v' false) eta r E hE
  have ht := hQ i (recoverObs v true) (recoverObs v' true) eta r E hE
  calc
    _ ≤ ENNReal.ofReal (1/2 : ℝ) *
          (ENNReal.ofReal (Real.exp eps) * Q.kernels i ((recoverObs v' false,r),eta) E) +
        ENNReal.ofReal (1/2 : ℝ) *
          (ENNReal.ofReal (Real.exp eps) * Q.kernels i ((recoverObs v' true,r),eta) E) :=
      add_le_add (by gcongr) (by gcongr)
    _ = _ := by ring

/-- Assume [the stated privacy condition for the protocol](hyp:hQ). [Averaging the ancillary assignment preserves history independence](goal). -/
-- @node: averagedProtocol_noninteraction
lemma averagedProtocol_noninteraction (Q : LocalProtocol n (ObsRecord d))
    (hQ : Noninteraction Q) : Noninteraction (averagedProtocol Q) := by
  intro i v eta eta' r
  change averagedRows Q i ((v,r),eta) = averagedRows Q i ((v,r),eta')
  simp only [averagedRows, recoveredKernel, Kernel.comap_apply]
  rw [hQ i (recoverObs v false) eta eta' r, hQ i (recoverObs v true) eta eta' r]

/-- Assume [the full participant record](hyp:hK). [Signed deterministic preprocessing preserves the all-history privacy inequality](goal). -/
-- @node: pulledProtocol_privacy
lemma pulledProtocol_privacy (K : LocalProtocol n (PairedSymbol d)) (eps : ℝ)
    (hK : FullRecordPrivacy K eps) : FullRecordPrivacy (pulledProtocol K) eps := by
  intro i o o' eta r E hE
  exact hK i (signedObserve o) (signedObserve o') eta r E hE

/-- Assume [the stated privacy condition for the protocol](hyp:hK). [Signed deterministic preprocessing preserves history independence](goal). -/
-- @node: pulledProtocol_noninteraction
lemma pulledProtocol_noninteraction (K : LocalProtocol n (PairedSymbol d))
    (hK : Noninteraction K) : Noninteraction (pulledProtocol K) := by
  intro i o eta eta' r
  exact hK i (signedObserve o) eta eta' r

/-- [Both directions of the ancillary-bit construction preserve the two protocol classes](goal). -/
-- @node: signed_protocol_classes
lemma signed_protocol_classes (eps : ℝ) :
    (∀ Q : LocalProtocol n (ObsRecord d),
      (SequentialClass Q eps → SequentialClass (averagedProtocol Q) eps) ∧
      (NoninteractiveClass Q eps → NoninteractiveClass (averagedProtocol Q) eps)) ∧
    (∀ K : LocalProtocol n (PairedSymbol d),
      (SequentialClass K eps → SequentialClass (pulledProtocol K) eps) ∧
      (NoninteractiveClass K eps → NoninteractiveClass (pulledProtocol K) eps)) := by
  constructor
  · intro Q
    constructor
    · intro hQ
      exact ⟨averagedProtocol_privacy Q eps hQ.privacy⟩
    · intro hQ
      exact ⟨averagedProtocol_privacy Q eps hQ.privacy,
        averagedProtocol_noninteraction Q hQ.noninteraction⟩
  · intro K
    constructor
    · intro hK
      exact ⟨pulledProtocol_privacy K eps hK.privacy⟩
    · intro hK
      exact ⟨pulledProtocol_privacy K eps hK.privacy,
        pulledProtocol_noninteraction K hK.noninteraction⟩

/-- [Recovering an observation gives its specified paired input back](goal). -/
-- @node: signedObserve_recoverObs
lemma signedObserve_recoverObs (v : PairedSymbol d) (a : Bool) :
    signedObserve (recoverObs v a) = v := by
  rcases v with ⟨j,s⟩
  cases s <;> cases a <;> rfl

/-- [The observed outcome sign is reconstructed from the signed observation and assignment](goal). -/
-- @node: outcome_sign_reconstruction
lemma outcome_sign_reconstruction (w : FullRecord d) :
    signVal (outcome w) = obsSign (observe w) * signVal (arm w) := by
  rcases w with ⟨j,a,y,y0,y1⟩
  cases a <;> cases y <;> norm_num [outcome, obsSign, observe, arm, signVal]

/-- Assume [the stated htheta condition](hyp:htheta). [The recovered original-record atom has exactly half its paired-input mass. [](](goal). -/
-- @node: symmetricLaw_observed_recover_real
lemma symmetricLaw_observed_recover_real (theta : Fin d → ℝ)
    (htheta : theta ∈ parameterCube d) (v : PairedSymbol d) (a : Bool) :
    (observedLaw (symmetricLaw theta)).real {recoverObs v a} =
      (pairedLaw theta).real {v}/2 := by
  rw [observedLaw, Measure.real, Measure.map_apply (by fun_prop)
    (MeasurableSet.singleton _)]
  change (symmetricLaw theta).real (observe ⁻¹' {recoverObs v a}) = _
  have hevent : observe ⁻¹' {recoverObs v a} =
      {w | cell w = v.1 ∧ signedObserve (observe w) = v ∧ arm w = a} := by
    ext w
    rcases v with ⟨j,s⟩
    rcases w with ⟨j',a',y,y0,y1⟩
    cases s <;> cases a <;> cases a' <;> cases y <;>
      simp [observe, recoverObs, signedObserve, cell, arm]
  rw [hevent]
  exact symmetricLaw_ancillary theta htheta v.1 v.2 a

/-- [Every observed atom is reconstructed from its signed input and assignment](goal). -/
-- @node: recoverObs_signedObserve
lemma recoverObs_signedObserve (o : ObsRecord d) :
    recoverObs (signedObserve o) o.2.1 = o := by
  rcases o with ⟨j,a,y⟩
  cases a <;> cases y <;> rfl

/-- Assume [the stated htheta condition](hyp:htheta) and [positive dimension](hyp:hd). [Original-record singleton probabilities factor into paired mass and a fair bit](goal). -/
-- @node: symmetricLaw_observed_singleton
lemma symmetricLaw_observed_singleton (theta : Fin d → ℝ)
    (htheta : theta ∈ parameterCube d) (hd : 0 < d) (o : ObsRecord d) :
    observedLaw (symmetricLaw theta) {o} =
      ENNReal.ofReal (1/2 : ℝ) * pairedLaw theta {signedObserve o} := by
  haveI := symmetricLaw_probability theta htheta hd
  haveI : IsProbabilityMeasure (observedLaw (symmetricLaw theta)) :=
    Measure.isProbabilityMeasure_map (show Measurable observe by fun_prop).aemeasurable
  haveI : IsProbabilityMeasure (pairedLaw theta) :=
    pairedFamily_subset_simplex hd (Set.mem_image_of_mem pairedLaw htheta)
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (by finiteness)).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num)]
  change (observedLaw (symmetricLaw theta)).real {o} =
    (1/2 : ℝ) * (pairedLaw theta).real {signedObserve o}
  have h := symmetricLaw_observed_recover_real theta htheta (signedObserve o) o.2.1
  rw [recoverObs_signedObserve] at h
  linarith

/-- Assume [the stated htheta condition](hyp:htheta) and [positive dimension](hyp:hd). [At every history and seed, integrating the original row equals integrating its ancillary-bit average against the paired law. This is the one-stage experiment identity](goal). -/
-- @node: averagedKernel_integrated_row
lemma averagedKernel_integrated_row (Q : LocalProtocol n (ObsRecord d))
    (theta : Fin d → ℝ) (htheta : theta ∈ parameterCube d) (hd : 0 < d)
    (i : Fin n) (eta : ProtocolHistory Q i) (r : Q.Seed)
    (E : Set (Q.Message i)) :
    (∫⁻ o, Q.kernels i ((o,r),eta) E ∂observedLaw (symmetricLaw theta)) =
      ∫⁻ v, averagedKernel Q i ((v,r),eta) E ∂pairedLaw theta := by
  rw [lintegral_fintype, lintegral_fintype]
  simp_rw [symmetricLaw_observed_singleton theta htheta hd]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, averagedKernel, averagedRows,
    Kernel.coe_mk, Measure.add_apply, Measure.smul_apply, smul_eq_mul, recoveredKernel,
    Kernel.comap_apply, signedObserve, recoverObs]
  simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.not_true,
    show (true == true) = true from rfl, show (true == false) = false from rfl,
    show (false == true) = false from rfl, show (false == false) = true from rfl]
  ring

/-- Assume [the stated htheta condition](hyp:htheta) and [positive dimension](hyp:hd). [Integrating out the next iid participant gives the same message measure in both experiments, with no restriction on the history or public seed](goal). -/
-- @node: averagedKernel_marginal_messageLaw
lemma averagedKernel_marginal_messageLaw (Q : LocalProtocol n (ObsRecord d))
    (theta : Fin d → ℝ) (htheta : theta ∈ parameterCube d) (hd : 0 < d)
    (i : Fin n) (eta : ProtocolHistory Q i) (r : Q.Seed) :
    (observedLaw (symmetricLaw theta)).bind (fun o => Q.kernels i ((o,r),eta)) =
      (pairedLaw theta).bind (fun v => averagedKernel Q i ((v,r),eta)) := by
  ext E hE
  rw [Measure.bind_apply hE (by fun_prop), Measure.bind_apply hE (by fun_prop)]
  exact averagedKernel_integrated_row Q theta htheta hd i eta r E

/-- Assume [order no larger than the sample size](hyp:hk) and [the function hxy](hyp:hxy). [An adaptive prefix uses only records from participants already queried](goal). -/
-- @node: protocol_prefixLaw_congr_inputs
lemma protocol_prefixLaw_congr_inputs {α : Type} [MeasurableSpace α]
    (Q : LocalProtocol n α) (x y : Fin n → α × Q.Seed)
    (k : ℕ) (hk : k ≤ n) (hxy : ∀ i : Fin n, i.val < k → x i = y i) :
    Causalean.Mathlib.Probability.Kernel.FiniteSequence.prefixLaw Q.kernels x k hk =
      Causalean.Mathlib.Probability.Kernel.FiniteSequence.prefixLaw Q.kernels y k hk := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Causalean.Mathlib.Probability.Kernel.FiniteSequence.prefixLaw_succ,
      Causalean.Mathlib.Probability.Kernel.FiniteSequence.prefixLaw_succ,
      ih (Nat.le_of_succ_le hk) (fun i hi => hxy i (by omega))]
    have hnext := hxy (Causalean.Mathlib.Probability.Kernel.FiniteSequence.nextIndex hk) (by
      simp [Causalean.Mathlib.Probability.Kernel.FiniteSequence.nextIndex])
    simp only [hnext]

/-- Assume [one plus the stage index no larger than the sample size](hyp:hk). [Changing the next participant cannot change the preceding adaptive history law](goal). -/
-- @node: protocol_prefixLaw_update_next
lemma protocol_prefixLaw_update_next {α : Type} [MeasurableSpace α]
    (Q : LocalProtocol n α) (x : Fin n → α × Q.Seed)
    (k : ℕ) (hk : k + 1 ≤ n) (v : α × Q.Seed) :
    Causalean.Mathlib.Probability.Kernel.FiniteSequence.prefixLaw Q.kernels
      (Function.update x (Causalean.Mathlib.Probability.Kernel.FiniteSequence.nextIndex hk) v)
      k (Nat.le_of_succ_le hk) =
    Causalean.Mathlib.Probability.Kernel.FiniteSequence.prefixLaw Q.kernels x
      k (Nat.le_of_succ_le hk) := by
  apply protocol_prefixLaw_congr_inputs
  intro i hi
  apply Function.update_of_ne
  intro heq
  have := congrArg Fin.val heq
  simp [Causalean.Mathlib.Probability.Kernel.FiniteSequence.nextIndex] at this
  omega

/-- [Averaging the ancillary assignment at a next step commutes with extending any previous history law, including an adaptive law](goal). -/
-- @node: averagedKernel_extend_history
lemma averagedKernel_extend_history (Q : LocalProtocol n (ObsRecord d))
    (i : Fin n) (mu : Measure (ProtocolHistory Q i)) [IsFiniteMeasure mu]
    (v : PairedSymbol d) (r : Q.Seed) :
    mu ⊗ₘ (averagedKernel Q i).comap (fun eta => ((v,r),eta)) (by fun_prop) =
      ENNReal.ofReal (1/2 : ℝ) •
        (mu ⊗ₘ (Q.kernels i).comap (fun eta => ((recoverObs v false,r),eta)) (by fun_prop)) +
      ENNReal.ofReal (1/2 : ℝ) •
        (mu ⊗ₘ (Q.kernels i).comap (fun eta => ((recoverObs v true,r),eta)) (by fun_prop)) := by
  haveI := averagedKernel_markov Q i
  ext E hE
  rw [Measure.compProd_apply hE, Measure.add_apply, Measure.smul_apply,
    Measure.smul_apply, Measure.compProd_apply hE, Measure.compProd_apply hE]
  simp only [Kernel.comap_apply, averagedKernel, Kernel.coe_mk, averagedRows,
    recoveredKernel, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  have hm (a : Bool) : Measurable (fun eta : ProtocolHistory Q i =>
      Q.kernels i ((recoverObs v a,r),eta) (Prod.mk eta ⁻¹' E)) := by
    exact Kernel.measurable_kernel_prodMk_left' (η := Q.kernels i) hE (recoverObs v a,r)
  rw [lintegral_add_left ((hm false).const_mul _), lintegral_const_mul _ (hm false),
    lintegral_const_mul _ (hm true)]

/-- Assume [one plus the stage index no larger than the sample size](hyp:hk). [The next adaptive prefix with the ancillary bit averaged is exactly the fair mixture of the two original-record prefixes, retaining the common past](goal). -/
-- @node: averagedKernel_prefix_step
lemma averagedKernel_prefix_step (Q : LocalProtocol n (ObsRecord d))
    (x : Fin n → ObsRecord d × Q.Seed) (k : ℕ) (hk : k + 1 ≤ n)
    (v : PairedSymbol d) (r : Q.Seed) :
    ((Causalean.Mathlib.Probability.Kernel.FiniteSequence.prefixLaw Q.kernels x
        k (Nat.le_of_succ_le hk)) ⊗ₘ
      (averagedKernel Q (Causalean.Mathlib.Probability.Kernel.FiniteSequence.nextIndex hk)).comap
        (fun eta => ((v,r),eta)) (by fun_prop)).map
      (fun p => Causalean.Mathlib.Probability.Kernel.FiniteSequence.snoc hk p.1 p.2) =
    ENNReal.ofReal (1/2 : ℝ) •
      Causalean.Mathlib.Probability.Kernel.FiniteSequence.prefixLaw Q.kernels
        (Function.update x (Causalean.Mathlib.Probability.Kernel.FiniteSequence.nextIndex hk)
          (recoverObs v false,r)) (k+1) hk +
    ENNReal.ofReal (1/2 : ℝ) •
      Causalean.Mathlib.Probability.Kernel.FiniteSequence.prefixLaw Q.kernels
        (Function.update x (Causalean.Mathlib.Probability.Kernel.FiniteSequence.nextIndex hk)
          (recoverObs v true,r)) (k+1) hk := by
  have hprob := Causalean.Mathlib.Probability.Kernel.FiniteSequence.isProbabilityMeasure_prefixLaw
    Q.kernels Q.markov x k (Nat.le_of_succ_le hk)
  have hext := @averagedKernel_extend_history n d Q
    (Causalean.Mathlib.Probability.Kernel.FiniteSequence.nextIndex hk)
    (Causalean.Mathlib.Probability.Kernel.FiniteSequence.prefixLaw Q.kernels x
      k (Nat.le_of_succ_le hk))
    ⟨hprob.measure_univ.trans_lt ENNReal.one_lt_top⟩ v r
  have hmap := congrArg (fun mu : Measure (ProtocolHistory Q
      (Causalean.Mathlib.Probability.Kernel.FiniteSequence.nextIndex hk) ×
      Q.Message (Causalean.Mathlib.Probability.Kernel.FiniteSequence.nextIndex hk)) =>
    mu.map (fun p => Causalean.Mathlib.Probability.Kernel.FiniteSequence.snoc hk p.1 p.2)) hext
  have hm : Measurable (fun p : ProtocolHistory Q
      (Causalean.Mathlib.Probability.Kernel.FiniteSequence.nextIndex hk) ×
      Q.Message (Causalean.Mathlib.Probability.Kernel.FiniteSequence.nextIndex hk) =>
    Causalean.Mathlib.Probability.Kernel.FiniteSequence.snoc hk p.1 p.2) :=
      Causalean.Mathlib.Probability.Kernel.FiniteSequence.measurable_snoc hk
  refine hmap.trans ?_
  rw [Measure.map_add _ _ hm,
    Measure.map_smul, Measure.map_smul]
  congr 1 <;> congr 1
  all_goals
    rw [Causalean.Mathlib.Probability.Kernel.FiniteSequence.prefixLaw_succ,
      protocol_prefixLaw_update_next]
    simp only [Function.update_self]
    rfl



/-- Assume [the stated htheta condition](hyp:htheta), [positive dimension](hyp:hd), and [the function f](hyp:f). [Integrating any nonnegative observed-record function first integrates the parameter-independent ancillary assignment bit](goal). -/
-- @node: symmetricLaw_observed_lintegral
lemma symmetricLaw_observed_lintegral (theta : Fin d → ℝ)
    (htheta : theta ∈ parameterCube d) (hd : 0 < d)
    (f : ObsRecord d → ℝ≥0∞) :
    (∫⁻ o, f o ∂observedLaw (symmetricLaw theta)) =
      ∫⁻ v, ENNReal.ofReal (1/2 : ℝ) * f (recoverObs v false) +
        ENNReal.ofReal (1/2 : ℝ) * f (recoverObs v true) ∂pairedLaw theta := by
  rw [lintegral_fintype, lintegral_fintype]
  simp_rw [symmetricLaw_observed_singleton theta htheta hd]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, signedObserve, recoverObs,
    Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.not_true,
    show (true == true) = true from rfl, show (true == false) = false from rfl,
    show (false == true) = false from rfl, show (false == false) = true from rfl]
  ring

/-- Assume [the stated htheta condition](hyp:htheta), [positive dimension](hyp:hd), and [measurability of f](hyp:hf). [Ancillary reconstruction applies to arbitrary measurable measure-valued rows, not merely to an event in a stage kernel](goal). -/
-- @node: symmetricLaw_observed_bind
lemma symmetricLaw_observed_bind {Ω : Type} [MeasurableSpace Ω]
    (theta : Fin d → ℝ) (htheta : theta ∈ parameterCube d) (hd : 0 < d)
    (f : ObsRecord d → Measure Ω) (hf : Measurable f) :
    (observedLaw (symmetricLaw theta)).bind f =
      (pairedLaw theta).bind (fun v =>
        ENNReal.ofReal (1/2 : ℝ) • f (recoverObs v false) +
        ENNReal.ofReal (1/2 : ℝ) • f (recoverObs v true)) := by
  have hmix : Measurable (fun v =>
      ENNReal.ofReal (1/2 : ℝ) • f (recoverObs v false) +
      ENNReal.ofReal (1/2 : ℝ) • f (recoverObs v true)) := by
    apply Measure.measurable_of_measurable_coe
    intro E hE
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    exact (measurable_const.mul (((Measure.measurable_coe hE).comp hf).comp (by fun_prop))).add
      (measurable_const.mul (((Measure.measurable_coe hE).comp hf).comp (by fun_prop)))
  ext E hE
  rw [Measure.bind_apply hE hf.aemeasurable, Measure.bind_apply hE hmix.aemeasurable]
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  exact symmetricLaw_observed_lintegral theta htheta hd (fun o => f o E)

/-- Assume [the stated htheta condition](hyp:htheta) and [positive dimension](hyp:hd). [The original observed law is exactly the paired law followed by independent fair reconstruction](goal). -/
-- @node: symmetricLaw_observed_reconstruction
lemma symmetricLaw_observed_reconstruction (theta : Fin d → ℝ)
    (htheta : theta ∈ parameterCube d) (hd : 0 < d) :
    observedLaw (symmetricLaw theta) =
      (pairedLaw theta).bind (fun v =>
        ENNReal.ofReal (1/2 : ℝ) • Measure.dirac (recoverObs v false) +
        ENNReal.ofReal (1/2 : ℝ) • Measure.dirac (recoverObs v true)) := by
  simpa only [Measure.bind_dirac] using
    symmetricLaw_observed_bind theta htheta hd Measure.dirac Measure.measurable_dirac


/-- Assume [the stated htheta condition](hyp:htheta) and [positive dimension](hyp:hd). [Fresh iid input can be integrated before or after extending any adaptive history law; the two experiments give the same history-message joint measure](goal). -/
-- @node: averagedKernel_integrated_historyLaw
lemma averagedKernel_integrated_historyLaw (Q : LocalProtocol n (ObsRecord d))
    (theta : Fin d → ℝ) (htheta : theta ∈ parameterCube d) (hd : 0 < d)
    (i : Fin n) (mu : Measure (ProtocolHistory Q i)) [IsFiniteMeasure mu] (r : Q.Seed) :
    (observedLaw (symmetricLaw theta)).bind (fun o =>
      mu ⊗ₘ (Q.kernels i).comap (fun eta => ((o,r),eta)) (by fun_prop)) =
    (pairedLaw theta).bind (fun v =>
      mu ⊗ₘ (averagedKernel Q i).comap (fun eta => ((v,r),eta)) (by fun_prop)) := by
  rw [symmetricLaw_observed_bind theta htheta hd _ (by
    first | fun_prop | exact measurable_of_countable _)]
  congr 1
  funext v
  exact (averagedKernel_extend_history Q i mu v r).symm

/-- Assume [the stated htheta condition](hyp:htheta), [positive dimension](hyp:hd), and [measurability of f](hyp:hf). [The same transition equality survives measurable transcript processing, including retention of histories and appending the next message](goal). -/
-- @node: averagedKernel_integrated_historyLaw_map
lemma averagedKernel_integrated_historyLaw_map {Ω : Type} [MeasurableSpace Ω]
    (Q : LocalProtocol n (ObsRecord d)) (theta : Fin d → ℝ)
    (htheta : theta ∈ parameterCube d) (hd : 0 < d)
    (i : Fin n) (mu : Measure (ProtocolHistory Q i)) [IsFiniteMeasure mu] (r : Q.Seed)
    (f : ProtocolHistory Q i × Q.Message i → Ω) (hf : Measurable f) :
    (observedLaw (symmetricLaw theta)).bind (fun o =>
      (mu ⊗ₘ (Q.kernels i).comap (fun eta => ((o,r),eta)) (by fun_prop)).map f) =
    (pairedLaw theta).bind (fun v =>
      (mu ⊗ₘ (averagedKernel Q i).comap (fun eta => ((v,r),eta)) (by fun_prop)).map f) := by
  rw [symmetricLaw_observed_bind theta htheta hd _ (by
    first | fun_prop | exact measurable_of_countable _)]
  congr 1
  funext v
  rw [averagedKernel_extend_history, Measure.map_add _ _ hf,
    Measure.map_smul, Measure.map_smul]

/-- Assume [the stated htheta condition](hyp:htheta), [positive dimension](hyp:hd), and [one plus the stage index no larger than the sample size](hyp:hk). [Averaging a fresh participant's iid observed input gives precisely the paired next-prefix transition while leaving the previously queried records fixed](goal). -/
-- @node: averagedKernel_integrated_prefix_step
lemma averagedKernel_integrated_prefix_step (Q : LocalProtocol n (ObsRecord d))
    (theta : Fin d → ℝ) (htheta : theta ∈ parameterCube d) (hd : 0 < d)
    (x : Fin n → ObsRecord d × Q.Seed) (k : ℕ) (hk : k + 1 ≤ n) (r : Q.Seed) :
    (observedLaw (symmetricLaw theta)).bind (fun o =>
      Causalean.Mathlib.Probability.Kernel.FiniteSequence.prefixLaw Q.kernels
        (Function.update x (Causalean.Mathlib.Probability.Kernel.FiniteSequence.nextIndex hk)
          (o,r)) (k+1) hk) =
    (pairedLaw theta).bind (fun v =>
      ((Causalean.Mathlib.Probability.Kernel.FiniteSequence.prefixLaw Q.kernels x
          k (Nat.le_of_succ_le hk)) ⊗ₘ
        (averagedKernel Q (Causalean.Mathlib.Probability.Kernel.FiniteSequence.nextIndex hk)).comap
          (fun eta => ((v,r),eta)) (by fun_prop)).map
        (fun p => Causalean.Mathlib.Probability.Kernel.FiniteSequence.snoc hk p.1 p.2)) := by
  rw [symmetricLaw_observed_bind theta htheta hd _ (by fun_prop)]
  congr 1
  funext v
  exact (averagedKernel_prefix_step Q x k hk v r).symm

end CausalSmith.Stat.LdpOptvalueUniformFrontier
