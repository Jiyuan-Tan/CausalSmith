module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Contraction.Derivative
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Contraction.StageIdentification
public import Causalean.Mathlib.Probability.Kernel.FiniteHistory.Expectation

/-!
# Transcript-history martingale scores

Fresh-input message kernels and the structural product density identify the
actual history-message law. Repaired row scores are adapted bounded martingale
differences, giving the binomial elementary-score first-moment bound.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open Causalean.Mathlib.Probability.Kernel.FiniteSequence
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier

/-- Assume [measurability of x](hyp:hX), [measurability of y](hyp:hY), [the stated hlaw condition](hyp:hlaw), [measurability of s](hyp:hs), [the stated hb condition](hyp:hb), and [the stated hzero condition](hyp:hzero). [A bounded score centered in each conditional message law is centered given history under any transcript law with the corresponding history-message marginal](goal). -/
-- @node: transcript_score_condExp_zero_of_jointLaw
lemma transcript_score_condExp_zero_of_jointLaw
    {Ω H Z : Type*} [MeasurableSpace Ω] [MeasurableSpace H] [MeasurableSpace Z]
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (rho : Measure H) [IsProbabilityMeasure rho] (K : Kernel H Z) [IsMarkovKernel K]
    (X : Ω → H) (Y : Ω → Z) (hX : Measurable X) (hY : Measurable Y)
    (hlaw : mu.map (fun w => (X w, Y w)) = rho ⊗ₘ K)
    (s : H × Z → ℝ) (hs : Measurable s) (b : ℝ)
    (hb : ∀ w, |s w| ≤ b) (hzero : ∀ h, (∫ z, s (h, z) ∂K h) = 0) :
    mu[(fun w => s (X w, Y w)) | MeasurableSpace.comap X inferInstance] =ᵐ[mu] 0 := by
  have hint : Integrable (fun w => s (X w, Y w)) mu :=
    Integrable.of_bound (hs.comp (hX.prodMk hY)).aestronglyMeasurable b
      (Filter.Eventually.of_forall fun w => by simpa only [Real.norm_eq_abs] using hb _)
  apply (ae_eq_condExp_of_forall_setIntegral_eq hX.comap_le hint
    (fun t _ _ => (integrable_const (0 : ℝ)).integrableOn) ?_
    (stronglyMeasurable_const.aestronglyMeasurable)).symm
  intro t ht hfinite
  obtain ⟨A, hA, rfl⟩ := MeasurableSpace.measurableSet_comap.mp ht
  rw [integral_zero]
  let g : H × Z → ℝ := (A ×ˢ Set.univ).indicator s
  have hg : Measurable g := hs.indicator (hA.prod MeasurableSet.univ)
  have hgb : ∀ w, |g w| ≤ max b 0 := by
    intro w
    by_cases hw : w ∈ A ×ˢ Set.univ
    · simpa [g, Set.indicator_of_mem hw] using (hb w).trans (le_max_left b 0)
    · simp [g, Set.indicator_of_notMem hw]
  have heq : (fun w => (X ⁻¹' A).indicator (fun w => s (X w, Y w)) w) =
      (fun w => g (X w, Y w)) := by
    funext w
    by_cases hw : X w ∈ A <;> simp [g, Set.indicator, hw]
  rw [← integral_indicator (hX hA), heq,
    ← integral_map (hX.prodMk hY).aemeasurable hg.aestronglyMeasurable, hlaw]
  rw [Causalean.Mathlib.Probability.Kernel.FiniteHistory.integral_compProd_bounded
    rho K _ rfl g hg (max b 0) hgb]
  symm
  calc
    _ = ∫ h, (0 : ℝ) ∂rho := by
      apply integral_congr_ae
      filter_upwards [] with h
      by_cases hh : h ∈ A
      · simpa [g, Set.indicator, hh] using hzero h
      · simp [g, Set.indicator, hh]
    _ = 0 := by simp

/-- Fix [the local protocol Q](hyp:Q), [the function theta](hyp:theta), and [the participant index](hyp:i). [The conditional message kernel obtained by integrating a fresh paired input](goal). -/
-- @node: stageParameterKernel
def stageParameterKernel {n d : ℕ} (Q : LocalProtocol n (ObsRecord d))
    (theta : Fin d → ℝ) (i : Fin n) : Kernel (Q.Seed × ProtocolHistory Q i) (Q.Message i) :=
  ⟨fun w => (pairedLaw theta).bind (fun a => averagedKernel Q i ((a, w.1), w.2)), by
    apply Measure.measurable_of_measurable_coe
    intro E hE
    have hr (w : Q.Seed × ProtocolHistory Q i) :
        Measurable (fun a : PairedSymbol d => averagedKernel Q i ((a, w.1), w.2)) := by
      fun_prop
    simp_rw [Measure.bind_apply hE (hr _).aemeasurable, lintegral_fintype]
    exact Finset.measurable_sum _ (fun a _ =>
      ((averagedKernel Q i).measurable_coe hE |>.comp (by fun_prop)).mul measurable_const)⟩

/-- Assume [the stated htheta condition](hyp:htheta) and [positive dimension](hyp:hd). [The fresh-input message kernels have unit mass on the parameter cube](goal). -/
-- @node: stageParameterKernel_markov
lemma stageParameterKernel_markov {n d : ℕ} (Q : LocalProtocol n (ObsRecord d))
    (theta : Fin d → ℝ) (htheta : theta ∈ parameterCube d) (hd : 0 < d)
    (i : Fin n) : IsMarkovKernel (stageParameterKernel Q theta i) := by
  haveI : IsProbabilityMeasure (pairedLaw theta) :=
    pairedFamily_subset_simplex hd (Set.mem_image_of_mem pairedLaw htheta)
  constructor
  intro w
  change IsProbabilityMeasure ((pairedLaw theta).bind
    (fun a => averagedKernel Q i ((a, w.1), w.2)))
  constructor
  rw [Measure.bind_apply MeasurableSet.univ (by fun_prop)]
  have hm (a : PairedSymbol d) : averagedKernel Q i ((a, w.1), w.2) Set.univ = 1 := by
    letI := averagedKernel_markov Q i
    exact measure_univ
  simp [hm]

/-- Assume [the stated htheta condition](hyp:htheta), [measurability of f](hyp:hf), [the stated hf0 condition](hyp:hf0), and [the Markov kernel hrow](hyp:hrow). [Repaired row densities represent the fresh-input message kernel](goal). -/
-- @node: stageParameterKernel_withDensity
lemma stageParameterKernel_withDensity {n d : ℕ} (Q : LocalProtocol n (ObsRecord d))
    (theta : Fin d → ℝ) (htheta : theta ∈ parameterCube d) (i : Fin n)
    (r : Q.Seed) (eta : ProtocolHistory Q i)
    (f : ((PairedSymbol d × Q.Seed) × ProtocolHistory Q i) × Q.Message i → ℝ)
    (hf : Measurable f) (hf0 : ∀ w, 0 ≤ f w)
    (hrow : ∀ a, (stageReferenceKernel Q i (r, eta)).withDensity
      (fun z => ENNReal.ofReal (f (((a, r), eta), z))) = averagedKernel Q i ((a, r), eta)) :
    (stageReferenceKernel Q i (r, eta)).withDensity
      (fun z => ENNReal.ofReal (stageMixtureDensity theta (fun a => f (((a, r), eta), z)))) =
      stageParameterKernel Q theta i (r, eta) := by
  exact finite_weighted_density_bind _ (stageInputWeight theta)
    (stageInputWeight_nonneg theta htheta) _
    (fun a => hf.comp (by fun_prop)) (fun a z => hf0 _) _ (by fun_prop) hrow

/-- Assume [positive dimension](hyp:hd), [the stated htheta condition](hyp:htheta), [measurability of f](hyp:hf), [the stated hf0 condition](hyp:hf0), [the Markov kernel hrow](hyp:hrow), [the stated href condition](hyp:href), and [the stated hprod condition](hyp:hprod). [Structural iteration of the conditional message densities identifies the parameter-specific chain with the original-record transcript experiment](goal). -/
-- @node: originalTranscript_eq_parameterChain
lemma originalTranscript_eq_parameterChain {n d : ℕ}
    (Q : LocalProtocol n (ObsRecord d)) (hd : 0 < d)
    (theta : Fin d → ℝ) (htheta : theta ∈ parameterCube d) (r : Q.Seed)
    (f : (i : Fin n) →
      ((PairedSymbol d × Q.Seed) × ProtocolHistory Q i) × Q.Message i → ℝ)
    (hf : ∀ i, Measurable (f i)) (hf0 : ∀ i w, 0 ≤ f i w)
    (hrow : ∀ i a eta, (stageReferenceKernel Q i (r, eta)).withDensity
      (fun z => ENNReal.ofReal (f i (((a, r), eta), z))) = averagedKernel Q i ((a, r), eta))
    (href : stageReferenceTranscriptLaw Q r = referenceLaw Q r)
    (hprod : (referenceLaw Q r).withDensity (fun z => ENNReal.ofReal
      (∏ i : Fin n, stageMixtureDensity theta
        (fun a => f i (((a, r), take (Nat.le_of_lt i.isLt) z), z i)))) =
          conditionalTranscriptLaw Q theta r) :
    conditionalTranscriptLaw Q theta r =
      transcriptLaw (stageParameterKernel Q theta) (fun _ => r) := by
  let g := fun (i : Fin n) (w : ProtocolHistory Q i × Q.Message i) =>
    ENNReal.ofReal (stageMixtureDensity theta (fun a => f i (((a, r), w.1), w.2)))
  have hg : ∀ i, Measurable (g i) := by
    intro i
    unfold g stageMixtureDensity
    exact (Finset.measurable_sum _ (fun a _ =>
      measurable_const.mul ((hf i).comp (by fun_prop)))).ennreal_ofReal
  have hchain := sequentialPrefixDensity_withDensity (stageReferenceKernel Q)
    (stageParameterKernel Q theta) (fun i => stageReferenceKernel_markov Q i hd)
    (stageParameterKernel_markov Q theta htheta hd) (fun _ => r) (fun _ => r) g hg
    (fun i eta => stageParameterKernel_withDensity Q theta htheta i r eta (f i)
      (hf i) (hf0 i) (fun a => hrow i a eta)) n le_rfl
  change (stageReferenceTranscriptLaw Q r).withDensity
    (sequentialPrefixDensity g n le_rfl) = _ at hchain
  have hfun : sequentialPrefixDensity g n le_rfl =
      (fun z : ProtocolTranscript Q => ENNReal.ofReal (∏ i : Fin n,
        stageMixtureDensity theta
          (fun a => f i (((a, r), take (Nat.le_of_lt i.isLt) z), z i)))) := by
    funext z
    rw [sequentialPrefixDensity_eq_prod, ENNReal.ofReal_prod_of_nonneg]
    · rfl
    · intro i hi
      exact Finset.sum_nonneg (fun a _ =>
        mul_nonneg (stageInputWeight_nonneg theta htheta a) (hf0 i _))
  rw [href, hfun, hprod] at hchain
  exact hchain

/-- Assume [positive dimension](hyp:hd), [the stated htheta condition](hyp:htheta), and [the Markov kernel hchain](hyp:hchain). [The actual transcript law has the fresh-input history-message marginal, including on adaptive histories in arbitrary standard-Borel message spaces](goal). -/
-- @node: originalTranscript_map_take_next
lemma originalTranscript_map_take_next {n d : ℕ}
    (Q : LocalProtocol n (ObsRecord d)) (hd : 0 < d)
    (theta : Fin d → ℝ) (htheta : theta ∈ parameterCube d) (r : Q.Seed)
    (hchain : conditionalTranscriptLaw Q theta r =
      transcriptLaw (stageParameterKernel Q theta) (fun _ => r)) (i : Fin n) :
    (conditionalTranscriptLaw Q theta r).map
      (fun z => (take (Nat.le_of_lt i.isLt) z, z i)) =
      (prefixLaw (stageParameterKernel Q theta) (fun _ => r) i.val
        (Nat.le_of_lt i.isLt)) ⊗ₘ
          (stageParameterKernel Q theta i).comap (fun eta => (r, eta)) (by fun_prop) := by
  rw [hchain]
  exact transcriptLaw_map_take_next (stageParameterKernel Q theta)
    (stageParameterKernel_markov Q theta htheta hd) (fun _ => r) i.val i.isLt

/-- Assume [positive dimension](hyp:hd), [the stated htheta condition](hyp:htheta), [a nonnegative privacy budget](hyp:heps), [measurability of f](hyp:hf), [the stated hbound condition](hyp:hbound), [the stated hpriv condition](hyp:hpriv), [the Markov kernel hrow](hyp:hrow), and [the Markov kernel hchain](hyp:hchain). [The repaired coordinate score has zero conditional expectation given the actual original-record transcript history](goal). -/
-- @node: originalTranscript_stageScore_condExp_zero
lemma originalTranscript_stageScore_condExp_zero {n d : ℕ}
    (Q : LocalProtocol n (ObsRecord d)) (hd : 0 < d)
    (theta : Fin d → ℝ) (htheta : theta ∈ parameterCube d) (r : Q.Seed)
    (eps : ℝ) (heps : 0 ≤ eps)
    (f : (i : Fin n) →
      ((PairedSymbol d × Q.Seed) × ProtocolHistory Q i) × Q.Message i → ℝ)
    (hf : ∀ i, Measurable (f i))
    (hbound : ∀ i w, Real.exp (-eps) ≤ f i w ∧ f i w ≤ Real.exp eps)
    (hpriv : ∀ i a b r eta z,
      f i (((a, r), eta), z) ≤ Real.exp eps * f i (((b, r), eta), z))
    (hrow : ∀ i a eta, (stageReferenceKernel Q i (r, eta)).withDensity
      (fun z => ENNReal.ofReal (f i (((a, r), eta), z))) = averagedKernel Q i ((a, r), eta))
    (hchain : conditionalTranscriptLaw Q theta r =
      transcriptLaw (stageParameterKernel Q theta) (fun _ => r)) (i : Fin n) (j : Fin d) :
    (conditionalTranscriptLaw Q theta r)[(fun z =>
      stageCoordinateSlope (fun a => f i (((a, r), take (Nat.le_of_lt i.isLt) z), z i)) j /
      stageMixtureDensity theta (fun a => f i (((a, r), take (Nat.le_of_lt i.isLt) z), z i))) |
        MeasurableSpace.comap (take (Nat.le_of_lt i.isLt) :
          ProtocolTranscript Q → ProtocolHistory Q i) inferInstance] =ᵐ[
            conditionalTranscriptLaw Q theta r] 0 := by
  letI := conditionalTranscriptLaw_probability Q theta htheta hd r
  letI := stageParameterKernel_markov Q theta htheta hd i
  letI := isProbabilityMeasure_prefixLaw (stageParameterKernel Q theta)
    (stageParameterKernel_markov Q theta htheta hd) (fun _ => r) i.val (Nat.le_of_lt i.isLt)
  let s := fun w : ProtocolHistory Q i × Q.Message i =>
    stageCoordinateSlope (fun a => f i (((a, r), w.1), w.2)) j /
      stageMixtureDensity theta (fun a => f i (((a, r), w.1), w.2))
  have hs : Measurable s := by
    unfold s stageCoordinateSlope stageMixtureDensity
    fun_prop
  have hscore (eta : ProtocolHistory Q i) (z : Q.Message i) :=
    stageCoordinateScore_bound hd theta htheta (fun a => f i (((a, r), eta), z))
      (fun a => lt_of_lt_of_le (Real.exp_pos _) (hbound i _).1) eps heps
      (fun a b => hpriv i a b r eta z) j
  apply transcript_score_condExp_zero_of_jointLaw _ _
    ((stageParameterKernel Q theta i).comap (fun eta => (r, eta)) (by fun_prop))
    (take (Nat.le_of_lt i.isLt)) (fun z => z i)
    (measurable_restrictHistory _ _ _) (by fun_prop)
    (originalTranscript_map_take_next Q hd theta htheta r hchain i)
    s hs (derivativeScale d eps) (fun w => (hscore w.1 w.2).2)
  intro eta
  change (∫ z, s (eta, z) ∂stageParameterKernel Q theta i (r, eta)) = 0
  rw [← stageParameterKernel_withDensity Q theta htheta i r eta (f i) (hf i)
    (fun w => le_trans (le_of_lt (Real.exp_pos _)) (hbound i w).1)
    (fun a => hrow i a eta)]
  letI := stageReferenceKernel_markov Q i hd
  letI := averagedKernel_markov Q i
  apply stageCoordinateScore_integral_zero (stageReferenceKernel Q i (r, eta))
    (fun a z => f i (((a, r), eta), z))
    (fun a => (hf i).comp (by fun_prop))
    (fun a z => le_trans (le_of_lt (Real.exp_pos _)) (hbound i _).1)
    (Real.exp eps)
  · intro a z
    rw [abs_of_nonneg (le_trans (le_of_lt (Real.exp_pos _)) (hbound i _).1)]
    exact (hbound i _).2
  · intro a
    rw [hrow]
    infer_instance
  · intro z
    exact (hscore eta z).1

/-- Fix [the local protocol Q](hyp:Q) and [the natural-number parameter v](hyp:v). [Transcript information available by a stage, held constant after the horizon](goal). -/
-- @node: transcriptHistorySpace
def transcriptHistorySpace {n d : ℕ} (Q : LocalProtocol n (ObsRecord d))
    (v : ℕ) : MeasurableSpace (ProtocolTranscript Q) :=
  if hv : v ≤ n then
    MeasurableSpace.comap (take hv : ProtocolTranscript Q → History Q.Message v hv) inferInstance
  else inferInstance

/-- [Every history sigma-algebra is contained in the full transcript sigma-algebra](goal). -/
-- @node: transcriptHistorySpace_le
lemma transcriptHistorySpace_le {n d : ℕ} (Q : LocalProtocol n (ObsRecord d)) (v : ℕ) :
    transcriptHistorySpace Q v ≤ (inferInstance : MeasurableSpace (ProtocolTranscript Q)) := by
  unfold transcriptHistorySpace
  split_ifs with hv
  · exact (measurable_restrictHistory _ _ _).comap_le
  · exact le_rfl

/-- [Transcript histories form an increasing family of sub-sigma-algebras](goal). -/
-- @node: transcriptHistorySpace_mono
lemma transcriptHistorySpace_mono {n d : ℕ} (Q : LocalProtocol n (ObsRecord d)) :
    Monotone (transcriptHistorySpace Q) := by
  intro v w hvw
  by_cases hw : w ≤ n
  · have hv : v ≤ n := hvw.trans hw
    unfold transcriptHistorySpace
    rw [dif_pos hv, dif_pos hw]
    apply Measurable.comap_le
    have htake : Measurable[MeasurableSpace.comap (take hw :
        ProtocolTranscript Q → History Q.Message w hw) inferInstance]
        (take hw : ProtocolTranscript Q → History Q.Message w hw) :=
      Measurable.of_comap_le le_rfl
    exact (measurable_restrictHistory _ _ hvw).comp htake
  · simpa only [transcriptHistorySpace, dif_neg hw] using transcriptHistorySpace_le Q v

/-- Fix [the local protocol Q](hyp:Q), [the function theta](hyp:theta), [the public seed](hyp:r), [the function f](hyp:f), [the coordinate index](hyp:j), [the natural-number parameter v](hyp:v), and [the protocol transcript](hyp:z). [The conditional coordinate scores are extended by zero after the horizon](goal). -/
-- @node: transcriptCoordinateScore
def transcriptCoordinateScore {n d : ℕ} (Q : LocalProtocol n (ObsRecord d))
    (theta : Fin d → ℝ) (r : Q.Seed)
    (f : (i : Fin n) →
      ((PairedSymbol d × Q.Seed) × ProtocolHistory Q i) × Q.Message i → ℝ)
    (j : Fin d) (v : ℕ) (z : ProtocolTranscript Q) : ℝ :=
  if hv : v < n then
    stageCoordinateSlope (fun a => f ⟨v, hv⟩ (((a, r), take (Nat.le_of_lt hv) z), z ⟨v, hv⟩)) j /
      stageMixtureDensity theta (fun a => f ⟨v, hv⟩ (((a, r), take (Nat.le_of_lt hv) z), z ⟨v, hv⟩))
  else 0

/-- [Each stage score is measurable once its message has been observed](goal) when [the repaired row densities are measurable](hyp:hf). -/
-- @node: transcriptCoordinateScore_adapted
@[fun_prop] lemma transcriptCoordinateScore_adapted {n d : ℕ}
    (Q : LocalProtocol n (ObsRecord d)) (theta : Fin d → ℝ) (r : Q.Seed)
    (f : (i : Fin n) →
      ((PairedSymbol d × Q.Seed) × ProtocolHistory Q i) × Q.Message i → ℝ)
    (hf : ∀ i, Measurable (f i)) (j : Fin d) (v : ℕ) :
    Measurable[transcriptHistorySpace Q (v + 1)] (transcriptCoordinateScore Q theta r f j v) := by
  unfold transcriptCoordinateScore transcriptHistorySpace
  by_cases hv : v < n
  · rw [dif_pos (Nat.succ_le_of_lt hv)]
    simp only [dif_pos hv]
    have htake : Measurable[MeasurableSpace.comap (take (Nat.succ_le_of_lt hv) :
        ProtocolTranscript Q → History Q.Message (v + 1) (Nat.succ_le_of_lt hv)) inferInstance]
        (take (Nat.succ_le_of_lt hv) : ProtocolTranscript Q →
          History Q.Message (v + 1) (Nat.succ_le_of_lt hv)) :=
      Measurable.of_comap_le le_rfl
    have hs : Measurable (fun u : History Q.Message (v + 1) (Nat.succ_le_of_lt hv) =>
      stageCoordinateSlope
        (fun a => f ⟨v, hv⟩ (((a, r), init (Nat.succ_le_of_lt hv) u), last (Nat.succ_le_of_lt hv) u)) j /
      stageMixtureDensity theta
        (fun a => f ⟨v, hv⟩ (((a, r), init (Nat.succ_le_of_lt hv) u), last (Nat.succ_le_of_lt hv) u))) := by
      have hi := (measurable_fst.comp (measurable_init_last (Z := Q.Message) (Nat.succ_le_of_lt hv)))
      have hl := (measurable_snd.comp (measurable_init_last (Z := Q.Message) (Nat.succ_le_of_lt hv)))
      unfold stageCoordinateSlope stageMixtureDensity
      fun_prop
    convert hs.comp htake using 1
    funext z
    have hi : init (Nat.succ_le_of_lt hv) (take (Nat.succ_le_of_lt hv) z) =
        take (Nat.le_of_lt hv) z := by
      funext a
      rfl
    simp only [Function.comp_apply, hi]
    rfl
  · simp only [dif_neg hv]
    exact measurable_const

/-- Assume [positive dimension](hyp:hd), [the stated htheta condition](hyp:htheta), [a nonnegative privacy budget](hyp:heps), [the stated hbound condition](hyp:hbound), and [the stated hpriv condition](hyp:hpriv). [The sharp privacy envelope bounds all scores, including their zero extension](goal). -/
-- @node: transcriptCoordinateScore_bound
lemma transcriptCoordinateScore_bound {n d : ℕ}
    (Q : LocalProtocol n (ObsRecord d)) (hd : 0 < d)
    (theta : Fin d → ℝ) (htheta : theta ∈ parameterCube d) (r : Q.Seed)
    (eps : ℝ) (heps : 0 ≤ eps)
    (f : (i : Fin n) →
      ((PairedSymbol d × Q.Seed) × ProtocolHistory Q i) × Q.Message i → ℝ)
    (hbound : ∀ i w, Real.exp (-eps) ≤ f i w)
    (hpriv : ∀ i a b r eta z,
      f i (((a, r), eta), z) ≤ Real.exp eps * f i (((b, r), eta), z))
    (j : Fin d) (v : ℕ) (z : ProtocolTranscript Q) :
    |transcriptCoordinateScore Q theta r f j v z| ≤ derivativeScale d eps := by
  by_cases hv : v < n
  · simp only [transcriptCoordinateScore, dif_pos hv]
    exact (originalTranscript_stageScore_bound Q hd theta htheta eps heps f hbound hpriv
      r z ⟨v, hv⟩ j).2
  · simp only [transcriptCoordinateScore, dif_neg hv, abs_zero]
    unfold derivativeScale
    exact div_nonneg (sub_nonneg.mpr (Real.one_le_exp_iff.mpr heps)) (by positivity)

/-- Assume [positive dimension](hyp:hd), [the stated htheta condition](hyp:htheta), [a nonnegative privacy budget](hyp:heps), [measurability of f](hyp:hf), [the stated hbound condition](hyp:hbound), [the stated hpriv condition](hyp:hpriv), [the Markov kernel hrow](hyp:hrow), and [the Markov kernel hchain](hyp:hchain). [The extended scores are martingale differences for transcript history](goal). -/
-- @node: transcriptCoordinateScore_condExp_zero
lemma transcriptCoordinateScore_condExp_zero {n d : ℕ}
    (Q : LocalProtocol n (ObsRecord d)) (hd : 0 < d)
    (theta : Fin d → ℝ) (htheta : theta ∈ parameterCube d) (r : Q.Seed)
    (eps : ℝ) (heps : 0 ≤ eps)
    (f : (i : Fin n) →
      ((PairedSymbol d × Q.Seed) × ProtocolHistory Q i) × Q.Message i → ℝ)
    (hf : ∀ i, Measurable (f i))
    (hbound : ∀ i w, Real.exp (-eps) ≤ f i w ∧ f i w ≤ Real.exp eps)
    (hpriv : ∀ i a b r eta z,
      f i (((a, r), eta), z) ≤ Real.exp eps * f i (((b, r), eta), z))
    (hrow : ∀ i a eta, (stageReferenceKernel Q i (r, eta)).withDensity
      (fun z => ENNReal.ofReal (f i (((a, r), eta), z))) = averagedKernel Q i ((a, r), eta))
    (hchain : conditionalTranscriptLaw Q theta r =
      transcriptLaw (stageParameterKernel Q theta) (fun _ => r)) (j : Fin d) (v : ℕ) :
    (conditionalTranscriptLaw Q theta r)[transcriptCoordinateScore Q theta r f j v |
        transcriptHistorySpace Q v] =ᵐ[conditionalTranscriptLaw Q theta r] 0 := by
  unfold transcriptCoordinateScore transcriptHistorySpace
  by_cases hv : v < n
  · simpa only [dif_pos hv, dif_pos (Nat.le_of_lt hv)] using
      originalTranscript_stageScore_condExp_zero Q hd theta htheta r eps heps f hf hbound
        hpriv hrow hchain ⟨v, hv⟩ j
  · simp only [dif_neg hv]
    change (conditionalTranscriptLaw Q theta r)[(0 : ProtocolTranscript Q → ℝ) | _] =ᵐ[_] 0
    rw [condExp_zero]

/-- Assume [positive dimension](hyp:hd), [the stated htheta condition](hyp:htheta), [a nonnegative privacy budget](hyp:heps), [measurability of f](hyp:hf), [the stated hbound condition](hyp:hbound), [the stated hpriv condition](hyp:hpriv), [the Markov kernel hrow](hyp:hrow), and [the Markov kernel hchain](hyp:hchain). [Transcript martingale certification gives the binomial first-moment bound for the elementary score polynomial under the actual experiment law](goal). -/
-- @node: originalTranscript_scoreElementary_firstMoment
lemma originalTranscript_scoreElementary_firstMoment {n d : ℕ}
    (Q : LocalProtocol n (ObsRecord d)) (hd : 0 < d)
    (theta : Fin d → ℝ) (htheta : theta ∈ parameterCube d) (r : Q.Seed)
    (eps : ℝ) (heps : 0 ≤ eps)
    (f : (i : Fin n) →
      ((PairedSymbol d × Q.Seed) × ProtocolHistory Q i) × Q.Message i → ℝ)
    (hf : ∀ i, Measurable (f i))
    (hbound : ∀ i w, Real.exp (-eps) ≤ f i w ∧ f i w ≤ Real.exp eps)
    (hpriv : ∀ i a b r eta z,
      f i (((a, r), eta), z) ≤ Real.exp eps * f i (((b, r), eta), z))
    (hrow : ∀ i a eta, (stageReferenceKernel Q i (r, eta)).withDensity
      (fun z => ENNReal.ofReal (f i (((a, r), eta), z))) = averagedKernel Q i ((a, r), eta))
    (hchain : conditionalTranscriptLaw Q theta r =
      transcriptLaw (stageParameterKernel Q theta) (fun _ => r)) (j : Fin d) (k : ℕ) :
    (∫ z, |scoreElementary (fun v => transcriptCoordinateScore Q theta r f j v z) n k|
      ∂conditionalTranscriptLaw Q theta r) ≤
        Real.sqrt (Nat.choose n k) * (derivativeScale d eps)^k := by
  letI := conditionalTranscriptLaw_probability Q theta htheta hd r
  refine scoreElementary_martingale_firstMoment _ (transcriptHistorySpace Q)
    (transcriptHistorySpace_mono Q) (transcriptHistorySpace_le Q)
    (transcriptCoordinateScore Q theta r f j)
    (transcriptCoordinateScore_adapted Q theta r f hf j) (derivativeScale d eps) ?_ ?_ ?_ n k
  · unfold derivativeScale
    exact div_nonneg (sub_nonneg.mpr (Real.one_le_exp_iff.mpr heps)) (by positivity)
  · exact transcriptCoordinateScore_bound Q hd theta htheta r eps heps f
      (fun i w => (hbound i w).1) hpriv j
  · exact transcriptCoordinateScore_condExp_zero Q hd theta htheta r eps heps f hf hbound
      hpriv hrow hchain j

end CausalSmith.Stat.LdpOptvalueUniformFrontier
