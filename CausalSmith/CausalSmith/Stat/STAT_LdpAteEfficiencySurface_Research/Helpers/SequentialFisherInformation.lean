module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.SequentialAdjacentScore
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-! # Square integrability and one-step Fisher information -/

@[expose] public section
noncomputable section
namespace CausalSmith.Stat.LdpAteEfficiencySurface

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open Causalean.Mathlib.Probability.Kernel.FiniteSequence

/-- [the transcript prefix derivative eq complete data score mixture assertion](goal) holds. For [the displayed quantities and conditions](hyp:P,v,p,n,k,hk,h,hx), these specify the stated inputs. -/
lemma transcriptPrefixDerivative_eq_completeDataScoreMixture
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (n k : ℕ) (hk : k ≤ n) (h : History (Z n) k hk)
    (hx : ∀ x : Fin n → Fin 4, inputPathProbability θ p x ≠ 0) :
    transcriptPrefixMixtureRealDerivative P θ v p n k hk h =
      ∑ x : Fin n → Fin 4,
        inputPathProbability θ p x * inputPathDirectionalScore θ v p x *
          transcriptPrefixComponentRealDensity P n k hk x h := by
  unfold transcriptPrefixMixtureRealDerivative
  apply Finset.sum_congr rfl
  intro x _
  rw [inputPathDerivative_eq_probability_mul_score θ v p x (hx x)]

/-- the abs conditional transcript prefix directional score le assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hk), [the abs conditional Transcript Prefix Directional Score le](goal).

Under the stated assumptions, the abs conditional Transcript Prefix Directional Score le. -/
lemma abs_conditionalTranscriptPrefixDirectionalScore_le
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (n k : ℕ) (hk : k ≤ n) (h : History (Z n) k hk) :
    |conditionalTranscriptPrefixDirectionalScore P θ v p n k hk h| ≤
      inputPathScoreBound (n := n) θ v p := by
  let B := inputPathScoreBound (n := n) θ v p
  let d := transcriptPrefixMixtureRealDensity P θ p n k hk h
  have hB : 0 ≤ B := inputPathScoreBound_nonneg θ v p
  have hd : 0 ≤ d := transcriptPrefixMixtureRealDensity_nonneg
    P θ p n k hk hp hθ h
  have hx (x : Fin n → Fin 4) : inputPathProbability θ p x ≠ 0 :=
    ne_of_gt (inputPathProbability_pos_of_interior θ p hp hθ x)
  have hn : |transcriptPrefixMixtureRealDerivative P θ v p n k hk h| ≤ B * d := by
    rw [transcriptPrefixDerivative_eq_completeDataScoreMixture
      P θ v p n k hk h hx]
    calc
      |∑ x : Fin n → Fin 4, inputPathProbability θ p x *
          inputPathDirectionalScore θ v p x *
          transcriptPrefixComponentRealDensity P n k hk x h| ≤
        ∑ x : Fin n → Fin 4, |inputPathProbability θ p x *
          inputPathDirectionalScore θ v p x *
          transcriptPrefixComponentRealDensity P n k hk x h| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ x : Fin n → Fin 4,
          (inputPathProbability θ p x *
            transcriptPrefixComponentRealDensity P n k hk x h) *
              |inputPathDirectionalScore θ v p x| := by
        apply Finset.sum_congr rfl
        intro x _
        have hc : 0 ≤ transcriptPrefixComponentRealDensity P n k hk x h :=
          ENNReal.toReal_nonneg
        rw [abs_mul, abs_mul, abs_of_pos
          (inputPathProbability_pos_of_interior θ p hp hθ x),
          abs_of_nonneg hc]
        ring
      _ ≤ ∑ x : Fin n → Fin 4,
          (inputPathProbability θ p x *
            transcriptPrefixComponentRealDensity P n k hk x h) * B := by
        apply Finset.sum_le_sum
        intro x _
        exact mul_le_mul_of_nonneg_left
          (abs_inputPathDirectionalScore_le_bound θ v p x)
          (mul_nonneg (inputPathProbability_pos_of_interior θ p hp hθ x).le
            ENNReal.toReal_nonneg)
      _ = B * d := by
        simp only [d, transcriptPrefixMixtureRealDensity]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
  by_cases hdz : d = 0
  · have hn0 : transcriptPrefixMixtureRealDerivative P θ v p n k hk h = 0 := by
      rw [hdz, mul_zero] at hn
      exact abs_eq_zero.mp (le_antisymm hn (abs_nonneg _))
    rw [conditionalTranscriptPrefixDirectionalScore, hn0,
      show transcriptPrefixMixtureRealDensity P θ p n k hk h = 0 from hdz]
    simpa using hB
  · have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hdz)
    rw [conditionalTranscriptPrefixDirectionalScore, abs_div,
      abs_of_nonneg hd]
    exact (div_le_iff₀ hdpos).2 (by simpa [d] using hn)

/-- the conditional transcript prefix directional score mem lp two assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hk), [the conditional Transcript Prefix Directional Score mem Lp two](goal).

Under the stated assumptions, the conditional Transcript Prefix Directional Score mem Lp two. -/
lemma conditionalTranscriptPrefixDirectionalScore_memLp_two
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (n k : ℕ) (hk : k ≤ n) :
    MemLp (conditionalTranscriptPrefixDirectionalScore P θ v p n k hk) 2
      (transcriptPrefixLaw P θ p n k hk) := by
  letI : IsProbabilityMeasure (transcriptPrefixLaw P θ p n k hk) :=
    transcriptPrefixLaw_isProbability P θ p hp hθ n k hk
  apply MemLp.of_bound
    ((measurable_transcriptPrefixMixtureRealDerivative P θ v p n k hk).div
      (measurable_transcriptPrefixMixtureRealDensity P θ p n k hk)).aestronglyMeasurable
    (inputPathScoreBound (n := n) θ v p)
  filter_upwards with h
  rw [Real.norm_eq_abs]
  exact abs_conditionalTranscriptPrefixDirectionalScore_le
    P θ v p hp hθ n k hk h

/-- the conditional transcript prefix directional score sq integrable assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hk), [the conditional Transcript Prefix Directional Score sq integrable](goal).

Under the stated assumptions, the conditional Transcript Prefix Directional Score sq integrable. -/
lemma conditionalTranscriptPrefixDirectionalScore_sq_integrable
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (n k : ℕ) (hk : k ≤ n) :
    Integrable (fun h =>
      conditionalTranscriptPrefixDirectionalScore P θ v p n k hk h ^ 2)
      (transcriptPrefixLaw P θ p n k hk) :=
  (conditionalTranscriptPrefixDirectionalScore_memLp_two
    P θ v p hp hθ n k hk).integrable_sq

/-- the actual successor score in coordinates sq integrable assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hk), [the actual Successor Score In Coordinates sq integrable](goal).

Under the stated assumptions, the actual Successor Score In Coordinates sq integrable. -/
lemma actualSuccessorScoreInCoordinates_sq_integrable
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (n k : ℕ) (hk : k + 1 ≤ n) :
    Integrable (fun z => actualSuccessorScoreInCoordinates P θ v p n k hk z ^ 2)
      (outputLaw θ p (sequentialJointChannel P n (canonicalNextIndex hk)
        (transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk)))) := by
  rw [← transcriptSuccessorLaw_map_canonicalInitLast P θ p hp hθ n k hk]
  have hm : Measurable (fun z =>
      actualSuccessorScoreInCoordinates P θ v p n k hk z ^ 2) :=
    (measurable_actualSuccessorScoreInCoordinates P θ v p n k hk).pow_const 2
  rw [integrable_map_measure
    hm.aestronglyMeasurable
    (measurable_canonicalInitLast hk).aemeasurable]
  simpa [Function.comp_def, actualSuccessorScoreInCoordinates] using
    (conditionalTranscriptPrefixDirectionalScore_sq_integrable
      P θ v p hp hθ n (k + 1) hk)

/-- the lifted prefix directional score sq integrable successor law assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hk), [the lifted Prefix Directional Score sq integrable successor Law](goal).

Under the stated assumptions, the lifted Prefix Directional Score sq integrable successor Law. -/
lemma liftedPrefixDirectionalScore_sq_integrable_successorLaw
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (n k : ℕ) (hk : k + 1 ≤ n) :
    Integrable (fun z => liftedPrefixDirectionalScore P θ v p n k hk z ^ 2)
      (outputLaw θ p (sequentialJointChannel P n (canonicalNextIndex hk)
        (transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk)))) := by
  let i := canonicalNextIndex hk
  let μ := transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk)
  let K : Kernel (History (Z n) k (Nat.le_of_succ_le hk)) (Z n i) :=
    (observedStageKernel P θ p n i).comap
      (fun h => ((), h)) (measurable_const.prodMk measurable_id)
  letI : IsProbabilityMeasure μ :=
    transcriptPrefixLaw_isProbability P θ p hp hθ n k (Nat.le_of_succ_le hk)
  letI : IsMarkovKernel (observedStageKernel P θ p n i) :=
    observedStageKernel_isMarkov P θ p hp hθ n i
  letI : IsMarkovKernel K := by
    dsimp [K]
    infer_instance
  have hout : outputLaw θ p (sequentialJointChannel P n i μ) = μ ⊗ₘ K := by
    simpa [K] using outputLaw_sequentialJointChannel P θ p hp hθ n i μ
  rw [hout]
  have hmeas : AEStronglyMeasurable
      (fun z => liftedPrefixDirectionalScore P θ v p n k hk z ^ 2) (μ ⊗ₘ K) := by
    have hm : Measurable (fun z =>
        liftedPrefixDirectionalScore P θ v p n k hk z ^ 2) :=
      (measurable_liftedPrefixDirectionalScore P θ v p n k hk).pow_const 2
    exact hm.aestronglyMeasurable
  rw [Measure.integrable_compProd_iff hmeas]
  constructor
  · filter_upwards with h
    simpa [liftedPrefixDirectionalScore] using
      (integrable_const
        (conditionalTranscriptPrefixDirectionalScore P θ v p n k
          (Nat.le_of_succ_le hk) h ^ 2) : Integrable _ (K h))
  · simpa [liftedPrefixDirectionalScore, μ] using
      (conditionalTranscriptPrefixDirectionalScore_sq_integrable
        P θ v p hp hθ n k (Nat.le_of_succ_le hk)).norm

/-- the channel directional score sq integrable successor law assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hk), [the channel Directional Score sq integrable successor Law](goal).

Under the stated assumptions, the channel Directional Score sq integrable successor Law. -/
lemma channelDirectionalScore_sq_integrable_successorLaw
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (n k : ℕ) (hk : k + 1 ≤ n) :
    Integrable (fun z => channelDirectionalScore θ p
      (sequentialJointChannel P n (canonicalNextIndex hk)
        (transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk))) v z ^ 2)
      (outputLaw θ p (sequentialJointChannel P n (canonicalNextIndex hk)
        (transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk)))) := by
  let ν := outputLaw θ p (sequentialJointChannel P n (canonicalNextIndex hk)
    (transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk)))
  have ha := actualSuccessorScoreInCoordinates_sq_integrable
    P θ v p hp hθ n k hk
  have hl := liftedPrefixDirectionalScore_sq_integrable_successorLaw
    P θ v p hp hθ n k hk
  have hmaMeas : AEStronglyMeasurable
      (actualSuccessorScoreInCoordinates P θ v p n k hk) ν := by
    exact (measurable_actualSuccessorScoreInCoordinates P θ v p n k hk)
      |>.aestronglyMeasurable
  have hmlMeas : AEStronglyMeasurable
      (liftedPrefixDirectionalScore P θ v p n k hk) ν := by
    exact (measurable_liftedPrefixDirectionalScore P θ v p n k hk)
      |>.aestronglyMeasurable
  have hma : MemLp (actualSuccessorScoreInCoordinates P θ v p n k hk) 2 ν :=
    (memLp_two_iff_integrable_sq hmaMeas).2 ha
  have hml : MemLp (liftedPrefixDirectionalScore P θ v p n k hk) 2 ν :=
    (memLp_two_iff_integrable_sq hmlMeas).2 hl
  have hsub := hma.sub hml
  have hae := actualSuccessorScoreIncrement_ae_eq_channelDirectionalScore
    P θ v p hp hθ n k hk
  exact (((memLp_congr_ae hae).mp hsub).integrable_sq)

/-- the integral channel directional score sq successor law assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hk), [the integral channel Directional Score sq successor Law](goal).

Under the stated assumptions, the integral channel Directional Score sq successor Law. -/
lemma integral_channelDirectionalScore_sq_successorLaw
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (n k : ℕ) (hk : k + 1 ≤ n) :
    ∫ z, channelDirectionalScore θ p
        (sequentialJointChannel P n (canonicalNextIndex hk)
          (transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk))) v z ^ 2
      ∂outputLaw θ p (sequentialJointChannel P n (canonicalNextIndex hk)
        (transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk))) =
      informationQuadratic (channelFisherInfo θ p
        (sequentialJointChannel P n (canonicalNextIndex hk)
          (transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk)))) v := by
  let μ := transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk)
  let Q := sequentialJointChannel P n (canonicalNextIndex hk) μ
  let ν := dominatingMeasure Q
  let ρ := outputLaw θ p Q
  letI : IsProbabilityMeasure μ :=
    transcriptPrefixLaw_isProbability P θ p hp hθ n k (Nat.le_of_succ_le hk)
  letI : IsMarkovKernel Q :=
    sequentialJointChannel_isMarkov P n (canonicalNextIndex hk) μ
  letI : IsFiniteMeasure ν := ⟨by simp [ν, dominatingMeasure]⟩
  letI : IsFiniteMeasure ρ := by
    constructor
    dsimp [ρ, outputLaw]
    simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
      smul_eq_mul, measure_univ, mul_one]
    exact ENNReal.sum_lt_top.mpr fun _ _ => ENNReal.ofReal_lt_top
  change (∫ z, channelDirectionalScore θ p Q v z ^ 2 ∂ρ) = _
  rw [← Measure.withDensity_rnDeriv_eq ρ ν
    (outputLaw_ac_dominatingMeasure θ p Q)]
  rw [integral_withDensity_eq_integral_toReal_smul
    (Measure.measurable_rnDeriv ρ ν) (Measure.rnDeriv_lt_top ρ ν)]
  rw [show (∫ z, (ρ.rnDeriv ν z).toReal •
      channelDirectionalScore θ p Q v z ^ 2 ∂ν) =
      ∫ z, channelDirectionalScore θ p Q v z ^ 2 *
        channelOutputDensity θ p Q z ∂ν by
    apply integral_congr_ae
    filter_upwards [outputLawDensity_toReal_ae_eq_channelOutputDensity
      θ p Q hp hθ] with z hz
    rw [smul_eq_mul, hz]
    ring]
  exact @integral_sequentialJoint_channelDirectionalScore_sq
    Z _ ε P θ v p hp hθ n (canonicalNextIndex hk) μ _

/-- the successor channel fisher le upper envelope assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hε,hk), [the successor channel Fisher le upper Envelope](goal).

Under the stated assumptions, the successor channel Fisher le upper Envelope. -/
lemma successor_channelFisher_le_upperEnvelope
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ : TrialParameter) (p t : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε)
    (n k : ℕ) (hk : k + 1 ≤ n) :
    ∫ z, channelDirectionalScore θ p
        (sequentialJointChannel P n (canonicalNextIndex hk)
          (transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk)))
        (direction t) z ^ 2
      ∂outputLaw θ p (sequentialJointChannel P n (canonicalNextIndex hk)
        (transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk))) ≤
      upperEnvelope θ p ε t := by
  rw [integral_channelDirectionalScore_sq_successorLaw
    P θ (direction t) p hp hθ n k hk]
  letI : IsProbabilityMeasure
      (transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk)) :=
    transcriptPrefixLaw_isProbability P θ p hp hθ n k (Nat.le_of_succ_le hk)
  exact sequentialJointChannel_fisher_le_upperEnvelope P n
    (canonicalNextIndex hk)
    (transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk))
    θ p t hp hθ hε

/-- Under [the supplied quantities and conditions](hyp:p,v), [the sum input directional derivative eq zero assertion](goal) holds. -/
lemma sum_inputDirectionalDerivative_eq_zero (p : ℝ) (v : TrialParameter) :
    ∑ a : Fin 4, inputDirectionalDerivative p v a = 0 := by
  unfold inputDirectionalDerivative inputDerivative
  simp [Fin.sum_univ_succ]

/-- The current channel score has zero integral on every event determined by the predecessor history. This is the exact first-marginal centering input for the remaining cross-term argument. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hk,hB), [the set Integral channel Directional Score fst preimage eq zero](goal).

Under the stated assumptions, the set Integral channel Directional Score fst preimage eq zero. -/
lemma setIntegral_channelDirectionalScore_fst_preimage_eq_zero
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (n k : ℕ) (hk : k + 1 ≤ n)
    (B : Set (History (Z n) k (Nat.le_of_succ_le hk)))
    (hB : MeasurableSet B) :
    ∫ z in Prod.fst ⁻¹' B, channelDirectionalScore θ p
        (sequentialJointChannel P n (canonicalNextIndex hk)
          (transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk))) v z
      ∂outputLaw θ p (sequentialJointChannel P n (canonicalNextIndex hk)
        (transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk))) = 0 := by
  let μ := transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk)
  let i := canonicalNextIndex hk
  let Q := sequentialJointChannel P n i μ
  letI : IsProbabilityMeasure μ :=
    transcriptPrefixLaw_isProbability P θ p hp hθ n k (Nat.le_of_succ_le hk)
  letI : IsMarkovKernel Q := sequentialJointChannel_isMarkov P n i μ
  have hA : MeasurableSet (Prod.fst ⁻¹' B :
      Set (History (Z n) k (Nat.le_of_succ_le hk) × Z n i)) :=
    hB.preimage measurable_fst
  rw [setIntegral_channelDirectionalScore_outputLaw θ v p Q hp hθ _ hA]
  rw [@setIntegral_sequentialJoint_channelDirectionalScore
    Z _ ε P θ v p hp hθ n i μ _ (Prod.fst ⁻¹' B)]
  unfold sequentialJointEventDerivative
  change (∑ a : Fin 4,
    inputDirectionalDerivative p v a * (Q a (Prod.fst ⁻¹' B)).toReal) = 0
  have hrow (a : Fin 4) : (Q a (Prod.fst ⁻¹' B)).toReal = (μ B).toReal := by
    letI : IsMarkovKernel (P.channel n i) := (P.privacy n).1 i
    rw [show Prod.fst ⁻¹' B = B ×ˢ Set.univ by ext z; simp]
    dsimp [Q, sequentialJointChannel, releasedHistoryRowKernel]
    rw [Kernel.compProd_apply_prod hB MeasurableSet.univ]
    simp_rw [Kernel.comap_apply', measure_univ]
    rw [Kernel.const_apply, setLIntegral_one]
  simp_rw [hrow]
  rw [← Finset.sum_mul]
  rw [sum_inputDirectionalDerivative_eq_zero]
  simp

/-- The score increment is conditionally centered given the predecessor history. This formulation is the one needed to kill the Fisher cross term. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hk), [the cond Exp channel Directional Score fst eq zero](goal).

Under the stated assumptions, the cond Exp channel Directional Score fst eq zero. -/
lemma condExp_channelDirectionalScore_fst_eq_zero
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (n k : ℕ) (hk : k + 1 ≤ n) :
    condExp (MeasurableSpace.comap Prod.fst inferInstance)
      (outputLaw θ p (sequentialJointChannel P n (canonicalNextIndex hk)
        (transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk))))
      (channelDirectionalScore θ p
        (sequentialJointChannel P n (canonicalNextIndex hk)
          (transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk))) v) =ᵐ[
      outputLaw θ p (sequentialJointChannel P n (canonicalNextIndex hk)
        (transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk)))] 0 := by
  let i := canonicalNextIndex hk
  let H := History (Z n) i.val i.isLt.le
  let μ : Measure H := transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk)
  let Q := sequentialJointChannel P n i μ
  let ρ := outputLaw θ p Q
  letI : IsProbabilityMeasure μ :=
    transcriptPrefixLaw_isProbability P θ p hp hθ n k (Nat.le_of_succ_le hk)
  letI : IsMarkovKernel Q :=
    sequentialJointChannel_isMarkov P n (canonicalNextIndex hk) μ
  letI : IsFiniteMeasure ρ := by
    constructor
    dsimp [ρ, outputLaw]
    simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
      smul_eq_mul, measure_univ, mul_one]
    exact ENNReal.sum_lt_top.mpr fun _ _ => ENNReal.ofReal_lt_top
  have hc2 := channelDirectionalScore_sq_integrable_successorLaw
    P θ v p hp hθ n k hk
  have hcMeas : Measurable (channelDirectionalScore θ p Q v) := by
    have hdens (j : Fin 4) : Measurable (channelDensity Q j) :=
      (Measure.measurable_rnDeriv (Q j) (dominatingMeasure Q)).ennreal_toReal
    have hout : Measurable (channelOutputDensity θ p Q) := by
      unfold channelOutputDensity
      exact Finset.measurable_sum _ fun j _ => measurable_const.mul (hdens j)
    have hder : Measurable (channelDirectionalDerivativeDensity p Q v) := by
      unfold channelDirectionalDerivativeDensity channelDerivativeDensity
      exact Finset.measurable_sum _ fun j _ => measurable_const.mul
        (Finset.measurable_sum _ fun a _ => measurable_const.mul (hdens a))
    unfold channelDirectionalScore
    exact (hder.div hout).ite (measurableSet_lt measurable_const hout) measurable_const
  have hcMem : MemLp (channelDirectionalScore θ p Q v) 2 ρ :=
    (memLp_two_iff_integrable_sq hcMeas.aestronglyMeasurable).2 hc2
  have hc : Integrable (channelDirectionalScore θ p Q v) ρ :=
    hcMem.integrable (by norm_num)
  have hm : MeasurableSpace.comap (@Prod.fst H (Z n i)) inferInstance ≤
      (inferInstance : MeasurableSpace (H × Z n i)) :=
    (measurable_fst (α := H) (β := Z n i)).comap_le
  have hz : (fun _ : H × Z n i => (0 : ℝ)) =ᵐ[ρ]
      condExp (MeasurableSpace.comap (@Prod.fst H (Z n i)) inferInstance) ρ
        (channelDirectionalScore θ p Q v) := by
    refine ae_eq_condExp_of_forall_setIntegral_eq hm hc (fun s _ _ => ?_) ?_ ?_
    · exact integrableOn_zero
    · intro s hs _
      obtain ⟨B, hB, rfl⟩ := hs
      simpa [Q, ρ] using (setIntegral_channelDirectionalScore_fst_preimage_eq_zero
        P θ v p hp hθ n k hk B hB).symm
    · exact aestronglyMeasurable_zero
  exact hz.symm

/-- The lifted predecessor score is orthogonal to the current channel-score increment under the actual successor law. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hk), [the integral lifted Prefix mul channel Directional Score eq zero](goal).

Under the stated assumptions, the integral lifted Prefix mul channel Directional Score eq zero. -/
lemma integral_liftedPrefix_mul_channelDirectionalScore_eq_zero
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (n k : ℕ) (hk : k + 1 ≤ n) :
    ∫ z, liftedPrefixDirectionalScore P θ v p n k hk z *
        channelDirectionalScore θ p
          (sequentialJointChannel P n (canonicalNextIndex hk)
            (transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk))) v z
      ∂outputLaw θ p (sequentialJointChannel P n (canonicalNextIndex hk)
        (transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk))) = 0 := by
  let i := canonicalNextIndex hk
  let H := History (Z n) i.val i.isLt.le
  let μ : Measure H := transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk)
  let Q := sequentialJointChannel P n i μ
  let ρ := outputLaw θ p Q
  let past : H × Z n i → ℝ := liftedPrefixDirectionalScore P θ v p n k hk
  let current : H × Z n i → ℝ := channelDirectionalScore θ p Q v
  letI : IsProbabilityMeasure μ :=
    transcriptPrefixLaw_isProbability P θ p hp hθ n k (Nat.le_of_succ_le hk)
  letI : IsMarkovKernel Q := sequentialJointChannel_isMarkov P n i μ
  letI : IsFiniteMeasure ρ := by
    constructor
    dsimp [ρ, outputLaw]
    simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
      smul_eq_mul, measure_univ, mul_one]
    exact ENNReal.sum_lt_top.mpr fun _ _ => ENNReal.ofReal_lt_top
  have hm : MeasurableSpace.comap (@Prod.fst H (Z n i)) inferInstance ≤
      (inferInstance : MeasurableSpace (H × Z n i)) :=
    (measurable_fst (α := H) (β := Z n i)).comap_le
  have hpastMeas : @Measurable (H × Z n i) ℝ
      (MeasurableSpace.comap (@Prod.fst H (Z n i)) inferInstance) (borel ℝ) past := by
    dsimp [past, liftedPrefixDirectionalScore]
    exact (measurable_transcriptPrefixMixtureRealDerivative
      P θ v p n k (Nat.le_of_succ_le hk)).div
        (measurable_transcriptPrefixMixtureRealDensity
          P θ p n k (Nat.le_of_succ_le hk)) |>.comp
            (Measurable.of_comap_le le_rfl)
  have hpastSq := liftedPrefixDirectionalScore_sq_integrable_successorLaw
    P θ v p hp hθ n k hk
  have hcurrentSq := channelDirectionalScore_sq_integrable_successorLaw
    P θ v p hp hθ n k hk
  have hpastMem : MemLp past 2 ρ :=
    (memLp_two_iff_integrable_sq
      (measurable_liftedPrefixDirectionalScore P θ v p n k hk).aestronglyMeasurable).2
      hpastSq
  have hcurrentMeas : Measurable current := by
    dsimp [current]
    have hdens (j : Fin 4) : Measurable (channelDensity Q j) :=
      (Measure.measurable_rnDeriv (Q j) (dominatingMeasure Q)).ennreal_toReal
    have hout : Measurable (channelOutputDensity θ p Q) := by
      unfold channelOutputDensity
      exact Finset.measurable_sum _ fun j _ => measurable_const.mul (hdens j)
    have hder : Measurable (channelDirectionalDerivativeDensity p Q v) := by
      unfold channelDirectionalDerivativeDensity channelDerivativeDensity
      exact Finset.measurable_sum _ fun j _ => measurable_const.mul
        (Finset.measurable_sum _ fun a _ => measurable_const.mul (hdens a))
    unfold channelDirectionalScore
    exact (hder.div hout).ite (measurableSet_lt measurable_const hout) measurable_const
  have hcurrentMem : MemLp current 2 ρ :=
    (memLp_two_iff_integrable_sq hcurrentMeas.aestronglyMeasurable).2 hcurrentSq
  have hprod : Integrable (past * current) ρ :=
    hpastMem.integrable_mul hcurrentMem
  have hcurrentInt : Integrable current ρ := hcurrentMem.integrable (by norm_num)
  have hpull := condExp_mul_of_aestronglyMeasurable_left
    hpastMeas.aestronglyMeasurable hprod hcurrentInt
  have hcenter := condExp_channelDirectionalScore_fst_eq_zero
    P θ v p hp hθ n k hk
  change ∫ z, past z * current z ∂ρ = 0
  calc
    ∫ z, past z * current z ∂ρ =
        ∫ z, condExp (MeasurableSpace.comap (@Prod.fst H (Z n i)) inferInstance)
          ρ (past * current) z ∂ρ := (integral_condExp hm).symm
    _ = ∫ z, past z * condExp
          (MeasurableSpace.comap (@Prod.fst H (Z n i)) inferInstance)
          ρ current z ∂ρ := integral_congr_ae hpull
    _ = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hcenter] with z hz
      have hz' : condExp
          (MeasurableSpace.comap (@Prod.fst H (Z n i)) inferInstance)
          ρ current z = 0 := by
        simpa [current, ρ, Q, μ, i] using hz
      simp [hz']


end CausalSmith.Stat.LdpAteEfficiencySurface
