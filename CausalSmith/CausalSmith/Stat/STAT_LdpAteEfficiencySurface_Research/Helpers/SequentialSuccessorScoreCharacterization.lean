module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.SequentialHistoryTransport

/-! # Event characterization of the successor score candidate -/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open Causalean.Mathlib.Probability.Kernel.FiniteSequence

/-- [the output law ac dominating measure assertion](goal) holds. For [the displayed quantities and conditions](hyp:p,Q), these specify the stated inputs. -/
lemma outputLaw_ac_dominatingMeasure {Y : Type*} [MeasurableSpace Y]
    (θ : TrialParameter) (p : ℝ) (Q : Kernel (Fin 4) Y) :
    outputLaw θ p Q ≪ dominatingMeasure Q := by
  rw [outputLaw, dominatingMeasure]
  apply Measure.AbsolutelyContinuous.mk
  intro A hA href
  simp only [Measure.coe_finsetSum, Finset.sum_apply] at href ⊢
  apply Finset.sum_eq_zero
  intro a _
  rw [Measure.smul_apply, smul_eq_mul]
  apply mul_eq_zero_of_right
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => zero_le)).mp href a
    (Finset.mem_univ a)

/-- the output law density to real ae eq channel output density assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ), [the output Law Density to Real ae eq channel Output Density](goal).

Under the stated assumptions, the output Law Density to Real ae eq channel Output Density. -/
lemma outputLawDensity_toReal_ae_eq_channelOutputDensity
    {Y : Type*} [MeasurableSpace Y]
    (θ : TrialParameter) (p : ℝ) (Q : Kernel (Fin 4) Y)
    [IsMarkovKernel Q] (hp : InteriorAssignment p) (hθ : InteriorMeans θ) :
    (fun y => ((outputLaw θ p Q).rnDeriv (dominatingMeasure Q) y).toReal)
      =ᵐ[dominatingMeasure Q] channelOutputDensity θ p Q := by
  classical
  let ν := dominatingMeasure Q
  let μ (a : Fin 4) := Q a
  let w (a : Fin 4) : ℝ≥0∞ := ENNReal.ofReal (piTheta θ p a)
  letI : IsFiniteMeasure ν := ⟨by simp [ν, dominatingMeasure]⟩
  have hw (a : Fin 4) : w a ≠ ∞ := by simp [w]
  haveI (a : Fin 4) : IsFiniteMeasure (w a • μ a) :=
    (μ a).smul_finite (hw a)
  have hrn (s : Finset (Fin 4)) :
      (s.sum fun a => w a • μ a).rnDeriv ν =ᵐ[ν]
        fun y => s.sum fun a => w a * (μ a).rnDeriv ν y := by
    induction s using Finset.induction_on with
    | empty =>
        filter_upwards [Measure.rnDeriv_zero ν] with y hy
        simpa using hy
    | @insert a s ha ih =>
        haveI : IsFiniteMeasure (s.sum fun b => w b • μ b) := inferInstance
        have hadd := Measure.rnDeriv_add (w a • μ a)
          (s.sum fun b => w b • μ b) ν
        have hsmul := Measure.rnDeriv_smul_left_of_ne_top (μ a) ν (hw a)
        filter_upwards [hadd, hsmul, ih] with y hy hs hi
        simpa [Finset.sum_insert ha, Pi.add_apply, Pi.smul_apply,
          smul_eq_mul, hs, hi] using hy
  have hfinite : ∀ᵐ y ∂ν, ∀ a : Fin 4, (μ a).rnDeriv ν y ≠ ∞ := by
    rw [Filter.eventually_all]
    intro a
    exact (Measure.rnDeriv_lt_top (μ a) ν).mono (fun _ h => ne_of_lt h)
  filter_upwards [hrn Finset.univ, hfinite] with y hy hfin
  change ((outputLaw θ p Q).rnDeriv ν y).toReal =
    channelOutputDensity θ p Q y
  rw [show outputLaw θ p Q = ∑ a : Fin 4, w a • μ a by rfl]
  rw [hy, ENNReal.toReal_sum
    (fun a _ => ENNReal.mul_ne_top (hw a) (hfin a))]
  simp [channelOutputDensity, channelDensity, μ, w, ν, ENNReal.toReal_mul,
    (piTheta_pos_of_interior θ p hp hθ _).le]

/-- [the channel directional derivative density integrable dominating assertion](goal) holds. For [the displayed quantities and conditions](hyp:p,Q,v), these specify the stated inputs. -/
lemma channelDirectionalDerivativeDensity_integrable_dominating
    {Y : Type*} [MeasurableSpace Y]
    (p : ℝ) (Q : Kernel (Fin 4) Y) [IsMarkovKernel Q]
    (v : TrialParameter) :
    Integrable (channelDirectionalDerivativeDensity p Q v)
      (dominatingMeasure Q) := by
  have hsum : Integrable (fun y => ∑ a : Fin 4,
      inputDirectionalDerivative p v a * channelDensity Q a y)
      (dominatingMeasure Q) :=
    integrable_finsetSum _ fun a _ =>
      (integrable_channelDensity_dominating Q a).const_mul _
  exact hsum.congr (ae_of_all _ fun y =>
    (channelDirectionalDerivativeDensity_eq_inputSum p Q v y).symm)

/-- the channel directional score integrable output law assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ), [the channel Directional Score integrable output Law](goal).

Under the stated assumptions, the channel Directional Score integrable output Law. -/
lemma channelDirectionalScore_integrable_outputLaw
    {Y : Type*} [MeasurableSpace Y]
    (θ v : TrialParameter) (p : ℝ) (Q : Kernel (Fin 4) Y)
    [IsMarkovKernel Q] (hp : InteriorAssignment p) (hθ : InteriorMeans θ) :
    Integrable (channelDirectionalScore θ p Q v) (outputLaw θ p Q) := by
  let ν := dominatingMeasure Q
  let μ := outputLaw θ p Q
  letI : IsFiniteMeasure ν := ⟨by simp [ν, dominatingMeasure]⟩
  letI : IsFiniteMeasure μ := by
    constructor
    dsimp [μ, outputLaw]
    simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
      smul_eq_mul, measure_univ, mul_one]
    exact ENNReal.sum_lt_top.mpr fun _ _ => ENNReal.ofReal_lt_top
  change Integrable (channelDirectionalScore θ p Q v) μ
  rw [← Measure.withDensity_rnDeriv_eq μ ν
    (outputLaw_ac_dominatingMeasure θ p Q)]
  rw [integrable_withDensity_iff_integrable_smul'
    (Measure.measurable_rnDeriv μ ν) (Measure.rnDeriv_lt_top μ ν)]
  have hderiv := channelDirectionalDerivativeDensity_integrable_dominating p Q v
  refine hderiv.congr ?_
  filter_upwards [outputLawDensity_toReal_ae_eq_channelOutputDensity
    θ p Q hp hθ] with y hdensity
  rw [smul_eq_mul, hdensity, mul_comm,
    channelDirectionalScore_mul_outputDensity θ v p Q hp hθ y]

/-- the set integral channel directional score output law assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hA), [the set Integral channel Directional Score output Law](goal).

Under the stated assumptions, the set Integral channel Directional Score output Law. -/
lemma setIntegral_channelDirectionalScore_outputLaw
    {Y : Type*} [MeasurableSpace Y]
    (θ v : TrialParameter) (p : ℝ) (Q : Kernel (Fin 4) Y)
    [IsMarkovKernel Q] (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (A : Set Y) (hA : MeasurableSet A) :
    ∫ y in A, channelDirectionalScore θ p Q v y ∂outputLaw θ p Q =
      ∫ y in A, channelDirectionalScore θ p Q v y *
        channelOutputDensity θ p Q y ∂dominatingMeasure Q := by
  let ν := dominatingMeasure Q
  let μ := outputLaw θ p Q
  letI : IsFiniteMeasure ν := ⟨by simp [ν, dominatingMeasure]⟩
  letI : IsFiniteMeasure μ := by
    constructor
    dsimp [μ, outputLaw]
    simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
      smul_eq_mul, measure_univ, mul_one]
    exact ENNReal.sum_lt_top.mpr fun _ _ => ENNReal.ofReal_lt_top
  change (∫ y in A, channelDirectionalScore θ p Q v y ∂μ) = _
  rw [← Measure.withDensity_rnDeriv_eq μ ν
    (outputLaw_ac_dominatingMeasure θ p Q)]
  simp_rw [← integral_indicator hA]
  rw [integral_withDensity_eq_integral_toReal_smul
    (Measure.measurable_rnDeriv μ ν) (Measure.rnDeriv_lt_top μ ν)]
  apply integral_congr_ae
  filter_upwards [outputLawDensity_toReal_ae_eq_channelOutputDensity
    θ p Q hp hθ] with y hdensity
  have hdensity' : (μ.rnDeriv ν y).toReal =
      channelOutputDensity θ p Q y := by
    simpa [μ, ν] using hdensity
  by_cases hy : y ∈ A
  · simp [hy, smul_eq_mul, hdensity']
    ring
  · simp [hy]

/-- The prefix score lifted to successor coordinates. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. [The lifted Prefix Directional Score](goal) is determined by [the displayed parameters](hyp:P,θ,v,p,n,k,hk,z). -/
def liftedPrefixDirectionalScore {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (n k : ℕ) (hk : k + 1 ≤ n)
    (z : History (Z n) k (Nat.le_of_succ_le hk) ×
      Z n (canonicalNextIndex hk)) : ℝ :=
  conditionalTranscriptPrefixDirectionalScore P θ v p n k
    (Nat.le_of_succ_le hk) z.1

/-- [the measurable lifted prefix directional score assertion](goal) holds. For [the displayed quantities and conditions](hyp:P,v,p,n,k,hk), these specify the stated inputs. -/
lemma measurable_liftedPrefixDirectionalScore
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (n k : ℕ) (hk : k + 1 ≤ n) :
    Measurable (liftedPrefixDirectionalScore P θ v p n k hk) := by
  unfold liftedPrefixDirectionalScore conditionalTranscriptPrefixDirectionalScore
  exact ((measurable_transcriptPrefixMixtureRealDerivative P θ v p n k
    (Nat.le_of_succ_le hk)).div
      (measurable_transcriptPrefixMixtureRealDensity P θ p n k
        (Nat.le_of_succ_le hk))).comp measurable_fst

/-- the conditional transcript prefix directional score integrable assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hk), [the conditional Transcript Prefix Directional Score integrable](goal).

Under the stated assumptions, the conditional Transcript Prefix Directional Score integrable. -/
lemma conditionalTranscriptPrefixDirectionalScore_integrable
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (n k : ℕ) (hk : k + 1 ≤ n) :
    Integrable (conditionalTranscriptPrefixDirectionalScore P θ v p n k
      (Nat.le_of_succ_le hk))
      (transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk)) := by
  letI : IsMarkovKernel (P.channel n (nextIndex hk)) :=
    (P.privacy n).1 (nextIndex hk)
  have h :=
    integrable_conditionalTranscriptPrefixDirectionalScore_mul_successorRowKernelSection
      P θ v p hp hθ n k hk (0 : Fin 4) Set.univ MeasurableSet.univ
  simpa [successorRowKernelSection] using h

/-- Exact event characterization before the final projection step. The past part is in its verified row-disintegrated form, while the current channel score is integrated against the actual joint-channel output law. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hk,hA), [the successor Event Derivative eq past Rows add current Score Integral](goal).

Under the stated assumptions, the successor Event Derivative eq past Rows add current Score Integral. -/
-- keep: reusable sequential-law, Fisher-information, or van-Trees bridge for related adaptive experiments
lemma successorEventDerivative_eq_pastRows_add_currentScoreIntegral
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (n k : ℕ) (hk : k + 1 ≤ n)
    (A : Set (History (Z n) k (Nat.le_of_succ_le hk) ×
      Z n (nextIndex hk))) (hA : MeasurableSet A) :
    predecessorSuccessorEventDerivative θ p
        (fun a => predecessorRowEventDerivative P θ v p n k hk a A) +
      sequentialJointEventDerivative P v p n (nextIndex hk)
        (transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk)) A =
      (∑ a : Fin 4, piTheta θ p a *
        ∫ h, conditionalTranscriptPrefixDirectionalScore P θ v p n k
            (Nat.le_of_succ_le hk) h *
          successorRowKernelSection P n k hk a A h
          ∂transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk)) +
      ∫ z in A, channelDirectionalScore θ p
        (sequentialJointChannel P n (nextIndex hk)
          (transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk))) v z
        ∂outputLaw θ p (sequentialJointChannel P n (nextIndex hk)
          (transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk))) := by
  rw [predecessorSuccessorEventDerivative_eq_sum_integral_pastScore
    P θ v p hp hθ n k hk A hA]
  let μ := transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk)
  let Q := sequentialJointChannel P n (nextIndex hk) μ
  have hμ : IsProbabilityMeasure μ :=
    transcriptPrefixLaw_isProbability P θ p hp hθ n k (Nat.le_of_succ_le hk)
  have hQ : IsMarkovKernel Q := @sequentialJointChannel_isMarkov
    Z _ ε P n (nextIndex hk) μ hμ
  have hcurrent := (transcriptSuccessorLaw_jointScore_characterization
    P θ v p hp hθ n k hk A).2.1
  have hchange := @setIntegral_channelDirectionalScore_outputLaw
    _ _ θ v p Q hQ hp hθ A hA
  change _ + sequentialJointEventDerivative P v p n (nextIndex hk) μ A =
    _ + ∫ z in A, channelDirectionalScore θ p Q v z ∂outputLaw θ p Q
  rw [hchange, hcurrent]

/-- the lifted prefix directional score integrable successor law assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hk), [the lifted Prefix Directional Score integrable successor Law](goal).

Under the stated assumptions, the lifted Prefix Directional Score integrable successor Law. -/
lemma liftedPrefixDirectionalScore_integrable_successorLaw
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (n k : ℕ) (hk : k + 1 ≤ n) :
    Integrable (liftedPrefixDirectionalScore P θ v p n k hk)
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
  letI : IsMarkovKernel (P.channel n i) := (P.privacy n).1 i
  letI : IsMarkovKernel K := by
    dsimp [K]
    infer_instance
  have hout : outputLaw θ p (sequentialJointChannel P n i μ) = μ ⊗ₘ K := by
    simpa [K] using outputLaw_sequentialJointChannel P θ p hp hθ n i μ
  rw [hout]
  have hscore := conditionalTranscriptPrefixDirectionalScore_integrable
    P θ v p hp hθ n k hk
  have hmeas : AEStronglyMeasurable
      (liftedPrefixDirectionalScore P θ v p n k hk) (μ ⊗ₘ K) :=
    (measurable_liftedPrefixDirectionalScore P θ v p n k hk).aestronglyMeasurable
  rw [Measure.integrable_compProd_iff hmeas]
  constructor
  · filter_upwards with h
    simpa [liftedPrefixDirectionalScore] using
      (integrable_const
        (conditionalTranscriptPrefixDirectionalScore P θ v p n k
          (Nat.le_of_succ_le hk) h) : Integrable _ (K h))
  · simpa [liftedPrefixDirectionalScore, μ] using hscore.norm

/-- the set integral lifted prefix directional score successor law assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hk,hA), [the set Integral lifted Prefix Directional Score successor Law](goal).

Under the stated assumptions, the set Integral lifted Prefix Directional Score successor Law. -/
lemma setIntegral_liftedPrefixDirectionalScore_successorLaw
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (n k : ℕ) (hk : k + 1 ≤ n)
    (A : Set (History (Z n) k (Nat.le_of_succ_le hk) ×
      Z n (canonicalNextIndex hk))) (hA : MeasurableSet A) :
    ∫ z in A, liftedPrefixDirectionalScore P θ v p n k hk z
        ∂outputLaw θ p (sequentialJointChannel P n (canonicalNextIndex hk)
          (transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk))) =
      ∑ a : Fin 4, piTheta θ p a *
        ∫ h, conditionalTranscriptPrefixDirectionalScore P θ v p n k
            (Nat.le_of_succ_le hk) h *
          ((P.channel n (canonicalNextIndex hk))
            (a, fsHistoryToPrivate (canonicalNextIndex hk) h)
            (Prod.mk h ⁻¹' A)).toReal
          ∂transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk) := by
  let i := canonicalNextIndex hk
  let μ := transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk)
  let K : Kernel (History (Z n) k (Nat.le_of_succ_le hk)) (Z n i) :=
    (observedStageKernel P θ p n i).comap
      (fun h => ((), h)) (measurable_const.prodMk measurable_id)
  letI : IsProbabilityMeasure μ :=
    transcriptPrefixLaw_isProbability P θ p hp hθ n k (Nat.le_of_succ_le hk)
  letI : IsMarkovKernel (observedStageKernel P θ p n i) :=
    observedStageKernel_isMarkov P θ p hp hθ n i
  letI : IsMarkovKernel (P.channel n i) := (P.privacy n).1 i
  letI : IsMarkovKernel K := by
    dsimp [K]
    infer_instance
  have hout : outputLaw θ p (sequentialJointChannel P n i μ) = μ ⊗ₘ K := by
    simpa [K] using outputLaw_sequentialJointChannel P θ p hp hθ n i μ
  rw [hout, ← integral_indicator hA]
  have hint : Integrable (A.indicator
      (liftedPrefixDirectionalScore P θ v p n k hk)) (μ ⊗ₘ K) := by
    rw [← hout]
    simpa only [nextIndex_eq_canonicalNextIndex] using
      (liftedPrefixDirectionalScore_integrable_successorLaw
        P θ v p hp hθ n k hk).indicator hA
  rw [Measure.integral_compProd hint]
  have hsection (h : History (Z n) k (Nat.le_of_succ_le hk)) :
      MeasurableSet (Prod.mk h ⁻¹' A) :=
    hA.preimage (measurable_const.prodMk measurable_id)
  have hinner (h : History (Z n) k (Nat.le_of_succ_le hk)) :
      (∫ y, A.indicator (liftedPrefixDirectionalScore P θ v p n k hk)
        (h, y) ∂K h) =
      conditionalTranscriptPrefixDirectionalScore P θ v p n k
        (Nat.le_of_succ_le hk) h *
        ∑ a : Fin 4, piTheta θ p a *
          ((P.channel n i) (a, fsHistoryToPrivate i h)
            (Prod.mk h ⁻¹' A)).toReal := by
    rw [show (fun y => A.indicator
        (liftedPrefixDirectionalScore P θ v p n k hk) (h, y)) =
        (Prod.mk h ⁻¹' A).indicator (fun _ =>
          conditionalTranscriptPrefixDirectionalScore P θ v p n k
            (Nat.le_of_succ_le hk) h) by
      funext y
      by_cases hy : (h, y) ∈ A <;> simp [hy, liftedPrefixDirectionalScore]]
    rw [integral_indicator (hsection h), setIntegral_const]
    dsimp [K]
    simp only [observedStageKernel_apply, measureReal_def]
    rw [Measure.finsetSum_apply, ENNReal.toReal_sum]
    · simp only [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
          ENNReal.toReal_ofReal (piTheta_pos_of_interior θ p hp hθ _).le]
      ring
    · intro a _
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  rw [show (fun h => ∫ y, A.indicator
      (liftedPrefixDirectionalScore P θ v p n k hk) (h, y) ∂K h) =
      fun h => conditionalTranscriptPrefixDirectionalScore P θ v p n k
          (Nat.le_of_succ_le hk) h *
        ∑ a : Fin 4, piTheta θ p a *
          ((P.channel n i) (a, fsHistoryToPrivate i h)
            (Prod.mk h ⁻¹' A)).toReal by
    funext h
    exact hinner h]
  simp only [Finset.mul_sum]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro a _
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with h
    ring
  · intro a _
    let Krow : Kernel (History (Z n) k (Nat.le_of_succ_le hk)) (Z n i) :=
      (P.channel n i).comap
        (fun h => (a, fsHistoryToPrivate i h))
        (measurable_const.prodMk (measurable_fsHistoryToPrivate i))
    have hmeas : Measurable (fun h : History (Z n) k (Nat.le_of_succ_le hk) =>
        ((P.channel n i) (a, fsHistoryToPrivate i h)
          (Prod.mk h ⁻¹' A)).toReal) :=
      (Krow.measurable_kernel_prodMk_left hA).ennreal_toReal
    have hbounded : ∀ h, ‖((P.channel n i)
        (a, fsHistoryToPrivate i h) (Prod.mk h ⁻¹' A)).toReal‖ ≤ 1 := by
      intro h
      rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      apply ENNReal.toReal_mono ENNReal.one_ne_top
      calc
        _ ≤ (P.channel n i) (a, fsHistoryToPrivate i h) Set.univ :=
          measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      ((conditionalTranscriptPrefixDirectionalScore_integrable
      P θ v p hp hθ n k hk).bdd_mul hmeas.aestronglyMeasurable
        (ae_of_all _ hbounded)).const_mul (piTheta θ p a)

/-- The full successor score candidate: the inherited prefix score plus the directional score of the current privatization channel. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. [The successor Directional Score Candidate](goal) is determined by [the displayed parameters](hyp:P,θ,v,p,n,k,hk,z). -/
def successorDirectionalScoreCandidate {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (n k : ℕ) (hk : k + 1 ≤ n)
    (z : History (Z n) k (Nat.le_of_succ_le hk) ×
      Z n (canonicalNextIndex hk)) : ℝ :=
  liftedPrefixDirectionalScore P θ v p n k hk z +
    channelDirectionalScore θ p
      (sequentialJointChannel P n (canonicalNextIndex hk)
        (transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk))) v z

/-- the successor directional score candidate integrable assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hk), [the successor Directional Score Candidate integrable](goal).

Under the stated assumptions, the successor Directional Score Candidate integrable. -/
lemma successorDirectionalScoreCandidate_integrable
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (n k : ℕ) (hk : k + 1 ≤ n) :
    Integrable (successorDirectionalScoreCandidate P θ v p n k hk)
      (outputLaw θ p (sequentialJointChannel P n (canonicalNextIndex hk)
        (transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk)))) := by
  let μ := transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk)
  let Q := sequentialJointChannel P n (canonicalNextIndex hk) μ
  letI : IsProbabilityMeasure μ :=
    transcriptPrefixLaw_isProbability P θ p hp hθ n k (Nat.le_of_succ_le hk)
  letI : IsMarkovKernel Q := sequentialJointChannel_isMarkov
    P n (canonicalNextIndex hk) μ
  exact (liftedPrefixDirectionalScore_integrable_successorLaw
    P θ v p hp hθ n k hk).add
      (channelDirectionalScore_integrable_outputLaw θ v p Q hp hθ)

/-- Canonical successor-coordinate packaging of the entire event derivative coefficient as one score integral. The first term is the derivative carried by the predecessor law and the second is the current-channel derivative. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hk,hA), [the set Integral successor Directional Score Candidate successor Law](goal).

Under the stated assumptions, the set Integral successor Directional Score Candidate successor Law. -/
lemma setIntegral_successorDirectionalScoreCandidate_successorLaw
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (n k : ℕ) (hk : k + 1 ≤ n)
    (A : Set (History (Z n) k (Nat.le_of_succ_le hk) ×
      Z n (canonicalNextIndex hk))) (hA : MeasurableSet A) :
    ∫ z in A, successorDirectionalScoreCandidate P θ v p n k hk z
        ∂outputLaw θ p (sequentialJointChannel P n (canonicalNextIndex hk)
          (transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk))) =
      (∑ a : Fin 4, piTheta θ p a *
        ∫ h, conditionalTranscriptPrefixDirectionalScore P θ v p n k
            (Nat.le_of_succ_le hk) h *
          ((P.channel n (canonicalNextIndex hk))
            (a, fsHistoryToPrivate (canonicalNextIndex hk) h)
            (Prod.mk h ⁻¹' A)).toReal
          ∂transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk)) +
      sequentialJointEventDerivative P v p n (canonicalNextIndex hk)
        (transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk)) A := by
  let μ := transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk)
  let Q := sequentialJointChannel P n (canonicalNextIndex hk) μ
  letI : IsProbabilityMeasure μ :=
    transcriptPrefixLaw_isProbability P θ p hp hθ n k (Nat.le_of_succ_le hk)
  letI : IsMarkovKernel Q := sequentialJointChannel_isMarkov
    P n (canonicalNextIndex hk) μ
  have hpast := liftedPrefixDirectionalScore_integrable_successorLaw
    P θ v p hp hθ n k hk
  have hcurrent := channelDirectionalScore_integrable_outputLaw θ v p Q hp hθ
  change (∫ z in A, liftedPrefixDirectionalScore P θ v p n k hk z +
      channelDirectionalScore θ p Q v z ∂outputLaw θ p Q) = _
  rw [integral_add hpast.integrableOn hcurrent.integrableOn]
  rw [setIntegral_liftedPrefixDirectionalScore_successorLaw
    P θ v p hp hθ n k hk A hA]
  rw [setIntegral_channelDirectionalScore_outputLaw
    θ v p Q hp hθ A hA]
  exact congrArg (fun x => _ + x)
    (@setIntegral_sequentialJoint_channelDirectionalScore
      Z _ ε P θ v p hp hθ n (canonicalNextIndex hk) μ _ A)

/-- The actual predecessor-plus-current successor derivative equals the single integral of the full candidate score. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hk,hA), [the successor Event Derivative eq set Integral successor Directional Score Candidate](goal).

Under the stated assumptions, the successor Event Derivative eq set Integral successor Directional Score Candidate. -/
lemma successorEventDerivative_eq_setIntegral_successorDirectionalScoreCandidate
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (n k : ℕ) (hk : k + 1 ≤ n)
    (A : Set (History (Z n) k (Nat.le_of_succ_le hk) ×
      Z n (canonicalNextIndex hk))) (hA : MeasurableSet A) :
    predecessorSuccessorEventDerivative θ p
        (fun a => predecessorRowEventDerivative P θ v p n k hk a A) +
      sequentialJointEventDerivative P v p n (canonicalNextIndex hk)
        (transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk)) A =
      ∫ z in A, successorDirectionalScoreCandidate P θ v p n k hk z
        ∂outputLaw θ p (sequentialJointChannel P n (canonicalNextIndex hk)
          (transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk))) := by
  rw [setIntegral_successorDirectionalScoreCandidate_successorLaw
    P θ v p hp hθ n k hk A hA]
  rw [predecessorSuccessorEventDerivative_eq_sum_integral_pastScore
    P θ v p hp hθ n k hk A hA]
  unfold successorRowKernelSection
  cases nextIndex_eq_canonicalNextIndex hk
  rfl

end CausalSmith.Stat.LdpAteEfficiencySurface
