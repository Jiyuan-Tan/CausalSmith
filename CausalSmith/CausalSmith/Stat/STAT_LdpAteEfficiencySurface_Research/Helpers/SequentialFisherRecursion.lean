module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.SequentialFisherInformation

/-! # Finite sequential Fisher recursion -/

@[expose] public section
noncomputable section
namespace CausalSmith.Stat.LdpAteEfficiencySurface

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open Causalean.Mathlib.Probability.Kernel.FiniteSequence

/-- the integral lifted prefix score sq eq prefix score sq assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hk), [the integral lifted Prefix Score sq eq prefix Score sq](goal).

Under the stated assumptions, the integral lifted Prefix Score sq eq prefix Score sq. -/
lemma integral_liftedPrefixScore_sq_eq_prefixScore_sq
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (n k : ℕ) (hk : k + 1 ≤ n) :
    ∫ z, liftedPrefixDirectionalScore P θ v p n k hk z ^ 2
      ∂outputLaw θ p (sequentialJointChannel P n (canonicalNextIndex hk)
        (transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk))) =
      ∫ h, conditionalTranscriptPrefixDirectionalScore P θ v p n k
          (Nat.le_of_succ_le hk) h ^ 2
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
  letI : IsMarkovKernel K := by
    dsimp [K]
    infer_instance
  have hout : outputLaw θ p (sequentialJointChannel P n i μ) = μ ⊗ₘ K := by
    simpa [K] using outputLaw_sequentialJointChannel P θ p hp hθ n i μ
  have hint := liftedPrefixDirectionalScore_sq_integrable_successorLaw
    P θ v p hp hθ n k hk
  have hint' : Integrable
      (fun z => liftedPrefixDirectionalScore P θ v p n k hk z ^ 2) (μ ⊗ₘ K) := by
    rw [← hout]
    simpa [i, μ] using hint
  rw [hout, Measure.integral_compProd hint']
  simp [liftedPrefixDirectionalScore, μ]

/-- the integral actual successor score sq eq prefix successor score sq assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hk), [the integral actual Successor Score sq eq prefix Successor Score sq](goal).

Under the stated assumptions, the integral actual Successor Score sq eq prefix Successor Score sq. -/
lemma integral_actualSuccessorScore_sq_eq_prefixSuccessorScore_sq
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (n k : ℕ) (hk : k + 1 ≤ n) :
    ∫ z, actualSuccessorScoreInCoordinates P θ v p n k hk z ^ 2
      ∂outputLaw θ p (sequentialJointChannel P n (canonicalNextIndex hk)
        (transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk))) =
      ∫ h, conditionalTranscriptPrefixDirectionalScore P θ v p n (k + 1) hk h ^ 2
        ∂transcriptPrefixLaw P θ p n (k + 1) hk := by
  rw [← transcriptSuccessorLaw_map_canonicalInitLast P θ p hp hθ n k hk]
  have hm : Measurable (fun z =>
      actualSuccessorScoreInCoordinates P θ v p n k hk z ^ 2) :=
    (measurable_actualSuccessorScoreInCoordinates P θ v p n k hk).pow_const 2
  rw [integral_map (measurable_canonicalInitLast hk).aemeasurable hm.aestronglyMeasurable]
  simp [Function.comp_def, actualSuccessorScoreInCoordinates]


/-- [the measurable channel directional score recursion assertion](goal) holds. For [the displayed quantities and conditions](hyp:v,p,Q), these specify the stated inputs. -/
lemma measurable_channelDirectionalScore_recursion
    {Y : Type*} [MeasurableSpace Y]
    (θ v : TrialParameter) (p : ℝ) (Q : Kernel (Fin 4) Y) :
    Measurable (channelDirectionalScore θ p Q v) := by
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

/-- the prefix score energy succ assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hk), [the prefix Score Energy succ](goal).

Under the stated assumptions, the prefix Score Energy succ. -/
lemma prefixScoreEnergy_succ
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (n k : ℕ) (hk : k + 1 ≤ n) :
    (∫ h, conditionalTranscriptPrefixDirectionalScore P θ v p n (k + 1) hk h ^ 2
      ∂transcriptPrefixLaw P θ p n (k + 1) hk) =
      (∫ h, conditionalTranscriptPrefixDirectionalScore P θ v p n k
          (Nat.le_of_succ_le hk) h ^ 2
        ∂transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk)) +
      ∫ z, channelDirectionalScore θ p
          (sequentialJointChannel P n (canonicalNextIndex hk)
            (transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk))) v z ^ 2
        ∂outputLaw θ p (sequentialJointChannel P n (canonicalNextIndex hk)
          (transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk))) := by
  rw [← integral_actualSuccessorScore_sq_eq_prefixSuccessorScore_sq
    P θ v p hp hθ n k hk]
  rw [← integral_liftedPrefixScore_sq_eq_prefixScore_sq
    P θ v p hp hθ n k hk]
  let i := canonicalNextIndex hk
  let H := History (Z n) i.val i.isLt.le
  let ρ : Measure (H × Z n i) :=
    outputLaw θ p (sequentialJointChannel P n (canonicalNextIndex hk)
    (transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk)))
  let A : H × Z n i → ℝ := actualSuccessorScoreInCoordinates P θ v p n k hk
  let L : H × Z n i → ℝ := liftedPrefixDirectionalScore P θ v p n k hk
  let C : H × Z n i → ℝ := channelDirectionalScore θ p
    (sequentialJointChannel P n (canonicalNextIndex hk)
      (transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk))) v
  have hL2 := liftedPrefixDirectionalScore_sq_integrable_successorLaw
    P θ v p hp hθ n k hk
  have hC2 := channelDirectionalScore_sq_integrable_successorLaw
    P θ v p hp hθ n k hk
  have hLMem : MemLp L 2 ρ :=
    (memLp_two_iff_integrable_sq
      (measurable_liftedPrefixDirectionalScore P θ v p n k hk).aestronglyMeasurable).2 hL2
  have hCMem : MemLp C 2 ρ :=
    (memLp_two_iff_integrable_sq
      (measurable_channelDirectionalScore_recursion θ v p _).aestronglyMeasurable).2 hC2
  have hLC : Integrable (L * C) ρ := hLMem.integrable_mul hCMem
  have hae := actualSuccessorScoreInCoordinates_ae_eq_candidate
    P θ v p hp hθ n k hk
  have hcross := integral_liftedPrefix_mul_channelDirectionalScore_eq_zero
    P θ v p hp hθ n k hk
  change (∫ z, A z ^ 2 ∂ρ) = (∫ z, L z ^ 2 ∂ρ) + ∫ z, C z ^ 2 ∂ρ
  calc
    ∫ z, A z ^ 2 ∂ρ = ∫ z, (L z + C z) ^ 2 ∂ρ := by
      apply integral_congr_ae
      filter_upwards [hae] with z hz
      simpa [A, L, C, successorDirectionalScoreCandidate] using
        congrArg (fun x => x ^ 2) hz
    _ = ∫ z, (L z ^ 2 + 2 * (L z * C z)) + C z ^ 2 ∂ρ := by
      congr 1
      funext z
      ring
    _ = (∫ z, L z ^ 2 + 2 * (L z * C z) ∂ρ) +
        ∫ z, C z ^ 2 ∂ρ :=
      integral_add (hLMem.integrable_sq.add (hLC.const_mul 2))
        hCMem.integrable_sq
    _ = ((∫ z, L z ^ 2 ∂ρ) + ∫ z, 2 * (L z * C z) ∂ρ) +
        ∫ z, C z ^ 2 ∂ρ := by
      congr 1
      exact integral_add hLMem.integrable_sq (hLC.const_mul 2)
    _ = ((∫ z, L z ^ 2 ∂ρ) + 2 * ∫ z, L z * C z ∂ρ) +
        ∫ z, C z ^ 2 ∂ρ := by rw [integral_const_mul]
    _ = (∫ z, L z ^ 2 ∂ρ) + ∫ z, C z ^ 2 ∂ρ := by
      rw [show (∫ z, L z * C z ∂ρ) = 0 by simpa [L, C, ρ] using hcross]
      ring


/-- [the integral transcript prefix mixture real derivative eq zero assertion](goal) holds. For [the displayed quantities and conditions](hyp:P,v,p,n,k,hk), these specify the stated inputs. -/
lemma integral_transcriptPrefixMixtureRealDerivative_eq_zero
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (n k : ℕ) (hk : k ≤ n) :
    ∫ h, transcriptPrefixMixtureRealDerivative P θ v p n k hk h
      ∂transcriptPrefixReferenceMeasure P n k hk = 0 := by
  let ν := transcriptPrefixReferenceMeasure P n k hk
  let μ (x : Fin n → Fin 4) := (P.transcript n x).map (transcriptPrefix hk)
  letI (x : Fin n → Fin 4) : IsProbabilityMeasure (P.transcript n x) :=
    (P.factorizes n x).1
  letI (x : Fin n → Fin 4) : IsProbabilityMeasure (μ x) :=
    Measure.isProbabilityMeasure_map (measurable_transcriptPrefix hk).aemeasurable
  letI : IsFiniteMeasure ν := by
    dsimp [ν, transcriptPrefixReferenceMeasure]
    infer_instance
  have hac (x : Fin n → Fin 4) : μ x ≪ ν := by
    dsimp [μ, ν]
    exact (transcriptComponent_ac_reference P n x).map
      (measurable_transcriptPrefix hk)
  have hint (x : Fin n → Fin 4) : Integrable
      (transcriptPrefixComponentRealDensity P n k hk x) ν := by
    have h := (integrable_toReal_rnDeriv_mul_iff (hac x)
      (f := fun _ => (1 : ℝ))).2 (integrable_const (1 : ℝ))
    change Integrable (fun z => ((μ x).rnDeriv ν z).toReal) ν
    simpa only [mul_one] using h
  unfold transcriptPrefixMixtureRealDerivative
  rw [integral_finset_sum _ (fun x _ => (hint x).const_mul _)]
  calc
    ∑ x : Fin n → Fin 4,
        ∫ h, inputPathDirectionalDerivative θ v p x *
          transcriptPrefixComponentRealDensity P n k hk x h ∂ν =
      ∑ x : Fin n → Fin 4, inputPathDirectionalDerivative θ v p x := by
        apply Finset.sum_congr rfl
        intro x _
        rw [integral_const_mul]
        rw [show (∫ h, transcriptPrefixComponentRealDensity P n k hk x h ∂ν) = 1 by
          unfold transcriptPrefixComponentRealDensity
          rw [Measure.integral_toReal_rnDeriv (hac x)]
          simp [measureReal_def, μ]]
        ring
    _ = 0 := sum_inputPathDirectionalDerivative_eq_zero θ v p

/-- the prefix score energy zero assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,h0), [the prefix Score Energy zero](goal).

Under the stated assumptions, the prefix Score Energy zero. -/
lemma prefixScoreEnergy_zero
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (n : ℕ)
    (h0 : 0 ≤ n) :
    ∫ h, conditionalTranscriptPrefixDirectionalScore P θ v p n 0 h0 h ^ 2
      ∂transcriptPrefixLaw P θ p n 0 h0 = 0 := by
  let μ := transcriptPrefixLaw P θ p n 0 h0
  let emptyHistory : History (Z n) 0 h0 := fun j => j.elim0
  let score := conditionalTranscriptPrefixDirectionalScore P θ v p n 0 h0
  letI : IsProbabilityMeasure μ :=
    transcriptPrefixLaw_isProbability P θ p hp hθ n 0 h0
  have hscoreInt : ∫ h, score h ∂μ = 0 := by
    have hset := setIntegral_conditionalTranscriptPrefixDirectionalScore
      P θ v p hp hθ n 0 h0 Set.univ MeasurableSet.univ
    simpa [score, μ, integral_transcriptPrefixMixtureRealDerivative_eq_zero
      P θ v p n 0 h0] using hset
  have hconst : score = fun _ => score emptyHistory := by
    funext h
    congr 1
    funext j
    exact j.elim0
  rw [hconst] at hscoreInt
  have hvalue : score emptyHistory = 0 := by
    simpa [μ] using hscoreInt
  change ∫ h, score h ^ 2 ∂μ = 0
  rw [hconst]
  simp [hvalue]


/-- the prefix score energy le mul upper envelope assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hε,hk), [the prefix Score Energy le mul upper Envelope](goal).

Under the stated assumptions, the prefix Score Energy le mul upper Envelope. -/
lemma prefixScoreEnergy_le_mul_upperEnvelope
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ : TrialParameter) (p t : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε)
    (n k : ℕ) (hk : k ≤ n) :
    (∫ h, conditionalTranscriptPrefixDirectionalScore P θ (direction t) p n k hk h ^ 2
      ∂transcriptPrefixLaw P θ p n k hk) ≤
      (k : ℝ) * upperEnvelope θ p ε t := by
  induction k with
  | zero =>
      rw [prefixScoreEnergy_zero P θ (direction t) p hp hθ n hk]
      simp
  | succ k ih =>
      have hprev : k ≤ n := Nat.le_of_succ_le hk
      rw [prefixScoreEnergy_succ P θ (direction t) p hp hθ n k hk]
      calc
        (∫ h, conditionalTranscriptPrefixDirectionalScore P θ (direction t) p n k hprev h ^ 2
            ∂transcriptPrefixLaw P θ p n k hprev) +
            ∫ z, channelDirectionalScore θ p
                (sequentialJointChannel P n (canonicalNextIndex hk)
                  (transcriptPrefixLaw P θ p n k hprev)) (direction t) z ^ 2
              ∂outputLaw θ p (sequentialJointChannel P n (canonicalNextIndex hk)
                (transcriptPrefixLaw P θ p n k hprev)) ≤
          (k : ℝ) * upperEnvelope θ p ε t + upperEnvelope θ p ε t :=
            add_le_add (ih hprev)
              (successor_channelFisher_le_upperEnvelope
                P θ p t hp hθ hε n k hk)
        _ = ((k + 1 : ℕ) : ℝ) * upperEnvelope θ p ε t := by
          push_cast
          ring

/-- [the terminal prefix score energy eq transcript score energy assertion](goal) holds. For [the displayed quantities and conditions](hyp:P,v,p,n), these specify the stated inputs. -/
lemma terminalPrefixScoreEnergy_eq_transcriptScoreEnergy
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ) (n : ℕ) :
    (∫ h, conditionalTranscriptPrefixDirectionalScore P θ v p n n (Nat.le_refl n) h ^ 2
      ∂transcriptPrefixLaw P θ p n n (Nat.le_refl n)) =
      ∫ z, conditionalTranscriptDirectionalScore P θ v p n z ^ 2
        ∂transcriptLaw P θ p n := by
  have hmap (μ : Measure (Transcript (Z n))) :
      μ.map (transcriptPrefix (Z := Z n) (Nat.le_refl n)) = μ := by
    have hf : transcriptPrefix (Z := Z n) (Nat.le_refl n) =
        (fun z : Transcript (Z n) => z) := by
      funext z
      funext j
      rfl
    rw [hf]
    exact Measure.map_id'
  unfold conditionalTranscriptPrefixDirectionalScore
    transcriptPrefixMixtureRealDerivative transcriptPrefixMixtureRealDensity
    transcriptPrefixComponentRealDensity transcriptPrefixLaw
    transcriptPrefixReferenceMeasure
  simp_rw [hmap]
  rfl

/-- the transcript directional fisher le mul upper envelope assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hε), [the transcript Directional Fisher le mul upper Envelope](goal).

Under the stated assumptions, the transcript Directional Fisher le mul upper Envelope. -/
lemma transcriptDirectionalFisher_le_mul_upperEnvelope
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ : TrialParameter) (p t : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε)
    (n : ℕ) :
    (∫ z, conditionalTranscriptDirectionalScore P θ (direction t) p n z ^ 2
      ∂transcriptLaw P θ p n) ≤
      (n : ℝ) * upperEnvelope θ p ε t := by
  rw [← terminalPrefixScoreEnergy_eq_transcriptScoreEnergy
    P θ (direction t) p n]
  exact prefixScoreEnergy_le_mul_upperEnvelope
    P θ p t hp hθ hε n n (Nat.le_refl n)


/-- Under [the supplied quantities and conditions](hyp:p,c,v,j), [the input directional derivative scaled direction assertion](goal) holds. -/
lemma inputDirectionalDerivative_scaledDirection
    (p c : ℝ) (v : TrialParameter) (j : Fin 4) :
    inputDirectionalDerivative p (scaledDirection c v) j =
      c * inputDirectionalDerivative p v j := by
  unfold inputDirectionalDerivative scaledDirection
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- [the input path directional derivative scaled direction assertion](goal) holds. For [the displayed quantities and conditions](hyp:v,p,c,x), these specify the stated inputs. -/
lemma inputPathDirectionalDerivative_scaledDirection {n : ℕ}
    (θ v : TrialParameter) (p c : ℝ) (x : Fin n → Fin 4) :
    inputPathDirectionalDerivative θ (scaledDirection c v) p x =
      c * inputPathDirectionalDerivative θ v p x := by
  unfold inputPathDirectionalDerivative
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [inputDirectionalDerivative_scaledDirection]
  ring

/-- [the conditional transcript directional score scaled direction assertion](goal) holds. For [the displayed quantities and conditions](hyp:P,v,p,c,n), these specify the stated inputs. -/
lemma conditionalTranscriptDirectionalScore_scaledDirection
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p c : ℝ) (n : ℕ) :
    conditionalTranscriptDirectionalScore P θ (scaledDirection c v) p n =
      fun z => c * conditionalTranscriptDirectionalScore P θ v p n z := by
  funext z
  unfold conditionalTranscriptDirectionalScore transcriptMixtureRealDerivative
  simp_rw [inputPathDirectionalDerivative_scaledDirection]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  ring

/-- the transcript scaled directional fisher le assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hε), [the transcript Scaled Directional Fisher le](goal).

Under the stated assumptions, the transcript Scaled Directional Fisher le. -/
lemma transcriptScaledDirectionalFisher_le
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ : TrialParameter) (p t c : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) (hε : 0 < ε)
    (n : ℕ) :
    (∫ z, conditionalTranscriptDirectionalScore P θ
        (scaledDirection c (direction t)) p n z ^ 2
      ∂transcriptLaw P θ p n) ≤
      c ^ 2 * ((n : ℝ) * upperEnvelope θ p ε t) := by
  rw [conditionalTranscriptDirectionalScore_scaledDirection]
  rw [show (∫ z, (c * conditionalTranscriptDirectionalScore P θ (direction t) p n z) ^ 2
        ∂transcriptLaw P θ p n) =
      c ^ 2 * ∫ z, conditionalTranscriptDirectionalScore P θ (direction t) p n z ^ 2
        ∂transcriptLaw P θ p n by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with z
    ring]
  exact mul_le_mul_of_nonneg_left
    (transcriptDirectionalFisher_le_mul_upperEnvelope
      P θ p t hp hθ hε n) (sq_nonneg c)

end CausalSmith.Stat.LdpAteEfficiencySurface
