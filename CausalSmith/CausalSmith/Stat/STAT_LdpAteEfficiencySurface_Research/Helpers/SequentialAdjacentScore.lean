module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.SequentialSuccessorScoreCharacterization
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-! # Actual adjacent-prefix score characterization -/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open Causalean.Mathlib.Probability.Kernel.FiniteSequence

/-- Canonical splitting coordinates, with the last coordinate indexed by the
literal successor index rather than by an opaque proof term. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:hk,u), these specify the stated inputs. -/
def canonicalInitLast {n k : ℕ} {Z : Fin n → Type*}
    (hk : k + 1 ≤ n) (u : History Z (k + 1) hk) :
    History Z k (Nat.le_of_succ_le hk) × Z (canonicalNextIndex hk) :=
  (Fin.init u, u (Fin.last k))

/-- The inverse of `canonicalInitLast`. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:hk,u), these specify the stated inputs. -/
def canonicalSnoc {n k : ℕ} {Z : Fin n → Type*}
    (hk : k + 1 ≤ n)
    (u : History Z k (Nat.le_of_succ_le hk) × Z (canonicalNextIndex hk)) :
    History Z (k + 1) hk :=
  Fin.snoc u.1 u.2

/-- [the measurable canonical init last assertion](goal) holds. For [the displayed quantities and conditions](hyp:hk), these specify the stated inputs. -/
lemma measurable_canonicalInitLast {n k : ℕ} {Z : Fin n → Type*}
    [∀ i, MeasurableSpace (Z i)] (hk : k + 1 ≤ n) :
    Measurable (canonicalInitLast (Z := Z) hk) := by
  cases nextIndex_eq_canonicalNextIndex hk
  exact measurable_init_last hk

/-- [the measurable canonical snoc assertion](goal) holds. For [the displayed quantities and conditions](hyp:hk), these specify the stated inputs. -/
lemma measurable_canonicalSnoc {n k : ℕ} {Z : Fin n → Type*}
    [∀ i, MeasurableSpace (Z i)] (hk : k + 1 ≤ n) :
    Measurable (canonicalSnoc (Z := Z) hk) := by
  cases nextIndex_eq_canonicalNextIndex hk
  exact measurable_snoc hk

/-- Under [the stated assumptions](hyp:hk), [canonically rejoining a history with its last observation recovers the original history](goal). -/
@[simp] lemma canonicalSnoc_initLast {n k : ℕ} {Z : Fin n → Type*}
    (hk : k + 1 ≤ n) (u : History Z (k + 1) hk) :
    canonicalSnoc hk (canonicalInitLast hk u) = u := by
  exact Fin.snoc_init_self u

/-- Under [the stated assumptions](hyp:hk), [splitting a canonically extended history recovers its original history and last observation](goal). -/
@[simp] lemma canonicalInitLast_snoc {n k : ℕ} {Z : Fin n → Type*}
    (hk : k + 1 ≤ n)
    (u : History Z k (Nat.le_of_succ_le hk) × Z (canonicalNextIndex hk)) :
    canonicalInitLast hk (canonicalSnoc hk u) = u := by
  cases u with
  | mk h z =>
      apply Prod.ext
      · funext i
        exact congrFun (Fin.init_snoc
          (α := fun j : Fin (k + 1) => Z (Fin.castLE hk j))
          (p := h) (x := z)) i
      · exact Fin.snoc_last
          (α := fun j : Fin (k + 1) => Z (Fin.castLE hk j))
          (p := h) (x := z)

/-- [the integrable transcript prefix mixture real derivative assertion](goal) holds. For [the displayed quantities and conditions](hyp:P,v,p,n,k,hk), these specify the stated inputs. -/
lemma integrable_transcriptPrefixMixtureRealDerivative
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (n k : ℕ) (hk : k ≤ n) :
    Integrable (transcriptPrefixMixtureRealDerivative P θ v p n k hk)
      (transcriptPrefixReferenceMeasure P n k hk) := by
  let ν := transcriptPrefixReferenceMeasure P n k hk
  let μ (x : Fin n → Fin 4) :=
    (P.transcript n x).map (transcriptPrefix hk)
  letI (x : Fin n → Fin 4) : IsProbabilityMeasure (P.transcript n x) :=
    (P.factorizes n x).1
  letI (x : Fin n → Fin 4) : IsProbabilityMeasure (μ x) :=
    Measure.isProbabilityMeasure_map (measurable_transcriptPrefix hk).aemeasurable
  letI : IsFiniteMeasure ν := by
    dsimp [ν, transcriptPrefixReferenceMeasure]
    infer_instance
  have hac (x : Fin n → Fin 4) : μ x ≪ ν := by
    dsimp [μ, ν, transcriptPrefixReferenceMeasure]
    exact (transcriptComponent_ac_reference P n x).map
      (measurable_transcriptPrefix hk)
  have hcomponent (x : Fin n → Fin 4) : Integrable
      (transcriptPrefixComponentRealDensity P n k hk x) ν := by
    have h := (integrable_toReal_rnDeriv_mul_iff (hac x)
      (f := fun _ => (1 : ℝ))).2 (integrable_const (1 : ℝ))
    change Integrable (fun y => ((μ x).rnDeriv ν y).toReal) ν
    simpa only [mul_one] using h
  unfold transcriptPrefixMixtureRealDerivative
  exact integrable_finsetSum _ fun x _ => (hcomponent x).const_mul _

/-- the conditional transcript prefix directional score integrable general assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hk), [the conditional Transcript Prefix Directional Score integrable general](goal).

Under the stated assumptions, the conditional Transcript Prefix Directional Score integrable general. -/
lemma conditionalTranscriptPrefixDirectionalScore_integrable_general
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (n k : ℕ) (hk : k ≤ n) :
    Integrable (conditionalTranscriptPrefixDirectionalScore P θ v p n k hk)
      (transcriptPrefixLaw P θ p n k hk) := by
  let ν := transcriptPrefixReferenceMeasure P n k hk
  let μ := transcriptPrefixLaw P θ p n k hk
  letI : IsFiniteMeasure ν := by
    dsimp [ν, transcriptPrefixReferenceMeasure]
    infer_instance
  letI : IsFiniteMeasure μ := by
    dsimp [μ, transcriptPrefixLaw]
    infer_instance
  rw [← transcriptPrefixLaw_eq_withDensity_reference P θ p n k hk]
  rw [integrable_withDensity_iff_integrable_smul'
    (Measure.measurable_rnDeriv μ ν) (Measure.rnDeriv_lt_top μ ν)]
  refine (integrable_transcriptPrefixMixtureRealDerivative P θ v p n k hk).congr ?_
  filter_upwards [transcriptPrefixDensity_toReal_ae_eq_mixture_of_interior
    P θ p n k hk hp hθ] with h hdensity
  rw [smul_eq_mul, hdensity]
  rw [← conditionalTranscriptPrefixDirectionalScore_mul_density
    P θ v p hp hθ n k hk h]

/-- the set integral conditional transcript prefix directional score assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hk,hA), [the set Integral conditional Transcript Prefix Directional Score](goal).

Under the stated assumptions, the set Integral conditional Transcript Prefix Directional Score. -/
lemma setIntegral_conditionalTranscriptPrefixDirectionalScore
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (n k : ℕ) (hk : k ≤ n) (A : Set (History (Z n) k hk))
    (hA : MeasurableSet A) :
    ∫ h in A, conditionalTranscriptPrefixDirectionalScore P θ v p n k hk h
        ∂transcriptPrefixLaw P θ p n k hk =
      ∫ h in A, transcriptPrefixMixtureRealDerivative P θ v p n k hk h
        ∂transcriptPrefixReferenceMeasure P n k hk := by
  let ν := transcriptPrefixReferenceMeasure P n k hk
  let μ := transcriptPrefixLaw P θ p n k hk
  letI : IsFiniteMeasure ν := by
    dsimp [ν, transcriptPrefixReferenceMeasure]
    infer_instance
  letI : IsFiniteMeasure μ := by
    dsimp [μ, transcriptPrefixLaw]
    infer_instance
  rw [← transcriptPrefixLaw_eq_withDensity_reference P θ p n k hk]
  simp_rw [← integral_indicator hA]
  rw [integral_withDensity_eq_integral_toReal_smul
    (Measure.measurable_rnDeriv μ ν) (Measure.rnDeriv_lt_top μ ν)]
  apply integral_congr_ae
  filter_upwards [transcriptPrefixDensity_toReal_ae_eq_mixture_of_interior
    P θ p n k hk hp hθ] with h hdensity
  by_cases hh : h ∈ A
  · simp only [hh, indicator_of_mem, smul_eq_mul]
    rw [show (μ.rnDeriv ν h).toReal =
        transcriptPrefixMixtureRealDensity P θ p n k hk h by
      simpa [μ, ν] using hdensity]
    simpa only [mul_comm] using
      (conditionalTranscriptPrefixDirectionalScore_mul_density
        P θ v p hp hθ n k hk h)
  · simp [hh]

/-- the transcript successor law map canonical init last assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hk), [the transcript Successor Law map canonical Init Last](goal).

Under the stated assumptions, the transcript Successor Law map canonical Init Last. -/
lemma transcriptSuccessorLaw_map_canonicalInitLast
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (n k : ℕ) (hk : k + 1 ≤ n) :
    (transcriptPrefixLaw P θ p n (k + 1) hk).map
        (canonicalInitLast (Z := Z n) hk) =
      outputLaw θ p (sequentialJointChannel P n (canonicalNextIndex hk)
        (transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk))) := by
  cases nextIndex_eq_canonicalNextIndex hk
  exact transcriptSuccessorLaw_eq_jointChannel P θ p hp hθ n k hk

/-- The actual successor-prefix score, written in canonical split coordinates. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. [The actual Successor Score In Coordinates](goal) is determined by [the displayed parameters](hyp:P,θ,v,p,n,k,hk,z). -/
def actualSuccessorScoreInCoordinates {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (n k : ℕ) (hk : k + 1 ≤ n)
    (z : History (Z n) k (Nat.le_of_succ_le hk) ×
      Z n (canonicalNextIndex hk)) : ℝ :=
  conditionalTranscriptPrefixDirectionalScore P θ v p n (k + 1) hk
    (canonicalSnoc hk z)

/-- [the measurable actual successor score in coordinates assertion](goal) holds. For [the displayed quantities and conditions](hyp:P,v,p,n,k,hk), these specify the stated inputs. -/
lemma measurable_actualSuccessorScoreInCoordinates
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (n k : ℕ) (hk : k + 1 ≤ n) :
    Measurable (actualSuccessorScoreInCoordinates P θ v p n k hk) := by
  unfold actualSuccessorScoreInCoordinates
    conditionalTranscriptPrefixDirectionalScore
  exact ((measurable_transcriptPrefixMixtureRealDerivative
    P θ v p n (k + 1) hk).div
      (measurable_transcriptPrefixMixtureRealDensity
        P θ p n (k + 1) hk)).comp (measurable_canonicalSnoc hk)

/-- the actual successor score in coordinates integrable assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hk), [the actual Successor Score In Coordinates integrable](goal).

Under the stated assumptions, the actual Successor Score In Coordinates integrable. -/
lemma actualSuccessorScoreInCoordinates_integrable
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (n k : ℕ) (hk : k + 1 ≤ n) :
    Integrable (actualSuccessorScoreInCoordinates P θ v p n k hk)
      (outputLaw θ p (sequentialJointChannel P n (canonicalNextIndex hk)
        (transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk)))) := by
  rw [← transcriptSuccessorLaw_map_canonicalInitLast
    P θ p hp hθ n k hk]
  rw [integrable_map_measure
    (measurable_actualSuccessorScoreInCoordinates P θ v p n k hk).aestronglyMeasurable
    (measurable_canonicalInitLast hk).aemeasurable]
  simpa [Function.comp_def, actualSuccessorScoreInCoordinates] using
    (conditionalTranscriptPrefixDirectionalScore_integrable_general
      P θ v p hp hθ n (k + 1) hk)

/-- the has deriv at transcript prefix event mass assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hk,hA), [the has Deriv At transcript Prefix Event Mass](goal).

Under the stated assumptions, the has Deriv At transcript Prefix Event Mass. -/
lemma hasDerivAt_transcriptPrefixEventMass
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (n k : ℕ) (hk : k ≤ n) (A : Set (History (Z n) k hk))
    (hA : MeasurableSet A) :
    HasDerivAt (fun u =>
      (transcriptPrefixLaw P (parameterPath θ v u) p n k hk A).toReal)
      (∫ h in A, transcriptPrefixMixtureRealDerivative P θ v p n k hk h
        ∂transcriptPrefixReferenceMeasure P n k hk) 0 := by
  let g : History (Z n) k hk → ℝ := A.indicator (fun _ => 1)
  have hg : Measurable g := measurable_const.indicator hA
  have hgInt (x : Fin n → Fin 4) : Integrable g
      ((P.transcript n x).map (transcriptPrefix hk)) := by
    letI : IsProbabilityMeasure (P.transcript n x) := (P.factorizes n x).1
    letI : IsProbabilityMeasure
        ((P.transcript n x).map (transcriptPrefix hk)) :=
      Measure.isProbabilityMeasure_map (measurable_transcriptPrefix hk).aemeasurable
    exact (integrable_const (1 : ℝ)).indicator hA
  have h := hasDerivAt_integral_transcriptPrefixLaw
    P θ v p hp hθ n k hk g hg hgInt
  have hcoef : (∫ h, transcriptPrefixMixtureRealDerivative P θ v p n k hk h * g h
      ∂transcriptPrefixReferenceMeasure P n k hk) =
      ∫ h in A, transcriptPrefixMixtureRealDerivative P θ v p n k hk h
        ∂transcriptPrefixReferenceMeasure P n k hk := by
    rw [← integral_indicator hA]
    apply integral_congr_ae
    filter_upwards with y
    by_cases hy : y ∈ A <;> simp [g, hy]
  rw [hcoef] at h
  simpa [g, integral_indicator hA, measureReal_def] using h

/-- The actual adjacent prefix score is the inherited prefix score plus the current channel score, almost everywhere under the actual successor law. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hk), [the actual Successor Score In Coordinates ae eq candidate](goal).

Under the stated assumptions, the actual Successor Score In Coordinates ae eq candidate. -/
lemma actualSuccessorScoreInCoordinates_ae_eq_candidate
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (n k : ℕ) (hk : k + 1 ≤ n) :
    actualSuccessorScoreInCoordinates P θ v p n k hk =ᵐ[
      outputLaw θ p (sequentialJointChannel P n (canonicalNextIndex hk)
        (transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk)))]
      successorDirectionalScoreCandidate P θ v p n k hk := by
  cases nextIndex_eq_canonicalNextIndex hk
  let μ := transcriptPrefixLaw P θ p n (k + 1) hk
  let split := canonicalInitLast (Z := Z n) hk
  let ν := outputLaw θ p (sequentialJointChannel P n (canonicalNextIndex hk)
    (transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk)))
  have hmap : μ.map split = ν :=
    transcriptSuccessorLaw_map_canonicalInitLast P θ p hp hθ n k hk
  have hf := actualSuccessorScoreInCoordinates_integrable
    P θ v p hp hθ n k hk
  have hg := successorDirectionalScoreCandidate_integrable
    P θ v p hp hθ n k hk
  refine Integrable.ae_eq_of_forall_setIntegral_eq _ _ hf hg ?_
  intro A hA _
  have hprefix := hasDerivAt_transcriptPrefixEventMass P θ v p hp hθ
    n (k + 1) hk (split ⁻¹' A) (hA.preimage (measurable_canonicalInitLast hk))
  have hsuccessor := hasDerivAt_successorPrefixEventMass
    P θ v p hp hθ n k hk A hA
  have hevent : (fun u =>
      (transcriptPrefixLaw P (parameterPath θ v u) p n (k + 1) hk
        (split ⁻¹' A)).toReal) =
      fun u => successorPrefixEventMass P θ v p n k hk u A := by
    funext u
    unfold successorPrefixEventMass
    change ((transcriptPrefixLaw P (parameterPath θ v u) p n (k + 1) hk)
      (split ⁻¹' A)).toReal =
      ((Measure.map split
        (transcriptPrefixLaw P (parameterPath θ v u) p n (k + 1) hk)) A).toReal
    rw [Measure.map_apply (measurable_canonicalInitLast hk) hA]
  rw [hevent] at hprefix
  have hcoeff := hprefix.unique hsuccessor
  change (∫ x in A, actualSuccessorScoreInCoordinates P θ v p n k hk x ∂ν) =
    ∫ x in A, successorDirectionalScoreCandidate P θ v p n k hk x ∂ν
  rw [← hmap]
  simp_rw [← integral_indicator hA]
  have hactualMeas : AEStronglyMeasurable
      (A.indicator (actualSuccessorScoreInCoordinates P θ v p n k hk))
      (Measure.map split μ) := by
    have hm : Measurable
        (A.indicator (actualSuccessorScoreInCoordinates P θ v p n k hk)) :=
      (measurable_actualSuccessorScoreInCoordinates P θ v p n k hk).indicator hA
    exact hm.aestronglyMeasurable
  rw [integral_map (measurable_canonicalInitLast hk).aemeasurable
    hactualMeas]
  have hactual : (fun u => A.indicator
      (actualSuccessorScoreInCoordinates P θ v p n k hk) (split u)) =
      (split ⁻¹' A).indicator
        (conditionalTranscriptPrefixDirectionalScore P θ v p n (k + 1) hk) := by
    funext u
    by_cases hu : split u ∈ A <;>
      simp [hu, split, actualSuccessorScoreInCoordinates]
  rw [hactual, integral_indicator
    (hA.preimage (measurable_canonicalInitLast hk))]
  rw [setIntegral_conditionalTranscriptPrefixDirectionalScore
    P θ v p hp hθ n (k + 1) hk (split ⁻¹' A)
      (hA.preimage (measurable_canonicalInitLast hk))]
  rw [hmap, integral_indicator hA]
  rw [← successorEventDerivative_eq_setIntegral_successorDirectionalScoreCandidate
    P θ v p hp hθ n k hk A hA]
  exact hcoeff

/-- Consequently, the adjacent score increment is exactly the current joint-channel directional score almost everywhere. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hk), [the actual Successor Score Increment ae eq channel Directional Score](goal).

Under the stated assumptions, the actual Successor Score Increment ae eq channel Directional Score. -/
lemma actualSuccessorScoreIncrement_ae_eq_channelDirectionalScore
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (n k : ℕ) (hk : k + 1 ≤ n) :
    (fun z => actualSuccessorScoreInCoordinates P θ v p n k hk z -
      liftedPrefixDirectionalScore P θ v p n k hk z) =ᵐ[
        outputLaw θ p (sequentialJointChannel P n (canonicalNextIndex hk)
          (transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk)))]
      channelDirectionalScore θ p
        (sequentialJointChannel P n (canonicalNextIndex hk)
          (transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk))) v := by
  filter_upwards [actualSuccessorScoreInCoordinates_ae_eq_candidate
    P θ v p hp hθ n k hk] with z hz
  rw [hz]
  simp [successorDirectionalScoreCandidate]

end CausalSmith.Stat.LdpAteEfficiencySurface
