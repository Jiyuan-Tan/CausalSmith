module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.SequentialSuccessorDerivative
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.SequentialScoreProjectionInputs

/-! # The predecessor score in a successor event derivative

This file rewrites the explicit prefix-mixture derivative from
`SequentialSuccessorDerivative` as an integral of the prefix directional score
against the actual prefix law.  It uses only finite-mixture domination and does
not invoke score projection.
-/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open Causalean.Mathlib.Probability.Kernel.FiniteSequence

/-- The explicit prefix derivative remains integrable after multiplication by
a measurable successor-row event section. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:P,v,p,n,k,hk,a,A,hA), these specify the stated inputs. -/
lemma integrable_transcriptPrefixMixtureRealDerivative_mul_successorRowKernelSection
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (n k : ℕ) (hk : k + 1 ≤ n) (a : Fin 4)
    (A : Set (History (Z n) k (Nat.le_of_succ_le hk) ×
      Z n (nextIndex hk))) (hA : MeasurableSet A) :
    Integrable (fun h =>
      transcriptPrefixMixtureRealDerivative P θ v p n k
          (Nat.le_of_succ_le hk) h *
        successorRowKernelSection P n k hk a A h)
      (transcriptPrefixReferenceMeasure P n k (Nat.le_of_succ_le hk)) := by
  let ν := transcriptPrefixReferenceMeasure P n k (Nat.le_of_succ_le hk)
  let μ (x : Fin n → Fin 4) :=
    (P.transcript n x).map (transcriptPrefix (Nat.le_of_succ_le hk))
  letI (x : Fin n → Fin 4) : IsProbabilityMeasure (P.transcript n x) :=
    (P.factorizes n x).1
  letI (x : Fin n → Fin 4) : IsProbabilityMeasure (μ x) := by
    dsimp [μ]
    exact Measure.isProbabilityMeasure_map
      (measurable_transcriptPrefix (Nat.le_of_succ_le hk)).aemeasurable
  letI : IsFiniteMeasure ν := by
    dsimp [ν, transcriptPrefixReferenceMeasure]
    infer_instance
  have hac (x : Fin n → Fin 4) : μ x ≪ ν := by
    dsimp [μ, ν, transcriptPrefixReferenceMeasure]
    exact (transcriptComponent_ac_reference P n x).map
      (measurable_transcriptPrefix (Nat.le_of_succ_le hk))
  have hcomponent (x : Fin n → Fin 4) : Integrable (fun h =>
      transcriptPrefixComponentRealDensity P n k (Nat.le_of_succ_le hk) x h *
        successorRowKernelSection P n k hk a A h) ν := by
    have h := (integrable_toReal_rnDeriv_mul_iff (hac x)).2
      (integrable_successorRowKernelSection_component P n k hk a A hA x)
    simpa [transcriptPrefixComponentRealDensity, μ, ν] using h
  unfold transcriptPrefixMixtureRealDerivative
  simp_rw [Finset.sum_mul]
  exact integrable_finsetSum _ fun x _ => by
    simpa only [mul_assoc] using (hcomponent x).const_mul
      (inputPathDirectionalDerivative θ v p x)

/-- A prefix law is its common reference measure weighted by its
Radon--Nikodym derivative. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:P,p,n,k,hk), these specify the stated inputs. -/
lemma transcriptPrefixLaw_eq_withDensity_reference
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ : TrialParameter) (p : ℝ)
    (n k : ℕ) (hk : k ≤ n) :
    (transcriptPrefixReferenceMeasure P n k hk).withDensity
        ((transcriptPrefixLaw P θ p n k hk).rnDeriv
          (transcriptPrefixReferenceMeasure P n k hk)) =
      transcriptPrefixLaw P θ p n k hk := by
  letI : IsFiniteMeasure (transcriptPrefixReferenceMeasure P n k hk) := by
    unfold transcriptPrefixReferenceMeasure
    infer_instance
  letI : IsFiniteMeasure (transcriptPrefixLaw P θ p n k hk) := by
    unfold transcriptPrefixLaw
    infer_instance
  exact Measure.withDensity_rnDeriv_eq (transcriptPrefixLaw P θ p n k hk)
    (transcriptPrefixReferenceMeasure P n k hk)
    (transcriptPrefixLaw_ac_reference P θ p n k hk)

/-- Multiplying the guarded prefix score by the prefix density recovers the explicit real derivative density everywhere. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hk), [the conditional Transcript Prefix Directional Score mul density](goal).

Under the stated assumptions, the conditional Transcript Prefix Directional Score mul density. -/
lemma conditionalTranscriptPrefixDirectionalScore_mul_density
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (n k : ℕ) (hk : k ≤ n) (h : History (Z n) k hk) :
    transcriptPrefixMixtureRealDensity P θ p n k hk h *
        conditionalTranscriptPrefixDirectionalScore P θ v p n k hk h =
      transcriptPrefixMixtureRealDerivative P θ v p n k hk h := by
  rw [conditionalTranscriptPrefixDirectionalScore_eq_guarded
    P θ v p n k hk hp hθ h]
  split_ifs with hpos
  · field_simp
  · have hnonneg := transcriptPrefixMixtureRealDensity_nonneg
      P θ p n k hk hp hθ h
    have hz : transcriptPrefixMixtureRealDensity P θ p n k hk h = 0 :=
      le_antisymm (le_of_not_gt hpos) hnonneg
    rw [hz, zero_mul,
      transcriptPrefixMixtureRealDerivative_eq_zero_of_density_eq_zero
        P θ v p n k hk hp hθ h hz]

/-- The predecessor-row derivative is the integral of the actual prefix score times the bounded row-event section under the actual prefix law. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hk,hA), [the predecessor Row Event Derivative eq integral past Score](goal).

Under the stated assumptions, the predecessor Row Event Derivative eq integral past Score. -/
lemma predecessorRowEventDerivative_eq_integral_pastScore
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (n k : ℕ) (hk : k + 1 ≤ n) (a : Fin 4)
    (A : Set (History (Z n) k (Nat.le_of_succ_le hk) ×
      Z n (nextIndex hk))) (hA : MeasurableSet A) :
    predecessorRowEventDerivative P θ v p n k hk a A =
      ∫ h, conditionalTranscriptPrefixDirectionalScore P θ v p n k
          (Nat.le_of_succ_le hk) h *
        successorRowKernelSection P n k hk a A h
        ∂transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk) := by
  let ν := transcriptPrefixReferenceMeasure P n k (Nat.le_of_succ_le hk)
  let μ := transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk)
  letI : IsFiniteMeasure ν := by
    dsimp [ν, transcriptPrefixReferenceMeasure]
    infer_instance
  letI : IsFiniteMeasure μ := by
    dsimp [μ, transcriptPrefixLaw]
    infer_instance
  rw [← transcriptPrefixLaw_eq_withDensity_reference P θ p n k
    (Nat.le_of_succ_le hk)]
  rw [integral_withDensity_eq_integral_toReal_smul
    (Measure.measurable_rnDeriv μ ν) (Measure.rnDeriv_lt_top μ ν)]
  unfold predecessorRowEventDerivative
  apply integral_congr_ae
  filter_upwards
    [transcriptPrefixDensity_toReal_ae_eq_mixture_of_interior
      P θ p n k (Nat.le_of_succ_le hk) hp hθ]
    with h hdensity
  rw [smul_eq_mul, hdensity]
  rw [← conditionalTranscriptPrefixDirectionalScore_mul_density
    P θ v p hp hθ n k (Nat.le_of_succ_le hk) h]
  ring

/-- The past-score integrand used above is integrable under the actual prefix law. This is the integrability input needed by a subsequent projection or conditional-expectation uniqueness argument. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hk,hA), [the integrable conditional Transcript Prefix Directional Score mul successor Row Kernel Section](goal).

Under the stated assumptions, the integrable conditional Transcript Prefix Directional Score mul successor Row Kernel Section. -/
lemma integrable_conditionalTranscriptPrefixDirectionalScore_mul_successorRowKernelSection
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (n k : ℕ) (hk : k + 1 ≤ n) (a : Fin 4)
    (A : Set (History (Z n) k (Nat.le_of_succ_le hk) ×
      Z n (nextIndex hk))) (hA : MeasurableSet A) :
    Integrable (fun h =>
      conditionalTranscriptPrefixDirectionalScore P θ v p n k
          (Nat.le_of_succ_le hk) h *
        successorRowKernelSection P n k hk a A h)
      (transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk)) := by
  let ν := transcriptPrefixReferenceMeasure P n k (Nat.le_of_succ_le hk)
  let μ := transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk)
  letI : IsFiniteMeasure ν := by
    dsimp [ν, transcriptPrefixReferenceMeasure]
    infer_instance
  letI : IsFiniteMeasure μ := by
    dsimp [μ, transcriptPrefixLaw]
    infer_instance
  rw [← transcriptPrefixLaw_eq_withDensity_reference P θ p n k
    (Nat.le_of_succ_le hk)]
  rw [integrable_withDensity_iff_integrable_smul'
    (Measure.measurable_rnDeriv μ ν) (Measure.rnDeriv_lt_top μ ν)]
  have hderiv :=
    integrable_transcriptPrefixMixtureRealDerivative_mul_successorRowKernelSection
      P θ v p n k hk a A hA
  refine hderiv.congr ?_
  filter_upwards
    [transcriptPrefixDensity_toReal_ae_eq_mixture_of_interior
      P θ p n k (Nat.le_of_succ_le hk) hp hθ]
    with h hdensity
  rw [smul_eq_mul, hdensity,
    ← conditionalTranscriptPrefixDirectionalScore_mul_density
      P θ v p hp hθ n k (Nat.le_of_succ_le hk) h]
  ring

/-- Summing the row identities with the base four-cell probabilities gives the complete predecessor contribution in the successor product rule. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hk,hA), [the predecessor Successor Event Derivative eq sum integral past Score](goal).

Under the stated assumptions, the predecessor Successor Event Derivative eq sum integral past Score. -/
lemma predecessorSuccessorEventDerivative_eq_sum_integral_pastScore
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (n k : ℕ) (hk : k + 1 ≤ n)
    (A : Set (History (Z n) k (Nat.le_of_succ_le hk) ×
      Z n (nextIndex hk))) (hA : MeasurableSet A) :
    predecessorSuccessorEventDerivative θ p
        (fun a => predecessorRowEventDerivative P θ v p n k hk a A) =
      ∑ a : Fin 4, piTheta θ p a *
        ∫ h, conditionalTranscriptPrefixDirectionalScore P θ v p n k
            (Nat.le_of_succ_le hk) h *
          successorRowKernelSection P n k hk a A h
          ∂transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk) := by
  unfold predecessorSuccessorEventDerivative
  apply Finset.sum_congr rfl
  intro a _
  change piTheta θ p a * predecessorRowEventDerivative P θ v p n k hk a A = _
  rw [predecessorRowEventDerivative_eq_integral_pastScore
    P θ v p hp hθ n k hk a A hA]

/-- Paper-side successor characterization before score projection: the mapped successor law is the joint-channel output law, and every predecessor row derivative is represented by the integrable prefix-score kernel integral. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ,hk,hA), [the transcript Successor Law past Score characterization](goal).

Under the stated assumptions, the transcript Successor Law past Score characterization. -/
-- keep: reusable sequential-law, Fisher-information, or van-Trees bridge for related adaptive experiments
lemma transcriptSuccessorLaw_pastScore_characterization
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (n k : ℕ) (hk : k + 1 ≤ n)
    (A : Set (History (Z n) k (Nat.le_of_succ_le hk) ×
      Z n (nextIndex hk))) (hA : MeasurableSet A) :
    let μ := transcriptPrefixLaw P θ p n k (Nat.le_of_succ_le hk)
    (transcriptPrefixLaw P θ p n (k + 1) hk).map
        (fun u => (init hk u, last hk u)) =
        outputLaw θ p (sequentialJointChannel P n (nextIndex hk) μ) ∧
      ∀ a : Fin 4,
        Integrable (fun h =>
          conditionalTranscriptPrefixDirectionalScore P θ v p n k
              (Nat.le_of_succ_le hk) h *
            successorRowKernelSection P n k hk a A h) μ ∧
        predecessorRowEventDerivative P θ v p n k hk a A =
          ∫ h, conditionalTranscriptPrefixDirectionalScore P θ v p n k
              (Nat.le_of_succ_le hk) h *
            successorRowKernelSection P n k hk a A h ∂μ := by
  dsimp only
  refine ⟨transcriptSuccessorLaw_eq_jointChannel P θ p hp hθ n k hk, ?_⟩
  intro a
  exact ⟨
    integrable_conditionalTranscriptPrefixDirectionalScore_mul_successorRowKernelSection
      P θ v p hp hθ n k hk a A hA,
    predecessorRowEventDerivative_eq_integral_pastScore
      P θ v p hp hθ n k hk a A hA⟩

end CausalSmith.Stat.LdpAteEfficiencySurface
