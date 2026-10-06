module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.SequentialScore
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.PilotPrefix

/-! # Global finite-mixture transcript scores -/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

/-- A finite bound for the complete-data path scores. For the displayed inputs and conditions, the stated result follows. [The input Path Score Bound](goal) is determined by [the displayed parameters](hyp:θ,v,p). -/
def inputPathScoreBound {n : ℕ} (θ v : TrialParameter) (p : ℝ) : ℝ :=
  ∑ x : Fin n → Fin 4, |inputPathDirectionalScore θ v p x|

/-- Under [the supplied quantities and conditions](hyp:v,p), [the input path score bound nonneg assertion](goal) holds. -/
lemma inputPathScoreBound_nonneg {n : ℕ} (θ v : TrialParameter) (p : ℝ) :
    0 ≤ inputPathScoreBound (n := n) θ v p := by
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- [the abs input path directional score le bound assertion](goal) holds. For [the displayed quantities and conditions](hyp:v,p,x), these specify the stated inputs. -/
lemma abs_inputPathDirectionalScore_le_bound {n : ℕ}
    (θ v : TrialParameter) (p : ℝ) (x : Fin n → Fin 4) :
    |inputPathDirectionalScore θ v p x| ≤ inputPathScoreBound (n := n) θ v p := by
  unfold inputPathScoreBound
  exact Finset.single_le_sum
    (fun y _ => abs_nonneg (inputPathDirectionalScore θ v p y))
    (Finset.mem_univ x)

/-- [the measurable transcript component real density assertion](goal) holds. For [the displayed quantities and conditions](hyp:P,n,x), these specify the stated inputs. -/
lemma measurable_transcriptComponentRealDensity {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (n : ℕ) (x : Fin n → Fin 4) :
    Measurable (transcriptComponentRealDensity P n x) := by
  exact (Measure.measurable_rnDeriv _ _).ennreal_toReal

/-- [the measurable transcript mixture real density assertion](goal) holds. For [the displayed quantities and conditions](hyp:P,p,n), these specify the stated inputs. -/
lemma measurable_transcriptMixtureRealDensity {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ : TrialParameter) (p : ℝ) (n : ℕ) :
    Measurable (transcriptMixtureRealDensity P θ p n) := by
  unfold transcriptMixtureRealDensity
  exact Finset.measurable_fun_sum _ fun x _ =>
    measurable_const.mul (measurable_transcriptComponentRealDensity P n x)

/-- [the measurable transcript mixture real derivative assertion](goal) holds. For [the displayed quantities and conditions](hyp:P,v,p,n), these specify the stated inputs. -/
lemma measurable_transcriptMixtureRealDerivative {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ) (n : ℕ) :
    Measurable (transcriptMixtureRealDerivative P θ v p n) := by
  unfold transcriptMixtureRealDerivative
  exact Finset.measurable_fun_sum _ fun x _ =>
    measurable_const.mul (measurable_transcriptComponentRealDensity P n x)

/-- [the measurable conditional transcript directional score assertion](goal) holds. For [the displayed quantities and conditions](hyp:P,v,p,n), these specify the stated inputs. -/
lemma measurable_conditionalTranscriptDirectionalScore {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ) (n : ℕ) :
    Measurable (conditionalTranscriptDirectionalScore P θ v p n) := by
  exact (measurable_transcriptMixtureRealDerivative P θ v p n).div
    (measurable_transcriptMixtureRealDensity P θ p n)

/-- the transcript mixture real density nonneg assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ), [the transcript Mixture Real Density nonneg](goal).

Under the stated assumptions, the transcript Mixture Real Density nonneg. -/
lemma transcriptMixtureRealDensity_nonneg {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ : TrialParameter) (p : ℝ) (n : ℕ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (z : Transcript (Z n)) :
    0 ≤ transcriptMixtureRealDensity P θ p n z := by
  unfold transcriptMixtureRealDensity
  exact Finset.sum_nonneg fun x _ => mul_nonneg
    (inputPathProbability_pos_of_interior θ p hp hθ x).le ENNReal.toReal_nonneg

/-- The observed transcript score is a finite weighted average of the complete-data path scores and is therefore uniformly bounded. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ), [the abs conditional Transcript Directional Score le](goal).

Under the stated assumptions, the abs conditional Transcript Directional Score le. -/
lemma abs_conditionalTranscriptDirectionalScore_le {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ) (n : ℕ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ)
    (z : Transcript (Z n)) :
    |conditionalTranscriptDirectionalScore P θ v p n z| ≤
      inputPathScoreBound (n := n) θ v p := by
  let B := inputPathScoreBound (n := n) θ v p
  let d := transcriptMixtureRealDensity P θ p n z
  have hB : 0 ≤ B := inputPathScoreBound_nonneg θ v p
  have hd : 0 ≤ d := transcriptMixtureRealDensity_nonneg P θ p n hp hθ z
  have hx (x : Fin n → Fin 4) : inputPathProbability θ p x ≠ 0 :=
    ne_of_gt (inputPathProbability_pos_of_interior θ p hp hθ x)
  have hn : |transcriptMixtureRealDerivative P θ v p n z| ≤ B * d := by
    rw [transcriptDerivative_eq_completeDataScoreMixture P θ v p n z hx]
    calc
      |∑ x : Fin n → Fin 4,
          inputPathProbability θ p x * inputPathDirectionalScore θ v p x *
            transcriptComponentRealDensity P n x z| ≤
          ∑ x : Fin n → Fin 4,
            |inputPathProbability θ p x * inputPathDirectionalScore θ v p x *
            transcriptComponentRealDensity P n x z| :=
              Finset.abs_sum_le_sum_abs _ _
      _ = ∑ x : Fin n → Fin 4,
            (inputPathProbability θ p x *
              transcriptComponentRealDensity P n x z) *
                |inputPathDirectionalScore θ v p x| := by
          apply Finset.sum_congr rfl
          intro x _
          rw [abs_mul, abs_mul, abs_of_pos
            (inputPathProbability_pos_of_interior θ p hp hθ x),
            abs_of_nonneg (show 0 ≤ transcriptComponentRealDensity P n x z by
              exact ENNReal.toReal_nonneg)]
          ring
      _ ≤ ∑ x : Fin n → Fin 4,
            (inputPathProbability θ p x *
              transcriptComponentRealDensity P n x z) * B := by
          apply Finset.sum_le_sum
          intro x _
          exact mul_le_mul_of_nonneg_left
            (abs_inputPathDirectionalScore_le_bound θ v p x)
            (mul_nonneg (inputPathProbability_pos_of_interior θ p hp hθ x).le
              ENNReal.toReal_nonneg)
      _ = B * d := by
          simp only [d, transcriptMixtureRealDensity]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          ring
  by_cases hdz : d = 0
  · have hn0 : transcriptMixtureRealDerivative P θ v p n z = 0 := by
      rw [hdz, mul_zero] at hn
      exact abs_eq_zero.mp (le_antisymm hn (abs_nonneg _))
    rw [conditionalTranscriptDirectionalScore, hn0, show
      transcriptMixtureRealDensity P θ p n z = 0 by exact hdz]
    simp only [zero_div, abs_zero]
    exact hB
  · have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hdz)
    rw [conditionalTranscriptDirectionalScore, abs_div,
      abs_of_nonneg (show 0 ≤ transcriptMixtureRealDensity P θ p n z by exact hd)]
    exact (div_le_iff₀ hdpos).2 (by simpa [d] using hn)

/-- the conditional transcript directional score mem lp two assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ), [the conditional Transcript Directional Score mem Lp two](goal).

Under the stated assumptions, the conditional Transcript Directional Score mem Lp two. -/
lemma conditionalTranscriptDirectionalScore_memLp_two {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ) (n : ℕ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) :
    MemLp (conditionalTranscriptDirectionalScore P θ v p n) 2
      (transcriptLaw P θ p n) := by
  apply MemLp.of_bound
    (measurable_conditionalTranscriptDirectionalScore P θ v p n).aestronglyMeasurable
    (inputPathScoreBound (n := n) θ v p)
  filter_upwards [] with z
  simpa [Real.norm_eq_abs] using
    abs_conditionalTranscriptDirectionalScore_le P θ v p n hp hθ z

/-- the transcript reference ac transcript law of interior assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ), [the transcript Reference ac transcript Law of interior](goal).

Under the stated assumptions, the transcript Reference ac transcript Law of interior. -/
lemma transcriptReference_ac_transcriptLaw_of_interior {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ : TrialParameter) (p : ℝ) (n : ℕ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) :
    transcriptReferenceMeasure P n ≪ transcriptLaw P θ p n := by
  classical
  apply Measure.AbsolutelyContinuous.mk
  intro A hA hlaw
  have hsum : ∑ x : Fin n → Fin 4,
      ENNReal.ofReal (inputPathProbability θ p x) * P.transcript n x A = 0 := by
    simpa [transcriptLaw, Measure.finsetSum_apply, Measure.smul_apply,
      smul_eq_mul] using hlaw
  have hcomponent (x : Fin n → Fin 4) : P.transcript n x A = 0 := by
    have hx := (Finset.sum_eq_zero_iff.mp hsum x (Finset.mem_univ x))
    exact (mul_eq_zero.mp hx).resolve_left
      (ne_of_gt (ENNReal.ofReal_pos.mpr
        (inputPathProbability_pos_of_interior θ p hp hθ x)))
  simp [transcriptReferenceMeasure, Measure.finsetSum_apply, hcomponent]

/-- the transcript mixture real density pos ae assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ), [the transcript Mixture Real Density pos ae](goal).

Under the stated assumptions, the transcript Mixture Real Density pos ae. -/
lemma transcriptMixtureRealDensity_pos_ae {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ : TrialParameter) (p : ℝ) (n : ℕ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) :
    ∀ᵐ z ∂transcriptReferenceMeasure P n,
      0 < transcriptMixtureRealDensity P θ p n z := by
  have hac := transcriptLaw_ac_reference P θ p n
  have hrev := transcriptReference_ac_transcriptLaw_of_interior P θ p n hp hθ
  have hposENN : ∀ᵐ z ∂transcriptReferenceMeasure P n,
      0 < transcriptDensity P θ p n z :=
    hrev.ae_le (Measure.rnDeriv_pos hac)
  have hneTop : ∀ᵐ z ∂transcriptReferenceMeasure P n,
      transcriptDensity P θ p n z ≠ ∞ :=
    Measure.rnDeriv_ne_top _ _
  have hpos : ∀ᵐ z ∂transcriptReferenceMeasure P n,
      0 < (transcriptDensity P θ p n z).toReal := by
    filter_upwards [hposENN, hneTop] with z hz htop
    exact ENNReal.toReal_pos hz.ne' htop
  filter_upwards [hpos,
    transcriptDensity_toReal_ae_eq_mixture_of_interior P θ p n hp hθ]
    with z hz heq
  simpa [heq] using hz

/-- [the sum input path directional derivative eq zero assertion](goal) holds. For [the displayed quantities and conditions](hyp:v,p), these specify the stated inputs. -/
lemma sum_inputPathDirectionalDerivative_eq_zero {n : ℕ}
    (θ v : TrialParameter) (p : ℝ) :
    ∑ x : Fin n → Fin 4, inputPathDirectionalDerivative θ v p x = 0 := by
  have hzero : parameterPath θ v 0 = θ := by
    funext k
    simp [parameterPath]
  have hder : HasDerivAt
      (fun a => ∑ x : Fin n → Fin 4,
        inputPathProbability (parameterPath θ v a) p x)
      (∑ x : Fin n → Fin 4, inputPathDirectionalDerivative θ v p x) 0 := by
    simpa only [hzero] using HasDerivAt.fun_sum
      (u := (Finset.univ : Finset (Fin n → Fin 4)))
      (fun x _ => hasDerivAt_inputPathProbability_parameterPath θ v p 0 x)
  have heq : (fun a => ∑ x : Fin n → Fin 4,
      inputPathProbability (parameterPath θ v a) p x) = fun _ : ℝ => 1 := by
    funext a
    exact inputPathProbability_sum_eq_one _ p n
  rw [heq] at hder
  exact hder.unique (hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ)))

/-- [the integral transcript mixture real derivative eq zero assertion](goal) holds. For [the displayed quantities and conditions](hyp:P,v,p,n), these specify the stated inputs. -/
lemma integral_transcriptMixtureRealDerivative_eq_zero {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ) (n : ℕ) :
    ∫ z, transcriptMixtureRealDerivative P θ v p n z
        ∂transcriptReferenceMeasure P n = 0 := by
  letI (x : Fin n → Fin 4) : IsProbabilityMeasure (P.transcript n x) :=
    (P.factorizes n x).1
  have hint (x : Fin n → Fin 4) : Integrable
      (transcriptComponentRealDensity P n x) (transcriptReferenceMeasure P n) := by
    have h := (integrable_toReal_rnDeriv_mul_iff
      (transcriptComponent_ac_reference P n x)
      (f := fun _ => (1 : ℝ))).2 (integrable_const (1 : ℝ))
    change Integrable (fun z =>
      ((P.transcript n x).rnDeriv (transcriptReferenceMeasure P n) z).toReal)
      (transcriptReferenceMeasure P n)
    simpa only [mul_one] using h
  simp_rw [transcriptMixtureRealDerivative]
  rw [integral_finset_sum _ (fun x _ => (hint x).const_mul _)]
  calc
    ∑ x : Fin n → Fin 4,
        ∫ z, inputPathDirectionalDerivative θ v p x *
          transcriptComponentRealDensity P n x z
          ∂transcriptReferenceMeasure P n =
      ∑ x : Fin n → Fin 4, inputPathDirectionalDerivative θ v p x := by
        apply Finset.sum_congr rfl
        intro x _
        rw [integral_const_mul]
        rw [show (∫ z, transcriptComponentRealDensity P n x z
              ∂transcriptReferenceMeasure P n) = 1 by
          unfold transcriptComponentRealDensity
          rw [Measure.integral_toReal_rnDeriv
            (transcriptComponent_ac_reference P n x)]
          simp [measureReal_def]]
        ring
    _ = 0 := sum_inputPathDirectionalDerivative_eq_zero θ v p

/-- the conditional transcript directional score integrable assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ), [the conditional Transcript Directional Score integrable](goal).

Under the stated assumptions, the conditional Transcript Directional Score integrable. -/
lemma conditionalTranscriptDirectionalScore_integrable {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ) (n : ℕ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) :
    Integrable (conditionalTranscriptDirectionalScore P θ v p n)
      (transcriptLaw P θ p n) :=
  (conditionalTranscriptDirectionalScore_memLp_two P θ v p n hp hθ).integrable
    (by norm_num)

/-- The global observed transcript score is centered under the transcript law. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ), [the integral conditional Transcript Directional Score eq zero](goal).

Under the stated assumptions, the integral conditional Transcript Directional Score eq zero. -/
lemma integral_conditionalTranscriptDirectionalScore_eq_zero {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ) (n : ℕ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) :
    ∫ z, conditionalTranscriptDirectionalScore P θ v p n z
        ∂transcriptLaw P θ p n = 0 := by
  rw [← transcriptLaw_eq_withDensity_reference P θ p n]
  change (∫ z, conditionalTranscriptDirectionalScore P θ v p n z
    ∂(transcriptReferenceMeasure P n).withDensity
      ((transcriptLaw P θ p n).rnDeriv (transcriptReferenceMeasure P n))) = 0
  rw [integral_withDensity_eq_integral_toReal_smul
    (Measure.measurable_rnDeriv _ _)
    (Measure.rnDeriv_lt_top _ _)]
  change (∫ z, (transcriptDensity P θ p n z).toReal •
    conditionalTranscriptDirectionalScore P θ v p n z
    ∂transcriptReferenceMeasure P n) = 0
  rw [show (∫ z,
      (transcriptDensity P θ p n z).toReal •
        conditionalTranscriptDirectionalScore P θ v p n z
        ∂transcriptReferenceMeasure P n) =
      ∫ z, transcriptMixtureRealDerivative P θ v p n z
        ∂transcriptReferenceMeasure P n by
    apply integral_congr_ae
    filter_upwards
      [transcriptDensity_toReal_ae_eq_mixture_of_interior P θ p n hp hθ,
       transcriptMixtureRealDensity_pos_ae P θ p n hp hθ]
      with z heq hpos
    simpa [smul_eq_mul, heq] using
      (transcriptDerivative_eq_density_mul_conditionalScore
        P θ v p n z hpos.ne').symm]
  exact integral_transcriptMixtureRealDerivative_eq_zero P θ v p n

-- keep: reusable sequential-law, Fisher-information, or van-Trees bridge for related adaptive experiments
/-- the conditional transcript directional score sq integrable assertion holds. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hp,hθ), [the conditional Transcript Directional Score sq integrable](goal).

Under the stated assumptions, the conditional Transcript Directional Score sq integrable. -/
lemma conditionalTranscriptDirectionalScore_sq_integrable {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ v : TrialParameter) (p : ℝ) (n : ℕ)
    (hp : InteriorAssignment p) (hθ : InteriorMeans θ) :
    Integrable (fun z => (conditionalTranscriptDirectionalScore P θ v p n z) ^ 2)
      (transcriptLaw P θ p n) :=
  (conditionalTranscriptDirectionalScore_memLp_two P θ v p n hp hθ).integrable_sq

end CausalSmith.Stat.LdpAteEfficiencySurface
