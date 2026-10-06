module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.SequentialScoreProjectionInputs

/-! # Measurability of scalar-direction local risks -/

public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

/-- Squared scaled error is jointly measurable in a scalar local direction and
an arbitrary released transcript. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:P,theta,v,n), these specify the stated inputs. -/
lemma measurable_scaledError_sq_scaledDirection
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (theta v : TrialParameter) (n : ℕ) :
    Measurable (fun az : ℝ × Transcript (Z n) =>
      ENNReal.ofReal ((scaledError P theta (scaledDirection az.1 v) n az.2) ^ 2)) := by
  apply ENNReal.measurable_ofReal.comp
  apply Measurable.pow_const
  unfold scaledError contrast localAlternative
  simp only [scaledDirection]
  exact measurable_const.mul ((P.estimate_measurable n).comp measurable_snd |>.sub (by fun_prop))

/-- For every procedure, the local risk along a scalar direction is measurable
without any countability assumption on the output spaces. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:P,theta,v,p,n), these specify the stated inputs. -/
lemma measurable_localRisk_scaledDirection
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (theta v : TrialParameter) (p : ℝ) (n : ℕ) :
    Measurable (fun a => localRisk P theta (scaledDirection a v) p n) := by
  let loss : ℝ → Transcript (Z n) → ℝ≥0∞ := fun a z =>
    ENNReal.ofReal ((scaledError P theta (scaledDirection a v) n z) ^ 2)
  have hloss : Measurable (Function.uncurry loss) := by
    exact measurable_scaledError_sq_scaledDirection P theta v n
  have hcomponent (x : Fin n → Fin 4) : Measurable (fun a =>
      ∫⁻ z, loss a z ∂P.transcript n x) := by
    letI : IsProbabilityMeasure (P.transcript n x) := (P.factorizes n x).1
    exact hloss.lintegral_prod_right
  have hweight (x : Fin n → Fin 4) : Measurable (fun a =>
      ENNReal.ofReal (inputPathProbability
        (localAlternative theta (scaledDirection a v) n) p x)) := by
    apply ENNReal.measurable_ofReal.comp
    have heq (a : ℝ) : localAlternative theta (scaledDirection a v) n =
        parameterPath theta v (a / Real.sqrt n) := by
      funext k
      simp only [localAlternative, scaledDirection, parameterPath]
      ring
    simp_rw [heq]
    have hc : Continuous (fun u => inputPathProbability
        (parameterPath theta v u) p x) := by
      rw [continuous_iff_continuousAt]
      intro u
      exact (hasDerivAt_inputPathProbability_parameterPath theta v p u x).continuousAt
    exact hc.measurable.comp (by fun_prop)
  have hsum : Measurable (fun a => ∑ x : Fin n → Fin 4,
      ENNReal.ofReal (inputPathProbability
        (localAlternative theta (scaledDirection a v) n) p x) *
      ∫⁻ z, loss a z ∂P.transcript n x) := by
    apply Finset.measurable_fun_sum
    intro x hx
    exact (hweight x).mul (hcomponent x)
  convert hsum using 1
  funext a
  unfold localRisk transcriptLaw
  rw [MeasureTheory.lintegral_finset_sum_measure]
  apply Finset.sum_congr rfl
  intro x hx
  rw [MeasureTheory.lintegral_smul_measure]
  rfl

/-- The scalar local-risk measurability hypothesis used by compact-prior Bayes
ordering is therefore automatic. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:P,theta,v,p,ell,upper,n), these specify the stated inputs. -/
lemma aemeasurable_localRisk_scaledDirection
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (theta v : TrialParameter) (p ell upper : ℝ)
    (n : ℕ) :
    AEMeasurable (fun a => localRisk P theta (scaledDirection a v) p n)
      (Causalean.Stat.Minimax.ObservationDependentVanTrees.parameterMeasure ell upper) :=
  (measurable_localRisk_scaledDirection P theta v p n).aemeasurable

/-- The compact-prior Bayes ordering theorem has no remaining measurability
premise for a paper procedure. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:P,theta,v,p,H,ell,upper,htheta,w,hw,hwint,hw_nonneg,hnorm,hcover), these specify the stated inputs. -/
-- keep: reusable sequential-law, Fisher-information, or van-Trees bridge for related adaptive experiments
lemma eventually_compactPrior_bayesRisk_le_localWorstRisk_auto
    {Z : OutputFamily} [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (theta v : TrialParameter) (p H ell upper : ℝ)
    (htheta : InteriorMeans theta)
    (w : ℝ → ℝ) (hw : Measurable w)
    (hwint : Integrable w
      (Causalean.Stat.Minimax.ObservationDependentVanTrees.parameterMeasure ell upper))
    (hw_nonneg : ∀ a, 0 ≤ w a)
    (hnorm : ∫ a, w a
      ∂Causalean.Stat.Minimax.ObservationDependentVanTrees.parameterMeasure ell upper = 1)
    (hcover : ∀ a ∈ Set.Icc ell upper,
      Real.sqrt (((scaledDirection a v) 0) ^ 2 +
        ((scaledDirection a v) 1) ^ 2) ≤ H) :
    ∀ᶠ n in Filter.atTop,
      AEMeasurable (fun a => ENNReal.ofReal (w a) *
        localRisk P theta (scaledDirection a v) p n)
        (Causalean.Stat.Minimax.ObservationDependentVanTrees.parameterMeasure ell upper) ∧
      (∫⁻ a, ENNReal.ofReal (w a) *
        localRisk P theta (scaledDirection a v) p n
        ∂Causalean.Stat.Minimax.ObservationDependentVanTrees.parameterMeasure ell upper) ≤
          localWorstRisk P theta p H n := by
  exact eventually_compactPrior_bayesRisk_le_localWorstRisk
    P theta v p H ell upper htheta w hw hwint hw_nonneg hnorm hcover
    (fun n ↦ aemeasurable_localRisk_scaledDirection P theta v p ell upper n)

end CausalSmith.Stat.LdpAteEfficiencySurface
