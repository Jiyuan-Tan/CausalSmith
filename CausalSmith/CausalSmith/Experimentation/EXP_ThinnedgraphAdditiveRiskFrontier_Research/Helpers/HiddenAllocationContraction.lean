module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.ActiveLabelEnergyBound
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.ConditionalDensityBridge
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.ActiveRowAverage
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.ChiSqDecomposition
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.ContractionSeries
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.HiddenAllocationSummation
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.HiddenSignEnergy
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.RevealedSubsetEnergyBridge
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.RetainedRowAverage
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.RowEnergyCounts

/-!
# Hidden-allocation chi-squared contraction
-/

public section

open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- All-degree contraction on the good event, integrated over the actual detailed retained graph.  [For the stated data and conditions](hyp:n,B,d,h,q,μZ,hn,hB,hd,hfit,hh,hq,ha,hsmall), [the stated conclusion holds](goal). -/
-- @node: lem:hidden-allocation-contraction
lemma hidden_allocation_contraction (n B d : ℕ) (h q : ℝ) (μZ : Measure (Assign (Fin n)))
    (hn : 4 ≤ n) (hB : 1 ≤ B) (hd : 1 ≤ d) (hfit : 2 * (B * d) ≤ n)
    (hh : h ∈ Set.Icc 0 (1 / 4)) (hq : q ∈ Set.Icc 0 1)
    (ha : AssignmentLaw (μZ.prod (auditLaw (Fin n) q)))
    (hsmall : 4 * Real.exp 1 * eta d h < 1) :
    (∫ H, Set.indicator {H | (B * d : ℕ) / (4 : ℝ) ≤ undiscovered n B d H}
      (hiddenChiSq n B d (μZ.prod (auditLaw (Fin n) q)) h) H
        ∂(retainedGraphMarginal n B d (μZ.prod (auditLaw (Fin n) q)))) ≤
      Real.exp (Real.exp 1 * B * retentionP d q * etaOne d h) /
        (1 - 4 * Real.exp 1 * eta d h) - 1 := by
  have henergy := eta_nonneg_le_etaOne d h
  have hrevealed : 0 ≤ retentionP d q * etaOne d h :=
    mul_nonneg (retentionP_mem_Icc d q hq).1 (henergy.1.trans henergy.2)
  have hseries := contraction_nonconstant_sum_bound B (retentionP d q * etaOne d h)
    (eta d h) (by omega) hrevealed henergy.1 hsmall
  rw [show Real.exp 1 * (B : ℝ) * (retentionP d q * etaOne d h) =
    Real.exp 1 * B * retentionP d q * etaOne d h by ring] at hseries
  refine le_trans ?_ hseries
  have hμ : μZ = halfBernoulli (Fin n) := by
    let : IsProbabilityMeasure (bernoulliLaw q) := bernoulliLaw_probability q hq
    let : IsProbabilityMeasure (auditLaw (Fin n) q) := by
      unfold auditLaw; infer_instance
    have hm := ha
    change (μZ.prod (auditLaw (Fin n) q)).map Prod.fst = halfBernoulli (Fin n) at hm
    rw [Measure.map_fst_prod, measure_univ, one_smul] at hm
    exact hm
  rw [hμ, show (halfBernoulli (Fin n)).prod (auditLaw (Fin n) q) =
    thinnedDesign (Fin n) q from rfl]
  have hnorm :
      (∫ H, Set.indicator {H | (B * d : ℕ) / (4 : ℝ) ≤ undiscovered n B d H}
        (actualDensityEnergy n B d h) H
        ∂retainedGraphMarginal n B d (thinnedDesign (Fin n) q)) =
      (∫ H, Set.indicator {H | (B * d : ℕ) / (4 : ℝ) ≤ undiscovered n B d H}
        (actualLabelEnergy n B d h) H
        ∂retainedGraphMarginal n B d (thinnedDesign (Fin n) q)) := by
    apply integral_congr_ae
    filter_upwards [retainedGraphMarginal_valid n B d (thinnedDesign (Fin n) q) hfit]
      with H hH
    obtain ⟨_, s, hs⟩ := hH
    by_cases hg : (B * d : ℕ) / (4 : ℝ) ≤ undiscovered n B d H
    · simp only [Set.indicator, Set.mem_ofPred_eq, hg, if_true]
      exact actualDensityEnergy_eq_actualLabelEnergy n B d hd hfit h H ⟨s, hs⟩
    · simp only [Set.indicator, Set.mem_ofPred_eq, hg, if_false]
  rw [hiddenChiSq_good_integral_eq_actualDensityEnergy n B d h q hn hB hd hfit hh hq,
    hnorm]
  suffices hbridge :
      (∫ H, Set.indicator {H | (B * d : ℕ) / (4 : ℝ) ≤ undiscovered n B d H}
        (actualLabelEnergy n B d h) H
        ∂retainedGraphMarginal n B d (thinnedDesign (Fin n) q)) ≤
      ∑ a ∈ Finset.range (B + 1), ∑ b ∈ Finset.range (B + 1),
        if a + b = 0 then 0 else
          (B.choose a : ℝ) * ((B - a).choose b : ℝ) *
            (min 1 (4 * (a + b : ℕ) / (B : ℝ))) ^ b *
            (retentionP d q * etaOne d h) ^ a * eta d h ^ b by
    exact hbridge
  let := design_isProbabilityMeasure (thinnedDesign (Fin n) q) q
    (thinnedDesign_assignment q hq) (thinnedDesign_audit q hq)
    (thinnedDesign_independent q hq)
  let := retainedGraphMarginal_probability n B d (thinnedDesign (Fin n) q)
  calc
    _ ≤ ∫ H, Set.indicator {H | (B * d : ℕ) / (4 : ℝ) ≤ undiscovered n B d H}
        (fun H => actualLabelActiveEnvelope n B d h H - 1) H
        ∂retainedGraphMarginal n B d (thinnedDesign (Fin n) q) := by
      apply integral_mono
      · fun_prop
      · fun_prop
      · intro H
        by_cases hg : (B * d : ℕ) / (4 : ℝ) ≤ undiscovered n B d H
        · simp only [Set.indicator, Set.mem_ofPred_eq, hg, if_true]
          exact actualLabelEnergy_le_activeEnvelope n B d h (by omega) (by omega) H hg
        · simp only [Set.indicator, Set.mem_ofPred_eq, hg, if_false, le_refl]
    _ = ∫ H, Set.indicator {H | (B * d : ℕ) / (4 : ℝ) ≤ undiscovered n B d H}
        (retainedRowEnergyEnvelope n B d h) H
        ∂retainedGraphMarginal n B d (thinnedDesign (Fin n) q) := by
      apply integral_congr_ae
      filter_upwards [retainedGraphMarginal_valid n B d (thinnedDesign (Fin n) q) hfit]
        with H hH
      by_cases hg : (B * d : ℕ) / (4 : ℝ) ≤ undiscovered n B d H
      · simp only [Set.indicator, Set.mem_ofPred_eq, hg, if_true]
        exact actualLabelActiveEnvelope_sub_one_eq_row_energy n B d h H hH
      · simp only [Set.indicator, Set.mem_ofPred_eq, hg, if_false]
    _ ≤ _ := by
      exact retained_row_energy_average_le n B d h q hfit hq

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
