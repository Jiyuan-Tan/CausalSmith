import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.Witness

/-! Conditional-independence verification for the explicit finite witness. -/

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open scoped BigOperators ENNReal
open MeasureTheory Set

noncomputable section

-- @node: witness_sum_restrict_latentCell
lemma witness_sum_restrict_latentCell (eps : ℝ) (u : Fin 2) (t : Bool)
    [dA : DecidablePred (· ∈ latentCell u t)] (F : FullData 2 2 2 → ℝ) :
    (∑ v : Fin 2, ∑ s : Bool, ∑ x : Bool, ∑ z : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
      witnessWeight eps v s x z y0 y1 *
        @ite ℝ (witnessPoint v s x z y0 y1 ∈ latentCell u t)
          (dA (witnessPoint v s x z y0 y1))
          (F (witnessPoint v s x z y0 y1)) 0) =
    ∑ x : Bool, ∑ z : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
      witnessWeight eps u t x z y0 y1 * F (witnessPoint u t x z y0 y1) := by
  classical
  rw [Finset.sum_eq_single u]
  · rw [Finset.sum_eq_single t]
    · have hin (x z y0 y1 : Bool) : witnessPoint u t x z y0 y1 ∈ latentCell u t := by
        simp [latentCell, witnessPoint]
      simp_rw [if_pos (hin _ _ _ _)]
    · intro s _ hst
      have hout (x z y0 y1 : Bool) : witnessPoint u s x z y0 y1 ∉ latentCell u t := by
        simp [latentCell, witnessPoint, hst]
      simp_rw [if_neg (hout _ _ _ _)]
      simp
    · simp
  · intro v _ hvu
    have hout (s x z y0 y1 : Bool) : witnessPoint v s x z y0 y1 ∉ latentCell u t := by
      simp [latentCell, witnessPoint, hvu]
    simp_rw [if_neg (hout _ _ _ _ _)]
    simp
  · simp

-- @node: conditionalMean_witness_latentCell
lemma conditionalMean_witness_latentCell (eps : ℝ) (hlo : 0 ≤ eps)
    (hhi : eps ≤ 1 / 8) (u : Fin 2) (t : Bool) (F : FullData 2 2 2 → ℝ) :
    conditionalMean (witnessLaw eps) (latentCell u t) F =
      (∑ x : Bool, ∑ z : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
        witnessWeight eps u t x z y0 y1)⁻¹ *
      (∑ x : Bool, ∑ z : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
        witnessWeight eps u t x z y0 y1 * F (witnessPoint u t x z y0 y1)) := by
  classical
  rw [conditionalMean_witnessLaw eps _ (measurableSet_witness_latentCell u t)]
  simp_rw [ENNReal.toReal_ofReal (witnessWeight_nonneg eps hlo hhi _ _ _ _ _ _)]
  rw [witness_sum_restrict_latentCell eps u t (fun _ => (1 : ℝ)),
    witness_sum_restrict_latentCell]
  simp

-- @node: witness_sum_restrict_latentClass
lemma witness_sum_restrict_latentClass (eps : ℝ) (u : Fin 2)
    [dA : DecidablePred (· ∈ latentClass u)] (F : FullData 2 2 2 → ℝ) :
    (∑ v : Fin 2, ∑ t : Bool, ∑ x : Bool, ∑ z : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
      witnessWeight eps v t x z y0 y1 *
        @ite ℝ (witnessPoint v t x z y0 y1 ∈ latentClass u)
          (dA (witnessPoint v t x z y0 y1))
          (F (witnessPoint v t x z y0 y1)) 0) =
    ∑ t : Bool, ∑ x : Bool, ∑ z : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
      witnessWeight eps u t x z y0 y1 * F (witnessPoint u t x z y0 y1) := by
  classical
  rw [Finset.sum_eq_single u]
  · have hin (t x z y0 y1 : Bool) : witnessPoint u t x z y0 y1 ∈ latentClass u := by
      simp [latentClass, witnessPoint]
    simp_rw [if_pos (hin _ _ _ _ _)]
  · intro v _ hvu
    have hout (t x z y0 y1 : Bool) : witnessPoint v t x z y0 y1 ∉ latentClass u := by
      simp [latentClass, witnessPoint, hvu]
    simp_rw [if_neg (hout _ _ _ _ _)]
    simp
  · simp

-- @node: conditionalMean_witness_latentClass
lemma conditionalMean_witness_latentClass (eps : ℝ) (hlo : 0 ≤ eps)
    (hhi : eps ≤ 1 / 8) (u : Fin 2) (F : FullData 2 2 2 → ℝ) :
    conditionalMean (witnessLaw eps) (latentClass u) F =
      (∑ t : Bool, ∑ x : Bool, ∑ z : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
        witnessWeight eps u t x z y0 y1)⁻¹ *
      (∑ t : Bool, ∑ x : Bool, ∑ z : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
        witnessWeight eps u t x z y0 y1 * F (witnessPoint u t x z y0 y1)) := by
  classical
  rw [conditionalMean_witnessLaw eps _ (measurableSet_witness_latentClass u)]
  simp_rw [ENNReal.toReal_ofReal (witnessWeight_nonneg eps hlo hhi _ _ _ _ _ _)]
  rw [witness_sum_restrict_latentClass eps u (fun _ => (1 : ℝ)),
    witness_sum_restrict_latentClass]
  simp

-- @node: witness_referenceProxySeparation
lemma witness_referenceProxySeparation (eps : ℝ) (hlo : 0 ≤ eps) (hhi : eps ≤ 1 / 8) :
    ReferenceProxySeparation (witnessLaw eps) := by
  intro u t f q _hf _hq _hfb _hqb
  rw [conditionalMean_witness_latentCell eps hlo hhi,
    conditionalMean_witness_latentCell eps hlo hhi,
    conditionalMean_witness_latentCell eps hlo hhi]
  fin_cases u <;> cases t <;>
    simp (config := { maxSteps := 1000000 })
      [witnessWeight, witnessPoint, boolReal, bernoulliMass] <;> ring

-- @node: witness_targetProxySeparation
lemma witness_targetProxySeparation (eps : ℝ) (hlo : 0 ≤ eps) (hhi : eps ≤ 1 / 8) :
    TargetProxySeparation (witnessLaw eps) := by
  intro u f q _hf _hq _hfb _hqb
  rw [conditionalMean_witness_latentClass eps hlo hhi,
    conditionalMean_witness_latentClass eps hlo hhi,
    conditionalMean_witness_latentClass eps hlo hhi]
  fin_cases u <;>
    simp (config := { maxSteps := 1000000 })
      [witnessWeight, witnessPoint, boolReal, bernoulliMass] <;> ring

-- @node: witness_armwiseLatentIgnorability
lemma witness_armwiseLatentIgnorability (eps : ℝ) (hlo : 0 ≤ eps) (hhi : eps ≤ 1 / 8) :
    ArmwiseLatentIgnorability (witnessLaw eps) := by
  intro u t f q _hf _hq _hfb _hqb
  rw [conditionalMean_witness_latentClass eps hlo hhi,
    conditionalMean_witness_latentClass eps hlo hhi,
    conditionalMean_witness_latentClass eps hlo hhi]
  fin_cases u <;> cases t <;>
    simp (config := { maxSteps := 1000000 })
      [witnessWeight, witnessPoint, potential, boolReal, bernoulliMass] <;> ring

end

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
