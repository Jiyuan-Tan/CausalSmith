import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.PathCertificates

/-! Paper-local conditional-moment factorization certificates for the labelled path. -/

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open scoped BigOperators ENNReal
open MeasureTheory Set

noncomputable section

/-- Restricting the finite path sum to a latent-arm cell selects exactly that class and arm. -/
-- @node: path_sum_restrict_latentCell
lemma path_sum_restrict_latentCell (g h : ℝ) (u : Fin 2) (t : Bool)
    [dA : DecidablePred (· ∈ latentCell u t)] (F : FullData 2 2 2 → ℝ) :
    (∑ v : Fin 2, ∑ s : Bool, ∑ x : Bool, ∑ z : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
      pathWeight g h v s x z y0 y1 *
        @ite ℝ (pathPoint v s x z y0 y1 ∈ latentCell u t)
          (dA (pathPoint v s x z y0 y1)) (F (pathPoint v s x z y0 y1)) 0) =
    ∑ x : Bool, ∑ z : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
      pathWeight g h u t x z y0 y1 * F (pathPoint u t x z y0 y1) := by
  classical
  rw [Finset.sum_eq_single u]
  · rw [Finset.sum_eq_single t]
    · have hin (x z y0 y1 : Bool) : pathPoint u t x z y0 y1 ∈ latentCell u t := by
        simp [latentCell, pathPoint, witnessPoint]
      simp_rw [if_pos (hin _ _ _ _)]
    · intro s _ hst
      have hout (x z y0 y1 : Bool) : pathPoint u s x z y0 y1 ∉ latentCell u t := by
        simp [latentCell, pathPoint, witnessPoint, hst]
      simp_rw [if_neg (hout _ _ _ _)]
      simp
    · simp
  · intro v _ hvu
    have hout (s x z y0 y1 : Bool) : pathPoint v s x z y0 y1 ∉ latentCell u t := by
      simp [latentCell, pathPoint, witnessPoint, hvu]
    simp_rw [if_neg (hout _ _ _ _ _)]
    simp
  · simp

/-- Restricted integrals under the labelled path reduce to its defining finite sum. -/
-- @node: integral_pathLaw_restrict
lemma integral_pathLaw_restrict (g h : ℝ) (A : Set (FullData 2 2 2))
    [DecidablePred (· ∈ A)] (hA : MeasurableSet A) (F : FullData 2 2 2 → ℝ) :
    ∫ w in A, F w ∂pathLaw g h =
      ∑ u : Fin 2, ∑ t : Bool, ∑ x : Bool, ∑ z : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
        (ENNReal.ofReal (pathWeight g h u t x z y0 y1)).toReal *
          if pathPoint u t x z y0 y1 ∈ A then F (pathPoint u t x z y0 y1) else 0 := by
  classical
  let c : Fin 2 × Bool × Bool × Bool × Bool × Bool → ℝ≥0∞ := fun i =>
    ENNReal.ofReal (pathWeight g h i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2.1
      i.2.2.2.2.2)
  let p : Fin 2 × Bool × Bool × Bool × Bool × Bool → FullData 2 2 2 := fun i =>
    pathPoint i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2.1 i.2.2.2.2.2
  have hpath : pathLaw g h = ∑ i, c i • Measure.dirac (p i) := by
    simp only [pathLaw, c, p, Fintype.sum_prod_type]
  rw [← integral_indicator hA, hpath, integral_finsetSum_measure]
  · simp only [c, p, Fintype.sum_prod_type, integral_smul_measure, integral_dirac,
      smul_eq_mul, Set.indicator_apply]
  · intro i _
    exact (integrable_dirac (by simp)).smul_measure (by simp [c])

/-- Conditional means on a labelled-path latent-arm cell reduce to the corresponding finite sum. -/
-- @node: conditionalMean_path_latentCell
lemma conditionalMean_path_latentCell (g h : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1 / 4)
    (hh : |h| ≤ 1 / 100) (u : Fin 2) (t : Bool) (F : FullData 2 2 2 → ℝ) :
    conditionalMean (pathLaw g h) (latentCell u t) F =
      (∑ x : Bool, ∑ z : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
        pathWeight g h u t x z y0 y1)⁻¹ *
      (∑ x : Bool, ∑ z : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
        pathWeight g h u t x z y0 y1 * F (pathPoint u t x z y0 y1)) := by
  classical
  rw [conditionalMean, pathLaw_real g h _ (measurableSet_witness_latentCell u t),
    integral_pathLaw_restrict g h _ (measurableSet_witness_latentCell u t)]
  simp_rw [ENNReal.toReal_ofReal (pathWeight_nonneg g h hg0 hg1 hh _ _ _ _ _ _)]
  rw [path_sum_restrict_latentCell g h u t (fun _ => (1 : ℝ)),
    path_sum_restrict_latentCell]
  simp

/-- Conditional means on a labelled-path latent class reduce to the corresponding finite sum. -/
-- @node: conditionalMean_path_latentClass
lemma conditionalMean_path_latentClass (g h : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1 / 4)
    (hh : |h| ≤ 1 / 100) (u : Fin 2) (F : FullData 2 2 2 → ℝ) :
    conditionalMean (pathLaw g h) (latentClass u) F =
      (∑ t : Bool, ∑ x : Bool, ∑ z : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
        pathWeight g h u t x z y0 y1)⁻¹ *
      (∑ t : Bool, ∑ x : Bool, ∑ z : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
        pathWeight g h u t x z y0 y1 * F (pathPoint u t x z y0 y1)) := by
  classical
  rw [conditionalMean, pathLaw_real g h _ (measurableSet_witness_latentClass u),
    integral_pathLaw_restrict g h _ (measurableSet_witness_latentClass u)]
  simp_rw [ENNReal.toReal_ofReal (pathWeight_nonneg g h hg0 hg1 hh _ _ _ _ _ _)]
  rw [path_sum_restrict_latentClass g h u (fun _ => (1 : ℝ)),
    path_sum_restrict_latentClass]
  simp

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
-- Expanding the 64 Bernoulli terms requires more than the default heartbeat budget.
/-- The labelled path preserves reference-proxy conditional independence. -/
-- @node: path_referenceProxySeparation
lemma path_referenceProxySeparation (g h : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1 / 4)
    (hh : |h| ≤ 1 / 100) : ReferenceProxySeparation (pathLaw g h) := by
  have hb := abs_le.mp hh
  have hp0 : 2 / 5 + h ≠ 0 := by nlinarith [hb.1, hb.2]
  have hp1 : 3 / 5 - h ≠ 0 := by nlinarith [hb.1, hb.2]
  have h4 : 15 * h + 4 ≠ 0 := by nlinarith [hb.1, hb.2]
  have h3 : 5 * h + 3 ≠ 0 := by nlinarith [hb.1, hb.2]
  have hw0f : 6 / 25 + 2 * h / 5 ≠ 0 := by nlinarith [hb.1, hb.2]
  have hw0t : 4 / 25 + 3 * h / 5 ≠ 0 := by nlinarith [hb.1, hb.2]
  have hw1f : 6 / 25 - 2 * h / 5 ≠ 0 := by nlinarith [hb.1, hb.2]
  have hw1t : 9 / 25 - 3 * h / 5 ≠ 0 := by nlinarith [hb.1, hb.2]
  intro u t f q _hf _hq _hfb _hqb
  rw [conditionalMean_path_latentCell g h hg0 hg1 hh,
    conditionalMean_path_latentCell g h hg0 hg1 hh,
    conditionalMean_path_latentCell g h hg0 hg1 hh]
  fin_cases u <;> cases t <;>
    simp (config := { maxSteps := 1000000 })
      [pathWeight, pathPoint, witnessPoint, boolReal, bernoulliMass,
        pathArmWeights_formula _ _ _ hh,
        pathReferenceFeature_second_formula _ _ _ hh, pathTargetFeature] <;>
    field_simp [hp0, hp1, h4, h3, hw0f, hw0t, hw1f, hw1t]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
-- Expanding the 128 Bernoulli terms requires more than the default heartbeat budget.
/-- The labelled path preserves target-proxy conditional independence. -/
-- @node: path_targetProxySeparation
lemma path_targetProxySeparation (g h : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1 / 4)
    (hh : |h| ≤ 1 / 100) : TargetProxySeparation (pathLaw g h) := by
  have hb := abs_le.mp hh
  have hp0 : 2 / 5 + h ≠ 0 := by nlinarith [hb.1, hb.2]
  have hp1 : 3 / 5 - h ≠ 0 := by nlinarith [hb.1, hb.2]
  have h4 : 15 * h + 4 ≠ 0 := by nlinarith [hb.1, hb.2]
  have h3 : 5 * h + 3 ≠ 0 := by nlinarith [hb.1, hb.2]
  have hw0f : 6 / 25 + 2 * h / 5 ≠ 0 := by nlinarith [hb.1, hb.2]
  have hw0t : 4 / 25 + 3 * h / 5 ≠ 0 := by nlinarith [hb.1, hb.2]
  have hw1f : 6 / 25 - 2 * h / 5 ≠ 0 := by nlinarith [hb.1, hb.2]
  have hw1t : 9 / 25 - 3 * h / 5 ≠ 0 := by nlinarith [hb.1, hb.2]
  intro u f q _hf _hq _hfb _hqb
  rw [conditionalMean_path_latentClass g h hg0 hg1 hh,
    conditionalMean_path_latentClass g h hg0 hg1 hh,
    conditionalMean_path_latentClass g h hg0 hg1 hh]
  fin_cases u <;>
    simp (config := { maxSteps := 1000000 })
      [pathWeight, pathPoint, witnessPoint, boolReal, bernoulliMass,
        pathArmWeights_formula _ _ _ hh,
        pathReferenceFeature_second_formula _ _ _ hh, pathTargetFeature] <;>
    field_simp [hp0, hp1, h4, h3, hw0f, hw0t, hw1f, hw1t]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Expanding the 128 Bernoulli terms requires more than the default heartbeat budget.
/-- The labelled path preserves armwise latent ignorability. -/
-- @node: path_armwiseLatentIgnorability
lemma path_armwiseLatentIgnorability (g h : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1 / 4)
    (hh : |h| ≤ 1 / 100) : ArmwiseLatentIgnorability (pathLaw g h) := by
  have hb := abs_le.mp hh
  have hp0 : 2 / 5 + h ≠ 0 := by nlinarith [hb.1, hb.2]
  have hp1 : 3 / 5 - h ≠ 0 := by nlinarith [hb.1, hb.2]
  have h4 : 15 * h + 4 ≠ 0 := by nlinarith [hb.1, hb.2]
  have h3 : 5 * h + 3 ≠ 0 := by nlinarith [hb.1, hb.2]
  have hw0f : 6 / 25 + 2 * h / 5 ≠ 0 := by nlinarith [hb.1, hb.2]
  have hw0t : 4 / 25 + 3 * h / 5 ≠ 0 := by nlinarith [hb.1, hb.2]
  have hw1f : 6 / 25 - 2 * h / 5 ≠ 0 := by nlinarith [hb.1, hb.2]
  have hw1t : 9 / 25 - 3 * h / 5 ≠ 0 := by nlinarith [hb.1, hb.2]
  intro u t f q _hf _hq _hfb _hqb
  rw [conditionalMean_path_latentClass g h hg0 hg1 hh,
    conditionalMean_path_latentClass g h hg0 hg1 hh,
    conditionalMean_path_latentClass g h hg0 hg1 hh]
  fin_cases u <;> cases t <;>
    simp (config := { maxSteps := 1000000 })
      [pathWeight, pathPoint, witnessPoint, potential, boolReal, bernoulliMass,
        pathArmWeights_formula _ _ _ hh,
        pathReferenceFeature_second_formula _ _ _ hh, pathTargetFeature] <;>
    field_simp [hp0, hp1, h4, h3, hw0f, hw0t, hw1f, hw1t]

end

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
