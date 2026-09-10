import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.PathKL
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.PathModelCertificates

/-! Gap and local-experiment certificates for the factorization-preserving labelled path. -/

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open scoped BigOperators ENNReal
open MeasureTheory Set

/-- Multiplying a Bernoulli mass by its Boolean outcome and summing returns its mean. -/
-- @node: pathBernoulli_mean
lemma pathBernoulli_mean (a p : ℝ) :
    ∑ b : Bool, a * bernoulliMass p b * boolReal b = a * p := by
  norm_num [bernoulliMass, boolReal]

/-- A Bernoulli nuisance coordinate integrates out even with a trailing constant factor. -/
-- @node: pathBernoulli_sum_mul
lemma pathBernoulli_sum_mul (a p c : ℝ) :
    ∑ b : Bool, a * bernoulliMass p b * c = a * c := by
  norm_num [bernoulliMass]
  ring

set_option maxHeartbeats 800000 in
-- The explicit 64-cell Bernoulli sum needs a larger heartbeat budget.
/-- Potential-outcome means on the labelled path equal their construction probabilities. -/
-- @node: path_latentMean
lemma path_latentMean (g h : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1 / 4)
    (hh : |h| ≤ 1 / 100) (u : Fin 2) (t : Bool) :
    latentMean (pathLaw g h) t u =
      if t then (if u.val = 0 then 1 / 2 - g / 2 else 1 / 2 + g / 2) else 1 / 4 := by
  rw [latentMean, conditionalMean_path_latentClass g h hg0 hg1 hh]
  have hb := abs_le.mp hh
  have hpu : (if u.val = 0 then 2 / 5 + h else 3 / 5 - h : ℝ) ≠ 0 := by
    fin_cases u <;> simp <;> nlinarith [hb.1, hb.2]
  rw [show (∑ s : Bool, ∑ x : Bool, ∑ z : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
      pathWeight g h u s x z y0 y1) =
      (if u.val = 0 then 2 / 5 + h else 3 / 5 - h) from pathWeight_sum_nuisance g h u]
  simp only [pathWeight, pathPoint, witnessPoint, potential]
  by_cases ht : t = true
  · subst t
    simp only [↓reduceIte]
    simp_rw [pathBernoulli_mean]
    simp_rw [pathBernoulli_sum_mul]
    rw [← mul_assoc, inv_mul_cancel₀ hpu, one_mul]
  · have ht' : t = false := Bool.eq_false_of_not_eq_true ht
    subst t
    simp only [Bool.false_eq_true, ↓reduceIte]
    simp_rw [pathBernoulli_sum_mul]
    simp_rw [pathBernoulli_mean]
    simp_rw [pathBernoulli_sum_mul]
    rw [← mul_assoc, inv_mul_cancel₀ hpu, one_mul]

/-- The two latent effects on the labelled path are exactly separated by `g`. -/
-- @node: path_latentEffect
lemma path_latentEffect (g h : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1 / 4)
    (hh : |h| ≤ 1 / 100) (u : Fin 2) :
    latentEffect (pathLaw g h) u =
      if u.val = 0 then 1 / 4 - g / 2 else 1 / 4 + g / 2 := by
  rw [latentEffect, path_latentMean g h hg0 hg1 hh u true,
    path_latentMean g h hg0 hg1 hh u false]
  fin_cases u <;> norm_num <;> ring

/-- The nearest positive effect gap of the labelled path is exactly `g`. -/
-- @node: path_effectGap
lemma path_effectGap (g h : ℝ) (hg : 0 < g) (hg1 : g ≤ 1 / 4)
    (hh : |h| ≤ 1 / 100) : effectGap (pathLaw g h) = (g : EReal) := by
  unfold effectGap
  have hset : {d : EReal | ∃ u v : Fin 2,
      0 < latentMass (pathLaw g h) u ∧ 0 < latentMass (pathLaw g h) v ∧
      latentEffect (pathLaw g h) u ≠ latentEffect (pathLaw g h) v ∧
      d = |latentEffect (pathLaw g h) u - latentEffect (pathLaw g h) v|} =
      {(g : EReal)} := by
    ext d
    constructor
    · rintro ⟨u, v, _hu, _hv, huv, rfl⟩
      rw [path_latentEffect g h hg.le hg1 hh u, path_latentEffect g h hg.le hg1 hh v]
      fin_cases u <;> fin_cases v <;> simp_all [abs_of_pos hg] <;> try ring
      rw [abs_neg, abs_of_pos hg]
    · intro hd
      simp only [Set.mem_singleton_iff] at hd
      subst d
      refine ⟨0, 1, ?_, ?_, ?_, ?_⟩
      · rw [path_latentMass g h hg.le hg1 hh]
        have hb := abs_le.mp hh
        norm_num
        linarith
      · rw [path_latentMass g h hg.le hg1 hh]
        have hb := abs_le.mp hh
        norm_num
        linarith
      · rw [path_latentEffect g h hg.le hg1 hh 0, path_latentEffect g h hg.le hg1 hh 1]
        norm_num
        linarith
      · rw [path_latentEffect g h hg.le hg1 hh 0, path_latentEffect g h hg.le hg1 hh 1]
        norm_num
        rw [show 1 / 4 - g / 2 - (1 / 4 + g / 2) = -g by ring,
          abs_neg, abs_of_pos hg]
  rw [hset]
  simp

/-- Both positive-mass effects on the labelled path are distinct. -/
-- @node: path_distinctEffects
lemma path_distinctEffects (g h : ℝ) (hg : 0 < g) (hg1 : g ≤ 1 / 4)
    (hh : |h| ≤ 1 / 100) : DistinctEffects (pathLaw g h) := by
  unfold DistinctEffects
  have hmass (u : Fin 2) : 0 < latentMass (pathLaw g h) u := by
    rw [path_latentMass g h hg.le hg1 hh]
    have hb := abs_le.mp hh
    fin_cases u <;> norm_num <;> linarith
  rw [Finset.filter_eq_self.mpr (fun u _ => hmass u)]
  apply Finset.card_image_iff.mpr
  intro u _ v _ huv
  rw [path_latentEffect g h hg.le hg1 hh u, path_latentEffect g h hg.le hg1 hh v] at huv
  fin_cases u <;> fin_cases v <;> simp_all <;> linarith

/-- Every small-displacement path law lies in the gap-localized model. -/
-- @node: path_gapStratum
lemma path_gapStratum (g h : ℝ) (hg : 0 < g) (hg1 : g ≤ 1 / 4)
    (hh : |h| ≤ 1 / 100) :
    letI := pathLaw_isProbabilityMeasure g h hg.le hg1
      (by constructor <;> linarith [abs_le.mp hh]) hh
    GapStratum (L := 2) (pi0 := 1 / 10) (sigma0 := 1 / 10) (g := g)
      (pathLaw g h) := by
  letI := pathLaw_isProbabilityMeasure g h hg.le hg1
    (by constructor <;> linarith [abs_le.mp hh]) hh
  refine { toUCVMWModel := path_ucvmwModel g h hg.le hg1 hh
           gapDomain := ⟨hg, hg1⟩
           gapWindow := ?_
           distinctEffects := path_distinctEffects g h hg hg1 hh }
  unfold GapWindow
  rw [path_effectGap g h hg hg1 hh]
  constructor
  · change ((g / 2 : ℝ) : EReal) ≤ (g : EReal)
    exact EReal.coe_le_coe_iff.mpr (div_le_self hg.le (by norm_num))
  · norm_cast
    nlinarith

/-- The observed KL certificate promotes a small labelled path into the local experiment. -/
-- @node: path_localWeightExperiment
lemma path_localWeightExperiment (n : ℕ) (cLoc g h : ℝ)
    (hcLoc : LocalRadiusDomain cLoc) (hg : 0 < g) (hg1 : g ≤ 1 / 4)
    (hh : |h| ≤ 1 / 100) (hKL : 16000 * g ^ 2 * h ^ 2 ≤ cLoc / n) :
    letI := pathLaw_isProbabilityMeasure g h hg.le hg1
      (by constructor <;> linarith [abs_le.mp hh]) hh
    LocalWeightExperiment (n := n) (L := 2) (pi0 := 1 / 10)
      (sigma0 := 1 / 10) (cLoc := cLoc) (g := g) (pathLaw g h) := by
  letI := pathLaw_isProbabilityMeasure g h hg.le hg1
    (by constructor <;> linarith [abs_le.mp hh]) hh
  letI : IsProbabilityMeasure (witnessLaw (g / 2)) :=
    witnessLaw_isProbabilityMeasure (g / 2) (by positivity) (by linarith)
  refine { toGapStratum := path_gapStratum g h hg hg1 hh
           cLoc_pos := hcLoc.1
           cLoc_lt_one := hcLoc.2
           neighborhood := ?_ }
  unfold LocalWeightNeighborhood
  dsimp only
  change InformationTheory.klDiv (obsLaw (pathLaw g h))
      (obsLaw (witnessLaw (g / 2))) ≤ ENNReal.ofReal (cLoc / n)
  simpa only [obsLaw, pathLaw_zero] using
    ((pathLaw_observed_kl_bound g h hg.le hg1 hh).trans
      (ENNReal.ofReal_le_ofReal hKL))

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
