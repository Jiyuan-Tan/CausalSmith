import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Helpers.DenseMomentMatchingLower

/-! Pairwise assembly of the dense priors' variance and concentration bounds. -/

namespace CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched

open MeasureTheory ProbabilityTheory

/-- Both members of a Cai--Low prior pair satisfy the variance and one-eighth
target-concentration clauses needed by the dense fuzzy-hypothesis argument. This uses [the dense construction domain conditions hold](hyp:hdom), and [the two priors satisfy the moment-matching certificate](hyp:hpair), and [the stated scale inequality holds](hyp:hscale). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma densePriorPair_variance_and_concentration {n d : ℕ} {epsilon : ℝ}
    (hdom : DenseConstructionDomain n d epsilon) (nu0 nu1 : Measure ℝ)
    (hpair : DensePriorPairConditions (lowerDegree d) nu0 nu1)
    (hscale : 32 ≤ (d : ℝ) *
      bestEvenApproxError (lowerDegree d) ^ 2) :
    ∀ nu ∈ ({nu0, nu1} : Set (Measure ℝ)),
      (∫ theta, (denseTargetAt theta -
          densePriorTargetMean n d epsilon hdom nu) ^ 2
          ∂denseScaledProductPrior n d epsilon hdom nu ≤
            denseAmplitude n d ^ 2 / (4 * d)) ∧
      denseScaledProductPrior n d epsilon hdom nu
          {theta | |denseTargetAt theta -
            densePriorTargetMean n d epsilon hdom nu| >
            densePriorSeparation n d / 4} ≤ 1 / 8 := by
  have hE_nonneg : 0 ≤
      bestEvenApproxError (lowerDegree d) := by
    unfold bestEvenApproxError
    apply le_csInf
    · refine ⟨1, 0, by simp, ?_⟩
      intro t ht
      simpa using (abs_le.mpr ht)
    · intro e he
      rcases he with ⟨p, _hpdeg, hp⟩
      have hzero := hp 0 (by constructor <;> norm_num)
      have hzero' : |Polynomial.eval 0 p| ≤ e := by
        simpa only [abs_zero, zero_sub, abs_neg] using hzero
      exact (abs_nonneg _).trans hzero'
  have hE : 0 < bestEvenApproxError (lowerDegree d) := by
    by_contra hnot
    have hzero : bestEvenApproxError (lowerDegree d) = 0 :=
      le_antisymm (le_of_not_gt hnot) hE_nonneg
    rw [hzero] at hscale
    norm_num at hscale
  intro nu hnu
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hnu
  rcases hnu with hnu | hnu
  · subst nu
    letI : IsProbabilityMeasure nu0 := hpair.1
    exact ⟨densePriorTarget_variance_le hdom nu0 hpair.2.2.1,
      densePriorTarget_tail_le hdom nu0 hpair.2.2.1 hE hscale⟩
  · subst nu
    letI : IsProbabilityMeasure nu1 := hpair.2.1
    exact ⟨densePriorTarget_variance_le hdom nu1 hpair.2.2.2.1,
      densePriorTarget_tail_le hdom nu1 hpair.2.2.2.1 hE hscale⟩

end CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched
