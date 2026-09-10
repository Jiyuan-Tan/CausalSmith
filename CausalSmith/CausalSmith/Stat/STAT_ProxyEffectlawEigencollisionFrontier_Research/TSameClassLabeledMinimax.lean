import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.TLabeledWeightUpper
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.TMatchingLocalLowerBounds

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open MeasureTheory

/-- The inverse-gap lower and upper bounds hold on the same gap-localized two-class model. -/
-- @node: prop:same-class-labeled-minimax
theorem same_class_labeled_minimax :
    ∃ c C : ℝ,
      0 < c ∧ -- @realizes \(c\)(positive same-class labeled lower constant)
      0 < C ∧ -- @realizes \(C\)(positive finite same-class labeled upper constant)
      c < C ∧
      ∀ n : ℕ, 1 ≤ n →
    ∀ g : ℝ, GapScaleDomain g →
      (∀ est : WeightEstimator 2 2 2 n,
        ∃ (P : Measure (FullData 2 2 2)) (_hP : IsProbabilityMeasure P),
          letI := _hP
          ∃ hM : GapStratum (L := 2) (pi0 := 1 / 10) (sigma0 := 1 / 10) (g := g) P,
          c * min 1 (Real.sqrt n * g)⁻¹ ≤
            expectedWeightRisk P
              (orderedMasses (quotientLawRaw P (effectRadius 2 2 (1 / 10)))) est) ∧
      ∃ est : WeightEstimator 2 2 2 n,
        ∀ (P : Measure (FullData 2 2 2)) (_hP : IsProbabilityMeasure P),
          letI := _hP
          (hM : GapStratum (L := 2) (pi0 := 1 / 10) (sigma0 := 1 / 10) (g := g) P) →
          expectedWeightRisk P
            (orderedMasses (quotientLawRaw P (effectRadius 2 2 (1 / 10)))) est ≤
            C * min 1 (Real.sqrt n * g)⁻¹ := by
  obtain ⟨cLoc, a, cLower, CKL, hcLoc, ha, haMax, hcLower, hCKL, hlower⟩ :=
    matching_local_lower_bounds
  obtain ⟨CUpper, hCUpper, hupper⟩ :=
    labeled_weight_upper 2 2 2 2 (1 / 10) (1 / 10)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let c : ℝ := min cLower (CUpper / 2)
  refine ⟨c, CUpper, lt_min hcLower (half_pos hCUpper), hCUpper, ?_, ?_⟩
  · exact lt_of_le_of_lt (min_le_right _ _) (half_lt_self hCUpper)
  · intro n hn g hGap
    obtain ⟨hg, hgMax⟩ := hGap
    constructor
    · intro est
      obtain ⟨P, hP, hLocal, _hWitness, hRisk⟩ :=
        (hlower n hn).2.1 g ⟨hg, hgMax⟩ est
      refine ⟨P, hP, hLocal.toGapStratum, ?_⟩
      exact le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _)
        (by positivity)) hRisk
    · obtain ⟨R, est, hest, hRisk⟩ := hupper n hn
      refine ⟨est, ?_⟩
      intro P hP
      letI := hP
      intro hM
      have htargetEq :
          orderedMasses (quotientLaw P hM.toUCVMWModel).representative.1 =
            orderedMasses (quotientLawRaw P (effectRadius 2 2 (1 / 10))) := by
        let nu : AtomicLaw.ProbabilityLaw 2 (effectRadius 2 2 (1 / 10)) :=
          ⟨quotientLawRaw P (effectRadius 2 2 (1 / 10)),
            quotientLawRaw_valid P hM.toUCVMWModel⟩
        have hrel :
            (quotientLaw P hM.toUCVMWModel).representative.MeasureEquivalent nu := by
          change (AtomicLaw.probabilityLawSetoid 2 (effectRadius 2 2 (1 / 10))).r
            (quotientLaw P hM.toUCVMWModel).representative nu
          change (AtomicLaw.probabilityLawSetoid 2 (effectRadius 2 2 (1 / 10))).r
            (AtomicLaw.LawModulo.ofProbabilityLaw nu).representative nu
          exact (Quotient.eq_mk_iff_out
            (x := AtomicLaw.LawModulo.ofProbabilityLaw nu) (y := nu)).mp rfl
        exact orderedMasses_eq_of_measureEquivalent
          (quotientLaw P hM.toUCVMWModel).representative nu hrel
      rw [← htargetEq]
      exact hRisk g ⟨hg, hgMax⟩ P hP hM

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
