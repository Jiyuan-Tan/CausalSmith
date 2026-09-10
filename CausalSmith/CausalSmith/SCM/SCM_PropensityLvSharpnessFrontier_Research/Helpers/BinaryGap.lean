import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.Helpers.FiniteQuery
import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.Helpers.BinaryWitness
import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.TSupportRegimeOpenIllegalDichotomy

/-! # Binary success-query legality gaps -/

namespace CausalSmith.SCM.PropensityLvSharpnessFrontier

open MeasureTheory Set

/-- One-sided binary propensity mixtures have lower success-probability
endpoint `e * p`.  For the specified model objects, [the stated conditions](hyp:hPos,hp), [the stated mathematical relationship holds](goal).
-/
-- @node: binaryOneSidedMixture_sInf
lemma binaryOneSidedMixture_sInf (e p : ℝ) (hPos : StrictPositivity e)
    (hp : p ∈ Set.Ioo 0 1) :
    sInf {q : ℝ | q ∈ Set.Icc 0 1 ∧
      binaryLaw q ∈ mixtureClassOneSidedSet e (binaryLaw p)} = e * p := by
  let _ : IsProbabilityMeasure (binaryLaw p) :=
    binaryLaw_isProbabilityMeasure p ⟨hp.1.le, hp.2.le⟩
  have hep : e * p ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg hPos.1.le hp.1.le,
      calc
        e * p ≤ 1 * p := mul_le_mul_of_nonneg_right hPos.2.le hp.1.le
        _ ≤ 1 := by simpa using hp.2.le⟩
  apply le_antisymm
  · apply csInf_le
    · refine ⟨0, ?_⟩
      rintro q ⟨hq, _⟩
      exact hq.1
    · exact ⟨hep, binaryLaw_lowerCap_mem_mixtureOneSided e p hPos
        ⟨hp.1.le, hp.2.le⟩⟩
  · apply le_csInf
    · exact ⟨e * p, hep, binaryLaw_lowerCap_mem_mixtureOneSided e p hPos
        ⟨hp.1.le, hp.2.le⟩⟩
    · intro q hq
      have hle := ((mixture_oneSided_iff_measure_le e (binaryLaw p)
        (binaryLaw q) hPos).1 hq.2).2
      have htrue := hle {true}
      have htrue' : ENNReal.ofReal (e * p) ≤ ENNReal.ofReal q := by
        simpa [Measure.smul_apply, binaryLaw_true p ⟨hp.1.le, hp.2.le⟩,
          binaryLaw_true q hq.1, ENNReal.ofReal_mul hPos.1.le] using htrue
      exact (ENNReal.ofReal_le_ofReal_iff hq.1.1).mp htrue'

/-- The oriented open illegal region yields a strict binary success-query gap
for the one-sided relaxation.  For the specified model objects, [the stated conditions](hyp:hPos,hf,hNot), [the stated mathematical relationship holds](goal).
-/
-- @node: oneSided_successIndicatorGap_of_openIllegal
lemma oneSided_successIndicatorGap_of_openIllegal
    (e : ℝ) (f : ℝ → ℝ) (hPos : StrictPositivity e)
    (hf : AdmissibleGenerator f) (hNot : f ∉ hingeClassSet (1 / e)) :
    SuccessIndicatorLegalityGap f e true := by
  rcases support_regime_open_illegal_dichotomy e f hPos hf hNot with
    ⟨O, hO, hOne, hSub, hLower, hcases⟩
  obtain ⟨z₀, hz₀⟩ := hOne
  have hzcoord := hSub hz₀
  let O' : Set ℝ := {p | (p, z₀.2) ∈ O}
  have hO' : IsOpen O' := by
    exact hO.preimage (continuous_id.prodMk continuous_const)
  have hp₀ : z₀.1 ∈ O' := hz₀
  refine ⟨O', hO', ⟨z₀.1, hp₀⟩, ?_, ?_⟩
  · intro p hp
    exact (hSub hp).1
  · intro p hp
    have hpcoord := hSub hp
    have hqball : binaryLaw z₀.2 ∈ jkBallOneSidedSet f e (binaryLaw p) := by
      rcases hcases with hcase | hcase
      · exact (hcase.2 (p, z₀.2) hp).1.1
      · rcases hcase with ⟨b, d, hcd, hzero, hregion⟩
        exact (hregion (p, z₀.2) hp).1.1
    have hlower : z₀.2 < e * p := hLower (p, z₀.2) hp
    change sInf {q : ℝ | q ∈ Set.Icc 0 1 ∧
      binaryLaw q ∈ jkBallOneSidedSet f e (binaryLaw p)} <
      sInf {q : ℝ | q ∈ Set.Icc 0 1 ∧
        binaryLaw q ∈ mixtureClassOneSidedSet e (binaryLaw p)}
    rw [binaryOneSidedMixture_sInf e p hPos hpcoord.1]
    exact lt_of_le_of_lt (csInf_le (by
      refine ⟨0, ?_⟩
      rintro q ⟨hq, _⟩
      exact hq.1) ⟨⟨hpcoord.2.1.le, hpcoord.2.2.le⟩, hqball⟩) hlower

/-- Mutual-support binary propensity mixtures have lower success-probability
endpoint `e * p`.  For the specified model objects, [the stated conditions](hyp:hPos,hp), [the stated mathematical relationship holds](goal).
-/
-- @node: binaryMutualMixture_sInf
lemma binaryMutualMixture_sInf (e p : ℝ) (hPos : StrictPositivity e)
    (hp : p ∈ Set.Ioo 0 1) :
    sInf {q : ℝ | q ∈ Set.Icc 0 1 ∧
      binaryLaw q ∈ mixtureClassSet e (binaryLaw p)} = e * p := by
  let _ : IsProbabilityMeasure (binaryLaw p) :=
    binaryLaw_isProbabilityMeasure p ⟨hp.1.le, hp.2.le⟩
  have hepIoo : e * p ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨mul_pos hPos.1 hp.1,
      calc e * p < 1 * p := mul_lt_mul_of_pos_right hPos.2 hp.1
        _ < 1 := by simpa using hp.2⟩
  have hLowerOne := binaryLaw_lowerCap_mem_mixtureOneSided e p hPos
    ⟨hp.1.le, hp.2.le⟩
  have hLowerMutual : binaryLaw (e * p) ∈ mixtureClassSet e (binaryLaw p) :=
    (mixture_reverse_support e (binaryLaw p) (binaryLaw (e * p)) hPos).2
      ⟨hLowerOne, (binaryLaw_mutuallyAC (e * p) p hepIoo hp).1⟩
  have hep : e * p ∈ Set.Icc (0 : ℝ) 1 := ⟨hepIoo.1.le, hepIoo.2.le⟩
  apply le_antisymm
  · exact csInf_le (by
      refine ⟨0, ?_⟩
      rintro q ⟨hq, _⟩
      exact hq.1) ⟨hep, hLowerMutual⟩
  · apply le_csInf
    · exact ⟨e * p, hep, hLowerMutual⟩
    · intro q hq
      have hOne := (mixture_reverse_support e (binaryLaw p) (binaryLaw q) hPos).1 hq.2 |>.1
      have hle := ((mixture_oneSided_iff_measure_le e (binaryLaw p)
        (binaryLaw q) hPos).1 hOne).2
      have htrue := hle {true}
      have htrue' : ENNReal.ofReal (e * p) ≤ ENNReal.ofReal q := by
        simpa [Measure.smul_apply, binaryLaw_true p ⟨hp.1.le, hp.2.le⟩,
          binaryLaw_true q hq.1, ENNReal.ofReal_mul hPos.1.le] using htrue
      exact (ENNReal.ofReal_le_ofReal_iff hq.1.1).mp htrue'

/-- The common oriented open illegal region yields a strict binary
success-query gap for the mutual-support relaxation.  For the specified model objects, [the stated conditions](hyp:hPos,hf,hNot), [the stated mathematical relationship holds](goal).
-/
-- @node: mutual_successIndicatorGap_of_openIllegal
lemma mutual_successIndicatorGap_of_openIllegal
    (e : ℝ) (f : ℝ → ℝ) (hPos : StrictPositivity e)
    (hf : AdmissibleGenerator f) (hNot : f ∉ hingeClassSet (1 / e)) :
    SuccessIndicatorLegalityGap f e false := by
  rcases support_regime_open_illegal_dichotomy e f hPos hf hNot with
    ⟨O, hO, hOne, hSub, hLower, hcases⟩
  obtain ⟨z₀, hz₀⟩ := hOne
  let O' : Set ℝ := {p | (p, z₀.2) ∈ O}
  have hO' : IsOpen O' := hO.preimage (continuous_id.prodMk continuous_const)
  refine ⟨O', hO', ⟨z₀.1, hz₀⟩, fun p hp => (hSub hp).1, ?_⟩
  intro p hp
  have hpcoord := hSub hp
  have hqball : binaryLaw z₀.2 ∈ jkBallSet f e (binaryLaw p) := by
    rcases hcases with hcase | hcase
    · exact (hcase.2 (p, z₀.2) hp).2.1.1
    · rcases hcase with ⟨b, d, hcd, hzero, hregion⟩
      exact (hregion (p, z₀.2) hp).2.1.1
  change sInf {q : ℝ | q ∈ Set.Icc 0 1 ∧
    binaryLaw q ∈ jkBallSet f e (binaryLaw p)} <
    sInf {q : ℝ | q ∈ Set.Icc 0 1 ∧
      binaryLaw q ∈ mixtureClassSet e (binaryLaw p)}
  rw [binaryMutualMixture_sInf e p hPos hpcoord.1]
  exact lt_of_le_of_lt (csInf_le (by
    refine ⟨0, ?_⟩
    rintro q ⟨hq, _⟩
    exact hq.1) ⟨⟨hpcoord.2.1.le, hpcoord.2.2.le⟩, hqball⟩)
    (hLower (p, z₀.2) hp)

end CausalSmith.SCM.PropensityLvSharpnessFrontier
