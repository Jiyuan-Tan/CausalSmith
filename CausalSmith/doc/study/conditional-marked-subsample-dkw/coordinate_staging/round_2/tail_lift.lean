import Causalean.Stat.Quantile.ConditionalMarkedSubsampleDkw.ConditionalLaw
import Causalean.Stat.Quantile.ConditionalMarkedSubsampleDkw.FiniteAggregation
import Causalean.Stat.Quantile.ConditionalMarkedSubsampleDkw.Measurability

/-!
# Empirical-CDF tail bounds after Boolean selection

This module lifts any fixed-size i.i.d. empirical-CDF tail bound through
independent Boolean marking and the resulting random sample size.  It also
packages the count-dependent radius used with the sharp two-sided
DKW--Massart bound.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace Causalean.Stat.Quantile.ConditionalMarkedSubsampleDkw

/-- Given [a finite marked iid experiment](hyp:S), [a requested mark](hyp:a), [a selected-outcome
probability law](hyp:ρ), and [a count-indexed radius](hyp:radius), [the selected-subsample empirical-CDF bad event is measurable](goal). -/
lemma measurableSet_selectedCDFBadEvent
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    {μ : Measure Ω} {ν : Measure (Bool × ℝ)}
    (S : MarkedIID Ω n μ ν) (a : Bool) (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ] (radius : ℕ → ℝ) :
    MeasurableSet (selectedCDFBadEvent S.Z a ρ radius) := by
  -- Decompose over words and use `measurableSet_fixedCDFBadSet` on positive-count pullbacks.
  -- For a zero-count word, `selectedCount_eq_on_wordEvent` makes the intersection empty.
  rw [show selectedCDFBadEvent S.Z a ρ radius =
      ⋃ w : Fin n → Bool, selectedCDFBadEvent S.Z a ρ radius ∩ wordEvent S.Z w by
    ext ω
    constructor
    · intro hbad
      have hcover : ω ∈ ⋃ w : Fin n → Bool, wordEvent S.Z w := by
        rw [iUnion_wordEvent]
        exact Set.mem_univ ω
      rcases Set.mem_iUnion.mp hcover with ⟨w, hword⟩
      exact Set.mem_iUnion_of_mem w ⟨hbad, hword⟩
    · rintro h
      rcases Set.mem_iUnion.mp h with ⟨w, hbad, _⟩
      exact hbad]
  exact MeasurableSet.iUnion fun w => by
    by_cases hw : 0 < selectedWordCount w a
    · rw [selectedCDFBadEvent_inter_wordEvent S.Z a ρ radius w hw]
      exact ((measurableSet_fixedCDFBadSet ρ _).preimage
        (measurable_selectedOutcomes S a w)).inter
          (measurableSet_wordEvent S.Z S.measurable w)
    · rw [show selectedCDFBadEvent S.Z a ρ radius ∩ wordEvent S.Z w = ∅ by
        ext ω
        constructor
        · rintro ⟨hbad, hword⟩
          exact (hw (by simpa [selectedCount_eq_on_wordEvent S.Z a w hword] using hbad.1)).elim
        · simp]
      exact MeasurableSet.empty

/-- Given [a finite marked iid experiment](hyp:S), [a requested mark](hyp:a), [its mass](hyp:e),
[a selected-outcome law](hyp:ρ), [a Boolean mark factorization](hyp:hfac), [a count-indexed radius](hyp:radius), [a probability bound](hyp:β), and [the corresponding fixed-size iid empirical-CDF bound at every positive sample size](hyp:hfixed), [the probability that the selected arm is nonempty and its uniform empirical-CDF deviation exceeds its count-indexed radius is at most β](goal). -/
theorem conditionalMarkedSubsample_empiricalCDF_tail
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    {μ : Measure Ω} {ν : Measure (Bool × ℝ)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (S : MarkedIID Ω n μ ν) (a : Bool) (e : ℝ≥0∞) (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ] (hfac : BooleanMarkFactorization ν a e ρ)
    (radius : ℕ → ℝ) (β : ℝ≥0∞)
    (hfixed : ∀ m : ℕ, 0 < m →
      (Measure.pi (fun _ : Fin m => ρ)) (fixedCDFBadSet ρ (radius m)) ≤ β) :
    μ (selectedCDFBadEvent S.Z a ρ radius) ≤ β := by
  -- Apply finite aggregation to exact words; positive-count cells use the conditional product law.
  -- Rewrite the cell intersection with `selectedCDFBadEvent_inter_wordEvent`, turn its pullback
  -- probability into a mapped conditional measure via `Measure.map_apply`, and then rewrite that
  -- map with `selectedOutcomes_conditionalLaw`.  Zero-count cells again have empty intersection.
  apply measure_le_of_cond_le_on_finite_partition μ
    (fun w : Fin n → Bool => wordEvent S.Z w)
    (fun w => measurableSet_wordEvent S.Z S.measurable w)
    (fun w v hwv => disjoint_wordEvent S.Z hwv)
    (iUnion_wordEvent S.Z) (selectedCDFBadEvent S.Z a ρ radius)
    (measurableSet_selectedCDFBadEvent S a ρ radius) β
  intro w hwprob
  by_cases hw : 0 < selectedWordCount w a
  · rw [cond_apply (measurableSet_wordEvent S.Z S.measurable w),
      inter_comm (wordEvent S.Z w),
      selectedCDFBadEvent_inter_wordEvent S.Z a ρ radius w hw]
    calc
      (μ (wordEvent S.Z w))⁻¹ *
          μ ((selectedOutcomes S.Z w a) ⁻¹'
            fixedCDFBadSet ρ (radius (selectedWordCount w a)) ∩ wordEvent S.Z w) =
          (Measure.map (selectedOutcomes S.Z w a) μ[|wordEvent S.Z w])
            (fixedCDFBadSet ρ (radius (selectedWordCount w a))) := by
              rw [Measure.map_apply (measurable_selectedOutcomes S a w)
                (measurableSet_fixedCDFBadSet ρ _),
                cond_apply (measurableSet_wordEvent S.Z S.measurable w), inter_comm]
      _ = (Measure.pi (fun _ : Fin (selectedWordCount w a) => ρ))
            (fixedCDFBadSet ρ (radius (selectedWordCount w a))) := by
              rw [S.selectedOutcomes_conditionalLaw a e ρ hfac w hwprob]
      _ ≤ β := hfixed (selectedWordCount w a) hw
  · rw [cond_apply (measurableSet_wordEvent S.Z S.measurable w)]
    have hinter : wordEvent S.Z w ∩ selectedCDFBadEvent S.Z a ρ radius = ∅ := by
      ext ω
      constructor
      · rintro ⟨hword, hbad⟩
        exact (hw (by simpa [selectedCount_eq_on_wordEvent S.Z a w hword] using hbad.1)).elim
      · simp
    simp [hinter]

/-- For [a confidence parameter](hyp:α) and [a selected count](hyp:m), [the DKW confidence radius](goal)
is [the square root of log(4/α) divided by twice that count](step:1). -/
noncomputable def dkwRadius (α : ℝ) (m : ℕ) : ℝ :=
  Real.sqrt (Real.log (4 / α) / (2 * (m : ℝ)))

/-- Given [a finite marked iid experiment](hyp:S), [a requested mark](hyp:a), [its mass](hyp:e),
[a selected-outcome law](hyp:ρ), [a Boolean mark factorization](hyp:hfac), [a confidence parameter between zero and one](hyp:α,hα,hα_one), and [the fixed-size DKW--Massart bound at every positive sample size](hyp:hDKW), [the selected-subsample empirical-CDF deviation at the DKW radius has tail probability at most α/2](goal). -/
theorem conditionalMarkedSubsample_dkwRadius
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    {μ : Measure Ω} {ν : Measure (Bool × ℝ)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (S : MarkedIID Ω n μ ν) (a : Bool) (e : ℝ≥0∞) (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ] (hfac : BooleanMarkFactorization ν a e ρ)
    (α : ℝ) (hα : 0 < α) (hα_one : α ≤ 1)
    (hDKW : ∀ m : ℕ, 0 < m →
      (Measure.pi (fun _ : Fin m => ρ))
          (fixedCDFBadSet ρ (dkwRadius α m)) ≤ ENNReal.ofReal (α / 2)) :
    μ (selectedCDFBadEvent S.Z a ρ (dkwRadius α)) ≤ ENNReal.ofReal (α / 2) := by
  -- This is the generic lifting theorem specialized to `dkwRadius` and the supplied DKW bound.
  exact conditionalMarkedSubsample_empiricalCDF_tail S a e ρ hfac
    (dkwRadius α) (ENNReal.ofReal (α / 2)) hDKW

end Causalean.Stat.Quantile.ConditionalMarkedSubsampleDkw
