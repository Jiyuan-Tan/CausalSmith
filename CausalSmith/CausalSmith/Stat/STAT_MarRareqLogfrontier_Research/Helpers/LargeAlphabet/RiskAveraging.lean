module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.LargeAlphabet.RiskTesting
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.NearComplete.CompleteArrivalTwoPoint

/-! Prior averaging of the common randomized test and member squared risks. -/

public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace CausalSmith.Stat.MarRareqLogfrontier

/-- Given [the specified inputs and assumptions](hyp:n,d,q,hd,hq,hq1,f), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabetSampleMixture_integral
lemma largeAlphabetSampleMixture_integral (n d : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1)
    (f : (Fin n → ObsRecord d) → ℝ) :
    (∫ s, f s ∂largeAlphabetSampleMixture n d q hd hq hq1) =
      ∫ ξ, (∫ s, f s ∂sampleLaw n (largeAlphabetLaw q ξ hd hq hq1))
        ∂binaryCellPrior d := by
  classical
  let μ : Measure Bool := (1 / 2 : ℝ≥0∞) • Measure.dirac false +
    (1 / 2 : ℝ≥0∞) • Measure.dirac true
  let : IsProbabilityMeasure μ := fairBinary_probability
  let : IsProbabilityMeasure (binaryCellPrior d) := inferInstanceAs
    (IsProbabilityMeasure (Measure.pi (fun _ : Fin d => μ)))
  let : IsProbabilityMeasure (largeAlphabetSampleMixture n d q hd hq hq1) :=
    largeAlphabetSampleMixture_probability n d q hd hq hq1
  rw [integral_fintype Integrable.of_finite]
  simp only [smul_eq_mul]
  simp_rw [largeAlphabetSampleMixture_real_singleton]
  simp_rw [← integral_mul_const]
  rw [← integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  apply integral_congr_ae
  filter_upwards [] with ξ
  let := (largeAlphabetLaw q ξ hd hq hq1).2
  let : IsProbabilityMeasure ((largeAlphabetLaw q ξ hd hq hq1).1.map obs) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  let : IsProbabilityMeasure (sampleLaw n (largeAlphabetLaw q ξ hd hq hq1)) := by
    unfold sampleLaw
    infer_instance
  exact (integral_fintype Integrable.of_finite).symm

/-- Given [the specified inputs and assumptions](hyp:Z,Q,κ,E,hE), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabet_joint_event_integral
lemma largeAlphabet_joint_event_integral
    {Z : Type*} [MeasurableSpace Z] (Q : Measure Z) [IsProbabilityMeasure Q]
    (κ : BoundedKernel Z) (E : Set (Z × ℝ)) (hE : MeasurableSet E) :
    (Q ⊗ₘ κ.1).real E =
      ∫ s, ∫ w, E.indicator (fun _ => (1 : ℝ)) (s, w) ∂κ.1 s ∂Q := by
  let : IsMarkovKernel κ.1 := κ.2.1
  have hi : Integrable (E.indicator (fun _ => (1 : ℝ))) (Q ⊗ₘ κ.1) :=
    (integrable_const 1).indicator hE
  rw [← Measure.integral_compProd hi, integral_indicator_const 1 hE]
  simp

/-- Given [the specified inputs and assumptions](hyp:n,d,q,hd,hq,hq1,κ,E,hE), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabetSampleMixture_joint_event
lemma largeAlphabetSampleMixture_joint_event (n d : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1)
    (κ : BoundedKernel (Fin n → ObsRecord d))
    (E : Set ((Fin n → ObsRecord d) × ℝ)) (hE : MeasurableSet E) :
    (largeAlphabetSampleMixture n d q hd hq hq1 ⊗ₘ κ.1).real E =
      ∫ ξ, (sampleLaw n (largeAlphabetLaw q ξ hd hq hq1) ⊗ₘ κ.1).real E
        ∂binaryCellPrior d := by
  let : IsProbabilityMeasure (largeAlphabetSampleMixture n d q hd hq hq1) :=
    largeAlphabetSampleMixture_probability n d q hd hq hq1
  rw [largeAlphabet_joint_event_integral _ κ E hE,
    largeAlphabetSampleMixture_integral]
  apply integral_congr_ae
  filter_upwards [] with ξ
  let := (largeAlphabetLaw q ξ hd hq hq1).2
  let : IsProbabilityMeasure ((largeAlphabetLaw q ξ hd hq hq1).1.map obs) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  let : IsProbabilityMeasure (sampleLaw n (largeAlphabetLaw q ξ hd hq hq1)) := by
    unfold sampleLaw
    infer_instance
  exact (largeAlphabet_joint_event_integral _ κ E hE).symm

/-- Given [the specified inputs and assumptions](hyp:n,d,q,hd,hq,hq1,T,a,h,hh), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabet_prior_test_risk
lemma largeAlphabet_prior_test_risk (n d : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1)
    (T : Estimator n d) (a h : ℝ) (hh : 0 ≤ h) :
    (h ^ 2 / 16) *
      (largeAlphabetSampleMixture n d q hd hq hq1 ⊗ₘ T.1).real
        {z | z.2 ≤ a - h / 2} ≤
      (∫ ξ, squaredRisk T (largeAlphabetLaw q ξ hd hq hq1) ∂binaryCellPrior d) +
        (h ^ 2 / 16) * (binaryCellPrior d).real
          {ξ | h / 4 < |cellPriorTarget ξ - a|} := by
  classical
  let μ : Measure Bool := (1 / 2 : ℝ≥0∞) • Measure.dirac false +
    (1 / 2 : ℝ≥0∞) • Measure.dirac true
  let : IsProbabilityMeasure μ := fairBinary_probability
  let : IsProbabilityMeasure (binaryCellPrior d) := inferInstanceAs
    (IsProbabilityMeasure (Measure.pi (fun _ : Fin d => μ)))
  rw [largeAlphabetSampleMixture_joint_event n d q hd hq hq1 T _ (by measurability),
    ← integral_const_mul]
  have hp (ξ : Fin d → Bool) := by
    let := (largeAlphabetLaw q ξ hd hq hq1).2
    let : IsProbabilityMeasure ((largeAlphabetLaw q ξ hd hq hq1).1.map obs) :=
      Measure.isProbabilityMeasure_map (by fun_prop)
    let : IsProbabilityMeasure (sampleLaw n (largeAlphabetLaw q ξ hd hq hq1)) := by
      unfold sampleLaw
      infer_instance
    exact largeAlphabet_member_test_risk
      (sampleLaw n (largeAlphabetLaw q ξ hd hq hq1)) T a h
      (ate (largeAlphabetLaw q ξ hd hq hq1)) hh
  have havg := integral_mono (μ := binaryCellPrior d)
    Integrable.of_finite Integrable.of_finite hp
  simp_rw [largeAlphabetLaw_ate] at havg
  rw [integral_add Integrable.of_finite Integrable.of_finite] at havg
  have hpenalty :
      (∫ ξ, (if h / 4 < |cellPriorTarget ξ - a| then h ^ 2 / 16 else 0)
        ∂binaryCellPrior d) =
      (h ^ 2 / 16) * (binaryCellPrior d).real
        {ξ | h / 4 < |cellPriorTarget ξ - a|} := by
    change (∫ ξ, {ξ | h / 4 < |cellPriorTarget ξ - a|}.indicator
      (fun _ => h ^ 2 / 16) ξ ∂binaryCellPrior d) = _
    rw [integral_indicator_const _ (by measurability), smul_eq_mul, mul_comm]
  rw [hpenalty] at havg
  simpa only [squaredRisk, largeAlphabetLaw_ate] using havg

/-- Given [the specified inputs and assumptions](hyp:n,d,q,hn,hd,hq,hq1,T), [the stated mathematical conclusion holds](goal). -/
-- @node: largeAlphabet_prior_squaredRisk_le_worst
lemma largeAlphabet_prior_squaredRisk_le_worst (n d : ℕ) (q : ℝ)
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1)
    (T : Estimator n d) :
    (∫ ξ, squaredRisk T (largeAlphabetLaw q ξ hd hq hq1) ∂binaryCellPrior d) ≤
      Causalean.Stat.worstCaseRiskReal
        (fun (T : Estimator n d) (P : {P : FullLaw d //
          UnrestrictedArrivalModelClass n d q P}) => squaredRisk T P.1) T := by
  let μ : Measure Bool := (1 / 2 : ℝ≥0∞) • Measure.dirac false +
    (1 / 2 : ℝ≥0∞) • Measure.dirac true
  let : IsProbabilityMeasure μ := fairBinary_probability
  let : IsProbabilityMeasure (binaryCellPrior d) := inferInstanceAs
    (IsProbabilityMeasure (Measure.pi (fun _ : Fin d => μ)))
  have hbdd : BddAbove (Set.range (fun P : {P : FullLaw d //
      UnrestrictedArrivalModelClass n d q P} => squaredRisk T P.1)) := by
    refine ⟨4, ?_⟩
    rintro _ ⟨P, rfl⟩
    exact (unrestricted_squaredRisk_bounds T P.1).2
  have hle (ξ : Fin d → Bool) := Causalean.Stat.le_worstCaseRisk
    (risk := fun (T : Estimator n d) (P : {P : FullLaw d //
      UnrestrictedArrivalModelClass n d q P}) => squaredRisk T P.1)
    (e := T) hbdd ⟨_, largeAlphabetLaw_model q ξ hn hd hq hq1⟩
  simpa using integral_mono (μ := binaryCellPrior d)
    Integrable.of_finite (integrable_const _) hle

end CausalSmith.Stat.MarRareqLogfrontier
