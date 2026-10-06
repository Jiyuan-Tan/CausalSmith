module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.TUnrestrictedMixedCountUpper
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.NearComplete.ObservedContrast
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.NearComplete.CompleteArrivalTwoPoint
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.SyntheticKernel

/-! The all-kernel point-risk envelope at every arrival floor. The same universal
constant also certifies the mixed-count upper theorem. No rare-arrival slice is used. -/

public section
open MeasureTheory ProbabilityTheory Set
namespace CausalSmith.Stat.MarRareqLogfrontier

/-- Given [the specified inputs and assumptions](hyp:n,d,q,q',P,hP,hq,hqq'), [the stated mathematical conclusion holds](goal). -/
-- @node: unrestricted_arrival_floor_mono
lemma unrestricted_arrival_floor_mono {n d : ℕ} {q q' : ℝ} {P : FullLaw d}
    (hP : UnrestrictedArrivalModelClass n d q' P) (hq : 0 < q) (hqq' : q ≤ q') :
    UnrestrictedArrivalModelClass n d q P := by
  refine ⟨hP.n_pos, hP.d_pos, hq, hqq'.trans hP.q_le_one,
    hP.randomized, hP.balanced, hP.surrogate, hP.outcome, hP.mar, ?_⟩
  intro j hj
  exact (mul_le_mul_of_nonneg_right hqq' measureReal_nonneg).trans (hP.arrival j hj)

/-- Given [the specified inputs and assumptions](hyp:n,d,q,b,f,hf,hb,hbound), [the stated mathematical conclusion holds](goal). -/
-- @node: unrestricted_deterministic_upper
lemma unrestricted_deterministic_upper {n d : ℕ} {q b : ℝ}
    (f : (Fin n → ObsRecord d) → ℝ)
    (hf : Measurable f ∧ ∀ s, f s ∈ Icc (-1 : ℝ) 1) (hb : 0 ≤ b)
    (hbound : ∀ P : FullLaw d, UnrestrictedArrivalModelClass n d q P →
      deterministicRisk f P ≤ b) :
    unrestrictedMinimaxRisk n d q ≤ b ∧
      Causalean.Stat.worstCaseRiskReal
        (fun (_ : Unit) (P : {P : FullLaw d // UnrestrictedArrivalModelClass n d q P}) =>
          deterministicRisk f P.1) () ≤ b := by
  have hw : Causalean.Stat.worstCaseRiskReal
      (fun (_ : Unit) (P : {P : FullLaw d // UnrestrictedArrivalModelClass n d q P}) =>
        deterministicRisk f P.1) () ≤ b := by
    unfold Causalean.Stat.worstCaseRiskReal
    by_cases hne : Nonempty {P : FullLaw d // UnrestrictedArrivalModelClass n d q P}
    · letI := hne
      exact ciSup_le (fun P => hbound P.1 P.2)
    · haveI := not_nonempty_iff.mp hne
      simpa using hb
  refine ⟨le_trans ?_ hw, hw⟩
  let T : Estimator n d := Estimator.ofMap f hf
  have h := Causalean.Stat.minimaxValue_le_worstCaseRisk_of_nonneg
    (risk := fun (T : Estimator n d)
      (P : {P : FullLaw d // UnrestrictedArrivalModelClass n d q P}) => squaredRisk T P.1)
    (fun T P => (unrestricted_squaredRisk_bounds T P.1).1) T
  simpa [unrestrictedMinimaxRisk, Causalean.Stat.worstCaseRiskReal,
    squaredRisk, deterministicRisk, T, Estimator.ofMap, Kernel.deterministic_apply] using h

/-- Given [the specified inputs and assumptions](hyp:n,d,q,hn,hd,hq,hq1), [the stated mathematical conclusion holds](goal). -/
-- @node: unrestricted_complete_submodel_floor
lemma unrestricted_complete_submodel_floor {n d : ℕ} {q : ℝ}
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hq : 0 < q) (hq1 : q ≤ 1) :
    1 / (256 * (n : ℝ)) ≤ unrestrictedMinimaxRisk n d q := by
  have hfloor := (complete_arrival_frontier_direct n d hn hd).1
  refine hfloor.trans ?_
  let T₀ : Estimator n d :=
    Estimator.ofMap (fun _ => 0) ⟨measurable_const, by intro s; norm_num⟩
  letI : Nonempty (Estimator n d) := ⟨T₀⟩
  apply Causalean.Stat.minimaxValue_mono_class_of_nonneg
    (risk := fun (T : Estimator n d)
      (P : {P : FullLaw d // UnrestrictedArrivalModelClass n d 1 P}) => squaredRisk T P.1)
    (risk' := fun (T : Estimator n d)
      (P : {P : FullLaw d // UnrestrictedArrivalModelClass n d q P}) => squaredRisk T P.1)
    (fun P => ⟨P.1, unrestricted_arrival_floor_mono P.2 hq hq1⟩)
  · exact fun T P => (unrestricted_squaredRisk_bounds T P.1).1
  · exact fun T P => (unrestricted_squaredRisk_bounds T P.1).1
  · intro T
    refine ⟨4, ?_⟩
    rintro _ ⟨P, rfl⟩
    exact (unrestricted_squaredRisk_bounds T P.1).2
  · exact fun _ _ => le_rfl

-- @node: thm:unrestricted-near-complete-arrival-envelope
/-- [the stated mathematical conclusion holds](goal). -/
theorem unrestricted_near_complete_arrival_envelope :
    ∃ C : ℝ, 0 < C ∧ -- @realizes \(\overline C\)(shared universal upper constant)
      (∀ (n d : ℕ) (q : ℝ) (P : FullLaw d),
        UnrestrictedArrivalModelClass n d q P →
        IIDSampling n (sampleLaw n P)
          (fun (i : Fin n) (s : Fin n → ObsRecord d) => s i) P →
        deterministicRisk (mixedCountEstimator n d q) P ≤ riskEnvelope n d q ∧
        riskEnvelope n d q ≤ C * frontierRate n d q ∧
        deterministicRisk (mixedCountEstimator n d q) P ≤ auxiliaryMixedRisk n q P) ∧
      ∀ (n d : ℕ) (q : ℝ), 1 ≤ n → 1 ≤ d → 0 < q → q ≤ 1 →
        1 / (256 * (n : ℝ)) ≤ unrestrictedMinimaxRisk n d q ∧
        unrestrictedMinimaxRisk n d q ≤
          min 1 (min (C * frontierRate n d q) (4 / (n : ℝ) + (1 - q) ^ 2)) ∧
        Causalean.Stat.worstCaseRiskReal
          (fun (_ : Unit) (P : {P : FullLaw d // UnrestrictedArrivalModelClass n d q P}) =>
            deterministicRisk (completeArrivalHTEstimator n d) P.1) () ≤
          4 / (n : ℝ) + (1 - q) ^ 2 := by
  obtain ⟨C, hC, hmixed⟩ := unrestricted_mixed_count_upper
  refine ⟨C, hC, hmixed, ?_⟩
  intro n d q hn hd hq hq1
  have hzero : unrestrictedMinimaxRisk n d q ≤ 1 := by
    apply (unrestricted_deterministic_upper (fun _ => 0)
      ⟨measurable_const, by intro s; norm_num⟩ (by norm_num) ?_).1
    intro P hP
    letI : IsProbabilityMeasure P.1 := P.2
    letI : IsProbabilityMeasure (P.1.map obs) :=
      Measure.isProbabilityMeasure_map (by fun_prop)
    letI : IsProbabilityMeasure (sampleLaw n P) := by unfold sampleLaw; infer_instance
    have ht := ate_mem_unit_interval P
    have hs : (ate P) ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    simpa [deterministicRisk] using hs
  have hrate : 0 ≤ C * frontierRate n d q := by
    apply mul_nonneg hC.le
    unfold frontierRate effectiveSize
    exact le_min (by norm_num) (add_nonneg (inv_nonneg.mpr (mul_nonneg (Nat.cast_nonneg _) hq.le))
      (sq_nonneg _))
  have hmix : unrestrictedMinimaxRisk n d q ≤ C * frontierRate n d q := by
    apply (unrestricted_deterministic_upper (mixedCountEstimator n d q)
      (mixed_count_estimator_regular n d q) hrate ?_).1
    intro P hP
    obtain ⟨hrisk, henv, _⟩ := hmixed n d q P hP (sampleLaw_iid n P)
    exact hrisk.trans henv
  have hht := unrestricted_deterministic_upper (q := q) (completeArrivalHTEstimator n d)
    (complete_arrival_ht_estimator_regular n d)
    (add_nonneg (div_nonneg (by norm_num) (Nat.cast_nonneg _)) (sq_nonneg _))
    (fun P hP => observed_contrast_risk_le P hP)
  exact ⟨unrestricted_complete_submodel_floor hn hd hq hq1,
    le_min hzero (le_min hmix hht.1), hht.2⟩

end CausalSmith.Stat.MarRareqLogfrontier
