module
public import Causalean.Stat.RecurrentEvent.CountingProcess.SubjectMoments

/-!
The single-subject predictable isometry for compensated censor counts,
with square-integrability and cancellation lemmas for its two terms.
-/

public section

open MeasureTheory

namespace Causalean.Stat.RecurrentEvent.CountingProcess

/-- Suppose subjects are drawn independently with [failure times following a nonnegative time
law](hyp:hFailure) and independent [censor times whose law has the given censor
hazard](hyp:hazard,hHazard), and let the payoff process be [jointly measurable in time and sample](hyp:hMeasurable).
For a horizon u and [finite expected quadratic energy](hyp:hQuadratic),
[the square of subject i's accumulated hazard-weighted at-risk payoff up to u is integrable over
samples](goal). -/
theorem subject_hazard_square_integrable {n : ℕ}
    (failureLaw censorLaw : Measure ℝ) (hazard : ℝ → ℝ)
    (hFailure : NonnegativeTimeLaw failureLaw)
    (hHazard : HasCensorHazard censorLaw hazard)
    (H : ℝ → Sample n → ℝ)
    (hMeasurable : Measurable (fun p : ℝ × Sample n => H p.1 p.2))
    (i : Fin n) (u : ℝ)
    (hQuadratic : QuadraticEnergyFinite failureLaw censorLaw hazard H u) :
    Integrable (fun x : Sample n =>
      (∫ s in Set.Icc 0 u,
        H s x * hazard s * riskIndicator i s x ∂volume) ^ 2)
      (sampleLaw n failureLaw censorLaw) := by
  /- Apply `subject_absolute_payoff_square_le_energy` on almost every path.
     The right side is a fixed finite hazard mass times subject energy; its
     expected integral is finite by `hQuadratic`. Joint measurability of the
     prefix integral supplies strong measurability of the square. -/
  classical
  haveI : IsProbabilityMeasure failureLaw := ⟨hFailure.1⟩
  haveI : IsProbabilityMeasure censorLaw := ⟨hHazard.1.1⟩
  let μ := sampleLaw n failureLaw censorLaw
  let ν := (volume : Measure ℝ).restrict (Set.Icc 0 u)
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ, sampleLaw]
    infer_instance
  let e : Sample n → ℝ → ℝ := fun x s =>
    (H s x) ^ 2 * hazard s * (∑ j : Fin n, riskIndicator j s x)
  have he_meas : Measurable (fun p : Sample n × ℝ => e p.1 p.2) := by
    have hrisk (j : Fin n) : Measurable (fun p : Sample n × ℝ =>
        riskIndicator j p.2 p.1) := by
      unfold riskIndicator
      have hf : Measurable (fun p : Sample n × ℝ => (p.1 j).1) := by fun_prop
      have hc : Measurable (fun p : Sample n × ℝ => (p.1 j).2) := by fun_prop
      have hs : MeasurableSet {p : Sample n × ℝ |
          0 ≤ p.2 ∧ p.2 ≤ (p.1 j).1 ∧ p.2 ≤ (p.1 j).2} := by
        simpa only [Set.ofPred_and, Set.inter_assoc, id_eq] using
          (((show MeasurableSet {p : Sample n × ℝ | (0 : ℝ) ≤ p.2} from
            measurableSet_le measurable_const measurable_snd).inter
          (measurableSet_le measurable_snd hf)).inter
          (measurableSet_le measurable_snd hc))
      exact measurable_const.ite hs measurable_const
    exact (((hMeasurable.comp (measurable_snd.prodMk measurable_fst)).pow_const 2).mul
      (hHazard.2.1.comp measurable_snd)).mul
      (Finset.measurable_fun_sum _ (fun j _ => hrisk j))
  have he_nonneg (x : Sample n) (s : ℝ) : 0 ≤ e x s := by
    dsimp [e]
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (hHazard.2.2.1 s))
      (Finset.sum_nonneg (fun j _ => by unfold riskIndicator; split_ifs <;> norm_num))
  have he_joint : Integrable (fun p : Sample n × ℝ => e p.1 p.2) (μ.prod ν) := by
    apply (lintegral_ofReal_ne_top_iff_integrable he_meas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => he_nonneg p.1 p.2))).1
    rw [lintegral_prod _ he_meas.ennreal_ofReal.aemeasurable]
    exact hQuadratic
  have he_outer : Integrable (fun x => ∫ s, e x s ∂ν) μ :=
    he_joint.integral_prod_left
  have he_path : ∀ᵐ x ∂μ, Integrable (e x) ν :=
    he_joint.prod_right_ae
  have hprefix : Measurable (fun x : Sample n =>
      ∫ s in Set.Icc 0 u,
        H s x * hazard s * riskIndicator i s x ∂volume) := by
    let F : Sample n × ℝ → ℝ := fun p =>
      H p.2 p.1 * hazard p.2 * riskIndicator i p.2 p.1
    have hrisk : Measurable (fun p : Sample n × ℝ =>
        riskIndicator i p.2 p.1) := by
      unfold riskIndicator
      have hf : Measurable (fun p : Sample n × ℝ => (p.1 i).1) := by fun_prop
      have hc : Measurable (fun p : Sample n × ℝ => (p.1 i).2) := by fun_prop
      have hs : MeasurableSet {p : Sample n × ℝ |
          0 ≤ p.2 ∧ p.2 ≤ (p.1 i).1 ∧ p.2 ≤ (p.1 i).2} := by
        simpa only [Set.ofPred_and, Set.inter_assoc, id_eq] using
          (((show MeasurableSet {p : Sample n × ℝ | (0 : ℝ) ≤ p.2} from
            measurableSet_le measurable_const measurable_snd).inter
          (measurableSet_le measurable_snd hf)).inter
          (measurableSet_le measurable_snd hc))
      exact measurable_const.ite hs measurable_const
    have hF : Measurable F :=
      ((hMeasurable.comp (measurable_snd.prodMk measurable_fst)).mul
        (hHazard.2.1.comp measurable_snd)).mul hrisk
    exact hF.stronglyMeasurable.integral_prod_right'.measurable
  have hmeas : AEStronglyMeasurable (fun x : Sample n =>
      (∫ s in Set.Icc 0 u,
        H s x * hazard s * riskIndicator i s x ∂volume) ^ 2) μ :=
    (hprefix.pow_const 2).aestronglyMeasurable
  apply integrable_of_le_of_le hmeas
    (Filter.Eventually.of_forall (fun x => sq_nonneg _)) ?_
    (integrable_const 0)
    (he_outer.const_mul (∫ s in Set.Icc 0 u, hazard s ∂volume))
  filter_upwards [subject_hazard_path_integrable_ae failureLaw censorLaw hazard
    hHazard H hMeasurable i u hQuadratic, he_path] with x hx hxe
  have henergy : Integrable (fun s =>
      (H s x) ^ 2 * hazard s * riskIndicator i s x) ν := by
    have hm : Measurable (fun s =>
        (H s x) ^ 2 * hazard s * riskIndicator i s x) := by
      have hrisk : Measurable (fun s : ℝ => riskIndicator i s x) := by
        unfold riskIndicator
        have hs : MeasurableSet {s : ℝ |
            0 ≤ s ∧ s ≤ (x i).1 ∧ s ≤ (x i).2} := by
          simpa only [Set.ofPred_and, Set.inter_assoc, id_eq] using
            (((show MeasurableSet {s : ℝ | (0 : ℝ) ≤ s} from
              measurableSet_le measurable_const measurable_id).inter
            (measurableSet_le measurable_id measurable_const)).inter
            (measurableSet_le measurable_id measurable_const))
        exact measurable_const.ite hs measurable_const
      exact (((hMeasurable.comp (measurable_id.prodMk measurable_const)).pow_const 2).mul
        hHazard.2.1).mul hrisk
    apply hxe.mono' hm.aestronglyMeasurable
    filter_upwards [] with s
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (mul_nonneg (sq_nonneg _) (hHazard.2.2.1 s)) (by
        unfold riskIndicator
        split_ifs <;> norm_num))]
    exact mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (f := fun j : Fin n => riskIndicator j s x)
        (fun j hj => by unfold riskIndicator; split_ifs <;> norm_num)
        (Finset.mem_univ i))
      (mul_nonneg (sq_nonneg _) (hHazard.2.2.1 s))
  have hsq := subject_absolute_payoff_square_le_energy hazard hHazard.2.2.1
    H i u x (hHazard.2.2.2.1 u) henergy
  have hmass : 0 ≤ ∫ s in Set.Icc 0 u, hazard s ∂volume :=
    integral_nonneg hHazard.2.2.1
  have henergy_le :
      (∫ s in Set.Icc 0 u,
        (H s x) ^ 2 * hazard s * riskIndicator i s x ∂volume) ≤
      ∫ s, e x s ∂ν := by
    apply integral_mono henergy hxe
    intro s
    exact mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (f := fun j : Fin n => riskIndicator j s x)
        (fun j hj => by unfold riskIndicator; split_ifs <;> norm_num)
        (Finset.mem_univ i))
      (mul_nonneg (sq_nonneg _) (hHazard.2.2.1 s))
  calc
    (∫ s in Set.Icc 0 u,
        H s x * hazard s * riskIndicator i s x ∂volume) ^ 2 ≤
        (∫ s in Set.Icc 0 u,
          |H s x * hazard s * riskIndicator i s x| ∂volume) ^ 2 := by
            have habs := abs_integral_le_integral_abs
              (μ := ν) (f := fun s => H s x * hazard s * riskIndicator i s x)
            have hnonneg : 0 ≤ ∫ s in Set.Icc 0 u,
                |H s x * hazard s * riskIndicator i s x| ∂volume :=
              integral_nonneg (fun s => abs_nonneg _)
            simpa only [sq_abs] using
              (pow_le_pow_left₀ (abs_nonneg _) habs 2)
    _ ≤ _ := hsq.trans (mul_le_mul_of_nonneg_left henergy_le hmass)

/-- Suppose subjects have independent failure and [censor times whose law has the given censor
hazard](hyp:hazard,hHazard), and let the payoff process be [jointly measurable in time and sample](hyp:hMeasurable).
For [a nonnegative horizon u](hyp:hu) and [finite expected quadratic energy](hyp:hQuadratic),
[the expected square of subject i's accumulated hazard-weighted at-risk payoff up to u equals the
expected integral from 0 to u of twice the accumulated payoff times its current rate](goal). -/
theorem subject_hazard_square_expectation {n : ℕ}
    (failureLaw censorLaw : Measure ℝ) (hazard : ℝ → ℝ)
    (hHazard : HasCensorHazard censorLaw hazard)
    (H : ℝ → Sample n → ℝ)
    (hMeasurable : Measurable (fun p : ℝ × Sample n => H p.1 p.2))
    (i : Fin n) (u : ℝ) (hu : 0 ≤ u)
    (hQuadratic : QuadraticEnergyFinite failureLaw censorLaw hazard H u) :
    (∫ x : Sample n,
      (∫ s in Set.Icc 0 u,
        H s x * hazard s * riskIndicator i s x ∂volume) ^ 2
        ∂sampleLaw n failureLaw censorLaw) =
    ∫ x : Sample n,
      (∫ s in Set.Icc 0 u,
        2 * (∫ t in Set.Icc 0 s,
          H t x * hazard t * riskIndicator i t x ∂volume) *
        (H s x * hazard s * riskIndicator i s x) ∂volume)
        ∂sampleLaw n failureLaw censorLaw := by
  /- `subject_hazard_path_integrable_ae` gives an integrable path for almost
     every sample. Apply `cumulative_hazard_square` there and finish with
     `integral_congr_ae`. The mixed time integrand is integrable by
     `subject_prefix_mixed_hazard_integrable_prod`. -/
  apply integral_congr_ae
  filter_upwards [subject_hazard_path_integrable_ae failureLaw censorLaw hazard
    hHazard H hMeasurable i u hQuadratic] with x hPath
  exact cumulative_hazard_square hazard H i u hu x hPath

/-- Suppose subjects are drawn independently with [failure times following a nonnegative time
law](hyp:hFailure) and independent [censor times whose law has the given censor
hazard](hyp:hazard,hHazard), and let the payoff process be [left predictable](hyp:hPredictable) and [jointly
measurable in time and sample](hyp:hMeasurable). For [a nonnegative horizon u](hyp:hu) and
[finite expected quadratic energy](hyp:hQuadratic), [the expected value, at subject i's observed
censor event by u, of the accumulated hazard-weighted at-risk payoff up to the censor time times
the payoff there equals the expected integral from 0 to u of the accumulated payoff times the
payoff times the hazard times the subject's at-risk indicator](goal). -/
theorem subject_prefix_mixed_compensator_expectation {n : ℕ}
    (failureLaw censorLaw : Measure ℝ) (hazard : ℝ → ℝ)
    (hFailure : NonnegativeTimeLaw failureLaw)
    (hHazard : HasCensorHazard censorLaw hazard)
    (H : ℝ → Sample n → ℝ) (hPredictable : LeftPredictable H)
    (hMeasurable : Measurable (fun p : ℝ × Sample n => H p.1 p.2))
    (i : Fin n) (u : ℝ) (hu : 0 ≤ u)
    (hQuadratic : QuadraticEnergyFinite failureLaw censorLaw hazard H u) :
    (∫ x : Sample n,
      (if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then
        (∫ t in Set.Icc 0 (x i).2,
          H t x * hazard t * riskIndicator i t x ∂volume) * H (x i).2 x
      else 0) ∂sampleLaw n failureLaw censorLaw) =
    ∫ x : Sample n,
      (∫ s in Set.Icc 0 u,
        (∫ t in Set.Icc 0 s,
          H t x * hazard t * riskIndicator i t x ∂volume) *
        H s x * hazard s * riskIndicator i s x ∂volume)
        ∂sampleLaw n failureLaw censorLaw := by
  /- Apply `predictable_censor_compensator` to the prefix-product process.
     Predictability, joint measurability, and both integrability claims are
     already proved in `PredictablePrefix` and above in this file. -/
  let P : ℝ → Sample n → ℝ := fun s x =>
    (∫ t in Set.Icc 0 s,
      H t x * hazard t * riskIndicator i t x ∂volume) * H s x
  have hPpred : LeftPredictable P :=
    subject_prefix_mixed_predictable hazard H hPredictable i
  have hPmeas : Measurable (fun p : ℝ × Sample n => P p.1 p.2) :=
    subject_prefix_mixed_jointMeasurable hazard hHazard.2.1 H hMeasurable i
  have hEvent := subject_prefix_mixed_event_integrable
    failureLaw censorLaw hazard hFailure hHazard H hPredictable hMeasurable
    i u hu hQuadratic
  exact predictable_censor_compensator failureLaw censorLaw hazard
    hFailure hHazard P hPpred hPmeas i u hEvent

/-- Suppose subjects are drawn independently with [failure times following a nonnegative time
law](hyp:hFailure) and independent [censor times whose law has the given censor
hazard](hyp:hazard,hHazard), and let the payoff process be [left predictable](hyp:hPredictable) and [jointly
measurable in time and sample](hyp:hMeasurable). For [a nonnegative horizon u](hyp:hu) and
[finite expected quadratic energy](hyp:hQuadratic), [the expected product of the payoff at subject
i's observed censor event by u and the subject's full hazard-weighted at-risk payoff up to u
equals the expected integral from 0 to u of the accumulated payoff times the payoff times the
hazard times the at-risk indicator](goal). -/
theorem subject_event_hazard_product_expectation {n : ℕ}
    (failureLaw censorLaw : Measure ℝ) (hazard : ℝ → ℝ)
    (hFailure : NonnegativeTimeLaw failureLaw)
    (hHazard : HasCensorHazard censorLaw hazard)
    (H : ℝ → Sample n → ℝ) (hPredictable : LeftPredictable H)
    (hMeasurable : Measurable (fun p : ℝ × Sample n => H p.1 p.2))
    (i : Fin n) (u : ℝ) (hu : 0 ≤ u)
    (hQuadratic : QuadraticEnergyFinite failureLaw censorLaw hazard H u) :
    (∫ x : Sample n,
      (if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then H (x i).2 x else 0) *
        (∫ s in Set.Icc 0 u,
          H s x * hazard s * riskIndicator i s x ∂volume)
        ∂sampleLaw n failureLaw censorLaw) =
    ∫ x : Sample n,
      (∫ s in Set.Icc 0 u,
        (∫ t in Set.Icc 0 s,
          H t x * hazard t * riskIndicator i t x ∂volume) *
        H s x * hazard s * riskIndicator i s x ∂volume)
        ∂sampleLaw n failureLaw censorLaw := by
  /- On almost every sample path the censor time is nonnegative and the
     hazard payoff is integrable. On a censor event, the full compensator
     equals its value at the event by `subject_mixed_event_stops`; outside
     the event both products vanish. Then use
     `subject_prefix_mixed_compensator_expectation`. -/
  haveI : IsProbabilityMeasure failureLaw := ⟨hFailure.1⟩
  haveI : IsProbabilityMeasure censorLaw := ⟨hHazard.1.1⟩
  haveI : IsProbabilityMeasure (failureLaw.prod censorLaw) := inferInstance
  have hCensor : ∀ᵐ c ∂censorLaw, 0 ≤ c :=
    (mem_ae_iff_prob_eq_one measurableSet_Ici).2 hHazard.1.2
  have hPair : ∀ᵐ z ∂failureLaw.prod censorLaw, 0 ≤ z.2 := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_le measurable_const measurable_snd)).2
    filter_upwards [] with a
    exact hCensor
  have hCensorSample : ∀ᵐ x ∂sampleLaw n failureLaw censorLaw,
      0 ≤ (x i).2 := by
    unfold sampleLaw
    exact (Measure.tendsto_eval_ae_ae
      (μ := fun _ : Fin n => failureLaw.prod censorLaw) (i := i)) hPair
  calc
    _ = ∫ x : Sample n,
        (if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then
          (∫ t in Set.Icc 0 (x i).2,
            H t x * hazard t * riskIndicator i t x ∂volume) * H (x i).2 x
        else 0) ∂sampleLaw n failureLaw censorLaw := by
          apply integral_congr_ae
          filter_upwards [hCensorSample,
            subject_hazard_path_integrable_ae failureLaw censorLaw hazard
              hHazard H hMeasurable i u hQuadratic] with x hc0 hPath
          by_cases hEvent : (x i).2 ≤ u ∧ (x i).2 < (x i).1
          · simp only [if_pos hEvent]
            rw [mul_comm (H (x i).2 x),
              subject_mixed_event_stops hazard H i x u hEvent.1]
          · simp [hEvent]
    _ = _ := subject_prefix_mixed_compensator_expectation
      failureLaw censorLaw hazard hFailure hHazard H hPredictable hMeasurable
      i u hu hQuadratic

/-- Suppose subjects are drawn independently with [failure times following a nonnegative time
law](hyp:hFailure) and independent [censor times whose law has the given censor
hazard](hyp:hazard,hHazard), and let the payoff process be [left predictable](hyp:hPredictable) and [jointly
measurable in time and sample](hyp:hMeasurable). For [a nonnegative horizon u](hyp:hu) and [finite
expected quadratic energy](hyp:hQuadratic), [the expectation of twice the censor-event payoff times
the subject's compensator up to u, minus the square of that compensator, is zero](goal). -/
theorem subject_jump_compensator_cancellation {n : ℕ}
    (failureLaw censorLaw : Measure ℝ) (hazard : ℝ → ℝ)
    (hFailure : NonnegativeTimeLaw failureLaw)
    (hHazard : HasCensorHazard censorLaw hazard)
    (H : ℝ → Sample n → ℝ) (hPredictable : LeftPredictable H)
    (hMeasurable : Measurable (fun p : ℝ × Sample n => H p.1 p.2))
    (i : Fin n) (u : ℝ) (hu : 0 ≤ u)
    (hQuadratic : QuadraticEnergyFinite failureLaw censorLaw hazard H u) :
    (∫ x : Sample n,
      (2 * (if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then H (x i).2 x else 0) *
          (∫ s in Set.Icc 0 u, H s x * hazard s * riskIndicator i s x ∂volume) -
        (∫ s in Set.Icc 0 u, H s x * hazard s * riskIndicator i s x ∂volume) ^ 2)
        ∂sampleLaw n failureLaw censorLaw) = 0 := by
  /- First obtain integrability of B(u)² from
     `subject_hazard_square_integrable`. The mixed event term is integrable:
     `subject_prefix_mixed_event_integrable` supplies its stopped form, and
     `subject_mixed_event_stops` identifies it with H(C) * B(u) almost surely.
     `subject_hazard_square_expectation` expresses E[B(u)²] as twice the
     expected prefix-hazard product. The same product is E[H(C) * B(u)] by
     `subject_event_hazard_product_expectation`. Now split the integral of
     the difference with `integral_sub` and `integral_const_mul`, using the
     established integrability; finish by arithmetic. -/
  have hSquare := subject_hazard_square_integrable failureLaw censorLaw hazard
    hFailure hHazard H hMeasurable i u hQuadratic
  haveI : IsProbabilityMeasure failureLaw := ⟨hFailure.1⟩
  haveI : IsProbabilityMeasure censorLaw := ⟨hHazard.1.1⟩
  haveI : IsProbabilityMeasure (failureLaw.prod censorLaw) := inferInstance
  have hCensor : ∀ᵐ c ∂censorLaw, 0 ≤ c :=
    (mem_ae_iff_prob_eq_one measurableSet_Ici).2 hHazard.1.2
  have hPair : ∀ᵐ z ∂failureLaw.prod censorLaw, 0 ≤ z.2 := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_le measurable_const measurable_snd)).2
    filter_upwards [] with a
    exact hCensor
  have hCensorSample : ∀ᵐ x ∂sampleLaw n failureLaw censorLaw,
      0 ≤ (x i).2 := by
    unfold sampleLaw
    exact (Measure.tendsto_eval_ae_ae
      (μ := fun _ : Fin n => failureLaw.prod censorLaw) (i := i)) hPair
  have hStopped := subject_prefix_mixed_event_integrable
    failureLaw censorLaw hazard hFailure hHazard H hPredictable hMeasurable
    i u hu hQuadratic
  have hMixedAE :
      (fun x : Sample n =>
        if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then
          (∫ t in Set.Icc 0 (x i).2,
            H t x * hazard t * riskIndicator i t x ∂volume) * H (x i).2 x
        else 0) =ᵐ[sampleLaw n failureLaw censorLaw]
      (fun x : Sample n =>
        (if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then H (x i).2 x else 0) *
          (∫ s in Set.Icc 0 u,
            H s x * hazard s * riskIndicator i s x ∂volume)) := by
    filter_upwards [hCensorSample,
      subject_hazard_path_integrable_ae failureLaw censorLaw hazard
        hHazard H hMeasurable i u hQuadratic] with x hc0 hPath
    by_cases hEvent : (x i).2 ≤ u ∧ (x i).2 < (x i).1
    · simp only [if_pos hEvent]
      rw [mul_comm (H (x i).2 x),
        subject_mixed_event_stops hazard H i x u hEvent.1]
    · simp [hEvent]
  have hMixed := hStopped.congr hMixedAE
  have hSquareExpectation :
      (∫ x : Sample n,
        (∫ s in Set.Icc 0 u,
          H s x * hazard s * riskIndicator i s x ∂volume) ^ 2
          ∂sampleLaw n failureLaw censorLaw) =
      2 * (∫ x : Sample n,
        (if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then H (x i).2 x else 0) *
          (∫ s in Set.Icc 0 u,
            H s x * hazard s * riskIndicator i s x ∂volume)
          ∂sampleLaw n failureLaw censorLaw) := by
    calc
      _ = ∫ x : Sample n,
          (∫ s in Set.Icc 0 u,
            2 * (∫ t in Set.Icc 0 s,
              H t x * hazard t * riskIndicator i t x ∂volume) *
            (H s x * hazard s * riskIndicator i s x) ∂volume)
            ∂sampleLaw n failureLaw censorLaw :=
          subject_hazard_square_expectation failureLaw censorLaw hazard
            hHazard H hMeasurable i u hu hQuadratic
      _ = ∫ x : Sample n,
          2 * (∫ s in Set.Icc 0 u,
            (∫ t in Set.Icc 0 s,
              H t x * hazard t * riskIndicator i t x ∂volume) *
            H s x * hazard s * riskIndicator i s x ∂volume)
            ∂sampleLaw n failureLaw censorLaw := by
          apply integral_congr_ae
          filter_upwards [] with x
          calc
            _ = ∫ s in Set.Icc 0 u,
                2 * ((∫ t in Set.Icc 0 s,
                  H t x * hazard t * riskIndicator i t x ∂volume) *
                  H s x * hazard s * riskIndicator i s x) ∂volume := by
                    congr 1
                    funext s
                    ring
            _ = _ := integral_const_mul 2 _
      _ = 2 * (∫ x : Sample n,
          (∫ s in Set.Icc 0 u,
            (∫ t in Set.Icc 0 s,
              H t x * hazard t * riskIndicator i t x ∂volume) *
            H s x * hazard s * riskIndicator i s x ∂volume)
            ∂sampleLaw n failureLaw censorLaw) := integral_const_mul 2 _
      _ = _ := congrArg (fun z : ℝ => 2 * z)
        (subject_event_hazard_product_expectation failureLaw censorLaw hazard
          hFailure hHazard H hPredictable hMeasurable i u hu hQuadratic).symm
  have hFirst : Integrable (fun x : Sample n =>
      (2 * (if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then H (x i).2 x else 0)) *
        (∫ s in Set.Icc 0 u,
          H s x * hazard s * riskIndicator i s x ∂volume))
      (sampleLaw n failureLaw censorLaw) := by
    apply (hMixed.const_mul 2).congr
    filter_upwards [] with x
    ring
  have hFirstIntegral :
      (∫ x : Sample n,
        (2 * (if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then H (x i).2 x else 0)) *
          (∫ s in Set.Icc 0 u,
            H s x * hazard s * riskIndicator i s x ∂volume)
          ∂sampleLaw n failureLaw censorLaw) =
      2 * (∫ x : Sample n,
        (if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then H (x i).2 x else 0) *
          (∫ s in Set.Icc 0 u,
            H s x * hazard s * riskIndicator i s x ∂volume)
          ∂sampleLaw n failureLaw censorLaw) := by
    calc
      _ = ∫ x : Sample n,
          2 * ((if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then H (x i).2 x else 0) *
            (∫ s in Set.Icc 0 u,
              H s x * hazard s * riskIndicator i s x ∂volume))
            ∂sampleLaw n failureLaw censorLaw := by
              apply integral_congr_ae
              filter_upwards [] with x
              ring
      _ = _ := integral_const_mul 2 _
  rw [integral_sub hFirst hSquare, hFirstIntegral, ← hSquareExpectation, sub_self]

/-- Suppose subjects are drawn independently with [failure times following a nonnegative time
law](hyp:hFailure) and independent [censor times whose law has the given censor
hazard](hyp:hazard,hHazard), and let the integrand be [left predictable](hyp:hPredictable) and [jointly measurable in
time and sample](hyp:hMeasurable). For [a nonnegative horizon u](hyp:hu) and [finite expected
quadratic energy](hyp:hQuadratic), [the expected square of the subject's integral against its
compensated censor count up to u equals the expected integral from 0 to u of the squared
integrand times the hazard times the subject's at-risk indicator](goal). -/
theorem subject_integral_isometry {n : ℕ}
    (failureLaw censorLaw : Measure ℝ) (hazard : ℝ → ℝ)
    (hFailure : NonnegativeTimeLaw failureLaw)
    (hHazard : HasCensorHazard censorLaw hazard)
    (H : ℝ → Sample n → ℝ) (hPredictable : LeftPredictable H)
    (hMeasurable : Measurable (fun p : ℝ × Sample n => H p.1 p.2))
    (i : Fin n) (u : ℝ) (hu : 0 ≤ u)
    (hQuadratic : QuadraticEnergyFinite failureLaw censorLaw hazard H u) :
    (∫ x : Sample n, (subjectIntegral hazard H i u x) ^ 2
      ∂sampleLaw n failureLaw censorLaw) =
    ∫ x : Sample n,
      (∫ s in Set.Icc 0 u,
        (H s x) ^ 2 * hazard s * riskIndicator i s x ∂volume)
        ∂sampleLaw n failureLaw censorLaw := by
  /- Write the subject integral as J - B. `subject_event_square_expectation`
     gives E[J²] = E[energy], while
     `subject_jump_compensator_cancellation` gives E[2 J B - B²] = 0.
     Establish integrability of J² from the event-square bridge and of B²
     from `subject_hazard_square_integrable`; then split the integral of
     (J - B)², using the cancellation identity. -/
  classical
  let μ := sampleLaw n failureLaw censorLaw
  let Q : ℝ → Sample n → ℝ := fun s x => (H s x) ^ 2
  have hQpred : LeftPredictable Q := by
    intro s x y hxy
    simpa [Q] using congrArg (fun z : ℝ => z ^ 2) (hPredictable s x y hxy)
  have hQmeas : Measurable (fun p : ℝ × Sample n => Q p.1 p.2) :=
    hMeasurable.pow_const 2
  have hlin := predictable_censor_compensator_lintegral
    failureLaw censorLaw hazard hFailure hHazard Q hQpred hQmeas
    (fun s x => sq_nonneg _) i u
  have hfinite : (∫⁻ x : Sample n, ∫⁻ s in Set.Icc 0 u,
      ENNReal.ofReal (Q s x * hazard s * riskIndicator i s x)
        ∂volume ∂μ) ≠ ⊤ := by
    have hle : (∫⁻ x : Sample n, ∫⁻ s in Set.Icc 0 u,
        ENNReal.ofReal (Q s x * hazard s * riskIndicator i s x)
          ∂volume ∂μ) ≤
        ∫⁻ x : Sample n, ∫⁻ s in Set.Icc 0 u,
          ENNReal.ofReal ((H s x) ^ 2 * hazard s *
            (∑ j : Fin n, riskIndicator j s x)) ∂volume ∂μ := by
      apply lintegral_mono
      intro x
      apply lintegral_mono
      intro s
      apply ENNReal.ofReal_le_ofReal
      dsimp [Q]
      apply mul_le_mul_of_nonneg_left
      · exact Finset.single_le_sum (f := fun j : Fin n => riskIndicator j s x)
          (fun j hj => by unfold riskIndicator; split_ifs <;> norm_num)
          (Finset.mem_univ i)
      · exact mul_nonneg (sq_nonneg _) (hHazard.2.2.1 s)
    exact ne_top_of_le_ne_top hQuadratic hle
  have hEventQ : Integrable (fun x : Sample n =>
      if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then Q (x i).2 x else 0) μ := by
    have hm : Measurable (fun x : Sample n =>
        if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then Q (x i).2 x else 0) := by
      have hc : Measurable (fun x : Sample n => (x i).2) := by fun_prop
      have hf : Measurable (fun x : Sample n => (x i).1) := by fun_prop
      exact (hQmeas.comp (hc.prodMk measurable_id)).ite
        ((measurableSet_le hc measurable_const).inter (measurableSet_lt hc hf))
        measurable_const
    apply (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable (by
      filter_upwards [] with x
      split_ifs <;> positivity)).1
    rw [hlin]
    exact hfinite
  have hEventSquare : Integrable (fun x : Sample n =>
      (if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then H (x i).2 x else 0) ^ 2) μ := by
    convert hEventQ using 1 <;> simp only [Q, ite_pow, zero_pow (by decide : (2 : ℕ) ≠ 0)]
  have hSquare := subject_hazard_square_integrable failureLaw censorLaw hazard
    hFailure hHazard H hMeasurable i u hQuadratic
  haveI : IsProbabilityMeasure failureLaw := ⟨hFailure.1⟩
  haveI : IsProbabilityMeasure censorLaw := ⟨hHazard.1.1⟩
  haveI : IsProbabilityMeasure (failureLaw.prod censorLaw) := inferInstance
  have hCensor : ∀ᵐ c ∂censorLaw, 0 ≤ c :=
    (mem_ae_iff_prob_eq_one measurableSet_Ici).2 hHazard.1.2
  have hPair : ∀ᵐ z ∂failureLaw.prod censorLaw, 0 ≤ z.2 := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_le measurable_const measurable_snd)).2
    filter_upwards [] with a
    exact hCensor
  have hCensorSample : ∀ᵐ x ∂μ, 0 ≤ (x i).2 := by
    unfold μ sampleLaw
    exact (Measure.tendsto_eval_ae_ae
      (μ := fun _ : Fin n => failureLaw.prod censorLaw) (i := i)) hPair
  have hStopped := subject_prefix_mixed_event_integrable
    failureLaw censorLaw hazard hFailure hHazard H hPredictable hMeasurable
    i u hu hQuadratic
  have hMixedAE :
      (fun x : Sample n =>
        if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then
          (∫ t in Set.Icc 0 (x i).2,
            H t x * hazard t * riskIndicator i t x ∂volume) * H (x i).2 x
        else 0) =ᵐ[μ]
      (fun x : Sample n =>
        (if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then H (x i).2 x else 0) *
          (∫ s in Set.Icc 0 u,
            H s x * hazard s * riskIndicator i s x ∂volume)) := by
    filter_upwards [hCensorSample,
      subject_hazard_path_integrable_ae failureLaw censorLaw hazard
        hHazard H hMeasurable i u hQuadratic] with x hc0 hPath
    by_cases hEvent : (x i).2 ≤ u ∧ (x i).2 < (x i).1
    · simp only [if_pos hEvent]
      rw [mul_comm (H (x i).2 x),
        subject_mixed_event_stops hazard H i x u hEvent.1]
    · simp [hEvent]
  have hMixed := hStopped.congr hMixedAE
  have hCross : Integrable (fun x : Sample n =>
      2 * (if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then H (x i).2 x else 0) *
        (∫ s in Set.Icc 0 u,
          H s x * hazard s * riskIndicator i s x ∂volume)) μ := by
    apply (hMixed.const_mul 2).congr
    filter_upwards [] with x
    ring
  have hCancel := hCross.sub hSquare
  calc
    (∫ x : Sample n, (subjectIntegral hazard H i u x) ^ 2 ∂μ) =
        ∫ x : Sample n,
          (if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then H (x i).2 x else 0) ^ 2 -
          (2 * (if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then H (x i).2 x else 0) *
            (∫ s in Set.Icc 0 u,
              H s x * hazard s * riskIndicator i s x ∂volume) -
            (∫ s in Set.Icc 0 u,
              H s x * hazard s * riskIndicator i s x ∂volume) ^ 2) ∂μ := by
          apply integral_congr_ae
          filter_upwards [] with x
          unfold subjectIntegral
          ring
    _ = (∫ x : Sample n,
          (if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then H (x i).2 x else 0) ^ 2 ∂μ) -
        (∫ x : Sample n,
          2 * (if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then H (x i).2 x else 0) *
            (∫ s in Set.Icc 0 u,
              H s x * hazard s * riskIndicator i s x ∂volume) -
          (∫ s in Set.Icc 0 u,
              H s x * hazard s * riskIndicator i s x ∂volume) ^ 2 ∂μ) :=
          integral_sub hEventSquare hCancel
    _ = _ := by
      rw [subject_jump_compensator_cancellation failureLaw censorLaw hazard
        hFailure hHazard H hPredictable hMeasurable i u hu hQuadratic,
        sub_zero]
      exact subject_event_square_expectation failureLaw censorLaw hazard
        hFailure hHazard H hPredictable hMeasurable i u hQuadratic

end Causalean.Stat.RecurrentEvent.CountingProcess
