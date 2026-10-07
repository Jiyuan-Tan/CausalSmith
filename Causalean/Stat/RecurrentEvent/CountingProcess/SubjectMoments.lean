module
public import Causalean.Stat.RecurrentEvent.CountingProcess.SubjectMomentsBasic

/-!
# Mixed predictable-moment bounds

This module derives the mixed event and compensator integrability estimates
needed to turn finite predictable quadratic energy into compensated-count
second-moment identities.
-/

public section

open MeasureTheory

namespace Causalean.Stat.RecurrentEvent.CountingProcess

/-- Suppose subjects are drawn independently with [failure times following a nonnegative time
law](hyp:hFailure) and independent [censor times whose law has the given censor
hazard](hyp:hazard,hHazard), and let the payoff process be [jointly measurable in time and sample](hyp:hMeasurable).
For [a nonnegative horizon u](hyp:hu) and [finite expected quadratic energy](hyp:hQuadratic),
[subject i's accumulated hazard-weighted at-risk payoff up to time s times its current
hazard-weighted at-risk payoff at s is integrable jointly over samples and times s from 0 to
u](goal). -/
theorem subject_prefix_mixed_hazard_integrable_prod {n : ℕ}
    (failureLaw censorLaw : Measure ℝ) (hazard : ℝ → ℝ)
    (hFailure : NonnegativeTimeLaw failureLaw)
    (hHazard : HasCensorHazard censorLaw hazard)
    (H : ℝ → Sample n → ℝ)
    (hMeasurable : Measurable (fun p : ℝ × Sample n => H p.1 p.2))
    (i : Fin n) (u : ℝ) (hu : 0 ≤ u)
    (hQuadratic : QuadraticEnergyFinite failureLaw censorLaw hazard H u) :
    Integrable (fun p : Sample n × ℝ =>
      (∫ t in Set.Icc 0 p.2,
        H t p.1 * hazard t * riskIndicator i t p.1 ∂volume) *
        H p.2 p.1 * hazard p.2 * riskIndicator i p.2 p.1)
      ((sampleLaw n failureLaw censorLaw).prod
        (volume.restrict (Set.Icc 0 u))) := by
  /- Apply `integrable_prod_iff` to the jointly measurable mixed payoff.
     Almost-everywhere section integrability follows from hazard-path
     integrability and continuity of its indefinite integral. The previous
     pathwise bound controls the integral of the absolute section by total
     hazard mass times subject energy; Tonelli and finite expected quadratic
     energy make that bound integrable over the sample law. -/
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
  let f : Sample n × ℝ → ℝ := fun p =>
    (∫ t in Set.Icc 0 p.2,
      H t p.1 * hazard t * riskIndicator i t p.1 ∂volume) *
      H p.2 p.1 * hazard p.2 * riskIndicator i p.2 p.1
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
    apply mul_nonneg (mul_nonneg (sq_nonneg _) (hHazard.2.2.1 s))
    exact Finset.sum_nonneg (fun j _ => by unfold riskIndicator; split_ifs <;> norm_num)
  have he_joint : Integrable (fun p : Sample n × ℝ => e p.1 p.2) (μ.prod ν) := by
    apply (lintegral_ofReal_ne_top_iff_integrable he_meas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => he_nonneg p.1 p.2))).1
    rw [lintegral_prod _ he_meas.ennreal_ofReal.aemeasurable]
    exact hQuadratic
  have he_outer : Integrable (fun x => ∫ s, e x s ∂ν) μ :=
    he_joint.integral_prod_left
  have he_path : ∀ᵐ x ∂μ, Integrable (e x) ν :=
    he_joint.prod_right_ae
  have hf_meas : Measurable f := by
    dsimp [f]
    have hm := subject_prefix_mixed_jointMeasurable hazard hHazard.2.1 H hMeasurable i
    have hm' : Measurable (fun p : Sample n × ℝ =>
        (∫ t in Set.Icc 0 p.2,
          H t p.1 * hazard t * riskIndicator i t p.1 ∂volume) * H p.2 p.1) :=
      hm.comp (measurable_snd.prodMk measurable_fst)
    exact (hm'.mul (hHazard.2.1.comp measurable_snd)).mul
      (by
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
        exact measurable_const.ite hs measurable_const)
  have hsection : ∀ᵐ x ∂μ, Integrable (fun s => f (x, s)) ν := by
    filter_upwards [subject_hazard_path_integrable_ae failureLaw censorLaw hazard
      hHazard H hMeasurable i u hQuadratic] with x hx
    have hinterval : IntervalIntegrable
        (fun s => H s x * hazard s * riskIndicator i s x) volume 0 u :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hu).2 hx
    let F : ℝ → ℝ := fun s =>
      ∫ t in (0 : ℝ)..s, H t x * hazard t * riskIndicator i t x
    have hF : ContinuousOn F (Set.Icc 0 u) := by
      simpa [F, Set.uIcc_of_le hu] using
        (hinterval.absolutelyContinuousOnInterval_intervalIntegral (by simp)).continuousOn
    have hprod : Integrable
        (fun s => F s * (H s x * hazard s * riskIndicator i s x)) ν :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hu).1
        (hinterval.continuousOn_mul (by simpa [Set.uIcc_of_le hu] using hF))
    apply hprod.congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    dsimp [f, F]
    rw [intervalIntegral.integral_of_le hs.1, ← integral_Icc_eq_integral_Ioc]
    ring
  have henergy_subject : ∀ᵐ x ∂μ,
      Integrable (fun s => (H s x) ^ 2 * hazard s * riskIndicator i s x) ν := by
    filter_upwards [he_path] with x hx
    have hm : Measurable (fun s => (H s x) ^ 2 * hazard s * riskIndicator i s x) := by
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
    apply hx.mono' hm.aestronglyMeasurable
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
  have houter : Integrable (fun x => ∫ s, ‖f (x, s)‖ ∂ν) μ := by
    have hm : AEStronglyMeasurable (fun x => ∫ s, ‖f (x, s)‖ ∂ν) μ :=
      hf_meas.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    apply integrable_of_le_of_le hm
      (Filter.Eventually.of_forall (fun x => integral_nonneg (fun s => norm_nonneg _)))
      ?_ (integrable_const 0)
      (he_outer.const_mul (∫ s in Set.Icc 0 u, hazard s ∂volume))
    filter_upwards [subject_hazard_path_integrable_ae failureLaw censorLaw hazard
      hHazard H hMeasurable i u hQuadratic,
      henergy_subject, he_path] with x hx hxe hxt
    have hbound := subject_prefix_mixed_abs_integral_le_energy
      hazard hHazard.2.2.1 H i u hu x (hHazard.2.2.2.1 u) hx hxe
    have henergy_le :
        (∫ s in Set.Icc 0 u,
          (H s x) ^ 2 * hazard s * riskIndicator i s x ∂volume) ≤
        ∫ s, e x s ∂ν := by
      apply integral_mono hxe hxt
      intro s
      exact mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (f := fun j : Fin n => riskIndicator j s x)
          (fun j hj => by unfold riskIndicator; split_ifs <;> norm_num)
          (Finset.mem_univ i))
        (mul_nonneg (sq_nonneg _) (hHazard.2.2.1 s))
    have hmass : 0 ≤ ∫ s in Set.Icc 0 u, hazard s ∂volume :=
      integral_nonneg hHazard.2.2.1
    calc
      (∫ s, ‖f (x, s)‖ ∂ν) =
          ∫ s in Set.Icc 0 u,
            |(∫ t in Set.Icc 0 s,
              H t x * hazard t * riskIndicator i t x ∂volume) *
              (H s x * hazard s * riskIndicator i s x)| ∂volume := by
            congr 1
            funext s
            simp only [f, Real.norm_eq_abs]
            congr 1
            ring
      _ ≤ _ := hbound.trans (mul_le_mul_of_nonneg_left henergy_le hmass)
  exact (integrable_prod_iff hf_meas.aestronglyMeasurable).2 ⟨hsection, houter⟩

/-- Suppose subjects are drawn independently with [failure times following a nonnegative time
law](hyp:hFailure) and independent [censor times whose law has the given censor
hazard](hyp:hazard,hHazard), and let the payoff process be [left predictable](hyp:hPredictable) and [jointly
measurable in time and sample](hyp:hMeasurable). For [a nonnegative horizon u](hyp:hu) and
[finite expected quadratic energy](hyp:hQuadratic), [the product, at subject i's observed censor
event by u, of the accumulated hazard-weighted at-risk payoff up to the censor time and the
payoff there, taken as zero when no such event occurs, is integrable over samples](goal). -/
theorem subject_prefix_mixed_event_integrable {n : ℕ}
    (failureLaw censorLaw : Measure ℝ) (hazard : ℝ → ℝ)
    (hFailure : NonnegativeTimeLaw failureLaw)
    (hHazard : HasCensorHazard censorLaw hazard)
    (H : ℝ → Sample n → ℝ) (hPredictable : LeftPredictable H)
    (hMeasurable : Measurable (fun p : ℝ × Sample n => H p.1 p.2))
    (i : Fin n) (u : ℝ) (hu : 0 ≤ u)
    (hQuadratic : QuadraticEnergyFinite failureLaw censorLaw hazard H u) :
    Integrable (fun x : Sample n =>
      if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then
        (∫ t in Set.Icc 0 (x i).2,
          H t x * hazard t * riskIndicator i t x ∂volume) * H (x i).2 x
      else 0) (sampleLaw n failureLaw censorLaw) := by
  /- Set Q(s,x) = |B_i(s,x) * H(s,x)|, where B_i is the prefix hazard integral.
     `subject_prefix_mixed_predictable` and
     `subject_prefix_mixed_jointMeasurable` give the hypotheses for
     `predictable_censor_compensator_lintegral`. The compensator's nonnegative
     joint lintegral is finite because
     `subject_prefix_mixed_hazard_integrable_prod` gives L¹ integrability of
     the signed product and the risk indicator is nonnegative. Convert the
     finite event lintegral to `Integrable` using
     `lintegral_ofReal_ne_top_iff_integrable`. Event measurability follows by
     composing the joint-measurability result with x ↦ (censorTime_i x,x),
     then restricting to the measurable event predicate. -/
  classical
  let μ := sampleLaw n failureLaw censorLaw
  let ν := (volume : Measure ℝ).restrict (Set.Icc 0 u)
  let P : ℝ → Sample n → ℝ := fun s x =>
    (∫ t in Set.Icc 0 s,
      H t x * hazard t * riskIndicator i t x ∂volume) * H s x
  let Q : ℝ → Sample n → ℝ := fun s x => |P s x|
  have hPpred : LeftPredictable P :=
    subject_prefix_mixed_predictable hazard H hPredictable i
  have hPmeas : Measurable (fun p : ℝ × Sample n => P p.1 p.2) :=
    subject_prefix_mixed_jointMeasurable hazard hHazard.2.1 H hMeasurable i
  have hQpred : LeftPredictable Q := by
    intro s x y hxy
    exact congrArg abs (hPpred s x y hxy)
  have hQmeas : Measurable (fun p : ℝ × Sample n => Q p.1 p.2) :=
    by simpa only [Real.norm_eq_abs] using hPmeas.norm
  have hQnonneg : ∀ s x, 0 ≤ Q s x := fun s x => abs_nonneg _
  have hlin := predictable_censor_compensator_lintegral
    failureLaw censorLaw hazard hFailure hHazard Q hQpred hQmeas hQnonneg i u
  have hJoint := subject_prefix_mixed_hazard_integrable_prod
    failureLaw censorLaw hazard hFailure hHazard H hMeasurable i u hu hQuadratic
  have hfinite : (∫⁻ x : Sample n, ∫⁻ s in Set.Icc 0 u,
      ENNReal.ofReal (Q s x * hazard s * riskIndicator i s x)
        ∂volume ∂μ) ≠ ⊤ := by
    have hmeas : Measurable (fun p : Sample n × ℝ =>
        Q p.2 p.1 * hazard p.2 * riskIndicator i p.2 p.1) := by
      have hrisk : Measurable (fun p : Sample n × ℝ => riskIndicator i p.2 p.1) := by
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
      exact ((hQmeas.comp (measurable_snd.prodMk measurable_fst)).mul
        (hHazard.2.1.comp measurable_snd)).mul hrisk
    rw [← lintegral_prod _ hmeas.ennreal_ofReal.aemeasurable]
    have hnorm : Integrable (fun p : Sample n × ℝ =>
        ‖(∫ t in Set.Icc 0 p.2,
          H t p.1 * hazard t * riskIndicator i t p.1 ∂volume) *
          H p.2 p.1 * hazard p.2 * riskIndicator i p.2 p.1‖) (μ.prod ν) :=
      hJoint.norm
    have heq : (fun p : Sample n × ℝ =>
        Q p.2 p.1 * hazard p.2 * riskIndicator i p.2 p.1) =
        (fun p : Sample n × ℝ =>
          ‖(∫ t in Set.Icc 0 p.2,
            H t p.1 * hazard t * riskIndicator i t p.1 ∂volume) *
            H p.2 p.1 * hazard p.2 * riskIndicator i p.2 p.1‖) := by
      funext p
      have hh : 0 ≤ hazard p.2 := hHazard.2.2.1 p.2
      have hr : 0 ≤ riskIndicator i p.2 p.1 := by
        unfold riskIndicator
        split_ifs <;> norm_num
      simp only [Q, P, Real.norm_eq_abs, abs_mul, abs_of_nonneg hh,
        abs_of_nonneg hr]
    simp_rw [congrFun heq]
    exact (lintegral_ofReal_ne_top_iff_integrable hnorm.1
      (Filter.Eventually.of_forall (fun p => norm_nonneg _))).2 hnorm
  have hm : Measurable (fun x : Sample n =>
      if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then P (x i).2 x else 0) := by
    have hc : Measurable (fun x : Sample n => (x i).2) := by fun_prop
    have hf : Measurable (fun x : Sample n => (x i).1) := by fun_prop
    exact (hPmeas.comp (hc.prodMk measurable_id)).ite
      ((measurableSet_le hc measurable_const).inter (measurableSet_lt hc hf))
      measurable_const
  have hnorm : Integrable (fun x : Sample n =>
      |if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then P (x i).2 x else 0|) μ := by
    apply (lintegral_ofReal_ne_top_iff_integrable
      (show Measurable (fun x : Sample n =>
        |if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then P (x i).2 x else 0|) by
          simpa only [Real.norm_eq_abs] using hm.norm).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => abs_nonneg _))).1
    simp only [abs_ite, abs_zero]
    rw [hlin]
    exact hfinite
  exact (integrable_norm_iff hm.aestronglyMeasurable).1 (by
    simpa only [Real.norm_eq_abs] using hnorm)

/-- If [a subject's censor time occurs by the horizon u](hyp:hcu), then for [a censor hazard](hyp:hazard)
[the accumulated payoff up to u times the payoff at the censor time equals the accumulated payoff
up to the censor time times the same payoff](goal). -/
theorem subject_mixed_event_stops {n : ℕ}
    (hazard : ℝ → ℝ) (H : ℝ → Sample n → ℝ)
    (i : Fin n) (x : Sample n) (u : ℝ)
    (hcu : (x i).2 ≤ u) :
    (∫ s in Set.Icc 0 u,
      H s x * hazard s * riskIndicator i s x ∂volume) * H (x i).2 x =
    (∫ s in Set.Icc 0 (x i).2,
      H s x * hazard s * riskIndicator i s x ∂volume) * H (x i).2 x := by
  exact congrArg (fun z : ℝ => z * H (x i).2 x)
    (subject_hazard_stops_at_censor hazard H i x u hcu)

end Causalean.Stat.RecurrentEvent.CountingProcess
