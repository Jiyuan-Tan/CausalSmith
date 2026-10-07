module
public import Causalean.Stat.RecurrentEvent.CountingProcess.HazardTonelli

/-!
The hazard-density law of a censor time gives the predictable compensator
identity under an iid sample law. This is the bridge from an ordinary product
probability measure to the compensated counting process.
-/

public section

open MeasureTheory

namespace Causalean.Stat.RecurrentEvent.CountingProcess

/-- Suppose subjects are drawn independently with [failure times following a nonnegative time
law](hyp:hFailure) and independent [censor times whose law has the given censor
hazard](hyp:hazard,hHazard). Let the payoff process be [left predictable](hyp:hPredictable),
[jointly measurable in time and sample](hyp:hMeasurable), and [nonnegative](hyp:hNonnegative),
fix a horizon u, and assume [the payoff at subject i's observed censor event
by u is integrable](hyp:hEvent). Then [the expected payoff at that censor event equals the
expected integral, over times from 0 to u, of the payoff times the hazard times the subject's
at-risk indicator](goal).

Integrability of the compensator side follows from the extended-valued compensator identity, so
both real expectations are well defined. -/
theorem predictable_censor_compensator_nonnegative {n : ℕ}
    (failureLaw censorLaw : Measure ℝ) (hazard : ℝ → ℝ)
    (hFailure : NonnegativeTimeLaw failureLaw)
    (hHazard : HasCensorHazard censorLaw hazard)
    (H : ℝ → Sample n → ℝ) (hPredictable : LeftPredictable H)
    (hMeasurable : Measurable (fun p : ℝ × Sample n => H p.1 p.2))
    (hNonnegative : ∀ s x, 0 ≤ H s x)
    (i : Fin n) (u : ℝ)
    (hEvent : Integrable (fun x : Sample n =>
      if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then H (x i).2 x else 0)
      (sampleLaw n failureLaw censorLaw)) :
    (∫ x : Sample n,
      (if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then H (x i).2 x else 0)
        ∂sampleLaw n failureLaw censorLaw) =
    ∫ x : Sample n,
      (∫ s in Set.Icc 0 u, H s x * hazard s * riskIndicator i s x ∂volume)
        ∂sampleLaw n failureLaw censorLaw := by
  /- Use `predictable_censor_compensator_lintegral`. Since the event payoff
     is integrable, the outer and inner extended hazard integrals are finite;
     convert each to a Bochner integral with
     `integral_eq_lintegral_of_nonneg_ae`. The inner conversion holds for
     almost every sample, which suffices for the outer integral. -/
  classical
  let μ := sampleLaw n failureLaw censorLaw
  let F : Sample n → ℝ := fun x =>
    if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then H (x i).2 x else 0
  let G : Sample n → ℝ := fun x =>
    ∫ s in Set.Icc 0 u, H s x * hazard s * riskIndicator i s x ∂volume
  let g : Sample n → ℝ → ℝ := fun x s =>
    H s x * hazard s * riskIndicator i s x
  have hg_nonneg : ∀ x s, 0 ≤ g x s := by
    intro x s
    dsimp [g]
    exact mul_nonneg (mul_nonneg (hNonnegative s x) (hHazard.2.2.1 s)) (by
      unfold riskIndicator
      split_ifs <;> norm_num)
  have hg_meas : Measurable (fun p : Sample n × ℝ => g p.1 p.2) := by
    dsimp [g]
    have hrisk : Measurable (fun p : Sample n × ℝ => riskIndicator i p.2 p.1) := by
      unfold riskIndicator
      have hfail : Measurable (fun p : Sample n × ℝ => (p.1 i).1) := by fun_prop
      have hcens : Measurable (fun p : Sample n × ℝ => (p.1 i).2) := by fun_prop
      have hevent : MeasurableSet {p : Sample n × ℝ |
          0 ≤ p.2 ∧ p.2 ≤ (p.1 i).1 ∧ p.2 ≤ (p.1 i).2} := by
        simpa only [Set.ofPred_and, Set.inter_assoc] using
          (((show MeasurableSet {p : Sample n × ℝ | (0 : ℝ) ≤ p.2} from
            measurableSet_le measurable_const measurable_snd).inter
          (measurableSet_le measurable_snd hfail)).inter
          (measurableSet_le measurable_snd hcens))
      exact measurable_const.ite hevent measurable_const
    exact ((hMeasurable.comp (measurable_snd.prodMk measurable_fst)).mul
      (hHazard.2.1.comp measurable_snd)).mul hrisk
  have hlin : (∫⁻ x, ENNReal.ofReal (F x) ∂μ) =
      ∫⁻ x, ∫⁻ s in Set.Icc 0 u, ENNReal.ofReal (g x s) ∂volume ∂μ := by
    exact predictable_censor_compensator_lintegral failureLaw censorLaw hazard
      hFailure hHazard H hPredictable hMeasurable hNonnegative i u
  have hF_nonneg : 0 ≤ᵐ[μ] F := Filter.Eventually.of_forall (by
    intro x
    dsimp [F]
    split_ifs <;> simp_all)
  have hfinite : (∫⁻ x, ∫⁻ s in Set.Icc 0 u,
      ENNReal.ofReal (g x s) ∂volume ∂μ) ≠ ⊤ := by
    rw [← hlin]
    rw [← ofReal_integral_eq_lintegral_ofReal hEvent hF_nonneg]
    exact ENNReal.ofReal_ne_top
  have hinner_meas : Measurable (fun x => ∫⁻ s in Set.Icc 0 u,
      ENNReal.ofReal (g x s) ∂volume) := by
    exact (hg_meas.ennreal_ofReal.lintegral_prod_right')
  have hinner_finite : ∀ᵐ x ∂μ, (∫⁻ s in Set.Icc 0 u,
      ENNReal.ofReal (g x s) ∂volume) < ⊤ :=
    ae_lt_top hinner_meas hfinite
  have hinner : ∀ᵐ x ∂μ, G x =
      (∫⁻ s in Set.Icc 0 u, ENNReal.ofReal (g x s) ∂volume).toReal := by
    filter_upwards [hinner_finite] with x hx
    exact integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (fun s => hg_nonneg x s))
      (hg_meas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have houter : ∫ x, G x ∂μ =
      (∫⁻ x, ∫⁻ s in Set.Icc 0 u,
        ENNReal.ofReal (g x s) ∂volume ∂μ).toReal := by
    rw [integral_congr_ae hinner]
    exact integral_toReal hinner_meas.aemeasurable hinner_finite
  have hF : ∫ x, F x ∂μ = (∫⁻ x, ENNReal.ofReal (F x) ∂μ).toReal :=
    integral_eq_lintegral_of_nonneg_ae hF_nonneg hEvent.aestronglyMeasurable
  exact hF.trans (congrArg ENNReal.toReal hlin |>.trans houter.symm)

private theorem nonnegative_compensator_integrable {n : ℕ}
    (failureLaw censorLaw : Measure ℝ) (hazard : ℝ → ℝ)
    (hFailure : NonnegativeTimeLaw failureLaw)
    (hHazard : HasCensorHazard censorLaw hazard)
    (H : ℝ → Sample n → ℝ) (hPredictable : LeftPredictable H)
    (hMeasurable : Measurable (fun p : ℝ × Sample n => H p.1 p.2))
    (hNonnegative : ∀ s x, 0 ≤ H s x)
    (i : Fin n) (u : ℝ)
    (hEvent : Integrable (fun x : Sample n =>
      if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then H (x i).2 x else 0)
      (sampleLaw n failureLaw censorLaw)) :
    Integrable (fun x : Sample n =>
      ∫ s in Set.Icc 0 u, H s x * hazard s * riskIndicator i s x ∂volume)
      (sampleLaw n failureLaw censorLaw) ∧
    ∀ᵐ x ∂sampleLaw n failureLaw censorLaw,
      Integrable (fun s => H s x * hazard s * riskIndicator i s x)
        (volume.restrict (Set.Icc 0 u)) := by
  classical
  let μ := sampleLaw n failureLaw censorLaw
  let g : Sample n → ℝ → ℝ := fun x s =>
    H s x * hazard s * riskIndicator i s x
  have hmeas : Measurable (fun p : Sample n × ℝ => g p.1 p.2) := by
    dsimp [g]
    have hrisk : Measurable (fun p : Sample n × ℝ => riskIndicator i p.2 p.1) := by
      unfold riskIndicator
      have hfail : Measurable (fun p : Sample n × ℝ => (p.1 i).1) := by fun_prop
      have hcens : Measurable (fun p : Sample n × ℝ => (p.1 i).2) := by fun_prop
      have hevent : MeasurableSet {p : Sample n × ℝ |
          0 ≤ p.2 ∧ p.2 ≤ (p.1 i).1 ∧ p.2 ≤ (p.1 i).2} := by
        simpa only [Set.ofPred_and, Set.inter_assoc] using
          (((show MeasurableSet {p : Sample n × ℝ | (0 : ℝ) ≤ p.2} from
            measurableSet_le measurable_const measurable_snd).inter
          (measurableSet_le measurable_snd hfail)).inter
          (measurableSet_le measurable_snd hcens))
      exact measurable_const.ite hevent measurable_const
    exact ((hMeasurable.comp (measurable_snd.prodMk measurable_fst)).mul
      (hHazard.2.1.comp measurable_snd)).mul hrisk
  have hfinite : (∫⁻ x : Sample n, ∫⁻ s in Set.Icc 0 u,
      ENNReal.ofReal (g x s) ∂volume ∂μ) ≠ ⊤ := by
    rw [← predictable_censor_compensator_lintegral failureLaw censorLaw hazard
      hFailure hHazard H hPredictable hMeasurable hNonnegative i u]
    exact (lintegral_ofReal_ne_top_iff_integrable hEvent.1 (by
      filter_upwards [] with x
      split_ifs <;> simp_all)).2 hEvent
  have hinner_meas : Measurable (fun x : Sample n =>
      ∫⁻ s in Set.Icc 0 u, ENNReal.ofReal (g x s) ∂volume) :=
    hmeas.ennreal_ofReal.lintegral_prod_right'
  have hinner_finite : ∀ᵐ x ∂μ,
      (∫⁻ s in Set.Icc 0 u, ENNReal.ofReal (g x s) ∂volume) < ⊤ :=
    ae_lt_top hinner_meas hfinite
  have hinner : ∀ᵐ x ∂μ,
      (∫ s in Set.Icc 0 u, g x s ∂volume) =
      (∫⁻ s in Set.Icc 0 u, ENNReal.ofReal (g x s) ∂volume).toReal := by
    filter_upwards [hinner_finite] with x hx
    exact integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (fun s =>
        mul_nonneg (mul_nonneg (hNonnegative s x) (hHazard.2.2.1 s)) (by
          unfold riskIndicator
          split_ifs <;> norm_num)))
      (hmeas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  constructor
  · apply (integrable_toReal_of_lintegral_ne_top hinner_meas.aemeasurable hfinite).congr
    filter_upwards [hinner] with x hx
    exact hx.symm
  · filter_upwards [hinner_finite] with x hx
    apply (lintegral_ofReal_ne_top_iff_integrable
      (hmeas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun s =>
        mul_nonneg (mul_nonneg (hNonnegative s x) (hHazard.2.2.1 s)) (by
          unfold riskIndicator
          split_ifs <;> norm_num)))).1
    exact hx.ne

/-- Suppose subjects are drawn independently with [failure times following a nonnegative time
law](hyp:hFailure) and independent [censor times whose law has the given censor
hazard](hyp:hazard,hHazard). If the payoff process is [left predictable](hyp:hPredictable) and [jointly
measurable in time and sample](hyp:hMeasurable), and
[the payoff at subject i's observed censor event by u is integrable](hyp:hEvent), then [the
integral over times from 0 to u of the payoff times the hazard times the subject's at-risk
indicator is integrable over samples](goal). -/
theorem predictable_censor_compensator_integrable {n : ℕ}
    (failureLaw censorLaw : Measure ℝ) (hazard : ℝ → ℝ)
    (hFailure : NonnegativeTimeLaw failureLaw)
    (hHazard : HasCensorHazard censorLaw hazard)
    (H : ℝ → Sample n → ℝ) (hPredictable : LeftPredictable H)
    (hMeasurable : Measurable (fun p : ℝ × Sample n => H p.1 p.2))
    (i : Fin n) (u : ℝ)
    (hEvent : Integrable (fun x : Sample n =>
      if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then H (x i).2 x else 0)
      (sampleLaw n failureLaw censorLaw)) :
    Integrable (fun x : Sample n =>
      ∫ s in Set.Icc 0 u, H s x * hazard s * riskIndicator i s x ∂volume)
      (sampleLaw n failureLaw censorLaw) := by
  /- Split H into its positive and negative parts. The nonnegative extended
     compensator identity gives integrability of both time integrals and
     almost-everywhere integrability of their time integrands. Subtract the
     two time integrals on that full-measure set. -/
  classical
  let μ := sampleLaw n failureLaw censorLaw
  let Hpos : ℝ → Sample n → ℝ := fun s x => max (H s x) 0
  let Hneg : ℝ → Sample n → ℝ := fun s x => max (-H s x) 0
  have hp_pred : LeftPredictable Hpos := by
    intro s x y hxy
    simp only [Hpos, hPredictable s x y hxy]
  have hn_pred : LeftPredictable Hneg := by
    intro s x y hxy
    simp only [Hneg, hPredictable s x y hxy]
  have hp_meas : Measurable (fun p : ℝ × Sample n => Hpos p.1 p.2) :=
    hMeasurable.max measurable_const
  have hn_meas : Measurable (fun p : ℝ × Sample n => Hneg p.1 p.2) :=
    hMeasurable.neg.max measurable_const
  have hp_event : Integrable (fun x : Sample n =>
      if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then Hpos (x i).2 x else 0) μ := by
    convert hEvent.sup (integrable_zero (Sample n) ℝ μ) using 1
    funext x
    by_cases hx : (x i).2 ≤ u ∧ (x i).2 < (x i).1 <;> simp [Hpos, hx]
  have hn_event : Integrable (fun x : Sample n =>
      if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then Hneg (x i).2 x else 0) μ := by
    convert hEvent.neg.sup (integrable_zero (Sample n) ℝ μ) using 1
    funext x
    by_cases hx : (x i).2 ≤ u ∧ (x i).2 < (x i).1 <;> simp [Hneg, hx]
  have hp_comp := nonnegative_compensator_integrable failureLaw censorLaw hazard
    hFailure hHazard Hpos hp_pred hp_meas (fun _ _ => le_max_right _ _) i u hp_event
  have hn_comp := nonnegative_compensator_integrable failureLaw censorLaw hazard
    hFailure hHazard Hneg hn_pred hn_meas (fun _ _ => le_max_right _ _) i u hn_event
  have hcomp_sub : ∀ᵐ x ∂μ,
      (∫ s in Set.Icc 0 u, Hpos s x * hazard s * riskIndicator i s x ∂volume) -
      (∫ s in Set.Icc 0 u, Hneg s x * hazard s * riskIndicator i s x ∂volume) =
      ∫ s in Set.Icc 0 u, H s x * hazard s * riskIndicator i s x ∂volume := by
    filter_upwards [hp_comp.2, hn_comp.2] with x hpi hni
    rw [← integral_sub hpi hni]
    congr 1
    funext s
    dsimp [Hpos, Hneg]
    rw [← sub_mul, ← sub_mul, max_zero_sub_max_neg_zero_eq_self]
  exact (hp_comp.1.sub hn_comp.1).congr hcomp_sub

/-- Suppose subjects are drawn independently with [failure times following a nonnegative time
law](hyp:hFailure) and independent [censor times whose law has the given censor
hazard](hyp:hazard,hHazard). If the payoff process is [left predictable](hyp:hPredictable) and [jointly
measurable in time and sample](hyp:hMeasurable), and
[the payoff at subject i's observed censor event by u is integrable](hyp:hEvent), then [the expected censor-event payoff
equals the expected at-risk hazard integral](goal). -/
theorem predictable_censor_compensator {n : ℕ}
    (failureLaw censorLaw : Measure ℝ) (hazard : ℝ → ℝ)
    (hFailure : NonnegativeTimeLaw failureLaw)
    (hHazard : HasCensorHazard censorLaw hazard)
    (H : ℝ → Sample n → ℝ) (hPredictable : LeftPredictable H)
    (hMeasurable : Measurable (fun p : ℝ × Sample n => H p.1 p.2))
    (i : Fin n) (u : ℝ)
    (hEvent : Integrable (fun x : Sample n =>
      if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then H (x i).2 x else 0)
      (sampleLaw n failureLaw censorLaw)) :
    (∫ x : Sample n,
      (if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then H (x i).2 x else 0)
        ∂sampleLaw n failureLaw censorLaw) =
    ∫ x : Sample n,
      (∫ s in Set.Icc 0 u, H s x * hazard s * riskIndicator i s x ∂volume)
        ∂sampleLaw n failureLaw censorLaw := by
  /- Apply the nonnegative identity to the positive and negative parts.
     Its extended-integral proof also supplies integrability of their
     compensators and the almost-everywhere inner-integrability needed
     to subtract the time integrals. -/
  classical
  let μ := sampleLaw n failureLaw censorLaw
  let Hpos : ℝ → Sample n → ℝ := fun s x => max (H s x) 0
  let Hneg : ℝ → Sample n → ℝ := fun s x => max (-H s x) 0
  have hp_pred : LeftPredictable Hpos := by
    intro s x y hxy
    simp only [Hpos, hPredictable s x y hxy]
  have hn_pred : LeftPredictable Hneg := by
    intro s x y hxy
    simp only [Hneg, hPredictable s x y hxy]
  have hp_meas : Measurable (fun p : ℝ × Sample n => Hpos p.1 p.2) :=
    hMeasurable.max measurable_const
  have hn_meas : Measurable (fun p : ℝ × Sample n => Hneg p.1 p.2) :=
    hMeasurable.neg.max measurable_const
  have hp_nonneg : ∀ s x, 0 ≤ Hpos s x := fun s x => le_max_right _ _
  have hn_nonneg : ∀ s x, 0 ≤ Hneg s x := fun s x => le_max_right _ _
  have hp_event : Integrable (fun x : Sample n =>
      if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then Hpos (x i).2 x else 0) μ := by
    convert hEvent.sup (integrable_zero (Sample n) ℝ μ) using 1
    funext x
    by_cases hx : (x i).2 ≤ u ∧ (x i).2 < (x i).1 <;> simp [Hpos, hx]
  have hn_event : Integrable (fun x : Sample n =>
      if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then Hneg (x i).2 x else 0) μ := by
    convert hEvent.neg.sup (integrable_zero (Sample n) ℝ μ) using 1
    funext x
    by_cases hx : (x i).2 ≤ u ∧ (x i).2 < (x i).1 <;> simp [Hneg, hx]
  have hp_comp := nonnegative_compensator_integrable failureLaw censorLaw hazard
    hFailure hHazard Hpos hp_pred hp_meas hp_nonneg i u hp_event
  have hn_comp := nonnegative_compensator_integrable failureLaw censorLaw hazard
    hFailure hHazard Hneg hn_pred hn_meas hn_nonneg i u hn_event
  have hp_eq := predictable_censor_compensator_nonnegative failureLaw censorLaw
    hazard hFailure hHazard Hpos hp_pred hp_meas hp_nonneg i u hp_event
  have hn_eq := predictable_censor_compensator_nonnegative failureLaw censorLaw
    hazard hFailure hHazard Hneg hn_pred hn_meas hn_nonneg i u hn_event
  have hevent_sub : (fun x : Sample n =>
      (if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then Hpos (x i).2 x else 0) -
      (if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then Hneg (x i).2 x else 0)) =
      (fun x => if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then H (x i).2 x else 0) := by
    funext x
    by_cases hx : (x i).2 ≤ u ∧ (x i).2 < (x i).1
    · simp [hx, Hpos, Hneg, max_zero_sub_max_neg_zero_eq_self]
    · simp [hx]
  have hcomp_sub : ∀ᵐ x ∂μ,
      (∫ s in Set.Icc 0 u, Hpos s x * hazard s * riskIndicator i s x ∂volume) -
      (∫ s in Set.Icc 0 u, Hneg s x * hazard s * riskIndicator i s x ∂volume) =
      ∫ s in Set.Icc 0 u, H s x * hazard s * riskIndicator i s x ∂volume := by
    filter_upwards [hp_comp.2, hn_comp.2] with x hpi hni
    rw [← integral_sub hpi hni]
    congr 1
    funext s
    dsimp [Hpos, Hneg]
    rw [← sub_mul, ← sub_mul, max_zero_sub_max_neg_zero_eq_self]
  calc
    (∫ x : Sample n,
      (if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then H (x i).2 x else 0) ∂μ)
        = ∫ x : Sample n,
          ((if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then Hpos (x i).2 x else 0) -
           (if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then Hneg (x i).2 x else 0)) ∂μ := by
          rw [hevent_sub]
    _ = (∫ x : Sample n,
          (if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then Hpos (x i).2 x else 0) ∂μ) -
        (∫ x : Sample n,
          (if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then Hneg (x i).2 x else 0) ∂μ) :=
          integral_sub hp_event hn_event
    _ = (∫ x : Sample n,
          (∫ s in Set.Icc 0 u, Hpos s x * hazard s * riskIndicator i s x ∂volume) ∂μ) -
        (∫ x : Sample n,
          (∫ s in Set.Icc 0 u, Hneg s x * hazard s * riskIndicator i s x ∂volume) ∂μ) := by
          rw [hp_eq, hn_eq]
    _ = ∫ x : Sample n,
          ((∫ s in Set.Icc 0 u, Hpos s x * hazard s * riskIndicator i s x ∂volume) -
           (∫ s in Set.Icc 0 u, Hneg s x * hazard s * riskIndicator i s x ∂volume)) ∂μ :=
          (integral_sub hp_comp.1 hn_comp.1).symm
    _ = ∫ x : Sample n,
          (∫ s in Set.Icc 0 u, H s x * hazard s * riskIndicator i s x ∂volume) ∂μ :=
          integral_congr_ae hcomp_sub

/-- Under independent sampling with [failure times following a nonnegative time
law](hyp:hFailure) and independent [censor times whose law has the given censor
hazard](hyp:hazard,hHazard), each subject's compensated censor count at a horizon u [has mean zero](goal). -/
theorem compensatedCensor_mean_zero {n : ℕ}
    (failureLaw censorLaw : Measure ℝ) (hazard : ℝ → ℝ)
    (hFailure : NonnegativeTimeLaw failureLaw)
    (hHazard : HasCensorHazard censorLaw hazard)
    (i : Fin n) (u : ℝ) :
    (∫ x : Sample n, compensatedCensor hazard i u x
      ∂sampleLaw n failureLaw censorLaw) = 0 := by
  /- Specialize the nonnegative compensator identity to the constant
     predictable process 1. The event payoff is bounded by 1. -/
  classical
  haveI : IsProbabilityMeasure failureLaw := ⟨hFailure.1⟩
  haveI : IsProbabilityMeasure censorLaw := ⟨hHazard.1.1⟩
  let μ := sampleLaw n failureLaw censorLaw
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ, sampleLaw]
    infer_instance
  have hevent_meas : Measurable (fun x : Sample n =>
      if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then (1 : ℝ) else 0) := by
    have hpair : Measurable (fun x : Sample n => x i) := measurable_pi_apply i
    have hset : MeasurableSet {x : Sample n |
        (x i).2 ≤ u ∧ (x i).2 < (x i).1} := by
      exact (measurableSet_le hpair.snd measurable_const).inter
        (measurableSet_lt hpair.snd hpair.fst)
    exact measurable_const.ite hset measurable_const
  have hevent : Integrable (fun x : Sample n =>
      if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then (1 : ℝ) else 0) μ := by
    apply Integrable.of_mem_Icc 0 1 hevent_meas.aemeasurable
    filter_upwards [] with x
    split_ifs <;> simp
  have hpred : LeftPredictable (fun (_ : ℝ) (_ : Sample n) => (1 : ℝ)) := by
    intro s x y hxy
    rfl
  have hcomp := (nonnegative_compensator_integrable failureLaw censorLaw hazard
    hFailure hHazard (fun (_ : ℝ) (_ : Sample n) => (1 : ℝ)) hpred measurable_const
    (fun _ _ => by norm_num) i u hevent).1
  have heq := predictable_censor_compensator_nonnegative failureLaw censorLaw
    hazard hFailure hHazard (fun (_ : ℝ) (_ : Sample n) => (1 : ℝ)) hpred measurable_const
    (fun _ _ => by norm_num) i u hevent
  simp only [one_mul] at hcomp heq
  change (∫ x : Sample n,
      ((if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then (1 : ℝ) else 0) -
        ∫ s in Set.Icc 0 u, hazard s * riskIndicator i s x ∂volume) ∂μ) = 0
  rw [integral_sub hevent hcomp, heq, sub_self]

end Causalean.Stat.RecurrentEvent.CountingProcess
