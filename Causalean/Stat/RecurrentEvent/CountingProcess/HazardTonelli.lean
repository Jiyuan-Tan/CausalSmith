module
public import Causalean.Stat.RecurrentEvent.CountingProcess.HazardDensity
public import Causalean.Stat.RecurrentEvent.CountingProcess.History
public import Causalean.Stat.RecurrentEvent.CountingProcess.ProductResampling

/-!
The nonnegative predictable censor-compensator identity. Its extended
integrals separate the product-law disintegration and Tonelli argument
from the signed integrability bookkeeping in `HazardBridge`.
-/

public section

open MeasureTheory

namespace Causalean.Stat.RecurrentEvent.CountingProcess

/-- Suppose subjects are drawn independently with [failure times following a nonnegative time
law](hyp:hFailure) and independent [censor times whose law has the given censor
hazard](hyp:hazard,hHazard), and let the payoff process be [jointly measurable in time and
sample](hyp:hMeasurable) and [nonnegative](hyp:hNonnegative). For a horizon
u, [the expected payoff at subject i's observed censor event by u equals the expected
Lebesgue integral, over times s from 0 to u strictly before the subject's failure time, of the
payoff at s evaluated with that subject's censor time reset to s, times the hazard at s, times
the probability of censoring at or after s](goal).

Both sides are extended nonnegative integrals and may be infinite. -/
theorem predictable_censor_event_hazard_lintegral {n : ℕ}
    (failureLaw censorLaw : Measure ℝ) (hazard : ℝ → ℝ)
    (hFailure : NonnegativeTimeLaw failureLaw)
    (hHazard : HasCensorHazard censorLaw hazard)
    (H : ℝ → Sample n → ℝ)
    (hMeasurable : Measurable (fun p : ℝ × Sample n => H p.1 p.2))
    (hNonnegative : ∀ s x, 0 ≤ H s x)
    (i : Fin n) (u : ℝ) :
    (∫⁻ x : Sample n,
      ENNReal.ofReal (if (x i).2 ≤ u ∧ (x i).2 < (x i).1
        then H (x i).2 x else 0)
        ∂sampleLaw n failureLaw censorLaw) =
    ∫⁻ x : Sample n, ∫⁻ s in Set.Icc 0 u,
      ENNReal.ofReal (if s < (x i).1 then
        H s (Function.update x i ((x i).1, s)) * hazard s *
          (censorLaw (Set.Ici s)).toReal else 0) ∂volume
      ∂sampleLaw n failureLaw censorLaw := by
  /- Use `lintegral_censor_event_resample`. For each fixed sample, apply
     `censor_event_hazard_lintegral` to
     `g s = H s (Function.update x i ((x i).1, s))`. Joint measurability
     gives measurability of `g`; nonnegativity is inherited from `H`. -/
  classical
  rw [lintegral_censor_event_resample failureLaw censorLaw hFailure hHazard.1
    H hMeasurable i u]
  apply lintegral_congr
  intro x
  let g : ℝ → ℝ := fun s => H s (Function.update x i ((x i).1, s))
  have hg : Measurable g := by
    have hp : Measurable (fun s : ℝ =>
        (s, Function.update x i ((x i).1, s))) := by fun_prop
    simpa only [g, Function.comp_def] using hMeasurable.comp hp
  have hgn : ∀ s, 0 ≤ g s := fun s => hNonnegative s _
  exact censor_event_hazard_lintegral censorLaw hazard g hHazard hg
    (x i).1 u

/-- Suppose subjects are drawn independently with [failure times following a nonnegative time
law](hyp:hFailure) and independent [censor times whose law has the given censor
hazard](hyp:hazard,hHazard), and let the payoff process be [left predictable](hyp:hPredictable),
[jointly measurable in time and sample](hyp:hMeasurable), and [nonnegative](hyp:hNonnegative).
At [a fixed nonnegative time s](hyp:hs), [the expected value of the payoff times the hazard times
subject i's at-risk indicator equals the expected value, over samples whose subject-i failure
time is at least s, of the payoff evaluated with that subject's censor time reset to s, times the
hazard at s, times the probability of censoring at or after s](goal).

The failure-time boundary remains inclusive in this fixed-time identity. -/
theorem predictable_censor_atRisk_fixed_time_resample {n : ℕ}
    (failureLaw censorLaw : Measure ℝ) (hazard : ℝ → ℝ)
    (hFailure : NonnegativeTimeLaw failureLaw)
    (hHazard : HasCensorHazard censorLaw hazard)
    (H : ℝ → Sample n → ℝ) (hPredictable : LeftPredictable H)
    (hMeasurable : Measurable (fun p : ℝ × Sample n => H p.1 p.2))
    (hNonnegative : ∀ s x, 0 ≤ H s x)
    (i : Fin n) (s : ℝ) (hs : 0 ≤ s) :
    (∫⁻ x : Sample n,
      ENNReal.ofReal (H s x * hazard s * riskIndicator i s x)
        ∂sampleLaw n failureLaw censorLaw) =
    ∫⁻ x : Sample n,
      ENNReal.ofReal (if s ≤ (x i).1 then
        H s (Function.update x i ((x i).1, s)) * hazard s *
          (censorLaw (Set.Ici s)).toReal else 0)
        ∂sampleLaw n failureLaw censorLaw := by
  /- Apply `lintegral_resample_censor` to the at-risk payoff. For each
     fixed x, `leftPredictable_censor_tail_invariant` makes H constant
     over c ≥ s. The remaining censor integral is the measure of Ici s;
     use hHazard.2.2.1 and hNonnegative for ofReal multiplication. -/
  classical
  have hF : Measurable (fun x : Sample n =>
      ENNReal.ofReal (H s x * hazard s * riskIndicator i s x)) := by
    have hHs : Measurable (H s) :=
      hMeasurable.comp (measurable_const.prodMk measurable_id)
    have hrisk : Measurable (riskIndicator i s : Sample n → ℝ) := by
      unfold riskIndicator
      have hfail : Measurable (fun x : Sample n => (x i).1) := by fun_prop
      have hcens : Measurable (fun x : Sample n => (x i).2) := by fun_prop
      have hevent : MeasurableSet
          {x : Sample n | 0 ≤ s ∧ s ≤ (x i).1 ∧ s ≤ (x i).2} := by
        simpa only [hs, true_and, Set.ofPred_and] using
          (measurableSet_le measurable_const hfail).inter
            (measurableSet_le measurable_const hcens)
      exact measurable_const.ite hevent measurable_const
    exact (hHs.mul_const _ |>.mul hrisk).ennreal_ofReal
  rw [lintegral_resample_censor failureLaw censorLaw hFailure hHazard.1 _ hF i]
  apply lintegral_congr
  intro x
  by_cases hf : s ≤ (x i).1
  · let a : ℝ := H s (Function.update x i ((x i).1, s)) * hazard s
    have ha : 0 ≤ a := mul_nonneg (hNonnegative s _) (hHazard.2.2.1 s)
    have hp : ∀ c : ℝ,
        ENNReal.ofReal (H s (Function.update x i ((x i).1, c)) * hazard s *
          riskIndicator i s (Function.update x i ((x i).1, c))) =
        (Set.Ici s).indicator (fun _ => ENNReal.ofReal a) c := by
      intro c
      by_cases hc : s ≤ c
      · have hInv := leftPredictable_censor_tail_invariant H hPredictable s
          (Function.update x i ((x i).1, s)) i c (by simp) hc
        have hInv' : H s (Function.update x i ((x i).1, s)) =
            H s (Function.update x i ((x i).1, c)) := by
          simpa [Function.update_idem] using hInv
        simpa [Set.indicator, Set.mem_Ici, hc, riskIndicator, hs, hf,
          Function.update_self, a] using
          congrArg (fun y : ℝ => ENNReal.ofReal (y * hazard s)) hInv'.symm
      · simp [Set.indicator, Set.mem_Ici, hc, riskIndicator, hs, hf,
          Function.update_self]
    simp_rw [hp]
    rw [lintegral_indicator_const measurableSet_Ici]
    have hfinite : censorLaw (Set.Ici s) ≠ ⊤ := by
      have hle : censorLaw (Set.Ici s) ≤ censorLaw Set.univ :=
        measure_mono (Set.subset_univ _)
      rw [hHazard.1.1] at hle
      exact ne_top_of_le_ne_top ENNReal.one_ne_top hle
    rw [← ENNReal.ofReal_toReal hfinite, ← ENNReal.ofReal_mul ha]
    simp [hf, a]
  · simp [riskIndicator, hs, hf, Function.update_self]

/-- [For any nonnegative extended-valued process, the expected Lebesgue integral from 0 to u of
the process restricted to times at or before subject i's failure time equals the same quantity
with times strictly before the failure time](goal), whatever the failure and censor laws.

The two integrands differ only at each sample's single failure time, a Lebesgue-null set. -/
theorem lintegral_failure_time_boundary {n : ℕ}
    (failureLaw censorLaw : Measure ℝ) (i : Fin n) (u : ℝ)
    (G : ℝ → Sample n → ENNReal) :
    (∫⁻ x : Sample n, ∫⁻ s in Set.Icc 0 u,
      (if s ≤ (x i).1 then G s x else 0) ∂volume
      ∂sampleLaw n failureLaw censorLaw) =
    ∫⁻ x : Sample n, ∫⁻ s in Set.Icc 0 u,
      (if s < (x i).1 then G s x else 0) ∂volume
      ∂sampleLaw n failureLaw censorLaw := by
  /- For each fixed `x`, use `lintegral_congr_ae`. Outside the null
     singleton `{(x i).1}`, the two order tests agree. The identity
     requires no measurability of `G`, since the two functions agree
     almost everywhere on the time measure. -/
  apply lintegral_congr
  intro x
  apply lintegral_congr_ae
  filter_upwards [Measure.ae_ne (volume.restrict (Set.Icc 0 u)) (x i).1] with s hs
  have hiff : s ≤ (x i).1 ↔ s < (x i).1 :=
    ⟨fun h => lt_of_le_of_ne h hs, le_of_lt⟩
  simp only [hiff]

/-- Suppose subjects are drawn independently with [failure times following a nonnegative time
law](hyp:hFailure) and independent [censor times whose law has the given censor
hazard](hyp:hazard,hHazard), and let the payoff process be [left predictable](hyp:hPredictable),
[jointly measurable in time and sample](hyp:hMeasurable), and [nonnegative](hyp:hNonnegative).
For a horizon u, [the expected integral from 0 to u of the payoff times the
hazard times subject i's at-risk indicator equals the expected integral, over times s before the
subject's failure time, of the payoff with that subject's censor time reset to s, times the
hazard at s, times the probability of censoring at or after s](goal).

This is the same resampled time integral as for the censor-event payoff; the strict failure-time
test differs from the inclusive at-risk test only on a Lebesgue-null singleton. -/
theorem predictable_censor_atRisk_hazard_lintegral {n : ℕ}
    (failureLaw censorLaw : Measure ℝ) (hazard : ℝ → ℝ)
    (hFailure : NonnegativeTimeLaw failureLaw)
    (hHazard : HasCensorHazard censorLaw hazard)
    (H : ℝ → Sample n → ℝ) (hPredictable : LeftPredictable H)
    (hMeasurable : Measurable (fun p : ℝ × Sample n => H p.1 p.2))
    (hNonnegative : ∀ s x, 0 ≤ H s x)
    (i : Fin n) (u : ℝ) :
    (∫⁻ x : Sample n, ∫⁻ s in Set.Icc 0 u,
      ENNReal.ofReal (H s x * hazard s * riskIndicator i s x)
        ∂volume ∂sampleLaw n failureLaw censorLaw) =
    ∫⁻ x : Sample n, ∫⁻ s in Set.Icc 0 u,
      ENNReal.ofReal (if s < (x i).1 then
        H s (Function.update x i ((x i).1, s)) * hazard s *
          (censorLaw (Set.Ici s)).toReal else 0) ∂volume
      ∂sampleLaw n failureLaw censorLaw := by
  classical
  haveI : IsProbabilityMeasure failureLaw := ⟨hFailure.1⟩
  haveI : IsProbabilityMeasure censorLaw := ⟨hHazard.1.1⟩
  let μ := sampleLaw n failureLaw censorLaw
  let ν := volume.restrict (Set.Icc 0 u)
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ, sampleLaw]
    infer_instance
  have hleft : Measurable (fun p : Sample n × ℝ =>
      ENNReal.ofReal (H p.2 p.1 * hazard p.2 * riskIndicator i p.2 p.1)) := by
    have hrisk : Measurable (fun p : Sample n × ℝ =>
        riskIndicator i p.2 p.1) := by
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
    exact ENNReal.measurable_ofReal.comp
      (((hMeasurable.comp (measurable_snd.prodMk measurable_fst)).mul
        (hHazard.2.1.comp measurable_snd)).mul hrisk)
  have hright : Measurable (fun p : Sample n × ℝ =>
      ENNReal.ofReal (if p.2 ≤ (p.1 i).1 then
        H p.2 (Function.update p.1 i ((p.1 i).1, p.2)) * hazard p.2 *
          (censorLaw (Set.Ici p.2)).toReal else 0)) := by
    have htail : Measurable (fun s : ℝ => (censorLaw (Set.Ici s)).toReal) := by
      apply ENNReal.measurable_toReal.comp
      apply Antitone.measurable
      intro a b hab
      exact measure_mono (Set.Ici_subset_Ici.mpr hab)
    have hevent : MeasurableSet {p : Sample n × ℝ | p.2 ≤ (p.1 i).1} :=
      measurableSet_le measurable_snd (by fun_prop)
    have hupdate : Measurable (fun p : Sample n × ℝ =>
        Function.update p.1 i ((p.1 i).1, p.2)) := by
      apply measurable_pi_lambda
      intro k
      by_cases hk : k = i
      · subst k
        simpa using ((show Measurable (fun p : Sample n × ℝ => (p.1 i).1)
          by fun_prop).prodMk measurable_snd :
          Measurable (fun p : Sample n × ℝ => ((p.1 i).1, p.2)))
      · simpa [Function.update_of_ne hk] using
          (show Measurable (fun p : Sample n × ℝ => p.1 k) by fun_prop)
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.ite hevent
    · exact ((hMeasurable.comp
          (measurable_snd.prodMk hupdate)).mul
          (hHazard.2.1.comp measurable_snd)).mul
          (htail.comp measurable_snd)
    · exact measurable_const
  calc
    (∫⁻ x : Sample n, ∫⁻ s in Set.Icc 0 u,
      ENNReal.ofReal (H s x * hazard s * riskIndicator i s x) ∂volume ∂μ)
        = ∫⁻ s : ℝ, ∫⁻ x : Sample n,
            ENNReal.ofReal (H s x * hazard s * riskIndicator i s x) ∂μ ∂ν := by
          exact lintegral_lintegral_swap hleft.aemeasurable
    _ = ∫⁻ s : ℝ, ∫⁻ x : Sample n,
          ENNReal.ofReal (if s ≤ (x i).1 then
            H s (Function.update x i ((x i).1, s)) * hazard s *
              (censorLaw (Set.Ici s)).toReal else 0) ∂μ ∂ν := by
          apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
          exact predictable_censor_atRisk_fixed_time_resample
            failureLaw censorLaw hazard hFailure hHazard H hPredictable
            hMeasurable hNonnegative i s hs.1
    _ = ∫⁻ x : Sample n, ∫⁻ s in Set.Icc 0 u,
          ENNReal.ofReal (if s ≤ (x i).1 then
            H s (Function.update x i ((x i).1, s)) * hazard s *
              (censorLaw (Set.Ici s)).toReal else 0) ∂volume ∂μ := by
          exact (lintegral_lintegral_swap hright.aemeasurable).symm
    _ = _ := by
          dsimp [μ]
          convert lintegral_failure_time_boundary failureLaw censorLaw i u
              (fun s x => ENNReal.ofReal
                (H s (Function.update x i ((x i).1, s)) * hazard s *
                  (censorLaw (Set.Ici s)).toReal)) using 1 <;>
            simp only [ENNReal.ofReal_zero, apply_ite]

/-- Suppose subjects are drawn independently with [failure times following a nonnegative time
law](hyp:hFailure) and independent [censor times whose law has the given censor
hazard](hyp:hazard,hHazard), and let the payoff process be [left predictable](hyp:hPredictable),
[jointly measurable in time and sample](hyp:hMeasurable), and [nonnegative](hyp:hNonnegative).
For [any horizon u](hyp:u), [the expected payoff at subject i's observed censor event
by u equals the expected integral from 0 to u of the payoff times the hazard times the subject's
at-risk indicator](goal), as extended nonnegative integrals that may be infinite. -/
theorem predictable_censor_compensator_lintegral {n : ℕ}
    (failureLaw censorLaw : Measure ℝ) (hazard : ℝ → ℝ)
    (hFailure : NonnegativeTimeLaw failureLaw)
    (hHazard : HasCensorHazard censorLaw hazard)
    (H : ℝ → Sample n → ℝ) (hPredictable : LeftPredictable H)
    (hMeasurable : Measurable (fun p : ℝ × Sample n => H p.1 p.2))
    (hNonnegative : ∀ s x, 0 ≤ H s x)
    (i : Fin n) (u : ℝ) :
    (∫⁻ x : Sample n,
      ENNReal.ofReal (if (x i).2 ≤ u ∧ (x i).2 < (x i).1
        then H (x i).2 x else 0)
        ∂sampleLaw n failureLaw censorLaw) =
    ∫⁻ x : Sample n, ∫⁻ s in Set.Icc 0 u,
      ENNReal.ofReal (H s x * hazard s * riskIndicator i s x)
        ∂volume ∂sampleLaw n failureLaw censorLaw := by
  /- Disintegrate the finite product law at subject `i`. For a fixed
     `s`, `leftPredictable_censor_tail_invariant` identifies the value of
     H across all censor times at or after `s`; the two preceding lemmas
     identify both sides with the same resampled time integral. -/
  exact (predictable_censor_event_hazard_lintegral failureLaw censorLaw hazard
    hFailure hHazard H hMeasurable hNonnegative i u).trans
    (predictable_censor_atRisk_hazard_lintegral failureLaw censorLaw hazard
      hFailure hHazard H hPredictable hMeasurable hNonnegative i u).symm

end Causalean.Stat.RecurrentEvent.CountingProcess
