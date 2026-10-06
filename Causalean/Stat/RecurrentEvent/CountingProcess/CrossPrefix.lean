module
public import Causalean.Stat.RecurrentEvent.CountingProcess.Basic
public import Mathlib.MeasureTheory.Integral.Prod

/-!
The strict-past version of a subjectwise compensated censor integral. Its
event term excludes a jump at the evaluation time, so it can be used as a
predictable factor in cross-subject integration by parts.
-/

@[expose] public section

open MeasureTheory

namespace Causalean.Stat.RecurrentEvent.CountingProcess

/-- [The strict-past compensated integral](goal) of [a process](hyp:H) for [subject i](hyp:i)
before [time s](hyp:s) in [a sample](hyp:x) is the process's value at the subject's censor time
when an observed censor event occurs strictly before s (zero otherwise), minus the integral over
times from 0 to s of the process times [the censor hazard](hyp:hazard) times the subject's
at-risk indicator. -/
noncomputable def subjectIntegralBefore {n : ℕ} (hazard : ℝ → ℝ)
    (H : ℝ → Sample n → ℝ) (i : Fin n) (s : ℝ) (x : Sample n) : ℝ :=
  (if (x i).2 < s ∧ (x i).2 < (x i).1 then H (x i).2 x else 0) -
    ∫ t in Set.Icc 0 s, H t x * hazard t * riskIndicator i t x ∂volume

/-- If [the integrand is left predictable](hyp:hPredictable), then [each subject's strict-past
compensated integral, as a process in time, is left predictable](goal), whatever [the censor
hazard](hyp:hazard) used in its compensator. -/
theorem subjectIntegralBefore_leftPredictable {n : ℕ}
    (hazard : ℝ → ℝ) (H : ℝ → Sample n → ℝ)
    (hPredictable : LeftPredictable H) (i : Fin n) :
    LeftPredictable (subjectIntegralBefore hazard H i) := by
  have hRisk (t : ℝ) (z : Sample n)
      (hf : t ≠ (z i).1) (hc : t ≠ (z i).2) :
      riskIndicator i t z =
        if 0 ≤ t ∧ censorCount i t z = 0 ∧ failureCount i t z = 0
        then 1 else 0 := by
    by_cases h0 : 0 ≤ t
    · rcases lt_or_gt_of_ne hf with htf | htf
      · rcases lt_or_gt_of_ne hc with htc | htc
        · simp [riskIndicator, censorCount, failureCount, h0, htf, htc, le_of_lt]
        · have hcf : (z i).2 < (z i).1 := lt_trans htc htf
          simp [riskIndicator, censorCount, failureCount, h0, htf, htc, hcf, le_of_lt]
      · rcases lt_or_gt_of_ne hc with htc | htc
        · have hfc : (z i).1 < (z i).2 := lt_trans htf htc
          simp [riskIndicator, censorCount, failureCount, h0, htf, htc, hfc, le_of_lt]
        · by_cases hfc : (z i).1 ≤ (z i).2
          · simp [riskIndicator, censorCount, failureCount, h0, htf, htc, hfc, le_of_lt]
          · have hcf : (z i).2 < (z i).1 := lt_of_not_ge hfc
            simp [riskIndicator, censorCount, failureCount, h0, htf, htc, hcf, le_of_lt]
    · simp [riskIndicator, censorCount, failureCount, h0]
  have hNe (a : ℝ) : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ a := by
    rw [ae_iff]
    simpa only [not_ne_iff, Set.ofPred_eq_eq_singleton] using
      (measure_singleton a : (volume : Measure ℝ) {a} = 0)
  intro s x y hHist
  have hInt : (∫ t in Set.Icc 0 s,
      H t x * hazard t * riskIndicator i t x ∂volume) =
      ∫ t in Set.Icc 0 s,
        H t y * hazard t * riskIndicator i t y ∂volume := by
    rw [integral_Icc_eq_integral_Ico, integral_Icc_eq_integral_Ico]
    apply integral_congr_ae
    have hxF := ae_restrict_of_ae (s := Set.Ico 0 s) (hNe (x i).1)
    have hxC := ae_restrict_of_ae (s := Set.Ico 0 s) (hNe (x i).2)
    have hyF := ae_restrict_of_ae (s := Set.Ico 0 s) (hNe (y i).1)
    have hyC := ae_restrict_of_ae (s := Set.Ico 0 s) (hNe (y i).2)
    have htMem : ∀ᵐ t ∂(volume : Measure ℝ).restrict (Set.Ico 0 s),
        t ∈ Set.Ico 0 s := ae_restrict_mem measurableSet_Ico
    filter_upwards [hxF, hxC, hyF, hyC, htMem] with t hxF hxC hyF hyC ht
    have hHistory := hHist i t ht.2
    have hHt : H t x = H t y :=
      hPredictable t x y (fun j u hu => hHist j u (lt_trans hu ht.2))
    rw [hHt, hRisk t x hxF hxC, hRisk t y hyF hyC,
      hHistory.1, hHistory.2]
  have hEvent :
      (if (x i).2 < s ∧ (x i).2 < (x i).1 then H (x i).2 x else 0) =
      (if (y i).2 < s ∧ (y i).2 < (y i).1 then H (y i).2 y else 0) := by
    by_cases hx : (x i).2 < s ∧ (x i).2 < (x i).1
    · have hxc : censorCount i (x i).2 x = 1 := by
        simp [censorCount, hx.2]
      have hyc : censorCount i (x i).2 y = 1 := by
        rw [← (hHist i (x i).2 hx.1).1, hxc]
      have hyEvent : (y i).2 ≤ (x i).2 ∧ (y i).2 < (y i).1 := by
        by_contra hn
        simp [censorCount, hn] at hyc
      have hy : (y i).2 < s ∧ (y i).2 < (y i).1 :=
        ⟨lt_of_le_of_lt hyEvent.1 hx.1, hyEvent.2⟩
      have hyc' : censorCount i (y i).2 y = 1 := by
        simp [censorCount, hy.2]
      have hxc' : censorCount i (y i).2 x = 1 := by
        rw [(hHist i (y i).2 hy.1).1, hyc']
      have hxy : (x i).2 ≤ (y i).2 := by
        by_contra hn
        have hn' : ¬ ((x i).2 ≤ (y i).2 ∧ (x i).2 < (x i).1) := by
          simp [hn]
        simp [censorCount, hn'] at hxc'
      have heq : (x i).2 = (y i).2 := le_antisymm hxy hyEvent.1
      have hH : H (x i).2 x = H (y i).2 y := by
        rw [← heq]
        exact hPredictable (x i).2 x y
          (fun j u hu => hHist j u (lt_trans hu hx.1))
      simp [hx, hy, hH]
    · have hyFalse : ¬ ((y i).2 < s ∧ (y i).2 < (y i).1) := by
        intro hy
        have hyc : censorCount i (y i).2 y = 1 := by
          simp [censorCount, hy.2]
        have hxc : censorCount i (y i).2 x = 1 := by
          rw [(hHist i (y i).2 hy.1).1, hyc]
        have hxEvent : (x i).2 ≤ (y i).2 ∧ (x i).2 < (x i).1 := by
          by_contra hn
          simp [censorCount, hn] at hxc
        exact hx ⟨lt_of_le_of_lt hxEvent.1 hy.1, hxEvent.2⟩
      simp [hx, hyFalse]
  simp only [subjectIntegralBefore, hEvent, hInt]

/-- If [the censor hazard is measurable](hyp:hazard,hHazard) and [the integrand is jointly measurable in
time and sample](hyp:hMeasurable), then [a subject's strict-past compensated integral is jointly
measurable in time and sample](goal). -/
@[fun_prop] theorem subjectIntegralBefore_jointMeasurable {n : ℕ}
    (hazard : ℝ → ℝ) (hHazard : Measurable hazard)
    (H : ℝ → Sample n → ℝ)
    (hMeasurable : Measurable (fun p : ℝ × Sample n => H p.1 p.2))
    (i : Fin n) :
    Measurable (fun p : ℝ × Sample n =>
      subjectIntegralBefore hazard H i p.1 p.2) := by
  let F : (ℝ × Sample n) × ℝ → ℝ := fun q =>
    if 0 ≤ q.2 ∧ q.2 ≤ q.1.1 then
      H q.2 q.1.2 * hazard q.2 * riskIndicator i q.2 q.1.2
    else 0
  have hq2 : Measurable (fun q : (ℝ × Sample n) × ℝ => q.2) := by fun_prop
  have hq1 : Measurable (fun q : (ℝ × Sample n) × ℝ => q.1.1) := by fun_prop
  have hf : Measurable (fun q : (ℝ × Sample n) × ℝ => (q.1.2 i).1) := by fun_prop
  have hc : Measurable (fun q : (ℝ × Sample n) × ℝ => (q.1.2 i).2) := by fun_prop
  have hp : Measurable (fun q : (ℝ × Sample n) × ℝ => (q.2, q.1.2)) := by fun_prop
  have hRisk : Measurable (fun q : (ℝ × Sample n) × ℝ =>
      riskIndicator i q.2 q.1.2) := by
    unfold riskIndicator
    apply Measurable.ite
    · simpa only [Set.ofPred_and, Set.inter_assoc] using
        ((measurableSet_le
          (measurable_const : Measurable (fun _ : (ℝ × Sample n) × ℝ => (0 : ℝ)))
          hq2).inter (measurableSet_le hq2 hf)).inter (measurableSet_le hq2 hc)
    · exact measurable_const
    · exact measurable_const
  have hF : Measurable F := by
    dsimp [F]
    apply Measurable.ite
    · simpa only [Set.ofPred_and] using
        (measurableSet_le
          (measurable_const : Measurable (fun _ : (ℝ × Sample n) × ℝ => (0 : ℝ)))
          hq2).inter (measurableSet_le hq2 hq1)
    · exact ((hMeasurable.comp hp).mul (hHazard.comp hq2)).mul hRisk
    · exact measurable_const
  have hI : Measurable (fun p : ℝ × Sample n => ∫ t, F (p, t) ∂volume) :=
    hF.stronglyMeasurable.integral_prod_right'.measurable
  have hEq : ∀ p : ℝ × Sample n, (∫ t, F (p, t) ∂volume) =
      ∫ t in Set.Icc 0 p.1,
        H t p.2 * hazard t * riskIndicator i t p.2 ∂volume := by
    intro p
    rw [← integral_indicator measurableSet_Icc]
    congr 1
    funext t
    simp only [F, Set.indicator, Set.mem_Icc]
  rw [show (fun p : ℝ × Sample n => ∫ t, F (p, t) ∂volume) =
    (fun p => ∫ t in Set.Icc 0 p.1,
      H t p.2 * hazard t * riskIndicator i t p.2 ∂volume)
    from funext hEq] at hI
  have hC : Measurable (fun p : ℝ × Sample n => (p.2 i).2) := by fun_prop
  have hD : Measurable (fun p : ℝ × Sample n => (p.2 i).1) := by fun_prop
  have hS : Measurable (fun p : ℝ × Sample n => p.1) := by fun_prop
  have hP : Measurable (fun p : ℝ × Sample n => ((p.2 i).2, p.2)) := by fun_prop
  have hEvent : Measurable (fun p : ℝ × Sample n =>
      if (p.2 i).2 < p.1 ∧ (p.2 i).2 < (p.2 i).1
      then H (p.2 i).2 p.2 else 0) := by
    apply Measurable.ite
    · simpa only [Set.ofPred_and] using
        (measurableSet_lt hC hS).inter (measurableSet_lt hC hD)
    · exact hMeasurable.comp hP
    · exact measurable_const
  exact hEvent.sub hI

end Causalean.Stat.RecurrentEvent.CountingProcess
