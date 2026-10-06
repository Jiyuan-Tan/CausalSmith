module
public import Causalean.Stat.RecurrentEvent.CountingProcess.Basic
public import Mathlib.MeasureTheory.Integral.Prod

/-!
Predictability and joint measurability of a cumulative at-risk hazard payoff
multiplied by its current predictable payoff. These properties prepare the
signed compensator identity used in subjectwise isometry.
-/

public section

open MeasureTheory

namespace Causalean.Stat.RecurrentEvent.CountingProcess

/-- For [any censor hazard](hyp:hazard), if [the payoff process is left
predictable](hyp:hPredictable), then [the process whose value at time s is subject i's
hazard-weighted accumulated at-risk payoff up to s times the payoff at s is also left
predictable](goal). -/
theorem subject_prefix_mixed_predictable {n : ℕ}
    (hazard : ℝ → ℝ) (H : ℝ → Sample n → ℝ)
    (hPredictable : LeftPredictable H) (i : Fin n) :
    LeftPredictable (fun s x =>
      (∫ t in Set.Icc 0 s,
        H t x * hazard t * riskIndicator i t x ∂volume) * H s x) := by
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
  have hNe (a : ℝ) :
      ∀ᵐ t ∂(volume : Measure ℝ), t ≠ a := by
    rw [ae_iff]
    simpa only [not_ne_iff, Set.ofPred_eq_eq_singleton] using
      (measure_singleton a : (volume : Measure ℝ) {a} = 0)
  intro s x y hHist
  have hHs : H s x = H s y := hPredictable s x y hHist
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
  change (∫ t in Set.Icc 0 s,
      H t x * hazard t * riskIndicator i t x ∂volume) * H s x =
    (∫ t in Set.Icc 0 s,
      H t y * hazard t * riskIndicator i t y ∂volume) * H s y
  rw [hInt, hHs]

/-- If [the censor hazard is measurable](hyp:hazard,hHazardMeasurable) and [the payoff is jointly
measurable in time and sample](hyp:hMeasurable), then [subject i's accumulated hazard-weighted
at-risk payoff up to each time, multiplied by the payoff at that time, is jointly measurable in
time and sample](goal). -/
theorem subject_prefix_mixed_jointMeasurable {n : ℕ}
    (hazard : ℝ → ℝ) (hHazardMeasurable : Measurable hazard)
    (H : ℝ → Sample n → ℝ)
    (hMeasurable : Measurable (fun p : ℝ × Sample n => H p.1 p.2))
    (i : Fin n) :
    Measurable (fun p : ℝ × Sample n =>
      (∫ t in Set.Icc 0 p.1,
        H t p.2 * hazard t * riskIndicator i t p.2 ∂volume) * H p.1 p.2) := by
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
    · exact ((hMeasurable.comp hp).mul (hHazardMeasurable.comp hq2)).mul hRisk
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
  exact hI.mul hMeasurable

end Causalean.Stat.RecurrentEvent.CountingProcess
