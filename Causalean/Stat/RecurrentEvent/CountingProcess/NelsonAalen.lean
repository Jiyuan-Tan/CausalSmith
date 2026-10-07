module
public import Causalean.Stat.RecurrentEvent.CountingProcess.Isometry
public import Causalean.Stat.RecurrentEvent.CountingProcess.RandomHorizon
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.MeasureTheory.Integral.Prod

/-!
The zero-safe Nelson–Aalen inverse-risk integrand specializes the counting
process isometry. An independent random evaluation time weights the fixed-time
risk integrand by the evaluation-time survival probability.
-/

public section

open MeasureTheory

namespace Causalean.Stat.RecurrentEvent.CountingProcess

/-- [The zero-safe inverse risk-set size is a left-predictable process](goal): its value at each
time depends only on the observed censor and failure counts at strictly earlier times. -/
theorem inverseRisk_leftPredictable {n : ℕ} :
    LeftPredictable (inverseRisk (n := n)) := by
  intro s x y hhistory
  have hbefore (i : Fin n) (a b : Sample n)
      (hab : ∀ (j : Fin n) t, t < s →
        censorCount j t a = censorCount j t b ∧
        failureCount j t a = failureCount j t b) :
      (a i).1 < s ∨ (a i).2 < s → (b i).1 < s ∨ (b i).2 < s := by
    intro ha
    by_cases hf : (a i).1 ≤ (a i).2
    · have ht : (a i).1 < s := by rcases ha with ha | ha <;> linarith
      have he := (hab i (a i).1 ht).2
      have haCount : failureCount i (a i).1 a = 1 := by
        simp [failureCount, hf]
      rw [haCount] at he
      have hb : (b i).1 ≤ (a i).1 ∧ (b i).1 ≤ (b i).2 := by
        by_contra hh
        simp [failureCount, hh] at he
      exact Or.inl (lt_of_le_of_lt hb.1 ht)
    · have hc : (a i).2 < (a i).1 := lt_of_not_ge hf
      have ht : (a i).2 < s := by rcases ha with ha | ha <;> linarith
      have he := (hab i (a i).2 ht).1
      have haCount : censorCount i (a i).2 a = 1 := by
        simp [censorCount, hc]
      rw [haCount] at he
      have hb : (b i).2 ≤ (a i).2 ∧ (b i).2 < (b i).1 := by
        by_contra hh
        simp [censorCount, hh] at he
      exact Or.inr (lt_of_le_of_lt hb.1 ht)
  have hreverse : ∀ (i : Fin n) t, t < s →
      censorCount i t y = censorCount i t x ∧
      failureCount i t y = failureCount i t x := by
    intro i t ht
    exact ⟨((hhistory i t ht).1).symm, ((hhistory i t ht).2).symm⟩
  have hrisk : riskSet s x = riskSet s y := by
    unfold riskSet
    apply Finset.sum_congr rfl
    intro i _
    have hstatus : ((x i).1 < s ∨ (x i).2 < s) ↔
        ((y i).1 < s ∨ (y i).2 < s) :=
      ⟨hbefore i x y hhistory, hbefore i y x hreverse⟩
    have hle : (s ≤ (x i).1 ∧ s ≤ (x i).2) ↔
        (s ≤ (y i).1 ∧ s ≤ (y i).2) := by
      simpa only [not_or, not_lt] using not_congr hstatus
    simp only [and_congr Iff.rfl hle]
  simp only [inverseRisk, hrisk]

/-- [The zero-safe inverse risk-set size is jointly measurable in time and in the sample of
failure and censor times](goal). -/
theorem inverseRisk_jointMeasurable {n : ℕ} :
    Measurable (fun p : ℝ × Sample n => inverseRisk p.1 p.2) := by
  classical
  have hcoord (i : Fin n) :
      Measurable (fun p : ℝ × Sample n => (p.2 i).1) := by fun_prop
  have hcoord' (i : Fin n) :
      Measurable (fun p : ℝ × Sample n => (p.2 i).2) := by fun_prop
  have hcond (i : Fin n) :
      MeasurableSet {p : ℝ × Sample n |
        0 ≤ p.1 ∧ p.1 ≤ (p.2 i).1 ∧ p.1 ≤ (p.2 i).2} := by
    have h0 : MeasurableSet {p : ℝ × Sample n | (0 : ℝ) ≤ p.1} :=
      measurableSet_le measurable_const measurable_fst
    simpa only [Set.ofPred_and] using
      h0.inter ((measurableSet_le measurable_fst (hcoord i)).inter
        (measurableSet_le measurable_fst (hcoord' i)))
  have hcount : Measurable (fun p : ℝ × Sample n => riskSet p.1 p.2) := by
    unfold riskSet
    exact Finset.measurable_sum _ (fun i _ =>
      Measurable.ite (hcond i) measurable_const measurable_const)
  unfold inverseRisk
  exact Measurable.ite (measurableSet_eq_fun hcount measurable_const) measurable_const
    (measurable_const.div ((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp hcount))

/-- At [any time s](hyp:s) and in [any sample](hyp:x), [the square of the zero-safe inverse
risk-set size times the number of subjects at risk equals the zero-safe inverse risk-set size
itself](goal), including when the risk set is empty. -/
theorem inverseRisk_square_risk {n : ℕ} (s : ℝ) (x : Sample n) :
    (inverseRisk s x) ^ 2 * (∑ i : Fin n, riskIndicator i s x) =
      inverseRisk s x := by
  classical
  have hs : (∑ i : Fin n, riskIndicator i s x) = (riskSet s x : ℝ) := by
    simp only [riskIndicator, riskSet, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
      Nat.cast_zero]
  rw [hs]
  by_cases hz : riskSet s x = 0
  · simp [inverseRisk, hz]
  · have hr : (riskSet s x : ℝ) ≠ 0 := by exact_mod_cast hz
    simp only [inverseRisk, hz, ↓reduceIte]
    field_simp

private theorem inverseRisk_nonneg_le_one {n : ℕ} (s : ℝ) (x : Sample n) :
    0 ≤ inverseRisk s x ∧ inverseRisk s x ≤ 1 := by
  by_cases hz : riskSet s x = 0
  · simp [inverseRisk, hz]
  · have hpos : (1 : ℝ) ≤ (riskSet s x : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
    simp only [inverseRisk, hz, ↓reduceIte]
    constructor
    · positivity
    · exact div_le_self (by norm_num : (0 : ℝ) ≤ 1) hpos

private theorem inverseRisk_hazard_integrable_prod {n : ℕ}
    (failureLaw censorLaw : Measure ℝ) (hazard : ℝ → ℝ)
    (hFailure : NonnegativeTimeLaw failureLaw)
    (hHazard : HasCensorHazard censorLaw hazard) (u : ℝ) :
    Integrable (fun p : Sample n × ℝ => hazard p.2 * inverseRisk p.2 p.1)
      ((sampleLaw n failureLaw censorLaw).prod (volume.restrict (Set.Icc 0 u))) := by
  letI : IsProbabilityMeasure failureLaw := ⟨hFailure.1⟩
  letI : IsProbabilityMeasure censorLaw := ⟨hHazard.1.1⟩
  letI : IsProbabilityMeasure (sampleLaw n failureLaw censorLaw) := by
    unfold sampleLaw
    infer_instance
  let μ := sampleLaw n failureLaw censorLaw
  let ν := volume.restrict (Set.Icc 0 u)
  have hbase : Integrable (fun p : Sample n × ℝ => hazard p.2) (μ.prod ν) :=
    Integrable.comp_snd (hHazard.2.2.2.1 u) μ
  have hm : Measurable (fun p : Sample n × ℝ => hazard p.2 * inverseRisk p.2 p.1) :=
    (hHazard.2.1.comp measurable_snd).mul
      (inverseRisk_jointMeasurable.comp measurable_swap)
  apply Integrable.mono' hbase hm.aestronglyMeasurable
  filter_upwards [] with p
  have hn := inverseRisk_nonneg_le_one p.2 p.1
  have hh := hHazard.2.2.1 p.2
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hh hn.1)]
  exact (mul_le_mul_of_nonneg_left hn.2 hh).trans_eq (mul_one _)

/-- Under independent sampling with [failure times following a nonnegative time
law](hyp:hFailure) and independent [censor times whose law has the given censor
hazard](hyp:hazard,hHazard), at a horizon u [the zero-safe inverse risk-set size
has finite expected quadratic energy](goal).

Its square weighted by the risk-set size is at most one, so the energy is bounded by the
integrated hazard. -/
theorem inverseRisk_quadratic_energy_finite {n : ℕ}
    (failureLaw censorLaw : Measure ℝ) (hazard : ℝ → ℝ)
    (hFailure : NonnegativeTimeLaw failureLaw)
    (hHazard : HasCensorHazard censorLaw hazard)
    (u : ℝ) :
    QuadraticEnergyFinite failureLaw censorLaw hazard (inverseRisk (n := n)) u := by
  let μ := sampleLaw n failureLaw censorLaw
  let ν := volume.restrict (Set.Icc 0 u)
  have hm : Measurable (fun p : Sample n × ℝ => hazard p.2 * inverseRisk p.2 p.1) :=
    (hHazard.2.1.comp measurable_snd).mul
      (inverseRisk_jointMeasurable.comp measurable_swap)
  have hnonneg : ∀ p : Sample n × ℝ, 0 ≤ hazard p.2 * inverseRisk p.2 p.1 := by
    intro p
    exact mul_nonneg (hHazard.2.2.1 p.2) (inverseRisk_nonneg_le_one p.2 p.1).1
  have hfinite : (∫⁻ p : Sample n × ℝ,
      ENNReal.ofReal (hazard p.2 * inverseRisk p.2 p.1) ∂μ.prod ν) ≠ ⊤ :=
    (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
      (Filter.Eventually.of_forall hnonneg)).2
      (inverseRisk_hazard_integrable_prod failureLaw censorLaw hazard hFailure hHazard u)
  unfold QuadraticEnergyFinite
  change (∫⁻ x : Sample n, ∫⁻ s : ℝ,
    ENNReal.ofReal ((inverseRisk s x) ^ 2 * hazard s *
      (∑ i : Fin n, riskIndicator i s x)) ∂ν ∂μ) ≠ ⊤
  have hrewrite (x : Sample n) (s : ℝ) :
      (inverseRisk s x) ^ 2 * hazard s * (∑ i : Fin n, riskIndicator i s x) =
        hazard s * inverseRisk s x := by
    calc
      _ = hazard s * ((inverseRisk s x) ^ 2 *
          (∑ i : Fin n, riskIndicator i s x)) := by ring
      _ = hazard s * inverseRisk s x := by rw [inverseRisk_square_risk]
  simp_rw [hrewrite]
  rw [lintegral_lintegral hm.ennreal_ofReal.aemeasurable]
  exact hfinite

/-- Under independent sampling with [failure times following a nonnegative time
law](hyp:hFailure) and independent [censor times whose law has the given censor
hazard](hyp:hazard,hHazard), at a horizon u [the predictable quadratic energy of
the zero-safe inverse risk-set size, the Nelson–Aalen integrand, is integrable over
samples](goal). -/
theorem inverseRisk_energy_integrable {n : ℕ}
    (failureLaw censorLaw : Measure ℝ) (hazard : ℝ → ℝ)
    (hFailure : NonnegativeTimeLaw failureLaw)
    (hHazard : HasCensorHazard censorLaw hazard)
    (u : ℝ) :
    Integrable (predictableEnergy hazard (inverseRisk (n := n)) u)
      (sampleLaw n failureLaw censorLaw) := by
  have h := (inverseRisk_hazard_integrable_prod (n := n) failureLaw censorLaw hazard
    hFailure hHazard u).integral_prod_left
  have hrewrite (x : Sample n) (s : ℝ) :
      (inverseRisk s x) ^ 2 * hazard s * (∑ i : Fin n, riskIndicator i s x) =
        hazard s * inverseRisk s x := by
    calc
      _ = hazard s * ((inverseRisk s x) ^ 2 *
          (∑ i : Fin n, riskIndicator i s x)) := by ring
      _ = hazard s * inverseRisk s x := by rw [inverseRisk_square_risk]
  simp_rw [← hrewrite] at h
  exact h

/-- Under independent sampling with [failure times following a nonnegative time
law](hyp:hFailure) and independent [censor times whose law has the given censor
hazard](hyp:hazard,hHazard), at [a nonnegative horizon u](hyp:hu) [the expected squared compensated
Nelson–Aalen error equals the integral over times from 0 to u of the censor hazard times the
expected zero-safe inverse risk-set size](goal). -/
theorem nelsonAalen_squared_risk {n : ℕ}
    (failureLaw censorLaw : Measure ℝ) (hazard : ℝ → ℝ)
    (hFailure : NonnegativeTimeLaw failureLaw)
    (hHazard : HasCensorHazard censorLaw hazard)
    (u : ℝ) (hu : 0 ≤ u) :
    (∫ x : Sample n, (nelsonAalenError hazard u x) ^ 2
      ∂sampleLaw n failureLaw censorLaw) =
    ∫ s in Set.Icc 0 u, hazard s *
      (∫ x : Sample n, inverseRisk s x
        ∂sampleLaw n failureLaw censorLaw) ∂volume := by
  letI : IsProbabilityMeasure failureLaw := ⟨hFailure.1⟩
  letI : IsProbabilityMeasure censorLaw := ⟨hHazard.1.1⟩
  letI : IsProbabilityMeasure (sampleLaw n failureLaw censorLaw) := by
    unfold sampleLaw
    infer_instance
  let μ := sampleLaw n failureLaw censorLaw
  let ν := volume.restrict (Set.Icc 0 u)
  have hprod : Integrable
      (fun p : Sample n × ℝ => hazard p.2 * inverseRisk p.2 p.1) (μ.prod ν) :=
    inverseRisk_hazard_integrable_prod failureLaw censorLaw hazard hFailure hHazard u
  have hrewrite (x : Sample n) (s : ℝ) :
      (inverseRisk s x) ^ 2 * hazard s * (∑ i : Fin n, riskIndicator i s x) =
        hazard s * inverseRisk s x := by
    calc
      _ = hazard s * ((inverseRisk s x) ^ 2 *
          (∑ i : Fin n, riskIndicator i s x)) := by ring
      _ = hazard s * inverseRisk s x := by rw [inverseRisk_square_risk]
  calc
    _ = ∫ x : Sample n, predictableEnergy hazard (inverseRisk (n := n)) u x ∂μ := by
      simpa only [nelsonAalenError, μ] using
        aggregate_integral_isometry failureLaw censorLaw hazard hFailure hHazard
          (inverseRisk (n := n)) inverseRisk_leftPredictable
          inverseRisk_jointMeasurable u hu
          (inverseRisk_quadratic_energy_finite failureLaw censorLaw hazard
            hFailure hHazard u)
          (inverseRisk_energy_integrable failureLaw censorLaw hazard
            hFailure hHazard u)
    _ = ∫ x : Sample n, ∫ s : ℝ, hazard s * inverseRisk s x ∂ν ∂μ := by
      simp_rw [predictableEnergy, hrewrite]
      rfl
    _ = ∫ s : ℝ, ∫ x : Sample n, hazard s * inverseRisk s x ∂μ ∂ν := by
      exact integral_integral_swap hprod
    _ = ∫ s : ℝ, hazard s * (∫ x : Sample n, inverseRisk s x ∂μ) ∂ν := by
      simp_rw [integral_const_mul]
    _ = _ := rfl

/-- If [the censor hazard is measurable](hyp:hazard,hHazard), then [the compensated Nelson–Aalen error
is jointly measurable in the evaluation horizon and the sample](goal). -/
@[fun_prop] theorem nelsonAalenError_jointMeasurable {n : ℕ}
    (hazard : ℝ → ℝ) (hHazard : Measurable hazard) :
    Measurable (fun p : ℝ × Sample n => nelsonAalenError hazard p.1 p.2) := by
  classical
  have hcoord (i : Fin n) :
      Measurable (fun p : ℝ × Sample n => (p.2 i).2) := by fun_prop
  have hcoord' (i : Fin n) :
      Measurable (fun p : ℝ × Sample n => (p.2 i).1) := by fun_prop
  have hrisk (i : Fin n) :
      Measurable (fun q : (ℝ × Sample n) × ℝ => riskIndicator i q.2 q.1.2) := by
    unfold riskIndicator
    have hfirst : Measurable (fun q : (ℝ × Sample n) × ℝ => (q.1.2 i).1) := by
      fun_prop
    have hsecond : Measurable (fun q : (ℝ × Sample n) × ℝ => (q.1.2 i).2) := by
      fun_prop
    have hs : MeasurableSet {q : (ℝ × Sample n) × ℝ |
        0 ≤ q.2 ∧ q.2 ≤ (q.1.2 i).1 ∧ q.2 ≤ (q.1.2 i).2} := by
      exact (measurableSet_le measurable_const measurable_snd).inter
        ((measurableSet_le measurable_snd hfirst).inter
          (measurableSet_le measurable_snd hsecond))
    exact Measurable.ite hs measurable_const measurable_const
  have hcomp (i : Fin n) : Measurable (fun p : ℝ × Sample n =>
      ∫ s in Set.Icc 0 p.1,
        inverseRisk s p.2 * hazard s * riskIndicator i s p.2 ∂volume) := by
    have hset : MeasurableSet {q : (ℝ × Sample n) × ℝ |
        0 ≤ q.2 ∧ q.2 ≤ q.1.1} :=
      (measurableSet_le measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd (measurable_fst.comp measurable_fst))
    have hbase : Measurable (fun q : (ℝ × Sample n) × ℝ =>
        inverseRisk q.2 q.1.2 * hazard q.2 * riskIndicator i q.2 q.1.2) := by
      exact ((inverseRisk_jointMeasurable.comp
        (measurable_snd.prodMk (measurable_snd.comp measurable_fst))).mul
          (hHazard.comp measurable_snd)).mul (hrisk i)
    have hjoint : Measurable (fun q : (ℝ × Sample n) × ℝ =>
        if 0 ≤ q.2 ∧ q.2 ≤ q.1.1 then
          inverseRisk q.2 q.1.2 * hazard q.2 * riskIndicator i q.2 q.1.2 else 0) :=
      hbase.ite hset measurable_const
    have hint := hjoint.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))
    convert hint.measurable using 1
    ext p
    rw [← integral_indicator (measurableSet_Icc : MeasurableSet (Set.Icc 0 p.1))]
    congr 1
    funext s
    simp only [Set.indicator, Set.mem_Icc]
  unfold nelsonAalenError aggregateIntegral
  apply Finset.measurable_sum
  intro i hi
  unfold subjectIntegral
  have hevent : MeasurableSet {p : ℝ × Sample n |
      (p.2 i).2 ≤ p.1 ∧ (p.2 i).2 < (p.2 i).1} :=
    (measurableSet_le (hcoord i) measurable_fst).inter
      (measurableSet_lt (hcoord i) (hcoord' i))
  exact (Measurable.ite hevent
    (inverseRisk_jointMeasurable.comp ((hcoord i).prodMk measurable_snd))
    measurable_const).sub (hcomp i)

/-- Under independent sampling with [failure times following a nonnegative time
law](hyp:hFailure) and independent [censor times whose law has the given censor
hazard](hyp:hazard,hHazard), and with an evaluation time drawn independently of the sample from [a
nonnegative time law](hyp:hEvaluation), [the expected squared compensated Nelson–Aalen error at
the random evaluation time equals the integral over all times s of the censor hazard at s, times
the probability that evaluation occurs at or after s, times the expected zero-safe inverse
risk-set size at s](goal).

Both sides are extended nonnegative integrals, so the identity also covers infinite risk without
a global integrability assumption. -/
theorem nelsonAalen_random_time_tonelli {n : ℕ}
    (failureLaw censorLaw evaluationLaw : Measure ℝ)
    (hazard : ℝ → ℝ)
    (hFailure : NonnegativeTimeLaw failureLaw)
    (hHazard : HasCensorHazard censorLaw hazard)
    (hEvaluation : NonnegativeTimeLaw evaluationLaw) :
    (∫⁻ z : Sample n × ℝ,
      ENNReal.ofReal ((nelsonAalenError hazard z.2 z.1) ^ 2)
        ∂(sampleLaw n failureLaw censorLaw).prod evaluationLaw) =
    ∫⁻ s : ℝ, ENNReal.ofReal (hazard s) *
      evaluationLaw (Set.Ici s) *
      (∫⁻ x : Sample n, ENNReal.ofReal (inverseRisk s x)
        ∂sampleLaw n failureLaw censorLaw) ∂volume := by
  classical
  letI : IsProbabilityMeasure failureLaw := ⟨hFailure.1⟩
  letI : IsProbabilityMeasure censorLaw := ⟨hHazard.1.1⟩
  let μ := sampleLaw n failureLaw censorLaw
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, sampleLaw]
    infer_instance
  let B (i : Fin n) (u : ℝ) (x : Sample n) : ℝ :=
    ∫ s in Set.Icc 0 u, inverseRisk s x * hazard s * riskIndicator i s x ∂volume
  have hSquare (u : ℝ) (hu : 0 ≤ u) :
      Integrable (fun x : Sample n => (nelsonAalenError hazard u x) ^ 2) μ := by
    let J (i : Fin n) (x : Sample n) : ℝ :=
      if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then inverseRisk (x i).2 x else 0
    have hJ (i : Fin n) : Integrable (fun x : Sample n => (J i x) ^ 2) μ :=
      subject_event_payoff_square_integrable failureLaw censorLaw hazard hFailure
        hHazard inverseRisk inverseRisk_leftPredictable inverseRisk_jointMeasurable
        i u (inverseRisk_quadratic_energy_finite failureLaw censorLaw hazard
          hFailure hHazard u)
    have hB (i : Fin n) : Integrable (fun x : Sample n => (B i u x) ^ 2) μ :=
      subject_hazard_square_integrable failureLaw censorLaw hazard hFailure
        hHazard inverseRisk inverseRisk_jointMeasurable i u
        (inverseRisk_quadratic_energy_finite failureLaw censorLaw hazard
          hFailure hHazard u)
    have hBound : Integrable (fun x : Sample n =>
        (n : ℝ) * ∑ i : Fin n, (2 * (J i x) ^ 2 + 2 * (B i u x) ^ 2)) μ := by
      apply Integrable.const_mul
      apply integrable_finsetSum
      intro i hi
      exact ((hJ i).const_mul 2).add ((hB i).const_mul 2)
    have hm : Measurable (fun x : Sample n => (nelsonAalenError hazard u x) ^ 2) :=
      ((nelsonAalenError_jointMeasurable hazard hHazard.2.1).comp
        (measurable_const.prodMk measurable_id)).pow_const 2
    apply Integrable.mono' hBound hm.aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hsum : (∑ i : Fin n, (J i x - B i u x)) ^ 2 ≤
        (n : ℝ) * (∑ i : Fin n, (J i x - B i u x) ^ 2) := by
      simpa using (sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset (Fin n))) (f := fun i => J i x - B i u x))
    have hterms : (∑ i : Fin n, (J i x - B i u x) ^ 2) ≤
        ∑ i : Fin n, (2 * (J i x) ^ 2 + 2 * (B i u x) ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      nlinarith [sq_nonneg (J i x + B i u x)]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hfinal := hsum.trans (mul_le_mul_of_nonneg_left hterms hn)
    simpa only [nelsonAalenError, aggregateIntegral, subjectIntegral, J, B, μ]
      using hfinal
  have hRisk (s : ℝ) : Integrable (fun x : Sample n => inverseRisk s x) μ := by
    have hm : Measurable (fun x : Sample n => inverseRisk s x) :=
      inverseRisk_jointMeasurable.comp (measurable_const.prodMk measurable_id)
    apply Integrable.of_bound hm.aestronglyMeasurable 1
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (inverseRisk_nonneg_le_one s x).1]
    exact (inverseRisk_nonneg_le_one s x).2
  let f (s : ℝ) : ENNReal := ENNReal.ofReal (hazard s) *
    ∫⁻ x : Sample n, ENNReal.ofReal (inverseRisk s x) ∂μ
  have hf : Measurable f := by
    have hJoint : Measurable (fun p : Sample n × ℝ =>
        ENNReal.ofReal (inverseRisk p.2 p.1)) :=
      (inverseRisk_jointMeasurable.comp measurable_swap).ennreal_ofReal
    exact (hHazard.2.1.ennreal_ofReal).mul hJoint.lintegral_prod_left'
  have hFixed (u : ℝ) (hu : 0 ≤ u) :
      (∫⁻ x : Sample n, ENNReal.ofReal ((nelsonAalenError hazard u x) ^ 2) ∂μ) =
      ∫⁻ s in Set.Icc 0 u, f s ∂volume := by
    let ν := (volume : Measure ℝ).restrict (Set.Icc 0 u)
    have hprod : Integrable
        (fun p : Sample n × ℝ => hazard p.2 * inverseRisk p.2 p.1) (μ.prod ν) :=
      inverseRisk_hazard_integrable_prod failureLaw censorLaw hazard hFailure hHazard u
    have hright : Integrable (fun s : ℝ =>
        hazard s * (∫ x : Sample n, inverseRisk s x ∂μ)) ν := by
      convert hprod.integral_prod_right using 1
      ext s
      exact (integral_const_mul (hazard s) (fun x : Sample n => inverseRisk s x)).symm
    have hnonneg (s : ℝ) :
        0 ≤ hazard s * (∫ x : Sample n, inverseRisk s x ∂μ) :=
      mul_nonneg (hHazard.2.2.1 s)
        (integral_nonneg fun x => (inverseRisk_nonneg_le_one s x).1)
    calc
      _ = ENNReal.ofReal (∫ x : Sample n,
          (nelsonAalenError hazard u x) ^ 2 ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal (hSquare u hu)
          (Filter.Eventually.of_forall fun x => sq_nonneg _)).symm
      _ = ENNReal.ofReal (∫ s in Set.Icc 0 u,
          hazard s * (∫ x : Sample n, inverseRisk s x ∂μ) ∂volume) := by
        rw [nelsonAalen_squared_risk failureLaw censorLaw hazard hFailure hHazard u hu]
      _ = ∫⁻ s in Set.Icc 0 u,
          ENNReal.ofReal (hazard s * (∫ x : Sample n, inverseRisk s x ∂μ))
          ∂volume :=
        ofReal_integral_eq_lintegral_ofReal hright
          (Filter.Eventually.of_forall hnonneg)
      _ = ∫⁻ s in Set.Icc 0 u, f s ∂volume := by
        apply lintegral_congr
        intro s
        rw [ENNReal.ofReal_mul (hHazard.2.2.1 s),
          ofReal_integral_eq_lintegral_ofReal (hRisk s)
            (Filter.Eventually.of_forall fun x => (inverseRisk_nonneg_le_one s x).1)]
  letI : IsProbabilityMeasure evaluationLaw := ⟨hEvaluation.1⟩
  have hEvaluationAE : Set.Ici (0 : ℝ) ∈ ae evaluationLaw :=
    (mem_ae_iff_prob_eq_one measurableSet_Ici).2 hEvaluation.2
  have hSquaredJoint : Measurable (fun p : Sample n × ℝ =>
      ENNReal.ofReal ((nelsonAalenError hazard p.2 p.1) ^ 2)) :=
    (((nelsonAalenError_jointMeasurable hazard hHazard.2.1).comp
      measurable_swap).pow_const 2).ennreal_ofReal
  calc
    _ = ∫⁻ x : Sample n, ∫⁻ u : ℝ,
        ENNReal.ofReal ((nelsonAalenError hazard u x) ^ 2) ∂evaluationLaw ∂μ :=
      (lintegral_lintegral hSquaredJoint.aemeasurable).symm
    _ = ∫⁻ u : ℝ, ∫⁻ x : Sample n,
        ENNReal.ofReal ((nelsonAalenError hazard u x) ^ 2) ∂μ ∂evaluationLaw :=
      lintegral_lintegral_swap hSquaredJoint.aemeasurable
    _ = ∫⁻ u : ℝ, ∫⁻ s in Set.Icc 0 u, f s ∂volume ∂evaluationLaw := by
      apply lintegral_congr_ae
      filter_upwards [hEvaluationAE] with u hu
      exact hFixed u hu
    _ = ∫⁻ s : ℝ, f s * evaluationLaw (Set.Ici s)
          ∂(volume.restrict (Set.Ici (0 : ℝ))) :=
      lintegral_random_horizon evaluationLaw hEvaluation f hf
    _ = _ := by
      rw [← lintegral_indicator measurableSet_Ici]
      apply lintegral_congr
      intro s
      by_cases hs : 0 ≤ s
      · simp only [Set.indicator, Set.mem_Ici, hs, ↓reduceIte, f]
        ac_rfl
      · have hzero (x : Sample n) : inverseRisk s x = 0 := by
          simp [inverseRisk, riskSet, hs]
        simp [Set.indicator, hs, hzero]

end Causalean.Stat.RecurrentEvent.CountingProcess
