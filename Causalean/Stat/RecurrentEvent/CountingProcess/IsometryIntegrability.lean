module
public import Causalean.Stat.RecurrentEvent.CountingProcess.SubjectIsometry
public import Mathlib.MeasureTheory.Function.L2Space

/-!
Integrability lemmas behind the finite-sample aggregate isometry and pairwise
orthogonality for predictable integrals against compensated censor-event
counts: integrability of each subject's quadratic hazard energy, square
integrability of event payoffs, and integrability of the cross-prefix event and
compensator terms. The isometry and orthogonality statements themselves are in
the `Isometry` module.
-/

public section

open MeasureTheory

namespace Causalean.Stat.RecurrentEvent.CountingProcess

/-- Suppose subjects are drawn independently with [failure times following a nonnegative time
law](hyp:hFailure) and independent [censor times whose law has the given censor
hazard](hyp:hazard,hHazard), and let the integrand be [jointly measurable in time and
sample](hyp:hMeasurable). For a horizon u, [finite expected quadratic
energy](hyp:hQuadratic), and [an integrable predictable quadratic energy summed over all
subjects](hyp:hEnergy), [each single subject's quadratic hazard energy up to u is integrable over
samples](goal). -/
theorem subject_energy_integrable {n : ℕ}
    (failureLaw censorLaw : Measure ℝ) (hazard : ℝ → ℝ)
    (hFailure : NonnegativeTimeLaw failureLaw)
    (hHazard : HasCensorHazard censorLaw hazard)
    (H : ℝ → Sample n → ℝ)
    (hMeasurable : Measurable (fun p : ℝ × Sample n => H p.1 p.2))
    (i : Fin n) (u : ℝ)
    (hQuadratic : QuadraticEnergyFinite failureLaw censorLaw hazard H u)
    (hEnergy : Integrable (predictableEnergy hazard H u)
      (sampleLaw n failureLaw censorLaw)) :
    Integrable (fun x : Sample n =>
      ∫ s in Set.Icc 0 u,
        (H s x) ^ 2 * hazard s * riskIndicator i s x ∂volume)
      (sampleLaw n failureLaw censorLaw) := by
  /- The nonnegative subject energy density is bounded by the sum density.
     `hQuadratic` gives almost-everywhere path integrability via Tonelli.
     Use integral monotonicity on those paths and `hEnergy` for the outer
     domination; joint measurability supplies the subject integral's
     strong measurability. -/
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
  let f : Sample n → ℝ → ℝ := fun x s =>
    (H s x) ^ 2 * hazard s * riskIndicator i s x
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
  have hbase : Measurable (fun p : Sample n × ℝ =>
      (H p.2 p.1) ^ 2 * hazard p.2) :=
    ((hMeasurable.comp (measurable_snd.prodMk measurable_fst)).pow_const 2).mul
      (hHazard.2.1.comp measurable_snd)
  have he_meas : Measurable (fun p : Sample n × ℝ => e p.1 p.2) :=
    hbase.mul (Finset.measurable_fun_sum _ (fun j _ => hrisk j))
  have hf_meas : Measurable (fun p : Sample n × ℝ => f p.1 p.2) :=
    hbase.mul (hrisk i)
  have he_nonneg (x : Sample n) (s : ℝ) : 0 ≤ e x s := by
    dsimp [e]
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (hHazard.2.2.1 s))
      (Finset.sum_nonneg (fun j _ => by unfold riskIndicator; split_ifs <;> norm_num))
  have hf_nonneg (x : Sample n) (s : ℝ) : 0 ≤ f x s := by
    dsimp [f]
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (hHazard.2.2.1 s)) (by
      unfold riskIndicator
      split_ifs <;> norm_num)
  have hf_le (x : Sample n) (s : ℝ) : f x s ≤ e x s := by
    dsimp [f, e]
    exact mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (f := fun j : Fin n => riskIndicator j s x)
        (fun j hj => by unfold riskIndicator; split_ifs <;> norm_num)
        (Finset.mem_univ i))
      (mul_nonneg (sq_nonneg _) (hHazard.2.2.1 s))
  have he_joint : Integrable (fun p : Sample n × ℝ => e p.1 p.2) (μ.prod ν) := by
    apply (lintegral_ofReal_ne_top_iff_integrable he_meas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => he_nonneg p.1 p.2))).1
    rw [lintegral_prod _ he_meas.ennreal_ofReal.aemeasurable]
    exact hQuadratic
  have he_path : ∀ᵐ x ∂μ, Integrable (e x) ν := he_joint.prod_right_ae
  have hf_path : ∀ᵐ x ∂μ, Integrable (f x) ν := by
    filter_upwards [he_path] with x hx
    exact hx.mono'
      (hf_meas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun s => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hf_nonneg x s)]
        exact hf_le x s))
  have hf_outer_meas : AEStronglyMeasurable (fun x => ∫ s, f x s ∂ν) μ :=
    hf_meas.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
  apply integrable_of_le_of_le hf_outer_meas
    (Filter.Eventually.of_forall (fun x => integral_nonneg (hf_nonneg x)))
    ?_ (integrable_const 0) hEnergy
  filter_upwards [hf_path, he_path] with x hx hxe
  exact integral_mono hx hxe (hf_le x)

/-- Suppose subjects are drawn independently with [failure times following a nonnegative time
law](hyp:hFailure) and independent [censor times whose law has the given censor
hazard](hyp:hazard,hHazard), and let the integrand be [left predictable](hyp:hPredictable) and [jointly
measurable in time and sample](hyp:hMeasurable). For a horizon u and [finite
expected quadratic energy](hyp:hQuadratic), [the squared payoff at subject i's observed censor event by u, taken as
zero when no such event occurs, is integrable over samples](goal). -/
theorem subject_event_payoff_square_integrable {n : ℕ}
    (failureLaw censorLaw : Measure ℝ) (hazard : ℝ → ℝ)
    (hFailure : NonnegativeTimeLaw failureLaw)
    (hHazard : HasCensorHazard censorLaw hazard)
    (H : ℝ → Sample n → ℝ) (hPredictable : LeftPredictable H)
    (hMeasurable : Measurable (fun p : ℝ × Sample n => H p.1 p.2))
    (i : Fin n) (u : ℝ)
    (hQuadratic : QuadraticEnergyFinite failureLaw censorLaw hazard H u)
    :
    Integrable (fun x : Sample n =>
      (if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then H (x i).2 x else 0) ^ 2)
      (sampleLaw n failureLaw censorLaw) := by
  /- Use the nonnegative extended compensator identity
     `predictable_censor_compensator_lintegral` with payoff H². Bound its
     right side by `hQuadratic`, then turn the finite nonnegative lintegral
     into integrability. The Bochner equality in
     `subject_event_square_expectation` alone cannot certify this, since a
     nonintegrable Bochner integral is defined to be zero. -/
  classical
  let μ := sampleLaw n failureLaw censorLaw
  let Q : ℝ → Sample n → ℝ := fun s x => (H s x) ^ 2
  have hQpred : LeftPredictable Q := by
    intro s x y hxy
    simpa [Q] using congrArg (fun z : ℝ => z ^ 2) (hPredictable s x y hxy)
  have hQmeas : Measurable (fun p : ℝ × Sample n => Q p.1 p.2) :=
    hMeasurable.pow_const 2
  have hQnonneg : ∀ s x, 0 ≤ Q s x := fun s x => sq_nonneg _
  have hlin := predictable_censor_compensator_lintegral
    failureLaw censorLaw hazard hFailure hHazard Q hQpred hQmeas hQnonneg i u
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
  have hm : Measurable (fun x : Sample n =>
      if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then Q (x i).2 x else 0) := by
    have hc : Measurable (fun x : Sample n => (x i).2) := by fun_prop
    have hf : Measurable (fun x : Sample n => (x i).1) := by fun_prop
    exact (hQmeas.comp (hc.prodMk measurable_id)).ite
      ((measurableSet_le hc measurable_const).inter (measurableSet_lt hc hf))
      measurable_const
  have hEventInt : Integrable (fun x : Sample n =>
      if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then Q (x i).2 x else 0) μ := by
    apply (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable (by
      filter_upwards [] with x
      split_ifs <;> positivity)).1
    rw [hlin]
    exact hfinite
  simpa only [Q, ite_pow, zero_pow (by decide : (2 : ℕ) ≠ 0)] using hEventInt

/-- Suppose subjects are drawn independently with [failure times following a nonnegative time
law](hyp:hFailure) and independent [censor times whose law has the given censor
hazard](hyp:hazard,hHazard), and let the integrand be [left predictable](hyp:hPredictable) and [jointly
measurable in time and sample](hyp:hMeasurable). For a horizon u and [finite
expected quadratic energy](hyp:hQuadratic), [the square of subject j's strict-past compensated integral evaluated at
subject i's observed censor event by u, taken as zero when no such event occurs, is integrable
over samples](goal). -/
theorem cross_prefix_at_event_square_integrable {n : ℕ}
    (failureLaw censorLaw : Measure ℝ) (hazard : ℝ → ℝ)
    (hFailure : NonnegativeTimeLaw failureLaw)
    (hHazard : HasCensorHazard censorLaw hazard)
    (H : ℝ → Sample n → ℝ) (hPredictable : LeftPredictable H)
    (hMeasurable : Measurable (fun p : ℝ × Sample n => H p.1 p.2))
    (i j : Fin n) (u : ℝ)
    (hQuadratic : QuadraticEnergyFinite failureLaw censorLaw hazard H u)
    :
    Integrable (fun x : Sample n =>
      (if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then
        subjectIntegralBefore hazard H j (x i).2 x else 0) ^ 2)
      (sampleLaw n failureLaw censorLaw) := by
  /- On the event branch, expand `subjectIntegralBefore`. The jump payoff
     for j is bounded by its horizon-u jump payoff in absolute value; the
     strict-past hazard integral is bounded by the absolute hazard payoff
     on [0,u]. Apply (a-b)² ≤ 2a²+2b². The jump square is integrable after
     establishing `subject_event_payoff_square_integrable` with subject j;
     the hazard square is integrable by
     `subject_hazard_square_integrable` (its absolute-payoff version is in
     `SubjectMoments`). Restrict the pathwise comparison to the full-measure
     set of nonnegative failure/censor times, since a negative censor time
     need not appear in the horizon-u event payoff. Joint measurability
     follows from `subjectIntegralBefore_jointMeasurable`. The strict
     boundary changes the hazard integral only on a Lebesgue-null
     singleton. -/
  classical
  let μ := sampleLaw n failureLaw censorLaw
  let f : Sample n → ℝ := fun x =>
    if (x j).2 ≤ u ∧ (x j).2 < (x j).1 then H (x j).2 x else 0
  let g : Sample n → ℝ := fun x =>
    ∫ s in Set.Icc 0 u,
      |H s x * hazard s * riskIndicator j s x| ∂volume
  have hJump : Integrable (fun x => (f x) ^ 2) μ :=
    subject_event_payoff_square_integrable failureLaw censorLaw hazard
      hFailure hHazard H hPredictable hMeasurable j u hQuadratic
  have hAbsQ : QuadraticEnergyFinite failureLaw censorLaw hazard
      (fun s x => |H s x|) u := by
    simpa only [QuadraticEnergyFinite, sq_abs] using hQuadratic
  have hAbs : Integrable (fun x => (g x) ^ 2) μ := by
    have h := subject_hazard_square_integrable failureLaw censorLaw hazard
      hFailure hHazard (fun s x => |H s x|)
      (by fun_prop) j u hAbsQ
    convert h using 1
    funext x
    congr 1
    apply integral_congr_ae
    filter_upwards [] with s
    rw [abs_mul, abs_mul, abs_of_nonneg (hHazard.2.2.1 s)]
    have hr : 0 ≤ riskIndicator j s x := by
      unfold riskIndicator
      split_ifs <;> norm_num
    rw [abs_of_nonneg hr]
  have hMeas : AEStronglyMeasurable (fun x : Sample n =>
      (if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then
        subjectIntegralBefore hazard H j (x i).2 x else 0) ^ 2) μ := by
    have hc : Measurable (fun x : Sample n => (x i).2) := by fun_prop
    have hf : Measurable (fun x : Sample n => (x i).1) := by fun_prop
    exact (((subjectIntegralBefore_jointMeasurable hazard hHazard.2.1 H
      hMeasurable j).comp (hc.prodMk measurable_id)).ite
      ((measurableSet_le hc measurable_const).inter (measurableSet_lt hc hf))
      measurable_const).pow_const 2 |>.aestronglyMeasurable
  have hCensor : ∀ᵐ x ∂μ, 0 ≤ (x j).2 := by
    haveI : IsProbabilityMeasure failureLaw := ⟨hFailure.1⟩
    haveI : IsProbabilityMeasure censorLaw := ⟨hHazard.1.1⟩
    haveI : IsProbabilityMeasure (failureLaw.prod censorLaw) := inferInstance
    have hC : ∀ᵐ c ∂censorLaw, 0 ≤ c :=
      (mem_ae_iff_prob_eq_one measurableSet_Ici).2 hHazard.1.2
    have hPair : ∀ᵐ z ∂failureLaw.prod censorLaw, 0 ≤ z.2 := by
      apply (Measure.ae_prod_iff_ae_ae
        (measurableSet_le measurable_const measurable_snd)).2
      filter_upwards [] with a
      exact hC
    unfold μ sampleLaw
    exact (Measure.tendsto_eval_ae_ae
      (μ := fun _ : Fin n => failureLaw.prod censorLaw) (i := j)) hPair
  have hPath := subject_hazard_path_integrable_ae failureLaw censorLaw hazard
    hHazard H hMeasurable j u hQuadratic
  haveI : IsProbabilityMeasure failureLaw := ⟨hFailure.1⟩
  haveI : IsProbabilityMeasure censorLaw := ⟨hHazard.1.1⟩
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ, sampleLaw]
    infer_instance
  apply integrable_of_le_of_le hMeas
    (Filter.Eventually.of_forall (fun x => sq_nonneg _)) ?_
    (integrable_const 0) ((hJump.const_mul 2).add (hAbs.const_mul 2))
  filter_upwards [hCensor, hPath] with x hxC hxPath
  by_cases hi : (x i).2 ≤ u ∧ (x i).2 < (x i).1
  · have hJumpBound :
        |(if (x j).2 < (x i).2 ∧ (x j).2 < (x j).1 then
          H (x j).2 x else 0)| ≤ |f x| := by
      by_cases hj : (x j).2 < (x i).2 ∧ (x j).2 < (x j).1
      · have hju : (x j).2 ≤ u ∧ (x j).2 < (x j).1 :=
          ⟨le_trans (le_of_lt hj.1) hi.1, hj.2⟩
        simp [hj, hju, f]
      · simp [hj]
    have hIntBound :
        |∫ s in Set.Icc 0 (x i).2,
          H s x * hazard s * riskIndicator j s x ∂volume| ≤ g x := by
      let F : ℝ → ℝ := fun s => H s x * hazard s * riskIndicator j s x
      have hsub : Set.Icc 0 (x i).2 ⊆ Set.Icc 0 u := by
        intro s hs
        exact ⟨hs.1, le_trans hs.2 hi.1⟩
      have hAbsPath : IntegrableOn (fun s => |F s|) (Set.Icc 0 u) volume := by
        exact hxPath.abs
      calc
        |∫ s in Set.Icc 0 (x i).2, F s ∂volume| ≤
            ∫ s in Set.Icc 0 (x i).2, |F s| ∂volume :=
          abs_integral_le_integral_abs
        _ ≤ ∫ s in Set.Icc 0 u, |F s| ∂volume :=
          setIntegral_mono_set hAbsPath
            (Filter.Eventually.of_forall (fun s => abs_nonneg _))
            (Filter.Eventually.of_forall (fun s hs => hsub hs))
    have hmain : |subjectIntegralBefore hazard H j (x i).2 x| ≤
        |f x| + g x := by
      unfold subjectIntegralBefore
      calc
        |_ - _| ≤ _ + _ := abs_sub _ _
        _ ≤ |f x| + g x := add_le_add hJumpBound hIntBound
    have hg : 0 ≤ g x := by
      dsimp [g]
      exact integral_nonneg (fun s => abs_nonneg _)
    have hsquare : (subjectIntegralBefore hazard H j (x i).2 x) ^ 2 ≤
        2 * (f x) ^ 2 + 2 * (g x) ^ 2 := by
      have hsq := (sq_le_sq₀ (abs_nonneg _)
        (add_nonneg (abs_nonneg _) hg)).2 hmain
      nlinarith [sq_nonneg (|f x| - g x), sq_abs (f x),
        sq_abs (subjectIntegralBefore hazard H j (x i).2 x)]
    simpa [hi] using hsquare
  · simp only [hi, ↓reduceIte, zero_pow (by decide : (2 : ℕ) ≠ 0)]
    change 0 ≤ 2 * f x ^ 2 + 2 * g x ^ 2
    positivity

/-- Suppose subjects are drawn independently with [failure times following a nonnegative time
law](hyp:hFailure) and independent [censor times whose law has the given censor
hazard](hyp:hazard,hHazard), and let the integrand be [left predictable](hyp:hPredictable) and [jointly
measurable in time and sample](hyp:hMeasurable). For a horizon u and [finite
expected quadratic energy](hyp:hQuadratic), [the payoff at subject i's observed censor event by u times subject j's
strict-past compensated integral at that event, taken as zero when no such event occurs, is
integrable over samples](goal). -/
theorem cross_prefix_event_integrable {n : ℕ}
    (failureLaw censorLaw : Measure ℝ) (hazard : ℝ → ℝ)
    (hFailure : NonnegativeTimeLaw failureLaw)
    (hHazard : HasCensorHazard censorLaw hazard)
    (H : ℝ → Sample n → ℝ) (hPredictable : LeftPredictable H)
    (hMeasurable : Measurable (fun p : ℝ × Sample n => H p.1 p.2))
    (i j : Fin n) (u : ℝ)
    (hQuadratic : QuadraticEnergyFinite failureLaw censorLaw hazard H u)
    :
    Integrable (fun x : Sample n =>
      if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then
        H (x i).2 x * subjectIntegralBefore hazard H j (x i).2 x else 0)
      (sampleLaw n failureLaw censorLaw) := by
  /- Use `subject_event_payoff_square_integrable` for the event payoff of i
     and `cross_prefix_at_event_square_integrable` for the strict-past
     integral of j on the same event. Obtain measurability of the first
     factor from `hMeasurable` and of the second from
     `subjectIntegralBefore_jointMeasurable`. Convert both square-integrability
     claims with Mathlib's `memLp_two_iff_integrable_sq`, then apply
     `MemLp.integrable_mul` with exponents 2 and 2. The product of the two
     event-restricted factors simplifies to the target. -/
  let μ := sampleLaw n failureLaw censorLaw
  let f : Sample n → ℝ := fun x =>
    if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then H (x i).2 x else 0
  let g : Sample n → ℝ := fun x =>
    if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then
      subjectIntegralBefore hazard H j (x i).2 x else 0
  have hc : Measurable (fun x : Sample n => (x i).2) := by fun_prop
  have ht : Measurable (fun x : Sample n => (x i).1) := by fun_prop
  have hevent : MeasurableSet {x : Sample n |
      (x i).2 ≤ u ∧ (x i).2 < (x i).1} :=
    (measurableSet_le hc measurable_const).inter (measurableSet_lt hc ht)
  have hfmeas : AEStronglyMeasurable f μ :=
    ((hMeasurable.comp (hc.prodMk measurable_id)).ite hevent
      measurable_const).aestronglyMeasurable
  have hgmeas : AEStronglyMeasurable g μ :=
    (((subjectIntegralBefore_jointMeasurable hazard hHazard.2.1 H
      hMeasurable j).comp (hc.prodMk measurable_id)).ite hevent
      measurable_const).aestronglyMeasurable
  have hfLp : MemLp f 2 μ :=
    (MeasureTheory.memLp_two_iff_integrable_sq hfmeas).2 (by
      simpa only [f, μ] using
        subject_event_payoff_square_integrable failureLaw censorLaw hazard
          hFailure hHazard H hPredictable hMeasurable i u hQuadratic)
  have hgLp : MemLp g 2 μ :=
    (MeasureTheory.memLp_two_iff_integrable_sq hgmeas).2 (by
      simpa only [g, μ] using
        cross_prefix_at_event_square_integrable failureLaw censorLaw hazard
          hFailure hHazard H hPredictable hMeasurable i j u hQuadratic)
  have hfg : Integrable (f * g) μ := hfLp.integrable_mul hgLp
  convert hfg using 1
  funext x
  by_cases hx : (x i).2 ≤ u ∧ (x i).2 < (x i).1 <;> simp [f, g, hx]

/-- Suppose subjects are drawn independently with [failure times following a nonnegative time
law](hyp:hFailure) and independent [censor times whose law has the given censor
hazard](hyp:hazard,hHazard), and let the integrand be [left predictable](hyp:hPredictable) and [jointly
measurable in time and sample](hyp:hMeasurable). For a horizon u and [finite
expected quadratic energy](hyp:hQuadratic), [the integral from 0 to u of subject j's strict-past compensated integral
times the integrand times the hazard times subject i's at-risk indicator is integrable over
samples](goal). -/
theorem cross_prefix_compensator_integrable {n : ℕ}
    (failureLaw censorLaw : Measure ℝ) (hazard : ℝ → ℝ)
    (hFailure : NonnegativeTimeLaw failureLaw)
    (hHazard : HasCensorHazard censorLaw hazard)
    (H : ℝ → Sample n → ℝ) (hPredictable : LeftPredictable H)
    (hMeasurable : Measurable (fun p : ℝ × Sample n => H p.1 p.2))
    (i j : Fin n) (u : ℝ)
    (hQuadratic : QuadraticEnergyFinite failureLaw censorLaw hazard H u)
    :
    Integrable (fun x : Sample n =>
      ∫ s in Set.Icc 0 u,
        subjectIntegralBefore hazard H j s x * H s x * hazard s *
          riskIndicator i s x ∂volume)
      (sampleLaw n failureLaw censorLaw) := by
  /- Let P(s,x) be the product of H and the strict-past integral for j.
     `subjectIntegralBefore_leftPredictable` and
     `subjectIntegralBefore_jointMeasurable` make P an admissible predictable
     payoff. `predictable_censor_compensator_integrable` derives the signed
     compensator's integrability from its event payoff. -/
  let P : ℝ → Sample n → ℝ := fun s x =>
    H s x * subjectIntegralBefore hazard H j s x
  have hPpred : LeftPredictable P := by
    intro s x y hxy
    exact congrArg₂ (· * ·) (hPredictable s x y hxy)
      (subjectIntegralBefore_leftPredictable hazard H hPredictable j s x y hxy)
  have hPmeas : Measurable (fun p : ℝ × Sample n => P p.1 p.2) :=
    hMeasurable.mul
      (subjectIntegralBefore_jointMeasurable hazard hHazard.2.1 H hMeasurable j)
  have hEvent : Integrable (fun x : Sample n =>
      if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then P (x i).2 x else 0)
      (sampleLaw n failureLaw censorLaw) := by
    convert cross_prefix_event_integrable failureLaw censorLaw hazard
      hFailure hHazard H hPredictable hMeasurable i j u hQuadratic using 1
  have hComp := predictable_censor_compensator_integrable
    failureLaw censorLaw hazard hFailure hHazard P hPpred hPmeas i u hEvent
  convert hComp using 1
  funext x
  apply integral_congr_ae
  filter_upwards [] with s
  dsimp [P]
  ring

