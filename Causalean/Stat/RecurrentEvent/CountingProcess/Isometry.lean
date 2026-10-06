module
public import Causalean.Stat.RecurrentEvent.CountingProcess.IsometryIntegrability

/-!
# Aggregate compensated-count isometry

This module combines finite-sample subjectwise compensated censor integrals.
It supplies pairwise orthogonality and the aggregate predictable-integral
isometry whose bracket is the at-risk hazard integral.
-/

public section

open MeasureTheory

namespace Causalean.Stat.RecurrentEvent.CountingProcess

/-- Suppose subjects are drawn independently with [failure times following a nonnegative time
law](hyp:hFailure) and independent [censor times whose law has the given censor
hazard](hyp:hazard,hHazard), and let the integrand be [left predictable](hyp:hPredictable) and [jointly
measurable in time and sample](hyp:hMeasurable). For [two different subjects](hyp:hij), [a
nonnegative horizon u](hyp:hu), [finite expected quadratic energy](hyp:hQuadratic), and [an
integrable predictable quadratic energy](hyp:hEnergy), [the expected product of the two
subjects' integrals against their compensated censor counts up to u is zero](goal). -/
theorem distinct_subject_integrals_orthogonal {n : ℕ}
    (failureLaw censorLaw : Measure ℝ) (hazard : ℝ → ℝ)
    (hFailure : NonnegativeTimeLaw failureLaw)
    (hHazard : HasCensorHazard censorLaw hazard)
    (H : ℝ → Sample n → ℝ) (hPredictable : LeftPredictable H)
    (hMeasurable : Measurable (fun p : ℝ × Sample n => H p.1 p.2))
    (i j : Fin n) (hij : i ≠ j) (u : ℝ) (hu : 0 ≤ u)
    (hQuadratic : QuadraticEnergyFinite failureLaw censorLaw hazard H u)
    (hEnergy : Integrable (predictableEnergy hazard H u)
      (sampleLaw n failureLaw censorLaw)) :
    (∫ x : Sample n,
      subjectIntegral hazard H i u x * subjectIntegral hazard H j u x
        ∂sampleLaw n failureLaw censorLaw) = 0 := by
  /- Work in the sample probability law. Derive integrability of each
     subject's square directly from the event-payoff square and hazard-payoff
     square integrability lemmas, using `(a-b)^2 ≤ 2a²+2b²`; an equality of
     Bochner integrals alone does not establish integrability. Then use
     `memLp_two_iff_integrable_sq` and `MemLp.integrable_mul` for the product.
     `distinct_subject_integral_product_pathwise`
     expands that product into two jump/prefix terms minus two time integrals.
     Censor times differ almost surely by `distinct_censor_times_ae`.

     For each orientation (i,j), set P(s,x) := H(s,x) *
     subjectIntegralBefore hazard H j s x. The cross-prefix lemmas show that
     P is left predictable and jointly measurable. Use
     `cross_prefix_event_integrable` and
     `cross_prefix_compensator_integrable` for its two payoffs. Apply
     `predictable_censor_compensator` to identify the expectations. Finally
     integrate the pathwise expansion and cancel the two matched pairs. -/
  classical
  let μ := sampleLaw n failureLaw censorLaw
  haveI : IsProbabilityMeasure failureLaw := ⟨hFailure.1⟩
  haveI : IsProbabilityMeasure censorLaw := ⟨hHazard.1.1⟩
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ, sampleLaw]
    infer_instance
  have hSquare (k : Fin n) :
      AEStronglyMeasurable (subjectIntegral hazard H k u) μ ∧
      Integrable (fun x : Sample n => (subjectIntegral hazard H k u x) ^ 2) μ := by
    let E : Sample n → ℝ := fun x =>
      if (x k).2 ≤ u ∧ (x k).2 < (x k).1 then H (x k).2 x else 0
    let A : Sample n → ℝ := fun x =>
      ∫ s in Set.Icc 0 u, H s x * hazard s * riskIndicator k s x ∂volume
    have hEmeas : Measurable E := by
      have hc : Measurable (fun x : Sample n => (x k).2) := by fun_prop
      have hf : Measurable (fun x : Sample n => (x k).1) := by fun_prop
      exact (hMeasurable.comp (hc.prodMk measurable_id)).ite
        ((measurableSet_le hc measurable_const).inter (measurableSet_lt hc hf))
        measurable_const
    have hAmeas : Measurable A := by
      let F : Sample n × ℝ → ℝ := fun p =>
        H p.2 p.1 * hazard p.2 * riskIndicator k p.2 p.1
      have hrisk : Measurable (fun p : Sample n × ℝ =>
          riskIndicator k p.2 p.1) := by
        unfold riskIndicator
        have hf : Measurable (fun p : Sample n × ℝ => (p.1 k).1) := by fun_prop
        have hc : Measurable (fun p : Sample n × ℝ => (p.1 k).2) := by fun_prop
        have hs : MeasurableSet {p : Sample n × ℝ |
            0 ≤ p.2 ∧ p.2 ≤ (p.1 k).1 ∧ p.2 ≤ (p.1 k).2} := by
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
    have hELp : MemLp E 2 μ :=
      (memLp_two_iff_integrable_sq hEmeas.aestronglyMeasurable).2
        (subject_event_payoff_square_integrable failureLaw censorLaw hazard
          hFailure hHazard H hPredictable hMeasurable k u hu hQuadratic hEnergy)
    have hALp : MemLp A 2 μ :=
      (memLp_two_iff_integrable_sq hAmeas.aestronglyMeasurable).2
        (subject_hazard_square_integrable failureLaw censorLaw hazard
          hFailure hHazard H hMeasurable k u hu hQuadratic)
    constructor
    · change AEStronglyMeasurable (E - A) μ
      exact (hEmeas.sub hAmeas).aestronglyMeasurable
    · simpa [subjectIntegral, E, A, Pi.sub_apply] using
        (hELp.sub hALp).integrable_sq
  have hProduct : Integrable (fun x : Sample n =>
      subjectIntegral hazard H i u x * subjectIntegral hazard H j u x) μ := by
    exact ((memLp_two_iff_integrable_sq (hSquare i).1).2 (hSquare i).2).integrable_mul
      ((memLp_two_iff_integrable_sq (hSquare j).1).2 (hSquare j).2)
  let P : Fin n → Fin n → ℝ → Sample n → ℝ := fun _ l s x =>
    H s x * subjectIntegralBefore hazard H l s x
  let E : Fin n → Fin n → Sample n → ℝ := fun k l x =>
    if (x k).2 ≤ u ∧ (x k).2 < (x k).1 then P k l (x k).2 x else 0
  let C : Fin n → Fin n → Sample n → ℝ := fun k l x =>
    ∫ s in Set.Icc 0 u,
      subjectIntegralBefore hazard H l s x *
        H s x * hazard s * riskIndicator k s x ∂volume
  have hPair (k l : Fin n) (hkl : k ≠ l) :
      Integrable (E k l) μ ∧ Integrable (C k l) μ ∧
        (∫ x, E k l x ∂μ) = ∫ x, C k l x ∂μ := by
    have hPpred : LeftPredictable (fun s x => H s x *
        subjectIntegralBefore hazard H l s x) := by
      intro s x y hxy
      exact congrArg₂ (· * ·) (hPredictable s x y hxy)
        (subjectIntegralBefore_leftPredictable hazard H hPredictable l s x y hxy)
    have hPmeas : Measurable (fun p : ℝ × Sample n =>
        H p.1 p.2 * subjectIntegralBefore hazard H l p.1 p.2) :=
      hMeasurable.mul
        (subjectIntegralBefore_jointMeasurable hazard hHazard.2.1 H hMeasurable l)
    have hE : Integrable (fun x : Sample n =>
        if (x k).2 ≤ u ∧ (x k).2 < (x k).1 then
          H (x k).2 x * subjectIntegralBefore hazard H l (x k).2 x else 0) μ :=
      cross_prefix_event_integrable failureLaw censorLaw hazard hFailure hHazard
        H hPredictable hMeasurable k l u hu hQuadratic hEnergy
    have hC : Integrable (fun x : Sample n =>
        ∫ s in Set.Icc 0 u,
          subjectIntegralBefore hazard H l s x * H s x * hazard s *
            riskIndicator k s x ∂volume) μ :=
      cross_prefix_compensator_integrable failureLaw censorLaw hazard
        hFailure hHazard H hPredictable hMeasurable k l u hu hQuadratic hEnergy
    have hEq := predictable_censor_compensator failureLaw censorLaw hazard
      hFailure hHazard (fun s x => H s x * subjectIntegralBefore hazard H l s x)
      hPpred hPmeas k u hu hE (by
        convert hC using 1
        funext x
        apply integral_congr_ae
        filter_upwards [] with s
        ring)
    refine ⟨?_, ?_, ?_⟩
    · simpa [E, P] using hE
    · simpa [C] using hC
    · convert hEq using 1
      congr 1
      funext x
      apply integral_congr_ae
      filter_upwards [] with s
      ring
  have hi := hPair i j hij
  have hj := hPair j i (Ne.symm hij)
  have hPathi := subject_hazard_path_integrable_ae failureLaw censorLaw hazard
    hFailure hHazard H hMeasurable i u hu hQuadratic
  have hPathj := subject_hazard_path_integrable_ae failureLaw censorLaw hazard
    hFailure hHazard H hMeasurable j u hu hQuadratic
  have hCensori : ∀ᵐ x ∂μ, 0 ≤ (x i).2 := by
    have hC : ∀ᵐ c ∂censorLaw, 0 ≤ c :=
      (mem_ae_iff_prob_eq_one measurableSet_Ici).2 hHazard.1.2
    have hPair : ∀ᵐ z ∂failureLaw.prod censorLaw, 0 ≤ z.2 := by
      apply (Measure.ae_prod_iff_ae_ae
        (measurableSet_le measurable_const measurable_snd)).2
      filter_upwards [] with a
      exact hC
    unfold μ sampleLaw
    exact (Measure.tendsto_eval_ae_ae
      (μ := fun _ : Fin n => failureLaw.prod censorLaw) (i := i)) hPair
  have hCensorj : ∀ᵐ x ∂μ, 0 ≤ (x j).2 := by
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
  have hPath : ∀ᵐ x ∂μ,
      subjectIntegral hazard H i u x * subjectIntegral hazard H j u x =
        E i j x + E j i x - C i j x - C j i x := by
    filter_upwards [hPathi, hPathj, hCensori, hCensorj,
      distinct_censor_times_ae failureLaw censorLaw hazard hFailure hHazard
        i j hij] with x hpi hpj hci hcj hne
    simpa [E, P, C] using
      distinct_subject_integral_product_pathwise hazard H i j u hu x
        hci hcj hne hpi hpj
  have hRhs : Integrable (fun x => E i j x + E j i x - C i j x - C j i x) μ :=
    hProduct.congr hPath
  calc
    (∫ x, subjectIntegral hazard H i u x * subjectIntegral hazard H j u x ∂μ) =
        ∫ x, E i j x + E j i x - C i j x - C j i x ∂μ :=
      integral_congr_ae hPath
    _ = 0 := by
      change (∫ x, (E i j + E j i - C i j - C j i) x ∂μ) = 0
      rw [integral_sub' ((hi.1.add hj.1).sub hi.2.1) hj.2.1,
        integral_sub' (hi.1.add hj.1) hi.2.1,
        integral_add' hi.1 hj.1, hi.2.2, hj.2.2]
      ring

/-- Suppose subjects are drawn independently with [failure times following a nonnegative time
law](hyp:hFailure) and independent [censor times whose law has the given censor
hazard](hyp:hazard,hHazard), and let the integrand be [left predictable](hyp:hPredictable) and [jointly
measurable in time and sample](hyp:hMeasurable). For [a nonnegative horizon u](hyp:hu), [finite
expected quadratic energy](hyp:hQuadratic), and [an integrable predictable quadratic
energy](hyp:hEnergy), [the expected square of the integral against the sum of all compensated
censor counts up to u equals the expected predictable quadratic energy](goal). -/
theorem aggregate_integral_isometry {n : ℕ}
    (failureLaw censorLaw : Measure ℝ) (hazard : ℝ → ℝ)
    (hFailure : NonnegativeTimeLaw failureLaw)
    (hHazard : HasCensorHazard censorLaw hazard)
    (H : ℝ → Sample n → ℝ) (hPredictable : LeftPredictable H)
    (hMeasurable : Measurable (fun p : ℝ × Sample n => H p.1 p.2))
    (u : ℝ) (hu : 0 ≤ u)
    (hQuadratic : QuadraticEnergyFinite failureLaw censorLaw hazard H u)
    (hEnergy : Integrable (predictableEnergy hazard H u)
      (sampleLaw n failureLaw censorLaw)) :
    (∫ x : Sample n, (aggregateIntegral hazard H u x) ^ 2
      ∂sampleLaw n failureLaw censorLaw) =
    ∫ x : Sample n, predictableEnergy hazard H u x
      ∂sampleLaw n failureLaw censorLaw := by
  /- For each i, derive integrability of the subject energy by domination
     by `predictableEnergy`. Derive subject square integrability directly
     from the event-payoff and hazard-payoff squares; isometry by itself is
     only an equality of Bochner integrals. Cauchy--Schwarz gives products.
     Expand `(∑ i, subjectIntegral ... i)^2` as a double sum, interchange
     each finite sum with the expectation, and use the subject isometry on
     diagonal terms and `distinct_subject_integrals_orthogonal` elsewhere.
     The sum of subject energies is `predictableEnergy` by linearity of the
     time integral (pathwise almost everywhere integrability follows from
     the finite quadratic-energy hypothesis). -/
  classical
  let μ := sampleLaw n failureLaw censorLaw
  let J : Fin n → Sample n → ℝ := fun i x => subjectIntegral hazard H i u x
  let Q : Fin n → Sample n → ℝ := fun i x =>
    ∫ s in Set.Icc 0 u,
      (H s x) ^ 2 * hazard s * riskIndicator i s x ∂volume
  have hQ (i : Fin n) : Integrable (Q i) μ :=
    subject_energy_integrable failureLaw censorLaw hazard hFailure hHazard
      H hMeasurable i u hu hQuadratic hEnergy
  have hSquare (i : Fin n) : AEStronglyMeasurable (J i) μ ∧
      Integrable (fun x => (J i x) ^ 2) μ := by
    let E : Sample n → ℝ := fun x =>
      if (x i).2 ≤ u ∧ (x i).2 < (x i).1 then H (x i).2 x else 0
    let A : Sample n → ℝ := fun x =>
      ∫ s in Set.Icc 0 u, H s x * hazard s * riskIndicator i s x ∂volume
    have hEmeas : Measurable E := by
      have hc : Measurable (fun x : Sample n => (x i).2) := by fun_prop
      have hf : Measurable (fun x : Sample n => (x i).1) := by fun_prop
      exact (hMeasurable.comp (hc.prodMk measurable_id)).ite
        ((measurableSet_le hc measurable_const).inter (measurableSet_lt hc hf))
        measurable_const
    have hAmeas : Measurable A := by
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
    have hELp : MemLp E 2 μ :=
      (memLp_two_iff_integrable_sq hEmeas.aestronglyMeasurable).2
        (subject_event_payoff_square_integrable failureLaw censorLaw hazard
          hFailure hHazard H hPredictable hMeasurable i u hu hQuadratic hEnergy)
    have hALp : MemLp A 2 μ :=
      (memLp_two_iff_integrable_sq hAmeas.aestronglyMeasurable).2
        (subject_hazard_square_integrable failureLaw censorLaw hazard
          hFailure hHazard H hMeasurable i u hu hQuadratic)
    constructor
    · change AEStronglyMeasurable (E - A) μ
      exact (hEmeas.sub hAmeas).aestronglyMeasurable
    · simpa [J, subjectIntegral, E, A, Pi.sub_apply] using
        (hELp.sub hALp).integrable_sq
  have hProd (i j : Fin n) : Integrable (fun x => J i x * J j x) μ :=
    ((memLp_two_iff_integrable_sq (hSquare i).1).2 (hSquare i).2).integrable_mul
      ((memLp_two_iff_integrable_sq (hSquare j).1).2 (hSquare j).2)
  have hIso (i : Fin n) : (∫ x, (J i x) ^ 2 ∂μ) = ∫ x, Q i x ∂μ :=
    subject_integral_isometry failureLaw censorLaw hazard hFailure hHazard
      H hPredictable hMeasurable i u hu hQuadratic (hQ i)
  have hCross (i j : Fin n) (hij : i ≠ j) :
      (∫ x, J i x * J j x ∂μ) = 0 :=
    distinct_subject_integrals_orthogonal failureLaw censorLaw hazard
      hFailure hHazard H hPredictable hMeasurable i j hij u hu hQuadratic hEnergy
  have hEnergyPath : ∀ᵐ x ∂μ,
      IntegrableOn (fun s => (H s x) ^ 2 * hazard s *
        (∑ i : Fin n, riskIndicator i s x)) (Set.Icc 0 u) volume := by
    let e : Sample n → ℝ → ℝ := fun x s =>
      (H s x) ^ 2 * hazard s * (∑ i : Fin n, riskIndicator i s x)
    let ν := (volume : Measure ℝ).restrict (Set.Icc 0 u)
    have he_meas : Measurable (fun p : Sample n × ℝ => e p.1 p.2) := by
      have hrisk (i : Fin n) : Measurable (fun p : Sample n × ℝ =>
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
      exact (((hMeasurable.comp (measurable_snd.prodMk measurable_fst)).pow_const 2).mul
        (hHazard.2.1.comp measurable_snd)).mul
        (Finset.measurable_fun_sum _ (fun i _ => hrisk i))
    have he_nonneg (x : Sample n) (s : ℝ) : 0 ≤ e x s := by
      dsimp [e]
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (hHazard.2.2.1 s))
        (Finset.sum_nonneg (fun i _ => by unfold riskIndicator; split_ifs <;> norm_num))
    have he_inner_meas : Measurable (fun x => ∫⁻ s, ENNReal.ofReal (e x s) ∂ν) :=
      he_meas.ennreal_ofReal.lintegral_prod_right'
    have hfinite : (∫⁻ x, ∫⁻ s, ENNReal.ofReal (e x s) ∂ν ∂μ) ≠ ⊤ :=
      hQuadratic
    filter_upwards [ae_lt_top he_inner_meas hfinite] with x hx
    exact (lintegral_ofReal_ne_top_iff_integrable
      (he_meas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (Filter.Eventually.of_forall (he_nonneg x))).1 hx.ne
  have hQPath : ∀ᵐ x ∂μ, ∀ i : Fin n,
      IntegrableOn (fun s => (H s x) ^ 2 * hazard s * riskIndicator i s x)
        (Set.Icc 0 u) volume := by
    apply ae_all_iff.2
    intro i
    filter_upwards [hEnergyPath] with x hx
    have hmeas : Measurable (fun s => (H s x) ^ 2 * hazard s *
        riskIndicator i s x) := by
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
      exact ((hMeasurable.comp (measurable_id.prodMk measurable_const)).pow_const 2 |>.mul
        hHazard.2.1).mul hrisk
    exact hx.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall (fun s => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
        (mul_nonneg (sq_nonneg _) (hHazard.2.2.1 s)) (by
          unfold riskIndicator; split_ifs <;> norm_num))]
      exact mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (f := fun j : Fin n => riskIndicator j s x)
          (fun j hj => by unfold riskIndicator; split_ifs <;> norm_num)
          (Finset.mem_univ i))
        (mul_nonneg (sq_nonneg _) (hHazard.2.2.1 s))))
  have hEnergyEq : (fun x => ∑ i : Fin n, Q i x) =ᵐ[μ]
      predictableEnergy hazard H u := by
    filter_upwards [hQPath] with x hx
    simp only [Q, predictableEnergy]
    rw [← integral_finsetSum Finset.univ (fun i _ => hx i)]
    congr 1
    funext s
    rw [Finset.mul_sum]
  calc
    (∫ x : Sample n, (aggregateIntegral hazard H u x) ^ 2 ∂μ) =
        ∫ x : Sample n, ∑ i : Fin n, ∑ j : Fin n, J i x * J j x ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [aggregateIntegral, J, pow_two, Finset.sum_mul_sum]
    _ = ∑ i : Fin n, ∑ j : Fin n, ∫ x : Sample n, J i x * J j x ∂μ := by
      rw [integral_finsetSum Finset.univ (fun i _ =>
        integrable_finsetSum Finset.univ (fun j _ => hProd i j))]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum Finset.univ (fun j _ => hProd i j)]
    _ = ∑ i : Fin n, ∫ x : Sample n, Q i x ∂μ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single i]
      · simpa [pow_two] using hIso i
      · intro j _ hji
        exact hCross i j (Ne.symm hji)
      · simp
    _ = ∫ x : Sample n, predictableEnergy hazard H u x ∂μ := by
      rw [← integral_finsetSum Finset.univ (fun i _ => hQ i)]
      exact integral_congr_ae hEnergyEq

end Causalean.Stat.RecurrentEvent.CountingProcess
