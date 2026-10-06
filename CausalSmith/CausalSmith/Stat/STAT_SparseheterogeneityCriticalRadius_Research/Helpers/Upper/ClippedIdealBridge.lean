module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.FiniteTransportRisk

/-! Removal of clipping and zero-mass ideal-cell artifacts in the upper-risk transport. -/

@[expose] public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

lemma idealSelectedCorrection_ae_eq_idealCellStatistic {n : ℕ} (P : Law n)
    (k : Fin n) (t rho : ℝ) :
    idealSelectedCorrection P k t rho =ᵐ[idealCellLaw P k]
      idealCellStatistic P k t rho := by
  by_cases hp : 0 < P.cellMass k
  · filter_upwards with q
    simp [idealCellStatistic, hp]
  · have hp0 : P.cellMass k = 0 :=
      le_antisymm (le_of_not_gt hp) (P.cellMass_range k).1
    have harm (u : Bool) : armMass P u k = 0 := by simp [armMass, hp0]
    have hrate (u : Bool) :
        Real.toNNReal (blockMean n * armMass P u k) = 0 := by simp [harm]
    have houtcome : ∀ᵐ q ∂cellOutcomePoissonLaw P k,
        idealLightCorrection P k t rho q = 0 ∧
          idealHeavyCorrection P k t q = 0 := by
      letI : IsProbabilityMeasure (P.outcomeLaw false k) :=
        P.outcome_isProbability false k
      letI : IsProbabilityMeasure (P.outcomeLaw true k) :=
        P.outcome_isProbability true k
      unfold cellOutcomePoissonLaw
      rw [hrate false, hrate true]
      apply (Measure.ae_prod_iff_ae_ae
        ((measurableSet_eq_fun (measurable_idealLightCorrection P k t rho)
          measurable_const).inter
        (measurableSet_eq_fun (measurable_idealHeavyCorrection P k t)
          measurable_const))).2
      filter_upwards [finitePoissonSample_count_ae_zero (P.outcomeLaw false k)]
        with q0 hq0
      filter_upwards [finitePoissonSample_count_ae_zero (P.outcomeLaw true k)]
        with q1 hq1
      constructor
      · change idealLightCorrection P k t rho (q0, q1) = 0
        unfold idealLightCorrection
        rw [show lightFactorialCoefficient n rho q0.count q1.count = 0 by
          simp [lightFactorialCoefficient, hq0, hq1]]
        simp
      · change idealHeavyCorrection P k t (q0, q1) = 0
        unfold idealHeavyCorrection
        rw [show heavyCoefficient n q0.count q1.count = 0 by
          simp [heavyCoefficient, hq0, hq1]]
        simp
    have hprod : ∀ᵐ q ∂idealCellLaw P k,
        idealLightCorrection P k t rho q.2 = 0 ∧
          idealHeavyCorrection P k t q.2 = 0 := by
      unfold idealCellLaw
      exact Measure.quasiMeasurePreserving_snd.ae houtcome
    filter_upwards [hprod] with q hq
    unfold idealSelectedCorrection
    split_ifs <;> simp [idealCellStatistic, hp, hq.1, hq.2]

lemma idealSelected_sum_ae_eq_idealCellStatistic_sum {n : ℕ} (P : Law n)
    (t rho : ℝ) :
    (fun q : Fin n → IdealCellSample n =>
      ∑ k, idealSelectedCorrection P k t rho (q k)) =ᵐ[idealProductLaw P]
    (fun q => ∑ k, idealCellStatistic P k t rho (q k)) := by
  have hk (k : Fin n) :
      (fun q : Fin n → IdealCellSample n =>
        idealSelectedCorrection P k t rho (q k)) =ᵐ[idealProductLaw P]
      (fun q => idealCellStatistic P k t rho (q k)) := by
    exact (measurePreserving_eval (fun j => idealCellLaw P j) k).quasiMeasurePreserving.ae
      (idealSelectedCorrection_ae_eq_idealCellStatistic P k t rho)
  have hall : ∀ᵐ q ∂idealProductLaw P, ∀ k, k ∈ (Finset.univ : Finset (Fin n)) →
      idealSelectedCorrection P k t rho (q k) =
        idealCellStatistic P k t rho (q k) := by
    induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
    | empty => simp
    | @insert k s hks ih =>
        filter_upwards [ih, hk k] with q hi hkq
        intro j hj
        simp only [Finset.mem_insert] at hj
        rcases hj with rfl | hj
        · exact hkq
        · exact hi j hj
  filter_upwards [hall] with q hq
  apply Finset.sum_congr rfl
  intro k hk'
  exact hq k hk'

private lemma measurable_jointPairCentered_bridge {n : ℕ} (P : Law n) (k : Fin n) :
    Measurable (fun z : ℝ × (FiniteSample ℝ × FiniteSample ℝ) =>
      Causalean.Mathlib.Probability.Poisson.PairSecondMoment.pairSum
        (centeredNumeratorKernel P k z.1) z.2.1 z.2.2) := by
  let base : FiniteSample ℝ × FiniteSample ℝ → ℝ := fun p =>
    Causalean.Mathlib.Probability.Poisson.PairSecondMoment.pairSum
      (fun x y : ℝ => y - x) p.1 p.2
  have hbase : Measurable base :=
    Causalean.Mathlib.Probability.Poisson.PairSecondMoment.measurable_pairSum
      (fun x y : ℝ => y - x) (measurable_snd.sub measurable_fst)
  rw [show (fun z : ℝ × (FiniteSample ℝ × FiniteSample ℝ) =>
      Causalean.Mathlib.Probability.Poisson.PairSecondMoment.pairSum
        (centeredNumeratorKernel P k z.1) z.2.1 z.2.2) = fun z =>
      base z.2 - z.1 * (z.2.1.count : ℝ) * (z.2.2.count : ℝ) by
    funext z
    rcases z with ⟨t, ⟨⟨m, x⟩, ⟨r, y⟩⟩⟩
    unfold base Causalean.Mathlib.Probability.Poisson.PairSecondMoment.pairSum
      centeredNumeratorKernel
    simp only [FiniteSample.count]
    simp_rw [Finset.sum_sub_distrib]
    simp
    ring]
  exact (hbase.comp measurable_snd).sub
    ((measurable_fst.mul
      ((measurable_of_countable (fun m : ℕ => (m : ℝ))).comp
        (measurable_finiteSample_count.comp measurable_snd.fst))).mul
      ((measurable_of_countable (fun m : ℕ => (m : ℝ))).comp
        (measurable_finiteSample_count.comp measurable_snd.snd)))

private lemma measurable_jointIdealCellStatistic {n : ℕ} (P : Law n)
    (k : Fin n) (rho : ℝ) :
    Measurable (fun z : ℝ × IdealCellSample n =>
      idealCellStatistic P k z.1 rho z.2) := by
  unfold idealCellStatistic
  by_cases hp : 0 < P.cellMass k
  · simp only [if_pos hp]
    unfold idealSelectedCorrection idealLightCorrection idealHeavyCorrection
    have hout : Measurable (fun z : ℝ × IdealCellSample n => z.2.2) :=
      measurable_snd.snd
    apply Measurable.ite
    · exact measurableSet_le
        ((measurable_finiteSampleCellCount k).comp measurable_snd.fst) measurable_const
    · apply Measurable.mul
      · exact (measurable_jointPairCentered_bridge P k).comp
          (measurable_fst.prodMk hout)
      · exact (measurable_of_countable (Function.uncurry
          (lightFactorialCoefficient n rho))).comp
          ((measurable_finiteSample_count.comp hout.fst).prodMk
            (measurable_finiteSample_count.comp hout.snd))
    · apply Measurable.mul
      · exact (measurable_jointPairCentered_bridge P k).comp
          (measurable_fst.prodMk hout)
      · exact (measurable_of_countable (Function.uncurry
          (heavyCoefficient n))).comp
          ((measurable_finiteSample_count.comp hout.fst).prodMk
            (measurable_finiteSample_count.comp hout.snd))
  · simp only [if_neg hp]
    exact measurable_const

/-- The transported clipped ideal risk is bounded by the guarded unprojected
ideal risk used by the independent-cell aggregation theorem. -/
lemma clippedIdeal_pilot_sqRisk_le_guarded {n : ℕ} (M rho : ℝ)
    (P : KnownRadiusClass n M rho) :
    (∫ sample : Fin n → SampleObs n,
      ∫ q : Fin n → IdealCellSample n,
        (clipM M (pilotTau n M sample +
            ∑ k, idealSelectedCorrection P.law k (pilotTau n M sample) rho (q k)) -
          DiscreteAteHeterogeneityFrontier.rawAteFormula P.law) ^ 2
        ∂idealProductLaw P.law
      ∂DiscreteAteHeterogeneityFrontier.productLaw n P.law) ≤
    ∫ sample : Fin n → SampleObs n,
      ∫ q : Fin n → IdealCellSample n,
        (pilotTau n M sample +
            ∑ k, idealCellStatistic P.law k (pilotTau n M sample) rho (q k) -
          DiscreteAteHeterogeneityFrontier.rawAteFormula P.law) ^ 2
      ∂idealProductLaw P.law
      ∂DiscreteAteHeterogeneityFrontier.productLaw n P.law := by
  let μ := DiscreteAteHeterogeneityFrontier.productLaw n P.law
  let target := DiscreteAteHeterogeneityFrontier.rawAteFormula P.law
  let V := 3 * (2000000 * M ^ 2 * auditConstant ^ degree n rho *
    (degree n rho : ℝ) ^ 4 / n)
  let B := 2 * 196612 ^ 2 / (degree n rho : ℝ) ^ 2
  have hM : 0 ≤ M := le_trans zero_le_one P.M_ge_one
  have hguardedMeas : Measurable (fun z :
      (Fin n → SampleObs n) × (Fin n → IdealCellSample n) =>
      (pilotTau n M z.1 +
        ∑ k, idealCellStatistic P.law k (pilotTau n M z.1) rho (z.2 k) -
        target) ^ 2) := by
    have hsum : Measurable (fun z :
        (Fin n → SampleObs n) × (Fin n → IdealCellSample n) =>
        ∑ k, idealCellStatistic P.law k (pilotTau n M z.1) rho (z.2 k)) := by
      apply Finset.measurable_sum Finset.univ
      intro k hk
      exact (measurable_jointIdealCellStatistic P.law k rho).comp
        (((pilotTau_measurable n M).comp measurable_fst).prodMk
          ((measurable_pi_apply k).comp measurable_snd))
    exact ((((pilotTau_measurable n M).comp measurable_fst).add hsum).sub
      measurable_const).pow_const 2
  have hinnerMeas : StronglyMeasurable (fun sample : Fin n → SampleObs n =>
      ∫ q : Fin n → IdealCellSample n,
        (pilotTau n M sample +
          ∑ k, idealCellStatistic P.law k (pilotTau n M sample) rho (q k) -
          target) ^ 2 ∂idealProductLaw P.law) :=
    hguardedMeas.stronglyMeasurable.integral_prod_right'
  have hresMeas : StronglyMeasurable (fun sample : Fin n → SampleObs n =>
      (target - pilotTau n M sample) ^ 2) :=
    ((measurable_const.sub (pilotTau_measurable n M)).pow_const 2).stronglyMeasurable
  have hresInt : Integrable (fun sample : Fin n → SampleObs n =>
      (target - pilotTau n M sample) ^ 2) μ := by
    apply Integrable.of_bound hresMeas.aestronglyMeasurable ((2 * M) ^ 2)
    filter_upwards with sample
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have ht := rawAte_mem_clip P
    have hp := pilotTau_range n M hM sample
    have habs : |target - pilotTau n M sample| ≤ 2 * M := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2, hp.1, hp.2]
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (target - pilotTau n M sample))
        (mul_nonneg (by norm_num) hM)).2 habs
  have hEnvelopeInt : Integrable (fun sample : Fin n → SampleObs n =>
      V + B * (M ^ 2 * rho ^ 2 + (target - pilotTau n M sample) ^ 2)) μ := by
    have hsum : Integrable (fun sample : Fin n → SampleObs n =>
        M ^ 2 * rho ^ 2 + (target - pilotTau n M sample) ^ 2) μ :=
      (integrable_const (M ^ 2 * rho ^ 2)).add hresInt
    exact (integrable_const V).add (hsum.const_mul B)
  have hGuardedInt : Integrable (fun sample : Fin n → SampleObs n =>
      ∫ q : Fin n → IdealCellSample n,
        (pilotTau n M sample +
          ∑ k, idealCellStatistic P.law k (pilotTau n M sample) rho (q k) -
          target) ^ 2 ∂idealProductLaw P.law) μ := by
    apply hEnvelopeInt.mono' hinnerMeas.aestronglyMeasurable
    filter_upwards with sample
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun q => sq_nonneg _)]
    simpa only [V, B, target] using
      idealProduct_sqRisk_le M rho (pilotTau n M sample) P
        (pilotTau_range n M hM sample)
  apply integral_mono_of_nonneg
  · filter_upwards with sample
    exact integral_nonneg fun q => sq_nonneg _
  · simpa only [μ, target] using hGuardedInt
  · filter_upwards with sample
    let t := pilotTau n M sample
    have hsum := idealSelected_sum_ae_eq_idealCellStatistic_sum P.law t rho
    apply integral_mono_of_nonneg
    · filter_upwards with q
      exact sq_nonneg _
    · have hstatLp (k : Fin n) : MemLp
          (fun q : Fin n → IdealCellSample n =>
            idealCellStatistic P.law k t rho (q k)) 2 (idealProductLaw P.law) :=
        (idealCellStatistic_memLp_two M rho P.law k t
          (lt_of_lt_of_le (by norm_num) P.n_ge_three) P.mean_envelope
          P.variance_envelope (pilotTau_range n M
            (le_trans zero_le_one P.M_ge_one) sample)).comp_measurePreserving
          (measurePreserving_eval (fun j => idealCellLaw P.law j) k)
      have hsumLp : MemLp (fun q : Fin n → IdealCellSample n =>
          ∑ k, idealCellStatistic P.law k t rho (q k)) 2 (idealProductLaw P.law) :=
        memLp_finsetSum Finset.univ (fun k hk => hstatLp k)
      exact (((memLp_const t).add hsumLp).sub
        (memLp_const (DiscreteAteHeterogeneityFrontier.rawAteFormula P.law))).integrable_sq
    · filter_upwards [hsum] with q hq
      rw [hq]
      simpa [clipM, Causalean.Mathlib.Analysis.clipIcc] using
        Causalean.Mathlib.Analysis.clipIcc_sub_sq_le (rawAte_mem_clip P)
          (t + ∑ k, idealCellStatistic P.law k t rho (q k))

/-- The implemented estimator is bounded by the guarded ideal-product risk
plus the exact geometric cap-tail contribution. -/
lemma knownRadiusEstimator_sqRisk_le_idealProduct_add_geometric {n : ℕ}
    (M rho : ℝ) (P : KnownRadiusClass n M rho) :
    Causalean.Stat.sqRisk
        (DiscreteAteHeterogeneityFrontier.productLaw n P.law)
        (knownRadiusEstimator n M rho)
        (DiscreteAteHeterogeneityFrontier.rawAteFormula P.law) ≤
      (∫ sample : Fin n → SampleObs n,
        ∫ q : Fin n → IdealCellSample n,
          (pilotTau n M sample +
              ∑ k, idealCellStatistic P.law k (pilotTau n M sample) rho (q k) -
            DiscreteAteHeterogeneityFrontier.rawAteFormula P.law) ^ 2
          ∂idealProductLaw P.law
        ∂DiscreteAteHeterogeneityFrontier.productLaw n P.law) +
      4 * M ^ 2 * (Real.exp 1 / 4) ^ (postPilotSize n / 2) := by
  refine (knownRadiusEstimator_sqRisk_le_legal_add_geometric M rho P).trans ?_
  gcongr
  exact (randomizedPoissonLegalSqRisk_le_idealProduct M rho P).trans
    (clippedIdeal_pilot_sqRisk_le_guarded M rho P)

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
