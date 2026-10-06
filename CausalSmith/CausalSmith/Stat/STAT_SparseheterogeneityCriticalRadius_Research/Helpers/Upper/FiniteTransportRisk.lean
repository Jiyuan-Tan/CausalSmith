module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.FiniteTransport
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.LegalRiskTriangle
public import Causalean.Mathlib.Probability.Poisson.PairSecondMoment.Mixture

/-! Risk comparison between the legal randomized fibres and the ideal Poisson experiment. -/

@[expose] public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

private lemma measurable_jointPairCentered {n : ℕ} (P : Law n) (k : Fin n) :
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

noncomputable def clippedPrefixLoss {n : ℕ} (_P : Law n)
    (M rho tau : ℝ)
    (z : ℝ × (FiniteSample (SampleObs n) × FiniteSample (SampleObs n))) : ℝ :=
  (clipM M (z.1 + ∑ k, prefixSelectedCorrection rho z.1 z.2 k) - tau) ^ 2

set_option maxHeartbeats 800000 in
-- Expanding joint measurability through the finite-sample correction needs extra elaboration time.
private lemma measurable_clippedPrefixLoss {n : ℕ} (P : Law n)
    (M rho tau : ℝ) : Measurable (clippedPrefixLoss P M rho tau) := by
  unfold clippedPrefixLoss
  have hsum : Measurable (fun z : ℝ ×
      (FiniteSample (SampleObs n) × FiniteSample (SampleObs n)) =>
      ∑ k, prefixSelectedCorrection rho z.1 z.2 k) := by
    apply Finset.measurable_sum Finset.univ
    intro k hk
    rw [show (fun z : ℝ ×
        (FiniteSample (SampleObs n) × FiniteSample (SampleObs n)) =>
        prefixSelectedCorrection rho z.1 z.2 k) = fun z =>
        transportSelectedCorrection P k z.1 rho
          (observedTransportVector z.2 k) by
      funext z
      exact prefixSelectedCorrection_eq_transport P rho z.1 z.2 k]
    unfold transportSelectedCorrection idealLightCorrection idealHeavyCorrection
    have hout : Measurable (fun z : ℝ ×
        (FiniteSample (SampleObs n) × FiniteSample (SampleObs n)) =>
        (observedTransportVector z.2 k).2) :=
      (measurable_pi_apply k).snd.comp
        ((measurable_observedTransportVector n).comp measurable_snd)
    apply Measurable.ite
    · exact measurableSet_le
        ((measurable_finiteSampleCellCount k).comp measurable_snd.fst)
        measurable_const
    · apply Measurable.mul
      · exact (measurable_jointPairCentered P k).comp
          (measurable_fst.prodMk hout)
      · exact (measurable_of_countable (Function.uncurry
          (lightFactorialCoefficient n rho))).comp
          ((measurable_finiteSample_count.comp hout.fst).prodMk
            (measurable_finiteSample_count.comp hout.snd))
    · apply Measurable.mul
      · exact (measurable_jointPairCentered P k).comp
          (measurable_fst.prodMk hout)
      · exact (measurable_of_countable (Function.uncurry
          (heavyCoefficient n))).comp
          ((measurable_finiteSample_count.comp hout.fst).prodMk
            (measurable_finiteSample_count.comp hout.snd))
  exact (((Causalean.Mathlib.Analysis.measurable_clipIcc (-M) M).comp
    (measurable_fst.add hsum)).sub measurable_const).pow_const 2

private lemma clippedPrefixLoss_nonneg {n : ℕ} (P : Law n)
    (M rho tau : ℝ)
    (z : ℝ × (FiniteSample (SampleObs n) × FiniteSample (SampleObs n))) :
    0 ≤ clippedPrefixLoss P M rho tau z := sq_nonneg _

private lemma clippedPrefixLoss_le {n : ℕ} (M rho : ℝ)
    (P : KnownRadiusClass n M rho)
    (z : ℝ × (FiniteSample (SampleObs n) × FiniteSample (SampleObs n))) :
    clippedPrefixLoss P.law M rho
      (DiscreteAteHeterogeneityFrontier.rawAteFormula P.law) z ≤ 4 * M ^ 2 := by
  have hM : 0 ≤ M := le_trans zero_le_one P.M_ge_one
  have hc : clipM M (z.1 + ∑ k, prefixSelectedCorrection rho z.1 z.2 k) ∈
      Set.Icc (-M) M := by
    simp only [clipM, Set.mem_Icc]
    constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left _ _)
  have ht := rawAte_mem_clip P
  have ha : |clipM M (z.1 + ∑ k, prefixSelectedCorrection rho z.1 z.2 k) -
      DiscreteAteHeterogeneityFrontier.rawAteFormula P.law| ≤ 2 * M := by
    rw [abs_le]
    constructor <;> linarith [hc.1, hc.2, ht.1, ht.2]
  unfold clippedPrefixLoss
  calc
    _ = |clipM M (z.1 + ∑ k, prefixSelectedCorrection rho z.1 z.2 k) -
        DiscreteAteHeterogeneityFrontier.rawAteFormula P.law| ^ 2 := (sq_abs _).symm
    _ ≤ (2 * M) ^ 2 := (sq_le_sq₀ (abs_nonneg _)
      (mul_nonneg (by norm_num) hM)).2 ha
    _ = _ := by ring

/-- The legal randomized count fibres are bounded by the unrestricted raw
finite-Poisson prefix experiment, while retaining the independent pilot. -/
lemma randomizedPoissonLegalSqRisk_le_rawPoissonPilot {n : ℕ} (M rho : ℝ)
    (P : KnownRadiusClass n M rho) :
    randomizedPoissonLegalSqRisk P.law M rho
        (DiscreteAteHeterogeneityFrontier.rawAteFormula P.law) ≤
      ∫ z : ℝ × (FiniteSample (SampleObs n) × FiniteSample (SampleObs n)),
        clippedPrefixLoss P.law M rho
          (DiscreteAteHeterogeneityFrontier.rawAteFormula P.law) z
        ∂((Measure.map (pilotTau n M)
            (DiscreteAteHeterogeneityFrontier.productLaw n P.law)).prod
          ((finitePoissonSampleLaw P.law.observedLaw
            (Real.toNNReal (blockMean n))).prod
           (finitePoissonSampleLaw P.law.observedLaw
            (Real.toNNReal (blockMean n))))) := by
  simpa only [clippedPrefixLoss] using
    randomizedPoissonLegalSqRisk_le_rawPrefix M rho P

/-- The legal randomized squared risk is no larger than the pilot-integrated
ideal-product clipped risk. -/
lemma randomizedPoissonLegalSqRisk_le_idealProduct {n : ℕ} (M rho : ℝ)
    (P : KnownRadiusClass n M rho) :
    randomizedPoissonLegalSqRisk P.law M rho
        (DiscreteAteHeterogeneityFrontier.rawAteFormula P.law) ≤
      ∫ sample : Fin n → SampleObs n,
        ∫ q : Fin n → IdealCellSample n,
          (clipM M (pilotTau n M sample +
              ∑ k, idealSelectedCorrection P.law k (pilotTau n M sample) rho (q k)) -
            DiscreteAteHeterogeneityFrontier.rawAteFormula P.law) ^ 2
          ∂idealProductLaw P.law
        ∂DiscreteAteHeterogeneityFrontier.productLaw n P.law := by
  refine (randomizedPoissonLegalSqRisk_le_rawPoissonPilot M rho P).trans_eq ?_
  let mu := DiscreteAteHeterogeneityFrontier.productLaw n P.law
  let pi := Measure.map (pilotTau n M) mu
  let raw := (finitePoissonSampleLaw P.law.observedLaw
      (Real.toNNReal (blockMean n))).prod
    (finitePoissonSampleLaw P.law.observedLaw
      (Real.toNNReal (blockMean n)))
  let target := DiscreteAteHeterogeneityFrontier.rawAteFormula P.law
  let L : ℝ × (FiniteSample (SampleObs n) × FiniteSample (SampleObs n)) → ℝ :=
    clippedPrefixLoss P.law M rho target
  have hL : Integrable L (pi.prod raw) := by
    apply Integrable.of_bound
      (measurable_clippedPrefixLoss P.law M rho target).aestronglyMeasurable
      (4 * M ^ 2)
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (clippedPrefixLoss_nonneg
      P.law M rho target z)]
    exact clippedPrefixLoss_le M rho P z
  have hG : Integrable (fun t => ∫ p, L (t, p) ∂raw) pi :=
    hL.integral_prod_left
  calc
    (∫ z, clippedPrefixLoss P.law M rho target z ∂pi.prod raw) =
        ∫ t, ∫ p, L (t, p) ∂raw ∂pi := by
      exact integral_prod L hL
    _ = ∫ sample : Fin n → SampleObs n,
        (∫ p, L (pilotTau n M sample, p) ∂raw) ∂mu := by
      rw [show pi = Measure.map (pilotTau n M) mu by rfl]
      exact integral_map (pilotTau_measurable n M).aemeasurable
        hG.aestronglyMeasurable
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with sample
      simpa only [L, raw, target, clippedPrefixLoss] using
        rawPoisson_clippedRisk_eq_idealProduct P.law P.overlap M rho
          (pilotTau n M sample) target

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
