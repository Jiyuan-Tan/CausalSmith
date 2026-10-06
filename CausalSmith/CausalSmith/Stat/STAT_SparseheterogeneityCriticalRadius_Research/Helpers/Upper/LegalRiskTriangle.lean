module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.FiniteTransport
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.TriangularCountRisk
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.PilotCountFibres

/-! Assembly of the legal count triangle into the unrestricted pair of
finite-Poisson samples. -/

@[expose] public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

private lemma measurable_jointPairCentered' {n : ℕ} (P : Law n) (k : Fin n) :
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
    simp only [FiniteSample.count, FiniteSample.points]
    simp_rw [Finset.sum_sub_distrib]
    simp
    ring]
  exact (hbase.comp measurable_snd).sub
    ((measurable_fst.mul
      ((measurable_of_countable (fun m : ℕ => (m : ℝ))).comp
        (measurable_finiteSample_count.comp measurable_snd.fst))).mul
      ((measurable_of_countable (fun m : ℕ => (m : ℝ))).comp
        (measurable_finiteSample_count.comp measurable_snd.snd)))

set_option maxHeartbeats 1000000 in
/-- The legal randomized count contribution is dominated by the unrestricted
finite-Poisson prefix experiment, while retaining the pilot statistic. -/
lemma randomizedPoissonLegalSqRisk_le_rawPrefix {n : ℕ} (M rho : ℝ)
    (P : KnownRadiusClass n M rho) :
    randomizedPoissonLegalSqRisk P.law M rho
        (DiscreteAteHeterogeneityFrontier.rawAteFormula P.law) ≤
      ∫ z : ℝ × (FiniteSample (SampleObs n) × FiniteSample (SampleObs n)),
        (clipM M (z.1 + ∑ k, prefixSelectedCorrection rho z.1 z.2 k) -
          DiscreteAteHeterogeneityFrontier.rawAteFormula P.law) ^ 2
        ∂((Measure.map (pilotTau n M)
            (DiscreteAteHeterogeneityFrontier.productLaw n P.law)).prod
          ((finitePoissonSampleLaw P.law.observedLaw
            (Real.toNNReal (blockMean n))).prod
           (finitePoissonSampleLaw P.law.observedLaw
            (Real.toNNReal (blockMean n))))) := by
  let mu := DiscreteAteHeterogeneityFrontier.productLaw n P.law
  let pi := Measure.map (pilotTau n M) mu
  let lam := Real.toNNReal (blockMean n)
  let target := DiscreteAteHeterogeneityFrontier.rawAteFormula P.law
  let L : ℝ × (FiniteSample (SampleObs n) × FiniteSample (SampleObs n)) → ℝ :=
    fun z => (clipM M (z.1 + ∑ k, prefixSelectedCorrection rho z.1 z.2 k) -
      target) ^ 2
  have hM : 0 ≤ M := le_trans zero_le_one P.M_ge_one
  have htarget := rawAte_mem_clip P
  have hL0 (z) : 0 ≤ L z := sq_nonneg _
  have hLle (z) : L z ≤ 4 * M ^ 2 := by
    have hc : clipM M (z.1 + ∑ k, prefixSelectedCorrection rho z.1 z.2 k) ∈
        Set.Icc (-M) M := by
      simp only [clipM, Set.mem_Icc]
      constructor
      · exact le_max_left _ _
      · exact max_le (by linarith) (min_le_left _ _)
    have ha : |clipM M (z.1 + ∑ k, prefixSelectedCorrection rho z.1 z.2 k) -
        target| ≤ 2 * M := by
      rw [abs_le]
      constructor <;> dsimp only [target] at * <;>
        linarith [hc.1, hc.2, htarget.1, htarget.2]
    dsimp only [L]
    calc
      _ = |clipM M (z.1 + ∑ k, prefixSelectedCorrection rho z.1 z.2 k) -
          target| ^ 2 := (sq_abs _).symm
      _ ≤ (2 * M) ^ 2 := (sq_le_sq₀ (abs_nonneg _)
        (mul_nonneg (by norm_num) hM)).2 ha
      _ = _ := by ring
  have hL : Measurable L := by
    unfold L
    have hsum : Measurable (fun z : ℝ ×
        (FiniteSample (SampleObs n) × FiniteSample (SampleObs n)) =>
        ∑ k, prefixSelectedCorrection rho z.1 z.2 k) := by
      apply Finset.measurable_sum Finset.univ
      intro k hk
      rw [show (fun z : ℝ ×
          (FiniteSample (SampleObs n) × FiniteSample (SampleObs n)) =>
          prefixSelectedCorrection rho z.1 z.2 k) = fun z =>
          transportSelectedCorrection P.law k z.1 rho
            (observedTransportVector z.2 k) by
        funext z
        exact prefixSelectedCorrection_eq_transport P.law rho z.1 z.2 k]
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
        · exact (measurable_jointPairCentered' P.law k).comp
            (measurable_fst.prodMk hout)
        · exact (measurable_of_countable (Function.uncurry
            (lightFactorialCoefficient n rho))).comp
            ((measurable_finiteSample_count.comp hout.fst).prodMk
              (measurable_finiteSample_count.comp hout.snd))
      · apply Measurable.mul
        · exact (measurable_jointPairCentered' P.law k).comp
            (measurable_fst.prodMk hout)
        · exact (measurable_of_countable (Function.uncurry
            (heavyCoefficient n))).comp
            ((measurable_finiteSample_count.comp hout.fst).prodMk
              (measurable_finiteSample_count.comp hout.snd))
    exact (((Causalean.Mathlib.Analysis.measurable_clipIcc (-M) M).comp
      (measurable_fst.add hsum)).sub measurable_const).pow_const 2
  have hbound (sample : Fin n → SampleObs n) (z : ℕ × ℕ) :
      |(conditionalEstimator n M rho sample z.1 z.2 - target) ^ 2| ≤
        4 * M ^ 2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    have hc := conditionalEstimator_range n M rho hM sample z.1 z.2
    have ha : |conditionalEstimator n M rho sample z.1 z.2 - target| ≤ 2 * M := by
      rw [abs_le]
      dsimp only [target] at *
      constructor <;> linarith [hc.1, hc.2, htarget.1, htarget.2]
    calc
      _ = |conditionalEstimator n M rho sample z.1 z.2 - target| ^ 2 :=
        (sq_abs _).symm
      _ ≤ (2 * M) ^ 2 := (sq_le_sq₀ (abs_nonneg _)
        (mul_nonneg (by norm_num) hM)).2 ha
      _ = _ := by ring
  have hpoint (sample : Fin n → SampleObs n) :
      (∫ z : ℕ × ℕ,
        if z.1 + z.2 ≤ postPilotSize n then
          (conditionalEstimator n M rho sample z.1 z.2 - target) ^ 2 else 0
        ∂poissonCountLaw n) =
      ∑ u ∈ Finset.range (postPilotSize n + 1),
        ∑ v ∈ Finset.range (postPilotSize n - u + 1),
          poissonWeight n u v *
            (conditionalEstimator n M rho sample u v - target) ^ 2 := by
    simpa only [poissonCountLaw, sub_zero] using
      triangularPoisson_correction_integral n
        (fun z => (conditionalEstimator n M rho sample z.1 z.2 - target) ^ 2)
        0 (4 * M ^ 2) (hbound sample)
  have houterInt : Integrable (fun w : (Fin n → SampleObs n) × (ℕ × ℕ) =>
      if w.2.1 + w.2.2 ≤ postPilotSize n then
        (conditionalEstimator n M rho w.1 w.2.1 w.2.2 - target) ^ 2 else 0)
      (mu.prod (poissonCountLaw n)) := by
    have hmeas : Measurable (fun w : (Fin n → SampleObs n) × (ℕ × ℕ) =>
        if w.2.1 + w.2.2 ≤ postPilotSize n then
          (conditionalEstimator n M rho w.1 w.2.1 w.2.2 - target) ^ 2 else 0) := by
      apply measurable_from_prod_countable_left
      intro z
      change Measurable (fun x : Fin n → SampleObs n =>
        if z.1 + z.2 ≤ postPilotSize n then
          (conditionalEstimator n M rho x z.1 z.2 - target) ^ 2 else 0)
      split_ifs
      · exact ((conditionalEstimator_measurable n M rho z.1 z.2).sub
          measurable_const).pow_const 2
      · exact measurable_const
    apply Integrable.of_bound
    · exact hmeas.aestronglyMeasurable
    · filter_upwards with w
      split_ifs
      · simpa [Real.norm_eq_abs] using hbound w.1 w.2
      · simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (sq_nonneg M)
  rw [show randomizedPoissonLegalSqRisk P.law M rho target =
      ∫ sample, ∫ z,
        (if z.1 + z.2 ≤ postPilotSize n then
          (conditionalEstimator n M rho sample z.1 z.2 - target) ^ 2 else 0)
        ∂poissonCountLaw n ∂mu by
    unfold randomizedPoissonLegalSqRisk
    exact integral_prod _ houterInt]
  simp_rw [hpoint]
  rw [integral_finsetSum]
  · have hrawInt : Integrable L (pi.prod
        ((finitePoissonSampleLaw P.law.observedLaw lam).prod
          (finitePoissonSampleLaw P.law.observedLaw lam))) := by
      apply Integrable.of_bound hL.aestronglyMeasurable (4 * M ^ 2)
      filter_upwards with z
      rw [Real.norm_eq_abs, abs_of_nonneg (hL0 z)]
      exact hLle z
    have hterm (u v : ℕ) (huv : u + v ≤ postPilotSize n) :
        (∫ sample, poissonWeight n u v *
          (conditionalEstimator n M rho sample u v - target) ^ 2 ∂mu) =
        ∫ z, L z ∂pi.prod
          (((finitePoissonSampleLaw P.law.observedLaw lam).restrict
            (FiniteSample.count ⁻¹' ({u} : Set ℕ))).prod
           ((finitePoissonSampleLaw P.law.observedLaw lam).restrict
            (FiniteSample.count ⁻¹' ({v} : Set ℕ)))) := by
      rw [integral_const_mul]
      have hcond : (fun sample =>
          (conditionalEstimator n M rho sample u v - target) ^ 2) =
          fun sample => L (pilotTau n M sample,
            fixedPrefixSamples n u v huv sample) := by
        funext sample
        rw [conditionalEstimator_eq_prefixSelectedCorrection_sum huv M rho sample]
      rw [hcond]
      let G := fun sample : Fin n → SampleObs n =>
        (pilotTau n M sample, fixedPrefixSamples n u v huv sample)
      have hG : Measurable G :=
        (pilotTau_measurable n M).prodMk (measurable_fixedPrefixSamples n u v huv)
      rw [← integral_map hG.aemeasurable hL.aestronglyMeasurable]
      have hw := poissonWeight_eq_product_singletons n u v
      rw [hw]
      change (poissonMeasure lam {u}).toReal *
          (poissonMeasure lam {v}).toReal * (∫ y, L y ∂Measure.map G mu) = _
      rw [← ENNReal.toReal_mul]
      change (poissonMeasure lam {u} * poissonMeasure lam {v}).toReal •
        (∫ y, L y ∂Measure.map G mu) = _
      rw [← integral_smul_measure]
      unfold G
      rw [smul_map_pilotTau_fixedPrefixSamples_eq_countFibres M P.law lam huv rfl]
    have hdouble :
        (∑ u ∈ Finset.range (postPilotSize n + 1),
          ∫ sample, ∑ v ∈ Finset.range (postPilotSize n - u + 1),
            poissonWeight n u v *
              (conditionalEstimator n M rho sample u v - target) ^ 2 ∂mu) =
        ∑ u ∈ Finset.range (postPilotSize n + 1),
          ∑ v ∈ Finset.range (postPilotSize n - u + 1),
            ∫ z, L z ∂pi.prod
              (((finitePoissonSampleLaw P.law.observedLaw lam).restrict
                (FiniteSample.count ⁻¹' ({u} : Set ℕ))).prod
               ((finitePoissonSampleLaw P.law.observedLaw lam).restrict
                (FiniteSample.count ⁻¹' ({v} : Set ℕ)))) := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro v hv
        have hu' : u ≤ postPilotSize n := by
          rw [Finset.mem_range, Nat.lt_succ_iff] at hu
          exact hu
        have hv' : v ≤ postPilotSize n - u := by
          rw [Finset.mem_range, Nat.lt_succ_iff] at hv
          exact hv
        exact hterm u v (by omega)
      · intro v hv
        exact (Integrable.of_bound
          (((conditionalEstimator_measurable n M rho u v).sub
            measurable_const).pow_const 2).aestronglyMeasurable
          (4 * M ^ 2) (Filter.Eventually.of_forall fun sample => by
            simpa [Real.norm_eq_abs] using hbound sample (u, v))).const_mul _
    rw [hdouble]
    exact triangular_finiteSample_countFibre_integral_le pi
      (finitePoissonSampleLaw P.law.observedLaw lam) L hrawInt hL0
  · intro u hu
    exact integrable_finset_sum _ fun v hv =>
      (Integrable.of_bound
        (((conditionalEstimator_measurable n M rho u v).sub
          measurable_const).pow_const 2).aestronglyMeasurable
        (4 * M ^ 2) (Filter.Eventually.of_forall fun sample => by
          simpa [Real.norm_eq_abs] using hbound sample (u, v))).const_mul _

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
