module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.HybridThreePoolRaoBlackwell
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.PairedHistogram
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.PairedHistogram.Risk
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.Depoissonization
public import Causalean.Stat.Concentration.Poisson.SelfNormalized.Chernoff

/-! Transfer of the Poisson hybrid to the fixed two-sample experiment. -/

public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

open MeasureTheory ProbabilityTheory Causalean.Stat
open Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix.FiniteFamily

private lemma poisson_eighth_tail (N : Nat) (hN : 0 < N) :
    (poissonMeasure (Real.toNNReal ((N : Real) / 8))).real (Set.Ioi N) ≤
      8 / (N : Real) := by
  have hNR : 0 < (N : Real) := by exact_mod_cast hN
  have hlam : Real.toNNReal ((N : Real) / 8) = (N : NNReal) / 8 := by
    ext
    simp [show 0 ≤ (N : Real) / 8 by positivity]
  rw [hlam]
  have hsqrt : Real.sqrt
      (2 * ((((N : NNReal) / 8 : NNReal) : Real)) * ((N : Real) / 4)) =
      (N : Real) / 4 := by
    rw [show 2 * ((((N : NNReal) / 8 : NNReal) : Real)) * ((N : Real) / 4) =
        ((N : Real) / 4) ^ 2 by norm_num; ring]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]
    positivity
  have hsubset : Set.Ioi N ⊆
      {w : Nat | (w : Real) - ((((N : NNReal) / 8 : NNReal) : Real)) >
        Real.sqrt
          (2 * ((((N : NNReal) / 8 : NNReal) : Real)) * ((N : Real) / 4)) +
        2 * ((N : Real) / 4)} := by
    intro w hw
    simp only [Set.mem_Ioi] at hw ⊢
    have hwR : (N : Real) < w := by exact_mod_cast hw
    rw [hsqrt]
    norm_num
    linarith
  have hbern := Causalean.Stat.Concentration.PoissonSelfNormalized.poisson_upper_bernstein
    ((N : NNReal) / 8) (z := (N : Real) / 4) (by positivity)
  have hmono : poissonMeasure ((N : NNReal) / 8) (Set.Ioi N) ≤
      poissonMeasure ((N : NNReal) / 8)
        {w : Nat | (w : Real) - ((((N : NNReal) / 8 : NNReal) : Real)) >
          Real.sqrt
              (2 * ((((N : NNReal) / 8 : NNReal) : Real)) * ((N : Real) / 4)) +
            2 * ((N : Real) / 4)} := measure_mono hsubset
  have hexp : (poissonMeasure ((N : NNReal) / 8)).real (Set.Ioi N) ≤
      Real.exp (-(N : Real) / 4) := by
    simpa only [Measure.real_def, ENNReal.toReal_ofReal (Real.exp_pos _).le,
      neg_div] using ENNReal.toReal_mono ENNReal.ofReal_ne_top (hmono.trans hbern)
  calc
    _ ≤ Real.exp (-(N : Real) / 4) := hexp
    _ = 1 / Real.exp ((N : Real) / 4) := by
      rw [show -(N : Real) / 4 = -((N : Real) / 4) by ring,
        Real.exp_neg, one_div]
    _ ≤ 1 / ((N : Real) / 4) := by
      exact one_div_le_one_div_of_le (by positivity)
        (by linarith [Real.add_one_le_exp ((N : Real) / 4)])
    _ = 4 / (N : Real) := by field_simp
    _ ≤ 8 / (N : Real) := by
      exact mul_le_mul_of_nonneg_right (by norm_num) (inv_nonneg.mpr hNR.le)

-- @node: lem:fixed-sample-hybrid-transfer
/-- The deterministic fixed-sample implementation costs at most a factor two and
an additive order-`1/n` overflow term.  [the stated conclusion](goal). -/
lemma fixed_sample_hybrid_transfer :
    ∃ C : Real, 0 < C ∧
    ∀ (eps : Real), 0 < eps → eps < 1 / 2 →
    ∀ (n m d : Nat), 1 ≤ n → 2 ≤ d →
    ∀ (P : DiscreteLaw d), ModelClass d eps P →
      Measurable (mixedEstimator n m d eps) ∧
      twoSampleMSE (annotationLaw P n m) (mixedEstimator n m d eps)
          (ateFunctional P) ≤
        2 * poissonHybridMSE P n m eps + C / n := by
  refine ⟨384, by norm_num, ?_⟩
  intro eps _heps _heps2 n m d hn _hd P hP
  refine ⟨measurable_mixedEstimator n m d eps, ?_⟩
  by_cases hcal : calibrationPredicate n m eps
  · let bs := blockSizes n m
    let u : Real := bs.M0 / 8
    let tp : Real := (bs.np + bs.mp : Nat) / 8
    let t : Real := (bs.nf + bs.mf : Nat) / 8
    let P3 := threePoolObservationLaw (obsLaw P) (auxMarginal P).toMeasure
    let lam := threePoolIntensity (Real.toNNReal u)
      (Real.toNNReal tp) (Real.toNNReal t)
    let cap := threePoolCapacity bs.M0 (bs.np + bs.mp) (bs.nf + bs.mf)
    let T := finitePrefixHybridStatistic (d := d) n m eps
    let RB := prefixRaoBlackwellStatistic (N := cap) lam T 0
    have htransfer := finiteAlphabet_threePoolSharedLaw_risk_le
      (obsLaw P) (auxMarginal P).toMeasure
      (Real.toNNReal u) (Real.toNNReal tp) (Real.toNNReal t)
      bs.M0 (bs.np + bs.mp) (bs.nf + bs.mf)
      (T := T) (measurable_finitePrefixHybridStatistic n m eps)
      (a := (-1 : Real)) (b := 1) (theta := ateFunctional P) (zOver := 0)
      (by norm_num) (finitePrefixHybridStatistic_mem_Icc n m eps)
      (ateFunctional_mem_Icc_neg_one_one P hP.overlap) (by norm_num)
    have hRB : mixedEstimator n m d eps = RB ∘ hybridFixedPools := by
      funext sample
      exact (prefixRaoBlackwellStatistic_hybridFixedPools eps hcal sample).symm
    have hfixed : twoSampleMSE (annotationLaw P n m)
        (mixedEstimator n m d eps) (ateFunctional P) =
        sqRisk (fixedPoolsLaw P3 cap) RB (ateFunctional P) := by
      unfold twoSampleMSE sqRisk
      rw [hRB]
      change (∫ z, (RB (hybridFixedPools z) - ateFunctional P) ^ 2
        ∂annotationLaw P n m) = _
      have hf : AEStronglyMeasurable
          (fun z ↦ (RB z - ateFunctional P) ^ 2)
          (Measure.map hybridFixedPools (annotationLaw P n m)) :=
        (measurable_of_countable _).aestronglyMeasurable
      rw [← integral_map (measurable_hybridFixedPools n m d).aemeasurable hf,
        hybridFixedPools_map_annotationLaw]
    have hpoisson : sqRisk (independentPoissonPrefixLaw P3 lam) T
        (ateFunctional P) = poissonHybridMSE P n m eps := by
      unfold sqRisk
      let stat := hybridPoissonStatistic (d := d) n m eps u t
      have hf : AEStronglyMeasurable
          (fun K ↦ (stat K - ateFunctional P) ^ 2)
          (Measure.map hybridPrefixCounts
            (independentPoissonPrefixLaw P3 lam)) :=
        (measurable_of_countable _).aestronglyMeasurable
      have hi := integral_map measurable_hybridPrefixCounts.aemeasurable hf
      change (∫ s, (stat (hybridPrefixCounts s) - ateFunctional P) ^ 2
          ∂independentPoissonPrefixLaw P3 lam) = _
      rw [← hi]
      rw [hybridPrefixCounts_map_eq_hybridPoissonCountLaw P u tp t
        (by positivity) (by positivity) (by positivity)]
      simp only [poissonHybridMSE, hcal, if_pos, stat, u, tp, t, bs]
    have hn24 : 24 ≤ n := by
      simpa only [calibrationPredicate] using hcal.1
    have hM : n ≤ 4 * bs.M0 := by dsimp [bs, blockSizes]; omega
    have hPcap : n ≤ 4 * (bs.np + bs.mp) := by dsimp [bs, blockSizes]; omega
    have hF : n ≤ 4 * (bs.nf + bs.mf) := by dsimp [bs, blockSizes]; omega
    have hMpos : 0 < bs.M0 := by omega
    have hPpos : 0 < bs.np + bs.mp := by omega
    have hFpos : 0 < bs.nf + bs.mf := by omega
    have hnR : 0 < (n : Real) := by positivity
    have tail_le (N : Nat) (hN : 0 < N) (hlarge : n ≤ 4 * N) :
        (poissonMeasure (Real.toNNReal ((N : Real) / 8))).real (Set.Ioi N) ≤
          32 / (n : Real) := by
      refine (poisson_eighth_tail N hN).trans ?_
      apply (div_le_div_iff₀ (by positivity : (0 : Real) < N) hnR).2
      have hc : (n : Real) ≤ 4 * (N : Real) := by exact_mod_cast hlarge
      nlinarith
    have htails :
        (poissonMeasure (Real.toNNReal u)).real (Set.Ioi bs.M0) +
          (poissonMeasure (Real.toNNReal tp)).real (Set.Ioi (bs.np + bs.mp)) +
          (poissonMeasure (Real.toNNReal t)).real (Set.Ioi (bs.nf + bs.mf)) ≤
            96 / (n : Real) := by
      have h0 := tail_le bs.M0 hMpos hM
      have hp := tail_le (bs.np + bs.mp) hPpos hPcap
      have hf := tail_le (bs.nf + bs.mf) hFpos hF
      dsimp [u, tp, t] at h0 hp hf ⊢
      calc
        _ ≤ 32 / (n : Real) + 32 / (n : Real) + 32 / (n : Real) :=
          add_le_add (add_le_add h0 hp) hf
        _ = 96 / (n : Real) := by ring
    rw [hfixed]
    calc
      _ ≤ sqRisk (independentPoissonPrefixLaw P3 lam) T (ateFunctional P) +
          4 * ((poissonMeasure (Real.toNNReal u)).real (Set.Ioi bs.M0) +
            (poissonMeasure (Real.toNNReal tp)).real (Set.Ioi (bs.np + bs.mp)) +
            (poissonMeasure (Real.toNNReal t)).real
              (Set.Ioi (bs.nf + bs.mf))) := by
        convert htransfer using 1 <;> norm_num [P3, lam, cap, T, RB, bs, u, tp, t]
      _ ≤ poissonHybridMSE P n m eps + 384 / (n : Real) := by
        rw [hpoisson]
        gcongr
        calc
          4 * ((poissonMeasure (Real.toNNReal u)).real (Set.Ioi bs.M0) +
              (poissonMeasure (Real.toNNReal tp)).real (Set.Ioi (bs.np + bs.mp)) +
              (poissonMeasure (Real.toNNReal t)).real
                (Set.Ioi (bs.nf + bs.mf))) ≤ 4 * (96 / (n : Real)) :=
            mul_le_mul_of_nonneg_left htails (by norm_num)
          _ = 384 / (n : Real) := by ring
      _ ≤ 2 * poissonHybridMSE P n m eps + 384 / (n : Real) := by
        have hmse : 0 ≤ poissonHybridMSE P n m eps := by
          simp only [poissonHybridMSE, hcal, if_pos]
          exact integral_nonneg fun _ ↦ sq_nonneg _
        linarith
  · unfold twoSampleMSE
    letI : IsProbabilityMeasure (annotationLaw P n m) := by
      unfold annotationLaw labeledProductLaw auxProductLaw
      infer_instance
    simp only [mixedEstimator, poissonHybridMSE, hcal, if_false,
      zero_sub, neg_sq, integral_const]
    have hnR : 0 < (n : Real) := by positivity
    have hnonneg : 0 ≤ ateFunctional P ^ 2 := sq_nonneg _
    have hconst : 0 ≤ (384 : Real) / n := by positivity
    rw [show (annotationLaw P n m).real Set.univ = 1 by simp]
    simp only [one_smul]
    nlinarith

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
