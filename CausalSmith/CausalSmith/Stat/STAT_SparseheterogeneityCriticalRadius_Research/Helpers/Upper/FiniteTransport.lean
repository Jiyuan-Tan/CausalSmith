module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.PilotPostSplit
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.PrefixCorrection
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.IdealAggregation
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.OutcomeVectorPartition
public import Causalean.Stat.Concentration.Poisson.Threshold

/-! Transport of the capped Poisson count randomization to finite Poisson samples. -/

@[expose] public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram

private lemma observedOutcomeVector_arm_eq {n : ℕ}
    (s : FiniteSample (SampleObs n)) (k : Fin n) (a : Bool) :
    (observedOutcomeVector s k).casesOn
        (fun q0 q1 => if a then q1 else q0) =
      finiteSampleArmCellOutcomes s a k := by
  rcases s with ⟨m, x⟩
  let sm := finiteSampleMap
    (fun o : SampleObs n => (toFullObservedMark o, (0 : ℝ)))
    (⟨m, x⟩ : FiniteSample (SampleObs n))
  have ht : (fullMarkArmCellPartition n).cellIndices (k, a) sm =
      armCellIndices (⟨m, x⟩ : FiniteSample (SampleObs n)) a k := by
    unfold FiniteMeasurablePartition.cellIndices armCellIndices
    dsimp [sm, finiteSampleMap, fullMarkArmCellPartition, toFullObservedMark]
    simp only [FiniteSample.count, FiniteSample.points]
    congr 1
    funext i
    exact Prod.mk.injEq (x i).x (x i).a k a
  cases a <;>
    unfold observedOutcomeVector fullMarkOutcomeVector
      FiniteMeasurablePartition.restrictCell finiteSampleArmCellOutcomes <;>
    change finiteSampleMap (fun z : FullObservedMark n × ℝ => z.1.2.2)
      (let t := (fullMarkArmCellPartition n).cellIndices (k, _) sm
       ⟨t.card, fun i => sm.points (t.orderIsoOfFin rfl i)⟩) = _ <;>
    rw [ht] <;>
    unfold finiteSampleMap sm <;>
    rfl

/-- The outcome vector produced by the partition theorem is exactly the pair
used in the pointwise prefix correction. -/
lemma observedOutcomeVector_eq_prefixOutcomePair {n : ℕ}
    (s : FiniteSample (SampleObs n)) (k : Fin n) :
    observedOutcomeVector s k = prefixOutcomePair s k := by
  apply Prod.ext
  · exact observedOutcomeVector_arm_eq s k false
  · exact observedOutcomeVector_arm_eq s k true

/-- The complete vector of outcome pairs extracted by `prefixOutcomePair`
has the independent per-cell outcome law at the estimator block intensity. -/
lemma map_prefixOutcomePair_vector_blockMean {n : ℕ} (P : Law n)
    (hoverlap : FixedOverlap P) :
    Measure.map (fun s : FiniteSample (SampleObs n) =>
        fun k : Fin n => prefixOutcomePair s k)
        (finitePoissonSampleLaw P.observedLaw
          (Real.toNNReal (blockMean n))) =
      Measure.pi (fun k : Fin n => cellOutcomePoissonLaw P k) := by
  rw [show (fun s : FiniteSample (SampleObs n) =>
      fun k : Fin n => prefixOutcomePair s k) = observedOutcomeVector by
    funext s
    funext k
    exact (observedOutcomeVector_eq_prefixOutcomePair s k).symm]
  exact map_observedOutcomeVector_blockMean P hoverlap

noncomputable def classifierCountVector {n : ℕ}
    (s : FiniteSample (SampleObs n)) : Fin n → ℕ :=
  fun k => finiteSampleCellCount s k

lemma measurable_classifierCountVector (n : ℕ) :
    Measurable (classifierCountVector (n := n)) := by
  exact measurable_pi_lambda _ (measurable_finiteSampleCellCount)

/-- Jointly, all classifier cell counts are independent Poisson variables. -/
lemma map_classifierCountVector_finitePoissonSampleLaw {n : ℕ}
    (P : Law n) (lam : ℝ≥0) :
    Measure.map classifierCountVector
        (finitePoissonSampleLaw P.observedLaw lam) =
      Measure.pi (fun k : Fin n =>
        poissonMeasure (lam * Real.toNNReal (P.cellMass k))) := by
  let Q := Measure.map (fun o : SampleObs n => o.x) P.observedLaw
  let F : FiniteSample (SampleObs n) → FiniteSample (Fin n) :=
    finiteSampleMap (fun o => o.x)
  let H : FiniteSample (Fin n) → (Fin n → ℕ) :=
    fun s => finiteSampleHistogram s.points
  have hF : Measurable F := measurable_finiteSampleMap _ measurable_sampleObs_x
  have hH : Measurable H := measurable_finiteSampleHistogram
  have hfactor : classifierCountVector = H ∘ F := by
    funext s
    rfl
  letI : IsProbabilityMeasure Q :=
    Measure.isProbabilityMeasure_map measurable_sampleObs_x.aemeasurable
  rw [hfactor, ← Measure.map_map hH hF,
    map_finitePoissonSampleLaw_finiteSampleMap_local
      P.observedLaw (fun o : SampleObs n => o.x) measurable_sampleObs_x lam,
    finitePoissonSampleLaw_map_histogram]
  unfold independentPoissonCountLaw
  congr 1
  funext k
  rw [map_covariate_observedLaw_singleton_toNNReal]

abbrev TransportCellSample := ℕ × (FiniteSample ℝ × FiniteSample ℝ)

noncomputable def observedTransportVector {n : ℕ}
    (p : FiniteSample (SampleObs n) × FiniteSample (SampleObs n)) :
    Fin n → TransportCellSample := fun k =>
  (finiteSampleCellCount p.1 k, prefixOutcomePair p.2 k)

noncomputable def idealTransportVector {n : ℕ}
    (q : Fin n → IdealCellSample n) : Fin n → TransportCellSample := fun k =>
  (finiteSampleCellCount (q k).1 k, (q k).2)

lemma measurable_observedTransportVector (n : ℕ) :
    Measurable (observedTransportVector (n := n)) := by
  apply measurable_pi_lambda
  intro k
  have hk : Measurable (fun s : FiniteSample (SampleObs n) =>
      prefixOutcomePair s k) := by
    rw [show (fun s : FiniteSample (SampleObs n) => prefixOutcomePair s k) =
      fun s => observedOutcomeVector s k by
        funext s
        exact (observedOutcomeVector_eq_prefixOutcomePair s k).symm]
    exact (measurable_pi_apply k).comp (measurable_observedOutcomeVector n)
  exact ((measurable_finiteSampleCellCount k).comp measurable_fst).prodMk
    (hk.comp measurable_snd)

lemma measurable_idealTransportVector (n : ℕ) :
    Measurable (idealTransportVector (n := n)) := by
  apply measurable_pi_lambda
  intro k
  exact ((measurable_finiteSampleCellCount k).comp
      ((measurable_pi_apply k).fst)).prodMk
    ((measurable_pi_apply k).snd)

/-- The raw classifier/estimation Poisson pair and the canonical ideal
product experiment have the same compressed independent cell-data law. -/
lemma map_observedTransportVector_eq_map_idealTransportVector {n : ℕ}
    (P : Law n) (hoverlap : FixedOverlap P) :
    Measure.map observedTransportVector
        ((finitePoissonSampleLaw P.observedLaw
          (Real.toNNReal (blockMean n))).prod
         (finitePoissonSampleLaw P.observedLaw
          (Real.toNNReal (blockMean n)))) =
      Measure.map idealTransportVector (idealProductLaw P) := by
  let lam := Real.toNNReal (blockMean n)
  let C : Fin n → Measure ℕ := fun k =>
    poissonMeasure (lam * Real.toNNReal (P.cellMass k))
  let O : Fin n → Measure (FiniteSample ℝ × FiniteSample ℝ) :=
    fun k => cellOutcomePoissonLaw P k
  let mu := finitePoissonSampleLaw P.observedLaw lam
  have hc : Measure.map classifierCountVector mu = Measure.pi C := by
    exact map_classifierCountVector_finitePoissonSampleLaw P lam
  have ho : Measure.map (fun s : FiniteSample (SampleObs n) =>
      fun k : Fin n => prefixOutcomePair s k) mu = Measure.pi O := by
    exact map_prefixOutcomePair_vector_blockMean P hoverlap
  have hOutcomeMeas : Measurable (fun s : FiniteSample (SampleObs n) =>
      fun k : Fin n => prefixOutcomePair s k) := by
    rw [show (fun s : FiniteSample (SampleObs n) =>
      fun k : Fin n => prefixOutcomePair s k) = observedOutcomeVector by
      funext s k
      exact (observedOutcomeVector_eq_prefixOutcomePair s k).symm]
    exact measurable_observedOutcomeVector n
  letI (k : Fin n) : IsProbabilityMeasure (O k) := by
    dsimp only [O]
    unfold cellOutcomePoissonLaw
    infer_instance
  have hactual : Measure.map observedTransportVector (mu.prod mu) =
      Measure.pi (fun k => (C k).prod (O k)) := by
    let group : ((Fin n → ℕ) ×
        (Fin n → (FiniteSample ℝ × FiniteSample ℝ))) →
        (Fin n → TransportCellSample) := fun z k => (z.1 k, z.2 k)
    calc
      _ = Measure.map group
          (Measure.map (Prod.map classifierCountVector
            (fun s : FiniteSample (SampleObs n) =>
              fun k : Fin n => prefixOutcomePair s k)) (mu.prod mu)) := by
        rw [Measure.map_map (by fun_prop)
          ((measurable_classifierCountVector n).prodMap hOutcomeMeas)]
        rfl
      _ = Measure.map group ((Measure.pi C).prod (Measure.pi O)) := by
        rw [← Measure.map_prod_map mu mu
          (measurable_classifierCountVector n) hOutcomeMeas, hc, ho]
      _ = Measure.pi (fun k => (C k).prod (O k)) := by
        exact (measurePreserving_arrowProdEquivProdArrow
          ℕ (FiniteSample ℝ × FiniteSample ℝ) (Fin n) C O).symm.map_eq
  have hideal : Measure.map idealTransportVector (idealProductLaw P) =
      Measure.pi (fun k => (C k).prod (O k)) := by
    unfold idealProductLaw
    let f : (k : Fin n) → IdealCellSample n → TransportCellSample :=
      fun k q => (finiteSampleCellCount q.1 k, q.2)
    have hf (k : Fin n) : Measurable (f k) :=
      ((measurable_finiteSampleCellCount k).comp measurable_fst).prodMk
        measurable_snd
    change Measure.map (fun q => fun k => f k (q k))
      (Measure.pi fun k => idealCellLaw P k) = _
    rw [Measure.pi_map_pi (fun k => (hf k).aemeasurable)]
    congr 1
    funext k
    unfold idealCellLaw
    change Measure.map (Prod.map (fun s => finiteSampleCellCount s k) id)
      ((finitePoissonSampleLaw P.observedLaw
        (Real.toNNReal (blockMean n))).prod (cellOutcomePoissonLaw P k)) = _
    rw [← Measure.map_prod_map _ _ (measurable_finiteSampleCellCount k)
      measurable_id, Measure.map_id,
      map_finiteSampleCellCount_finitePoissonSampleLaw]
  rw [hactual, hideal]

/-- Integral form of the common compressed law. -/
lemma integral_observedTransportVector_eq_idealTransportVector {n : ℕ}
    (P : Law n) (hoverlap : FixedOverlap P)
    (F : (Fin n → TransportCellSample) → ℝ) (hF : Measurable F) :
    (∫ p, F (observedTransportVector p)
      ∂((finitePoissonSampleLaw P.observedLaw
          (Real.toNNReal (blockMean n))).prod
        (finitePoissonSampleLaw P.observedLaw
          (Real.toNNReal (blockMean n))))) =
      ∫ q, F (idealTransportVector q) ∂idealProductLaw P := by
  calc
    _ = ∫ z, F z ∂Measure.map observedTransportVector
        ((finitePoissonSampleLaw P.observedLaw
          (Real.toNNReal (blockMean n))).prod
         (finitePoissonSampleLaw P.observedLaw
          (Real.toNNReal (blockMean n)))) :=
      (integral_map (measurable_observedTransportVector n).aemeasurable
        hF.aestronglyMeasurable).symm
    _ = ∫ z, F z ∂Measure.map idealTransportVector
        (idealProductLaw P) := by
      rw [map_observedTransportVector_eq_map_idealTransportVector P hoverlap]
    _ = _ := integral_map (measurable_idealTransportVector n).aemeasurable
      hF.aestronglyMeasurable

noncomputable def transportSelectedCorrection {n : ℕ} (P : Law n)
    (k : Fin n) (t rho : ℝ) (d : TransportCellSample) : ℝ :=
  if d.1 ≤ 256 * degree n rho then
    idealLightCorrection P k t rho d.2 else idealHeavyCorrection P k t d.2

lemma measurable_transportSelectedCorrection {n : ℕ} (P : Law n)
    (k : Fin n) (t rho : ℝ) : Measurable (transportSelectedCorrection P k t rho) := by
  unfold transportSelectedCorrection
  exact Measurable.ite
    (measurableSet_le measurable_fst measurable_const)
    ((measurable_idealLightCorrection P k t rho).comp measurable_snd)
    ((measurable_idealHeavyCorrection P k t).comp measurable_snd)

lemma prefixSelectedCorrection_eq_transport {n : ℕ} (P : Law n)
    (rho t : ℝ)
    (p : FiniteSample (SampleObs n) × FiniteSample (SampleObs n))
    (k : Fin n) :
    prefixSelectedCorrection rho t p k =
      transportSelectedCorrection P k t rho (observedTransportVector p k) := by
  rw [prefixSelectedCorrection_eq_idealSelectedCorrection P rho t p k]
  unfold transportSelectedCorrection idealSelectedCorrection observedTransportVector
  rfl

/-- For a fixed pilot value, the full raw classifier/estimation Poisson
experiment and the canonical ideal product have identical clipped risk for
the selected correction sum. -/
lemma rawPoisson_clippedRisk_eq_idealProduct {n : ℕ} (P : Law n)
    (hoverlap : FixedOverlap P) (M rho t tau : ℝ) :
    (∫ p : FiniteSample (SampleObs n) × FiniteSample (SampleObs n),
      (clipM M (t + ∑ k, prefixSelectedCorrection rho t p k) - tau) ^ 2
      ∂((finitePoissonSampleLaw P.observedLaw
          (Real.toNNReal (blockMean n))).prod
        (finitePoissonSampleLaw P.observedLaw
          (Real.toNNReal (blockMean n))))) =
      ∫ q : Fin n → IdealCellSample n,
        (clipM M (t + ∑ k, idealSelectedCorrection P k t rho (q k)) - tau) ^ 2
        ∂idealProductLaw P := by
  let F : (Fin n → TransportCellSample) → ℝ := fun d =>
    (clipM M (t + ∑ k, transportSelectedCorrection P k t rho (d k)) - tau) ^ 2
  have hF : Measurable F := by
    unfold F
    have hsum : Measurable (fun d : Fin n → TransportCellSample =>
        ∑ k, transportSelectedCorrection P k t rho (d k)) := by
      apply Finset.measurable_sum Finset.univ
      intro k hk
      exact (measurable_transportSelectedCorrection P k t rho).comp
        (measurable_pi_apply k)
    exact (((Causalean.Mathlib.Analysis.measurable_clipIcc (-M) M).comp
      (measurable_const.add hsum)).sub measurable_const).pow_const 2
  have h := integral_observedTransportVector_eq_idealTransportVector
    P hoverlap F hF
  calc
    _ = ∫ p, F (observedTransportVector p)
        ∂((finitePoissonSampleLaw P.observedLaw
            (Real.toNNReal (blockMean n))).prod
          (finitePoissonSampleLaw P.observedLaw
            (Real.toNNReal (blockMean n)))) := by
      congr 1
      funext p
      unfold F
      congr 3
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      exact prefixSelectedCorrection_eq_transport P rho t p k
    _ = ∫ q, F (idealTransportVector q) ∂idealProductLaw P := h
    _ = _ := rfl

/-- The overflow event for the two independent randomized block sizes. -/
def poissonCountOverflow (n : ℕ) : Set (ℕ × ℕ) :=
  {z | postPilotSize n < z.1 + z.2}

lemma measurableSet_poissonCountOverflow (n : ℕ) :
    MeasurableSet (poissonCountOverflow n) := MeasurableSet.of_discrete

/-- The two randomized block sizes add to a Poisson variable with twice the
block intensity. -/
lemma map_add_poissonCountLaw (n : ℕ) :
    Measure.map (fun z : ℕ × ℕ => z.1 + z.2) (poissonCountLaw n) =
      poissonMeasure (Real.toNNReal (blockMean n) +
        Real.toNNReal (blockMean n)) := by
  unfold poissonCountLaw
  change (poissonMeasure (Real.toNNReal (blockMean n)) ∗
      poissonMeasure (Real.toNNReal (blockMean n))) = _
  exact poissonMeasure_conv_poissonMeasure _ _

/-- Chernoff form of the exact cap-overflow probability. -/
lemma poissonCountOverflow_measureReal_mul_exp_le (n : ℕ) :
    (poissonCountLaw n).real (poissonCountOverflow n) *
        Real.exp (-(Real.toNNReal (blockMean n) +
          Real.toNNReal (blockMean n) : ℝ)) ≤
      Real.exp (-Real.log 2 * (postPilotSize n : ℝ)) := by
  have ht := Causalean.Stat.Concentration.Poisson.poisson_upper_tail_mul_exp_le
    (Real.toNNReal (blockMean n) + Real.toNNReal (blockMean n))
    (postPilotSize n) (r := 1) (by norm_num)
  have hpre : (fun z : ℕ × ℕ => z.1 + z.2) ⁻¹'
      Set.Ioi (postPilotSize n) = poissonCountOverflow n := by
    ext z
    simp [poissonCountOverflow]
  rw [← map_add_poissonCountLaw n] at ht
  have hmass :
      (Measure.map (fun z : ℕ × ℕ => z.1 + z.2) (poissonCountLaw n)).real
          {w : ℕ | postPilotSize n < w} =
        (poissonCountLaw n).real (poissonCountOverflow n) := by
    unfold Measure.real
    change ((Measure.map (fun z : ℕ × ℕ => z.1 + z.2) (poissonCountLaw n))
      (Set.Ioi (postPilotSize n))).toReal = _
    rw [Measure.map_apply (by fun_prop) measurableSet_Ioi, hpre]
  rw [hmass] at ht
  simpa only [Nat.cast_one, one_add_one_eq_two, one_mul, NNReal.coe_add,
    neg_mul] using ht

/-- The exact two-count overflow probability has the geometric envelope used
in the finite-sample risk calculation. -/
lemma poissonCountOverflow_measureReal_le (n : ℕ) :
    (poissonCountLaw n).real (poissonCountOverflow n) ≤
      (Real.exp 1 / 4) ^ (postPilotSize n / 2) := by
  let r := postPilotSize n
  let q := r / 2
  let L := Real.toNNReal (blockMean n) + Real.toNNReal (blockMean n)
  have hchernoff := poissonCountOverflow_measureReal_mul_exp_le n
  have hblock : blockMean n = (r : ℝ) / 4 := by rfl
  have hblock0 : 0 ≤ blockMean n := by rw [hblock]; positivity
  have hL : (L : ℝ) = (r : ℝ) / 2 := by
    dsimp only [L]
    rw [NNReal.coe_add, Real.coe_toNNReal _ hblock0, hblock]
    ring
  have hprob : (poissonCountLaw n).real (poissonCountOverflow n) ≤
      Real.exp (-Real.log 2 * (r : ℝ) + (r : ℝ) / 2) := by
    have hp := (le_div_iff₀ (Real.exp_pos (-(L : ℝ)))).2 hchernoff
    calc
      _ ≤ Real.exp (-Real.log 2 * (r : ℝ)) / Real.exp (-(L : ℝ)) := hp
      _ = Real.exp (-Real.log 2 * (r : ℝ) + (r : ℝ) / 2) := by
        rw [← Real.exp_sub, hL]
        congr 1
        ring
  have hexpHalfSq : Real.exp ((1 : ℝ) / 2) ^ 2 = Real.exp 1 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hexpHalf : Real.exp ((1 : ℝ) / 2) < 2 := by
    have he := Real.exp_one_lt_d9
    have hp := Real.exp_pos ((1 : ℝ) / 2)
    nlinarith
  have hlog : (1 : ℝ) / 2 < Real.log 2 := by
    rw [← Real.exp_lt_exp, Real.exp_log (by norm_num)]
    exact hexpHalf
  have hc : 1 - 2 * Real.log 2 < 0 := by linarith
  have hq : (q : ℝ) ≤ (r : ℝ) / 2 := by
    exact Nat.cast_div_le
  have hexponent :
      -Real.log 2 * (r : ℝ) + (r : ℝ) / 2 ≤
        (q : ℝ) * (1 - 2 * Real.log 2) := by
    have hm := mul_le_mul_of_nonpos_right hq hc.le
    nlinarith
  have hbase : Real.exp (1 - 2 * Real.log 2) = Real.exp 1 / 4 := by
    rw [show 2 * Real.log 2 = Real.log 2 + Real.log 2 by ring,
      Real.exp_sub, Real.exp_add, Real.exp_log (by norm_num)]
    norm_num
  calc
    _ ≤ Real.exp (-Real.log 2 * (r : ℝ) + (r : ℝ) / 2) := hprob
    _ ≤ Real.exp ((q : ℝ) * (1 - 2 * Real.log 2)) :=
      Real.exp_le_exp.mpr hexponent
    _ = (Real.exp 1 / 4) ^ q := by rw [Real.exp_nat_mul, hbase]
    _ = _ := rfl

/-- The legal part of the randomized squared risk, with overflow set to zero. -/
noncomputable def randomizedPoissonLegalSqRisk {n : ℕ} (P : Law n)
    (M rho tau : ℝ) : ℝ :=
  ∫ w : (Fin n → SampleObs n) × (ℕ × ℕ),
    if w.2.1 + w.2.2 ≤ postPilotSize n then
      (conditionalEstimator n M rho w.1 w.2.1 w.2.2 - tau) ^ 2
    else 0
    ∂((DiscreteAteHeterogeneityFrontier.productLaw n P).prod (poissonCountLaw n))

/-- On overflow, the randomized output is the clipped pilot and hence has
squared loss at most `4 M²` against the class target. -/
-- keep: pointwise overflow safety bound for the finite-sample transport
lemma randomizedPoissonOutput_overflow_sqLoss_le {n : ℕ} (M rho : ℝ)
    (P : KnownRadiusClass n M rho)
    (sample : Fin n → SampleObs n) (z : ℕ × ℕ)
    (hz : postPilotSize n < z.1 + z.2) :
    (randomizedPoissonOutput n M rho (sample, z) -
      DiscreteAteHeterogeneityFrontier.rawAteFormula P.law) ^ 2 ≤ 4 * M ^ 2 := by
  have hM : 0 ≤ M := le_trans zero_le_one P.M_ge_one
  have hp := pilotTau_range n M hM sample
  have ht := rawAte_mem_clip P
  have habs : |pilotTau n M sample -
      DiscreteAteHeterogeneityFrontier.rawAteFormula P.law| ≤ 2 * M := by
    rw [abs_le]
    constructor <;> linarith [hp.1, hp.2, ht.1, ht.2]
  unfold randomizedPoissonOutput
  rw [if_neg (by simpa using (not_le.mpr hz))]
  change (pilotTau n M sample -
    DiscreteAteHeterogeneityFrontier.rawAteFormula P.law) ^ 2 ≤ 4 * M ^ 2
  have hs := (sq_le_sq₀ (abs_nonneg _)
    (mul_nonneg (by norm_num) hM)).2 habs
  calc
    _ = |pilotTau n M sample -
        DiscreteAteHeterogeneityFrontier.rawAteFormula P.law| ^ 2 :=
      (sq_abs _).symm
    _ ≤ (2 * M) ^ 2 := hs
    _ = _ := by ring

/-- The randomized squared risk is its legal-prefix contribution plus at
most `4 M²` times the exact two-count overflow probability. -/
lemma randomizedPoisson_sqRisk_le_legal_add_overflow {n : ℕ} (M rho : ℝ)
    (P : KnownRadiusClass n M rho) :
    Causalean.Stat.sqRisk
        ((DiscreteAteHeterogeneityFrontier.productLaw n P.law).prod
          (poissonCountLaw n))
        (randomizedPoissonOutput n M rho)
        (DiscreteAteHeterogeneityFrontier.rawAteFormula P.law) ≤
      randomizedPoissonLegalSqRisk P.law M rho
        (DiscreteAteHeterogeneityFrontier.rawAteFormula P.law) +
      4 * M ^ 2 * (poissonCountLaw n).real (poissonCountOverflow n) := by
  let mu := DiscreteAteHeterogeneityFrontier.productLaw n P.law
  let nu := poissonCountLaw n
  let tau := DiscreteAteHeterogeneityFrontier.rawAteFormula P.law
  let f : ((Fin n → SampleObs n) × (ℕ × ℕ)) → ℝ := fun w =>
    (randomizedPoissonOutput n M rho w - tau) ^ 2
  let g : ((Fin n → SampleObs n) × (ℕ × ℕ)) → ℝ := fun w =>
    if w.2.1 + w.2.2 ≤ postPilotSize n then f w else 0
  let b : ((Fin n → SampleObs n) × (ℕ × ℕ)) → ℝ := fun w =>
    if postPilotSize n < w.2.1 + w.2.2 then 4 * M ^ 2 else 0
  have hf : Measurable f :=
    ((randomizedPoissonOutput_measurable n M rho).sub measurable_const).pow_const 2
  have hg : Measurable g := by
    apply Measurable.ite
    · exact measurableSet_le (measurable_snd.fst.add measurable_snd.snd)
        measurable_const
    · exact hf
    · exact measurable_const
  have hb : Measurable b := by
    apply Measurable.ite
    · exact measurableSet_lt measurable_const
        (measurable_snd.fst.add measurable_snd.snd)
    · exact measurable_const
    · exact measurable_const
  have hM : 0 ≤ M := le_trans zero_le_one P.M_ge_one
  have hC : 0 ≤ 4 * M ^ 2 := mul_nonneg (by norm_num) (sq_nonneg M)
  have htarget := rawAte_mem_clip P
  have hfBound (w : (Fin n → SampleObs n) × (ℕ × ℕ)) :
      f w ≤ 4 * M ^ 2 := by
    have ho := abs_le.mp (randomizedPoissonOutput_abs_le n M rho hM w)
    dsimp only [f, tau]
    have ha : |randomizedPoissonOutput n M rho w -
        DiscreteAteHeterogeneityFrontier.rawAteFormula P.law| ≤ 2 * M := by
      rw [abs_le]
      constructor <;> linarith [ho.1, ho.2, htarget.1, htarget.2]
    have hs := (sq_le_sq₀ (abs_nonneg _)
      (mul_nonneg (by norm_num) hM)).2 ha
    calc
      _ = |randomizedPoissonOutput n M rho w -
          DiscreteAteHeterogeneityFrontier.rawAteFormula P.law| ^ 2 :=
        (sq_abs _).symm
      _ ≤ (2 * M) ^ 2 := hs
      _ = _ := by ring
  have hpoint (w : (Fin n → SampleObs n) × (ℕ × ℕ)) :
      f w ≤ g w + b w := by
    by_cases hz : w.2.1 + w.2.2 ≤ postPilotSize n
    · have hz' : ¬postPilotSize n < w.2.1 + w.2.2 := by omega
      simp [g, b, hz, hz']
    · have hz' : postPilotSize n < w.2.1 + w.2.2 := by omega
      simp only [g, b, hz, hz', if_false, if_true, zero_add]
      exact hfBound w
  have hfInt : Integrable f (mu.prod nu) := by
    apply Integrable.of_bound hf.aestronglyMeasurable (4 * M ^ 2)
    filter_upwards with w
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hfBound w
  have hgInt : Integrable g (mu.prod nu) := by
    apply Integrable.of_bound hg.aestronglyMeasurable (4 * M ^ 2)
    filter_upwards with w
    dsimp only [g]
    split_ifs
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hfBound w
    · simpa using hC
  have hbInt : Integrable b (mu.prod nu) := by
    apply Integrable.of_bound hb.aestronglyMeasurable (4 * M ^ 2)
    filter_upwards with w
    dsimp only [b]
    split_ifs
    · rw [Real.norm_eq_abs, abs_of_nonneg hC]
    · simpa using hC
  have hmono : (∫ w, f w ∂mu.prod nu) ≤ ∫ w, (g w + b w) ∂mu.prod nu :=
    integral_mono_ae hfInt (hgInt.add hbInt) (Filter.Eventually.of_forall hpoint)
  rw [integral_add hgInt hbInt] at hmono
  have hbval : (∫ w, b w ∂mu.prod nu) =
      4 * M ^ 2 * nu.real (poissonCountOverflow n) := by
    rw [integral_prod _ hbInt]
    have hinner (sample : Fin n → SampleObs n) :
        (∫ z, b (sample, z) ∂nu) =
          4 * M ^ 2 * nu.real (poissonCountOverflow n) := by
      rw [show (fun z => b (sample, z)) =
          (poissonCountOverflow n).indicator (fun _ => 4 * M ^ 2) by
        funext z
        simp [b, poissonCountOverflow, Set.indicator_apply]]
      rw [integral_indicator_const (4 * M ^ 2)
        (measurableSet_poissonCountOverflow n)]
      rw [smul_eq_mul]
      ring
    simp_rw [hinner]
    rw [integral_const, probReal_univ, one_smul]
  rw [hbval] at hmono
  have hgDef : g = fun w : (Fin n → SampleObs n) × (ℕ × ℕ) =>
      if w.2.1 + w.2.2 ≤ postPilotSize n then
        (conditionalEstimator n M rho w.1 w.2.1 w.2.2 - tau) ^ 2 else 0 := by
    funext w
    by_cases hw : w.2.1 + w.2.2 ≤ postPilotSize n
    · simp [g, f, randomizedPoissonOutput, hw]
    · simp [g, hw]
  rw [hgDef] at hmono
  simpa only [Causalean.Stat.sqRisk, randomizedPoissonLegalSqRisk,
    mu, nu, tau, f, g] using hmono

/-- The preceding overflow contribution is bounded by the explicit geometric
cap tail. -/
lemma randomizedPoisson_sqRisk_le_legal_add_geometric {n : ℕ} (M rho : ℝ)
    (P : KnownRadiusClass n M rho) :
    Causalean.Stat.sqRisk
        ((DiscreteAteHeterogeneityFrontier.productLaw n P.law).prod
          (poissonCountLaw n))
        (randomizedPoissonOutput n M rho)
        (DiscreteAteHeterogeneityFrontier.rawAteFormula P.law) ≤
      randomizedPoissonLegalSqRisk P.law M rho
        (DiscreteAteHeterogeneityFrontier.rawAteFormula P.law) +
      4 * M ^ 2 * (Real.exp 1 / 4) ^ (postPilotSize n / 2) := by
  refine (randomizedPoisson_sqRisk_le_legal_add_overflow M rho P).trans ?_
  gcongr
  exact poissonCountOverflow_measureReal_le n

/-- Jensen followed by the cap decomposition reduces the implemented
finite estimator to its legal randomized fibres and the explicit cap tail. -/
lemma knownRadiusEstimator_sqRisk_le_legal_add_geometric {n : ℕ} (M rho : ℝ)
    (P : KnownRadiusClass n M rho) :
    Causalean.Stat.sqRisk
        (DiscreteAteHeterogeneityFrontier.productLaw n P.law)
        (knownRadiusEstimator n M rho)
        (DiscreteAteHeterogeneityFrontier.rawAteFormula P.law) ≤
      randomizedPoissonLegalSqRisk P.law M rho
        (DiscreteAteHeterogeneityFrontier.rawAteFormula P.law) +
      4 * M ^ 2 * (Real.exp 1 / 4) ^ (postPilotSize n / 2) := by
  exact (knownRadiusEstimator_sqRisk_le_randomized P.law M rho
    (DiscreteAteHeterogeneityFrontier.rawAteFormula P.law)
    (le_trans zero_le_one P.M_ge_one)).trans
      (randomizedPoisson_sqRisk_le_legal_add_geometric M rho P)

/-- A fixed legal fibre transports exactly to the retained pilot law times
the two independent fixed-size prefix laws. -/
-- keep: exact fixed-prefix integral transport including the retained pilot
lemma integral_pilotTau_fixedPrefixSamples_productLaw {n u v : ℕ}
    (M : ℝ) (P : Law n) (h : u + v ≤ postPilotSize n)
    (F : ℝ × (FiniteSample (SampleObs n) × FiniteSample (SampleObs n)) → ℝ)
    (hF : Measurable F) :
    (∫ sample, F (pilotTau n M sample, fixedPrefixSamples n u v h sample)
      ∂DiscreteAteHeterogeneityFrontier.productLaw n P) =
    ∫ z, F z ∂((Measure.map (pilotTau n M)
        (DiscreteAteHeterogeneityFrontier.productLaw n P)).prod
      ((Measure.map (fixedSizeEmbed u)
        (Measure.pi fun _ : Fin u => P.observedLaw)).prod
       (Measure.map (fixedSizeEmbed v)
        (Measure.pi fun _ : Fin v => P.observedLaw)))) := by
  let G := fun sample : Fin n → SampleObs n =>
    (pilotTau n M sample, fixedPrefixSamples n u v h sample)
  have hG : Measurable G :=
    (pilotTau_measurable n M).prodMk (measurable_fixedPrefixSamples n u v h)
  calc
    _ = ∫ z, F z ∂Measure.map G
        (DiscreteAteHeterogeneityFrontier.productLaw n P) :=
      (integral_map hG.aemeasurable hF.aestronglyMeasurable).symm
    _ = _ := by rw [map_pilotTau_fixedPrefixSamples_productLaw M P h]

/-- On a legal count fibre, the implemented output is the clipped pilot plus
the existing ideal selected correction evaluated on the classifier prefix
and the arm/cell outcome restrictions of the estimation prefix. -/
-- keep: pointwise representation of the implemented estimator on legal count fibres
lemma conditionalEstimator_eq_idealPrefix_sum {n u v : ℕ}
    (P : Law n) (h : u + v ≤ postPilotSize n) (M rho : ℝ)
    (sample : Fin n → SampleObs n) :
    conditionalEstimator n M rho sample u v =
      clipM M (pilotTau n M sample +
        ∑ k : Fin n, idealSelectedCorrection P k (pilotTau n M sample) rho
          ((fixedPrefixSamples n u v h sample).1,
            prefixOutcomePair (fixedPrefixSamples n u v h sample).2 k)) := by
  rw [conditionalEstimator_eq_prefixSelectedCorrection_sum h M rho sample]
  congr 2
  apply Finset.sum_congr rfl
  intro k hk
  exact prefixSelectedCorrection_eq_idealSelectedCorrection P rho
    (pilotTau n M sample) (fixedPrefixSamples n u v h sample) k

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
