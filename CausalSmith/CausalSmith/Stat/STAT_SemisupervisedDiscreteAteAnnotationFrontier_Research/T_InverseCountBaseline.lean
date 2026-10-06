module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.PoissonInverseCountMarginalEnergy
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.Estimator
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.IndependentOuterBlocks
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.IndependentPoissonHistogram
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.ParametricLabelFloor
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.IndependentPrefix.Risk
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.PairedHistogram.Risk
public import Causalean.Stat.Concentration.Poisson.SelfNormalized.Chernoff

/-! The clipped all-heavy inverse-count upper bound. -/

@[expose] public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

open MeasureTheory ProbabilityTheory Causalean.Stat
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram
open Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix

-- @node: sqRisk_eq_varianceUnder_add_bias_sq
/-- Bias--variance decomposition for the paper's explicit expectation and
variance wrappers.  This is the analytic assembly used after transporting the
Poisson inverse-count statistic to fixed prefixes.  [the stated conditions](hyp:hf) [the stated conclusion](goal). -/
lemma sqRisk_eq_varianceUnder_add_bias_sq {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → Real) (theta : Real)
    (hf : MemLp f 2 μ) :
    (∫ z, (f z - theta) ^ 2 ∂μ) =
      varianceUnder μ f + (expectationUnder μ f - theta) ^ 2 := by
  have hf_int : Integrable f μ := hf.integrable (by norm_num)
  have hf_sq : Integrable (fun z => f z ^ 2) μ := by
    simpa [Pi.pow_apply] using hf.integrable_sq
  rw [varianceUnder, expectationUnder]
  have hleft : (fun z => (f z - theta) ^ 2) =
      fun z => f z ^ 2 - 2 * theta * f z + theta ^ 2 := by
    funext z
    ring
  have hcenter : (fun z => (f z - ∫ y, f y ∂μ) ^ 2) =
      fun z => f z ^ 2 - 2 * (∫ y, f y ∂μ) * f z +
        (∫ y, f y ∂μ) ^ 2 := by
    funext z
    ring
  rw [hleft, hcenter]
  integral_linearity
  simp
  ring

-- @node: poisson_inverse_count_sqRisk_bound
/-- The bias and variance conclusions of `poisson_inverse_count_risk` assemble
into the squared-risk bound needed by the fixed-prefix transfer.  [the stated conditions](hyp:heps,heps2) [the stated conclusion](goal). -/
lemma poisson_inverse_count_sqRisk_bound {eps : Real}
    (heps : 0 < eps) (heps2 : eps < 1 / 2) :
    ∃ C : Real, 0 < C ∧
    ∀ (d : Nat) (u t : Real), 0 < u → 0 < t →
    ∀ (P : DiscreteLaw d), ModelClass d eps P →
      (∫ K, (inverseCountStatistic u K - ateFunctional P) ^ 2
          ∂poissonCountLaw P u t) ≤
        C * (u⁻¹ + t⁻¹) +
          C ^ 2 * (min 1 ((d : Real) / t)) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := poisson_inverse_count_risk heps heps2
  refine ⟨C, hC, ?_⟩
  intro d u t hu ht P hP
  rcases hbound d u t hu ht P hP with ⟨hbias, hvar⟩
  letI : IsProbabilityMeasure (poissonCountLaw P u t) :=
    ⟨by simp [poissonCountLaw]⟩
  letI : IsFiniteMeasure
      (Causalean.Mathlib.Probability.PoissonAddOnePoincare.nestedPairedPoissonMeasure
        (fun x a => Real.toNNReal (u * markedMass P x a))
        (fun x a => Real.toNNReal (t * armMass P x a))) := by
    change IsFiniteMeasure (poissonCountLaw P u t)
    infer_instance
  have hf : MemLp (inverseCountStatistic u) 2 (poissonCountLaw P u t) :=
    (inverseCountStatistic_memLp_and_addOne P (t := t) hu).1
  rw [sqRisk_eq_varianceUnder_add_bias_sq
    (poissonCountLaw P u t) (inverseCountStatistic u) (ateFunctional P) hf]
  apply add_le_add hvar
  rw [← sq_abs]
  simpa [mul_pow] using pow_le_pow_left₀ (abs_nonneg _) hbias 2

/-- Valid-prefix all-heavy statistic using the disjoint outcome and factorial
blocks and their fixed Poisson intensities.  [the stated conditions](hyp:sample,r0,rf) [the stated conclusion](goal). -/
noncomputable def inverseCountPrefixOutput {n m d : Nat}
    (sample : Sample n m d) (r0 rf : Nat) : Real :=
  let bs := blockSizes n m
  let u : Real := bs.M0 / 8
  clipUnit <| ∑ x : Fin d,
    let s1 : Real := labeledBlockCount sample.1 0 r0 x true true
    let s0 : Real := labeledBlockCount sample.1 0 r0 x false true
    let k1 := pooledArmCount sample (bs.M0 + bs.np) bs.nf bs.mp rf x true
    let k0 := pooledArmCount sample (bs.M0 + bs.np) bs.nf bs.mp rf x false
    s1 / u * (k0 + k1 + 1 : Nat) / (k1 + 1 : Nat) -
      s0 / u * (k0 + k1 + 1 : Nat) / (k0 + 1 : Nat)

/-- Clipped, derandomized Poisson-prefix inverse-count estimator.  [the stated conditions](hyp:n,m,d) [the stated conclusion](goal). -/
noncomputable def inverseCountEstimator (n m d : Nat) : Sample n m d → Real :=
  fun sample =>
    let bs := blockSizes n m
    let u : Real := bs.M0 / 8
    let t : Real := (bs.nf + bs.mf : Nat) / 8
    ∑ r0 ∈ Finset.range (bs.M0 + 1),
      ∑ rf ∈ Finset.range (bs.nf + bs.mf + 1),
        (ProbabilityTheory.poissonMeasure (Real.toNNReal u)).real {r0} *
          (ProbabilityTheory.poissonMeasure (Real.toNNReal t)).real {rf} *
          inverseCountPrefixOutput sample r0 rf
/-- The formal statement establishes [the stated conclusion](goal). -/

lemma measurable_inverseCountEstimator (n m d : Nat) :
    Measurable (inverseCountEstimator n m d) := by
  fun_prop
/-- The formal statement establishes [the stated conclusion](goal). -/

lemma inverseCountPrefixOutput_mem_Icc {n m d : Nat}
    (sample : Sample n m d) (r0 rf : Nat) :
    inverseCountPrefixOutput sample r0 rf ∈ Set.Icc (-1 : Real) 1 := by
  dsimp [inverseCountPrefixOutput, clipUnit]
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
/-- The formal statement establishes [the stated conclusion](goal). -/

lemma inverseCountEstimator_mem_Icc (n m d : Nat) (sample : Sample n m d) :
    inverseCountEstimator n m d sample ∈ Set.Icc (-1 : Real) 1 := by
  let bs := blockSizes n m
  let u : Real := bs.M0 / 8
  let t : Real := (bs.nf + bs.mf : Nat) / 8
  let w0 : Nat → Real := fun r =>
    (ProbabilityTheory.poissonMeasure (Real.toNNReal u)).real {r}
  let wf : Nat → Real := fun r =>
    (ProbabilityTheory.poissonMeasure (Real.toNNReal t)).real {r}
  have hw0 (r : Nat) : 0 ≤ w0 r := MeasureTheory.measureReal_nonneg
  have hwf (r : Nat) : 0 ≤ wf r := MeasureTheory.measureReal_nonneg
  have hm0 : ∑ r ∈ Finset.range (bs.M0 + 1), w0 r ≤ 1 :=
    poissonPrefixMass_le_one _ _
  have hmf : ∑ r ∈ Finset.range (bs.nf + bs.mf + 1), wf r ≤ 1 :=
    poissonPrefixMass_le_one _ _
  have hmass :
      (∑ r ∈ Finset.range (bs.M0 + 1), w0 r) *
          (∑ r ∈ Finset.range (bs.nf + bs.mf + 1), wf r) ≤ 1 := by
    have hf0 : 0 ≤ ∑ r ∈ Finset.range (bs.nf + bs.mf + 1), wf r :=
      Finset.sum_nonneg fun _ _ => hwf _
    have hprod := mul_nonneg (sub_nonneg.mpr hm0) hf0
    nlinarith
  have hweights :
      (∑ r0 ∈ Finset.range (bs.M0 + 1),
        ∑ rf ∈ Finset.range (bs.nf + bs.mf + 1), w0 r0 * wf rf) =
        (∑ r ∈ Finset.range (bs.M0 + 1), w0 r) *
          (∑ r ∈ Finset.range (bs.nf + bs.mf + 1), wf r) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r0 _
    rw [Finset.mul_sum]
  change (∑ r0 ∈ Finset.range (bs.M0 + 1),
      ∑ rf ∈ Finset.range (bs.nf + bs.mf + 1),
        w0 r0 * wf rf * inverseCountPrefixOutput sample r0 rf) ∈
          Set.Icc (-1 : Real) 1
  constructor
  · calc
      (-1 : Real) ≤ -((∑ r ∈ Finset.range (bs.M0 + 1), w0 r) *
          (∑ r ∈ Finset.range (bs.nf + bs.mf + 1), wf r)) :=
        neg_le_neg hmass
      _ = ∑ r0 ∈ Finset.range (bs.M0 + 1),
          ∑ rf ∈ Finset.range (bs.nf + bs.mf + 1),
            w0 r0 * wf rf * (-1 : Real) := by
        rw [← hweights]
        simp only [mul_neg, mul_one, Finset.sum_neg_distrib]
      _ ≤ _ := by
        gcongr
        exact (inverseCountPrefixOutput_mem_Icc sample _ _).1
  · calc
      _ ≤ ∑ r0 ∈ Finset.range (bs.M0 + 1),
          ∑ rf ∈ Finset.range (bs.nf + bs.mf + 1),
            w0 r0 * wf rf * (1 : Real) := by
        gcongr
        exact (inverseCountPrefixOutput_mem_Icc sample _ _).2
      _ = (∑ r ∈ Finset.range (bs.M0 + 1), w0 r) *
          (∑ r ∈ Finset.range (bs.nf + bs.mf + 1), wf r) := by
        simpa using hweights
      _ ≤ 1 := hmass

/-- The clipped inverse-count statistic on two unordered finite Poisson
prefixes: complete observations supply the marked numerator counts, while
auxiliary observations supply the arm-denominator counts.  [the stated conditions](hyp:u,s) [the stated conclusion](goal). -/
noncomputable def finitePrefixInverseCountStatistic {d : Nat} (u : Real)
    (s : FiniteSample (Obs d) × FiniteSample (AuxObs d)) : Real :=
  let histL :=
    Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.finiteSampleHistogram
      s.1.points
  let histA :=
    Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.finiteSampleHistogram
      s.2.points
  clipUnit (inverseCountStatistic u fun x a =>
    (histL (x, a, true), histA (x, a)))
/-- The formal statement establishes [the stated conclusion](goal). -/

lemma measurable_finitePrefixInverseCountStatistic {d : Nat}
    (u : Real) : Measurable (finitePrefixInverseCountStatistic (d := d) u) := by
  unfold finitePrefixInverseCountStatistic
  have hclip : Measurable clipUnit := by
    unfold clipUnit
    fun_prop
  have hinv : Measurable (inverseCountStatistic (d := d) u) :=
    measurable_of_countable _
  let counts : FiniteSample (Obs d) × FiniteSample (AuxObs d) → PoissonCounts d :=
    fun s x a => (finiteSampleHistogram s.1.points (x, a, true),
      finiteSampleHistogram s.2.points (x, a))
  have hcounts : Measurable counts := by
    have hL : Measurable (fun s : FiniteSample (Obs d) × FiniteSample (AuxObs d) =>
        finiteSampleHistogram s.1.points) :=
      measurable_finiteSampleHistogram.comp measurable_fst
    have hA : Measurable (fun s : FiniteSample (Obs d) × FiniteSample (AuxObs d) =>
        finiteSampleHistogram s.2.points) :=
      measurable_finiteSampleHistogram.comp measurable_snd
    exact measurable_pi_lambda _ fun x => measurable_pi_lambda _ fun a =>
      ((measurable_pi_apply (x, a, true)).comp hL).prodMk
        ((measurable_pi_apply (x, a)).comp hA)
  change Measurable (clipUnit ∘ inverseCountStatistic u ∘ counts)
  exact hclip.comp (hinv.comp hcounts)
/-- The formal statement establishes [the stated conclusion](goal). -/

lemma finitePrefixInverseCountStatistic_mem_Icc {d : Nat} (u : Real)
    (s : FiniteSample (Obs d) × FiniteSample (AuxObs d)) :
    finitePrefixInverseCountStatistic u s ∈ Set.Icc (-1 : Real) 1 := by
  dsimp [finitePrefixInverseCountStatistic, clipUnit]
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
/-- [the stated conditions](hyp:s) defines [the specified object](goal). -/

def finitePrefixCounts {d : Nat}
    (s : FiniteSample (Obs d) × FiniteSample (AuxObs d)) : PoissonCounts d :=
  let histL := finiteSampleHistogram s.1.points
  let histA := finiteSampleHistogram s.2.points
  fun x a => (histL (x, a, true), histA (x, a))

/-- [Forming inverse-count histograms from finite prefixes is measurable](goal). -/
@[fun_prop] lemma measurable_finitePrefixCounts {d : Nat} :
    Measurable (finitePrefixCounts (d := d)) := by
  unfold finitePrefixCounts
  have hL : Measurable (fun s : FiniteSample (Obs d) × FiniteSample (AuxObs d) =>
      finiteSampleHistogram s.1.points) :=
    measurable_finiteSampleHistogram.comp measurable_fst
  have hA : Measurable (fun s : FiniteSample (Obs d) × FiniteSample (AuxObs d) =>
      finiteSampleHistogram s.2.points) :=
    measurable_finiteSampleHistogram.comp measurable_snd
  exact measurable_pi_lambda _ fun x => measurable_pi_lambda _ fun a =>
    ((measurable_pi_apply (x, a, true)).comp hL).prodMk
      ((measurable_pi_apply (x, a)).comp hA)
/-- The formal statement establishes [the stated conclusion](goal). -/

lemma finitePrefixInverseCountStatistic_eq {d : Nat} (u : Real) :
    finitePrefixInverseCountStatistic (d := d) u =
      clipUnit ∘ inverseCountStatistic u ∘ finitePrefixCounts := by
  rfl
/-- The formal statement establishes [the stated conclusion](goal). -/

lemma finitePrefixCounts_map_independentPoissonPrefixLaw {d : Nat}
    (P : DiscreteLaw d) (u t : NNReal) :
    Measure.map finitePrefixCounts
        (independentPoissonPrefixLaw (obsLaw P) (auxMarginal P).toMeasure u t) =
      Measure.pi fun x : Fin d => Measure.pi fun a : Bool =>
        (poissonMeasure
          (u * ((obsLaw P) ({(x, a, true)} : Set (Obs d))).toNNReal)).prod
        (poissonMeasure
          (t * ((auxMarginal P).toMeasure ({(x, a)} : Set (AuxObs d))).toNNReal)) := by
  let histL : FiniteSample (Obs d) → (Obs d → Nat) :=
    fun s => finiteSampleHistogram s.points
  let histA : FiniteSample (AuxObs d) → (AuxObs d → Nat) :=
    fun s => finiteSampleHistogram s.points
  let extractL : (Obs d → Nat) → (AuxObs d → Nat) :=
    fun h xa => h (xa.1, xa.2, true)
  let pairFlat : (AuxObs d → Nat) × (AuxObs d → Nat) →
      (AuxObs d → Nat × Nat) := fun z xa => (z.1 xa, z.2 xa)
  let curryCounts : (AuxObs d → Nat × Nat) → PoissonCounts d :=
    fun z x a => z (x, a)
  have hL := finitePoissonSampleLaw_map_histogram (obsLaw P) u
  have hA := finitePoissonSampleLaw_map_histogram (auxMarginal P).toMeasure t
  have hextract : Measure.map extractL
      (Measure.pi fun z : Obs d =>
        poissonMeasure (u * ((obsLaw P) {z}).toNNReal)) =
      Measure.pi fun xa : AuxObs d =>
        poissonMeasure (u * ((obsLaw P) {(xa.1, xa.2, true)}).toNNReal) := by
    exact map_pi_finProjection _ (fun xa : AuxObs d => (xa.1, xa.2, true))
      (by
        intro x y h
        apply Prod.ext
        · simpa only using congrArg Prod.fst h
        · simpa only using congrArg (fun z : Obs d => z.2.1) h)
  have hpair := map_prod_pi_pointwisePair
    (fun xa : AuxObs d =>
      poissonMeasure (u * ((obsLaw P) {(xa.1, xa.2, true)}).toNNReal))
    (fun xa : AuxObs d =>
      poissonMeasure (t * ((auxMarginal P).toMeasure {xa}).toNNReal))
  have hcurry : Measure.map curryCounts
      (Measure.pi fun xa : AuxObs d =>
        (poissonMeasure
          (u * ((obsLaw P) {(xa.1, xa.2, true)}).toNNReal)).prod
        (poissonMeasure
          (t * ((auxMarginal P).toMeasure {xa}).toNNReal))) =
      Measure.pi fun x : Fin d => Measure.pi fun a : Bool =>
        (poissonMeasure
          (u * ((obsLaw P) {(x, a, true)}).toNNReal)).prod
        (poissonMeasure
          (t * ((auxMarginal P).toMeasure {(x, a)}).toNNReal)) := by
    change Measure.map (MeasurableEquiv.curry (Fin d) Bool (Nat × Nat))
      (Measure.pi fun xa : AuxObs d =>
        (poissonMeasure
          (u * ((obsLaw P) {(xa.1, xa.2, true)}).toNNReal)).prod
        (poissonMeasure
          (t * ((auxMarginal P).toMeasure {xa}).toNNReal))) = _
    simpa only [Measure.infinitePi_eq_pi] using Measure.infinitePi_map_curry
      (fun x : Fin d => fun a : Bool =>
        (poissonMeasure
          (u * ((obsLaw P) {(x, a, true)}).toNNReal)).prod
        (poissonMeasure
          (t * ((auxMarginal P).toMeasure {(x, a)}).toNNReal)))
  unfold independentPoissonPrefixLaw
  let source := (finitePoissonSampleLaw (obsLaw P) u).prod
    (finitePoissonSampleLaw (auxMarginal P).toMeasure t)
  have hhistL : Measurable histL := measurable_finiteSampleHistogram
  have hhistA : Measurable histA := measurable_finiteSampleHistogram
  have hhistPair : Measurable (Prod.map histL histA) :=
    (hhistL.comp measurable_fst).prodMk (hhistA.comp measurable_snd)
  change Measure.map
      (curryCounts ∘ pairFlat ∘ Prod.map extractL id ∘ Prod.map histL histA)
      source = _
  calc
    _ = Measure.map curryCounts
        (Measure.map pairFlat
          (Measure.map (Prod.map extractL id)
            (Measure.map (Prod.map histL histA) source))) := by
      rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
        Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
        Measure.map_map (measurable_of_countable _) hhistPair]
      rfl
    _ = Measure.map curryCounts
        (Measure.map pairFlat
          (Measure.map (Prod.map extractL id)
            ((Measure.map histL (finitePoissonSampleLaw (obsLaw P) u)).prod
              (Measure.map histA
                (finitePoissonSampleLaw (auxMarginal P).toMeasure t))))) := by
      rw [Measure.map_prod_map _ _ hhistL hhistA]
    _ = Measure.map curryCounts
        (Measure.map pairFlat
          (Measure.map (Prod.map extractL id)
            ((Measure.pi fun z : Obs d =>
                poissonMeasure (u * ((obsLaw P) {z}).toNNReal)).prod
              (Measure.pi fun z : AuxObs d =>
                poissonMeasure (t * ((auxMarginal P).toMeasure {z}).toNNReal))))) := by
      rw [hL, hA]
    _ = Measure.map curryCounts
        (Measure.map pairFlat
          ((Measure.map extractL (Measure.pi fun z : Obs d =>
              poissonMeasure (u * ((obsLaw P) {z}).toNNReal))).prod
            (Measure.map id (Measure.pi fun z : AuxObs d =>
              poissonMeasure (t * ((auxMarginal P).toMeasure {z}).toNNReal))))) := by
      rw [Measure.map_prod_map _ _ (measurable_of_countable _)
        (measurable_of_countable _)]
    _ = Measure.map curryCounts
        (Measure.map pairFlat
          ((Measure.pi fun xa : AuxObs d =>
              poissonMeasure (u * ((obsLaw P) {(xa.1, xa.2, true)}).toNNReal)).prod
            (Measure.pi fun z : AuxObs d =>
              poissonMeasure (t * ((auxMarginal P).toMeasure {z}).toNNReal)))) := by
      rw [hextract, Measure.map_id]
    _ = Measure.map curryCounts
        (Measure.pi fun i : AuxObs d =>
          (poissonMeasure
            (u * ((obsLaw P) {(i.1, i.2, true)}).toNNReal)).prod
          (poissonMeasure
            (t * ((auxMarginal P).toMeasure {i}).toNNReal))) := by rw [hpair]
    _ = _ := hcurry
/-- [the stated conditions](hyp:hu,ht) establishes [the stated conclusion](goal). -/

lemma finitePrefixCounts_map_eq_poissonCountLaw {d : Nat}
    (P : DiscreteLaw d) (u t : Real) (hu : 0 ≤ u) (ht : 0 ≤ t) :
    Measure.map finitePrefixCounts
        (independentPoissonPrefixLaw (obsLaw P) (auxMarginal P).toMeasure
          (Real.toNNReal u) (Real.toNNReal t)) =
      poissonCountLaw P u t := by
  rw [finitePrefixCounts_map_independentPoissonPrefixLaw]
  unfold poissonCountLaw
  congr 1
  funext x
  congr 1
  funext a
  congr 1
  · congr 1
    unfold obsLaw markedMass jointMass
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    rw [Real.toNNReal_mul hu]
    congr 1
    apply NNReal.eq
    simpa [Real.coe_toNNReal] using ENNReal.coe_toNNReal_eq_toReal
      (P.pmf (x, a, true))
  · congr 1
    have haux : (auxMarginal P (x, a)).toReal = armMass P x a := by
      unfold auxMarginal armMass jointMass
      rw [PMF.map_apply, tsum_fintype]
      cases a <;> simp only [Fintype.sum_prod_type] <;> simp
      all_goals
        rw [ENNReal.toReal_add (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)]
    unfold armMass jointMass
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    rw [Real.toNNReal_mul ht]
    congr 1
    apply NNReal.eq
    rw [ENNReal.coe_toNNReal_eq_toReal]
    have hsum : 0 ≤ ∑ y : Bool, (P.pmf (x, a, y)).toReal :=
      Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
    rw [Real.coe_toNNReal _ hsum]
    exact haux
/-- [the stated conditions](hyp:htheta) establishes [the stated conclusion](goal). -/

lemma clipUnit_sq_sub_le (z theta : Real)
    (htheta : theta ∈ Set.Icc (-1 : Real) 1) :
    (clipUnit z - theta) ^ 2 ≤ (z - theta) ^ 2 := by
  unfold clipUnit
  rcases htheta with ⟨htlo, hthi⟩
  by_cases hzlo : z < -1
  · rw [min_eq_right (by linarith), max_eq_left (by linarith)]
    nlinarith [sq_nonneg (z - theta), sq_nonneg (-1 - theta)]
  · by_cases hzhi : 1 < z
    · rw [min_eq_left (by linarith), max_eq_right (by norm_num)]
      nlinarith [sq_nonneg (z - theta), sq_nonneg (1 - theta)]
    · rw [min_eq_right (by linarith), max_eq_right (by linarith)]
/-- [the stated conditions](hyp:hu,ht,htheta) establishes [the stated conclusion](goal). -/

lemma finitePrefixInverseCountStatistic_risk_le_poissonCount {d : Nat}
    (P : DiscreteLaw d) (u t theta : Real) (hu : 0 < u) (ht : 0 ≤ t)
    (htheta : theta ∈ Set.Icc (-1 : Real) 1) :
    sqRisk
        (independentPoissonPrefixLaw (obsLaw P) (auxMarginal P).toMeasure
          (Real.toNNReal u) (Real.toNNReal t))
        (finitePrefixInverseCountStatistic u) theta ≤
      ∫ K, (inverseCountStatistic u K - theta) ^ 2
        ∂poissonCountLaw P u t := by
  let mu := independentPoissonPrefixLaw (obsLaw P) (auxMarginal P).toMeasure
    (Real.toNNReal u) (Real.toNNReal t)
  letI : IsProbabilityMeasure mu := ⟨by
    simp [mu, independentPoissonPrefixLaw]⟩
  letI : IsProbabilityMeasure (poissonCountLaw P u t) :=
    ⟨by simp [poissonCountLaw]⟩
  letI : IsFiniteMeasure
      (Causalean.Mathlib.Probability.PoissonAddOnePoincare.nestedPairedPoissonMeasure
        (fun x a => Real.toNNReal (u * markedMass P x a))
        (fun x a => Real.toNNReal (t * armMass P x a))) := by
    change IsFiniteMeasure (poissonCountLaw P u t)
    infer_instance
  have hmap := finitePrefixCounts_map_eq_poissonCountLaw P u t hu.le ht
  have hleft : Integrable
      (fun s => (finitePrefixInverseCountStatistic u s - theta) ^ 2) mu := by
    apply Integrable.of_bound
      (((measurable_finitePrefixInverseCountStatistic u).sub measurable_const).pow_const 2
        ).aestronglyMeasurable ((1 + |theta|) ^ 2)
    filter_upwards [] with s
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq_le_sq,
      abs_of_nonneg (add_nonneg (by norm_num) (abs_nonneg theta))]
    exact (abs_sub _ _).trans (add_le_add
      (abs_le.2 (finitePrefixInverseCountStatistic_mem_Icc u s)) le_rfl)
  have hright : Integrable (fun K => (inverseCountStatistic u K - theta) ^ 2)
      (poissonCountLaw P u t) :=
    (((inverseCountStatistic_memLp_and_addOne P (t := t) hu).1.sub
      (memLp_const theta)).integrable_sq)
  have hclipright : Integrable
      (fun K => (clipUnit (inverseCountStatistic u K) - theta) ^ 2)
      (poissonCountLaw P u t) := by
    apply Integrable.of_bound
      ((measurable_of_countable _).aestronglyMeasurable) ((1 + |theta|) ^ 2)
    filter_upwards [] with K
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq_le_sq,
      abs_of_nonneg (add_nonneg (by norm_num) (abs_nonneg theta))]
    have hclip : clipUnit (inverseCountStatistic u K) ∈ Set.Icc (-1 : Real) 1 := by
      simp [clipUnit]
    exact (abs_sub _ _).trans (add_le_add
      (abs_le.2 hclip) le_rfl)
  have hclipmap : Integrable
      (fun K => (clipUnit (inverseCountStatistic u K) - theta) ^ 2)
      (Measure.map finitePrefixCounts mu) := by
    rw [hmap]
    exact hclipright
  unfold sqRisk
  rw [finitePrefixInverseCountStatistic_eq]
  change (∫ z, (clipUnit (inverseCountStatistic u (finitePrefixCounts z)) - theta) ^ 2
      ∂mu) ≤ _
  rw [← integral_map
    (f := fun K => (clipUnit (inverseCountStatistic u K) - theta) ^ 2)
    measurable_finitePrefixCounts.aemeasurable
    hclipmap.aestronglyMeasurable, hmap]
  exact integral_mono
    hclipright hright
    (fun K => clipUnit_sq_sub_le _ _ htheta)

/-- The two disjoint fixed pools actually used by the inverse-count estimator.  [the stated conditions](hyp:sample) [the stated conclusion](goal). -/
def inverseCountFixedPools {n m d : Nat} (sample : Sample n m d) :
    (Fin (blockSizes n m).M0 → Obs d) ×
      (Fin ((blockSizes n m).nf + (blockSizes n m).mf) → AuxObs d) := by
  let bs := blockSizes n m
  have hn : bs.M0 + (bs.np + bs.nf) = n := by
    dsimp [bs, blockSizes]
    omega
  have hm : 0 + (bs.mp + bs.mf) = m := by
    dsimp [bs, blockSizes]
    omega
  let labeled := independentOuterBlocks bs.M0 bs.np bs.nf
    (fun i => sample.1 (Fin.cast hn i))
  let auxiliary := independentOuterBlocks 0 bs.mp bs.mf
    (fun i => sample.2 (Fin.cast hm i))
  exact (labeled.1,
    Fin.append (fun i => ((labeled.2 i).1, (labeled.2 i).2.1)) auxiliary.2)

/-- Extracting inverse-count pools for [labeled size, auxiliary size, and dimension](hyp:n,m,d) [is measurable](goal). -/
@[fun_prop] lemma measurable_inverseCountFixedPools (n m d : Nat) :
    Measurable (inverseCountFixedPools (n := n) (m := m) (d := d)) := by
  unfold inverseCountFixedPools
  fun_prop
/-- The formal statement establishes [the stated conclusion](goal). -/

lemma inverseCountFixedPools_map_annotationLaw {n m d : Nat} (P : DiscreteLaw d) :
    Measure.map (inverseCountFixedPools (n := n) (m := m) (d := d))
        (annotationLaw P n m) =
      Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix.fixedPoolsLaw
        (obsLaw P) (auxMarginal P).toMeasure (blockSizes n m).M0
          ((blockSizes n m).nf + (blockSizes n m).mf) := by
  let bs := blockSizes n m
  have hn : bs.M0 + (bs.np + bs.nf) = n := by
    dsimp [bs, blockSizes]
    omega
  have hm : 0 + (bs.mp + bs.mf) = m := by
    dsimp [bs, blockSizes]
    omega
  let castL : (Fin n → Obs d) → Fin (bs.M0 + (bs.np + bs.nf)) → Obs d :=
    fun z i => z (Fin.cast hn i)
  let castA : (Fin m → AuxObs d) → Fin (0 + (bs.mp + bs.mf)) → AuxObs d :=
    fun z i => z (Fin.cast hm i)
  let outerL := independentOuterBlocks bs.M0 bs.np bs.nf ∘ castL
  let outerA := independentOuterBlocks 0 bs.mp bs.mf ∘ castA
  have hcastL : Measure.map castL (labeledProductLaw P n) =
      Measure.pi fun _ : Fin (bs.M0 + (bs.np + bs.nf)) => obsLaw P := by
    exact (MeasureTheory.measurePreserving_piCongrLeft
      (fun _ : Fin (bs.M0 + (bs.np + bs.nf)) => obsLaw P)
      (finCongr hn).symm).map_eq
  have hcastA : Measure.map castA (auxProductLaw P m) =
      Measure.pi fun _ : Fin (0 + (bs.mp + bs.mf)) =>
        (auxMarginal P).toMeasure := by
    exact (MeasureTheory.measurePreserving_piCongrLeft
      (fun _ : Fin (0 + (bs.mp + bs.mf)) => (auxMarginal P).toMeasure)
      (finCongr hm).symm).map_eq
  have houterL : Measure.map outerL (labeledProductLaw P n) =
      (Measure.pi fun _ : Fin bs.M0 => obsLaw P).prod
        (Measure.pi fun _ : Fin bs.nf => obsLaw P) := by
    dsimp [outerL]
    rw [← Measure.map_map (measurable_independentOuterBlocks bs.M0 bs.np bs.nf)
      (by fun_prop), hcastL]
    exact map_pi_independentOuterBlocks (obsLaw P) bs.M0 bs.np bs.nf
  have houterA : Measure.map outerA (auxProductLaw P m) =
      (Measure.pi fun _ : Fin 0 => (auxMarginal P).toMeasure).prod
        (Measure.pi fun _ : Fin bs.mf => (auxMarginal P).toMeasure) := by
    dsimp [outerA]
    rw [← Measure.map_map (measurable_independentOuterBlocks 0 bs.mp bs.mf)
      (by fun_prop), hcastA]
    exact map_pi_independentOuterBlocks (auxMarginal P).toMeasure 0 bs.mp bs.mf
  let project : Obs d → AuxObs d := fun z => (z.1, z.2.1)
  have hproject : Measure.map project (obsLaw P) = (auxMarginal P).toMeasure := by
    exact PMF.toMeasure_map (p := P.pmf) (f := project) (by fun_prop)
  have hprojectPi : Measure.map (fun z : Fin bs.nf → Obs d =>
      fun i => project (z i)) (Measure.pi fun _ : Fin bs.nf => obsLaw P) =
      Measure.pi fun _ : Fin bs.nf => (auxMarginal P).toMeasure := by
    rw [Causalean.Stat.map_pi_finCoordinatewise bs.nf (obsLaw P)
      (by fun_prop : Measurable project)]
    simp [hproject]
  unfold annotationLaw
  change Measure.map _ ((labeledProductLaw P n).prod (auxProductLaw P m)) = _
  let stage1 := Prod.map outerL outerA
  let stage2 := fun z :
      ((Fin bs.M0 → Obs d) × (Fin bs.nf → Obs d)) ×
        ((Fin 0 → AuxObs d) × (Fin bs.mf → AuxObs d)) =>
      (z.1.1, Fin.append (fun i => project (z.1.2 i)) z.2.2)
  rw [show inverseCountFixedPools = stage2 ∘ stage1 by
    funext sample
    simp [inverseCountFixedPools, stage1, stage2, outerL, outerA,
      castL, castA, bs, project, Function.comp_def]]
  rw [← Measure.map_map (by fun_prop : Measurable stage2)
    (by fun_prop : Measurable stage1)]
  rw [← Measure.map_prod_map _ _ (by fun_prop : Measurable outerL)
    (by fun_prop : Measurable outerA)]
  rw [houterL, houterA]
  let muA := Measure.pi fun _ : Fin bs.M0 => obsLaw P
  let muL := Measure.pi fun _ : Fin bs.nf => obsLaw P
  let muZ := Measure.pi fun _ : Fin 0 => (auxMarginal P).toMeasure
  let muF := Measure.pi fun _ : Fin bs.mf => (auxMarginal P).toMeasure
  let coord := fun z : Fin bs.nf → Obs d => fun i => project (z i)
  let assoc : (((Fin bs.M0 → Obs d) × (Fin bs.nf → Obs d)) ×
      ((Fin 0 → AuxObs d) × (Fin bs.mf → AuxObs d))) ≃ᵐ
      ((Fin bs.M0 → Obs d) × ((Fin bs.nf → Obs d) ×
        ((Fin 0 → AuxObs d) × (Fin bs.mf → AuxObs d)))) :=
    MeasurableEquiv.prodAssoc
  let drop := fun z : (Fin bs.M0 → Obs d) ×
      ((Fin bs.nf → Obs d) ×
        ((Fin 0 → AuxObs d) × (Fin bs.mf → AuxObs d))) =>
      (z.1, (z.2.1, z.2.2.2))
  let recode :
      (Fin bs.M0 → Obs d) ×
          ((Fin bs.nf → Obs d) × (Fin bs.mf → AuxObs d)) →
        (Fin bs.M0 → Obs d) ×
          ((Fin bs.nf → AuxObs d) × (Fin bs.mf → AuxObs d)) :=
    fun z => (z.1, (coord z.2.1, z.2.2))
  let join :
      (Fin bs.M0 → Obs d) ×
          ((Fin bs.nf → AuxObs d) × (Fin bs.mf → AuxObs d)) →
        (Fin bs.M0 → Obs d) ×
          (Fin (bs.nf + bs.mf) → AuxObs d) :=
    fun z => (z.1, Fin.append z.2.1 z.2.2)
  have hdrop : Measure.map drop (muA.prod (muL.prod (muZ.prod muF))) =
      muA.prod (muL.prod muF) := by
    change Measure.map (Prod.map id (Prod.map id Prod.snd))
      (muA.prod (muL.prod (muZ.prod muF))) = _
    rw [← Measure.map_prod_map _ _ measurable_id (by fun_prop), Measure.map_id]
    rw [← Measure.map_prod_map _ _ measurable_id measurable_snd, Measure.map_id,
      MeasureTheory.measurePreserving_snd.map_eq]
  have hrecode : Measure.map recode (muA.prod (muL.prod muF)) =
      muA.prod ((Measure.pi fun _ : Fin bs.nf => (auxMarginal P).toMeasure).prod muF) := by
    change Measure.map
      (Prod.map (id : (Fin bs.M0 → Obs d) → (Fin bs.M0 → Obs d))
        (Prod.map coord (id : (Fin bs.mf → AuxObs d) →
          (Fin bs.mf → AuxObs d)))) (muA.prod (muL.prod muF)) = _
    rw [← Measure.map_prod_map _ _ measurable_id (by fun_prop), Measure.map_id]
    rw [← Measure.map_prod_map _ _ (by fun_prop : Measurable coord) measurable_id,
      Measure.map_id]
    exact congrArg (muA.prod ·) (congrArg (·.prod muF) hprojectPi)
  have hjoin : Measure.map join
      (muA.prod ((Measure.pi fun _ : Fin bs.nf =>
        (auxMarginal P).toMeasure).prod muF)) =
      muA.prod (Measure.pi fun _ : Fin (bs.nf + bs.mf) =>
        (auxMarginal P).toMeasure) := by
    change Measure.map
      (Prod.map (id : (Fin bs.M0 → Obs d) → (Fin bs.M0 → Obs d))
        (fun z : (Fin bs.nf → AuxObs d) × (Fin bs.mf → AuxObs d) =>
          Fin.append z.1 z.2))
        (muA.prod ((Measure.pi fun _ : Fin bs.nf =>
          (auxMarginal P).toMeasure).prod muF)) = _
    rw [← Measure.map_prod_map _ _ measurable_id (by fun_prop), Measure.map_id]
    exact congrArg (muA.prod ·)
      (map_prod_finAppend (auxMarginal P).toMeasure bs.nf bs.mf)
  unfold Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix.fixedPoolsLaw
  change Measure.map stage2 ((muA.prod muL).prod (muZ.prod muF)) = _
  have hassoc : Measurable assoc := assoc.measurable
  have hdrop_meas : Measurable drop := by fun_prop
  have hrecode_meas : Measurable recode := by fun_prop
  have hjoin_meas : Measurable join := by fun_prop
  have hcomp_meas : Measurable (join ∘ recode ∘ drop) :=
    hjoin_meas.comp (hrecode_meas.comp hdrop_meas)
  calc
    _ = Measure.map join (Measure.map recode
        (Measure.map drop (Measure.map assoc ((muA.prod muL).prod (muZ.prod muF))))) := by
      rw [Measure.map_map hrecode_meas hdrop_meas,
        Measure.map_map hjoin_meas (hrecode_meas.comp hdrop_meas),
        Measure.map_map hcomp_meas hassoc]
      apply congrArg (fun f => Measure.map f ((muA.prod muL).prod (muZ.prod muF)))
      funext z
      rfl
    _ = Measure.map join (Measure.map recode
        (Measure.map drop (muA.prod (muL.prod (muZ.prod muF))))) := by
      rw [Measure.prodAssoc_prod]
    _ = Measure.map join (Measure.map recode (muA.prod (muL.prod muF))) := by
      rw [hdrop]
    _ = Measure.map join
        (muA.prod ((Measure.pi fun _ : Fin bs.nf =>
          (auxMarginal P).toMeasure).prod muF)) := by
      rw [hrecode]
    _ = _ := hjoin

private lemma finiteSampleHistogram_prefixOfLE_eq_filter
    {X : Type*} [MeasurableSpace X] [DecidableEq X] {N r : Nat} (z : Fin N → X)
    (hr : r ≤ N) (v : X) :
    finiteSampleHistogram (prefixOfLE z r hr).points v =
      (Finset.univ.filter fun i : Fin N => i.1 < r ∧ z i = v).card := by
  classical
  unfold finiteSampleHistogram prefixOfLE
  let e : {i : Fin r // z ⟨i.1, lt_of_lt_of_le i.2 hr⟩ = v} ≃
      {i : Fin N // i.1 < r ∧ z i = v} :=
    { toFun := fun i =>
        ⟨⟨i.1.1, lt_of_lt_of_le i.1.2 hr⟩, i.1.2, i.2⟩
      invFun := fun i => ⟨⟨i.1.1, i.2.1⟩, i.2.2⟩
      left_inv := by intro i; apply Subtype.ext; rfl
      right_inv := by intro i; apply Subtype.ext; rfl }
  change Fintype.card {i : Fin r // z ⟨i.1, lt_of_lt_of_le i.2 hr⟩ = v} = _
  rw [Fintype.card_congr e]
  let e' : {i : Fin N // i.1 < r ∧ z i = v} ≃
      ↑(Finset.univ.filter fun i : Fin N => i.1 < r ∧ z i = v) :=
    { toFun := fun i => ⟨i.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.2⟩⟩
      invFun := fun i => ⟨i.1, (Finset.mem_filter.mp i.2).2⟩
      left_inv := by intro i; apply Subtype.ext; rfl
      right_inv := by intro i; apply Subtype.ext; rfl }
  rw [Fintype.card_congr e', Fintype.card_coe]

private lemma card_prefix_offset_eq_filter {X : Type*} [DecidableEq X]
    {N L r offset : Nat} (z : Fin N → X) (hbound : offset + L ≤ N)
    (hr : r ≤ L) (v : X) :
    (Finset.univ.filter fun i : Fin L =>
        i.1 < r ∧ z ⟨offset + i.1, lt_of_lt_of_le (by omega) hbound⟩ = v).card =
      (Finset.univ.filter fun i : Fin N =>
        offset ≤ i.1 ∧ i.1 < offset + r ∧ z i = v).card := by
  classical
  let e : {i : Fin L // i.1 < r ∧
        z ⟨offset + i.1, lt_of_lt_of_le (by omega) hbound⟩ = v} ≃
      {i : Fin N // offset ≤ i.1 ∧ i.1 < offset + r ∧ z i = v} :=
    { toFun := fun i =>
        ⟨⟨offset + i.1.1, lt_of_lt_of_le (by omega) hbound⟩,
          by exact ⟨Nat.le_add_right offset i.1.1,
            Nat.add_lt_add_left i.2.1 offset, i.2.2⟩⟩
      invFun := fun i =>
        ⟨⟨i.1.1 - offset, by
            exact lt_of_lt_of_le
              ((Nat.sub_lt_iff_lt_add' i.2.1).2 i.2.2.1) hr⟩, by
          constructor
          · exact (Nat.sub_lt_iff_lt_add' i.2.1).2 i.2.2.1
          · let j : Fin N := ⟨offset + (i.1.1 - offset), by
                rw [Nat.add_sub_of_le i.2.1]
                exact i.1.2⟩
            have hfin : j = i.1 := by
                apply Fin.ext
                dsimp [j]
                exact Nat.add_sub_of_le i.2.1
            change z j = v
            simpa [hfin] using i.2.2.2⟩
      left_inv := by intro i; apply Subtype.ext; apply Fin.ext; simp
      right_inv := by intro i; apply Subtype.ext; apply Fin.ext; simp; omega }
  let eL : {i : Fin L // i.1 < r ∧
        z ⟨offset + i.1, lt_of_lt_of_le (by omega) hbound⟩ = v} ≃
      ↑(Finset.univ.filter fun i : Fin L => i.1 < r ∧
        z ⟨offset + i.1, lt_of_lt_of_le (by omega) hbound⟩ = v) :=
    { toFun := fun i => ⟨i.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.2⟩⟩
      invFun := fun i => ⟨i.1, (Finset.mem_filter.mp i.2).2⟩
      left_inv := by intro i; apply Subtype.ext; rfl
      right_inv := by intro i; apply Subtype.ext; rfl }
  let eR : {i : Fin N // offset ≤ i.1 ∧ i.1 < offset + r ∧ z i = v} ≃
      ↑(Finset.univ.filter fun i : Fin N =>
        offset ≤ i.1 ∧ i.1 < offset + r ∧ z i = v) :=
    { toFun := fun i => ⟨i.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.2⟩⟩
      invFun := fun i => ⟨i.1, (Finset.mem_filter.mp i.2).2⟩
      left_inv := by intro i; apply Subtype.ext; rfl
      right_inv := by intro i; apply Subtype.ext; rfl }
  rw [← Fintype.card_coe (Finset.univ.filter fun i : Fin L => i.1 < r ∧
      z ⟨offset + i.1, lt_of_lt_of_le (by omega) hbound⟩ = v),
    ← Fintype.card_coe (Finset.univ.filter fun i : Fin N =>
      offset ≤ i.1 ∧ i.1 < offset + r ∧ z i = v),
    ← Fintype.card_congr eL, ← Fintype.card_congr eR,
    Fintype.card_congr e]

private lemma finiteSampleHistogram_prefix_append
    {X : Type*} [MeasurableSpace X] [DecidableEq X] {A B r : Nat}
    (z₁ : Fin A → X) (z₂ : Fin B → X) (hr : r ≤ A + B) (v : X) :
    finiteSampleHistogram (prefixOfLE (Fin.append z₁ z₂) r hr).points v =
      finiteSampleHistogram
          (prefixOfLE z₁ (min r A) (Nat.min_le_right _ _)).points v +
        finiteSampleHistogram
          (prefixOfLE z₂ (r - A) (by omega)).points v := by
  classical
  unfold finiteSampleHistogram prefixOfLE
  let e : {i : Fin r // Fin.append z₁ z₂
        ⟨i.1, lt_of_lt_of_le i.2 hr⟩ = v} ≃
      ({i : Fin (min r A) // z₁ ⟨i.1, lt_of_lt_of_le i.2 (Nat.min_le_right _ _)⟩ = v} ⊕
       {i : Fin (r - A) // z₂
          ⟨i.1, lt_of_lt_of_le i.2 (by omega)⟩ = v}) :=
    { toFun := fun i => if hi : i.1.1 < A then
          Sum.inl ⟨⟨i.1.1, lt_min i.1.2 hi⟩, by
            have hip := i.2
            rw [show ⟨i.1.1, lt_of_lt_of_le i.1.2 hr⟩ =
                Fin.castAdd B ⟨i.1.1, hi⟩ by apply Fin.ext; rfl,
              Fin.append_left] at hip
            exact hip⟩
        else Sum.inr ⟨⟨i.1.1 - A, by omega⟩, by
            have hip := i.2
            rw [show ⟨i.1.1, lt_of_lt_of_le i.1.2 hr⟩ =
                Fin.natAdd A ⟨i.1.1 - A, by omega⟩ by apply Fin.ext; simp; omega,
              Fin.append_right] at hip
            exact hip⟩
      invFun := fun i => match i with
        | Sum.inl j => ⟨⟨j.1.1, by omega⟩, by
            rw [show ⟨j.1.1, lt_of_lt_of_le (by omega) hr⟩ =
                Fin.castAdd B ⟨j.1.1,
                  lt_of_lt_of_le j.1.2 (Nat.min_le_right _ _)⟩ by apply Fin.ext; rfl,
              Fin.append_left]
            exact j.2⟩
        | Sum.inr j => ⟨⟨A + j.1.1, by omega⟩, by
            rw [show ⟨A + j.1.1, lt_of_lt_of_le (by omega) hr⟩ =
                Fin.natAdd A ⟨j.1.1, lt_of_lt_of_le j.1.2 (by omega)⟩ by
                  apply Fin.ext; simp,
              Fin.append_right]
            exact j.2⟩
      left_inv := by
        intro i
        dsimp
        split_ifs with hi
        · apply Subtype.ext
          rfl
        · apply Subtype.ext
          apply Fin.ext
          exact Nat.add_sub_of_le (Nat.le_of_not_gt hi)
      right_inv := by
        intro i
        rcases i with i | i
        · simp [lt_of_lt_of_le i.1.2 (Nat.min_le_right _ _)]
        · simp [Nat.not_lt.mpr (Nat.le_add_right A i.1.1)] }
  change Fintype.card {i : Fin r // Fin.append z₁ z₂
      ⟨i.1, lt_of_lt_of_le i.2 hr⟩ = v} = _
  rw [Fintype.card_congr e, Fintype.card_sum]
  rfl

private lemma finiteSampleHistogram_forgetOutcome {N d : Nat}
    (z : Fin N → Obs d) (x : Fin d) (a : Bool) :
    finiteSampleHistogram (fun i => ((z i).1, (z i).2.1)) (x, a) =
      finiteSampleHistogram z (x, a, false) +
        finiteSampleHistogram z (x, a, true) := by
  classical
  unfold finiteSampleHistogram
  let e : {i : Fin N // ((z i).1, (z i).2.1) = (x, a)} ≃
      ({i : Fin N // z i = (x, a, false)} ⊕
        {i : Fin N // z i = (x, a, true)}) :=
    { toFun := fun i => if hy : (z i.1).2.2 = false then
          Sum.inl ⟨i.1, by
            apply Prod.ext
            · exact congrArg (fun q : Fin d × Bool => q.1) i.2
            · apply Prod.ext
              · exact congrArg (fun q : Fin d × Bool => q.2) i.2
              · exact hy⟩
        else Sum.inr ⟨i.1, by
          have hy' : (z i.1).2.2 = true := by
            cases h : (z i.1).2.2 <;> simp_all
          apply Prod.ext
          · exact congrArg (fun q : Fin d × Bool => q.1) i.2
          · apply Prod.ext
            · exact congrArg (fun q : Fin d × Bool => q.2) i.2
            · exact hy'⟩
      invFun := fun i => match i with
        | Sum.inl j => ⟨j.1, by simpa using congrArg (fun w => (w.1, w.2.1)) j.2⟩
        | Sum.inr j => ⟨j.1, by simpa using congrArg (fun w => (w.1, w.2.1)) j.2⟩
      left_inv := by
        intro i
        dsimp
        split_ifs <;> apply Subtype.ext <;> rfl
      right_inv := by
        intro i
        rcases i with i | i
        · simp [i.2]
        · simp [i.2] }
  rw [Fintype.card_congr e, Fintype.card_sum]

private lemma finiteSampleHistogram_prefix_forgetOutcome {N r d : Nat}
    (z : Fin N → Obs d) (hr : r ≤ N) (x : Fin d) (a : Bool) :
    finiteSampleHistogram
        (prefixOfLE (fun i => ((z i).1, (z i).2.1)) r hr).points (x, a) =
      finiteSampleHistogram (prefixOfLE z r hr).points (x, a, false) +
        finiteSampleHistogram (prefixOfLE z r hr).points (x, a, true) := by
  change finiteSampleHistogram
      (fun i => (((prefixOfLE z r hr).points i).1,
        ((prefixOfLE z r hr).points i).2.1)) (x, a) = _
  exact finiteSampleHistogram_forgetOutcome
    (z := (prefixOfLE z r hr).points) x a
/-- [the stated conditions](hyp:hr0,hrf) establishes [the stated conclusion](goal). -/

lemma finitePrefixInverseCountStatistic_fixedPools {n m d : Nat}
    (sample : Sample n m d) (r0 rf : Nat)
    (hr0 : r0 ≤ (blockSizes n m).M0)
    (hrf : rf ≤ (blockSizes n m).nf + (blockSizes n m).mf) :
    finitePrefixInverseCountStatistic ((blockSizes n m).M0 / 8 : Real)
        (prefixOfLE (inverseCountFixedPools sample).1 r0 hr0,
          prefixOfLE (inverseCountFixedPools sample).2 rf hrf) =
      inverseCountPrefixOutput sample r0 rf := by
  classical
  have hmarked (x : Fin d) (a : Bool) :
      finiteSampleHistogram
          (prefixOfLE (inverseCountFixedPools sample).1 r0 hr0).points
          (x, a, true) = labeledBlockCount sample.1 0 r0 x a true := by
    rw [finiteSampleHistogram_prefixOfLE_eq_filter]
    unfold labeledBlockCount
    have h := card_prefix_offset_eq_filter sample.1
      (offset := 0) (L := (blockSizes n m).M0) (r := r0)
      (by dsimp [blockSizes]; omega) hr0 (x, a, true)
    simpa [inverseCountFixedPools] using h
  have hpooled (x : Fin d) (a : Bool) :
      finiteSampleHistogram
          (prefixOfLE (inverseCountFixedPools sample).2 rf hrf).points (x, a) =
        pooledArmCount sample ((blockSizes n m).M0 + (blockSizes n m).np)
          (blockSizes n m).nf (blockSizes n m).mp rf x a := by
    dsimp only [inverseCountFixedPools]
    rw [finiteSampleHistogram_prefix_append]
    rw [finiteSampleHistogram_prefix_forgetOutcome]
    rw [finiteSampleHistogram_prefixOfLE_eq_filter,
      finiteSampleHistogram_prefixOfLE_eq_filter,
      finiteSampleHistogram_prefixOfLE_eq_filter]
    unfold pooledArmCount labeledArmBlockCount labeledBlockCount auxiliaryBlockCount
    have hL0 := card_prefix_offset_eq_filter sample.1
      (offset := (blockSizes n m).M0 + (blockSizes n m).np)
      (L := (blockSizes n m).nf) (r := min rf (blockSizes n m).nf)
      (by dsimp [blockSizes]; omega) (Nat.min_le_right _ _) (x, a, false)
    have hL1 := card_prefix_offset_eq_filter sample.1
      (offset := (blockSizes n m).M0 + (blockSizes n m).np)
      (L := (blockSizes n m).nf) (r := min rf (blockSizes n m).nf)
      (by dsimp [blockSizes]; omega) (Nat.min_le_right _ _) (x, a, true)
    have hA := card_prefix_offset_eq_filter sample.2
      (offset := (blockSizes n m).mp) (L := (blockSizes n m).mf)
      (r := rf - (blockSizes n m).nf)
      (by dsimp [blockSizes]; omega) (by omega) (x, a)
    simpa [inverseCountFixedPools] using
      (congrArg₂ (fun p q : Nat => p + q)
        (congrArg₂ (fun p q : Nat => p + q) hL0 hL1) hA)
  unfold finitePrefixInverseCountStatistic inverseCountPrefixOutput
  apply congrArg clipUnit
  unfold inverseCountStatistic
  simp_rw [hmarked, hpooled]
/-- The formal statement establishes [the stated conclusion](goal). -/

lemma independentPrefixInverseCountStatistic_fixedPools {n m d : Nat}
    (sample : Sample n m d) :
    independentPrefixRaoBlackwellStatistic
          (Real.toNNReal ((blockSizes n m).M0 / 8 : Real))
          (Real.toNNReal
            (((blockSizes n m).nf + (blockSizes n m).mf : Nat) / 8 : Real))
          (finitePrefixInverseCountStatistic
            ((blockSizes n m).M0 / 8 : Real)) 0
          (inverseCountFixedPools sample) =
      inverseCountEstimator n m d sample := by
  classical
  let bs := blockSizes n m
  let u : Real := bs.M0 / 8
  let t : Real := (bs.nf + bs.mf : Nat) / 8
  let T := finitePrefixInverseCountStatistic (d := d) u
  rw [independentPrefixRaoBlackwellStatistic_eq_integral _ _ T
      (measurable_finitePrefixInverseCountStatistic u) 0]
  have hint : Integrable (fun counts : Nat × Nat =>
      cappedPrefixStatistic T 0
          (((inverseCountFixedPools sample).1, counts.1),
            ((inverseCountFixedPools sample).2, counts.2)))
      ((poissonMeasure (Real.toNNReal u)).prod
        (poissonMeasure (Real.toNNReal t))) := by
    apply Integrable.of_bound
      ((measurable_cappedPrefixStatistic
          (measurable_finitePrefixInverseCountStatistic u) 0).comp
          (by fun_prop)).aestronglyMeasurable 1
    filter_upwards [] with z
    rw [Real.norm_eq_abs]
    by_cases h0 : z.1 ≤ bs.M0
    · by_cases hf : z.2 ≤ bs.nf + bs.mf
      · simp only [Function.comp_apply, cappedPrefixStatistic, bs, h0, hf,
          dite_true]
        exact abs_le.2 (finitePrefixInverseCountStatistic_mem_Icc u _)
      · simp [cappedPrefixStatistic, bs, h0, hf]
    · simp [cappedPrefixStatistic, bs, h0]
  rw [MeasureTheory.integral_prod _ hint]
  rw [integral_poissonMeasure]
  simp only [smul_eq_mul]
  rw [tsum_eq_sum (s := Finset.range (bs.M0 + 1))]
  · apply Finset.sum_congr rfl
    intro r0 hr0
    have hr0le : r0 ≤ bs.M0 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr0)
    rw [integral_poissonMeasure]
    simp only [smul_eq_mul]
    rw [tsum_eq_sum (s := Finset.range (bs.nf + bs.mf + 1))]
    · simp only [inverseCountEstimator, bs, u, t]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro rf hrf
      have hrfle : rf ≤ bs.nf + bs.mf :=
        Nat.lt_succ_iff.mp (Finset.mem_range.mp hrf)
      rw [show cappedPrefixStatistic T 0
            (((inverseCountFixedPools sample).1, r0),
              ((inverseCountFixedPools sample).2, rf)) =
            inverseCountPrefixOutput sample r0 rf by
        simp only [cappedPrefixStatistic, bs, hr0le, hrfle, dite_true]
        exact finitePrefixInverseCountStatistic_fixedPools sample r0 rf hr0le hrfle]
      simp only [ProbabilityTheory.poissonMeasure_singleton,
        MeasureTheory.measureReal_def]
      rw [ENNReal.toReal_ofReal (by positivity),
        ENNReal.toReal_ofReal (by positivity)]
      ring
    · intro rf hrf
      have hnot : ¬ rf ≤ bs.nf + bs.mf :=
        fun h => hrf (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr h))
      simp [cappedPrefixStatistic, bs, hr0le, hnot]
  · intro r0 hr0
    have hnot : ¬ r0 ≤ bs.M0 :=
      fun h => hr0 (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr h))
    simp [cappedPrefixStatistic, bs, hnot]
/-- [the stated conditions](hyp:hP) establishes [the stated conclusion](goal). -/

lemma inverseCountEstimator_risk_le_poissonPrefixes {n m d : Nat}
    (eps : Real) (P : DiscreteLaw d) (hP : ModelClass d eps P) :
    twoSampleMSE (annotationLaw P n m) (inverseCountEstimator n m d)
        (ateFunctional P) ≤
      sqRisk
          (independentPoissonPrefixLaw (obsLaw P) (auxMarginal P).toMeasure
            (Real.toNNReal ((blockSizes n m).M0 / 8 : Real))
            (Real.toNNReal
              (((blockSizes n m).nf + (blockSizes n m).mf : Nat) / 8 : Real)))
          (finitePrefixInverseCountStatistic
            ((blockSizes n m).M0 / 8 : Real)) (ateFunctional P) +
        4 * ((poissonMeasure
              (Real.toNNReal ((blockSizes n m).M0 / 8 : Real))).real
                (Set.Ioi (blockSizes n m).M0) +
          (poissonMeasure
              (Real.toNNReal
                (((blockSizes n m).nf + (blockSizes n m).mf : Nat) / 8 : Real))).real
                (Set.Ioi ((blockSizes n m).nf + (blockSizes n m).mf))) := by
  let bs := blockSizes n m
  let u : NNReal := Real.toNNReal (bs.M0 / 8 : Real)
  let t : NNReal := Real.toNNReal ((bs.nf + bs.mf : Nat) / 8 : Real)
  let T := finitePrefixInverseCountStatistic (d := d) (bs.M0 / 8 : Real)
  let RB := independentPrefixRaoBlackwellStatistic
    (NX := bs.M0) (NY := bs.nf + bs.mf) u t T 0
  have htransfer := finiteAlphabet_independentUnequalPrefix_risk_le
    (obsLaw P) (auxMarginal P).toMeasure u t bs.M0 (bs.nf + bs.mf)
      (T := T) (measurable_finitePrefixInverseCountStatistic _) (a := (-1 : Real))
      (b := 1) (theta := ateFunctional P) (zOver := 0) (by norm_num)
      (finitePrefixInverseCountStatistic_mem_Icc _) 
      (ateFunctional_mem_Icc_neg_one_one P hP.overlap) (by norm_num)
  have hRB : inverseCountEstimator n m d = RB ∘ inverseCountFixedPools := by
    funext sample
    exact (independentPrefixInverseCountStatistic_fixedPools sample).symm
  unfold twoSampleMSE
  rw [hRB]
  change (∫ z, (RB (inverseCountFixedPools z) - ateFunctional P) ^ 2
      ∂annotationLaw P n m) ≤ _
  have hf : AEStronglyMeasurable
      (fun z : FixedPools bs.M0 (bs.nf + bs.mf) =>
        (RB z - ateFunctional P) ^ 2)
      (Measure.map inverseCountFixedPools (annotationLaw P n m)) :=
    (measurable_of_countable _).aestronglyMeasurable
  rw [← integral_map
    (f := fun z : FixedPools bs.M0 (bs.nf + bs.mf) =>
      (RB z - ateFunctional P) ^ 2)
    (measurable_inverseCountFixedPools n m d).aemeasurable
    hf]
  rw [inverseCountFixedPools_map_annotationLaw P]
  convert htransfer using 1 <;> norm_num [sqRisk, bs, u, t, T, RB]
/-- [the stated conditions](hyp:hN) establishes [the stated conclusion](goal). -/

lemma poisson_eighth_overflow_le_inv (N : Nat) (hN : 0 < N) :
    (poissonMeasure (Real.toNNReal ((N : Real) / 8))).real (Set.Ioi N) ≤
      8 / (N : Real) := by
  have hNR : 0 < (N : Real) := by exact_mod_cast hN
  have hN8 : 0 ≤ (N : Real) / 8 := by positivity
  have hlam : Real.toNNReal ((N : Real) / 8) = (N : NNReal) / 8 := by
    ext
    simp [hN8]
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
    ((N : NNReal) / 8)
      (z := (N : Real) / 4) (by positivity)
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
/-- [the stated conditions](hyp:hP) establishes [the stated conclusion](goal). -/

lemma inverseCountEstimator_mse_le_four {n m d : Nat} {eps : Real} (P : DiscreteLaw d)
    (hP : ModelClass d eps P) :
    twoSampleMSE (annotationLaw P n m) (inverseCountEstimator n m d)
      (ateFunctional P) ≤ 4 := by
  unfold twoSampleMSE
  letI : IsProbabilityMeasure (annotationLaw P n m) := by
    unfold annotationLaw labeledProductLaw auxProductLaw
    infer_instance
  have htheta := ateFunctional_mem_Icc_neg_one_one P hP.overlap
  calc
    _ ≤ ∫ _z, (4 : Real) ∂annotationLaw P n m := by
      apply integral_mono (Integrable.of_finite) (integrable_const 4)
      intro z
      have hz := inverseCountEstimator_mem_Icc n m d z
      rcases htheta with ⟨htlo, hthi⟩
      rcases hz with ⟨hzlo, hzhi⟩
      nlinarith [sq_nonneg (inverseCountEstimator n m d z - ateFunctional P)]
    _ = 4 := by simp
set_option maxHeartbeats 800000 in
-- @node: thm:inverse-count-baseline
/-- The displayed clipped inverse-count estimator, and hence minimax risk, obey
the baseline `1/n+d²/(n+m)²` bound.  [the stated conditions](hyp:heps,heps2) [the stated conclusion](goal). -/
theorem inverse_count_baseline {eps : Real}
    (heps : 0 < eps) (heps2 : eps < 1 / 2) :
    ∃ C : Real, 0 < C ∧ ∀ (n m d : Nat), 1 ≤ n → 2 ≤ d →
      Measurable (inverseCountEstimator n m d) ∧
      (⨆ P : ClassLaw d eps,
        twoSampleMSE (annotationLaw P.1 n m) (inverseCountEstimator n m d)
          (ateFunctional P.1)) ≤
          C * min 1
            (1 / (n : Real) + (d : Real) ^ 2 / ((n + m : Nat) : Real) ^ 2) ∧
      minimaxRisk n m d eps ≤
          C * min 1
            (1 / (n : Real) + (d : Real) ^ 2 / ((n + m : Nat) : Real) ^ 2) := by
  obtain ⟨C₀, hC₀, hpoisson⟩ := poisson_inverse_count_sqRisk_bound heps heps2
  let C : Real := 100000 * (1 + C₀ + C₀ ^ 2)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro n m d hn hd
  letI : Nonempty (Fin d) := ⟨⟨0, lt_of_lt_of_le Nat.zero_lt_two hd⟩⟩
  let hv0 := Causalean.Estimation.MinimaxATE.Parametric.validDGP_null
    (C := Fin d) (m₀ := (1 / 2 : Real)) (g₀ := (1 / 2 : Real))
    (g₁ := (1 / 2 : Real))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  letI : Nonempty (ClassLaw d eps) := ⟨⟨parametricFloorNullLaw hv0,
    parametricFloorNullLaw_model hd heps heps2 hv0⟩⟩
  have hmeas := measurable_inverseCountEstimator n m d
  have hfixed :
      (⨆ P : ClassLaw d eps,
        twoSampleMSE (annotationLaw P.1 n m) (inverseCountEstimator n m d)
          (ateFunctional P.1)) ≤
          C * min 1
            (1 / (n : Real) + (d : Real) ^ 2 / ((n + m : Nat) : Real) ^ 2) := by
    apply ciSup_le
    intro P
    let bs := blockSizes n m
    let u : Real := bs.M0 / 8
    let t : Real := (bs.nf + bs.mf : Nat) / 8
    let q : Real := 1 / (n : Real) +
      (d : Real) ^ 2 / ((n + m : Nat) : Real) ^ 2
    have hq0 : 0 ≤ q := by dsimp [q]; positivity
    have hmse4 := inverseCountEstimator_mse_le_four (n := n) (m := m) P.1 P.2
    by_cases hn24 : 24 ≤ n
    · have hM0nat : n ≤ 4 * bs.M0 := by
        dsimp [bs, blockSizes]
        omega
      have hFnat : n + m ≤ 4 * (bs.nf + bs.mf) := by
        dsimp [bs, blockSizes]
        omega
      have hM0pos : 0 < bs.M0 := by
        dsimp [bs, blockSizes]
        omega
      have hFpos : 0 < bs.nf + bs.mf := by omega
      have hnR : 0 < (n : Real) := by positivity
      have hNR : 0 < ((n + m : Nat) : Real) := by positivity
      have hu : 0 < u := by dsimp [u]; positivity
      have ht : 0 < t := by dsimp [t]; positivity
      have huLower : (n : Real) / 32 ≤ u := by
        have hc : (n : Real) ≤ 4 * (bs.M0 : Real) := by exact_mod_cast hM0nat
        dsimp [u]
        linarith
      have htLower : ((n + m : Nat) : Real) / 32 ≤ t := by
        have hc : ((n + m : Nat) : Real) ≤
            4 * ((bs.nf + bs.mf : Nat) : Real) := by exact_mod_cast hFnat
        dsimp [t]
        norm_num at hc ⊢
        linarith
      have huInv : u⁻¹ ≤ 32 / (n : Real) := by
        rw [show 32 / (n : Real) = ((n : Real) / 32)⁻¹ by field_simp]
        exact (inv_le_inv₀ (a := u) (b := (n : Real) / 32) hu (by positivity)).2 huLower
      have htInv : t⁻¹ ≤ 32 / ((n + m : Nat) : Real) := by
        rw [show 32 / ((n + m : Nat) : Real) =
            (((n + m : Nat) : Real) / 32)⁻¹ by field_simp]
        exact (inv_le_inv₀ (a := t) (b := ((n + m : Nat) : Real) / 32)
          ht (by positivity)).2 htLower
      have hdt : (d : Real) / t ≤
          32 * (d : Real) / ((n + m : Nat) : Real) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        calc
          (d : Real) * t⁻¹ ≤ (d : Real) * (32 * ((n + m : Nat) : Real)⁻¹) :=
            mul_le_mul_of_nonneg_left htInv (by positivity)
          _ = 32 * (d : Real) * ((n + m : Nat) : Real)⁻¹ := by ring
      have hdt0 : 0 ≤ (d : Real) / t := by positivity
      have hdtSq : (min 1 ((d : Real) / t)) ^ 2 ≤
          1024 * (d : Real) ^ 2 / ((n + m : Nat) : Real) ^ 2 := by
        calc
          _ ≤ ((d : Real) / t) ^ 2 := by
            gcongr
            exact min_le_right _ _
          _ ≤ (32 * (d : Real) / ((n + m : Nat) : Real)) ^ 2 :=
            pow_le_pow_left₀ hdt0 hdt 2
          _ = _ := by ring
      have htail0 := poisson_eighth_overflow_le_inv bs.M0 hM0pos
      have htailf := poisson_eighth_overflow_le_inv (bs.nf + bs.mf) hFpos
      have hM0Inv : 8 / (bs.M0 : Real) ≤ 32 / (n : Real) := by
        apply (div_le_div_iff₀ (by positivity) hnR).2
        have hc : (n : Real) ≤ 4 * (bs.M0 : Real) := by exact_mod_cast hM0nat
        nlinarith
      have hFInv : 8 / ((bs.nf + bs.mf : Nat) : Real) ≤
          32 / ((n + m : Nat) : Real) := by
        apply (div_le_div_iff₀ (by positivity) hNR).2
        have hc : ((n + m : Nat) : Real) ≤
            4 * ((bs.nf + bs.mf : Nat) : Real) := by exact_mod_cast hFnat
        norm_num at hc ⊢
        nlinarith
      have hNInv : 32 / ((n + m : Nat) : Real) ≤ 32 / (n : Real) := by
        apply (div_le_div_iff₀ hNR hnR).2
        have hc : (n : Real) ≤ ((n + m : Nat) : Real) := by
          exact_mod_cast Nat.le_add_right n m
        nlinarith
      have htransfer := inverseCountEstimator_risk_le_poissonPrefixes
        (n := n) (m := m) (d := d) eps P.1 P.2
      have hclip := finitePrefixInverseCountStatistic_risk_le_poissonCount
        P.1 u t (ateFunctional P.1) hu ht.le
          (ateFunctional_mem_Icc_neg_one_one P.1 P.2.overlap)
      have hp := hpoisson d u t hu ht P.1 P.2
      have hquant : twoSampleMSE (annotationLaw P.1 n m)
          (inverseCountEstimator n m d) (ateFunctional P.1) ≤
          (64 * C₀ + 1024 * C₀ ^ 2 + 256) * q := by
        calc
          _ ≤ sqRisk
                (independentPoissonPrefixLaw (obsLaw P.1)
                  (auxMarginal P.1).toMeasure (Real.toNNReal u) (Real.toNNReal t))
                (finitePrefixInverseCountStatistic u) (ateFunctional P.1) +
              4 * ((poissonMeasure (Real.toNNReal u)).real (Set.Ioi bs.M0) +
                (poissonMeasure (Real.toNNReal t)).real
                  (Set.Ioi (bs.nf + bs.mf))) := by
            simpa [bs, u, t] using htransfer
          _ ≤ (∫ K, (inverseCountStatistic u K - ateFunctional P.1) ^ 2
                ∂poissonCountLaw P.1 u t) +
              4 * ((poissonMeasure (Real.toNNReal u)).real (Set.Ioi bs.M0) +
                (poissonMeasure (Real.toNNReal t)).real
                  (Set.Ioi (bs.nf + bs.mf))) := add_le_add hclip le_rfl
          _ ≤ (C₀ * (u⁻¹ + t⁻¹) + C₀ ^ 2 *
                (min 1 ((d : Real) / t)) ^ 2) +
              4 * (8 / (bs.M0 : Real) +
                8 / ((bs.nf + bs.mf : Nat) : Real)) := by
            gcongr
          _ ≤ (64 * C₀ + 1024 * C₀ ^ 2 + 256) * q := by
            have hC0nonneg := hC₀.le
            have hvarTerm : C₀ * (u⁻¹ + t⁻¹) ≤
                64 * C₀ * (1 / (n : Real)) := by
              have htN : t⁻¹ ≤ 32 / (n : Real) := htInv.trans hNInv
              calc
                _ ≤ C₀ * (32 / (n : Real) + 32 / (n : Real)) := by
                  gcongr
                _ = _ := by ring
            have hbiasTerm : C₀ ^ 2 * (min 1 ((d : Real) / t)) ^ 2 ≤
                1024 * C₀ ^ 2 *
                  ((d : Real) ^ 2 / ((n + m : Nat) : Real) ^ 2) := by
              calc
                _ ≤ C₀ ^ 2 *
                    (1024 * (d : Real) ^ 2 /
                      ((n + m : Nat) : Real) ^ 2) := by gcongr
                _ = _ := by ring
            have htailTerm : 4 * (8 / (bs.M0 : Real) +
                8 / ((bs.nf + bs.mf : Nat) : Real)) ≤
                256 * (1 / (n : Real)) := by
              have hfN : 8 / ((bs.nf + bs.mf : Nat) : Real) ≤
                  32 / (n : Real) := hFInv.trans hNInv
              calc
                _ ≤ 4 * (32 / (n : Real) + 32 / (n : Real)) := by gcongr
                _ = _ := by ring
            dsimp [q]
            have hA : 0 ≤ 1 / (n : Real) := by positivity
            have hB : 0 ≤ (d : Real) ^ 2 /
                ((n + m : Nat) : Real) ^ 2 := by positivity
            calc
              _ ≤ (64 * C₀ * (1 / (n : Real)) +
                    1024 * C₀ ^ 2 *
                      ((d : Real) ^ 2 / ((n + m : Nat) : Real) ^ 2)) +
                  256 * (1 / (n : Real)) :=
                add_le_add (add_le_add hvarTerm hbiasTerm) htailTerm
              _ ≤ (64 * C₀ + 1024 * C₀ ^ 2 + 256) *
                  (1 / (n : Real) +
                    (d : Real) ^ 2 / ((n + m : Nat) : Real) ^ 2) := by
                nlinarith [mul_nonneg hC0nonneg hA,
                  mul_nonneg (sq_nonneg C₀) hB]
      have hAleC : 64 * C₀ + 1024 * C₀ ^ 2 + 256 ≤ C := by
        dsimp [C]
        nlinarith [sq_nonneg C₀]
      by_cases hq : q ≤ 1
      · rw [min_eq_right hq]
        exact hquant.trans (mul_le_mul_of_nonneg_right hAleC hq0)
      · rw [min_eq_left (le_of_not_ge hq)]
        exact hmse4.trans (by
          dsimp [C]
          nlinarith [sq_nonneg C₀])
    · have hnle : n ≤ 23 := by omega
      have hnR : 0 < (n : Real) := by positivity
      have hinv : (1 : Real) / 23 ≤ 1 / (n : Real) := by
        apply one_div_le_one_div_of_le hnR
        exact_mod_cast hnle
      have hqLower : (1 : Real) / 23 ≤ min 1 q := by
        apply le_min (by norm_num)
        exact hinv.trans (by
          dsimp [q]
          exact le_add_of_nonneg_right (by positivity))
      exact hmse4.trans (by
        have hCle : 92 ≤ C := by
          dsimp [C]
          nlinarith [sq_nonneg C₀]
        nlinarith)
  refine ⟨hmeas, hfixed, ?_⟩
  unfold minimaxRisk
  have hnonneg (est : {f : Sample n m d → Real // Measurable f}) :
      0 ≤ ⨆ P : ClassLaw d eps,
        twoSampleMSE (annotationLaw P.1 n m) est.1 (ateFunctional P.1) := by
    cases isEmpty_or_nonempty (ClassLaw d eps) with
    | inl hempty =>
        letI := hempty
        simp
    | inr hnonempty =>
        letI := hnonempty
        by_cases hb : BddAbove (Set.range (fun P : ClassLaw d eps =>
            twoSampleMSE (annotationLaw P.1 n m) est.1 (ateFunctional P.1)))
        · exact (integral_nonneg fun z => sq_nonneg
              (est.1 z - ateFunctional (Classical.arbitrary (ClassLaw d eps)).1)).trans
            (le_ciSup hb (Classical.arbitrary _))
        · rw [show (⨆ P : ClassLaw d eps,
              twoSampleMSE (annotationLaw P.1 n m) est.1
                (ateFunctional P.1)) = sSup ∅ from csSup_of_not_bddAbove hb]
          simp
  have hb : BddBelow (Set.range (fun est :
      {f : Sample n m d → Real // Measurable f} =>
        ⨆ P : ClassLaw d eps,
          twoSampleMSE (annotationLaw P.1 n m) est.1 (ateFunctional P.1))) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨est, rfl⟩
    exact hnonneg est
  exact (ciInf_le hb ⟨inverseCountEstimator n m d, hmeas⟩).trans hfixed

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
