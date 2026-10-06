module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.TObservableUpper
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! TFiniteHonesty -/
public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology BigOperators
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition
universe u


/-- The two stratum masses form a probability partition. [This is the stated conclusion](goal). -/
-- @node: strataProb_bool_sum
lemma strataProb_bool_sum {S : Type*} [MeasurableSpace S]
    (P : Measure (StructSpace S)) [IsProbabilityMeasure P] :
    strataProb P false + strataProb P true = 1 := by
  have hm : MeasurableSet {w : StructSpace S | sX w = false} :=
    measurableSet_eq_fun (by fun_prop) measurable_const
  have hc : {w : StructSpace S | sX w = false}ᶜ = {w | sX w = true} := by
    ext w
    cases sX w <;> simp
  simpa [strataProb, hc] using measureReal_add_measureReal_compl (μ := P) hm

/-- The causal target is the stratum-weighted potential mean, by the finite partition. [Under the stated conditions](hyp:hoverlap,hbounded). [This is the stated conclusion](goal). -/
-- @node: causalTarget_strata
lemma causalTarget_strata {S : Type*} [MeasurableSpace S]
    (E : PathSpace S) (P : Measure (StructSpace S)) [IsProbabilityMeasure P]
    (hoverlap : StratumPositive P) (hbounded : BoundedPotentialOutcomes E P) :
    causalTarget E P = strataProb P false * condPotMean E P false a0 +
      strataProb P true * condPotMean E P true a0 := by
  have hi := potentialOutcome_integrable E P hbounded a0 (by norm_num [a0])
  have hm (x : Bool) : MeasurableSet {w : StructSpace S | sX w = x} :=
    measurableSet_eq_fun (by fun_prop) measurable_const
  have hir (x : Bool) : Integrable
      (fun w => if sX w = x then potentialOutcome E w a0 else 0) P := by
    have heq : (fun w => if sX w = x then potentialOutcome E w a0 else 0) =
        {w : StructSpace S | sX w = x}.indicator (fun w => potentialOutcome E w a0) := by
      funext w
      by_cases hw : sX w = x <;> simp [hw]
    rw [heq]
    exact hi.indicator (hm x)
  have hp (x : Bool) : strataProb P x ≠ 0 := (hoverlap x).ne'
  simp only [condPotMean, mul_div_cancel₀ _ (hp _)]
  rw [← integral_add (hir false) (hir true)]
  apply integral_congr_ae
  filter_upwards [] with w
  cases sX w <;> simp

/-- The unit mean range transfers to the causal target through its probability weights. [Under the stated conditions](hyp:hoverlap,hbounded,hrange). [This is the stated conclusion](goal). -/
-- @node: causalTarget_mem_Icc
lemma causalTarget_mem_Icc {S : Type*} [MeasurableSpace S]
    (E : PathSpace S) (P : Measure (StructSpace S)) [IsProbabilityMeasure P]
    (hoverlap : StratumPositive P) (hbounded : BoundedPotentialOutcomes E P)
    (hrange : MeanRange E P) : causalTarget E P ∈ Icc 0 1 := by
  rw [causalTarget_strata E P hoverlap hbounded]
  have hf := hrange false a0 (by norm_num [a0])
  have ht := hrange true a0 (by norm_num [a0])
  have hs := strataProb_bool_sum P
  have hpf : 0 ≤ strataProb P false := measureReal_nonneg
  have hpt : 0 ≤ strataProb P true := measureReal_nonneg
  constructor
  · nlinarith [mul_nonneg hpf (sub_nonneg.mpr hf.1),
      mul_nonneg hpt (sub_nonneg.mpr ht.1)]
  · nlinarith [mul_nonneg hpf (sub_nonneg.mpr hf.2),
      mul_nonneg hpt (sub_nonneg.mpr ht.2)]

/-- The pushed-forward iid experiment is a probability measure. [This is the stated conclusion](goal). -/
-- @node: experiment_isProbabilityMeasure
lemma experiment_isProbabilityMeasure {S : Type*} [MeasurableSpace S]
    (P : Measure (StructSpace S)) [IsProbabilityMeasure P] (n : ℕ) (sigma : ℝ) :
    IsProbabilityMeasure (experiment n sigma P) := by
  have hm : Measurable (obsMap (S := S) sigma) := by
    unfold obsMap contaminatedDose
    fun_prop
  haveI : IsProbabilityMeasure (obsLaw sigma P) :=
    Measure.isProbabilityMeasure_map hm.aemeasurable
  unfold experiment
  infer_instance

/-- Empirical stratum frequencies form a probability partition on a nonempty frequency block. [Under the stated conditions](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: phat_bool_sum
lemma phat_bool_sum (n : ℕ) (data : Fin n → Obs) (hn : blocksNonempty n) :
    phat n data false + phat n data true = 1 := by
  have hc : ((splitBlock n 0).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr (hn 0 (by omega)))
  unfold phat
  rw [← add_div, ← Finset.sum_add_distrib]
  have hs : (∑ i ∈ splitBlock n 0,
      ((if (data i).1 = false then (1 : ℝ) else 0) +
       (if (data i).1 = true then (1 : ℝ) else 0))) = (splitBlock n 0).card := by
    have hi (i : Fin n) :
        ((if (data i).1 = false then (1 : ℝ) else 0) +
         (if (data i).1 = true then (1 : ℝ) else 0)) = 1 := by
      cases (data i).1 <;> norm_num
    simp_rw [hi]
    simp
  rw [hs, div_self hc]

/-- Projection and empirical probability weights keep the total estimator in the unit outcome range. [This is the stated conclusion](goal). -/
-- @node: totalEstimator_mem_Icc
lemma totalEstimator_mem_Icc (K : ClassConstants) (beta kappa : ℝ) (n : ℕ) (sigma : ℝ)
    (data : Fin n → Obs) : totalEstimator K beta kappa n sigma data ∈ Icc 0 1 := by
  unfold totalEstimator
  split_ifs with hn
  · have hm (x : Bool) : muhat K kappa n data x
        (pairOf sigma (selectedTag K beta kappa n sigma)) ∈ Icc 0 1 := by
      constructor
      · exact le_max_left _ _
      · exact max_le (by norm_num) (min_le_left _ _)
    have hp (x : Bool) : 0 ≤ phat n data x := by
      unfold phat
      positivity
    have hs := phat_bool_sum n data hn
    rw [weightEstimator, Fintype.sum_bool]
    have hf := hm false
    have ht := hm true
    constructor
    · nlinarith [mul_nonneg (hp false) (sub_nonneg.mpr hf.1),
        mul_nonneg (hp true) (sub_nonneg.mpr ht.1)]
    · nlinarith [mul_nonneg (hp false) (sub_nonneg.mpr hf.2),
        mul_nonneg (hp true) (sub_nonneg.mpr ht.2)]
  · norm_num

/-- Nonempty modulo-three blocks require at least three observations. [Under the stated conditions](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: three_le_of_blocksNonempty
lemma three_le_of_blocksNonempty (n : ℕ) (hn : blocksNonempty n) : 3 ≤ n := by
  obtain ⟨i, hi⟩ := hn 2 (by omega)
  have hmod : i.val % 3 = 2 := (Finset.mem_filter.mp hi).2
  have := i.isLt
  omega

/-- Every admissible pair has a strictly positive finite-sample public score. [Under the stated conditions](hyp:hn,hq). [This is the stated conclusion](goal). -/
-- @node: Aq_pos
lemma Aq_pos (K : ClassConstants) (beta kappa sigma : ℝ) (n : ℕ) (hn : 0 < n)
    (q : WeightPair) (hq : PairAdmissible kappa sigma q) :
    0 < Aq K beta kappa n sigma q := by
  have hI : 0 < weightMoment kappa q.q := hq.2.2.2.2.1
  have hB : 0 ≤ Bq K beta kappa q.q := by
    unfold Bq
    apply div_nonneg _ hI.le
    apply mul_nonneg (div_nonneg (K.clo_pos.le.trans K.clo_le_chi) K.clo_pos.le)
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (hq.2.2.1 t ht)
  have hb : 0 < bq K kappa q.q := by unfold bq; have := K.pmin_pos; have := K.clo_pos; positivity
  have hs : 0 ≤ 12 / bq K kappa q.q * Real.sqrt (pubVq K kappa sigma q.ell / n) := by positivity
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hp : 0 < 2 * Real.sqrt (3 / (n : ℝ)) := by positivity
  unfold Aq
  linarith

/-- The interval contains any unit-range target within the declared public radius. [Under the stated conditions](hyp:hn,htheta,herror). [This is the stated conclusion](goal). -/
-- @node: mem_honestInterval_of_abs_le
lemma mem_honestInterval_of_abs_le (K : ClassConstants) (beta kappa alpha : ℝ) (n : ℕ) (sigma theta : ℝ)
    (data : Fin n → Obs) (hn : blocksNonempty n) (htheta : theta ∈ Icc 0 1)
    (herror : |totalEstimator K beta kappa n sigma data - theta| ≤
      score K beta kappa n sigma (selectedTag K beta kappa n sigma) / alpha) :
    theta ∈ honestInterval K beta kappa alpha n sigma data := by
  rw [honestInterval, if_pos hn, mem_Icc]
  obtain ⟨hl, hu⟩ := abs_le.mp herror
  exact ⟨max_le htheta.1 (by linarith), le_min htheta.2 (by linarith)⟩

/-- Clipping cannot increase the length beyond twice the public radius, the score divided by the noncoverage level. [Under the stated conditions](hyp:hn,hscore). [This is the stated conclusion](goal). -/
-- @node: honestInterval_volume_le
lemma honestInterval_volume_le (K : ClassConstants) (beta kappa alpha : ℝ) (n : ℕ) (sigma : ℝ)
    (hn : blocksNonempty n)
    (hscore : 0 ≤ score K beta kappa n sigma (selectedTag K beta kappa n sigma))
    (data : Fin n → Obs) :
    volume (honestInterval K beta kappa alpha n sigma data) ≤
      ENNReal.ofReal (2 * (score K beta kappa n sigma (selectedTag K beta kappa n sigma) / alpha)) := by
  rw [honestInterval, if_pos hn, Real.volume_Icc]
  apply ENNReal.ofReal_le_ofReal
  have hl := le_max_right (0 : ℝ)
    (totalEstimator K beta kappa n sigma data -
      score K beta kappa n sigma (selectedTag K beta kappa n sigma) / alpha)
  have hu := min_le_right (1 : ℝ)
    (totalEstimator K beta kappa n sigma data +
      score K beta kappa n sigma (selectedTag K beta kappa n sigma) / alpha)
  linarith

/-- [For any public class constants](hyp:K), [smoothness exponent positive and at most one](hyp:hbeta), [design exponent between zero and two](hyp:hkappa) and [any noncoverage level strictly between zero and one](hyp:halpha), [the clipped interval covers the causal target with probability at least one minus the noncoverage level at every sample size, and its expected length is at most a constant (depending on the noncoverage level) times the frontier rate, uniformly for large samples](goal). -/
-- @node: thm:finite-honesty
theorem finite_honesty (K : ClassConstants) (beta kappa alpha : ℝ)
    (hbeta : beta ∈ Ioc (0 : ℝ) 1) (hkappa : kappa ∈ Icc (0 : ℝ) 2)
    (halpha : alpha ∈ Ioo (0 : ℝ) 1) : -- @realizes alpha(public noncoverage level in the open unit interval for coverage)
    (∀ (S : Type u) [MeasurableSpace S], ∀ E : PathSpace S, ∀ n : ℕ, ∀ sigma ∈ Icc (0 : ℝ) (1/4),
      ∀ P : modelClass E K beta kappa sigma,
      1-alpha ≤ (experiment n sigma (P.1 : Measure (StructSpace S))).real
        {data | causalTarget E (P.1 : Measure (StructSpace S)) ∈ honestInterval K beta kappa alpha n sigma data}) ∧
    (∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, ∀ (S : Type u) [MeasurableSpace S], ∀ E : PathSpace S, ∀ n ≥ n0,
      ∀ sigma ∈ Icc (0 : ℝ) (1/4), ∀ P : modelClass E K beta kappa sigma,
      (∫⁻ data, volume (honestInterval K beta kappa alpha n sigma data)
        ∂experiment n sigma (P.1 : Measure (StructSpace S))) ≤ ENNReal.ofReal (C*frontierRate beta kappa sigma n)) := by
  constructor
  · intro S _ E n sigma hsigma P
    let μ := experiment n sigma (P.1 : Measure (StructSpace S))
    haveI : IsProbabilityMeasure μ := experiment_isProbabilityMeasure _ n sigma
    have ht := causalTarget_mem_Icc E (P.1 : Measure (StructSpace S))
      P.2.strataPos P.2.boundedPO P.2.meanRange
    by_cases hn : blocksNonempty n
    · have hn3 := three_le_of_blocksNonempty n hn
      obtain ⟨hq, hV, hlaw⟩ := (dictionary_score_rate E K beta kappa hbeta hkappa).1
        n (by omega) sigma hsigma _ (selectedTag_minimizes K beta kappa n sigma).1
      have hpos : 0 < score K beta kappa n sigma (selectedTag K beta kappa n sigma) :=
        Aq_pos K beta kappa sigma n (by omega) _ hq
      have hcert := public_error_certificate E beta kappa hbeta hkappa n hn3 sigma hsigma
        (P.1 : Measure (StructSpace S)) P.2 (iidSampling_holds n sigma _) _ hq (hlaw P) hV
      have hbound : (∫ data, |totalEstimator K beta kappa n sigma data -
          causalTarget E (P.1 : Measure (StructSpace S))| ∂μ) ≤
          score K beta kappa n sigma (selectedTag K beta kappa n sigma) := by
        simpa only [μ, totalEstimator, if_pos hn, score] using hcert
      have hi : Integrable (fun data => |totalEstimator K beta kappa n sigma data -
          causalTarget E (P.1 : Measure (StructSpace S))|) μ := by
        apply Integrable.of_bound (by fun_prop) 1
        filter_upwards [] with data
        have he := totalEstimator_mem_Icc K beta kappa n sigma data
        rw [Real.norm_eq_abs, abs_abs]
        apply abs_le.mpr
        constructor <;> linarith [he.1, he.2, ht.1, ht.2]
      let G := {data | |totalEstimator K beta kappa n sigma data -
        causalTarget E (P.1 : Measure (StructSpace S))| ≤
          score K beta kappa n sigma (selectedTag K beta kappa n sigma) / alpha}
      have hG : MeasurableSet G := measurableSet_le (by fun_prop) measurable_const
      have hmarkov := mul_meas_ge_le_integral_of_nonneg
        (μ := μ) (ae_of_all _ (fun data => abs_nonneg _)) hi
        (score K beta kappa n sigma (selectedTag K beta kappa n sigma) / alpha)
      have hbad : μ.real Gᶜ ≤ alpha := by
        have hm : μ.real Gᶜ ≤ μ.real {data |
            score K beta kappa n sigma (selectedTag K beta kappa n sigma) / alpha ≤
              |totalEstimator K beta kappa n sigma data -
                causalTarget E (P.1 : Measure (StructSpace S))|} := by
          refine measureReal_mono ?_ (measure_ne_top μ _)
          intro data hd
          change ¬ |totalEstimator K beta kappa n sigma data -
            causalTarget E (P.1 : Measure (StructSpace S))| ≤
              score K beta kappa n sigma (selectedTag K beta kappa n sigma) / alpha at hd
          exact (lt_of_not_ge hd).le
        have hsa : 0 < score K beta kappa n sigma (selectedTag K beta kappa n sigma) / alpha :=
          div_pos hpos halpha.1
        have h1 := hmarkov.trans hbound
        have h2 : score K beta kappa n sigma (selectedTag K beta kappa n sigma) / alpha * alpha =
            score K beta kappa n sigma (selectedTag K beta kappa n sigma) :=
          div_mul_cancel₀ _ halpha.1.ne'
        exact hm.trans (le_of_mul_le_mul_left (h1.trans_eq h2.symm) hsa)
      have hgood : 1 - alpha ≤ μ.real G := by
        rw [probReal_compl_eq_one_sub hG] at hbad
        linarith
      apply hgood.trans
      refine measureReal_mono ?_ (measure_ne_top μ _)
      intro data hd
      exact mem_honestInterval_of_abs_le K beta kappa alpha n sigma _ data hn ht hd
    · have heq : {data : Fin n → Obs | causalTarget E (P.1 : Measure (StructSpace S)) ∈
          honestInterval K beta kappa alpha n sigma data} = Set.univ := by
        ext data
        simp only [honestInterval, if_neg hn, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        exact ht
      rw [heq]
      change 1 - alpha ≤ μ.real Set.univ
      rw [probReal_univ]
      linarith [halpha.1]
  · obtain ⟨C, hC, n0, hupper⟩ := observable_upper.{u} K beta kappa hbeta hkappa
    refine ⟨(2/alpha) * C, mul_pos (div_pos two_pos halpha.1) hC, max 3 n0, ?_⟩
    intro S _ E n hn sigma hsigma P
    have hn3 : 3 ≤ n := (le_max_left _ _).trans hn
    have hn0 : n0 ≤ n := (le_max_right _ _).trans hn
    have hblocks := blocksNonempty_of_three n hn3
    obtain ⟨_, hF, hM⟩ := hupper S E n hn0 sigma hsigma
    have hs : score K beta kappa n sigma (selectedTag K beta kappa n sigma) ≤
        C * frontierRate beta kappa sigma n := by
      have hmin := (selectedTag_minimizes K beta kappa n sigma).2
      by_cases hbranch : sigma ≤ (logScale n)^(-1/2 : ℝ)
      · obtain ⟨k, hk, _, _, hscore⟩ := hF hbranch
        exact (hmin _ hk).trans hscore
      · obtain ⟨j, hj, _, _, hscore⟩ := hM (lt_of_not_ge hbranch)
        exact (hmin _ hj).trans hscore
    obtain ⟨hq, _, _⟩ := (dictionary_score_rate E K beta kappa hbeta hkappa).1
      n (by omega) sigma hsigma _ (selectedTag_minimizes K beta kappa n sigma).1
    have hpos : 0 < score K beta kappa n sigma (selectedTag K beta kappa n sigma) :=
      Aq_pos K beta kappa sigma n (by omega) _ hq
    haveI := experiment_isProbabilityMeasure (P.1 : Measure (StructSpace S)) n sigma
    calc
      _ ≤ ∫⁻ _data, ENNReal.ofReal
          (2 * (score K beta kappa n sigma (selectedTag K beta kappa n sigma) / alpha))
          ∂experiment n sigma (P.1 : Measure (StructSpace S)) :=
        lintegral_mono (honestInterval_volume_le K beta kappa alpha n sigma hblocks hpos.le)
      _ = ENNReal.ofReal (2 * (score K beta kappa n sigma (selectedTag K beta kappa n sigma) / alpha)) := by
        simp
      _ ≤ ENNReal.ofReal ((2/alpha) * C * frontierRate beta kappa sigma n) := by
        apply ENNReal.ofReal_le_ofReal
        have h2a : 0 ≤ 2/alpha := div_nonneg zero_le_two halpha.1.le
        calc
          2 * (score K beta kappa n sigma (selectedTag K beta kappa n sigma) / alpha) =
              (2/alpha) * score K beta kappa n sigma (selectedTag K beta kappa n sigma) := by ring
          _ ≤ (2/alpha) * (C * frontierRate beta kappa sigma n) := mul_le_mul_of_nonneg_left hs h2a
          _ = _ := by ring

end CausalSmith.Stat.NoisydoseWeakdesignTransition
