module
public import CausalSmith.Stat.STAT_DiscreteBudgetvalueCurve_Research.Helpers.CitedGates
public import Causalean.Stat.Minimax.ChiSquared
public import Causalean.Stat.Minimax.MinimaxRisk
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.IIDPoisson
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! The fixed two-sample L1 reduction conditional on the cited known-reference gate. -/

@[expose] public section

namespace CausalSmith.Stat.DiscreteBudgetvalueCurve

open MeasureTheory
open scoped BigOperators

/-- Product law of two independent fixed samples. -/
noncomputable abbrev twoSampleLaw {k : ℕ} (n : ℕ)
    (RS : ProbabilitySimplex k × ProbabilitySimplex k) :
    Measure ((Fin n → Fin k) × (Fin n → Fin k)) :=
  Causalean.Stat.Minimax.Multinomial.TwoSampleL1.twoSampleLaw n RS

/-- Every measurable real-valued statistic of the paired samples. -/
abbrev TwoSampleEstimator (n k : ℕ) :=
  Causalean.Stat.Minimax.Multinomial.TwoSampleL1.TwoSampleEstimator n k

/-- Squared risk in the normalized two-sample L1 experiment. -/
noncomputable abbrev twoSampleL1Risk {k : ℕ} (n : ℕ)
    (est : TwoSampleEstimator n k)
    (RS : ProbabilitySimplex k × ProbabilitySimplex k) : ℝ :=
  Causalean.Stat.Minimax.Multinomial.TwoSampleL1.twoSampleL1Risk n est RS

/-- The exact fixed two-sample minimax risk. -/
noncomputable abbrev twoSampleL1MinimaxRisk (n k : ℕ) : ℝ :=
  Causalean.Stat.Minimax.Multinomial.TwoSampleL1.twoSampleL1MinimaxRisk n k

/-- Atom probabilities of the two independent fixed samples factor coordinatewise. With [the specified inputs and conditions](hyp:k,n,R,S,x), [the stated relationship holds](goal). -/
-- @node: twoSampleLaw_singleton
lemma twoSampleLaw_singleton {k : ℕ} (n : ℕ)
    (R S : ProbabilitySimplex k)
    (x : (Fin n → Fin k) × (Fin n → Fin k)) :
    twoSampleLaw n (R, S) {x} =
      (∏ t : Fin n, (simplexPMF R) (x.1 t)) *
        (∏ t : Fin n, (simplexPMF S) (x.2 t)) :=
  Causalean.Stat.Minimax.Multinomial.TwoSampleL1.twoSampleLaw_singleton n R S x

/-- Conditional Jensen for the known-reference reduction: averaging over the
second sample cannot increase squared loss at a fixed first sample. With [the specified inputs and conditions](hyp:k,n,S,est,x,target), [the stated relationship holds](goal). -/
-- @node: twoSampleL1_conditional_jensen
lemma twoSampleL1_conditional_jensen {k n : ℕ}
    (S : ProbabilitySimplex k) (est : TwoSampleEstimator n k)
    (x : Fin n → Fin k) (target : ℝ) :
    (∫ y, est.1 (x, y) ∂simplexSampleLaw S n - target) ^ 2 ≤
      ∫ y, (est.1 (x, y) - target) ^ 2 ∂simplexSampleLaw S n := by
  let μ := simplexSampleLaw S n
  have hprob : IsProbabilityMeasure μ := by
    dsimp [μ, simplexSampleLaw]
    infer_instance
  let : IsProbabilityMeasure μ := hprob
  have hfun : Integrable (fun y => est.1 (x, y) - target) μ := Integrable.of_finite
  have hsq : Integrable (fun y => (est.1 (x, y) - target) ^ 2) μ :=
    Integrable.of_finite
  have h := (Even.convexOn_pow (show Even (2 : ℕ) by decide) :
    ConvexOn ℝ Set.univ (fun t : ℝ => t ^ 2)).map_integral_le
    (by fun_prop) isClosed_univ (by simp) hfun hsq
  have hshift : (∫ y, est.1 (x, y) - target ∂μ) =
      (∫ y, est.1 (x, y) ∂μ) - target := by
    rw [integral_sub Integrable.of_finite Integrable.of_finite]
    simp
  rw [hshift] at h
  exact h

/-- Integrating conditional Jensen gives the risk comparison used when the
reference distribution is revealed to the estimator. With [the specified inputs and conditions](hyp:k,n,R,S,est), [the stated relationship holds](goal). -/
-- @node: twoSampleL1_conditional_risk_le
lemma twoSampleL1_conditional_risk_le {k n : ℕ}
    (R S : ProbabilitySimplex k) (est : TwoSampleEstimator n k) :
    knownL1Risk n S
      ⟨fun x => ∫ y, est.1 (x, y) ∂simplexSampleLaw S n,
        measurable_of_finite _⟩ R ≤ twoSampleL1Risk n est (R, S) := by
  let μ := simplexSampleLaw R n
  let ν := simplexSampleLaw S n
  let : IsProbabilityMeasure μ := by
    dsimp [μ, simplexSampleLaw]
    infer_instance
  let : IsProbabilityMeasure ν := by
    dsimp [ν, simplexSampleLaw]
    infer_instance
  have hleft : Integrable
      (fun x => (∫ y, est.1 (x, y) ∂ν - simplexL1 R S) ^ 2) μ :=
    Integrable.of_finite
  have hright : Integrable
      (fun x => ∫ y, (est.1 (x, y) - simplexL1 R S) ^ 2 ∂ν) μ :=
    Integrable.of_finite
  have hmono :
      (∫ x, (∫ y, est.1 (x, y) ∂ν - simplexL1 R S) ^ 2 ∂μ) ≤
        ∫ x, ∫ y, (est.1 (x, y) - simplexL1 R S) ^ 2 ∂ν ∂μ := by
    exact integral_mono hleft hright (fun x =>
      twoSampleL1_conditional_jensen S est x (simplexL1 R S))
  change (∫ x, (∫ y, est.1 (x, y) ∂ν - simplexL1 R S) ^ 2 ∂μ) ≤
    ∫ z, (est.1 z - simplexL1 R S) ^ 2 ∂μ.prod ν
  rw [integral_prod _ (Integrable.of_finite : Integrable
    (fun z : (Fin n → Fin k) × (Fin n → Fin k) =>
      (est.1 z - simplexL1 R S) ^ 2) (μ.prod ν))]
  exact hmono

/-- At each fixed reference distribution, the two-sample worst-case risk
dominates the known-reference minimax risk. With [the specified inputs and conditions](hyp:k,n,S), [the stated relationship holds](goal). -/
-- @node: knownL1_worst_bddBelow
lemma knownL1_worst_bddBelow {k n : ℕ} (S : ProbabilitySimplex k) :
    BddBelow (Set.range (fun e : KnownL1Estimator n k =>
      Causalean.Stat.worstCaseRiskReal (knownL1Risk n S) e)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨e, rfl⟩
  apply Real.iSup_nonneg
  intro R
  exact integral_nonneg (fun z => sq_nonneg _)

-- @node: twoSampleL1Risk_bddAbove_all
/-- The two sample l1 risk bdd above all result. It proves [the stated conclusion](goal). -/
lemma twoSampleL1Risk_bddAbove_all {k n : ℕ} [NeZero k]
    (est : TwoSampleEstimator n k) :
    BddAbove (Set.range (twoSampleL1Risk n est)) := by
  obtain ⟨M, hM⟩ := Finite.bddAbove_range
    (fun z : (Fin n → Fin k) × (Fin n → Fin k) => |est.1 z|)
  have hM0 : 0 ≤ M := by
    let z : (Fin n → Fin k) × (Fin n → Fin k) :=
      (fun _ => 0, fun _ => 0)
    exact (abs_nonneg (est.1 z)).trans (hM ⟨z, rfl⟩)
  refine ⟨(M + 2) ^ 2, ?_⟩
  rintro _ ⟨⟨R, S⟩, rfl⟩
  let : IsProbabilityMeasure (twoSampleLaw n (R, S)) := by
    infer_instance
  have hpoint (z : (Fin n → Fin k) × (Fin n → Fin k)) :
      (est.1 z - simplexL1 R S) ^ 2 ≤ (M + 2) ^ 2 := by
    have ht := simplexL1_nonneg_le_two R S
    have he : |est.1 z| ≤ M := hM ⟨z, rfl⟩
    have habs : |est.1 z - simplexL1 R S| ≤ M + 2 := by
      calc
        _ ≤ |est.1 z| + |simplexL1 R S| := by
          simpa using abs_sub_le (est.1 z) 0 (simplexL1 R S)
        _ ≤ M + 2 := by rw [abs_of_nonneg ht.1]; linarith
    have hs : |est.1 z - simplexL1 R S| ^ 2 ≤ (M + 2) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg _) (by linarith)).mpr habs
    simpa only [sq_abs] using hs
  have hi := integral_mono
    (Integrable.of_finite : Integrable
      (fun z : (Fin n → Fin k) × (Fin n → Fin k) =>
        (est.1 z - simplexL1 R S) ^ 2) (twoSampleLaw n (R, S)))
    (integrable_const ((M + 2) ^ 2)) hpoint
  simpa [Causalean.Stat.Minimax.Multinomial.TwoSampleL1.twoSampleL1Risk] using hi

-- @node: twoSampleL1Risk_bddAbove_fixed
/-- The two sample l1 risk bdd above fixed result. It proves [the stated conclusion](goal). -/
lemma twoSampleL1Risk_bddAbove_fixed {k n : ℕ} [NeZero k]
    (S : ProbabilitySimplex k) (est : TwoSampleEstimator n k) :
    BddAbove (Set.range (fun R : ProbabilitySimplex k =>
      twoSampleL1Risk n est (R, S))) := by
  obtain ⟨M, hM⟩ := twoSampleL1Risk_bddAbove_all est
  refine ⟨M, ?_⟩
  rintro _ ⟨R, rfl⟩
  exact hM ⟨(R, S), rfl⟩

-- @node: twoSampleL1_known_reference_le
/-- The two sample l1 known reference le result. It proves [the stated conclusion](goal). -/
lemma twoSampleL1_known_reference_le {k n : ℕ}
    [Nonempty (ProbabilitySimplex k)] [NeZero k]
    (S : ProbabilitySimplex k) (est : TwoSampleEstimator n k) :
    Causalean.Stat.minimaxValueReal (knownL1Risk n S) ≤
      ⨆ R : ProbabilitySimplex k, twoSampleL1Risk n est (R, S) := by
  let e : KnownL1Estimator n k :=
    ⟨fun x => ∫ y, est.1 (x, y) ∂simplexSampleLaw S n,
      measurable_of_finite _⟩
  have hmin : Causalean.Stat.minimaxValueReal (knownL1Risk n S) ≤
      Causalean.Stat.worstCaseRiskReal (knownL1Risk n S) e := by
    exact ciInf_le (knownL1_worst_bddBelow S) e
  have hmax : Causalean.Stat.worstCaseRiskReal (knownL1Risk n S) e ≤
      ⨆ R : ProbabilitySimplex k, twoSampleL1Risk n est (R, S) := by
    apply ciSup_le
    intro R
    exact (twoSampleL1_conditional_risk_le R S est).trans
      (le_ciSup (twoSampleL1Risk_bddAbove_fixed S est) R)
  exact hmin.trans hmax

/-- The fixed-reference minimax lower bound transfers to the experiment
where both distributions are sampled and unknown. With [the specified inputs and conditions](hyp:k,n), [the stated relationship holds](goal). -/
-- @node: twoSampleL1_known_minimax_le
lemma twoSampleL1_known_minimax_le {k n : ℕ}
    [Nonempty (ProbabilitySimplex k)] [NeZero k] :
    sSup (Set.range (fun S : ProbabilitySimplex k =>
      Causalean.Stat.minimaxValueReal (knownL1Risk n S))) ≤
        twoSampleL1MinimaxRisk n k := by
  let : Nonempty (TwoSampleEstimator n k) :=
    ⟨⟨fun _ => 0, measurable_const⟩⟩
  unfold twoSampleL1MinimaxRisk
  unfold Causalean.Stat.Minimax.Multinomial.TwoSampleL1.twoSampleL1MinimaxRisk
    Causalean.Stat.minimaxValueReal
  apply le_ciInf
  intro est
  change sSup (Set.range (fun S : ProbabilitySimplex k =>
      Causalean.Stat.minimaxValueReal (knownL1Risk n S))) ≤
    ⨆ RS, twoSampleL1Risk n est RS
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨S, rfl⟩
  calc
    Causalean.Stat.minimaxValueReal (knownL1Risk n S) ≤
        ⨆ R : ProbabilitySimplex k, twoSampleL1Risk n est (R, S) :=
      twoSampleL1_known_reference_le S est
    _ ≤ ⨆ RS : ProbabilitySimplex k × ProbabilitySimplex k,
        twoSampleL1Risk n est RS := by
      apply ciSup_le
      intro R
      exact le_ciSup (twoSampleL1Risk_bddAbove_all est) (R, S)

/-- The known-reference cited bound applies unchanged to two fixed samples
through conditional averaging over the reference sample. With [the specified inputs and conditions](hyp:of_gate,a0,C0,ha0), [the stated relationship holds](goal). -/
-- @node: twoSampleL1_lower_in_cited_regime
lemma twoSampleL1_lower_in_cited_regime
    (of_gate : JHWKnownQL1LowerRegime) (a0 C0 : ℝ) (ha0 : 0 < a0) :
    ∃ c : ℝ, 0 < c ∧ ∃ k0 : ℕ,
      ∀ k n : ℕ, k0 ≤ k →
        a0 * k / Real.log k ≤ n → Real.log n ≤ C0 * Real.log k →
        c * k / (n * Real.log n) ≤ twoSampleL1MinimaxRisk n k := by
  obtain ⟨c, hc, k0, hk0⟩ := of_gate a0 C0 ha0
  refine ⟨c, hc, max k0 2, ?_⟩
  intro k n hk hsample hlog
  have hk0' : k0 ≤ k := le_trans (le_max_left _ _) hk
  have hk2 : 2 ≤ k := le_trans (le_max_right _ _) hk
  haveI : NeZero k := ⟨by omega⟩
  haveI : Nonempty (ProbabilitySimplex k) := by
    let R : ProbabilitySimplex k :=
      ⟨fun i => if i = 0 then 1 else 0, by
        constructor
        · intro i
          change 0 ≤ (if i = 0 then (1 : ℝ) else 0)
          split_ifs <;> norm_num
        · simp⟩
    exact ⟨R⟩
  exact (hk0 k n hk0' hsample hlog).trans twoSampleL1_known_minimax_le

/-- The cited dense-regime bound with the alphabet logarithm used by the
two-sample theorem. With [the specified inputs and conditions](hyp:of_gate), [the stated relationship holds](goal). -/
-- @node: twoSampleL1_lower_dense_logAlphabet
lemma twoSampleL1_lower_dense_logAlphabet
    (of_gate : JHWKnownQL1LowerRegime) :
    ∃ c : ℝ, 0 < c ∧ ∃ k0 : ℕ,
      ∀ k n : ℕ, k0 ≤ k → 2 ≤ k → 2 ≤ n →
        (k : ℝ) / Real.log k ≤ n →
        Real.log n ≤ 2 * Real.log k →
        c * k / (n * logAlphabet k) ≤ twoSampleL1MinimaxRisk n k := by
  obtain ⟨c, hc, k0, hbound⟩ :=
    twoSampleL1_lower_in_cited_regime of_gate 1 2 (by norm_num)
  refine ⟨c / 2, by positivity, k0, ?_⟩
  intro k n hk hk2 hn hsample hlog
  have hbase := hbound k n hk (by simpa using hsample) hlog
  have hnreal : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlogn : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hkreal : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hlogk : 0 ≤ Real.log k := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
    exact Real.log_nonneg this
  have hL : Real.log k ≤ logAlphabet k := by
    rw [logAlphabet, Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hkreal)]
    simp
  have hlogkpos : 0 < Real.log k := Real.log_pos (by exact_mod_cast (by omega : 1 < k))
  have hLpos : 0 < logAlphabet k := lt_of_lt_of_le hlogkpos hL
  have hden : (n : ℝ) * Real.log n ≤ 2 * ((n : ℝ) * logAlphabet k) := by
    nlinarith
  have hcomp : (c / 2) * k / (n * logAlphabet k) ≤ c * k / (n * Real.log n) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hden
      (le_of_lt (mul_pos hc hkreal))]
  exact hcomp.trans hbase

/-- A finite sample can be read as the initial coordinates of a longer sample. With [the specified inputs and conditions](hyp:k,n,m,hnm,est,R,S), [the stated relationship holds](goal). -/
-- @node: twoSampleL1_prefix_risk
lemma twoSampleL1_prefix_risk {k n m : ℕ} (hnm : n ≤ m)
    (est : TwoSampleEstimator n k) (R S : ProbabilitySimplex k) :
    twoSampleL1Risk m
      ⟨fun z => est.1 (fun i => z.1 (Fin.castLE hnm i),
        fun i => z.2 (Fin.castLE hnm i)), measurable_of_finite _⟩ (R, S) =
      twoSampleL1Risk n est (R, S) := by
  let pref : (Fin m → Fin k) → (Fin n → Fin k) :=
    fun z i => z (Fin.castLE hnm i)
  have hp : Measurable pref := by fun_prop
  have hmap (T : ProbabilitySimplex k) :
      Measure.map pref (simplexSampleLaw T m) = simplexSampleLaw T n := by
    let μ := (simplexPMF T).toMeasure
    haveI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
    have hm : Measurable (fun z : ℕ → Fin k => fun i : Fin m => z i) :=
      measurable_pi_lambda _ fun i => measurable_pi_apply (i : ℕ)
    change Measure.map pref (Measure.pi (fun _ : Fin m => μ)) =
      Measure.pi (fun _ : Fin n => μ)
    rw [← Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.iidStreamLaw_map_finPrefix μ m,
      Measure.map_map hp hm]
    change Measure.map (fun z : ℕ → Fin k => fun i : Fin n => z i)
      (Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.iidStreamLaw μ) = _
    exact Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.iidStreamLaw_map_finPrefix μ n
  have hprod :
      Measure.map (Prod.map pref pref) (twoSampleLaw m (R, S)) =
        twoSampleLaw n (R, S) := by
    unfold twoSampleLaw
    unfold Causalean.Stat.Minimax.Multinomial.TwoSampleL1.twoSampleLaw
    rw [← Measure.map_prod_map _ _ hp hp, hmap R, hmap S]
  have hf : Measurable (fun z : (Fin n → Fin k) × (Fin n → Fin k) =>
      (est.1 z - simplexL1 R S) ^ 2) := measurable_of_finite _
  change (∫ z, (est.1 (Prod.map pref pref z) - simplexL1 R S) ^ 2
      ∂twoSampleLaw m (R, S)) =
    ∫ z, (est.1 z - simplexL1 R S) ^ 2 ∂twoSampleLaw n (R, S)
  rw [← hprod]
  exact (integral_map (hp.prodMap hp).aemeasurable hf.aestronglyMeasurable).symm

/-- Discarding observations shows that the two-sample minimax risk decreases
with the sample size. With [the specified inputs and conditions](hyp:k,n,m,hnm), [the stated relationship holds](goal). -/
-- @node: twoSampleL1_minimax_antitone
lemma twoSampleL1_minimax_antitone {k n m : ℕ} [NeZero k]
    (hnm : n ≤ m) :
    twoSampleL1MinimaxRisk m k ≤ twoSampleL1MinimaxRisk n k := by
  letI : Nonempty (TwoSampleEstimator m k) := ⟨⟨fun _ => 0, measurable_const⟩⟩
  letI : Nonempty (TwoSampleEstimator n k) := ⟨⟨fun _ => 0, measurable_const⟩⟩
  letI : Nonempty (ProbabilitySimplex k) := by
    let R : ProbabilitySimplex k :=
      ⟨fun i => if i = 0 then 1 else 0, by
        constructor
        · intro i
          change 0 ≤ (if i = 0 then (1 : ℝ) else 0)
          split_ifs <;> norm_num
        · simp⟩
    exact ⟨R⟩
  unfold twoSampleL1MinimaxRisk
  unfold Causalean.Stat.Minimax.Multinomial.TwoSampleL1.twoSampleL1MinimaxRisk
    Causalean.Stat.minimaxValueReal
  apply le_ciInf
  intro est
  let est' : TwoSampleEstimator m k :=
    ⟨fun z => est.1 (fun i => z.1 (Fin.castLE hnm i),
      fun i => z.2 (Fin.castLE hnm i)), measurable_of_finite _⟩
  have hbelow : BddBelow (Set.range (fun e : TwoSampleEstimator m k =>
      Causalean.Stat.worstCaseRiskReal (twoSampleL1Risk m) e)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨e, rfl⟩
    apply Real.iSup_nonneg
    intro RS
    exact integral_nonneg (fun z => sq_nonneg _)
  have hmin := ciInf_le hbelow est'
  change (⨅ e : TwoSampleEstimator m k, ⨆ RS, twoSampleL1Risk m e RS) ≤
    ⨆ RS, twoSampleL1Risk n est RS
  apply hmin.trans
  apply ciSup_le
  rintro ⟨R, S⟩
  rw [show twoSampleL1Risk m est' (R, S) = twoSampleL1Risk n est (R, S) from
    twoSampleL1_prefix_risk hnm est R S]
  exact le_ciSup (twoSampleL1Risk_bddAbove_all est) (R, S)

/-- The known-reference gate supplies the claimed two-sample rate throughout
the dense range of large alphabets. With [the specified inputs and conditions](hyp:of_gate), [the stated relationship holds](goal). -/
-- @node: twoSampleL1_lower_large_dense
lemma twoSampleL1_lower_large_dense (of_gate : JHWKnownQL1LowerRegime) :
    ∃ c : ℝ, 0 < c ∧ ∃ k0 : ℕ,
      ∀ k n : ℕ, k0 ≤ k → 2 ≤ k → 2 ≤ n → n ≤ k ^ 2 →
        (k : ℝ) / Real.log k ≤ n →
        c * min 1 ((k : ℝ) / (n * logAlphabet k)) ≤
          twoSampleL1MinimaxRisk n k := by
  obtain ⟨c, hc, k0, hbound⟩ := twoSampleL1_lower_dense_logAlphabet of_gate
  refine ⟨c, hc, k0, ?_⟩
  intro k n hk hk2 hn hnk hsample
  have hlog : Real.log n ≤ 2 * Real.log k := by
    have hkn : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hsq : (n : ℝ) ≤ (k : ℝ) ^ 2 := by exact_mod_cast hnk
    calc
      Real.log n ≤ Real.log ((k : ℝ) ^ 2) := Real.log_le_log hkn hsq
      _ = 2 * Real.log k := by rw [Real.log_pow]; ring
  have hbase := hbound k n hk hk2 hn hsample hlog
  calc
    c * min 1 ((k : ℝ) / (n * logAlphabet k)) ≤
        c * ((k : ℝ) / (n * logAlphabet k)) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) (le_of_lt hc)
    _ = c * k / (n * logAlphabet k) := by ring
    _ ≤ twoSampleL1MinimaxRisk n k := hbase

/-- The two fixed hypotheses used to handle finitely many small alphabets. -/
-- @node: twoSampleL1_pointMass
noncomputable def twoSampleL1_pointMass (k : ℕ) [NeZero k] : ProbabilitySimplex k :=
  ⟨fun i => if i = 0 then 1 else 0, by
    constructor
    · intro i
      change 0 ≤ (if i = 0 then (1 : ℝ) else 0)
      split_ifs <;> norm_num
    · simp⟩

-- @node: twoSampleL1_halfMass
/-- For [k](hyp:k), [hk](hyp:hk), the two sample l1 half mass definition specifies [the stated object](goal). -/
noncomputable def twoSampleL1_halfMass (k : ℕ) (hk : 2 ≤ k) : ProbabilitySimplex k := by
  letI : NeZero k := ⟨by omega⟩
  let i₁ : Fin k := ⟨1, by omega⟩
  refine ⟨fun i => if i = 0 then (1 / 2 : ℝ) else if i = i₁ then 1 / 2 else 0, ?_⟩
  constructor
  · intro i
    change 0 ≤ (if i = 0 then (1 / 2 : ℝ) else if i = i₁ then 1 / 2 else 0)
    split_ifs <;> norm_num
  · have h10 : i₁ ≠ (0 : Fin k) := by simp [i₁]
    simp only [Finset.sum_ite, Finset.sum_singleton]
    have hA : ({x : Fin k | x = 0} : Finset (Fin k)) = {0} := by ext i; simp
    have hB : ({x : Fin k | x ≠ 0 ∧ x = i₁} : Finset (Fin k)) = {i₁} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · exact And.right
      · intro hi
        subst i
        exact ⟨h10, rfl⟩
    simp only [Finset.filter_filter]
    rw [hA, hB]
    norm_num

-- @node: twoSampleL1_fixedTargets
/-- The two sample l1 fixed targets result. Under [the hk premise](hyp:hk), It proves [the stated conclusion](goal). -/
lemma twoSampleL1_fixedTargets (k : ℕ) [NeZero k] (hk : 2 ≤ k) :
    simplexL1 (twoSampleL1_pointMass k) (twoSampleL1_pointMass k) = 0 ∧
    simplexL1 (twoSampleL1_halfMass k hk) (twoSampleL1_pointMass k) = 1 := by
  constructor
  · exact simplexL1_self _
  · calc
      simplexL1 (twoSampleL1_halfMass k hk) (twoSampleL1_pointMass k) =
          ∑ i : Fin k, (twoSampleL1_halfMass k hk).1 i := by
            unfold simplexL1
            apply Finset.sum_congr rfl
            intro i _
            by_cases h0 : i = 0
            · subst i
              norm_num [twoSampleL1_halfMass, twoSampleL1_pointMass]
            · by_cases h1 : i = (⟨1, by omega⟩ : Fin k)
              · simp [twoSampleL1_halfMass, twoSampleL1_pointMass, h0, h1]
              · simp [twoSampleL1_halfMass, twoSampleL1_pointMass, h0, h1]
      _ = 1 := (twoSampleL1_halfMass k hk).2.2

-- @node: twoSampleL1_commonAtom
/-- The two sample l1 common atom result. Under [the hk premise](hyp:hk), It proves [the stated conclusion](goal). -/
lemma twoSampleL1_commonAtom (k n : ℕ) [NeZero k] (hk : 2 ≤ k) :
    let z₀ : (Fin n → Fin k) × (Fin n → Fin k) := (fun _ => 0, fun _ => 0)
    (twoSampleLaw n (twoSampleL1_pointMass k, twoSampleL1_pointMass k) {z₀}).toReal = 1 ∧
    (twoSampleLaw n (twoSampleL1_halfMass k hk, twoSampleL1_pointMass k) {z₀}).toReal =
      (1 / 2 : ℝ) ^ n := by
  dsimp
  constructor
  · rw [twoSampleLaw_singleton]
    simp [simplexPMF,
      Causalean.Stat.Minimax.Multinomial.TwoSampleL1.simplexPMF,
      twoSampleL1_pointMass]
  · rw [twoSampleLaw_singleton]
    simp [simplexPMF,
      Causalean.Stat.Minimax.Multinomial.TwoSampleL1.simplexPMF,
      twoSampleL1_halfMass, twoSampleL1_pointMass]

-- @node: twoSampleL1_atomRisk_le
/-- The two sample l1 atom risk le result. It proves [the stated conclusion](goal). -/
lemma twoSampleL1_atomRisk_le {k n : ℕ}
    (est : TwoSampleEstimator n k) (R S : ProbabilitySimplex k)
    (z : (Fin n → Fin k) × (Fin n → Fin k)) :
    (twoSampleLaw n (R, S)).real {z} *
        (est.1 z - simplexL1 R S) ^ 2 ≤ twoSampleL1Risk n est (R, S) := by
  letI : IsProbabilityMeasure (twoSampleLaw n (R, S)) := by
    infer_instance
  unfold twoSampleL1Risk
  unfold Causalean.Stat.Minimax.Multinomial.TwoSampleL1.twoSampleL1Risk
  rw [integral_fintype (Integrable.of_finite : Integrable
    (fun x => (est.1 x - simplexL1 R S) ^ 2) (twoSampleLaw n (R, S)))]
  simp only [smul_eq_mul]
  refine Finset.single_le_sum
    (f := fun x => (twoSampleLaw n (R, S)).real {x} *
      (est.1 x - simplexL1 R S) ^ 2) ?_ (Finset.mem_univ z)
  intro x _
  exact mul_nonneg (by positivity) (sq_nonneg _)

/-- A common observation atom gives a positive two-point squared-risk bound
at every finite sample size, uniformly over alphabets with two labels. With [the specified inputs and conditions](hyp:k,n,hk), [the stated relationship holds](goal). -/
-- @node: twoSampleL1_finiteAlphabetLower
lemma twoSampleL1_finiteAlphabetLower (k n : ℕ) (hk : 2 ≤ k) :
    (1 / 2 : ℝ) ^ n / 4 ≤ twoSampleL1MinimaxRisk n k := by
  letI : NeZero k := ⟨by omega⟩
  let R₀ := twoSampleL1_pointMass k
  let R₁ := twoSampleL1_halfMass k hk
  let z₀ : (Fin n → Fin k) × (Fin n → Fin k) := (fun _ => 0, fun _ => 0)
  let p : ℝ := (1 / 2 : ℝ) ^ n
  have hp : 0 < p := by dsimp [p]; positivity
  have hp1 : p ≤ 1 := by dsimp [p]; exact pow_le_one₀ (by norm_num) (by norm_num)
  have htargets := twoSampleL1_fixedTargets k hk
  have hatom := twoSampleL1_commonAtom k n hk
  letI : Nonempty (TwoSampleEstimator n k) := ⟨⟨fun _ => 0, measurable_const⟩⟩
  unfold twoSampleL1MinimaxRisk
  unfold Causalean.Stat.Minimax.Multinomial.TwoSampleL1.twoSampleL1MinimaxRisk
    Causalean.Stat.minimaxValueReal
  apply le_ciInf
  intro est
  have hr0 := twoSampleL1_atomRisk_le est R₀ R₀ z₀
  have hr1 := twoSampleL1_atomRisk_le est R₁ R₀ z₀
  change (twoSampleLaw n (R₀, R₀) {z₀}).toReal *
    (est.1 z₀ - simplexL1 R₀ R₀) ^ 2 ≤ twoSampleL1Risk n est (R₀, R₀) at hr0
  change (twoSampleLaw n (R₁, R₀) {z₀}).toReal *
    (est.1 z₀ - simplexL1 R₁ R₀) ^ 2 ≤ twoSampleL1Risk n est (R₁, R₀) at hr1
  rw [hatom.1, htargets.1] at hr0
  rw [hatom.2, htargets.2] at hr1
  have hq : p / 2 ≤ p * (est.1 z₀) ^ 2 + p * (est.1 z₀ - 1) ^ 2 := by
    nlinarith [mul_nonneg hp.le (sq_nonneg (2 * est.1 z₀ - 1))]
  have h0' : p * (est.1 z₀) ^ 2 ≤ twoSampleL1Risk n est (R₀, R₀) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hp1) (sq_nonneg (est.1 z₀))]
  have hmax : p / 4 ≤ max (twoSampleL1Risk n est (R₀, R₀))
      (twoSampleL1Risk n est (R₁, R₀)) := by
    nlinarith [le_max_left (twoSampleL1Risk n est (R₀, R₀))
      (twoSampleL1Risk n est (R₁, R₀)),
      le_max_right (twoSampleL1Risk n est (R₀, R₀))
      (twoSampleL1Risk n est (R₁, R₀))]
  have hB := twoSampleL1Risk_bddAbove_all est
  exact hmax.trans (max_le
    (le_ciSup hB (R₀, R₀)) (le_ciSup hB (R₁, R₀)))
end CausalSmith.Stat.DiscreteBudgetvalueCurve
