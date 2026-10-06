module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.MarkedTable
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.Testing
public import Mathlib.MeasureTheory.Integral.Prod

/-! Finite-moment homogeneity testing: Helpers/TwoPrior. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma


/-- Rejection expectations of admissible tests lie in the unit interval. [This is the stated conclusion](goal). -/
-- @node: rejectProb_bounds
lemma rejectProb_bounds (n : ℕ) (law : ObservedLaw) (φ : Test n) :
    0 ≤ rejectProb n law.P φ ∧ rejectProb n law.P φ ≤ 1 := by
  have : IsProbabilityMeasure design := by
    change IsProbabilityMeasure (volume : Measure unitInterval)
    infer_instance
  have : IsProbabilityMeasure (expLaw n law.P) := by
    dsimp [expLaw]
    infer_instance
  refine ⟨integral_nonneg (fun z => (φ.2.2 z).1), ?_⟩
  have h := integral_mono_of_nonneg
    (ae_of_all (expLaw n law.P) (fun z => (φ.2.2 z).1))
    (integrable_const (1 : ℝ))
    (ae_of_all (expLaw n law.P) (fun z => (φ.2.2 z).2))
  simpa [rejectProb] using h

/-- The worst-alternative error is nonnegative, including an empty alternative set. [This is the stated conclusion](goal). -/
-- @node: worstError_nonneg
lemma worstError_nonneg (n : ℕ) (Alt : Set ObservedLaw) (r : ℝ) (φ : Test n) :
    0 ≤ ⨆ law : {law : ObservedLaw // law ∈ Alt ∧ r ≤ hetDist law},
      1-rejectProb n law.1.P φ := by
  let A := {law : ObservedLaw // law ∈ Alt ∧ r ≤ hetDist law}
  by_cases hA : Nonempty A
  · have := hA
    let law : A := Classical.choice hA
    have hb : BddAbove (Set.range (fun law : A => 1-rejectProb n law.1.P φ)) := by
      refine ⟨1, ?_⟩
      rintro _ ⟨law, rfl⟩
      linarith [(rejectProb_bounds n law.1 φ).1]
    exact (sub_nonneg.mpr (rejectProb_bounds n law.1 φ).2).trans (le_ciSup hb law)
  · have : IsEmpty A := not_nonempty_iff.mp hA
    change 0 ≤ ⨆ law : A, 1-rejectProb n law.1.P φ
    rw [Real.iSup_of_isEmpty]

/-- Testingriskon antitone: the displayed mathematical construction or bound. This statement assumes [the hrt condition](hyp:hrt), [the hne condition](hyp:hne). [This is the stated conclusion](goal). -/
-- @node: testingRiskOn_antitone
lemma testingRiskOn_antitone (n : ℕ) (Null Alt : Set ObservedLaw) (r t : ℝ)
    (hrt : r ≤ t) (hne : ∃ law ∈ Alt, t ≤ hetDist law) :
    testingRiskOn n t Null Alt ≤ testingRiskOn n r Null Alt := by
  unfold testingRiskOn
  refine ciInf_mono ?_ ?_
  · refine ⟨0, ?_⟩
    rintro _ ⟨φ, rfl⟩
    exact worstError_nonneg n Alt t φ.1
  · intro φ
    rcases hne with ⟨law, hAlt, ht⟩
    have : Nonempty {law : ObservedLaw // law ∈ Alt ∧ t ≤ hetDist law} :=
      ⟨⟨law, hAlt, ht⟩⟩
    have hb : BddAbove (Set.range (fun law : {law : ObservedLaw // law ∈ Alt ∧ r ≤ hetDist law} =>
        1-rejectProb n law.1.P φ.1)) := by
      refine ⟨1, ?_⟩
      rintro _ ⟨law, rfl⟩
      linarith [(rejectProb_bounds n law.1 φ.1).1]
    apply ciSup_le
    intro law
    exact le_ciSup hb ⟨law.1, law.2.1, hrt.trans law.2.2⟩
/-- A normalized finite prior mixes full iid laws into a probability measure. This statement assumes [the hπ condition](hyp:hπ). [This is the stated conclusion](goal). -/
-- @node: priorMixture_probability
lemma priorMixture_probability (n : ℕ) (π : FinitePrior) (hπ : PriorNormalized π) :
    IsProbabilityMeasure (priorMixture n π) := by
  apply isProbabilityMeasure_iff.mpr
  simp only [priorMixture, Measure.finsetSum_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hπ.1 i), hπ.2]
  norm_num

/-- Integrating the public seed produces a measurable rejection probability in the unit interval. [This is the stated conclusion](goal). -/
-- @node: seedAverage_properties
lemma seedAverage_properties (n : ℕ) (φ : Test n) :
    Measurable (fun data : Dataset n => ∫ u, φ.1 (data,u) ∂design) ∧
    ∀ data : Dataset n, 0 ≤ (∫ u, φ.1 (data,u) ∂design) ∧
      (∫ u, φ.1 (data,u) ∂design) ≤ 1 := by
  have : IsProbabilityMeasure design := by
    change IsProbabilityMeasure (volume : Measure unitInterval)
    infer_instance
  refine ⟨φ.2.1.stronglyMeasurable.integral_prod_right'.measurable, ?_⟩
  intro data
  refine ⟨integral_nonneg (fun u => (φ.2.2 (data,u)).1), ?_⟩
  have h := integral_mono_of_nonneg
    (ae_of_all design (fun u => (φ.2.2 (data,u)).1)) (integrable_const (1 : ℝ))
    (ae_of_all design (fun u => (φ.2.2 (data,u)).2))
  simpa using h

/-- The seed-averaged rejection expectation commutes with a normalized finite prior mixture. This statement assumes [the hπ condition](hyp:hπ). [This is the stated conclusion](goal). -/
-- @node: priorMixture_reject_average
lemma priorMixture_reject_average (n : ℕ) (π : FinitePrior) (hπ : PriorNormalized π)
    (φ : Test n) :
    (∫ data, (∫ u, φ.1 (data,u) ∂design) ∂priorMixture n π) =
      ∑ i, priorWeight π i * rejectProb n (priorLaw π i).P φ := by
  have : IsProbabilityMeasure design := by
    change IsProbabilityMeasure (volume : Measure unitInterval)
    infer_instance
  let f : Dataset n → ℝ := fun data => ∫ u, φ.1 (data,u) ∂design
  have hf := seedAverage_properties n φ
  have hi (μ : Measure (Dataset n)) [IsFiniteMeasure μ] : Integrable f μ := by
    apply Integrable.of_bound hf.1.aestronglyMeasurable 1
    exact ae_of_all μ (fun data => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf.2 data).1]
      exact (hf.2 data).2)
  have hex (law : ObservedLaw) :
      (∫ data, f data ∂Measure.pi (fun _ : Fin n => law.P)) = rejectProb n law.P φ := by
    symm
    apply integral_prod
    apply Integrable.of_bound φ.2.1.aestronglyMeasurable 1
    exact ae_of_all _ (fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (φ.2.2 z).1]
      exact (φ.2.2 z).2)
  change (∫ data, f data ∂(∑ i, ENNReal.ofReal (priorWeight π i) •
    Measure.pi (fun _ : Fin n => (priorLaw π i).P))) = _
  rw [integral_finsetSum_measure (fun i _ => (hi _).smul_measure ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure, ENNReal.toReal_ofReal (hπ.1 _), smul_eq_mul, hex]

/-- Finite two prior testing lower: the displayed mathematical construction or bound. This statement assumes [the h0 condition](hyp:h0), [the h1 condition](hyp:h1), [the hnull condition](hyp:hnull), [the halt condition](hyp:halt). [This is the stated conclusion](goal). -/
-- @node: finite_two_prior_testing_lower
lemma finite_two_prior_testing_lower (n : ℕ) (Null Alt : Set ObservedLaw) (r : ℝ)
    (π0 π1 : FinitePrior) (h0 : PriorNormalized π0) (h1 : PriorNormalized π1)
    (hnull : PriorSupported π0 Null) (halt : PriorSupported π1 {law | law ∈ Alt ∧ r ≤ hetDist law}) :
    9/10-Causalean.Stat.tvDist (priorMixture n π0) (priorMixture n π1) ≤ testingRiskOn n r Null Alt := by
  have : IsProbabilityMeasure (priorMixture n π0) := priorMixture_probability n π0 h0
  have : IsProbabilityMeasure (priorMixture n π1) := priorMixture_probability n π1 h1
  have hindex : ∃ i, 0 < priorWeight π1 i := by
    by_contra h
    have hz : ∀ i, priorWeight π1 i = 0 := by
      intro i
      exact le_antisymm (le_of_not_gt (fun hi => h ⟨i,hi⟩)) (h1.1 i)
    have hs := h1.2
    simp only [hz, Finset.sum_const_zero] at hs
    norm_num at hs
  obtain ⟨i,hi⟩ := hindex
  have : Nonempty {law : ObservedLaw // law ∈ Alt ∧ r ≤ hetDist law} :=
    ⟨⟨priorLaw π1 i, halt i hi⟩⟩
  let zeroTest : Test n := ⟨fun _ => 0, measurable_const, fun _ => by norm_num⟩
  have hz : LevelValid n Null zeroTest := by
    intro law _
    simp [rejectProb, zeroTest]
  have : Nonempty {φ : Test n // LevelValid n Null φ} := ⟨⟨zeroTest,hz⟩⟩
  unfold testingRiskOn
  apply le_ciInf
  intro φ
  let err := ⨆ law : {law : ObservedLaw // law ∈ Alt ∧ r ≤ hetDist law},
    1-rejectProb n law.1.P φ.1
  have hb : BddAbove (Set.range (fun law : {law : ObservedLaw // law ∈ Alt ∧ r ≤ hetDist law} =>
      1-rejectProb n law.1.P φ.1)) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨law,rfl⟩
    linarith [(rejectProb_bounds n law.1 φ.1).1]
  have hnullavg : (∑ j, priorWeight π0 j * rejectProb n (priorLaw π0 j).P φ.1) ≤ 1/10 := by
    calc
      _ ≤ ∑ j, priorWeight π0 j * (1/10) := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : 0 < priorWeight π0 j
        · exact mul_le_mul_of_nonneg_left (φ.2 _ (hnull j hj)) (h0.1 j)
        · have hzero : priorWeight π0 j = 0 := le_antisymm (le_of_not_gt hj) (h0.1 j)
          simp [hzero]
      _ = 1/10 := by rw [← Finset.sum_mul, h0.2]; ring
  have haltavg : 1-(∑ j, priorWeight π1 j * rejectProb n (priorLaw π1 j).P φ.1) ≤ err := by
    calc
      _ = ∑ j, priorWeight π1 j * (1-rejectProb n (priorLaw π1 j).P φ.1) := by
        simp only [mul_sub, mul_one, Finset.sum_sub_distrib, h1.2]
      _ ≤ ∑ j, priorWeight π1 j * err := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : 0 < priorWeight π1 j
        · exact mul_le_mul_of_nonneg_left (le_ciSup hb ⟨priorLaw π1 j, halt j hj⟩) (h1.1 j)
        · have hzero : priorWeight π1 j = 0 := le_antisymm (le_of_not_gt hj) (h1.1 j)
          simp [hzero]
      _ = err := by rw [← Finset.sum_mul, h1.2]; ring
  have hf := seedAverage_properties n φ.1
  have htv := Causalean.Stat.tvDist_integral_range (priorMixture n π0) (priorMixture n π1)
    (fun data => ∫ u, φ.1.1 (data,u) ∂design) hf.1 0 1 (by norm_num)
    (fun data => by simpa using hf.2 data)
  rw [priorMixture_reject_average n π0 h0 φ.1,
    priorMixture_reject_average n π1 h1 φ.1] at htv
  have hgap := (abs_le.mp htv).1
  change 9/10-Causalean.Stat.tvDist (priorMixture n π0) (priorMixture n π1) ≤ err
  nlinarith

/-- Cappedradius ge of failed: the displayed mathematical construction or bound. This statement assumes [the hr condition](hyp:hr), [the hanti condition](hyp:hanti), [the hfailed condition](hyp:hfailed). [This is the stated conclusion](goal). -/
-- @node: cappedRadius_ge_of_failed
lemma cappedRadius_ge_of_failed (D r : ℝ) (B : ℝ → ℝ) (hr : 0 < r ∧ r < D)
    (hanti : AntitoneOn B (Ioo 0 D)) (hfailed : 1/10 < B r) : r ≤ cappedRadius D B := by
  apply le_csInf ⟨D, Or.inr (Set.mem_singleton D)⟩
  intro t ht
  rcases ht with ht | ht
  · by_contra hrt
    have htr : t ≤ r := le_of_not_ge hrt
    have hBr : B r ≤ B t := hanti ⟨ht.1, ht.2.1⟩ hr htr
    exact (not_le_of_gt hfailed) (hBr.trans ht.2.2)
  · exact hr.2.le.trans (le_of_eq (Set.mem_singleton_iff.mp ht).symm)
/-- The explicit rejection rule is Borel measurable and takes values between zero and one. This statement assumes [the hD condition](hyp:hD), [the hr condition](hyp:hr), [the hlevel condition](hyp:hlevel), [the hpower condition](hyp:hpower). [This is the stated conclusion](goal). -/
-- @node: cappedRadius_le_of_test
lemma cappedRadius_le_of_test (n : ℕ) (Null Alt : Set ObservedLaw) (D r : ℝ)
    (hD : 0 ≤ D) (hr : 0 < r) (φ : Test n) (hlevel : LevelValid n Null φ)
    (hpower : r < D → ∀ law ∈ Alt, r ≤ hetDist law → 1-rejectProb n law.P φ ≤ 1/10) :
    cappedRadius D (fun t => testingRiskOn n t Null Alt) ≤ r := by
  have hb : BddBelow ({t | 0 < t ∧ t < D ∧ testingRiskOn n t Null Alt ≤ 1/10} ∪ {D}) := by
    refine ⟨0, ?_⟩
    intro t ht
    rcases ht with ht | ht
    · exact ht.1.le
    · simpa only [Set.mem_singleton_iff.mp ht] using hD
  by_cases hrd : r < D
  · have hrisk : testingRiskOn n r Null Alt ≤ 1/10 := by
      refine ciInf_le_of_le (f := fun ψ : {ψ : Test n // LevelValid n Null ψ} =>
        ⨆ law : {law : ObservedLaw // law ∈ Alt ∧ r ≤ hetDist law},
          1-rejectProb n law.1.P ψ.1) ?_ ⟨φ, hlevel⟩ ?_
      · refine ⟨0, ?_⟩
        rintro _ ⟨ψ, rfl⟩
        exact worstError_nonneg n Alt r ψ.1
      · by_cases hA : Nonempty {law : ObservedLaw // law ∈ Alt ∧ r ≤ hetDist law}
        · have := hA
          apply ciSup_le
          intro law
          exact hpower hrd law.1 law.2.1 law.2.2
        · have := not_nonempty_iff.mp hA
          rw [Real.iSup_of_isEmpty]
          norm_num
    exact csInf_le hb (Or.inl ⟨hr, hrd, hrisk⟩)
  · exact (csInf_le hb (Or.inr (Set.mem_singleton D))).trans (le_of_not_gt hrd)


/-- Fixing the supplied continuous function gives an admissible original-record test. This statement assumes [the n parameter](hyp:n), [the f parameter](hyp:f), [the φ parameter](hyp:φ). [This is the stated defined object](goal). -/
-- @node: oracleTestAt
def oracleTestAt (n : ℕ) (f : Nuisance) (φ : OracleTest n) : Test n :=
  ⟨fun z => φ.1 (f,z), φ.2.1.comp (measurable_const.prodMk measurable_id),
    fun z => φ.2.2 (f,z)⟩

/-- When the entire propensity agrees, fixing its value preserves rejection expectations. This statement assumes [the he condition](hyp:he). [This is the stated conclusion](goal). -/
-- @node: oracleRejectProb_eq_testAt
lemma oracleRejectProb_eq_testAt (n : ℕ) (law : ObservedLaw) (f : Nuisance)
    (φ : OracleTest n) (he : law.e = f) :
    oracleRejectProb n law φ = rejectProb n law.P (oracleTestAt n f φ) := by
  simp only [oracleRejectProb, rejectProb, oracleTestAt, he]

/-- Supplied-propensity rejection expectations are between zero and one. [This is the stated conclusion](goal). -/
-- @node: oracleRejectProb_bounds
lemma oracleRejectProb_bounds (n : ℕ) (law : ObservedLaw) (φ : OracleTest n) :
    0 ≤ oracleRejectProb n law φ ∧ oracleRejectProb n law φ ≤ 1 := by
  rw [oracleRejectProb_eq_testAt n law law.e φ rfl]
  exact rejectProb_bounds n law (oracleTestAt n law.e φ)

/-- A nonempty alternative set has nonnegative worst error in the supplied-propensity experiment. This statement assumes [the hne condition](hyp:hne). [This is the stated conclusion](goal). -/
-- @node: oracleWorstError_nonneg
lemma oracleWorstError_nonneg (n : ℕ) (v : Params) (r : ℝ) (φ : OracleTest n)
    (hne : ∃ law, InModel v law ∧ r ≤ hetDist law) :
    0 ≤ ⨆ law : {law : ObservedLaw // InModel v law ∧ r ≤ hetDist law},
      1-oracleRejectProb n law.1 φ := by
  obtain ⟨law, hm, hr⟩ := hne
  have hb : BddAbove (Set.range (fun law : {law : ObservedLaw // InModel v law ∧ r ≤ hetDist law} =>
      1-oracleRejectProb n law.1 φ)) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨P, rfl⟩
    linarith [(oracleRejectProb_bounds n P.1 φ).1]
  exact (sub_nonneg.mpr (oracleRejectProb_bounds n law φ).2).trans
    (le_ciSup hb ⟨law, hm, hr⟩)

/-- Increasing separation shrinks the worst-alternative set for every calibrated oracle test. This statement assumes [the hrt condition](hyp:hrt), [the hne condition](hyp:hne). [This is the stated conclusion](goal). -/
-- @node: oracleTestingRisk_antitone
lemma oracleTestingRisk_antitone (n : ℕ) (v : Params) (r t : ℝ)
    (hrt : r ≤ t) (hne : ∃ law, InModel v law ∧ t ≤ hetDist law) :
    oracleTestingRisk n v t ≤ oracleTestingRisk n v r := by
  unfold oracleTestingRisk
  refine ciInf_mono ?_ ?_
  · refine ⟨0, ?_⟩
    rintro _ ⟨φ, rfl⟩
    exact oracleWorstError_nonneg n v t φ.1 hne
  · intro φ
    obtain ⟨law, hm, ht⟩ := hne
    have : Nonempty {law : ObservedLaw // InModel v law ∧ t ≤ hetDist law} :=
      ⟨⟨law, hm, ht⟩⟩
    have hb : BddAbove (Set.range (fun law : {law : ObservedLaw // InModel v law ∧ r ≤ hetDist law} =>
        1-oracleRejectProb n law.1 φ.1)) := by
      refine ⟨1, ?_⟩
      rintro _ ⟨P, rfl⟩
      linarith [(oracleRejectProb_bounds n P.1 φ.1).1]
    apply ciSup_le
    intro P
    exact le_ciSup hb ⟨P.1, P.2.1, hrt.trans P.2.2⟩

/-- Strict failure at a legal nonempty separation bounds the capped oracle radius below. This statement assumes [the hr condition](hyp:hr), [the hne condition](hyp:hne), [the hfailed condition](hyp:hfailed). [This is the stated conclusion](goal). -/
-- @node: oracleCriticalRadius_ge_of_failed
lemma oracleCriticalRadius_ge_of_failed (n : ℕ) (v : Params) (r : ℝ)
    (hr : 0 < r ∧ r < maxDist v)
    (hne : ∃ law, InModel v law ∧ r ≤ hetDist law)
    (hfailed : 1/10 < oracleTestingRisk n v r) : r ≤ oracleCriticalRadius n v := by
  apply le_csInf ⟨maxDist v, Or.inr (Set.mem_singleton _)⟩
  intro t ht
  rcases ht with ht | ht
  · by_contra hrt
    have htr : t ≤ r := le_of_not_ge hrt
    have hBr := oracleTestingRisk_antitone n v t r htr hne
    exact (not_le_of_gt hfailed) (hBr.trans ht.2.2)
  · exact hr.2.le.trans (le_of_eq (Set.mem_singleton_iff.mp ht).symm)

/-- A nonempty broad-oracle alternative set has nonnegative worst error. This statement assumes [the hne condition](hyp:hne). [This is the stated conclusion](goal). -/
lemma oracleBroadWorstError_nonneg (n : ℕ) (v : Params) (r : ℝ) (φ : OracleTest n)
    (hne : ∃ law, InOracleModel v law ∧ r ≤ hetDist law) :
    0 ≤ ⨆ law : {law : ObservedLaw // InOracleModel v law ∧ r ≤ hetDist law},
      1-oracleRejectProb n law.1 φ := by
  obtain ⟨law, hm, hr⟩ := hne
  have hb : BddAbove (Set.range (fun law :
      {law : ObservedLaw // InOracleModel v law ∧ r ≤ hetDist law} =>
      1-oracleRejectProb n law.1 φ)) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨P, rfl⟩
    linarith [(oracleRejectProb_bounds n P.1 φ).1]
  exact (sub_nonneg.mpr (oracleRejectProb_bounds n law φ).2).trans
    (le_ciSup hb ⟨law, hm, hr⟩)

/-- Increasing separation shrinks the broad-oracle alternative set. This statement assumes [the hrt condition](hyp:hrt), [the hne condition](hyp:hne). [This is the stated conclusion](goal). -/
lemma oracleBroadTestingRisk_antitone (n : ℕ) (v : Params) (r t : ℝ)
    (hrt : r ≤ t) (hne : ∃ law, InOracleModel v law ∧ t ≤ hetDist law) :
    oracleBroadTestingRisk n v t ≤ oracleBroadTestingRisk n v r := by
  unfold oracleBroadTestingRisk
  refine ciInf_mono ?_ ?_
  · refine ⟨0, ?_⟩
    rintro _ ⟨φ, rfl⟩
    exact oracleBroadWorstError_nonneg n v t φ.1 hne
  · intro φ
    obtain ⟨law, hm, ht⟩ := hne
    have : Nonempty {law : ObservedLaw // InOracleModel v law ∧ t ≤ hetDist law} :=
      ⟨⟨law, hm, ht⟩⟩
    have hb : BddAbove (Set.range (fun law :
        {law : ObservedLaw // InOracleModel v law ∧ r ≤ hetDist law} =>
        1-oracleRejectProb n law.1 φ.1)) := by
      refine ⟨1, ?_⟩
      rintro _ ⟨P, rfl⟩
      linarith [(oracleRejectProb_bounds n P.1 φ.1).1]
    apply ciSup_le
    intro P
    exact le_ciSup hb ⟨P.1, P.2.1, hrt.trans P.2.2⟩

/-- Strict failure at a legal broad-oracle separation bounds its capped radius below. This statement assumes [the hr condition](hyp:hr), [the hne condition](hyp:hne), [the hfailed condition](hyp:hfailed). [This is the stated conclusion](goal). -/
lemma oracleBroadCriticalRadius_ge_of_failed (n : ℕ) (v : Params) (r : ℝ)
    (hr : 0 < r ∧ r < maxDistOracle v)
    (hne : ∃ law, InOracleModel v law ∧ r ≤ hetDist law)
    (hfailed : 1/10 < oracleBroadTestingRisk n v r) :
    r ≤ oracleBroadCriticalRadius n v := by
  apply le_csInf ⟨maxDistOracle v, Or.inr (Set.mem_singleton _)⟩
  intro t ht
  rcases ht with ht | ht
  · by_contra hrt
    have htr : t ≤ r := le_of_not_ge hrt
    have hBr := oracleBroadTestingRisk_antitone n v t r htr hne
    exact (not_le_of_gt hfailed) (hBr.trans ht.2.2)
  · exact hr.2.le.trans (le_of_eq (Set.mem_singleton_iff.mp ht).symm)

/-- Total variation below one half forces an error of at least two fifths at a positive-weight atom. This statement assumes [the hπ condition](hyp:hπ), [the htv condition](hyp:htv), [the hsize condition](hyp:hsize). [This is the stated conclusion](goal). -/
-- @node: single_null_prior_error_witness
lemma single_null_prior_error_witness (n : ℕ) (P0 : ObservedLaw) (π : FinitePrior)
    (hπ : PriorNormalized π)
    (htv : Causalean.Stat.tvDist (Measure.pi (fun _ : Fin n => P0.P)) (priorMixture n π) < 1/2)
    (φ : Test n) (hsize : rejectProb n P0.P φ ≤ 1/10) :
    ∃ i, 0 < priorWeight π i ∧ 2/5 ≤ 1-rejectProb n (priorLaw π i).P φ := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  have : IsProbabilityMeasure (priorMixture n π) := priorMixture_probability n π hπ
  have hf := seedAverage_properties n φ
  have h := Causalean.Stat.tvDist_integral_range
    (Measure.pi (fun _ : Fin n => P0.P)) (priorMixture n π)
    (fun data => ∫ u, φ.1 (data,u) ∂design) hf.1 0 1 (by norm_num)
    (fun data => by simpa using hf.2 data)
  have hex : (∫ data, (∫ u, φ.1 (data,u) ∂design)
      ∂Measure.pi (fun _ : Fin n => P0.P)) = rejectProb n P0.P φ := by
    symm
    apply integral_prod
    apply Integrable.of_bound φ.2.1.aestronglyMeasurable 1
    exact ae_of_all _ (fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (φ.2.2 z).1]
      exact (φ.2.2 z).2)
  rw [hex, priorMixture_reject_average n π hπ φ, mul_one] at h
  have havg : (∑ i, priorWeight π i * rejectProb n (priorLaw π i).P φ) < 3/5 := by
    have hgap := (abs_le.mp h).1
    linarith
  by_contra hn
  have hlow : ∀ i, priorWeight π i*(3/5) ≤
      priorWeight π i*rejectProb n (priorLaw π i).P φ := by
    intro i
    by_cases hi : 0 < priorWeight π i
    · have he : ¬ 2/5 ≤ 1-rejectProb n (priorLaw π i).P φ := fun he => hn ⟨i,hi,he⟩
      exact mul_le_mul_of_nonneg_left (by linarith) (hπ.1 i)
    · have hz : priorWeight π i = 0 := le_antisymm (le_of_not_gt hi) (hπ.1 i)
      simp [hz]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hlow i)
  rw [← Finset.sum_mul, hπ.2, one_mul] at hs
  exact (not_le_of_gt havg) hs

/-- Supplying a common entire propensity adds no information to the finite-prior testing comparison. This statement assumes [the hπ condition](hyp:hπ), [the he condition](hyp:he), [the htv condition](hyp:htv), [the hsize condition](hyp:hsize). [This is the stated conclusion](goal). -/
-- @node: oracle_single_null_prior_error_witness
lemma oracle_single_null_prior_error_witness (n : ℕ) (P0 : ObservedLaw) (π : FinitePrior)
    (hπ : PriorNormalized π)
    (he : ∀ i, 0 < priorWeight π i → (priorLaw π i).e = P0.e)
    (htv : Causalean.Stat.tvDist (Measure.pi (fun _ : Fin n => P0.P)) (priorMixture n π) < 1/2)
    (φ : OracleTest n) (hsize : oracleRejectProb n P0 φ ≤ 1/10) :
    ∃ i, 0 < priorWeight π i ∧ 2/5 ≤ 1-oracleRejectProb n (priorLaw π i) φ := by
  rw [oracleRejectProb_eq_testAt n P0 P0.e φ rfl] at hsize
  obtain ⟨i, hi, herr⟩ := single_null_prior_error_witness n P0 π hπ htv
    (oracleTestAt n P0.e φ) hsize
  exact ⟨i, hi, by rw [oracleRejectProb_eq_testAt n (priorLaw π i) P0.e φ (he i hi)]; exact herr⟩

end CausalSmith.Stat.FinitepHomogeneityDensegamma
