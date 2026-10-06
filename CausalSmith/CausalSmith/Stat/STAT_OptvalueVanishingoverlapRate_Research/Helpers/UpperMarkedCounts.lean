module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperIndependentAggregation
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperPilotRegularity
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperPoissonization
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.PairedHistogram.HistogramReconstruction.CountLaw

/-! # Actual marked Poisson counts and cell regularity

The histogram law realizes roadmap equations (7)–(8) for the counts used by
`markedPoissonStatistic`. Marginal laws then discharge the unconditional
square-integrability required by the variance assembly in equation (29).
-/

@[expose] public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram
open scoped BigOperators NNReal


-- @node: markedPoissonHistogram
/-- All observation–mark singleton counts in the uncapped finite sample. For the displayed parameters, markedPoissonHistogram is the object specified by this definition. -/
 def markedPoissonHistogram {d : ℕ} (s : FiniteSample (Obs d × Bool)) : (Obs d × Bool) → ℕ := finiteSampleHistogram s.points 
/-- The complete histogram is measurable on each fixed-count fibre. The [stated conclusion](goal) holds. -/
-- @node: markedPoissonHistogram_measurable
@[fun_prop]
lemma markedPoissonHistogram_measurable (d : ℕ) :
    Measurable (markedPoissonHistogram (d := d)) := by
  intro A hA
  rw [MeasurableSpace.measurableSet_iInf]
  intro k
  change MeasurableSet ((fun z : Fin k → Obs d × Bool =>
    markedPoissonHistogram ⟨k, z⟩) ⁻¹' A)
  exact Measurable.of_discrete hA

-- @node: markedPoissonHistogram_hasLaw
/-- The actual marked histogram has the product law of independent singleton Poisson counts, including zero-mass symbols. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma markedPoissonHistogram_hasLaw {d : ℕ} (P : DiscreteLaw d) (n : ℕ) :
    HasLaw (markedPoissonHistogram (d := d))
      (independentPoissonCountLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
        ((n : ℝ≥0) / 4))
      (finitePoissonSampleLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
        ((n : ℝ≥0) / 4)) := by
  exact ⟨(markedPoissonHistogram_measurable d).aemeasurable,
    finitePoissonSampleLaw_map_histogram _ _⟩


-- @node: markedCount_eq_markedPoissonHistogram
/-- A coordinate of the marked histogram is exactly the implementation's pilot or evaluation count, with the same four-coordinate encoding. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma markedCount_eq_markedPoissonHistogram {d : ℕ}
    (s : FiniteSample (Obs d × Bool)) (pilot : Bool) (x : Fin d) (j : Fin 4) :
    markedCount (le_refl s.1) (fun i => (s.2 i).1) (fun i => (s.2 i).2) pilot x j =
      markedPoissonHistogram s ((x, decide (j.val / 2 = 1),
        decide (j.val % 2 = 1)), pilot) := by
  classical
  unfold markedCount markedPoissonHistogram finiteSampleHistogram
  simp only [Fintype.card_subtype, Finset.sum_boole, Nat.cast_id]
  apply congrArg Finset.card
  ext i
  simp only [FiniteSample.points, FiniteSample.count, Fin.eta, Finset.mem_filter,
    Finset.mem_univ, true_and, Prod.eq_iff_fst_eq_snd_eq]
  constructor
  · intro h
    exact ⟨Finset.mem_univ i, h.2, h.1⟩
  · intro h
    exact ⟨h.2.2, h.2.1⟩


-- @node: markedCount_poisson_hasLaw
/-- Either mark gives the intended intensity n/8 times the observed atom mass. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma markedCount_poisson_hasLaw {d : ℕ} (P : DiscreteLaw d) (n : ℕ)
    (pilot : Bool) (x : Fin d) (j : Fin 4) :
    HasLaw (fun s : FiniteSample (Obs d × Bool) =>
      markedCount (le_refl s.1) (fun i => (s.2 i).1) (fun i => (s.2 i).2) pilot x j)
      (poissonMeasure (((n : ℝ≥0) / 8) *
        (P.pmf (x, decide (j.val / 2 = 1), decide (j.val % 2 = 1))).toNNReal))
      (finitePoissonSampleLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
        ((n : ℝ≥0) / 4)) := by
  have h := (measurePreserving_eval
    (fun z : Obs d × Bool => poissonMeasure (((n : ℝ≥0) / 4) *
      ((P.pmf.toMeasure.prod (bernoulliBool (1 / 2))) {z}).toNNReal))
    ((x, decide (j.val / 2 = 1), decide (j.val % 2 = 1)), pilot)).hasLaw.fun_comp
      (markedPoissonHistogram_hasLaw P n)
  simp_rw [← markedCount_eq_markedPoissonHistogram] at h
  convert h using 1
  congr 1
  rw [← Set.singleton_prod_singleton, Measure.prod_prod,
    PMF.toMeasure_apply_singleton, ENNReal.toNNReal_mul] <;> try measurability
  have hb : (bernoulliBool (1 / 2) {pilot}).toNNReal = (1 / 2 : ℝ≥0) := by
    cases pilot <;> apply NNReal.coe_injective <;>
      simp only [bernoulliBool, Measure.add_apply, Measure.smul_apply,
        Measure.dirac_apply' _ (measurableSet_singleton _)] <;>
      norm_num <;> change (ENNReal.ofReal (1 / 2 : ℝ)).toReal = _ <;> norm_num
  rw [hb]
  ring


-- @node: markedPoissonHistogram_iIndepFun
/-- All pilot and evaluation atom counts are mutually independent under the actual uncapped experiment, as in roadmap (8). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma markedPoissonHistogram_iIndepFun {d : ℕ} (P : DiscreteLaw d) (n : ℕ) :
    iIndepFun (fun z s => markedPoissonHistogram (d := d) s z)
      (finitePoissonSampleLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
        ((n : ℝ≥0) / 4)) := by
  let rates := fun z : Obs d × Bool => poissonMeasure (((n : ℝ≥0) / 4) *
    ((P.pmf.toMeasure.prod (bernoulliBool (1 / 2))) {z}).toNNReal)
  have hlaw := markedPoissonHistogram_hasLaw P n
  exact (iIndepFun_iff_hasLaw_pi_pi (fun z =>
    (measurePreserving_eval rates z).hasLaw.fun_comp hlaw)).2 hlaw


-- @node: markedPoissonCellValue
/-- One implemented clipped contribution before the final unit projection.
For the displayed parameters, markedPoissonCellValue is the object specified by this definition. -/
noncomputable def markedPoissonCellValue (n d : ℕ) (H : ℝ) (hH : 0 < H)
    (κ ε : ℝ) (x : Fin d) (s : FiniteSample (Obs d × Bool)) : ℝ :=
  let Np :=
    markedCount (le_refl s.1) (fun i => (s.2 i).1) (fun i => (s.2 i).2) true x
  let Ne :=
    markedCount (le_refl s.1) (fun i => (s.2 i).1) (fun i => (s.2 i).2) false x
  clippedCellValueFormula ε (jacksonDegree κ d) d (poissonIntensityFormula n)
    (pilotMidpoint H hH (poissonIntensityFormula n) (logAlphabet d) Np)
    (pilotRadiusFormula H hH (poissonIntensityFormula n) (logAlphabet d) Np) Ne
/-- Each actual marked count is measurable, including on unbounded count fibres. The [stated conclusion](goal) holds. -/
-- @node: markedPoissonCount_measurable
@[fun_prop]
lemma markedPoissonCount_measurable (d : ℕ) (pilot : Bool) (x : Fin d) (j : Fin 4) :
    Measurable (fun s : FiniteSample (Obs d × Bool) =>
      markedCount (le_refl s.1) (fun i => (s.2 i).1) (fun i => (s.2 i).2) pilot x j) := by
  simp_rw [markedCount_eq_markedPoissonHistogram]
  exact (measurable_pi_apply _).comp (markedPoissonHistogram_measurable d)

-- @node: markedPoissonCellValue_memLp_two
/-- Marginal Poisson laws supply unconditional L² regularity for every actual clipped cell, without assuming any moment bound for its factorial polynomial. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hn,hd,hHpos,hH,hε,hε1), the [stated conclusion](goal) holds. -/
lemma markedPoissonCellValue_memLp_two {n d : ℕ} (hn : 1 ≤ n) (hd : 1 ≤ d)
    (P : DiscreteLaw d) (H : ℝ) (hHpos : 0 < H)
    (hH : Causalean.Stat.Concentration.PoissonSelfNormalized.universalH ≤ H)
    (κ ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (x : Fin d) :
    MemLp (markedPoissonCellValue n d H hHpos κ ε x) 2
      (finitePoissonSampleLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
        ((n : ℝ≥0) / 4)) := by
  have hm : 0 < (n : ℝ≥0) / 8 := by positivity
  have hL : 1 ≤ logAlphabet d := by
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
    rw [logAlphabet, Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp]
    linarith [Real.log_nonneg hdR]
  unfold markedPoissonCellValue
  simpa only [poissonIntensityFormula, NNReal.coe_div,
    NNReal.coe_natCast, NNReal.coe_ofNat] using
    pilotClippedCellValue_memLp_two
      (finitePoissonSampleLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
        ((n : ℝ≥0) / 4))
      (fun j s => markedCount (le_refl s.1) (fun i => (s.2 i).1)
        (fun i => (s.2 i).2) true x j)
      (fun j s => markedCount (le_refl s.1) (fun i => (s.2 i).1)
        (fun i => (s.2 i).2) false x j)
      (fun j => (P.pmf (x, decide (j.val / 2 = 1), decide (j.val % 2 = 1))).toNNReal)
      ((n : ℝ≥0) / 8) hm H hHpos (logAlphabet d) ε hH hL hε hε1
      (jacksonDegree κ d) d
      (fun j => markedPoissonCount_measurable d true x j)
      (fun j => markedPoissonCount_measurable d false x j)
      (fun j => markedCount_poisson_hasLaw P n true x j)


-- @node: markedPoissonCellValue_sum_memLp_two
/-- The sum whose projection defines the actual marked statistic is L². In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hn,hd,hHpos,hH,hε,hε1), the [stated conclusion](goal) holds. -/
lemma markedPoissonCellValue_sum_memLp_two {n d : ℕ} (hn : 1 ≤ n) (hd : 1 ≤ d)
    (P : DiscreteLaw d) (H : ℝ) (hHpos : 0 < H)
    (hH : Causalean.Stat.Concentration.PoissonSelfNormalized.universalH ≤ H)
    (κ ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    MemLp (fun s => ∑ x, markedPoissonCellValue n d H hHpos κ ε x s) 2
      (finitePoissonSampleLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
        ((n : ℝ≥0) / 4)) :=
  memLp_finsetSum Finset.univ (fun x _ =>
    markedPoissonCellValue_memLp_two hn hd P H hHpos hH κ ε hε hε1 x)


-- @node: markedPoissonCellValue_pairwise_indepFun
/-- Distinct cells use disjoint sets of observation–mark atom counts. Their actual clipped contributions are consequently independent, including bad pilots. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hH), the [stated conclusion](goal) holds. -/
lemma markedPoissonCellValue_pairwise_indepFun {d : ℕ} (P : DiscreteLaw d)
    (n : ℕ) (H : ℝ) (hH : 0 < H) (κ ε : ℝ) :
    Pairwise (fun x y : Fin d => IndepFun
      (markedPoissonCellValue n d H hH κ ε x)
      (markedPoissonCellValue n d H hH κ ε y)
      (finitePoissonSampleLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
        ((n : ℝ≥0) / 4))) := by
  classical
  let cells (x : Fin d) : Finset (Obs d × Bool) :=
    Finset.univ.filter (fun z => z.1.1 = x)
  let atom (x : Fin d) (pilot : Bool) (j : Fin 4) : cells x :=
    ⟨((x, decide (j.val / 2 = 1), decide (j.val % 2 = 1)), pilot), by simp [cells]⟩
  let F (x : Fin d) (v : cells x → ℕ) : ℝ :=
    clippedCellValueFormula ε (jacksonDegree κ d) d (poissonIntensityFormula n)
      (pilotMidpoint H hH (poissonIntensityFormula n) (logAlphabet d)
        (fun j => v (atom x true j)))
      (pilotRadiusFormula H hH (poissonIntensityFormula n) (logAlphabet d)
        (fun j => v (atom x true j))) (fun j => v (atom x false j))
  have heq (x : Fin d) : markedPoissonCellValue n d H hH κ ε x =
      F x ∘ (fun s z => markedPoissonHistogram s (z : Obs d × Bool)) := by
    funext s
    have hc (pilot : Bool) :
        markedCount (le_refl s.1) (fun i => (s.2 i).1) (fun i => (s.2 i).2) pilot x =
          (fun j => markedPoissonHistogram s ((x, decide (j.val / 2 = 1),
            decide (j.val % 2 = 1)), pilot)) := by
      funext j
      exact markedCount_eq_markedPoissonHistogram s pilot x j
    simp only [markedPoissonCellValue, F, atom, Function.comp_apply, hc]
  intro x y hxy
  have hdis : Disjoint (cells x) (cells y) := by
    apply Finset.disjoint_left.2
    intro z hx hy
    simp only [cells, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    exact hxy (hx.symm.trans hy)
  rw [heq x, heq y]
  exact ((markedPoissonHistogram_iIndepFun P n).indepFun_finset
    (cells x) (cells y) hdis (fun z =>
      (measurable_pi_apply z).comp (markedPoissonHistogram_measurable d))).comp
    (Measurable.of_discrete (f := F x)) (Measurable.of_discrete (f := F y))


-- @node: markedPoissonCellValue_sum_sqRisk_eq
/-- Equation (29) holds for the actual unprojected marked statistic: distinct cell variances add, and the total bias is squared only after summation. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hn,hd,hHpos,hH,hε,hε1), the [stated conclusion](goal) holds. -/
lemma markedPoissonCellValue_sum_sqRisk_eq {n d : ℕ} (hn : 1 ≤ n) (hd : 1 ≤ d)
    (P : DiscreteLaw d) (H : ℝ) (hHpos : 0 < H)
    (hH : Causalean.Stat.Concentration.PoissonSelfNormalized.universalH ≤ H)
    (κ ε t : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let μ := finitePoissonSampleLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
      ((n : ℝ≥0) / 4)
    Causalean.Stat.sqRisk μ (fun s => ∑ x, markedPoissonCellValue n d H hHpos κ ε x s) t =
      (∑ x, variance (markedPoissonCellValue n d H hHpos κ ε x) μ) +
        ((∑ x, ∫ s, markedPoissonCellValue n d H hHpos κ ε x s ∂μ) - t) ^ 2 := by
  dsimp only
  let μ := finitePoissonSampleLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
    ((n : ℝ≥0) / 4)
  let T := markedPoissonCellValue n d H hHpos κ ε
  have hT (x : Fin d) : MemLp (T x) 2 μ :=
    markedPoissonCellValue_memLp_two hn hd P H hHpos hH κ ε hε hε1 x
  have hsum := markedPoissonCellValue_sum_memLp_two hn hd P H hHpos hH κ ε hε hε1
  have hind := markedPoissonCellValue_pairwise_indepFun P n H hHpos κ ε
  rw [cellStatistic_sqRisk_eq_variance_add_bias _ _ _ hsum,
    integral_finsetSum _ (fun x _ => (hT x).integrable (by norm_num))]
  have hfun : (∑ x, T x) = (fun s => ∑ x, T x s) := by funext s; simp
  have hv := IndepFun.variance_sum (X := T) (s := Finset.univ)
    (fun x _ => hT x) (fun x _ y _ hxy => hind hxy)
  rw [hfun] at hv
  rw [hv]


-- @node: markedPoissonStatistic_sqRisk_le_variance_add_bias
/-- The unit projection in the implemented uncapped statistic preserves the variance-plus-squared-bias upper bound for its actual cell sum. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hn,hd,hHpos,hH,hε,hε1), the [stated conclusion](goal) holds. -/
lemma markedPoissonStatistic_sqRisk_le_variance_add_bias {n d : ℕ}
    (hn : 1 ≤ n) (hd : 1 ≤ d) (P : DiscreteLaw d) (H : ℝ) (hHpos : 0 < H)
    (hH : Causalean.Stat.Concentration.PoissonSelfNormalized.universalH ≤ H)
    (κ ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let μ := finitePoissonSampleLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
      ((n : ℝ≥0) / 4)
    Causalean.Stat.sqRisk μ (markedPoissonStatistic n d H hHpos κ ε) (observedValue P) ≤
      (∑ x, variance (markedPoissonCellValue n d H hHpos κ ε x) μ) +
        ((∑ x, ∫ s, markedPoissonCellValue n d H hHpos κ ε x s ∂μ) - observedValue P) ^ 2 := by
  dsimp only
  have hsum := markedPoissonCellValue_sum_memLp_two hn hd P H hHpos hH κ ε hε hε1
  have hp := projectUnit_sqRisk_le _ _ (observedValue P) hsum (observedValue_mem_unitInterval P)
  change Causalean.Stat.sqRisk _ (markedPoissonStatistic n d H hHpos κ ε) _ ≤ _ at hp
  exact hp.trans_eq (markedPoissonCellValue_sum_sqRisk_eq hn hd P H hHpos hH κ ε
    (observedValue P) hε hε1)

end CausalSmith.Stat.OptvalueVanishingoverlapRate
